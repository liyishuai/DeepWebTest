From CAS Require Export
     Observe.

Definition exp_state:= list (var * (string + list string)).

Definition fresh_var {T} (vs : list (var * T)) : var :=
  S $ fold_left max (map fst vs) O.

Definition fresh_value (s : exp_state) : exp_state * var :=
  let x := fresh_var s in
  (update x (inr []) s, x).

Definition assert (x : var) (v : string) (s : exp_state) : string + exp_state :=
  let ov := get x s in
  let err := inl $ "Expect " ++ to_string ov
        ++ ", but observed " ++ to_string v in
  match ov with
  | Some (inl v0) => if v =? v0 then inr s else err
  | Some (inr vs) => if existsb (String.eqb v) vs
                    then err else inr $ update x (inl v) s
  | None          => inr $ update x (inl v) s
  end.

Definition assert_not (x : var) (v : string) (s : exp_state)
  : string + exp_state :=
  let ov := get x s in
  let err := inl $ "Expect not " ++ to_string ov
            ++ ", but observed " ++ to_string v in
  match ov with
  | Some (inl v0) => if v =? v0 then err else inr s
  | Some (inr vs) => if existsb (String.eqb v) vs
                    then inr s
                    else inr $ update x (inr (v :: vs)) s
  | None          => inr $ update x (inr [v]) s
  end.

Definition unify {T} (e : exp T) (v : T) (s : exp_state) : string + exp_state :=
  match e in exp T return T -> exp_state -> string + exp_state with
  | Exp__Const v0 =>
    fun v s =>
      if v = v0? then inr s
      else inl $ "Expect " ++ to_string e ++ ", but observed " ++ to_string v
  | Exp__Var x    => fun v s => assert x v s
  | Exp__Match v0 (Exp__Var x) =>
    fun b => if b then assert x v0 else assert_not x v0
  | Exp__Match _ vx => fun _ _ => inl $ "Unexpected expression " ++ to_string vx
  end v s.

Variant testerE : Type -> Type :=
  Tester__Recv : testerE (packetT id)
| Tester__Send : server_state exp -> testerE (packetT id).

Class Is__stE E `{failureE -< E} `{decideE -< E} `{testerE -< E}.
Notation stE := (failureE +' decideE +' testerE).
Instance stE_Is__stE : Is__stE stE. Defined.

Definition instantiate_unify {E R} `{failureE -< E} (e : unifyE R)
  : Monads.stateT exp_state (itree E) R :=
  fun s =>
    match e with
    | Unify__Fresh =>
      let (s', x) := fresh_value s in
      Ret (s', Exp__Var x)
    | Unify__Match bx b =>
      match unify bx b s with
      | inl err => throw $ "Unify match failed: " ++ err
      | inr s'  => Ret (s', tt)
      end
    | Unify__Response rx r =>
      match rx, r with
      | Response__NotModified       , Response__NotModified
      | Response__NoContent         , Response__NoContent
      | Response__PreconditionFailed, Response__PreconditionFailed => ret (s, tt)
      | Response__OK tx vx, Response__OK t v =>
        match unify tx t s with
        | inl err => throw $ "Unify tag failed: " ++ err
        | inr s1  =>
          match unify vx v s1 with
          | inl err => throw $ "Unify value failed: " ++ err
          | inr s2  => Ret (s2, tt)
          end
        end
      | _, _ => throw $ "Expect response " ++ to_string rx
                     ++ ", but observed " ++ to_string r
      end
    end.

Definition instantiate_observe {E R} `{Is__stE E} (e : observeE R)
  : Monads.stateT exp_state (itree E) R :=
  fun s =>
    match e with
    | Observe__ToServer st => pkt <- embed Tester__Send st;;
                           Ret (s, pkt)
    | Observe__FromServer  => pkt <- trigger Tester__Recv;;
                           Ret (s, pkt)
    end.

Definition unifier' {E} `{Is__stE E}
  : itree oE ~> Monads.stateT exp_state (itree E) :=
  interp
    (fun _ e =>
       match e with
       | (Throw err|) => fun s => throw err
       | (|de|)       => Monads.liftState $ trigger de
       | (||ue|)       => instantiate_unify ue
       | (|||oe)      => instantiate_observe oe
       end).

Definition unifier {E R} `{Is__stE E} (m : itree oE R) : itree E R :=
  snd <$> unifier' _ m [].

CoFixpoint match_event {T R} (e0 : testerE R) (r : R) (m : itree stE T)
  : itree stE T :=
  match observe m with
  | RetF x  => Ret x
  | TauF m' => Tau (match_event e0 r m')
  | VisF e k =>
    match e with
    | (||oe) =>
      match oe in testerE Y, e0 in testerE R return (Y -> _) -> R -> _ with
      | Tester__Send _  , Tester__Send _
      | Tester__Recv    , Tester__Recv => id
      | _, _ => fun _ _ => throw "Unexpected event"
      end k r
    | _ => vis e (match_event e0 r ∘ k)
    end
  end.

Definition match_observe {T R} (e : testerE T) (r : T) (l : list (itree stE R))
  : list (itree stE R) := map (match_event e r) l.

Notation clientE    := (clientE    requestT responseT connT (server_state exp)).
Notation Client__Recv := (Client__Recv requestT responseT connT (server_state exp)).
Notation Client__Send := (Client__Send requestT responseT connT (server_state exp)).
Notation tE := (failureE +' clientE +' nondetE).

CoFixpoint backtrack' {R} (others : list (itree stE R))
           (m : itree stE R) : itree tE R :=
  match observe m with
  | RetF r => Ret r
  | TauF m' => Tau (backtrack' others m')
  | VisF e k =>
    let catch (err : string) : itree tE R :=
        match others with
        | [] => throw err
        | other :: others' =>
          (* embed Log ("Retry upon " ++ err);; *)
          Tau (backtrack' others' other)
        end in
    match e with
    | (Throw err|) => catch err
    | (|de|) =>
      match de in decideE Y return (Y -> _) -> _ with
      | Decide => fun k => b <- trigger Or;;
                       Tau (backtrack' (k (negb b) :: others) (k b))
      end k
    | (||te) =>
      let postpone :=
          match others with
          | []              => Tau (backtrack' [] m)
          | other :: others' => Tau (backtrack' (others' ++ [m]) other)
          end in
      match te in testerE Y return (Y -> _) -> _ with
      | Tester__Send st =>
        fun k => op1 <- trigger Client__Recv;;
              match op1 with
              | Some p1 =>
                match match_observe Tester__Recv p1 others with
                | [] => throw "Unexpected receive from server"
                | other :: others' =>
                  Tau (backtrack' others' other)
                end
              | None =>
                opkt <- embed Client__Send st;;
                match opkt with
                | Some pkt =>
                  Tau (backtrack' (match_observe (Tester__Send st)
                                                 pkt others) (k pkt))
                | None => postpone
                end
              end
      | Tester__Recv =>
        fun k => opkt <- embed Client__Recv;;
              match opkt with
              | Some pkt =>
                Tau (backtrack' (match_observe Tester__Recv pkt others) (k pkt))
              | None => postpone
              end
      end k
    end
  end.

Definition backtrack {R} : itree stE R -> itree tE R :=
  backtrack' [].

Definition tester {R} : itree oE R -> itree tE R :=
  backtrack ∘ unifier.
