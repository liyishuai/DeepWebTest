From IShrink Require Export
     IShrink.
From CAS Require Export
     NetUnix
     Tester.
From ExtLib Require Export
     Applicative.
Export
  ApplicativeNotation.

Variant texp : Type -> Set :=
  Texp__Random :    texp tag
| Texp__Var : var -> texp tag.

Instance Serialize__texp : Serialize (texp tag) :=
  fun tx => match tx with
         | Texp__Random => Atom "Random"
         | Texp__Var x => [Atom "Step"; to_sexp x]%sexp
         end.

Instance Serialize__reqtexp : Serialize (requestT texp) :=
  fun m =>
    match m with
    | Request__GET k t =>
      [Atom "GET"; to_sexp k; to_sexp t]
    | Request__CAS k t v =>
      [Atom "CAS"; to_sexp k; to_sexp t; to_sexp v]
    end%sexp.

(** Find all [n] s.t. [f (nth n l) = true]. *)
Definition find_nth' {A} (f : A -> bool) (l : list A) : list (nat * A) :=
  let index : list nat := seq 0 $ length l in
  filter (f ∘ snd) $ zip index l.

Notation stepT  := (stepT  texp requestT).
Notation logT   := (logT   texp requestT responseT connT).
Notation traceT := (traceT texp requestT responseT connT).

Definition get_tag (sc : logT) : option tag :=
  if snd sc is Some (Response__OK t _) then Some t else None.

Definition has_tag (sc : logT) : bool :=
  if get_tag sc is Some _ then true else false.

Definition gen_step (ss : server_state exp) (tr : traceT)
  : IO stepT :=
  let x : var := fresh_var $ map (snd ∘ fst) tr in
  k <- io_or gen_string (io_choose_ gen_string (map fst ss));;
  let ts : list (texp tag) :=
      map (Texp__Var ∘ fst ∘ snd ∘ fst) $ filter has_tag tr in
  t <- io_choose_ (ret Texp__Random) ts;;
  pair x <$> io_or (pure $ Request__GET k t) (Request__CAS k t <$> gen_string).

Definition fill_tag (tr : traceT) (tx : texp tag) : id tag :=
  match tx with
  | Texp__Random => """Random"""
  | Texp__Var x =>
    match find (Nat.eqb x ∘ fst ∘ snd ∘ fst) tr with
    | Some (_, _, Some (Response__OK _ t)) => t
    | _ => """Unknown"""
    end
  end.

Definition fill_request (tr : traceT) (step : stepT) : requestT id :=
  match snd step with
  | Request__GET k tx => Request__GET k $ fill_tag tr tx
  | Request__CAS k tx v => Request__CAS k (fill_tag tr tx) v
  end.

Definition replace {A} (n : nat) (a : A) (l : list A) : list A :=
  firstn n l ++ a :: skipn (S n) l.

Definition replace_first {A} (f : A -> bool) (g : A -> A) (l : list A) : list A :=
  match find_nth' f l with
  | [] => l
  | (n, a)::_ => replace n (g a) l
  end.

Definition fill_trace (p : packetT id) : traceT -> traceT :=
  match p with
  | Packet _ _ (inl _) => id
  | Packet _ c (inr res) =>
    replace_first
      (fun sc =>
         let '(c0, _, ores) := sc in
         if ores is None then c0 = c? else false)%nat
      (fun sc =>
         let '(c, st, _) := sc in
         (c, st, Some res))
  end.

Fixpoint findResponse (s : conn_state)
  : IO (conn_state * option (packetT id)) :=
  match s with
  | [] => ret ([], None)
  | (c, (f, str)) as cfs :: t =>
    match parse parseParens str with
    | inl (Some err) =>
      failwith $ "Bad response " ++ to_string str ++ " received on connection "
               ++ to_string c ++ ", error message: " ++ err
    | inl None => '(t', op) <- findResponse t;;
                 ret (cfs :: t', op)
    | inr (r, str') =>
      match from_string (H:=Deserialize__responseT) r with
      | inl err =>
        failwith $ "Bad response " ++ to_string r ++ " received on connection "
                 ++ to_string c
      | inr res =>
        (* prerr_endline ("================ RECEIVED =================");; *)
        let pkt := Packet Conn__Server (Conn__Client c) (inr res) in
        (* prerr_endline (to_string pkt);; *)
        ret ((c, (f, str')) :: t, Some pkt)
      end
    end
  end.

Definition cas_tester {R} : itree tE R :=
  tester $ observer _ $ compose_switch tcp cas_smi.

Instance Shrink__requestT : Shrink (requestT texp) := {
  shrink _ := [] }.

Arguments test : default implicits.

Definition test_cas : IO bool :=
  test (expT:=texp)
       (requestT:=requestT)
       (responseT:=responseT)
       Shrink__requestT
       Serialize__reqtexp
       Serialize__responseT
       (connT:=connT)
       Conn__Server
       Serialize__connT
       (gen_state:=server_state exp)
       (otherE:=nondetE)
       (fun _ e => match e with
                | Or => ORandom.bool tt
                end)
       (conn_state:=conn_state)
       []
       fill_trace
       fill_request
       gen_step
       (recv_bytes;; findResponse)
       send_request
       (R:=void)
       (fun s => fold_left (fun m fd => OUnix.close fd;; m)
                        (map (fst ∘ snd) s) (ret tt))
       cas_tester.
