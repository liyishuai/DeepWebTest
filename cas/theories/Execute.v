From CAS Require Export
     NetUnix
     Tester.
From ExtLib Require Export
     OptionMonad
     Applicative.
Export
  ApplicativeNotation.

Variant texp : Type -> Set :=
  Texp__FandB : nat -> nat -> texp tag.

Definition scriptT : Set := clientT * requestT texp * option (responseT id).
Definition traceT := list scriptT.

Instance Serialize__texp : Serialize (texp tag) :=
  fun tx => match tx with
         | Texp__FandB f b => [Atom "Texp"; to_sexp f; to_sexp b]%sexp
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

Definition find_nth {A} (f : A -> bool) : list A -> list nat :=
  map fst ∘ find_nth' f.

Definition get_tag (sc : scriptT) : option tag :=
  if snd sc is Some (Response__OK t _) then Some t else None.

Definition has_tag (sc : scriptT) : bool :=
  if get_tag sc is Some _ then true else false.

Definition arbitraryNat (n : nat) : IO nat :=
  nat_of_int <$> ORandom.int (int_of_nat n).

Definition arbitraryRequest (ss : server_state exp) (t : traceT)
  : IO (requestT texp) :=
  let n :      nat := length           t in
  let i : list nat := find_nth has_tag t in
  k <- io_or gen_string (io_choose_ gen_string (map fst ss));;
  f <- io_choose_ (if n is O then ret O else arbitraryNat n) i;;
  let t : texp tag := Texp__FandB f (n - S f) in
  io_or (pure $ Request__GET k t) (Request__CAS k t <$> gen_string).

Definition pick_tag (tr : traceT) : texp tag * tag :=
  match find_nth' has_tag tr with
  | [] => (Texp__FandB O O, """Random""")
  | (f, sc) :: _ =>
    (Texp__FandB f (length tr - S f),
     match get_tag sc with
     | Some t => t
     | None   => """Random"""    (* should not happen *)
     end)
  end.

Definition fill_tag (tr : traceT) (tx : texp tag) : texp tag * id tag :=
  let n := length tr in
  match tx with
  | Texp__FandB f b =>
    let tf := nth_error tr f        >>= get_tag in
    let tb := nth_error (rev' tr) b >>= get_tag in
    match tf, tb with
    | Some t, _ =>
      (Texp__FandB f (n - S f), t)
    | None, Some t =>
      (Texp__FandB (n - S b) b, t)
    | None, None => pick_tag tr
    end
  end.

Definition fill_request (tr : traceT) (rx : requestT texp) : requestT texp * requestT id :=
  match rx with
  | Request__GET k tx =>
    let (tx', t) := fill_tag tr tx in
    (Request__GET k tx', Request__GET k t)
  | Request__CAS k tx v =>
    let (tx', t) := fill_tag tr tx in
    (Request__CAS k tx' v, Request__CAS k t v)
  end.

Definition replace {A} (n : nat) (a : A) (l : list A) : list A :=
  firstn n l ++ a :: skipn (S n) l.

Definition replace_first {A} (f : A -> bool) (g : A -> A) (l : list A) : list A :=
  match find_nth' f l with
  | [] => l
  | (n, a)::_ => replace n (g a) l
  end.

Definition fill_trace (c : clientT) (res : responseT id) : traceT -> traceT :=
  replace_first (fun sc =>
                let '(c0, _, ores) := sc in
                if ores is None then c0 =? c else false)%nat
             (fun sc =>
                let '(c, req, _) := sc in
                (c, req, Some res)).

Fixpoint findResponse (s : conn_state)
  : IO (option (packetT id) * conn_state) :=
  match s with
  | [] => ret (None, [])
  | (c, (f, str)) as cfs :: t =>
    match parse parseParens str with
    | inl (Some err) =>
      failwith $ "Bad response " ++ to_string str ++ " received on connection "
               ++ to_string c ++ ", error message: " ++ err
    | inl None => '(op, t') <- findResponse t;;
                 ret (op, cfs :: t')
    | inr (r, str') =>
      match from_string r with
      | inl err =>
        failwith $ "Bad response " ++ to_string r ++ " received on connection "
                 ++ to_string c
      | inr res =>
        (* prerr_endline ("================ RECEIVED =================");; *)
        let pkt := Packet Conn__Server (Conn__Client c) (inr res) in
        (* prerr_endline (to_string pkt);; *)
        ret (Some pkt, (c, (f, str')) :: t)
      end
    end
  end.

Fixpoint execute' {R} (fuel : nat) (s : conn_state) (otrace : option traceT)
         (acc : traceT) (m : itree tE R)
  : IO (bool * conn_state * traceT) :=
  match fuel with
  | O => ret (true, s, acc)
  | S fuel =>
    match observe m with
    | RetF _ => ret (true, s, acc)
    | TauF m' => execute' fuel s otrace acc m'
    | VisF e k =>
      match e with
      | (Throw err|) => ret (false, s, acc)
      | (|ne|) =>
        match ne in nondetE Y return (Y -> _) -> _ with
        | Or => fun k => b <- ORandom.bool tt;;
                     execute' fuel s otrace acc (k b)
        end k
      | (||ce) =>
        match ce in clientE Y return (Y -> _) -> _ with
        | Client__Recv =>
          fun k => '(op, s') <- execStateT recv_bytes s >>= findResponse;;
                let acc' :=
                    match op with
                    | Some (Packet Conn__Server (Conn__Client c) (inr res)) =>
                      fill_trace c res acc
                    | _ => acc
                    end in
                execute' fuel s' otrace acc' (k op)
        | Client__Send ss es =>
          fun k =>
            '(orx, ot') <- match otrace with
                          | Some [] => ret (None, Some [])
                          | Some (sc :: tr') =>
                            ret (Some $ snd $ fst sc, Some tr')
                          | None =>
                            rx <- arbitraryRequest ss acc;;
                            ret (Some rx, None)
                          end;;
            match orx with
            | Some rx =>
              let (rx', req) := fill_request acc rx in
              '(oc, s1) <- runStateT (send_request req) s;;
              match oc with
              | Some c =>
                (* prerr_endline ("================== SENT ===================");; *)
                let pkt := Packet (Conn__Client c) Conn__Server $ inl req in
                (* prerr_endline (to_string pkt);; *)
                execute' fuel s1 ot' (acc++[(c, rx', None)])%list (k (Some pkt))
              | None => execute' fuel s1 ot' acc (k None)
              end
            | None => execute' fuel s ot' acc (k None)
            end
        end k
      end
    end
  end.

Definition execute {R} (m : itree tE R) (otrace : option traceT)
  : IO (bool * traceT) :=
  (* prerr_endline "<<<<< begin test >>>>>";; *)
  '(b, s, t') <- execute' bigNumber [] otrace [] m;;
  (* prerr_endline "<<<<<<< end test >>>>>";; *)
  fold_left (fun m fd => OUnix.close fd;; m) (map (fst ∘ snd) s) (ret tt);;
  ret (b, t').

Fixpoint shrink_list {A} (l : list A) : list (list A) :=
  match l with
  | [] => []
  | a :: l' => let sl' := shrink_list l' in
             l' :: cons a <$> sl'
  end.

Fixpoint repeat_list {A} (n : nat) (l : list A) : list A :=
  match n with
  | O => []
  | S n' => l ++ repeat_list n' l
  end.

Definition shrink_execute' {R} (m : itree tE R) (trace : traceT)
  : IO (option traceT) :=
  prerr_endline "<<<<< begin shrinking >>>>>";;
  prerr_endline (to_string trace);;
  IO.fix_io
    (fun shrink_rec ts =>
       match ts with
       | [] => ret None
       | t :: ts' =>
         '(b, t') <- execute m (Some t);;
         if (b : bool) ||| (length trace <=? length t')
         then
           prerr_endline "<<<<< accepting trace >>>>>";;
           prerr_endline (to_string t');;
           shrink_rec ts'
         else
           prerr_endline "<<<<< rejecting trace >>>>>";;
           prerr_endline (to_string t');;
           prerr_endline "<<<<<<< end shrinking >>>>>";;
           ret (Some t')
       end) (repeat_list 20 $ shrink_list trace).

Definition shrink_execute {R} (m : itree tE R) : IO bool :=
  '(b, t) <- execute m None;;
  if b : bool
  then ret true
  else IO.while_loop (shrink_execute' m) t;; ret false.

Definition test {R} : itree smE R -> IO bool :=
  shrink_execute ∘ tester ∘ observer _ ∘ compose_switch tcp.
