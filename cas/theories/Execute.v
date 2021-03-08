From CAS Require Export
     NetUnix
     Shrink
     Tester.
From ExtLib Require Export
     Applicative.
Export
  ApplicativeNotation.

(** Find all [n] s.t. [f (nth n l) = true]. *)
Definition find_nth' {A} (f : A -> bool) (l : list A) : list (nat * A) :=
  let index : list nat := seq 0 $ length l in
  filter (f ∘ snd) $ zip index l.

Definition get_tag (sc : logT) : option tag :=
  if snd sc is Some (Response__OK t _) then Some t else None.

Definition has_tag (sc : logT) : bool :=
  if get_tag sc is Some _ then true else false.

Definition arbitraryRequest (ss : server_state exp) (tr : traceT)
  : IO stepT :=
  let x : var := fresh_var $ script_of_trace tr in
  k <- io_or gen_string (io_choose_ gen_string (map fst ss));;
  let ts : list (texp tag) :=
      map (Texp__Var ∘ fst ∘ fst ∘ fst) $ filter has_tag tr in
  t <- io_choose_ (ret Texp__Random) ts;;
  pair x <$> io_or (pure $ Request__GET k t) (Request__CAS k t <$> gen_string).

Definition fill_tag (tr : traceT) (tx : texp tag) : id tag :=
  match tx with
  | Texp__Random => """Random"""
  | Texp__Var x =>
    match find (Nat.eqb x ∘ fst ∘ fst ∘ fst) tr with
    | Some (_, _, _, Some (Response__OK _ t)) => t
    | _ => """Unknown"""
    end
  end.

Definition fill_request (tr : traceT) (rx : requestT texp) : requestT id :=
  match rx with
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

Definition fill_trace (c : clientT) (res : responseT id) : traceT -> traceT :=
  replace_first (fun sc =>
                let '(_, c0, ores) := sc in
                if ores is None then c0 =? c else false)%nat
             (fun sc =>
                let '(x, req, c, _) := sc in
                (x, req, c, Some res)).

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

Fixpoint execute' {R} (fuel : nat) (s : conn_state) (oscript : option scriptT)
         (acc : traceT) (m : itree tE R)
  : IO (bool * conn_state * traceT) :=
  match fuel with
  | O => ret (true, s, acc)
  | S fuel =>
    match observe m with
    | RetF _ => ret (true, s, acc)
    | TauF m' => execute' fuel s oscript acc m'
    | VisF e k =>
      match e with
      | (Throw err|) => ret (false, s, acc)
      | (|ne|) =>
        match ne in nondetE Y return (Y -> _) -> _ with
        | Or => fun k => b <- ORandom.bool tt;;
                     execute' fuel s oscript acc (k b)
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
                execute' fuel s' oscript acc' (k op)
        | Client__Send ss es =>
          fun k =>
            '(orx, ot') <- match oscript with
                          | Some [] => ret (None, Some [])
                          | Some (sc :: script') =>
                            ret (Some $ sc, Some script')
                          | None =>
                            rx <- arbitraryRequest ss acc;;
                            ret (Some rx, None)
                          end;;
            match orx with
            | Some ((n, reqx) as step) =>
              let req := fill_request acc reqx in
              '(oc, s1) <- runStateT (send_request req) s;;
              match oc with
              | Some c =>
                (* prerr_endline ("================== SENT ===================");; *)
                let pkt := Packet (Conn__Client c) Conn__Server $ inl req in
                (* prerr_endline (to_string pkt);; *)
                execute' fuel s1 ot' (acc++[(step, c, None)])%list (k (Some pkt))
              | None => execute' fuel s1 ot' acc (k None)
              end
            | None => execute' fuel s ot' acc (k None)
            end
        end k
      end
    end
  end.

Definition execute {R} (otrace : option scriptT) (m : itree tE R)
  : IO (bool * traceT) :=
  (* prerr_endline "<<<<< begin test >>>>>";; *)
  '(b, s, t') <- execute' bigNumber [] otrace [] m;;
  (* prerr_endline "<<<<<<< end test >>>>>";; *)
  fold_left (fun m fd => OUnix.close fd;; m) (map (fst ∘ snd) s) (ret tt);;
  ret (b, t').

Definition single_test {R} (otrace : option scriptT)
  : itree smE R -> IO (bool * traceT) :=
  execute otrace ∘ tester ∘ observer _ ∘ compose_switch tcp.

Definition first_exec {R} : itree smE R -> IO (bool * traceT) :=
  single_test None.

Definition then_exec {R} (m : itree smE R) (init : scriptT) : IO (bool * traceT) :=
  single_test (Some init) m.

Definition test {R} (m : itree smE R) : IO bool :=
  shrink_execute (first_exec m) (then_exec m).
