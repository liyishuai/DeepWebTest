From CAS Require Export
     NetUnix
     Tester.
From ExtLib Require Export
     Applicative.
Export
  ApplicativeNotation.

Definition gen_request (ss : server_state exp) : IO (requestT exp) :=
  io_or
    (k <- io_choose_ gen_string (map fst ss);;
     t <- io_choose_ (Exp__Const <$> gen_string) (map (fst ∘ snd) ss);;
     ret (Request__GET k t))
    (k <- io_choose_ gen_string (map fst ss);;
     t <- io_choose_ (Exp__Const <$> gen_string) (map (fst ∘ snd) ss);;
     Request__CAS k t <$> gen_string).

Definition fill_tag (tx : exp tag) (es : exp_state) : IO (id tag) :=
  match tx with
  | Exp__Const t => io_or (ret t) gen_string
  | Exp__Var x =>
    match get x es with
    | Some (inl t) => io_or (ret t) gen_string
    | Some (inr ts) => io_or (io_choose_ gen_string ts) gen_string
    | None => gen_string
    end
  | Exp__Match _ _ => gen_string
  end.

Definition fill_request (rx : requestT exp) (es : exp_state)
  : IO (requestT id) :=
  match rx with
  | Request__GET k tx   => Request__GET k <$> fill_tag tx es
  | Request__CAS k tx v => flip (Request__CAS k) v <$> fill_tag tx es
  end.

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
        prerr_endline ("================ RECEIVED =================");;
        let pkt := Packet Conn__Server (Conn__Client c) (inr res) in
        prerr_endline (to_string pkt);;
        ret (Some pkt, (c, (f, str')) :: t)
      end
    end
  end.

Fixpoint execute' {R} (fuel : nat) (s : conn_state) (script : list (requestT exp))
         (m : itree tE R) : IO (bool * conn_state * list (requestT exp)) :=
  match fuel with
  | O => ret (true, s, [])
  | S fuel =>
    match observe m with
    | RetF _ => ret (true, s, [])
    | TauF m' => execute' fuel s script m'
    | VisF e k =>
      match e with
      | (Throw err|) => ret (false, s, [])
      | (|ne|) =>
        match ne in nondetE Y return (Y -> _) -> _ with
        | Or => fun k => b <- ORandom.bool tt;;
                     execute' fuel s script (k b)
        end k
      | (||ce) =>
        match ce in clientE Y return (Y -> _) -> _ with
        | Client__Recv =>
          fun k => '(op, s') <- execStateT recv_bytes s >>= findResponse;;
                execute' fuel s' script (k op)
        | Client__Send ss es =>
          fun k =>
            '(sc', rx) <- match script with
                         | [] => pair [] <$> gen_request ss
                         | rx :: rs => ret (rs, rx)
                         end;;
            req <- fill_request rx es;;
            '(oc, s1) <- runStateT (send_request req) s;;
            match oc with
            | Some c =>
              prerr_endline ("================== SENT ===================");;
              let pkt := Packet (Conn__Client c) Conn__Server $ inl req in
              prerr_endline (to_string pkt);;
              '(res, s2, tr) <- execute' fuel s1 sc' (k (Some pkt));;
              ret (res, s2, rx :: tr)
            | None => execute' fuel s1 sc' (k None)
            end
        end k
      end
    end
  end.

Definition execute {R} (m : itree tE R) (script : list (requestT exp))
  : IO (bool * list (requestT exp)) :=
  prerr_endline "<<<<< begin test >>>>>";;
  '(b, s, ns) <- execute' bigNumber [] [] m;;
  prerr_endline "<<<<<<< end test >>>>>";;
  fold_left (fun m fd => OUnix.close fd;; m) (map (fst ∘ snd) s) (ret tt);;
  ret (b, ns).

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

Definition shrink_execute' {R} (m : itree tE R) (script : list (requestT exp))
  : IO (option (list (requestT exp))) :=
  IO.fix_io
    (fun shrink_rec ss =>
       match ss with
       | [] => ret None
       | s :: ss' =>
         '(b, s') <- execute m s;;
         if (b : bool) ||| (length script <=? length s')
         then shrink_rec ss'
         else ret (Some s')
       end) (repeat_list 20 $ shrink_list script).

Definition shrink_execute {R} (m : itree tE R) : IO bool :=
  '(b, s) <- execute m [];;
  if b : bool
  then ret true
  else IO.while_loop (shrink_execute' m) s;; ret false.

Definition test {R} : itree smE R -> IO bool :=
  shrink_execute ∘ tester ∘ observer _ ∘ compose_switch tcp.
