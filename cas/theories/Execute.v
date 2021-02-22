From CAS Require Export
     NetUnix
     Tester.
From ExtLib Require Export
     Applicative.
Export
  ApplicativeNotation.

Definition gen_request (ss : server_state exp) (es : exp_state)
  : list (IO requestT) :=
  let random_get :=
      liftA2 Request__GET gen_string gen_string in
  let random_cas :=
      liftA2 Request__CAS gen_string gen_string <*> gen_string in
  [match ss with                (* Expect Not Modified *)
   | [] => random_get
   | _::_ =>
     '(k, (tx, vx)) <- io_choose ss;;
     match tx with
     | Exp__Const t => ret $ Request__GET k t
     | Exp__Var   x =>
       match get x es with
       | Some (inl t)      => ret $ Request__GET k t
       | Some (inr ((t0::_) as ts)) => Request__GET k <$> io_choose ts
       | Some (inr []) | None    => Request__GET k <$> gen_string
       end
     | Exp__Match _ _ => Request__GET k <$> gen_string
     end
   end;
   match ss with                (* Expect No Content *)
   | [] => random_cas
   | ss0::_ =>
     '(k, (tx, vx)) <- io_choose ss;;
     match tx with
     | Exp__Const t => Request__CAS k t <$> gen_string
     | Exp__Var   x =>
       match get x es with
       | Some (inl t) => Request__CAS k t <$> gen_string
       | Some (inr ((t0::_) as ts)) =>
         liftA2 (Request__CAS k) (io_choose ts) gen_string
       | Some (inr []) | None => liftA2 (Request__CAS k) gen_string gen_string
       end
     | Exp__Match _ _ => liftA2 (Request__CAS k) gen_string gen_string
     end
   end;
  match ss with                 (* Expect OK *)
   | [] => random_get
   | ss0::_ =>
     '(k, (tx, vx)) <- io_choose ss;;
     match tx with
     | Exp__Const t => Request__GET k <$> gen_string
     | Exp__Var   x =>
       match get x es with
       | Some (inr ((t0::_) as ts)) => Request__GET k <$> io_choose ts
       | _                       => Request__GET k <$> gen_string
       end
     | Exp__Match _ _ => Request__GET k <$> gen_string
     end
   end;
   match ss with                (* Expect Precondition Failed *)
   | [] => random_cas
   | ss0::_ =>
     '(k, (tx, vx)) <- io_choose ss;;
     match tx with
     | Exp__Var   x =>
       match get x es with
       | Some (inr ((t0::_) as ts)) =>
             liftA2 (Request__CAS k) (io_choose ts) gen_string
       | _ => liftA2 (Request__CAS k)  gen_string       gen_string
       end
     | _ => liftA2 (Request__CAS k) gen_string gen_string
     end
   end;
   random_get;
   random_cas].

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

Fixpoint execute' {R} (fuel : nat) (s : conn_state) (script : list nat)
         (m : itree tE R) : IO (bool * conn_state * list nat) :=
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
            '(n, sc', req) <- match script with
                             | [] =>
                               '(n, greq) <- io_choose' (gen_request ss es);;
                               pair (n, []) <$> greq
                             | n :: ns =>
                               match nth_error (gen_request ss es) n with
                               | Some greq => pair (n, ns) <$> greq
                               | None =>
                                 '(n', greq) <- io_choose' (gen_request ss es);;
                                 pair (n', ns) <$> greq
                               end
                             end;;
            '(oc, s1) <- runStateT (send_request req) s;;
            match oc with
            | Some c =>
              prerr_endline ("================== SENT ===================");;
              let pkt := Packet (Conn__Client c) Conn__Server $ inl req in
              prerr_endline (to_string pkt);;
              '(res, s2, tr) <- execute' fuel s1 sc' (k (Some pkt));;
              ret (res, s2, n :: tr)
            | None => execute' fuel s1 sc' (k None)
            end
        end k
      end
    end
  end.

Definition execute {R} (m : itree tE R) (script : list nat) : IO (bool * list nat) :=
  prerr_endline "<<<<< begin test >>>>>";;
  '(b, s, ns) <- execute' bigNumber [] [] m;;
  prerr_endline "<<<<<<< end test >>>>>";;
  fold_left (fun m fd => OUnix.close fd;; m) (map (fst ∘ snd) s) (ret tt);;
  ret (b, ns).

Fixpoint shrink_list {A} (l : list A) : list (list A) :=
  match l with
  | [] => []
  | a :: l' => let sl' := shrink_list l' in
             l' :: sl' ++ cons a <$> sl'
  end.

Definition shrink_execute' {R} (m : itree tE R) (script : list nat)
  : IO (option (list nat)) :=
  IO.fix_io
    (fun shrink_rec ss =>
       match ss with
       | [] => ret None
       | s :: ss' =>
         '(b, s') <- execute m s;; (* maybe multiple times *)
         if (b : bool) ||| (length script <? length s')
         then shrink_rec ss'
         else ret (Some s')
       end) (shrink_list script).

Definition shrink_execute {R} (m : itree tE R) : IO bool :=
  '(b, s) <- execute m [];;
  if b : bool
  then ret true
  else IO.while_loop (shrink_execute' m) s;; ret false.

Definition test {R} : itree smE R -> IO bool :=
  shrink_execute ∘ tester ∘ observer _ ∘ compose_switch tcp.
