From Parsec Require Export
     Parser.
From CAS Require Export
     NetUnix
     Tester.
From ExtLib Require Export
     Applicative.
From Coq Require Export
     Ascii.
Export
  ApplicativeNotation.
Open Scope parser_scope.

Definition io_choose' {A} (l : list A) : IO (nat * A) :=
  match l with
  | [] => failwith "Cannot choose from empty list"
  | a :: _ =>
    i <- nat_of_int <$> ORandom.int (int_of_nat (length l));;
    ret (i, nth i l a)
  end.

Definition io_choose {A} : list A -> IO A :=
  fmap snd ∘ io_choose'.

Definition gen_string' : IO string :=
  io_choose ["Hello"; "World"].

Definition io_or {A} (x y : IO A) : IO A :=
  b <- ORandom.bool tt;;
  if b : bool then x else y.

Fixpoint gen_many {A} (n : nat) (ma : IO A) : IO (list A) :=
  match n with
  | O => ret []
  | S n' => liftA2 cons ma $ io_or (ret []) (gen_many n' ma)
  end.

Definition gen_string : IO string :=
  String "~" ∘ String.concat "" <$> gen_many 3 gen_string'.

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
       | Some (inr (t0::_ as ts)) => Request__GET k <$> io_choose ts
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
       | Some (inr (t0::_ as ts)) =>
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
       | Some (inr (t0::_ as ts)) => Request__GET k <$> io_choose ts
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
       | Some (inr (t0::_ as ts)) =>
             liftA2 (Request__CAS k) (io_choose ts) gen_string
       | _ => liftA2 (Request__CAS k)  gen_string       gen_string
       end
     | _ => liftA2 (Request__CAS k) gen_string gen_string
     end
   end;
   random_get;
   random_cas].

Fixpoint parseParens' (depth : nat) : parser string :=
  match depth with
  | O => raise None
  | S depth =>
    prefix <- string_of_list_ascii <$> untilMulti ["(";")"]%char;;
    r <- anyToken;;
    match r with
    | ")"%char => ret $ prefix ++ ")"
    | "("%char =>
      append prefix ∘ String r <$>
             liftA2 append (parseParens' depth) (parseParens' depth)
    | _ => raise $ Some "Should not happen"
    end
  end.

Definition parseParens : parser string :=
  liftA2 String (expect "("%char) $ parseParens' bigNumber.

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
        ret (Some (Packet Conn__Server (Conn__Client c) (inr res)),
             (c, (f, str')) :: t)
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
            c <- io_choose (length s :: map fst s);;
            '(b, s1) <- runStateT (send_request c req) s;;
            if b : bool
            then
              '(res, s2, tr) <- execute' fuel s1 sc'
                       (k $ Some $ Packet (Conn__Client c) Conn__Server $ inl req);;
              ret (res, s2, n :: tr)
            else execute' fuel s1 sc' (k None)
        end k
      end
    end
  end.

Definition execute {R} (m : itree tE R) (script : list nat) : IO (bool * list nat) :=
  '(b, s, ns) <- execute' bigNumber [] [] m;;
  fold_left (fun m fd => OUnix.close fd;; m) (map (fst ∘ snd) s) (ret tt);;
  ret (b, ns).
