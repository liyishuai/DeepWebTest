From DeepWeb Require Export
     Compose
     NetUnix
     Switch
     Test.

Fixpoint execute' {R} (fuel : nat) (s : conn_state) (m : itree tE R) : IO bool :=
  match fuel with
  | O => ret true
  | S fuel =>
    match observe m with
    | RetF _   => ret true
    | TauF m'  => execute' fuel s m'
    | VisF e k =>
      match e with
      | (ge|) =>
        match ge in genE T return (T -> _) -> _ with
        | Gen c =>
          (bind $ Packet c 0 ∘ ascii_of_int <$> ORandom.int 256)
            ∘ (compose $ execute' fuel s)
        end k
      | (|ne|) =>
        match ne in nondetE T return (T -> _) -> _ with
        | Or => (bind $ ORandom.bool tt) ∘ (compose $ execute' fuel s)
        end k
      | (||Throw err|) => prerr_endline (to_ostring err);;
                         ret false
      | (|||le|) =>
        match le in logE T return (T -> _) -> _ with
        | Log str => fun k => prerr_endline ("Tester: " ++ str);;
                          execute' fuel s (k tt)
        end k
      | (||||ne) => '(s', r) <- client_io _ ne s;;
                  execute' fuel s' (k r)
      end
    end
  end.

Definition execute {R} (m : itree tE R) : IO bool :=
  cs <- client_init;;
  execute' 500000 cs m.

Definition test : itree netE void -> IO bool :=
  execute ∘ tester ∘ observer ∘ compose_switch tcp.

Definition run' (m : itree netE void) (cs : conn_state) : IO void :=
  snd <$> interp server_io m cs.

Definition run_server (m : itree netE void) : IO void :=
  server_init >>= run' m.

Definition echo0 : IO void :=
  cs <- server_init;;
  IO.fix_io
    (fun loop _ =>
       fds <- select_fds cs;;
       let cfds := conns_of_fds fds cs in
       prerr_endline ("selected " ++ to_string (map fst cfds));;
       fold_left
         (fun _ (cfd : connT * _) =>
            let (c, fd) := cfd in
            prerr_endline "receiving...";;
            req <- recv_byte fd;;
            prerr_endline ("recv " ++ to_string (Packet c 0 req));;
            send_byte fd req;;
            prerr_endline ("sent " ++ to_string (Packet 0 c req)))
         cfds (ret tt);;
       loop tt) tt.

Definition echo1 : IO void :=
  cs <- server_init;;
  IO.fix_io
    (fun loop _ =>
       fds <- select_fds cs;;
       let cfds := conns_of_fds fds cs in
       prerr_endline ("selected " ++ to_string (map fst cfds));;
       fold_left
         (fun _ (cfd : connT * _) =>
            let (c, fd) := cfd in
            prerr_endline "receiving...";;
            req <- recv_byte fd;;
            prerr_endline ("recv " ++ to_string (Packet c 0 req));;
            let res : messageT := ascii_of_nat (Nat.lor 1 (nat_of_ascii req)) in (* bug here *)
            send_byte fd res;;
            prerr_endline ("sent " ++ to_string (Packet 0 c res)))
         cfds (ret tt);;
       loop tt) tt.

Definition client1 : IO void :=
  cs <- client_init;;
  IO.fix_io
    (fun loop _ =>
       c <- S ∘ nat_of_int <$> ORandom.int 9;;
       fd <- snd <$> create_conn c cs;;
       req <- ascii_of_int <$> ORandom.int 256;;
       send_byte fd req;;
       prerr_endline ("sent " ++ to_string (Packet c 0 req));;
       res <- recv_byte fd;;
       prerr_endline ("recv " ++ to_string (Packet 0 c res));;
       loop tt) tt.
