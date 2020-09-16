From DeepWeb Require Export
     Common.

Import
  OSys
  OUnix.

Definition getport : IO int :=
  let default : int := int_of_n 8000 in
  oport <- getenv_opt "PORT";;
  ret (match oport with
       | Some ostr => match int_of_ostring_opt ostr with
                     | Some port => port
                     | None => default
                     end
       | None => default
       end).

Definition create_sock : IO file_descr :=
  let iaddr : inet_addr := inet_addr_any in
  fd <- socket PF_INET SOCK_STREAM int_zero;;
  (ADDR_INET iaddr <$> getport) >>= bind fd;;
  listen fd 128;;
  ret fd.

Definition accept_conn (sfd : file_descr) : IO file_descr :=
  fd <- fst <$> accept sfd;;
  ret fd.

Definition conn_state := list (connT * file_descr).

Definition fd_of_conn (c : connT) : conn_state -> option file_descr :=
  fmap snd ∘ find (eqb c ∘ fst).

Definition create_conn (c : connT) : stateT conn_state IO file_descr :=
  (fun s =>
     match fd_of_conn c s with
     | Some fd => ret (s, fd)
     | None =>
       let iaddr : inet_addr := inet_addr_loopback in
       fd <- socket PF_INET SOCK_STREAM int_zero;;
       (ADDR_INET iaddr <$> getport) >>= connect fd;;
       ret ((c, fd) :: s, fd)
     end).

Definition conns_of_fds (fds : list file_descr) : conn_state -> list (connT * file_descr) :=
  filter (fun cf => existsb (file_descr_eqb $ snd cf) fds).

Definition select_fds (cs : conn_state) : IO (list file_descr) :=
  '(reads, _, _) <- select (map snd cs) [] [] (OFloat.of_int 1);;
  ret reads.

Definition recv_byte (fd : file_descr) : IO messageT :=
  buf <- OBytes.create 1;;
  IO.fix_io
    (fun recv_rec _ =>
       len <- z_of_int <$> recv fd buf int_zero 1 [];;
       match len with
       | 0%Z => prerr_endline "received 0 byte, retry";;
               OUnix.sleep 1;;
               recv_rec tt
       | 1%Z => ostr <- OBytes.to_string buf;;
               match from_ostring ostr with
               | "" => failwith "string of buffer is empty"
               | String b _ => ret b
               end
       | _ => close fd;; failwith ("recv 1 byte but returned " ++ to_string len)
       end) tt.

Definition send_byte (fd : file_descr) (msg : messageT) : IO unit :=
  buf <- OBytes.of_string (String msg "");;
  IO.fix_io
    (fun send_rec _ =>
       sent <- z_of_int <$> send fd buf int_zero 1 [];;
       match sent with
       | 0%Z => send_rec tt
       | 1%Z => ret tt
       | _   => close fd;; failwith "send byte failed"
       end) tt.

Definition client_init : IO conn_state :=
  ORandom.self_init tt;;
  fold_left
    (fun ml c => l <- ml;;
              fst <$> create_conn c l)
    conns (ret []).

Definition server_init : IO conn_state :=
  sfd <- create_sock;;
  (fold_left
     (fun ml c =>
        l <- ml;;
        fd <- accept_conn sfd;;
        ret ((c, fd) :: l)) conns (ret [])).

Definition client_io : netE ~> stateT conn_state IO :=
  fun _ ne =>
    match ne with
    | Net__Select =>
      (fun s =>
         reads <- select_fds s;;
         let cs : list connT := map fst $ conns_of_fds reads s in
         print_endline ("slct " ++ to_string cs);;
         ret (s, cs))
    | Net__Recv c =>
      (fun s =>
         match fd_of_conn c s with
         | Some fd => b <- recv_byte fd;;
                     let pkt : packetT := Packet 0 c b in
                     print_endline ("recv " ++ to_string pkt);;
                     ret (s, pkt)
         | None => failwith $ "unknown connection ID" ++ to_string c
         end)
    | Net__Send (Packet src dst msg as pkt) =>
      (fun s => '(s', fd) <- create_conn src s;;
              send_byte fd msg;;
              print_endline ("send " ++ to_string pkt);;
              ret (s', tt))
    end.

Definition server_io : netE ~> stateT conn_state IO :=
  fun _ ne =>
    match ne with
    | Net__Select =>
      (fun s =>
         reads <- select_fds s;;
         let cs : list connT := map fst $ conns_of_fds reads s in
         prerr_endline ("slct " ++ to_string cs);;
         ret (s, cs))
    | Net__Recv c =>
      (fun s =>
         match fd_of_conn c s with
         | Some fd => b <- recv_byte fd;;
                     let pkt : packetT := Packet c 0 b in
                     prerr_endline ("recv " ++ to_string pkt);;
                     ret (s, pkt)
         | None => failwith $ "unknown connection ID" ++ to_string c
         end)
    | Net__Send (Packet src dst msg as pkt) =>
      (fun s => '(s', fd) <- create_conn dst s;;
              send_byte fd msg;;
              prerr_endline ("send " ++ to_string pkt);;
              ret (s', tt))
    end.
