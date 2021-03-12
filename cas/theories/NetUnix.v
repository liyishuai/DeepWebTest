From CAS Require Export
     Observe.
From SimpleIO Require Export
     IO_Bytes
     IO_Float
     IO_Sys
     IO_Unix.
From Coq Require Export
     NArith.
Import
  OSys
  OUnix.
Local Open Scope N_scope.

Coercion int_of_n : N >-> int.

Notation default_port := 80.

Definition getport : IO int :=
  oport <- getenv_opt "PORT";;
  ret (match oport with
       | Some ostr => match int_of_ostring_opt ostr with
                     | Some port => port
                     | None => default_port
                     end
       | None => default_port
       end).

Definition conn_state := list (clientT * (file_descr * string)).

Definition conn_of_fd (fd : file_descr)
  : conn_state -> option (clientT * (file_descr * string)) :=
  find (file_descr_eqb fd ∘ fst ∘ snd).

Notation BUFFER_SIZE := 1024.
Definition SELECT_TIMEOUT := OFloat.Unsafe.of_string "0".

Definition recv_bytes : Monads.stateT conn_state IO unit :=
    (fun s =>
       '(fds, _, _) <- select (map (fst ∘ snd) s) [] [] SELECT_TIMEOUT;;
       IO.fix_io
         (fun recv_rec fds =>
            match fds with
            | [] => ret (s, tt)
            | fd :: fds' =>
              match conn_of_fd fd s with
              | Some (c, (fd, str0)) =>
                buf <- OBytes.create BUFFER_SIZE;;
                len <- recv fd buf int_zero BUFFER_SIZE [];;
                if len <? int_zero
                then close fd;;
                     ret (delete c s, tt)
                else if len =? int_zero
                     then recv_rec fds'
                     else str <- from_ostring <$> OBytes.to_string buf;;
                          let str1 : string := substring 0 (nat_of_int len) str in
                          (* prerr_endline ("Received " ++ str1 *)
                          (*                ++ " from " ++ to_string c);; *)
                          ret (update c (fd, str0 ++ str1) s, tt)
              | None => failwith "Should not happen"
              end
            end)%int (rev' fds)).

Definition try {a b} (f : IO a) (g : IO b) : IO (option a) :=
  catch_error (Some <$> f) $ fun e m _ => g;; ret None.

Definition create_conn (s : conn_state)
  : IO (conn_state * option (file_descr * clientT)) :=
  let iaddr : inet_addr := inet_addr_loopback in
  port <- getport;;
  ofd <- try (fd <- socket PF_INET SOCK_STREAM int_zero;;
             connect fd (ADDR_INET iaddr port);;
             ret fd) (ret tt);;
  match ofd with
  | Some fd =>
    let c := length s in
    ret ((c, (fd, ""))::s, Some (fd, c))
  | None => ret (s, None)
  end.

Definition send_request (req : requestT id) (s : conn_state)
  : IO (conn_state * option connT) :=
  '(s', ofdc) <- create_conn s;;
  if ofdc is Some (fd, c)
  then let str : string := to_string req in
       buf <- OBytes.of_string str;;
       let len : int := OBytes.length buf in
       IO.fix_io
         (fun send_rec o =>
            sent <- send fd buf o (len - o)%int [];;
            if sent <? int_zero
            then close fd;; ret (s', None)
            else
              if o + sent =? len
              then ret (s', Some $ Conn__Client c)
              else send_rec (o + sent))%int int_zero
  else ret (s', None).
