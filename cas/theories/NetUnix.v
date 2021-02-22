From CAS Require Export
     Observe.
From SimpleIO Require Export
     IO_Bytes
     IO_Float
     IO_Random
     IO_Unix
     SimpleIO.
From ExtLib Require Export
     StateMonad.
From Coq Require Export
     ExtrOcamlIntConv
     NArith.
Import
  OUnix.
Local Open Scope N_scope.

Coercion int_of_n : N >-> int.

Definition getport : IO N :=
  N.add 8000 ∘ n_of_int <$> ORandom.int 5000.

Definition try {a b} (f : IO a) (g : IO b) : IO (option a) :=
  catch_error (Some <$> f) $ fun e m _ => g;; ret None.

Definition create_sock' (port : N) : IO (option file_descr) :=
  let iaddr : inet_addr := inet_addr_any in
  ofd <- try (socket PF_INET SOCK_STREAM int_zero) (ret tt);;
  match ofd with
  | Some fd =>
    let f := bind fd (ADDR_INET iaddr $ int_of_n port);;
             listen fd 128;;
             ret fd in
    try f $ close fd
  | None => ret None
  end.

Definition create_sock : IO (N * file_descr) :=
  getport >>= IO.fix_io
          (fun next p => ofd <- create_sock' p;;
                      match ofd with
                      | Some fd => ret (p, fd)
                      | None    => getport >>= next
                      end).

Definition conn_state := list (clientT * (file_descr * string)).

Definition conn_of_fd (fd : file_descr)
  : conn_state -> option (clientT * (file_descr * string)) :=
  find (file_descr_eqb fd ∘ fst ∘ snd).

Notation server_port := 80.

Notation BUFFER_SIZE := 1024.
Definition SELECT_TIMEOUT := OFloat.Unsafe.of_string "0".

Definition recv_bytes' : stateT conn_state IO bool :=
  mkStateT
    (fun s =>
       '(fds, _, _) <- select (map (fst ∘ snd) s) [] [] SELECT_TIMEOUT;;
       fold_left
         (fun _bs0 fd =>
            '(b, s0) <- _bs0;;
            match conn_of_fd fd s0 with
            | Some (c, (fd, str0)) =>
              buf <- OBytes.create BUFFER_SIZE;;
              len <- recv fd buf int_zero BUFFER_SIZE [];;
              if len <? int_zero
              then close fd;; _bs0
              else if len =? int_zero
                   then _bs0
                   else str <- from_ostring <$> OBytes.to_string buf;;
                        let str1 : string := substring 0 (nat_of_int len) str in
                        ret (true, update c (fd, str0 ++ str1) s0)
            | None => _bs0
            end)%int fds (ret (false, s))).

Definition recv_bytes : stateT conn_state IO unit :=
  mkStateT
    (IO.fix_io
       (fun recv_rec s =>
          '(b, s') <- runStateT recv_bytes' s;;
          if b : bool then recv_rec s' else ret (tt, s'))).

Definition create_conn : stateT conn_state IO (option (file_descr * clientT)) :=
  mkStateT
    (fun s =>
       let iaddr : inet_addr := inet_addr_loopback in
       ofd <- try (fd <- socket PF_INET SOCK_STREAM int_zero;;
                  connect fd (ADDR_INET iaddr server_port);;
                  ret fd) (ret tt);;
       match ofd with
       | Some fd =>
         let c := length s in
         ret (Some (fd, c), (c, (fd, ""))::s)
       | None => ret (None, s)
       end).

Definition send_request (req : requestT)
  : stateT conn_state IO (option clientT):=
  let send_bytes fd s :=
      let str : string := to_string req in
      buf <- OBytes.of_string str;;
      let len : int := OBytes.length buf in
      IO.fix_io
        (fun send_rec o =>
           sent <- send fd buf o (len - o)%int [];;
           if sent <? int_zero
           then close fd;; ret false
           else
             if o + sent =? len
             then ret true
             else send_rec (o + sent))%int int_zero in
  mkStateT
    (fun s => '(ocfd, s') <- runStateT create_conn s;;
           match ocfd with
           | Some (fd, c) => b <- send_bytes fd s';;
                            ret (if b : bool then Some c else None, s')
           | None => ret (None, s')
           end).
