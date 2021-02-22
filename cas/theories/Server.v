From CAS Require Export
     NetUnix.
Import
  OUnix.
Open Scope string_scope.

Fixpoint findRequest (s : conn_state)
  : IO (option (file_descr * requestT) * conn_state) :=
  match s with
  | [] => ret (None, [])
  | (c, (f, str)) as cfs :: t =>
    match parse parseParens str with
    | inl (Some err) =>
      prerr_endline ("Bad response " ++ to_string str
       ++ " received on connection " ++ to_string c
                      ++ ", error: " ++ err);;
      close f;; findRequest t
    | inl None => '(op, t') <- findRequest t;;
                 ret (op, cfs :: t')
    | inr (r, str') =>
      match from_string r with
      | inl _ =>
        prerr_endline ("Bad response " ++ to_string r ++
                           " received on connection " ++ to_string c);;
        close f;; findRequest t
      | inr res =>
        prerr_endline ("================ RECEIVED =================");;
        prerr_endline (to_string (c, res));;
        ret (Some (f, res), (c, (f, str')) :: t)
      end
    end
  end.

Definition create_sock : IO file_descr :=
  let iaddr : inet_addr := inet_addr_any in
  fd <- socket PF_INET SOCK_STREAM int_zero;;
  port <- getport;;
  bind fd (ADDR_INET iaddr port);;
  listen fd 128%N;;
  ret fd.

Definition accept_conn (fd : file_descr) : stateT conn_state IO unit :=
  mkStateT $
    IO.fix_io
    (fun accept_rec s0 =>
       '(fds, _, _) <- select [fd] [] [] SELECT_TIMEOUT;;
       match fds with
       | [] => ret (tt, s0)
       | fd :: _ => cfd <- fst <$> accept fd;;
                  accept_rec (put (length s0) (fd, "") s0)
       end).

Definition receiveRequest (fd : file_descr)
  : stateT conn_state IO (file_descr * requestT) :=
  mkStateT $
    IO.fix_io
    (fun recv_rec s0 =>
       s1 <- execStateT (accept_conn fd;; recv_bytes) s0;;
       '(oreq, s2) <- findRequest s1;;
       if oreq is Some req
       then ret (req, s2)
       else recv_rec s2).

Definition sendResponse (fd : file_descr) (res : responseT id)
  : stateT conn_state IO unit :=
  mkStateT
    (fun s =>
       let str : string := to_string res in
       buf <- OBytes.of_string str;;
       let len : int := OBytes.length buf in
       IO.fix_io
         (fun send_rec o =>
            sent <- send fd buf o (len - o)%int [];;
            if sent <? int_zero
            then close fd;;
                 ret (tt, filter (negb ∘ file_descr_eqb fd ∘ fst ∘ snd) s)
            else
              if o + sent =? len
              then ret (tt, s)
              else send_rec (o + sent))%int int_zero).

Definition handler (req : requestT)
  : stateT (server_state id) IO (responseT id) :=
  let handle k (f : tag -> value -> server_state id ->
                    IO (responseT id * server_state id))
      : stateT (server_state id) IO (responseT id) :=
      mkStateT
        (fun st =>
           match get k st with
           | Some (t, v) => f t v st
           | None =>
             t <- gen_string;; v <- gen_string;;
             f t v (put k (t, v) st)
           end) in
  match req with
  | Request__GET k t0 =>
    let get_handler t v st :=
        ret (if t =? t0 then Response__NotModified : responseT id
             else Response__OK t v, st) in
    handle k get_handler
  | Request__CAS k t0 v =>
    let cas_handler t _ st :=
        if t =? t0
        then
          t1 <- gen_string;;
          ret (Response__NoContent,
               update k (t1 : tag, v) st : server_state id)
        else ret (Response__PreconditionFailed, st) in
    handle k cas_handler
  end.

Definition cas_server {R} : IO R :=
  ORandom.self_init tt;;
  sfd <- create_sock;;
  IO.loop
    (fun cs =>
    let (c0, s0) := cs : conn_state * server_state id in
       '(fd, req, c1) <- runStateT (receiveRequest sfd) c0;;
       '(res, s1) <- runStateT (handler req) s0;;
       c2 <- execStateT (sendResponse fd res) c1;;
       ret (c2, s1)) ([], []).
