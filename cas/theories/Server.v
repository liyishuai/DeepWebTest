From CAS Require Export
     NetUnix.
Import
  OUnix.
Open Scope string_scope.

Definition create_sock : IO file_descr :=
  let iaddr : inet_addr := inet_addr_any in
  fd <- socket PF_INET SOCK_STREAM int_zero;;
  port <- getport;;
  bind fd (ADDR_INET iaddr port);;
  listen fd 128%N;;
  ret fd.

Definition receiveRequest : file_descr -> IO (file_descr * requestT id) :=
  IO.fix_io
    (fun recv_rec sfd =>
       fd <- fst <$> accept sfd;;
       buf <- OBytes.create BUFFER_SIZE;;
       len <- recv fd buf int_zero BUFFER_SIZE [];;
       let retry := close fd;; recv_rec sfd in
       if (len <=? int_zero)%int
       then retry
       else str <- substring O (nat_of_int len) ∘ from_ostring
                            <$> OBytes.to_string buf;;
            match from_string str with
            | inl _ => retry
            | inr req => ret (fd, req)
            end).

Definition sendResponse (fd : file_descr) (res : responseT id) : IO unit :=
       let str : string := to_string res in
       buf <- OBytes.of_string str;;
       let len : int := OBytes.length buf in
       IO.fix_io
         (fun send_rec o =>
            sent <- send fd buf o (len - o)%int [];;
            if sent <? int_zero
            then close fd
            else
              if o + sent =? len
              then close fd
              else send_rec (o + sent))%int int_zero.

Definition handler (req : requestT id)
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
          ret (Response__NoContent, st
               (* update k (t1 : tag, v) st : server_state id *))
        else ret (Response__PreconditionFailed, st) in
    handle k cas_handler
  end.

Definition cas_server : IO unit :=
  ORandom.self_init tt;;
  sfd <- create_sock;;
  IO.loop
    (fun s0 =>
       '(fd, req) <- receiveRequest sfd;;
       '(res, s1) <- runStateT (handler req) s0;;
       sendResponse fd res;;
       ret s1) [].
