From Coq Require Import
     ExtrOcamlIntConv
     ZArith.
From Ceres Require Import
     Ceres.
From ExtLib Require Import
     StateMonad.
From SimpleIO Require Import
     IO_Bytes
     IO_Float
     IO_Sys
     IO_Unix
     SimpleIO.
From DeepWeb Require Export
     Test.
Coercion int_of_nat : nat >-> int.

Module Unix.

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
    fst <$> accept sfd.

  Definition conn_state := list (connT * file_descr).

  Definition fd_of_conn (c : connT) : conn_state -> option file_descr :=
    fmap snd ∘ find (eqb c ∘ fst).

  Definition create_conn (c : connT) : stateT conn_state IO file_descr :=
    mkStateT
      (fun s =>
         match fd_of_conn c s with
         | Some fd => ret (fd, s)
         | None =>
           let iaddr : inet_addr := inet_addr_loopback in
           fd <- socket PF_INET SOCK_STREAM int_zero;;
           (ADDR_INET iaddr <$> getport) >>= connect fd;;
           ret (fd, (c, fd) :: s)
         end).

  Definition conns_of_fds (fds : list file_descr) : conn_state -> list connT :=
    map fst ∘ filter (fun cf => existsb (file_descr_eqb $ snd cf) fds).

  Definition recv_byte (fd : file_descr) : IO messageT :=
    buf <- OBytes.create 1;;
    IO.fix_io
      (fun recv_rec _ =>
         len <- z_of_int <$> recv fd buf int_zero 1 [];;
         match len with
         | 0%Z => recv_rec tt
         | 1%Z => ostr <- OBytes.to_string buf;;
                 match from_ostring ostr with
                 | "" => failwith "string of buffer is empty"
                 | String b _ => ret b
                 end
         | _ => close fd;; failwith ("recv 1 byte but returned " ++ to_string len)
         end) tt.

  Definition send_byte (fd : file_descr) (msg : messageT) : IO unit :=
    buf <- OBytes.create 1;;
    IO.fix_io
      (fun send_rec _ =>
         sent <- z_of_int <$> send fd buf int_zero 1 [];;
         match sent with
         | 0%Z => send_rec tt
         | 1%Z => ret tt
         | _   => close fd;; failwith "send byte failed"
         end) tt.

  Definition net_io : netE ~> stateT conn_state IO :=
    fun _ ne =>
      match ne with
      | Net__Select =>
        mkStateT
          (fun s =>
             '(reads, _, _) <- select (map snd s) [] [] (OFloat.of_int 1);;
             ret (conns_of_fds reads s, s))
      | Net__Recv c =>
        mkStateT
          (fun s =>
             match fd_of_conn c s with
             | Some fd => b <- recv_byte fd;;
                         ret (Packet 0 c b, s)
             | None => failwith $ "unknown connection ID" ++ to_string c
             end)
      | Net__Send (Packet src dst msg) =>
        mkStateT
          (fun s =>
             if conn_is_app dst
             then
               '(fd, s') <- runStateT (create_conn dst) s;;
               send_byte fd msg;;
               ret (tt, s')
             else
               prerr_endline "Ignore sends other than the application";;
               ret (tt, s))
      end.

End Unix.

Import Unix.

Notation tE := (genE +' nondetE +' failureE +' netE).

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
      | (|||ne) => '(r, s') <- runStateT (net_io _ ne) s;;
                  execute' fuel s' (k r)
      end
    end
  end.

Definition execute {R} : itree tE R -> IO bool :=
  bind (fold_right (flip bind ∘ execStateT ∘ create_conn) (ret []) conns)
       ∘ flip (execute' 5000).

Definition test {R} : itree netE R -> IO bool :=
  execute ∘ tester ∘ observer.

Definition run' {R} : itree netE R -> conn_state -> IO R :=
  curry $ IO.fix_io
        (fun loop ms =>
           let (m, s) := ms : _ * conn_state in
           match observe m with
           | RetF r   => ret r
           | TauF m'  => loop (m', s)
           | VisF e k =>
             '(r, s') <- runStateT (net_io _ e) s;;
             loop (k r, s')
           end).

Definition run_server {R} (m : itree netE R) : IO R :=
  sfd <- create_sock;;
  (fold_left
     (fun ml c =>
        l <- ml;;
        fd <- accept_conn sfd;;
        ret ((c, fd) :: l)) conns (ret [])) >>= run' m.
