From Coq Require Export
     Ascii
     Basics
     ExtrOcamlIntConv
     List
     String
     ZArith
     Nat.
From ExtLib Require Export
     Extras
     Functor
     StateMonad
     Monad.
From Ceres Require Import
     Ceres.
From ITree Require Export
     Nondeterminism
     ITree.
From SimpleIO Require Export
     IO_Bytes
     IO_Float
     IO_Sys
     IO_Unix
     SimpleIO.
Export
  FunNotation
  FunctorNotation
  ListNotations
  MonadNotation.
Global Open Scope bool_scope.
Global Open Scope monad_scope.
Global Open Scope nat_scope.
Global Open Scope program_scope.

Definition sublist {E A} `{nondetE -< E} : list A -> itree E (list A * list A) :=
  fold_right
    (fun a lr =>
       '(l, r) <- lr;;
       or (ret (a :: l, r))
          (ret (l, a :: r))) (ret ([], [])).

Variant decideE : Type -> Set :=
  Decide : decideE bool.

Notation connT    := nat.
Definition conn_is_app : connT -> bool :=
  Nat.eqb O.

Notation messageT := ascii.
Record packetT := Packet {
  packet__src     : connT;
  packet__dst     : connT;
  packet__payload : messageT }.

Definition eqb_packet (p1 p2 : packetT) : bool :=
  let 'Packet src1 dst1 msg1 := p1 in
  let 'Packet src2 dst2 msg2 := p2 in
  (src1 =? src2) && (dst1 =? dst2) && (msg1 =? msg2)%char.

Variant netE : Type -> Set :=
  Net__Select : netE (list connT)
| Net__Recv   : connT -> netE packetT
| Net__Send   : packetT -> netE unit.

Variant genE : Type -> Set :=
  Gen : genE packetT.

Fixpoint step {E R} (fuel : nat) (m : itree E R) : itree E (option R) :=
  match fuel with
  | O => ret None
  | S fuel =>
    match observe m with
    | RetF r   => ret (Some r)
    | TauF m'  => step fuel m'
    | VisF e k => trigger e >>= step fuel ∘ k
    end
  end.

Import
  OSys
  OUnix.
Coercion int_of_nat : nat >-> int.

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
