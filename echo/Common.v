From Coq Require Export
     Ascii
     Basics
     ExtrOcamlIntConv
     List
     String
     ZArith
     Nat.
From Ceres Require Export
     CeresSerialize
     Ceres.
From ExtLib Require Export
     Extras
     Functor
     Monad.
From ITree Require Export
     Exception
     Nondeterminism
     ITree.
From SimpleIO Require Export
     IO_Bytes
     IO_Float
     IO_Random
     IO_Unix
     IO_Sys
     SimpleIO.
From ITreeIO Require Export
     ITreeIO.
Export
  FunNotation
  FunctorNotation
  ListNotations
  Monads
  SumNotations
  MonadNotation.
Global Open Scope bool_scope.
Global Open Scope monad_scope.
Global Open Scope nat_scope.
Global Open Scope program_scope.
Global Open Scope sum_scope.

Fixpoint pick {A} (f : A -> bool) (l : list A) : option (A * list A) :=
  match l with
  | [] => None
  | a :: tl =>
    if f a
    then Some (a, tl)
    else match pick f tl with
         | Some (x, l') => Some (x, a :: l')
         | None => None
         end
  end.

Definition sublist {E A} `{nondetE -< E} : list A -> itree E (list A * list A) :=
  fold_right
    (fun a lr =>
       '(l, r) <- lr;;
       or (ret (a :: l, r))
          (ret (l, a :: r))) (ret ([], [])).

Variant decideE : Type -> Set :=
  Decide : decideE bool.

Notation connT    := nat.
Definition conns : list connT := seq 1 9.
Definition conn_is_app : connT -> bool :=
  Nat.eqb O.

Notation messageT := ascii.
Record packetT := Packet {
  packet__src     : connT;
  packet__dst     : connT;
  packet__payload : messageT }.

Coercion Z.of_nat : connT >-> Z.

Local Open Scope sexp_scope.
Instance Serialize__messageT : Serialize messageT :=
  fun msg => [Atom "payload"; Atom (Str (String msg ""))].

Instance Serialize__packetT : Serialize packetT :=
  fun pkt =>
    let 'Packet src dst payload := pkt in
    [Atom "Packet";
     [Atom "source";      Atom src];
     [Atom "destination"; Atom dst];
     to_sexp payload
    ].

Definition eqb_packet (p1 p2 : packetT) : bool :=
  let 'Packet src1 dst1 msg1 := p1 in
  let 'Packet src2 dst2 msg2 := p2 in
  (src1 =? src2) && (dst1 =? dst2) && (msg1 =? msg2)%char.

Variant netE : Type -> Set :=
  Net__Select : netE (list connT)
| Net__Recv   : connT -> netE packetT
| Net__Send   : packetT -> netE unit.

Variant logE : Type -> Set :=
  Log : string -> logE unit.

Definition failureE := exceptE string.

Coercion int_of_nat : nat >-> int.
