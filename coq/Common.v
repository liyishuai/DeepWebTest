From Coq Require Export
     List
     Nat.
From ExtLib Require Export
     Monad.
From Ceres Require Import
     Ceres.
From ITree Require Export
     Nondeterminism
     ITree.
Export
  ListNotations
  MonadNotation.
Global Open Scope bool_scope.
Global Open Scope monad_scope.

Definition sublist {E A} `{nondetE -< E} : list A -> itree E (list A * list A) :=
  fold_right
    (fun a lr =>
       '(l, r) <- lr;;
       or (ret (a :: l, r))
          (ret (l, a :: r))) (ret ([], [])).

Variant decideE : Type -> Set :=
  Decide : decideE bool.

Notation connT    := nat.
Notation messageT := sexp.
Record packetT := Packet {
  packet__src     : connT;
  packet__dst     : connT;
  packet__payload : messageT }.

Definition eqb_packet (p1 p2 : packetT) : bool :=
  let 'Packet src1 dst1 msg1 := p1 in
  let 'Packet src2 dst2 msg2 := p2 in
  (src1 =? src2) && (dst1 =? dst2) && eqb_sexp msg1 msg2.

Variant netE : Type -> Set :=
  Net__Select : netE (list connT)
| Net__Recv   : connT -> netE packetT
| Net__Send   : packetT -> netE unit.

Variant genE : Type -> Set :=
  Gen : genE packetT.
