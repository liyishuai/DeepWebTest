From Coq Require Export
     Ascii
     Basics
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
     Nondeterminism
     ITree.
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

Coercion Z.of_nat : connT >-> Z.

Local Open Scope sexp_scope.
Instance Serialize__packetT : Serialize packetT :=
  fun pkt =>
    let 'Packet src dst payload := pkt in
    [Atom "Packet";
     [Atom "source";      Atom src];
     [Atom "destination"; Atom dst];
     [Atom "payload";     Atom (Str (String payload ""))]
    ].

Definition eqb_packet (p1 p2 : packetT) : bool :=
  let 'Packet src1 dst1 msg1 := p1 in
  let 'Packet src2 dst2 msg2 := p2 in
  (src1 =? src2) && (dst1 =? dst2) && (msg1 =? msg2)%char.

Variant netE : Type -> Set :=
  Net__Select : netE (list connT)
| Net__Recv   : connT -> netE packetT
| Net__Send   : packetT -> netE unit.

Variant genE : Type -> Set :=
  Gen : connT -> genE packetT.
