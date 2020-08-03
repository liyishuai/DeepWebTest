From Ceres Require Import
     Ceres.

Notation connT    := nat.
Notation messageT := sexp.
Record packetT := Packet {
  packet__src     : connT;
  packet__dst     : connT;
  packet__payload : messageT }.

Variant netE : Type -> Set :=
  Net__Select : netE (list connT)
| Net__Recv   : connT -> netE packetT
| Net__Send   : packetT -> netE unit.
