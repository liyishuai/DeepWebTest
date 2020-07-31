From Ceres Require Import
     Ceres.

Notation connT    := nat.
Notation messageT := sexp.

Variant netE : Type -> Set :=
  Net__Select : netE (list connT)
| Net__Recv   : connT -> netE messageT
| Net__Send   : connT -> messageT -> netE unit.
