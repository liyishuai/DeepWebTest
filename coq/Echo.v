From ExtLib Require Import
     Extras.
From DeepWeb Require Import
     Common.
Import
  FunNotation.

Definition echo : itree netE void :=
  (rec-fix loop _ :=
     conns <- trigger Net__Select;;
     fold_left
       (fun _ conn =>
          '(Packet src dst msg) <- embed Net__Recv conn;;
          trigger (Net__Send $ Packet dst src msg))
       conns (ret tt) >>= call) tt.
