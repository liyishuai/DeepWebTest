From DeepWeb Require Import
     Common.

Definition echo : itree netE void :=
  (rec-fix loop _ :=
     conns <- trigger Net__Select;;
     fold_left
       (fun r conn =>
          r;;
          '(Packet src dst msg) <- embed Net__Recv conn;;
          trigger (Net__Send $ Packet dst src msg))
       conns (ret tt) >>= call) tt.
