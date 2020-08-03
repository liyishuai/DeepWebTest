From Coq Require Import
     List.
From ExtLib Require Import
     Extras
     Monad.
From ITree Require Import
     ITree.
From DeepWeb Require Import
     Net.
Import
  FunNotation
  ListNotations
  MonadNotation.
Open Scope monad_scope.

Definition echo : itree netE void :=
  (rec-fix loop _ :=
     conns <- trigger Net__Select;;
     fold_left
       (fun _ conn =>
          '(Packet src dst msg) <- embed Net__Recv conn;;
          trigger (Net__Send $ Packet dst src msg))
       conns (ret tt) >>= call) tt.
