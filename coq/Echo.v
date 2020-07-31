From Coq Require Import
     List.
From ExtLib Require Import
     Monad.
From ITree Require Import
     ITree.
From DeepWeb Require Import
     Net.
Import
  ListNotations
  MonadNotation.
Open Scope monad_scope.

Definition echo : itree netE void :=
  (rec-fix loop _ :=
     conns <- trigger Net__Select;;
     fold_left
       (fun _ conn =>
          req <- embed Net__Recv conn;;
          trigger (Net__Send conn req))
       conns (ret tt) >>= call) tt.
