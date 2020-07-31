From Coq Require Import
     List.
From ExtLib Require Import
     Extras
     Functor
     Monad.
From ITree Require Import
     Nondeterminism
     ITree.
From DeepWeb Require Import
     Net.
Import
  FunctorNotation
  ListNotations
  MonadNotation.
Open Scope monad_scope.

Definition switch {E} `{nondetE -< E} `{netE -< E} : itree E void :=
  (rec-fix loop in_pkt0 :=
     conns <- trigger Net__Select;;
     in_pkt1 <- fold_left
               (fun in_pkt conn =>
                  msg <- embed Net__Recv conn;;
                  (cons (conn, msg)) <$> in_pkt)
               conns (ret in_pkt0);;
     '(in_pkt2, out_pkt2) <- fold_left
                               (fun i_o pkt =>
                                  '(in_pkt, out_pkt) <- i_o;;
                                  or (ret (pkt :: in_pkt, out_pkt))
                                     (ret (in_pkt, pkt :: out_pkt)))
                               in_pkt1 (ret ([], []));;
     fold_left (fun _ pkt => trigger (uncurry Net__Send pkt)) out_pkt2 (ret tt);;
     call in_pkt2) [].
