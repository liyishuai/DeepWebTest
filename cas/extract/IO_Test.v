From SimpleIO Require Export
     SimpleIO.
From Ceres Require Export
     Ceres.
From ExtLib Require Export
     Monad.
From Coq Require Export
     String.
Export
  MonadNotation.
Open Scope monad_scope.
Open Scope string_scope.

Fixpoint multi_test' (fuel : nat) (t : IO bool) : IO bool :=
  match fuel with
  | O => ret true
  | S fuel =>
    b <- t;;
    if b : bool
    then prerr_endline (to_string fuel);;
         multi_test' fuel t
    else ret false
  end.

Definition multi_test (t : IO bool) : IO unit :=
  b <- multi_test' 5000 t;;
  if b : bool
  then prerr_endline "Success"
  else prerr_endline "Failure".
