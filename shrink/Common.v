From Coq Require Export
     List.
Export ListNotations.

Fixpoint repeat_list {A} (n : nat) (l : list A) : list A :=
  match n with
  | O    => []
  | S n' => l ++ repeat_list n' l
  end.
