From CAS Require Export
     App.
From ExtLib Require Export
     OptionMonad.

Variant texp : Type -> Set :=
  Texp__Random :    texp tag
| Texp__Var : var -> texp tag.

Instance Serialize__texp : Serialize (texp tag) :=
  fun tx => match tx with
         | Texp__Random => Atom "Random"
         | Texp__Var x => [Atom "Step"; to_sexp x]%sexp
         end.

Instance Serialize__reqtexp : Serialize (requestT texp) :=
  fun m =>
    match m with
    | Request__GET k t =>
      [Atom "GET"; to_sexp k; to_sexp t]
    | Request__CAS k t v =>
      [Atom "CAS"; to_sexp k; to_sexp t; to_sexp v]
    end%sexp.

Definition stepT : Set := var * requestT texp.
Definition logT : Set := stepT * clientT * option (responseT id).
Definition scriptT := list stepT.
Definition traceT := list logT.

Definition script_of_trace : traceT -> scriptT := map (fst ∘ fst).

Fixpoint shrink_list {A} (l : list A) : list (list A) :=
  match l with
  | [] => []
  | a :: l' => let sl' := shrink_list l' in
             l' :: cons a <$> sl'
  end.

Fixpoint repeat_list {A} (n : nat) (l : list A) : list A :=
  match n with
  | O => []
  | S n' => l ++ repeat_list n' l
  end.

Definition shrink_execute' (exec : scriptT -> IO (bool * traceT))
           (init : scriptT) : IO (option scriptT) :=
  prerr_endline "<<<<< initial script >>>>>";;
  prerr_endline (to_string init);;
  IO.fix_io
    (fun shrink_rec ss =>
       match ss with
       | [] => prerr_endline "<<<<< shrink exhausted >>>>";; ret None
       | sc :: ss' =>
         '(b, tr) <- exec sc;;
         if b : bool
         then prerr_endline "<<<<< accepting trace >>>>>";;
              prerr_endline (to_string tr);;
              shrink_rec ss'
         else prerr_endline "<<<<< rejecting trace >>>>>";;
              prerr_endline (to_string tr);;
              prerr_endline "<<<<< shrink ended >>>>>>>>";;
              ret (Some $ script_of_trace tr)
       end) (repeat_list 20 $ shrink_list init).

Definition shrink_execute (first_exec : IO (bool * traceT))
           (then_exec : scriptT -> IO (bool * traceT)) : IO bool :=
  '(b, tr) <- first_exec;;
  if b : bool
  then ret true
  else IO.while_loop (shrink_execute' then_exec) (script_of_trace tr);;
       ret false.
