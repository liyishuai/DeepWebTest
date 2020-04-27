From Coq Require Export
     Basics
     List
     NArith.
From ExtLib Require Export
     Functor
     ListMonad
     OptionMonad.
Export
  FunctorNotation
  ListNotations.
Open Scope program_scope.
Open Scope N_scope.

Definition var := N.

Inductive exp : Type -> Set :=
  exp_var   : var -> exp N
| exp_int   : N   -> exp N
| exp_true  : exp bool
| exp_false : exp bool
| exp_negb  : exp bool -> exp bool
| exp_eq    : N   -> exp N -> exp bool.

Definition exp_state := list (var * (N + list N)).

Definition fresh_var (vs : list var) : var :=
  1 + fold_left N.max vs 0.

Definition fresh (s : exp_state) : exp_state * exp N :=
  let x := fresh_var (fst <$> s) in
  ((x, inr []) :: s, exp_var x).

Definition get {A} (k : N) : list (N * A) -> option A :=
  fmap snd ∘ find (N.eqb k ∘ fst).

Definition assert (x : var) (n : N) (s : exp_state) : option exp_state :=
  match get x s with
  | Some (inl n') => if n' =? n then Some s else None
  | Some (inr l)  => if existsb (N.eqb n) l then None else (Some ((x, inl n) :: s))
  | None          => Some ((x, inl n) :: s)
  end.

Definition assert_not (x : var) (n : N) (s : exp_state) : option exp_state :=
  match get x s with
  | Some (inl n') => if n' =? n then None else Some s
  | Some (inr l)  => Some ((x, inr (n :: l)) :: s)
  | None          => Some ((x, inr [n]) :: s)
  end.

Fixpoint unify {T} (e : exp T) (v : T) (s : exp_state) : option exp_state :=
  match e in exp U return U -> option exp_state with
  | exp_eq n (exp_var x)  => fun b => if b then assert x n s else assert_not x n s
  | exp_eq n (exp_int n') => fun b => if bool_eq b (n' =? n) then Some s else None
  | exp_var x   => fun n => assert x n s
  | exp_int n'  => fun n => if n' =? n then Some s else None
  | exp_true    => fun b => if b then Some s else None
  | exp_false   => fun b => if b then None else Some s
  | exp_negb e' => fun b => unify e' (negb b) s
  | exp_eq _ _ => const None
  end v.
