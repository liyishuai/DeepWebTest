From ITree Require Export
     ITree.
From ExtLib Require Export
     Extras
     Functor
     Monad.
From CAS Require Export
     Message.
Export
  FunctorNotation
  FunNotation
  SumNotations
  MonadNotation.
Open Scope sum_scope.
Open Scope monad_scope.

Notation var := nat.

Inductive exp : Type -> Set :=
  Exp__Const : string -> exp string
| Exp__Var   : var    -> exp string
| Exp__Match : tag -> exp tag -> exp bool.

Fixpoint exp_to_sexp {T} (e : exp T) : sexp :=
    match e with
    | Exp__Const s    => [Atom "Constant"; to_sexp s]
    | Exp__Var   v    => [Atom "Variable"; to_sexp v]
    | Exp__Match f fx => [Atom "Matching"; to_sexp f; exp_to_sexp fx]
    end.

Instance Serialize__exp {T} : Serialize (exp T) :=
  exp_to_sexp.

Definition server_state exp_ :=
  list (key * (exp_ tag * exp_ value)).

Definition clientT := nat.

Variant appE {exp_} : Type -> Type :=
  App__Send : clientT -> responseT exp_ -> appE unit
| App__Recv : server_state exp_ -> appE (clientT * requestT).
Arguments appE : clear implicits.

Variant symE {exp_} : Type -> Type :=
  Sym__Fresh  : symE (exp_ string)
| Sym__Decide : exp_ bool -> symE bool.
Arguments symE : clear implicits.

Definition ifx {exp_ E R} `{appE exp_ -< E} `{symE exp_ -< E} (bx : exp_ bool)
           (t f : itree E R) : itree E R :=
  b <- embed Sym__Decide bx;;
  if b : bool then t else f.

Class Is__smE E `{appE exp -< E} `{symE exp -< E}.
Notation smE := (appE exp +' symE exp).
Instance smE_Is__smE : Is__smE smE. Defined.

Definition iter_forever {E A R} (f : A -> itree E A)
  : A -> itree E R :=
  ITree.iter (fun a => inl <$> f a).

Definition cas_smi {E R} `{Is__smE E} : itree E R :=
  iter_forever
    (fun st : server_state exp =>
       let handle k f :=
           match get k st with
           | Some (tx, vx) => f tx vx st
           | None =>
             tx <- trigger Sym__Fresh;;
             vx <- trigger Sym__Fresh;;
             f tx vx (update k (tx, vx) st)
           end in
       '(c, req) <- embed App__Recv st;;
       match req with
       | Request__GET k t =>
         let get_handler tx vx st1 :=
             ifx (Exp__Match t tx)
                 (embed App__Send c Response__NotModified)
                 (embed App__Send c (Response__OK tx vx));;
             ret st1 in
         handle k get_handler
       | Request__CAS k t v =>
         let cas_handler tx _ st1 :=
             ifx (Exp__Match t tx)
                 (embed App__Send c Response__NoContent;;
                  tx1 <- trigger Sym__Fresh;;
                  ret (update k (tx1, Exp__Const v) st1))
                 (embed App__Send c Response__PreconditionFailed;;
                  ret st1) in
         handle k cas_handler
       end) [].
