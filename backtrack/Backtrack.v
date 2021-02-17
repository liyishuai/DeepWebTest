From Coq Require Export
     Basics
     List
     String.
From Ceres Require Export
     Ceres.
From ExtLib Require Export
     Extras
     Monad.
From ITree Require Export
     Exception
     Nondeterminism
     ITree.
Export
  FunNotation
  ListNotations
  MonadNotation
  SumNotations.
Open Scope program_scope.
Open Scope sum_scope.

Variant observeE : Type -> Set :=
  Observe__Send : observeE nat
| Observe__Recv : observeE nat.

Instance Serialize__observeE {R} : Serialize (observeE R) :=
  fun oe =>
    match oe with
    | Observe__Send => Atom "OSend"
    | Observe__Recv => Atom "ORecv"
    end.

Definition failureE := exceptE string.

Class Is__oE E `{failureE -< E} `{nondetE -< E} `{observeE -< E}.
Notation oE := (failureE +' nondetE +' observeE).
Instance oE_Is__oE : Is__oE oE. Defined.

CoFixpoint match_event {T R} `{Serialize R} (e1 : observeE R) (r : R)
           (m : itree oE T) : itree oE T :=
  match observe m with
  | RetF x  => Ret x
  | TauF m' => Tau (match_event e1 r m')
  | VisF e k =>
    match e with
    | (||e0) =>
      match e0 in observeE Y, e1 in observeE R return (Y -> _) -> R -> _ with
      | Observe__Send, Observe__Send
      | Observe__Recv, Observe__Recv => id
      | _, _ => fun _ _ => throw $ "Expect " ++ to_string e0
                             ++ ", but observed " ++ to_string e1
                             ++ " returning " ++ to_string r
      end k r
    | _ => Vis e (match_event e1 r ∘ k)
    end
  end.

Definition match_observe {T R} `{Serialize T} (e : observeE T) (r : T)
  : list (itree oE R) -> list (itree oE R) := map (match_event e r).

Variant testerE : Type -> Set :=
  Tester__Send : testerE (option nat)
| Tester__Recv : testerE (option nat).

Class Is__tE E `{failureE -< E} `{testerE -< E}.
Notation tE := (failureE +' testerE).
Instance tE_Is__tE : Is__tE tE. Defined.

CoFixpoint backtrack' {E R} `{Is__tE E} (others : list (itree oE R))
           (m : itree oE R) : itree E R :=
  match observe m with
  | RetF r => Ret r
  | TauF m' => Tau (backtrack' others m')
  | VisF e k =>
    let catch (err : string) : itree E R :=
        match others with
        | [] => throw err
        | other :: others' =>
          Tau (backtrack' others' other)
        end in
    match e with
    | (Throw err|) => catch err
    | (|ne|) =>
      match ne in nondetE Y return (Y -> _) -> _ with
      | Or => fun k => Tau (backtrack' (k false::others) (k true))
      end k
    | (||oe) =>
      let postpone : itree E R :=
          match others with
          | []              => Tau (backtrack' []               m)
          | other :: others' => Tau (backtrack' (others' ++ [m]) other)
          end in
      match oe in observeE Y return (Y -> _) -> _ with
      | Observe__Send =>
        fun k =>
          on <- trigger Tester__Send;;
          match on with
          | Some n =>
            Tau (backtrack' (match_observe Observe__Send n others) (k n))
          | None => postpone
          end
      | Observe__Recv =>
        fun k =>
          on <- trigger Tester__Recv;;
          match on with
          | Some n =>
            Tau (backtrack' (match_observe Observe__Recv n others) (k n))
          | None => postpone
          end
      end k
    end
  end.

Definition backtrack {E R} `{Is__tE E} : itree oE R -> itree E R := backtrack' [].
