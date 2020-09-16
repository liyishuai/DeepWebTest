From DeepWeb Require Export
     Observe2.

CoFixpoint match_event {T R} (e0 : observeE R) (r : R) (m : itree oE T)
  : itree oE T :=
  match observe m with
  | RetF x   => ret x
  | TauF m'  => Tau (match_event e0 r m')
  | VisF e k =>
    match e with
    | (||||oe) =>
      match oe in observeE Y, e0 in observeE R return (Y -> _) -> R -> _ with
      | Observe__Send, Observe__Send
      | Observe__Recv, Observe__Recv => id
      | _, _ => fun _ _ => throw "Unexpected event"
      end k r
    | _ => vis e (match_event e0 r ∘ k)
    end
  end.

Definition match_observe {T R} (e : observeE T) (r : T)
           : list (itree oE R) -> list (itree oE R) := map (match_event e r).

Variant genE : Type -> Set :=
  Gen : genE packetT.

Class Is__tE E `{genE -< E} `{nondetE -< E}
      `{failureE -< E} `{logE -< E} `{netE -< E}.
Notation tE := (genE +' nondetE +' failureE +' logE +' netE).
Instance tE_Is__tE : Is__tE tE. Defined.

CoFixpoint tester' {E R} `{Is__tE E} (others : list (itree oE R)) (m : itree oE R)
  : itree E R :=
  match observe m with
  | RetF r   => Ret r
  | TauF m'  => Tau (tester' others m')
  | VisF e k =>
    let catch (err : string) : itree E R :=
        embed Log ("Catch " ++ err ++ " with " ++ to_string (List.length others)
                            ++ " other branches ");;
        match others with
        | [] => throw err
        | other :: others' =>
          Tau (tester' others' other)
        end in
    match e with
    | (Throw err|) => catch err
    | (|ne|) =>
      match ne in nondetE Y return (Y -> _) -> _ with
      | Or =>
        fun k =>
          b <- trigger Or;;
          Tau (tester' others (k b))
      end k
    | (||de|) =>
      match de in decideE Y return (Y -> _) -> _ with
      | Decide =>
        fun k =>
          b <- trigger Or;;
          Tau (tester' (others ++ [k (negb b)]) (k b))
      end k
    | (|||le|) =>
      match le in logE Y return (Y -> _) -> _ with
      | Log str =>
        fun k =>
          embed Log ("Observer: " ++ str);;
          Tau (tester' others (k tt))
      end k
    | (||||oe) =>
      match oe in observeE Y return (Y -> _) -> _ with
      | Observe__Send =>
        fun k =>
          pkt <- trigger Gen;;
          embed Net__Send pkt;;
          Tau (tester' (match_observe Observe__Send pkt others) (k pkt))
      | Observe__Recv =>
        fun k =>
          conns <- trigger Net__Select;;
          match conns with
          | [] =>
            match others with
            | [] => Tau (tester' [] m)
            | other :: others' =>
              Tau (tester' (others' ++ [m]) other)
            end
          | c :: _ =>
            pkt <- embed Net__Recv c;;
            Tau (tester' (match_observe Observe__Recv pkt others) (k pkt))
          end
      end k
    end
  end.

Definition tester {E R} `{Is__tE E} : itree oE R -> itree E R := tester' [].
