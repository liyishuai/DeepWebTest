From DeepWeb Require Import
     Observe.

Notation tE := (failureE +' nondetE +' decideE +' observeE).

Definition match_event {T R} (e : observeE R) (r : R) (m : itree tE T)
  : option (itree tE T).
Admitted.

Definition pickSome {T} : list (option T) -> list T :=
  fold_right
    (fun oh =>
       match oh with
       | Some h => cons h
       | None   => id
       end) [].

Definition match_observe {T R} (e : observeE T) (r : T) (l : list (itree tE R))
  : list (itree tE R) := pickSome (map (match_event e r) l).

CoFixpoint tester' {E R} `{genE -< E} `{nondetE -< E} `{failureE -< E}
           `{netE -< E} (others : list (itree tE R)) (m : itree tE R)
  : itree E R :=
  match observe m with
  | RetF r  => ret r
  | TauF m' => Tau (tester' others m')
  | VisF e k =>
    let catch (err : string) : itree E R :=
      match others with
      | [] => throw err
      | other :: others' => Tau (tester' others' other)
      end in
    match e with
    | (Throw err|) => catch err
    | (|ne|) =>
      match ne in nondetE Y return (Y -> _) -> _ with
      | Or => fun k => b <- trigger Or;; Tau (tester' others (k b))
      end k
    | (||de|) =>
      match de in decideE Y return (Y -> _) -> _ with
      | Decide => fun k => Tau (tester' (k false :: others) (k true))
      end k
    | (|||oe) =>
      match oe in observeE Y return (Y -> _) -> _ with
      | Observe__Send c =>
        fun k =>
          pkt <- trigger Gen;;
          embed Net__Send pkt;;
          Tau (tester' (match_observe (Observe__Send c) pkt others) (k pkt))
      | Observe__Recv =>
        fun k =>
          conns <- trigger Net__Select;;
          match conns with
          | [] => catch "Not ready to receive"
          | c :: _ =>
            pkt <- embed Net__Recv c;;
            Tau (tester' (match_observe Observe__Recv pkt others) (k pkt))
          end
      end k
    end
  end.
