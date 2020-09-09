From ITree Require Export
     Exception.
From DeepWeb Require Export
     Common.
Export
  SumNotations.
Global Open Scope sum_scope.

Variant observeE : Type -> Set :=
  Observe__Send : connT -> observeE packetT
| Observe__Recv : observeE packetT.

Definition conns : list connT := seq 1 9.

Definition failureE := exceptE string.

Variant logE : Type -> Set :=
  Log : string -> logE unit.

Class Is__oE E `{failureE -< E} `{nondetE -< E}
      `{decideE -< E} `{logE -< E} `{observeE -< E}.
Notation oE := (failureE +' nondetE +' decideE +' logE +' observeE).
Instance oE_Is__oE : Is__oE oE. Defined.

Definition dualize {E R} `{Is__oE E} (e : netE R) : itree E R :=
  match e in netE R return _ R with
  | Net__Select => cs <- fst <$> sublist conns;;
                embed Log ("Selected " ++ to_string cs);;
                ret cs
  | Net__Recv c => pkt <- embed Observe__Send c;;
                ret pkt
  | Net__Send p => p0 <- trigger Observe__Recv;;
                if eqb_packet p p0
                then ret tt
                else throw ("Expect recv " ++ to_string p
                         ++ ", but observed " ++ to_string p0)

  end.

Definition observer {E R} `{Is__oE E} (m : itree (nondetE +' netE) R) : itree E R :=
  interp
    (fun _ e =>
       match e with
       | (e|) =>
         match e in nondetE R return _ R with
         | Or => b <- trigger Decide;;
                ret b
         end
       | (|e) => dualize e
       end) m.
