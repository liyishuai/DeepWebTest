From DeepWeb Require Export
     Switch2.

Variant observeE : Type -> Set :=
  Observe__Send : observeE packetT
| Observe__Recv : observeE packetT.

Class Is__oE E `{failureE -< E} `{nondetE -< E}
      `{decideE -< E} `{logE -< E} `{observeE -< E}.
Notation oE := (failureE +' nondetE +' decideE +' logE +' observeE).
Instance oE_Is__oE : Is__oE oE. Defined.

Definition dualize {E R} `{Is__oE E} (e : switchE R) : itree E R :=
  match e in switchE R return _ R with
  | Switch__In      => trigger Observe__Send
  | Switch__Out p =>
    p0 <- trigger Observe__Recv;;
    if eqb_packet p p0
    then ret tt
    else throw ("Expect " ++ to_string p ++ ", but received " ++ to_string p0)
  end.

Definition observer {E R} `{Is__oE E} (m : itree sE R) : itree E R :=
  interp
    (fun _ e =>
       match e with
       | (ne|) =>
         match ne in nondetE R return _ R with
         | Or => trigger Decide
         end
       | (|le|) =>
         match le in logE R return _ R with
         | Log str => embed Log ("Network: " ++ str)
         end
       | (||e) => dualize e
       end) m.
