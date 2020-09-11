From ITree Require Export
     Exception.
From DeepWeb Require Export
     Common
     Switch.
Export
  SumNotations.
Global Open Scope sum_scope.

Variant observeE : Type -> Set :=
  Observe__Send : connT -> observeE packetT
| Observe__Select : observeE (list (connT))
| Observe__Recv : observeE packetT.

Definition failureE := exceptE string.

Class Is__oE E `{failureE -< E} `{nondetE -< E}
      `{decideE -< E} `{logE -< E} `{observeE -< E}.
Notation oE := (failureE +' nondetE +' decideE +' logE +' observeE).
Instance oE_Is__oE : Is__oE oE. Defined.

Definition dualize {E R} `{Is__oE E} (e : netE R) : itree E R :=
  match e in netE R return _ R with
  | Net__Select => cs <- trigger Observe__Select;;
                embed Log ("Selected " ++ to_string cs);;
                ret cs
  | Net__Recv c => pkt <- embed Observe__Send c;;
                (* embed Log ("Sent " ++ to_string pkt);; *)
                ret pkt
  | Net__Send p => p0 <- trigger Observe__Recv;;
                if eqb_packet p p0
                then (* embed Log ("Received " ++ to_string p0);; *)
                     ret tt
                else throw ("Expect recv " ++ to_string p
                         ++ ", but observed " ++ to_string p0)

  end.

Definition observer {E R} `{Is__oE E} (m : itree nE R) : itree E R :=
  interp
    (fun _ e =>
       match e with
       | (e|) =>
         match e in nondetE R return _ R with
         | Or => b <- trigger Decide;;
                ret b
         end
       | (|e|) =>
         match e in logE R return _ R with
         | Log str => embed Log ("Network: " ++ str)
         end
       | (||e) => dualize e
       end) m.
