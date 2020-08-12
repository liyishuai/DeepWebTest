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

Definition conns : list connT := seq 1 10.

Definition failureE := exceptE string.

Definition dualize {E R} `{failureE -< E} `{nondetE -< E} `{observeE -< E}
           (e : netE R) : itree E R :=
  match e in netE R return _ R with
  | Net__Select => fst <$> sublist conns
  | Net__Recv c => embed Observe__Send c
  | Net__Send p => p0 <- trigger Observe__Recv;;
                if eqb_packet p p0
                then ret tt
                else throw "Unexpected packet"
  end.

Definition observer {E R} `{failureE -< E} `{nondetE -< E} `{decideE -< E} `{observeE -< E}
           (m : itree (nondetE +' netE) R) : itree E R :=
  interp
    (fun _ e =>
       match e with
       | (e|) =>
         match e in nondetE R return _ R with
         | Or => trigger Or
         end
       | (|e) => dualize e
       end) m.
