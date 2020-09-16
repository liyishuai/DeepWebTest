From DeepWeb Require Export
     Common.

Variant switchE : Type -> Set :=
  Switch__In  : switchE packetT
| Switch__Out : packetT -> switchE unit.

Class Is__sE E `{nondetE -< E} `{logE -< E} `{switchE -< E}.
Notation sE := (nondetE +' logE +' switchE).
Instance sE_Is__sE : Is__sE sE. Defined.

Definition tcp {E T} `{Is__sE E} : itree E T :=
  (rec-fix loop in_pkt0 :=
     let input :=
         pkt <- trigger Switch__In;;
         call (pkt :: in_pkt0) in
     let output :=
         '(in_pkt1, out_pkt1, _) <-
           fold_right
             (fun pkt i_o_f =>
                '(in_pkt, out_pkt, f) <- i_o_f;;
                if f pkt : bool
                then
                  or (ret (pkt :: in_pkt, out_pkt,
                           fun pkt' =>
                             if (packet__src pkt' =? packet__src pkt) &&
                                (packet__dst pkt' =? packet__dst pkt)
                             then false
                             else f pkt'))
                     (ret (in_pkt, pkt :: out_pkt, f))
                else ret (pkt :: in_pkt, out_pkt, f))
             (ret ([], [], const true)) in_pkt0;;
         match out_pkt1 with
         | _ :: _ =>
           fold_right (fun pkt r => r;;
                                  embed Switch__Out pkt) (ret tt) out_pkt1;;
           call in_pkt1
         | [] =>
           match rev' in_pkt1 with
           | [] => input
           | pkt :: in_pkt2 =>
             embed Switch__Out pkt;;
             call in_pkt2
           end
         end in
     match in_pkt0 with
     | []    => input
     | _ :: _ => or input output
     end) [].
