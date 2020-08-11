From DeepWeb Require Import
     Common.

Definition udp {E} `{nondetE -< E} `{netE -< E} : itree E void :=
  (rec-fix loop in_pkt0 :=
     conns <- trigger Net__Select;;
     in_pkt1 <- fold_left
               (fun in_pkt conn =>
                  pkt <- embed Net__Recv conn;;
                  cons pkt <$> in_pkt)
               conns (ret in_pkt0);;
     '(in_pkt2, out_pkt2) <- sublist in_pkt1;;
     fold_left (fun _ pkt => trigger (Net__Send pkt)) out_pkt2 (ret tt);;
     call in_pkt2) [].

Definition tcp {E} `{nondetE -< E} `{netE -< E} : itree E void :=
  (rec-fix loop in_pkt0 :=      (* Head of every list came latest. *)
     conns <- trigger Net__Select;;
     in_pkt1 <- fold_left
               (fun in_pkt conn =>
                  pkt <- embed Net__Recv conn;;
                  cons pkt <$> in_pkt)
               conns (ret in_pkt0);;
     '(in_pkt2, out_pkt2, _) <-
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
         (ret ([], [], const true)) in_pkt1;;
     fold_right (fun pkt _ => trigger (Net__Send pkt)) (ret tt) out_pkt2;;
     call in_pkt2) [].
