From DeepWeb Require Import
     Common.

Variant logE : Type -> Set :=
  Log : string -> logE unit.

Class Is__nE E `{nondetE -< E} `{logE -< E} `{netE -< E}.
Notation nE := (nondetE +' logE +' netE).
Instance nE_Is__nE : Is__nE nE. Defined.

Definition udp {E} `{Is__nE E} : itree E void :=
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

Definition tcp {E} `{Is__nE E} : itree E void :=
  (rec-fix loop in_pkt0 :=
     conns <- trigger Net__Select;;
     in_pkt1 <- fold_left
                  (fun in_pkt conn =>
                     pkts <- in_pkt;;
                     pkt <- embed Net__Recv conn;;
                     (* embed Log ("Received " ++ to_string pkt);; *)
                     ret (pkt :: pkts))
                  conns (ret in_pkt0);;
     (* embed Log ("Pending: " ++ to_string in_pkt1);; *)
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
     (* embed Log ("Ready: " ++ to_string out_pkt2);; *)
     fold_right (fun pkt r => r;;
                           (* embed Log ("Send " ++ to_string pkt);; *)
                           embed Net__Send pkt) (ret tt) out_pkt2;;
     (* embed Log ("Delayed: " ++ to_string in_pkt2);; *)
     call in_pkt2) [].
