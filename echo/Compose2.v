From DeepWeb Require Import
     Switch2.
Export
  SumNotations.
Open Scope sum_scope.

CoFixpoint compose' {E T} `{Is__sE E}
           (bfi bfo : list packetT)
           (net : itree sE T)
           (app : itree netE T) : itree E T :=
  match observe net, observe app with
  | RetF r, _
  | _, RetF r => Ret r
  | TauF net', _ => Tau (compose' bfi bfo net' app)
  | _, TauF app' => Tau (compose' bfi bfo net  app')
  | VisF vn kn, VisF va ka =>
    let step__net :=
        match vn with
        | (ne|) =>
          match ne in nondetE Y return (Y -> _) -> _ with
          | Or =>
            fun k =>
              b <- trigger Or;;
              Tau (compose' bfi bfo (k b) app)
          end kn
        | (|le|) =>
          match le in logE Y return (Y -> _) -> _ with
          | Log str =>
            fun k =>
              embed Log ("Switch: " ++ str)%string;;
              Tau (compose' bfi bfo (k tt) app)
          end kn
        | (||se) =>
          match se in switchE Y return (Y -> _) -> _ with
          | Switch__In =>
            fun k =>
              match bfo with
              | [] =>
                pkt <- trigger Switch__In;;
                Tau (compose' bfi [] (k pkt) app)
              | pkt :: bo' =>
                Tau (compose' bfi bo' (k pkt) app)
              end
          | Switch__Out pkt =>
            fun k =>
              if conn_is_app (packet__dst pkt)
              then Tau (compose' (bfi ++ [pkt]) bfo (k tt) app)
              else
                embed Switch__Out pkt;;
                Tau (compose' bfi bfo (k tt) app)
          end kn
        end in
    let step__app :=
        match va in netE Y return (Y -> _) -> _ with
        | Net__Select =>
          fun k =>
            let cs : list connT := map packet__src bfi in
            match cs with
            | [] => step__net
            | _ :: _ => Tau (compose' bfi bfo net (k cs))
            end
        | Net__Recv c =>
          fun k =>
            match pick (Nat.eqb c ∘ packet__src) bfi with
            | Some (pkt, bi') =>
              Tau (compose' bi' bfo net (k pkt))
            | None =>
              step__net
            end
        | Net__Send pkt =>
          fun k => Tau (compose' bfi (bfo ++ [pkt]) net (k tt))
        end ka in
    step__app
  end.

Definition compose_switch {E T} `{Is__sE E}
  : itree sE T -> itree netE T -> itree E T := compose' [] [].
