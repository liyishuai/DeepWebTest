From DeepWeb Require Import
     Common
     Switch.
Import
  SumNotations.
Open Scope list_scope.
Global Open Scope sum_scope.

CoFixpoint compose' {E T} `{Is__nE E}
           (bfi bfo : list packetT)
           (net     : itree nE T)
           (app     : itree netE T) : itree E T :=
  match observe net, observe app with
  | RetF r, _
  | _, RetF r => Ret r
  | TauF net', _ => Tau (compose' bfi bfo net' app)
  | _, TauF app' => Tau (compose' bfi bfo net  app')
  | VisF vn kn, VisF va ka =>
    let step__net :=
        match vn with
        | (e|) =>
          match e in nondetE Y return (Y -> _) -> _ with
          | Or =>
            fun k =>
              b <- trigger Or;;
              Tau (compose' bfi bfo (k b) app)
          end kn
        | (|e|) =>
          match e in logE Y return (Y -> _) -> _ with
          | Log str =>
            fun k =>
              embed Log ("Switch: " ++ str)%string;;
              Tau (compose' bfi bfo (k tt) app)
          end kn
        | (||e) =>
          match e in netE Y return (Y -> _) -> _ with
          | Net__Select =>
            fun k =>
              conns <- trigger Net__Select;;
              Tau (compose' bfi bfo (k (map packet__src bfo ++ conns)) app)
          | Net__Recv c =>
            fun k =>
              if conn_is_app c
              then
                match pick (Nat.eqb c ∘ packet__src) bfo with
                | Some (pkt, bo') =>
                  Tau (compose' bfi bo' (k pkt) app)
                | None            => ITree.spin (* should not happen *)
                end
              else
                pkt <- embed Net__Recv c;;
                Tau (compose' bfi bfo (k pkt) app)
          | Net__Send pkt =>
            fun k =>
              if conn_is_app (packet__dst pkt)
              then Tau (compose' (bfi ++ [pkt]) bfo (k tt) app)
              else
                embed Net__Send pkt;;
                Tau (compose' bfi bfo (k tt) app)
          end kn
        end in
    let step__app :=
        match va in netE Y return (Y -> _) -> _ with
        | Net__Select =>
          fun k =>
            let cs : list connT := map packet__src bfi in
            match cs with
            | [] =>
              (* embed Log ("App selected nothing, step net");; *)
              step__net
            | _ :: _ => Tau (compose' bfi bfo net (k cs))
            end
        | Net__Recv c =>
          fun k =>
            match pick (Nat.eqb c ∘ packet__src) bfi with
            | Some (pkt, bi') =>
              Tau (compose' bi' bfo net (k pkt))
            | None =>
              (* embed Log ("App received nothing, step net");; *)
              step__net
            end
        | Net__Send pkt =>
          fun k => Tau (compose' bfi (bfo ++ [pkt]) net (k tt))
        end ka in
    step__app
  end.

Definition compose_switch {E T} `{Is__nE E}
  : itree nE T -> itree netE T -> itree E T :=
  compose' [] [].
