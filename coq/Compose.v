From DeepWeb Require Import
     Common.
Import
  SumNotations.
Open Scope list_scope.
Global Open Scope sum_scope.

Fixpoint pick {A} (f : A -> bool) (l : list A) : option (A * list A) :=
  match l with
  | [] => None
  | a :: tl =>
    if f a
    then Some (a, tl)
    else match pick f tl with
         | Some (x, l') => Some (x, a :: l')
         | None => None
         end
  end.

Definition reset_block (pkt : packetT) (blk : option connT) : option connT :=
  match blk with
  | Some c => if packet__dst pkt =? c then None else Some c
  | None    => None
  end.

CoFixpoint compose' {E T} `{nondetE -< E} `{netE -< E}
           (blk     : option connT)
           (bfi bfo : list packetT)
           (net     : itree (nondetE +' netE) T)
           (app     : itree netE T) : itree E T :=
  match observe net, observe app with
  | RetF r, _
  | _, RetF r => Ret r
  | TauF net', _ => Tau (compose' blk bfi bfo net' app)
  | _, TauF app' => Tau (compose' blk bfi bfo net  app')
  | VisF vn kn, VisF va ka =>
    let step__app :=
        match blk with
        | Some _ => ITree.spin   (* should not happen *)
        | None =>
          match va in netE Y return (Y -> _) -> _ with
          | Net__Select =>
            fun k => Tau (compose' blk bfi bfo net (k (map packet__src bfi)))
          | Net__Recv c =>
            fun k =>
              match pick (Nat.eqb c ∘ packet__src) bfi with
              | Some (pkt, bi') => Tau (compose' None bi' bfo net (k pkt))
              | None            => Tau (compose' (Some c) bfi bfo net app)
              end
          | Net__Send pkt =>
            fun k => Tau (compose' None bfi (pkt :: bfo) net (k tt))
          end ka
        end in
    let step__net :=
        match vn with
        | (e|) =>
          match e in nondetE Y return (Y -> _) -> _ with
          | Or =>
            fun k =>
              b <- trigger Or;;
              Tau (compose' blk bfi bfo (k b) app)
          end kn
        | (|e) =>
          match e in netE Y return (Y -> _) -> _ with
          | Net__Select =>
            fun k =>
              conns <- trigger Net__Select;;
              Tau (compose' blk bfi bfo (k (map packet__src bfo ++ conns)) app)
          | Net__Recv c =>
            fun k =>
              if conn_is_app c
              then
                match pick (Nat.eqb c ∘ packet__src) bfo with
                | Some (pkt, bo') => Tau (compose' blk bfi bo' (k pkt) app)
                | None            => ITree.spin (* should not happen *)
                end
              else
                pkt <- embed Net__Recv c;;
                Tau (compose' blk bfi bfo (k pkt) app)
          | Net__Send pkt =>
            fun k =>
              if conn_is_app (packet__dst pkt)
              then Tau (compose' (reset_block pkt blk) (pkt :: bfi) bfo (k tt) app)
              else
                embed Net__Send pkt;;
                Tau (compose' blk bfi bfo (k tt) app)
          end kn
        end in
    match blk with
    | Some _ =>    step__net
    | None   => or step__net step__app
    end
  end.

Definition compose_switch {E T} `{nondetE -< E} `{netE -< E}
  : itree (nondetE +' netE) T -> itree netE T -> itree E T :=
  compose' None [] [].
