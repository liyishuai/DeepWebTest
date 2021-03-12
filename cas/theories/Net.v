From IShrink Require Export
     IShrink.
From CAS Require Export
     App.
From ITree Require Export
     Nondeterminism
     ITree.
From Coq Require Export
     List.
Export
  IfNotations.

Variant connT :=
  Conn__Client (c : clientT)
| Conn__Server.

Instance Serialize__connT : Serialize connT :=
  fun c =>
    match c with
    | Conn__Client c => [Atom "Client"; to_sexp c]
    | Conn__Server   =>  Atom "Server"
    end%sexp.

Instance Dec_Eq__connT : Dec_Eq connT.
Proof. dec_eq. Defined.

Arguments packetT : clear implicits.
Notation payloadT := (payloadT requestT responseT).
Notation  packetT := (packetT  requestT responseT connT).
Arguments Packet        {_ _ _ _}.
Arguments packet__src     {_ _ _ _}.
Arguments packet__dst     {_ _ _ _}.
Arguments packet__payload {_ _ _ _}.

Polymorphic Instance Serialize_id {A} {Serialize_A : Serialize A} : Serialize (id A) :=
  Serialize_A.

Instance Serialize__payloadT : Serialize (payloadT id).
Proof.                          (* wat *)
  apply Serialize_sum.
  - apply Serialize__requestT.
  - apply Serialize__responseT.
Defined.

Instance Serialize__packetT : Serialize (packetT id) :=
  fun pkt =>
    let 'Packet s d p := pkt in
    [[Atom "Src"; to_sexp s];
    [Atom "Dst"; to_sexp d];
    [Atom "Msg"; to_sexp p]]%sexp.

Variant switchE : Type -> Type :=
  Switch__In  : switchE (packetT exp)
| Switch__Out : packetT exp -> switchE unit.

Lemma filter_length {A} (f : A -> bool) (l : list A) :
  length (filter f l) <= length l.
Proof.
  induction l; simpl; intuition.
  destruct (f a); simpl; intuition.
Qed.

Program Fixpoint nodup {A} `{Dec_Eq A}
        (l : list A) {measure (length l)} : list A :=
  match l with
  | [] => []
  | a :: l' => a :: nodup (filter (fun b => negb (a = b?)) l')
  end.
Next Obligation.
  apply le_n_S.
  apply filter_length.
Defined.

Fixpoint choose_from_list {E A} `{nondetE -< E} (l : list A)
  : itree E (option A) :=
  match l with
  | []  => ret None
  | [a] => ret (Some a)
  | a :: l' => or (ret (Some a)) (choose_from_list l')
  end.

Definition tcp {E R} `{switchE -< E} `{nondetE -< E} : itree E R :=
  rec
    (fun in_pkt0 =>
       let input :=
           pkt <- trigger Switch__In;;
           call (in_pkt0 ++ [pkt]) in
       let conns : list connT := nodup (map packet__src in_pkt0) in
       out <- choose_from_list conns;;
       match out with
       | None => input
       | Some c =>
         match pick (fun p => packet__src p = c?) in_pkt0 with
         | None => input         (* should not happen *)
         | Some (p, in_pkt1) =>
           embed Switch__Out p;;
           call in_pkt1
         end
       end) ([] : list (packetT exp)).

Variant netE : Type -> Type :=
  Net__In  : server_state exp -> netE (packetT exp)
| Net__Out : packetT exp -> netE unit.

Class Is__nE E `{netE -< E} `{nondetE -< E} `{symE exp -< E}.
Notation nE := (netE +' nondetE +' symE exp).
Instance nE_Is__nE : Is__nE nE. Defined.

Definition packet_from_client {exp_} (p : packetT exp_) : bool :=
  if packet__src p is Conn__Client _ then true else false.

CoFixpoint compose' {E R} `{Is__nE E}
           (bfi bfo : list (packetT exp))
           (net : itree (switchE +' nondetE) R)
           (app : itree smE R) : itree E R :=
  match observe net, observe app with
  | RetF r, _
  | _, RetF r => Ret r
  | TauF net', _ => Tau (compose' bfi bfo net' app)
  | _, TauF app' => Tau (compose' bfi bfo net  app')
  | VisF vn kn, VisF va ka =>
    let step__net st :=
        match vn with
        | (se|) =>
          match se in switchE Y return (Y -> _) -> _ with
          | Switch__In =>
            fun k =>
              match bfo with
              | [] =>
                pkt <- embed Net__In st;;
                Tau (compose' bfi []  (k pkt) app)
              | pkt :: bo' =>
                Tau (compose' bfi bo' (k pkt) app)
              end
          | Switch__Out pkt =>
            fun k =>
              if packet__dst pkt is Conn__Server
              then Tau (compose' (bfi ++ [pkt]) bfo (k tt) app)
              else embed Net__Out pkt;;
                   Tau (compose' bfi bfo (k tt) app)
          end kn
        | (|ne) =>
          match ne in nondetE Y return (Y -> _) -> _ with
          | Or => fun k => b <- trigger Or;;
                       Tau (compose' bfi bfo (k b) app)
          end kn
        end in
    match va with
    | (ae|) =>
      match ae in appE _ Y return (Y -> _) -> _ with
      | App__Recv st =>
        fun k =>
          match pick packet_from_client bfi with
          | None => step__net st
          | Some (Packet s _ p, bi') =>
            match s, p with
            | Conn__Client c, inl r => Tau (compose' bi' bfo net (k (c, r)))
            | _, _ => Tau (compose' bi' bfo net app) (* drop the packet *)
            end
          end
      | App__Send c r =>
        fun k =>
          Tau (compose' bfi (bfo ++ [Packet Conn__Server (Conn__Client c) (inr r)])
                        net (k tt))
      end ka
    | (|se) =>
      match se in symE _ Y return (Y -> _) -> _ with
      | se =>
        fun k => x <- trigger se;;
              Tau (compose' bfi bfo net (k x))
      end ka
    end
  end.

Definition compose_switch {E R} `{Is__nE E} :
  itree (switchE +' nondetE) R -> itree smE R -> itree E R :=
  compose' [] [].
