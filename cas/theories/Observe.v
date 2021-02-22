From ITree Require Export
     Exception.
From CAS Require Export
     Net.
Open Scope string_scope.

Variant observeE : Type -> Type :=
  Observe__ToServer   : server_state exp -> observeE (packetT id)
| Observe__FromServer : observeE (packetT id).

Variant decideE : Type -> Set :=
  Decide : decideE bool.

Variant unifyE : Type -> Type :=
  Unify__Fresh    : unifyE (exp string)
| Unify__Match    : exp bool -> bool -> unifyE unit
| Unify__Response : responseT exp -> responseT id -> unifyE unit.

Notation failureE := (exceptE string).

Class Is__oE E `{failureE -< E}
      `{decideE -< E} `{unifyE -< E} `{observeE -< E}.
Notation oE := (failureE +' decideE +' unifyE +' observeE).
Instance oE_Is__oE : Is__oE oE. Defined.

Definition wrap_response (r : responseT id) : responseT exp :=
  match r with
  | Response__NotModified        => Response__NotModified
  | Response__OK t v             => Response__OK (Exp__Const t) (Exp__Const v)
  | Response__NoContent          => Response__NoContent
  | Response__PreconditionFailed => Response__PreconditionFailed
  end.

Definition wrap_payload : payloadT id -> payloadT exp :=
  fmap wrap_response.

Definition wrap_packet (pkt : packetT id) : packetT exp :=
  let 'Packet s d p := pkt in
  Packet s d (wrap_payload p).

Definition dualize {E R} `{Is__oE E} (e : netE R) : itree E R :=
  match e in netE R return _ R with
  | Net__In st => wrap_packet <$> embed Observe__ToServer st
  | Net__Out (Packet s0 d0 p0) =>
    '(Packet s d p) <- trigger Observe__FromServer;;
    if (s, d) = (s0, d0)?
    then
      match p0, p with
      | inl r0, inl r =>
        if r = r0? then ret tt
        else throw $ "Expect request " ++ to_string r0
                  ++ ", but observed " ++ to_string r
      | inr r0, inr r => embed Unify__Response r0 r
      | inl _ , inr _ => throw "Expect request but observed response"
      | inr _ , inl _ => throw "Expect response but observed request"
      end
    else throw $ "Expect route " ++ to_string (s0, d0)
            ++ ", but observed " ++ to_string (s, d)
  end.

Definition observer {E R} `{Is__oE E} (m : itree nE R) : itree E R :=
  interp
    (fun _ e =>
       match e with
       | (ae|) => dualize ae
       | (|ne|) =>
         match ne in nondetE R return _ R with
         | Or => trigger Decide
         end
       | (||se) =>
         match se in symE _ R return _ R with
         | Sym__Fresh    => trigger Unify__Fresh
         | Sym__Decide x => b <- trigger Decide;;
                         embed Unify__Match x b;;
                         ret b
         end
       end) m.
