From IShrink Require Export
     Common.
From QuickChick Require Export
     QuickChick.
From SimpleIO Require Export
     SimpleIO.
From ITree Require Export
     Exception
     Nondeterminism
     ITree.
From Ceres Require Export
     Ceres.
From ExtLib Require Export
     Extras
     ExtLib.
From Coq Require Export
     Basics.
Export
  FunNotation
  IfNotations
  MonadNotation
  SumNotations.
Open Scope sum_scope.
Open Scope string_scope.
Open Scope list_scope.

Section IShrink.

Variable expT               : Type -> Type.
Variable requestT responseT : (Set -> Type) -> Type.
Context `{Shrink (requestT expT)}.
Context `{Serialize (requestT expT)} `{Serialize (responseT id)}.

Definition payloadT exp_ : Type := requestT id + responseT exp_.

Variable connT      : Type.
Variable Conn__Server : connT.
Context `{Serialize connT}.

Record packetT {exp_} :=
  Packet {
      packet__src : connT;
      packet__dst : connT;
      packet__payload : payloadT exp_
    }.
Arguments packetT : clear implicits.
Arguments Packet {_}.

Definition varT := nat.

Definition stepT : Type := varT * requestT expT.
Definition logT  : Type := connT * stepT * option (responseT id).

Definition scriptT := list stepT.
Definition traceT  := list logT.

Definition shrink_execute' (exec : scriptT -> IO (bool * traceT))
           (init : scriptT) : IO (option scriptT) :=
  prerr_endline "<<<<< initial script >>>>>";;
  prerr_endline (to_string init);;
  IO.fix_io
    (fun shrink_rec ss =>
       match ss with
       | [] => prerr_endline "<<<<< shrink exhausted >>>>";; ret None
       | sc :: ss' =>
         '(b, tr) <- exec sc;;
         if b : bool
         then prerr_endline "<<<<< accepting trace >>>>>";;
              prerr_endline (to_string tr);;
              shrink_rec ss'
         else prerr_endline "<<<<< rejecting trace >>>>>";;
              prerr_endline (to_string tr);;
              prerr_endline "<<<<< shrink ended >>>>>>>>";;
              ret (Some sc)
       end) (repeat_list 20 $ shrink init).

Definition shrink_execute (first_exec : IO (bool * traceT))
           (then_exec : scriptT -> IO (bool * traceT)) : IO bool :=
  '(b, tr) <- first_exec;;
  if b : bool
  then ret true
  else IO.while_loop (shrink_execute' then_exec) (map (snd ∘ fst) tr);;
       ret false.

Variable gen_state : Type.

Variant clientE : Type -> Type :=
  Client__Recv : clientE (option (packetT id))
| Client__Send : gen_state -> clientE (option (packetT id)).

Variable otherE : Type -> Type.
Variable other_handler : otherE ~> IO.
Arguments other_handler {_}.

Definition failureE := (exceptE string).
Notation tE := (failureE +' clientE +' otherE).

Variable conn_state    : Type.
Variable init_state    : conn_state.
Variable fill_trace    : packetT id -> traceT -> traceT.
Variable fill_request  : traceT -> stepT -> requestT id.
Variable gen_step      : gen_state -> traceT -> IO stepT.
Variable recv_response : Monads.stateT conn_state IO (option (packetT id)).
Variable send_request  : requestT id -> Monads.stateT conn_state IO (option connT).

Fixpoint execute' {R} (fuel : nat) (s : conn_state)
         (oscript : option scriptT) (acc : traceT) (m : itree tE R)
  : IO (bool * conn_state * traceT) :=
  match fuel with
  | O => ret (true, s, acc)
  | S fuel =>
    prerr_endline "Hi";;
    prerr_endline (to_string fuel);;
    prerr_endline "Wat";;
    match observe m with
    | RetF _ => ret (true, s, acc)
    | TauF m' => execute' fuel s oscript acc m'
    | VisF e k =>
      match e with
      | (Throw err|) => ret (false, s, acc)
      | (|ce|) =>
        match ce in clientE Y return (Y -> _) -> _ with
        | Client__Recv =>
          fun k => '(s', op) <- recv_response s;;
                let acc' : traceT :=
                    match op with
                    | Some p => fill_trace p acc
                    | None   => acc
                    end in
                execute' fuel s' oscript acc' (k op)
        | Client__Send gs =>
          fun k => '(ostep, osc') <- match oscript with
                                 | Some [] => ret (None, Some [])
                                 | Some (sc :: script') =>
                                   ret (Some sc, Some script')
                                 | None => step <- gen_step gs acc;;
                                          ret (Some step, None)
                               end;;
                match ostep with
                | Some step =>
                  let req : requestT id := fill_request acc step in
                  '(s', oc) <- send_request req s;;
                  if oc is Some c
                  then let pkt : packetT id := Packet c Conn__Server (inl req) in
                       execute' fuel s' osc' (acc++[(c, step, None)])
                                (k (Some pkt))
                  else execute' fuel s' osc' acc (k None)
                | None => execute' fuel s osc' acc (k None)
                end
        end k
      | (||oe) => other_handler oe >>= execute' fuel s oscript acc ∘ k
      end
    end
  end.

Variable cleanup : conn_state -> IO unit.

Definition execute {R} (m : itree tE R) (oscript : option scriptT)
  : IO (bool * traceT) :=
  '(b, s, t') <- execute' 5000 init_state oscript [] m;;
  cleanup s;;
  ret (b, t').

Definition test {R} (m : itree tE R) : IO bool :=
  shrink_execute (execute m None) (execute m ∘ Some).

End IShrink.

Arguments packetT : clear implicits.
Arguments Packet        {_ _ _ _}.
Arguments packet__src     {_ _ _ _}.
Arguments packet__dst     {_ _ _ _}.
Arguments packet__payload {_ _ _ _}.
