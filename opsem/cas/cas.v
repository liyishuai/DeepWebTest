From CAS Require Import Exp.

Variant request :=
  Request_CAS (cmp swp : N)
| Request_Q   (cmp     : N)
| Request_R.

Variant state :=
  State_Init
| State_Ready (data : exp N)
| State_Recv  (data : exp N) (req : request).

Variant transition :=
  Transition_Tau
| Transition_Send (res : exp bool)
| Transition_Recv (req : request).

Inductive rule :=
  Rule_Base (precondition : state -> exp bool)
            (trans        : state -> transition)
            (poststate    : state -> state)
| Rule_Exists {T} (k : T -> rule).

Definition reset : rule :=
  Rule_Exists
    (fun data : exp N =>
       Rule_Base (fun st =>
                    match st with
                    | State_Recv _ Request_R
                    | State_Init => exp_true
                    | _          => exp_false
                    end)
                 (fun st =>
                    match st with
                    | State_Recv _ _ => Transition_Send exp_true
                    | _ => Transition_Tau
                    end)
                 (const (State_Ready data))).

Definition recv : rule :=
  Rule_Exists
    (fun req : request =>
       Rule_Base (const exp_true)
                 (const (Transition_Recv req))
                 (fun st =>
                    match st with
                    | State_Ready data => State_Recv data req
                    | _ => State_Init (* don't care *)
                    end)).

Definition q : rule :=
  Rule_Base (fun st => match st with
                     | State_Recv _ (Request_Q _) => exp_true
                     | _ => exp_false
                     end)
            (fun st => match st with
                     | State_Recv data (Request_Q cmp) =>
                       Transition_Send (exp_eq cmp data)
                     | _ => Transition_Tau (* don't care *)
                     end)
            (fun st => match st with
                     | State_Recv data _ => State_Ready data
                     | _ => State_Init (* don't care *)
                     end).

Definition hit : rule :=
  Rule_Base (fun st =>
               match st with
               | State_Recv data (Request_CAS cmp _) =>
                 exp_eq cmp data
               | _ => exp_false
               end)
            (const (Transition_Send exp_true))
            (fun st =>
               match st with
               | State_Recv _ (Request_CAS _ swp) =>
                 State_Ready (exp_int swp)
               | _ => State_Init (* don't care *)
               end).

Definition miss : rule :=
  Rule_Base (fun st =>
               match st with
               | State_Recv data (Request_CAS cmp _) =>
                 exp_negb (exp_eq cmp data)
               | _ => exp_false
               end)
            (const (Transition_Send exp_false))
            (fun st =>
               match st with
               | State_Recv data _ => State_Ready data
               | _ => State_Init (* don't care *)
               end).
