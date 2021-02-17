From Coq Require Export
     Nat.
From Test Require Export
     Spec.
Open Scope nat_scope.

Definition expect {E R} `{failureE -< E} `{observeE -< E}
           (a : nat) (r : itree E R) : itree E R :=
  b <- trigger Observe__Recv;;
  if a =? b
  then r
  else throw $ "Sent " ++ to_string a ++
             ", but received " ++ to_string b.

Definition echo0 : itree oE unit :=
  a <- trigger Observe__Send;;
  expect a (ret tt).

Definition trace0 : list traceT :=
  [Trace__Send 0;
  Trace__Recv 0].

Goal is_trace echo0 trace0 = inr "Returned".
Proof. reflexivity. Qed.

Goal accepts (backtrack echo0) trace0 = inr "Returned".
Proof. reflexivity. Qed.

Definition trace1 : list traceT :=
  [Trace__Send 0;
  Trace__Send 1;
  Trace__Recv 0;
  Trace__Recv 1].

Goal is_trace echo0 trace1 = inl "Expect ORecv, but observed (TSend 1)".
Proof. reflexivity. Qed.

Definition echo1 : itree oE unit :=
  a1 <- trigger Observe__Send;;
  or (expect a1 echo0)
     (a2 <- trigger Observe__Send;;
      or (expect a1 (expect a2 (ret tt)))
         (expect a2 (expect a1 (ret tt)))).

Goal is_trace echo1 trace1 = inr "Returned".
Proof. reflexivity. Qed.


(* Definition echotest1 : itree tE unit := *)
(*   oa1 <- trigger Tester__Send;; *)
(*   match oa1 with *)
(*   | Some a1 => *)
(*     ob1 <- trigger Tester__Recv;; *)
(*     match ob1 with *)
(*     | Some b1 => *)
(*       if a1 =? b1 *)
(*       then backtrack echo0 *)
(*       else throw $ "Sent " ++ to_string a1 ++ *)
(*                  ", but received " ++ to_string b1 *)
(*     | None => *)
