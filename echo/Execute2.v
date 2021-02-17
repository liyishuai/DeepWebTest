From DeepWeb Require Export
     NetUnix
     Compose2
     Switch2
     Test2.
Import MonadNotation.
Open Scope string_scope.

Fixpoint execute' {R} (fuel : nat) (s : conn_state) (m : itree tE R) : IO bool :=
  match fuel with
  | O => ret true
  | S fuel =>
    match observe m with
    | RetF _   => ret true
    | TauF m'  => execute' fuel s m'
    | VisF e k =>
      match e with
      | (ge|) =>
        match ge in genE T return (T -> _) -> _ with
        | Gen =>
          fun k =>
            n <- nat_of_int <$> ORandom.int (List.length conns);;
            let c : connT := nth n conns 1 in
            pkt <- Packet c 0 ∘ ascii_of_int <$> ORandom.int 256;;
            execute' fuel s (k pkt)
        end k
      | (|ne|) =>
        match ne in nondetE T return (T -> _) -> _ with
        | Or => (bind $ ORandom.bool tt) ∘ (compose $ execute' fuel s)
        end k
      | (||Throw err|) => prerr_endline (to_ostring err);;
                         ret false
      | (|||le|) =>
        match le in logE T return (T -> _) -> _ with
        | Log str => fun k => prerr_endline ("Tester: " ++ str);;
                          execute' fuel s (k tt)
        end k
      | (||||ne) => '(s', r) <- client_io _ ne s;;
                  execute' fuel s' (k r)
      end
    end
  end.

Definition execute {R} (m : itree tE R) : IO bool :=
  cs <- client_init;;
  execute' 5000 cs m.

Definition test : itree netE void -> IO bool :=
  execute ∘ tester ∘ observer ∘ compose_switch tcp.
