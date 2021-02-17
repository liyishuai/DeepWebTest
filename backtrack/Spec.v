From Coq Require Export
     Ascii.
From Test Require Export
     Backtrack.

Variant traceT :=
  Trace__Send : nat -> traceT
| Trace__Recv : nat -> traceT.

Instance Serialize__traceT : Serialize traceT :=
  fun t =>
    match t with
    | Trace__Send n => [Atom "TSend"; to_sexp n]
    | Trace__Recv n => [Atom "TRecv"; to_sexp n]
    end%sexp.

Fixpoint is_trace' {R} (fuel : nat) (m : itree oE R) (l : list traceT)
  : list string + list string :=
  match fuel with
  | O => inr ["Out of fuel"]
  | S fuel =>
    match observe m with
    | RetF vd => inr ["Returned"]
    | TauF m' => is_trace' fuel m' l
    | VisF e k =>
      match e with
      | (Throw err|) => inl [err]
      | (|ne|) =>
        match ne in nondetE Y return (Y -> _) -> _ with
        | Or =>
          fun k =>
            let rt := is_trace' fuel (k true)  l in
            let rf := is_trace' fuel (k false) l in
            match rt, rf with
            | inl et, inl ef =>
              inl $ "TRUE  branch failed with:"::et ++
                    "FALSE branch failed with:"::ef
            | inr _, _ => rt
            | _    , _ => rf
            end
        end k
      | (||oe) =>
        match l with
        | [] => inr ["Out of trace"]
        | h::l' =>
          match oe in observeE Y, h return (Y -> _) -> _ with
          | Observe__Send, Trace__Send n
          | Observe__Recv, Trace__Recv n =>
            fun k => is_trace' fuel (k n) l'
          | _, _ => fun k => inl ["Expect " ++ to_string oe ++
                              ", but observed " ++ to_string h]
          end k
        end
      end
    end
  end.

Definition newline : string := String "010" "".

Definition bigNumber : nat := 5000.

Definition is_trace {R} (m : itree oE R) (l : list traceT)
  : string + string :=
  match is_trace' bigNumber m l with
  | inl ss => inl (concat newline ss)
  | inr ss => inr (concat newline ss)
  end.

Fixpoint accepts' {R} (fuel : nat) (m : itree tE R) (l : list traceT)
  : list string + list string :=
  match fuel with
  | O => inr ["Out of fuel"]
  | S fuel =>
    match observe m with
    | RetF vd => inr ["Returned"]
    | TauF m' => accepts' fuel m' l
    | VisF e k =>
      match e with
      | (Throw err|) => inl [err]
      | (|te) =>
        match l with
        | [] => inr ["Out of trace"]
        | h::l' =>
          match te in testerE Y, h return (Y -> _) -> _ with
          | Tester__Send, Trace__Send n
          | Tester__Recv, Trace__Recv n =>
            fun k => accepts' fuel (k $ Some n) l'
          | _, _ => fun k => accepts' fuel (k None) l
          end k
        end
      end
    end
  end.

Definition accepts {R} (m : itree tE R) (l : list traceT)
  : string + string :=
  match accepts' bigNumber m l with
  | inl ss => inl (concat newline ss)
  | inr ss => inr (concat newline ss)
  end.
