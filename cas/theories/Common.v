From SimpleIO Require Export
     IO_Random
     SimpleIO.
From Parsec Require Export
     Parser.
From QuickChick Require Export
     Decidability.
From ExtLib Require Export
     Functor
     Option.
From Coq Require Export
     Ascii
     Basics
     Bool
     DecidableClass
     ExtrOcamlIntConv
     String
     List.
Export
  ListNotations.
Open Scope string_scope.
Open Scope parser_scope.
Open Scope lazy_bool_scope.
Open Scope program_scope.

Instance Dec_Eq__id {A} `{Dec_Eq A} : Dec_Eq (id A).
Proof. dec_eq. Defined.

Definition get {K V} `{Dec_Eq K} (k : K) :
  list (K * V) -> option V :=
  fmap snd ∘ find ((fun kv => k = fst kv?)).

Definition delete {K V} `{Dec_Eq K} (k : K) :
  list (K * V) -> list (K * V) :=
  filter (fun kv => (k <> fst kv?)).

Definition put {K V} : K -> V -> list (K * V) -> list (K * V) :=
  compose cons ∘ pair.

Definition update {K V} `{Dec_Eq K} (k : K) (v : V)
  : list (K * V) -> list (K * V) :=
  put k v ∘ delete k.

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

Fixpoint parseParens' (depth : nat) : parser string :=
  match depth with
  | O => raise None
  | S depth =>
    prefix <- string_of_list_ascii <$> untilMulti ["(";")"]%char;;
    r <- anyToken;;
    match r with
    | ")"%char => ret $ prefix ++ ")"
    | "("%char =>
      append prefix ∘ String r <$>
             liftA2 append (parseParens' depth) (parseParens' depth)
    | _ => raise $ Some "Should not happen"
    end
  end.

Definition parseParens : parser string :=
  liftA2 String (expect "("%char) $ parseParens' bigNumber.

Definition io_choose_ {A} (default : IO A) (l : list A) : IO A :=
  match l with
  | [] => default
  | a :: _ =>
    i <- nat_of_int <$> ORandom.int (int_of_nat (length l));;
    ret (nth i l a)
  end.

Definition io_choose' {A} (l : list A) : IO (nat * A) :=
  match l with
  | [] => failwith "Cannot choose from empty list"
  | a :: _ =>
    i <- nat_of_int <$> ORandom.int (int_of_nat (length l));;
    ret (i, nth i l a)
  end.

Definition io_choose {A} : list A -> IO A :=
  fmap snd ∘ io_choose'.

Definition gen_string' : IO string :=
  io_choose ["Hello"; "World"].

Definition io_or {A} (x y : IO A) : IO A :=
  b <- ORandom.bool tt;;
  if b : bool then x else y.

Fixpoint gen_many {A} (n : nat) (ma : IO A) : IO (list A) :=
  match n with
  | O => ret []
  | S n' => liftA2 cons ma $ io_or (ret []) (gen_many n' ma)
  end.

Definition gen_string : IO string :=
  String "~" ∘ String.concat "" <$> gen_many 3 gen_string'.

Polymorphic Instance Serialize_id {A} {Serialize_A : Serialize A}
  : Serialize (id A)
  := Serialize_A.

Polymorphic Instance Deserialize_id {A} {Deserialize_A : Deserialize A}
  : Deserialize (id A)
  := Deserialize_A.
