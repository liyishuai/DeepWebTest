From Ceres Require Export
     Ceres.
From Coq Require Export
     List
     String
     ZArith.
Export
  ListNotations.
Open Scope string_scope.
Local Open Scope Z_scope.

Notation key   := string.
Notation tag   := string.
Notation value := string.

Variant requestT :=
  Request__GET (k : key) (t : tag)
| Request__CAS (k : key) (t : tag) (v : value).

Variant responseT {exp_} :=
  Response__NotModified
| Response__OK (t : exp_ tag) (v : exp_ value)
| Response__NoContent
| Response__PreconditionFailed.
Arguments responseT : clear implicits.

Instance Serialize__requestT : Serialize requestT :=
  fun m =>
    match m with
    | Request__GET k t =>
      [Atom "GET"; to_sexp k; to_sexp t]
    | Request__CAS k t v =>
      [Atom "CAS"; to_sexp k; to_sexp t; to_sexp v]
    end%sexp.

Instance Serialize__responseT {exp_} `{Serialize (exp_ string)}
  : Serialize (responseT exp_) :=
  fun m =>
    match m with
    | Response__NotModified => Atom "NotModified"
    | Response__OK t v      => [Atom "OK"; to_sexp t; to_sexp v]
    | Response__NoContent   => Atom "NoContent"
    | Response__PreconditionFailed => Atom "PreconditionFailed"
    end%sexp.

Instance Serialize__idString : Serialize (id string) :=
  fun (s : string) => to_sexp s.

Instance Deserialize__requestT : Deserialize requestT :=
  Deser.match_con "request" []
    [ ("GET", Deser.con2_ Request__GET)
    ; ("CAS", Deser.con3_ Request__CAS)].

Instance Deserialize__responseT {exp_} `{Deserialize (exp_ string)}
  : Deserialize (responseT exp_) :=
  Deser.match_con "response"
    [ ("NotModified"       , Response__NotModified       )
    ; ("NoContent"         , Response__NoContent         )
    ; ("PreconditionFailed", Response__PreconditionFailed)]
    [ ("OK", Deser.con2_ Response__OK)].
