From Ceres Require Export
     Ceres.
From Coq Require Export
     List
     String
     ZArith.
From CAS Require Export
     Common.
Export
  ListNotations.
Open Scope string_scope.
Local Open Scope Z_scope.

Notation key   := string.
Notation tag   := string.
Notation value := string.

Variant requestT {exp_} :=
  Request__GET (k : key) (t : exp_ tag)
| Request__CAS (k : key) (t : exp_ tag) (v : value).
Arguments requestT : clear implicits.

Variant responseT {exp_} :=
  Response__NotModified
| Response__OK (t : exp_ tag) (v : exp_ value)
| Response__NoContent
| Response__PreconditionFailed.
Arguments responseT : clear implicits.

Instance Dec_Eq__requestT : Dec_Eq (requestT id).
Proof. dec_eq. Defined.

Instance Serialize__requestT : Serialize (requestT id) :=
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
    | Response__NotModified => [Atom "NotModified"]
    | Response__OK t v      => [Atom "OK"; to_sexp t; to_sexp v]
    | Response__NoContent   => [Atom "NoContent"]
    | Response__PreconditionFailed => [Atom "PreconditionFailed"]
    end%sexp.

Instance Deserialize__requestT : Deserialize (requestT id) :=
  Deser.match_con "request" []
    [ ("GET", Deser.con2_ Request__GET)
    ; ("CAS", Deser.con3_ Request__CAS)].

Instance Deserialize__responseT : Deserialize (responseT id) :=
  Deser.match_con "response" []
    [ ("NotModified"       , Deser.con0 Response__NotModified       )
    ; ("NoContent"         , Deser.con0 Response__NoContent         )
    ; ("PreconditionFailed", Deser.con0 Response__PreconditionFailed)
    ; ("OK", Deser.con2_ Response__OK)].
