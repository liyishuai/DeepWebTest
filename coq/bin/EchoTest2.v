From DeepWeb Require Import
     Echo
     Execute2
     IO_Test.

Definition run_echotest : io_unit :=
  IO.unsafe_run $ ORandom.self_init tt;; run_test (test echo).

Separate Extraction run_echotest.
