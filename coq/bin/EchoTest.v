From DeepWeb Require Import
     Echo
     Execute
     IO_Test.

Definition run_echotest : io_unit :=
  IO.unsafe_run $ run_test (multi_test $ test echo).

Separate Extraction run_echotest.
