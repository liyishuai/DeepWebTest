From DeepWeb Require Import
     Echo
     Execute
     IO_Test.

Definition run_echo : io_unit :=
  IO.unsafe_run (run_server echo;; ret tt).

Separate Extraction run_echo.
