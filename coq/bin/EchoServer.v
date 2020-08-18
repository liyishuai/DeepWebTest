From DeepWeb Require Import
     Echo
     Execute
     IO_Test.

Definition run_echo : io_unit :=
  IO.unsafe_run (vd <- run_server echo;; match vd in void with end).

Separate Extraction run_echo.
