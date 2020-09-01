From DeepWeb Require Import
     Echo
     Execute
     IO_Test.

Definition run_echo : io_unit :=
  IO.unsafe_run (vd <- echo1;; match vd in void with end).

Separate Extraction run_echo.
