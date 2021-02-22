From CAS Require Export
     Server.

Definition run_server : io_unit :=
  IO.unsafe_run cas_server.

Separate Extraction run_server.
