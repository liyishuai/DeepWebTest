From CAS Require Export
     Execute.
From Extract Require Export
     IO_Test.

Definition run_test : io_unit :=
  IO.unsafe_run
    (ORandom.self_init tt;;
     multi_test (@test void cas_smi)).

Separate Extraction run_test.
