Require Import extraction sha256.

Definition sha256_core_print_tb :=
  pretty_print_tb "sha256_core" sha256_core.
Extract Constant main => "Prelude.putStrLn sha256_core_print_tb".
(* run the program 'sha256_core.hs' and pipe to a file to get verilog *)
Extraction "sha256_core.hs" sha256_core_print_tb main.

Definition sha256_mult0_print_tb :=
  pretty_print_tb "sha256_mult0" sha256_mult0.
Extract Constant main => "Prelude.putStrLn sha256_mult0_print_tb".
(* run the program 'sha256_mult0.hs' and pipe to a file to get verilog *)
Extraction "sha256_mult0.hs" sha256_mult0_print_tb main.

Definition sha256_mult1_print_tb :=
  pretty_print_tb "sha256_mult1" sha256_mult1.
Extract Constant main => "Prelude.putStrLn sha256_mult1_print_tb".
(* run the program 'sha256_mult1.hs' and pipe to a file to get verilog *)
Extraction "sha256_mult1.hs" sha256_mult1_print_tb main.

