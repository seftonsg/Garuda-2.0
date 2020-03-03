Set Implicit Arguments.
Unset Strict Implicit.

Require Import List. Import ListNotations.
Require Import ZArith.
Require Import extraction.
Require Import Integers.
Require Import String.
Require Import lang syntax.

Open Scope hdl_type_scope.
Open Scope hdl_exp_scope.
Open Scope hdl_stmt_scope.
Open Scope string_scope.

Definition TRUE := (true:interp_ty TBit).
Definition FALSE := (false:interp_ty TBit).

Definition encode
        (n:nat)
        (input:id (tbit))
        (output:id (tarr n<<<tbit>>>))                
  : prog :=
  iter 0 n (fun i => output@i <- evar input).

Definition decode
        (n:nat)
        (input:id (tarr n<<<tbit>>>))
        (output:id (tbit))
  : prog :=
  Local vec "r" ::== int32 0;;;
  iter 0 n (fun i => "r" <= evar "r" plus input[[i]]);;;
  SITE ((evar "r" lt val (Int.repr (Z.of_nat (n/2 + 1)) : interp_ty TVec32)))
    (output <= val FALSE)
    (output <= val TRUE).

Definition example: prog :=
  Input vec "in" <<< tbit >>> ::== TRUE;;;
  Local arr "mid" <<< tbit, 3 >>>;;;
  Output vec "out" <<< tbit >>> ::== FALSE;;;
  @encode 3 "in" "mid";;;
  @decode 3 "mid" "out".

Definition example_tb: verilog := 
  pretty_print_tb "example" example.
Extract Constant main => "Prelude.putStrLn example_tb".
(* run the program 'example.hs' and pipe to a file to get verilog *)
Extraction "example.hs" example_tb main.



              
  
  
  
