(* *********************************************************************)
(*                                                                     *)
(*                   Example Policies for GARUDA 2.0                   *)
(*                                                                     *)
(* *********************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Arith ZArith.
Require Import Vector. 
Require Import String.
Require Import JMeq.
Require Import List. Import ListNotations.

Require Import Integers.
Require Import lang.
Require Import extraction.
Require Import syntax. 
Require Import combinators.



(* ***************************)
(*  A Nil Obfuscation Policy *)
(* ***************************)
Section noObf.
	Variables i o : id TVec64.
  (* Main Streams *)
    (* E Stream *)
    (* EffAddr - 64 *)
	  Definition noObf_E := TVec64.
    (*Definition noObf_E := TArr (128)%nat TBit.*)
    (*Definition noObf_E_id := id noObf_E.*)
    (* M Stream *)
	  Definition noObf_M := TVec64.
    (*Definition noObf_M := TArr (128)%nat TBit.*)
  (* EffAddr *)
  Definition noObf_ea  := EffAddr.
  Definition noObf_eaO := Obf noObf_ea.
  Definition noObf_Phi x := EPhiop (OPhiNone) x.
  (*Definition (ea : fld) := ea -> ea -> Phi.*)

  (*Definition noObf: pol noObf_E noObf_M := PPhi noObf_Phi.*)
  Definition noObf: pol TVec64 TVec64 := PPhi noObf_Phi.

End noObf.


(* ***********************)
(*  Define Pols Compiled *)
(* ***********************)
Definition noObf_EVar : id noObf_E := "E".
Definition noObf_MVar : id noObf_M := "M".
Definition noObf_compiled : prog := compile noObf_EVar noObf_MVar noObf.


(* ****************************)
(*  Define HS Print Functions *)
(* ****************************)
Definition pretty_print_noObf :=
  pretty_print_tb "noObf" noObf_compiled.


(* ************************)
(*  Extraction to Haskell *)
(* ************************)
(* run the program 'secjmp.hs' and pipe to a file to get verilog       *)
(* Ignore warnings on opacity, see the end of the section on realizing *)
(* axioms for a proper explanation on why this is safe to do so:       *)
(* https://coq.inria.fr/refman/addendum/extraction.html?highlight=extraction%20warning#realizing-axioms *)
Extract Constant main => "Prelude.putStrLn pretty_print_noObf".
Extraction "noObf.hs" pretty_print_noObf main.