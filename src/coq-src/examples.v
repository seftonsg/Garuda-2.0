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
  Definition noObf_Phi := PPhi OPhiNone.
  (*Definition (ea : fld) := ea -> ea -> Phi.*)

  (*Definition noObf: pol noObf_E noObf_M := PPhi noObf_Phi.*)
  Definition noObf: pol TVec64 TVec64 := noObf_Phi.

End noObf.


(* ***********************************)
(*  An XOR Policy with Inverse Proof *)
(* ***********************************)
Section XORO.
  Variables i o : id TVec64.
  (* Main Streams *)
    (* E Stream *)
    (* EffAddr - 64 *)
    Definition XORO_E := TVec64.
    (*Definition XORO_E := TArr (128)%nat TBit.*)
    (*Definition XORO_E_id := id XORO_E.*)
    (* M Stream *)
    Definition XORO_M := TVec64.
    (*Definition XORO_M := TArr (128)%nat TBit.*)
  (* EffAddr *)
  Definition XORO_ea  := EffAddr.
  Definition XORO_eaO := Obf XORO_ea.
  Definition XORO_key := EVal (ofromz 11673330234144325632).
  (*Definition XORO_Phi x := EPhiop (OPhiSome ((OPhiNone) x) (OXor (EVar XORO_key))).*)
  Definition XORO_Phi := OPhiSome "test".
  Definition XORO_EPhi := PPhi XORO_Phi.


  Definition XORO: pol XORO_E XORO_M := XORO_EPhi.
  (*Definition XORO: pol TVec64 TVec64 := XORO_EPhi (EVal (ofromz 0)).*)

End XORO.

(* ***********************)
(*  Define Pols Compiled *)
(* ***********************)
Definition noObf_EVar : id noObf_E := "EXE_Stream".
Definition noObf_MVar : id noObf_M := "MEM_Stream".
Definition noObf_compiled : prog := compile noObf_EVar noObf_MVar noObf.
Definition XORO_compiled : prog := compile noObf_EVar noObf_MVar XORO.


(* ****************************)
(*  Define HS Print Functions *)
(* ****************************)
Definition pretty_print_noObf :=
  pretty_print_tb "noObf" noObf_compiled.
Definition pretty_print_XORO :=
  pretty_print_tb "XORO" XORO_compiled.


(* ************************)
(*  Extraction to Haskell *)
(* ************************)
(* run the program 'secjmp.hs' and pipe to a file to get verilog       *)
(* Ignore warnings on opacity, see the end of the section on realizing *)
(* axioms for a proper explanation on why this is safe to do so:       *)
(* https://coq.inria.fr/refman/addendum/extraction.html?highlight=extraction%20warning#realizing-axioms *)
Extract Constant main => "Prelude.putStrLn pretty_print_noObf".
Extraction "noObf.hs" pretty_print_noObf main.
Extract Constant main => "Prelude.putStrLn pretty_print_XORO".
Extraction "XORO.hs" pretty_print_XORO main.




