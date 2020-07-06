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

(*Require Import Integers.*)
Require Import lang.
Require Import extraction.
(*Require Import syntax.*)
Require Import combinators.



(* ***************************)
(*  A Nil Obfuscation Policy *)
(* ***************************)
Section noObf.
  (* Main Streams *)
    (* E Stream *)
    (*Definition noObf_E := TVec64.*)
    (*Definition noObf_E := TArr (128)%nat TBit.*)
    (* M Stream *)
    (*Definition noObf_M := TVec64.*)
    (*Definition noObf_M := TArr (128)%nat TBit.*)
  (* EffAddr *)
  Definition noObf_ea  := EffAddr.
  Definition noObf_eaO := Obf noObf_ea.
  Definition noObf_Phi := PPhi OPhiId.

  Definition noObf: pol TVec64 TVec64 := noObf_Phi.

End noObf.


(* ***********************************)
(*  An XOR Policy with Inverse Proof *)
(* ***********************************)
Section XORO.
  (* Monitors that obfuscate *)
  (* XOR Module Obfuscate: *)
    Definition XORM_O e := EBinop OXor (EVal (ofromz 11673330234144325632)) e.
    Definition XORO_Mod: pol TVec64 TVec64 := PUpd XORM_O.

  (*Definition XOR_Mod_DeO :=*)

  (* Overarching Monitor *)
  (*Variables i is os o : id TVec64.*)
  (* Main Streams *)
    (* E Stream *)
    Definition XORO_E := TVec64.
    (* M Stream *)
    Definition XORO_M := TVec64.
  (* EffAddr *)
  Definition XORO_ea  := EffAddr.
  Definition XORO_eaO := Obf XORO_ea.
  Definition XORO_key := EVal (ofromz 11673330234144325632).
  Definition XORO_Phi := PPhi (OPhi "XORO_Mod").


  Definition XORO: pol XORO_E XORO_M := XORO_Phi.

End XORO.

(* ***********************)
(*  Define Pols Compiled *)
(* ***********************)
  Definition EVar : id TVec64 := "EXE_Stream".
  Definition MVar : id TVec64 := "MEM_Stream".

  Definition noObf_compiled : prog := compile EVar MVar noObf.

  Definition XORM_compiled : prog := compile EVar MVar XORO_Mod.
  Definition XORO_compiled : prog := compile EVar MVar XORO.

(* Definition EXE_O  : id noObf_E := "EXE_Out". 
   Definition EXE_SR : id noObf_E := "EXE_SReg".
   Definition MEM_SR : id noObf_E := "MEM_SReg".
   Definition MEM_I  : id noObf_E := "MEM_In".
*)

(* ****************************)
(*  Define HS Print Functions *)
(* ****************************)
  Definition pretty_print_noObf :=
    pretty_print_tb "noObf" noObf_compiled.

  Definition pretty_print_XORM :=
    pretty_print_tb "XORO_Mod" XORM_compiled.
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

  Extract Constant main => "Prelude.putStrLn pretty_print_XORM".
  Extraction "XORM.hs" pretty_print_XORM main.
  Extract Constant main => "Prelude.putStrLn pretty_print_XORO".
  Extraction "XORO.hs" pretty_print_XORO main.




