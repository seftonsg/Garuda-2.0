(* *********************************************************************)
(*                                                                     *)
(*           Original GARUDA Example Policies and Extractions          *)
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




(* ************************)
(*  SecJmp Example Policy *)
(* ************************)
Section test_secjmp.
  Variables i o : id TVec64.
  (*High-order 10 bits of immediate address are zeroed. Because the effective 
    address of the jump is calculated in MIPS as pc[0:3]++imm_addr[0:25]++[0;0], 
    this enforces that all jumps are within a 2^16 offset of the higher-order 4 
    bits of any instruction. Note that this policy doesn't deal with branches 
    or indirect jumps. Note also that it's possible in principle to check 
    statically that direct jumps are policy compliant.*)  
  Definition sec_addr := BFieldRange ImmAddr (ofromz 10) (ofromz 0).
  Definition sec_jmp : pol TVec64 TVec64 :=
    `IF` jump `THEN` PTest sec_addr PId `ELSE` PId.
End test_secjmp.

(* *************************************)
(*  Secure Control Flow Example Policy *)
(* *************************************)
Section scf.
  (*A control-flow isolation policy. We assume that the effective address
    is pre-calculated in the top 32 bits of the input vector. *)
  Variables i o : id TVec64.
  Definition control_domain := ofromz 0.
  Definition sec_addr32 := BFieldRange EffAddr (ofromz 10) control_domain.
  Definition scf: pol TVec64 TVec64 :=
    `IF` ctrl `THEN` PTest (BNeg sec_addr32) PId `ELSE` PId.
  (*We define a second version of this policy that applies just to indirect 
    control flows (direct flows could be checked statically).*)
  Definition scf2: pol TVec64 TVec64 :=
    `IF` jump_indirect `THEN` PTest (BNeg sec_addr32) PId `ELSE` PId.    
End scf.

(* ****************************************)
(*  Secure Failt Isolation Example Policy *)
(* ****************************************)
Section sfi.
  (*A write isolation policy, which we called SFI in the original paper. Note that 
    SFI sometimes refers to a combination of write isolation and control-flow isolation 
    (a point the paper clarifies). Below, the logical fault domain (lfd_mask) 
    is the sub-address space beginning with higher-order bits 0^8.*)
  Variables ri ro : id TVec64.

  Definition lfd_start := ofromz 11673330234144325632. (*162<<56*)
  Definition lfd_mask := ofromz 72057594037927935. (*0^8 1^56*)

  Definition mask e := EBinop OAnd (EVal lfd_mask) e.
  Definition force_range e := EBinop OOr (EVal lfd_start) e.
 
  Definition sfi: pol TVec64 TVec64 :=
    `IF` store `THEN` PConcat (PUpd mask) (PUpd force_range) `ELSE` PId.
End sfi.

(* ******************************)
(*  Simple Taint Example Policy *)
(* ******************************)
Section taint.
  (*Taint tracking through ALU operations only (the monitors could be extended to 
    support other taint propagation rules).*)
  Definition rs_taint := TaintBit (ofromz 63).
  Definition rt_taint := TaintBit (ofromz 62).  
  Definition pc_taint := TaintBit (ofromz 61).
  Definition TAINTED := ofromz 1.
  Definition NOT_TAINTED := ofromz 0.  
  Definition tainted_Itype: pred TVec64 :=
    BField pc_taint TAINTED `orpred` BField rs_taint TAINTED.
  Definition tainted_Rtype: pred TVec64 := BField rt_taint TAINTED.  
  Definition taint64: pol TVec64 TVec64 :=
    `IF` tainted_Itype `orpred` (R_type `andpred` tainted_Rtype)
     `THEN` PUpd (fun _ => EVal TAINTED)
     `ELSE` PUpd (fun _ => EVal NOT_TAINTED).

  (*Here's an alternative implementation of taint64 that inputs just the required bits:
    in[0] = is_rtype, in[1] = rs_taint, in[2] = rt_taint, in[3] = pc_taint.*)
  Definition TaintTy := TArr 4 TBit.
  Lemma zlt4: 0 < 4. omega. Qed.
  Lemma olt4: 1 < 4. omega. Qed.
  Lemma tlt4: 2 < 4. omega. Qed.
  Lemma thlt4: 3 < 4. omega. Qed.      
  Definition taint: pol TaintTy TBit :=
    let rtype_idx := @Fin.of_nat_lt 0 4 zlt4 in
    let rs_taint_idx := @Fin.of_nat_lt 1 4 olt4 in
    let rt_taint_idx := @Fin.of_nat_lt 2 4 tlt4 in
    let pc_taint_idx := @Fin.of_nat_lt 3 4 thlt4 in        
    @PUpd TaintTy TBit _ _ (fun ax: exp TaintTy =>
            match ax with
            | EVar _ a => 
              let is_rtype := EDeref rtype_idx a in
              let rs_taint := EDeref rs_taint_idx a in
              let rt_taint := EDeref rt_taint_idx a in
              let pc_taint := EDeref pc_taint_idx a in
              EBinop OOr pc_taint (EBinop OOr rs_taint (EBinop OAnd is_rtype rt_taint))
            | _ => @EVal TBit _ false (*BOGUS: Can't occur by defn. of compile_pol.*)
            end).
End taint.

(* *********************)
(*  Print the Programs *)
(* *********************)
Require Import extraction.

(* ****************)
(*  Define Fields *)
(* ****************)
Definition i : id TVec64 := "i".
Definition o : id TVec64 := "o".
Definition ri : id TVec64 := "ri".
Definition ro : id TVec64 := "ro".
(* These don't really mean anything: *)
(*
Definition Es : id TVec64 := "Es".
Definition Eos : id TVec64 := "Eos".
Definition Mos : id TVec64 := "Mos".
Definition Ms : id TVec64 := "Ms".
*)

(* ***********************)
(*  Define Pols Compiled *)
(* ***********************)
Definition sec_jmp_compiled : prog := compile i o sec_jmp.
Definition SFI_compiled : prog := compile ri ro sfi.
Definition sec_jmp_sfi_compiled : prog := compile i o (PConcat sec_jmp sfi).
Opaque sec_jmp.
Opaque sfi.

Definition taint_i: id TaintTy := "ti".
Definition taint_o: id TBit := "to".
Definition taint_compiled : prog := compile taint_i taint_o taint.

Definition scf_compiled : prog := compile i o scf.

(* ****************************)
(*  Define HS Print Functions *)
(* ****************************)
Definition pretty_print_sec_jmp :=
  pretty_print_tb "secjmp" sec_jmp_compiled.
Definition pretty_print_SFI :=
  pretty_print_tb "SFI" SFI_compiled.
Definition pretty_print_taint := 
  pretty_print_tb "taint" taint_compiled.
Definition pretty_print_SCF := 
  pretty_print_tb "SCF" scf_compiled.
Definition pretty_print_SJSFI := 
  pretty_print_tb "SJSFI" sec_jmp_sfi_compiled.

(* ************************)
(*  Extraction to Haskell *)
(* ************************)
(* run the program 'secjmp.hs' and pipe to a file to get verilog       *)
(* Ignore warnings on opacity, see the end of the section on realizing *)
(* axioms for a proper explanation on why this is safe to do so:       *)
(* https://coq.inria.fr/refman/addendum/extraction.html?highlight=extraction%20warning#realizing-axioms *)
Extract Constant main => "Prelude.putStrLn pretty_print_sec_jmp".
Extraction "secjmp.hs" pretty_print_sec_jmp main.
Extract Constant main => "Prelude.putStrLn pretty_print_SFI".
Extraction "SFI.hs" pretty_print_SFI main.
Extract Constant main => "Prelude.putStrLn pretty_print_taint".
Extraction "taint.hs" pretty_print_taint main.
Extract Constant main => "Prelude.putStrLn pretty_print_SCF".
Extraction "SCF.hs" pretty_print_SCF main.
Extract Constant main => "Prelude.putStrLn pretty_print_SJSFI".
Extraction "SJSFI.hs" pretty_print_SJSFI main.

