Set Implicit Arguments.
Unset Strict Implicit.

Require Import Arith ZArith.
Require Import Vector. 
Require Import String.
Require Import JMeq.
Require Import List. Import ListNotations.

Require Import Integers.

Require Import lang.

Inductive fld : Type :=
  | OpCode
  | Funct
  | Format
  | Rt
  | ImmAddr    
  | TaintBit : Int64.int -> fld
  | OffsetFld : Int64.int -> fld -> fld
  (*OffsetFld i f: Increase offset of f by i bits. OffsetFld is used primarily 
    to test the high-order bits of particular fields, like EffAddr.*)
  | EffAddr
  | PC.                                      

Fixpoint offset (f : fld) : Int64.int :=
  match f with
  | OpCode => Int64.repr 26
  | Funct => Int64.repr 0 
  | Format => Int64.repr 21                         
  | Rt => Int64.repr 11                     
  | ImmAddr => Int64.repr 0 
  | TaintBit off => off
  | OffsetFld i f => Int64.add i (offset f)
  | EffAddr => Int64.repr 32  
  | PC => Int64.repr 0                             
  end.

Fixpoint size (f : fld) : Int64.int :=
  match f with
  | OpCode => Int64.repr 6
  | Funct => Int64.repr 6
  | Format => Int64.repr 5
  | Rt => Int64.repr 5
  | ImmAddr => Int64.repr 26
  | TaintBit _ => Int64.one  (* Taint bits are always size-1 *)
  | OffsetFld _ f => size f
  | EffAddr => Int64.repr 32 
  | PC => Int64.repr 64                        
  end.

Inductive pred {t:ty} : Type :=
  (* Binary Operation of Two Predicates *)
  (* Sum, Product *)
  | BPred : binop -> pred -> pred -> pred
  (* Falsity *)
  | BZero : pred
  (* Negation *)
  | BNeg : pred -> pred
  (* Test *) (* TODO: double check *)
  | BField : fld -> interp_ty t -> pred.

Arguments pred t : clear implicits.

(*BFieldRange f size v: check whether the 'size' higher-order bits of 'fld' equal 'v'*) 
Definition BFieldRange t (f:fld) (i:Int64.int) (v:interp_ty t) : pred t :=
  BField (OffsetFld i f) v.

Inductive pol : ty -> ty -> Type :=
  (* Test *)
  | PTest : forall ity oty `{ScalarTy ity} `{ScalarTy oty}, pred ity -> pol ity oty -> pol ity oty
  (* Update *)
  | PUpd : forall ity oty  `{ScalarTy ity} `{ScalarTy oty}, (exp ity -> exp oty) -> pol ity oty
  (* TODO: nonfunctional, compiles to nothing *)
  | PProj1 : forall ity1 ity2 `{ScalarTy ity1} `{ScalarTy ity2}, pol (TProd ity1 ity2) ity1
  (* TODO: nonfunctional, compiles to nothing *)
  | PProj2 : forall ity1 ity2 `{ScalarTy ity1} `{ScalarTy ity2}, pol (TProd ity1 ity2) ity2
  (* Choice *)
  | PChoice : forall ity oty `{ScalarTy ity} `{ScalarTy oty}, pol ity oty -> pol ity oty -> pol ity oty
  (* Sequential Concatenation *)
  | PConcat : forall ity mty oty  `{ScalarTy ity} `{ScalarTy mty} `{ScalarTy oty},
      pol ity mty -> pol mty oty -> pol ity oty
  (* Skip: compile nothing *)
  | PSkip : forall ity oty `{ScalarTy ity} `{ScalarTy oty}, pol ity oty
  (* Fail: assign a noop *)
  | PFail : forall ity oty `{ScalarTy ity} `{ScalarTy oty}, pol ity oty
  (* Identity *)
  | PId : forall ity `{ScalarTy ity}, pol ity ity.

Record Pol: Type :=
  mkPol {
      ity: ty; ity_ScalarTy: `{ScalarTy ity};
      oty: ty; oty_ScalarTy: `{ScalarTy oty};
      the_pol: pol ity oty
    }.

Fixpoint pred_interp t `{ScalarTy t} (e : pred t) : interp_ty t -> Prop :=
  match e with 
  (* Product *)
  | BPred OAnd e1 e2 => fun v => pred_interp e1 v /\ pred_interp e2 v
  (* Sum *)
  | BPred OOr e1 e2 => fun v => pred_interp e1 v \/ pred_interp e2 v
  (* catch other binops *)
  | BPred _ _ _ => fun _ => False (*other binops are nonboolean*)
  (* Falsity *)
  | BZero => fun _ => False
  (* Negation *)
  | BNeg e2 => fun v => not (pred_interp e2 v)
  (* Test *) (* TODO: double check *)
  | BField f i => fun v =>
                    oiszero
                      (obinop OEq
                              (obinop
                                 OAnd
                                 (obinop OShru v (ofromz (Int64.intval (offset f))))
                                 (obinop OShru
                                         (ofromz 18446744073709551615)
                                         (ofromz (Int64.intval (size f)))))
                              i)
                    = false
  end.

Module PolInterp. Section pol_interp.
  Variable s: forall t, id t -> interp_ty t.

  Fixpoint pol_interp {ity oty} `{ScalarTy ity} `{ScalarTy oty}
           (p: pol ity oty) : interp_ty ity -> interp_ty oty -> Prop :=
    match p with
    (* Test *)
    | PTest _ _ _ _ e p2 => fun v_in v_out => pred_interp e v_in /\ pol_interp p2 v_in v_out
    (* Update *)
    | PUpd _ _ _ _ f => fun v_in v_out => exp_interp s (f (EVal v_in)) = v_out
    (* TODO: nonfunctional, compiles to nothing *)
    | PProj1 _ _ _ _ => fun v_in v_out => fst v_in = v_out
    (* TODO: nonfunctional, compiles to nothing *)
    | PProj2 _ _ _ _ => fun v_in v_out => snd v_in = v_out
    (* Choice *)                                           
    | PChoice _ _ _ _ p1 p2 => fun v_in v_out => pol_interp p1 v_in v_out \/ pol_interp p2 v_in v_out
    (* Sequential Concatenation *)
    | PConcat ity mty oty _ _ _ p1 p2 => fun v_in v_out =>
                             exists v_int:interp_ty mty,
                               pol_interp p1 v_in v_int /\ pol_interp p2 v_int v_out
    (* Skip: compile nothing *)
    | PSkip _ _ _ _ => fun v_in v_out => True
    (* Fail: assign a noop *)
    | PFail _ _ _ _ => fun v_in v_out => False
    (* Identity *)
    | PId _ _ => fun v_in v_out => v_out = v_in
    end.
End pol_interp. End PolInterp.

Section equations.
Variable P: Pol.

Notation ity := P.(ity).
Notation oty := P.(oty).

Definition the_ity_ScalarTy := P.(ity_ScalarTy).
Existing Instance the_ity_ScalarTy.
Definition the_oty_ScalarTy := P.(oty_ScalarTy).
Existing Instance the_oty_ScalarTy.

Notation pol := (pol _ _).
Notation PId := (@PId _ _).

Import PolInterp.

Notation pol_interp s p v_in v_out :=
  (@pol_interp s ity oty the_ity_ScalarTy the_oty_ScalarTy p v_in v_out).

Definition pol_eq (p1 p2 : pol) := 
  forall s v_in v_out,
    pol_interp s p1 v_in v_out <-> pol_interp s p2 v_in v_out.

Infix "===" := (pol_eq) (at level 70).

Lemma concat_idl : forall p: pol, PConcat PId p === p.
Proof.
  intros p; split; simpl.
  { intros [v [-> H]]; auto. }
  intros H.
  exists v_in.
  split; auto.
Qed.

Lemma concat_idr (H:ity=oty) : forall p, PConcat p PId === p.
Proof.
  intros p; split; simpl.
  { intros [v_int [H1 H2]]; auto.
    subst; auto. }
  intros H2; exists v_out; split; auto.
Qed.

Lemma concat_test_id : forall p e,
  PConcat (PTest e PId) p === PTest e p.
Proof.
  intros p e; unfold pol_eq; intros s v_in v_out; split.
  { simpl. 
     intros [v_int [[H1 H2] H3]].
     subst.
     split; auto. }
  simpl.
  intros [H1 H2]; exists v_in.
  split; auto.
Qed.

(*Lemma pupd_id : @PUpd ity oty (fun x => x) === PId eq_refl.
Proof.
  unfold pol_eq; intros s v_in v_out; simpl; split; auto.
Qed.*)

Lemma concat_comp : forall f g,
  (forall s e, 
     exp_interp s (g e) = 
     exp_interp s (g (EVal (exp_interp s e)))) ->
  PConcat (PUpd f) (PUpd g) === PUpd (fun x => g (f x)).
Proof.
  intros f g X; unfold pol_eq; intros s v_in v_out; split.
  { simpl; intros [v_int [H1 H2]].
     rewrite <-H2.
     revert g s X H1 H2.
     generalize (f (EVal v_in)).
     inversion e; intros; subst; auto. }
  simpl; intros H.
  revert g v_out X H.
  generalize (f (EVal v_in)). 
  intros.
  eexists.
  split.
  { specialize (X s e).
     rewrite H in  X. subst. eapply eq_refl. }
  specialize (X s e); rewrite <-H, X; auto.
Qed.

Lemma pol_eq_sym : forall p1 p2, p1 === p2 -> p2 === p1.
Proof.
  intros p1 p2; unfold pol_eq; intros H v1 v2.
  intros v_out.
  rewrite (H v1 v2); split; auto.
Qed.

Lemma choice_failr : forall p, PChoice p PFail === p.
Proof.
  intros p v1 v2; split. 
  { intros [H|H]; [auto|inversion H]. }
  intros; left; auto.
Qed.
End equations.

(* Compile Predicates *)
Fixpoint compile_pred t `{ScalarTy t} (x : id t) (p : pred t) : exp t :=
  match p with
  | BPred op pl pr => EBinop op (compile_pred x pl) (compile_pred x pr)
  | BZero => EVal (ofromz 0)
  | BNeg p' => ENot (compile_pred x p')
  | BField f i => 
    let field_val :=
        EBinop
          OAnd
          (EBinop OShru (EVar x) (EVal (ofromz (Int64.intval (offset f)))))
          (EBinop OShru (EVal (ofromz 18446744073709551615))
                  (EVal (ofromz (Int64.intval (Int64.sub (Int64.repr 64) (size f))))))
    in EBinop OEq field_val (EVal i)
  end.

(* State monad *)
Section M.
  Variable state : Type.

  Definition M (A : Type) := state -> state * A.

  Definition ret (A : Type) (a : A) : M A := fun s => (s, a).

  Definition bind (A B : Type) (m : M A) (f : A -> M B) : M B :=
    fun s =>
      match m s with
      | (s', a) => f a s'
      end.
End M.

(* Variables using decimal integers *)
Inductive digit : Type :=
  Zero | One | Two | Three | Four | Five | Six | Seven | Eight | Nine.

Definition digit2string (d : digit) : string :=
  match d with
  | Zero => "0"
  | One => "1"
  | Two => "2"
  | Three => "3"
  | Four => "4"
  | Five => "5"
  | Six => "6"
  | Seven => "7"
  | Eight => "8"
  | Nine => "9"
  end.

Definition decimal := list digit.

Fixpoint decimal2string (d : decimal) : string :=
  match d with
  | nil => ""
  | x :: d' => append (digit2string x) (decimal2string d')
  end.

Fixpoint nat2decimal_aux (fuel n : nat) (acc : decimal) : decimal :=
  match fuel with
  | O => Zero :: acc
  | S fuel' => 
      match n with
      | 0 => Zero :: acc
      | 1 => One :: acc
      | 2 => Two :: acc
      | 3 => Three :: acc
      | 4 => Four :: acc
      | 5 => Five :: acc
      | 6 => Six :: acc
      | 7 => Seven :: acc
      | 8 => Eight :: acc
      | 9 => Nine :: acc
      | _ =>
        let d := Nat.div n 10 in
        let r := Nat.modulo n 10 in
        nat2decimal_aux fuel' d (nat2decimal_aux fuel' r acc)
      end
  end.
 
 Definition nat2decimal (n : nat) : decimal :=
   nat2decimal_aux n n nil.
 
 Definition nat2string (n : nat) : string := decimal2string (nat2decimal n).

 Definition state := (nat * list string)%type.
 
 Definition new_buf : M state string :=
   fun p =>
     match p with
     | (n, l) =>
       let new_buf := append "internal" (nat2string n) in 
       ((S n, new_buf::l), new_buf)
     end.       
 
 (* Compile Policies *)
 Fixpoint compile_pol
          t1 t2
          `{ScalarTy t1} `{ScalarTy t2}
          (i:id t1) (o:id t2) (p : pol t1 t2) : M state stmt :=
  match p in pol t1 t2 with
  | PTest t1 t2 _ _ test p_cont =>
    let e_test := @compile_pred t1 _ i test
    in bind (@compile_pol t1 t2 _ _ i o p_cont) (fun s_cont =>
       ret (SITE e_test s_cont SSkip))

  | PUpd t1 t2 _ _ f => ret (@SAssign t2 _ o (f (@EVar t1 i)))

  | PProj1 t1 t2 _ _ => ret SSkip (*FIXME*)
  | PProj2 t1 t2 _ _ => ret SSkip (*FIXME*)                                                        

  | PChoice t1 t2 _ _ p1 p2 =>
    bind new_buf (fun o_new1 =>
    bind new_buf (fun o_new2 =>                     
    bind (@compile_pol t1 t2 _ _ i o_new1 p1) (fun s1 =>
    bind (@compile_pol t1 t2 _ _ i o_new2 p2) (fun s2 => 
    ret (SSeq s1 
        (SSeq s2
        (SAssign o
          (EBinop OOr (EVar o_new1) (EVar o_new2)))))))))

  | PConcat t1 t2 t3 _ _ _ p1 p2 =>
    bind new_buf (fun m_new_buf =>
    bind (@compile_pol t1 t2 _ _ i m_new_buf p1) (fun s1 =>
    bind (@compile_pol t2 t3 _ _ m_new_buf o p2) (fun s2 => 
    ret (SSeq s1 s2))))

  | PSkip _ _ _ _ => ret SSkip

  | PFail _ _ _ _ => ret (SAssign o (EVal (ofromz 0)))

  | PId _ _ => ret (@SAssign t1 _ o (EVar i))
  end.

 Fixpoint compile_bufs (bufs : list string) (p : prog) : prog :=
   match bufs with
   | nil => p
   | x::bufs' => VDecl Local x (ofromz 0) (compile_bufs bufs' p)
   end.
 
Section compile.
  Context (ity: ty) `{ScalarTy ity}.
  Context (oty: ty) `{ScalarTy oty}.  
  
  Variable i: id ity.
  Variable o: id oty.
  
  Definition compile (p: pol ity oty): prog :=
    let (state, s) := compile_pol i o p (O, nil) in 
    let output_p := VDecl Input i (ofromz 0) (VDecl Output o (ofromz 0) (PStmt s))
    in match state with
       | (_, bufs) => compile_bufs bufs output_p
       end.
End compile.

Section Compile.
  Variable P: Pol.
  Notation ity := P.(ity).
  Notation oty := P.(oty).

  Definition compile_ity_ScalarTy := P.(ity_ScalarTy).
  Existing Instance compile_ity_ScalarTy.
  Definition compile_oty_ScalarTy := P.(oty_ScalarTy).
  Existing Instance compile_oty_ScalarTy.
  
  Variable i: id ity.
  Variable o: id oty.
  
  Definition Compile: prog := compile i o P.(the_pol).
End Compile.

Section Compile2.
  Variables P1 P2: Pol.
  Variables (i1: id P1.(ity)) (o1: id P1.(oty)).
  Variables (i2: id P2.(ity)) (o2: id P2.(oty)).

  Definition Compile2: prog := PSeq (Compile i1 o1) (Compile i2 o2).
End Compile2.

Section Compile3.
  Variables P1 P2 P3: Pol.
  Variables (i1: id P1.(ity)) (o1: id P1.(oty)).
  Variables (i2: id P2.(ity)) (o2: id P2.(oty)).
  Variables (i3: id P2.(ity)) (o3: id P2.(oty)).  

  Definition Compile3: prog := PSeq (Compile i1 o1) (Compile2 i2 o2 i3 o3).
End Compile3.

Infix "`orpred`" := (BPred OOr) (at level 60).

Fixpoint of_bin_aux (i:Z) (l:list Z): Z :=
  match l with
  | nil => 0
  | z :: l' =>
    if Z.eqb z 0 then of_bin_aux (i+1) l'
    else Z.pow 2 i + of_bin_aux (i+1) l'
  end.

Definition of_bin (l:list Z): Z := of_bin_aux 0 (rev l).

Infix "`andpred`" := (BPred OAnd) (at level 60).

Section MIPS.
  Notation read x := (ofromz (of_bin x)%Z).
  
  (*R-type instructions*)
  Definition R_type := BField OpCode (read [0;0;0;0;0;0]).
  Definition add := R_type `andpred` BField Funct (read [1;0;0;0;0;0]).
  Definition addu := R_type `andpred` BField Funct (read [1;0;0;0;0;1]).
  Definition and := R_type `andpred` BField Funct (read [1;0;0;1;0;0]).
  Definition break := R_type `andpred` BField Funct (read [0;0;1;1;0;1]).
  Definition div := R_type `andpred` BField Funct (read [0;1;1;0;1;0]).
  Definition divu := R_type `andpred` BField Funct (read [0;1;1;0;1;1]).
  Definition jalr := R_type `andpred` BField Funct (read [0;0;1;0;0;1]).
  Definition jr := R_type `andpred` BField Funct (read [0;0;1;0;0;0]).
  Definition mfhi := R_type `andpred` BField Funct (read [0;1;0;0;0;0]).
  Definition mflo := R_type `andpred` BField Funct (read [0;1;0;0;1;0]).
  Definition mthi := R_type `andpred` BField Funct (read [0;1;0;0;0;1]).
  Definition mtlo := R_type `andpred` BField Funct (read [0;1;0;0;1;1]).
  Definition mult := R_type `andpred` BField Funct (read [0;1;1;0;0;0]).
  Definition multu := R_type `andpred` BField Funct (read [0;1;1;0;0;1]). 
  Definition nor := R_type `andpred` BField Funct (read [1;0;0;1;1;1]).
  Definition or := R_type `andpred` BField Funct (read [1;0;0;1;0;1]).
  Definition sll := R_type `andpred` BField Funct (read [0;0;0;0;0;0]).
  Definition sllv := R_type `andpred` BField Funct (read [0;0;0;1;0;0]).
  Definition slt := R_type `andpred` BField Funct (read [1;0;1;0;1;0]).
  Definition sltu := R_type `andpred` BField Funct (read [1;0;1;0;1;1]).
  Definition sra := R_type `andpred` BField Funct (read [0;0;0;0;1;1]).
  Definition srav := R_type `andpred` BField Funct (read [0;0;0;1;1;1]).
  Definition srl := R_type `andpred` BField Funct (read [0;0;0;0;1;0]).
  Definition srlv := R_type `andpred` BField Funct (read [0;0;0;1;1;0]).
  Definition sub := R_type `andpred` BField Funct (read [1;0;0;0;1;0]).
  Definition subu := R_type `andpred` BField Funct (read [1;0;0;0;1;1]).
  Definition syscall := R_type `andpred` BField Funct (read [0;0;1;1;0;0]).
  Definition xor := R_type `andpred` BField Funct (read [1;0;1;1;0;0]).                      

  Definition jump_indirect := jalr `orpred` jr.
  
  (*I-type instructions*)
  Definition addi := BField OpCode (read [0;0;1;0;0;0]).
  Definition addiu := BField OpCode (read [0;0;1;0;0;1]).
  Definition andi := BField OpCode (read [0;0;1;1;0;0]).
  Definition beq := BField OpCode (read [0;0;0;1;0;0]).
  Definition bgez := BField OpCode (read [0;0;0;0;0;1]) `andpred` BField Rt (read [0;0;0;0;1]).
  Definition bgtz := BField OpCode (read [0;0;0;1;1;1]) `andpred` BField Rt (read [0;0;0;0;0]).
  Definition blez := BField OpCode (read [0;0;0;1;1;0]) `andpred` BField Rt (read [0;0;0;0;0]).
  Definition bltz := BField OpCode (read [0;0;0;0;0;1]) `andpred` BField Rt (read [0;0;0;0;0]).  
  Definition bne := BField OpCode (read [0;0;0;1;0;1]).
  Definition lb := BField OpCode (read [1;0;0;0;0;0]).
  Definition lbu := BField OpCode (read [1;0;0;1;0;0]).
  Definition lh := BField OpCode (read [1;0;0;0;0;1]).
  Definition lhu := BField OpCode (read [1;0;0;1;0;1]).
  Definition lui := BField OpCode (read [0;0;1;1;1;1]).
  Definition lw := BField OpCode (read [1;0;0;0;1;1]).
  Definition lwcl := BField OpCode (read [1;1;0;0;0;1]).
  Definition ori := BField OpCode (read [0;0;1;1;0;1]).
  Definition sb := BField OpCode (read [1;0;1;0;0;0]).
  Definition slti := BField OpCode (read [0;0;1;0;1;0]).
  Definition sltiu := BField OpCode (read [0;0;1;0;1;1]).
  Definition sh := BField OpCode (read [1;0;1;0;0;1]).
  Definition sw := BField OpCode (read [1;0;1;0;1;1]).
  Definition swcl := BField OpCode (read [1;1;1;0;0;1]).
  Definition xori := BField OpCode (read [0;0;1;1;1;0]).

  Definition store := sb `orpred` sw.
  
  Definition branch := beq `orpred` bgez `orpred` bgtz `orpred` blez `orpred` bltz `orpred` bne.

  (*J-type instructions*)
  Definition j := BField OpCode (read [0;0;0;0;1;0]).
  Definition jal := BField OpCode (read [0;0;0;0;1;1]).

  Definition jump_direct := j `orpred` jal.
  Definition jump := jump_indirect `orpred` jump_direct.

  Definition ctrl := branch `orpred` jump.

  (*FP instructions*)
  Definition FP_type := BField OpCode (read [0;1;0;0;0;1]).
  Definition add_s :=
    FP_type `andpred` BField Funct (read [0;0;0;0;0;0])
            `andpred` BField Format (read [1;0;0;0;0]).
  Definition cvt_s_w :=
    FP_type `andpred` BField Funct (read [1;0;0;0;0;0])
            `andpred` BField Format (read [1;0;1;0;0]).
  Definition cvt_w_s :=
    FP_type `andpred` BField Funct (read [1;0;0;1;0;0])
            `andpred` BField Format (read [1;0;0;0;0]).
  Definition div_s :=
    FP_type `andpred` BField Funct (read [0;0;0;0;1;1])
            `andpred` BField Format (read [1;0;0;0;0]).
  Definition mfcl :=
    FP_type `andpred` BField Funct (read [0;0;0;0;0;0])
            `andpred` BField Format (read [0;0;0;0;0]).
  Definition mov_s :=
    FP_type `andpred` BField Funct (read [0;0;0;1;1;0])
            `andpred` BField Format (read [1;0;0;0;0]).
  Definition mtcl :=
    FP_type `andpred` BField Funct (read [0;0;0;0;0;0])
            `andpred` BField Format (read [0;0;1;0;0]).
  Definition mul_s :=
    FP_type `andpred` BField Funct (read [0;0;0;0;1;0])
            `andpred` BField Format (read [1;0;0;0;0]).
  Definition sub_s :=
    FP_type `andpred` BField Funct (read [0;0;0;0;0;1])
            `andpred` BField Format (read [0;0;0;0;1]).
End MIPS.

Require Import syntax.

Notation "'`IF`' e '`THEN`' p1 '`ELSE`' p2" :=
  (PChoice (PTest e p1) (PTest (BNeg e) p2)) (at level 101).

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

(*Section thesis_example.
  Definition KernelPC := BFieldRange (ofromz 8191 (*0x0FFF*)
*)
Require Import extraction.

(* print the program *)

Definition i : id TVec64 := "i".
Definition o : id TVec64 := "o".
Definition ri : id TVec64 := "ri".
Definition ro : id TVec64 := "ro".

Definition sec_jmp_compiled : prog := compile i o sec_jmp.
Definition SFI_compiled : prog := compile ri ro sfi.

Definition sec_jmp_sfi : prog := compile i o (PConcat sec_jmp sfi).
Opaque sec_jmp.
Opaque sfi.

Definition taint_i: id TaintTy := "ti".
Definition taint_o: id TBit := "to".
Definition taint_compiled : prog := compile taint_i taint_o taint.

Definition scf_compiled : prog := compile i o scf.

Definition pretty_print_sec_jmp :=
  pretty_print_tb "secjmp" sec_jmp_compiled.
Definition pretty_print_SFI :=
  pretty_print_tb "SFI" SFI_compiled.
Definition pretty_print_taint := 
  pretty_print_tb "taint" taint_compiled.
Definition pretty_print_SCF := 
  pretty_print_tb "SCF" scf_compiled.

(* run the program 'secjmp.hs' and pipe to a file to get verilog *)
Extract Constant main => "Prelude.putStrLn pretty_print_sec_jmp".
Extraction "secjmp.hs" pretty_print_sec_jmp main.
Extract Constant main => "Prelude.putStrLn pretty_print_SFI".
Extraction "SFI.hs" pretty_print_SFI main.
Extract Constant main => "Prelude.putStrLn pretty_print_taint".
Extraction "taint.hs" pretty_print_taint main.
Extract Constant main => "Prelude.putStrLn pretty_print_SCF".
Extraction "SCF.hs" pretty_print_SCF main.


