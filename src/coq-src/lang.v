(* *********************************************************************)
(*                                                                     *)
(*                        Intermediate Language                        *)
(*                         (Nondescript Title)                         *)
(*                                                                     *)
(* *********************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Arith ZArith.
Require Import Vector. 
Require Import String.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.Eqdep.

Require Import Integers.

(* semantics definitions *)
Definition bit := bool.
Definition bvec32 := Int.int.
Definition bvec64 := Int64.int.
Definition bvec64_nil : bvec64 := Int64.zero.

Definition iN (N : nat) := Fin.t N.

Definition arr (N:nat) T := Vector.t T N.
Definition arr_upd N T (a:arr N T) (i:iN N) (v:T) : arr N T :=
  Vector.replace a i v.

(* syntax *)
Inductive ty : Type :=
  | TBit : ty
  | TVec32 : ty  
  | TVec64 : ty
  | TProd : ty -> ty -> ty             
  | TArr : nat -> ty -> ty.

Ltac solve_ty_dec :=
  repeat
    (match goal with
     | |- context[not (?X)] => 
       let x := fresh "x" in intros x
     | [ H : (?T /\ ?T1) |- _ ] => destruct H
     | [ H : ~ (?T /\ ?T1) |- _ ] => destruct H
     | [ H : ?P |- _] => 
       match type of P with
         Prop =>
         repeat
           (match goal with
            | H : ?T |- False =>
              solve [ subst; inversion H]
            end)
       end
     end); auto.

Program Fixpoint ty_dec (t1 t2 : ty) : {t1=t2} + {t1<>t2} :=
  match t1, t2 with
  | TBit, TBit => left eq_refl
  | TVec32, TBit => right _
  | TVec64, TBit => right _
  | TArr _ _, TBit => right _
  | TBit, TVec32 => right _
  | TBit, TVec64 => right _
  | TBit, TArr _ _ => right _
  | TBit, TProd _ _ => right _
  | TVec32, TProd _ _ => right _
  | TVec32, TVec32 => left eq_refl
  | TVec64, TProd _ _ => right _
  | TVec64, TVec64 => left eq_refl
  | TProd t1 t2, TBit => right _
  | TProd t1 t2, TVec32 => right _
  | TProd t1 t2, TVec64 => right _
  | TProd t1 t2, TArr _ _ => right _                                                            
  | TProd t1 t2, TProd t1' t2' =>
    match ty_dec t1 t1' with
    | left pf => match ty_dec t2 t2' with
                 | left pf' => left _
                 | right pf' => right _
                 end
    | right pf => right _
    end
  | TArr n1 t1', TArr n2 t2' =>
    match eq_nat_dec n1 n2 with
    | left pf =>
      match ty_dec t1' t2' with
      | left pf' => left _
      | right pf' => right _
      end
    | right pf => right _
    end
  | TVec32, TVec64 => right _
  | TVec64, TVec32 => right _
  | TVec64, TArr n2 t2' => right _
  | TVec32, TArr n2 t2' => right _                                 
  | TArr n1 t1', TVec64 => right _
  | TArr n1 t1', TVec32  => right _
  | TArr n1 t1', TProd _ _ => right _                                
  end.

Fixpoint interp_ty (t : ty) : Type :=
  match t with
  | TBit => bool  
  | TVec32 => bvec32
  | TVec64 => bvec64
  | TProd t1 t2 => (interp_ty t1 * interp_ty t2)
  | TArr N t2 => arr N (interp_ty t2)
  end.

Definition cast_interp_ty (t1 t2 : ty) (pf : t1=t2)
  : interp_ty t1 -> interp_ty t2 :=
  fun v:interp_ty t1 =>
    match pf in _ = t2 return interp_ty t2 with
    | eq_refl => v
    end.

Lemma cast_interp_ty_elim t (pf: t = t) (v:interp_ty t) :
  cast_interp_ty pf v = v.
Proof.
  unfold cast_interp_ty.
  assert (pf = eq_refl) as ->.
  { apply UIP_refl. }
  auto.
Qed.

Definition id (t : ty) := string.

Inductive binop : Type :=
| OAnd (* and *)
| OXor (* xor *)
| OOr  (*  or *)
| OShr  (* (signed) shift right *)
| OShru (* unsigned shift right *)
| OShl  (*          shift left  *)
| OAddu (* unsigned add *)
| OSubu (* unsigned sub *)
| OEq  (* equality *)
| OLt  (* less than *).


Inductive phiop : Type :=
| OPhiNone (* no change*)
| OPhiSome (m : string). (* A module *)
(* Should I support embedded modules (strings of binops)? *)

(* ***************************************)
(*  Coercions from Inductive to Function *)
(* ***************************************)
Class ScalarTy (t:ty) : Type :=
  mkScalarTy {
      oiszero : interp_ty t -> bool;
      otoz : interp_ty t -> Z;
      ofromz : Z -> interp_ty t;
      onot : interp_ty t -> interp_ty t;
      obinop : binop -> interp_ty t -> interp_ty t -> interp_ty t;
      ophiop : phiop -> interp_ty t -> interp_ty t;
    }.

(*  Bit Type Coercions *)
Instance Bit_ScalarTy : ScalarTy TBit :=
  mkScalarTy
    (fun b:interp_ty TBit => b)
    (fun b:interp_ty TBit => if b then 1%Z else 0%Z)
    (fun z:Z => if Z.eq_dec z 0 then false else true)
    (fun b:interp_ty TBit => negb b)
    (fun o =>
      match o with
      | OAnd => andb
      | OXor => xorb
      | OOr => orb
      | OShr => fun _ _ => false  (*unsupported*)
      | OShru => fun _ _ => false (*unsupported*)
      | OShl => fun _ _ => false  (*unsupported*)
      | OAddu => xorb
      | OSubu => fun _ _ => false (*unsupported*)
      | OEq => fun b1 b2 => negb (xorb b1 b2)
      | OLt => fun b1 b2 => andb (negb b1) b2
      end)
    (fun p =>
      match p with
      | OPhiNone => fun x => x
      | OPhiSome m => fun x => x
      end).

(*  Int32 Type Coercions *)
Instance Int32_ScalarTy : ScalarTy TVec32 :=
  mkScalarTy
    (fun i:interp_ty TVec32 => Int.eq i Int.zero)
    (fun i:interp_ty TVec32 => Int.intval i)
    Int.repr    
    (fun i:interp_ty TVec32 => Int.not i)
    (fun b =>
      match b with
      | OAnd => Int.and
      | OXor => Int.xor
      | OAddu => Int.add
      | OShr => Int.shr
      | OShru => Int.shru
      | OShl => Int.shl
      | OOr => Int.or
      | OSubu => Int.sub
      | OEq => fun v1 v2 => if Int.eq v1 v2 then Int.one else Int.zero
      | OLt => fun v1 v2 => if Int.lt v1 v2 then Int.one else Int.zero
      end)
    (fun p => 
      match p with
      | OPhiNone => fun x => x
      | OPhiSome m => fun x => x
    end).

(*  Int64 Type Coercions *)
Instance Int64_ScalarTy : ScalarTy TVec64 :=
  mkScalarTy
    (fun i:interp_ty TVec64 => Int64.eq i Int64.zero)
    (fun i:interp_ty TVec64 => Int64.intval i)
    Int64.repr    
    (fun i:interp_ty TVec64 => Int64.not i)
    (fun b =>
      match b with
      | OAnd => Int64.and
      | OXor => Int64.xor
      | OAddu => Int64.add
      | OShr => Int64.shr
      | OShru => Int64.shru
      | OShl => Int64.shl
      | OOr => Int64.or
      | OSubu => Int64.sub
      | OEq => fun v1 v2 => if Int64.eq v1 v2 then Int64.one else Int64.zero
      | OLt => fun v1 v2 => if Int64.lt v1 v2 then Int64.one else Int64.zero       
      end)
    (fun p => 
      match p with
      | OPhiNone => fun x => x
      | OPhiSome m => fun x => x
    end).

(*  Prod (Pair) Type Coercions *)
Instance TProd_ScalarTy {t1 t2} `{ScalarTy t1} `{ScalarTy t2} : ScalarTy (TProd t1 t2) := 
  mkScalarTy
    (fun p:interp_ty (TProd t1 t2) => andb (oiszero (fst p)) (oiszero (snd p)))
    (fun p:interp_ty (TProd t1 t2) => 0%Z)
    (fun z => (ofromz z, ofromz z))
    (fun p:interp_ty (TProd t1 t2) => (onot (fst p), onot (snd p)))
    (fun b (p1 p2:interp_ty (TProd t1 t2)) => (obinop b (fst p1) (fst p2), obinop b (snd p1) (snd p2)))
    (fun P (pr:interp_ty (TProd t1 t2)) => (ophiop P (fst pr), ophiop P (snd pr))).
    
Definition arr_iszero {n t} `{ScalarTy t} (a: interp_ty (TArr n t)): bool :=
  fold_left (fun b x => andb b (oiszero x)) true a.

(*  Array Type Coercions *)
Instance TArr_ScalarTy {n t} `{ScalarTy t} : ScalarTy (TArr n t) :=
  mkScalarTy
    (fun a:interp_ty (TArr n t) => fold_left (fun b x => andb b (oiszero x)) true a)
    (fun a:interp_ty (TArr n t) => fold_left (fun z x => (otoz x * z)%Z) 1%Z a)
    (fun z => const (ofromz z) n)
    (fun a:interp_ty (TArr n t) => map onot a)
    (fun b (a1 a2 : interp_ty (TArr n t))
      => map2 (fun x y => obinop b x y) a1 a2)
    (fun P (a : interp_ty (TArr n t))
      => (map (fun x => ophiop P x) a)).

(* ****************************)
(*  Definition of Expressions *)
(* ****************************)
Inductive exp : ty -> Type :=
  | EVal : forall t `{ScalarTy t}, interp_ty t -> exp t
  | EVar : forall t, id t -> exp t
  | EDeref : forall N t (i : iN N), id (TArr N t) -> exp t
  | EBinop : forall t `{ScalarTy t}, binop -> exp t -> exp t -> exp t
  (*| EPhiop : forall t `{ScalarTy t}, phiop -> exp t -> exp t (* Would this be single arg? i.e. obf -> exp t -> exp t *)*)
  | ENot : forall t `{ScalarTy t}, exp t -> exp t
  | EProj1 : forall t1 t2 `{ScalarTy t1} `{ScalarTy t2}, exp (TProd t1 t2) -> exp t1
  | EProj2 : forall t1 t2 `{ScalarTy t1} `{ScalarTy t2}, exp (TProd t1 t2) -> exp t2.

Definition cast_exp (t1 t2: ty) (H:t1=t2): exp t1 -> exp t2 :=
  fun e:exp t1 =>
    match H in _ = t2 return exp t2 with
    | eq_refl => e
    end.

Lemma cast_exp_elim t (pf:t=t) (e:exp t): cast_exp eq_refl e = e.
Proof.
  unfold cast_exp.
  assert (pf = eq_refl) as ->.
  { apply UIP_refl. }
  auto.
Qed.

Inductive stmt : Type :=
  | SAssign : forall t `{ScalarTy t} (x:id t) (e:exp t), stmt
  | SPhi    : forall t `{ScalarTy t} (p : phiop) (x y : id t), stmt
  | SUpdate : forall t `{ScalarTy t} N (x:id (TArr N t)) (i:iN N) (e:exp t), stmt
  | SSeq : stmt -> stmt -> stmt
  | SITE : forall t `{ScalarTy t}, exp t -> stmt -> stmt -> stmt
  | SSkip : stmt.

Definition int32 (z:Z) : interp_ty TVec32 := Int.repr z.
Definition int64 (z:Z) : interp_ty TVec64 := Int64.repr z.

Definition r_rotate32 (x : exp TVec32) (i : exp TVec32) : exp TVec32 :=
  EBinop OOr
         (EBinop OShr x i)
         (EBinop OShl x (EBinop OSubu (EVal (int32 32)) i)).

Definition r_rotate64 (x : exp TVec64) (i : exp TVec64) : exp TVec64 :=
  EBinop OOr (EBinop OShr x i) (EBinop OShl x 
           (EBinop OSubu (EVal (int64 64)) i)).

Inductive var_kind : Type := Local | Input | Output.

Inductive prog : Type :=
  | VDecl : forall t `{ScalarTy t}, var_kind -> id t -> interp_ty t -> prog -> prog
  | ADecl : var_kind -> forall N t, id (TArr N t) -> prog -> prog
  | PStmt : stmt -> prog
  | PSeq : prog -> prog -> prog
  | PDone : prog.

Definition binop_interp t `{ScalarTy t} (op : binop) (v1 v2 : interp_ty t) : interp_ty t :=
  obinop op v1 v2.

(* I feel like this should have something to do with the processing of the exp EVal? *)
Definition phiop_interp t `{ScalarTy t} (p : phiop) (x : interp_ty t) : interp_ty t :=
  ophiop p x.

Section state.
  Definition state := forall t, id t -> interp_ty t.

  Definition upd t (x : id t) (v : interp_ty t) (s : state)
    : state :=
    fun t2 (y : id t2) =>
      match ty_dec t t2 as t' in sumbool _ _ with
      | left pf => 
        match string_dec x y with
        | left pf' => cast_interp_ty pf v
        | right pf' => s t2 y
        end
      | right _ => s t2 y
      end.

  Lemma upd_get_same t (x: id t) (v: interp_ty t) (s: state) :
    upd x v s x = v.
  Proof.
    unfold upd.
    destruct (ty_dec t t) eqn:H; auto.
    { destruct (string_dec x x) eqn:H2.
      apply cast_interp_ty_elim.
      exfalso; apply n; auto. }
    exfalso; apply n; auto.
  Qed.

  Lemma upd_get_other t t0 (x: id t) (y: id t0) (v: interp_ty t) (s: state) :
    x<>y -> 
    upd x v s y = s t0 y.
  Proof.
    unfold upd.
    destruct (ty_dec t t0) eqn:H; auto.
    destruct (string_dec x y) eqn:H2; auto.
    rewrite e0; intros H3; exfalso; apply H3; auto.
  Qed.
  
  Lemma upd_upd t (x: id t) (v1 v2: interp_ty t) (s: state) :
    upd x v1 (upd x v2 s) = upd x v1 s.
  Proof.
    unfold upd.
    apply functional_extensionality_dep; intros tx.
    apply functional_extensionality; intros y.
    destruct (ty_dec t tx); auto.
    destruct (string_dec x y); auto.
  Qed.

  Lemma state_ext (s1 s2: state) :
    (forall t (x:id t), s1 _ x = s2 _ x) ->
    s1=s2.
  Proof.
    intros H.
    apply functional_extensionality_dep.
    intros t.
    apply functional_extensionality.
    intros x.
    rewrite H; auto.
  Qed.    
End state.
  
Section exp_interp.
  Variable s : forall t, id t -> interp_ty t.
  
  Fixpoint exp_interp t `{ScalarTy t} (e : exp t) : interp_ty t := 
    match e as e' in exp t return interp_ty t with 
    | EVal _ _ v => v
    | EVar _ x => s x
    | EDeref _ _ i x => Vector.nth (s x) i
    | EBinop _ _ op e1 e2 =>
      let v1 := exp_interp e1 in
      let v2 := exp_interp e2 in
      binop_interp op v1 v2
    (* Needs two intermediates: varname of module & varname of output *)
    | EPhiop _ _ p x y =>
      let x' := exp_interp x in
      phiop_interp p x'*)
    | ENot _ _ e' => onot (exp_interp e')
    | EProj1 _ _ _ _ e' => fst (exp_interp e')
    | EProj2 _ _ _ _ e' => snd (exp_interp e')                    
    end.
End exp_interp.

Fixpoint enum_iN_rec (n: nat): list nat := 
  match n with
  | O => O :: List.nil
  | S n' => n :: enum_iN_rec n'
  end.

Definition nat_to_iN (N n: nat): iN (S N) :=
  match le_lt_dec (S n) (S N) with 
  | left pf => Fin.of_nat_lt pf
  | right _ => Fin.F1
  end.

Definition enum_iN' (N: nat): list (iN (S N)) :=
  List.map (@nat_to_iN N) (enum_iN_rec N).

Definition enum_iN (N: nat): list (iN N) :=
  match N with
  | O => List.nil
  | S N' => List.map (@nat_to_iN N') (enum_iN_rec N')
  end.

Definition Fin_list_lo_hi lo hi : list (iN hi) :=
  List.filter (fun i => let n := proj1_sig (Fin.to_nat i) in
    (lo <=? n)) (enum_iN hi).

Section itern.
  Variable T: Type.
  Variable t0: T.
  Fixpoint itern hi (l: list (iN hi)) (f: iN hi -> T -> T): T :=
  match l with
  | Datatypes.nil => t0
  | Datatypes.cons hd tl => f hd (itern tl f)
  end.
End itern.

Definition itern_seq_list hi (l : list (iN hi)) (f : iN hi -> stmt) : stmt :=
  @itern stmt SSkip hi l (fun ix s => SSeq s (f ix)).
(*Fixpoint itern_seq_list hi (l : list (iN hi)) (f : iN hi -> stmt) : stmt :=
  match l with
  | Datatypes.nil => SSkip
  | Datatypes.cons hd tl => SSeq (f hd) (itern_seq_list tl f)
  end.*)

Definition SIter lo hi (f : iN hi -> stmt) : stmt :=
  itern_seq_list (Fin_list_lo_hi lo hi) f.

(* Determine if the state needs to be changed *)
Fixpoint stmt_interp (s : state) (c : stmt) : state :=
  match c with
  | SAssign _ _ x e => 
    let v := exp_interp s e in upd x v s
  | SPhi _ _ p x y =>
    let p' := exp_interp s p in upd x p' s
  | SUpdate _ _ t x i e =>
    let v := exp_interp s e in
      upd x (arr_upd (s _ x) i v) s
  | SSeq c1 c2 =>
    stmt_interp (stmt_interp s c1) c2
  | SITE _ _ e c1 c2 =>
    let v := exp_interp s e in
    if oiszero v then stmt_interp s c2
    else stmt_interp s c1
  | SSkip => s
  end.

Lemma fwd_seq s c1 c2: 
  stmt_interp s (SSeq c1 c2) = stmt_interp (stmt_interp s c1) c2.
Proof. reflexivity. Qed.

Lemma fwd_skip s: 
  stmt_interp s SSkip = s.
Proof. reflexivity. Qed.

Lemma fwd_update {T} `{ScalarTy T} N s (x : id (TArr N T)) (i: iN N) e:
  let v := exp_interp s e in 
  stmt_interp s (SUpdate x i e) = upd x (arr_upd (s _ x) i v) s.
Proof. reflexivity. Qed.

Program Fixpoint prog_interp (s : state) (p : prog) : state :=
  match p with
  | VDecl _ _ vk x v p' =>
    prog_interp (upd x v s) p'
  | ADecl vk N t x p' =>
    prog_interp s p'
  | PStmt c => stmt_interp s c
  | PSeq p1 p2 =>
    prog_interp (prog_interp s p1) p2
  | PDone => s
  end.

Lemma fwd_adecl s vk N t x p':
  prog_interp s (@ADecl vk N t x p') = prog_interp s p'.
Proof. reflexivity. Qed.

Lemma fwd_vdecl s t H vk x v p': 
  prog_interp s (@VDecl t H vk x v p') = 
  prog_interp (upd x v s) p'.
Proof. reflexivity. Qed.

Lemma fwd_pseq s p1 p2: 
  prog_interp s (PSeq p1 p2) = prog_interp (prog_interp s p1) p2.
Proof. reflexivity. Qed.

Lemma fwd_pstmt s c: 
  prog_interp s (PStmt c) = stmt_interp s c.
Proof. reflexivity. Qed.

Lemma fwd_done s: 
  prog_interp s PDone = s.
Proof. reflexivity. Qed.

Definition predicate := state -> Prop.

Definition hoare_stmt (P : predicate) (c : stmt) (Q : predicate) : Prop :=
  forall s, P s -> Q (stmt_interp s c).

Definition hoare (P : predicate) (p : prog) (Q : predicate) : Prop :=
  forall s, P s -> Q (prog_interp s p).

Definition is_wp (WP : predicate) (p : prog) (Q : predicate) : Prop :=
  forall P,
    hoare P p Q ->
    (forall s, P s -> WP s).

Fixpoint wp_stmt (c : stmt) (Q : predicate) : predicate :=
  match c with
  | SSkip => Q
  | SAssign _ _ x e => fun s =>
      Q (let v := exp_interp s e in upd x v s)
  | SPhi _ _ p x y => Q
  | SUpdate _ _ t x i e => fun s =>
      Q (let v := exp_interp s e in upd x (arr_upd (s _ x) i v) s)
  | SSeq s1 s2 =>
    let wp_s2 := wp_stmt s2 Q
    in wp_stmt s1 wp_s2
  | SITE _ _ e c1 c2 => fun s =>
    let v := exp_interp s e in
    if oiszero v then wp_stmt c2 Q s
    else wp_stmt c1 Q s
  end.

Lemma wp_stmt_sound c Q : hoare_stmt (wp_stmt c Q) c Q.
Proof.
  unfold hoare_stmt. revert Q.
  induction c; try assumption; simpl; intros; try assumption.
  { remember (wp_stmt c1 Q) as P. apply IHc1 in H. 
    apply IHc2 in H. assumption. }
  destruct (oiszero _) eqn:H1.
  - apply IHc2; auto.
  - apply IHc1; auto.
Qed.

Fixpoint wp (p : prog) (Q : predicate) : predicate :=
  match p with
  | PDone => Q
  | PStmt c => wp_stmt c Q 
  | VDecl _ _ vk x v p' =>
    let Q' := wp p' Q in
    fun s => Q' (upd x v s)
  | ADecl vk N t x p' => wp p' Q
  | PSeq p1 p2 =>
    let wp_p2 := wp p2 Q
    in wp p1 wp_p2
  end.
     
Lemma wp_sound p Q : hoare (wp p Q) p Q.
Proof.
  unfold hoare. generalize Q. induction p; simpl; intros; try auto.
  { unfold prog_interp. fold prog_interp. apply IHp; auto. }
  { unfold prog_interp. fold prog_interp. apply IHp; auto. }
  { apply (wp_stmt_sound H). }
  { remember (wp p2 Q0) as P. apply IHp1 in H.
    rewrite HeqP in H. apply IHp2 in H. assumption. }
Qed. 

Lemma wp_proof (P Q : predicate) p :
  (forall s:state, P s -> wp p Q s) -> hoare P p Q.
Proof.
  intros H s HP; apply (@wp_sound p Q).
  apply (H _ HP).
Qed.
