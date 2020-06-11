Set Implicit Arguments.
Unset Strict Implicit.

Require Import List. Import ListNotations.
Require Import ZArith.
Require Import JMeq.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Require Import Integers.

Require Import lang hmac slice.

Definition first_16 (v: Vector.t bvec32 32): Vector.t bvec32 16 := slice 0 16 v.
Definition first_16_24 (v: Vector.t bvec32 24): Vector.t bvec32 16 := slice 0 16 v.
Definition last_16 (v: Vector.t bvec32 32): Vector.t bvec32 16 := slice 16 32 v.
Definition last_8 (v: Vector.t bvec32 24): Vector.t bvec32 8 := slice 16 24 v.

Lemma first_16_append: forall (v1 v2:Vector.t bvec32 16), first_16 (Vector.append v1 v2) = v1.
Proof.
  unfold first_16.
  intros v1 v2.
  generalize (@slice_app_first 16 16 32 v1 v2 eq_refl).
  rewrite <-(@vector_cast_elim _ _ _ (minus_n_O 16)).
  rewrite <-(@vector_cast_elim _ _ _ eq_refl).
  auto.
Qed.

Lemma first_16_24_append: forall (v1:Vector.t bvec32 16) (v2:Vector.t bvec32 8),
    first_16_24 (Vector.append v1 v2) = v1.
Proof.
  unfold first_16_24.
  intros v1 v2.
  generalize (@slice_app_first 16 8 24 v1 v2 eq_refl).
  rewrite <-(@vector_cast_elim _ _ _ (minus_n_O 16)).
  rewrite <-(@vector_cast_elim _ _ _ eq_refl).
  auto.
Qed.

Section arr_map2.
  Variable N: nat.
  Variables A B C: Type.
  Variable c0: C.
  Variable f: A -> B -> C.
  Definition arr_map2 (avec: arr N A) (bvec: arr N B): arr N C := Vector.map2 f avec bvec.
End arr_map2.

Lemma array_upd_lem_16: forall
       y (v:Vector.t (interp_ty TVec32) 16)
       (st':forall t, id t -> interp_ty t)
       (pf:forall j : iN 16, let s := Fin.to_nat j in proj1_sig (Fin.to_nat j) < 16)
       n (yid : id (TArr 16 TVec32)) (e : id (TArr 16 TVec32) -> iN 16 -> Z -> exp TVec32) x,
   st' _ yid = y ->
   (*e's result is independent of x*)
   (forall (st1 st2:forall t, id t -> interp_ty t),
       (forall z, z<>x -> st1 _ z = st2 _ z) -> 
       forall i n, exp_interp st1 (e yid i n) = exp_interp st2 (e yid i n)) -> 
   (forall i:iN 16, exp_interp st' (e yid i n) = Vector.nth v i) -> 
   stmt_interp st'
     (itern_seq_list (hi:=16) (Fin_list_lo_hi 0 16)
       (fun i : iN 16 =>
          SUpdate (N:=16) x (Fin.of_nat_lt (pf i)) (e yid i n))) =
   upd (t:=TArr 16 TVec32) x v st'.
Proof. apply array_upd_ax. Qed.
  
Lemma array_upd_lem_8: forall
       y (v:Vector.t (interp_ty TVec32) 8)
       (st':forall t, id t -> interp_ty t)
       (pf:forall j : iN 8, let s := Fin.to_nat j in proj1_sig (Fin.to_nat j) < 8)
       n (yid : id (TArr 8 TVec32)) (e : id (TArr 8 TVec32) -> iN 8 -> Z -> exp TVec32) x,
   st' _ yid = y ->
   (*e's result is independent of x*)
   (forall (st1 st2:forall t, id t -> interp_ty t),
       (forall z, z<>x -> st1 _ z = st2 _ z) -> 
       forall i n, exp_interp st1 (e yid i n) = exp_interp st2 (e yid i n)) -> 
   (forall i:iN 8, exp_interp st' (e yid i n) = Vector.nth v i) -> 
   stmt_interp st'
     (itern_seq_list (hi:=8) (Fin_list_lo_hi 0 8)
       (fun i : iN 8 =>
          SUpdate (N:=8) x (Fin.of_nat_lt (pf i)) (e yid i n))) =
   upd (t:=TArr 8 TVec32) x v st'.
Proof. apply array_upd_ax. Qed.

Definition Fin_lt_N N (i : iN N) := proj2_sig (Fin.to_nat i).

Lemma eq_JMeq A (x y:A): x=y -> JMeq x y.
Proof.
  intros ->; auto.
Qed.  
  
Lemma Fin_of_nat_ext': forall (p p' n n': nat) (pf1:p=p') (pf2:n=n') (h:p < n) (h':p' < n'),
    JMeq (Fin.of_nat_lt h) (Fin.of_nat_lt h').
Proof.
  intros.
  generalize h h'. subst.
  intros.
  apply eq_JMeq.
  apply Fin.of_nat_ext.
Qed.  

Definition widen_iN N M (i:iN N) (pf:N<=M): iN M :=
  @Fin.of_nat_lt (proj1_sig (Fin.to_nat i)) M (lt_le_trans _ _ _ (@Fin_lt_N N i) pf).

Lemma widen_iN_same N (i:iN N) (pf:N<=N) : widen_iN i pf = i.
Proof.
  unfold widen_iN.
  rewrite <-(@Fin.of_nat_to_nat_inv N i).
  apply JMeq_eq.
  apply Fin_of_nat_ext'; auto.
  rewrite Fin.of_nat_to_nat_inv; auto.
Qed.  

Lemma vector_cast_eq1 A n n1 n2 (v1 v2:Vector.t A n) (pf1:n=n1) (pf2:n=n2) :
  v1 = v2 -> 
  JMeq (Vector.cast v1 pf1) (Vector.cast v2 pf2).
Proof.
  intros ->.
  rewrite <-(@vector_cast_elim _ _ _ pf1).
  rewrite <-(@vector_cast_elim _ _ _ pf2).
  auto.
Qed.  

Lemma vector_cast_eq2 A n n1 n2 (v1:Vector.t A n1) (v2:Vector.t A n2) (pf1:n1=n) (pf2:n2=n) :
  JMeq v1 v2 -> 
  Vector.cast v1 pf1 = Vector.cast v2 pf2.
Proof.
  intros H.
  subst.
  apply JMeq_eq.
  rewrite <-(@vector_cast_elim _ _ _ eq_refl).
  rewrite <-(@vector_cast_elim _ _ _ eq_refl).
  auto.
Qed.  

Lemma vector_app_nilr: forall A n (v:Vector.t A n),
    Vector.append v (Vector.nil _) = Vector.cast v (plus_i_0 n).
Proof.
  intros.
  induction v; auto.
  simpl.
  rewrite IHv.
  f_equal.
  clear IHv.
  apply vector_cast_eq2; auto.
Qed.  
  
Lemma vector_app_nill: forall A n (v:Vector.t A n),
    Vector.append (Vector.nil _) v = Vector.cast v eq_refl.
Proof.
  intros.
  induction v; auto.
  simpl.
  rewrite <-IHv.
  auto.
Qed.

Lemma array_copy_ax1: forall
    LO HI N st' (to:id (TArr N TVec32)) from (pf1: LO <= HI) (pf2: HI <= N),
    JMeq
      (stmt_interp st' 
        (itern_seq_list
         (hi:=HI) (Fin_list_lo_hi LO HI)
         (fun i : iN HI =>
            SUpdate (N:=N) to (widen_iN i pf2)
                    (EDeref (N:=HI) (t:=TVec32) i from))))
      (upd to
           (Vector.cast
              (Vector.append (slice 0 LO (st' _ to))
                             (Vector.append (slice LO HI (st' _ from))
                                            (slice HI N (st' _ to))))
              (copy_lem (conj pf1 pf2)))
           st').
Proof.
  intros.
  set (cast_HI_NX := fun (x:nat) (pf:x<HI) => lt_le_trans _ _ _ pf pf2).
  set (cast_SHIFT_M := fun (x:nat) (pf:x<HI) => @eq_rect _ x (fun x => x<HI) pf (x-0) (minus_i_0 x)).
  assert (pf3: 0 <= LO) by omega.
  generalize (@array_copy_ax LO HI N HI st' to from pf1 pf2 cast_HI_NX 0 cast_SHIFT_M pf3).
  unfold cast_HI_NX, cast_SHIFT_M.
  intros H.
  apply eq_JMeq.
  assert (H2:
            stmt_interp st'
           (itern_seq_list (hi:=HI) (Fin_list_lo_hi LO HI)
              (fun i : iN HI =>
               SUpdate (N:=N) to
                 (Fin.of_nat_lt
                    (Nat.lt_le_trans (proj1_sig (Fin.to_nat i)) HI N (proj2_sig (Fin.to_nat i)) pf2))
                 (EDeref (N:=HI) (t:=TVec32)
                    (Fin.of_nat_lt
                       (eq_rect (proj1_sig (Fin.to_nat i)) (fun x : nat => x < HI)
                          (proj2_sig (Fin.to_nat i)) (proj1_sig (Fin.to_nat i) - 0)
                          (minus_i_0 (proj1_sig (Fin.to_nat i))))) from))) =
         stmt_interp st'
                     (itern_seq_list (hi:=HI) (Fin_list_lo_hi LO HI)
                                     (fun i : iN HI => SUpdate (N:=N) to (widen_iN i pf2) (EDeref (N:=HI) (t:=TVec32) i from)))).
  { f_equal.
    f_equal.
    apply functional_extensionality; intros ix.
    f_equal.
    f_equal.
    rewrite <-(@Fin.of_nat_to_nat_inv HI ix).
    apply JMeq_eq.
    apply Fin_of_nat_ext'; auto.
    rewrite <-minus_i_0.
    f_equal.
    rewrite Fin.of_nat_to_nat_inv; auto. }
  rewrite H2 in H.
  rewrite H.
  f_equal.
  clear H H2.
  clear cast_HI_NX cast_SHIFT_M.
  apply vector_cast_eq2.
  generalize (slice 0 LO (st' (TArr N TVec32) to)); intros v1.
  generalize (slice HI N (st' (TArr N TVec32) to)); intro v2.
  clear - v1 v2.
  revert v1 v2.
  assert (LO - 0 = LO) as -> by omega.
  assert (HI - 0 = HI) as -> by omega.
  auto.
Qed.  

Lemma JMeq_append A N N' M M' (v1:Vector.t A N) (v2:Vector.t A M) (v1':Vector.t A N') (v2':Vector.t A M')
      (pf1:N=N') (pf2:M=M') :
  JMeq v1 v1' ->
  JMeq v2 v2' -> 
  JMeq (Vector.append v1 v2) (Vector.append v1' v2').
Proof.
  intros H1 H2.
  subst N'.
  subst M'.
  rewrite H1, H2.
  auto.
Qed.

Lemma array_copy_end: forall
    LO HI st' (to:id (TArr HI TVec32)) (from:id (TArr HI TVec32)) (pf: LO <= HI),
    JMeq
      (stmt_interp st' 
        (itern_seq_list
         (hi:=HI) (Fin_list_lo_hi LO HI)
         (fun i : iN HI =>
            SUpdate (N:=HI) to (Fin.of_nat_lt (Fin_lt_N i))
                    (EDeref (N:=HI) (t:=TVec32) i from)))
        (t:=(TArr HI) TVec32) to)
      (Vector.append (slice 0 LO (st' _ to)) (slice LO HI (st' _ from))).
Proof.
  intros.
  assert (H1: LO <= HI) by omega.
  assert (H2: HI <= HI) by omega.
  assert (cast_SHIFT_M : forall x : nat, x < HI -> x + 0 < HI).
  { intros. omega. }
  generalize (@array_copy_ax1 LO HI HI st' to from H1 H2).
  rewrite slice_empty; auto.
  generalize (@vector_cast_elim bvec32 0 (HI-HI) (minus_i_i HI) (Vector.nil _)).
  generalize (copy_lem (conj H1 H2)).
  destruct (minus_i_i HI).
  intros e.
  intros <-.
  intros H.
  assert (H3: JMeq
        (stmt_interp st'
           (itern_seq_list (hi:=HI) (Fin_list_lo_hi LO HI)
              (fun i : iN HI => SUpdate (N:=HI) to (widen_iN i H2) (EDeref (N:=HI) (t:=TVec32) i from))))
        (stmt_interp st'
           (itern_seq_list (hi:=HI) (Fin_list_lo_hi LO HI)
                           (fun i : iN HI => SUpdate (N:=HI) to
                                                     (Fin.of_nat_lt (Fin_lt_N (N:=HI) i))
                                                     (EDeref (N:=HI) (t:=TVec32) i from))))).
  { apply eq_JMeq.
    f_equal.
    f_equal.
    apply functional_extensionality; intros x.
    f_equal.
    rewrite widen_iN_same.
    unfold Fin_lt_N.
    rewrite Fin.of_nat_to_nat_inv; auto. }
  rewrite H3 in H.
  rewrite H.
  rewrite upd_get_same.  
  rewrite vector_app_nilr.
  clear H H3.
  generalize (@vector_cast_elim bvec32 (HI-LO) ((HI-LO)+0) (plus_i_0 (HI-LO))
                                (slice LO HI (st' (TArr HI TVec32) from))).
  destruct (plus_i_0 (HI-LO)).
  intros <-.
  destruct e.
  rewrite <-(@vector_cast_elim _ _ _ eq_refl).
  apply JMeq_append; auto.
  { omega. }
  assert (LO - 0 + (HI - LO) = HI) as H3 by omega.
  rewrite H3.
  auto.
Qed.

Lemma Fin_lt_le_N N M (i:Fin.t N) (pf:N<=M) : 
  let s := Fin.to_nat i in proj1_sig (Fin.to_nat i) < M.
Proof. apply (Nat.lt_le_trans _ _ _ (Fin_lt_N i) pf). Qed.

Lemma array_copy_start: forall
    LO HI st' (to:id (TArr HI TVec32)) (from:id (TArr LO TVec32)) (pf: LO <= HI) pf',
    JMeq
      (stmt_interp st' 
        (itern_seq_list
         (hi:=LO) (Fin_list_lo_hi 0 LO)
         (fun i : iN LO =>
            SUpdate (N:=HI) to (Fin.of_nat_lt (Fin_lt_le_N i pf))
                    (EDeref (N:=LO) (t:=TVec32) i from))))
      (upd to (Vector.cast
                 (Vector.append (slice 0 LO (st' _ from)) (slice LO HI (st' _ to)))
                 pf') st').
Proof.
  intros.
  assert (H1: 0 <= LO) by omega.
  assert (H2: LO <= HI) by omega.
  generalize (@array_copy_ax1 0 LO HI st' to from H1 H2).
  intros H.
  assert (H3: JMeq
        (stmt_interp st'
           (itern_seq_list (hi:=LO) (Fin_list_lo_hi 0 LO)
                           (fun i : iN LO => SUpdate (N:=HI) to (widen_iN i H2) (EDeref (N:=LO) (t:=TVec32) i from))))
    (stmt_interp st'
       (itern_seq_list (hi:=LO) (Fin_list_lo_hi 0 LO)
          (fun i : iN LO =>
           SUpdate (N:=HI) to (Fin.of_nat_lt (Fin_lt_le_N i pf)) (EDeref (N:=LO) (t:=TVec32) i from))))).
  { apply eq_JMeq.
    f_equal.
    f_equal.
    apply functional_extensionality; intros x.
    f_equal.
    unfold widen_iN.
    f_equal.
    apply proof_irrelevance. }
  rewrite H3 in H.
  rewrite H.
  clear H3 H.
  rewrite slice_empty; auto. 
  generalize (@vector_cast_elim bvec32 0 (0-0) (minus_i_i 0) (Vector.nil _)).
  intros <-.
  generalize (copy_lem (conj H1 H2)).
  intros e.
  assert (pf' = e) as ->.
  { apply proof_irrelevance. }
  rewrite vector_app_nill.
  rewrite <-(@vector_cast_elim bvec32 _ _ eq_refl).
  auto.
  omega.
Qed.

Lemma array_copy_8: forall st' to from,
    stmt_interp st' 
      (itern_seq_list
         (hi:=8) (Fin_list_lo_hi 0 8)
         (fun i : iN 8 =>
            SUpdate (N:=8) to (Fin.of_nat_lt (hmac.h_core0_obligation_9 i))
                    (EDeref (N:=8) (t:=TVec32) i from))) (t:=TArr 8 TVec32) to =
    st' _ from.
Proof.
  intros.
  assert (H: 8 = 0-0 + (8-0)) by omega.
  generalize hmac.h_core0_obligation_9 as pf.  
  revert to.
  rewrite H.
  intros.
  assert (H2: 0 <= 8) by omega.
  assert (H3: forall i : iN 8, let s := Fin.to_nat i in proj1_sig (Fin.to_nat i) < 8) by auto.  
  generalize (@array_copy_end 0 8 st' to from H2) as H4; intro.
  rewrite slice_empty, slice_all in H4; auto.
  assert (H5: TArr (0 - 0 + (8 - 0)) TVec32 = TArr 8 TVec32).
  { rewrite <-H; auto. }
  assert (H6: st' (TArr (0-0 + (8-0)) TVec32) from =
              Vector.append (Vector.cast (Vector.nil bvec32) (minus_i_i 0))
                            (Vector.cast (st' (TArr 8 TVec32) from) (minus_n_O 8))).
  { simpl; rewrite <-(@vector_cast_elim _ 8 _ (minus_n_O 8)); auto. }
  rewrite H6, <-H4; auto.
Qed. 

Lemma array_copy_first_16: forall
        key (key_id: id (TArr 16 TVec32))
        (st':forall t:ty, id t -> interp_ty t)
        (pf: st' _ key_id = key)
        (from:id (TArr 16 TVec32))
        (to:id (TArr 32 TVec32)),
    stmt_interp
      st'
      (itern_seq_list
         (hi:=16) (Fin_list_lo_hi 0 16)
         (fun i : iN 16 =>
            SUpdate (N:=32) to (Fin.of_nat_lt (hmac.h_core0_obligation_3 i))
                    (EDeref (N:=16) (t:=TVec32) i from))) = 
    upd (t:=TArr 32 TVec32) to (Vector.append (st' _ from) (last_16 (st' _ to))) st'.
Proof.  
  intros.
  assert (H: 16 <= 32) by omega.
  generalize (@array_copy_start 16 32 st' to from H).
  intros H3.
  unfold last_16.
  rewrite slice_all in H3.
  revert H3.
  destruct (minus_n_O 16).
  rewrite <-(@vector_cast_elim _ _ _ eq_refl).
  intros H2.
  assert (H3:
            (itern_seq_list (hi:=16) (Fin_list_lo_hi 0 16)
                            (fun i : iN 16 =>
                               SUpdate (N:=32) to (Fin.of_nat_lt (hmac.h_core0_obligation_3 i))
                                       (EDeref (N:=16) (t:=TVec32) i from))) =
            (itern_seq_list (hi:=16) (Fin_list_lo_hi 0 16)
                            (fun i : iN 16 =>
                               SUpdate (N:=32) to (Fin.of_nat_lt (Fin_lt_le_N i H))
                                       (EDeref (N:=16) (t:=TVec32) i from)))).
  { f_equal.
    apply functional_extensionality; intros x.
    f_equal.
    f_equal.
    apply proof_irrelevance. }
  rewrite H3.
  apply state_ext; intros t x.
  assert (pf': 16+(32-16) = 32) by omega.
  rewrite (H2 pf').
  f_equal.
  clear - pf'.
  rewrite <-(@vector_cast_elim _ _ _ pf'); auto.
Qed.  
                                                                            
Lemma array_copy_first_16_24: forall
        key (key_id: id (TArr 16 TVec32))
        (st':forall t:ty, id t -> interp_ty t)
        (from:id (TArr 16 TVec32))
        (to:id (TArr 24 TVec32))
        (pf: st' _ key_id = key),        
    stmt_interp
      st'
      (itern_seq_list
         (hi:=16) (Fin_list_lo_hi 0 16)
         (fun i : iN 16 =>
            SUpdate (N:=24) to (Fin.of_nat_lt (hmac.h_core0_obligation_6 i))
                    (EDeref (N:=16) (t:=TVec32) i from))) = 
    upd (t:=TArr 24 TVec32) to (Vector.append (st' _ from) (last_8 (st' _ to))) st'.
Proof.
  intros.
  assert (H: 16 <= 24) by omega.
  generalize (@array_copy_start 16 24 st' to from H).
  intros H3.
  unfold last_16.
  rewrite slice_all in H3.
  revert H3.
  destruct (minus_n_O 16).
  rewrite <-(@vector_cast_elim _ _ _ eq_refl).
  intros H2.
  assert (H3:
            (itern_seq_list (hi:=16) (Fin_list_lo_hi 0 16)
                            (fun i : iN 16 =>
                               SUpdate (N:=24) to (Fin.of_nat_lt (hmac.h_core0_obligation_6 i))
                                       (EDeref (N:=16) (t:=TVec32) i from))) =
            (itern_seq_list (hi:=16) (Fin_list_lo_hi 0 16)
                            (fun i : iN 16 =>
                               SUpdate (N:=24) to (Fin.of_nat_lt (Fin_lt_le_N i H))
                                       (EDeref (N:=16) (t:=TVec32) i from)))).
  { f_equal.
    apply functional_extensionality; intros x.
    f_equal.
    f_equal.
    apply proof_irrelevance. }
  rewrite H3.
  apply state_ext; intros t x.
  assert (pf': 16+(24-16) = 24) by omega.
  rewrite (H2 pf').
  f_equal.
  clear - pf'.
  rewrite <-(@vector_cast_elim _ _ _ pf'); auto.
Qed.  
  
Lemma array_copy_last_8_24: forall
        key (key_id: id (TArr 16 TVec32))
        (st':forall t:ty, id t -> interp_ty t)
        (from:id (TArr 8 TVec32))
        (to:id (TArr 24 TVec32))
        (pf: st' _ key_id = key),        
  stmt_interp
    st'   
    (itern_seq_list (hi:=24) (Fin_list_lo_hi 16 24)
       (fun j : iN 24 =>
        SUpdate (N:=24) to (Fin.of_nat_lt (hmac.h_core0_obligation_7 j))
          (EDeref (N:=8) (t:=TVec32) (Fin.of_nat_lt (hmac.h_core0_obligation_8 j)) from))) =
  upd (t:=TArr 24 TVec32) to (Vector.append (first_16_24 (st' _ to)) (st' _ from)) st'.
Proof.
  intros.
  assert (pf1:16<=24) by omega.
  assert (pf2:24<=24) by omega.
  assert (cast_HI_N : forall x : nat, x < 24 -> x < 24) by auto.
  assert (cast_SHIFT_M : forall x : nat, x < 24 -> x - 16 < 8).
  { intros. omega. }
  generalize (@array_copy_ax 16 24 24 8 st' to from pf1 pf2 cast_HI_N 16 cast_SHIFT_M (le_refl _)).
  intros H.
  assert (H2: stmt_interp st'
           (itern_seq_list (hi:=24) (Fin_list_lo_hi 16 24)
              (fun i : iN 24 =>
               let ix := Fin.to_nat i in
               SUpdate (N:=24) to (Fin.of_nat_lt (cast_HI_N (proj1_sig ix) (proj2_sig ix)))
                 (EDeref (N:=8) (t:=TVec32) (Fin.of_nat_lt (cast_SHIFT_M (proj1_sig ix) (proj2_sig ix)))
                         from))) =
              stmt_interp st'
                (itern_seq_list (hi:=24) (Fin_list_lo_hi 16 24)
                  (fun j : iN 24 =>
                   SUpdate (N:=24) to (Fin.of_nat_lt (hmac.h_core0_obligation_7 j))
                           (EDeref (N:=8) (t:=TVec32) (Fin.of_nat_lt (hmac.h_core0_obligation_8 j)) from)))).
  { auto. }
  rewrite H2 in H.
  rewrite H.
  clear H H2.
  f_equal.
  rewrite <-(@vector_cast_elim _ _ _ (copy_lem2 (Nat.le_refl 16) (conj pf1 pf2))).
  unfold first_16_24.
  f_equal.
  rewrite slice_empty; auto.
  rewrite <-(@vector_cast_elim _ _ _ (minus_i_i 24)).
  rewrite vector_app_nilr.
  rewrite <-(@vector_cast_elim _ _ _ (plus_i_0 (24 - 16 - (16-16)))).
  rewrite slice_all.
  rewrite <-(@vector_cast_elim _ _ _ (minus_n_O (24-16))); auto.
Qed.  

Lemma array_copy_last_16: forall
        key (key_id: id (TArr 16 TVec32))
        (st':forall t:ty, id t -> interp_ty t)
        (from:id (TArr 16 TVec32))
        (to:id (TArr 32 TVec32))
        (pf: st' _ key_id = key),        
    stmt_interp
      st'
      (itern_seq_list
         (hi:=32) (Fin_list_lo_hi 16 32)
         (fun j : iN 32 =>
            SUpdate (N:=32) to (Fin.of_nat_lt (hmac.h_core0_obligation_4 j))
                    (EDeref (N:=16) (t:=TVec32)
                            (Fin.of_nat_lt (hmac.h_core0_obligation_5 j))
                            from))) = 
    upd (t:=TArr 32 TVec32) to (Vector.append (first_16 (st' _ to)) (st' _ from)) st'.
Proof.
  intros.
  assert (pf1:16<=32) by omega.
  assert (pf2:32<=32) by omega.
  assert (cast_HI_N : forall x : nat, x < 32 -> x < 32) by auto.
  assert (cast_SHIFT_M : forall x : nat, x < 32 -> x - 16 < 16).
  { intros. omega. }
  generalize (@array_copy_ax 16 32 32 16 st' to from pf1 pf2 cast_HI_N 16 cast_SHIFT_M (le_refl _)).
  intros H.
  assert (H2: stmt_interp st'
           (itern_seq_list (hi:=32) (Fin_list_lo_hi 16 32)
              (fun i : iN 32 =>
               let ix := Fin.to_nat i in
               SUpdate (N:=32) to (Fin.of_nat_lt (cast_HI_N (proj1_sig ix) (proj2_sig ix)))
                 (EDeref (N:=16) (t:=TVec32) (Fin.of_nat_lt (cast_SHIFT_M (proj1_sig ix) (proj2_sig ix)))
                         from))) =
              stmt_interp st'
                (itern_seq_list (hi:=32) (Fin_list_lo_hi 16 32)
                  (fun j : iN 32 =>
                   SUpdate (N:=32) to (Fin.of_nat_lt (hmac.h_core0_obligation_4 j))
                           (EDeref (N:=16) (t:=TVec32) (Fin.of_nat_lt (hmac.h_core0_obligation_5 j)) from)))).
  { auto. }
  rewrite H2 in H.
  rewrite H.
  clear H H2.
  f_equal.
  rewrite <-(@vector_cast_elim _ _ _ (copy_lem2 (Nat.le_refl 16) (conj pf1 pf2))).
  unfold first_16.
  f_equal.
  rewrite slice_empty; auto.
  rewrite <-(@vector_cast_elim _ _ _ (minus_i_i 32)).
  rewrite vector_app_nilr.
  rewrite <-(@vector_cast_elim _ _ _ (plus_i_0 (32 - 16 - (16-16)))).
  rewrite slice_all.
  rewrite <-(@vector_cast_elim _ _ _ (minus_n_O (32-16))); auto.
Qed.  
