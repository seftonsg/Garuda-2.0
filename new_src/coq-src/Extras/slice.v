Set Implicit Arguments.
Unset Strict Implicit.

Require Import List. Import ListNotations.
Require Import ZArith.
Require Import JMeq.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Require Import Integers.

Require Import lang hmac.

(* Function to split a vector of A's into two smaller vectors,
  one of length n, the other of length m (from HMAC_spec.v) *)
Fixpoint splitVector(A : Set)(n m : nat) : Vector.t A (n + m) -> (Vector.t A n * Vector.t A m) :=
  match n with
    | 0 => 
      fun (v : Vector.t A (O + m)) => (@Vector.nil A, v)
    | S n' => 
      fun (v : Vector.t A (S n' + m)) => 
        let (v1, v2) := splitVector (Vector.tl v) in
          (Vector.cons _ (Vector.hd v) _ v1, v2)
  end.

Lemma minus_i_i i : 0 = i-i. omega. Qed.
Lemma plus_i_0 i : i = i+0. omega. Qed.
Lemma minus_i_0 i : i = i-0. omega. Qed.

Definition slice_aux (A:Set) N LO HI (v: Vector.t A (LO + ((HI - LO) + (N - HI)))):
  (Vector.t A LO * (Vector.t A (HI - LO) * Vector.t A (N - HI))) :=
  let (v1, v2) := splitVector v in
  (v1, splitVector v2).

(*AXIOMATIZED SLICING*)

Axiom mk_vec: forall n:nat, Vector.t bvec32 n.

Definition slice N LO HI (v: Vector.t bvec32 N): Vector.t bvec32 (HI - LO) :=
  match eq_nat_dec N (LO + ((HI-LO) + (N-HI))) with
  | left pf =>
    match slice_aux (Vector.cast v pf) with
    | (_, (mid, _)) => mid
    end
  | right _ => mk_vec _
  end.

Lemma vector_cast_elim: forall A n m (pf:n=m) (v:Vector.t A n), JMeq v (Vector.cast v pf).
Proof.
  intros.
  destruct pf.
  induction v; auto.
  simpl.
  rewrite <-IHv; auto.
Qed.  

Lemma slice_empty: forall N (v: Vector.t bvec32 N) i,
  i <= N -> slice i i v = Vector.cast (Vector.nil _) (minus_i_i _).
Proof.
  intros N v i H.
  unfold slice.
  destruct (Nat.eq_dec N _) eqn:H2.
  { destruct (slice_aux _) eqn:H3.
    destruct p.
    clear - t0.
    apply JMeq_eq.
    rewrite <-(@vector_cast_elim _ _ _ (minus_i_i i)).
    assert (H: i - i = 0) by omega.
    revert t0.
    rewrite H.
    destruct t0; auto.
    exfalso.
    omega. }
  omega.
Qed.  

Lemma splitVector_all (A:Set) n (v:Vector.t A n) pf1 :
  exists t, @splitVector _ n 0 (Vector.cast v pf1) = (v, t).
Proof.
  induction v.
  { exists (Vector.nil _); auto. }
  unfold splitVector.
  fold splitVector.
  destruct (splitVector _) eqn:H.
  exists t0.
  f_equal.
  f_equal.
  destruct (IHv (plus_i_0 n)) as [vx Hx].
  revert H Hx.
  simpl.
  generalize (@f_equal nat nat Init.Nat.pred (S n) (S (Init.Nat.add n O)) pf1).
  generalize (plus_i_0 n).
  intros e1 e2.
  assert (e1 = e2) as ->.
  { apply proof_irrelevance. }
  intros ->.
  inversion 1.
  auto.
Qed.  

Lemma splitVector_all' (A:Set) n (v:Vector.t A n) pf1 :
  exists t, @splitVector _ n (n-n) (Vector.cast v pf1) = (v, t).
Proof.
  revert pf1.
  assert (n-n = 0) as -> by omega.
  intros.
  apply splitVector_all.
Qed.  

Lemma slice_all: forall N (v: Vector.t bvec32 N), slice 0 N v = Vector.cast v (minus_n_O _).
Proof.
  intros.
  induction v.
  { simpl. rewrite slice_empty; auto. }
  simpl.
  unfold slice.
  destruct (Nat.eq_dec _ _) eqn:H.
  { simpl.
    destruct (splitVector _) eqn:H2.
    f_equal.
    assert (pf1: Init.Nat.pred (0 + (S n - 0 + (S n - S n))) =
                 Init.Nat.pred (0 + (S n - 0 + (S n - S n))) +
                 (Init.Nat.pred (0 + (S n - 0 + (S n - S n))) -
                  Init.Nat.pred (0 + (S n - 0 + (S n - S n))))).
    { simpl. omega. }
    destruct (splitVector_all' (Vector.cast v (f_equal Init.Nat.pred e)) pf1); eauto.
    simpl in *.
    clear - H0 H2.
    revert H0 H2.
    generalize (f_equal Init.Nat.pred e) as X; intro.
    generalize (@f_equal nat nat Init.Nat.pred (S n) (S n) (minus_n_O (S n))) as Y; intro.
    revert v e t t0 pf1 x X Y.
Admitted.
  
Axiom slice_app_first: forall N1 N2 M (v1: Vector.t bvec32 N1) (v2: Vector.t bvec32 N2) (pf:N1+N2=M),
    @slice M 0 N1 (Vector.cast (Vector.append v1 v2) pf) = Vector.cast v1 (minus_n_O _).

(*AXIOMATIZED ARRAY COPY AND UPDATE OPERATIONS*)
Axiom array_upd_ax: forall
       N y (v:Vector.t (interp_ty TVec32) N)
       (st':forall t, id t -> interp_ty t)
       (pf:forall j : iN N, let s := Fin.to_nat j in proj1_sig (Fin.to_nat j) < N)
       n (yid : id (TArr N TVec32)) (e : id (TArr N TVec32) -> iN N -> Z -> exp TVec32) x,
    st' _ yid = y ->
    (*e's result is independent of x*)
    (forall (st1 st2:forall t, id t -> interp_ty t),
        (forall z, z<>x -> st1 _ z = st2 _ z) -> 
        forall i n, exp_interp st1 (e yid i n) = exp_interp st2 (e yid i n)) -> 
    (*e produces v*)  
    (forall i:iN N, exp_interp st' (e yid i n) = Vector.nth v i) -> 
    stmt_interp st'
     (itern_seq_list (hi:=N) (Fin_list_lo_hi 0 N)
       (fun i : iN N =>
          SUpdate (N:=N) x (Fin.of_nat_lt (pf i)) (e yid i n))) =
    upd (t:=TArr N TVec32) x v st'.

Lemma copy_lem LO HI N: LO <= HI <= N -> LO - 0 + (HI - LO + (N - HI)) = N.
Proof. intros pf. omega. Qed.

Lemma copy_lem2 LO HI N SHIFT:
  SHIFT <= LO -> LO <= HI <= N -> LO - 0 + (HI - SHIFT - (LO - SHIFT) + (N - HI)) = N.
Proof. intros pf. omega. Qed.

Axiom array_copy_ax: forall
  LO HI N M st'
  (to:id (TArr N TVec32)) (from:id (TArr M TVec32)) 
  (pf1: LO <= HI) (pf2: HI <= N)
  (cast_HI_N: forall x, x < HI -> x < N)
  SHIFT (cast_SHIFT_M: forall x, x < HI -> x - SHIFT < M) (pf3: SHIFT <= LO),
  JMeq
    (stmt_interp st'
       (itern_seq_list (hi:=HI) (Fin_list_lo_hi LO HI)
          (fun i : iN HI =>
           let ix := Fin.to_nat i in
           SUpdate (N:=N) to (Fin.of_nat_lt (cast_HI_N (proj1_sig ix) (proj2_sig ix)))
             (EDeref (N:=M) (t:=TVec32) (Fin.of_nat_lt (cast_SHIFT_M (proj1_sig ix) (proj2_sig ix))) from))))
    (upd (t:=TArr N TVec32) to
       (Vector.cast
          (Vector.append (slice 0 LO (st' (TArr N TVec32) to))
             (Vector.append (slice (LO - SHIFT) (HI - SHIFT) (st' (TArr M TVec32) from))
                (slice HI N (st' (TArr N TVec32) to)))) (copy_lem2 pf3 (conj pf1 pf2))) st').
