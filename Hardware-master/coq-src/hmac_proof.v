Set Implicit Arguments.
Unset Strict Implicit.

Require Import List. Import ListNotations.
Require Import ZArith.

Require Import Integers.

Require Import lang hmac array.

Section higherlevel_hmac.
  Variables key msg: arr 16 bvec32.
  Variable hash1: arr 32 bvec32 -> arr 8 bvec32.
  Variable hash2: arr 24 bvec32 -> arr 8 bvec32.
  Definition opad_val: bvec32 := Int.repr 1549556828. (*0x5c5c5c5c*)
  Definition ipad_val: bvec32 := Int.repr 909522486. (*0x36363636*)
  Definition opad: arr 16 bvec32 := Vector.const opad_val 16.
  Definition ipad: arr 16 bvec32 := Vector.const ipad_val 16.
  Definition ikeypad: arr 16 bvec32 := arr_map2 Int.xor ipad key.
  Definition ikeypad_msg: arr 32 bvec32 := Vector.append ikeypad msg.
  Definition okeypad: arr 16 bvec32 := arr_map2 Int.xor opad key.
  Definition okeypad_hash: arr 24 bvec32 := Vector.append okeypad (hash1 ikeypad_msg).
  Definition out: arr 8 bvec32 := hash2 okeypad_hash.
End higherlevel_hmac.

Open Scope string_scope.

Section hmac_proof1.
  Variable st: state.
  Variables key msg: arr 16 bvec32.
  Definition key_id: id (TArr 16 TVec32) := "key".
  Definition msg_id: id (TArr 16 TVec32) := "msg".
  Variable st_key: st key_id = key.
  Variable st_msg: st msg_id = msg.
  Variable hash: 
    forall (n:nat)
           (m: id (TArr n TVec32))
           (h: id (TArr 8 TVec32)), prog.
  (*HASH_ASSUMPTION 1: The hash function doesn't overwrite key_id or "okp"*)
  Variable hash_frame1: forall xin (xout:id (TArr 8 TVec32)) st t (y:id t),
    y=key_id \/ y="okp" ->   
    prog_interp st (hash (n:=32) xin xout) (t:=t) y = st _ y.
  (*HASH_ASSUMPTION 1: The hash function produces equal outputs (xout) from initial
    states that agree on the input (xin).*)
  Variable hash_frame2:
    forall
      n (xin: id (TArr n TVec32)) (xout: id (TArr 8 TVec32))
      (st st':forall t, id t -> interp_ty t) (pf: st _ xin = st' _ xin),
    prog_interp st (hash (n:=n) xin xout) (t:=TArr 8 TVec32) xout =
    prog_interp st' (hash (n:=n) xin xout) (t:=TArr 8 TVec32) xout.

  Definition hash1 (m: arr 32 bvec32): arr 8 bvec32 :=
    prog_interp 
      (upd ("fstin": id (TArr 32 TVec32)) m st) 
      (@hash 32 "fstin" "fstot") 
      ("fstot" : id (TArr 8 TVec32)).

 Definition hash2 (m: arr 24 bvec32): arr 8 bvec32 :=
    prog_interp 
      (upd ("sndin": id (TArr 24 TVec32)) m st) 
      (@hash 24 "sndin" "sndot") 
      ("sndot" : id (TArr 8 TVec32)).

 Lemma filter_true T (l: list T) : filter (fun _ => true) l = l.
 Proof.   
   induction l; auto.
   simpl. rewrite IHl; auto.
 Qed.   
 
 Lemma Fin_list_lo_hi_0 n : Fin_list_lo_hi 0 n = enum_iN n.
 Proof.
   unfold Fin_list_lo_hi. unfold enum_iN. induction (enum_iN_rec n); auto.
   simpl. f_equal. rewrite filter_true; auto.
 Qed.
 
 Lemma vector_nth_lem' C (f:bvec32 -> bvec32 -> C) m (i:iN m) n v :
   Vector.nth (arr_map2 (N:=m) f (Vector.const (int32 n) m) v) i =
   f (int32 n) (Vector.nth v i).
 Proof.
   unfold arr_map2; erewrite Vector.nth_map2; eauto.
   rewrite VectorSpec.const_nth; auto.
 Qed.   
 
 Lemma vector_nth_lem i n v :
   Vector.nth (arr_map2 (N:=16) Int.xor (Vector.const (int32 n) 16) v) i =
   Int.xor (Vector.nth v i) (int32 n).
 Proof.
   rewrite vector_nth_lem'.
   apply Int.xor_commut.
 Qed.   
 
 Lemma ikp_ikeypad' (st':forall t:ty, id t -> interp_ty t) n 
   (key_prop: st' (TArr 16 TVec32) key_id = key) :
   stmt_interp
     st'
     (itern_seq_list (hi:=16) (Fin_list_lo_hi 0 16)
                     (fun i : iN 16 =>
                        SUpdate (N:=16) "ikp" (Fin.of_nat_lt (hmac.h_core0_obligation_1 i))
                                (EBinop OXor (EDeref (N:=16) (t:=TVec32) i key_id)
                                        (EVal (int32 n)))))
   = upd (t:=TArr 16 TVec32) "ikp"
         (arr_map2 (N:=16) Int.xor (Vector.const (int32 n) 16) key) st'.
 Proof.
   unfold ikeypad, ipad.
   set (e key_id i n := (EBinop OXor (EDeref (N:=16) (t:=TVec32) i key_id) (EVal (int32 n)))).
   change (stmt_interp st'
    (itern_seq_list (hi:=16) (Fin_list_lo_hi 0 16)
       (fun i : iN 16 =>
          SUpdate (N:=16) "ikp" (Fin.of_nat_lt (hmac.h_core0_obligation_1 i))
                  (e key_id i n))) =
     upd (t:=TArr 16 TVec32) "ikp"
         (arr_map2 (N:=16) Int.xor (Vector.const (int32 n) 16) key) st').
   rewrite (@array_upd_lem_16 key (arr_map2 (N:=16) Int.xor (Vector.const (int32 n) 16) key)); auto.
   { intros st1 st2 H i n0.
     unfold e.
     simpl.
     specialize (H key_id).
     rewrite H; auto.
     inversion 1. }
   intros i; unfold e.
   assert (H: Vector.nth (arr_map2 (N:=16) Int.xor (Vector.const (int32 n) 16) key) i =
              Int.xor (Vector.nth key i) (int32 n)).
   { apply vector_nth_lem. }
   unfold interp_ty, bvec32 in H|-*; rewrite H.
   unfold exp_interp; fold exp_interp; simpl; rewrite key_prop; auto.
  Qed.

 Lemma ikp_ikeypad
    (st':forall t:ty, id t -> interp_ty t)  
    (key_prop: st' (TArr 16 TVec32) key_id = key) :   
   stmt_interp
     st'
     (itern_seq_list (hi:=16) (Fin_list_lo_hi 0 16)
                     (fun i : iN 16 =>
                        SUpdate (N:=16) "ikp" (Fin.of_nat_lt (hmac.h_core0_obligation_1 i))
                                (EBinop OXor (EDeref (N:=16) (t:=TVec32) i key_id)
                                        (EVal (int32 909522486)))))
   = upd (t:=TArr 16 TVec32) "ikp" (ikeypad key) st'.
  Proof. apply ikp_ikeypad'; auto. Qed.
 
  Lemma okp_okeypad' n
    (st':forall t:ty, id t -> interp_ty t)          
    (key_prop: st' (TArr 16 TVec32) key_id = key) :
    stmt_interp
      st' 
      (itern_seq_list
         (hi:=16) (Fin_list_lo_hi 0 16)
         (fun j : iN 16 =>
            SUpdate (N:=16) "okp" (Fin.of_nat_lt (hmac.h_core0_obligation_2 j))
                    (EBinop OXor (EDeref (N:=16) (t:=TVec32) j key_id) (EVal (int32 n)))))
    = upd (t:=TArr 16 TVec32) "okp"
          (arr_map2 (N:=16) Int.xor (Vector.const (Int.repr n) 16) key) st'.
  Proof.
   set (e key_id i n := (EBinop OXor (EDeref (N:=16) (t:=TVec32) i key_id) (EVal (int32 n)))).
   change (stmt_interp st'
    (itern_seq_list (hi:=16) (Fin_list_lo_hi 0 16)
       (fun i : iN 16 =>
          SUpdate (N:=16) "okp" (Fin.of_nat_lt (hmac.h_core0_obligation_1 i))
                  (e key_id i n))) =
     upd (t:=TArr 16 TVec32) "okp"
         (arr_map2 (N:=16) Int.xor (Vector.const (int32 n) 16) key) st').
   rewrite (@array_upd_lem_16 key (arr_map2 (N:=16) Int.xor (Vector.const (int32 n) 16) key)); auto.
   { intros st1 st2 H i n0.
     unfold e.
     simpl.
     specialize (H key_id).
     rewrite H; auto.
     inversion 1. }
   intros i; unfold e.
   assert (H: Vector.nth (arr_map2 (N:=16) Int.xor (Vector.const (int32 n) 16) key) i =
              Int.xor (Vector.nth key i) (int32 n)).
   { apply vector_nth_lem. }
   unfold interp_ty, bvec32 in H|-*; rewrite H.
   unfold exp_interp; fold exp_interp; simpl; rewrite key_prop; auto.
  Qed.

  Lemma okp_okeypad
    (st':forall t:ty, id t -> interp_ty t)          
    (key_prop: st' (TArr 16 TVec32) key_id = key) :
    stmt_interp
      st' 
      (itern_seq_list
         (hi:=16) (Fin_list_lo_hi 0 16)
         (fun j : iN 16 =>
            SUpdate (N:=16) "okp" (Fin.of_nat_lt (hmac.h_core0_obligation_2 j))
                    (EBinop OXor (EDeref (N:=16) (t:=TVec32) j key_id) (EVal (int32 1549556828)))))
    = upd ("okp": id (TArr 16 TVec32)) (okeypad key) st'.
  Proof. apply okp_okeypad'; auto. Qed.

  Lemma fstin_ikeypad_msg (st':forall t:ty, id t -> interp_ty t)
     (pf1: st' _ key_id = key)
     (pf2: st' (TArr 16 TVec32) "ikp" = ikeypad key)
     (pf3: st' (TArr 16 TVec32) msg_id = msg) :    
    stmt_interp
      (stmt_interp
         st'
         (itern_seq_list
            (hi:=16) (Fin_list_lo_hi 0 16)
            (fun i : iN 16 =>
               SUpdate (N:=32) "fstin" (Fin.of_nat_lt (hmac.h_core0_obligation_3 i))
                       (EDeref (N:=16) (t:=TVec32) i "ikp"))))
      (itern_seq_list
         (hi:=32) (Fin_list_lo_hi 16 32)
         (fun j : iN 32 =>
            SUpdate (N:=32) "fstin" (Fin.of_nat_lt (hmac.h_core0_obligation_4 j))
                    (EDeref (N:=16) (t:=TVec32) (Fin.of_nat_lt (hmac.h_core0_obligation_5 j)) msg_id)))
    = upd ("fstin": id (TArr 32 TVec32)) (ikeypad_msg key msg) st'.
  Proof.
    rewrite (@array_copy_first_16 key key_id); auto.
    set (st'' := (upd (t:=TArr 32 TVec32) "fstin"
       (Vector.append (st' (TArr 16 TVec32) "ikp") (last_16 (st' (TArr 32 TVec32) "fstin"))) st')).
    rewrite (@array_copy_last_16 key key_id st'' msg_id "fstin"); auto.
    unfold st''.
    assert (H: (first_16
          (upd (t:=TArr 32 TVec32) "fstin"
             (Vector.append (st' (TArr 16 TVec32) "ikp") (last_16 (st' (TArr 32 TVec32) "fstin"))) st'
             (t0:=TArr 32 TVec32) "fstin")) = st' (TArr 16 TVec32) "ikp").
    { rewrite upd_get_same.
      rewrite first_16_append; auto. }
    rewrite H; unfold ikeypad_msg. 
    assert (H2: (upd (t:=TArr 32 TVec32) "fstin"
     (Vector.append (st' (TArr 16 TVec32) "ikp") (last_16 (st' (TArr 32 TVec32) "fstin"))) st'
     (t0:=TArr 16 TVec32) msg_id) = msg).
    { rewrite upd_get_other; auto.
      unfold msg_id; inversion 1. }
    rewrite H2.
    rewrite pf2.
    rewrite upd_upd; auto.
  Qed.

  Lemma sndin_okeypad_hash :
    let st :=
        prog_interp
          (upd (t:=TArr 32 TVec32) "fstin" (ikeypad_msg key msg)
               (upd (t:=TArr 16 TVec32) "okp" (okeypad key)
                    (upd (t:=TArr 16 TVec32) "ikp" (ikeypad key) st))) (hash (n:=32) "fstin" "fstot")
    in 
    stmt_interp
      (stmt_interp
         st
         (itern_seq_list
            (hi:=16) (Fin_list_lo_hi 0 16)
            (fun i : iN 16 =>
               SUpdate (N:=24) "sndin" (Fin.of_nat_lt (hmac.h_core0_obligation_6 i))
                       (EDeref (N:=16) (t:=TVec32) i "okp"))))
      (itern_seq_list
         (hi:=24) (Fin_list_lo_hi 16 24)
         (fun j : iN 24 =>
            SUpdate (N:=24) "sndin" (Fin.of_nat_lt (hmac.h_core0_obligation_7 j))
                    (EDeref (N:=8) (t:=TVec32) (Fin.of_nat_lt (hmac.h_core0_obligation_8 j)) "fstot")))
    = upd ("sndin": id (TArr 24 TVec32)) (okeypad_hash key msg hash1) st.
  Proof.
    intros st0.
    assert (H: st0 (TArr 16 TVec32) key_id = key).
    { unfold st0. rewrite hash_frame1; auto. }
    rewrite (@array_copy_first_16_24 key key_id st0 "okp" "sndin" H).
    unfold okeypad_hash.
    rewrite (@array_copy_last_8_24 key key_id); auto.
    rewrite upd_upd; auto.
    f_equal.
    f_equal.
    { rewrite upd_get_same.
      rewrite first_16_24_append.
      unfold st0; rewrite hash_frame1; [|right; auto].
      rewrite upd_get_other; [|inversion 1].
      rewrite upd_get_same; auto. }
    rewrite upd_get_other; [|inversion 1].
    unfold st0.
    unfold hash1.
    apply hash_frame2.
    do 2 rewrite upd_get_same; auto.
  Qed.    
  
  Lemma hout_eq :
    stmt_interp
      (prog_interp
         (upd (t:=TArr 24 TVec32) "sndin" (okeypad_hash key msg hash1)
              (prog_interp
                 (upd (t:=TArr 32 TVec32) "fstin" (ikeypad_msg key msg)
                      (upd (t:=TArr 16 TVec32) "okp" (okeypad key)
                           (upd (t:=TArr 16 TVec32)
                                "ikp" (ikeypad key) st))) (hash (n:=32) "fstin" "fstot")))
         (hash (n:=24) "sndin" "sndot"))
      (itern_seq_list
         (hi:=8) (Fin_list_lo_hi 0 8)
         (fun i : iN 8 =>
            SUpdate (N:=8) "hout" (Fin.of_nat_lt (hmac.h_core0_obligation_9 i))
                    (EDeref (N:=8) (t:=TVec32) i "sndot"))) (t:=TArr 8 TVec32) "hout"
    = hash2 (okeypad_hash key msg hash1).
  Proof.
    rewrite array_copy_8.
    unfold hash2.
    unfold okeypad_hash.
    unfold hash1.
    generalize (hash (n:=32) "fstin" "fstot") as HASH1; intro.
    generalize (prog_interp (upd (t:=TArr 32 TVec32) "fstin" (ikeypad_msg key msg) st) HASH1
                            (t:=TArr 8 TVec32) "fstot") as HASH1_ST; intro.
    set (st' := 
    (upd (t:=TArr 24 TVec32) "sndin" (Vector.append (okeypad key) HASH1_ST)
       (prog_interp
          (upd (t:=TArr 32 TVec32) "fstin" (ikeypad_msg key msg)
             (upd (t:=TArr 16 TVec32) "okp" (okeypad key) (upd (t:=TArr 16 TVec32) "ikp" (ikeypad key) st)))
          (hash (n:=32) "fstin" "fstot")))).
    set (st'' := (upd (t:=TArr 24 TVec32) "sndin" (Vector.append (okeypad key) HASH1_ST) st)).
    assert (H: st' (TArr 24 TVec32) "sndin" = st'' _ "sndin").
    { unfold st', st''.
      do 2 rewrite upd_get_same; auto. }
    generalize (@hash_frame2 24 "sndin" "sndot" st' st'' H); auto.
  Qed.    

  Lemma hmac_higherlevel_hmac:
    prog_interp st 
      (h_core0' hash key_id msg_id "hout")  
      ("hout" : id (TArr 8 TVec32)) =
    out key msg hash1 hash2.
  Proof.
    unfold h_core0'.
    unfold h_core0.
    unfold syntax.iter.
    unfold okeypad_hash.
    unfold ikeypad_msg.
    unfold okeypad.
    unfold ikeypad.
    rewrite fwd_adecl.
    rewrite fwd_adecl.
    rewrite fwd_adecl.
    rewrite fwd_adecl.
    rewrite fwd_adecl.
    rewrite fwd_adecl.
    rewrite fwd_adecl.
    rewrite fwd_pseq.
    rewrite fwd_pseq.
    rewrite fwd_pseq.
    rewrite fwd_pseq.
    do 4 rewrite fwd_pstmt.
    do 3 rewrite fwd_pseq.
    do 2 rewrite fwd_pstmt.
    do 2 rewrite fwd_pseq.
    rewrite fwd_pstmt.
    rewrite fwd_done.
    repeat unfold SIter.
    rewrite ikp_ikeypad; auto.
    rewrite okp_okeypad; auto.
    rewrite fstin_ikeypad_msg; auto.
    rewrite sndin_okeypad_hash; auto.
    apply hout_eq.
  Qed.
End hmac_proof1.