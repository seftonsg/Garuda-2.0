(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)
Set Implicit Arguments.


Require Import Bvector.
Require Import List.
Require Import Arith.

Require Import slice.

Arguments splitVector [_] _ _ _.

Definition Blist := list bool.

Module HMAC. Section HMAC.

  Variable c p : nat. (* 32 bytes each, size of hash output and... something else *)
  Definition b := c + p. (* 64 bytes, size of key and constants *)
  
  (* The following block of code defines the hash function.  Wiley's code uses SHA256. *)
  (* The compression function.  Is this the main loop or the processing before it?  Or both? *)
  Variable h : Bvector c -> Bvector b -> Bvector c.
  (* The initialization vector is part of the spec of the hash function. Wiley's is hard-coded. *)
  Variable iv : Bvector c. (* Size is 32 bytes in Wiley's code; initialized as "hashvals" *)
  (* The iteration of the compression function gives a keyed hash function on lists of words. *)
  Definition h_star k (m : list (Bvector b)) :=
    fold_left h m k. (* Reminder: fold_left runs a function (h) on an entire list (m) successively. *)
  (* The composition of the keyed hash function with the IV gives a hash function on lists of words. *)
  Definition hash_words := h_star iv.

  Variable Message : Set.
  (* Function for converting a message variable into a workable list *)
  Variable splitAndPad : Message -> list (Bvector b).
  Hypothesis splitAndPad_1_1 : 
    forall b1 b2,
      splitAndPad b1 = splitAndPad b2 ->
      b1 = b2.
  
  Variable fpad : Bvector c -> Bvector p. 
  (* ...I'm still not actually sure what this function is for *)
  Definition app_fpad (x : Bvector c) : Bvector b :=
    (Vector.append x (fpad x)).

  (* Combination of h_star and app_fpad. *)
  Definition h_star_pad k x :=
    app_fpad (h_star k x).

  (* k and m stand for "key" and "message" respectively.
    In Wiley's code, they're just called "key" and "message". *)
  Definition GNMAC k m :=
    let (k_Out, k_In) := splitVector c c k in
    h k_Out (app_fpad (h_star k_In m)).

  (* The "two-key" version of GHMAC and HMAC. *)
  (* k and m stand for "key" and "message" respectively.
    In Wiley's code, they're just called "key" and "message". *)
  Definition GHMAC_2K (k : Bvector (b + b)) m := (* b = 64 bytes in Wiley's code *)
    let (k_Out, k_In) := splitVector b b k in (* k_Out and k_In = opad and ipad, xor k *)
      let h_in := (hash_words (k_In :: m)) in (* First hash *)
        hash_words (k_Out :: (app_fpad h_in) :: nil). (* Second hash *)
  
  Definition HMAC_2K (k : Bvector (b + b)) (m : Message) :=
    GHMAC_2K k (splitAndPad m).

  (* opad and ipad are constants defined in the HMAC spec. *)
  (* In Wiley's code, these constants are the hex digits
   "5c" and "36", respectively, each repeated 64 times. *)
  Variable opad ipad : Bvector b.
  Hypothesis opad_ne_ipad : opad <> ipad.

  (* Global hash function.  k is the hash key.
    Note that the key is XOR'd with the constants here. *)
  Definition GHMAC (k : Bvector b) :=
    GHMAC_2K (Vector.append (BVxor _ k opad) (BVxor _ k ipad)).

  (* Normal hash function.  k is the hash key.
    Note that the key is XOR'd with the constants here. *)
  Definition HMAC (k : Bvector b) :=
    HMAC_2K (Vector.append (BVxor _ k opad) (BVxor _ k ipad)).

End HMAC. End HMAC.

Require Import lang hmac array.

Module HMAC_Words. Section HMAC_Words.

  (* A version of the above but specialized to 32-bit word vectors. *)

  Variable c p : nat. (* 32 bytes each, size of hash output and... something else *)
  Definition b := c + p. (* 64 bytes, size of key and constants *)

  Definition W := Bvector 32.
  
  (* The following block of code defines the hash function.  Wiley's code uses SHA256. *)
  (* The compression function.  Is this the main loop or the processing before it?  Or both? *)
  Variable h : arr c W  -> arr b W -> arr c W.
  (* The initialization vector is part of the spec of the hash function. Wiley's is hard-coded. *)
  Variable iv : arr c W. (* Size is 32 bytes in Wiley's code; initialized as "hashvals" *)
  (* The iteration of the compression function gives a keyed hash function on lists of words. *)
  Definition h_star k (m : list (arr b W)) :=
    fold_left h m k. (* Reminder: fold_left runs a function (h) on an entire list (m) successively. *)
  (* The composition of the keyed hash function with the IV gives a hash function on lists of words. *)
  Definition hash_words := h_star iv.

  Variable Message : Set.
  (* Function for converting a message variable into a workable list *)
  Variable splitAndPad : Message -> list (arr b W).
  Hypothesis splitAndPad_1_1 : 
    forall b1 b2,
      splitAndPad b1 = splitAndPad b2 ->
      b1 = b2.
  
  Variable fpad : arr c W -> arr p W. 
  (* ...I'm still not actually sure what this function is for *)
  Definition app_fpad (x : arr c W) : arr b W :=
    (Vector.append x (fpad x)).

  (* Combination of h_star and app_fpad. *)
  Definition h_star_pad k x :=
    app_fpad (h_star k x).

  (* k and m stand for "key" and "message" respectively.
    In Wiley's code, they're just called "key" and "message". *)
  Definition GNMAC k m :=
    let (k_Out, k_In) := splitVector c c k in
    h k_Out (app_fpad (h_star k_In m)).

  (* The "two-key" version of GHMAC and HMAC. *)
  (* k and m stand for "key" and "message" respectively.
    In Wiley's code, they're just called "key" and "message". *)
  Definition GHMAC_2K (k : arr (b + b) W) m := (* b = 64 bytes in Wiley's code *)
    let (k_Out, k_In) := splitVector b b k in (* k_Out and k_In = opad and ipad, xor k *)
      let h_in := (hash_words (k_In :: m)) in (* First hash *)
        hash_words (k_Out :: (app_fpad h_in) :: nil). (* Second hash *)
  
  Definition HMAC_2K (k : arr (b + b) W) (m : Message) :=
    GHMAC_2K k (splitAndPad m).

  (* opad and ipad are constants defined in the HMAC spec. *)
  (* In Wiley's code, these constants are the hex digits
   "5c" and "36", respectively, each repeated 64 times. *)
  Variable opad ipad : arr b W.
  Hypothesis opad_ne_ipad : opad <> ipad.

  (* Global hash function.  k is the hash key.
    Note that the key is XOR'd with the constants here. *)
  Definition GHMAC (k : arr b W) :=
    GHMAC_2K (Vector.append (Vector.map2 (BVxor _) k opad)
                            (Vector.map2 (BVxor _) k ipad)).

  (* Normal hash function.  k is the hash key.
    Note that the key is XOR'd with the constants here. *)
  Definition HMAC (k : arr b W) :=
    HMAC_2K (Vector.append (Vector.map2 (BVxor _) k opad)
                           (Vector.map2 (BVxor _) k ipad)).

End HMAC_Words. End HMAC_Words.


