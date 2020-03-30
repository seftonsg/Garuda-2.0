Set Implicit Arguments.
Unset Strict Implicit.

Require Import List. Import ListNotations.
Require Import ZArith.
Require Import extraction.
Require Import Integers.
Require Import String.
Require Import lang syntax.

Definition h0' : interp_ty TVec32 := Int.repr 1779033703.
Definition h1' : interp_ty TVec32 := Int.repr 3144134277.
Definition h2' : interp_ty TVec32 := Int.repr 1013904242.
Definition h3' : interp_ty TVec32 := Int.repr 2773480762.
Definition h4' : interp_ty TVec32 := Int.repr 1359893119.
Definition h5' : interp_ty TVec32 := Int.repr 2600822924.
Definition h6' : interp_ty TVec32 := Int.repr 528734635.
Definition h7' : interp_ty TVec32 := Int.repr 1541459225.

Definition k (n:nat) : interp_ty TVec32  :=
  match n with
  | 0 => Int.repr 1116352408
  | 1 => Int.repr 1899447441
  | 2 => Int.repr 3049323471
  | 3 => Int.repr 3921009573
  | 4 => Int.repr 961987163
  | 5 => Int.repr 1508970993
  | 6 => Int.repr 2453635748
  | 7 => Int.repr 2870763221
  | 8 => Int.repr 3624381080
  | 9 => Int.repr 310598401
  | 10 => Int.repr 607225278
  | 11 => Int.repr 1426881987
  | 12 => Int.repr 1925078388
  | 13 => Int.repr 2162078206
  | 14 => Int.repr 2614888103
  | 15 => Int.repr 3248222580
  | 16 => Int.repr 3835390401
  | 17 => Int.repr 4022224774
  | 18 => Int.repr 264347078
  | 19 => Int.repr 604807628
  | 20 => Int.repr 770255983
  | 21 => Int.repr 1249150122
  | 22 => Int.repr 1555081692
  | 23 => Int.repr 1996064986
  | 24 => Int.repr 2554220882
  | 25 => Int.repr 2821834349
  | 26 => Int.repr 2952996808
  | 27 => Int.repr 3210313671
  | 28 => Int.repr 3336571891
  | 29 => Int.repr 3584528711
  | 30 => Int.repr 113926993
  | 31 => Int.repr 338241895
  | 32 => Int.repr 666307205
  | 33 => Int.repr 773529912
  | 34 => Int.repr 1294757372
  | 35 => Int.repr 1396182291
  | 36 => Int.repr 1695183700
  | 37 => Int.repr 1986661051
  | 38 => Int.repr 2177026350
  | 39 => Int.repr 2456956037
  | 40 => Int.repr 2730485921
  | 41 => Int.repr 2820302411
  | 42 => Int.repr 3259730800
  | 43 => Int.repr 3345764771
  | 44 => Int.repr 3516065817
  | 45 => Int.repr 3600352804
  | 46 => Int.repr 4094571909
  | 47 => Int.repr 275423344
  | 48 => Int.repr 430227734
  | 49 => Int.repr 506948616
  | 50 => Int.repr 659060556
  | 51 => Int.repr 883997877
  | 52 => Int.repr 958139571
  | 53 => Int.repr 1322822218
  | 54 => Int.repr 1537002063
  | 55 => Int.repr 1747873779
  | 56 => Int.repr 1955562222
  | 57 => Int.repr 2024104815
  | 58 => Int.repr 2227730452
  | 59 => Int.repr 2361852424
  | 60 => Int.repr 2428436474
  | 61 => Int.repr 2756734187
  | 62 => Int.repr 3204031479
  | 63 => Int.repr 3329325298
  | _ => Int.zero (*Shouldn't happen*)
  end.

Open Scope hdl_type_scope.
Open Scope hdl_exp_scope.
Open Scope hdl_stmt_scope.
Open Scope string_scope.

Lemma LessThanB: forall x y j : nat,
  (x < y -> x-j < y).
Proof. 
  intros; induction j; omega.
Qed.

Ltac LessBSolve i l :=
  unfold nat_of_fin;
  destruct (Fin.to_nat i); simpl;
  clear - l;
  apply LessThanB; apply l.

(* Calculate the number of zeroes needed for padding *)
Definition calc_zeroes
  (size : nat)
  : nat :=
  512 - Nat.modulo (size + 65) 512.

(* Calculate the number of chunks the message needs to be broken into *)
(* Will be useful if I implement "preprocessing on the fly" *)
Definition calc_chunks
  (size : nat) (*size in bits*)
  : nat :=
  (size + 1 + 64 + 512) / 512. (* Remember, division rounds down *)

Ltac solve_obligations :=
  match goal with
  | |- context[proj1_sig (Fin.to_nat ?i) < ?n] =>
    destruct (Fin.to_nat i); simpl; omega; auto
  | |- context[?i - _ < _] =>
    unfold nat_of_fin; simpl; apply LessThanB; solve_obligations
  | |- context[?i < _] => omega
  end; auto.                                            
Hint Extern 3 =>
 solve_obligations
: core.

Definition CHUNK: ty := tarr 16<<<tvec32>>>. (*512 bits*)

Program Definition core
        (* inputs *)
        (m : id CHUNK) 
        (w : id (tarr 64<<<tvec32>>>))        
        (h0 h1 h2 h3 h4 h5 h6 h7 : id (tvec32))
        (* local variables *)
        (s0 s1 : id (tvec32))
        (S1 ch temp1 S0 maj temp2 : id (tvec32))
        (a b c d e f g h : id (tvec32))
        (* outputs *)
        (hash : id (tarr 8<<<tvec32>>>))  
  : stmt := 

(* Initialize the values of h0 to h7 *)
h0 <= val h0';; 
h1 <= val h1';;
h2 <= val h2';;
h3 <= val h3';;
h4 <= val h4';;
h5 <= val h5';;
h6 <= val h6';;
h7 <= val h7';;
          
(* Copy chunk into first 16 words of w. *)
syntax.iter 0 16 (fun i => w@'i <- m[[''(i)]]);;

(* Extend the first 16 words into the remaining 48 words w[16..63] of the message schedule array: *)
syntax.iter 16 64 (fun i =>
    s0 <= (w[[''(i-15)]] rightrotate (val (int32 7%Z)))
             xor (w[[''(i-15)]] rightrotate (val (int32 18%Z)))
             xor (w[[''(i-15)]] rightshift (val (int32 3%Z)));;
    s1 <= (w[[''(i-2)]] rightrotate (val (int32 17%Z)))
             xor (w[[''(i-2)]] rightrotate (val (int32 19%Z)))
             xor (w[[''(i-2)]] rightshift (val (int32 10%Z)));;
    w@i <- w[[''(i-16)]] plus (evar s0) plus w[[''(i-7)]] plus (evar s1)
);;

(* Initialize working variables to current hash value: *)
a <= evar h0;;
b <= evar h1;;
c <= evar h2;;
d <= evar h3;;
e <= evar h4;;
f <= evar h5;;
g <= evar h6;;
h <= evar h7;;

(* Compression function main loop: *)
syntax.iter 0 64 (fun i =>
    S1 <= (evar e rightrotate (val (int32 6%Z))) xor (evar e rightrotate (val (int32 11%Z))) xor
          (evar e rightrotate (val (int32 25%Z)));;
    ch <= (evar e and evar f) xor (not (evar e) and evar g);;
    temp1 <= evar h plus evar S1 plus evar ch plus val (k i) plus w[[i]];;
    S0 <= (evar a rightrotate (val (int32 2%Z))) xor (evar a rightrotate (val (int32 13%Z))) xor
          (evar a rightrotate (val (int32 22%Z)));;
    maj <= (evar a and evar b) xor (evar a and evar c) xor (evar b and evar c);;
    temp2 <= (evar S0) plus evar maj;;

    h <= evar g;;
    g <= evar f;;
    f <= evar e;;
    e <= evar d plus evar temp1;;
    d <= evar c;;
    c <= evar b;;
    b <= evar a;;
    a <= evar temp1 plus evar temp2
);;

(* Add the compressed chunk to the current hash value: *)
h0 <= evar h0 plus evar a;;
h1 <= evar h1 plus evar b;;                       
h2 <= evar h2 plus evar c;;
h3 <= evar h3 plus evar d;;                       
h4 <= evar h4 plus evar e;;
h5 <= evar h5 plus evar f;;                      
h6 <= evar h6 plus evar g;;
h7 <= evar h7 plus evar h;;

(* Produce the final hash value (big-endian): *)
hash@''0 <- evar h0;;
hash@''1 <- evar h1;;             
hash@''2 <- evar h2;; 
hash@''3 <- evar h3;;             
hash@''4 <- evar h4;; 
hash@''5 <- evar h5;;             
hash@''6 <- evar h6;; 
hash@''7 <- evar h7.
Next Obligation.
  apply (proj2_sig (Fin.to_nat i)).
Defined.

(* Run just the core compression function *)
Program Definition sha256_aux
  (* inputs *)
  (m : id (tarr 16<<<tvec32>>>))
  (* outputs *)
  (hash : id (tarr 8 <<<tvec32>>>))
  : prog := 

  Local arr "ww" <<<(tarr 64<<<tvec32>>>), 64 >>>;;;

  Local vec "h0" ::== int32 0;;;
  Local vec "h1" ::== int32 0;;;
  Local vec "h2" ::== int32 0;;;      
  Local vec "h3" ::== int32 0;;;      
  Local vec "h4" ::== int32 0;;;
  Local vec "h5" ::== int32 0;;;
  Local vec "h6" ::== int32 0;;;      
  Local vec "h7" ::== int32 0;;;      

  Local vec "s0" ::== int32 0;;;
  Local vec "s1" ::== int32 0;;;

  Local vec "S1" ::== int32 0;;;
  Local vec "ch" ::== int32 0;;;
  Local vec "temp1" ::== int32 0;;;
  Local vec "S0" ::== int32 0;;;
  Local vec "maj" ::== int32 0;;;
  Local vec "temp2" ::== int32 0;;;

  Local vec "a" ::== int32 0;;;
  Local vec "b" ::== int32 0;;;
  Local vec "c" ::== int32 0;;;      
  Local vec "d" ::== int32 0;;;      
  Local vec "e" ::== int32 0;;;
  Local vec "f" ::== int32 0;;;
  Local vec "g" ::== int32 0;;;      
  Local vec "h" ::== int32 0;;;      
  
  (core
    m "ww" "h0" "h1" "h2" "h3" "h4" "h5" "h6" "h7"
    "s0" "s1" "S1" "ch" "temp1" "S0" "maj" "temp2"
    "a" "b" "c" "d" "e" "f" "g" "h"
    hash).  

Definition sha256_core : prog.
  refine (@ADecl Input 16 TVec32 "m" _).
  refine (@ADecl Output 8 TVec32 "hash" _).
  refine (sha256_aux "m" "hash").
Defined.

(* Run the core compression function on a multi-chunk message *)
Program Definition sha256_chunks
  (* inputs *)
  (n : nat)        
  (chunks : id (tarr (16*n) <<<tvec32>>>)) (*n CHUNKS, flattened*)
  (* outputs *)
  (hash : id (tarr 8 <<<tvec32>>>))
  : prog := 

  Local arr "ww" <<<tvec32, 64>>>;;;
  Local arr "chunk" <<<tvec32, 16>>>;;; (*CHUNK*)

  Local vec "h0" ::== int32 0;;;
  Local vec "h1" ::== int32 0;;;
  Local vec "h2" ::== int32 0;;;      
  Local vec "h3" ::== int32 0;;;      
  Local vec "h4" ::== int32 0;;;
  Local vec "h5" ::== int32 0;;;
  Local vec "h6" ::== int32 0;;;      
  Local vec "h7" ::== int32 0;;;
  
  Local vec "s0" ::== int32 0;;;
  Local vec "s1" ::== int32 0;;;
  
  Local vec "S1" ::== int32 0;;;
  Local vec "ch" ::== int32 0;;;
  Local vec "temp1" ::== int32 0;;;
  Local vec "S0" ::== int32 0;;;
  Local vec "maj" ::== int32 0;;;
  Local vec "temp2" ::== int32 0;;;

  Local vec "a" ::== int32 0;;;
  Local vec "b" ::== int32 0;;;
  Local vec "c" ::== int32 0;;;      
  Local vec "d" ::== int32 0;;;      
  Local vec "e" ::== int32 0;;;
  Local vec "f" ::== int32 0;;;
  Local vec "g" ::== int32 0;;;      
  Local vec "h" ::== int32 0;;; 

  syntax.iter 0 n (fun j =>
    (*copy current chunk into "chunk"*)                             
    syntax.iter 0 16 (fun i => "chunk"@i <- chunks[[@nat_to_iN (16*n) (16*j + i)]]);;   
    (*run the core hash function*)
    core "chunk" "ww" "h0" "h1" "h2" "h3" "h4" "h5" "h6" "h7"
         "s0" "s1" "S1" "ch" "temp1" "S0" "maj" "temp2"
         "a" "b" "c" "d" "e" "f" "g" "h" hash).
(*Compute @nat_to_iN (16*(calc_chunks 32*1) - 1) 1.*)
Definition sha256_mult
           (n:nat) (*message size in w32*)
           (m:id (tarr n<<<tvec32>>>))
           (hash:id (tarr 8<<<tvec32>>>)): prog :=
  let num_chunks := calc_chunks (32*n) in
  let padded_size_w32_m1 := 16*num_chunks - 1 in
  let padded_size_w32 := S padded_size_w32_m1 in
  let onebit_idx: iN padded_size_w32 := force n in
  let size_idx: iN padded_size_w32 := force padded_size_w32_m1 in
  Local arr "padded" <<< tvec32, padded_size_w32 >>>;;;
  syntax.iter 0 padded_size_w32 (fun i => "padded"@i <- val (int32 0%Z));;;
  syntax.iter 0 n (fun i => "padded"@i <- "m"[[i]]);;; 
  syntax.iter n padded_size_w32 (fun i => "padded"@i <- val (int32 0%Z));;;
  "padded"@onebit_idx <- val (int32 1%Z) rightrotate val (int32 1%Z);;; (*'1' bit after message*)
  "padded"@size_idx <- val (int32 (Z.of_nat (32*n)));;; (*The message size in bits*)
  sha256_chunks (n:=num_chunks) "padded" hash.

Definition sha256_multn (n:nat) : prog := 
  Input arr "m" <<< tvec32, n >>>;;;
  Output arr "hash" <<< tvec32, 8 >>>;;;
  sha256_mult (n:=n) "m" "hash".

Definition sha256_mult0 : prog := sha256_multn 0.
Definition sha256_mult1 : prog := sha256_multn 1.
Definition sha256_mult16 : prog := sha256_multn 16.
Definition sha256_mult24 : prog := sha256_multn 24.
Definition sha256_mult32 : prog := sha256_multn 32.

