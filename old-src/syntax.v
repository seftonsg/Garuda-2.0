Set Implicit Arguments.
Unset Strict Implicit.

Require Import Integers.
Require Import lang.

Declare Scope hdl_type_scope.
Notation "'tbit'" := (TBit) (at level 60) : hdl_type_scope.
Notation "'tvec32'" := (TVec32) (at level 60) : hdl_type_scope.
Notation "'tvec64'" := (TVec64) (at level 60) : hdl_type_scope.
Notation "'tarr' N <<< t >>>" := (TArr N t) (at level 60, right associativity) : hdl_type_scope.
Close Scope hdl_type_scope.

Declare Scope hdl_exp_scope.
Notation "'val' v" := (EVal v) (at level 59) : hdl_exp_scope.
Notation "'var' x" := (EVar x) (at level 59) : hdl_exp_scope.
Notation "e [[ i ]]" := (EDeref i e) (at level 60) : hdl_exp_scope.
Notation "e 'rightrotate' n" := (r_rotate32 e n) (at level 60) : hdl_exp_scope.
Notation "e 'rightshift' n" := (EBinop OShru e n) (at level 60) : hdl_exp_scope.
Notation "e1 'and' e2" := (EBinop OAnd e1 e2) (at level 61) : hdl_exp_scope.
Notation "e1 'xor' e2" := (EBinop OXor e1 e2) (at level 61) : hdl_exp_scope.
Notation "e1 'plus' e2" := (EBinop OAddu e1 e2) (at level 61) : hdl_exp_scope.
Notation "e1 'lt' e2" := (EBinop OLt e1 e2) (at level 61) : hdl_exp_scope.
Notation "'not' e" := (ENot e) (at level 60) : hdl_exp_scope.
Close Scope hdl_exp_scope.

Declare Scope hdl_stmt_scope.
Notation "x <= e" := (SAssign x e) (at level 70) : hdl_stmt_scope. (*TODO: change to ::= to avoid confusion with Verilog nonblocking assignments*)
Definition iter (lo hi:nat) (f:iN hi -> stmt) := @SIter lo hi f.
Arguments iter lo hi f : clear implicits.
Notation "x @ i <- e" := (SUpdate x i e) (at level 70).
Notation "'skip'" := (SSkip) (at level 70).
Infix ";;" := (SSeq) (at level 71).
Close Scope hdl_stmt_scope.

Coercion PSeq : prog >-> Funclass.
Coercion PStmt : stmt >-> prog.
Notation "i 'vec' x ::== v" := (VDecl i x v) (at level 79).
Notation "i 'vec' x <<< t >>> ::== v" := (@VDecl t _ i x v) (at level 79).
Notation "i 'arr' x <<< t , N >>>" := (@ADecl i N t x) (at level 79).
Notation "f ;;; p" := (f p) (at level 80, right associativity, only parsing).
Notation "'done'" := (PDone) (at level 79).

Definition nat2bool (n:nat) : bool :=
  match n with
  | O => false
  | 1 => true
  | _ => false (*bogus*)
  end.

Notation "' i" := (@Fin.of_nat_lt (proj1_sig (Fin.to_nat i)) _ _) (at level 55) : hdl_exp_scope.
Notation "'' m" := (@Fin.of_nat_lt m _ _) (at level 55) : hdl_exp_scope.
Notation "'force' m" := (@nat_to_iN _ m) (at level 55) : hdl_exp_scope.

Require Export ZArith.

Coercion Int.repr : Z >-> Int.int.

Coercion nat_of_fin (N:nat) (x:iN N) : nat := proj1_sig (Fin.to_nat x).

Definition evar (t:ty) (x:id t) : exp t := @EVar t x. Arguments evar {t} x.



