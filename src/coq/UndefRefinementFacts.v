(* TODO: clean up imports *)
From Coq Require Import List String Ascii ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

From Vellvm Require Import
     LLVMAst
     LLVMEvents
     UndefTests
     TopLevel
     Refinement
     TopLevelRefinements
     CFG
     DynamicTypes
     PropT
     Transformations.Traversal.

From Vellvm.Handlers Require Import
     Stack
     Local
     Global.

From ITree Require Import
     ITree
     Basics
     Eq.Eq
     Events.State.

From ExtLib Require Import
     Structures.Monads
     Structures.Maps
     Core.RelDec
     Programming.Eqv.

Import EqvNotation.


Import ITree.Basics.Basics.Monads.

Import MonadNotation.
Import ListNotations.
Import Monads.

Require Import Morphisms.
Require Import Relations.

Import R.
Import TopLevelEnv.
Import IO.
Import D.


(* -------------------------------------------------------- *)
(* Facts about multiplication and undef                     *)
(* -------------------------------------------------------- *)

Theorem undef_refines_mul_undef_undef:
  refine_uvalue (UVALUE_Undef (DTYPE_I 64)) (UVALUE_IBinop (Mul false false) (UVALUE_Undef (DTYPE_I 64)) (UVALUE_Undef (DTYPE_I 64))).
Proof.
  constructor.
  intros dv H.
  apply Concretize_IBinop with (dv1:=DVALUE_I64 one) (dv2:=dv).
  - apply Concretize_Undef. constructor.
  - auto.
  - simpl. inversion H; subst.
    + inversion H0.
    + inversion H1; subst; auto.
      unfold DynamicValues.Int64.mul. unfold DynamicValues.Int64.one.
      replace (DynamicValues.Int64.unsigned (DynamicValues.Int64.repr 1) *
               DynamicValues.Int64.unsigned x) with (DynamicValues.Int64.unsigned x).
      * destruct (Eqv.eqv_dec_p 64%nat 1%nat); rewrite DynamicValues.Int64.repr_unsigned; reflexivity.
      * rewrite Integers.Int64.unsigned_repr; try lia; cbn; try omega.
Qed.

Lemma rel_prime_mod_mul :
  forall a b x,
    Znumtheory.rel_prime a b ->
  exists k, (a * k) mod b = x.
Proof.
Admitted.

Lemma mod_range :
  forall x m, -1 < x mod m < m.
Proof.
Admitted.

Lemma Int64_mul_mod :
  forall a b intrange,
    (DynamicValues.Int64.mul (DynamicValues.Int64.repr a)
                             (DynamicValues.Int64.repr b)) = 
    {| DynamicValues.Int64.intval := ((a * b) mod DynamicValues.Int64.modulus);
       DynamicValues.Int64.intrange := intrange
    |}.
Proof.
Admitted.

Theorem undef_refines_mul_undef_relprime :
  forall a,
    Znumtheory.rel_prime a DynamicValues.Int64.modulus -> 
    refine_uvalue (UVALUE_Undef (DTYPE_I 64))
                  (UVALUE_IBinop (Mul false false)
                                 (UVALUE_Undef (DTYPE_I 64)) (UVALUE_I64 (DynamicValues.Int64.repr a))).
Proof.
  intros a Hrp.
  constructor.
  intros dv H.
  inversion H; subst.
  - inversion H0. 
  - inversion H1; subst; inversion H; subst.
    + inversion H0.
    + destruct x eqn:Hx.
      pose proof rel_prime_mod_mul a DynamicValues.Int64.modulus intval Hrp as Hmod.

      destruct Hmod as [k Hmod].
      rewrite Z.mul_comm in Hmod.

      match goal with
      | [ H : concretize (UVALUE_Undef ?t) ?dv |- concretize (UVALUE_IBinop _ (UVALUE_Undef ?t) (UVALUE_I64 ?v1)) ?dv ]
        => apply Concretize_IBinop with (dv2:=(DVALUE_I64 v1)) (dv1:=DVALUE_I64 (repr k))
      end.
   -- apply Concretize_Undef; constructor.
   -- constructor; reflexivity.
   -- subst; simpl.
      destruct (Eqv.eqv_dec_p 64%nat 1%nat);
        (rewrite (Int64_mul_mod k a intrange); reflexivity).
Qed.

Theorem undef_refines_mul_relprime_undef :
  forall a,
    Znumtheory.rel_prime a DynamicValues.Int64.modulus -> 
    refine_uvalue (UVALUE_Undef (DTYPE_I 64))
                  (UVALUE_IBinop (Mul false false)
                                 (UVALUE_I64 (DynamicValues.Int64.repr a)) (UVALUE_Undef (DTYPE_I 64))).
Proof.
  intros a Hrp.
  constructor.
  intros dv H.
  inversion H; subst.
  - inversion H0. 
  - inversion H1; subst; inversion H; subst.
    + inversion H0.
    + destruct x eqn:Hx.
      pose proof rel_prime_mod_mul a DynamicValues.Int64.modulus intval Hrp as Hmod.

      destruct Hmod as [k Hmod].

    match goal with
    | [ H : concretize (UVALUE_Undef ?t) ?dv |- concretize (UVALUE_IBinop _ (UVALUE_I64 ?v1) (UVALUE_Undef ?t)) ?dv ]
      => apply Concretize_IBinop with (dv1:=(DVALUE_I64 v1)) (dv2:=DVALUE_I64 (repr k))
    end.
   -- constructor; reflexivity.
   -- apply Concretize_Undef; constructor.
   -- subst; simpl.
      destruct (Eqv.eqv_dec_p 64%nat 1%nat);
        (rewrite (Int64_mul_mod a k intrange); reflexivity).
Qed.

Lemma zero_refines_undef :
  refine_uvalue (UVALUE_I64 (DynamicValues.Int64.repr 0)) (UVALUE_Undef (DTYPE_I 64)).
Proof.
  constructor. intros dv H.
  inversion H; subst.
  inversion H0; subst.
  apply Concretize_Undef.
  constructor.
Qed.

Lemma zero_refines_undef_mul_a :
  forall a,
    refine_uvalue (UVALUE_I64 (DynamicValues.Int64.repr 0))
                  (UVALUE_IBinop (Mul false false)
                                 (UVALUE_Undef (DTYPE_I 64)) (UVALUE_I64 a)).
Proof.
  constructor. intros dv H.
  inversion H; subst.
  inversion H0; subst.
  simpl in *.
  clear H0.

  eapply Concretize_IBinop with
      (dv1:=DVALUE_I64 (DynamicValues.Int64.repr 0)).

  apply Concretize_Undef.
  constructor.
  constructor. reflexivity.
Admitted.


Lemma zero_refines_a_mul_undef :
  forall a,
    refine_uvalue (UVALUE_I64 (DynamicValues.Int64.repr 0))
                  (UVALUE_IBinop (Mul false false)
                                 (UVALUE_I64 a) (UVALUE_Undef (DTYPE_I 64))).
Proof.
Admitted.


(* -------------------------------------------------------- *)
(* Facts about undef and bitwise and                        *)
(* -------------------------------------------------------- *)

Theorem undef_refines_and_undef_undef:
  refine_uvalue (UVALUE_Undef (DTYPE_I 64)) (UVALUE_IBinop And (UVALUE_Undef (DTYPE_I 64)) (UVALUE_Undef (DTYPE_I 64))).
Proof.
  constructor.
  intros dv H.
  apply Concretize_IBinop with (dv1:=DVALUE_I64 (DynamicValues.Int64.repr (Z.ones 64))) (dv2:=dv).
  - apply Concretize_Undef. constructor.
  - auto.
  - simpl. inversion H; subst.
    + inversion H0.
    + inversion H1; subst; auto.
      unfold DynamicValues.Int64.and.
      replace (Z.land
                 (DynamicValues.Int64.unsigned
                    (DynamicValues.Int64.repr (Z.ones 64)))
                 (DynamicValues.Int64.unsigned x))
        with (DynamicValues.Int64.unsigned x).
      * destruct (Eqv.eqv_dec_p 64%nat 1%nat); rewrite DynamicValues.Int64.repr_unsigned; reflexivity.
      * rewrite Integers.Int64.unsigned_repr by (cbn; lia).
        rewrite Z.land_comm.
        rewrite Z.land_ones by lia.
        rewrite Z.mod_small. reflexivity.
        
        cbn.
        pose proof DynamicValues.Int64.unsigned_range_2 x.
        cbn in H0.
        lia.
Qed.

(* -------------------------------------------------------- *)
(* Facts about undef and bitwise or                         *)
(* -------------------------------------------------------- *)

Theorem undef_refines_or_undef_undef:
  refine_uvalue (UVALUE_Undef (DTYPE_I 64)) (UVALUE_IBinop Or (UVALUE_Undef (DTYPE_I 64)) (UVALUE_Undef (DTYPE_I 64))).
Proof.
  constructor.
  intros dv H.
  apply Concretize_IBinop with (dv1:=DVALUE_I64 (DynamicValues.Int64.repr 0)) (dv2:=dv).
  - apply Concretize_Undef. constructor.
  - auto.
  - simpl. inversion H; subst.
    + inversion H0.
    + inversion H1; subst; auto.
      unfold DynamicValues.Int64.or.
      replace (Z.lor
                 (DynamicValues.Int64.unsigned
                    (DynamicValues.Int64.repr 0))
                 (DynamicValues.Int64.unsigned x))
        with (DynamicValues.Int64.unsigned x).
      * destruct (Eqv.eqv_dec_p 64%nat 1%nat); rewrite DynamicValues.Int64.repr_unsigned; reflexivity.
      * rewrite Integers.Int64.unsigned_repr by (cbn; lia).
        reflexivity.
Qed.


(* -------------------------------------------------- *)
(* Division and undef facts                           *)
(* -------------------------------------------------- *)

Theorem undef_refines_undef_udiv_1:
    refine_uvalue (UVALUE_Undef (DTYPE_I 64)) (UVALUE_IBinop (UDiv false) (UVALUE_Undef (DTYPE_I 64)) (UVALUE_I64 (DynamicValues.Int64.repr 1))).
Proof.
  constructor.
  intros dv H.
  apply Concretize_IBinop with (dv1:=dv) (dv2:=DVALUE_I64 (DynamicValues.Int64.repr 1)).
  - auto.
  - constructor; reflexivity.
  - inversion H; subst; simpl in *.
    + inversion H0.
    + inversion H1. simpl.
      destruct (DynamicValues.Int64.unsigned (DynamicValues.Int64.repr 1) =?
                0)%Z eqn:Heq.
      inversion Heq.
      simpl.
      rewrite DynamicValues.Int64.divu_one.
      reflexivity.
Qed.

Theorem undef_refines_undef_sdiv_1:
    refine_uvalue (UVALUE_Undef (DTYPE_I 64)) (UVALUE_IBinop (SDiv false) (UVALUE_Undef (DTYPE_I 64)) (UVALUE_I64 (DynamicValues.Int64.repr 1))).
Proof.
  constructor.
  intros dv H.
  apply Concretize_IBinop with (dv1:=dv) (dv2:=DVALUE_I64 (DynamicValues.Int64.repr 1)).
  - auto.
  - constructor; reflexivity.
  - inversion H; subst; simpl in *.
    + inversion H0.
    + inversion H1. simpl.
      destruct (DynamicValues.Int64.signed (DynamicValues.Int64.repr 1) =?
                0)%Z eqn:Heq.
      inversion Heq.
      simpl.
      rewrite DynamicValues.Int64.divs_one.
      reflexivity.
      cbn.
      lia.
Qed.

Theorem zero_refines_undef_urem_1:
    refine_uvalue (UVALUE_I64 (DynamicValues.Int64.repr 0)) (UVALUE_IBinop URem (UVALUE_Undef (DTYPE_I 64)) (UVALUE_I64 (DynamicValues.Int64.repr 1))).
Proof.
  constructor.
  intros dv H. inversion H; subst; inversion H0; subst.
  apply Concretize_IBinop with (dv1:=DVALUE_I64 (DynamicValues.Int64.repr 0)) (dv2:=DVALUE_I64 (DynamicValues.Int64.repr 1)).
  - apply Concretize_Undef. constructor.
  - constructor. reflexivity.
  - simpl.
    destruct (DynamicValues.Int64.unsigned (DynamicValues.Int64.repr 1) =?
              0)%Z eqn:Heq; simpl.
    inversion Heq.

    rewrite Integers.Int64.modu_one. reflexivity.
Qed.

Theorem zero_refines_undef_srem_1:
    refine_uvalue (UVALUE_I64 (DynamicValues.Int64.repr 0)) (UVALUE_IBinop SRem (UVALUE_Undef (DTYPE_I 64)) (UVALUE_I64 (DynamicValues.Int64.repr 1))).
Proof.
  constructor.
  intros dv H. inversion H; subst; inversion H0; subst.
  apply Concretize_IBinop with (dv1:=DVALUE_I64 (DynamicValues.Int64.repr 0)) (dv2:=DVALUE_I64 (DynamicValues.Int64.repr 1)).
  - apply Concretize_Undef. constructor.
  - constructor. reflexivity.
  - simpl.
    destruct (DynamicValues.Int64.signed (DynamicValues.Int64.repr 1) =?
              0)%Z eqn:Heq; simpl.
    inversion Heq.
Admitted.
