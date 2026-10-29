(** * I2F invariant for the pure annotation checks of [Semantics/Attributes.v]

    Each pure check is an [EOU] computation; related inputs give related
    results ([I2F_EOU]), which [I2F_denotation.v] lifts into the itree
    semantics with [I2F_refine_lift'].  The checks that read memory
    (section [MemoryChecks]) are itrees, and their lemmas are in
    [I2F_denotation.v]. *)

From Stdlib Require Import Lia Program.

From ExtLib Require Import Structures.Monads.

From ITree Require Import
  HeterogeneousRelations.

From Vellvm Require Import
  Utils
  Syntax
  Semantics
  VellvmIntegers
  Integers
  Interfaces.IPtr
  Interfaces.Params
  Implementations.Pointer
  Implementations.Provenance
  Implementations.IPtrInfinite
  Implementations.IPtrFinite
  Implementations.ParamsV.

From Vellvm Require Import
  Theory.I2F.Refinement
  Theory.I2F.I2F_exp.

Import MonadNotation.
Open Scope monad_scope.

(** The explicit-alignment checks: related pointers are aligned alike
    ([I2F_Addr_ptr_aligned_to]), so both sides continue, or the infinite
    side raises UB. *)
Lemma I2F_assert_aligned_to a1 a2 align msg :
  I2F_dvalue a1 a2 ->
  I2F_EOU (fun _ _ => True)
    (@assert_aligned_to PInf a1 align msg) (@assert_aligned_to PFin a2 align msg).
Proof.
  intros H; unfold assert_aligned_to.
  inv H; [inv H0 | |]; cbn; try now constructor.
  break_match_goal; [ | now constructor].
  (* The two conditions differ in hidden instance arguments, so equate
     them by [apply] (up to conversion) rather than rewriting. *)
  match goal with
  | |- I2F_EOU _ (if ?b1 then _ else _) (if ?b2 then _ else _) =>
      assert (EQ : b1 = b2) by (apply I2F_Addr_ptr_aligned_to; assumption);
      rewrite EQ; destruct b2
  end; now constructor.
Qed.

Lemma I2F_assert_alignment a1 a2 anns msg :
  I2F_dvalue a1 a2 ->
  I2F_EOU (fun _ _ => True)
    (@assert_alignment PInf a1 anns msg) (@assert_alignment PFin a2 anns msg).
Proof. apply I2F_assert_aligned_to. Qed.

(** Value attributes.  Each poison-producing stage keeps related values
    related: both sides test the same address or the same integer. *)
Lemma I2F_value_attr_nonnull attrs v1 v2 :
  I2F_dvalue v1 v2 ->
  I2F_dvalue (@value_attr_nonnull PInf attrs v1) (@value_attr_nonnull PFin attrs v2).
Proof.
  intros H; pose proof H as H'; unfold value_attr_nonnull.
  inv H; [inv H0 | |]; cbn; auto.
  match goal with
  | |- I2F_dvalue (if ?b1 then _ else _) (if ?b2 then _ else _) =>
      assert (EQ : b1 = b2)
        by (f_equal; destruct p, p'; destruct H as [HI ->]; red in HI; subst; reflexivity);
      rewrite EQ; destruct b2; auto
  end.
Qed.

Lemma I2F_value_attr_align attrs v1 v2 :
  I2F_dvalue v1 v2 ->
  I2F_dvalue (@value_attr_align PInf attrs v1) (@value_attr_align PFin attrs v2).
Proof.
  intros H; pose proof H as H'; unfold value_attr_align.
  inv H; [inv H0 | |]; cbn; auto.
  break_match_goal; auto.
  match goal with
  | |- I2F_dvalue (if ?b1 then _ else _) (if ?b2 then _ else _) =>
      assert (EQ : b1 = b2) by (apply I2F_Addr_ptr_aligned_to; exact H);
      rewrite EQ; destruct b2; auto
  end.
Qed.

Lemma I2F_value_attr_range attrs v1 v2 :
  I2F_dvalue v1 v2 ->
  I2F_dvalue (@value_attr_range PInf attrs v1) (@value_attr_range PFin attrs v2).
Proof.
  intros H; pose proof H as H'; unfold value_attr_range.
  inv H; [inv H0 | |]; cbn; auto.
  repeat break_match_goal; auto.
Qed.

(** [nofpclass]: related floats are equal, so both sides test the same
    class, element by element. *)
Lemma I2F_fp_class b1 b2 :
  I2F_dvalue_base b1 b2 -> @fp_class PInf b1 = @fp_class PFin b2.
Proof. intros H; inversion H; subst; cbn; auto. Qed.

Lemma I2F_value_nofpclass mask v1 v2 :
  I2F_dvalue v1 v2 ->
  I2F_dvalue (@value_nofpclass PInf mask v1) (@value_nofpclass PFin mask v2).
Proof.
  induction 1 as [b1 b2 HB | p s1 s2 F IH | vec s1 s2 F IH] using I2F_dvalue_ind; cbn.
  - rewrite (I2F_fp_class HB).
    destruct (@fp_class PFin b2); [| constructor; auto].
    destruct (Z.land mask z =? 0)%Z; repeat constructor; auto.
  - constructor; induction IH; cbn; constructor; auto; inv F; auto.
  - constructor; induction IH; cbn; constructor; auto; inv F; auto.
Qed.

Lemma I2F_value_attr_nofpclass attrs v1 v2 :
  I2F_dvalue v1 v2 ->
  I2F_dvalue (@value_attr_nofpclass PInf attrs v1) (@value_attr_nofpclass PFin attrs v2).
Proof.
  intros H; unfold value_attr_nofpclass.
  destruct (find_option attr_nofpclass attrs); auto using I2F_value_nofpclass.
Qed.

Lemma I2F_value_attrs_poison attrs v1 v2 :
  I2F_dvalue v1 v2 ->
  I2F_dvalue (@value_attrs_poison PInf attrs v1) (@value_attrs_poison PFin attrs v2).
Proof.
  intros H; unfold value_attrs_poison.
  apply I2F_value_attr_nofpclass, I2F_value_attr_range, I2F_value_attr_align,
    I2F_value_attr_nonnull, H.
Qed.

(** Applying value attributes: related values give the same [noundef]
    verdict ([I2F_dvalue_well_defined]), so both sides pass on related
    values, or the infinite side raises UB. *)
Lemma I2F_apply_value_attrs attrs msg v1 v2 :
  I2F_dvalue v1 v2 ->
  I2F_EOU I2F_dvalue
    (@apply_value_attrs PInf attrs msg v1) (@apply_value_attrs PFin attrs msg v2).
Proof.
  intros H; unfold apply_value_attrs; cbv zeta.
  pose proof (I2F_value_attrs_poison attrs H) as HP.
  match goal with
  | |- I2F_EOU _ (if ?b1 then _ else _) (if ?b2 then _ else _) =>
      assert (EQ : b1 = b2)
        by (f_equal; f_equal; apply I2F_dvalue_well_defined; exact HP);
      rewrite EQ; destruct b2
  end; now constructor.
Qed.

(** Load and call metadata [!range]: both sides test the same integer,
    lane by lane for vectors. *)
Lemma I2F_value_metadata_range_base rs v1 v2 :
  I2F_dvalue v1 v2 ->
  I2F_dvalue (@value_metadata_range_base PInf rs v1) (@value_metadata_range_base PFin rs v2).
Proof.
  intros H; pose proof H as H'; unfold value_metadata_range_base.
  inv H; [inv H0 | |]; cbn; auto.
  repeat break_match_goal; auto.
Qed.

Lemma I2F_value_metadata_range r v1 v2 :
  I2F_dvalue v1 v2 ->
  I2F_dvalue (@value_metadata_range PInf r v1) (@value_metadata_range PFin r v2).
Proof.
  intros H.
  destruct r as [rs|]; cbn; auto.
  inversion H; subst; try (apply I2F_value_metadata_range_base; auto).
  destruct v; [| apply I2F_value_metadata_range_base; auto].
  constructor.
  match goal with
  | HF : Forall2 I2F_dvalue _ _ |- _ =>
      induction HF; cbn; constructor; auto using I2F_value_metadata_range_base
  end.
Qed.

Lemma I2F_forallb_well_defined vs1 vs2 :
  Forall2 I2F_dvalue vs1 vs2 ->
  forallb (@dvalue_well_defined PInf) vs1 = forallb (@dvalue_well_defined PFin) vs2.
Proof.
  induction 1 as [|v1 v2 vs1 vs2 H F IH]; cbn; auto.
  rewrite (I2F_dvalue_well_defined H), IH; reflexivity.
Qed.

(** The noreturn/nounwind/nocreateundeforpoison check sees related call
    results, which are both returns or both unwinds, and related arguments:
    both sides agree on which are well defined. *)
Lemma I2F_check_call_result fattrs msg args1 args2 r1 r2 :
  Forall2 I2F_dvalue args1 args2 ->
  sum_rel I2F_dvalue I2F_dvalue r1 r2 ->
  I2F_EOU (fun _ _ => True)
    (@check_call_result PInf fattrs msg args1 r1) (@check_call_result PFin fattrs msg args2 r2).
Proof.
  intros HA H; unfold check_call_result.
  rewrite (I2F_forallb_well_defined HA).
  destruct H as [e1 e2 He | v1 v2 Hv];
    [| rewrite (I2F_dvalue_well_defined Hv)];
    repeat break_match_goal; now constructor.
Qed.

(** Related function values are rejected alike: poison is UB on the
    infinite side, a non-pointer is a failure on both sides, and related
    addresses agree on being null. *)
Lemma I2F_check_callee f1 f2 :
  I2F_dvalue f1 f2 ->
  I2F_EOU (fun _ _ => True) (@check_callee PInf f1) (@check_callee PFin f2).
Proof.
  intros H; unfold check_callee.
  inv H; [inv H0 | |]; cbn; try now constructor.
  destruct p as [z1 pr1], p' as [z2 pr2]; destruct H as [HI ->]; red in HI; subst; cbn.
  destruct (unsigned z2 =? 0)%Z; now constructor.
Qed.

(** Related pointers have the same address. *)
Lemma I2F_dvalue_ptr_address : forall v1 v2,
    I2F_dvalue v1 v2 ->
    @dvalue_ptr_address PInf v1 = @dvalue_ptr_address PFin v2.
Proof.
  intros v1 v2 R.
  inversion R; subst; cbn; auto.
  match goal with
  | HB : I2F_dvalue_base _ _ |- _ => inversion HB; subst; cbn; auto
  end.
  match goal with
  | HA : I2F_Addr ?a ?a' |- _ => destruct a, a'; destruct HA as [HI ->]; red in HI; subst
  end.
  reflexivity.
Qed.

(** The integer operands of [llvm.assume] bundles. *)
Lemma I2F_bundle_uint v1 v2 :
  I2F_dvalue v1 v2 -> @bundle_uint PInf v1 = @bundle_uint PFin v2.
Proof.
  intros R; inversion R; subst; cbn; auto.
  match goal with HB : I2F_dvalue_base _ _ |- _ => inversion HB; subst; cbn; auto end.
Qed.

Lemma I2F_bundle_sint v1 v2 :
  I2F_dvalue v1 v2 -> @bundle_sint PInf v1 = @bundle_sint PFin v2.
Proof.
  intros R; inversion R; subst; cbn; auto.
  match goal with HB : I2F_dvalue_base _ _ |- _ => inversion HB; subst; cbn; auto end.
Qed.
