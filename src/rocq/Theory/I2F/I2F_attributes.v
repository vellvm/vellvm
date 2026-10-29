(** * I2F invariant for the annotation checks of [Semantics/Attributes.v]

    Each check is a pure [EOU] computation; related inputs give related
    results ([I2F_EOU]), which [I2F_denotation.v] lifts into the itree
    semantics with [I2F_refine_lift']. *)

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

Lemma I2F_value_attrs_poison attrs v1 v2 :
  I2F_dvalue v1 v2 ->
  I2F_dvalue (@value_attrs_poison PInf attrs v1) (@value_attrs_poison PFin attrs v2).
Proof.
  intros H; unfold value_attrs_poison.
  apply I2F_value_attr_range, I2F_value_attr_align, I2F_value_attr_nonnull, H.
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

(** Per-argument attributes applied to related argument lists. *)
Lemma I2F_apply_args_attrs attrss msg args1 args2 :
  Forall2 I2F_dvalue args1 args2 ->
  I2F_EOU (Forall2 I2F_dvalue)
    (@apply_args_attrs PInf attrss msg args1) (@apply_args_attrs PFin attrss msg args2).
Proof.
  intros H; revert attrss; induction H as [| v1 v2 vs1 vs2 Hv _ IH]; intros attrss;
    cbn [apply_args_attrs].
  - apply I2F_EOU_ret; constructor.
  - destruct attrss as [| attrs rest]; cbv beta iota;
      (eapply I2F_EOU_bind; [apply I2F_apply_value_attrs; eauto | intros v1' v2' Hv'];
       eapply I2F_EOU_bind; [apply IH | intros vs1' vs2' Hvs'];
       apply I2F_EOU_ret; constructor; auto).
Qed.

(** The noreturn/nounwind check sees related call results, which are both
    returns or both unwinds. *)
Lemma I2F_check_call_result fattrs msg r1 r2 :
  sum_rel I2F_dvalue I2F_dvalue r1 r2 ->
  I2F_EOU (fun _ _ => True)
    (@check_call_result PInf fattrs msg r1) (@check_call_result PFin fattrs msg r2).
Proof.
  intros H; unfold check_call_result.
  destruct H; break_match_goal; now constructor.
Qed.

Lemma I2F_check_call_return fattrs ret_attrs loc r1 r2 :
  sum_rel I2F_dvalue I2F_dvalue r1 r2 ->
  I2F_EOU (sum_rel I2F_dvalue I2F_dvalue)
    (@check_call_return PInf fattrs ret_attrs loc r1)
    (@check_call_return PFin fattrs ret_attrs loc r2).
Proof.
  intros H; unfold check_call_return.
  eapply I2F_EOU_bind; [apply I2F_check_call_result; eauto | intros _ _ _].
  destruct H; cbv beta iota.
  - apply I2F_EOU_ret; constructor; auto.
  - eapply I2F_EOU_bind; [apply I2F_apply_value_attrs; eauto | intros].
    apply I2F_EOU_ret; constructor; auto.
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
