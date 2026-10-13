(** * I2F invariant for the uninterpreted denotation *)

From Equations Require Import Equations.

From Stdlib Require Import Lia Program.

From ExtLib Require Import Structures.Monads.

From ITree Require Import
  ITree Eq HeterogeneousRelations.
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
  Implementations.Memory
  Implementations.ParamsV.

From Vellvm Require Import
  Utils.rutt_cutoff
  Theory.I2F.Refinement
  Theory.I2F.I2F_exp.

From Paco Require Import paco.

Ltac bind_exp := erbind; [apply I2F_denote_exp'| intros].

(** The CFG-signature instances of the shared lifting lemmas
    ([refine_dvalue_base_map_gen] in Refinement.v, [I2F_freeze_*_gen] in
    I2F_exp.v, [I2F_refine_lift_gen] in Refinement.v): the former
    primed/unprimed duplication is now just a different [draw]-refinement
    ([I2F_draw_CFG]) resp. [Throw] side-condition ([I2FE_CFG_Throw]). *)
Lemma refine_dvalue_base_map' t1 t2 :
  I2F_refine_CFG I2F_dvalue_base t1 t2 ->
  I2F_refine_CFG I2F_dvalue (ITree.map DVALUE_Base t1) (ITree.map DVALUE_Base t2).
Proof. apply refine_dvalue_base_map_gen. Qed.
Hint Resolve refine_dvalue_base_map' : core.
Hint Unfold I2F_refine_CFG : core.

Lemma I2F_draw_CFG : forall dt,
    I2F_refine_CFG I2F_dvalue (draw dt) (draw dt).
Proof. intros; unfold I2F_refine_CFG, draw; rstep. Qed.

Lemma I2F_freeze_base' dt a b :
  I2F_dvalue_base a b ->
  I2F_refine_CFG I2F_dvalue (freeze_base dt a) (freeze_base dt b).
Proof. intros H; unfold I2F_refine_CFG; now apply (I2F_freeze_base_gen I2F_draw_CFG). Qed.

Lemma I2F_freeze' dt a b :
  I2F_dvalue a b ->
  I2F_refine_CFG I2F_dvalue (freeze dt a) (freeze dt b).
Proof.
  intros H; unfold I2F_refine_CFG;
    now apply (I2F_freeze_gen I2F_draw_CFG I2FE_CFG_Throw).
Qed.

Lemma I2F_refine_lift' {R1 R2} (RR : R1 -> R2 -> Prop) (m1 : EOU R1) (m2 : EOU R2) :
  I2F_EOU RR m1 m2 ->
  I2F_refine_CFG RR (EOU_to_itree m1) (EOU_to_itree m2).
Proof. intros H; unfold I2F_refine_CFG; apply (I2F_refine_lift_gen I2FE_CFG_Throw); exact H. Qed.

(** The explicit-alignment checks: related pointers are aligned alike
    ([I2F_Addr_ptr_aligned_to]), so both sides continue, or the infinite
    side raises UB. *)
Lemma I2F_assert_aligned_to a1 a2 align msg :
  I2F_dvalue a1 a2 ->
  I2F_refine_CFG (fun _ _ => True)
    (@assert_aligned_to PInf a1 align msg) (@assert_aligned_to PFin a2 align msg).
Proof.
  intros H; unfold I2F_refine_CFG, assert_aligned_to.
  inv H; [inv H0 | |]; cbn; try now (rstep; cbnn; try easy; eauto).
  break_match_goal; [ | rstep; cbnn; easy].
  (* The two conditions differ in hidden instance arguments, so equate
     them by [apply] (up to conversion) rather than rewriting. *)
  match goal with
  | |- ruttc _ _ _ _ _ (if ?b1 then _ else _) (if ?b2 then _ else _) =>
      assert (EQ : b1 = b2) by (apply I2F_Addr_ptr_aligned_to; exact H);
      rewrite EQ; destruct b2
  end; rstep; cbnn; try easy; eauto.
Qed.

Lemma I2F_assert_alignment a1 a2 anns msg :
  I2F_dvalue a1 a2 ->
  I2F_refine_CFG (fun _ _ => True)
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

(** [!dereferenceable] metadata and the [dereferenceable] attributes:
    related pointers have the same address, so both sides skip the check or
    both read the same bytes. *)
Lemma I2F_assert_dereferenceable or_null n v1 v2 msg :
  I2F_dvalue v1 v2 ->
  I2F_refine_CFG (fun _ _ => True)
    (@assert_dereferenceable PInf or_null n v1 msg) (@assert_dereferenceable PFin or_null n v2 msg).
Proof.
  intros H; pose proof H as H'; unfold I2F_refine_CFG, assert_dereferenceable.
  inv H; [inv H0 | |]; cbn; try now (rstep; cbnn; try easy; eauto).
  match goal with
  | |- ruttc _ _ _ _ _ (if ?b1 then _ else _) (if ?b2 then _ else _) =>
      assert (EQ : b1 = b2)
        by (destruct p, p'; destruct H as [HI ->]; red in HI; subst; reflexivity);
      rewrite EQ; destruct b2
  end.
  - apply ruttc_ret; auto.
  - rbind I2F_dvalue; [unfold load; rstep; cbnn; intros; simp I2FA_Memory in *; eauto | intros].
    apply ruttc_ret; auto.
Qed.

Lemma I2F_assert_attrs_dereferenceable attrs v1 v2 msg :
  I2F_dvalue v1 v2 ->
  I2F_refine_CFG (fun _ _ => True)
    (@assert_attrs_dereferenceable PInf attrs v1 msg) (@assert_attrs_dereferenceable PFin attrs v2 msg).
Proof.
  intros H; unfold I2F_refine_CFG, assert_attrs_dereferenceable.
  destruct (find_option attr_dereferenceable attrs) as [[]|];
    inv H; [inv H0 | | | inv H0 | |]; cbn -[assert_dereferenceable]; try (apply ruttc_ret; auto);
    apply I2F_assert_dereferenceable; repeat constructor; auto.
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

(** ** Operand bundles

    The [llvm.assume] bundle checks ask the same questions of related
    operands on both sides (address, integer value, well-definedness), so
    both sides take the same branch; a ["dereferenceable"] bundle reads the
    same bytes. *)
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

Definition I2F_assume_bundle_check (c1 : @assume_bundle_check PInf) (c2 : @assume_bundle_check PFin) : Prop :=
  forall loc vs1 vs2, Forall2 I2F_dvalue vs1 vs2 ->
    I2F_refine_CFG (fun _ _ => True) (c1 loc vs1) (c2 loc vs2).

(* The proof of an [assume_bundle_check] (unfolded): split the operand
   lists into the shapes the check matches on, rewrite every question about
   an operand to the finite side, and close the identical branches. *)
Ltac i2f_assume_check :=
  do 4 (try (match goal with
             | H : Forall2 _ ?l _ |- _ => is_var l; inversion H; subst; clear H
             end));
  repeat match goal with
    | H : I2F_dvalue ?a ?b |- context [@dvalue_ptr_address PInf ?a] =>
        rewrite (I2F_dvalue_ptr_address H)
    | H : I2F_dvalue ?a ?b |- context [@bundle_uint PInf ?a] =>
        rewrite (I2F_bundle_uint H)
    | H : I2F_dvalue ?a ?b |- context [@bundle_sint PInf ?a] =>
        rewrite (I2F_bundle_sint H)
    | H : I2F_dvalue ?a ?b |- context [@dvalue_well_defined PInf ?a] =>
        rewrite (I2F_dvalue_well_defined H)
    end;
  repeat (break_match_goal; cbn -[assert_dereferenceable assume_violated assume_malformed]);
  try (apply I2F_assert_dereferenceable; auto);
  try (apply ruttc_ret; auto);
  unfold assume_violated, assume_malformed; rstep; cbnn; try easy; eauto.

Lemma I2F_assume_nonnull : I2F_assume_bundle_check (@assume_nonnull PInf) (@assume_nonnull PFin).
Proof. intros loc vs1 vs2 F; unfold I2F_refine_CFG, assume_nonnull; i2f_assume_check. Qed.

Lemma I2F_assume_noundef : I2F_assume_bundle_check (@assume_noundef PInf) (@assume_noundef PFin).
Proof. intros loc vs1 vs2 F; unfold I2F_refine_CFG, assume_noundef; i2f_assume_check. Qed.

Lemma I2F_assume_align : I2F_assume_bundle_check (@assume_align PInf) (@assume_align PFin).
Proof. intros loc vs1 vs2 F; unfold I2F_refine_CFG, assume_align; i2f_assume_check. Qed.

Lemma I2F_assume_dereferenceable or_null :
  I2F_assume_bundle_check (@assume_dereferenceable PInf or_null) (@assume_dereferenceable PFin or_null).
Proof. intros loc vs1 vs2 F; unfold I2F_refine_CFG, assume_dereferenceable; i2f_assume_check. Qed.

(** The two sides' tables of [llvm.assume] checks agree tag by tag.  A new
    entry in [assume_bundle_checks] needs its lemma here. *)
Lemma I2F_assume_bundle_checks :
  Forall2 (fun '(t1, c1) '(t2, c2) => t1 = t2 /\ I2F_assume_bundle_check c1 c2)
    (@assume_bundle_checks PInf) (@assume_bundle_checks PFin).
Proof.
  unfold assume_bundle_checks.
  repeat (apply Forall2_cons; [cbn; split; [reflexivity |] |]); [..| apply Forall2_nil].
  - apply I2F_assume_nonnull.
  - apply I2F_assume_noundef.
  - apply I2F_assume_align.
  - apply I2F_assume_dereferenceable.
  - apply I2F_assume_dereferenceable.
Qed.

Lemma I2F_find_bundle_check tag l1 l2 :
  Forall2 (fun '(t1, c1) '(t2, c2) => t1 = t2 /\ I2F_assume_bundle_check c1 c2) l1 l2 ->
  match option_map snd (find (fun '(t, _) => String.eqb t tag) l1),
        option_map snd (find (fun '(t, _) => String.eqb t tag) l2) with
  | Some c1, Some c2 => I2F_assume_bundle_check c1 c2
  | None, None => True
  | _, _ => False
  end.
Proof.
  induction 1 as [|[t1 c1] [t2 c2] l1 l2 [-> Hc] F IH]; cbn; auto.
  destruct (String.eqb t2 tag); cbn; auto.
Qed.

Lemma I2F_bundle_check f tag :
  match @bundle_check PInf f tag, @bundle_check PFin f tag with
  | Some c1, Some c2 => I2F_assume_bundle_check c1 c2
  | None, None => True
  | _, _ => False
  end.
Proof.
  unfold bundle_check.
  destruct (is_llvm_assume f); [apply I2F_find_bundle_check, I2F_assume_bundle_checks | exact I].
Qed.

Lemma I2F_denote_operand_bundles loc f obs :
  I2F_refine_CFG (fun _ _ => True)
    (@denote_operand_bundles PInf loc f obs) (@denote_operand_bundles PFin loc f obs).
Proof.
  unfold I2F_refine_CFG, denote_operand_bundles.
  rbind (Forall2 (fun (_ _ : unit) => True)); [| intros; apply ruttc_ret; auto].
  apply ruttc_map_monad; intros ob _.
  rbind (Forall2 I2F_dvalue).
  - apply ruttc_map_monad; intros [[t e]|m] _; cbn.
    + apply I2F_denote_exp'.
    + apply ruttc_ret; repeat constructor.
  - intros vs1 vs2 HV.
    pose proof (I2F_bundle_check f (ob_tag ob)) as HC.
    destruct (@bundle_check PInf f (ob_tag ob)), (@bundle_check PFin f (ob_tag ob));
      try contradiction; [apply HC; auto | apply ruttc_ret; auto].
Qed.

(** Applying value attributes: related values give the same [noundef]
    verdict ([I2F_dvalue_well_defined]), so both sides pass on related
    values, or the infinite side raises UB. *)
Lemma I2F_apply_value_attrs attrs msg v1 v2 :
  I2F_dvalue v1 v2 ->
  I2F_refine_CFG I2F_dvalue
    (@apply_value_attrs PInf attrs msg v1) (@apply_value_attrs PFin attrs msg v2).
Proof.
  intros H; unfold I2F_refine_CFG, apply_value_attrs.
  pose proof (I2F_value_attrs_poison attrs H) as HP.
  match goal with
  | |- ruttc _ _ _ _ _ (if ?b1 then _ else _) (if ?b2 then _ else _) =>
      assert (EQ : b1 = b2)
        by (f_equal; f_equal; apply I2F_dvalue_well_defined; exact HP);
      rewrite EQ; destruct b2
  end; [rstep; cbnn; easy |].
  rbind (fun (_ _ : unit) => True); [apply I2F_assert_attrs_dereferenceable; auto | intros _ _ _].
  apply ruttc_ret; auto.
Qed.

(** Load metadata [!range]: both sides test the same integer, lane by lane
    for vectors. *)
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


(** The noreturn/nounwind check sees related call results, which are both
    returns or both unwinds. *)
Lemma I2F_check_call_result fattrs msg r1 r2 :
  sum_rel I2F_dvalue I2F_dvalue r1 r2 ->
  I2F_refine_CFG (fun _ _ => True)
    (@check_call_result PInf fattrs msg r1) (@check_call_result PFin fattrs msg r2).
Proof.
  intros H; unfold I2F_refine_CFG, check_call_result.
  destruct H; break_match_goal; rstep; cbnn; try easy; eauto.
Qed.

(** Call arguments: each is evaluated and passed through its attributes on
    both sides. *)
Lemma I2F_denote_call_args args msg :
  I2F_refine_CFG (Forall2 I2F_dvalue)
    (@denote_call_args PInf args msg) (@denote_call_args PFin args msg).
Proof.
  unfold I2F_refine_CFG, denote_call_args.
  apply ruttc_map_monad.
  intros [[t op] attrs] _.
  erbind; [apply I2F_denote_exp' | intros; apply I2F_apply_value_attrs; auto].
Qed.

Lemma I2F_denote_instr :
  forall i va1 va2,
    option_rel I2F_Addr va1 va2 ->
      I2F_refine_CFG TT
        (@denote_instr PInf i va1) (@denote_instr PFin i va2).
  Proof with try now (rstep; cbnn; try (easy); eauto).
    intros [[x i] ?] ? ? HR.
    destruct i.
    - cbn; break_match...
    - cbn; break_match...
      subst.
      bind_exp.
      rbind TT...
      intros ???...
    - destruct x, fn.
      + cbn.
        rbind (Forall2 I2F_dvalue).
        { apply I2F_denote_call_args. }
        break_match...
        * intros.
          rbind (fun (_ _ : unit) => True); [apply I2F_denote_operand_bundles | intros _ _ _].
          rewrite 2 Eqit.bind_bind.
          rbind (sum_rel I2F_dvalue I2F_dvalue)...
          intros * HR'.
          rewrite 2 Eqit.bind_bind.
          rbind (fun (_ _ : unit) => True); [apply I2F_check_call_result; auto | intros _ _ _].
          inv HR'.
          rbind (fun _ _ => False)...
          intros ?? [].
          rewrite 2 Eqit.bind_ret_l.
          (* the call site's return-value attributes *)
          rbind I2F_dvalue; [apply I2F_apply_value_attrs, I2F_value_metadata_range; auto | intros]...
        * intros.
          rbind (fun (_ _ : unit) => True); [apply I2F_denote_operand_bundles | intros _ _ _].
          rewrite 2 Eqit.bind_bind.
          bind_exp.
          rewrite 2 Eqit.bind_bind.
          rbind (sum_rel I2F_dvalue I2F_dvalue)...
          intros * HR'.
          rewrite 2 Eqit.bind_bind.
          rbind (fun (_ _ : unit) => True); [apply I2F_check_call_result; auto | intros _ _ _].
          inv HR'.
          rbind (fun _ _ => False)...
          intros ?? [].
          rewrite 2 Eqit.bind_ret_l.
          (* the call site's return-value attributes *)
          rbind I2F_dvalue; [apply I2F_apply_value_attrs, I2F_value_metadata_range; auto | intros]...
      + cbn.
        rbind (Forall2 I2F_dvalue).
        { apply I2F_denote_call_args. }
        intros.
        break_match...
        * intros.
          rbind (fun (_ _ : unit) => True); [apply I2F_denote_operand_bundles | intros _ _ _].
          rewrite 2 Eqit.bind_bind.
          rbind (sum_rel I2F_dvalue I2F_dvalue)...
          intros * HR'.
          rewrite 2 Eqit.bind_bind.
          rbind (fun (_ _ : unit) => True); [apply I2F_check_call_result; auto | intros _ _ _].
          inv HR'.
          rbind (fun _ _ => False)...
          intros ?? [].
          rewrite 2 Eqit.bind_ret_l.
          (* the call site's return-value attributes *)
          rbind I2F_dvalue; [apply I2F_apply_value_attrs, I2F_value_metadata_range; auto | intros]...
        * intros.
          rbind (fun (_ _ : unit) => True); [apply I2F_denote_operand_bundles | intros _ _ _].
          rewrite 2 Eqit.bind_bind.
          bind_exp.
          rewrite 2 Eqit.bind_bind.
          rbind (sum_rel I2F_dvalue I2F_dvalue)...
          intros * HR'.
          rewrite 2 Eqit.bind_bind.
          rbind (fun (_ _ : unit) => True); [apply I2F_check_call_result; auto | intros _ _ _].
          inv HR'.
          rbind (fun _ _ => False)...
          intros ?? [].
          rewrite 2 Eqit.bind_ret_l.
          (* the call site's return-value attributes *)
          rbind I2F_dvalue; [apply I2F_apply_value_attrs, I2F_value_metadata_range; auto | intros]...
        
    - destruct x; cbn[denote_instr].
      2: rstep; constructor.
      break_match_goal.
      + break_goal_fast.
        cbn; rewrite 2 Eqit.bind_bind.
        bind_exp.
        (* a poison element count is UB, and related counts agree on it *)
        match goal with
        | |- ruttc _ _ _ _ _ (ITree.bind (if ?b1 then _ else _) _)
                             (ITree.bind (if ?b2 then _ else _) _) =>
            assert (EQP : b1 = b2) by (apply I2F_dvalue_is_poison; exact H);
            rewrite EQP; clear EQP; destruct b2;
            [rbind (fun _ _ => False); [rstep; cbnn; easy | intros ?? []] |]
        end.
        rewrite ?Eqit.bind_bind.
        rbind I2F_dvalue_base; [apply I2F_refine_lift', I2F_dvalue_to_dvalue_base; auto |].
        intros.
        rewrite 2 Eqit.bind_bind.
        pose proof I2F_dvalue_base_int_unsigned H0 as EQ; rewrite EQ.
        rbind I2F_dvalue; [rstep | intros]...
        rbind (fun _ _ => True); [rstep | intros]...
      + cbn; rewrite 2 Eqit.bind_bind.
        rbind I2F_dvalue; [rstep | intros].
        rbind (fun _ _ => True); [rstep | intros]...
        
    - destruct x; cbn...
      destruct ptr.
      bind_exp.
      rbind (fun _ _ => True); [apply I2F_assert_alignment; auto | intros _ _ _].
      rbind I2F_dvalue; [rstep; cbnn; intros; simp I2FA_Memory in *; eauto | intros].
      (* the load's value metadata: !range, then the ones applied like
         attributes, then !dereferenceable *)
      erbind; [apply I2F_apply_value_attrs, I2F_value_metadata_range; eauto | intros v1' v2' HV'].
      rbind (fun (_ _ : unit) => True).
      { destruct (load_metadata_dereferenceable _) as [[]|];
          [apply I2F_assert_dereferenceable; auto | apply ruttc_ret; auto]. }
      intros _ _ _.
      auto... (* [apply I2F_freeze'; auto | intros]...*)
    - destruct val,ptr, x; cbn...
      bind_exp.
      bind_exp.
      rbind (fun _ _ => True); [apply I2F_assert_alignment; auto | intros _ _ _].
      induction H0...
      induction H0...
      6: rbind (fun _ _ => False); [|intros _ _ []]...
      all: rbind (fun _ _ => True); [rstep; cbnn; simp I2FE_Memory; eauto| intros]...
    - destruct x; cbn...
    - destruct x; cbn...
      unfold denote_cmpxchg.
      do 3 break_goal_fast.
      break_match_goal...
      do 3 bind_exp.
      rbind (fun _ _ => True); [apply I2F_assert_aligned_to; auto | intros _ _ _].
      erbind; [rstep; cbnn; intros; simp I2FA_Memory in *; eauto |]. 
      intros.
      erbind.
      apply I2F_refine_lift', I2F_eval_icmp; eauto.
      intros.
      induction H3...
      induction H3...
      break_goal_fast...
      break_goal_fast...
      rbind (fun _ _ => True); [rstep; cbnn; intros; simp I2FA_Memory in *; eauto |].
      intros.
      rstep; cbnn; simp I2FE_Local; intuition.
      rstep; cbnn; simp I2FE_Local; intuition.
    - destruct x; cbn...
      unfold denote_atomicrmw.
      repeat break_goal_fast.
      bind_exp.
      bind_exp.
      rbind (fun _ _ => True); [apply I2F_assert_aligned_to; auto | intros _ _ _].
      erbind; [rstep; cbnn; intros; simp I2FA_Memory in *; eauto | intros].
      unfold denote_atomic_rmw_operation.
      break_goal_fast...
      
      cbn; erewrite 2 Eqit.bind_ret_l;
      rbind (fun _ _ => True); [rstep; cbnn; easy | intros];
        rbind (fun _ _ => True); [rstep; cbnn; easy | intros]...

      all: try (cbn; erbind; [apply I2F_refine_lift', I2F_eval_iop; eauto | intros];
      rbind (fun _ _ => True); [rstep; cbnn; easy | intros];
        rbind (fun _ _ => True); [rstep; cbnn; easy | intros])...

      2-5: rbind (fun _ _ => False); [|intros _ _ []]...
      4-11: rbind (fun _ _ => False); [|intros _ _ []]...
      { cbn; inv H0; [inv H2 | |]...
        1,3-10: rbind (fun _ _ => False); [|intros _ _ []]...
        rbind I2F_dvalue.
        2: intros;
        rbind (fun _ _ => True); [rstep; cbnn; easy | intros];
        rbind (fun _ _ => True); [rstep; cbnn; easy | intros]...
        apply I2F_refine_lift'.
        pose proof @I2F_eval_iop _ (DVALUE_I sz i) _ (DVALUE_I sz i) And H1.
        forward H0; [repeat constructor |].
        inv H0; [inv H4 |..]; repeat constructor.
        induction H0; repeat constructor.
        destruct (Pos.eq_dec sz sz0); repeat constructor.
        subst; cbn; repeat constructor.
      }
      all: erbind; [apply I2F_refine_lift', I2F_eval_fop; eauto | intros].
      all: rbind (fun _ _ => True); [rstep; cbnn; easy | intros].
      all: rbind (fun _ _ => True); [rstep; cbnn; easy | intros]...
    - destruct x, va_list_and_arg_list; cbn.
      all: bind_exp.
      all: rbind I2F_dvalue; [rstep; cbnn; intros; simp I2FA_Memory in *; eauto | intros].
      all: rbind I2F_dvalue; [rstep; cbnn; intros; simp I2FA_Memory in *; eauto | intros].
      all: rewrite 2 Eqit.bind_ret_l.
      all: erbind; [apply I2F_refine_lift', I2F_eval_gep; eauto; repeat constructor | intros].
      all: rbind (fun _ _ => True); [rstep | intros]...
    - destruct x; cbn...
      rbind (option_rel I2F_dvalue); [|intros].
      rstep; cbnn.
      induction H...
Qed.

Lemma I2F_denote_code :
  forall c va1 va2,
    option_rel I2F_Addr va1 va2 ->
    I2F_refine_CFG TT (@denote_code PInf c va1) (@denote_code PFin c va2).
Proof.
  intros.
  unfold denote_code, loop_monad.
  induction c; cbn.
  - now rstep.
  - rbind TT; [apply I2F_denote_instr; auto | intros [] [] _].
    apply IHc.
Qed.

Hint Constructors I2F_dvalue : core.
Hint Unfold TT : core.

(* [I2F_dvalue_is_poison] now lives in I2F_exp.v, which needs it earlier. *)

(** [select_switch] computes in the parameter-free [EOU block_id]: on
    related selectors and switch tables the two sides are literally
    equal (related [DVALUE_I]s carry equal payloads). *)
Lemma I2F_select_switch :
  forall v1 v2,
    I2F_dvalue v1 v2 ->
    forall sw1 sw2,
      Forall2 (prod_rel I2F_dvalue Logic.eq) sw1 sw2 ->
      forall db,
        @select_switch PInf v1 db sw1 = @select_switch PFin v2 db sw2.
Proof.
  intros v1 v2 HV sw1 sw2 F; induction F; intros db; cbn; [reflexivity |].
  destruct x as [xv xid], y as [yv yid].
  destruct H as [HXY EQ]; cbn in HXY, EQ; subst.
  inversion HV; subst; cbn; auto.
  all: inversion HXY; subst; cbn; auto.
  all: inv H0; cbn; auto.
  all: inv H; cbn; auto.
  destruct (Pos.eq_dec _ _); [| reflexivity].
  destruct e; cbv [eq_rec_r eq_rec eq_rect Logic.eq_sym].
  break_match_goal; auto.
Qed.


Lemma I2F_denote_terminator :
  forall t,
    I2F_refine_CFG (sum_rel Logic.eq I2F_dvalue) (@denote_terminator PInf t) (@denote_terminator PFin t).
Proof with try now (rstep; cbnn; try (easy); eauto).
  destruct t as [[? []] ?]; cbn...
  - destruct v; bind_exp...
  - rstep; repeat constructor.
  - destruct v; bind_exp.
    inv H; [induction H0 | |]...
    repeat break_goal_fast...
  - destruct v; bind_exp.
    rewrite (I2F_dvalue_is_poison H).
    break_match_goal...
    rbind (@Logic.eq block_id).
    { apply I2F_refine_lift'.
      eapply I2F_EOU_bind with (RA := Forall2 (prod_rel I2F_dvalue (@Logic.eq block_id))).
      - apply I2F_EOU_map_monad.
        intros [[sz x] id] _; cbn.
        now repeat constructor.
      - intros sw1 sw2 HSW.
        erewrite I2F_select_switch; eauto.
        apply I2F_EOU_refl. }
    intros ?? <-...
  - (* indirectbr: UB on a poison address; otherwise both sides read the
       same block addresses and, related pointers having the same address,
       pick the same listed block *)
    destruct v; bind_exp.
    rewrite (I2F_dvalue_is_poison H).
    break_match_goal...
    destruct fn...
    rbind (Forall2 (@Logic.eq (option Z))).
    { apply ruttc_map_monad; intros b _.
      rbind I2F_dvalue; [unfold gread; rstep | intros v1 v2 HV].
      apply ruttc_ret; now apply I2F_dvalue_ptr_address. }
    intros addrs1 addrs2 HA; apply ListUtil.Forall2_eq in HA; subst.
    rewrite (I2F_dvalue_ptr_address H).
    destruct (dvalue_ptr_address _)...
    destruct (indirectbr_target _ _)...
  - destruct v.
    bind_exp...
  - destruct fnptrval.
    erbind.
    apply I2F_denote_call_args.
    intros.
    rbind (fun (_ _ : unit) => True); [apply I2F_denote_operand_bundles | intros _ _ _].
    bind_exp.
    rbind (sum_rel I2F_dvalue I2F_dvalue)...
    intros * HR.
    rbind (fun (_ _ : unit) => True); [apply I2F_check_call_result; auto | intros _ _ _].
    induction HR.
    rbind TT...
    intros...
    (* the invoke's return-value attributes, on the normal path *)
    rbind I2F_dvalue; [apply I2F_apply_value_attrs, I2F_value_metadata_range; auto | intros].
    break_goal_fast...
    rbind TT...
    intros...
    rewrite !Eqit.bind_ret_l...
Qed.

Lemma I2F_denote_phi :
  forall from phi,
    I2F_refine_CFG (prod_rel Logic.eq I2F_dvalue) (@denote_phi PInf from phi) (@denote_phi PFin from phi).
Proof with try now (rstep; cbnn; try (easy); eauto).
  intros ? [[? []] ?]; cbn.
  break_goal_fast...
  bind_exp...
Qed.

Lemma I2F_denote_phis :
  forall from phis,
    I2F_refine_CFG TT (@denote_phis PInf from phis) (@denote_phis PFin from phis).
Proof with try now (rstep; cbnn; try (easy); eauto).
  intros; cbn.
  erbind.
  apply ruttc_map_monad.
  intros; apply I2F_denote_phi.
  intros.
  erbind.
  unshelve apply ruttc_map_monad_gen.
  exact TT.
  2: intros...
  induction H; cbn; auto.
  constructor; auto.
  destruct H,x,y; cbn in *; subst...
Qed.

Lemma I2F_denote_block :
  forall from block a1 a2,
    option_rel I2F_Addr a1 a2 ->
    I2F_refine_CFG (sum_rel Logic.eq I2F_dvalue) (@denote_block PInf block from a1) (@denote_block PFin block from a2).
Proof with try now (rstep; cbnn; try (easy); eauto).
  intros.
  erbind;[apply I2F_denote_phis| intros ???].
  erbind;[apply I2F_denote_code; auto| intros ???].
  apply I2F_denote_terminator.
Qed.

Lemma I2F_denote_ocfg :
  forall ocfg ft a1 a2,
    option_rel I2F_Addr a1 a2 ->
    I2F_refine_CFG (sum_rel Logic.eq I2F_dvalue) (@denote_ocfg PInf ocfg a1 ft) (@denote_ocfg PFin ocfg a2 ft).
Proof with try now (rstep; cbnn; try (easy); eauto).
  intros.
  apply ruttc_iter with Logic.eq; auto.
  intros [] ? <-.
  break_goal_fast...
  erbind; [apply I2F_denote_block; auto |].
  intros ?? HR; inv HR...
Qed.

Lemma I2F_denote_cfg :
  forall ocfg a1 a2,
    option_rel I2F_Addr a1 a2 ->
    I2F_refine_CFG I2F_dvalue (@denote_cfg PInf ocfg a1) (@denote_cfg PFin ocfg a2).
Proof with try now (rstep; cbnn; try (easy); eauto).
  intros.
  cbn.
  erbind; [apply I2F_denote_ocfg; auto |].
  intros ?? HR; inv HR...
Qed.

Definition I2F_function_denotation
  (ctx1 : @function_denotation PInf)
  (ctx2 : @function_denotation PFin) : Prop :=
  forall args1 args2,
    Forall2 I2F_dvalue args1 args2 ->
    I2F_refine_CFG (sum_rel I2F_dvalue I2F_dvalue) (ctx1 args1) (ctx2 args2).

Lemma I2F_combine_lists_varargs : 
  forall (d : definition dtyp (cfg dtyp)) y1 y2,
    Forall2 I2F_dvalue y1 y2 -> 
    I2F_EOU 
      (prod_rel (Forall2 (prod_rel Logic.eq I2F_dvalue)) (Forall2 I2F_dvalue))
      (combine_lists_varargs (df_args d) y1)
      (combine_lists_varargs (df_args d) y2).
Proof with cbn; eauto using I2F_EOU_error, I2F_EOU_ret, I2F_EOU_oom, I2F_EOU_ub.
  intros d.
  generalize (df_args d) as l.
  induction l as [| x l IH]; intros * HR.
  - dependent induction HR...
    apply I2F_EOU_ret; constructor...
  - dependent induction HR...
    apply IH in HR.
    induction HR...
    destruct a1,a2; constructor.
    inv H0.
    constructor; cbn...
Qed.

Lemma I2F_dtyp_of_dvalue :
  forall a1 a2 : dvalue,
    I2F_dvalue a1 a2 ->
    I2F_EOU Logic.eq (dtyp_of_dvalue a1) (dtyp_of_dvalue a2).
Proof.
  intros * H; erewrite I2F_dtyp_of_dvalue_eq; eauto.
  apply I2F_EOU_refl.
Qed.
  
Lemma I2F_push_call_frame d args1 args2:
    Forall2 I2F_dvalue args1 args2 ->
    I2F_refine_CFG I2F_Addr (push_call_frame d args1) (push_call_frame d args2).
Proof with try now (rstep; cbnn; try (easy); eauto).
  intros.
  erbind; [apply I2F_refine_lift', I2F_combine_lists_varargs; auto | intros].
  destruct r1, r2; inv H0; cbn in * |-.
  erbind; [eapply I2F_refine_lift', I2F_EOU_map_monad2 with (RB := Logic.eq); eauto | intros ?? HEQ; apply ListUtil.Forall2_eq in HEQ; subst].
  apply I2F_dtyp_of_dvalue.
  rbind TT...
  intros _ _ _.
  rbind TT...
  intros _ _ _.
  rbind I2F_dvalue...
  intros ?? HR.
  rbind TT.
  rstep; cbnn; try easy.
  constructor; intuition.
  intros _ _ _.
  induction HR; [induction H0 | |]...
Qed.

Lemma unfold_run_exc_strong `{Params.Params} {A} (t : itree _ A) :
  run_exc t ≅ match observe t with
         | RetF a  => Ret (inr a)
         | TauF u' => Tau (run_exc u')
         | VisF X e k =>
             match exc_of_event e with
             | Some x => Ret (inl x)
             | None   => Vis e (fun x => Tau (run_exc (k x)))
             end
    end.
Proof.
  unfold run_exc.
  rewrite unfold_iter.
  desobs t ot; cbn; auto.
  rewrite Eqit.bind_ret_l; reflexivity.
  rewrite Eqit.bind_ret_l; reflexivity.
  break_goal_fast; rewrite ?Eqit.bind_ret_l; [reflexivity |].
  rewrite bind_vis. apply eqit_Vis.
  intros.
  rewrite Eqit.bind_ret_l; reflexivity.
Qed.

Lemma cutUB_exc_of_event `{Params.Params} {X} (e : _ X) :
  cutUB e ->
  exc_of_event e = None.
Proof.
  intros CUT.
  induction CUT; reflexivity.
Qed.

Lemma cutOOM_exc_of_event `{Params.Params} {X} (e : _ X) :
  cutOOM e ->
  exc_of_event e = None.
Proof.
  intros CUT.
  induction CUT; reflexivity.
Qed.

(** Related events have related exception projections: the [LLVMExcE]
    payloads are related by [I2FE_Exc], and every other component
    projects to [None] on both sides (mismatched injections are ruled
    out by the computing [sum_prerel]). *)
Lemma I2FE_CFG_exc_of_event {A B} (e1 : @CFGEtop PInf A) (e2 : @CFGEtop PFin B) :
  I2FE_CFG e1 e2 ->
  option_rel I2F_dvalue (exc_of_event e1) (exc_of_event e2).
Proof.
  intros HE.
  repeat (destruct e1 as [e1|e1]); repeat (destruct e2 as [e2|e2]);
    cbn in *; try easy; try (now constructor).
  destruct e1, e2; simp I2FE_Exc in HE; constructor; auto.
Qed.

Lemma I2F_run_exc {R1 R2 : Type} {RR : R1 -> R2 -> Prop} t1 t2 :
  ruttc cutUB cutOOM I2FE_CFG I2FA_CFG RR t1 t2 ->
  ruttc cutUB cutOOM I2FE_CFG I2FA_CFG (sum_rel I2F_dvalue RR) (run_exc t1) (run_exc t2).
Proof.
  revert t1 t2.
  ginit; gcofix cih.
  intros * HR.
  rewrite 2 unfold_run_exc_strong.
  punfold HR; red in HR.
  induction HR; pclearbot.
  - gstep; constructor; eauto.
  - gstep. constructor; eauto.
    gfinal; left; apply cih; auto.
  - pose proof (I2FE_CFG_exc_of_event _ _ H) as EXC.
    destruct (exc_of_event e1), (exc_of_event e2); inv EXC.
    + gstep; constructor; constructor; auto.
    + gstep; constructor; auto.
      intros a b HAns.
      gstep; constructor.
      gfinal; left; apply cih.
      now apply H0.
  - rewrite tau_euttge, unfold_run_exc_strong.
    apply IHHR.
  - rewrite tau_euttge, unfold_run_exc_strong.
    apply IHHR.
  - rewrite cutUB_exc_of_event; auto.
    gstep; constructor; auto.
  - rewrite cutOOM_exc_of_event; auto.
    gstep; constructor; auto.
Qed.

(** Per-argument attributes applied to related argument lists. *)
Lemma I2F_apply_args_attrs attrss msg args1 args2 :
  Forall2 I2F_dvalue args1 args2 ->
  I2F_refine_CFG (Forall2 I2F_dvalue)
    (@apply_args_attrs PInf attrss msg args1) (@apply_args_attrs PFin attrss msg args2).
Proof.
  intros H; revert attrss; induction H as [| v1 v2 vs1 vs2 Hv _ IH]; intros attrss; cbn.
  - unfold I2F_refine_CFG; rstep; cbnn; auto.
  - destruct attrss as [| attrs rest];
      (erbind; [apply I2F_apply_value_attrs; eauto | intros v1' v2' Hv'];
       erbind; [apply IH | intros vs1' vs2' Hvs'];
       unfold I2F_refine_CFG; rstep; cbnn; auto).
Qed.

Lemma I2F_denote_function d :
    I2F_function_denotation (@denote_function PInf d) (@denote_function PFin d).
Proof with try now (rstep; cbnn; try (easy); eauto).
  unfold denote_function.
  destruct (dc_param_attrs (df_prototype d)) as [ret_attrs args_attrs].
  intros ???.
  (* the callee's declared argument attributes, on entry *)
  rbind (Forall2 I2F_dvalue); [apply I2F_apply_args_attrs; auto | intros args1' args2' Hargs'].
  rbind I2F_Addr; [apply I2F_push_call_frame; auto | intros].
  erbind...
  eapply I2F_run_exc, I2F_denote_cfg; constructor; auto.
  intros.
  unfold pop_call_frame; cbn; rewrite 2 Eqit.bind_bind.
  rbind TT...
  intros ???.
  rbind TT...
  intros ???.
  (* the callee's noreturn / nounwind attributes *)
  rbind (fun (_ _ : unit) => True); [apply I2F_check_call_result; auto | intros _ _ _].
  (* the callee's declared return attributes, on a normal return *)
  match goal with HR : sum_rel I2F_dvalue I2F_dvalue _ _ |- _ => destruct HR end.
  - rstep; cbnn; auto.
  - erbind; [apply I2F_apply_value_attrs; eauto | intros]...
Qed.

(** Pointwise lifting of [I2F_function_denotation] to function contexts,
    extensionally over [lookup] (in the style of [IntMaps.Equiv]): the two
    maps have the same domain, and denotations found at a common key are
    related. [denote_mcfg] keys the map by [ptr_to_int], which coincides
    on [I2F_Addr]-related addresses, so related lookups share their key. *)
Definition I2F_ctx
  (ctx1 : IntMap (@function_denotation PInf))
  (ctx2 : IntMap (@function_denotation PFin)) : Prop :=
  forall k, option_rel I2F_function_denotation (lookup k ctx1) (lookup k ctx2).

Lemma I2F_denote_mcfg :
  forall t ctx1 ctx2 f1 f2 args1 args2,
    I2F_dvalue f1 f2 ->
    Forall2 I2F_dvalue args1 args2 ->
    I2F_ctx ctx1 ctx2 ->
    I2F_refine_MCFG
      (sum_rel I2F_dvalue I2F_dvalue)
      (@denote_mcfg PInf ctx1 t f1 args1)
      (@denote_mcfg PFin ctx2 t f2 args2).
Proof with try now (rstep; cbnn; try (easy); eauto).
  intros * HF Hargs Hctx.
  red; unfold denote_mcfg.
  (* [ruttc_mrec] concludes at the per-call answer relation
     [fun a b => I2FA_Call d1 a d2 b]; weaken it into [sum_rel] (they
     compute to each other), the other relations are untouched. *)
  eapply ruttc_weaken; cycle -1.
  { eapply ruttc_mrec with (RCall := I2FE_Call) (RCall' := I2FA_Call).
    2: { simp I2FE_Call; repeat split; auto. }
    (* the bodies: related calls dispatch through related contexts *)
    intros A B [dt fv1 fas1] [dt' fv2 fas2] HC.
    simp I2FE_Call in HC; destruct HC as (<- & HFv & HAs).
    (* transport the CFG-level relations to the structural ones
       demanded by [ruttc_mrec] *)
    eapply ruttc_weaken with (RR := sum_rel I2F_dvalue I2F_dvalue).
    { intros ? ? CUT; exact (proj1 (I2F_cutUB_CFG _) CUT). }
    { intros ? ? CUT; exact (proj1 (I2F_cutOOM_CFG _) CUT). }
    { intros * HE; exact (I2FE_CFG_sum _ _ HE). }
    { intros * HA; exact (I2FA_CFG_sum HA). }
    { intros ? ? HS; cbn; simp I2FA_Call; exact HS. }
    cbn.
    (* Dispatch on the related function values: poison is UB on the
       infinite side, a non-pointer is a failure on both sides, and a
       pointer is checked against null and then looked up. *)
    pose proof HFv as HFv'.
    inv HFv; [inv H | |]; cbn.
    all: try now (rstep; cbnn; try (easy); eauto).
    (* the pointer case: related addresses share their [ptr_to_int] key *)
    destruct p as [z1 pr1], p' as [z2 pr2]; destruct H0 as [HI ->]; red in HI; subst; cbn.
    destruct (unsigned z2 =? 0)%Z; [now (rstep; cbnn; try (easy); eauto) |].
    specialize (Hctx (unsigned z2)).
    destruct (lookup (unsigned z2) ctx1), (lookup (unsigned z2) ctx2); inv Hctx.
    - (* internal call: the related denotations found in the contexts *)
      match goal with
      | HFD : I2F_function_denotation _ _ |- _ => now apply HFD
      end.
    - (* external call *)
      unfold external_call.
      rbind I2F_dvalue; [rstep |intros]...
  }
  (* the four identity inclusions, and [sum_rel] from the [I2FA_Call]
     instance (they are convertible) *)
  all: auto.
Qed.

