From Equations Require Import Equations.

From Stdlib Require Import
  ZArith
  Strings.String
  List
  Morphisms
  Equality.
Import ListNotations.

From ITree Require Import Basics.HeterogeneousRelations ITree InterpFacts Eq.
From ExtLib Require Import Structures.Maps.

From Vellvm Require Import
  Utils
  Syntax
  Semantics
  VellvmIntegers
  Integers
  Interfaces.IPtr
  Interfaces.Params
  Interfaces.Pointer
  Implementations.Pointer
  Implementations.Provenance
  Implementations.IPtrInfinite
  Implementations.IPtrFinite
  Implementations.Memory
  Implementations.ParamsV
  Interfaces.Memory.

From Vellvm Require Import
  Handlers
  Semantics.InterpretationStack
  Utils.rutt_cutoff.

From Vellvm Require Import
  Theory.I2F.Refinement
  Theory.I2F.I2F_exp
  Theory.I2F.I2F_MemS
  Theory.I2F.I2F_memory
  Theory.I2F.I2F_interp.

Existing Instance MemoryModelStateV.
Existing Instance MemoryModelPrimitivesV.


Import Monads State StateFacts.
From Paco Require Import paco.



Lemma I2F_fused_draw :
  forall T1 T2 (e1 : @DrawE PInf T1) (e2 : @DrawE PFin T2),
    I2FE_Draw e1 e2 ->
    forall s1 s2, I2F_FusedS s1 s2 ->
      I2F_refine_MCFGbot
        (prod_rel I2F_FusedS (fun r1 r2 => I2FA_Draw e1 r1 e2 r2))
        (fused_draw e1 s1) (fused_draw e2 s2).
Proof.
  intros T1 T2 e1 e2 H s1 s2 Hs.
  destruct e1 as [τ1]; destruct e2 as [τ2].
  simp I2FE_Draw in H; subst.
  unfold fused_draw, handle_draw, I2F_refine_MCFGbot.
  erbind; [apply I2F_refine_lift_bot, I2F_default_dvalue_of_dtyp |].
  intros r1 r2 Hr; apply ruttc_ret; auto.
Qed.

(** * Assembling the six per-handler lemmas into [interp_vellvm_h]
 *)
Lemma I2F_interp_vellvm_h :
  forall T1 T2 (e1 : @MCFGEtop PInf T1) (e2 : @MCFGEtop PFin T2),
    I2FE_MCFG e1 e2 ->
    forall s1 s2, I2F_FusedS s1 s2 ->
      I2F_refine_MCFGbot
        (prod_rel I2F_FusedS (fun r1 r2 => I2FA_MCFG e1 r1 e2 r2))
        (interp_vellvm_h e1 s1) (interp_vellvm_h e2 s2).
Proof.
  intros T1 T2 e1 e2 H s1 s2 Hs.
  unfold interp_vellvm_h.
  destruct e1 as [e1|e1]; destruct e2 as [e2|e2]; cbn in H; cbn; try easy.
  { (* ExternalCallE *)
    unfold fused_trigger.
    destruct e1 as [t1 f1 args1 | str1 | str1]; destruct e2 as [t2 f2 args2 | str2 | str2];
      simp I2FE_ExternalCall in H; cbn in H; try contradiction.
    - (* ExternalCall *)
      rbind I2F_dvalue.
      apply ruttc_trigger;
      [cbnn; simp I2FE_ExternalCall; auto |
      intros a b Hab; cbnn in Hab; simp I2FA_ExternalCall in Hab].
      intros r1 r2 Hr; rstep.
    - (* IO_stdout *)
      rbind Logic.eq.
      apply ruttc_trigger;
      [cbnn; simp I2FE_ExternalCall; auto |
      intros [] [] Hab; cbnn in Hab; simp I2FA_ExternalCall in Hab;
                  simp I2FA_ExternalCall; auto].
      intros r1 r2 <-; rstep.
      constructor; auto.
      cbn; simp I2FA_ExternalCall; auto.
    - (* IO_stderr *)
      rbind Logic.eq.
      apply ruttc_trigger;
      [cbnn; simp I2FE_ExternalCall; auto |
      intros [] [] Hab; cbnn in Hab; simp I2FA_ExternalCall in Hab;
      simp I2FA_ExternalCall; auto].
      intros r1 r2 <-; rstep.
      constructor; auto.
      cbn; simp I2FA_ExternalCall; auto.
  }
  destruct e1 as [e1|e1]; destruct e2 as [e2|e2]; cbn in H; cbn; try easy;
    [apply I2F_fused_intrinsic; auto |].
  destruct e1 as [e1|e1]; destruct e2 as [e2|e2]; cbn in H; cbn; try easy;
    [apply I2F_fused_global; auto|].
  destruct e1 as [e1|e1]; destruct e2 as [e2|e2]; cbn in H; cbn; try easy.
  destruct e1 as [e1|e1]; destruct e2 as [e2|e2]; cbn in H; cbn; try easy;
    [apply I2F_fused_local; auto | apply I2F_fused_stack; auto].
  destruct e1 as [e1|e1]; destruct e2 as [e2|e2]; cbn in H; cbn; try easy;
    [apply I2F_fused_memory; auto|].
  destruct e1 as [e1|e1]; destruct e2 as [e2|e2]; cbn in H; cbn; try easy;
    [apply I2F_fused_draw; auto|].
  destruct e1 as [e1|e1]; destruct e2 as [e2|e2]; cbn in H; cbn; try easy;
  [apply ruttc_trigger'; cbnn; auto |].
  destruct e1 as [e1|e1]; destruct e2 as [e2|e2]; cbn in H; cbn; try easy;
  [apply ruttc_trigger'; cbnn; auto |].
  destruct e1 as [e1|e1]; destruct e2 as [e2|e2]; cbn in H; cbn; try easy;
  [apply ruttc_trigger'; cbnn; auto |].
  destruct e1 as [e1|e1]; destruct e2 as [e2|e2]; cbn in H; cbn; try easy;
  [apply ruttc_trigger'; cbnn; auto |].
  apply ruttc_trigger'; cbnn; auto.
Qed.

(* This should be a generic lemma on [ruttc] and stateful interpreters, *)
(*    but the statement w.r.t. changing signatures is tricky *)
(*  *)
Lemma ruttc_interp_state_specialized {R1 R2} (RR : R1 -> R2 -> Prop) t1 t2
  (HR: I2F_refine_MCFG RR t1 t2):
  forall s1 s2,
    I2F_FusedS s1 s2 ->
    I2F_refine_MCFGbot (prod_rel I2F_FusedS RR)
      (interp_state interp_vellvm_h t1 s1)
      (interp_state interp_vellvm_h t2 s2).
Proof.
  ginit.
  revert t1 t2 HR.
  gcofix cih; intros.
  rewrite 2 unfold_interp_state.
  punfold HR; red in HR.
  induction HR; pclearbot.
  - cbn; gstep; constructor; auto.
  - cbn; gstep; constructor.
    gfinal; left; auto.
  - cbn.
    (* TODO fix *)
    guclo (@ruttc_clo_bind
             (@MCFGEbot PInf) (@MCFGEbot PFin) (@FusedS PInf * R1) (@FusedS PFin * R2)).
    econstructor.
    apply I2F_interp_vellvm_h; auto.
    intros [] [] []; cbn in *.
    gstep; constructor.
    gfinal; left; apply cih; auto.
    apply H1; auto.
  - cbn. rewrite tau_euttge.
    rewrite unfold_interp_state.
    apply IHHR.
  - cbn. rewrite tau_euttge.
    rewrite unfold_interp_state.
    apply IHHR.
  - cbn.
    generalize H; intros tmp.
    dependent induction H.
    cbnn; rewrite Eqit.bind_bind,bind_trigger.
    gstep; constructor; auto; constructor.
   - cbn.
    generalize H; intros tmp.
    dependent induction H.
    cbnn; rewrite Eqit.bind_bind,bind_trigger.
    gstep; constructor; auto; constructor.
Qed.

(** * Elementary [interp_mcfg] algebra

    [ruttc_interp_state_specialized] already relates [interp_mcfg t1 s1]
    to [interp_mcfg t2 s2] for *any* [t1 ~ t2] fact, by induction on the
    [ruttc] derivation of that fact — so it doubles as a generic "commute
    interpretation with the monadic structure" principle. The three
    corollaries below just package it at the shape of the three
    constructors callers actually build [MCFGtop] trees with ([Ret],
    [ITree.bind], [ITree.trigger]), mirroring itree's own
    [interp_ret]/[interp_bind]/[interp_trigger] — so proofs about
    [interp_mcfg] of a concretely-built tree (e.g. [denote_vellvm]'s
    binds) can rewrite/[apply] through them one constructor at a time
    instead of re-deriving [ruttc_interp_state_specialized]'s coinduction
    at each call site. *)

Lemma I2F_interp_mcfg_ret {R1 R2} (RR : R1 -> R2 -> Prop) (r1 : R1) (r2 : R2) :
  RR r1 r2 ->
  forall s1 s2, I2F_FusedS s1 s2 ->
    I2F_refine_MCFGbot (prod_rel I2F_FusedS RR)
      (interp_mcfg (Ret r1) s1) (interp_mcfg (Ret r2) s2).
Proof.
  intros Hr s1 s2 Hs.
  unfold interp_mcfg.
  apply ruttc_interp_state_specialized; auto.
  apply I2F_interp_intrinsics, ruttc_ret; auto.
Qed.

Lemma I2F_interp_mcfg_bind {R1 R2 T1 T2} (RR : R1 -> R2 -> Prop) (RT : T1 -> T2 -> Prop)
  (t1 : @MCFGtop PInf R1) (t2 : @MCFGtop PFin R2)
  (k1 : R1 -> @MCFGtop PInf T1) (k2 : R2 -> @MCFGtop PFin T2) :
  I2F_refine_MCFG RR t1 t2 ->
  (forall r1 r2, RR r1 r2 -> I2F_refine_MCFG RT (k1 r1) (k2 r2)) ->
  forall s1 s2, I2F_FusedS s1 s2 ->
    I2F_refine_MCFGbot (prod_rel I2F_FusedS RT)
      (interp_mcfg (ITree.bind t1 k1) s1) (interp_mcfg (ITree.bind t2 k2) s2).
Proof.
  intros Ht Hk s1 s2 Hs.
  unfold interp_mcfg.
  apply ruttc_interp_state_specialized; auto.
  apply I2F_interp_intrinsics.
  eapply ruttc_bind; eauto.
Qed.

Lemma I2F_interp_mcfg_trigger :
  forall T1 T2 (e1 : @MCFGEtop PInf T1) (e2 : @MCFGEtop PFin T2),
    I2FE_MCFG e1 e2 ->
    forall s1 s2, I2F_FusedS s1 s2 ->
      I2F_refine_MCFGbot (prod_rel I2F_FusedS (fun r1 r2 => I2FA_MCFG e1 r1 e2 r2))
        (interp_mcfg (ITree.trigger e1) s1) (interp_mcfg (ITree.trigger e2) s2).
Proof.
  intros * HE s1 s2 Hs.
  unfold interp_mcfg.
  apply ruttc_interp_state_specialized; auto.
  apply I2F_interp_intrinsics, ruttc_trigger; auto.
Qed.

(* TODO: Should this be generalized to an arbitrary relation on R? *)
Lemma I2F_interp_mcfg {R} (t1 : @MCFGtop PInf R) (t2 : @MCFGtop PFin R):
  I2F_refine_MCFG Logic.eq t1 t2 ->
  forall s1 s2, I2F_FusedS s1 s2 ->
  I2F_refine_MCFGbot (prod_rel I2F_FusedS Logic.eq)
    (interp_mcfg t1 s1)
    (interp_mcfg t2 s2).
Proof.
  intros Hmcfg * Hfused.
  apply ruttc_interp_state_specialized; auto.
  apply I2F_interp_intrinsics; auto.
Qed.



