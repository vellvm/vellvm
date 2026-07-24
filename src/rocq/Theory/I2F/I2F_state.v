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

(** * Relating [FusedS], the product state threaded by [interp_mcfg]

    [FusedS := state * ((stack_frame * stack) * global_env)]
    ([InterpretationStack.v:56]). The memory component already has a
    relation, [I2F_State] ([I2F_memory.v]) — this file lifts [I2F_dvalue] to
    the two remaining components: the [rmap dvalue]-based local/global
    environments, and the [stack_frame]/[stack] wrapping around locals for
    function calls. *)

(** ** [local_env] / [global_env]

    Both are [rmap dvalue] ([Handlers/Local.v:32], [Handlers/Global.v:33]):
    an AVL map keyed by the Params-independent [raw_id], storing
    Params-dependent [dvalue]s — the same "shared keys, related values"
    shape as [I2F_memory]/[I2F_Heap] over [IntMap], via [RM_Refine]
    ([Syntax/RawIdMaps.v], the [raw_id]-keyed analogue of [IM_Refine]). *)

Definition I2F_env : @local_env PInf -> @local_env PFin -> Prop := RM_Refine I2F_dvalue.
Definition I2F_local_env : @local_env PInf -> @local_env PFin -> Prop := I2F_env.
Definition I2F_global_env : @global_env PInf -> @global_env PFin -> Prop := I2F_env.

(** ** [stack_frame] / [stack]

    [stack_frame] ([Handlers/Stack.v:29]) bundles the current [local_env]
    with an exception-landing-pad slot ([stack_exc]) and a debug-only
    source location ([stack_loc], Params-independent — related by literal
    equality). [stack] is the list of enclosing frames pushed/popped across
    calls ([StackPush]/[StackPop]). *)

Record I2F_stack_frame (f1 : @stack_frame PInf) (f2 : @stack_frame PFin) : Prop :=
  { i2f_sf_vars : I2F_local_env f1.(stack_vars) f2.(stack_vars);
    i2f_sf_exc  : option_rel I2F_dvalue f1.(stack_exc) f2.(stack_exc);
    i2f_sf_loc  : f1.(stack_loc) = f2.(stack_loc);
  }.

Definition I2F_stack : @stack PInf -> @stack PFin -> Prop := Forall2 I2F_stack_frame.

(** ** [FusedS] itself *)

Record I2F_FusedS (s1 : @FusedS PInf) (s2 : @FusedS PFin) : Prop :=
  { i2f_fs_mem   : I2F_State (fst s1) (fst s2);
    i2f_fs_frame : I2F_stack_frame (fst (fst (snd s1))) (fst (fst (snd s2)));
    i2f_fs_stack : I2F_stack (snd (fst (snd s1))) (snd (fst (snd s2)));
    i2f_fs_genv  : I2F_global_env (snd (snd s1)) (snd (snd s2));
  }.


Import Monads State StateFacts.
From Paco Require Import paco.


(** * Per-handler compatibility *)

(** [fresh_provenance] resolves via [next_provenance], a single
    Params-independent function ([ProvenanceV], [Implementations/Provenance.v]),
    applied to [state_provenance] which [I2F_State] already forces equal
    ([i2f_st_prov]) — so, like [Cnext_key], [Cfresh_prov] resolves to
    literally the *same* provenance on both sides, and the resulting states
    stay [I2F_State]-related (the memory/heap component is untouched). *)
Lemma I2F_fresh_provenance_eq :
  forall s1 s2,
    I2F_State s1 s2 ->
    next_provenance (state_provenance s1) = next_provenance (state_provenance s2).
Proof.
  intros s1 s2 [_ Hprov]; cbn in *; rewrite Hprov; reflexivity.
Qed.

Lemma I2F_memM_interp R1 R2 RR (t1 : @memM PInf _ R1) (t2 : @memM PFin _ R2) :
  I2F_memS I2F_State RR t1 t2 ->
  forall s1 s2,
    I2F_State s1 s2 ->
    I2F_refine_MCFGbot (prod_rel I2F_State RR) (memM_interp t1 s1) (memM_interp t2 s2).
Proof.
  induction 1 as [x1 x2 Hr | e1 e2 | e m2 | m1 e
                  | k1 k2 Hget IHget | σ1 σ2 k1 k2 Hσ Hput IHput
                  | c k1 k2 Hc IHc];
    intros s1 s2 HS; cbn.
  - pstep; constructor; constructor; auto.
  - apply ruttc_trigger_cast; constructor.
  - unfold raiseUB, trigger_cast; rewrite bind_trigger.
    pstep; repeat constructor.
  - unfold raiseOOM, trigger_cast; rewrite bind_trigger.
    pstep; repeat constructor.
  - now apply IHget.
  - now apply IHput.
  - destruct c; cbn.
    + (* Cnext_key *)
      pose proof (I2F_next_key_with_alignment
                    (i2f_ms_memory (i2f_st_ms HS)) align) as Heq.
      rewrite Heq.
      apply IHc; auto.
    + (* Cfresh_prov *)
      rewrite !Eqit.bind_ret_l.
      pose proof (I2F_fresh_provenance_eq HS) as Heq.
      cbn in Heq.
      rewrite Heq.
      apply IHc.
      constructor; cbn; [exact (i2f_st_ms HS) | reflexivity].
    + (* Cexposed_prov *)
      now apply IHc.
Qed.

(* TODO: Define this lifting of Answer relations to value ones given two events *)
Lemma I2F_fused_intrinsic :
  forall T1 T2 (e1 : @IntrinsicE PInf T1) (e2 : @IntrinsicE PFin T2),
    I2FE_Intrinsic e1 e2 ->
    forall s1 s2, I2F_FusedS s1 s2 ->
      I2F_refine_MCFGbot
        (prod_rel I2F_FusedS (fun r1 r2 => I2FA_Intrinsic e1 r1 e2 r2))
        (fused_intrinsic e1 s1) (fused_intrinsic e2 s2).
Proof.
  intros * HI * HS.
  unfold fused_intrinsic.
  unfold handle_intrinsic.
  destruct s1,s2,HS; cbn in *.
  cbn.
  eapply ruttc_bind.
  apply I2F_memM_interp; [apply I2F_handle_intrinsicM; auto |]; auto.
  intros [] [] []; pstep; do 2 constructor; cbn; auto.
  constructor; auto.
Qed.

Lemma I2F_fused_global :
  forall T1 T2 (e1 : @GlobalE PInf T1) (e2 : @GlobalE PFin T2),
    I2FE_Global e1 e2 ->
    forall s1 s2, I2F_FusedS s1 s2 ->
      I2F_refine_MCFGbot
        (prod_rel I2F_FusedS (fun r1 r2 => I2FA_Global e1 r1 e2 r2))
        (fused_global e1 s1) (fused_global e2 s2).
Proof.
  intros T1 T2 e1 e2 H [m1 [ls1 g1]] [m2 [ls2 g2]] Hs.
  destruct Hs as [Hmem Hframe Hstack Hgenv]; cbn in Hmem, Hframe, Hstack, Hgenv.
  destruct e1 as [x1 dv1 | x1]; destruct e2 as [x2 dv2 | x2];
    simp I2FE_Global in H; cbn in H; try contradiction.
  - (* GlobalWrite *)
    destruct H as [-> Hdv].
    unfold fused_global, on_genv, handle_global_debug, handle_global, update_globals_ref,
      I2F_refine_MCFGbot; cbn; rewrite ?Eqit.bind_ret_l.
    apply ruttc_ret.
    split.
    + constructor; cbn; auto.
      apply RM_Refine_add; auto.
    + simp I2FA_Global; auto.
  - (* GlobalRead *)
    subst.
    unfold fused_global, on_genv, handle_global_debug, handle_global, update_globals_ref,
      I2F_refine_MCFGbot; cbn.
    pose proof (RM_Refine_lookup I2F_dvalue g1 g2 Hgenv x2) as Hlk.
    unfold rid_lookup in Hlk.
    destruct Hlk as [ | dv1 dv2 Hdv]; cbn; rewrite ?Eqit.bind_ret_l.
    + rbind (fun _ _ => False);
        [rbind (fun _ _ => False);
          [apply ruttc_trigger_cast; cbnn; first [simp I2FE_Failure | simp I2FE_UB]; auto |
            intros _ _ []] |
          intros _ _ []].
    + apply ruttc_ret. split; [constructor; cbn; auto | simp I2FA_Global; auto].
Qed.

Lemma I2F_fused_local :
  forall T1 T2 (e1 : @LocalE PInf T1) (e2 : @LocalE PFin T2),
    I2FE_Local e1 e2 ->
    forall s1 s2, I2F_FusedS s1 s2 ->
      I2F_refine_MCFGbot
        (prod_rel I2F_FusedS (fun r1 r2 => I2FA_Local e1 r1 e2 r2))
        (fused_local e1 s1) (fused_local e2 s2).
Proof.
  intros T1 T2 e1 e2 H [m1 [[f1 stk1] g1]] [m2 [[f2 stk2] g2]] Hs.
  destruct Hs as [Hmem Hframe Hstack Hgenv]; cbn in Hmem, Hframe, Hstack, Hgenv.
  destruct Hframe as [Hvars Hexc Hloc]; cbn in Hvars, Hexc, Hloc.
  destruct e1 as [x1 dv1 | x1]; destruct e2 as [x2 dv2 | x2];
    simp I2FE_Local in H; cbn in H; try contradiction.
  - (* LocalWrite *)
    destruct H as [-> Hdv].
    unfold fused_local, on_ls, handle_local_stack, handle_local_debug, handle_local,
      update_locals_ref, upd_local_sf, I2F_refine_MCFGbot; cbn; rewrite ?Eqit.bind_ret_l.
    apply ruttc_ret.
    split.
    + constructor; cbn; auto.
      constructor; cbn; auto.
      apply RM_Refine_add; auto.
    + simp I2FA_Local; auto.
  - (* LocalRead *)
    subst.
    unfold fused_local, on_ls, handle_local_stack, handle_local_debug, handle_local,
      update_locals_ref, I2F_refine_MCFGbot; cbn.
    pose proof (RM_Refine_lookup I2F_dvalue (stack_vars f1) (stack_vars f2) Hvars x2) as Hlk.
    unfold rid_lookup in Hlk.
    destruct Hlk as [ | dv1 dv2 Hdv]; cbn; rewrite ?Eqit.bind_ret_l.
    + rbind (fun _ _ => False);
        [rbind (fun _ _ => False);
          [rbind (fun _ _ => False);
            [apply ruttc_trigger_cast; cbnn; first [simp I2FE_Failure | simp I2FE_UB]; auto |
              intros _ _ []] |
            intros _ _ []] |
          intros _ _ []].
    + apply ruttc_ret.
      split; [constructor; cbn; auto; constructor; cbn; auto | simp I2FA_Local; auto].
Qed.

Lemma I2F_fused_stack :
  forall T1 T2 (e1 : @StackE PInf T1) (e2 : @StackE PFin T2),
    I2FE_Stack e1 e2 ->
    forall s1 s2, I2F_FusedS s1 s2 ->
      I2F_refine_MCFGbot
               (prod_rel I2F_FusedS (fun r1 r2 => I2FA_Stack e1 r1 e2 r2))
        (fused_stack e1 s1) (fused_stack e2 s2).
Proof.
  intros T1 T2 e1 e2 H [m1 [[f1 stk1] g1]] [m2 [[f2 stk2] g2]] Hs.
  destruct Hs as [Hmem Hframe Hstack Hgenv]; cbn in Hmem, Hframe, Hstack, Hgenv.
  destruct e1 as [args1 | |exc1| ]; destruct e2 as [args2 | |exc2| ];
    simp I2FE_Stack in H; cbn in H; try contradiction.
  - (* StackPush *)
    unfold fused_stack, on_ls, handle_stack, I2F_refine_MCFGbot; cbn; rewrite ?Eqit.bind_ret_l.
    assert (Hinit : I2F_local_env
                      (fold_right (fun '(x,dv) => Maps.add x dv) Maps.empty args1)
                      (fold_right (fun '(x,dv) => Maps.add x dv) Maps.empty args2)).
    { induction H as [ | [x1 dv1] [x2 dv2] l1 l2 Hxd Hrest IH]; cbn.
      - apply RM_Refine_empty.
      - destruct Hxd as [Heq Hdv]; cbn in Heq; subst.
        apply RM_Refine_add; auto. }
    apply ruttc_ret.
    split.
    + constructor; cbn.
      * auto.
      * constructor; cbn; [auto | constructor | auto].
      * constructor; auto.
      * auto.
    + simp I2FA_Stack; auto.
  - (* StackPop *)
    unfold fused_stack, on_ls, handle_stack, I2F_refine_MCFGbot; cbn.
    destruct Hstack as [ | f1' f2' stk1' stk2' Hf' Hstk'].
    + cbn; rewrite ?Eqit.bind_ret_l.
      rbind (fun _ _ => False);
        [rbind (fun _ _ => False);
          [apply ruttc_trigger;
            [cbnn; first [simp I2FE_Failure | simp I2FE_UB]; auto | intros [] [] _] |
            intros _ _ []] |
          intros _ _ []].
    + cbn; rewrite ?Eqit.bind_ret_l.
      apply ruttc_ret.
      split; [constructor; cbn; auto | simp I2FA_Stack; auto].
  - (* StackRaise *)
    unfold fused_stack, on_ls, handle_stack, I2F_refine_MCFGbot; cbn; rewrite ?Eqit.bind_ret_l.
    apply ruttc_ret.
    destruct Hframe as [Hvars Hexc Hloc].
    split.
    + constructor; cbn.
      * auto.
      * constructor; cbn; [auto | constructor; auto | auto].
      * auto.
      * auto.
    + simp I2FA_Stack; auto.
  - (* StackGetExc *)
    unfold fused_stack, on_ls, handle_stack, I2F_refine_MCFGbot; cbn; rewrite ?Eqit.bind_ret_l.
    apply ruttc_ret.
    destruct Hframe as [Hvars Hexc Hloc].
    split.
    + constructor; cbn.
      * auto.
      * constructor; cbn; [auto | constructor | auto].
      * auto.
      * auto.
    + simp I2FA_Stack; auto.
Qed.

Lemma I2F_fused_memory :
  forall T1 T2 (e1 : @MemoryE PInf T1) (e2 : @MemoryE PFin T2),
    I2FE_Memory e1 e2 ->
    forall s1 s2, I2F_FusedS s1 s2 ->
             I2F_refine_MCFGbot
               (prod_rel I2F_FusedS (fun r1 r2 => I2FA_Memory e1 r1 e2 r2))
               (fused_memory e1 s1) (fused_memory e2 s2).
Proof.
  intros * HM * HS.
  unfold fused_memory.
  unfold handle_memory.
  destruct s1,s2,HS; cbn in *.
  cbn in *.
  eapply ruttc_bind.
  apply I2F_memM_interp; [apply I2F_handle_memoryM; auto |]; auto.
  intros [] [] []; pstep; do 2 constructor; cbn; auto.
  constructor; auto.
Qed.

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



