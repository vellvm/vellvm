From Coq Require Import
     String Morphisms List.

From ITree Require Import
     ITree
     Basics.Monad
     Eq.Eq
     TranslateFacts.

From Vellvm Require Import
     Utils.Tactics
     Utils.Util
     Syntax.LLVMAst
     Syntax.AstLib
     Syntax.DynamicTypes
     Syntax.TypToDtyp
     Semantics.LLVMEvents
     Semantics.DynamicValues
     Semantics.TopLevel
     Semantics.InterpretationStack
     Handlers.Handlers
     Refinement
     Theory.InterpreterCFG
     Theory.ExpLemmas
     Theory.InstrLemmas
     Theory.InterpreterCFG
     Theory.SymbolicInterpreter.

From ExtLib Require Import
     Core.RelDec
     Data.Map.FMapAList
     Structures.Maps.

From Vellvm Require Import
     Utils.AListFacts
     Utils.PostConditions
     Syntax.Scope.

Import ListNotations.
Import AlistNotations.
Import ITreeNotations.
Import SemNotations.

Definition local_has_changed (l1 : local_env) (defs: list raw_id) : local_env -> Prop :=
  fun l2 => forall x, ~ In x defs -> l1 @ x = l2 @ x.

Definition lift_pred_L3 (T : Type) (P : local_env -> Prop) :
  (memory_stack * (local_env * (global_env * T))) -> Prop :=
  fun '(_,(l,_)) => P l.

Lemma raise_has_all_posts3 : forall {R} s g l m Q,
    ℑ3 (raise (A := R) s) g l m ⤳ Q.
Proof.
  unfold raise; intros.
  rewrite interp_cfg3_bind.
  cbn.
  unfold interp_cfg3.
  rewrite interp_intrinsics_trigger.
  cbn.
  unfold Intrinsics.F_trigger; cbn.
  rewrite subevent_subevent.
  rewrite interp_global_trigger; cbn.
  rewrite subevent_subevent.
  rewrite interp_local_bind, interp_local_trigger; cbn.
  rewrite subevent_subevent, bind_bind.
  rewrite interp_memory_bind, interp_memory_trigger; cbn.
  rewrite subevent_subevent, !bind_bind.
  apply has_post_bind; intros [].
Qed.

Lemma raiseUB_has_all_posts3 : forall {R} s g l m Q,
    ℑ3 (raiseUB (X := R) s) g l m ⤳ Q.
Proof.
  unfold raiseUB; intros.
  rewrite interp_cfg3_bind.
  cbn.
  unfold interp_cfg3.
  rewrite interp_intrinsics_trigger.
  cbn.
  unfold Intrinsics.F_trigger; cbn.
  rewrite subevent_subevent.
  rewrite interp_global_trigger; cbn.
  rewrite subevent_subevent.
  rewrite interp_local_bind, interp_local_trigger; cbn.
  rewrite subevent_subevent, bind_bind.
  rewrite interp_memory_bind, interp_memory_trigger; cbn.
  rewrite subevent_subevent, !bind_bind.
  apply has_post_bind; intros [].
Qed.

Ltac case_eq_id x id :=
  let EQ := fresh "EQ" in
  let NEQ := fresh "NEQ" in
  destruct (Eqv.eqv_dec_p x id) as [EQ | NEQ];
  [repeat red in EQ; subst | unfold Eqv.eqv, eqv_raw_id in NEQ].

Arguments alist_find : simpl never.
Hint Unfold In : core.

Lemma pickUnique_is_pure: forall v, pure (ℑ3 (pickUnique v)).
Proof.
  unfold pure; intros.
  unfold pickUnique,concretize_or_pick.
  break_match_goal.
  cbn.
  unfold lift_err.
  break_match_goal.
  apply failure_is_pure.
  vred_C3.
  apply eutt_Ret; cbn; auto.
  apply pick_is_pure.
Qed.

Ltac go := repeat vred_C3. 
Lemma Intrinsic_preserves_local:
  forall τ f args g l m,
    ℑ3 (trigger (Intrinsic τ f args)) g l m ⤳ lift_pred_L3 _ (fun l' => l' = l).
Proof.
  intros. unfold ℑ3.
  rewrite interp_intrinsics_trigger.
  cbn.
  break_match_goal.
  - break_match_goal.
    + unfold raise.
      rewrite interp_global_bind.
      rewrite interp_global_trigger. cbn.
      rewrite subevent_subevent.
      rewrite !interp_local_bind.
      rewrite interp_local_trigger.
      cbn.
      rewrite subevent_subevent, !bind_bind.
      rewrite interp_memory_bind,interp_memory_trigger.
      cbn.
      rewrite subevent_subevent, !bind_bind.
      apply has_post_bind; intros [].
    + rewrite interp_global_ret, interp_local_ret, interp_memory_ret.
      apply eutt_Ret; repeat red; auto.
  - cbn.
    rewrite subevent_subevent.
    rewrite interp_global_trigger.
    cbn; rewrite subevent_subevent.
    rewrite interp_local_bind, interp_local_trigger.
    cbn; rewrite subevent_subevent.
    rewrite !bind_bind.
    rewrite interp_memory_bind, interp_memory_trigger.
    destruct m; cbn.
    break_match_goal.
    + break_match_goal.
      * apply has_post_bind; intros [].
        rewrite interp_memory_bind, interp_memory_ret, bind_ret_l.
        rewrite interp_local_ret,interp_memory_ret.
        apply eutt_Ret; repeat red; auto.
      * rewrite bind_ret_l.
        rewrite interp_memory_bind, interp_memory_ret, bind_ret_l.
        rewrite interp_local_ret, interp_memory_ret.
        apply eutt_Ret; repeat red; auto.
    + unfold raise; rewrite bind_bind.
      apply has_post_bind; intros [].
Qed.

Lemma Call_is_pure:
  forall τ f args, 
    pure (ℑ3 (trigger (Call τ f args))). 
Proof.
  unfold pure; intros. unfold ℑ3.
  rewrite interp_intrinsics_trigger.
  cbn.
  unfold Intrinsics.E_trigger.
  rewrite subevent_subevent.
  rewrite interp_global_trigger.
  cbn; rewrite subevent_subevent.
  rewrite interp_local_bind, interp_local_trigger.
  cbn; rewrite subevent_subevent.
  rewrite bind_bind.
  rewrite interp_memory_bind, interp_memory_trigger.
  cbn; rewrite subevent_subevent.
  rewrite bind_bind.
  unfold ReSum_id, id_, Id_IFun.
  apply has_post_bind; intros.
  go.
  rewrite interp_local_ret, interp_memory_ret.
  apply eutt_Ret; repeat red; auto.
Qed.

Lemma LocalWrite_local_change :
  forall id v g l m,
    ℑ3 (trigger (LocalWrite id v)) g l m
       ⤳ lift_pred_L3 unit (local_has_changed l [id]).
Proof.
  intros.
  rewrite interp_cfg3_LW.
  apply eutt_Ret.
  intros ? NIN. 
  case_eq_id x id.
  exfalso; apply NIN; auto. 
  cbn; rewrite alist_find_neq; auto.
Qed.

Lemma trigger_Mem_local_change:
  forall {X : Type} (e : MemoryE X) g l m, 
    ℑ3 (trigger e: itree instr_E X) g l m ⤳ lift_pred_L3 _ (fun l' => l' = l).
Proof.
  intros. unfold ℑ3.
  rewrite interp_intrinsics_trigger.
  cbn.
  rewrite subevent_subevent.
  rewrite interp_global_trigger.
  cbn; rewrite subevent_subevent.
  rewrite interp_local_bind, interp_local_trigger.
  cbn; rewrite subevent_subevent.
  rewrite bind_bind.
  rewrite interp_memory_bind, interp_memory_trigger.
  cbn.
  destruct e; cbn.
  - try (rewrite bind_ret_l, interp_memory_bind, interp_memory_ret, bind_ret_l, interp_local_ret,interp_memory_ret; apply eutt_Ret; red; auto).
  - unfold lift_pure_err, lift_err.
    rewrite bind_bind.
    break_match_goal; [unfold raise; rewrite bind_bind; apply has_post_bind; intros [] |].
    cbn.
    try (rewrite ?bind_ret_l, ?interp_memory_bind, ?interp_memory_ret, ?bind_ret_l, interp_local_ret,interp_memory_ret; apply eutt_Ret; red; auto).
  - unfold lift_pure_err, lift_err.
    rewrite bind_bind.
    break_match_goal; [unfold raise; rewrite bind_bind; apply has_post_bind; intros [] |].
    destruct p; cbn.
    try (rewrite ?bind_ret_l, ?interp_memory_bind, ?interp_memory_ret, ?bind_ret_l, ?interp_local_ret, ?interp_memory_ret; try apply eutt_Ret; red; auto).
  - break_match_goal; try (unfold raise; rewrite bind_bind; apply has_post_bind; intros []).
    break_match_goal; try (unfold raiseUB; rewrite bind_bind; apply has_post_bind; intros []).
    try (rewrite ?bind_ret_l, ?interp_memory_bind, ?interp_memory_ret, ?bind_ret_l, ?interp_local_ret, ?interp_memory_ret; try apply eutt_Ret; red; auto).
  - break_match_goal; try (unfold raise; rewrite bind_bind; apply has_post_bind; intros []).
    try (rewrite ?bind_ret_l, ?interp_memory_bind, ?interp_memory_ret, ?bind_ret_l, ?interp_local_ret, ?interp_memory_ret; try apply eutt_Ret; red; auto).
  - unfold lift_pure_err, lift_err.
    rewrite bind_bind.
    break_match_goal; try (unfold raise; rewrite bind_bind; apply has_post_bind; intros []).
    cbn; try (rewrite ?bind_ret_l, ?interp_memory_bind, ?interp_memory_ret, ?bind_ret_l, ?interp_local_ret, ?interp_memory_ret; try apply eutt_Ret; red; auto).
  - break_match_goal; try (unfold raise; rewrite bind_bind; apply has_post_bind; intros []);
      break_match_goal; try (unfold raise; rewrite bind_bind; apply has_post_bind; intros []); destruct p; cbn.
    all:try (rewrite ?bind_ret_l, ?interp_memory_bind, ?interp_memory_ret, ?bind_ret_l, ?interp_local_ret, ?interp_memory_ret; try apply eutt_Ret; red; auto).
  - break_match_goal; try (unfold raise; rewrite bind_bind; apply has_post_bind; intros []).
    break_match_goal; try (unfold raise; rewrite bind_bind; apply has_post_bind; intros []).
    break_let.
    rewrite !bind_bind.
    unfold lift_undef_or_err.
    break_match_goal; try (unfold raise; rewrite bind_bind; apply has_post_bind; intros []).
    break_match_goal; try (unfold raiseUB; rewrite bind_bind; apply has_post_bind; intros []).
    break_match_goal; try (unfold raise; rewrite bind_bind; apply has_post_bind; intros []).
    all:try (rewrite ?bind_ret_l, ?interp_memory_bind, ?interp_memory_ret, ?bind_ret_l, ?interp_local_ret, ?interp_memory_ret; try apply eutt_Ret; red; auto).
Qed.

Lemma Ret_local_change :
  forall {X : Type} {E} (v : X) g l m,
    (Ret3 g l m v: itree E _) ⤳ lift_pred_L3 X (local_has_changed l []).
Proof.
  intros; apply eutt_Ret; repeat red; auto.
Qed.

Lemma concretize_or_pick_is_pure : forall v P, pure (ℑ3 (concretize_or_pick v P)).
Proof.
  unfold pure; intros.
  unfold concretize_or_pick.
  break_match_goal; [| apply pick_is_pure].
  unfold lift_err.
  break_match_goal; [apply failure_is_pure |].
  cbn.
  go.
  apply eutt_Ret; cbn; auto.
Qed.

Ltac __base :=
  first [apply raise_has_all_posts3 |
         apply LocalWrite_local_change |
         apply Ret_local_change | idtac].

Lemma instr_same_local : forall x i g l m,
    ⟦ (x,i) ⟧i3 g l m ⤳ lift_pred_L3 _ (local_has_changed l (def_sites_instr_id x)). 
Proof with __base.
  destruct i; intros.
  - destruct x; cbn; go...
  - destruct x; cbn; go... 
    eapply has_post_bind_strong; [apply expr_are_pure |].
    intros3; intros (-> & -> & ->).
    go...
  - destruct fn,x.
    + cbn; go.
      rewrite interp_cfg3_map_monad.
      apply has_post_bind_strong with (S := lift_state_cfgP (pure_P g l m)).
      apply map_monad_eutt_state3_ind; [intros [] ? ? ? ? (-> & -> & ->); apply expr_are_pure | cbn; intuition].
      intros3; intros (-> & -> & ->).
      break_match_goal.
      * go.
        rewrite interp_cfg3_map_monad.
        apply has_post_bind_strong with (S := lift_state_cfgP (pure_P g l m)).
        apply map_monad_eutt_state3_ind; [intros [] ? ? ? ? (-> & -> & ->); apply pickUnique_is_pure | cbn; intuition].
        intros3; intros (-> & -> & ->).
        unfold ITree.map; go.
        eapply has_post_bind_strong; [apply Intrinsic_preserves_local |].
        intros3; intros ->.
        go...
      * go.
        eapply has_post_bind_strong; [apply expr_are_pure |].
        intros3; intros (-> & -> & ->).
        eapply has_post_bind_strong; [apply Call_is_pure |].
        intros3; intros (-> & -> & ->).
        go...
    + cbn; go.
      rewrite interp_cfg3_map_monad.
      apply has_post_bind_strong with (S := lift_state_cfgP (pure_P g l m)).
       apply map_monad_eutt_state3_ind; [intros [] ? ? ? ? (-> & -> & ->); apply expr_are_pure | cbn; intuition].
      intros3; intros (-> & -> & ->).
      break_match_goal.
      * go.
        rewrite interp_cfg3_map_monad.
        apply has_post_bind_strong with (S := lift_state_cfgP (pure_P g l m)).
        apply map_monad_eutt_state3_ind; [intros [] ? ? ? ? (-> & -> & ->); apply pickUnique_is_pure | cbn; intuition].
        intros3; intros (-> & -> & ->).
        unfold ITree.map; go.
        eapply has_post_bind_strong; [apply Intrinsic_preserves_local |].
        intros3; intros ->.
        go...
      * go.
        eapply has_post_bind_strong; [apply expr_are_pure |].
        intros3; intros (-> & -> & ->).
        eapply has_post_bind_strong; [apply Call_is_pure |].
        intros3; intros (-> & -> & ->).
        go...
  - destruct x; cbn; go... 
    eapply has_post_bind_strong; [apply trigger_Mem_local_change |].
    intros3; intros ->.
    go...
  - destruct x, ptr; cbn; go...
    eapply has_post_bind_strong; [apply expr_are_pure |].
    intros3; intros (-> & -> & ->).
    go.
    eapply has_post_bind_strong; [apply concretize_or_pick_is_pure |].
    intros3; intros (-> & -> & ->).
    break_match_goal.
    all: try (go; eapply has_post_bind_strong; [apply trigger_Mem_local_change | intros3; intros ->]).
    all: try apply LocalWrite_local_change.
    apply raiseUB_has_all_posts3.
  - destruct x, ptr; cbn.
    __base.
    destruct val; cbn.
    go.
    eapply has_post_bind_strong; [apply expr_are_pure |].
    intros3; intros (-> & -> & ->).
    go.
    eapply has_post_bind_strong; [apply concretize_or_pick_is_pure |].
    intros3; intros (-> & -> & ->).
    go.
    eapply has_post_bind_strong; [apply expr_are_pure |].
    intros3; intros (-> & -> & ->).
    go.
    eapply has_post_bind_strong; [apply pickUnique_is_pure |].
    intros3; intros (-> & -> & ->).
    break_match_goal.
    all: try (eapply has_post_weaken; [apply trigger_Mem_local_change | cbn; intros3; cbn; intros ->; red; auto]).
    apply raiseUB_has_all_posts3.
  - cbn; break_match_goal; __base.
  - cbn; break_match_goal; __base.
  - cbn; break_match_goal; __base.
  - cbn; break_match_goal; __base.
  - cbn; break_match_goal; __base.
Qed.

Lemma def_sites_code_cons : forall {T} id x i (c : code T),
    In id (def_sites_code ((x,i):: c))
    <-> (In id (def_sites_instr_id x) \/ In id (def_sites_code c)).
Proof.
  induction c as [| [x' i'] c IH] using rev_ind; cbn.
  - destruct x; cbn; intuition.
  - destruct x; cbn; intuition.
Qed.

Arguments def_sites_code : simpl never.

Lemma local_frame_code : forall c g l m,
    ⟦ c ⟧c3 g l m ⤳ lift_pred_L3 _ (local_has_changed l (def_sites_code c)).
Proof.
  induction c as [| i c IH]; intros.
  - vred_C3.
    apply eutt_Ret.
    intros ? ?; reflexivity.
  - vred_C3.
    destruct i as [x i].
    eapply has_post_bind_strong; [apply instr_same_local |].
    intros3; cbn; intros H.
    eapply has_post_weaken.
    apply IH.
    intros3; cbn; intros H'.
    red.
    intros id NIN.
    cbn in *.
    rewrite def_sites_code_cons in NIN.
    destruct x.
    + cbn in H.
      case_eq_id id id0.
      * exfalso.
        eapply NIN; cbn; auto. 
      * replace (l@id) with (l0@id).
        apply H'.
        intros abs; apply NIN; auto.
        symmetry; apply H; auto.
    + replace (l@id) with (l0@id).
      apply H'.
      intros abs; apply NIN; auto.
      symmetry; apply H; auto.
Qed.

