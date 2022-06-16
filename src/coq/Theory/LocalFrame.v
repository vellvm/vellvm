(* begin hide *)
From Coq Require Import
     String Morphisms List.

From ITree Require Import
     ITree
     Basics.Monad
     Eq.Eqit
     TranslateFacts
     Events.State.

From Vellvm Require Import
     Utilities
     Syntax
     Semantics
     Utils.NoFailure
     Utils.PostConditions
     Theory.StatePredicates
     Theory.InterpreterCFG
     Theory.ExpLemmas
     Theory.InstrLemmas
     Theory.InterpreterCFG
     Theory.SymbolicInterpreter.

From ExtLib Require Import
     Core.RelDec
     Data.Map.FMapAList
     Structures.Maps.

Import ListNotations.
Import AlistNotations.
Import ITreeNotations.
Import SemNotations.
(* end hide *)

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
#[export] Hint Unfold In : core.

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

Ltac go := repeat (vred_C3 || rewrite translate_ret || rewrite translate_bind).
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

(* To be revisited, doesn't work for [conv] as is *)
Lemma instr_same_local : forall x i g l m,
    ⟦ (x,i) ⟧i3 g l m ⤳ lift_pred_L3 _ (local_has_changed l (def_sites x)).
Proof with __base.
  destruct i; intros.
  - destruct x; cbn; go...
  - destruct x; cbn; go...
    eapply has_post_bind_strong; [apply expr_are_pure |].
    admit.
    intros3; intros (-> & -> & ->).
    go...
  - destruct fn,x.
    + cbn; go.
      rewrite interp_cfg3_map_monad.
      apply has_post_bind_strong with (S := lift_state_cfgP (pure_P g l m)).
      apply map_monad_eutt_state3_ind; [intros [] ? ? ? ? (-> & -> & ->); apply expr_are_pure | cbn; intuition].
      admit.
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
        admit.
        intros3; intros (-> & -> & ->).
        eapply has_post_bind_strong; [apply Call_is_pure |].
        intros3; intros (-> & -> & ->).
        go...
    + cbn; go.
      rewrite interp_cfg3_map_monad.
      apply has_post_bind_strong with (S := lift_state_cfgP (pure_P g l m)).
      apply map_monad_eutt_state3_ind; [intros [] ? ? ? ? (-> & -> & ->); apply expr_are_pure | cbn; intuition].
      admit.
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
        admit.
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
    admit.
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
    admit.
    intros3; intros (-> & -> & ->).
    go.
    eapply has_post_bind_strong; [apply concretize_or_pick_is_pure |].
    intros3; intros (-> & -> & ->).
    go.
    eapply has_post_bind_strong; [apply expr_are_pure |].
    admit.
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
Admitted.

From Coq Require Import ListSet.
Import SetNotations.

Lemma code_def_cons :
  forall {T} i (c : code T),
    def_sites (i :: c ) = def_sites (fst i) +++ def_sites c.
Proof.
  intros ? [] ?; reflexivity.
Qed.
Arguments code_defs : simpl never.

Lemma set_add_empty_set : forall x xs, In x (∅ +++ xs) <-> In x xs.
Admitted.

Lemma set_union_empty_set : forall x xs, In x (∅ +++ xs) <-> In x xs.
Proof.
  induction xs as [| y xs IH]; [reflexivity |].
  cbn; split; intros IN.
Admitted.
Arguments code_defs : simpl never.

Lemma def_sites_code_cons : forall {T} id x i (c : code T),
    In id (def_sites (A := code T) ((x,i):: c))
    <-> (In id (def_sites x) \/ In id (def_sites c)).
Proof.
  induction c as [| [x' i'] c IH] using rev_ind.
  - destruct x; unfold def_sites, code_defs; cbn; intuition.
  - destruct x; cbn in *.
    + rewrite (code_def_cons (_,i)); cbn.
      split; intros IN.
      * apply set_union_elim in IN; destruct IN as [IN | IN]; intuition.
      * destruct IN as [[-> | abs] | IN]; try inv abs.
        apply set_union_intro1; cbn; auto.
        apply set_union_intro2; cbn; auto.
    + rewrite (code_def_cons (_,i)); cbn.
      split; intros IN.
      * apply set_union_elim in IN; destruct IN as [IN | IN]; intuition.
      * apply set_union_empty_set.
        intuition.
Qed.

Arguments code_defs : simpl never.
Lemma local_frame_code : forall c g l m,
    ⟦ c ⟧c3 g l m ⤳ lift_pred_L3 _ (local_has_changed l (def_sites c)).
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

From Vellvm Require Import Theory.DenotationTheory.

Ltac _intros := intros3; first [intros (-> & -> & ->) | intros -> | intros ?HP].

Definition lift_pure_cfgP {T : Type} (P : T -> Prop) : @state_cfg_TP T :=
  fun '(m,(l,(g,v))) => P v.

Definition andP {T : Type} (A B : T -> Prop) : T -> Prop := fun x => A x /\ B x.

Lemma local_has_changed_mono:
  forall xs ys l l',
    local_has_changed l xs l' ->
    (forall x, In x xs -> In x ys) ->
    local_has_changed l ys l'.
Proof.
  intros * HL HIN; red; intros.
  apply HL.
  intros abs; apply H.
  apply HIN; auto.
Qed.

Lemma local_has_changed_trans:
  forall xs l l' l'',
    local_has_changed l xs l' ->
    local_has_changed l' xs l'' ->
    local_has_changed l xs l''.
Proof.
  intros; red; intros.
  rewrite H, H0; auto.
Qed.

Lemma local_frame_phis : forall phis f g l m,
    ⟦ phis ⟧Φs3 f g l m ⤳ lift_pred_L3 _ (local_has_changed l (map fst phis)).
Proof.
  intros.
  cbn.
  go.
  rewrite interp_cfg3_map_monad.
  apply has_post_bind_strong
    with (S := andP (lift_state_cfgP (pure_P g l m))
                   (lift_pure_cfgP (fun l => forall x, In x (map fst l) -> In x (map fst phis)))).
  - induction phis as [| [x []] phis IH].
    + cbn; apply eutt_Ret; split; cbn; auto.
    + cbn; go.
      break_match_goal; cbn.
      2: rewrite exp_to_instr_raise;unfold raise; go; apply has_post_bind; intros3; inv e.
      go.
      eapply has_post_bind_strong; [apply expr_are_pure |].
      admit.
      _intros; go.
      cbn.
      eapply has_post_bind_strong; [apply IH |].
      _intros; go.
      destruct HP as [(-> & -> & ->) HP].
      cbn in *.
      apply eutt_Ret.
      split; cbn; auto.
      intros ? [<- | IN]; auto.
  - _intros.
    destruct HP as [(-> & -> & ->) HP].
    cbn in *.
    go.
    rewrite interp_cfg3_map_monad.
    apply has_post_bind_strong with (S := fun '(_, (l', (_, _))) => local_has_changed l (map fst phis) l').
    2: _intros; go; apply eutt_Ret; cbn; auto.
    apply map_monad_eutt_state3_ind; [intros [] ? ? ? ? ? | red; auto].
    eapply has_post_weaken; [apply LocalWrite_local_change |].
    _intros.
    cbn in *.
    apply (in_map fst), HP in H; cbn in H; clear HP.
    eapply local_has_changed_trans; eauto.
    eapply local_has_changed_mono; eauto.
    intros ? [-> | []]; auto.
Admitted.

Lemma terminator_are_pure : forall t,
    pure ⟦ t ⟧t3.
Proof with (apply eutt_Ret; do 2 red; auto).
  unfold pure; intros [] *; cbn.
  - destruct v; cbn.
    go.
    eapply has_post_bind_strong; [apply expr_are_pure |].
    admit.
    _intros; go...
  - go...
  - destruct v; cbn.
    go.
    eapply has_post_bind_strong; [apply expr_are_pure |].
    admit.
    _intros; go.
    eapply has_post_bind_strong; [apply ExpLemmas.concretize_or_pick_is_pure |].
    _intros.
    destruct d0; try (rewrite exp_to_instr_raise; apply failure_is_pure).
    2: rewrite exp_to_instr_raiseUB; apply UB_is_pure.
    break_match_goal; go...
  - go...
  - destruct v; cbn.
    go.
    eapply has_post_bind_strong; [apply expr_are_pure |].
    admit.
    _intros; go.
    eapply has_post_bind_strong; [apply ExpLemmas.concretize_or_pick_is_pure |].
    _intros; go.
    break_match_goal.
    rewrite exp_to_instr_raiseUB; apply UB_is_pure.
    go.
    unfold lift_undef_or_err.
    break_match_goal.
    break_match_goal.
    unfold raiseUB; go; apply has_post_bind; intros (? & ? & ? & []).
    break_match_goal.
    unfold raise; go; apply has_post_bind; intros (? & ? & ? & []).
    go.
    unfold lift_err.
    break_match_goal.
    unfold raise; go; apply has_post_bind; intros (? & ? & ? & []).
    go...
  - rewrite exp_to_instr_raise; apply failure_is_pure.
  - rewrite exp_to_instr_raise; apply failure_is_pure.
  - rewrite exp_to_instr_raise; apply failure_is_pure.
  - rewrite exp_to_instr_raiseUB; apply UB_is_pure.
Admitted.

Lemma not_in_set_union_l : forall (l1 l2 : set _) (x : _), ~ In x (l1 +++ l2) -> ~ In x l1.
Admitted.
Lemma not_in_set_union_r : forall (l1 l2 : list _) (x : _), ~ In x (l1 +++ l2) -> ~ In x l2.
Admitted.

Lemma local_frame_block : forall bk f g l m,
    ⟦ bk ⟧b3 f g l m ⤳ lift_pred_L3 _ (local_has_changed l (def_sites bk)).
Proof.
  intros; destruct bk.
  rewrite denote_block_unfold.
  go.
  eapply has_post_bind_strong; [apply local_frame_phis |].
  _intros.
  go.
  eapply has_post_bind_strong; [apply local_frame_code |].
  _intros.
  eapply has_post_weaken; [apply terminator_are_pure |].
  _intros.
  intros ? NIN.
  red in HP,HP0.
  cbn in NIN.
  destruct (in_dec raw_id_eq_dec x (map fst blk_phis)).
  apply not_in_set_union_l in NIN; exfalso; apply NIN; auto.
  destruct (in_dec raw_id_eq_dec x (def_sites blk_code)).
  apply not_in_set_union_r in NIN; exfalso; apply NIN; auto.
  apply HP in n.
  apply HP0 in n0.
  rewrite n,n0; reflexivity.
Qed.

Lemma interp_intrinsics_iter :
  forall {E F R I} `{FailureE -< F} (t: I -> itree (E +' IntrinsicE +' F) (I + R)) x,
             (interp_intrinsics (iter (C:=ktree _) t x)) ≈
             ITree.iter (fun x => interp_intrinsics (t x)) x.
Proof.
  intros.
  unfold interp_intrinsics at 1.
  rewrite InterpFacts.interp_iter.
  reflexivity.
Qed.

Lemma interp_global_iter :
  forall {k v map E F G R I} `{Map k v map} `{CeresSerialize.Serialize k} `{FailureE -< G }
    (t: I -> itree (E +' F +' (GlobalE _ _) +' G) (I + R)) x g,
    interp_global (ITree.iter t x) g ≈
    @Basics.iter _ MonadIter_stateT0 _ _ (fun x g => interp_global (t x) g) x g.
Proof.
  intros.
  apply interp_state_iter.
Qed.

Lemma interp_local_iter :
  forall {k v map E F G R I} `{Map k v map} `{CeresSerialize.Serialize k} `{FailureE -< G }
    (t: I -> itree (E +' F +' (LocalE _ _) +' G) (I + R)) x g,
    interp_local (ITree.iter t x) g ≈
    @Basics.iter _ MonadIter_stateT0 _ _ (fun x g => interp_local (t x) g) x g.
Proof.
  intros.
  apply interp_state_iter.
Qed.

Lemma interp_memory_iter :
  forall {E F R I} `{FailureE -< F} `{UBE -< F} `{PickE -< F}
    (t: I -> itree (E +' IntrinsicE +' MemoryE +' F) (I + R)) x m,
    interp_memory (ITree.iter t x) m ≈
    @Basics.iter _ MonadIter_stateT0 _ _ (fun x g => interp_memory (t x) g) x m.
Proof.
  intros.
  apply interp_state_iter.
Qed.

Lemma interp_cfg3_collapse :
  forall {R I} (t: I -> itree instr_E (I + R)) x g l m,
    interp_cfg3 (iter t x) g l m ≈
    ITree.iter (fun '(m,(l,(g,x))) =>
                  '(m,(l,(g,ir))) <- interp_cfg3 (t x) g l m;;
                  match ir with | inl i => Ret (inl (m,(l,(g,i)))) | inr r => Ret (inr (m,(l,(g,r)))) end)
    (m,(l,(g,x))).
Proof.
  intros.
  unfold interp_cfg3 at 1.
  rewrite interp_intrinsics_iter.
  rewrite interp_global_iter.
  unfold Basics.iter.
  unfold MonadIter_stateT0, Basics.iter, MonadIter_itree.
  rewrite interp_local_iter.
  unfold MonadIter_stateT0, Basics.iter, MonadIter_itree.
  cbn.
  rewrite interp_memory_iter.
  unfold MonadIter_stateT0, Basics.iter, MonadIter_itree.
  cbn.
  apply KTreeFacts.eutt_iter.
  red. intros (? & ? & ? & ?); cbn.
  unfold interp_cfg3.
  rewrite interp_local_bind, bind_bind.
  rewrite interp_memory_bind, bind_bind.
  apply eutt_eq_bind.
  intros (? & ? & ? & ?); cbn.
  rewrite interp_local_ret, bind_ret_l; cbn.
  rewrite interp_memory_ret, bind_ret_l; cbn.
  destruct s; cbn; reflexivity.
Qed.

(* Stateful, flow-insensitive inductive reasoning principle:
 *)
Arguments denote_block : simpl never.
Lemma has_post_denote_ocfg3 :
  forall bks fto g l m (I: state_cfgP),
    (forall bk id g' l' m' f,
        CFG.find_block bks id = Some bk ->
        I (m',(l',g')) ->
        ⟦ bk ⟧b3 f g' l' m' ⤳ lift_state_cfgP I) ->
    I (m,(l,g)) ->
    ⟦ bks ⟧bs3 fto g l m ⤳ lift_state_cfgP I.
Proof.
  intros.
  unfold denote_ocfg.
  rewrite interp_cfg3_collapse.
  apply has_post_iter_strong with (Inv := lift_state_cfgP I); auto.
  _intros; destruct p; cbn.
  break_match_goal.
  - go.
    eapply has_post_bind_strong.
    eapply H; eauto.
    _intros.
    break_match_goal; cbn; go.
    apply eutt_Ret; cbn; auto.
    apply eutt_Ret; cbn; auto.
  - go.
    apply eutt_Ret; cbn; auto.
Qed.

Definition sublist {A} (xs ys : list A) : Prop :=
  forall x, In x xs -> In x ys.

Lemma sublist_nil {A} :
  forall (xs : list A),
    sublist xs [] ->
    xs = [].
Proof.
  intros [| x xs] SUB; auto.
  exfalso.
  specialize (SUB x (or_introl eq_refl)).
  inv SUB.
Qed.

#[global] Instance sublist_refl {A} : Reflexive (@sublist A).
Proof.
  repeat red; intros; auto.
Qed.

Lemma sublist_app_l {A} :
  forall (ys xs zs : list A),
  sublist xs ys ->
  sublist xs (ys ++ zs).
Proof.
  intros; intros x IN.
  apply in_or_app; auto.
Qed.

Lemma sublist_app_r {A} :
  forall (ys xs zs : list A),
  sublist xs zs ->
  sublist xs (ys ++ zs).
Proof.
  intros; intros x IN.
  apply in_or_app; auto.
Qed.

Lemma sublist_set_union_l :
  forall (ys xs zs : list _),
  sublist xs ys ->
  sublist xs (ys +++ zs).
Proof.
Admitted.

Lemma sublist_set_union_r :
  forall (ys xs zs : list _),
  sublist xs zs ->
  sublist xs (ys +++ zs).
Proof.
Admitted.

Lemma def_sites_block_in_ocfg :
  forall {T} (bk : block T) id bks,
    find_block bks id = Some bk ->
    sublist (def_sites bk) (def_sites bks).
Proof.
  induction bks as [| bk0 bks IH]; [intros abs; inv abs |].
  intros FIND.
  cbn.
  case_eq_id id bk0.(blk_id).
  - rewrite ScopeTheory.find_block_eq in FIND; auto.
    inv FIND.
    eapply sublist_set_union_l; reflexivity.
  - rewrite ScopeTheory.find_block_ineq in FIND; auto.
    eapply sublist_set_union_r, IH; auto.
Qed.

Lemma local_has_changed_refl : forall l xs,
    local_has_changed l xs l.
Proof.
  intros.
  red; intros; reflexivity.
Qed.

Lemma local_frame_ocfg : forall bks fto g l m,
    ⟦ bks ⟧bs3 fto g l m ⤳ lift_pred_L3 _ (local_has_changed l (def_sites bks)).
Proof.
  intros.
  eapply has_post_weaken.
  apply has_post_denote_ocfg3 with (I := fun '(_,(l',_)) => local_has_changed l (def_sites bks) l').
  - intros * FIND HP.
    eapply has_post_weaken.
    apply local_frame_block.
    intros (? & ? & ? & ?) HP'.
    cbn in *.
    eapply local_has_changed_trans.
    apply HP.
    eapply local_has_changed_mono. eauto.
    intros * IN.
    eapply def_sites_block_in_ocfg; eauto.
  - apply local_has_changed_refl.
  - _intros.
    cbn in *.
    auto.
Qed.
