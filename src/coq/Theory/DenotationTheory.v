(* begin hide *)

From Coq Require Import
     String
     List.

From ITree Require Import
     ITree
     ITreeFacts
     Basics.HeterogeneousRelations
     Events.State
     Events.StateFacts
     InterpFacts
     KTreeFacts
     Eq.Eqit.

From Vellvm Require Import
     Utilities
     Syntax
     Semantics
     Syntax.ScopeTheory
     Utils.PostConditions.

#[export] Remove Hints Eqv.EqvWF_Build : typeclass_instances.

Set Implicit Arguments.
Set Strict Implicit.

Import ListNotations.

Import MonadNotation.
Open Scope list_scope.
Open Scope monad_scope.
Open Scope itree.
Import ITreeNotations.
Import SemNotations.

(* end hide *)

(** * Structural equations at the representation level

We prove here the equational theory that holds independently of the
interpretation of events.
These equations are expressed in terms of [eutt eq] over uninterpreted trees.
They derive from the [itree] combinators used to compute the uninterpreted
representation VIR's syntax.

In particular, notice that since [interp] is a iterative-monad morphism that respects
[eutt eq], these equations get transported at all levels of interpretations.

*)

Module DenoteTactics.

  #[export] Hint Rewrite @bind_ret_l : rwexp.
  #[export] Hint Rewrite @bind_bind : rwexp.
  #[export] Hint Rewrite @translate_ret : rwexp.
  #[export] Hint Rewrite @translate_bind : rwexp.
  #[export] Hint Rewrite @translate_trigger : rwexp.

  Ltac go := autorewrite with rwexp.

End DenoteTactics.
Import DenoteTactics.

(** [denote_code] *)

Lemma denote_code_nil :
  ⟦ [] ⟧c ≈ Ret tt.
Proof.
  intros.
  cbn.
  go.
  reflexivity.
Qed.

Lemma denote_code_app :
  forall a b,
    ⟦ a ++ b ⟧c ≈ ⟦ a ⟧c;;  ⟦ b ⟧c.
Proof.
  induction a; intros b.
  - cbn; go; reflexivity.
  - cbn in *.
    go.
    apply eutt_eq_bind; intros ().
    go.
    setoid_rewrite bind_ret_l.
    rewrite IHa.
    go.
    reflexivity.
Qed.

Lemma denote_code_app_eq_itree :
  forall a b,
    ⟦ a ++ b ⟧c ≅ ITree.bind ⟦ a ⟧c (fun _ => ⟦ b ⟧c).
Proof.
  induction a; intros b.
  - cbn.
    go.
    eapply eq_itree_clo_bind with (UU := eq); [reflexivity | intros ? ? ->; reflexivity].
  - cbn in *.
    go.
    eapply eq_itree_clo_bind with (UU := eq); [reflexivity | intros ? ? ->].
    setoid_rewrite bind_ret_l.
    setoid_rewrite bind_bind.
    setoid_rewrite bind_ret_l.
    rewrite IHa.
    setoid_rewrite bind_bind.
    eapply eq_itree_clo_bind with (UU := eq); [reflexivity | intros ? ? ->].
    setoid_rewrite bind_ret_l.
    eapply eq_itree_clo_bind with (UU := eq); [reflexivity | intros ? ? ->].
    reflexivity.
Qed.

Lemma denote_code_cons :
  forall i c,
     ⟦ i::c ⟧c ≈  ⟦ i ⟧i;; ⟦ c ⟧c.
Proof.
  intros.
  cbn.
  go.
  apply eutt_eq_bind; intros ().
  go.
  setoid_rewrite bind_ret_l.
  reflexivity.
Qed.

Lemma denote_code_singleton :
  forall i,
    ⟦ [i] ⟧c ≈ ⟦ i ⟧i.
Proof.
  intros a.
  cbn.
  go.
  bind_ret_r2.
  apply eutt_eq_bind; intros [].
  go.
  reflexivity.
Qed.

(** [denote_phi] *)
(* TODO: make a choice about it and move *)
Opaque assoc.
Lemma denote_phi_hd : forall bid e id τ tl,
    ⟦ (id, Phi τ ((bid,e)::tl)) ⟧Φ bid ≈ uv <- ⟦ e at τ ⟧e;; Ret (id,uv).
Proof.
  intros; cbn.
  rewrite assoc_hd; reflexivity.
Qed.

Lemma denote_phi_tl : forall bid bid' e id τ tl,
    bid <> bid' ->
    ⟦ (id, Phi τ ((bid',e)::tl)) ⟧Φ bid ≈ ⟦ (id, Phi τ tl) ⟧Φ bid.
Proof.
  intros; cbn.
  rewrite assoc_tl; auto; reflexivity.
Qed.

Lemma denote_no_phis : forall x,
    ⟦ [] ⟧Φs x ≈ Ret tt.
Proof.
  intros.
  cbn. go.
  cbn; go.
  unfold denote_phis; cbn.
  reflexivity.
Qed.

(** [denote_block] *)
Lemma denote_block_unfold_cont :
  forall {R} id phis c t s origin (k : _ -> itree _ R),
    ⟦ mk_block id phis c t s ⟧b origin >>= k
    ≈
    ⟦ phis ⟧Φs origin;;
    ⟦ c ⟧c;;
    translate exp_to_instr ⟦ t ⟧t >>= k.
Proof.
  intros; cbn; repeat setoid_rewrite bind_bind.
  reflexivity.
Qed.

Lemma denote_block_unfold :
  forall id phis c t s origin,
    ⟦ mk_block id phis c t s ⟧b origin ≈
    ⟦ phis ⟧Φs origin;;
    ⟦ c ⟧c;;
    translate exp_to_instr ⟦ t ⟧t.
Proof.
  intros; cbn; reflexivity.
Qed.

(** [denote_ocfg] *)
Lemma denote_ocfg_nil: forall s, ⟦ [] ⟧bs s ≈ Ret (inl s).
Proof.
  intros []; unfold denote_ocfg.
  match goal with
  | |- CategoryOps.iter (C := ktree _) ?body ?s ≈ _ =>
    rewrite (unfold_iter body s)
  end.
  cbn; go.
  reflexivity.
Qed.

Lemma denote_ocfg_unfold_in: forall bks bid_from bid_src bk,
    find_block bks bid_src = Some bk ->
    ⟦ bks ⟧bs (bid_from, bid_src) ≈
           vob <- ⟦ bk ⟧b bid_from ;;
    match vob with
    | inr v => Ret (inr v)
    | inl bid_target => ⟦ bks ⟧bs (bid_src, bid_target)
    end.
Proof.
  intros * GET_BK.
  cbn. unfold denote_ocfg at 1.
  rewrite KTreeFacts.unfold_iter_ktree. cbn.
  rewrite GET_BK.
  repeat setoid_rewrite bind_bind.
  repeat (apply eutt_eq_bind; intros ?).
  break_sum; rewrite bind_ret_l; [|reflexivity].
  rewrite tau_eutt; reflexivity.
Qed.

Lemma denote_ocfg_unfold_not_in: forall bks bid_from bid_src,
    find_block bks bid_src = None ->
    ⟦ bks ⟧bs (bid_from, bid_src) ≈ Ret (inl (bid_from,bid_src)).
Proof.
  intros * GET_BK.
  unfold denote_ocfg.
  rewrite KTreeFacts.unfold_iter_ktree.
  rewrite GET_BK; cbn.
  rewrite bind_ret_l.
  reflexivity.
Qed.

Lemma denote_ocfg_unfold_in_euttge: forall bks bid_from bid_src bk,
    find_block bks bid_src = Some bk ->
    ⟦ bks ⟧bs (bid_from, bid_src) ≳
           vob <- ⟦ bk ⟧b bid_from ;;
    match vob with
    | inr v => Ret (inr v)
    | inl bid_target => ⟦ bks ⟧bs (bid_src, bid_target)
    end.
Proof.
  intros * GET_BK.
  cbn. unfold denote_ocfg at 1.
  rewrite KTreeFacts.unfold_iter_ktree. cbn.
  rewrite GET_BK.
  repeat setoid_rewrite bind_bind.
  repeat (eapply eqit_bind; [reflexivity | intros ?]).
  break_sum; rewrite bind_ret_l; [|reflexivity].
  rewrite tau_euttge; reflexivity.
Qed.

Lemma denote_ocfg_unfold_in_eq_itree: forall bks bid_from bid_src bk,
    find_block bks bid_src = Some bk ->
    ⟦ bks ⟧bs (bid_from, bid_src) ≅
           vob <- ⟦ bk ⟧b bid_from ;;
    match vob with
    | inr v => Ret (inr v)
    | inl bid_target => Tau (⟦ bks ⟧bs (bid_src, bid_target))
    end.
Proof.
  intros * GET_BK.
  cbn. unfold denote_ocfg at 1.
  rewrite KTreeFacts.unfold_iter_ktree. cbn.
  rewrite GET_BK.
  repeat setoid_rewrite bind_bind.
  repeat (eapply eqit_bind; [reflexivity | intros ?]).
  break_sum; rewrite bind_ret_l; [|reflexivity].
  apply eqit_Tau.
  reflexivity.
Qed.

Lemma denote_ocfg_unfold_not_in_eq_itree: forall bks bid_from bid_src,
    find_block bks bid_src = None ->
    ⟦ bks ⟧bs (bid_from, bid_src) ≅ Ret (inl (bid_from,bid_src)).
Proof.
  intros * GET_BK.
  unfold denote_ocfg.
  rewrite KTreeFacts.unfold_iter_ktree.
  rewrite GET_BK; cbn.
  rewrite bind_ret_l.
  reflexivity.
Qed.

Lemma denote_ocfg_unfold_eq_itree: forall bks bid_from bid_src,
    ⟦ bks ⟧bs (bid_from, bid_src) ≅
           match find_block bks bid_src with
           | Some bk => vob <- ⟦ bk ⟧b bid_from ;;
                       match vob with
                       | inr v => Ret (inr v)
                       | inl bid_target => Tau (⟦ bks ⟧bs (bid_src, bid_target))
                       end
           | None => Ret (inl (bid_from,bid_src))
           end.
Proof.
  intros *.
  break_match_goal.
  - rewrite denote_ocfg_unfold_in_eq_itree; eauto; reflexivity.
  - rewrite denote_ocfg_unfold_not_in_eq_itree; eauto; reflexivity.
Qed.

Section Outputs.

  (** * outputs soundness *)

  Lemma raise_has_all_posts : forall {E X} `{FailureE -< E} s Q,
    @raise E X _ s ⤳ Q.
  Proof.
    unfold raise; intros.
    apply has_post_bind; intros [].
  Qed.

  Lemma raiseUB_has_all_posts : forall {E X} `{UBE -< E} s Q,
      @raiseUB E _ X s ⤳ Q.
  Proof.
    unfold raise; intros.
    apply has_post_bind; intros [].
  Qed.

  Lemma unEither_eta : forall {T m A} (x : eitherT T m A), {|unEitherT := unEitherT x|} = x.
  Proof.
    intros.
    destruct x.
    f_equal.
  Qed.

  Lemma denote_terminator_exits_in_outputs :
    forall term,
      ⟦ term ⟧t ⤳ sum_pred (fun id => In id (terminator_outputs term)) TT.
  Proof.
    intros []; cbn; try (apply raise_has_all_posts || apply eutt_Ret; cbn; eauto).
    - destruct v.
      apply has_post_bind; intros ?.
      apply eutt_Ret; cbn; eauto.
    - destruct v; cbn.
      apply has_post_bind; intros ?.
      apply has_post_bind; intros ?.
      break_match_goal; try (apply raise_has_all_posts || apply raiseUB_has_all_posts).
      break_match_goal; apply eutt_Ret; cbn; eauto.
    - destruct v; cbn.
      apply has_post_bind; intros ?.
      apply has_post_bind; intros ?.
      break_match_goal;
        try (apply raise_has_all_posts || apply raiseUB_has_all_posts).
      unfold lift_undef_or_err.
      do 2 break_match_goal.
      unfold raiseUB; go; apply has_post_bind; intros [].
      break_match_goal.
      unfold raise; go; apply has_post_bind; intros [].
      go.
      subst.
      assert (List.map snd brs = List.map snd l).
      {
        revert l Hequ; induction brs as [| br brs IH].
        - intros ? eq; inv eq; reflexivity.
        - intros ? eq; inv eq.
          repeat (break_match_hyp; cbn in *; try inv_sum).
          f_equal; apply IH.
          rewrite <- Heqs1.
          Set Nested Proofs Allowed.

          rewrite unEither_eta.
          reflexivity.
      }
      rewrite H.
      clear.
      induction l as [| br brs IH].
      + cbn; intros.
        apply eutt_Ret; red; auto.
      + cbn; intros.
        repeat (cbn; break_match_goal; try apply raise_has_all_posts).
        all: try apply eutt_Ret; red; auto.
        all: try subst; eapply has_post_weaken; [apply IH | intros [] ?; cbn in *; intuition].
    - apply raiseUB_has_all_posts.
  Qed.

  Definition exits_in_outputs {t} ocfg : block_id * block_id + uvalue -> Prop :=
    sum_pred (fun fto => In (snd fto) (@outputs t ocfg)) TT.

  Lemma denote_bk_exits_in_outputs :
    forall b from,
      ⟦ b ⟧b from ⤳ sum_pred (fun id => In id (successors b)) TT.
  Proof.
    intros.
    cbn.
    apply has_post_bind; intros [].
    apply has_post_bind; intros [].
    apply has_post_translate.
    apply denote_terminator_exits_in_outputs.
  Qed.

  (* Given a predicate [Qb] on pairs of block ids (the origin for phi-nodes and the input)
   and a predicate [Qv] on values, we establish that both hold after the denotation of an open_cfg if:
   - [Qb] holds at the initial entry point
   - [Qb] and [Qv] are preserved by the denotation of any blocks in the open cfg, assuming [Qb]
   *)
  Lemma denote_ocfg_has_post_strong :
    forall (bks : ocfg _) fto (Qb : block_id * block_id -> Prop) (Qv : uvalue -> Prop)
           (INIT : Qb fto)
           (IND : forall fto (b : block dtyp),
               Qb fto ->
               find_block bks (snd fto) = Some b ->
               ⟦ b ⟧b (fst fto) ⤳ sum_pred (fun to => Qb (snd fto, to)) Qv),
      ⟦ bks ⟧bs fto ⤳ sum_pred Qb Qv.
  Proof.
    intros * INIT IND.
    eapply has_post_iter_strong; eauto.
    intros [f to] PRE.
    flatten_goal.
    - specialize (IND (f,to) b).
      eapply eutt_post_bind; [apply IND |]; auto.
      intros [id | v]; cbn; intros ?; apply eutt_Ret; auto.
    - apply eutt_Ret; auto.
  Qed.

  (* A weaker but sometimes easier to use modular way to prove postconditions of open cfgs:
   - assuming that all blocks in the open cfg admits as postconditions [sum_pred Qb Qv]
   - and assuming that we indeed enter the [open_cfg]
   then we get [Qb/Qv], and ignore the origin of the jump.
   *)
  Lemma denote_ocfg_has_post :
    forall (bks : ocfg _) fto (Qb : block_id -> Prop) (Qv : uvalue -> Prop)
           (ENTER : In (snd fto) (inputs bks))
           (IND : forall fto (b : block dtyp),
               find_block bks (snd fto) = Some b ->
               ⟦ b ⟧b (fst fto) ⤳ sum_pred Qb Qv),
      ⟦ bks ⟧bs fto ⤳ sum_pred (prod_pred TT Qb) Qv.
  Proof.
    intros * IN IND.
    apply has_post_iter_strong with (Inv := fun x => In (snd x) (inputs bks) \/ Qb (snd x))
    ; eauto.
    intros [f to] HYP.
    flatten_goal.
    - specialize (IND (f,to) b).
      eapply eutt_post_bind; [apply IND |]; auto.
      intros [id | v]; cbn; intros ?; apply eutt_Ret; cbn; auto.
    - apply eutt_Ret.
      split; auto.
      destruct HYP as [abs | POST]; auto.
      apply find_block_in_inputs in abs as [? abs]; cbn in abs; rewrite abs in Heq; inv Heq.
  Qed.

  Lemma denote_ocfg_exits_in_outputs :
    forall bks fto,
      In (snd fto) (inputs bks) ->
      ⟦ bks ⟧bs fto ⤳ exits_in_outputs bks.
  Proof.
    intros * IN.
    apply has_post_weaken with (P := sum_pred (prod_pred TT (fun b => In b (outputs bks))) TT).
    2: intros [[]|] ?; cbn in *; intuition.
    apply denote_ocfg_has_post; eauto.
    intros.
    eapply has_post_weaken.
    eapply denote_bk_exits_in_outputs.
    intros []; cbn; intuition.
    eapply In_bk_outputs; eauto.
  Qed.

End Outputs.

(** * denote_ocfg  *)

Lemma denote_ocfg_app_no_edges :
  forall (bks1 bks2 : ocfg _) fto,
    find_block bks1 (snd fto) = None ->
    no_reentrance bks1 bks2 ->
    ⟦ bks1 ++ bks2 ⟧bs fto ≈ ⟦ bks2 ⟧bs fto.
Proof.
  intros bks1 bks2 [f to] FIND NOBACK.
  apply (@KTreeFacts.eutt_iter_gen _ _ _ (fun fto fto' => fto' = fto /\ find_block bks1 (snd fto) = None)); auto.
  clear f to FIND; intros fto fto' [-> FIND]; destruct fto as [f to] .
  cbn in *.
  epose proof (find_block_none_app _ bks2 _ FIND) as FIND_L1L2.
  rewrite FIND_L1L2.
  destruct (find_block bks2 to) eqn:FIND_L2.
  - eapply eutt_post_bind.
    apply denote_bk_exits_in_outputs.
    intros [id | v] ?; cbn; apply eutt_Ret; eauto.
    eapply inl_morphism; split; auto.
    eapply find_block_not_in_inputs,no_reentrance_not_in; eauto.
    eapply In_bk_outputs; eauto.

  - apply eutt_Ret; right; auto.
Qed.

Lemma denote_ocfg_app :
  forall bks1 bks2 fto,
    no_reentrance bks1 bks2 ->
    ⟦ bks1 ++ bks2 ⟧bs fto ≈
                    'x <- ⟦ bks1 ⟧bs fto;;
    match x with
    | inl fto2 => ⟦ bks2 ⟧bs fto2
    | inr v => Ret (inr v)
    end.
Proof.
  intros * NOBACK.
  revert fto.
  einit.
  ecofix CIH.
  intros [f to].
  destruct (find_block bks1 to) eqn:FIND.
  - unfold denote_ocfg.
    unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree.
    match goal with
      |- euttG _ _ _ _ _ ?t _ => remember t; rewrite unfold_iter; subst
    end.
    rewrite unfold_iter; cbn.
    match_rewrite.
    rewrite !bind_bind.
    pose proof find_block_some_app bks1 bks2 to FIND as FIND_APP.
    rewrite FIND_APP.
    cbn.
    rewrite !bind_bind.
    match goal with
      |- euttG _ _ _ _ _ ?t _ => remember t
    end.
    subst; ebind; econstructor; [reflexivity | intros ? ? <-].
    ebind; econstructor; [reflexivity | intros ? ? <-].
    ebind; econstructor; [reflexivity | intros ? ? <-].
    destruct u2 as [bid | v].
    + rewrite !bind_ret_l.
      rewrite bind_tau.
      etau.
    + rewrite !bind_ret_l.
      eret.
  - efinal.
    rewrite denote_ocfg_app_no_edges; auto.
    rewrite denote_ocfg_unfold_not_in with (bks := bks1); auto.
    rewrite bind_ret_l; reflexivity.
Qed.

Lemma denote_ocfg_flow_left :
  forall ocfg1 ocfg2 fto,
    independent_flows ocfg1 ocfg2 ->
    In (snd fto) (inputs ocfg1) ->
    ⟦ ocfg1 ++ ocfg2 ⟧bs fto ≈
                      ⟦ ocfg1 ⟧bs fto.
Proof.
  intros * INDEP IN.
  rewrite denote_ocfg_app; [| auto using independent_flows_no_reentrance_l].
  bind_ret_r2.

  eapply eutt_post_bind; [apply denote_ocfg_exits_in_outputs; eauto |].
  intros [[f to] | ?] EXIT; [| reflexivity].
  rewrite denote_ocfg_unfold_not_in; [reflexivity |].
  cbn in *.
  apply find_block_not_in_inputs.
  eapply no_reentrance_not_in; eauto.
  apply INDEP.
Qed.

Lemma denote_ocfg_flow_right :
  forall ocfg1 ocfg2 fto,
    independent_flows ocfg1 ocfg2 ->
    In (snd fto) (inputs ocfg2) ->
    ⟦ ocfg1 ++ ocfg2 ⟧bs fto ≈
                      ⟦ ocfg2 ⟧bs fto.
Proof.
  intros * INDEP IN.
  rewrite denote_ocfg_app; [| auto using independent_flows_no_reentrance_l].
  destruct fto as [f to]; cbn in *.
  rewrite denote_ocfg_unfold_not_in.
  rewrite bind_ret_l; reflexivity.
  eapply find_block_not_in_inputs, no_duplicate_bid_not_in_l; eauto using independent_flows_no_duplicate_bid.
Qed.

Opaque denote_block.
Lemma denote_ocfg_prefix :
  forall (prefix bks' postfix bks : ocfg dtyp) (from to: block_id),
    bks = (prefix ++ bks' ++ postfix) ->
    wf_ocfg_bid bks ->
    ⟦ bks ⟧bs (from, to) ≈
           'x <- ⟦ bks' ⟧bs (from, to);;
    match x with
    | inl x => ⟦ bks ⟧bs x
    | inr x => Ret (inr x)
    end
.
Proof.
  intros * ->; revert from to.
  einit.
  ecofix CIH.
  clear CIHH.
  intros * WF.
  destruct (find_block bks' to) as [bk |] eqn:EQ.
  - unfold denote_ocfg at 1 3.
    setoid_rewrite KTreeFacts.unfold_iter_ktree.
    cbn; rewrite !bind_bind.
    assert (find_block (prefix ++ bks' ++ postfix) to = Some bk).
    {
      erewrite find_block_app_r_wf; eauto.
      erewrite find_block_app_l_wf; eauto.
      eapply wf_ocfg_bid_app_r; eauto.
    }
    do 2 match_rewrite.
    rewrite !bind_bind.
    eapply euttG_bind; econstructor; [reflexivity | intros [] ? <-].
    + rewrite !bind_ret_l; cbn.
      rewrite bind_tau; etau.
    + rewrite !bind_ret_l.
      reflexivity.
  - edrop.
    rewrite (denote_ocfg_unfold_not_in bks'); auto.
    rewrite bind_ret_l.
    reflexivity.
Qed.
Transparent denote_block.
