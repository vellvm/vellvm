(* begin hide *)

From Coq Require Import
     List.

From ITree Require Import
     ITree
     ITreeFacts
     Basics.HeterogeneousRelations
     Events.State
     Events.StateFacts
     InterpFacts
     KTreeFacts
     Eq.Eq.

From Vellvm Require Import
     Utils.Util
     Utils.Tactics
     Utils.PropT
     Syntax.CFG
     Syntax.LLVMAst
     Syntax.AstLib
     Syntax.Scope
     Semantics.TopLevel
     Syntax.Traversal
     Syntax.DynamicTypes
     Semantics.LLVMEvents
     PostConditions.

Remove Hints Eqv.EqvWF_Build : typeclass_instances.

Set Implicit Arguments.
Set Strict Implicit.

Import ListNotations.
Import D.
Import Eq.
(* Import CatNotations. *)

Import MonadNotation.
Open Scope monad_scope.
Open Scope itree.

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

(** [denote_code] *)

Lemma denote_code_nil :
  denote_code [] ≈ Ret tt.
Proof.
  intros.
  cbn. rewrite bind_ret_l.
  reflexivity.
Qed.

Lemma denote_code_app :
  forall a b,
    denote_code (a ++ b)%list ≈ ITree.bind (denote_code a) (fun _ => denote_code b).
Proof.
  induction a; intros b.
  - cbn. rewrite 2 bind_ret_l.
    reflexivity.
  - simpl.
    unfold denote_code, map_monad_ in *.
    simpl in *.
    repeat rewrite bind_bind.
    specialize (IHa b).
    apply eutt_eq_bind; intros ().
    rewrite bind_bind.
    setoid_rewrite bind_ret_l.
    setoid_rewrite IHa.
    repeat rewrite bind_bind.
    setoid_rewrite bind_ret_l.
    reflexivity.
Qed.

Lemma denote_code_cons :
  forall a l,
    denote_code (a::l) ≈ ITree.bind (denote_instr a) (fun _ => denote_code l).
Proof.
  intros.
  rewrite list_cons_app, denote_code_app.
  cbn.
  repeat rewrite bind_bind.
  apply eutt_eq_bind; intros ().
  rewrite !bind_bind, !bind_ret_l.
  reflexivity.
Qed.

Lemma denote_code_singleton :
  forall a,
    denote_code [a] ≈ denote_instr a.
Proof.
  intros a.
  rewrite denote_code_cons.
  setoid_rewrite denote_code_nil.
  cbn.
  epose proof bind_ret_r.
  specialize (H (denote_instr a)).
  rewrite <- H.
  rewrite bind_bind.
  apply eutt_eq_bind; intros []; rewrite bind_ret_l; reflexivity. 
Qed.

(** [denote_phi] *)
Opaque assoc.
Lemma denote_phi_hd : forall bid e id τ tl,
    denote_phi bid (id, Phi τ ((bid,e)::tl)) ≈ uv <- denote_exp (Some τ) e;; Ret (id,uv).
Proof.
  intros; cbn.
  rewrite assoc_hd; reflexivity.
Qed.

Lemma denote_phi_tl : forall bid bid' e id τ tl,
    bid <> bid' ->
    denote_phi bid (id, Phi τ ((bid',e)::tl)) ≈ denote_phi bid (id, Phi τ tl).
Proof.
  intros; cbn.
  rewrite assoc_tl; auto; reflexivity.
Qed.

Lemma denote_no_phis : forall x,
    denote_phis x [] ≈ Ret tt.
Proof.
  intros.
  unfold denote_phis; cbn.
  rewrite bind_ret_l; cbn.
  rewrite bind_ret_l; cbn.
  reflexivity.
Qed.

(** [denote_ocfg] *)
Lemma denote_ocfg_nil: forall s, denote_ocfg [] s ≈ ret (inl s).
Proof.
  intros []; unfold denote_ocfg.
  match goal with
  | |- CategoryOps.iter (C := ktree _) ?body ?s ≈ _ =>
    rewrite (unfold_iter body s)
  end.
  repeat (cbn; (rewrite bind_bind || rewrite bind_ret_l)).
  reflexivity.
Qed.

Lemma denote_ocfg_unfold_in: forall bks bid_from bid_src bk,
    find_block bks bid_src = Some bk ->
    denote_ocfg bks (bid_from, bid_src) ≈
    vob <- denote_block bk bid_from ;;
    match vob with
    | inr v => ret (inr v)
    | inl bid_target => denote_ocfg bks (bid_src, bid_target)
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
    denote_ocfg bks (bid_from, bid_src) ≈ Ret (inl (bid_from,bid_src)).
Proof.
  intros * GET_BK.
  unfold denote_ocfg.
  rewrite KTreeFacts.unfold_iter_ktree.
  rewrite GET_BK; cbn.
  rewrite bind_ret_l.
  reflexivity.
Qed.

(** * outputs soundness *)

Lemma denote_terminator_exits_in_outputs :
  forall term,
    denote_terminator term ⤳ sum_pred (fun id => In id (terminator_outputs term)) TT.
Proof.
  unfold has_post; intros []; cbn;
    unfold raise, Exception.throw, raiseUB;
    try (einit; estep; intros []).

  - destruct v. 
    apply eutt_eq_bind; intros ?.
    apply eutt_Ret; cbn; eauto.

  - destruct v; cbn.
    apply eutt_eq_bind; intros ?.
    apply eutt_eq_bind; intros ?.
    unfold raise, Exception.throw, raiseUB.
    destruct u0; cbn;
      try (einit; estep; intros []).
    flatten_goal; cbn; apply eutt_Ret; eauto; left.
Qed.

Definition exits_in_outputs {t} ocfg : block_id * block_id + uvalue -> Prop :=
  sum_pred (fun fto => In (snd fto) (@outputs t ocfg)) TT.

Lemma denote_bk_exits_in_outputs :
  forall b from,
    denote_block b from ⤳ sum_pred (fun id => In id (bk_outputs b)) TT.
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
        denote_block b (fst fto) ⤳ sum_pred (fun to => Qb (snd fto, to)) Qv), 
    denote_ocfg bks fto ⤳ sum_pred Qb Qv.
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
        denote_block b (fst fto) ⤳ sum_pred Qb Qv),
    denote_ocfg bks fto ⤳ sum_pred (prod_pred TT Qb) Qv.
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
  forall ocfg fto,
    In (snd fto) (inputs ocfg) ->
    denote_ocfg ocfg fto ⤳ exits_in_outputs ocfg.
Proof.
  intros * IN.
  apply has_post_weaken with (P := sum_pred (prod_pred TT (fun b => In b (outputs ocfg))) TT).
  2: intros [[]|] ?; cbn in *; intuition.
  apply denote_ocfg_has_post; eauto.
  intros.
  eapply has_post_weaken.
  eapply denote_bk_exits_in_outputs.
  intros []; cbn; intuition.
  eapply In_bk_outputs; eauto.
Qed.

(** * denote_ocfg  *)

Lemma denote_ocfg_app_no_edges :
  forall (bks1 bks2 : ocfg _) fto,
    find_block bks1 (snd fto) = None ->
    no_reentrance bks1 bks2 ->
    denote_ocfg (bks1 ++ bks2) fto ≈ denote_ocfg bks2 fto.
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

Import ITreeNotations.
Lemma denote_ocfg_app :
  forall bks1 bks2 fto,
    no_reentrance bks1 bks2 ->
    denote_ocfg (bks1 ++ bks2) fto ≈ ITree.bind (denote_ocfg bks1 fto)
               (fun x =>
                  match x with
                  | inl fto2 => denote_ocfg bks2 fto2
                  | inr v => ret (inr v)
                  end).
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
    rewrite FIND.
    rewrite !bind_bind.
    pose proof find_block_some_app bks1 bks2 _ to FIND as FIND_APP.
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
    denote_ocfg (ocfg1 ++ ocfg2) fto ≈
    denote_ocfg ocfg1 fto.
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
    denote_ocfg (ocfg1 ++ ocfg2) fto ≈
    denote_ocfg ocfg2 fto.
Proof.
  intros * INDEP IN.
  rewrite denote_ocfg_app; [| auto using independent_flows_no_reentrance_l].
  destruct fto as [f to]; cbn in *.
  rewrite denote_ocfg_unfold_not_in.
  rewrite bind_ret_l; reflexivity.
  eapply find_block_not_in_inputs, no_duplicate_bid_not_in_l; eauto using independent_flows_no_duplicate_bid.
Qed.

