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
     Util
     PropT
     DynamicTypes
     CFG
     LLVMAst
     AstLib
     LLVMEvents
     TopLevel
     Tactics
     Traversal
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

(** [find_block] *)

Lemma find_block_nil: forall {T} b, find_block T [] b = None. 
Proof.
  reflexivity.
Qed.

Lemma find_block_eq: forall {T} x b bs,
    blk_id b = x ->
    find_block T (b:: bs) x = Some b.
Proof.
  intros; cbn.
  rewrite H.
  destruct (Eqv.eqv_dec_p x x).
  reflexivity.
  contradiction n; reflexivity.
Qed.

Lemma find_block_ineq: forall {T} x b bs,
    blk_id b <> x ->
    find_block T (b::bs) x = find_block T bs x. 
Proof.
  intros; cbn.
  destruct (Eqv.eqv_dec_p (blk_id b)) as [EQ | INEQ].
  unfold Eqv.eqv, AstLib.eqv_raw_id in *; intuition.
  reflexivity.
Qed.

Lemma find_none_app:
  forall {A} (l1 l2 : list A) pred,
    find pred l1 = None ->
    find pred (l1 ++ l2) = find pred l2.
Proof.
  induction l1; intros l2 pred FIND.
  - reflexivity.
  - cbn in FIND; cbn.
    destruct (pred a); inversion FIND.
    auto.
Qed.

Lemma find_some_app:
  forall {A} (l1 l2 : list A) a pred,
    find pred l1 = Some a ->
    find pred (l1 ++ l2) = Some a.
Proof.
  induction l1 as [|x l1']; intros l2 a pred FIND.
  - inversion FIND.
  - cbn in FIND. destruct (pred x) eqn:PRED.
    + inversion FIND; cbn; subst.
      rewrite PRED. reflexivity.
    + cbn. rewrite PRED.
      auto.
Qed.

Lemma find_block_none_app:
  forall {t} l1 l2 bid,
    find_block t l1 bid = None ->
    find_block t (l1 ++ l2) bid = find_block t l2 bid.
Proof.
  intros t l1 l2 bid FIND.
  apply find_none_app; auto.
Qed.

Lemma find_block_some_app:
  forall {t} l1 l2 bid bk,
    find_block t l1 bid = Some bk ->
    find_block t (l1 ++ l2) bid = Some bk.
Proof.
  intros t l1 l2 bid bk FIND.
  apply find_some_app; auto.
Qed.

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

(** [denote_bks] *)
Lemma denote_bks_nil: forall s, denote_bks [] s ≈ ret (inl s).
Proof.
  intros []; unfold denote_bks.
  match goal with
  | |- CategoryOps.iter (C := ktree _) ?body ?s ≈ _ =>
    rewrite (unfold_iter body s)
  end.
  repeat (cbn; (rewrite bind_bind || rewrite bind_ret_l)).
  reflexivity.
Qed.

Lemma denote_bks_unfold_in: forall bks bid_from bid_src bk,
    find_block dtyp bks bid_src = Some bk ->
    denote_bks bks (bid_from, bid_src) ≈
    vob <- denote_block bk bid_from ;;
    match vob with
    | inr v => ret (inr v)
    | inl bid_target => denote_bks bks (bid_src, bid_target)
    end.
Proof.
  intros * GET_BK.
  cbn. unfold denote_bks at 1.
  rewrite KTreeFacts.unfold_iter_ktree. cbn.
  rewrite GET_BK.
  repeat setoid_rewrite bind_bind.
  repeat (apply eutt_eq_bind; intros ?).
  break_sum; rewrite bind_ret_l; [|reflexivity].
  rewrite tau_eutt; reflexivity.
Qed.

Lemma denote_bks_unfold_not_in: forall bks bid_from bid_src, 
    find_block dtyp bks bid_src = None ->
    denote_bks bks (bid_from, bid_src) ≈ Ret (inl (bid_from,bid_src)).
Proof.
  intros * GET_BK.
  unfold denote_bks.
  rewrite KTreeFacts.unfold_iter_ktree.
  rewrite GET_BK; cbn.
  rewrite bind_ret_l.
  reflexivity.
Qed.

Definition open_cfg {t} : Type := list (LLVMAst.block t).
Definition inputs {t} (ocfg : @open_cfg t) :=
  fmap blk_id ocfg.

Definition terminator_outputs {t} (term : LLVMAst.terminator t) : list block_id
  := match term with
     | TERM_Ret v => []
     | TERM_Ret_void => []
     | TERM_Br v br1 br2 => [br1; br2]
     | TERM_Br_1 br => [br]
     | TERM_Switch v default_dest brs => default_dest :: fmap snd brs
     | TERM_IndirectBr v brs => brs
     | TERM_Resume v => []
     | TERM_Invoke fnptrval args to_label unwind_label => [to_label; unwind_label]
     end.

Definition bk_outputs {t} (bk : block t) : list block_id :=
  terminator_outputs (snd (blk_term bk)).

Definition outputs {t} (bks : @open_cfg t) : List.list block_id
  := fold_left (fun acc bk => acc ++ bk_outputs bk) bks [].

Lemma outputs_acc: forall {t} (bks: list (block t)) acc,
    fold_left (fun acc bk => acc ++ bk_outputs bk) bks acc =
    acc ++ fold_left (fun acc bk => acc ++ bk_outputs bk) bks [].
Proof.
  induction bks using List.list_rev_ind; intros; cbn.
  - rewrite app_nil_r; reflexivity.
  - rewrite 2 fold_left_app, IHbks.
    cbn.
    rewrite app_assoc.
    reflexivity.
Qed.

Lemma outputs_app: forall {t} l l',
    @outputs t (l ++ l') = outputs l ++ outputs l'.
Proof.
  intros.
  unfold outputs at 1.
  rewrite fold_left_app, outputs_acc.
  reflexivity.
Qed.

Lemma outputs_cons: forall {t} b l,
    @outputs t (b :: l) = bk_outputs b ++ outputs l.
Proof.
  intros.
  rewrite list_cons_app, outputs_app; reflexivity.
Qed.

Lemma In_bk_outputs: forall {t} bid br (b: block t) l,
    In br (bk_outputs b) ->
    find_block t l bid = Some b ->
    In br (outputs l). 
Proof.
  induction l as [| ? l IH].
  - cbn; intros ? abs; inv abs.
  - intros IN FIND.
    cbn in FIND.
    flatten_hyp FIND; inv FIND.
    + flatten_hyp Heq; inv Heq.
      rewrite outputs_cons.
      apply in_or_app; left; auto.
    + flatten_hyp Heq; inv Heq. 
      rewrite outputs_cons.
      apply in_or_app; right.
      auto.
Qed.
 
Infix "⊍" := Coqlib.list_disjoint (at level 60).

Definition no_reentrance {t} (ocfg1 ocfg2 : @open_cfg t) : Prop :=
  outputs ocfg2 ⊍ inputs ocfg1.

Definition no_duplicate_bid {t} (ocfg1 ocfg2 : @open_cfg t) : Prop :=
  inputs ocfg1 ⊍ inputs ocfg2.

Lemma no_reentrance_not_in {t} (ocfg1 ocfg2 : @open_cfg t) :
  no_reentrance ocfg1 ocfg2 ->
  forall x, In x (outputs ocfg2) -> ~ In x (inputs ocfg1).
Proof.
  intros; eauto using Coqlib.list_disjoint_notin.
Qed.

Lemma no_duplicate_bid_not_in_l {t} (ocfg1 ocfg2 : @open_cfg t) :
  no_duplicate_bid ocfg1 ocfg2 ->
  forall x, In x (inputs ocfg2) -> ~ In x (inputs ocfg1).
Proof.
  intros; eauto using Coqlib.list_disjoint_notin, Coqlib.list_disjoint_sym.
Qed.

Lemma no_duplicate_bid_not_in_r {t} (ocfg1 ocfg2 : @open_cfg t) :
  no_duplicate_bid ocfg1 ocfg2 ->
  forall x, In x (inputs ocfg1) -> ~ In x (inputs ocfg2).
Proof.
  intros; eauto using Coqlib.list_disjoint_notin, Coqlib.list_disjoint_sym.
Qed.

Definition independent_flows {t} (ocfg1 ocfg2 : @open_cfg t) : Prop :=
  no_reentrance ocfg1 ocfg2 /\ 
  no_reentrance ocfg2 ocfg1 /\
  no_duplicate_bid ocfg1 ocfg2.

Lemma independent_flows_no_reentrance_l {t} (ocfg1 ocfg2 : @open_cfg t):
  independent_flows ocfg1 ocfg2 ->
  no_reentrance ocfg1 ocfg2.
Proof.
  intros INDEP; apply INDEP; auto.
Qed.

Lemma independent_flows_no_reentrance_r {t} (ocfg1 ocfg2 : @open_cfg t):
  independent_flows ocfg1 ocfg2 ->
  no_reentrance ocfg2 ocfg1.
Proof.
  intros INDEP; apply INDEP; auto.
Qed.

Lemma independent_flows_no_duplicate_bid {t} (ocfg1 ocfg2 : @open_cfg t):
  independent_flows ocfg1 ocfg2 ->
  no_duplicate_bid ocfg1 ocfg2.
Proof.
  intros INDEP; apply INDEP; auto.
Qed.

Lemma find_block_not_in_inputs: forall b l,
        ~ In b (inputs l) ->
        find_block dtyp l b = None.
Proof.
  induction l as [| bk l IH]; intros NIN; auto.
  cbn.
  flatten_goal.
  - exfalso.
    flatten_hyp Heq; [| inv Heq].
    apply NIN.
    left; rewrite e; reflexivity.
  - flatten_hyp Heq; [inv Heq |].
    apply IH.
    intros abs; apply NIN.
    right; auto.
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

Lemma find_block_in_inputs : forall {to ocfg},
    In to (inputs ocfg) ->
    exists bk, find_block dtyp ocfg to = Some bk.
Proof.
  induction ocfg as [| id ocfg IH]; cbn; intros IN; [inv IN |].
  flatten_goal; flatten_hyp Heq; intuition; eauto.
Qed.

(* Given a predicate [Qb] on pairs of block ids (the origin for phi-nodes and the input)
   and a predicate [Qv] on values, we establish that both hold after the denotation of an open_cfg if:
   - [Qb] holds at the initial entry point
   - [Qb] and [Qv] are preserved by the denotation of any blocks in the open cfg, assuming [Qb]
 *)
Lemma denote_bks_has_post_strong :
  forall ocfg fto (Qb : block_id * block_id -> Prop) (Qv : uvalue -> Prop)
    (INIT : Qb fto)
    (IND : forall fto (b : block dtyp),
        Qb fto ->
        find_block _ ocfg (snd fto) = Some b ->
        denote_block b (fst fto) ⤳ sum_pred (fun to => Qb (snd fto, to)) Qv), 
    denote_bks ocfg fto ⤳ sum_pred Qb Qv.
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
Lemma denote_bks_has_post :
  forall ocfg fto (Qb : block_id -> Prop) (Qv : uvalue -> Prop)
    (ENTER : In (snd fto) (inputs ocfg)) 
    (IND : forall fto (b : block dtyp),
        find_block _ ocfg (snd fto) = Some b ->
        denote_block b (fst fto) ⤳ sum_pred Qb Qv),
    denote_bks ocfg fto ⤳ sum_pred (prod_pred TT Qb) Qv.
Proof.
  intros * IN IND.
  apply has_post_iter_strong with (Inv := fun x => In (snd x) (inputs ocfg) \/ Qb (snd x))
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

Lemma denote_bks_exits_in_outputs :
  forall ocfg fto,
    In (snd fto) (inputs ocfg) ->
    denote_bks ocfg fto ⤳ exits_in_outputs ocfg.
Proof.
  intros * IN.
  apply has_post_weaken with (P := sum_pred (prod_pred TT (fun b => In b (outputs ocfg))) TT).
  2: intros [[]|] ?; cbn in *; intuition.
  apply denote_bks_has_post; eauto.
  intros.
  eapply has_post_weaken.
  eapply denote_bk_exits_in_outputs.
  intros []; cbn; intuition.
  eapply In_bk_outputs; eauto.
Qed.

(** * denote_bks  *)

Lemma denote_bks_app_no_edges :
  forall (l1 l2 : open_cfg) fto,
    find_block dtyp l1 (snd fto) = None ->
    no_reentrance l1 l2 ->
    denote_bks (l1 ++ l2) fto ≈ denote_bks l2 fto.
Proof.
  intros l1 l2 [f to] FIND NOBACK.
  apply (@KTreeFacts.eutt_iter_gen _ _ _ (fun fto fto' => fto' = fto /\ find_block dtyp l1 (snd fto) = None)); auto.
  clear f to FIND; intros fto fto' [-> FIND]; destruct fto as [f to] .
  cbn in *.
  epose proof (find_block_none_app _ l2 _ FIND) as FIND_L1L2.
  rewrite FIND_L1L2.
  destruct (find_block dtyp l2 to) eqn:FIND_L2.
  - eapply eutt_post_bind.
    apply denote_bk_exits_in_outputs.
    intros [id | v] ?; cbn; apply eutt_Ret; eauto.
    eapply inl_morphism; split; auto.
    eapply find_block_not_in_inputs,no_reentrance_not_in; eauto.
    eapply In_bk_outputs; eauto.

  - apply eutt_Ret; right; auto.
Qed.

Import ITreeNotations.
Lemma denote_bks_app :
  forall ocfg1 ocfg2 fto,
    no_reentrance ocfg1 ocfg2 ->
    denote_bks (ocfg1 ++ ocfg2) fto ≈ ITree.bind (denote_bks ocfg1 fto)
               (fun x =>
                  match x with
                  | inl fto2 => denote_bks ocfg2 fto2
                  | inr v => ret (inr v)
                  end).
Proof.
  intros * NOBACK.
  revert fto.
  einit.
  ecofix CIH.
  intros [f to].
  destruct (find_block dtyp ocfg1 to) eqn:FIND.
  - unfold denote_bks.
    unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree.
    match goal with
      |- euttG _ _ _ _ _ ?t _ => remember t; rewrite unfold_iter; subst
    end.
    rewrite unfold_iter; cbn.
    rewrite FIND.
    rewrite !bind_bind.
    pose proof find_block_some_app ocfg1 ocfg2 to FIND as FIND_APP.
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
    rewrite denote_bks_app_no_edges; auto.
    rewrite denote_bks_unfold_not_in with (bks := ocfg1); auto.
    rewrite bind_ret_l; reflexivity.
Qed.

Lemma denote_bks_flow_left :
  forall ocfg1 ocfg2 fto,
    independent_flows ocfg1 ocfg2 ->
    In (snd fto) (inputs ocfg1) ->
    denote_bks (ocfg1 ++ ocfg2) fto ≈
    denote_bks ocfg1 fto.
Proof.
  intros * INDEP IN.
  rewrite denote_bks_app; [| auto using independent_flows_no_reentrance_l].
  bind_ret_r2.

  eapply eutt_post_bind; [apply denote_bks_exits_in_outputs; eauto |].
  intros [[f to] | ?] EXIT; [| reflexivity].
  rewrite denote_bks_unfold_not_in; [reflexivity |].
  cbn in *.
  apply find_block_not_in_inputs.
  eapply no_reentrance_not_in; eauto.
  apply INDEP.
Qed.

Lemma denote_bks_flow_right :
  forall ocfg1 ocfg2 fto,
    independent_flows ocfg1 ocfg2 ->
    In (snd fto) (inputs ocfg2) ->
    denote_bks (ocfg1 ++ ocfg2) fto ≈
    denote_bks ocfg2 fto.
Proof.
  intros * INDEP IN.
  rewrite denote_bks_app; [| auto using independent_flows_no_reentrance_l].
  destruct fto as [f to]; cbn in *.
  rewrite denote_bks_unfold_not_in.
  rewrite bind_ret_l; reflexivity.
  eapply find_block_not_in_inputs, no_duplicate_bid_not_in_l; eauto using independent_flows_no_duplicate_bid.
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

