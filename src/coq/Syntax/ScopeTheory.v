(* begin hide *)
From Coq Require Import
     List.
Import ListNotations.

From Vellvm Require Import
     Numeric.Coqlib
     Utilities
     Syntax.

From ExtLib Require Import List.

Set Implicit Arguments.
Set Strict Implicit.
(* end hide *)

Lemma app_snoc_app : forall {A} (l l' : list A) x,
    (l ++ [x]) ++ l' = l ++ (x :: l').
Proof using.
  intros.
  rewrite <- app_assoc; reflexivity.
Qed.

Section LABELS_THEORY.

  Context {T : Set}.

  Lemma inputs_app: forall (l l' : ocfg T),
      @inputs T (l ++ l') = inputs l ++ inputs l'.
  Proof using.
    intros.
    unfold inputs at 1.
    rewrite map_app; auto.
  Qed.

  Lemma inputs_cons: forall b (l : ocfg T),
      @inputs T (b :: l) = blk_id b :: inputs l.
  Proof using.
    intros.
    rewrite list_cons_app, inputs_app; reflexivity.
  Qed.

  Lemma outputs_acc: forall (bks: ocfg T) acc,
      fold_left (fun acc bk => acc ++ successors bk) bks acc =
      acc ++ fold_left (fun acc bk => acc ++ successors bk) bks [].
  Proof using.
    induction bks using list_rev_ind; intros; cbn.
    - rewrite app_nil_r; reflexivity.
    - rewrite 2 fold_left_app, IHbks.
      cbn.
      rewrite app_assoc.
      reflexivity.
  Qed.

  Lemma outputs_app: forall (l l' : ocfg T),
      @outputs T (l ++ l') = outputs l ++ outputs l'.
  Proof using.
    intros.
    unfold outputs at 1.
    rewrite fold_left_app, outputs_acc.
    reflexivity.
  Qed.

  Lemma outputs_cons: forall b (l : ocfg T),
      @outputs T (b :: l) = successors b ++ outputs l.
  Proof using.
    intros.
    rewrite list_cons_app, outputs_app; reflexivity.
  Qed.

  Lemma wf_ocfg_bid_nil:
    wf_ocfg_bid (T := T) [].
  Proof using.
    intros; apply list_norepet_nil.
  Qed.

  Lemma wf_ocfg_bid_cons :
    forall (b : block T) (bs : ocfg T),
      wf_ocfg_bid (b :: bs) ->
      wf_ocfg_bid bs.
  Proof using.
    intros * NOREP; inv NOREP; eauto.
  Qed.

  Lemma wf_ocfg_bid_cons_not_in :
    forall (b : block T) (bs : ocfg T),
      wf_ocfg_bid (b :: bs) ->
      not (In (blk_id b) (inputs bs)).
  Proof using.
    intros * NOREP; inv NOREP; eauto.
  Qed.

  Lemma wf_ocfg_bid_app_r :
    forall (bs1 bs2 : ocfg T),
      wf_ocfg_bid (bs1 ++ bs2) ->
      wf_ocfg_bid bs2.
  Proof using.
    intros * NR.
    eapply list_norepet_append_right.
    unfold wf_ocfg_bid in NR.
    rewrite inputs_app in NR.
    eauto.
  Qed.

  Lemma wf_ocfg_bid_app_l :
    forall (bs1 bs2 : ocfg T),
      wf_ocfg_bid (bs1 ++ bs2) ->
      wf_ocfg_bid bs1.
  Proof using.
    intros * NR.
    eapply list_norepet_append_left.
    unfold wf_ocfg_bid in NR.
    rewrite inputs_app in NR.
    eauto.
  Qed.

  Lemma wf_ocfg_commut :
    forall (G G' : ocfg T),
      wf_ocfg_bid (G ++ G') ->
      wf_ocfg_bid (G' ++ G).
  Proof using.
    intros.
    red; rewrite inputs_app; apply Coqlib.list_norepet_append_commut; rewrite <- inputs_app; apply H.
  Qed.

  Lemma wf_ocfg_commut_hd :
    forall (bk bk' : block T) G,
      wf_ocfg_bid (bk::bk'::G) ->
      wf_ocfg_bid (bk'::bk::G).
  Proof using.
    intros * WF.
    inv WF.
    inv H2.
    constructor.
    2: constructor; auto.
    - intros [EQ | IN]; auto.
      apply H1; left; auto.
    - intros IN; auto.
      eapply H1; right; auto.
  Qed.

  Lemma wf_ocfg_map : forall (f : block T -> block T) (G : ocfg T),
      (forall bk, blk_id (f bk) = blk_id bk) ->
      wf_ocfg_bid G <-> wf_ocfg_bid (map f G).
  Proof using.
    intros.
    unfold wf_ocfg_bid, inputs.
    rewrite List.map_map.
    replace (map (fun x : block T => blk_id (f x)) G) with (map blk_id G); [reflexivity |].
    apply map_ext.
    intros; rewrite H; auto.
  Qed.

  Lemma blk_id_convert_typ :
    forall env b,
      blk_id (convert_typ env b) = blk_id b.
  Proof using.
    intros ? []; reflexivity.
  Qed.

  (* TODO: Show symmetric case *)
  Lemma wf_ocfg_bid_app_not_in_l :
    forall id (bs bs' : ocfg T),
      In id (inputs bs) ->
      wf_ocfg_bid (bs' ++ bs) ->
      not (In id (inputs bs')).
  Proof using.
    intros. destruct bs.
    inversion H.
    inv H.
    apply wf_ocfg_bid_cons_not_in.
    unfold wf_ocfg_bid in *.
    rewrite inputs_app in H0.
    rewrite inputs_cons. rewrite inputs_cons in H0.
    rewrite list_cons_app in H0.
    rewrite app_assoc in H0.
    apply list_norepet_append_left in H0.
    rewrite list_cons_app.
    rewrite list_norepet_app in *.
    intuition auto with *. apply list_disjoint_sym. auto.
    unfold wf_ocfg_bid in H0.
    rewrite inputs_app in H0. rewrite inputs_cons in H0. rewrite list_cons_app in H0.
    apply list_norepet_append_commut in H0. rewrite <- app_assoc in H0.
    apply list_norepet_append_right in H0.
    rewrite list_norepet_app in H0.
    destruct H0 as (? & ? & ?).
    red in H2. intro. eapply H2; eauto.
  Qed.

  (* TODO: Show symmetric case *)
  Lemma wf_ocfg_app_not_in_r :
    forall id (bs bs' : ocfg T),
      In id (inputs bs) ->
      wf_ocfg_bid (bs' ++ bs) ->
      not (In id (inputs bs')).
  Proof using.
    intros. destruct bs.
    inversion H.
    inv H.
    apply wf_ocfg_bid_cons_not_in.
    unfold wf_ocfg_bid in *.
    rewrite inputs_app in H0.
    rewrite inputs_cons. rewrite inputs_cons in H0.
    rewrite list_cons_app in H0.
    rewrite app_assoc in H0.
    apply list_norepet_append_left in H0.
    rewrite list_cons_app.
    rewrite list_norepet_app in *.
    intuition auto with *. apply list_disjoint_sym. auto.
    unfold wf_ocfg_bid in H0.
    rewrite inputs_app in H0. rewrite inputs_cons in H0. rewrite list_cons_app in H0.
    apply list_norepet_append_commut in H0. rewrite <- app_assoc in H0.
    apply list_norepet_append_right in H0.
    rewrite list_norepet_app in H0.
    destruct H0 as (? & ? & ?).
    red in H2. intro. eapply H2; eauto.
  Qed.

  Lemma In_bk_outputs: forall bid br (b: block T) (l : ocfg T),
      In br (successors b) ->
      find_block l bid = Some b ->
      In br (outputs l).
  Proof using.
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

  Lemma find_block_in_inputs :
    forall to (bks : ocfg T),
      In to (inputs bks) ->
      exists bk, find_block bks to = Some bk.
  Proof using.
    induction bks as [| id ocfg IH]; cbn; intros IN; [inv IN |].
    flatten_goal; flatten_hyp Heq; intuition auto with *; eauto.
  Qed.

  Lemma no_reentrance_not_in (bks1 bks2 : ocfg T) :
    no_reentrance bks1 bks2 ->
    forall x, In x (outputs bks2) -> ~ In x (inputs bks1).
  Proof using.
    intros; eauto using Coqlib.list_disjoint_notin.
  Qed.

  Lemma no_reentrance_app_l :
    forall (bks1 bks1' bks2 : ocfg T),
      no_reentrance (bks1 ++ bks1') bks2 <->
      no_reentrance bks1 bks2 /\ no_reentrance bks1' bks2.
  Proof using.
    intros; unfold no_reentrance; split; [intros H | intros [H1 H2]].
    - rewrite inputs_app, list_disjoint_app_r in H; auto.
    - rewrite inputs_app, list_disjoint_app_r; auto.
  Qed.

  Lemma no_reentrance_app_r :
    forall (bks1 bks2 bks2' : ocfg T),
      no_reentrance bks1 (bks2 ++ bks2')%list <->
      no_reentrance bks1 bks2 /\ no_reentrance bks1 bks2'.
  Proof using.
    intros; unfold no_reentrance; split; [intros H | intros [H1 H2]].
    - rewrite outputs_app,list_disjoint_app_l in H; auto.
    - rewrite outputs_app, list_disjoint_app_l; auto.
  Qed.

  Lemma no_duplicate_bid_not_in_l (bks1 bks2 : ocfg T) :
    no_duplicate_bid bks1 bks2 ->
    forall x, In x (inputs bks2) -> ~ In x (inputs bks1).
  Proof using.
    intros; eauto using Coqlib.list_disjoint_notin, Coqlib.list_disjoint_sym.
  Qed.

  Lemma no_duplicate_bid_not_in_r (bks1 bks2 : ocfg T) :
    no_duplicate_bid bks1 bks2 ->
    forall x, In x (inputs bks1) -> ~ In x (inputs bks2).
  Proof using.
    intros; eauto using Coqlib.list_disjoint_notin, Coqlib.list_disjoint_sym.
  Qed.

  Lemma independent_flows_no_reentrance_l (bks1 bks2 : ocfg T):
    independent_flows bks1 bks2 ->
    no_reentrance bks1 bks2.
  Proof using.
    intros INDEP; apply INDEP; auto.
  Qed.

  Lemma independent_flows_no_reentrance_r (bks1 bks2 : ocfg T):
    independent_flows bks1 bks2 ->
    no_reentrance bks2 bks1.
  Proof using.
    intros INDEP; apply INDEP; auto.
  Qed.

  Lemma independent_flows_no_duplicate_bid (bks1 bks2 : ocfg T):
    independent_flows bks1 bks2 ->
    no_duplicate_bid bks1 bks2.
  Proof using.
    intros INDEP; apply INDEP; auto.
  Qed.

  Lemma find_block_not_in_inputs:
    forall bid (l : ocfg T),
      ~ In bid (inputs l) ->
      find_block l bid = None.
  Proof using.
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

  Lemma wf_ocfg_bid_singleton : forall (b : _ T), wf_ocfg_bid [b].
  Proof using.
    intros.
    red.
    eapply list_norepet_cons; eauto.
    eapply list_norepet_nil.
  Qed.

  Lemma wf_ocfg_bid_cons' : forall (b : _ T) (bks : ocfg T),
      not (In (blk_id b) (inputs bks)) ->
      wf_ocfg_bid bks ->
      wf_ocfg_bid (b :: bks).
  Proof using.
    intros.
    eapply list_norepet_cons; eauto.
  Qed.

  Lemma free_in_cfg_cons:
    forall b (bs : ocfg T) id,
      free_in_cfg (b::bs) id ->
      free_in_cfg bs id .
  Proof using.
    intros * FR abs; apply FR; cbn.
    destruct (Eqv.eqv_dec_p (blk_id b) id); [rewrite e; auto | right; auto].
  Qed.

  Lemma free_in_cfg_app : forall (bks1 bks2 : ocfg T) b,
      free_in_cfg (bks1 ++ bks2) b <->
      (free_in_cfg bks1 b /\ free_in_cfg bks2 b).
  Proof using.
    intros; split; unfold free_in_cfg; intro FREE.
    - split; intros abs; eapply FREE; rewrite inputs_app; eauto using in_or_app.
    - rewrite inputs_app; intros abs; apply in_app_or in abs; destruct FREE as [FREEL FREER]; destruct abs; [eapply FREEL | eapply FREER]; eauto.
  Qed.

  Lemma wf_ocfg_bid_distinct_labels :
    forall (bks1 bks2 : ocfg T) b1 b2,
      wf_ocfg_bid (bks1 ++ bks2) ->
      In b1 (inputs bks1) ->
      In b2 (inputs bks2) ->
      b1 <> b2.
  Proof using.
    intros * WF IN1 IN2.
    eapply wf_ocfg_bid_app_not_in_l in IN2; eauto.
    destruct (Eqv.eqv_dec_p b1 b2).
    rewrite e in IN1; contradiction IN2; auto.
    auto.
  Qed.

  Lemma predecessors_app :
    forall (bks bks' : ocfg T) f,
      predecessors f (bks ++ bks') = predecessors f bks' ++ predecessors f bks.
  Proof using.
    induction bks' as [| bk bks' IH] using rev_ind.
    - intros; cbn; rewrite !app_nil_r; reflexivity.
    - intros.
      unfold predecessors.
      rewrite app_assoc.
      rewrite 2 (fold_left_app _ _ [bk]).
      simpl.
      break_match_goal.
      + cbn; f_equal.
        apply IH.
      + apply IH.
  Qed.

  Lemma predecessors_cons :
    forall (bks : ocfg T) bk f,
      predecessors f (bk :: bks) = predecessors f bks ++ predecessors f [bk].
  Proof using.
    intros.
    rewrite list_cons_app, predecessors_app.
    reflexivity.
  Qed.

  Lemma find_block_In : forall G (bk : block T),
      find_block G bk.(blk_id) = Some bk ->
      In bk G.
  Proof using.
    induction G as [| x G IH]; intros * FIND; [inv FIND |].
    cbn in FIND; break_match_hyp; auto.
    inv FIND; left; reflexivity.
    right; apply IH; auto.
  Qed.

  Lemma successor_predecessor :
    forall (G : ocfg T) (source : block T) target,
      In target (successors source) ->
      find_block G source.(blk_id) = Some source ->
      In source.(blk_id) (predecessors target G).
  Proof using.
    intros * IN FIND.
    apply find_block_In in FIND; revert FIND.
    induction G as [| bki G IH]; intros * FIND.
    - inv FIND.
    - destruct FIND as [EQ | FIND].
      + subst.
        clear IH.
        rewrite predecessors_cons.
        apply in_or_app; right.
        cbn.
        unfold successors in IN.
        unfold is_predecessor.
        break_match_goal.
        left; auto.
        break_match_hyp; intuition auto with *.
      + rewrite predecessors_cons.
        apply in_or_app; left.
        apply IH; auto.
  Qed.

  Definition predecessors_aux (b : block_id) (G : ocfg T) acc :=
    fold_left (fun acc bk => if is_predecessor b bk then bk.(blk_id) :: acc else acc) G acc.

  Lemma In_predecessors_is_predecessor_aux :
    forall (G : ocfg T) acc (src tgt : block_id),
      In src (predecessors_aux tgt G acc) ->
      (In src acc \/ exists bk, In bk G /\ src = bk.(blk_id) /\ is_predecessor tgt bk = true).
  Proof using.
    intros *; revert acc; induction G as [| bk G IH]; intros acc IN; [left; auto |].
    cbn in IN.
    break_match_hyp.
    - edestruct IH as [INACC | (bk' & INbk & -> & PRED)]; eauto.
      + destruct INACC as [<- | ?]; [| left; auto].
        right; exists bk; intuition auto with *.
      + right.
        exists bk'; intuition auto with *.
    - edestruct IH as [INACC | (bk' & INbk & -> & PRED)]; eauto.
      right; exists bk'; intuition auto with *.
  Qed.

  Lemma In_predecessors_is_predecessor :
    forall (G : ocfg T) (src tgt : block_id),
      In src (predecessors tgt G) ->
      exists bk, In bk G /\ src = bk.(blk_id) /\ is_predecessor tgt bk = true.
  Proof using.
    intros * IN.
    edestruct In_predecessors_is_predecessor_aux as [INACC | (bk' & INbk & -> & PRED)]; eauto.
    inv INACC.
  Qed.

  Lemma find_block_nil:
    forall b,
      @find_block T [] b = None.
  Proof using.
    reflexivity.
  Qed.

  Lemma find_block_eq:
    forall x (b : block T) (bs : ocfg T),
      blk_id b = x ->
      find_block (b:: bs) x = Some b.
  Proof using.
    intros; cbn.
    rewrite H.
    destruct (Eqv.eqv_dec_p x x).
    reflexivity.
    contradiction n; reflexivity.
  Qed.

  Lemma find_block_ineq:
    forall x (b : block T) (bs : ocfg T),
      blk_id b <> x ->
      find_block (b::bs) x = find_block bs x.
  Proof using.
    intros; cbn.
    destruct (Eqv.eqv_dec_p (blk_id b)) as [EQ | INEQ].
    unfold Eqv.eqv, AstLib.eqv_raw_id in *; intuition auto with *.
    reflexivity.
  Qed.

  Lemma wf_ocfg_bid_In_is_found :
    forall (bks : ocfg T) bk,
      wf_ocfg_bid bks ->
      In bk bks ->
      find_block bks bk.(blk_id) = Some bk.
  Proof using.
    induction bks as [| x bks IH]; intros * WF IN; [inv IN |].
    destruct (Eqv.eqv_dec_p x.(blk_id) bk.(blk_id)).
    - rewrite find_block_eq; auto.
      destruct IN as [-> | IN]; auto.
      apply wf_ocfg_bid_cons_not_in in WF.
      exfalso; apply WF.
      do 2 red in e; rewrite e.
      eapply in_map; auto.
    - rewrite find_block_ineq; [| auto].
      apply IH.
      eapply wf_ocfg_bid_cons; eauto.
      destruct IN; auto.
      exfalso; subst; eapply n; reflexivity.
  Qed.

  Lemma predecessor_successor :
    forall (G : ocfg T) (source target : block_id) (bk : block T),
      wf_ocfg_bid G ->
      In source (predecessors target G) ->
      find_block G source = Some bk ->
      In target (successors bk).
  Proof using.
    intros * WF IN FIND.
    pose proof In_predecessors_is_predecessor _ _ _ IN as (bk' & IN' & -> & ISPRED).
    apply wf_ocfg_bid_In_is_found in IN'; auto.
    rewrite FIND in IN'; inv IN'.
    unfold is_predecessor in ISPRED.
    break_match_hyp; intuition auto with *.
  Qed.

  Lemma find_block_app_r_wf :
    forall (x : block_id) (b : block T) (bs1 bs2 : ocfg T),
      wf_ocfg_bid (bs1 ++ bs2)  ->
      find_block bs2 x = Some b ->
      find_block (bs1 ++ bs2) x = Some b.
  Proof using.
    intros x b; induction bs1 as [| hd bs1 IH]; intros * NOREP FIND.
    - rewrite app_nil_l; auto.
    - cbn; break_inner_match_goal.
      + cbn in NOREP; apply wf_ocfg_bid_cons_not_in in NOREP.
        exfalso; apply NOREP.
        rewrite e.
        apply find_some in FIND as [FIND EQ].
        clear - FIND EQ.
        rewrite inputs_app; eapply in_or_app; right.
        break_match; [| intuition auto with *].
        rewrite <- e.
        eapply in_map; auto.
      + cbn in NOREP; apply wf_ocfg_bid_cons in NOREP.
        apply IH; eauto.
  Qed.

  Lemma find_block_app_l_wf :
    forall (x : block_id) (b : block T) (bs1 bs2 : ocfg T),
      wf_ocfg_bid (bs1 ++ bs2)  ->
      find_block bs1 x = Some b ->
      find_block (bs1 ++ bs2) x = Some b.
  Proof using.
    intros x b; induction bs1 as [| hd bs1 IH]; intros * NOREP FIND.
    - inv FIND.
    - cbn in FIND |- *.
      break_inner_match; auto.
      apply IH; eauto.
      eapply wf_ocfg_bid_cons, NOREP.
  Qed.

  Lemma find_block_tail_wf :
    forall (x : block_id) (b b' : block T) (bs : ocfg T),
      wf_ocfg_bid (b :: bs)  ->
      find_block bs x = Some b' ->
      find_block (b :: bs) x = Some b'.
  Proof using.
    intros.
    rewrite list_cons_app.
    apply find_block_app_r_wf; auto.
  Qed.

  Lemma find_block_free_id :
    forall (cfg : ocfg T) id,
      free_in_cfg cfg id ->
      find_block cfg id = None.
  Proof using.
    induction cfg as [| b bs IH]; cbn; intros * FREE; auto.
    break_inner_match_goal.
    + exfalso; eapply FREE.
      cbn; rewrite e; auto.
    + apply IH.
      apply free_in_cfg_cons in FREE; auto.
  Qed.

  Lemma find_block_none_app:
    forall (bks1 bks2 : ocfg T) bid,
      find_block bks1 bid = None ->
      find_block (bks1 ++ bks2) bid = find_block bks2 bid.
  Proof using.
    intros; apply find_none_app; auto.
  Qed.

  Lemma find_block_some_app:
    forall (bks1 bks2 : ocfg T) (bk : block T) bid,
      find_block bks1 bid = Some bk ->
      find_block (bks1 ++ bks2) bid = Some bk.
  Proof using.
    intros; apply find_some_app; auto.
  Qed.

  Lemma find_block_Some_In_inputs : forall (bks : ocfg T) b bk,
      find_block bks b = Some bk ->
      In b (inputs bks).
  Proof using.
    induction bks as [| hd bks IH].
    - intros * H; inv H.
    - intros * FIND.
      destruct (Eqv.eqv_dec_p (blk_id hd) b).
      cbn; rewrite e; auto.
      right; eapply IH.
      erewrite <- find_block_ineq; eauto.
  Qed.

  Lemma wf_ocfg_bid_find_None_app_l :
    forall (bks1 bks2 : ocfg T) b bk,
      wf_ocfg_bid (bks1 ++ bks2)%list ->
      find_block bks2 b = Some bk ->
      find_block bks1 b = None.
  Proof using.
    induction bks1 as [| b bks1 IH]; intros * WF FIND.
    reflexivity.
    destruct (Eqv.eqv_dec_p (blk_id b) b0).
    - exfalso.
      cbn in WF; eapply wf_ocfg_bid_cons_not_in in WF.
      apply WF.
      rewrite inputs_app.
      apply in_or_app; right.
      rewrite e.
      apply find_block_Some_In_inputs in FIND; auto.
    - rewrite find_block_ineq; auto.
      eapply IH; eauto using wf_ocfg_bid_cons.
  Qed.

  Lemma find_block_has_id : forall (G : ocfg T) b bk,
      find_block G b = Some bk ->
      b = bk.(blk_id).
  Proof using.
    induction G as [| bkh G IH].
    - intros * LU; inv LU.
    - intros * LU.
      cbn in LU.
      break_match_hyp.
      + inv LU; break_match_hyp; intuition auto with *.
      + apply IH.
        apply LU.
  Qed.

  Lemma find_block_map_some :
    forall (f : block T -> block T) G b bk,
      (forall bk, blk_id (f bk) = blk_id bk) ->
      find_block G b = Some bk ->
      find_block (map f G) b = Some (f bk).
  Proof using.
    intros * ID; induction G as [| hd G IH]; intros FIND ; [inv FIND |].
    cbn in *.
    rewrite ID.
    break_match_goal; break_match_hyp; intuition auto with *.
    inv FIND; auto.
  Qed.

  Lemma find_block_map_none :
    forall (f : block T -> block T) G b,
      (forall bk, blk_id (f bk) = blk_id bk) ->
      find_block G b = None ->
      find_block (map f G) b = None.
  Proof using.
    intros * ID; induction G as [| hd G IH]; intros FIND; [reflexivity |].
    cbn in *.
    rewrite ID.
    break_match_goal; break_match_hyp; intuition auto with *.
    inv FIND; auto.
  Qed.

  Lemma wf_ocfg_bid_find_block_unique :
    forall (bks : ocfg T) bk1 b1 bk2,
      wf_ocfg_bid bks ->
      find_block bks b1 = Some bk1 ->
      find_block bks b1 = Some bk2 ->
      bk1 = bk2.
  Proof using.
    induction bks as [| bk bks IH]; intros * WF FIND1 FIND2; [inv FIND1 |].
    cbn in *.
    break_match_hyp.
    inv FIND1; inv FIND2; auto.
    break_match_hyp; intuition auto with *.
    eapply IH; eauto.
    eapply wf_ocfg_bid_cons; eauto.
  Qed.

  Lemma find_block_In' : forall G b (bk : block T),
      find_block G b = Some bk ->
      In bk G.
  Proof using.
    intros * LU; pose proof find_block_has_id _ _ LU; subst; apply find_block_In; auto.
  Qed.

  Lemma wf_ocfg_cons_not_in_tail :
    forall (bk : block T) G,
      wf_ocfg_bid (bk :: G) ->
      find_block G bk.(blk_id) = None.
  Proof using.
    induction G as [| x G IH]; intros; [reflexivity |].
    cbn; break_match_goal.
    - break_match_hyp; intuition auto with *.
      do 2 red in e.
      exfalso; clear Heqb.
      red in H.
      cbn in H.
      rewrite e in H.
      inv H.
      eapply H2; left; reflexivity.
    - break_match_hyp; intuition auto with *.
      apply IH.
      apply wf_ocfg_commut_hd in H.
      eapply wf_ocfg_bid_cons; eauto.
  Qed.

  Lemma In_find_block :
    forall (bks : ocfg T) bk,
      In bk bks ->
      exists bk', find_block bks bk.(blk_id) = Some bk'.
  Proof using.
    induction bks as [| x bks IH]; intros * IN; [inv IN | ].
    destruct (Eqv.eqv_dec_p x.(blk_id) bk.(blk_id)).
    - do 2 red in e; exists x; rewrite find_block_eq; auto.
    - rewrite find_block_ineq; [| auto].
      apply IH.
      destruct IN; auto.
      exfalso; subst; eapply n; reflexivity.
  Qed.

  Lemma find_block_map :
    forall (f : block T -> block T) G b,
      (forall bk, blk_id (f bk) = blk_id bk) ->
      find_block (map f G) b = option_map f (find_block G b).
  Proof using.
    intros.
    destruct (find_block G b) eqn:EQ.
    eapply find_block_map_some in EQ; eauto.
    eapply find_block_map_none in EQ; eauto.
  Qed.

End LABELS_THEORY.

Lemma free_in_convert_typ :
  forall env (bs : list (LLVMAst.block typ)) id,
    free_in_cfg bs id ->
    free_in_cfg (convert_typ env bs) id.
Proof using.
  induction bs as [| b bs IH]; intros * FR.
  - red; cbn; auto.
  - cbn.
    intros abs.
    eapply FR.
    destruct (Eqv.eqv_dec_p (blk_id b) id).
    left; rewrite e; auto.
    destruct abs.
    + cbn in H; unfold Traversal.endo, Traversal.Endo_id in H; cbn in H.
      exfalso; apply n; rewrite H; reflexivity.
    + apply IH in H; intuition auto with *.
      eapply free_in_cfg_cons; eauto.
Qed.



Section DTyp.

  Lemma convert_typ_terminator_outputs : forall t,
    terminator_outputs (convert_typ [] t) = terminator_outputs t.
  Proof using.
    intros []; cbn; try reflexivity.
    - induction brs as [| [τ i] brs IH]; cbn; auto.
      do 2 f_equal.
      inv IH; auto.
    - induction brs; cbn; auto; f_equal; auto.
  Qed.

  Lemma convert_typ_outputs : forall (bks : ocfg typ),
      outputs (convert_typ [] bks) = outputs bks.
  Proof using.
    induction bks as [| bk bks IH]; [reflexivity |].
    unfold convert_typ.
    simpl ConvertTyp_list.
    rewrite !outputs_cons, <- IH.
    f_equal.
    destruct bk; cbn.
    unfold successors.
    rewrite <- convert_typ_terminator_outputs.
    reflexivity.
  Qed.

  Lemma inputs_convert_typ : forall env bs,
      inputs (convert_typ env bs) = inputs bs.
  Proof using.
    induction bs as [| b bs IH]; cbn; auto.
    f_equal; auto.
  Qed.

  Lemma wf_ocfg_bid_convert_typ :
    forall env (bs : ocfg typ),
      wf_ocfg_bid bs ->
      wf_ocfg_bid (convert_typ env bs).
  Proof using.
    induction bs as [| b bs IH].
    - cbn; auto.
    - intros NOREP.
      change (wf_ocfg_bid (convert_typ env b :: convert_typ env bs)).
      apply list_norepet_cons.
      + apply wf_ocfg_bid_cons_not_in in NOREP.
        cbn.
        rewrite inputs_convert_typ; auto.
      + eapply IH, wf_ocfg_bid_cons; eauto.
  Qed.

End DTyp.
