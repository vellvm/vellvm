(* begin hide *)
From Coq Require Import
     List.
Import ListNotations.

From stdpp Require Import base gmap fin_maps fin_map_dom.
From Vellvm Require Import
     Numeric.Coqlib
     Utilities
     Syntax.

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
      @inputs T (l ∪ l') = inputs l ∪ inputs l'.
  Proof using.
    intros.
    unfold inputs.
    (* Is this good style? *)
    unfold_leibniz.
    apply dom_union.
  Qed.

  Lemma outputs_acc_comm:
    ∀ (i : block_id) (bk : block T) (g : gmap block_id (block T)) (j1 j2 : block_id)
      (z1 z2 : block T) (y : gset block_id),
      j1 ≠ j2 →
      <[i:=bk]> g !! j1 = Some z1 →
      <[i:=bk]> g !! j2 = Some z2 →
      outputs_acc j1 z1 (outputs_acc j2 z2 y) = outputs_acc j2 z2 (outputs_acc j1 z1 y).
  Proof.
    set_solver.
  Qed.

  (* TODO: the lib lemma is weirdly specialized, todo ask/PR stdpp *)
Lemma map_fold_comm_acc
  {K : Type} {M : Type → Type} `{FMap M, ∀ A : Type, Lookup K A (M A), ∀ A : Type, Empty (M A), ∀ A : Type, PartialAlter K A (M A),  OMap M, Merge M, ∀ A : Type, MapFold K A (M A), EqDecision K,
  FinMap K M}
  {A B} (f : K → A → B → B) (g : B → B) (x : B) (m : M A) :
  (∀ j1 j2 z1 z2 y, f j1 z1 (f j2 z2 y) = f j2 z2 (f j1 z1 y)) →
  (∀ j z y, f j z (g y) = g (f j z y)) →
  map_fold f (g x) m = g (map_fold f x m).
Proof.
  intros. apply (map_fold_comm_acc_strong _); [solve_proper|solve_proper|done..].
Qed.

  Lemma outputs_acc_union_acc : forall (g g' : ocfg T),
      g ##ₘ g' ->
      map_fold outputs_acc ∅ (g ∪ g') =
      map_fold outputs_acc (map_fold outputs_acc ∅ g) g'.
  Proof.
    induction g as [|i bk g ? IH] using (map_ind (M := gmap block_id)).
    - intros * _.
      now rewrite map_empty_union.
      Undo.
      now rewrite (left_id ∅ _).
    - intros ? DISJ.
      rewrite <- insert_union_l.

      do 2 (rewrite map_fold_insert_L;
        [| apply outputs_acc_comm |
           (auto || apply lookup_union_None; now simplify_map_eq)]).
      rewrite IH.
      2: eapply map_disjoint_insert_l; eauto.
      symmetry; apply map_fold_comm_acc.
      intros; set_solver.
      intros; set_solver.
  Qed.

  Lemma outputs_acc_union : forall i (b : block T) g g',
    outputs_acc i b (g ∪ g') = outputs_acc i b g ∪ g'.
  Proof.
    set_solver.
  Qed.

  Lemma outputs_empty : outputs (T := T) ∅ = ∅.
  Proof.
    set_solver.
  Qed.

  Lemma outputs_union: forall (g g' : ocfg T),
      g ##ₘ g' ->
      outputs (g ∪ g') = outputs g ∪ outputs g'.
  Proof.
    induction g as [|i bk g ? IH] using (map_ind (M := gmap block_id)).
    - intros * _.
      rewrite outputs_empty, map_empty_union.
      set_solver.
    - intros ? DISJ.
      rewrite <- insert_union_l.
      unfold outputs.
      do 2 (rewrite map_fold_insert_L;
        [| apply outputs_acc_comm |
           (auto || apply lookup_union_None; now simplify_map_eq)]).
      unfold outputs at 1 in IH.
      rewrite IH.
      2: solve_map_disjoint.
      apply outputs_acc_union.
  Qed.

  Lemma outputs_singleton: forall i (bk : block T),
      outputs {[ i := bk]} = successors bk.
  Proof.
    intros.
    unfold outputs.
    rewrite map_fold_singleton.
    set_solver.
  Qed.

  Lemma outputs_insert: forall i bk (g : ocfg T),
      g !! i = None ->
      outputs (<[ i := bk]> g) = successors bk ∪ outputs g.
  Proof using.
    intros.
    rewrite insert_union_singleton_l.
    rewrite outputs_union.
    now rewrite outputs_singleton.
    solve_map_disjoint.
  Qed.

  (* (* TODO: Show symmetric case *) *)
  (* Lemma wf_ocfg_bid_app_not_in_l : *)
  (*   forall id (bs bs' : ocfg T), *)
  (*     In id (inputs bs) -> *)
  (*     wf_ocfg_bid (bs' ++ bs) -> *)
  (*     not (In id (inputs bs')). *)
  (* Proof using. *)
  (*   intros. destruct bs. *)
  (*   inversion H. *)
  (*   inv H. *)
  (*   apply wf_ocfg_bid_cons_not_in. *)
  (*   unfold wf_ocfg_bid in *. *)
  (*   rewrite inputs_app in H0. *)
  (*   rewrite inputs_cons. rewrite inputs_cons in H0. *)
  (*   rewrite list_cons_app in H0. *)
  (*   rewrite app_assoc in H0. *)
  (*   apply list_norepet_append_left in H0. *)
  (*   rewrite list_cons_app. *)
  (*   rewrite list_norepet_app in *. *)
  (*   intuition. apply list_disjoint_sym. auto. *)
  (*   unfold wf_ocfg_bid in H0. *)
  (*   rewrite inputs_app in H0. rewrite inputs_cons in H0. rewrite list_cons_app in H0. *)
  (*   apply list_norepet_append_commut in H0. rewrite <- app_assoc in H0. *)
  (*   apply list_norepet_append_right in H0. *)
  (*   rewrite list_norepet_app in H0. *)
  (*   destruct H0 as (? & ? & ?). *)
  (*   red in H2. intro. eapply H2; eauto. *)
  (* Qed. *)

  (* (* TODO: Show symmetric case *) *)
  (* Lemma wf_ocfg_app_not_in_r : *)
  (*   forall id (bs bs' : ocfg T), *)
  (*     In id (inputs bs) -> *)
  (*     wf_ocfg_bid (bs' ++ bs) -> *)
  (*     not (In id (inputs bs')). *)
  (* Proof using. *)
  (*   intros. destruct bs. *)
  (*   inversion H. *)
  (*   inv H. *)
  (*   apply wf_ocfg_bid_cons_not_in. *)
  (*   unfold wf_ocfg_bid in *. *)
  (*   rewrite inputs_app in H0. *)
  (*   rewrite inputs_cons. rewrite inputs_cons in H0. *)
  (*   rewrite list_cons_app in H0. *)
  (*   rewrite app_assoc in H0. *)
  (*   apply list_norepet_append_left in H0. *)
  (*   rewrite list_cons_app. *)
  (*   rewrite list_norepet_app in *. *)
  (*   intuition. apply list_disjoint_sym. auto. *)
  (*   unfold wf_ocfg_bid in H0. *)
  (*   rewrite inputs_app in H0. rewrite inputs_cons in H0. rewrite list_cons_app in H0. *)
  (*   apply list_norepet_append_commut in H0. rewrite <- app_assoc in H0. *)
  (*   apply list_norepet_append_right in H0. *)
  (*   rewrite list_norepet_app in H0. *)
  (*   destruct H0 as (? & ? & ?). *)
  (*   red in H2. intro. eapply H2; eauto. *)
  (* Qed. *)

  (* Useful tactics:
    - set_solver
    - solve_map_disjoint
    - simplify_map_eq
 *)

  Lemma successors_outputs: forall i b (g : ocfg T),
      g !! i = Some b ->
      successors b ⊆ outputs g.
  Proof.
    intros * Lu.
    rewrite <- (insert_delete _ _ _ Lu).
    rewrite outputs_insert.
    2: now simplify_map_eq.
    set_solver.
  Qed.

  Lemma successor_outputs: forall i j (b: block T) (g : ocfg T),
      j ∈ successors b ->
      g !! i = Some b ->
      j ∈ outputs g.
  Proof using.
    intros * In Lu.
    pose proof successors_outputs _ _ Lu.
    set_solver.
  Qed.

  Lemma find_block_in_inputs :
    forall i (g : ocfg T),
      i ∈ inputs g ->
      is_Some (g !! i).
  Proof using.
    intros; now apply elem_of_dom.
  Qed.

  Lemma no_reentrance_not_in (g1 g2 : ocfg T) :
    no_reentrance g1 g2 ->
    forall i, i ∈ outputs g2 -> i ∉ inputs g1.
  Proof.
    set_solver.
  Qed.

  Lemma no_reentrance_app_l :
    forall (g1 g1' g2 : ocfg T),
      no_reentrance (g1 ∪ g1') g2 <->
      no_reentrance g1 g2 /\ no_reentrance g1' g2.
  Proof.
    set_solver.
  Qed.

  Lemma no_reentrance_app_r :
    forall (g1 g2 g2' : ocfg T),
      g2 ##ₘ g2' ->
      no_reentrance g1 (g2 ∪ g2') <->
      no_reentrance g1 g2 /\ no_reentrance g1 g2'.
  Proof.
    intros * DISJ; unfold no_reentrance; split; [intros H | intros [H1 H2]].
    - rewrite outputs_union in H; set_solver.
    - rewrite outputs_union; set_solver.
  Qed.

  Lemma no_duplicate_bid_not_in_l (g1 g2 : ocfg T) :
    no_duplicate_bid g1 g2 ->
    forall x, In x (inputs g2) -> ~ In x (inputs g1).
  Proof using.
    intros; eauto using Coqlib.list_disjoint_notin, Coqlib.list_disjoint_sym.
  Qed.

  Lemma no_duplicate_bid_not_in_r (g1 g2 : ocfg T) :
    no_duplicate_bid g1 g2 ->
    forall x, In x (inputs g1) -> ~ In x (inputs g2).
  Proof using.
    intros; eauto using Coqlib.list_disjoint_notin, Coqlib.list_disjoint_sym.
  Qed.

  Lemma independent_flows_no_reentrance_l (g1 g2 : ocfg T):
    independent_flows g1 g2 ->
    no_reentrance g1 g2.
  Proof using.
    intros INDEP; apply INDEP; auto.
  Qed.

  Lemma independent_flows_no_reentrance_r (g1 g2 : ocfg T):
    independent_flows g1 g2 ->
    no_reentrance g2 g1.
  Proof using.
    intros INDEP; apply INDEP; auto.
  Qed.

  Lemma independent_flows_no_duplicate_bid (g1 g2 : ocfg T):
    independent_flows g1 g2 ->
    no_duplicate_bid g1 g2.
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

  Lemma wf_ocfg_bid_cons' : forall (b : _ T) (g : ocfg T),
      not (In (blk_id b) (inputs g)) ->
      wf_ocfg_bid g ->
      wf_ocfg_bid (b :: g).
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

  Lemma free_in_cfg_app : forall (g1 g2 : ocfg T) b,
      free_in_cfg (g1 ++ g2) b <->
      (free_in_cfg g1 b /\ free_in_cfg g2 b).
  Proof using.
    intros; split; unfold free_in_cfg; intro FREE.
    - split; intros abs; eapply FREE; rewrite inputs_app; eauto using in_or_app.
    - rewrite inputs_app; intros abs; apply in_app_or in abs; destruct FREE as [FREEL FREER]; destruct abs; [eapply FREEL | eapply FREER]; eauto.
  Qed.

  Lemma wf_ocfg_bid_distinct_labels :
    forall (g1 g2 : ocfg T) b1 b2,
      wf_ocfg_bid (g1 ++ g2) ->
      In b1 (inputs g1) ->
      In b2 (inputs g2) ->
      b1 <> b2.
  Proof using.
    intros * WF IN1 IN2.
    eapply wf_ocfg_bid_app_not_in_l in IN2; eauto.
    destruct (Eqv.eqv_dec_p b1 b2).
    rewrite e in IN1; contradiction IN2; auto.
    auto.
  Qed.

  Lemma predecessors_app :
    forall (g g' : ocfg T) f,
      predecessors f (g ++ g') = predecessors f g' ++ predecessors f g.
  Proof using.
    induction g' as [| bk g' IH] using rev_ind.
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
    forall (g : ocfg T) bk f,
      predecessors f (bk :: g) = predecessors f g ++ predecessors f [bk].
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
        break_match_hyp; intuition.
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
        right; exists bk; intuition.
      + right.
        exists bk'; intuition.
    - edestruct IH as [INACC | (bk' & INbk & -> & PRED)]; eauto.
      right; exists bk'; intuition.
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
    unfold Eqv.eqv, AstLib.eqv_raw_id in *; intuition.
    reflexivity.
  Qed.

  Lemma wf_ocfg_bid_In_is_found :
    forall (g : ocfg T) bk,
      wf_ocfg_bid g ->
      In bk g ->
      find_block g bk.(blk_id) = Some bk.
  Proof using.
    induction g as [| x g IH]; intros * WF IN; [inv IN |].
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
    break_match_hyp; intuition.
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
        break_match; [| intuition].
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
    forall (g1 g2 : ocfg T) bid,
      find_block g1 bid = None ->
      find_block (g1 ++ g2) bid = find_block g2 bid.
  Proof using.
    intros; apply find_none_app; auto.
  Qed.

  Lemma find_block_some_app:
    forall (g1 g2 : ocfg T) (bk : block T) bid,
      find_block g1 bid = Some bk ->
      find_block (g1 ++ g2) bid = Some bk.
  Proof using.
    intros; apply find_some_app; auto.
  Qed.

  Lemma find_block_Some_In_inputs : forall (g : ocfg T) b bk,
      find_block g b = Some bk ->
      In b (inputs g).
  Proof using.
    induction g as [| hd g IH].
    - intros * H; inv H.
    - intros * FIND.
      destruct (Eqv.eqv_dec_p (blk_id hd) b).
      cbn; rewrite e; auto.
      right; eapply IH.
      erewrite <- find_block_ineq; eauto.
  Qed.

  Lemma wf_ocfg_bid_find_None_app_l :
    forall (g1 g2 : ocfg T) b bk,
      wf_ocfg_bid (g1 ++ g2)%list ->
      find_block g2 b = Some bk ->
      find_block g1 b = None.
  Proof using.
    induction g1 as [| b g1 IH]; intros * WF FIND.
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
      + inv LU; break_match_hyp; intuition.
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
    break_match_goal; break_match_hyp; intuition.
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
    break_match_goal; break_match_hyp; intuition.
    inv FIND; auto.
  Qed.

  Lemma wf_ocfg_bid_find_block_unique :
    forall (g : ocfg T) bk1 b1 bk2,
      wf_ocfg_bid g ->
      find_block g b1 = Some bk1 ->
      find_block g b1 = Some bk2 ->
      bk1 = bk2.
  Proof using.
    induction g as [| bk g IH]; intros * WF FIND1 FIND2; [inv FIND1 |].
    cbn in *.
    break_match_hyp.
    inv FIND1; inv FIND2; auto.
    break_match_hyp; intuition.
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
    - break_match_hyp; intuition.
      do 2 red in e.
      exfalso; clear Heqb.
      red in H.
      cbn in H.
      rewrite e in H.
      inv H.
      eapply H2; left; reflexivity.
    - break_match_hyp; intuition.
      apply IH.
      apply wf_ocfg_commut_hd in H.
      eapply wf_ocfg_bid_cons; eauto.
  Qed.

  Lemma In_find_block :
    forall (g : ocfg T) bk,
      In bk g ->
      exists bk', find_block g bk.(blk_id) = Some bk'.
  Proof using.
    induction g as [| x g IH]; intros * IN; [inv IN | ].
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
    + apply IH in H; intuition.
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

  Lemma convert_typ_outputs : forall (g : ocfg typ),
      outputs (convert_typ [] g) = outputs g.
  Proof using.
    induction g as [| bk g IH]; [reflexivity |].
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
