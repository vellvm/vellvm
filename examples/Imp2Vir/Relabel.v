From Coq Require Import
     Compare_dec
     FSets.FMapList
     String
     Structures.OrderedType
     Structures.OrderedTypeEx
     ZArith.

From ExtLib Require Import
     FMapAList
     Structures.Monad
     Tactics.

From ITree Require Import
     ITree
     ITreeFacts.

From Vellvm Require Import
     Semantics
     Syntax
     Syntax.ScopeTheory
     Utils.AListFacts
     Utils.Tactics
     Utils.Util.

Section Relabel.

Definition bid_map := alist block_id block_id.
Import MonadNotation.

Definition blk_id_relabel m bid : block_id :=
  match alist_find bid m with
  | Some bid => bid
  | None => bid
  end.

Theorem blk_id_relabel_find : forall {m} {bid bid'},
  alist_find bid m = Some bid' -> blk_id_relabel m bid = bid'.
Proof.
  intros.
  unfold blk_id_relabel.
  now rewrite H.
Qed.

Definition blk_id_relabel_rel (m : alist block_id block_id) bid bid' : Prop :=
  alist_find bid m = Some bid'.

Definition blk_term_relabel {typ} m t : terminator typ :=
  match t with
  | TERM_Br_1 bid => TERM_Br_1 (blk_id_relabel m bid)
  | TERM_Br e bid bid' => TERM_Br e (blk_id_relabel m bid) (blk_id_relabel m bid')
  | TERM_Switch e bid l => TERM_Switch e
    (blk_id_relabel m bid)
    (List.map (fun '(lit, bid) => (lit, blk_id_relabel m bid)) l)
  | t => t
  end.

Definition blk_phi_relabel {typ} m ph : phi typ :=
  let '(Phi t l) := ph in
  Phi t (List.map (fun '(bid, e) => (blk_id_relabel m bid, e)) l).

Definition blk_phis_relabel {typ} m l : list (local_id * phi typ) :=
  List.map (fun '(lid, phi) => (lid, blk_phi_relabel m phi)) l.

Definition bk_relabel {typ} (m : bid_map) (bk : block typ) : block typ :=
  mk_block
    (blk_id_relabel m (blk_id bk))
    (blk_phis_relabel m (blk_phis bk))
    (blk_code bk)
    (blk_term_relabel m (blk_term bk))
    (blk_comments bk).

Definition ocfg_relabel {typ} m cfg : ocfg typ :=
  List.map (bk_relabel m) cfg.

Definition ocfg_relabel_rel' {typ} (cfg cfg' : ocfg typ) m : Prop :=
  ocfg_relabel m cfg = cfg'.

Definition ocfg_relabel_rel {typ} (cfg cfg' : ocfg typ) : Prop :=
  exists m, ocfg_relabel_rel' cfg cfg' m.

Theorem bk_relabel_id : forall {typ} (bk : block typ), bk_relabel nil bk = bk.
Proof.
  intros.
  destruct bk.
  unfold bk_relabel.
  simpl.
  f_equal; try (compute; now break_match).
  unfold blk_phis_relabel, blk_phi_relabel, blk_id_relabel. simpl.
  rewrite map_ext with (g := fun x => x).
  - apply map_id.
  - intros. repeat break_match. do 2 f_equal.
    rewrite map_ext with (g := fun x => x).
    + apply map_id.
    + intros. break_match. reflexivity.
  - unfold blk_term_relabel.
    break_match; try easy.
    f_equal. subst.
    induction brs; intros; [ reflexivity |].
    simpl. f_equal; [ now break_let |].
    apply IHbrs.
Qed.

Definition inj_map (m : bid_map) : Prop :=
  forall a b a',
    alist_find a m = Some a' ->
    alist_find b m = Some a' ->
    a = b.

Definition defined_map (m : bid_map) (bids : list block_id) : Prop :=
  forall i : block_id, List.In i bids -> exists i', alist_find i m = Some i'.

Definition map_domain (m : bid_map) (bids : list block_id) : Prop :=
  forall bid,
    (In bid bids -> exists bid', alist_find bid m = Some bid') /\
    forall bid', alist_find bid m = Some bid' -> In bid bids.


(* Definitions to build a bid mapping. Not used anywhere. *)

Definition blk_id_relabel_build_map (bid bid' : raw_id) m : option bid_map :=
  match alist_find bid m with
  | Some bid => if raw_id_eq_dec bid bid' then Some m else None
  | None => Some (alist_add bid bid' m)
  end.

Definition blk_term_relabel_build_map {typ} (t t' : terminator typ) m : option bid_map :=
  match t, t' with
  | TERM_Br_1 bid, TERM_Br_1 bid' =>
    blk_id_relabel_build_map bid bid' m
  | TERM_Br e bid1 bid2, TERM_Br e' bid1' bid2' =>
    m <- blk_id_relabel_build_map bid1 bid1' m;;
    blk_id_relabel_build_map bid2 bid2' m
  | TERM_Ret _, TERM_Ret _ | TERM_Ret_void, TERM_Ret_void => Some m
  | _, _ => None
  end.

Definition blk_phi_relabel_build_map {typ} (ph ph' : phi typ) m : option bid_map :=
  Some m.

Definition blk_phis_relabel_build_map {typ} (phis phis' : list (local_id * phi typ)) m : option bid_map :=
  Some m.

Definition bk_relabel_build_map {typ} (bk bk' : block typ) m : option bid_map :=
  m <- blk_id_relabel_build_map (blk_id bk) (blk_id bk') m;;
  m <- blk_phis_relabel_build_map (blk_phis bk) (blk_phis bk') m;;
  blk_term_relabel_build_map (blk_term bk) (blk_term bk') m.

Fixpoint ocfg_relabel_build_map' {typ} (cfg cfg' : ocfg typ) m : option bid_map :=
  match cfg, cfg' with
  | (bk::t), (bk'::t') =>
    m <- bk_relabel_build_map bk bk' m;;
    ocfg_relabel_build_map' t t' m
  | nil, nil => Some m
  | _, _ => None
  end.

Definition ocfg_relabel_build_map {typ} (cfg cfg' : ocfg typ) : option bid_map :=
  ocfg_relabel_build_map' cfg cfg' nil.


Theorem blk_id_relabel_find_block1 : forall {typ} (cfg : ocfg typ) m bid bk,
  find_block cfg bid = Some bk ->
  defined_map m (inputs cfg) ->
  inj_map m ->
  find_block (ocfg_relabel m cfg) (blk_id_relabel m bid) = Some (bk_relabel m bk).
Proof.
  induction cfg; intros ? ? ? H0 H1 H2.
  - now simpl in H0.
  - simpl in *.
    inv_all.
    destruct (Eqv.eqv_dec_p (blk_id a) bid);
    destruct (Eqv.eqv_dec_p (blk_id_relabel m (blk_id a)) (blk_id_relabel m bid)).
    + now inv H0.
    + inv H0.
      unfold Eqv.eqv, eqv_raw_id in n, e.
      subst bid. tauto.
    + exfalso.
      unfold Eqv.eqv, eqv_raw_id in n, e.
      subst.
      simpl in *.
      unfold defined_map in H1.
      unfold blk_id_relabel in e.
      pose proof (H1 (blk_id a) (or_introl eq_refl)) as [].
      rewrite H in e.
      apply find_block_Some_In_inputs in H0.
      pose proof (H1 bid (or_intror H0)) as [].
      rewrite H3 in e.
      subst.
      pose proof (H2 _ _ _ H H3).
      tauto.
    + eapply IHcfg; try eassumption.
      unfold defined_map in *.
      intros. apply H1. simpl. tauto.
Qed.

Theorem blk_id_relabel_find_block2 : forall {typ} (cfg : ocfg typ) m bid bid' bk',
  find_block (ocfg_relabel m cfg) bid' = Some bk' ->
  defined_map m (inputs cfg) ->
  inj_map m ->
  alist_find bid m = Some bid' ->
  exists bk, bk' = bk_relabel m bk /\ find_block cfg bid = Some bk.
Proof.
  induction cfg; intros ? ? ? ? H0 H1 H2 H3.
  - now simpl in H0.
  - simpl in *.
    destruct (Eqv.eqv_dec_p (blk_id a) bid);
    destruct (Eqv.eqv_dec_p (blk_id_relabel m (blk_id a)) bid');
    unfold Eqv.eqv, eqv_raw_id in *.
    + eexists. now inv H0.
    + subst. simpl in n. unfold blk_id_relabel in n. rewrite H3 in n. tauto.
    + exfalso. clear bk' H0.
      subst.
      simpl in *.
      pose proof (H1 (blk_id a) (or_introl eq_refl)) as [].
      unfold blk_id_relabel in H3.
      rewrite H in H3.
      apply n.
      eapply H2; eassumption.
    + eapply IHcfg; try eassumption; try tauto.
      unfold defined_map in *.
      intros. apply H1. simpl. tauto.
Qed.

Theorem blk_id_relabel_find_block : forall {typ} (cfg : ocfg typ) m bid bk bk',
  find_block cfg bid = Some bk ->
  find_block (ocfg_relabel m cfg) (blk_id_relabel m bid) = Some bk' ->
  defined_map m (inputs cfg) ->
  inj_map m ->
  bk' = bk_relabel m bk.
Proof.
  unfold defined_map.
  induction cfg; intros ? ? ? ? H0 H1 H2 H3.
  - now compute in H0.
  - simpl in *.
    inv_all.
    destruct (Eqv.eqv_dec_p (blk_id a) bid);
    destruct (Eqv.eqv_dec_p (blk_id_relabel m (blk_id a)) (blk_id_relabel m bid));
    rename H1 into H.
    + inv H. inv H0.
      reflexivity.
    + inv H. inv H0.
      unfold Eqv.eqv, eqv_raw_id in n, e.
      subst bid. tauto.
    + inv H.
      unfold Eqv.eqv, eqv_raw_id in n, e. simpl in e.
      apply find_block_Some_In_inputs in H0 as ?.
      pose proof (H2 bid (or_intror H)).
      unfold blk_id_relabel in e.
      destruct H1.
      rewrite H1 in e.
      specialize (H2 (blk_id a) (or_introl eq_refl)).
      destruct H2.
      rewrite H2 in e.
      subst x0.
      specialize (H3 _ _ _ H2 H1).
      tauto.
    + eapply IHcfg; try eassumption.
      intuition.
Qed.

Theorem ocfg_relabel_build_map_def_inputs : forall {typ} (cfg cfg' : ocfg typ) m m',
  ocfg_relabel_build_map' cfg cfg' m = Some m' ->
  defined_map m' (inputs cfg).
Proof.
  unfold defined_map.
  induction cfg; intros; [ destruct H0 |].
  simpl in *.
  destruct cfg'; [ discriminate |].
  destruct H0.
  - subst.
    break_match; [| discriminate ].
    unfold bk_relabel_build_map in Heqo.
    simpl in Heqo.
    shelve. (* tedious *)
  - break_match; eapply IHcfg; try eassumption; discriminate.
  Unshelve. all: auto.
Abort.

Theorem bk_relabel_build_map_preserve : forall {typ} (bk bk' : block typ) m m' bid bid',
  alist_find bid m = Some bid' ->
  bk_relabel_build_map bk bk' m = Some m' ->
  alist_find bid m' = Some bid'.
Proof.
  intros.
  unfold bk_relabel_build_map, blk_id_relabel_build_map, blk_term_relabel_build_map in H0.
  simpl in H0.
  repeat break_match;
    try discriminate;
    try injection Heqo as Heqo; try injection H0 as H0; subst; try assumption.
  1,2: rewrite alist_find_neq; [ assumption | intro; subst; now rewrite H in * ].
  - unfold blk_id_relabel_build_map in *.
    repeat break_match;
      try discriminate;
      try injection Heqo0 as Heqo0; try injection H0 as H0; subst; try assumption.
    1,2: rewrite alist_find_neq; [ assumption | intro; subst; now rewrite H in * ].
    repeat rewrite alist_find_neq; try assumption;
      intro; subst.
    + now rewrite H in *.
    + apply alist_find_add_none in Heqo. now rewrite H in *.
  - unfold blk_id_relabel_build_map in *.
    repeat break_match;
      try discriminate;
      try injection Heqo0 as Heqo0; try injection H0 as H0; subst; try assumption.
Abort. (* easy but tedious, automate? *)

Theorem ocfg_relabel_build_map_preserve : forall {typ} (cfg cfg' : ocfg typ) m m' bid bid',
  alist_find bid m = Some bid' ->
  ocfg_relabel_build_map' cfg cfg' m = Some m' ->
  alist_find bid m' = Some bid'.
Proof.
  induction cfg; intros.
  - simpl in H0. destruct cfg'; try discriminate. inversion H0. subst m. assumption.
  - destruct cfg'; try discriminate.
    simpl in *.
    break_match; [| discriminate ].
    eapply IHcfg; [| eassumption ].
Abort.
    (*eapply bk_relabel_get_map_preserve; eassumption.
Qed.*)

Lemma assoc_alist_find : forall A B k (m : list (A * B)) {RD : RelDec.RelDec eq},
  assoc k m = alist_find k m.
Proof.
  reflexivity.
Qed.

Lemma alist_find_map_keys : forall {A B : Type} {RD : RelDec.RelDec eq},
  RelDec.RelDec_Correct RD -> forall (m : list (A * B)) (f : A -> A) k,
  (forall k' v', alist_find k' m = Some v' -> f k = f k' -> k = k') ->
  alist_find (f k) (List.map (fun '(k,v) => (f k, v)) m) = alist_find k m.
Proof.
  intros.
  induction m; [ reflexivity |].
  simpl.
  repeat break_let.
  inv Heqp.
  repeat break_match.
  - reflexivity.
  - apply H in Heqb0.
    apply RelDec.neg_rel_dec_correct in Heqb1.
    eapply H0 in Heqb0. tauto.
    rewrite <- assoc_alist_find. now rewrite assoc_hd.
  - apply H in Heqb1.
    apply RelDec.neg_rel_dec_correct in Heqb0.
    exfalso.
    apply Heqb0.
    now f_equal.
  - eapply IHm.
    intros.
    destruct (RelDec.rel_dec k' a1) eqn:?.
    + apply H in Heqb2. subst. eapply H0; try eassumption.
      rewrite <- assoc_alist_find. now rewrite assoc_hd.
    + apply RelDec.neg_rel_dec_correct in Heqb2. eapply H0; try eassumption.
      rewrite <- assoc_alist_find in *. rewrite assoc_tl; eassumption.
Qed.

Lemma alist_find_key_in : forall {A B : Type} {RD : RelDec.RelDec eq},
  RelDec.RelDec_Correct RD -> forall k (m : alist A B) v,
  alist_find k m = Some v ->
  In k (List.map fst m).
Proof.
  intros.
  induction m; [ easy |].
  simpl in *.
  break_let.
  destruct (RelDec.rel_dec k a0) eqn:?.
  - apply H in Heqb0.
    now left.
  - tauto.
Qed.

Theorem eutt_phi_relabel : forall {typ} (cfg : ocfg typ) bidf bidf' lid phi m,
  inj_map m ->
  defined_map m (phi_sources phi) ->
  alist_find bidf m = Some bidf' ->
  eutt eq (denote_phi bidf (lid, phi)) (denote_phi bidf' (lid, blk_phi_relabel m phi)).
Proof.
  intros ? ? ? ? ? ? ? ? ? H2.
  unfold denote_phi.
  repeat break_let. simpl in *.
  inv Heqp0.
  rewrite !assoc_alist_find.
  assert (H3 : forall (k' : block_id) (v' : exp dtyp),
    alist_find k' args = Some v' -> blk_id_relabel m bidf = blk_id_relabel m k' -> bidf = k'). {
    intros ? ? H3 H4.
    apply alist_find_key_in in H3.
    apply H0 in H3 as [? H3].
    unfold blk_id_relabel in H4.
    rewrite H2, H3 in H4. subst.
    eapply H; try eassumption.
    apply RelDec.RelDec_Correct_eq_typ.
  }
  do 2 break_match.
  - apply eutt_clo_bind with (UU := eq); [| intros; now subst ].
    erewrite <- alist_find_map_keys in Heqo.
    erewrite blk_id_relabel_find in Heqo by eassumption.
    rewrite Heqo0 in Heqo.
    now inv Heqo. apply RelDec.RelDec_Correct_eq_typ. apply H3.
  - exfalso.
    erewrite <- alist_find_map_keys with (f := blk_id_relabel m) in Heqo.
    rewrite (blk_id_relabel_find H2) in Heqo.
    erewrite Heqo0 in Heqo.
    discriminate. apply RelDec.RelDec_Correct_eq_typ. apply H3.
  - exfalso.
    erewrite <- alist_find_map_keys with (f := blk_id_relabel m) in Heqo.
    rewrite (blk_id_relabel_find H2) in Heqo.
    erewrite Heqo0 in Heqo.
    discriminate. apply RelDec.RelDec_Correct_eq_typ. apply H3.
  - reflexivity.
Qed.

Definition phis_sources {typ} (phis : list (local_id * phi typ)) : list (block_id) :=
  concat (List.map (compose snd phi_sources) phis).

Theorem eutt_phis_relabel : forall {typ} (cfg : ocfg typ) bidf bidf' phis m,
  inj_map m ->
  defined_map m (phis_sources phis) ->
  alist_find bidf m = Some bidf' ->
  eutt eq (denote_phis bidf phis) (denote_phis bidf' (blk_phis_relabel m phis)).
Proof.
  intros ? ? ? ? ? ? ? ? H2.
  cbn.
  apply eutt_clo_bind with (UU := eq).
  induction phis.
  - cbn.
    reflexivity.
  - cbn.
    apply eutt_clo_bind with (UU := eq).
    apply eutt_translate; [ reflexivity |].
    break_let.
    eapply eutt_phi_relabel; try eassumption.
    {
      unfold defined_map.
      intros.
      apply H0.
      unfold phis_sources, compose.
      simpl. apply in_app_iff. now left.
    }
    intros.
    apply eutt_clo_bind with (UU := eq).
    apply IHphis.
    {
      unfold defined_map.
      intros.
      apply H0.
      unfold phis_sources, compose.
      simpl.
      apply in_app_iff.
      now right.
    }
    intros.
    now subst.
  - intros. now subst.
Qed.

Definition term_relabel_helper_rel m (bidv bidv' : block_id + uvalue) :=
  match bidv, bidv' with
  | inl bid, inl bid' => blk_id_relabel_rel m bid bid'
  | inr v, inr v' => v = v'
  | _, _ => False
  end.

Definition switch_relabel_helper_rel m (l l' : list (dvalue * block_id)) :=
  Forall2 (fun '(v, bid) '(v', bid') =>
    v = v' /\ blk_id_relabel_rel m bid bid'
  ) l l'.

Lemma select_switch_indep_default : forall v default default' switches,
  forall s, select_switch v default switches = inl s -> select_switch v default' switches = inl s.
Proof.
  induction switches; intros. now simpl in H.
  simpl in *.
  repeat (break_match; try trivial); try discriminate; now apply IHswitches.
Qed.

Lemma select_switch_relabel : forall m v default switches switches',
  switch_relabel_helper_rel m switches switches' ->
  select_switch v (blk_id_relabel m default) switches = select_switch v default switches'. (* no *)
Proof.
  unfold switch_relabel_helper_rel.
  induction switches; intros; destruct switches'.
  - simpl. f_equal. (* needs more hypotheses *)
Abort.

Theorem eutt_term_relabel : forall cfg bid bid' bk m,
  defined_map m (outputs cfg) ->
  find_block cfg bid = Some bk ->
  find_block (ocfg_relabel m cfg) bid' = Some (bk_relabel m bk) ->
  eutt (term_relabel_helper_rel m)
    (denote_terminator (blk_term bk))
    (denote_terminator (blk_term_relabel m (blk_term bk))).
Proof.
  intros ? ? ? ? ? H2 H3 H4.
  destruct (blk_term bk) eqn:?; simpl; try (apply eutt_eq_bind; tauto).
  - break_match.
    apply eutt_eq_bind.
    intros.
    apply eutt_Ret.
    now f_equal.
  - apply eutt_Ret.
    reflexivity.
  - break_match.
    apply eutt_eq_bind.
    intros.
    apply eutt_eq_bind.
    intros. subst.
    break_match;
    try (apply eutt_eq_bind; intro u1; destruct u1).
    unfold term_relabel_helper_rel, blk_id_relabel_rel, blk_id_relabel.
    break_match; simpl; apply eutt_Ret;
    (eapply In_bk_outputs in H3; [ apply H2 in H3 as []; now rewrite H |];
      unfold successors; rewrite Heqt; simpl; tauto).
  - apply eutt_Ret.
    unfold term_relabel_helper_rel, blk_id_relabel_rel, blk_id_relabel.
    eapply In_bk_outputs in H3; [ apply H2 in H3 as []; now rewrite H |].
    unfold successors; rewrite Heqt; simpl; tauto.
  - break_let. subst.
    apply eutt_eq_bind.
    intro.
    apply eutt_eq_bind.
    intro.
    simpl.
    repeat break_match.
    unfold raiseUB. apply eutt_eq_bind. tauto.
    apply eutt_clo_bind with (UU := switch_relabel_helper_rel m); admit. (* TERM_Switch *)
Admitted.

Definition ocfg_relabel_helper_rel m (bidsv bidsv' : block_id * block_id + uvalue) : Prop :=
  match bidsv, bidsv' with
  | inl (bidf, bidt), inl (bidf', bidt') =>
    blk_id_relabel_rel m bidf bidf' /\ blk_id_relabel_rel m bidt bidt'
  | inr v, inr v' => v = v'
  | _, _ => False
  end.

Theorem eutt_ocfg_relabel : forall cfg bidf0 bidf0' bidt0 bidt0' m,
  (bidf0 = bidt0 <-> bidf0' = bidt0') ->
  alist_find bidf0 m = Some bidf0' ->
  alist_find bidt0 m = Some bidt0' ->
  inj_map m ->
  defined_map m (inputs cfg) ->
  defined_map m (outputs cfg) ->
  Forall (fun bk => defined_map m (phis_sources (blk_phis bk))) cfg ->
  eutt (ocfg_relabel_helper_rel m)
    (denote_ocfg cfg (bidf0, bidt0))
    (denote_ocfg (ocfg_relabel m cfg) (bidf0', bidt0')).
Proof.
  intros ? ? ? ? ? ? H4 H0 H7 H5 H6 H8 H10.
  set (I := blk_id_relabel_rel m).
  set (I' := fun fto fto' =>
    I (fst fto) (fst fto') /\ I (snd fto) (snd fto')).
  apply (@eutt_iter_gen _ _ _ I').
  - simpl.
    intros [bidf bidt] [bidf' bidt'] H1.
    unfold I' in H1. simpl in H1. destruct H1 as [H1 H2].
    do 2 break_match.
    + assert (b0 = bk_relabel m b). {
        apply (blk_id_relabel_find_block cfg m bidt); try assumption.
        unfold I, blk_id_relabel_rel in H2. unfold blk_id_relabel. now rewrite H2.
      }
      subst b0.
      apply eutt_clo_bind with (UU := term_relabel_helper_rel m).
      unfold denote_block.
      (* phis *)
      apply eutt_clo_bind with (UU := @eq unit).
      eapply eutt_phis_relabel; try eassumption.
      eapply Forall_forall in H10; try eassumption.
      now apply find_block_In' in Heqo.
      intros.
      (* code *)
      apply eutt_eq_bind.
      (* terminator *)
      intros _.
      simpl.
      apply eutt_translate_gen. simpl.
      eapply eutt_term_relabel; try eassumption.
      * (* post terminator *)
        intros ? ? H3.
        do 2 break_match; try easy; unfold term_relabel_helper_rel in H3.
        --apply eutt_Ret.
          left. unfold I'. simpl.
          subst.
          tauto.
        --apply eutt_Ret.
          right. simpl.
          assumption.
    + exfalso.
      unfold I, blk_id_relabel_rel in H2.
      apply (blk_id_relabel_find_block1 cfg m bidt b) in Heqo; try assumption.
      unfold blk_id_relabel in Heqo. rewrite H2 in Heqo.
      rewrite Heqo in Heqo0. discriminate.
    + exfalso.
      unfold I, blk_id_relabel_rel in H2.
      apply (blk_id_relabel_find_block2 cfg m bidt) in Heqo0 as [? [? H9]]; try assumption.
      now rewrite H9 in Heqo.
    + unfold I, blk_id_relabel_rel in H1, H2. apply eutt_Ret.
      right.
      unfold ocfg_relabel_helper_rel, blk_id_relabel_rel.
      tauto.
  - (* Proof that the relation holds initially. *)
    unfold I', I, blk_id_relabel_rel, blk_id_relabel.
    simpl.
    setoid_rewrite H0. setoid_rewrite H7.
    tauto.
Qed.

Theorem eutt_cfg_relabel : forall cfg cfg' m,
  ocfg_relabel m (blks cfg) = (blks cfg') ->
  alist_find (init cfg) m = Some (init cfg') ->
  inj_map m ->
  defined_map m (inputs (blks cfg)) ->
  defined_map m (outputs (blks cfg)) ->
  Forall (fun bk => defined_map m (phis_sources (blk_phis bk))) (blks cfg) ->
  eutt eq (denote_cfg cfg) (denote_cfg cfg').
Proof.
  intros.
  unfold denote_cfg.
  apply eutt_clo_bind with (UU := ocfg_relabel_helper_rel m).
  rewrite <- H.
  apply eutt_ocfg_relabel; try assumption.
  tauto.
  intros.
  unfold ocfg_relabel_helper_rel in H5.
  repeat break_match; subst; try easy.
Abort. (* the strings do not match... *)

End Relabel.
