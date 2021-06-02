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
     Utils.Tactics.
From Imp2Vir Require Import Unique.

Definition bid_map := alist block_id block_id.
Import MonadNotation.

Definition blk_id_relabel_get_map (bid bid' : raw_id) m : option bid_map :=
  match alist_find bid m with
  | Some bid => if raw_id_eq_dec bid bid' then Some m else None
  | None => Some (alist_add bid bid' m)
  end.

Definition blk_term_relabel_get_map {typ} (t t' : terminator typ) m : option bid_map :=
  match t, t' with
  | TERM_Br_1 bid, TERM_Br_1 bid' =>
    blk_id_relabel_get_map bid bid' m
  | TERM_Br e bid1 bid2, TERM_Br e' bid1' bid2' =>
    m <- blk_id_relabel_get_map bid1 bid1' m;;
    blk_id_relabel_get_map bid2 bid2' m
  | TERM_Ret _, TERM_Ret _ | TERM_Ret_void, TERM_Ret_void => Some m
  | _, _ => None
  end.

Definition bk_relabel_get_map {typ} (bk bk' : block typ) m : option bid_map :=
  m <- blk_id_relabel_get_map (blk_id bk) (blk_id bk') m;;
  blk_term_relabel_get_map (blk_term bk) (blk_term bk') m.

Fixpoint ocfg_relabel_get_map' {typ} (cfg cfg' : ocfg typ) m : option bid_map :=
  match cfg, cfg' with
  | (bk::t), (bk'::t') =>
    m <- bk_relabel_get_map bk bk' m;;
    ocfg_relabel_get_map' t t' m
  | nil, nil => Some m
  | _, _ => None
  end.

Definition ocfg_relabel_get_map {typ} (cfg cfg' : ocfg typ) : option bid_map :=
  ocfg_relabel_get_map' cfg cfg' nil.

Definition blk_id_relabel m bid : block_id :=
  match alist_find bid m with
  | Some bid => bid
  | None => bid
  end.

Definition blk_id_relabel_rel m bid bid' : Prop :=
  blk_id_relabel m bid = bid'.

Definition blk_term_relabel {typ} m t : terminator typ :=
  match t with
  | TERM_Br_1 bid => TERM_Br_1 (blk_id_relabel m bid)
  | TERM_Br e bid bid' => TERM_Br e (blk_id_relabel m bid) (blk_id_relabel m bid')
  | t => t
  end.

Definition bk_relabel {typ} (m : bid_map) (bk : block typ) : block typ :=
  mk_block
    (blk_id_relabel m (blk_id bk))
    (blk_phis bk)
    (blk_code bk)
    (blk_term_relabel m (blk_term bk))
    (blk_comments bk).

Definition ocfg_relabel {typ} m cfg : ocfg typ :=
  List.map (bk_relabel m) cfg.

Definition ocfg_relabel_rel' {typ} (cfg cfg' : ocfg typ) m : Prop :=
  match ocfg_relabel_get_map' cfg cfg' m with
  | Some m => ocfg_relabel m cfg = cfg'
  | None => False
  end.

Definition ocfg_relabel_rel {typ} (cfg cfg' : ocfg typ) : Prop :=
  ocfg_relabel_rel' cfg cfg' nil.

Theorem bk_relabel_id : forall {typ} (bk : block typ), bk_relabel nil bk = bk.
Proof.
  intros.
  destruct bk.
  compute.
  f_equal.
  now break_match.
Qed.

Definition inj_map (m : bid_map) : Prop :=
  forall a b, alist_find a m = alist_find b m -> a = b.

Definition surj_map (m : bid_map) (bids : list block_id) : Prop :=
  forall i : block_id, List.In i bids -> exists i', alist_find i m = Some i'.

Theorem ocfg_relabel_inputs : forall {typ} (cfg cfg' : ocfg typ) m m' (i : block_id),
  ocfg_relabel_get_map' cfg cfg' m = Some m' ->
  List.In i (inputs cfg) -> exists i', alist_find i m' = Some i'.
Proof.
  induction cfg; intros; [ destruct H0 |].
  simpl in *.
  destruct cfg'; [ discriminate |].
  destruct H0.
  - subst.
    break_match; [| discriminate ].
    unfold bk_relabel_get_map in Heqo.
    simpl in Heqo.
    admit. (* tedious *)
  - break_match; eapply IHcfg; try eassumption; discriminate.
  Unshelve. all: auto.
Admitted.

Theorem blk_id_relabel_find_block1 : forall {typ} (cfg cfg' : ocfg typ) m bid bk,
  ocfg_relabel m cfg = cfg' ->
  find_block cfg bid = Some bk ->
  surj_map m (inputs cfg) ->
  inj_map m ->
  find_block cfg' (blk_id_relabel m bid) = Some (bk_relabel m bk).
Proof.
Admitted. (* should be easy, see blk_id_relabel_find_block *)

Theorem blk_id_relabel_find_block2 : forall {typ} (cfg cfg' : ocfg typ) m bid bk',
  ocfg_relabel m cfg = cfg' ->
  find_block cfg' (blk_id_relabel m bid) = Some bk' ->
  (forall i, List.In i (inputs cfg) -> exists i', alist_find i m = Some i') ->
  inj_map m ->
  exists bk, bk' = bk_relabel m bk /\ find_block cfg bid = Some bk.
Proof.
Admitted. (* should be easy, see blk_id_relabel_find_block *)

Theorem blk_id_relabel_find_block : forall {typ} (cfg cfg' : ocfg typ) m bid bk bk',
  ocfg_relabel m cfg = cfg' ->
  find_block cfg bid = Some bk ->
  find_block cfg' (blk_id_relabel m bid) = Some bk' ->
  surj_map m (inputs cfg) ->
  inj_map m ->
  bk' = bk_relabel m bk.
Proof.
  unfold surj_map.
  induction cfg ; intros.
  - compute in H.
    now destruct cfg'.
  - destruct cfg'; [ discriminate |].
    simpl in *.
    inv_all.
    consider (Eqv.eqv_dec_p (blk_id a) bid);
    consider (Eqv.eqv_dec_p (blk_id b) (blk_id_relabel m bid)); intros.
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
      rewrite <- H1 in H2.
      apply H3 in H2.
      tauto.
    + eapply IHcfg; try eassumption.
      intuition.
Qed.

Theorem bk_relabel_get_map_preserve : forall {typ} (bk bk' : block typ) m m' bid bid',
  alist_find bid m = Some bid' ->
  bk_relabel_get_map bk bk' m = Some m' ->
  alist_find bid m' = Some bid'.
Proof.
  intros.
  unfold bk_relabel_get_map, blk_id_relabel_get_map, blk_term_relabel_get_map in H0.
  simpl in H0.
  repeat break_match;
    try discriminate;
    try injection Heqo as Heqo; try injection H0 as H0; subst; try assumption.
  1,2: rewrite alist_find_neq; [ assumption | intro; subst; now rewrite H in * ].
  - unfold blk_id_relabel_get_map in *.
    repeat break_match;
      try discriminate;
      try injection Heqo0 as Heqo0; try injection H0 as H0; subst; try assumption.
    1,2: rewrite alist_find_neq; [ assumption | intro; subst; now rewrite H in * ].
    repeat rewrite alist_find_neq; try assumption;
      intro; subst.
    + now rewrite H in *.
    + apply alist_find_add_none in Heqo. now rewrite H in *.
  - unfold blk_id_relabel_get_map in *.
    repeat break_match;
      try discriminate;
      try injection Heqo0 as Heqo0; try injection H0 as H0; subst; try assumption.
Admitted. (* easy but tedious, automate? *)

Theorem ocfg_relabel_get_map_preserve : forall {typ} (cfg cfg' : ocfg typ) m m' bid bid',
  alist_find bid m = Some bid' ->
  ocfg_relabel_get_map' cfg cfg' m = Some m' ->
  alist_find bid m' = Some bid'.
Proof.
  induction cfg; intros.
  - simpl in H0. destruct cfg'; try discriminate. inversion H0. subst m. assumption.
  - destruct cfg'; try discriminate.
    simpl in *.
    break_match; [| discriminate ].
    eapply IHcfg; [| eassumption ].
    eapply bk_relabel_get_map_preserve; eassumption.
Qed.

Definition ocfg_relabel_helper_rel m (bidsv bidsv' : block_id * block_id + uvalue) : Prop :=
  match bidsv, bidsv' with
  | inl (bidf, bidt), inl (bidf', bidt') =>
    blk_id_relabel_rel m bidf bidf' /\ blk_id_relabel_rel m bidt bidt'
  | inr v, inr v' => v = v'
  | _, _ => False
  end.

Theorem eutt_ocfg_relabel : forall cfg cfg' bidf0 bidf0' bidt0 bidt0' m,
  (bidf0 = bidt0 <-> bidf0' = bidt0') ->
  ocfg_relabel m cfg = cfg' ->
  ocfg_relabel_get_map' cfg cfg' (alist_add bidt0 bidt0' (alist_add bidf0 bidf0' nil)) = Some m ->
  inj_map m ->
  eutt (ocfg_relabel_helper_rel m)
    (denote_ocfg cfg (bidf0, bidt0))
    (denote_ocfg cfg' (bidf0', bidt0')).
Proof.
  intros ? ? ? ? ? ? ? H4 ? ? H5.
  assert (H6 : surj_map m (inputs cfg)). {
    unfold surj_map. intros. eapply ocfg_relabel_inputs; eassumption.
  }
  set (I := blk_id_relabel_rel m).
  set (I' := fun fto fto' =>
    I (fst fto) (fst fto') /\ I (snd fto) (snd fto')).
  apply (@eutt_iter_gen _ _ _ I').
  - simpl.
    intros [bidf bidt] [bidf' bidt'] ?.
    unfold I' in H1. simpl in H1. destruct H1.
    do 2 break_match.
    + assert (b0 = bk_relabel m b). {
        apply (blk_id_relabel_find_block cfg cfg' m bidt); try assumption.
        unfold I, blk_id_relabel_rel in H2. now rewrite H2.
      }
      subst b0.
      set (I'' := fun (x x' : block_id + uvalue) =>
        match x, x' with
        | inl bid, inl bid' => I bid bid'
        | _, _ => x = x'
        end).
      apply eutt_clo_bind with (UU := I'').
      unfold denote_block.
      (* phis *)
      apply eutt_clo_bind with (UU := eq).
      unfold denote_phis. simpl.
      (* eapply eutt_clo_bind with (UU := TODO map block ids in phis) *)
      admit. (* phi nodes ignored for now *)
      intros _ _ _.
      (* code *)
      apply eutt_eq_bind.
      (* terminator *)
      intros _.
      simpl.
      apply eutt_translate_gen.
      destruct (blk_term b); simpl; try (apply eutt_eq_bind; tauto). 5: admit. (* TERM_Switch *)
      * break_match.
        apply eutt_eq_bind.
        intros.
        apply eutt_Ret.
        now f_equal.
      * apply eutt_Ret.
        reflexivity.
      * break_match.
        apply eutt_eq_bind.
        intros. subst.
        apply eutt_eq_bind.
        intros. subst.
        break_match;
        try (apply eutt_eq_bind; intro u1; destruct u1).
        consider (Int1.eq x Int1.one);
          intro; apply eutt_Ret; reflexivity.
      * apply eutt_Ret.
        reflexivity.
      * (* post terminator *)
        intros.
        do 2 break_match; try discriminate; unfold I'' in H0.
        --apply eutt_Ret.
          left. unfold I'. simpl.
          subst.
          tauto.
        --apply eutt_Ret.
          right. f_equal. injection H3. tauto.
    + exfalso.
      unfold I, blk_id_relabel_rel in H2.
      subst bidt'.
      apply (blk_id_relabel_find_block1 cfg cfg' m bidt b) in Heqo; try assumption.
      rewrite Heqo in Heqo0. discriminate.
    + exfalso.
      unfold I, blk_id_relabel_rel in H2.
      subst bidt'.
      eapply (blk_id_relabel_find_block2 cfg cfg' m bidt b) in Heqo0; try assumption.
      rewrite Heqo in Heqo0. destruct Heqo0 as (? & _ & ?). discriminate.
    + unfold I, blk_id_relabel_rel in H1, H2. apply eutt_Ret.
      right.
      unfold ocfg_relabel_helper_rel, blk_id_relabel_rel.
      tauto.
  - (* Proof that the relation holds initially. *)
    unfold I', I, blk_id_relabel_rel, blk_id_relabel.
    simpl.
    erewrite ocfg_relabel_get_map_preserve with (bid' := bidf0'); try eassumption.
    2: {
      assert (bidf0 = bidt0 \/ bidf0 <> bidt0) by tauto.
      destruct H1.
      - rewrite <- H1.
        rewrite <- ((proj1 H4) H1).
        apply alist_find_add_eq.
      - rewrite alist_find_neq; [| assumption ].
        apply alist_find_add_eq.
    }
    split; [ reflexivity |].
    erewrite ocfg_relabel_get_map_preserve with (bid' := bidt0'); try eassumption.
    reflexivity.
    apply alist_find_add_eq.
Admitted.

Theorem eutt_cfg_relabel : forall cfg cfg' bid0 bid0' m,
  ocfg_relabel m (blks cfg) = (blks cfg') ->
  ocfg_relabel_get_map' (blks cfg) (blks cfg') (alist_add bid0 bid0' nil) = Some m ->
  inj_map m ->
  eutt eq (denote_cfg cfg) (denote_cfg cfg').
Proof.
  intros.
  unfold denote_cfg.
  apply eutt_clo_bind with (UU := ocfg_relabel_helper_rel m).
  apply eutt_ocfg_relabel; try assumption.
  tauto.
  admit. (* easy *)
  intros.
  unfold ocfg_relabel_helper_rel in H2.
  repeat break_match; subst; try easy.
  admit. (* the strings do not match... *)
Admitted.
