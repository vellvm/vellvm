From Coq Require Import
     List
     ZArith.
Import ListNotations.
From Vellvm Require Import
     Syntax
     Syntax.ScopeTheory
     Utils.Tactics.

Open Scope nat_scope.

(* Definition and lemmas about relation between block_id *)

Definition eq_bid b b' :=
  match b,b' with
  | Name s, Name s' => String.eqb s s'
  | Anon n, Anon n' => @RelDec.eq_dec int eq_dec_int n n'
  | Raw n, Raw n' => @RelDec.eq_dec int eq_dec_int n n'
  | _ , _ => false
    end.

(* Anon _ <= Raw _ <= Name _*)
Definition leb_bid b b' :=
  match b,b' with
  | Name s, Name s' => true
  | Anon n, Anon n' => (n <=? n')%Z
  | Raw n, Raw n' => (n <=? n')%Z
  | Anon _, Name _ => true
  | Anon _, Raw _ => true
  | Raw _, Anon _ => false
  | Name _, Anon _ => false
  | Name _, Raw _ => false
  | Raw _, Name _ => true
  end.

Definition le_bid (b b': block_id) : Prop :=
  leb_bid b b' = true.

Lemma le_bid_anon : forall b b' n n',
    b = Anon n ->
    b' = Anon n' ->
    le_bid b b' <-> (n <= n')%Z.
Proof.
  intros.
  subst.
  unfold le_bid.
  cbn.
  symmetry ; apply Zle_is_le_bool.
Qed.

Fixpoint max_bid' (l : list block_id) b :=
  match l with
  | [] => b
  | h :: t => if leb_bid b h then max_bid' t h else max_bid' t b
  end.

Fixpoint min_bid' (l : list block_id) b :=
  match l with
  | [] => b
  | h :: t => if leb_bid b h then min_bid' t b else min_bid' t h
  end.

Definition max_bid (l : list block_id) :=
  max_bid' l (hd (Anon 0%Z) l).

Definition min_bid (l : list block_id) :=
  min_bid' l (hd (Anon 0%Z) l).

Lemma leb_bid_refl : forall a, leb_bid a a = true.
Admitted.


Lemma max_bid_spec : forall l,
    (length l >= 1)%nat ->
    Forall (fun b => le_bid b (max_bid l)) l.
Proof.
  induction l ; try (now simpl).
  intros.
  apply Forall_cons.
  unfold le_bid.
  unfold max_bid ; simpl.
  rewrite leb_bid_refl.
Admitted.

Lemma min_bid_spec : forall l,
    (length l >= 1)%nat ->
        Forall (fun b => le_bid (min_bid l) b) l.
Admitted.



Definition mk_anon (n : nat) := Anon (Z.of_nat n).
Lemma neq_mk_anon : forall n1 n2, mk_anon n1 <> mk_anon n2 <-> n1 <> n2.
Proof.
  intros.
  unfold mk_anon.
  split ; intro.
  - intros ->. now destruct H.
  - apply inj_neq in H.
    unfold Zne in H.
    intro.
    injection H0.
    intro.
    rewrite H1 in H .
    contradiction.
Qed.

Lemma eqb_bid_eq : forall b b', eq_bid b b' = true <-> b=b'.
Proof.
  intros.
  split.
  - destruct b,b' ;
      try (intros ; simpl in H ; discriminate) ;
      simpl ; intros ; f_equal ;
      try (now apply String.eqb_eq) ;
      try (now apply Z.eqb_eq).
  - intros ; subst.
    destruct b' ; simpl ;
      try (now apply String.eqb_eq) ;
      try (now apply Z.eqb_eq).
Qed.

Lemma eqb_bid_neq : forall b b', eq_bid b b' = false <-> b<>b'.
Proof.
  intros.
  split.
  - destruct b,b' ;
      try (intros ; simpl in H ; discriminate) ;
      simpl ; intros ; intro ;
      try (apply String.eqb_neq in H);
      try (apply Z.eqb_neq in H);
        inv H0 ; contradiction.
  - intros ; subst.
    destruct b,b' ; simpl ; auto;
    try (apply String.eqb_neq) ;
      try (apply Z.eqb_neq) ;
      intro ; subst ;
    contradiction.
Qed.

Lemma eq_bid_comm : forall b b', eq_bid b b' = eq_bid b' b.
  intros.
  destruct b,b' ; simpl ; auto ;
    try (now apply String.eqb_sym) ;
    try (now apply Z.eqb_sym).
Qed.

Lemma eq_bid_refl : forall b, eq_bid b b = true.
  intros.
  destruct b ; simpl ; auto ;
    try (now apply String.eqb_refl) ;
    try (now apply Z.eqb_refl).
Qed.

Lemma eqv_dec_p_eq : forall b b' r,
    eq_bid b b' = r <-> (if Eqv.eqv_dec_p b b' then true else false) = r.
  intros.
  destruct r eqn:R.
  - destruct (Eqv.eqv_dec_p b b') eqn:E.
    + unfold Eqv.eqv,eqv_raw_id in e ; subst.
      now rewrite eq_bid_refl.
    + unfold Eqv.eqv,eqv_raw_id in n.
      rewrite eqb_bid_eq.
      split ; intros ; subst. contradiction. inversion H.
  - destruct (Eqv.eqv_dec_p b b') eqn:E.
    + unfold Eqv.eqv,eqv_raw_id in e ; subst.
    now rewrite eq_bid_refl.
    + unfold Eqv.eqv,eqv_raw_id in n ; subst.
      rewrite eqb_bid_neq.
      split ; intros ; auto.
Qed.

Lemma eqv_dec_p_refl : forall (b : block_id),
    (if Eqv.eqv_dec_p b b then true else false) = true.
Proof.
  intros.
  destruct (Eqv.eqv_dec_p b b) ; auto.
  unfold Eqv.eqv,eqv_raw_id in n ; auto.
Qed.

Lemma eqv_dec_p_eq_true : forall {T} b b' (xT xF : T),
    eq_bid b b' = true -> (if Eqv.eqv_dec_p b b' then xT else xF) = xT.
Proof.
  intros ; destruct (Eqv.eqv_dec_p b b') eqn:E.
  - reflexivity.
  - unfold Eqv.eqv,eqv_raw_id in n ; subst.
    rewrite eqb_bid_eq in H. now apply n in H.
Qed.

Lemma eqv_dec_p_eq_false : forall {T} b b' (xT xF : T),
    eq_bid b b' = false -> (if Eqv.eqv_dec_p b b' then xT else xF) = xF.
Proof.
   intros ; destruct (Eqv.eqv_dec_p b b') eqn:E.
  - unfold Eqv.eqv,eqv_raw_id in e ; subst.
    rewrite eqb_bid_neq in H. contradiction.
  - reflexivity.
Qed.

(* Misc lemmas on list *)

Lemma In_singleton : forall {A} (x y : A),
    In x [y] <-> x=y.
Proof.
  intros.
  split ; intro.
  cbn in H; intuition.
  subst; apply in_eq.
Qed.

Lemma hd_In : forall {A} (d : A) (l : list A),
    (length l >= 1)%nat ->
    In (hd d l) l.
Proof.
  intros.
  induction l.
  now simpl in H.
  simpl ; now left.
Qed.

Lemma List_norepet_singleton : forall {A} (x : A),
    Coqlib.list_norepet [x].
Proof.
  intros.
  apply Coqlib.list_norepet_cons ; auto.
  apply Coqlib.list_norepet_nil.
Qed.

Fixpoint remove (x : block_id) (l : list block_id) :=
  match l with
  | [] => []
  | h::t => if (eq_bid x h) then remove x t else h::(remove x t)
  end.

Lemma remove_ListRemove :
  forall b l, remove b l = List.remove Eqv.eqv_dec_p b l.
Proof.
  intros.
  induction l ; try reflexivity.
  simpl.
  destruct (eq_bid b a) eqn:E ;
  match goal with
    | |- context[if (_ ?b1 ?b2) then ?xT else ?xF] =>
        try apply (eqv_dec_p_eq_true b1 b2 xT xF) in E
        ; try apply (eqv_dec_p_eq_false b1 b2 xT xF) in E
  end ; setoid_rewrite E.
  - assumption.
  - now f_equal.
Qed.

Lemma in_remove : forall l x y, List.In x (remove y l) -> List.In x l.
Proof. intros.
       rewrite remove_ListRemove in H
       ; apply in_remove in H.
       intuition.
Qed.

Ltac in_list_rem :=
  match goal with
  | h: List.In _ _  |- _ => apply in_remove in h
  end.

Require Import Coqlib.
Require Import Util.

Lemma incl_disjoint : forall {A} (l1 sl1 l2 : list A),
    List.incl sl1 l1 ->
    list_disjoint l1 l2 ->
    list_disjoint sl1 l2.
Proof.
  intros.
  unfold incl in H.
  induction sl1.
  - apply list_disjoint_nil_l.
  - admit.
Admitted.

Lemma remove_disjoint : forall (x : block_id) (l1 l2 : list block_id),
    l1 ⊍ l2 -> (CFGC_Utils.remove x l1) ⊍ l2.
Proof.
  intros.
  induction l1.
  now simpl.
  simpl.
  destruct (eq_bid x a).
  - apply IHl1. now apply list_disjoint_cons_left in H.
  - apply list_disjoint_cons_l_iff in H ; destruct H.
    apply list_disjoint_cons_l.
    now apply IHl1. assumption.
Qed.

Lemma remove_disjoint_remove : forall (x : block_id) (l1 l2 : list block_id),
    (CFGC_Utils.remove x l1) ⊍ (CFGC_Utils.remove x l2) <->
    (CFGC_Utils.remove x l1) ⊍ l2.
Proof.
  intros.
Admitted.

Lemma remove_app:
  forall (x : block_id) (l1 l2 : list block_id),
  CFGC_Utils.remove x (l1 ++ l2) = CFGC_Utils.remove x l1 ++ CFGC_Utils.remove x l2.
Proof.
  intros.
  rewrite !remove_ListRemove.
  apply remove_app.
Qed.

Lemma list_norepet_remove : forall l a,
    list_norepet l ->
    list_norepet (CFGC_Utils.remove a l).
Proof.
  intros.
  induction l ; try auto.
  simpl.
  destruct (eq_bid a a0) ;
    [| apply list_norepet_cons ;
       [intro
        ; apply CFGC_Utils.in_remove in H0
        ; now inversion H|]]
  ; apply IHl
  ; rewrite list_cons_app in H
  ; eapply list_norepet_append_right
  ; eassumption.
Qed.


Ltac break_list_hyp :=
  match goal with
    | h: List.In _ (_ ++ _) |- _ => repeat (apply in_app_or in h)
  end.

Ltac break_list_goal :=
  try (rewrite Util.list_cons_app) ;
  try (
  match goal with
  | |- context[inputs (_ ++ _)] =>
      repeat (rewrite !ScopeTheory.inputs_app)
  | |- context[outputs (_ ++ _)] =>
      repeat (rewrite !ScopeTheory.outputs_app)
  end ) ;
  try (
  match goal with
  | |- context[List.In _ (_ ++ _)] => repeat (apply in_or_app)
  end).

(* Misc lemmas related to vellvm *)

Lemma find_block_none_singleton :
  forall c term phis comm b b' , b<>b' <->
   find_block
   (convert_typ []
      [{|
         blk_id := b;
         blk_phis := phis;
         blk_code := c;
         blk_term := term;
         blk_comments := comm
         |}]) b' = None.
Proof.
  intros.
  split; intros.
  - apply find_block_not_in_inputs.
    simpl; intuition.
  - simpl in H.
    unfold endo, Endo_id in H.
    destruct (if Eqv.eqv_dec_p b b' then true else false) eqn:E.
    + discriminate.
    + now rewrite <- eqv_dec_p_eq in E ; rewrite <- eqb_bid_neq.
Qed.



(* The following three are copied from vellvm,
   but with heterogeneous types T and T' for use with convert_typ *)


Lemma find_block_map_some' :
  forall {T T'} (f : block T -> block T') G b bk,
    (forall bk, blk_id (f bk) = blk_id bk) ->
    find_block G b = Some bk ->
    find_block (List.map f G) b = Some (f bk).
Proof.
  intros * ID; induction G as [| hd G IH]; intros FIND ; [inv FIND |].
  cbn in *.
  rewrite ID.
  break_match_goal; break_match_hyp; intuition.
  inv FIND; auto.
Qed.

Lemma find_block_map_none' :
  forall {T T'} (f : block T -> block T') G b,
    (forall bk, blk_id (f bk) = blk_id bk) ->
    find_block G b = None ->
    find_block (List.map f G) b = None.
Proof.
  intros * ID; induction G as [| hd G IH]; intros FIND; [reflexivity |].
  cbn in *.
  rewrite ID.
  break_match_goal; break_match_hyp; intuition.
  inv FIND; auto.
Qed.

Lemma find_block_map' :
  forall {T T'} (f : block T -> block T') G b,
    (forall bk, blk_id (f bk) = blk_id bk) ->
    find_block (List.map f G) b = option_map f (find_block G b).
Proof.
  intros.
  destruct (find_block G b) eqn:EQ.
  eapply find_block_map_some' in EQ; eauto.
  eapply find_block_map_none' in EQ; eauto.
Qed.

Lemma find_app :
  forall {A} (l1 l2 : list A) f x,
  List.find f (l1 ++ l2) = Some x ->
  List.find f l1 = Some x \/ List.find f l2 = Some x.
Proof.
  intros.
  induction l1.
  - now right.
  - simpl in *.
    break_match; tauto.
Qed.



Lemma find_block_app_wf :
  forall {T : Set} (x : block_id) [b : block T] (bs1 bs2 : ocfg T),
  wf_ocfg_bid (bs1 ++ bs2)%list ->
  find_block (bs1 ++ bs2) x = Some b ->
  find_block bs1 x = Some b \/ find_block bs2 x = Some b .
Proof.
  intros.
  unfold find_block in H0.
  now apply find_app.
Qed.

Lemma outputs_successors : forall {typ} (cfg : ocfg typ) o,
  List.In o (outputs cfg) ->
  exists bk, List.In bk cfg /\ List.In o (successors bk).
Proof.
  induction cfg; intros.
  - destruct H.
  - cbn in H. rewrite outputs_acc in H.
    apply List.in_app_iff in H. destruct H.
    + exists a. simpl. tauto.
    + apply IHcfg in H.
      destruct H. exists x.
      simpl. tauto.
Qed.

Lemma successors_outputs : forall {typ} (cfg : ocfg typ) o bk,
  List.In bk cfg ->
  List.In o (successors bk) ->
  List.In o (outputs cfg).
Proof.
  induction cfg; intros.
  - destruct H.
  - cbn. rewrite outputs_acc.
    apply List.in_app_iff.
    destruct H.
    + left. now subst a.
    + right. apply IHcfg in H0; assumption.
Qed.

Lemma convert_typ_inputs : forall bk,
  inputs (convert_typ nil bk) = inputs bk.
Proof.
  intros.
  unfold inputs, convert_typ, ConvertTyp_list, tfmap, TFunctor_list'.
  rewrite List.map_map.
  reflexivity.
Qed.

Lemma convert_typ_successors : forall (bk : block typ),
  successors (convert_typ nil bk) = successors bk.
Proof.
  intros.
  apply convert_typ_terminator_outputs.
Qed.

Notation conv := (convert_typ []).

Lemma find_block_some_conv :
  forall g bid bk,
    find_block g bid = Some bk ->
    find_block (conv g) bid = Some (conv bk).
Proof.
  intros.
  unfold conv in *.
  unfold ConvertTyp_list, tfmap, TFunctor_list'.
  apply (find_block_map_some' _ g bid bk) ; [|assumption].
  apply blk_id_convert_typ.
Qed.

Lemma find_block_none_conv :
  forall g bid,
    find_block g bid = None ->
    find_block (conv g) bid = None.
Proof.
  intros.
  unfold conv in *.
  unfold ConvertTyp_list, tfmap, TFunctor_list'.
  apply (find_block_map_none' _ g bid) ; [|assumption].
  apply blk_id_convert_typ.
Qed.


Ltac find_block_conv :=
  match goal with
  | h:context[ find_block _ _ = None ] |- _ =>
      apply find_block_none_conv in h
  | h:context[ find_block _ _ = Some _ ] |- _ =>
      apply find_block_some_conv in h
  end.


Lemma no_reentrance_conv :
  forall g1 g2,
    no_reentrance g1 g2 <-> no_reentrance (conv g1) (conv g2).
Proof.
  intros.
  unfold no_reentrance.
  now rewrite convert_typ_outputs, convert_typ_inputs.
Qed.

Lemma no_duplicate_bid_conv :
  forall g1 g2,
    no_duplicate_bid g1 g2 <-> no_duplicate_bid (conv g1) (conv g2).
Proof.
  intros.
  unfold no_duplicate_bid.
  now rewrite 2 convert_typ_inputs.
Qed.

Lemma independent_flows_conv :
  forall g1 g2,
    independent_flows g1 g2 <-> independent_flows (conv g1) (conv g2).
Proof.
  intros.
  unfold independent_flows.
  rewrite <- 2 no_reentrance_conv.
  now rewrite no_duplicate_bid_conv.
Qed.

Lemma inputs_app : forall {T} (g1 g2 : ocfg T), inputs (g1++g2) = inputs g1 ++ inputs g2.
Proof.
  intros.
  unfold inputs.
  apply Coqlib.list_append_map.
Qed.

Lemma typ_to_dtyp_pair :
  forall (t : typ) (e : exp typ),
    (typ_to_dtyp [] t, convert_typ [] e) = tfmap (typ_to_dtyp []) (t, e).
Proof.
  intros.
  now unfold tfmap, TFunctor_texp, convert_typ, ConvertTyp_exp, tfmap.
Qed.
