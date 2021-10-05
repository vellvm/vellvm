From Coq Require Import
     Lia
     List
     String
     ZArith.

From ExtLib Require Import FMapAList.

From ITree Require Import
     ITree
     ITreeFacts.

From Vellvm Require Import
     Handlers.Handlers
     Semantics
     Syntax
     Syntax.ScopeTheory
     Utils.AListFacts
     Utils.Tactics.

Open Scope nat_scope.

(* Misc lemmas related to the standard library *)

Lemma firstn_map : forall {A B} (l : list A) (f : A -> B) i,
  List.firstn i (List.map f l) = List.map f (List.firstn i l).
Proof.
  induction l ; intros ; simpl.
  - rewrite 2 List.firstn_nil.
    reflexivity.
  - destruct i.
    + reflexivity.
    + simpl. rewrite <- IHl.
      reflexivity.
Qed.

Lemma firstn_seq : forall n n' i, List.firstn n (List.seq i (n + n')) = List.seq i n.
Proof.
  induction n ; intros ; simpl.
  - reflexivity.
  - f_equal.
    rewrite IHn.
    reflexivity.
Qed.

Lemma skipn_map : forall {A B} (l : list A) (f : A -> B) i,
  List.skipn i (List.map f l) = List.map f (List.skipn i l).
Proof.
  induction l ; intros ; simpl.
  - rewrite 2 List.skipn_nil.
    reflexivity.
  - destruct i.
    + reflexivity.
    + simpl. rewrite <- IHl.
      reflexivity.
Qed.

Lemma skipn_seq : forall n n' i, List.skipn n (List.seq i (n + n')) = List.seq (i + n) n'.
Proof.
  induction n ; intros ; simpl.
  - auto.
  - destruct n'.
    + simpl.
      apply skipn_all2.
      rewrite seq_length.
      lia.
    + simpl.
      rewrite IHn. simpl.
      f_equal; auto.
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


Lemma combine_app : forall {A} (l1 l2 l1' l2' : list A) ,
  List.length l1 = List.length l1' ->
  List.length l2 = List.length l2' ->
  combine (l1++l2) (l1'++l2') = (combine l1 l1')++(combine l2 l2').
Proof.
  induction l1 ; intros.
  - simpl in H ; symmetry in H ; apply length_zero_iff_nil in H ; subst.
    auto.
  - destruct l1' ; try (discriminate).
    simpl in H ; inv H.
    simpl. rewrite IHl1 ; auto.
Qed.


Lemma combine_cons : forall {A} (a a' : A) (l l' : list A),
  (* List.length l = List.length l' -> *)
  combine (a::l) (a'::l') = (combine (a::nil) (a'::nil) )++(combine l l').
Proof.
  induction l eqn:E ; intros.
  - auto.
  - destruct l' ; auto.
Qed.


(* Misc lemmas related to extlib *)

Lemma key_in_alist_find : forall {A B : Type} {RD : RelDec.RelDec eq},
  RelDec.RelDec_Correct RD ->
  forall (l : alist A B) k,
  List.In k (fst (split l)) ->
  exists v, alist_find k l = Some v.
Proof.
  intros.
  induction l; [ destruct H0 |].
  cbn in *. repeat break_let. subst.
  cbn in *.
  destruct H0.
  - subst.
    exists b.
    break_match; try easy.
    now apply RelDec.neg_rel_dec_correct in Heqb0.
  - apply IHl in H0 as [].
    break_match.
    + now exists b.
    + now exists x.
Qed.

(* Misc lemmas related to vellvm *)

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
