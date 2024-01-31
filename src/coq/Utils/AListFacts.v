(* begin hide *)
From ExtLib Require Import
  Core.RelDec
  Data.Map.FMapAList
  Structures.Maps.

From Vellvm Require Import
  Utils.Tactics
  Utils.Util
  Utils.OptionUtil.

From Coq Require Import
  RelationClasses
  List.

Import ListNotations.
(* end hide *)

(** * Alist
 Generic facts about the association list datatype [alist] provided by ExtLib.
 These facts should probably be moved to ExtLib eventually.

 Association lists are currently used in Vellvm to map block identifiers to blocks
 in control flow graphs.
 **)

(** * Propositional variant to [alist_find]. *)
Definition alist_In {K R RD_K V} k m v :=
  @alist_find K R RD_K V k m = Some v.

(** * Freshness predicate: [alist_fresh k m] if [k] is a fresh key in [m] *)
Definition alist_fresh {K R RD_K V} (k : K) (m : alist K V) := 
  @alist_find K R RD_K V k m = None.

(** * Order on [alist]s
    - Inclusion of domains
    - Agreement on the common subdomain
 *)
Definition alist_le {K R RD_K V} (ρ1 ρ2 : alist K V): Prop :=
  forall (id : K) (v : V), @alist_In K R RD_K V id ρ1 v -> alist_In id ρ2 v.

(** * Weaker order on [alist]s
    - Inclusion of domains
 *)
Definition alist_extend {K R RD_K V} (l1 l2 : alist K V) : Prop :=
  forall id v, @alist_In K R RD_K V id l1 v -> exists v', alist_In id l2 v'.

Arguments alist_find {_ _ _ _}.
Arguments alist_add {_ _ _ _}.
Arguments alist_remove {_ _ _ _}. 

Module AlistNotations.
  Notation "m '⊑' m'" := (alist_le m m') (at level 45).
  Notation "m '@' x"  := (alist_find x m) (at level 50).
End AlistNotations.

Section alistFacts.

  Context {K V: Type}.
  Context {RR : @RelDec K (@eq K)}.
  Context {RRC : @RelDec_Correct K (@eq K) RR}.

  Import AlistNotations.

  Section Alist_In.

    (* Properties of [alist_in], the propositional lookup in an association map *)

    (* The last key mapped is in the map *)
    Lemma In_add_eq:
      forall k v (m: alist K V),
        alist_In k (alist_add k v m) v.
    Proof using K RR RRC V.
      intros; unfold alist_add, alist_In; simpl; flatten_goal; [reflexivity | rewrite <- neg_rel_dec_correct in Heq; tauto]. 
    Qed.

    (* A removed key is not contained in the resulting map *)
    Lemma not_In_remove:
      forall (m : alist K V) (k : K) (v: V),
        ~ alist_In k (alist_remove k m) v.
    Proof using K RR RRC V.
      induction m as [| [k1 v1] m IH]; intros.
      - simpl; intros abs; inv abs. 
      - simpl; flatten_goal.
        + unfold alist_In; simpl.
          rewrite Bool.negb_true_iff in Heq; rewrite Heq.
          intros abs; eapply IH; eassumption.
        + rewrite Bool.negb_false_iff, rel_dec_correct in Heq; subst.
          intros abs; eapply IH; eauto. 
    Qed.

    (* Removing a key does not alter other keys *)
    Lemma In_In_remove_ineq:
      forall (m : alist K V) (k : K) (v : V) (k' : K),
        k <> k' ->
        alist_In k m v ->
        alist_In k (alist_remove k' m) v.
    Proof using K RR RRC V.
      induction m as [| [? ?] m IH]; intros ?k ?v ?k' ineq IN; [inversion IN |].
      simpl.
      flatten_goal.
      - unfold alist_In in *; simpl in *.
        rewrite Bool.negb_true_iff, <- neg_rel_dec_correct in Heq.
        flatten_goal; auto.
      - unfold alist_In in *; simpl in *.
        rewrite Bool.negb_false_iff, rel_dec_correct in Heq; subst.
        flatten_hyp IN; [rewrite rel_dec_correct in Heq; subst; tauto | eapply IH; eauto].
    Qed.       

    (* Keys that are present in a map after a remove were present before the remove *)
    Lemma In_remove_In_ineq:
      forall (m : alist K V) (k : K) (v : V) (k' : K),
        alist_In k (alist_remove k' m) v ->
        alist_In k m v.
    Proof using K RR RRC V.
      induction m as [| [? ?] m IH]; intros ?k ?v ?k' IN; [inversion IN |].
      simpl in IN; flatten_hyp IN.
      - unfold alist_In in *; simpl in *.
        flatten_all; auto.
        eapply IH; eauto.
      -rewrite Bool.negb_false_iff, rel_dec_correct in Heq; subst.
       unfold alist_In; simpl. 
       flatten_goal; [rewrite rel_dec_correct in Heq; subst |].
       exfalso; eapply not_In_remove; eauto.
       eapply IH; eauto.
    Qed.       

    (* Keys are present in a map after a remove over a different key iff they were present before the remove *)
    Lemma In_remove_In_ineq_iff:
      forall (m : alist K V) (k : K) (v : V) (k' : K),
        k <> k' ->
        alist_In k (alist_remove k' m) v <->
          alist_In k m v.
    Proof using K RR RRC V.
      intros; split; eauto using In_In_remove_ineq, In_remove_In_ineq.
    Qed.       

    (* Adding a value to a key does not alter other keys *)
    Lemma In_In_add_ineq:
      forall k v k' v' (m: alist K V),
        k <> k' ->
        alist_In k m v ->
        alist_In k (alist_add k' v' m) v.
    Proof using K RR RRC V.
      intros.
      unfold alist_In; simpl; flatten_goal; [rewrite rel_dec_correct in Heq; subst; tauto |].
      apply In_In_remove_ineq; auto.
    Qed.

    (* Keys that are present in a map after an add over a different key were present before the add *)
    Lemma In_add_In_ineq:
      forall k v k' v' (m: alist K V),
        k <> k' ->
        alist_In k (alist_add k' v' m) v ->
        alist_In k m v. 
    Proof using K RR RRC V.
      intros k v k' v' m ineq IN.
      unfold alist_In in IN; simpl in IN; flatten_hyp IN; [rewrite rel_dec_correct in Heq; subst; tauto |].
      eapply In_remove_In_ineq; eauto.
    Qed.

    (* Keys are present in a map after an add over a different key iff they were present before the add *)
    Lemma In_add_ineq_iff: 
      forall m (v v' : V) (k k' : K),
        k <> k' ->
        alist_In k m v <-> alist_In k (alist_add k' v' m) v.
    Proof using K RR RRC V.
      intros; split; eauto using In_In_add_ineq, In_add_In_ineq.
    Qed.

    (* Looking a freshly added key returns the bound value *)
    Lemma alist_In_add_eq : forall m (k:K) (v n:V), alist_In k (alist_add k n m) v -> n = v.
    Proof using K RR RRC V.
      destruct m as [| [k1 v1]]; intros.
      - unfold alist_add in H.
        unfold alist_In in H. simpl in H.
        destruct (k ?[ eq ] k); inversion H; auto.
      - unfold alist_add in H.
        unfold alist_In in H.
        simpl in H.
        destruct (k ?[ eq ] k). inversion H; auto.
        pose proof (@not_In_remove ((k1,v1)::m)).
        unfold alist_In in H0. simpl in H0.
        apply H0 in H.
        contradiction.
    Qed.

    (* Weak relationship between [In] and [alist_In] *)
    Lemma In__alist_In :
      forall {R : K -> K -> Prop} {RD : @RelDec K (@Logic.eq K)} {RDC : RelDec_Correct RD} (k : K) (v : V) l,
        In (k,v) l ->
        exists v', alist_In k l v'.
    Proof using.
      intros R RD RDC k v l IN.
      induction l; inversion IN.
      - exists v. subst. unfold alist_In.
        cbn.
        assert (k ?[ Logic.eq ] k = true) as Hk.
        eapply rel_dec_correct; auto.
        rewrite Hk.
        reflexivity.
      - destruct a. inversion IN.
        + injection H0; intros; subst.
          exists v. unfold alist_In.
          cbn.
          assert (k ?[ Logic.eq ] k = true) as Hk.
          eapply rel_dec_correct; auto.
          rewrite Hk.
          reflexivity.
        + unfold alist_In.
          cbn.
          destruct (k ?[ Logic.eq ] k0) eqn:Hkk0.
          * exists v0; auto.
          * auto.
    Qed.

    (* [alist_in] is decidable if the domains of keys and values are decidables *)
    Lemma alist_In_dec :
      forall {RDV:RelDec (@Logic.eq V)} {RDCV:RelDec_Correct RDV}
        (id : K) (l : alist K V) (v : V),
        {alist_In id l v} + {~(alist_In id l v)}.
    Proof using.
      intros.
      destruct (l @ id) eqn:EQ.
      - destruct (rel_dec v v0) eqn:H.
        rewrite rel_dec_correct in H; subst; auto. 
        rewrite <- neg_rel_dec_correct in H.
        right; intros abs; red in abs; rewrite EQ in abs; inv abs; auto.
      - right; intros abs; red in abs; rewrite EQ in abs; inv abs. 
    Qed.

  End Alist_In.

  Section Alist_Fresh.

    (* Proporties of [alist_fresh], the freshness of key predicate *)

    (* Binding to fresh keys preserves the [alist_In] predicate *)
    Lemma add_fresh_lu : forall m (k1 k2 : K) (v1 v2 : V),
        alist_fresh k2 m ->
        alist_In k1 m v1 ->
        alist_In k1 (alist_add k2 v2 m) v1.
    Proof using K RR RRC V.
      intros; apply In_add_ineq_iff; auto.
      unfold alist_fresh, alist_In in *; intros ->.
      rewrite H in H0; inv H0.
    Qed.

    (* All keys are fresh in the empty map *)
    Lemma alist_fresh_nil : forall k,
        alist_fresh (V := V) k [].
    Proof using.
      intros; reflexivity.
    Qed.

  End Alist_Fresh.

  Section Alist_find.

    (* Properties of [alist_find], the partial lookup function *)

    (* [alist_find] fails iff no value is associated to the key in the map *)
    Lemma alist_find_None:
      forall k (m: alist K V),
        (forall v, ~ In (k,v) m) <-> alist_find k m = None.
    Proof using K RR RRC V.
      induction m as [| [k1 v1] m IH]; [simpl; easy |].
      simpl; split; intros H. 
      - flatten_goal; [rewrite rel_dec_correct in Heq; subst; exfalso | rewrite <- neg_rel_dec_correct in Heq].
        apply (H v1); left; reflexivity.
        apply IH; intros v abs; apply (H v); right; assumption.
      - intros v; flatten_hyp H; [inv H | rewrite <- IH in H].
        intros [EQ | abs]; [inv EQ; rewrite <- neg_rel_dec_correct in Heq; tauto | apply (H v); assumption]. 
    Qed.

    Lemma alist_find_remove_none:
      forall (m : list (K*V)) (k1 k2 : K), 
        k2 <> k1 -> 
        alist_find k1 (alist_remove k2 m) = None -> 
        alist_find k1 m = None.
    Proof using K RR RRC V.
      induction m as [| [? ?] m IH]; intros ?k1 ?k2 ineq HF; simpl in *.
      - reflexivity.
      - destruct (rel_dec_p k1 k).
        + subst. eapply rel_dec_neq_false in ineq; eauto. rewrite ineq in HF. simpl in HF.
          assert (k = k) by reflexivity.
          apply rel_dec_correct in H. rewrite H in HF. inversion HF.
        + destruct (rel_dec_p k2 k); simpl in *.
          apply rel_dec_correct in e. rewrite e in HF. simpl in HF.
          eapply rel_dec_neq_false in n; eauto. rewrite n. eapply IH. apply ineq. assumption.
          eapply rel_dec_neq_false in n0; eauto. rewrite n0 in HF. simpl in HF.
          eapply rel_dec_neq_false in n; eauto. rewrite n in *. eapply IH. apply ineq. assumption.
    Qed.
    
    Lemma alist_find_add_none:
      forall m (k r :K) (v:V), 
        alist_find k (alist_add r v m) = None ->
        alist_find k m = None.
    Proof using K RR RRC V.
      destruct m as [| [k1 v1]]; intros.
      - reflexivity.
      - simpl in *.
        remember (k ?[ eq ] r) as x.
        destruct x.  inversion H.
        remember (r ?[ eq] k1) as y.
        destruct y. simpl in *. symmetry in Heqy. rewrite rel_dec_correct in Heqy. subst.
        rewrite <- Heqx.
        apply (alist_find_remove_none _ k k1); auto.
        rewrite rel_dec_sym in Heqx; eauto.
        apply neg_rel_dec_correct. symmetry in Heqx. assumption.
        simpl in H.
        destruct (k ?[ eq ] k1); auto.
        apply (alist_find_remove_none _ k r); auto.
        rewrite rel_dec_sym in Heqx; eauto.
        apply neg_rel_dec_correct. symmetry in Heqx. assumption.
    Qed.      

    Lemma alist_find_neq : forall m (k r:K) (v:V), k <> r -> alist_find k (alist_add r v m) = alist_find k m.
    Proof using K RR RRC V.
      intros.
      remember (alist_find k (alist_add r v m)) as x.
      destruct x.
      - symmetry in Heqx. apply In_add_In_ineq in Heqx; auto.
      - symmetry in Heqx. symmetry. eapply alist_find_add_none. apply Heqx.
    Qed.

    Lemma alist_find_cons_neq
      (k k0 : K)
      (v0 : V)
      (xs: alist K V)
      :
      (k <> k0) ->
      alist_find k ((k0,v0)::xs) = alist_find k xs.
    Proof using K RR RRC V.
      intros H.
      cbn.
      destruct (rel_dec k k0) eqn:E.
      - exfalso.
        rewrite rel_dec_correct in E.
        congruence.
      - reflexivity.
    Qed.

    Lemma alist_find_cons_eq
      (k k0 : K)
      (v0 : V)
      (xs: alist K V)
      : (k = k0) ->
        alist_find k ((k0,v0)::xs) = Some v0.
    Proof using K RR RRC V.
      intros H.
      cbn.
      destruct (rel_dec k k0) eqn:E.
      - reflexivity.
      - exfalso.
        apply rel_dec_correct in H.
        congruence.
    Qed.

    Lemma alist_find_eq_dec : 
      forall {RDV:RelDec (@Logic.eq V)} {RDCV:RelDec_Correct RDV}
        k (m1 m2 : alist K V),
        {m2 @ k = m1 @ k} + {m2 @ k <> m1 @ k}.
    Proof using.
      intros.
      destruct (m2 @ k) eqn:EQ2, (m1 @ k) eqn:EQ1.
      - destruct (rel_dec v v0) eqn:H.
        rewrite rel_dec_correct in H; subst; auto. 
        rewrite <- neg_rel_dec_correct in H; right; intros abs; apply H; inv abs; auto.
      - right; intros abs; inv abs.
      - right; intros abs; inv abs.
      - left; auto.
    Qed.

    Lemma alist_find_add_eq : 
      forall {K V : Type} {RD:RelDec (@Logic.eq K)} {RDC:RelDec_Correct RD}
        k v (m : alist K V),
        (alist_add k v m) @ k = Some v.
    Proof using.
      intros.
      cbn. rewrite eq_dec_eq; reflexivity.
    Qed.

  End Alist_find.

  Section Alist_extend.

    #[global] Instance alist_extend_Reflexive : Reflexive (alist_extend (V := V)).
    Proof using K RR RRC V.
      unfold Reflexive.
      intros x.
      unfold alist_extend.
      intros id v H.
      exists v.
      auto.
    Qed.

    #[global] Instance alist_extend_Transitive : Transitive (alist_extend (V := V)).
    Proof using K RR RRC V.
      unfold Transitive.
      intros x.
      unfold alist_extend.
      intros y z Hy Hz id v IN.
      apply Hy in IN as (v' & IN).
      apply Hz in IN as (v'' & IN).
      exists v''; auto.
    Qed.

    Lemma alist_extend_add :
      forall l k v,
        alist_extend l (alist_add (V := V) k v l).
    Proof using K RR RRC V.
      intros l k v.
      unfold alist_extend.
      unfold alist_In.
      intros id v0 H.
      destruct (rel_dec_p k id).
      - exists v. subst; apply In_add_eq.
      - exists v0. apply In_In_add_ineq; eauto.
    Qed.

  End Alist_extend.

  Section Alist_le.

    #[global] Instance alist_le_refl : Reflexive (alist_le (V := V)).
    Proof using K RR RRC V.
      repeat intro; auto.
    Qed.

    #[global] Instance alist_le_trans : Transitive (alist_le (V := V)).
    Proof using K RR RRC V.
      repeat intro; auto.
    Qed.

    Lemma alist_le_add :
      forall k v (m : alist K V),
        alist_fresh k m ->
        m ⊑ (alist_add k v m).
    Proof using K RR RRC V.
      repeat intro.
      unfold alist_In, alist_fresh in *.
      destruct (rel_dec_p k id).
      subst; rewrite H in H0; inversion H0.
      apply In_In_add_ineq; auto.
    Qed.

  End Alist_le.

  Section Alist_Lookup.

    Lemma lookup_alist_add_eq :
      forall k v (m : alist K V),
        lookup k (alist_add k v m) = Some v.
    Proof using K RR RRC V.
      intros; cbn.
      rewrite eq_dec_eq; reflexivity.
    Qed.

    Lemma lookup_alist_add_ineq :
      forall k k' v (m : alist K V),
        k <> k' ->
        lookup k (alist_add k' v m) = lookup k m.
    Proof using K RR RRC V.
      cbn; intros.
      rewrite eq_dec_neq; auto.
      rewrite remove_neq_alist; auto.
      typeclasses eauto.
    Qed.

  End Alist_Lookup.

End alistFacts.

Section Alist_refine.
  Context {K V1 V2: Type}.
  Context {RR : @RelDec K (@eq K)}.
  Context {RRC : @RelDec_Correct K (@eq K) RR}.
  Variable (R : V1 -> V2 -> Prop).

  Definition alist_refine (m1 : alist K V1) (m2 : alist K V2):=
    forall k, option_rel2 R (alist_find k m1) (alist_find k m2).

  Lemma alist_refine_find_some_iff :
    forall m1 m2,
      alist_refine m1 m2 ->
      forall k,
        (exists v1, alist_find k m1 = Some v1) <->
          (exists v2, alist_find k m2 = Some v2).
  Proof using.
    intros m1 m2 REF k.
    split; intros [v FIND]; specialize (REF k).
    - red in REF.
      rewrite FIND in REF.
      break_match_hyp; try contradiction.
      exists v0; auto.
    - red in REF.
      rewrite FIND in REF.
      break_match_hyp; try contradiction.
      exists v0; auto.
  Qed.

  Lemma alist_refine_find_some :
    forall m1 m2,
      alist_refine m1 m2 ->
      (forall k v1 v2,
          alist_find k m1 = Some v1 ->
          alist_find k m2 = Some v2 ->
          R v1 v2).
  Proof using.
    intros m1 m2 REF k v1 v2 FIND1 FIND2.
    specialize (REF k).
    rewrite FIND1, FIND2 in REF.
    cbn in REF.
    auto.
  Qed.

  Lemma alist_refine_empty :
    alist_refine [] [].
  Proof using.
    red.
    intros k.
    cbn. auto.
  Qed.

  Lemma alist_refine_cons :
    forall xs ys x y,
      fst x = fst y ->
      R (snd x) (snd y) ->
      alist_refine xs ys ->
      alist_refine (x :: xs) (y :: ys).
  Proof using K R RRC V1 V2.
    induction xs, ys; intros x y H H0 H1.
    - destruct x, y.
      cbn in *.
      red.
      intros k1.
      cbn.
      red. subst.
      break_inner_match_goal; auto.
    - red in H1.
      cbn in H1.
      destruct p.
      specialize (H1 k).
      pose proof @rel_dec_correct K _ _ _ k k as [_ EQ].
      specialize (EQ eq_refl).
      rewrite EQ in H1.
      contradiction.
    - red in H1.
      cbn in H1.
      destruct a.
      specialize (H1 k).
      pose proof @rel_dec_correct K _ _ _ k k as [_ EQ].
      specialize (EQ eq_refl).
      rewrite EQ in H1.
      contradiction.
    - pose proof IHxs ys a p as IH.
      red.
      intros k.
      destruct x, y, a, p.
      cbn in H.
      destruct (rel_dec_p k k1); subst.
      + rewrite alist_find_cons_eq; auto.
        rewrite alist_find_cons_eq; auto.
      + rewrite alist_find_cons_neq; auto.
        setoid_rewrite alist_find_cons_neq at 2; auto.
  Qed.

  Lemma alist_refine_remove :
    forall xs ys rid,
      alist_refine xs ys ->
      alist_refine (FMapAList.alist_remove rid xs) (FMapAList.alist_remove rid ys).
  Proof using K R RR RRC V1 V2.
    induction xs, ys; intros rid REF.
    - cbn; auto.
    - red in REF.
      cbn in REF.
      destruct p.
      specialize (REF k).
      pose proof @rel_dec_correct K _ _ _ k k as [_ EQ].
      specialize (EQ eq_refl).
      rewrite EQ in REF.
      contradiction.
    - red in REF.
      cbn in REF.
      destruct a.
      specialize (REF k).
      pose proof @rel_dec_correct K _ _ _ k k as [_ EQ].
      specialize (EQ eq_refl).
      rewrite EQ in REF.
      contradiction.
    - pose proof IHxs ys rid as IH.
      red.
      intros k.
      destruct a, p.
      pose proof RelDec.rel_dec_p k rid as [EQ | NEQ]; subst.
      + repeat rewrite remove_eq_alist; auto.
      + repeat rewrite remove_neq_alist; auto; typeclasses eauto.
  Qed.

  Lemma alist_refine_add :
    forall xs ys x y,
      fst x = fst y ->
      R (snd x) (snd y) ->
      alist_refine xs ys ->
      alist_refine (FMapAList.alist_add (fst x) (snd x) xs) (FMapAList.alist_add (fst y) (snd y) ys).
  Proof using K R RR RRC V1 V2.
    intros xs ys x y H H0 H1.
    apply alist_refine_cons; cbn; auto.
    rewrite H.
    apply alist_refine_remove; auto.
  Qed.

  Lemma alist_refine_nil_cons_inv :
    forall p l,
      ~ (alist_refine [] (p::l)).
  Proof using K R RR RRC V1 V2.
    intros p l REF.
    red in REF.
    cbn in REF.
    destruct p.
    specialize (REF k).
    pose proof @rel_dec_correct K _ _ _ k k as [_ EQ].
    forward EQ; auto.
    rewrite EQ in REF.
    auto.
  Qed.

  Lemma alist_refine_cons_nil_inv :
    forall p l,
      ~ (alist_refine (p::l) []).
  Proof using K R RR RRC V1 V2.
    intros p l REF.
    red in REF.
    cbn in REF.
    destruct p.
    specialize (REF k).
    pose proof @rel_dec_correct K _ _ _ k k as [_ EQ].
    forward EQ; auto.
    rewrite EQ in REF.
    auto.
  Qed.
End Alist_refine.
