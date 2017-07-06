(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)


Require Import Arith Equalities EqualitiesFacts Orders List.
Import ListNotations.

Require Omega.

Set Implicit Arguments.

Definition functional (A B:Type) (R:A -> B -> Prop) : Prop :=
  forall a b1 b2, R a b1 -> R a b2 -> b1 = b2.

Definition injective (A B:Type) (R:A -> B -> Prop) : Prop :=
  forall a1 a2 b, R a1 b -> R a2 b -> a1 = a2.

(* additional properties of lists *)

Section LIST.

  Variable A : Type.

  Fixpoint Nth (a:A) (l:list A) (n:nat) : Prop :=
    match n, l with
      | _, nil => False
      | O, a' :: l' => a = a'
      | S n', _ :: l' => Nth a l' n'
    end.

  Lemma Nth_length : forall l a n,
    Nth a l n ->
    n < length l.
  Proof.
    induction l. destruct n; simpl; intuition.  
    destruct n; simpl; intuition.
    apply Lt.lt_n_S. eapply IHl; eauto.
  Qed.

  Lemma length_Nth : forall l n,
    n < length l ->
    exists a, Nth a l n.
  Proof. 
    induction l. inversion 1.
    intros. destruct n. simpl; eauto.
    simpl. apply IHl. auto with arith.
  Qed.

  Lemma Nth_eq : forall l a1 a2 n,
    Nth a1 l n -> Nth a2 l n -> a1 = a2.
  Proof.
    intros. generalize dependent n. induction l; intros.
    destruct n; contradiction.
    destruct n; simpl in *. intros; subst a; auto.
    eapply IHl; eauto.
  Qed.

  Lemma Nth_In : forall l a n,
    Nth a l n -> In a l.
  Proof.
    induction l; destruct n; intuition.
    left; auto.
    right. eapply IHl; eauto.
  Qed.

  Lemma In_Nth : forall l a,
    In a l -> exists n, Nth a l n.
  Proof.
    induction l; inversion 1; subst.
    exists 0. reflexivity.
    apply IHl in H0 as [n ?].
    exists (S n). auto.
  Qed.

  Lemma nth_error_iff_Nth: forall (l : list A) (offset: nat) (a : A),
      nth_error l offset = Some a <-> Nth a l offset.
  Proof.
    induction l as [| a l].
    - intros [| offset] a; split; simpl; intros H; try inversion H.
    - induction offset; intros a'.
      { split; simpl; intros H; inversion H; auto. }
      { simpl. rewrite IHl; reflexivity. }
  Qed.
  
End LIST.

Section NODUP.

  Variables (A B: Type).

  Lemma NoDup_assoc_func : forall (k:A) (v1 v2:B) l,
    NoDup (map (@fst _ _) l) ->
    In (k, v1) l ->
    In (k, v2) l ->
    v1 = v2.
  Proof.
    intros.
    induction l. inversion H0.
    destruct H0, H1. subst a. injection H1; auto.
    inversion H; subst. apply in_map with (f:=@fst _ _) in H1. contradiction. 
    inversion H; subst. apply in_map with (f:=@fst _ _) in H0. contradiction.
    apply IHl; auto. simpl in H. inversion H; auto.
  Qed.

  Lemma NoDup_nth_inj : forall (k:A) (v1 v2:B) (n1 n2:nat) (l:list (A*B)),
    NoDup (map (@fst _ _) l) ->
    Nth (k, v1) l n1 ->
    Nth (k, v2) l n2 ->
    n1 = n2.
  Proof.
    intros. generalize dependent n1. generalize dependent n2.
    induction l; simpl; intros. destruct n1; contradiction.
    destruct n1, n2. reflexivity.
    inversion H; subst. contradict H4.
    simpl. apply in_map_iff. exists (k, v2). eauto using Nth_In.
    inversion H; subst. contradict H4.
    simpl. apply in_map_iff. exists (k, v1). eauto using Nth_In.
    f_equal. inversion H; apply IHl; eauto.
  Qed.

  Lemma NoDup_app : forall (l l':list A),
    NoDup (l ++ l') -> NoDup l /\ NoDup l'.
  Proof.
    induction l; simpl; intros. auto using NoDup_nil. 
    inversion H; subst. 
    apply IHl in H3. destruct H3. split.
      eapply NoDup_cons. contradict H2. apply in_or_app. 
      auto. auto. auto.
  Qed.

  Lemma NoDup_split : forall (a:A) (l1 l2:list A),
    NoDup (l1 ++ l2) ->
    In a l1 -> ~ In a l2.
  Proof.
    intros. 
    apply in_split in H0 as [l11 [l12 Heql]].
    rewrite Heql in H. rewrite <- app_assoc, <- app_comm_cons in H. 
    apply NoDup_remove_2 in H. contradict H.
    rewrite app_assoc. apply in_or_app. auto.
  Qed.

End NODUP.

Section FOLDS.

  Variables A B : Type.

  Lemma NoDup_flat_map : forall (a1 a2:A) (b:B) (f:A -> list B) l,
    NoDup (flat_map f l) ->
    In a1 l -> In a2 l ->
    In b (f a1) ->
    In b (f a2) ->
    a1 = a2.
  Proof.
    intros.
    induction l. inversion H0.
    destruct H0, H1; simpl in H; subst. auto.
    exfalso. eapply NoDup_split; eauto.
    apply (in_flat_map f l b). eexists; eauto.
    exfalso. eapply NoDup_split; eauto.
    apply (in_flat_map f l b). eexists; eauto.
    eapply NoDup_app in H as [? ?].
    apply IHl; auto. 
  Qed.

  Lemma NoDup_flat_map__NoDup : forall (A B:Type) (a:A) (f:A -> list B) l,
    NoDup (flat_map f l) ->
    In a l ->
    NoDup (f a).
  Proof.
    intros. generalize dependent a. induction l. inversion 1.
    intros. simpl in H. apply NoDup_app in H as [? ?].
    inversion H0; subst; auto.
  Qed.

  Lemma fold_left_1 : forall  (P:A -> Prop) (f:A -> B -> A) (bs : list B)
    (Hpres : forall a b, In b bs -> P a -> P (f a b)),
    forall a a', 
      a' = fold_left f bs a -> P a -> P a'.
  Proof.
    intros. subst a'. generalize dependent a.
    induction bs; simpl; intros. assumption. 
    apply IHbs. intros. apply Hpres. right; auto. assumption.
    apply Hpres. left; auto. assumption.
  Qed.

  Lemma fold_left_2 : forall (P:A -> B -> Prop)
    (f:A -> B -> A)
    (Hpres : forall a b b', P a b -> P (f a b') b)
    (Hintr : forall a b, P (f a b) b),
    forall a a' bs b, 
    a' = fold_left f bs a ->
    In b bs -> P a' b.
  Proof.
    intros. subst a'. generalize dependent a.
    induction bs as [|b']. contradiction.
    simpl; intros. destruct H0. subst b'.
    set (a' := fold_left _ _ _). pattern a'.
    eapply fold_left_1; eauto. reflexivity. 
    apply IHbs. assumption.
  Qed.

End FOLDS.

Section ASSOC.

  Variable A B : Type.
  Variable eq_dec : forall (a b:A), {a = b} + {a <> b}.

  Fixpoint assoc (a:A) (l:list (A*B)) : option B :=
    match l with
      | [] => None
      | (a', b)::l' => if eq_dec a a'
                       then Some b
                       else assoc a l'
    end.

  Lemma assoc_in : forall l a b,
    assoc a l = Some b ->
    In (a, b) l.
  Proof.
    induction l. inversion 1. simpl. destruct a as [a' b'].
    intros. destruct (eq_dec a a'). injection H. intros; subst; auto.
    right. apply IHl; auto.
  Qed.

  Lemma in_assoc_some : forall l a b,
    In (a, b) l -> exists b', assoc a l = Some b'.
  Proof.
    induction l. inversion 1.
    intros. destruct a as [a b']. simpl.
    destruct (eq_dec a0 a). eauto. 
    destruct H. contradict n; inversion H; auto.
    eapply IHl; eauto.
  Qed.

End ASSOC.

Require Import FSets FMaps.

Module FMapProps (E:UsualDecidableType) (M:FMapInterface.WSfun E).

  Local Notation K := M.key.

  Section FMapProps.
  
  Variable V : Type.

  Definition find_default (m:M.t V) (k:K) (d:V) : V :=
    match M.find k m with
      | None => d
      | Some m => m
    end.

  Lemma find_default_neq : forall  m n1 n2 l d,
    n1 <> n2 ->
    find_default (M.add n1 l m) n2 d = find_default m n2 d.
  Proof.
    intros. unfold find_default.
    destruct (M.find n2 (M.add _ _ _)) eqn:Heq1, (M.find n2 m) eqn:Heq2.
    apply M.find_2 in Heq1. apply M.add_3 in Heq1; auto. apply M.find_1 in Heq1.
      rewrite Heq2 in Heq1. injection Heq1. auto. 
    apply M.find_2 in Heq1. apply M.add_3 in Heq1; auto. apply M.find_1 in Heq1.
      rewrite Heq2 in Heq1. discriminate Heq1.
    apply M.find_2 in Heq2. eapply M.add_2 in Heq2; eauto. apply M.find_1 in Heq2.
      rewrite Heq2 in Heq1. discriminate Heq1.
    trivial.
  Qed.

  Lemma find_default_eq : forall m n1 n2 l d,
    n1 = n2 ->
    find_default (M.add n1 l m) n2 d = l.
  Proof.
    unfold find_default; intros.
    erewrite M.find_1. reflexivity. apply M.add_1; auto.
  Qed.

  End FMapProps.

End FMapProps.

Module Type LATTICE.
  Include EqLe'.

  Declare Instance eq_equiv : Equivalence eq.
  Declare Instance le_preorder : PreOrder le.
  Declare Instance le_poset : PartialOrder eq le.
  
  Parameter eq_dec : forall x y, {x == y} + {x ~= y}.

  Parameter bot : t.
  Axiom le_bot : forall x, bot <= x.

  Parameter top : t.
  Axiom le_top : forall x, x <= top.

  Parameter join : t -> t -> t.
  Axiom le_join_l : forall x y, x <= join x y.
  Axiom le_join_r : forall x y, y <= join x y.
End LATTICE.

Module BoundedSet(Import S:FSetInterface.WS) <: LATTICE.

  Module Import SFacts := FSetFacts.WFacts S.

  Definition t : Type := option S.t.

  Definition eq (t1 t2: t) : Prop :=
    match t1, t2 with
      | Some s1, Some s2 => s1 [=] s2
      | None, None => True
      | _, _ => False
    end.

  Definition le (t1 t2: t) : Prop :=
    match t1, t2 with
      | Some s1, Some s2 => s2 [<=] s1
      | None, Some _ | None, None => True
      | Some _, None => False
    end.

  Include EqLeNotation.

  Instance eq_equiv : Equivalence eq.
  Proof.
    constructor.
    red. destruct x; simpl; intuition.
    red. destruct x, y; simpl; intros; intuition.
    red. destruct x, y, z; simpl; intros; intuition.
    transitivity t1; auto.
  Qed.

  Instance le_preorder : PreOrder le.
  Proof.
    constructor.
    red. destruct x; simpl; intuition. 
    red. destruct x, y, z; simpl; intros; intuition.
    transitivity t1; auto.
  Qed.

  Instance le_poset : PartialOrder eq le.
  Proof.
    constructor.
    intro. repeat red. split.
    destruct x, x0; simpl in *; intuition. 
    unfold Subset. intros. rewrite H; auto.
    red. destruct x, x0; simpl in *; intuition.
    unfold Subset. intros. rewrite <- H. auto.

    destruct x, x0; simpl; 
      intros H; repeat red in H; simpl in H; 
      intuition.
    repeat red in H1. repeat red in H0.
    red; intuition.
  Qed.

  Definition eq_dec : forall x y, {x == y} + {x ~= y}.
    refine (fun t1 t2 => match t1, t2 with
                           | Some s1, Some s2 => _
                           | None, None => left _
                           | _, _ => right _
                         end); auto using S.eq_dec.
  Defined.

  Definition bot : t := None.

  Lemma le_bot : forall x, bot <= x.
  Proof.
    simpl; destruct x; trivial.
  Qed.

  Definition top : t := Some S.empty.
  Lemma le_top : forall x, x <= top.
  Proof. 
    simpl. destruct x; trivial. red. intros.
    exfalso. eapply empty_iff; eauto. 
  Qed.

  Definition join (t1 t2: t) : t :=
    match t1, t2 with
      | Some s1, Some s2 => Some (S.inter s1 s2) 
      | None, Some s | Some s, None => Some s
      | None, None => None
    end.

  Lemma le_join_l : forall x y, x <= join x y.
  Proof.
    intros. destruct x, y; repeat red; auto.
    intros. eapply inter_1; eauto.
  Qed.

  Lemma le_join_r : forall x y, y <= join x y.
  Proof.
    intros. destruct x, y; repeat red; auto.
    intros. eapply inter_2; eauto.
  Qed.

  Definition union (t1 t2: t) : t :=
    match t1, t2 with
      | Some s1, Some s2 => Some (S.union s1 s2) 
      | None, Some s | Some s, None => None
      | None, None => None
    end.
    
  Definition singleton (e:S.elt) : t := Some (S.singleton e).

  Definition In (e:S.elt) (t:t) : Prop :=
    match t with
      | Some s => S.In e s
      | None => True
    end.

End BoundedSet.

