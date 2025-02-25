From Coq Require Import
  FSets.FMapAVL
  FSets.FSetAVL
  FSetProperties
  FMapFacts
  ZArith
  Lia
  List.

From ExtLib Require Import
  Structures.Monads
  Structures.Functor
  Structures.Applicative
  Structures.Traversable
  Structures.Foldable
  Programming.Eqv.

From Mem Require Import Tactics.

Import ListNotations.
Import MonadNotation.
Import FunctorNotation.
Import ApplicativeNotation.
Open Scope monad.

Module IM := FMapAVL.Make(Coq.Structures.OrderedTypeEx.Z_as_OT).
Module IS := FSetAVL.Make(Coq.Structures.OrderedTypeEx.Z_as_OT).
Module Import ISP := FSetProperties.WProperties_fun(Coq.Structures.OrderedTypeEx.Z_as_OT)(IS).
Module Import IP := FMapFacts.WProperties_fun(Coq.Structures.OrderedTypeEx.Z_as_OT)(IM).

Lemma find_add_eq :
  forall {elt} (m : @IM.t elt) (k : IM.key) (v : elt),
    IM.find k (IM.add k v m) = Some v.
Proof.
  intros elt m k v.
  apply IM.find_1.
  apply IM.add_1; auto.
Qed.

Lemma find_add_neq :
  forall {elt} (m : @IM.t elt) (k1 k2 : IM.key) (v x : elt),
    k1 <> k2 ->
    IM.find k1 m = Some x ->
    IM.find k1 (IM.add k2 v m) = Some x.
Proof.
  intros elt m k1 k2 v x NEQ FIND.
  apply IM.find_1.
  apply IM.add_2; auto.
  apply IM.find_2; auto.
Qed.

Lemma IS_mem_add_eq :
  forall (m : IS.t) (k : IS.elt),
    IS.mem k (IS.add k m) = true.
Proof.
  intros m k.
  apply IS.mem_1.
  apply IS.add_1; auto.
Qed.

Lemma IS_mem_add_neq :
  forall (m : IS.t) (k1 k2 : IS.elt),
    k1 <> k2 ->
    IS.mem k1 m = true ->
    IS.mem k1 (IS.add k2 m) = true.
Proof.
  intros m k1 k2 NEQ IN.
  apply IS.mem_1.
  apply IS.add_2; auto.
  apply IS.mem_2; auto.
Qed.

#[global] Coercion is_true : bool >-> Sortclass.

Section Map_Operations.

  (** ** Finite maps
      We use finite maps in several place of the memory model. We rely on the AVL implementation from the standard library.
      We redefine locally the operations we use and their axiomatisation as the interface exposed by the standard library
      tends to leak out the [Raw] underlying implementation, and feels overall tedious to use.
   *)

  (* Polymorphic type of maps indexed by [Z] *)
  Definition IntMap := IM.t.

  Definition add {a} k (v:a) := IM.add k v.
  Definition delete {a} k (m:IntMap a) := IM.remove k m.
  Definition member {a} k (m:IntMap a) := IM.mem k m.
  Definition lookup {a} k (m:IntMap a) := IM.find k m.
  Definition empty {a} := @IM.empty a.

  Definition add_with {a b} k (v:a) (def : a -> b) (merge : a -> b -> b) (m:IntMap b) :=
    match IM.find k m with
    | None => add k (def v) m
    | Some elt =>
        add k (merge v elt) m
    end.

  (* We use two notions of equivalence of maps depending on the type of objects stored.
       When we can get away with Leibniz's equality over the return type, we simply use
       [Equal] that implements extensional equality (and equality of domains).
       When the domain of value itself has a non-trivial notion of equivalence, we use [Equiv]
       which relax functional equivalence up-to this relation.
   *)
  Definition Equal {a} : IntMap a -> IntMap a -> Prop :=
    fun m m' => forall k, lookup k m = lookup k m'.
  Definition Equiv {a} (R : a -> a -> Prop) : IntMap a -> IntMap a -> Prop :=
    fun m m' =>
      (forall k, member k m <-> member k m') /\
      (forall k e e', lookup k m = Some e -> lookup k m' = Some e' -> R e e').

  (* Extends the map with a list of pairs key/value.
     Note: additions start from the end of the list, so in case of duplicate
     keys, the binding in the front will shadow though in the back.
   *)
  Fixpoint add_all {a} ks (m:IntMap a) :=
    match ks with
    | [] => m
    | (k,v) :: tl => add k v (add_all tl m)
    end.

  (* Extends the map with the bindings {(i,v_1) .. (i+n-1, v_n)} for [vs ::= v_1..v_n] *)
  Fixpoint add_all_index {a} vs (i:Z) (m:IntMap a) :=
    match vs with
    | [] => m
    | v :: tl => add i v (add_all_index tl (i+1) m)
    end.

  (* Takes the join of two maps, favoring the first one over the intersection of their domains *)
  Definition union {a} (m1 : IntMap a) (m2 : IntMap a)
    := IM.map2 (fun mx my =>
                  match mx with | Some x => Some x | None => my end) m1 m2.

  (* TODO : Move the three following functions *)
  Fixpoint max_default (l:list Z) (x:Z) :=
    match l with
    | [] => x
    | h :: tl =>
      max_default tl (if h >? x then h else x)%Z
    end.

  Definition maximumBy {A} (leq : A -> A -> bool) (def : A) (l : list A) : A :=
    fold_left (fun a b => if leq a b then b else a) l def.

  Definition maximumBy_Z_le_def :
    forall def l e,
      (e <=? def ->
       e <=? maximumBy Z.leb def l)%Z.
  Proof using.
    intros def l.
    revert def.
    induction l; intros def e LE.
    - cbn; auto.
    - cbn. destruct (def <=? a)%Z eqn:Hdef.
      + apply IHl.
        eapply Zle_bool_trans; eauto.
      + apply IHl; auto.
  Qed.

  Definition maximumBy_Z_def :
    forall def l,
      (def <=? maximumBy Z.leb def l)%Z.
  Proof using.
    intros def l.
    apply maximumBy_Z_le_def; eauto.
    apply Z.leb_refl.
  Qed.

  Definition maximumBy_Z_correct :
    forall def (l : list Z),
    forall a, In a l -> Z.leb a (maximumBy Z.leb def l).
  Proof using.
    intros def l.
    revert def.
    induction l as [|x xs];
      intros def a IN;
      inversion IN.
    - subst; cbn.
      apply maximumBy_Z_le_def.
      destruct (def <=? a)%Z eqn:LE.
      + apply Z.leb_refl.
      + rewrite Z.leb_gt in LE.
        apply Z.leb_le.
        lia.
    - subst; cbn; apply IHxs; auto.
  Qed.

  Definition is_some {A} (o : option A) :=
    match o with
    | Some x => true
    | None => false
    end.

  Fixpoint IM_raw_greatest_key {A} (m : IM.Raw.tree A) : option Z
    := match m with
       | IM.Raw.Leaf _ => None
       | IM.Raw.Node l k _ (@IM.Raw.Leaf _) _ =>
           Some k
       | IM.Raw.Node l k _ r _ =>
           IM_raw_greatest_key r
       end.

  Definition IM_greatest_key {A} (m : IM.t A) : option Z
    := IM_raw_greatest_key (IM.this m).

  Definition next_key {A} (m : IntMap A) : Z
    := match IM_greatest_key m with
       | Some k =>
           1 + Z.abs k
       | None => 1
       end.

  Definition next_key_old {A} (m : IntMap A) : Z
    := let keys := map fst (IM.elements m) in
       1 + maximumBy Z.leb (-1)%Z keys.

  Lemma next_key_old_gt_0 :
    forall {A} (m : IntMap A),
      (next_key_old m >= 0)%Z.
  Proof using.
    intros A m.
    unfold next_key_old.
    pose proof maximumBy_Z_def (-1) (map fst (IM.elements (elt:=A) m)).
    apply Zle_is_le_bool in H.
    lia.
  Qed.

  Lemma IM_greatest_key_none' :
    forall {A} (m : IM.t A), IM.Empty m -> IM_greatest_key m = None.
  Proof.
    intros A m H.
    induction m; cbn in *.
    induction this; cbn in *; auto.
    - exfalso; eapply H.
      cbn.
      constructor; reflexivity.
  Qed.

  Lemma IM_greatest_key_none'' :
    forall {A} (m : IM.t A), IM_greatest_key m = None -> IM.Empty m.
  Proof.
    intros A m H.
    induction m; cbn in *.
    induction this; cbn in *; auto.
    - intros k e CONTRA.
      inversion CONTRA.
    - exfalso.
      destruct (IM_raw_greatest_key this2) eqn:THIS2.
      + break_match_hyp_inv.
      + break_match_hyp_inv.
        inv is_bst.
        specialize (IHthis2 H5 eq_refl).
        eapply IHthis2.
        constructor; reflexivity.
  Qed.

  Lemma IM_greatest_key_none :
    forall {A} (m : IM.t A), IM_greatest_key m = None <-> IM.Empty m.
  Proof.
    intros A m.
    split; intros H.
    + apply IM_greatest_key_none''; auto.
    + apply IM_greatest_key_none'; auto.
  Qed.

  Lemma IM_greatest_key_In :
    forall {A} (m : IM.t A) gk,
      IM_greatest_key m = Some gk -> IM.In gk m.
  Proof.
    intros A m.
    intros gk H.
    apply F.in_find_iff.
    revert gk H.
    destruct m; cbn in *.
    induction this; intros gk GK.
    - cbn in *. inv GK.
    - rename k into current_key.
      cbn.
      (* gk is the greatest key. It should be larger than current_key *)
      cbn in GK.
      pose proof is_bst as is_bst2.
      inv is_bst.
      destruct (IM_raw_greatest_key this2) eqn:THIS2;
        destruct this2; inv GK.
      + (* At a leaf eq *)
        break_match; cbn in *;
          solve
            [ red in l; lia
            | discriminate
            ].
      + (* Not at a leaf... *)
        pose proof H5.
        eapply IHthis2 in H5; eauto.
        eapply IM.Raw.Proofs.find_in_iff in H5; eauto.

        red in H7.
        apply H7 in H5.

        break_match; cbn in *;
          try solve
            [ red in l; lia
            | discriminate
            ].

        apply IHthis2; auto.
      + break_match; cbn in *;
          solve
            [ red in l; lia
            | discriminate
            ].
  Qed.

  Lemma IM_greatest_key_In' :
    forall {A} (m : IM.t A) k,
      IM.In k m ->
      exists gk, IM_greatest_key m = Some gk.
  Proof.
    intros A m k IN.
    destruct (IM_greatest_key m) eqn:GK.
    exists z; auto.

    apply F.in_find_iff in IN.
    destruct (IM.find (elt:=A) k m) eqn:FIND; try contradiction.
    apply F.find_mapsto_iff in FIND.
    apply IM_greatest_key_none in FIND; try contradiction; auto.
  Qed.

  Lemma IM_greatest_key_lt :
    forall {A} (m : IM.t A) gk,
      IM_greatest_key m = Some gk -> IM.Raw.lt_tree (1 + gk) (IM.this m).
  Proof.
    intros A m.
    destruct m; cbn in *.
    induction this; intros gk GK.
    - cbn in *. inv GK.
    - rename k into current_key.
      cbn.
      (* gk is the greatest key. It should be larger than current_key *)
      cbn in GK.
      pose proof is_bst as is_bst2.
      inv is_bst.
      destruct (IM_raw_greatest_key this2) eqn:THIS2;
        destruct this2; inv GK.
      + (* At a leaf eq *)
        break_match; cbn in *;
          solve
            [ red in l; lia
            | discriminate
            ].
      + (* Not at a leaf... *)
        pose proof H5.
        eapply IHthis2 in H5; eauto.
        red.
        intros y H0.
        inv H0.
        * (* Root *)
          red in H5.
          specialize (H5 k).
          forward H5.
          constructor; auto.
          specialize (H7 k).
          forward H7.
          constructor; auto.
          cbn in H7.
          lia.
        * (* Left *)
          red in H6.
          specialize (H6 y H2).
          red in H5.
          specialize (H5 k).
          forward H5.
          constructor; auto.
          specialize (H7 k).
          forward H7.
          constructor; auto.
          cbn in H7.
          lia.
        * (* Right *)
          red in H5.
          specialize (H5 y H2).
          auto.
      + red.
        intros y H.
        assert (gk < 1 + gk)%Z by lia.
        inv H; auto.
        * apply H6 in H2.
          cbn in *; lia.
        * inv H2.
  Qed.


  Lemma IM_raw_greatest_key_lr :
    forall {elt} m k (e : elt) l t r kl kr,
      IM.this m = (IM.Raw.Node l k e r t) ->
      IM_raw_greatest_key l = Some kl ->
      IM_raw_greatest_key r = Some kr ->
      (kl < kr)%Z.
  Proof.
    intros elt m k e l t r kl kr NODE GL GR.
    destruct m.
    cbn in *.
    inv is_bst.
    inv H.
    inv H3.

    unfold IM.Raw.gt_tree in *.
    unfold IM.Raw.lt_tree in *.

    assert (IM_greatest_key (@IM.Bst elt l H) = Some kl) as GL' by (cbn; auto).
    assert (IM_greatest_key (@IM.Bst elt r H0) = Some kr) as GR' by (cbn; auto).

    apply IM_greatest_key_In in GL', GR'.
    unfold IM.In in *.
    apply IM.Raw.Proofs.In_alt in GL', GR'.
    apply H2 in GR'.
    apply H1 in GL'.

    lia.
  Qed.

  Lemma next_key_correct :
    forall {A} (m : IM.t A) (a : Z),
      IM.In a m ->
      (a < next_key m)%Z.
  Proof.
    intros A m a IN.
    pose proof IN as GK.
    unfold next_key.
    eapply IM_greatest_key_In' in GK.
    destruct GK as (gk & GK).
    rewrite GK.
    apply IM_greatest_key_lt in GK.
    red in GK.
    specialize (GK a).
    destruct m; cbn in IN.
    unfold IM.In in IN.
    apply IM.Raw.Proofs.In_alt in IN.
    apply GK in IN.
    auto.
    lia.
  Qed.

  Lemma next_key_gt_0 :
    forall {A} (m : IntMap A),
      (next_key m > 0)%Z.
  Proof using.
    intros A m.
    unfold next_key.
    break_match; try lia.
  Qed.

  Lemma MapsTo_inj : forall {a} k v v' (m : IntMap a),
    IM.MapsTo k v m ->
    IM.MapsTo k v' m ->
    v = v'.
  Proof using.
    intros.
    apply IM.find_1 in H; apply IM.find_1 in H0.
    rewrite H0 in H; inversion H.
    reflexivity.
  Qed.

    (** ** [member]/[lookup] interaction
        Keys are in the domain if and only if they lead to values when looked-up
   *)
  Lemma member_lookup {a} : forall k (m : IntMap a),
      member k m -> exists v, lookup k m = Some v.
  Proof using.
    unfold member,lookup in *.
    intros * IN.
    apply IM.Raw.Proofs.mem_2, IM.Raw.Proofs.In_MapsTo in IN.
    destruct IN as [v IN].
    exists v.
    apply IM.Raw.Proofs.find_1; eauto.
    apply IM.is_bst.
  Qed.

  Lemma lookup_member {a} : forall k v(m : IntMap a),
      lookup k m = Some v -> member k m .
  Proof using.
    unfold member,lookup in *.
    intros * IN.
    apply IM.Raw.Proofs.mem_1; [apply IM.is_bst |].
    apply IM.Raw.Proofs.find_2 in IN; eauto.
    eapply IM.Raw.Proofs.MapsTo_In; eauto.
  Qed.

  (** ** [add]/[lookup] interaction
        Lookups look up the lastly added value
   *)
  Lemma lookup_add_eq : forall {a} k x (m : IntMap a),
      lookup k (add k x m) = Some x.
  Proof using.
    intros.
    unfold lookup, add.
    apply IM.find_1, IM.add_1; auto.
  Qed.

  Lemma lookup_add_ineq : forall {a} k k' x (m : IntMap a),
      k <> k' ->
      lookup k (add k' x m) = lookup k m.
  Proof using.
    intros.
    unfold lookup, add.
    match goal with
      |- ?x = ?y => destruct x eqn:EQx,y eqn:EQy;
                    try apply IM.find_2,IM.add_3 in EQx;
                    try apply IM.find_2 in EQy
    end; auto.
    eapply MapsTo_inj in EQx; eauto; subst; eauto.
    apply IM.find_1 in EQx; rewrite EQx in EQy; inversion EQy.
    cbn in *.
    apply IM.Raw.Proofs.not_find_iff in EQx; [| apply IM.Raw.Proofs.add_bst, IM.is_bst].
    exfalso; apply EQx, IM.Raw.Proofs.add_in.
    right.
    unfold IM.MapsTo in *.
    eapply IM.Raw.Proofs.MapsTo_In,EQy.
  Qed.

  (* TODO: move this to list utilities? *)
  Definition list_values_injective {A} (xs : list A) : Prop :=
    forall i j x,
      nth_error xs i = Some x ->
      nth_error xs j = Some x ->
      i = j.

  Lemma list_values_injective_cons :
    forall {A} (xs : list A) x,
      list_values_injective (x :: xs) ->
      list_values_injective xs.
  Proof.
    intros A xs x H.
    red.
    intros i j a NTH1 NTH2.
    apply Nat.succ_inj.
    eapply H; cbn; eauto.
  Qed.

  Lemma find_in_add_all :
    forall {elt} i kvs m k (v : elt),
      nth_error kvs i = Some (k, v) ->
      list_values_injective (map fst kvs) ->
      IM.find k (add_all kvs m) = Some v.
  Proof.
    induction i;
      intros kvs m k v NTH INJ.
    - destruct kvs in *; cbn in NTH; inv NTH.
      cbn.
      apply find_add_eq.
    - cbn in NTH.
      destruct kvs in *; cbn in NTH; inv NTH.
      destruct p.
      cbn.
      apply find_add_neq.
      { erewrite <- nth_error_cons_succ with (x:=(k0,e)) in H0.
        eapply map_nth_error with (f:=fst) in H0.
        rewrite map_cons in H0.
        specialize (INJ (S i) 0 k).
        intros CONTRA; subst.
        repeat (forward INJ; cbn in *; auto).
        discriminate.
      }

      apply IHi; auto.
      eapply list_values_injective_cons; eauto.
  Qed.

  (** ** [add]/[member] interaction
        Added keys are a member of the map
   *)
  Lemma member_add_eq {a}: forall k v (m: IntMap a),
      member k (add k v m).
  Proof using.
    intros.
    cbn.
    apply IM.Raw.Proofs.mem_1.
    apply IM.Raw.Proofs.add_bst, IM.is_bst.
    rewrite IM.Raw.Proofs.add_in; auto.
  Qed.

  Lemma member_add_ineq {a}: forall k k' v (m: IntMap a),
      k <> k' ->
      member k (add k' v m) <-> member k m.
  Proof using.
    intros.
    cbn. split.
    - intros IN; apply IM.Raw.Proofs.mem_2 in IN.
      rewrite IM.Raw.Proofs.add_in in IN.
      destruct IN as [-> | IN]; [contradiction H; auto | ].
      apply IM.Raw.Proofs.mem_1; [apply IM.is_bst | auto].
    - intros IN.
      apply IM.Raw.Proofs.mem_1.
      apply IM.Raw.Proofs.add_bst, IM.is_bst.
      rewrite IM.Raw.Proofs.add_in; right; auto.
      apply IM.Raw.Proofs.mem_2 in IN; auto.
  Qed.

  Lemma member_add_preserved {a}: forall k k' v (m: IntMap a),
      member k m ->
      member k (add k' v m).
  Proof using.
    intros k k' v m H.
    cbn in *.
    apply IM.Raw.Proofs.mem_1.
    apply IM.Raw.Proofs.add_bst, IM.is_bst.
    rewrite IM.Raw.Proofs.add_in; auto.
    right. apply IM.Raw.Proofs.mem_2.
    apply H.
  Qed.

  (** ** Equivalences
        Both notions of equivalence of maps that we manipulate are indeed equivalences
        (assuming the relation on values is itself an equivalence for [Equiv]).
   *)
  #[global] Instance Equal_Equiv {a}: Equivalence (@Equal a).
  Proof using.
    split.
    - repeat intro; reflexivity.
    - repeat intro.
      symmetry; apply H.
    - intros ? ? ? EQ1 EQ2 ?.
      etransitivity; eauto.
  Qed.

  #[global] Instance Equiv_Equiv {a} {r: a -> a -> Prop} {rE : Equivalence r} : Equivalence (Equiv r).
  Proof using.
    split.
    - intros ?; split.
      intros k; reflexivity.
      intros * LU1 LU2; rewrite LU1 in LU2; inversion LU2; reflexivity.
    - intros ? ? [DOM EQ]; split.
      intros ?; split; intros ?; apply DOM; auto.
      intros; symmetry; eapply EQ; eauto.
    - intros ? ? ? [DOM1 EQ1] [DOM2 EQ2]; split.
      intros ?; split; intros ?.
      apply DOM2,DOM1; auto.
      apply DOM1,DOM2; auto.
      intros ? ? ? LU1 LU2.
      generalize LU1; intros LU3; apply lookup_member,DOM1,member_lookup in LU3.
      destruct LU3 as [e'' LU3].
      transitivity e''.
      eapply EQ1; eauto.
      eapply EQ2; eauto.
  Qed.

  #[global] Instance Proper_lookup {a} k: Proper (@Equal a ==> Logic.eq) (lookup k).
  Proof using.
    repeat intro.
    apply H.
  Qed.

  #[global] Instance Proper_add {a} : Proper (Logic.eq ==> Logic.eq ==> Equal ==> Equal) (@add a).
  Proof using.
    repeat intro; subst.
    destruct (Z.eq_dec k y); [subst; rewrite 2 lookup_add_eq; auto | rewrite 2 lookup_add_ineq; auto].
  Qed.

  (** ** [add]/[add]
        Consecutive extensions of the map either commute or erase the oldest one.
   *)
  Lemma add_add : forall {a} off b1 b2 (m : IM.t a),
      Equal (add off b2 (add off b1 m)) (add off b2 m).
  Proof using.
    intros; intro key; cbn.
    rewrite IM.Raw.Proofs.add_find; [| apply IM.Raw.Proofs.add_bst, IM.is_bst].
    rewrite IM.Raw.Proofs.add_find; [| apply  IM.is_bst].
    rewrite IM.Raw.Proofs.add_find; [| apply  IM.is_bst].
    flatten_goal; auto.
  Qed.

  Lemma Equiv_add_add : forall {a} {r: a -> a -> Prop} {rR: Reflexive r},
      forall k v1 v2 (m: IM.t a),
        Equiv r (add k v2 (add k v1 m)) (add k v2 m).
  Proof using.
    intros; split.
    - intros key.
      destruct (Z.eq_dec key k).
      + subst; rewrite 2 member_add_eq; reflexivity.
      + subst; rewrite 3 member_add_ineq; auto; reflexivity.
    - intros key v v' LU1 LU2; cbn.
      destruct (Z.eq_dec key k).
      + subst; rewrite lookup_add_eq in LU1, LU2; inv LU1; inv LU2.
        reflexivity.
      + subst; rewrite lookup_add_ineq in LU1, LU2; auto; rewrite lookup_add_ineq in LU1; auto.
        rewrite LU1 in LU2; inv LU2.
        reflexivity.
  Qed.

  Lemma add_add_ineq : forall {a} k1 k2 v1 v2 (m : IM.t a),
      k1 <> k2 ->
      Equal (add k2 v2 (add k1 v1 m)) (add k1 v1 (add k2 v2 m)).
  Proof using.
    intros; intro key; cbn.
    rewrite IM.Raw.Proofs.add_find; [| apply IM.Raw.Proofs.add_bst, IM.is_bst].
    rewrite IM.Raw.Proofs.add_find; [| apply  IM.is_bst].
    rewrite IM.Raw.Proofs.add_find; [| apply IM.Raw.Proofs.add_bst, IM.is_bst].
    rewrite IM.Raw.Proofs.add_find; [| apply  IM.is_bst].
    pose proof (IM.Raw.Proofs.MX.eqb_alt key k2).
    flatten_goal; auto.
    pose proof (IM.Raw.Proofs.MX.eqb_alt key k1).
    flatten_goal; auto.
    unfold IM.Raw.Proofs.MX.eqb in *.
    flatten_hyp H0.
    flatten_hyp H1.
    subst; contradiction H; auto.
    inv H1.
    inv H0.
  Qed.

  Lemma key_in_range_or_not_aux {a} : forall (k z : Z) (l : list a),
      ({z <= k <= z + Zlength l - 1} + {k < z} + {k >= z + Zlength l})%Z.
  Proof using.
    induction l as [| x l IH]; intros.
    - cbn; rewrite Z.add_0_r.
      destruct (Z_lt_ge_dec k z); [left; right; auto | right; lia].
    - rewrite Zlength_cons, <- Z.add_1_r.
      destruct IH as [[IH | IH] | IH].
      + left; left; lia.
      + left; right; lia.
      + destruct (Z.eq_dec k (z + Zlength l)).
        * subst; left; left; rewrite Zlength_correct; lia.
        * right; lia.
  Qed.

  Lemma key_in_range_or_not {a} : forall (k z : Z) (l : list a),
      ({z <= k <= z + Zlength l - 1} + {k < z \/ k >= z + Zlength l})%Z.
  Proof using.
    intros; destruct (@key_in_range_or_not_aux _ k z l) as [[? | ?] | ?]; [left; auto | right; auto | right; auto].
  Qed.

  Fixpoint IM_find_many {A} (xs : list Z) (im : IntMap A) : option (list A)
    := match xs with
       | [] => ret []
       | (x::xs) =>
         elt  <- IM.find x im;;
         elts <- IM_find_many xs im;;
         ret (elt :: elts)
       end.

  (* Merge taking the latter arguments' values if duplicates.
   Unclear if IM.Raw.merge would have this property.
   *)
  Definition IM_merge {a} (m1 : IM.Raw.t a) (m2 : IM.Raw.t a) : IM.Raw.t a
    := IM.Raw.fold (IM.Raw.add (elt:=a)) m2 m1.

  Definition IM_Refine {a b} (R : a -> b -> Prop) : IntMap a -> IntMap b -> Prop :=
    fun m m' =>
      (forall k, member k m <-> member k m') /\
        (forall k e e', lookup k m = Some e -> lookup k m' = Some e' -> R e e').

  Lemma IM_Refine_empty :
    forall {R1 R2} (R1R2 : R1 -> R2 -> Prop),
      IM_Refine R1R2 (IM.empty R1) (IM.empty R2).
  Proof.
    intros R1 R2 R1R2.
    split.
    - intros k.
      split; intros MEM;
        inv MEM.
    - intros k e e' L1 L2.
      inv L1.
  Qed.

  Lemma IM_Refine_add :
    forall {R1 R2} (R1R2 : R1 -> R2 -> Prop) m1 m2 k x y
      (REF : IM_Refine R1R2 m1 m2)
      (RXY : R1R2 x y),
      IM_Refine R1R2 (add k x m1) (add k y m2).
  Proof.
    intros R1 R2 R1R2 m1 m2 k x y REF RXY.
    split.
    - intros k0.
      destruct (Z.eq_dec k k0) eqn:K; subst.
      + split; intros MEM; apply member_add_eq.
      + split; intros MEM; apply member_add_ineq;
          apply member_add_ineq in MEM; eauto;
          apply REF; auto.
    - intros k0 e e' L L'.
      destruct (Z.eq_dec k k0) eqn:K; subst.
      + rewrite lookup_add_eq in L.
        rewrite lookup_add_eq in L'.
        inv L; inv L'; auto.
      + rewrite lookup_add_ineq in L; eauto.
        rewrite lookup_add_ineq in L'; eauto.
        eapply REF; eauto.
  Qed.
End Map_Operations.

Definition traverseWithKeyRaw {t} `{Applicative t} {a b} (f : IM.Raw.key -> a -> t b) (m : IM.Raw.t a) : t (IM.Raw.t b)
  :=
  let fix go x :=
    match x with
    | IM.Raw.Leaf _ => pure (IM.Raw.Leaf _)
    | IM.Raw.Node l k v r h =>
        if Z.eqb 1%Z h
        then (fun v' => IM.Raw.Node (IM.Raw.Leaf _) k v' (IM.Raw.Leaf _) 1%Z) <$> f k v
        else (fun l' v' r' => IM.Raw.Node l' k v' r' h) <$> go l <*> f k v <*> go r
    end
  in
  go m.

#[global] Instance Traversable_RawIntMap : Traversable IM.Raw.t.
split.
intros F Ap A B X X0.
eapply traverseWithKeyRaw.
intros k.
apply X.
apply X0.
Defined.

Definition traverseWithKey {t} `{Applicative t} {a b} (f : IM.key -> a -> t b) (m : IM.t a) : t (IM.t b).
  eapply @IM.fold.
  3: apply (pure (IM.empty _)).
  2: apply m.
  - intros k e acc.
    refine (let res := f k e in _).
    eapply ap.
    2: apply acc.
    eapply fmap.
    2: apply res.
    apply (IM.add k).
Defined.

#[global] Instance Traversable_IntMap : Traversable IntMap.
split.
intros F Ap A B X X0.
eapply traverseWithKey.
intros k.
apply X.
apply X0.
Defined.

Import Monoid.
#[global] Instance Foldable_IS : Foldable IS.t Z.
split.
intros m M conv s.
apply (IS.fold (fun k acc => monoid_plus M (conv k) acc) s (monoid_unit M)).
Defined.

#[global] Instance Foldable_IM_Raw {a} : Foldable (IM.Raw.t a) Z.
split.
intros m M conv s.
apply (IM.Raw.fold (fun k _ acc => monoid_plus M (conv k) acc) s (monoid_unit M)).
Defined.
