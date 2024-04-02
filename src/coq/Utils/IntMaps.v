From Coq Require Import
     FSets.FMapAVL
     FSets.FSetAVL
     FSetProperties
     FMapFacts
     ZArith
     List
     Lia.

From Vellvm Require Import
     Utils.Tactics
     Utils.Monads
     Utils.VellvmRelations
     Numeric.Coqlib
     ListUtil.

From ExtLib Require Import
  Structures.Monads
  Structures.Functor
  Structures.Applicative
  Structures.Traversable
  Structures.Foldable
  Programming.Eqv.

Import EqvNotation.
Import ListNotations.
Import MonadNotation.
Import FunctorNotation.
Import ApplicativeNotation.

#[local] Open Scope Z_scope.

Module IM := FMapAVL.Make(Coq.Structures.OrderedTypeEx.Z_as_OT).
Module IS := FSetAVL.Make(Coq.Structures.OrderedTypeEx.Z_as_OT).
Module Import ISP := FSetProperties.WProperties_fun(Coq.Structures.OrderedTypeEx.Z_as_OT)(IS).
Module Import IP := FMapFacts.WProperties_fun(Coq.Structures.OrderedTypeEx.Z_as_OT)(IM).

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

  (* Give back a list of values from [|i|] to [|i| + |sz| - 1] in [m].
     Uses [def] as the default value if a lookup failed.
   *)
  Definition lookup_all_index {a} (i:Z) (sz:N) (m:IntMap a) (def:a) : list a :=
    List.map (fun x =>
                match lookup x m with
                | None => def
                | Some val => val
                end) (Zseq i (N.to_nat sz)).

  (* Takes the join of two maps, favoring the first one over the intersection of their domains *)
  Definition union {a} (m1 : IntMap a) (m2 : IntMap a)
    := IM.map2 (fun mx my =>
                  match mx with | Some x => Some x | None => my end) m1 m2.

  (* TODO : Move the three following functions *)
  Fixpoint max_default (l:list Z) (x:Z) :=
    match l with
    | [] => x
    | h :: tl =>
      max_default tl (if h >? x then h else x)
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

  Definition next_key {A} (m : IntMap A) : Z
    := let keys := map fst (IM.elements m) in
       1 + maximumBy Z.leb (-1)%Z keys.

  Lemma next_key_gt_0 :
    forall {A} (m : IntMap A),
      next_key m >= 0.
  Proof using.
    intros A m.
    unfold next_key.
    pose proof maximumBy_Z_def (-1) (map fst (IM.elements (elt:=A) m)).
    apply Zle_is_le_bool in H.
    lia.
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

  (** ** Behavior of [lookup_all_index]
   *)

  Lemma lookup_all_index_cons {a} : forall k (n : N) (m : IntMap a) def,
      lookup_all_index k (N.succ n) m def =
      match lookup k m with
      | Some val => val
      | None => def
      end :: lookup_all_index (Z.succ k) n m def.
  Proof using.
    intros.
    unfold lookup_all_index.
    rewrite Zseq_succ; try lia.
    auto.
  Qed.

  Lemma lookup_all_index_add_out_aux {a} : forall l k (n : N) (m : IntMap a) key x def,
      l = Zseq k (N.to_nat n) ->
      (key < k \/ key >= k + Z.of_N n) ->
      lookup_all_index k n (add key x m) def =
      lookup_all_index k n m def.
  Proof using.
    induction l as [| x l IH]; simpl.
    - intros * EQ LT.
      unfold lookup_all_index; rewrite <- EQ; reflexivity.
    - intros * EQ RANGE.
      destruct (N.to_nat n) eqn:EQn; [inv EQ |].
      cbn in EQ; inv EQ.
      assert (n = N.succ (N.of_nat n0)) by lia.
      subst; rewrite lookup_all_index_cons; auto; try lia.
      subst; rewrite lookup_all_index_cons; auto; try lia.
      rewrite lookup_add_ineq; [| lia].
      f_equal.
      apply IH; try lia.
      rewrite Nnat.Nat2N.id.
      reflexivity.
  Qed.

  (* Generalization of [lookup_add_ineq]: adding outside of the range of the lookup is inconsequential *)
  Lemma lookup_all_index_add_out {a} : forall k (n : N) (m : IntMap a) key x def,
      (key < k \/ key >= k + Z.of_N n) ->
      lookup_all_index k n (add key x m) def =
      lookup_all_index k n m def.
  Proof using.
    intros; eapply lookup_all_index_add_out_aux; eauto.
  Qed.

  Lemma lookup_all_index_add {a} : forall k (size : N) x (m : IntMap a) def,
      lookup_all_index k (N.succ size) (add k x m) def =
      x :: lookup_all_index (Z.succ k) size m def.
  Proof using.
    intros *.
    rewrite lookup_all_index_cons; auto; try lia.
    rewrite lookup_add_eq.
    f_equal.
    rewrite lookup_all_index_add_out; auto; try lia.
  Qed.

  Lemma pred_succ_of_nat :
    forall n,
      Pos.pred_N (Pos.of_succ_nat n) = N.of_nat n.
  Proof using.
    induction n; auto.
    cbn.
    rewrite Pos.pred_N_succ.
    auto.
  Qed.

  Lemma lookup_all_index_length :
    forall {A} len off bytes (def : A),
      Datatypes.length (lookup_all_index off len bytes def) = N.to_nat len.
  Proof using.
    intros A len.
    remember (N.to_nat len) as n.
    assert (len = N.of_nat (N.to_nat len)) by lia.
    rewrite H. clear H.
    rewrite <- Heqn.
    clear Heqn len.

    induction n;
      intros off bytes def; auto.

    cbn.
    rewrite map_length.

    rewrite <- (IHn off bytes def).
    rewrite Zseq_length.
    lia.
  Qed.

  (** ** Behavior of [add_all_index]
   *)
  (* Generalization of [lookup_add_eq]: looking in range of the additions is fully defined *)
  Lemma lookup_add_all_index_in {a} : forall l k z (m : IntMap a) v,
      z <= k <= z + Zlength l - 1 ->
      list_nth_z l (k - z) = Some v ->
      lookup k (add_all_index l z m) = Some v.
  Proof using.
    induction l as [| x l IH]; simpl; intros * INEQ LU.
    inv LU.
    destruct (Z.eq_dec k z).
    - subst.
      rewrite Z.sub_diag in LU; cbn in LU; inv LU.
      rewrite lookup_add_eq;  reflexivity.
    - rewrite lookup_add_ineq; auto.
      apply IH.
      rewrite Zlength_cons in INEQ; lia.
      destruct (zeq (k - z)) eqn:INEQ'; [lia |].
      replace (k - (z + 1)) with (Z.pred (k-z)) by lia; auto.
  Qed.

  (* (Different from [lookup_all_index_add_out]) Generalization of [lookup_add_eq]: looking out of range of the additions can ignore the additions *)
  Lemma lookup_add_all_index_out {a} : forall l k z (m : IntMap a),
      (k < z \/ k >= z + Zlength l) ->
      lookup k (add_all_index l z m) = lookup k m.
  Proof using.
    induction l as [| x l IH]; simpl; intros * INEQ; auto.
    destruct (Z.eq_dec k z).
    - subst. exfalso; destruct INEQ as [INEQ | INEQ]; try lia.
      rewrite Zlength_cons, Zlength_correct in INEQ; lia.
    - rewrite lookup_add_ineq; auto.
      apply IH.
      destruct INEQ as [INEQ | INEQ]; [left; lia | ].
      right.
      rewrite Zlength_cons, Zlength_correct in INEQ.
      rewrite Zlength_correct.
      lia.
  Qed.

  Lemma key_in_range_or_not_aux {a} : forall (k z : Z) (l : list a),
      {z <= k <= z + Zlength l - 1} + {k < z} + {k >= z + Zlength l}.
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
      {z <= k <= z + Zlength l - 1} + {k < z \/ k >= z + Zlength l}.
  Proof using.
    intros; destruct (@key_in_range_or_not_aux _ k z l) as [[? | ?] | ?]; [left; auto | right; auto | right; auto].
  Qed.

  Lemma range_list_nth_z : forall {a} (l : list a) k,
      0 <= k < Zlength l ->
      exists v, list_nth_z l k = Some v.
  Proof using.
    induction l as [| x l IH]; intros k INEQ; [cbn in *; lia |].
    cbn; flatten_goal; [eexists; reflexivity |].
    destruct (IH (Z.pred k)) as [v LU]; eauto.
    rewrite Zlength_cons in INEQ; lia.
  Qed.

  Lemma in_range_is_in {a} :  forall (k z : Z) (l : list a),
      z <= k <= z + Zlength l - 1 ->
      exists v, list_nth_z l (k - z) = Some v.
  Proof using.
    intros.
    apply range_list_nth_z; lia.
  Qed.

  (* Generalization of [add_ad], with the added constraint on the size of the lists *)
  Lemma add_all_index_twice {a} : forall (l1 l2 : list a) z m,
      Zlength l1 = Zlength l2 ->
      Equal (add_all_index l2 z (add_all_index l1 z m))
            (add_all_index l2 z m).
  Proof using.
    intros * EQ k.
    destruct (@key_in_range_or_not _ k z l2) as [IN | OUT].
    - destruct (in_range_is_in _ _ _ IN) as [? LU].
      erewrite 2 lookup_add_all_index_in; eauto.
    - rewrite 3 lookup_add_all_index_out; eauto.
      rewrite EQ; auto.
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

  Lemma IM_Refine_Forall2 :
    forall {R1 R2} (r1 : list (Z * R1)) (r2 : list (Z * R2)) R1R2
      (ALL : Forall2 (eq × R1R2) r1 r2),
      IM_Refine R1R2 (IP.of_list r1) (IP.of_list r2).
  Proof.
    intros R1 R2 r1 r2 R1R2 ALL.
    induction ALL.
    - cbn.
      apply IM_Refine_empty.
    - cbn.
      destruct x, y.
      inv H.
      cbn in *; subst.
      unfold IP.uncurry; cbn.
      apply IM_Refine_add; auto.
  Qed.

  Lemma IM_Refine_of_list_app :
    forall {R1 R2} (R1R2 : R1 -> R2 -> Prop) r1 r1' r2 r2'
      (REF1 : Forall2 (eq × R1R2) r1' r2')
      (REF2 : Forall2 (eq × R1R2) r1 r2),
      IM_Refine R1R2 (IP.of_list (r1' ++ r1)) (IP.of_list (r2' ++ r2)).
  Proof.
    intros R1 R2 R1R2 r1 r1' r2 r2' REF1 REF2.
    induction REF1.
    - cbn.
      apply IM_Refine_Forall2; auto.
    - cbn.
      destruct x, y.
      inv H.
      cbn in *; subst.
      unfold IP.uncurry; cbn.
      apply IM_Refine_add; auto.
  Qed.

End Map_Operations.

Definition traverseWithKeyRaw {t} `{Applicative t} {a b} (f : IM.Raw.key -> a -> t b) (m : IM.Raw.t a) : t (IM.Raw.t b)
  :=
  let fix go x :=
    match x with
    | IM.Raw.Leaf => pure (IM.Raw.Leaf _)
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
