From Coq Require Import
     FSets.FMapAVL
     FSets.FSetAVL
     FSetProperties
     FMapFacts
     ZArith
     List
     Lia.

From Vellvm Require Import
     ListUtil.

Import ListNotations.

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
  Proof.
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
  Proof.
    intros def l.
    apply maximumBy_Z_le_def; eauto.
    apply Z.leb_refl.
  Qed.

  Definition maximumBy_Z_correct :
    forall def (l : list Z),
    forall a, In a l -> Z.leb a (maximumBy Z.leb def l).
  Proof.
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

End Map_Operations.
