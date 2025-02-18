From Coq Require Import
  FSets.FMapAVL
  FSets.FSetAVL
  FSetProperties
  FMapFacts.

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
