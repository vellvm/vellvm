From Coq Require Import
     FSets.FMapAVL
     FSets.FSetAVL
     FSetProperties
     FMapFacts
     ZArith
     List
     Lia.

From Vellvm Require Import
  Utils.Monads
  Utils.Tactics
  ListUtil.

From ExtLib Require Import
     Structures.Monads.

Import ListNotations.
Import MonadNotation.

(* N maps *)
Module NM := FMapAVL.Make(Coq.Structures.OrderedTypeEx.N_as_OT).
Definition NMap := NM.t.

Fixpoint NM_from_list {A} (kvs : list (N * A)) : NMap A
  := match kvs with
     | [] => @NM.empty _
     | ((k, v)::xs) => @NM.add _ k v (NM_from_list xs)
     end.

(* N sets *)
Module NS := FSetAVL.Make(Coq.Structures.OrderedTypeEx.N_as_OT).
Definition NSet := NS.t.

Fixpoint NS_from_list (kvs : list N) : NSet
  := match kvs with
     | [] => NS.empty
     | (x::xs) => NS.add x (NS_from_list xs)
     end.

Fixpoint NM_find_many {A} (xs : list N) (nm : NMap A) : option (list A)
  := match xs with
     | [] => ret []
     | (x::xs) =>
       elt  <- NM.find x nm;;
       elts <- NM_find_many xs nm;;
       ret (elt :: elts)
     end.

Definition NM_Refine
  {elt1 elt2 : Type}
  (ref_elt : elt1 -> elt2 -> Prop)
  (m1 : NM.t elt1)
  (m2 : NM.t elt2) : Prop
  :=
  (forall k : NM.key, NM.In (elt:=elt1) k m1 <-> NM.In (elt:=elt2) k m2) /\
    (forall (k : NM.key) e e', NM.MapsTo k e m1 -> NM.MapsTo k e' m2 -> ref_elt e e').

Lemma NM_In_empty_contra :
  forall {elt : Type} k,
    ~ (NM.In (elt:=elt) k (NM.empty elt)).
Proof.
  intros elt k CONTRA.
  repeat red in CONTRA.
  destruct CONTRA as (?&?).
  (* repeat red in H. *) (* Seems that you don't need this. *)
  eapply NM.Raw.Proofs.empty_1 in H; auto.
Qed.

Lemma NM_find_In :
  forall {elt} k m e,
    NM.find (elt:=elt) k m = Some e ->
    NM.In k m.
Proof.
  intros elt k m e FIND.
  apply NM.find_2 in FIND.
  repeat red.
  exists e.
  apply FIND.
Qed.

Lemma NM_find_not_In :
  forall {elt} k m,
    NM.find (elt:=elt) k m = None ->
    ~ NM.In k m.
Proof.
  intros elt k m NFIND CONTRA.
  destruct CONTRA as (?&?).
  apply NM.find_1 in H.
  rewrite NFIND in H; inv H.
Qed.

Lemma NM_In_add_eq :
  forall {elt} k v m,
    NM.In (elt:=elt) k (NM.add k v m).
Proof.
  intros elt k v m.
  repeat red.
  exists v.
  apply NM.add_1; auto.
Qed.

Lemma NM_In_add_neq :
  forall {elt} k1 k2 v m,
    k1 <> k2 ->
    NM.In (elt:=elt) k1 (NM.add k2 v m) <-> NM.In (elt:=elt) k1 m.
Proof.
  intros elt k1 k2 v m NEQ.
  split; intros [e MAPS]; exists e.
  - eapply NM.add_3; eauto.
  - eapply NM.add_2; eauto.
Qed.

Lemma NM_MapsTo_injective : forall {elt} k v1 v2 m,
    NM.MapsTo (elt:=elt) k v1 m -> NM.MapsTo(elt:=elt) k v2 m -> v1 = v2.
Proof.
  intros elt k v1 v2 m NMAP1 NMAP2.
  apply NM.find_1 in NMAP1.
  apply NM.find_1 in NMAP2.
  rewrite NMAP1 in NMAP2.
  injection NMAP2. auto.
Qed.
  
Lemma NM_MapsTo_eq :
  forall {elt} k e v m,
    NM.MapsTo (elt:=elt) k e (NM.add k v m) ->
    e = v.
Proof.
  intros elt k e v m NMAP.
  pose proof NM.add_1.
  assert (H1: k = k) by reflexivity.
  apply (@NM.add_1 elt m k k v) in H1.
  apply (NM_MapsTo_injective _ _ _ _ NMAP H1).
Qed.


