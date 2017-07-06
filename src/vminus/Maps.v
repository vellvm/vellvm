(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)


Require Import Equalities List.
Import ListNotations.

Set Implicit Arguments.

Module Type Map (K:UsualDecidableType).

Section withv.
Variable V : Type.

Parameter t : Type -> Type.
Parameter empty : t V.
Parameter get : t V -> K.t -> option V.
Parameter set : t V -> K.t -> V -> t V.
Parameter rem : t V -> K.t -> t V.
Parameter dom : t V -> list K.t.
Parameter forallb2 : (K.t -> V -> bool) -> t V -> bool.


Axiom update_eq : forall v k1 k2 m, k2 = k1 -> get (set m k1 v) k2 = Some v.
Axiom update_neq : forall v k1 k2 m, k2 <> k1 -> get (set m k1 v) k2 = get m k2.
Axiom get_in_dom : forall m k v, get m k = Some v -> In k (dom m).
Axiom dom_in_get : forall m k, In k (dom m) -> exists v, get m k = Some v.
Axiom get_forallb2 : forall m f,
                       (forall k v, get m k = Some v -> f k v = true) 
                       <-> forallb2 f m = true.
End withv.

End Map.


Module ListMap (K:UsualDecidableType) <: Map K.

Section withv.
Variable V : Type.

Definition t := list (K.t * V).

Definition empty : t := [].

Fixpoint get m k : option V := 
  match m with
    | [] => None
    | (k', v) :: m' => if K.eq_dec k k'
                       then Some v
                       else get m' k
  end.

Definition set (m:t) (k:K.t) (v:V) : t :=
  (k, v) :: m.


Fixpoint rem (m:t) (k:K.t) : t :=
  match m with
    | [] => []
    | (k', v) :: m' => if K.eq_dec k k'
                       then rem m' k
                       else (k', v) :: rem m' k
  end.

Fixpoint dom (m:t) : list K.t :=
  match m with
    | [] => []
    | (k', v) :: m' => k' :: dom m'
  end.

Fixpoint forallb2' (f:K.t -> V -> bool) (m:t) (d:list K.t) : bool :=
     match d with
       | [] => true
       | k :: d' => match get m k with
                      | None => false
                      | Some v => f k v && forallb2' f m d'
                    end
     end.  

Definition forallb2 (f:K.t -> V -> bool) (m:t) : bool :=
  forallb2' f m (dom m).


Lemma update_eq : forall v k1 k2 m,

    k2 = k1 -> get (set m k1 v) k2 = Some v.
Proof.
  intros; simpl. destruct (K.eq_dec _ _); intuition.
Qed.


Lemma update_neq : forall v k1 k2 m,
  k2 <> k1 -> get (set m k1 v) k2 = get m k2.
Proof.
  intros; simpl. destruct (K.eq_dec _ _); intuition.
Qed.

Lemma get_in_dom : forall m k v,
  get m k = Some v -> In k (dom m).
Proof.
  induction m; intros k v. inversion 1.
  destruct a as [k' v']; simpl in *. intros. destruct (K.eq_dec k k'); intuition eauto. 
Qed.

Lemma dom_in_get : forall m k,
  In k (dom m) -> exists v, get m k = Some v.
Proof.
  induction m. inversion 1.
  destruct a as [k' v']; simpl in *. 
  intro k. destruct (K.eq_dec k k') as [|Heq]; intros. intuition eauto.
  inversion H; eauto; contradict Heq; auto.
Qed.

Lemma get_forallb2' : forall m f P,
  (forall k v, P k v <-> f k v = true) ->
  ((forall k v, get m k = Some v -> P k v)
   <-> forallb2 f m = true).
Proof.
  intros until 0. intro Hpf. unfold forallb2.
  split; intros.

  - (* Case "->". *)
  pose proof (dom_in_get m) as Hd.
  set (d := dom m) in *. clearbody d.

  induction d. reflexivity. simpl. 
  destruct (get m a) eqn:Hget.
  rewrite IHd; auto. assert (f a v = true).
  apply Hpf. eapply H; eauto. rewrite H0. simpl. reflexivity.
  intros. apply Hd. simpl. right. auto.
  
  ecase (Hd a) as [v Hv]; try (left; auto). 
  rewrite Hv in Hget. inversion Hget.

  - (* Case "<-". *)
  pose proof (get_in_dom m _ H0) as Hd.
  set (d:=dom m) in *. clearbody d.

  induction d. inversion Hd.
  simpl in H.
  destruct (K.eq_dec a k). subst a. rewrite H0 in H.
  apply Hpf; auto. destruct (f k v); auto. 
  apply IHd. destruct (get m a); try solve [inversion H].
  destruct (f a v0).
  destruct (forallb2' f m d); auto.
  destruct (forallb2' f m d); auto.
  inversion Hd; intuition.
Qed.  


Lemma get_forallb2 : forall m f,
  (forall k v, get m k = Some v -> f k v = true) 
  <-> 
  forallb2 f m = true.
Proof.
  intros. unfold forallb2.
  split; intros.

  - (* Case "->". *)
  pose proof (dom_in_get m) as Hd.
  set (d := dom m) in *. clearbody d.

  induction d. reflexivity. simpl. 
  destruct (get m a) eqn:Hget.
  rewrite H; auto. rewrite IHd; auto. intros.
  apply Hd. simpl. right; auto.
  
  ecase (Hd a) as [v Hv]; try (left; auto). 
  rewrite Hv in Hget. inversion Hget.

  - (* Case "<-". *)
  pose proof (get_in_dom m _ H0) as Hd.
  set (d:=dom m) in *. clearbody d.

  induction d. inversion Hd.
  simpl in H.
  destruct (K.eq_dec a k). subst a. rewrite H0 in H.
  destruct (f k v); auto.
  apply IHd.
  destruct (get m a); try solve [inversion H].
  destruct (forallb2' f m d); auto.
  destruct (f a v0); auto.
  inversion Hd; intuition.
Qed.  

End withv.

End ListMap.


