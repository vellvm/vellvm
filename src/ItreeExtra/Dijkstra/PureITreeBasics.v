From Coq Require Import
     Morphisms.

From ExtLib Require Import
     Structures.Monad.

From Paco Require Import paco.

From ITree Require Import
     Axioms
     ITree
     ITreeFacts
     Props.Infinite.

Import Monads.
Import MonadNotation.
#[local] Open Scope monad_scope.

Set Implicit Arguments.

(* Contains some useful definitions and lemmas regarding ITrees with no events*)

(** The itree Tau (Tau (Tau ...))*)
#[local] Notation spin := ITree.spin.

(*this implies that if a spec w accepts spin, then bind w f should too?   *)
Lemma spin_bind : forall (E : Type -> Type) (A B : Type) (f : A -> itree E B), spin ≈ ITree.bind spin f.
Proof.
  intros. pcofix CIH. pfold. unfold bind. simpl. red.
  cbn. constructor. right. auto.
Qed.

(*Depreacated predicate on itree predicates. Intended to denote that a predicate is invariant wrt adding
  or subtracting a finite number of Tau's. Replaced with resp_eutt*)
Definition tau_invar (E : Type -> Type) (A : Type) (P : itree E A -> Prop) : Prop :=
    forall (t : itree E A), (P t -> (P (Tau t))) /\(P (Tau t) -> P t).

(*Characterizes predicates that respect the eutt relation on itrees. Captures the notion that a predicate
  is invariant wrt adding or subtracting a finite number of Tau's*)
Notation resp_eutt P := (Proper (eutt eq ==> iff) P).

Lemma tau_invar_resp_eutt1: forall (E : Type -> Type) (A : Type) (P : itree E A -> Prop),
                                 (forall t1 t2, t1 ≈ t2 ->(P t1 <-> P t2)) -> tau_invar P.
  Proof.
    intros. unfold tau_invar. split; intros;
    eapply H; try eassumption; rewrite tau_eutt; reflexivity.
  Qed.

(*spin is the only divergent itree with the void1 event type,*)
Lemma div_spin_eutt : forall (A : Type) (t : itree void1 A), any_infinite t -> t ≈ spin.
Proof.
  intros A. pcofix CIH. intros. pfold. red. cbn.
  destruct (observe t) eqn : Heqt.
  - specialize (itree_eta t) as H. rewrite Heqt in H. rewrite H in H0. pinversion H0.
  - constructor. right. apply CIH. specialize (itree_eta t) as H. rewrite Heqt in H.
    assert (t ≈ Tau t0).
    + rewrite H. reflexivity.
    + rewrite <- tau_eutt. rewrite <- H1. auto.
  - destruct e.
Qed.

Lemma eutt_reta_or_div_aux : forall A (t : itree void1 A), ~(exists a, ret a ≈ t) -> any_infinite t.
Proof.
  intro A. pcofix CIH. pfold. unfold any_infinite_. intros. destruct (observe t) eqn : Heqt.
  - exfalso. specialize (itree_eta t) as H. rewrite Heqt in H. apply H0.
    exists r0. rewrite H. reflexivity.
  - constructor. right. eapply CIH; eauto. intro. apply H0.
    destruct H as [a Ha]. exists a. specialize (itree_eta t) as Ht. rewrite Heqt in Ht.
    rewrite Ht. rewrite tau_eutt. auto.
  - destruct e.
Qed.

  (*All itrees with void1 event type either just return a value a, or they diverge (requires the law of the excluded middle to prove) *)
Lemma eutt_reta_or_div : forall A (t : itree void1 A), (exists a, ret a ≈ t) \/ (any_infinite t).
Proof.
  intros A t.  specialize (classic (exists a, ret a ≈ t) ) as Hlem. destruct Hlem; auto.
  right. apply eutt_reta_or_div_aux. auto.
Qed.

Lemma ret_not_div : forall (A : Type) (E : Type -> Type) (a : A), ~ (@any_infinite E A (ret a)).
Proof.
  intros. intro Hcontra. pinversion Hcontra.
Qed.

Lemma not_ret_eutt_spin : forall A E (a : A), ~ (Ret a ≈ @spin E A).
Proof.
  intros. intro Hcontra. symmetry in Hcontra. revert Hcontra; apply no_infinite_ret.
  apply spin_infinite.
Qed.

Lemma eutt_ret_euttge : forall (E : Type -> Type) (A : Type) (a : A) (t : itree E A),
      t ≈ Ret a -> t ≳ Ret a.
Proof.
  intros. generalize dependent t. pcofix CIH. intros. pfold. red. pinversion H0; subst; auto.
  - cbn. auto with itree.
  - cbn. apply EqTauL; auto.
    genobs t1 ot1. genobs (go (@RetF E A _ a)) ot2.  clear H1.
    generalize dependent t1. generalize dependent t.
    induction REL; intros; subst; auto; try discriminate.
    + constructor. inversion Heqot2. auto.
    + constructor; auto. eapply IHREL; eauto.
Qed.

Lemma unfold_spin : forall (E : Type -> Type) (A : Type), (@spin E A) ≅ Tau spin.
Proof.
  intros.  pcofix CIH. cbn. pfold. red. cbn. apply EqTau. cbn.
  left. pcofix CIH'. pfold. red. cbn. auto with itree.
Qed.

Lemma burn_eutt_r : forall (A : Type) (t t' : itree void1 A) (n : nat), t≈ t' -> burn n t ≈ t'.
Proof.
  intros. generalize dependent t. generalize dependent t'. induction n; intros; simpl; auto.
  destruct (observe t) eqn : Heq; try destruct e.
  - specialize (itree_eta t) as Ht. rewrite Heq in Ht. rewrite <- Ht. auto.
  - apply IHn. specialize (itree_eta t) as Ht. rewrite Heq in Ht. rewrite Ht in H.
    rewrite tau_eutt in H. auto.
Qed.
