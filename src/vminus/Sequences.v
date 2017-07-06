(* 
  Acknowledgements:  
  This file is taken from the compiler verification development created by 

    Xavier Leroy, INRIA Paris-Rocquencourt                    

  and available at: http://gallium.inria.fr/~xleroy/courses/Eugene-2012/
*)


(** A library of relation operators defining sequences of transitions
  and useful properties about them. *)

Set Implicit Arguments.

Section SEQUENCES.

Variable A: Type.                 (**r the type of states *)
Variable R: A -> A -> Prop.       (**r the transition relation, from one state to the next *)

(** ** Finite sequences of transitions *)

(** Zero, one or several transitions: reflexive, transitive closure of [R]. *)

Inductive star: A -> A -> Prop :=
  | star_refl: forall a,
      star a a
  | star_step: forall a b c,
      R a b -> star b c -> star a c.

Lemma star_one:
  forall (a b: A), R a b -> star a b.
Proof.
  intros. econstructor; eauto. constructor.
Qed.

Lemma star_trans:
  forall (a b: A), star a b -> forall c, star b c -> star a c.
Proof.
  induction 1; intros. auto. econstructor; eauto.
Qed.

(** One or several transitions: transitive closure of [R]. *)

Inductive plus: A -> A -> Prop :=
  | plus_left: forall a b c,
      R a b -> star b c -> plus a c.

Lemma plus_one:
  forall a b, R a b -> plus a b.
Proof.
  intros. apply plus_left with b. auto. apply star_refl.
Qed.

Lemma plus_star:
  forall a b,
  plus a b -> star a b.
Proof.
  intros. inversion H. eapply star_step; eauto. 
Qed.

Lemma plus_star_trans:
  forall a b c, plus a b -> star b c -> plus a c.
Proof.
  intros. inversion H. eapply plus_left; eauto. eapply star_trans; eauto.
Qed.

Lemma plus_star_trans':
  forall a b c, star a b -> plus b c -> plus a c.
Proof.
  intros. inversion H. auto. apply plus_star in H0. 
  eapply plus_left. eauto. eapply star_trans; eauto.
Qed.


Lemma star_plus_trans:
  forall a b c, star a b -> plus b c -> plus a c.
Proof.
  intros. inversion H0. inversion H. econstructor; eauto.
  econstructor; eauto. eapply star_trans; eauto. econstructor; eauto. 
Qed.

Lemma plus_right:
  forall a b c, star a b -> R b c -> plus a c.
Proof.
  intros. eapply star_plus_trans; eauto. apply plus_one; auto.
Qed.

(** ** Infinite sequences of transitions *)

(** It is easy to characterize the fact that all transition sequences starting
  from a state [a] are infinite: it suffices to say that any finite sequence
  starting from [a] can always be extended by one more transition. *)

Definition all_seq_inf (a: A) : Prop :=
  forall b, star a b -> exists c, R b c.

(** However, this is not the notion we are trying to characterize: that, starting
  from [a], there exists one infinite sequence of transitions
  [a --> a1 --> a2 --> ... -> aN -> ...].

  Indeed, consider [A = nat] and [R] such that [R 0 0] and [R 0 1].  
  [all_seq_inf 0] does not hold, because a sequence [0 -->* 1] cannot be extended.
  Yet, [R] admits an infinite sequence, namely [0 --> 0 --> ...].  

  Another attempt would be to represent the sequence of states 
  [a0 --> a1 --> a2 --> ... -> aN -> ...] explicitly, as a function 
  [f: nat -> A] such that [f i] is the [i]-th state [ai] of the sequence. *)

Definition infseq_with_function (a: A) : Prop :=
  exists f: nat -> A, f 0 = a /\ forall i, R (f i) (f (1 + i)).

(** This is a correct characterization of the existence of an infinite sequence
  of reductions.  However, it is very inconvenient to work with this definition
  in Coq's constructive logic: in most use cases, the function [f] is not
  computable and therefore cannot be defined in Coq.  *)

(** To obtain a practical definition of infinite sequences, we use the following
  coinductive definition of the predicate [infseq a]. *)

CoInductive infseq: A -> Prop :=
  | infseq_step: forall a b,
      R a b -> infseq b -> infseq a.

(** An inductive predicate such as [star a b] holds iff there exists a finite
  derivation of the conclusion [star a b] that uses the constructors
  [star_refl] and [star_step] a finite number of times.

  A coinductive predicate is similar, but holds iff there exists a finite
  OR INFINITE derivation of the conclusion that uses the constructors
  of the predicate a finite OR INFINITE number of times.

  In other words, an inductive predicate is a smallest fixpoint: the smallest predicate
  that satisfies its constructors; a coinductive predicate is a greatest fixpoint:
  the largest predicate that satisfies its constructors.

  The [infseq] predicate above must be defined coinductively.  Indeed, if
  we define it inductively, the predicate would be empty (always false),
  since there are no base cases!  

  Coq provides some primitive support for constructing infinite derivations
  of facts such as [infseq a].  Such constructions are proofs by coinduction.
  For example, we can prove the following: *)

Remark cycle_infseq:
  forall a, R a a -> infseq a.
Proof.
  intros. cofix COINDHYP. apply infseq_step with a. auto. apply COINDHYP.
Qed.

(** This style of proof by coinduction, using the [cofix] tactic, is effective
  but can run into limitations of Coq's proof engine (the so-called 
  "guard condition").  However, we can derive more conventional
  coinduction principles that are often easier to use. *)

(** Consider a set [X] of states [A], that is, a predicate [X: A -> Prop].
  Assume that for every [a] in [X], we can make one [R] transition to a [b]
  that is still in [X].  Then, starting from [a] in [X], we can transition
  to some [a1] in [X], then to some [a2] still in [X], then... It is clear
  that we are just building an infinite sequence of transitions starting from
  [a]. Therefore [infseq a] should hold.  Let's prove this! *)

Lemma infseq_coinduction_principle:
  forall (X: A -> Prop),
  (forall a, X a -> exists b, R a b /\ X b) ->
  forall a, X a -> infseq a.
Proof.
  intros X P. cofix COINDHYP; intros.
  destruct (P a H) as [b [U V]]. apply infseq_step with b; auto. 
Qed.

(** An even more useful variant of this coinduction principle considers a
  set [X] where for every [a] in [X], we can make one *or several* transitions
  to reach a [b] in [X].  *)

Lemma infseq_coinduction_principle_2:
  forall (X: A -> Prop),
  (forall a, X a -> exists b, plus a b /\ X b) ->
  forall a, X a -> infseq a.
Proof.
  intros.
  apply infseq_coinduction_principle with
    (X := fun a => exists b, star a b /\ X b).
  intros. 
  destruct H1 as [b [STAR Xb]]. inversion STAR; subst.
  destruct (H b Xb) as [c [PLUS Xc]]. inversion PLUS; subst.
  exists b0; split. auto. exists c; auto. 
  exists b0; split. auto. exists b; auto.

  exists a; split. apply star_refl. auto.
Qed.

(** Here is an example of use of [infseq_coinduction_principle]:
  if all finite transition sequences starting at [a] can be extended,
  [infseq a] holds. *)

Lemma infseq_if_all_seq_inf:
  forall a, all_seq_inf a -> infseq a.
Proof.
  apply infseq_coinduction_principle.
  intros. destruct (H a) as [b Rb]. constructor. 
  exists b; split; auto. 
  unfold all_seq_inf; intros. apply H. apply star_step with b; auto.
Qed.

(** Likewise, the function-based characterization [infseq_with_function]
  implies [infseq]. *)

Lemma infseq_from_function:
  forall a, infseq_with_function a -> infseq a.
Proof.
  apply infseq_coinduction_principle.
  intros. destruct H as [f [P Q]].
  exists (f 1); split.
  subst a. apply Q. 
  exists (fun n => f (1 + n)); split. auto. intros. apply Q.
Qed.
 
(** Consider the transition sequences starting at state [a].
  They can be infinite, or they can be finite: after a number of transitions,
  we reach a state from with no transition is possible.  It is intuitively
  obvious that at least one of the two cases must hold. 

  It is however impossible to prove this fact in Coq's constructive logic.
  Indeed, a constructive proof would be isomorphic (by the Curry-Howard isomorphism)
  to a terminating function that solves Turing's halting problem!

  To prove this fact, we must enrich Coq with axioms from classical logic,
  namely the axiom of excluded middle: for all propositions [P],
  either [P] or [~P] hold.  The Coq standard library provides such axioms
  in the module named [Classical], which we now import. *)

Require Import Classical.

Definition irred (a: A) : Prop := forall b, ~(R a b).

Lemma infseq_or_finseq:
  forall a, infseq a \/ exists b, star a b /\ irred b.
Proof.
  intros.
  destruct (classic (forall b, star a b -> exists c, R b c)).
  left. apply infseq_if_all_seq_inf; auto.
  right.
  generalize (not_all_ex_not _ _ H). intros [b P].
  generalize (imply_to_and _ _ P). intros [U V].
  exists b; split. auto.
  red; intros; red; intros. elim V. exists b0; auto.
Qed.

(** ** Determinism properties for functional transition relations. *)

(** A transition relation is functional if every state can transition to at most
  one other state. *)

Hypothesis R_functional:
  forall a b c, R a b -> R a c -> b = c.

(** Uniqueness of finite transition sequences. *)

Lemma star_star_inv:
  forall a b, star a b -> forall c, star a c -> star b c \/ star c b.
Proof.
  induction 1; intros.
  auto.
  inversion H1; subst. right. eapply star_step; eauto. 
  assert (b = b0). eapply R_functional; eauto. subst b0. 
  apply IHstar; auto.
Qed.

Lemma finseq_unique:
  forall a b b',
  star a b -> irred b ->
  star a b' -> irred b' ->
  b = b'.
Proof.
  intros. destruct (star_star_inv H H1).
  inversion H3; subst. auto. elim (H0 _ H4).
  inversion H3; subst. auto. elim (H2 _ H4).
Qed.

(** A state cannot both diverge and terminate on an irreducible state. *)

Lemma infseq_star_inv:
  forall a b, star a b -> infseq a -> infseq b.
Proof.
  induction 1; intros. auto. 
  inversion H1; subst. assert (b = b0). eapply R_functional; eauto. subst b0.
  apply IHstar. auto.
Qed.

Lemma infseq_finseq_excl:
  forall a b,
  star a b -> irred b -> infseq a -> False.
Proof.
  intros. 
  assert (infseq b). eapply infseq_star_inv; eauto. 
  inversion H2. elim (H0 b0); auto. 
Qed.

(** If there exists an infinite sequence of transitions from [a],
  all sequences of transitions arising from [a] are infinite. *)

Lemma infseq_all_seq_inf:
  forall a, infseq a -> all_seq_inf a.
Proof.
  intros. unfold all_seq_inf. intros. 
  assert (infseq b). eapply infseq_star_inv; eauto. 
  inversion H1. subst. exists b0; auto.
Qed.

End SEQUENCES.


  


