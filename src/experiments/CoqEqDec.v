(* This file is distributed under the terms of the MIT License, also
   known as the X11 Licence.  A copy of this license is in the README
   file that accompanied the original distribution of this file.

   Based on code written by:
     Brian Aydemir *)

(** A type class-based library for working with decidable equality. *)

Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Logic.Decidable.

Generalizable Variable A.

(* *********************************************************************** *)
(** * Hints for [equiv] *)

Hint Extern 0 (?x === ?x) => reflexivity.
Hint Extern 1 (_ === _) => (symmetry; trivial; fail).
Hint Extern 1 (_ =/= _) => (symmetry; trivial; fail).


(* *********************************************************************** *)
(** * Facts about [EqDec] *)

(** The [EqDec] class is defined in Coq's standard library. *)

Lemma equiv_reflexive' : forall `{EqDec A} (x : A),
  x === x.
Proof. intros. apply equiv_reflexive. Qed.

Lemma equiv_symmetric' : forall `{EqDec A} (x y : A),
  x === y ->
  y === x.
Proof. intros. apply equiv_symmetric; assumption. Qed.

Lemma equiv_transitive' : forall `{EqDec A} (x y z : A),
  x === y ->
  y === z ->
  x === z.
Proof. intros. eapply @equiv_transitive; eassumption. Qed.

Lemma equiv_decidable : forall `{EqDec A} (x y : A),
  decidable (x === y).
Proof. intros. unfold decidable. destruct (x == y); auto. Defined.

(* *********************************************************************** *)
(** * Specializing [EqDec] *)

(** It is convenient to be able to use a single notation for decidable
    equality on types.  This can naturally be done using a type class.
    However, the definition of [EqDec] in the EquivDec library is
    overly general for cases where the equality is [eq]: the extra
    layer of abstraction provided by abstracting over the equivalence
    relation gets in the way of smooth reasoning.  To get around this,
    we define a version of that class where the equivalence relation
    is hard-coded to be [eq].

    Implementation note: One should not declare an instance for
    [EqDec_eq A] directly.  First, declare an instance for [@EqDec A
    eq eq_equivalence].  Second, let class inference build an instance
    for [EqDec_eq A] using the instance declaration below.

    Implementation note (BEA): Specifying [eq_equivalence] explicitly
    is important.  Following Murphy's Law, if type class inference can
    find multiple ways of inferring the [@Equivalence A eq] argument,
    it will do so in the most inconvenient way possible.
    Additionally, I choose to infer [EqDec_eq] instances from [EqDec]
    instances because the standard library already defines instances
    for [EqDec]. *)

Class EqDec_eq (A : Type) :=
  eq_dec : forall (x y : A), {x = y} + {x <> y}.

Instance EqDec_eq_of_EqDec `(@EqDec A eq eq_equivalence) : EqDec_eq A.
Proof. trivial. Qed.

(* WM : Useful definitions and tactics. *)
Definition beq `{EqDec_eq A} x y := if eq_dec x y then true else false.

(* A tactic for instantiating EqDec. *)
Ltac eq_dec_inst := unfold EqDec; unfold equiv; unfold complement; intros x y;
  change ({x = y} + {x <> y}); repeat (decide equality).