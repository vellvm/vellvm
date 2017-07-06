(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)
(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)


(** Bounded iterators *)

(* we can get away with using unary nats in our toy compiler
   Q: why does compcert use positive vs. binary nats? 
      how are they extracted -- extra cons for each number?
   binary nats are better supported in the stdlib*)

Require Import NArith FunctionalExtensionality.

Set Implicit Arguments.

Module Iter.

Section ITERATION.

Variables A B: Type.
Variable step: A -> B + A.

Definition num_iterations := 1000000000000%N.

Open Scope N_scope.

Definition iter_step (x: N)
                     (next: forall y, y < x -> A -> option B)
                     (s: A) : option B :=
  match N.eq_dec x N.zero with
  | left EQ => None
  | right NOTEQ =>
      match step s with
      | inl res => Some res
      | inr s'  => next (N.pred x) (N.lt_pred_l x NOTEQ) s'
      end
  end.


Definition iter: N -> A -> option B := Fix N.lt_wf_0 _ iter_step.
Definition iterate := iter num_iterations.

Variable P: A -> Prop.
Variable Q: B -> Prop.

Hypothesis step_prop:
  forall a : A, P a ->
  match step a with inl b => Q b | inr a' => P a' end.

Lemma iter_prop:
  forall n b a, P a -> iter n a = Some b -> Q b.
Proof.
  intros n b. pattern n. apply (well_founded_ind N.lt_wf_0).
  intros until 2. rewrite (Fix_eq N.lt_wf_0 _ iter_step). 
  unfold iter_step at 1. destruct (N.eq_dec _ _). 
  discriminate 1. specialize (step_prop H0).
  destruct (step a).
    inversion 1; subst b0; exact step_prop.
    apply H; auto. apply N.lt_pred_l; auto.
  intros. f_equal. 
  apply functional_extensionality_dep. intro. 
  apply functional_extensionality_dep. auto.
Qed.

Lemma iterate_prop:
  forall a b, iterate a = Some b -> P a -> Q b.
Proof.
  intros. apply iter_prop with num_iterations a; assumption.
Qed.

End ITERATION.

End Iter.

