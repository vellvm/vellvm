(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)


(** * Environments *)

Require Import Equalities List.
Set Implicit Arguments.

(** An _environment_ maps values of type [K.t] to values of type 
    V. This module implements updateable environments using Coq 
    functions and proves some simple facts about equality. *)

Module Make_Env (K:UsualDecidableType).
Section WithV.
  Variable V : Type.

  Definition t := K.t -> V.

  Definition empty (init:V) : t := fun _ => init.

  Definition update (st:t) (k:K.t) (v:V) : t :=
    fun k' => if K.eq_dec k k' then v else st k'.

  (* Properties *)
  Theorem update_eq : forall v k1 k2 st,
    K.eq k1 k2 -> (update st k1 v) k2 = v.
(* FOLD *)
  Proof.
    intros. unfold update. 
    destruct (K.eq_dec k1 k2); intuition.
  Qed.
(* /FOLD *)

  Theorem update_neq : forall k1 k2 v st,
    ~ K.eq k1 k2 -> (update st k1 v) k2 = st k2.
(* FOLD *)
  Proof.
    intros. unfold update.
    destruct (K.eq_dec k1 k2); intuition.
  Qed.
(* /FOLD *)

  Theorem update_shadow : forall v1 v2 k1 k2 st,
    K.eq k1 k2 -> 
    (update (update st k1 v1) k1 v2) k2 = (update st k1 v2) k2.
(* FOLD *)
  Proof.
    intros. unfold update.
    destruct (K.eq_dec k1 k2); reflexivity.
  Qed.
(* /FOLD *)

  Theorem update_same : forall v1 k1 k2 (st : t),
    st k2 = v1 -> (update st k1 v1) k2 = st k2.
(* FOLD *)
  Proof.
    intros. unfold update. 
    destruct (K.eq_dec k1 k2); subst; reflexivity.
  Qed.
(* /FOLD *)

  Fixpoint mupdate (st:t) (ks:list K.t) (vs:list V) : t :=
    match ks, vs with
      | k :: ks', v :: vs' => mupdate (update st k v) ks' vs'
      | _, _ => st
    end.

End WithV.
End Make_Env.

