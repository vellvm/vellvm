(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)


Set Implicit Arguments.
Set Maximal Implicit Insertion.

Section STMON.

  Variable (S : Type).

  Definition stmon (A:Type) : Type := S -> (S * A).

  Definition ret (A:Type) (a:A) : stmon A := fun s => (s, a).

  Definition bind (A B:Type) (m:stmon A) (f:A -> stmon B) : (stmon B) :=
    fun s => let (s', a) := m s in f a s'.

  Definition bind2 (A B C:Type) (f:stmon (A * B)) (g:A -> B -> stmon C) : stmon C :=
    fun s => let '(s', (a, b)) := f s in g a b s'.

  Definition stget : stmon S := 
    fun s => (s, s).

  Definition stput (s:S) : stmon unit := 
    fun _ => (s, tt).

  Definition stmod (f:S -> S) : stmon unit :=
    fun s => (f s, tt).

  (* Definition strun (A:Type) (ma:stmon A) (s:S) : (S * A) := *)
  (*   ma s. *)

  Definition steval (A:Type) (ma:stmon A) (s:S) : A :=
    snd (ma s).

  Definition stexec (A:Type) (ma:stmon A) (s:S) : S :=
    fst (ma s).

  (* Global Arguments steval _ _ _ /. *)
  (* Global Arguments stexec _ _ _ /. *)

  Definition stlift (A:Type) (R:S -> S -> Prop) : stmon A -> Prop :=
    fun ma => forall s, R s (fst (ma s)).

  Require Import FunctionalExtensionality.

  Lemma stmon_left_id : forall A B (a:A) (f: A -> stmon B),
    bind (ret a) f = f a.
  Proof. 
    intros. unfold bind, ret. 
    change (f a) with (fun s => f a s) at 2; auto.
  Qed.

  Lemma stmon_right_id : forall A (a:A) (ma:stmon A),
    bind ma ret = ma.
  Proof. 
    intros. extensionality s. unfold bind, ret.
    destruct (ma s); reflexivity.
  Qed.

  Lemma stmon_assoc : 
    forall A B C (m:stmon A) (f:A -> stmon B) (g:B -> stmon C),
    bind m (fun a => bind (f a) g) = bind (bind m f) g.
  Proof.
    intros. extensionality s. unfold bind.
    destruct (m s); reflexivity.
  Qed.

End STMON.

Infix ">>=" := bind (at level 100, no associativity) : stmon_scope.
Infix ">>=2" := bind2 (at level 100, no associativity) : stmon_scope.

Notation "m '>>>' k" := (bind m (fun _:unit => k))
  (at level 100, right associativity) : stmon_scope.

Notation "'do' X <- A ; B" := (bind A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200) : stmon_scope.

Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
  (at level 200, X ident, Y ident, A at level 100, B at level 200, 
  format "'do'  ( X ,  Y )  <-  A  ;  B") : stmon_scope.

Delimit Scope stmon_scope with stmon.
