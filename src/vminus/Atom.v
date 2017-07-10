(* TODO:
   -  Use MetatheoryAtom instead of this one.
   -  license
*)




(** This file defines a type of atoms with: 
      - a _decidable equality_ 
      - a way of generating _fresh_ atoms
*)

Require Import Arith List Equalities PeanoNat.
Require Import String.

Require Import QuickChick.QuickChick.

(** ** ATOM *)

Module Type ATOM <: UsualDecidableType.

  Parameter t : Set.
  Parameter eq_dec : forall (x y:t), {x = y} + {x <> y}.
  Parameter fresh : list t -> t.
  Parameter fresh_not_in : forall l, ~ In (fresh l) l.
  Parameter nat_of: t -> nat.

  Include HasUsualEq <+ UsualIsEq.

End ATOM.

(** ** Atom *)
(** Implements the [ATOM] signature. *)

Module Atom : ATOM.

  Definition t := nat.
  Definition eq_dec := eq_nat_dec.
  
  Fixpoint max_elt (al:list t) : t :=
    match al with
      | nil => 0
      | n'::al' => max n' (max_elt al')
    end.

  Definition fresh (al:list t) : t :=
    S (max_elt al).

  Lemma max_elt_spec : forall al b,
    In b al -> b <= max_elt al.
(* FOLD *)
  Proof.
    intros. induction al. inversion H.
      inversion H; subst; simpl. apply Nat.le_max_l.
      eapply le_trans; auto with arith. (* apply Nat.le_max_r. *)
  Qed.
(* /FOLD *)
    
  Lemma fresh_not_in : forall l, 
    ~ In (fresh l) l.
(* FOLD *)
  Proof.
    unfold fresh, not. intros l Hin.
    specialize (max_elt_spec _ _ Hin). intro Ha.
    contradict Ha; apply le_Sn_n.
  Qed.
(* /FOLD *)

  Include HasUsualEq <+ UsualIsEq.

  Definition nat_of (a : nat) := a.
  
End Atom.

(* Automatically unfold Atom.eq *)
Global Arguments Atom.eq /.






