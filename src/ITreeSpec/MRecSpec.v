From Coq Require Import
  Program
  Setoid
  Morphisms
  Relations.

From ITree Require Import
  Basics.Basics
  Basics.Utils
  Basics.HeterogeneousRelations.

From ITree Require Import
  Basics.HeterogeneousRelations
  Core.ITreeDefinition
  Eq.Eqit
  Sum.

From ITreeSpec Require Import
  Padded
  ITreeSpecDefinition.

From Paco Require Import paco.

Local Open Scope itree_scope.

Section mrec.
Context {D E : Type -> Type}.
Context (bodies : forall X, itree (D +' E) X).
CoFixpoint interp_mrec' {R} (ot : itree' (D +' E) R) : itree E R :=
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (interp_mrec' (observe t) )
  | VisF ((inl1 d)) k => Tau (interp_mrec' (observe (ITree.bind (@bodies _) k )) )
  | VisF ((inr1 e)) k => Vis e (fun x => interp_mrec' (observe (k x))) 
  end.
Definition interp_mrec {R} (t : itree (D +' E) R) : itree E R :=
  interp_mrec' (observe t).
Definition mrec {X} := interp_mrec (bodies X).

End mrec.

Section mrec_spec.
Context {D E : Type -> Type}.
Context (bodies : forall X, itree_spec (D +' E) X).
CoFixpoint interp_mrec_spec' {R} (ot : itree_spec' (D +' E) R) : itree_spec E R :=
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (interp_mrec_spec' (observe t) )
  | VisF (Spec_vis (inl1 d)) k => Tau (interp_mrec_spec' (observe (ITree.bind (bodies _) k )) )
  | VisF (Spec_vis (inr1 e)) k => Vis (Spec_vis e) (fun x => interp_mrec_spec' (observe (k x))) 
  | VisF (Spec_forall _) k => Vis (@Spec_forall E _) (fun x => interp_mrec_spec' (observe (k x)))
  | VisF (Spec_exists _) k => Vis (@Spec_exists E _) (fun x => interp_mrec_spec' (observe (k x)))
end.
Definition interp_mrec_spec {R} (t : itree_spec (D +' E) R) : itree_spec E R :=
  interp_mrec_spec' (observe t).
Definition mrec_spec X := interp_mrec_spec (bodies X).

End mrec_spec.

(* Variant callE (A B : Type@{itree_u}) : Type@{itree_u} := Call (a : A). *)
(* #[global] Instance callE_encodes {A B} : EncodingType (callE A B) := *)
(*   fun _ => B. *)
