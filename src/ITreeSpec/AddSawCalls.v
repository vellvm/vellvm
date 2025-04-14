From ITree Require Import
     Basics.Basics
     Basics.Utils
     Basics.HeterogeneousRelations
 .
From EnTree Require Import
     Basics.HeterogeneousRelations
     Core.EnTreeDefinition
     Core.SubEvent
     Eq.Eqit
     Ref.Padded
     Ref.EnTreeSpecDefinition
     Ref.MRecSpec
.

From Paco Require Import paco.

Local Open Scope entree_scope.
Local Open Scope list_scope.
Variant call_depE (A : Type) (B : A -> Type) : Type@{entree_u} := CallDep (a : A).
#[global] Instance call_depE_encodes A B : EncodedType (call_depE A B) :=
  fun c => match c with CallDep _ _ a => B a end.

Variant call_dep_type := 
  ct_intro (A : Type) (B : A -> Type).
Notation call_stack := (list call_dep_type).
Inductive call_var : call_stack -> call_dep_type -> Type :=
| VarZ  : forall (G:call_stack) t, call_var (t::G) t
| VarS  : forall (G:call_stack) u t,
    call_var G t -> call_var (u::G) t.


(* call_var is a function into Type entree_u +1*)

Definition call_dep_type_trans (c : call_dep_type) : Type@{entree_u} :=
  match c with ct_intro A B => call_depE A B end.

#[global] Instance call_dep_type_trans_encodes (C : call_dep_type) : 
  EncodedType (call_dep_type_trans C) :=
 match C as C' return (call_dep_type_trans C' -> Type) with
   ct_intro A B =>
     fun c => match c with CallDep _ _ a => B a end end.

Definition uncall {A B} (c : call_depE A B) : A :=
  match c with CallDep _ _ a => a end.

Section SpecM.
(*can't give SpecM E Γ A : Type entree_u, but that doesn't mean we can't 
  map into entree E R : Type entree_u*)

Inductive SpecM (E : Type) `{EncodedType E} : call_stack -> Type@{entree_u} -> Type := 
  | RetS Γ A (a : A) : SpecM E Γ A
  | BindS Γ A B : SpecM E Γ A -> (A -> SpecM E Γ B) -> SpecM E Γ B
  | IterS Γ A B : (A -> SpecM E Γ (A + B)) -> A -> SpecM E Γ B
  | CallS Γ A B (a : A) : SpecM E (ct_intro A B :: Γ) (B a)
  | MrecS Γ A B (bodies : forall a, SpecM E (ct_intro A B :: Γ) (B a) ) (a : A):
    SpecM E Γ (B a)
  | TriggerS Γ (e : E) : SpecM E Γ (encodes e)
  | AssumeS Γ (P : Prop) : SpecM E Γ unit
  | AssertS Γ (P : Prop) : SpecM E Γ unit
  | ForallS Γ (A : Set) : SpecM E Γ A
  | ExistsS Γ (A : Set) : SpecM E Γ A
.
(* I think there is an associativity issue here want + E to be at the top
   maybe the way to do that is have nil map to void and only add E at the top level
*)
Fixpoint denote_call_stack (E : Type) (Γ : call_stack) : Type :=
  match Γ with
  | nil => E
  | C :: Γ' => call_dep_type_trans C + denote_call_stack E Γ' end.
(*
Print Instances EncodedType.
Definition denote_call_ctx_encodes_ (E : Type) `{EncodedType E} (Γ : call_ctx) : 
  denote_call_ctx E Γ -> Type. *)

(* replace with sanely written one *)
#[global] Instance denote_call_ctx_encodes E `{EncodedType E} Γ : EncodedType (denote_call_stack E Γ).
induction Γ.
- exact encodes.
- simpl. apply EncodedSum. exact (call_dep_type_trans_encodes a).
  exact IHΓ.
Defined.
Print Instances ReSum.

#[global] Instance denote_call_ctx_resum E Γ : ReSum E (denote_call_stack E Γ).
induction Γ.
- simpl. intros e. exact e.
- simpl. intros e. apply ReSum_inr. exact (IHΓ e).
Defined.

#[global] Instance denote_call_ctx_resumret E Γ `{EncodedType E} : ReSumRet E (denote_call_stack E Γ).
induction Γ.
- simpl. intros e. unfold resum. intros x. exact x.
- simpl. intros e. apply IHΓ.
Defined.

Arguments RetS {_ _ _ _} _.
Arguments BindS {_ _ _ _ _} _ _.
Arguments IterS {_ _ _ _ _} _ _.
Arguments AssumeS {_ _ _}.
Arguments AssertS {_ _ _}.
Arguments ExistsS {_ _ _}.
Arguments ForallS {_ _ _}.
Arguments CallS {_ _ _} _ _ _.
Arguments MrecS {_ _ _ _ _} _ _.
Arguments TriggerS {_ _ _} _.

Fixpoint denote_SpecM (E : Type@{entree_u}) `{EncodedType E} Γ A (spec : SpecM E Γ A) : 
  entree_spec (denote_call_stack E Γ) A :=
  match spec with
  | RetS a => Ret a
  | BindS m k => EnTree.bind (denote_SpecM E _ _ m) (fun x => denote_SpecM E _ _ (k x))
  | IterS body a => EnTree.iter (fun x => denote_SpecM E _ _ (body x)) a
  | AssumeS P => assume_spec P
  | AssertS P => assert_spec P
  | ForallS A => forall_spec A
  | ExistsS A => exists_spec A
  | TriggerS e => trigger e
  | CallS _ B a => (EnTree.trigger (Spec_vis (inl (CallDep _ B a))))
  | MrecS bodies a => mrec_spec (fun c : call_depE _ _  => 
                         match c with CallDep _ _ a => denote_SpecM E _ _ (bodies a) end) 
                               (CallDep _ _ a)
  end.

End SpecM.
