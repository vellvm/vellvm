(* begin hide *)
From ITree Require Import
     ITree
     Basics
     Basics.HeterogeneousRelations
     Eq.Eqit.

From Vellvm Require Import
     Utilities
     Syntax
     Semantics.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.EitherMonad
     Structures.Functor.


From Coq Require Import Relations RelationClasses.
(* end hide *)

Module Make (A:MemoryAddress.ADDRESS)(LLVMEvents: LLVM_INTERACTIONS(A)).

Import LLVMEvents.
Import DV.

(* Refinement relation for uvalues *)
(* Definition 5.6 UValue refinement *)
Variant refine_uvalue: uvalue -> uvalue -> Prop :=
| UndefPoison: forall uv, refine_uvalue UVALUE_Poison uv   
| RefineConcrete: forall uv1 uv2, uv2 <> UVALUE_Poison -> (forall (dv:dvalue), concretize uv2 dv -> concretize uv1  dv) -> refine_uvalue uv1 uv2
.
#[export] Hint Constructors refine_uvalue : core.

#[global] Instance refine_uvalue_Reflexive : Reflexive refine_uvalue.
Proof.
  repeat intro.
  destruct x; try (apply RefineConcrete;[intro; inversion H|auto];fail).
  apply UndefPoison.
Qed.

Lemma refine_poison : forall uv, refine_uvalue uv UVALUE_Poison -> uv = UVALUE_Poison.
Proof.
  intros.
  inv H.
  - reflexivity.
  - contradiction H0.
    reflexivity.
Qed.

#[global] Instance refine_uvalue_Transitive : Transitive refine_uvalue.
Proof.
  repeat intro.
  inversion H; subst.
  - inversion H0; subst.
    econstructor.
    econstructor.
  - inversion H0; subst.
    apply refine_poison in H. subst. econstructor.
    apply RefineConcrete. intros. assumption. auto. 
Qed.

Infix"×" := prod_rel (at level 90, left associativity).

Definition TT {A} : relation A := fun _ _ => True.

(* Lemma 5.7 - uses this definition of refinement 
   note that refine_uvalue is the basic Uvalue refinement given by Definition 5.6 *)
(* Refinement of uninterpreted mcfg *)
Definition refine_L0: relation (itree L0 uvalue) := eutt refine_uvalue.

(* Refinement of mcfg after globals *)
Definition refine_res1 : relation (global_env * uvalue)
  := TT × refine_uvalue.

Definition refine_L1 : relation (itree L1 (global_env * uvalue))
  := eutt refine_res1.

(* Refinement of mcfg after locals *)
Definition refine_res2 : relation (local_env * lstack * (global_env * uvalue))
  := TT × refine_res1.

Definition refine_L2 : relation (itree L2 (local_env * stack * (global_env * uvalue)))
  := eutt refine_res2.

(* For multiple CFG, after interpreting [LocalE] and [MemoryE] and [IntrinsicE] that are memory intrinsics *)
Definition refine_res3 : relation (memory_stack * (local_env * stack * (global_env * uvalue)))
  := TT × refine_res2.

Definition refine_L3 : relation (itree L3 (memory_stack * (local_env * stack * (global_env * uvalue))))
  := eutt refine_res3.

(* Refinement for after interpreting pick. *)
Definition refine_L4 : relation ((itree L4 (memory_stack * (local_env * stack * (global_env * uvalue)))) -> Prop)
  := fun ts ts' => forall t', ts' t' -> exists t, ts t /\ eutt refine_res3 t t'.

Inductive contains_UB {R} : itree L4 R -> Prop :=
| CrawlTau  : forall t, contains_UB t -> contains_UB (Tau t)
| CrawlVis1 : forall Y (e : ExternalCallE Y) x k, contains_UB (k x) -> contains_UB (vis e k)
| CrawlVis2 : forall Y (e : (DebugE +' FailureE) Y) x k, contains_UB (k x) -> contains_UB (vis e k)
| FindUB    : forall s, contains_UB (raiseUB s).

Definition refine_L5 : relation ((itree L4 (memory_stack * (local_env * stack * (global_env * uvalue)))) -> Prop)
  := fun ts ts' => 
      forall t', ts' t' -> 
        exists t, ts t /\ (contains_UB t \/ eutt refine_res3 t t').

End Make.
