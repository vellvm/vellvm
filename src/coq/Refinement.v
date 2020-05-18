From ITree Require Import
     ITree
     Basics
     Eq.Eq.

From Vellvm Require Import
     Util
     UndefinedBehaviour
     DynamicValues
     MemoryAddress
     LLVMEvents
     LLVMAst
     Handlers.Handlers.

From Coq Require Import Relations RelationClasses.

Module Make (A:MemoryAddress.ADDRESS)(LLVMEvents: LLVM_INTERACTIONS(A)).

Import LLVMEvents.
Import DV.

(* Refinement relation for uvalues *)
Inductive refine_uvalue: uvalue -> uvalue -> Prop :=
| UndefPoison: forall t, refine_uvalue (UVALUE_Undef t) UVALUE_Poison (* CB / YZ: TODO, type for poison? *)
| RefineConcrete: forall uv1 uv2, (forall dv, concretize uv1 dv -> concretize uv2 dv) -> refine_uvalue uv1 uv2
.
Hint Constructors refine_uvalue : core.

Instance refine_uvalue_Reflexive : Reflexive refine_uvalue.
Proof.
  repeat intro; auto.
Qed.

(* YZ: The following is unlikely to be useful I believe. *)
(*
Inductive refine_dvalue: dvalue -> dvalue -> Prop :=
| DvalueRefl : forall v, refine_dvalue v v
| Poison : forall v, refine_dvalue v DVALUE_Poison
.

Instance refine_dvalue_Reflexive : Reflexive refine_dvalue.
Proof.
  unfold Reflexive. intros x.
  induction x; constructor; auto.
Qed.
 *)

Infix "×" := prod_rel (at level 90, left associativity).

Definition TT {A} : relation A := fun _ _ => True.

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
  := fun ts ts' => forall t, ts t -> exists t', ts' t' /\ eutt refine_res3 t t'.

(*
Definition refine_res4 : relation (memory * (local_env * stack * (global_env * dvalue)))
  := TT × (TT × (TT × refine_dvalue)).
 *)

Definition refine_L5 : relation ((itree L5 (memory_stack * (local_env * stack * (global_env * uvalue)))) -> Prop)
  := fun ts ts' => forall t, ts t -> exists t', ts' t' /\ eutt refine_res3 t t'.

End Make.
