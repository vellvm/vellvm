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
     Environment
     Handlers.Stack.

From Coq Require Import Relations.


Module Make(A:MemoryAddress.ADDRESS)(LLVMIO: LLVM_INTERACTIONS(A))(ENV: Environment).

Import LLVMIO.
Import LLVMIO.DV.
Import ENV.

(* Refinement relation for uvalues *)
Inductive refine_uvalue: uvalue -> uvalue -> Prop :=
| UndefPoison: forall t, refine_uvalue (UVALUE_Undef t) UVALUE_Poison (* CB / YZ: TODO, type for poison? *)
| RefineConcrete: forall uv1 uv2, (forall dv, concretize uv1 dv -> concretize uv2 dv) -> refine_uvalue uv1 uv2
.

Inductive refine_dvalue: dvalue -> dvalue -> Prop :=
| DvalueRefl : forall v, refine_dvalue v v
| Poison : forall v, refine_dvalue v DVALUE_Poison
.

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
Definition refine_res2 : relation (local_env * stack * (global_env * uvalue))
  := TT × refine_res1.

Definition refine_L2 : relation (itree L2 (local_env * stack * (global_env * uvalue)))
  := eutt refine_res2.

(* For multiple CFG, after interpreting [LocalE] and [MemoryE] and [IntrinsicE] that are memory intrinsics *)
Definition refine_res3 : relation (memory * (local_env * stack * (global_env * uvalue)))
  := TT × refine_res2.

Definition refine_L3 : relation (itree L3 (memory * (local_env * stack * (global_env * uvalue))))
  := eutt refine_res3.

(* Refinement for after interpreting pick. *)
Definition refine_L4 : relation ((itree L4 (memory * (local_env * stack * (global_env * uvalue)))) -> Prop)
  := fun ts ts' => forall t, ts t -> exists t', ts' t' /\ eutt refine_res3 t t'.

End Make.
