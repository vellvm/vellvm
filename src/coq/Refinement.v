From ITree Require Import
     ITree
     Eq.Eq.

From Vellvm Require Import
     Util
     UndefinedBehaviour
     Failure
     DynamicValues
     MemoryAddress
     LLVMEvents.

From Coq Require Import Relations.


Module Make(A:MemoryAddress.ADDRESS)(LLVMIO: LLVM_INTERACTIONS(A)).

Import LLVMIO.

Variable global_env : Type.
Variable local_env : Type.
Variable stack : Type.
Variable memory : Type.
Variable refine_mem : relation memory.

(* Refinement relation for uvalues *)
Inductive refine_uvalue: uvalue -> uvalue -> Prop :=
| UndefPoison: forall t, refine_uvalue (UVALUE_Undef t) UVALUE_Poison (* CB / YZ: TODO, type for poison? *)
| RefineConcrete: forall uv1 uv2, (forall dv, concretize uv1 dv -> concretize uv2 dv) -> refine_uvalue uv1 uv2
.

Definition prod_rel {A B} (RA : relation A) (RB : relation B) : relation (A * B)
  := fun '(a,b) '(a', b') => RA a a' /\ RB b b'.

Infix "×" := prod_rel (at level 90, left associativity).

Definition TT {A} : relation A := fun _ _ => True.

(* Refinement of uninterpreted mcfg *)
Definition refine_MCFG: relation (LLVM _CFG uvalue) := eutt refine_uvalue.

(* Refinement of mcfg after globals *)
Definition refine_res1 : relation (global_env * uvalue)
  := TT × refine_uvalue.

Definition refine_MCFG1 : relation (LLVM _MCFG1 (global_env * uvalue))
  := eutt refine_res1.

(* Refinement of mcfg after locals *)
Definition refine_res2 : relation (local_env * stack * (global_env * uvalue))
  := TT × refine_res1.

Definition refine_MCFG2 : relation (LLVM _MCFG2 (local_env * stack * (global_env * uvalue)))
  := eutt refine_res2.

(* For multiple CFG, after interpreting [LocalE] and [MemoryE] and [IntrinsicE] that are memory intrinsics *)
Definition refine_res3 : relation (memory * (local_env * stack * (global_env * uvalue)))
  := refine_mem × refine_res2.

Definition refine_MCFG3 : relation (LLVM _MCFG3 (memory * (local_env * stack * (global_env * uvalue))))
  := eutt refine_res3.

(* Refinement for after interpreting pick. *)
Definition refine_MCFG4 : relation ((LLVM _MCFG4 (memory * (local_env * stack * (global_env * uvalue)))) -> Prop)
  := fun ts ts' => forall t, ts t -> exists t', ts' t' /\ eutt refine_res3 t t'.

End Make.
