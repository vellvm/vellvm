From ITree Require Import
     ITree.

From Vellvm Require Import
     Util
     UndefinedBehaviour
     Failure
     DynamicValues
     LLVMEvents.

(* Refinement of uninterpreted mcfg *)

Definition refine_MCFG: relation (LLVM _CFG uvalue) := eutt

(* Refinement of mcfg after locals *)

(* Refinement of mcfg after locals *)

Inductive refine_uvalue: uvalue -> uvalue -> Prop :=
| UndefPoison: refine_uvalue Uvalue_U
