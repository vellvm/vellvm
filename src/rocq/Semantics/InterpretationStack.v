(* begin hide *)
From ITree Require Import
     ITree
     Basics.Monad
     Events.StateFacts
     Eq.Eqit.

From Vellvm Require Import
     Utilities
     Semantics.LLVMEvents
     Semantics.DynamicValues
     Params
     Params.Memory
     Params.VellvmImplem.Memory.

From Vellvm Require Import
  Handlers.
(* end hide *)

Section withParams.
  Context {Pa : Params}.
  Existing Instance MemoryModelPrimitivesV.
  
  (**
   Partial interpretations of the trees produced by the denotation of _VIR_ programs.
   The intent is to allow us to only interpret as many layers as needed
   to perform the required semantic reasoning, and lift for free the
   equivalence down the pipe.
   This gives us a _vertical_ notion of compositionality.
   *)

  Definition Res X := (state * (stack_frame * stack * (global_env * X)))%type.
  
  Definition interp_mcfg {R} (t: MCFGtop R) g l m : MCFGbot (Res R)  :=
    let t0 := interp_intrinsics t in
    let t1 := interp_global t0 g in
    let t2 := interp_local_stack t1 l in
    let t3 := interp_memory t2 m in
    interp_draw t3.

End withParams.
