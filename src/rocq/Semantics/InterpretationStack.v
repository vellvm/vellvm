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

    (* TODO: just make these types, instead of duplicating the definitions? *)
    Definition interp_mcfg1 {R} (t: itree L0 R) g : itree L1 (global_env * R) :=
      let dvalue_trace       := interp_intrinsics t in
      let L1_trace           := interp_global dvalue_trace g in
      L1_trace.

    Definition interp_mcfg2 {R} (t: itree L0 R) (g : global_env) (l : stack_frame * stack) : itree L2 (stack_frame * stack * (global_env * R)) :=
      let L1_trace       := interp_mcfg1 t g in
      let L2_trace       := interp_local_stack L1_trace l in
      L2_trace.

    Definition interp_mcfg3 {R} (t: itree L0 R) (g : global_env) (l : stack_frame * stack) (m : state) :
      itree L3 (state * (stack_frame * stack * (global_env * R))) :=
      let L2_trace       := interp_mcfg2 t g l in
      let L3_trace       := interp_memory L2_trace m in
      L3_trace.

    Definition interp_mcfg4 {R} (t: itree L0 R) (g : global_env) (l : stack_frame * stack) (m : state) :
      itree L4 (state * (stack_frame * stack * (global_env * R))) :=
      let L3_trace       := interp_mcfg3 t g l m in
      let L4_trace       := interp_draw L3_trace in
      L4_trace.
    
End withParams.
