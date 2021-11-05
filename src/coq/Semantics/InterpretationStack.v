(* begin hide *)
From ITree Require Import
     ITree
     Basics.Monad
     Events.StateFacts
     Eq.Eq.

From Vellvm Require Import
     Utilities
     Syntax
     Semantics.LLVMEvents
     Semantics.Denotation
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof
     Semantics.Lang
     Semantics.LLVMParams.

From Vellvm.Handlers Require Export
     Global
     Local
     Stack
     Intrinsics
     FiniteMemory
     FiniteMemoryTheory
     Pick
     UndefinedBehaviour
     OOM
     Serialization.

(* end hide *)

Module Type InterpreterStack.
  Declare Module LP : LLVMParams.
  Module LLVM := Lang.Make LP.

  Export LLVM.Events.
  Export LLVM.Intrinsics.
  Export LLVM.MEM.
  Export LLVM.Pick.
  Export LLVM.Global.
  Export LLVM.Local.
  Export LLVM.Stack.
  Export LLVM.D.

  Section InterpreterMCFG.

    (**
   Partial interpretations of the trees produced by the denotation of _VIR_ programs.
   The intent is to allow us to only interpret as many layers as needed
   to perform the required semantic reasoning, and lift for free the
   equivalence down the pipe.
   This gives us a _vertical_ notion of compositionality.
     *)

    (* TODO: just make these types, instead of duplicating the definitions? *)
    Definition interp_mcfg1 {R} (t: itree L0 R) g : itree L1 (global_env * R) :=
      let uvalue_trace       := interp_intrinsics t in
      let L1_trace           := interp_global uvalue_trace g in
      L1_trace.

    Definition interp_mcfg2 {R} (t: itree L0 R) g l : itree L2 (local_env * stack * (global_env * R)) :=
      let uvalue_trace   := interp_intrinsics t in
      let L1_trace       := interp_global uvalue_trace g in
      let L2_trace       := interp_local_stack L1_trace l in
      L2_trace.

    Definition interp_mcfg3 {R} (t: itree L0 R) g l m : itree L3 (MemState * (local_env * stack * (global_env * R))) :=
      let uvalue_trace   := interp_intrinsics t in
      let L1_trace       := interp_global uvalue_trace g in
      let L2_trace       := interp_local_stack L1_trace l in
      let L3_trace       := interp_memory L2_trace m in
      L3_trace.

    Definition interp_mcfg4 {R} RR (t: itree L0 R) g l m : PropT L4 (MemState * (local_env * stack * (global_env * R))) :=
      let uvalue_trace   := interp_intrinsics t in
      let L1_trace       := interp_global uvalue_trace g in
      let L2_trace       := interp_local_stack L1_trace l in
      let L3_trace       := interp_memory L2_trace m in
      let L4_trace       := model_undef RR L3_trace in
      L4_trace.

    Definition interp_mcfg5 {R} RR (t: itree L0 R) g l m : PropT L5 (MemState * (local_env * stack * (global_env * R))) :=
      let uvalue_trace   := interp_intrinsics t in
      let L1_trace       := interp_global uvalue_trace g in
      let L2_trace       := interp_local_stack L1_trace l in
      let L3_trace       := interp_memory L2_trace m in
      let L4_trace       := model_undef RR L3_trace in
      let L5_trace_no_msgs := PropT_itree_map (@remove_OOM_msg _ _ _) L4_trace in
      let L5_trace := model_OOM L5_trace_no_msgs in
      L5_trace.

    Definition interp_mcfg6 {R} RR (t: itree L0 R) g l m : PropT L6 (MemState * (local_env * stack * (global_env * R))) :=
      let uvalue_trace   := interp_intrinsics t in
      let L1_trace       := interp_global uvalue_trace g in
      let L2_trace       := interp_local_stack L1_trace l in
      let L3_trace       := interp_memory L2_trace m in
      let L4_trace       := model_undef RR L3_trace in
      let L5_trace       := PropT_itree_map (@model_OOM _ _ _) L4_trace in
      model_UB RR L5_trace.

    (* The interpreter stray away from the model starting from the fourth layer: we pick an arbitrary valid path of execution *)
    Definition interp_mcfg4_exec {R} (t: itree L0 R) g l m : itree L4 (MemState * (local_env * stack * (global_env * R))) :=
      let uvalue_trace   := interp_intrinsics t in
      let L1_trace       := interp_global uvalue_trace g in
      let L2_trace       := interp_local_stack L1_trace l in
      let L3_trace       := interp_memory L2_trace m in
      let L4_trace       := exec_undef L3_trace in
      L4_trace.

    Definition interp_mcfg5_exec {R} (t: itree L0 R) g l m : itree L5_exec (MemState * (local_env * stack * (global_env * R))) :=
      let uvalue_trace   := interp_intrinsics t in
      let L1_trace       := interp_global uvalue_trace g in
      let L2_trace       := interp_local_stack L1_trace l in
      let L3_trace       := interp_memory L2_trace m in
      let L4_trace       := exec_undef L3_trace in
      let L5_trace       := exec_OOM L4_trace in
      L5_trace.

    Definition interp_mcfg6_exec {R} (t: itree L0 R) g l m : itree L6_exec (MemState * (local_env * stack * (global_env * R))) :=
      let uvalue_trace   := interp_intrinsics t in
      let L1_trace       := interp_global uvalue_trace g in
      let L2_trace       := interp_local_stack L1_trace l in
      let L3_trace       := interp_memory L2_trace m in
      let L4_trace       := exec_undef L3_trace in
      let L5_trace       := exec_OOM L4_trace in
      let L6_trace       := exec_UB L5_trace in
      L6_trace.

  End InterpreterMCFG.

  Section InterpreterCFG.

    (**
   Partial interpretations of the trees produced by the
   denotation of cfg. They differ from the ones of Vellvm programs by
   their event signature, as well as by the lack of a stack of local event.
   The intent is to allow us to only interpret as many layers as needed
   to perform the required semantic reasoning, and lift for free the
   equivalence down the pipe.
   This gives us a _vertical_ notion of compositionality.
     *)

    (**
   NOTE: Can we avoid this duplication w.r.t. [interpi]?
     *)

    Definition interp_cfg1 {R} (t: itree instr_E R) (g: global_env) : itree (CallE +' IntrinsicE +' LLVMEnvE +' MemoryE +' PickE +' OOME +' UBE +' DebugE +' FailureE) (global_env * R) :=
      let L0_trace       := interp_intrinsics t in
      let L1_trace       := interp_global L0_trace g in
      L1_trace.

    Definition interp_cfg2 {R} (t: itree instr_E R) (g: global_env) (l: local_env) : itree (CallE +' IntrinsicE +' MemoryE +' PickE +' OOME +' UBE +' DebugE +' FailureE) (local_env * (global_env * R)) :=
      let L0_trace       := interp_intrinsics t in
      let L1_trace       := interp_global L0_trace g in
      let L2_trace       := interp_local L1_trace l in
      L2_trace.

    Definition interp_cfg3 {R} (t: itree instr_E R) (g: global_env) (l: local_env) (m: MemState) : itree (CallE +' PickE +' OOME +' UBE +' DebugE +' FailureE) (MemState * (local_env * (global_env * R))) :=
      let L0_trace       := interp_intrinsics t in
      let L1_trace       := interp_global L0_trace g in
      let L2_trace       := interp_local L1_trace l in
      let L3_trace       := interp_memory L2_trace m in
      L3_trace.

    Definition interp_cfg4 {R} RR (t: itree instr_E R) (g: global_env) (l: local_env) (m: MemState) : PropT (CallE +' OOME +' UBE +' DebugE +' FailureE) (MemState * (local_env * (global_env * R))) :=
      let L0_trace       := interp_intrinsics t in
      let L1_trace       := interp_global L0_trace g in
      let L2_trace       := interp_local L1_trace l in
      let L3_trace       := interp_memory L2_trace m in
      let L4_trace       := model_undef RR L3_trace in
      L4_trace.

    Definition interp_cfg5 {R} RR (t: itree instr_E R) (g: global_env) (l: local_env) (m: MemState) : PropT (CallE +' OOME_NOMSG +' UBE +' DebugE +' FailureE) (MemState * (local_env * (global_env * R))) :=
      let L0_trace       := interp_intrinsics t in
      let L1_trace       := interp_global L0_trace g in
      let L2_trace       := interp_local L1_trace l in
      let L3_trace       := interp_memory L2_trace m in
      let L4_trace       := model_undef RR L3_trace in
      PropT_itree_map (@model_OOM _ _ _) L4_trace.

    Definition interp_cfg6 {R} RR (t: itree instr_E R) (g: global_env) (l: local_env) (m: MemState) : PropT (CallE +' OOME_NOMSG +' DebugE +' FailureE) (MemState * (local_env * (global_env * R))) :=
      let L0_trace       := interp_intrinsics t in
      let L1_trace       := interp_global L0_trace g in
      let L2_trace       := interp_local L1_trace l in
      let L3_trace       := interp_memory L2_trace m in
      let L4_trace       := model_undef RR L3_trace in
      let L5_trace       := PropT_itree_map (@model_OOM _ _ _) L4_trace in
      model_UB RR L5_trace.

  End InterpreterCFG.

  Module SemNotations.

    Notation ℑ1 := interp_cfg1.
    Notation ℑ2 := interp_cfg2.
    Notation ℑ3 := interp_cfg3.
    Notation ℑ4 := interp_cfg4.
    Notation ℑ5 := interp_cfg5.
    Notation ℑ6 := interp_cfg6.
    Notation ℑ  := interp_cfg6.

    Notation ℑs1 := interp_mcfg1.
    Notation ℑs2 := interp_mcfg2.
    Notation ℑs3 := interp_mcfg3.
    Notation ℑs4 := interp_mcfg4.
    Notation ℑs5 := interp_mcfg5.
    Notation ℑs6 := interp_mcfg6.
    Notation ℑs  := interp_mcfg6.

    Notation Ret1 g x     := (Ret (g,x)).
    Notation Ret2 g l x   := (Ret (l,(g,x))).
    Notation Ret3 g l m x := (Ret (m,(l,(g,x)))).

    Notation "⟦ e 'at?' t '⟧e'" :=  (denote_exp t e).
    Notation "⟦ e 'at' t '⟧e'" :=   (denote_exp (Some t) e).
    Notation "⟦ e '⟧e'" :=          (denote_exp None e).
    Notation "⟦ e 'at?' t '⟧e3'" := (ℑ3 (translate exp_to_instr ⟦ e at? t ⟧e)).
    Notation "⟦ e 'at' t '⟧e3'" :=  (ℑ3 (translate exp_to_instr ⟦ e at t ⟧e)).
    Notation "⟦ e '⟧e3'" :=         (ℑ3 (translate exp_to_instr ⟦ e ⟧e )).

    Notation "⟦ i '⟧i'" :=        (denote_instr i).
    Notation "⟦ i '⟧i3'" :=       (ℑ3 ⟦ i ⟧i).

    Notation "⟦ c '⟧c'" :=          (denote_code c).
    Notation "⟦ c '⟧c3'" :=         (ℑ3 ⟦ c ⟧c).

    Notation "⟦ t '⟧t'" :=        (denote_terminator t).
    Notation "⟦ t '⟧t3'" :=       (ℑ3 (translate exp_to_instr ⟦ t ⟧t)).

    Notation "⟦ phi '⟧Φ' from"  := (denote_phi from phi) (at level 0, from at next level).
    Notation "⟦ phi '⟧Φ3' from" := (ℑ3 (denote_phi from phi)) (at level 0, from at next level).

    Notation "⟦ phis '⟧Φs' from"  := (denote_phis from phis) (at level 0, from at next level).
    Notation "⟦ phis '⟧Φs3' from" := (ℑ3 (denote_phis from phis)) (at level 0, from at next level).

    Notation "⟦ bk '⟧b'" :=  (denote_block bk).
    Notation "⟦ bk '⟧b3' id" := (ℑ3 (⟦ bk ⟧b id)) (at level 0, id at next level).

    Notation "⟦ bks '⟧bs'"  := (denote_ocfg bks).
    Notation "⟦ bks '⟧bs3' ids" := (ℑ3 (denote_ocfg bks ids)) (at level 0, ids at next level).

    Notation "⟦ f '⟧cfg'"  := (denote_cfg f).
    Notation "⟦ f '⟧cfg3'" := (ℑ3 (denote_cfg f)).

    Notation "⟦ f '⟧f'"  := (denote_function f).

    Ltac intros3 := intros (? & ? & ? & ?).

  End SemNotations.
End InterpreterStack.


Module Make (LP' : LLVMParams) : InterpreterStack.
  Module LP := LP'.
  Export LP.

  Module LLVM := Lang.Make LP.

  Export LLVM.Events.
  Export LLVM.Intrinsics.
  Export LLVM.MEM.
  Export LLVM.Pick.
  Export LLVM.Global.
  Export LLVM.Local.
  Export LLVM.Stack.
  Export LLVM.D.

  
  Section InterpreterMCFG.

    (**
   Partial interpretations of the trees produced by the denotation of _VIR_ programs.
   The intent is to allow us to only interpret as many layers as needed
   to perform the required semantic reasoning, and lift for free the
   equivalence down the pipe.
   This gives us a _vertical_ notion of compositionality.
     *)

    Definition interp_mcfg1 {R} (t: itree L0 R) g : itree L1 (global_env * R) :=
      let uvalue_trace       := interp_intrinsics t in
      let L1_trace           := interp_global uvalue_trace g in
      L1_trace.

    Definition interp_mcfg2 {R} (t: itree L0 R) g l : itree L2 (local_env * stack * (global_env * R)) :=
      let uvalue_trace   := interp_intrinsics t in
      let L1_trace       := interp_global uvalue_trace g in
      let L2_trace       := interp_local_stack L1_trace l in
      L2_trace.

    Definition interp_mcfg3 {R} (t: itree L0 R) g l m : itree L3 (MemState * (local_env * stack * (global_env * R))) :=
      let uvalue_trace   := interp_intrinsics t in
      let L1_trace       := interp_global uvalue_trace g in
      let L2_trace       := interp_local_stack L1_trace l in
      let L3_trace       := interp_memory L2_trace m in
      L3_trace.

    Definition interp_mcfg4 {R} RR (t: itree L0 R) g l m : PropT L4 (MemState * (local_env * stack * (global_env * R))) :=
      let uvalue_trace   := interp_intrinsics t in
      let L1_trace       := interp_global uvalue_trace g in
      let L2_trace       := interp_local_stack L1_trace l in
      let L3_trace       := interp_memory L2_trace m in
      let L4_trace       := model_undef RR L3_trace in
      L4_trace.

    Definition interp_mcfg5 {R} RR (t: itree L0 R) g l m : PropT L5 (MemState * (local_env * stack * (global_env * R))) :=
      let uvalue_trace   := interp_intrinsics t in
      let L1_trace       := interp_global uvalue_trace g in
      let L2_trace       := interp_local_stack L1_trace l in
      let L3_trace       := interp_memory L2_trace m in
      let L4_trace       := model_undef RR L3_trace in
      PropT_itree_map (@model_OOM _ _ _) L4_trace. 

    Definition interp_mcfg6 {R} RR (t: itree L0 R) g l m : PropT L6 (MemState * (local_env * stack * (global_env * R))) :=
      let uvalue_trace   := interp_intrinsics t in
      let L1_trace       := interp_global uvalue_trace g in
      let L2_trace       := interp_local_stack L1_trace l in
      let L3_trace       := interp_memory L2_trace m in
      let L4_trace       := model_undef RR L3_trace in
      let L5_trace       := PropT_itree_map (@model_OOM _ _ _) L4_trace in
      model_UB RR L5_trace.

    (* The interpreter stray away from the model starting from the fourth layer: we pick an arbitrary valid path of execution *)
    Definition interp_mcfg4_exec {R} (t: itree L0 R) g l m : itree L4 (MemState * (local_env * stack * (global_env * R))) :=
      let uvalue_trace   := interp_intrinsics t in
      let L1_trace       := interp_global uvalue_trace g in
      let L2_trace       := interp_local_stack L1_trace l in
      let L3_trace       := interp_memory L2_trace m in
      let L4_trace       := exec_undef L3_trace in
      L4_trace.

    Definition interp_mcfg5_exec {R} (t: itree L0 R) g l m : itree L5_exec (MemState * (local_env * stack * (global_env * R))) :=
      let uvalue_trace   := interp_intrinsics t in
      let L1_trace       := interp_global uvalue_trace g in
      let L2_trace       := interp_local_stack L1_trace l in
      let L3_trace       := interp_memory L2_trace m in
      let L4_trace       := exec_undef L3_trace in
      let L5_trace       := exec_OOM L4_trace in
      L5_trace.

    Definition interp_mcfg6_exec {R} (t: itree L0 R) g l m : itree L6_exec (MemState * (local_env * stack * (global_env * R))) :=
      let uvalue_trace   := interp_intrinsics t in
      let L1_trace       := interp_global uvalue_trace g in
      let L2_trace       := interp_local_stack L1_trace l in
      let L3_trace       := interp_memory L2_trace m in
      let L4_trace       := exec_undef L3_trace in
      let L5_trace       := exec_OOM L4_trace in
      let L6_trace       := exec_UB L5_trace in
      L6_trace.

  End InterpreterMCFG.

  Section InterpreterCFG.

    (**
   Partial interpretations of the trees produced by the
   denotation of cfg. They differ from the ones of Vellvm programs by
   their event signature, as well as by the lack of a stack of local event.
   The intent is to allow us to only interpret as many layers as needed
   to perform the required semantic reasoning, and lift for free the
   equivalence down the pipe.
   This gives us a _vertical_ notion of compositionality.
     *)

    (**
   NOTE: Can we avoid this duplication w.r.t. [interpi]?
     *)

    Definition interp_cfg1 {R} (t: itree instr_E R) (g: global_env) : itree (CallE +' IntrinsicE +' LLVMEnvE +' MemoryE +' PickE +' OOME +' UBE +' DebugE +' FailureE) (global_env * R) :=
      let L0_trace       := interp_intrinsics t in
      let L1_trace       := interp_global L0_trace g in
      L1_trace.

    Definition interp_cfg2 {R} (t: itree instr_E R) (g: global_env) (l: local_env) : itree (CallE +' IntrinsicE +' MemoryE +' PickE +' OOME +' UBE +' DebugE +' FailureE) (local_env * (global_env * R)) :=
      let L0_trace       := interp_intrinsics t in
      let L1_trace       := interp_global L0_trace g in
      let L2_trace       := interp_local L1_trace l in
      L2_trace.

    Definition interp_cfg3 {R} (t: itree instr_E R) (g: global_env) (l: local_env) (m: MemState) : itree (CallE +' PickE +' OOME +' UBE +' DebugE +' FailureE) (MemState * (local_env * (global_env * R))) :=
      let L0_trace       := interp_intrinsics t in
      let L1_trace       := interp_global L0_trace g in
      let L2_trace       := interp_local L1_trace l in
      let L3_trace       := interp_memory L2_trace m in
      L3_trace.

    Definition interp_cfg4 {R} RR (t: itree instr_E R) (g: global_env) (l: local_env) (m: MemState) : PropT (CallE +' OOME +' UBE +' DebugE +' FailureE) (MemState * (local_env * (global_env * R))) :=
      let L0_trace       := interp_intrinsics t in
      let L1_trace       := interp_global L0_trace g in
      let L2_trace       := interp_local L1_trace l in
      let L3_trace       := interp_memory L2_trace m in
      let L4_trace       := model_undef RR L3_trace in
      L4_trace.

    Definition interp_cfg5 {R} RR (t: itree instr_E R) (g: global_env) (l: local_env) (m: MemState) : PropT (CallE +' OOME_NOMSG +' UBE +' DebugE +' FailureE) (MemState * (local_env * (global_env * R))) :=
      let L0_trace       := interp_intrinsics t in
      let L1_trace       := interp_global L0_trace g in
      let L2_trace       := interp_local L1_trace l in
      let L3_trace       := interp_memory L2_trace m in
      let L4_trace       := model_undef RR L3_trace in
      PropT_itree_map (@model_OOM _ _ _) L4_trace.

    Definition interp_cfg6 {R} RR (t: itree instr_E R) (g: global_env) (l: local_env) (m: MemState) : PropT (CallE +' OOME_NOMSG +' DebugE +' FailureE) (MemState * (local_env * (global_env * R))) :=
      let L0_trace       := interp_intrinsics t in
      let L1_trace       := interp_global L0_trace g in
      let L2_trace       := interp_local L1_trace l in
      let L3_trace       := interp_memory L2_trace m in
      let L4_trace       := model_undef RR L3_trace in
      let L5_trace       := PropT_itree_map (@model_OOM _ _ _) L4_trace in
      model_UB RR L5_trace.

  End InterpreterCFG.

  Module SemNotations.

    Notation ℑ1 := interp_cfg1.
    Notation ℑ2 := interp_cfg2.
    Notation ℑ3 := interp_cfg3.
    Notation ℑ4 := interp_cfg4.
    Notation ℑ5 := interp_cfg5.
    Notation ℑ6 := interp_cfg6.
    Notation ℑ  := interp_cfg6.

    Notation ℑs1 := interp_mcfg1.
    Notation ℑs2 := interp_mcfg2.
    Notation ℑs3 := interp_mcfg3.
    Notation ℑs4 := interp_mcfg4.
    Notation ℑs5 := interp_mcfg5.
    Notation ℑs6 := interp_mcfg6.
    Notation ℑs  := interp_mcfg6.

    Notation Ret1 g x     := (Ret (g,x)).
    Notation Ret2 g l x   := (Ret (l,(g,x))).
    Notation Ret3 g l m x := (Ret (m,(l,(g,x)))).

    Notation "⟦ e 'at?' t '⟧e'" :=  (denote_exp t e).
    Notation "⟦ e 'at' t '⟧e'" :=   (denote_exp (Some t) e).
    Notation "⟦ e '⟧e'" :=          (denote_exp None e).
    Notation "⟦ e 'at?' t '⟧e3'" := (ℑ3 (translate exp_to_instr ⟦ e at? t ⟧e)).
    Notation "⟦ e 'at' t '⟧e3'" :=  (ℑ3 (translate exp_to_instr ⟦ e at t ⟧e)).
    Notation "⟦ e '⟧e3'" :=         (ℑ3 (translate exp_to_instr ⟦ e ⟧e )).

    Notation "⟦ i '⟧i'" :=        (denote_instr i).
    Notation "⟦ i '⟧i3'" :=       (ℑ3 ⟦ i ⟧i).

    Notation "⟦ c '⟧c'" :=          (denote_code c).
    Notation "⟦ c '⟧c3'" :=         (ℑ3 ⟦ c ⟧c).

    Notation "⟦ t '⟧t'" :=        (denote_terminator t).
    Notation "⟦ t '⟧t3'" :=       (ℑ3 (translate exp_to_instr ⟦ t ⟧t)).

    Notation "⟦ phi '⟧Φ' from"  := (denote_phi from phi) (at level 0, from at next level).
    Notation "⟦ phi '⟧Φ3' from" := (ℑ3 (denote_phi from phi)) (at level 0, from at next level).

    Notation "⟦ phis '⟧Φs' from"  := (denote_phis from phis) (at level 0, from at next level).
    Notation "⟦ phis '⟧Φs3' from" := (ℑ3 (denote_phis from phis)) (at level 0, from at next level).

    Notation "⟦ bk '⟧b'" :=  (denote_block bk).
    Notation "⟦ bk '⟧b3' id" := (ℑ3 (⟦ bk ⟧b id)) (at level 0, id at next level).

    Notation "⟦ bks '⟧bs'"  := (denote_ocfg bks).
    Notation "⟦ bks '⟧bs3' ids" := (ℑ3 (denote_ocfg bks ids)) (at level 0, ids at next level).

    Notation "⟦ f '⟧cfg'"  := (denote_cfg f).
    Notation "⟦ f '⟧cfg3'" := (ℑ3 (denote_cfg f)).

    Notation "⟦ f '⟧f'"  := (denote_function f).

    Ltac intros3 := intros (? & ? & ? & ?).

  End SemNotations.
End Make.

Module InterpreterStackBigIntptr := Make LLVMParamsBigIntptr.
Module InterpreterStack64BitIntptr := Make LLVMParams64BitIntptr.
