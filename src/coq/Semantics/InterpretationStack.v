(* begin hide *)
From ITree Require Import
     ITree
     Basics.Monad
     Events.StateFacts
     Eq.Eqit.

From TwoPhase Require Import
     Utilities
     Semantics.LLVMEvents
     Semantics.Lang
     Semantics.LLVMParams
     Semantics.StoreId.

From TwoPhase.Handlers Require Export
     Global
     Local
     Stack
     Intrinsics
     MemoryModel
     MemoryModelImplementation
     MemPropT
     Pick
     OOM
     Concretization
     UndefinedBehaviour.

(* end hide *)

Module Type InterpreterStack_common (LP : LLVMParams) (MEM : Memory LP).
  Module LLVM := Lang.Make LP MEM.

  Import LP.Events.
  Import LP.PROV.
  Import LLVM.Intrinsics.
  Import MEM.MEM_MODEL.
  Import MEM.MMEP.MMSP.
  Import MEM.MMEP.MemExecM.
  Import MEM.MEM_EXEC_INTERP.
  Import MEM.MEM_SPEC_INTERP.
  Import MEM.GEP.
  Import LLVM.Pick.
  Import LLVM.Global.
  Import LLVM.Local.
  Import LLVM.Stack.
  Import LLVM.D.

  Section InterpreterMCFG.
    Context {MemM : Type -> Type}.
    Context `{MemMonad MemM}.

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

    Definition interp_mcfg3 {R} RR (t: itree L0 R) g l sid m : PropT L3 (MemState * (store_id * (local_env * @stack local_env * (global_env * R)))) :=
      let uvalue_trace   := interp_intrinsics t in
      let L1_trace       := interp_global uvalue_trace g in
      let L2_trace       := interp_local_stack L1_trace l in
      let L3_trace       := interp_memory_spec RR L2_trace sid m in
      L3_trace.

    Definition interp_mcfg3_exec {R} (t: itree L0 R) g l sid m : itree L3 (MemState * (store_id * (local_env * stack * (global_env * R)))) :=
      let uvalue_trace   := interp_intrinsics t in
      let L1_trace       := interp_global uvalue_trace g in
      let L2_trace       := interp_local_stack L1_trace l in
      let L3_trace       := interp_memory L2_trace sid m in
      L3_trace.

    Definition interp_mcfg4 {R} RR_mem RR_pick (t: itree L0 R) g l sid m : PropT L4 (MemState * (store_id * (local_env * @stack local_env * (global_env * R)))) :=
      let uvalue_trace   := interp_intrinsics t in
      let L1_trace       := interp_global uvalue_trace g in
      let L2_trace       := interp_local_stack L1_trace l in
      let L3_trace       := interp_memory_spec RR_mem L2_trace sid m in
      let L4_trace       := model_undef RR_pick L3_trace in
      L4_trace.

    Definition interp_mcfg4_exec {R} (t: itree L0 R) g l sid m : itree L4 (MemState * (store_id * (local_env * stack * (global_env * R)))) :=
      let uvalue_trace   := interp_intrinsics t in
      let L1_trace       := interp_global uvalue_trace g in
      let L2_trace       := interp_local_stack L1_trace l in
      let L3_trace       := interp_memory L2_trace sid m in
      let L4_trace       := exec_undef L3_trace in
      L4_trace.

    Definition interp_mcfg5 {R} RR_mem RR_pick (t: itree L0 R) g l sid m : PropT L5 (MemState * (store_id * (local_env * @stack local_env * (global_env * R)))) :=
      let uvalue_trace   := interp_intrinsics t in
      let L1_trace       := interp_global uvalue_trace g in
      let L2_trace       := interp_local_stack L1_trace l in
      let L3_trace       := interp_memory_spec RR_mem L2_trace sid m in
      let L4_trace       := model_undef RR_pick L3_trace in
      let L5_trace       := model_UB L4_trace in
      L5_trace.

    Definition interp_mcfg6 {R} RR_mem RR_pick RR_oom (t: itree L0 R) g l sid m : PropT L6 (MemState * (store_id * (local_env * @stack local_env * (global_env * R)))) :=
      let uvalue_trace   := interp_intrinsics t in
      let L1_trace       := interp_global uvalue_trace g in
      let L2_trace       := interp_local_stack L1_trace l in
      let L3_trace       := interp_memory_spec RR_mem L2_trace sid m in
      let L4_trace       := model_undef RR_pick L3_trace in
      let L5_trace       := model_UB L4_trace in
      let L6_trace       := refine_OOM RR_oom L5_trace in
      L6_trace.
  End InterpreterMCFG.

  Section InterpreterCFG.
    Context {MemM : Type -> Type}.
    Context `{MemMonad MemM}.

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

    Definition interp_cfg3 {R} RR (t: itree instr_E R) (g: global_env) (l: local_env) sid (m: MemState) : PropT (CallE +' PickE +' OOME +' UBE +' DebugE +' FailureE) (MemState * (store_id * (local_env * (global_env * R)))) :=
      let L0_trace       := interp_intrinsics t in
      let L1_trace       := interp_global L0_trace g in
      let L2_trace       := interp_local L1_trace l in
      let L3_trace       := interp_memory_spec RR L2_trace sid m in
      L3_trace.

    Definition interp_cfg3_exec {R} (t: itree instr_E R) (g: global_env) (l: local_env) sid (m: MemState) : itree (CallE +' PickE +' OOME +' UBE +' DebugE +' FailureE) (MemState * (store_id * (local_env * (global_env * R)))) :=
      let L0_trace       := interp_intrinsics t in
      let L1_trace       := interp_global L0_trace g in
      let L2_trace       := interp_local L1_trace l in
      let L3_trace       := interp_memory L2_trace sid m in
      L3_trace.

    Definition interp_cfg4 {R} RR_mem RR_pick (t: itree instr_E R) (g: global_env) (l: local_env) sid (m: MemState) : PropT (CallE +' OOME +' UBE +' DebugE +' FailureE) (MemState * (store_id * (local_env * (global_env * R)))) :=
      let L0_trace       := interp_intrinsics t in
      let L1_trace       := interp_global L0_trace g in
      let L2_trace       := interp_local L1_trace l in
      let L3_trace       := interp_memory_spec RR_mem L2_trace sid m in
      let L4_trace       := model_undef RR_pick L3_trace in
      L4_trace.

    Definition interp_cfg4_exec {R} (t: itree instr_E R) (g: global_env) (l: local_env) sid (m: MemState) : itree (CallE +' OOME +' UBE +' DebugE +' FailureE) (MemState * (store_id * (local_env * (global_env * R)))) :=
      let L0_trace       := interp_intrinsics t in
      let L1_trace       := interp_global L0_trace g in
      let L2_trace       := interp_local L1_trace l in
      let L3_trace       := interp_memory L2_trace sid m in
      let L4_trace       := exec_undef L3_trace in
      L4_trace.

    Definition interp_cfg5 {R} RR_mem RR_pick (t: itree instr_E R) (g: global_env) (l: local_env) sid (m: MemState) : PropT (CallE +' OOME +' UBE +' DebugE +' FailureE) (MemState * (store_id * (local_env * (global_env * R)))) :=
      let L0_trace       := interp_intrinsics t in
      let L1_trace       := interp_global L0_trace g in
      let L2_trace       := interp_local L1_trace l in
      let L3_trace       := interp_memory_spec RR_mem L2_trace sid m in
      let L4_trace       := model_undef RR_pick L3_trace in
      let L5_trace       := model_UB L4_trace in
      L5_trace.

    Definition interp_cfg6 {R} RR_mem RR_pick (t: itree instr_E R) (g: global_env) (l: local_env) sid (m: MemState) : PropT (CallE +' OOME +' UBE +' DebugE +' FailureE) (MemState * (store_id * (local_env * (global_env * R)))) :=
      let L0_trace       := interp_intrinsics t in
      let L1_trace       := interp_global L0_trace g in
      let L2_trace       := interp_local L1_trace l in
      let L3_trace       := interp_memory_spec RR_mem L2_trace sid m in
      let L4_trace       := model_undef RR_pick L3_trace in
      let L5_trace       := model_UB L4_trace in
      let L6_trace       := refine_OOM
                              (fun '(ms, (sid, (lenv, (genv, x))))
                                 '(ms', (sid', (lenv', (genv', y)))) =>
                                 x = y)
                              L5_trace in
      L6_trace.
  End InterpreterCFG.

  Module SemNotations.

    Notation ℑ1 := interp_cfg1.
    Notation ℑ2 := interp_cfg2.
    Notation ℑ3 := interp_cfg3.
    Notation ℑ4 := interp_cfg4.
    Notation ℑ5 := interp_cfg5.
    Notation ℑ6 := interp_cfg6.
    (* TODO: should probably switch to interp_cfg6 *)
    Notation ℑ  := interp_cfg5.

    Notation ℑs1 := interp_mcfg1.
    Notation ℑs2 := interp_mcfg2.
    Notation ℑs3 := interp_mcfg3.
    Notation ℑs4 := interp_mcfg4.
    Notation ℑs5 := interp_mcfg5.
    Notation ℑs6 := interp_mcfg6.
    (* TODO: should probably switch to interp_mcfg6 *)
    Notation ℑs  := interp_mcfg5.

    Notation Ret1 g x     := (Ret (g,x)).
    Notation Ret2 g l x   := (Ret (l,(g,x))).
    Notation Ret3 g l m x := (Ret (m,(l,(g,x)))).
    Notation Ret5 g l sid m x := (Ret (m,(sid,(l,(g,x))))).

    Notation "⟦ e 'at?' t '⟧e'" :=  (denote_exp t e).
    Notation "⟦ e 'at' t '⟧e'" :=   (denote_exp (Some t) e).
    Notation "⟦ e '⟧e'" :=          (denote_exp None e).
    Notation "⟦ e 'at?' t '⟧e1'" := (ℑ1 (translate exp_to_instr ⟦ e at? t ⟧e)).
    Notation "⟦ e 'at' t '⟧e1'" :=  (ℑ1 (translate exp_to_instr ⟦ e at t ⟧e)).
    Notation "⟦ e '⟧e1'" :=         (ℑ1 (translate exp_to_instr ⟦ e ⟧e )).
    Notation "⟦ e 'at?' t '⟧e2'" := (ℑ2 (translate exp_to_instr ⟦ e at? t ⟧e)).
    Notation "⟦ e 'at' t '⟧e2'" :=  (ℑ2 (translate exp_to_instr ⟦ e at t ⟧e)).
    Notation "⟦ e '⟧e2'" :=         (ℑ2 (translate exp_to_instr ⟦ e ⟧e )).
    Notation "⟦ e 'at?' t '⟧e3'" := (ℑ3 (translate exp_to_instr ⟦ e at? t ⟧e)).
    Notation "⟦ e 'at' t '⟧e3'" :=  (ℑ3 (translate exp_to_instr ⟦ e at t ⟧e)).
    Notation "⟦ e '⟧e3'" :=         (ℑ3 (translate exp_to_instr ⟦ e ⟧e )).

    Notation "⟦ i '⟧i'" :=        (denote_instr i).
    Notation "⟦ i '⟧i1'" :=       (ℑ1 ⟦ i ⟧i).
    Notation "⟦ i '⟧i2'" :=       (ℑ2 ⟦ i ⟧i).
    Notation "⟦ i '⟧i3'" :=       (ℑ3 ⟦ i ⟧i).

    Notation "⟦ c '⟧c'" :=          (denote_code c).
    Notation "⟦ c '⟧c1'" :=         (ℑ1 ⟦ c ⟧c).
    Notation "⟦ c '⟧c2'" :=         (ℑ2 ⟦ c ⟧c).
    Notation "⟦ c '⟧c3'" :=         (ℑ3 ⟦ c ⟧c).

    Notation "⟦ t '⟧t'" :=        (denote_terminator t).
    Notation "⟦ t '⟧t1'" :=       (ℑ1 (translate exp_to_instr ⟦ t ⟧t)).
    Notation "⟦ t '⟧t2'" :=       (ℑ2 (translate exp_to_instr ⟦ t ⟧t)).
    Notation "⟦ t '⟧t3'" :=       (ℑ3 (translate exp_to_instr ⟦ t ⟧t)).

    Notation "⟦ phi '⟧Φ' from"  := (denote_phi from phi) (at level 0, from at next level).
    Notation "⟦ phi '⟧Φ1' from" := (ℑ1 (denote_phi from phi)) (at level 0, from at next level).
    Notation "⟦ phi '⟧Φ2' from" := (ℑ2 (denote_phi from phi)) (at level 0, from at next level).
    Notation "⟦ phi '⟧Φ3' from" := (ℑ3 (denote_phi from phi)) (at level 0, from at next level).

    Notation "⟦ phis '⟧Φs' from"  := (denote_phis from phis) (at level 0, from at next level).
    Notation "⟦ phis '⟧Φs1' from" := (ℑ1 (denote_phis from phis)) (at level 0, from at next level).
    Notation "⟦ phis '⟧Φs2' from" := (ℑ2 (denote_phis from phis)) (at level 0, from at next level).
    Notation "⟦ phis '⟧Φs3' from" := (ℑ3 (denote_phis from phis)) (at level 0, from at next level).

    Notation "⟦ bk '⟧b'" :=  (denote_block bk).
    Notation "⟦ bk '⟧b1' id" := (ℑ1 (⟦ bk ⟧b id)) (at level 0, id at next level).
    Notation "⟦ bk '⟧b2' id" := (ℑ2 (⟦ bk ⟧b id)) (at level 0, id at next level).
    Notation "⟦ bk '⟧b3' id" := (ℑ3 (⟦ bk ⟧b id)) (at level 0, id at next level).

    Notation "⟦ bks '⟧bs'"  := (denote_ocfg bks).
    Notation "⟦ bks '⟧bs1' ids" := (ℑ1 (denote_ocfg bks ids)) (at level 0, ids at next level).
    Notation "⟦ bks '⟧bs2' ids" := (ℑ2 (denote_ocfg bks ids)) (at level 0, ids at next level).
    Notation "⟦ bks '⟧bs3' ids" := (ℑ3 (denote_ocfg bks ids)) (at level 0, ids at next level).

    Notation "⟦ f '⟧cfg'"  := (denote_cfg f).
    Notation "⟦ f '⟧cfg1'" := (ℑ1 (denote_cfg f)).
    Notation "⟦ f '⟧cfg2'" := (ℑ2 (denote_cfg f)).
    Notation "⟦ f '⟧cfg3'" := (ℑ3 (denote_cfg f)).

    Notation "⟦ f '⟧f'"  := (denote_function f).

    Ltac intros2 := intros (? & ? & ?).
    Ltac intros3 := intros (? & ? & ? & ?).

  End SemNotations.
End InterpreterStack_common.

Module Type InterpreterStack.
  Declare Module LP : LLVMParams.
  Declare Module MEM : Memory LP.
  Include InterpreterStack_common LP MEM.
End InterpreterStack.

Module Type InterpreterStackBig <: InterpreterStack.
  Declare Module LP : LLVMParamsBig.
  Declare Module MEM : Memory LP.
  Include InterpreterStack_common LP MEM.
End InterpreterStackBig.

Module Make (LP' : LLVMParams) (MEM' : Memory LP') <: InterpreterStack
with Module LP := LP' with Module MEM := MEM'.
  Include InterpreterStack with Module LP := LP' with Module MEM := MEM'.
End Make.

Module MakeBig (LP' : LLVMParamsBig) (MEM' : Memory LP') <: InterpreterStack
with Module LP := LP' with Module MEM := MEM'.
  Include InterpreterStackBig with Module LP := LP' with Module MEM := MEM'.
End MakeBig.

Module InterpreterStackBigIntptr := MakeBig LLVMParamsBigIntptr MemoryBigIntptr.
Module InterpreterStack64BitIntptr := Make LLVMParams64BitIntptr Memory64BitIntptr.
