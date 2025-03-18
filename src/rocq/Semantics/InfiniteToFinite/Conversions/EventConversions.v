From Stdlib Require Import
     Relations
     String
     List
     Lia
     ZArith
     Morphisms.

Require Import Stdlib.Logic.ProofIrrelevance.

From Vellvm Require Import
     Semantics.InterpretationStack
     Semantics.LLVMEvents
     Semantics.Denotation
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof
     Semantics.Lang
     Semantics.InterpretationStack
     Semantics.TopLevel
     Semantics.DynamicValues
     Semantics.LLVMParams
     Semantics.InfiniteToFinite.Conversions.BaseConversions
     Semantics.InfiniteToFinite.Conversions.DvalueConversions
     Syntax.DynamicTypes
     Theory.TopLevelRefinements
     Theory.ContainsUB
     Utils.Error
     Utils.Monads
     Utils.MapMonadExtra
     Utils.PropT
     Utils.InterpProp
     Utils.ListUtil
     Utils.Tactics
     Utils.OOMRutt
     Utils.OOMRuttProps
     Handlers.MemoryModules.FiniteAddresses
     Handlers.MemoryModules.InfiniteAddresses
     Handlers.MemoryModelImplementation.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor.

From ITree Require Import
     ITree
     Basics
     Basics.HeterogeneousRelations
     Eq.Rutt
     Eq.RuttFacts
     Eq.Eqit
     Eq.EqAxiom.

Require Import Stdlib.Program.Equality.
Require Import Paco.paco.

Import InterpFacts.

Import MonadNotation.
Import ListNotations.

Module Type EventConvert (LP1 : LLVMParams) (LP2 : LLVMParams) (AC : AddrConvert LP1.ADDR LP1.PTOI LP2.ADDR LP2.PTOI) (AC2 : AddrConvert LP2.ADDR LP2.PTOI LP1.ADDR LP1.PTOI) (E1 : LLVM_INTERACTIONS LP1.ADDR LP1.IP LP1.SIZEOF) (E2 : LLVM_INTERACTIONS LP2.ADDR LP2.IP LP2.SIZEOF) (DVC : DVConvert LP1 LP2 AC E1 E2) (DVCrev : DVConvert LP2 LP1 AC2 E2 E1).
  Import DVC.

  Section CONVERSIONS.
    Context
      (dvalue_convert : DV1.dvalue -> OOM DV2.dvalue)
        (uvalue_convert : DV1.uvalue -> OOM DV2.uvalue)
        (rev_dvalue_convert : DV2.dvalue -> OOM DV1.dvalue)
        (rev_uvalue_convert : DV2.uvalue -> OOM DV1.uvalue).

    Section HANDLER_CONVERSIONS.
      Context {E} `{OOM_E : OOME -< E}.

      Definition external_call_handler_convert `{E2.ExternalCallE -< E} : E1.ExternalCallE ~> itree E.
        intros T e0.
        destruct e0.
        - (* ExternalCall *)
          refine (f' <- lift_OOM (uvalue_convert f);;
                  args' <- lift_OOM (map_monad_In args (fun elt Hin => dvalue_convert elt));;
                  dv <- trigger (E2.ExternalCall t f' args');;
                  _).
          apply (lift_OOM (rev_dvalue_convert dv)).
        - (* Stdout *)
          apply (trigger (E2.IO_stdout str)).
        - (* Stderr *)
          apply (trigger (E2.IO_stderr str)).
      Defined.

      Definition intrinsic_handler_convert `{E2.IntrinsicE -< E} : E1.IntrinsicE ~> itree E.
        intros T i.
        inversion i; subst.
        refine (args' <- lift_OOM (map_monad_In args (fun elt Hin => dvalue_convert elt));;
                rv <- trigger (E2.Intrinsic t f args');;
                match rv with
                | inl exc =>
                    exc' <- lift_OOM (rev_uvalue_convert exc);;
                    ret (inl exc')
                | inr dv =>
                    dv' <- lift_OOM (rev_dvalue_convert dv);;
                    ret (inr dv')
                end).
      Defined.

      Definition global_handler_convert `{GlobalE LLVMAst.raw_id E2.DV.dvalue -< E} : GlobalE LLVMAst.raw_id E1.DV.dvalue ~> itree E.
        (* Globals *)
        intros T e0.
        inversion e0.
        - (* Global write *)
          apply (dv <- lift_OOM (dvalue_convert dv);;
                 trigger (GlobalWrite id dv)).
        - (* Global read *)
          apply (dv <- trigger (GlobalRead id);;
                 lift_OOM (rev_dvalue_convert dv)).
      Defined.

      Definition local_handler_convert `{LocalE LLVMAst.raw_id E2.DV.uvalue -< E} : LocalE LLVMAst.raw_id E1.DV.uvalue ~> itree E.
        (* Locals *)
        intros T e0.
        inversion e0.
        - (* Local write *)
          apply (dv <- lift_OOM (uvalue_convert dv);;
                 trigger (LocalWrite id dv)).
        - (* Local read *)
          apply (dv <- trigger (LocalRead id);;
                 lift_OOM (rev_uvalue_convert dv)).
      Defined.

      Definition stack_handler_convert
        `{StackE LLVMAst.raw_id E2.DV.uvalue E2.DV.uvalue -< E} :
        StackE LLVMAst.raw_id E1.DV.uvalue E1.DV.uvalue ~> itree E.
        (* Stack *)
        intros T e0.
        inversion e0.
        - (* Stack Push *)
          apply (args' <- lift_OOM
                           (map_monad_In args
                              (fun '(id, uv) Hin =>
                                 uv' <- uvalue_convert uv;;
                                 ret (id, uv')
                           ));;
                 trigger (StackPush args')).
        - (* Stack Pop *)
          apply (trigger StackPop).
        - (* Stack set handler *)
          apply (trigger (StackSetHandler H0)).
        - (* Stack handler *)
          apply (trigger StackHandler).
        - (* Stack raise *)
          apply (uv <- lift_OOM (uvalue_convert H0);; trigger (StackRaise uv)).
        - (* Stack get exception *)
          refine
            (uv <- trigger StackGetExc;;
             match uv with
             | None => ret None
             | Some uv =>
                 fmap ret (lift_OOM (rev_uvalue_convert uv))
             end).
      Defined.

      Definition memory_handler_convert
        `{E2.MemoryE -< E} :
        E1.MemoryE ~> itree E.
        (* MemoryE *)
        intros T e0.
        inversion e0.
        - (* MemPush *)
          apply (trigger E2.MemPush).
        - (* MemPop *)
          apply (trigger E2.MemPop).
        - (* Alloca *)
          apply (ptr <- trigger (E2.Alloca t num_elements align);;
                 lift_OOM (rev_dvalue_convert ptr)).
        - (* Load *)
          apply (a' <- lift_OOM (dvalue_convert a);;
                 uv <- trigger (E2.Load t a');;
                 lift_OOM (rev_uvalue_convert uv)).
        - (* Store *)
          apply (a' <- lift_OOM (dvalue_convert a);;
                 v' <- lift_OOM (uvalue_convert v);;
                 trigger (E2.Store t a' v')).
      Defined.

      Definition pick_handler_convert
        `{E2.PickUvalueE -< E} :
        E1.PickUvalueE ~> itree E.
        intros T e0.
        (* PickE *)
        (* TODO: confirm whether this is sane... *)
        inversion e0.
        - (* pickUnique *)
          subst.
          refine (x' <- lift_OOM (uvalue_convert x);;
                  dv <- trigger (E2.pickUnique x');;
                  _).
          destruct dv as [res _].
          apply (res' <- lift_OOM (rev_dvalue_convert res);;
                 ret (exist (fun x => True) res' I)).
        - (* pickNonPoison *)
          subst.
          refine (x' <- lift_OOM (uvalue_convert x);;
                  dv <- trigger (E2.pickNonPoison x');;
                  _).
          destruct dv as [res _].
          apply (res' <- lift_OOM (rev_dvalue_convert res);;
                 ret (exist (fun x => True) res' I)).
        - (* pick *)
          subst.
          refine (x' <- lift_OOM (uvalue_convert x);;
                  dv <- trigger (E2.pick x');;
                  _).
          destruct dv as [res _].
          apply (res' <- lift_OOM (rev_dvalue_convert res);;
                 ret (exist (fun x => True) res' I)).
      Defined.

      Definition oom_handler_convert
        `{OOME -< E} :
        OOME ~> itree E.
        intros T e0.
        (* OOME *)
        inversion e0.
        apply (raise_oom "").
      Defined.

      Definition llvm_exc_handler_convert
        `{LLVMExcE E2.DV.uvalue -< E} :
        LLVMExcE E1.DV.uvalue ~> itree E.
        (* LLVMExcE *)
        intros T e0.
        inversion e0.
        apply (uv <- lift_OOM (uvalue_convert H0);; raiseLLVM uv).
      Defined.

      Definition ub_handler_convert
        `{UBE -< E} :
        UBE ~> itree E.
        intros T e0.
        (* UBE *)
        inversion e0.
        apply (raise_ub "").
      Defined.

      Definition debug_handler_convert
        `{DebugE -< E} :
        DebugE ~> itree E.
        (* DebugE *)
        intros T e0.
        inversion e0.
        apply (debug "").
      Defined.

      Definition failure_handler_convert
        `{FailureE -< E} :
        FailureE ~> itree E.
        (* FailureE *)
        intros T e0.
        inversion e0.
        apply (raise_error "").
      Defined.
    End HANDLER_CONVERSIONS.

    Definition L0_convert_helper
      : Handler E1.L0 E2.L0.
      refine (fun A e => _).

      refine (match e with
              | inl1 e0 =>
                  external_call_handler_convert _ e0
              | inr1 (inl1 e0) =>
                  intrinsic_handler_convert _ e0
              | inr1 (inr1 (inl1 e0)) =>
                  global_handler_convert _ e0
              | inr1 (inr1 (inr1 (inl1 (inl1 e0)))) =>
                  local_handler_convert _ e0
              | inr1 (inr1 (inr1 (inl1 (inr1 e0)))) =>
                  stack_handler_convert _ e0
              | inr1 (inr1 (inr1 (inr1 (inl1 e0)))) =>
                  memory_handler_convert _ e0
              | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0))))) =>
                  pick_handler_convert _ e0
              | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))) =>
                  oom_handler_convert _ e0
              | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0))))))) =>
                  llvm_exc_handler_convert _ e0
              | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))))) =>
                  ub_handler_convert _ e0
              | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0))))))))) =>
                  debug_handler_convert _ e0
              | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e0))))))))) =>
                  failure_handler_convert _ e0
              end).
    Defined.

    Definition L1_convert_helper
      : Handler E1.L1 E2.L1.
      refine (fun A e => _).

      refine (match e with
              | inl1 e0 =>
                  external_call_handler_convert _ e0
              | inr1 (inl1 e0) =>
                  intrinsic_handler_convert _ e0
              | inr1 (inr1 (inl1 (inl1 e0))) =>
                  local_handler_convert _ e0
              | inr1 (inr1 (inl1 (inr1 e0))) =>
                  stack_handler_convert _ e0
              | inr1 (inr1 (inr1 (inl1 e0))) =>
                  memory_handler_convert _ e0
              | inr1 (inr1 (inr1 (inr1 (inl1 e0)))) =>
                  pick_handler_convert _ e0
              | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0))))) =>
                  oom_handler_convert _ e0
              | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))) =>
                  llvm_exc_handler_convert _ e0
              | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0))))))) =>
                  ub_handler_convert _ e0
              | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))))) =>
                  debug_handler_convert _ e0
              | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e0)))))))) =>
                  failure_handler_convert _ e0
              end).
    Defined.

    Definition L2_convert_helper
      : Handler E1.L2 E2.L2.
      refine (fun A e => _).

      refine (match e with
              | inl1 e0 =>
                  external_call_handler_convert _ e0
              | inr1 (inl1 e0) =>
                  intrinsic_handler_convert _ e0
              | inr1 (inr1 (inl1 e0)) =>
                  memory_handler_convert _ e0
              | inr1 (inr1 (inr1 (inl1 e0))) =>
                  pick_handler_convert _ e0
              | inr1 (inr1 (inr1 (inr1 (inl1 e0)))) =>
                  oom_handler_convert _ e0
              | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0))))) =>
                  llvm_exc_handler_convert _ e0
              | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))) =>
                  ub_handler_convert _ e0
              | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0))))))) =>
                  debug_handler_convert _ e0
              | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e0))))))) =>
                  failure_handler_convert _ e0
              end).
    Defined.

    Definition L3_convert_helper
      : Handler E1.L3 E2.L3.
      refine (fun A e => _).

      refine (match e with
              | inl1 e0 =>
                  external_call_handler_convert _ e0
              | inr1 (inl1 e0) =>
                  pick_handler_convert _ e0
              | inr1 (inr1 (inl1 e0)) =>
                  oom_handler_convert _ e0
              | inr1 (inr1 (inr1 (inl1 e0))) =>
                  llvm_exc_handler_convert _ e0
              | inr1 (inr1 (inr1 (inr1 (inl1 e0)))) =>
                  ub_handler_convert _ e0
              | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0))))) =>
                  debug_handler_convert _ e0
              | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e0))))) =>
                  failure_handler_convert _ e0
              end).
    Defined.

    Definition L4_convert_helper
      : Handler E1.L4 E2.L4.
      refine (fun A e => _).

      refine (match e with
              | inl1 e0 =>
                  external_call_handler_convert _ e0
              | inr1 (inl1 e0) =>
                  oom_handler_convert _ e0
              | inr1 (inr1 (inl1 e0)) =>
                  llvm_exc_handler_convert _ e0
              | inr1 (inr1 (inr1 (inl1 e0))) =>
                  ub_handler_convert _ e0
              | inr1 (inr1 (inr1 (inr1 (inl1 e0)))) =>
                  debug_handler_convert _ e0
              | inr1 (inr1 (inr1 (inr1 (inr1 e0)))) =>
                  failure_handler_convert _ e0
              end).
    Defined.

    Definition L5_convert_helper
      : Handler E1.L5 E2.L5 := L4_convert_helper.

    Definition L6_convert_helper
      : Handler E1.L6 E2.L6 := L5_convert_helper.
  End CONVERSIONS.

    (*
  Definition L0_convert_lazy : Handler E1.L0 E2.L0 := L0_convert_helper (ret ∘ dvalue_convert_lazy) (ret ∘ uvalue_convert_lazy) (ret ∘ DVCrev.dvalue_convert_lazy) (ret ∘ DVCrev.uvalue_convert_lazy).
  Definition L1_convert_lazy : Handler E1.L1 E2.L1 := L1_convert_helper (ret ∘ dvalue_convert_lazy) (ret ∘ uvalue_convert_lazy) (ret ∘ DVCrev.dvalue_convert_lazy) (ret ∘ DVCrev.uvalue_convert_lazy).
  Definition L2_convert_lazy : Handler E1.L2 E2.L2 := L2_convert_helper (ret ∘ dvalue_convert_lazy) (ret ∘ uvalue_convert_lazy) (ret ∘ DVCrev.dvalue_convert_lazy) (ret ∘ DVCrev.uvalue_convert_lazy).
  Definition L3_convert_lazy : Handler E1.L3 E2.L3 := L3_convert_helper (ret ∘ dvalue_convert_lazy) (ret ∘ uvalue_convert_lazy) (ret ∘ DVCrev.dvalue_convert_lazy) (ret ∘ DVCrev.uvalue_convert_lazy).
  Definition L4_convert_lazy : Handler E1.L4 E2.L4 := L4_convert_helper (ret ∘ dvalue_convert_lazy) (ret ∘ uvalue_convert_lazy) (ret ∘ DVCrev.dvalue_convert_lazy) (ret ∘ DVCrev.uvalue_convert_lazy).
  Definition L5_convert_lazy : Handler E1.L5 E2.L5 := L5_convert_helper (ret ∘ dvalue_convert_lazy) (ret ∘ uvalue_convert_lazy) (ret ∘ DVCrev.dvalue_convert_lazy) (ret ∘ DVCrev.uvalue_convert_lazy).
  Definition L6_convert_lazy : Handler E1.L6 E2.L6 := L6_convert_helper (ret ∘ dvalue_convert_lazy) (ret ∘ uvalue_convert_lazy) (ret ∘ DVCrev.dvalue_convert_lazy) (ret ∘ DVCrev.uvalue_convert_lazy).
     *)

    Definition L0_convert_strict : Handler E1.L0 E2.L0 := L0_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict DVCrev.uvalue_convert_strict.
    Definition L1_convert_strict : Handler E1.L1 E2.L1 := L1_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict DVCrev.uvalue_convert_strict.
    Definition L2_convert_strict : Handler E1.L2 E2.L2 := L2_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict DVCrev.uvalue_convert_strict.
    Definition L3_convert_strict : Handler E1.L3 E2.L3 := L3_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict.
    Definition L4_convert_strict : Handler E1.L4 E2.L4 := L4_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict.
    Definition L5_convert_strict : Handler E1.L5 E2.L5 := L5_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict.
    Definition L6_convert_strict : Handler E1.L6 E2.L6 := L6_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict.
End EventConvert.

Module EventConvertMake (LP1 : LLVMParams) (LP2 : LLVMParams) (AC : AddrConvert LP1.ADDR LP1.PTOI LP2.ADDR LP2.PTOI) (AC2 : AddrConvert LP2.ADDR LP2.PTOI LP1.ADDR LP1.PTOI) (E1 : LLVM_INTERACTIONS LP1.ADDR LP1.IP LP1.SIZEOF) (E2 : LLVM_INTERACTIONS LP2.ADDR LP2.IP LP2.SIZEOF) (DVC : DVConvert LP1 LP2 AC E1 E2) (DVCrev : DVConvert LP2 LP1 AC2 E2 E1) : EventConvert LP1 LP2 AC AC2 E1 E2 DVC DVCrev.
  Include EventConvert LP1 LP2 AC AC2 E1 E2 DVC DVCrev.
End EventConvertMake.

Module ECFinInf := EventConvertMake InterpreterStack64BitIntptr.LP InterpreterStackBigIntptr.LP FinToInfAddrConvert InfToFinAddrConvert InterpreterStack64BitIntptr.LP.Events InterpreterStackBigIntptr.LP.Events DVCFinInf DVCInfFin.
Module ECInfFin := EventConvertMake InterpreterStackBigIntptr.LP InterpreterStack64BitIntptr.LP InfToFinAddrConvert FinToInfAddrConvert InterpreterStackBigIntptr.LP.Events InterpreterStack64BitIntptr.LP.Events DVCInfFin DVCFinInf.

Module EventConvertSafe
  (LP1 : LLVMParams) (LP2 : LLVMParams)
  (AC1 : AddrConvert LP1.ADDR LP1.PTOI LP2.ADDR LP2.PTOI) (AC2 : AddrConvert LP2.ADDR LP2.PTOI LP1.ADDR LP1.PTOI)
  (ACSafe : AddrConvertSafe LP1.ADDR LP1.PTOI LP2.ADDR LP2.PTOI AC1 AC2)
  (IPSafe : IPConvertSafe LP1.IP LP2.IP)
  (Events1 : LLVM_INTERACTIONS LP1.ADDR LP1.IP LP1.SIZEOF) (Events2 : LLVM_INTERACTIONS LP2.ADDR LP2.IP LP2.SIZEOF)
  (DVC : DVConvert LP1 LP2 AC1 Events1 Events2) (DVCrev : DVConvert LP2 LP1 AC2 Events2 Events1) (EC : EventConvert LP1 LP2 AC1 AC2 Events1 Events2 DVC DVCrev).
  Module DVCSafe := DVConvertSafe LP1 LP2 AC1 AC2 ACSafe IPSafe Events1 Events2 DVC DVCrev.

  (* Converting finite events to infinite events... *)
  Module DV1 := DVC.DV1. (* Finite *)
  Module DV2 := DVC.DV2. (* Infinite *)

  (* DVC : Fin -> Inf
     DVCrev : Inf -> Fin
   *)

  Definition dvalue_convert (dv : DV1.dvalue) : OOM DV2.dvalue
    := DVC.dvalue_convert_strict dv.

  Definition dvalue_convert_safe (dv : DV1.dvalue) : DV2.dvalue.
  Proof.
    pose proof DVCSafe.dvalue_convert_strict_safe dv.
    destruct H as [dv_i [CONVf CONVi]].
    remember (DVC.dvalue_convert_strict dv).
    destruct o; inv CONVf.
    exact dv_i.
  Defined.

  Definition uvalue_convert (uv : DV1.uvalue) : OOM DV2.uvalue
    := DVC.uvalue_convert_strict uv.

  Definition uvalue_convert_safe (uv : DV1.uvalue) : DV2.uvalue.
  Proof.
    pose proof DVCSafe.uvalue_convert_strict_safe uv.
    destruct H as [uv_i [CONVf CONVi]].
    remember (DVC.uvalue_convert_strict uv).
    destruct o; inv CONVf.
    exact uv_i.
  Defined.

  Definition rev_dvalue_convert (dv : DV2.dvalue) : OOM DV1.dvalue
    := DVCrev.dvalue_convert_strict dv.

  Definition rev_uvalue_convert (uv : DV2.uvalue) : OOM DV1.uvalue
    := DVCrev.uvalue_convert_strict uv.

  Module E1 := Events1.
  Module E2 := Events2.
End EventConvertSafe.
