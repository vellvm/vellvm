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

Module Type EventConvert (LP1 : LLVMParams) (LP2 : LLVMParams) (AC : AddrConvert LP1.ADDR LP1.PTOI LP2.ADDR LP2.PTOI) (AC2 : AddrConvert LP2.ADDR LP2.PTOI LP1.ADDR LP1.PTOI) (DVC : DVConvert LP1 LP2 AC) (DVCrev : DVConvert LP2 LP1 AC2).
  Import DVC.

  Module DV1 := LP1.DV.
  Module DV2 := LP2.DV.

  #[global]
    Notation ExternalCallE1 := (ExternalCallE DV1.dvalue DV1.uvalue).
  #[global]  
    Notation ExternalCallE2 := (ExternalCallE DV2.dvalue DV2.uvalue).

  #[global]  
    Notation IntrinsicE1 := (IntrinsicE DV1.dvalue DV1.uvalue).  
  #[global]
    Notation IntrinsicE2 := (IntrinsicE DV2.dvalue DV2.uvalue).
  #[global]
    Notation MemoryE1 := (MemoryE DV1.dvalue DV1.uvalue).  
  #[global]
    Notation MemoryE2 := (MemoryE DV2.dvalue DV2.uvalue).
  #[global]
    Notation PickUvalueE1 := (PickUvalueE DV1.dvalue DV1.uvalue).  
  #[global]
    Notation PickUvalueE2 := (PickUvalueE DV2.dvalue DV2.uvalue).

  #[global]
    Notation L01 := (L0 DV1.dvalue DV1.uvalue).
  #[global]  
    Notation L02 := (L0 DV2.dvalue DV2.uvalue).
  #[global]
    Notation L11 := (L1 DV1.dvalue DV1.uvalue).
  #[global]  
    Notation L12 := (L1 DV2.dvalue DV2.uvalue).
  #[global]
    Notation L21 := (L2 DV1.dvalue DV1.uvalue).
  #[global]  
    Notation L22 := (L2 DV2.dvalue DV2.uvalue).
  #[global]  
    Notation L31 := (L3 DV1.dvalue DV1.uvalue).
  #[global]  
    Notation L32 := (L3 DV2.dvalue DV2.uvalue).
  #[global]  
    Notation L41 := (L4 DV1.dvalue DV1.uvalue).
  #[global]
    Notation L42 := (L4 DV2.dvalue DV2.uvalue).
  #[global]
    Notation L51 := (L5 DV1.dvalue DV1.uvalue).
  #[global]
    Notation L52 := (L5 DV2.dvalue DV2.uvalue).
  #[global]
    Notation L61 := (L6 DV1.dvalue DV1.uvalue).
  #[global]
    Notation L62 := (L6 DV2.dvalue DV2.uvalue).

  
  Section CONVERSIONS.
    Context
      (dvalue_convert : DV1.dvalue -> OOM DV2.dvalue)
        (uvalue_convert : DV1.uvalue -> OOM DV2.uvalue)
        (rev_dvalue_convert : DV2.dvalue -> OOM DV1.dvalue)
        (rev_uvalue_convert : DV2.uvalue -> OOM DV1.uvalue).

    Section HANDLER_CONVERSIONS.
      Context {E} `{OOM_E : OOME -< E}.

      Definition external_call_handler_convert `{ExternalCallE2 -< E} : ExternalCallE1 ~> itree E.
        intros T e0.
        destruct e0.
        - (* ExternalCall *)
          refine (f' <- lift_OOM (uvalue_convert f);;
                  args' <- lift_OOM (map_monad_In args (fun elt Hin => dvalue_convert elt));;
                  dv <- trigger (ExternalCall t f' args');;
                  _).
          apply (lift_OOM (rev_dvalue_convert dv)).
        - (* Stdout *)
          apply (trigger (IO_stdout str)).
        - (* Stderr *)
          apply (trigger (IO_stderr str)).
      Defined.

      Definition intrinsic_handler_convert `{IntrinsicE2 -< E} : IntrinsicE1 ~> itree E.
        intros T i.
        inversion i; subst.
        refine (args' <- lift_OOM (map_monad_In args (fun elt Hin => dvalue_convert elt));;
                rv <- trigger (Intrinsic t f args');;
                match rv with
                | inl exc =>
                    exc' <- lift_OOM (rev_uvalue_convert exc);;
                    ret (inl exc')
                | inr dv =>
                    dv' <- lift_OOM (rev_dvalue_convert dv);;
                    ret (inr dv')
                end).
      Defined.

      Definition global_handler_convert `{GlobalE LLVMAst.raw_id DV2.dvalue -< E} : GlobalE LLVMAst.raw_id DV1.dvalue ~> itree E.
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

      Definition local_handler_convert `{LocalE LLVMAst.raw_id DV2.uvalue -< E} : LocalE LLVMAst.raw_id DV1.uvalue ~> itree E.
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
        `{StackE LLVMAst.raw_id DV2.uvalue DV2.uvalue -< E} :
        StackE LLVMAst.raw_id DV1.uvalue DV1.uvalue ~> itree E.
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
        `{MemoryE2 -< E} :
        MemoryE1 ~> itree E.
        (* MemoryE *)
        intros T e0.
        inversion e0.
        - (* MemPush *)
          apply (trigger MemPush).
        - (* MemPop *)
          apply (trigger MemPop).
        - (* Alloca *)
          apply (ptr <- trigger (Alloca t num_elements align);;
                 lift_OOM (rev_dvalue_convert ptr)).
        - (* Load *)
          apply (a' <- lift_OOM (dvalue_convert a);;
                 uv <- trigger (Load t a');;
                 lift_OOM (rev_uvalue_convert uv)).
        - (* Store *)
          apply (a' <- lift_OOM (dvalue_convert a);;
                 v' <- lift_OOM (uvalue_convert v);;
                 trigger (Store t a' v')).
      Defined.

      Definition pick_handler_convert
        `{PickUvalueE2 -< E} :
        PickUvalueE1 ~> itree E.
        intros T e0.
        (* PickE *)
        (* TODO: confirm whether this is sane... *)
        inversion e0.
        - (* pickUnique *)
          subst.
          refine (x' <- lift_OOM (uvalue_convert x);;
                  dv <- trigger (pickUnique x');;
                  _).
          destruct dv as [res _].
          apply (res' <- lift_OOM (rev_dvalue_convert res);;
                 ret (exist (fun x => True) res' I)).
        - (* pickNonPoison *)
          subst.
          refine (x' <- lift_OOM (uvalue_convert x);;
                  dv <- trigger (pickNonPoison x');;
                  _).
          destruct dv as [res _].
          apply (res' <- lift_OOM (rev_dvalue_convert res);;
                 ret (exist (fun x => True) res' I)).
        - (* pick *)
          subst.
          refine (x' <- lift_OOM (uvalue_convert x);;
                  dv <- trigger (pick x');;
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
        `{LLVMExcE DV2.uvalue -< E} :
        LLVMExcE DV1.uvalue ~> itree E.
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
      : Handler L01 L02.
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
      : Handler L11 L12.
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
      : Handler L21 L22.
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
      : Handler L31 L32.
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
      : Handler L41 L42.
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
      : Handler L51 L52 := L4_convert_helper.


    Definition L6_convert_helper
      : Handler L61 L62 := L4_convert_helper.
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

    Definition L0_convert_strict : Handler L01 L02 := L0_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict DVCrev.uvalue_convert_strict.
    Definition L1_convert_strict : Handler L11 L12 := L1_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict DVCrev.uvalue_convert_strict.
    Definition L2_convert_strict : Handler L21 L22 := L2_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict DVCrev.uvalue_convert_strict.
    Definition L3_convert_strict : Handler L31 L32 := L3_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict.
    Definition L4_convert_strict : Handler L41 L42 := L4_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict.
    Definition L5_convert_strict : Handler L51 L52 := L5_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict.
    Definition L6_convert_strict : Handler L61 L62 := L6_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict.
End EventConvert.

Module EventConvertMake (LP1 : LLVMParams) (LP2 : LLVMParams) (AC : AddrConvert LP1.ADDR LP1.PTOI LP2.ADDR LP2.PTOI) (AC2 : AddrConvert LP2.ADDR LP2.PTOI LP1.ADDR LP1.PTOI) (DVC : DVConvert LP1 LP2 AC) (DVCrev : DVConvert LP2 LP1 AC2) : EventConvert LP1 LP2 AC AC2 DVC DVCrev.
  Include EventConvert LP1 LP2 AC AC2 DVC DVCrev.
End EventConvertMake.

Module ECFinInf := EventConvertMake InterpreterStack64BitIntptr.LP InterpreterStackBigIntptr.LP FinToInfAddrConvert InfToFinAddrConvert DVCFinInf DVCInfFin.
Module ECInfFin := EventConvertMake InterpreterStackBigIntptr.LP InterpreterStack64BitIntptr.LP InfToFinAddrConvert FinToInfAddrConvert DVCInfFin DVCFinInf.

Module EventConvertSafe
  (LP1 : LLVMParams) (LP2 : LLVMParams)
  (AC1 : AddrConvert LP1.ADDR LP1.PTOI LP2.ADDR LP2.PTOI) (AC2 : AddrConvert LP2.ADDR LP2.PTOI LP1.ADDR LP1.PTOI)
  (ACSafe : AddrConvertSafe LP1.ADDR LP1.PTOI LP2.ADDR LP2.PTOI AC1 AC2)
  (IPSafe : IPConvertSafe LP1.IP LP2.IP)
  (DVC : DVConvert LP1 LP2 AC1) (DVCrev : DVConvert LP2 LP1 AC2) (EC : EventConvert LP1 LP2 AC1 AC2 DVC DVCrev).
  Module DVCSafe := DVConvertSafe LP1 LP2 AC1 AC2 ACSafe IPSafe DVC DVCrev.

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

End EventConvertSafe.
