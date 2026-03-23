From Stdlib Require Import
  Lia
  ZArith
  List
  String
  Program.Equality.

From ITree Require Import
  ITree
  HeterogeneousRelations
  Rutt
  RuttFacts
  TranslateFacts
  Eqit.

From ExtLib Require Import
  Structures.Monads
  Structures.Functor.

Require Import Paco.paco.

From Vellvm Require Import
  TopLevelRefinements.

From Vellvm.Semantics Require Import
  MemoryAddress
  VellvmIntegers
  DynamicValues
  InterpretationStack
  TopLevel
  LLVMEvents.

From Vellvm.Semantics.InfiniteToFinite.Conversions Require Import
  BaseConversions
  DvalueConversions
  EventConversions.

From Vellvm.Utils Require Import
  Error
  Tactics
  Monads
  MapMonadExtra
  OOMRutt
  OOMRuttProps
  AListFacts
  PropT
  VellvmRelations.

From Vellvm.Semantics.InfiniteToFinite.LangRefine Require Import
  Events
  Sizeof
  Values
  Vectors
  Bytes
  IntegerUtils
  IntegerOps
  IntegerCmps
  FloatOps
  PointerOps
  AggregateOps
  MemoryOps
  Select
  Conversions
  GEP
  Utils
  Concretization
  Expressions
  Calls.

From Vellvm.Syntax Require Import
  DynamicTypes
  CFG.

Import MonadNotation.
Import ListNotations.

Module Type AtomicsRefine
  (IS1 : InterpreterStack)
  (IS2 : InterpreterStack)
  (LLVM1 : LLVMTopLevel IS1)
  (LLVM2 : LLVMTopLevel IS2)
  (TLR1 : TopLevelRefinements IS1 LLVM1)
  (TLR2 : TopLevelRefinements IS2 LLVM2)
  (AC1 : AddrConvert IS1.LP.ADDR IS1.LP.PTOI IS2.LP.ADDR IS2.LP.PTOI)
  (AC2 : AddrConvert IS2.LP.ADDR IS2.LP.PTOI IS1.LP.ADDR IS1.LP.PTOI)
  (IPS : IPConvertSafe IS2.LP.IP IS1.LP.IP)
  (ACS : AddrConvertSafe IS2.LP.ADDR IS2.LP.PTOI IS1.LP.ADDR IS1.LP.PTOI AC2 AC1)
  (DVC : DVConvert IS1.LP IS2.LP AC1)
  (DVCrev : DVConvert IS2.LP IS1.LP AC2)
  (EC : EventConvert IS1.LP IS2.LP AC1 AC2 DVC DVCrev)
  (SIZEOF_REF : Sizeof_Refine IS1.LP.SZ IS2.LP.SZ)
  (ITOP_REF : ItoP_Refine IS1 IS2 AC1 AC2)
  (VMEM_IP_PROP1 : VMemInt_Intptr_Properties IS1.LP.IP)
  (VMEM_IP_PROP2 : VMemInt_Intptr_Properties IS2.LP.IP)
  (VMEM_REF : VMemInt_Refine IS1.LP.IP IS2.LP.IP)
  (ER : EventRefine IS1 IS2 LLVM1 LLVM2 AC1 AC2 DVC DVCrev EC)
  (VAL_REF : ValueRefine 
               IS1 IS2
               LLVM1 LLVM2
               AC1 AC2
               IPS ACS
               DVC DVCrev
               EC SIZEOF_REF ER)
  (VEC_REF : VectorsRefine
               IS1
               IS2
               LLVM1
               LLVM2
               AC1
               AC2
               IPS
               ACS
               DVC
               DVCrev
               EC
               SIZEOF_REF
               ER
               VAL_REF)
  (BYTES_REF : BytesRefine
                 IS1
                 IS2
                 LLVM1
                 LLVM2
                 TLR1
                 TLR2
                 AC1
                 AC2
                 IPS
                 ACS
                 DVC
                 DVCrev
                 EC
                 SIZEOF_REF
                 ITOP_REF
                 ER
                 VAL_REF)
  (IOPS_REF : IntOpsRefine
                IS1
                IS2
                LLVM1
                LLVM2
                TLR1
                TLR2
                AC1
                AC2
                IPS
                ACS
                DVC
                DVCrev
                EC
                SIZEOF_REF
                VMEM_IP_PROP1
                VMEM_IP_PROP2
                VMEM_REF
                ER
                VAL_REF
                VEC_REF)
  (ICMPS_REF : IntCmpsRefine
                IS1
                IS2
                LLVM1
                LLVM2
                TLR1
                TLR2
                AC1
                AC2
                IPS
                ACS
                DVC
                DVCrev
                EC
                SIZEOF_REF
                VMEM_IP_PROP1
                VMEM_IP_PROP2
                VMEM_REF
                ER
                VAL_REF
                VEC_REF)
  (FLOPS_REF : FloatOpsRefine
                IS1
                IS2
                LLVM1
                LLVM2
                TLR1
                TLR2
                AC1
                AC2
                IPS
                ACS
                DVC
                DVCrev
                EC
                SIZEOF_REF
                ER
                VAL_REF)
  (CONV_REF : ConversionsRefine
                IS1
                IS2
                LLVM1
                LLVM2
                TLR1
                TLR2
                AC1
                AC2
                IPS
                ACS
                DVC
                DVCrev
                EC
                SIZEOF_REF
                ITOP_REF
                ER
                VAL_REF
                BYTES_REF)
  (GEP_REF : GEPRefine
               IS1
               IS2
               LLVM1
               LLVM2
               AC1
               AC2
               IPS
               ACS
               DVC
               DVCrev
               EC
               SIZEOF_REF
               ITOP_REF
               ER
               VAL_REF)
  (AGG_REF : AggregateOpsRefine
               IS1
               IS2
               LLVM1
               LLVM2
               TLR1
               TLR2
               AC1
               AC2
               IPS
               ACS
               DVC
               DVCrev
               EC
               SIZEOF_REF
               ER
               VAL_REF)
  (SELECT_REF : SelectRefine
                  IS1
                  IS2
                  LLVM1
                  LLVM2
                  TLR1
                  TLR2
                  AC1
                  AC2
                  IPS
                  ACS
                  DVC
                  DVCrev
                  EC
                  SIZEOF_REF
                  ER
                  VAL_REF)
  (CONC_REF : ConcretizationRefine
                IS1
                IS2
                LLVM1
                LLVM2
                TLR1
                TLR2
                AC1
                AC2
                IPS
                ACS
                DVC
                DVCrev
                EC
                SIZEOF_REF
                ITOP_REF
                VMEM_IP_PROP1
                VMEM_IP_PROP2
                VMEM_REF
                ER
                VAL_REF
                VEC_REF
                BYTES_REF
                IOPS_REF
                ICMPS_REF
                FLOPS_REF
                CONV_REF
                GEP_REF
                AGG_REF
                SELECT_REF)
  (EXP_REF : ExpressionsRefine
               IS1
               IS2
               LLVM1
               LLVM2
               TLR1
               TLR2
               AC1
               AC2
               IPS
               ACS
               DVC
               DVCrev
               EC
               SIZEOF_REF
               ITOP_REF
               VMEM_IP_PROP1
               VMEM_IP_PROP2
               VMEM_REF
               ER
               VAL_REF
               VEC_REF
               BYTES_REF
               IOPS_REF
               ICMPS_REF
               FLOPS_REF
               CONV_REF
               GEP_REF
               AGG_REF
               SELECT_REF
               CONC_REF)
  (MEM_REF : MemoryOpsRefine
               IS1
               IS2
               LLVM1
               LLVM2
               TLR1
               TLR2
               AC1
               AC2
               IPS
               ACS
               DVC
               DVCrev
               EC
               SIZEOF_REF
               ITOP_REF
               VMEM_IP_PROP1
               VMEM_IP_PROP2
               VMEM_REF
               ER
               VAL_REF
               VEC_REF
               BYTES_REF
               IOPS_REF
               ICMPS_REF
               FLOPS_REF
               CONV_REF
               GEP_REF
               AGG_REF
               SELECT_REF
               CONC_REF
               EXP_REF)
  (CALLS_REF : CallsRefine
                 IS1
                 IS2
                 LLVM1
                 LLVM2
                 TLR1
                 TLR2
                 AC1
                 AC2
                 IPS
                 ACS
                 DVC
                 DVCrev
                 EC
                 SIZEOF_REF
                 ITOP_REF
                 VMEM_IP_PROP1
                 VMEM_IP_PROP2
                 VMEM_REF
                 ER
                 VAL_REF
                 VEC_REF
                 BYTES_REF
                 IOPS_REF
                 ICMPS_REF
                 FLOPS_REF
                 CONV_REF
                 GEP_REF
                 AGG_REF
                 SELECT_REF
                 CONC_REF
                 EXP_REF
                 MEM_REF).

  Import EC.
  Import ER.
  Import DV2.
  Import IS2.LP.
  Import DynamicTypes.
  Import IPS.
  Import VAL_REF.
  Import VEC_REF.
  Import BYTES_REF.
  Import SIZEOF_REF.
  Import ITOP_REF.
  Import IOPS_REF.
  Import ICMPS_REF.
  Import FLOPS_REF.
  Import CONV_REF.
  Import GEP_REF.
  Import AGG_REF.
  Import SELECT_REF.
  Import CONC_REF.
  Import EXP_REF.
  Import MEM_REF.
  Import CALLS_REF.
  Import CONC_REF.
  Import DVC.
  Import TLR2.
  Import IS2.LLVM.MEM.CP.CONCBASE.
  Import ACS.

  Lemma denote_cmpxchg_orutt_strict :
    forall id c,
      orutt instr_E_refine_strict instr_E_res_refine_strict eq
        (IS1.LLVM.D.denote_cmpxchg id c) (denote_cmpxchg id c) (OOM:=OOME).
  Proof.
    intros id c.
    destruct c, c_ptr, c_cmp, c_new.
    cbn.
    break_match_goal; [|eauto with ORUTT].

    cbn.
    run_orutt_bind; [auto with ORUTT|].
    repeat (intros; subst; run_orutt_bind; [eauto with ORUTT DVALUE_REFINE|]).
    { apply orutt_bind with (RR:=fun a b => dvalue_refine_strict (proj1_sig a) (proj1_sig b)).
      { eauto with ORUTT. apply orutt_trigger; cbn; auto.
        - unfold uvalue_refine_strict.
          cbn.
          rewrite H3, H0.
          reflexivity.
        - intros [t1 ?] [t2 ?].
          intros H4.
          tauto.
        - intros o CONTRA.
          unfold_subevents.
          inv CONTRA.
      }

      intros; eauto with ORUTT.
    }

    intros r10 r11 H4.
    destruct r10, r11; cbn in *;
      try solve [first [apply orutt_raise
                       | apply orutt_raiseUB
                       | apply orutt_raiseOOM
                       | apply orutt_raiseLLVM
                   ]; [ intros * CONTRA; unfold_subevents; inv CONTRA | cbn; auto]
                | unfold dvalue_refine_strict in *; cbn in *;
                  break_match_hyp_inv
                | unfold dvalue_refine_strict in *; cbn in *; inv H4
        ].

    unfold dvalue_refine_strict in *; cbn in *; inv H4.
    subst_existT.

    destruct sz0; try solve [first [apply orutt_raise
                                     | apply orutt_raiseUB
                                     | apply orutt_raiseOOM
                                     | apply orutt_raiseLLVM
                                 ]; [ intros * CONTRA; unfold_subevents; inv CONTRA | cbn; auto]
                              | unfold dvalue_refine_strict in *; cbn in *;
                                break_match_hyp_inv
                              | unfold dvalue_refine_strict in *; cbn in *; inv H4
                    ].
    break_match_goal.
    { apply orutt_bind with (RR:=eq); eauto with ORUTT.
      intros; eauto with ORUTT.
      run_orutt_bind; eauto with ORUTT.
      eapply orutt_denote_concretize_if_no_undef_or_poison; eauto with ORUTT.
      rewrite uvalue_refine_strict_equation; cbn.
    rewrite H3; auto.
    }

    apply orutt_bind with (RR:=uvalue_refine_strict); eauto with ORUTT.
    eapply orutt_denote_concretize_if_no_undef_or_poison;
      try solve [ intros * CONTRA; inv CONTRA | constructor | auto ].
    rewrite uvalue_refine_strict_equation; cbn.
    rewrite H3; auto.

    auto with ORUTT.
  Qed.

  #[global] Hint Resolve
    denote_cmpxchg_orutt_strict : ORUTT.

  Lemma denote_atomic_rmw_operation_orutt_strict :
    forall r0 r8 r3 r9 a_operation,
      uvalue_refine_strict r0 r3 ->
      uvalue_refine_strict r8 r9 ->
      orutt instr_E_refine_strict instr_E_res_refine_strict uvalue_refine_strict
        (IS1.LLVM.D.denote_atomic_rmw_operation a_operation r8 r0)
        (denote_atomic_rmw_operation a_operation r9 r3)
        (OOM:=OOME).
  Proof.
    intros r0 r8 r3 r9 a_operation REF1 REF2.
    destruct a_operation; cbn;
      try solve
        [ apply orutt_Ret; unfold_uvalue_refine_strict; try rewrite REF1; try rewrite REF2; auto
        | first [apply orutt_raise
                | apply orutt_raiseUB
                | apply orutt_raiseOOM
                | apply orutt_raiseLLVM
            ]; [ intros * CONTRA; unfold_subevents; inv CONTRA | cbn; auto]].
    unfold_uvalue_refine_strict.
    (* TODO: this match is huge, we should be smarter about this *)
    destruct r0, r3;
      try solve
        [ first [apply orutt_raise
                | apply orutt_raiseUB
                | apply orutt_raiseOOM
                | apply orutt_raiseLLVM
            ]; [ intros * CONTRA; unfold_subevents; inv CONTRA | cbn; auto]
        | cbn in *; repeat break_match_hyp_inv
        | inv REF1
        | inv REF2
        | inv REF1; subst_existT;
          inv REF2; subst_existT;
          apply orutt_Ret; cbn;
          unfold_uvalue_refine_strict;
          repeat match goal with
            | H: uvalue_convert_strict _ = _ |- _ =>
                setoid_rewrite H
            end; auto
        ].
  Qed.

  #[global] Hint Resolve denote_atomic_rmw_operation_orutt_strict : ORUTT.

  Lemma denote_atomicrmw_orutt_strict :
    forall id a,
      orutt instr_E_refine_strict instr_E_res_refine_strict eq (IS1.LLVM.D.denote_atomicrmw id a)
        (denote_atomicrmw id a) (OOM:=OOME).
  Proof.
    intros id a.
    destruct a, a_ptr, a_val.
    cbn.
    run_orutt_bind. eauto with ORUTT.
    intros.
    run_orutt_bind. eauto with ORUTT.
    intros.
    run_orutt_bind. eauto with ORUTT.
    intros.
    run_orutt_bind. eauto with ORUTT.
    intros.
    run_orutt_bind. eauto with ORUTT.
    intros.
    run_orutt_bind; eauto with ORUTT. 
    intros.
    run_orutt_bind; eauto with ORUTT. 
  Qed.

  #[global] Hint Resolve denote_atomicrmw_orutt_strict : ORUTT.

End AtomicsRefine.
