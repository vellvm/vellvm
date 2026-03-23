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
  VellvmRelations
  IntMaps.

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
  Calls
  Blocks
  Phis
  Atomics
  Instructions
  Functions
  Exceptions.

From Vellvm.Syntax Require Import
  DynamicTypes
  CFG.

Import MonadNotation.
Import ListNotations.

Module Type MCFGRefine
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
                 MEM_REF)
  (PHIS_REF : PhisRefine
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
                 MEM_REF
                 CALLS_REF)
  (ATOMICS_REF : AtomicsRefine
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
                   MEM_REF
                   CALLS_REF)
  (INST_REF : InstructionsRefine
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
                 MEM_REF
                 CALLS_REF
                 ATOMICS_REF)
  (BLOCK_REF : BlocksRefine
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
                 MEM_REF
                 CALLS_REF
                 PHIS_REF
                 ATOMICS_REF
                 INST_REF)
  (FUNC_REF : FunctionsRefine
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
                MEM_REF
                CALLS_REF
                PHIS_REF
                ATOMICS_REF
                INST_REF
                BLOCK_REF)
  (EXCEPT_REF : ExceptionsRefine
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
                  VEC_REF).

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
  Import BLOCK_REF.
  Import FUNC_REF.
  Import EXCEPT_REF.
  Import DVC.
  Import TLR2.
  Import IS2.LLVM.MEM.CP.CONCBASE.
  Import ACS.

  Lemma denote_mcfg_E1E2_orutt' :
    forall dfns1 dfns2 dt f1 f2 args1 args2,
      IM_Refine function_denotation_refine_strict dfns1 dfns2 ->
      (uvalue_refine_strict f1 f2) ->
      (Forall2 uvalue_refine_strict args1 args2) ->
      call_refine_strict _ _ (LLVMEvents.Call dt f1 args1) (LLVMEvents.Call dt f2 args2) ->
      orutt event_refine_strict event_res_refine_strict (fun res1 res2 => call_res_refine_strict _ _ (LLVMEvents.Call dt f1 args1) res1 (LLVMEvents.Call dt f2 args2) res2)
        (IS1.LLVM.D.denote_mcfg dfns1 dt f1 args1)
        (IS2.LLVM.D.denote_mcfg dfns2 dt f2 args2)
        (OOM:=OOME).
  Proof.
    intros dfns1 dfns2 dt f1 f2 args1 args2 DFNS F1F2 ARGS PRE12.
    unfold IS1.LLVM.D.denote_mcfg.
    unfold denote_mcfg.
    cbn in PRE12.
    destruct PRE12 as [DT [CONVf1f2 MAPM12]]; subst.

    eapply mrec_orutt with (RPreInv:=call_refine_strict).
    { intros A B d1 d2 PRE.

      Opaque catch_llvm_exc_L0' IS1.LLVM.D.catch_llvm_exc_L0'.
      cbn.
      destruct d1.
      destruct d2.

      cbn in PRE.

      eapply orutt_bind with (RR:=dvalue_refine_strict).
      apply concretize_or_pick_L0'_orutt_strict; try tauto.

      intros r1 r2 R1R2.
      (* Should be able to determine that the lookups
         are equivalent using DFNS *)
      cbn.
      break_match.
      { eapply lookup_defn_some_refine_strict in Heqo; eauto.
        destruct Heqo as (f_den2 & LUP2 & FDEN2).

        rewrite LUP2.
        red in FDEN2.
        specialize (FDEN2 args args0).
        forward FDEN2.
        { tauto.
        }

        destruct PRE as [T [CONV MAPM]]; subst.

        eapply orutt_weaken; eauto.
        apply catch_llvm_exc_L0'_orutt; auto.
      }

      eapply lookup_defn_none_strict in Heqo; eauto.
      rewrite Heqo.

      eapply orutt_bind with (RR:=Forall2 dvalue_refine_strict).
      { (* Pick *)
        destruct PRE as [T [CONV MAPM]].
        induction MAPM.
        - cbn.
          apply orutt_Ret; auto.
        - do 2 rewrite map_monad_unfold.
          cbn.
          eapply orutt_bind with (RR:=dvalue_refine_strict).
          {
            apply concretize_or_pick_unique_orutt_strict; eauto with ORUTT;
              repeat constructor; cbn; try tauto.
            intros; cbn. inv H0; subst_existT.
            inv H7; auto.
          }

          intros r0 r3 R0R3.
          eapply orutt_bind with (RR:=Forall2 dvalue_refine_strict);
            eauto.

          intros r4 r5 R4R5.
          eapply orutt_Ret.
          constructor; eauto.
      }

      intros r3 r4 R3R4.
      cbn.

      destruct PRE as [T [UV ARGS_CONV]]; subst.

      unfold ITree.map.
      eapply orutt_bind with (RR:=uvalue_refine_strict).
      2: {
        intros r0 r5 H.
        apply orutt_Ret.
        eauto.
      }

      eapply orutt_bind with (RR:=dvalue_refine_strict).
      {
        apply orutt_trigger.
        { constructor.
          cbn.
          split; split; auto.
        }

        intros t1 t2 H.
        inv H.
        cbn in *.
        apply inj_pair2 in H0, H3, H4, H5.
        subst.

        cbn in H6.
        tauto.

        intros o CONTRA.
        inv CONTRA.
      }

      intros r0 r5 R0R5.
      apply orutt_Ret.
      eapply dvalue_refine_strict_dvalue_to_uvalue; auto.
    }

    cbn. auto.
  Qed.

  Lemma denote_mcfg_E1E2_orutt'_orutt :
    forall dfns1 dfns2 dt f1 f2 args1 args2,
      orutt event_refine_strict event_res_refine_strict (fun res1 res2 => call_res_refine_strict (DV1.uvalue + DV1.uvalue) (DV2.uvalue + DV2.uvalue) (LLVMEvents.Call dt f1 args1) res1 (LLVMEvents.Call dt f2 args2) res2)
        (IS1.LLVM.D.denote_mcfg dfns1 dt f1 args1)
        (IS2.LLVM.D.denote_mcfg dfns2 dt f2 args2)
        (OOM:=OOME) ->
      orutt event_refine_strict event_res_refine_strict (sum_rel uvalue_refine_strict uvalue_refine_strict)
        (IS1.LLVM.D.denote_mcfg dfns1 dt f1 args1)
        (IS2.LLVM.D.denote_mcfg dfns2 dt f2 args2)
        (OOM:=OOME).
  Proof.
    intros dfns1 dfns2 dt f1 f2 args1 args2 H.
    eapply orutt_weaken; eauto.
    intros r1 r2 H0.
    cbn in H0.
    tauto.
  Qed.

  Lemma denote_mcfg_E1E2_orutt :
    forall dfns1 dfns2 dt f1 f2 args1 args2,
      IM_Refine function_denotation_refine_strict dfns1 dfns2 ->
      (uvalue_refine_strict f1 f2) ->
      (Forall2 uvalue_refine_strict args1 args2) ->
      orutt event_refine_strict event_res_refine_strict (sum_rel uvalue_refine_strict uvalue_refine_strict)
        (IS1.LLVM.D.denote_mcfg dfns1 dt f1 args1)
        (IS2.LLVM.D.denote_mcfg dfns2 dt f2 args2)
        (OOM:=OOME).
  Proof.
    intros dfns1 dfns2 dt f1 f2 args1 args2 H H0 H1.
    eapply denote_mcfg_E1E2_orutt'_orutt.
    eapply denote_mcfg_E1E2_orutt'; auto.
    cbn.
    split; auto.
  Qed.

End MCFGRefine.
