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
  Calls
  Phis
  Instructions
  Atomics.

From Vellvm.Syntax Require Import
  DynamicTypes
  CFG.

Import MonadNotation.
Import ListNotations.

Module Type BlocksRefine
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
                 ATOMICS_REF).

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
  Import PHIS_REF.
  Import INST_REF.
  Import DVC.
  Import TLR2.
  Import IS2.LLVM.MEM.CP.CONCBASE.
  Import ACS.

  Lemma denote_terminator_orutt_strict :
    forall term,
      orutt instr_E_refine_strict instr_E_res_refine_strict (sum_rel eq uvalue_refine_strict) (IS1.LLVM.D.denote_terminator term)
        (denote_terminator term)
        (OOM:=OOME).
  Proof.
    intros term.
    destruct term as [[i term] md]; cbn.
    destruct term.
    all: eauto 10 with ORUTT.
    - destruct v.
      run_orutt_bind;
        eauto with ORUTT.
    - destruct v. 
      repeat (intros; run_orutt_bind; eauto with ORUTT).
      intros r0 r3 H0.
      destruct r3; dvalue_refine_strict_inv H0; eauto 10 with ORUTT.
      repeat break_match_goal; eauto with ORUTT.
    - destruct v. 
      repeat (intros; run_orutt_bind; eauto with ORUTT).
      intros r0 r3 H0.
      pose proof dvalue_refine_strict_preserves_dvalue_is_poison _ _ H0.
      rewrite H1.
      break_match_goal; eauto with ORUTT.
      eapply orutt_bind with (RR:=Forall2 (dvalue_refine_strict × eq)).
      { eapply map_monad_orutt.
        intros e0.
        destruct e0.
        destruct t.

        eapply orutt_bind with (RR:=dvalue_refine_strict).
        { repeat (break_match; try solve_orutt_raise).
          all: apply orutt_Ret; solve_dvalue_refine_strict.
        }

        intros r4 r5 H2.
        eapply orutt_Ret.
        constructor; auto.
      }

      (* TODO: Factor out this switch lemma *)
      { intros r4 r5 H2.
        induction H2.
        - cbn.
          apply orutt_Ret; auto.
        - cbn.
          destruct x, y.
          destruct r0;
            cbn in H1; inv H1;
            red in H0; cbn in H0;
            try break_match_hyp_inv; try inv H0;
            cbn; try solve_orutt_raise.
          + destruct H2; cbn in *; subst.
            destruct d0; red in fst_rel;
              cbn in fst_rel;
              subst;
              try break_match_hyp_inv; try inv fst_rel;
              cbn; try solve_orutt_raise.
            break_match_goal; subst; cbn; eauto;
              try solve_orutt_raise.
            break_match_goal; subst; cbn; eauto;
              apply orutt_Ret; auto.
      }
    - destruct v.
      run_orutt_bind;
        eauto with ORUTT.
    - (* invoke? *)
      destruct fnptrval.
      repeat (intros; repeat run_orutt_bind; eauto 0 with ORUTT).
      all: eauto with ORUTT.
      { eapply map_monad_orutt.
        intros [dt ex].
        eauto with ORUTT.
      }
      eapply orutt_trigger_Call; eauto with ORUTT.
      intros ? ? ? [? | ?] [? | ?] ?; cbn; inv H1; eauto with ORUTT; tauto.
      cbn; inv H1; eauto 10 with ORUTT.
      destruct i; cbn; eauto 10 with ORUTT.
  Qed.

  Lemma denote_block_orutt_strict :
    forall block bid varg1 varg2,
      OptionUtil.option_rel2 addr_refine varg1 varg2 ->
      orutt instr_E_refine_strict instr_E_res_refine_strict (sum_rel eq uvalue_refine_strict)
        (IS1.LLVM.D.denote_block block bid varg1)
        (denote_block block bid varg2)
        (OOM:=OOME).
  Proof.
    intros block bid varg1 varg2 VARG.
    cbn.
    apply orutt_bind with (RR:=eq).
    { apply denote_phis_orutt_strict. }

    intros [] [] _.
    apply orutt_bind with (RR:=eq).
    { apply orutt_bind with (RR:=Forall2 eq).
      { eapply map_monad_orutt.
        intros e.
        eapply denote_instr_orutt_strict; auto.
      }

      intros r1 r2 H.
      apply orutt_Ret.
      reflexivity.
    }

    intros [] [] _.
    apply denote_terminator_orutt_strict.
  Qed.

  Lemma denote_ocfg_orutt_strict :
    forall cfg bids varg1 varg2,
      OptionUtil.option_rel2 addr_refine varg1 varg2 ->
      orutt instr_E_refine_strict instr_E_res_refine_strict (sum_rel (eq × eq) uvalue_refine_strict)
        (IS1.LLVM.D.denote_ocfg cfg varg1 bids)
        (denote_ocfg cfg varg2 bids)
        (OOM:=OOME).
  Proof.
    intros cfg [bid_from bid_src] varg1 varg2 VARG.
    Opaque denote_phis denote_phi.
    Opaque IS1.LLVM.D.denote_phis IS1.LLVM.D.denote_phi.
    unfold denote_ocfg, IS1.LLVM.D.denote_ocfg.
    cbn.
    eapply @orutt_iter_gen with (R:=eq); auto.
    intros x0 y0 EQ.
    subst.
    destruct y0 as [from src].

    break_match_goal.
    { (* Found a block *)
      eapply orutt_bind with (RR:=sum_rel eq uvalue_refine_strict).
      { eapply orutt_bind with (RR:=eq).
        { apply denote_phis_orutt_strict. }

        intros [] [] _.
        eapply orutt_bind with (RR:=eq).
        { eapply orutt_bind with (RR:=Forall2 eq).
          { eapply map_monad_orutt.
            intros e.
            eapply denote_instr_orutt_strict; auto.
          }

          intros r1 r2 H.
          apply orutt_Ret; auto.
        }

        intros [] [] _.
        apply denote_terminator_orutt_strict.
      }

      intros r1 r2 H.
      inv H.
      apply orutt_Ret; auto.
      apply orutt_Ret; auto.
    }

    { (* No block found *)
      apply orutt_Ret.
      constructor.
      constructor.
      auto.
    }
  Qed.

End BlocksRefine.
