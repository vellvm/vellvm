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
  Atomics.

From Vellvm.Syntax Require Import
  DynamicTypes
  CFG.

Import MonadNotation.
Import ListNotations.

Module Type InstructionsRefine
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
                   CALLS_REF).

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

  Lemma denote_op_orutt_strict :
    forall op,
      orutt exp_E_refine_strict exp_E_res_refine_strict uvalue_refine_strict
        (IS1.LLVM.D.denote_op op)
        (denote_op op)
        (OOM:=OOME).
  Proof.
    intros op.
    run_orutt_bind; eauto with ORUTT.
  Qed.

  #[global] Hint Resolve
   denote_op_orutt_strict : ORUTT.

  Lemma dvalue_to_uvalue_orutt :
    forall d0 d1,
      dvalue_refine_strict d0 d1 ->
      orutt (OOM:=OOME) instr_E_refine_strict instr_E_res_refine_strict uvalue_refine_strict (Ret (IS1.LP.DV.dvalue_to_uvalue d0)) (Ret (dvalue_to_uvalue d1)).
  Proof.
    intros d0 d1 H.
    apply orutt_Ret.
    eauto with DVALUE_REFINE.
  Qed.

  #[global] Hint Resolve
    dvalue_to_uvalue_orutt : ORUTT.

  Lemma denote_instr_orutt_strict :
    forall instr varg1 varg2,
      OptionUtil.option_rel2 addr_refine varg1 varg2 ->
      orutt instr_E_refine_strict instr_E_res_refine_strict eq
        (IS1.LLVM.D.denote_instr instr varg1)
        (denote_instr instr varg2)
        (OOM:=OOME).
  Proof.
    Opaque denote_exp.
    Opaque IS1.LLVM.D.denote_exp.
    intros [[[id | id] instr] md] varg1 varg2 VARG.
    { cbn.
      destruct instr; eauto 10 with ORUTT.
      - destruct fn.
        repeat (run_orutt_bind).
        { apply map_monad_orutt.
          intros [? ?].
          eauto with ORUTT.
        }

        intros r1 r2 H.
        break_match_goal.
        { break_match_goal; [|break_match_goal; [|break_match_goal]].
          - (* va_start *)
            run_orutt_bind; eauto 10 with ORUTT.
            + destruct args; try solve_orutt_raise.
              destruct p, t.
              destruct args; try solve_orutt_raise.
              destruct varg1, varg2; inv VARG; try solve_orutt_raise.

              run_orutt_bind; eauto 10 with ORUTT.

              intros r0 r3 H0.
              run_orutt_bind; eauto 10 with ORUTT.
              intros ? ? ?.
              destruct r5; dvalue_refine_strict_inv H2; eauto 20 with ORUTT.
              (* Need to fix dvalue_refine_strict and uvalue_refine_strict solvers in ORUTT database *)
              all: try (apply orutt_bind with (RR:=Logic.eq);
                        [ apply orutt_trigger; cbn; eauto;
                          [ repeat split;
                            solve [ red; cbn;
                                    rewrite H2; auto
                                  | red; cbn;
                                    rewrite H1; auto
                                  | red; cbn;
                                    rewrite H3; auto
                                  | eauto
                              ]
                          | intros [] [] ?; auto
                          | intros o CONTRA; inv CONTRA
                          ]
                        | intros ? ? ?;
                            apply orutt_Ret;
                          solve_uvalue_refine_strict
                     ]).
          - (* va_copy *)
            run_orutt_bind; eauto 10 with ORUTT.
            + destruct args; try solve_orutt_raise.
              destruct p, t.
              destruct args; try solve_orutt_raise.
              destruct d0; try solve_orutt_raise.
              destruct d0; try solve_orutt_raise.
              destruct p, t.
              destruct d0; try solve_orutt_raise.
              destruct args; try solve_orutt_raise.
              eauto 200 with ORUTT.
          - (* va_end *)
            eauto 200 with ORUTT.
          - run_orutt_bind; eauto 10 with ORUTT.
            run_orutt_bind; eauto 10 with ORUTT.
            intros r0 r3 H0.
            run_orutt_bind; eauto 200 with ORUTT.
            eapply orutt_trigger_Intrinsic; eauto with ORUTT.

            intros ? ? [? | ?] [? | ?] ?; cbn; inv H1; eauto with ORUTT; tauto.
            intros [? | ?] [? | ?] ?; cbn; inv H1; eauto 10 with ORUTT.
        }

        run_orutt_bind; auto 10 with ORUTT.
        run_orutt_bind; auto 10 with ORUTT.
        intros r0 r3 H0.
        run_orutt_bind; eauto 10 with ORUTT.
        eapply orutt_trigger_Call; eauto with ORUTT.
        intros ? ? ? [? | ?] [? | ?] ?; cbn; inv H1; eauto with ORUTT; tauto.
        intros [? | ?] [? | ?] ?; cbn; inv H1; eauto with ORUTT.

      - break_inner_match.
        { run_orutt_bind; eauto 200 with ORUTT.
          break_match.
          + destruct t0.
            run_orutt_bind; eauto 200 with ORUTT.
            intros; run_orutt_bind; eauto 200 with ORUTT.
            intros; run_orutt_bind; eauto 200 with ORUTT.
            erewrite dvalue_int_unsigned_E1E2; eauto.
            eapply orutt_trigger_Alloca; eauto 10 with ORUTT DVALUE_REFINE.
            cbn; tauto.
            intros; run_orutt_bind; eauto 200 with ORUTT.
            apply orutt_denote_concretize_if_no_undef_or_poison; eauto with ORUTT DVALUE_REFINE.
          + run_orutt_bind; eauto 200 with ORUTT DVALUE_REFINE.
            eapply orutt_trigger_Alloca; eauto with ORUTT DVALUE_REFINE.
            cbn; tauto.
        }

        { eapply orutt_bind; eauto with ORUTT REF.
          apply orutt_bind with (RR:=dvalue_refine_strict).
          eapply orutt_trigger_Alloca; eauto with ORUTT; cbn; tauto.

          intros r1 r2 H.
          eauto with ORUTT DVALUE_REFINE.
        }

      - destruct ptr.
        eauto 200 with ORUTT.
      - (* va_arg *)
        break_match_goal; subst.
        repeat (intros; run_orutt_bind; auto with ORUTT DVALUE_REFINE).

        { unfold lift_OOM.
          destruct (IP.from_Z 1) eqn:FROM.
          - pose proof intptr_convert_succeeds i as (?&?).
            erewrite IP.from_Z_to_Z in e0; eauto.
            rewrite e0.
            apply orutt_Ret.
            unfold intptr_fin_inf.
            break_match.
            clear Heqs.
            erewrite IP.from_Z_to_Z in e1; eauto.
            rewrite e0 in e1; inv e1; auto.
          - apply orutt_raise_oom.
        }

        { unfold lift_err_oom_RAISE_ERROR_OOM.
          destruct (GEP.handle_gep t r7 [DVALUE_IPTR r11]) eqn:GEP.

          - erewrite handle_gep_err_fin_inf; eauto.
            solve_orutt_raise.
            cbn.
            rewrite fin_to_inf_dvalue_iptr. congruence.
          - destruct o.
            2: {
              apply orutt_raise_oom.
            }
            erewrite handle_gep_fin_inf with (res_addr_inf:=fin_to_inf_dvalue d0); eauto.
            + apply orutt_Ret.
              apply fin_to_inf_dvalue_refine_strict.
            + apply fin_to_inf_dvalue_refine_strict.
            + cbn; rewrite fin_to_inf_dvalue_iptr. congruence.
        }
    }

    { cbn.
      destruct instr; eauto 10 with ORUTT.
      - destruct fn.
        run_orutt_bind; eauto 10 with ORUTT.
        { apply map_monad_orutt.
          intros e0. destruct e0.
          apply translate_exp_to_instr_E1E2_orutt_strict.
          apply denote_exp_E1E2_orutt.
        }

        intros r1 r2 H.
        break_match_goal.
        { break_match_goal; [|break_match_goal; [|break_match_goal]].
          - (* va_start *)
            run_orutt_bind; eauto 10 with ORUTT.
            + destruct args; try solve_orutt_raise.
              destruct p, t.
              destruct args; try solve_orutt_raise.
              destruct varg1, varg2; inv VARG; try solve_orutt_raise.
              repeat (intros; run_orutt_bind; eauto 10 with ORUTT).
              intros.
              destruct r5; dvalue_refine_strict_inv H2; eauto 10 with ORUTT.
              all: try (apply orutt_bind with (RR:=Logic.eq);
                        [ apply orutt_trigger; cbn; eauto;
                       [ repeat split;
                         solve [ red; cbn;
                                 rewrite H2; auto
                               | red; cbn;
                                 rewrite H1; auto
                               | red; cbn;
                                 rewrite H3; auto
                               | eauto
                           ]
                       | intros [] [] ?; auto; reflexivity
                       | intros o CONTRA; inv CONTRA
                       ]
                     | intros ? ? ?;
                         apply orutt_Ret;
                       solve_uvalue_refine_strict
                       ]).
          - (* va_copy *)
            eapply orutt_bind with (RR:=uvalue_refine_strict).
            + destruct args; try solve_orutt_raise.
              destruct p, t.
              destruct args; try solve_orutt_raise.
              destruct d0; try solve_orutt_raise.
              destruct d0; try solve_orutt_raise.
              destruct p, t.
              destruct d0; try solve_orutt_raise.
              destruct args; try solve_orutt_raise.
              eauto 200 with ORUTT.
            + intros ? ? ?.
              apply orutt_Ret; auto.
          - (* va_end *)
            eauto 200 with ORUTT.
          - repeat (intros; run_orutt_bind; eauto 200 with ORUTT).
            eapply orutt_trigger_Intrinsic; eauto with ORUTT.
            intros ? ? [? | ?] [? | ?] ? ; cbn; inv H1; eauto with ORUTT; tauto.
            intros [? | ?] [? | ?] ?; cbn; inv H1; eauto with ORUTT.
        }

        repeat (intros; run_orutt_bind; auto 200 with ORUTT DVALUE_REFINE).
        eapply orutt_trigger_Call; eauto with ORUTT.
        intros ? ? ? [? | ?] [? | ?] ? ; cbn; inv H1; eauto with ORUTT; tauto.
        
        intros [? | ?] [? | ?] ?; cbn; inv H1; eauto with ORUTT.
      - destruct val, ptr.
        repeat (intros; run_orutt_bind; auto 200 with ORUTT DVALUE_REFINE).
        destruct r5; dvalue_refine_strict_inv H1; eauto 10 with ORUTT.
        all: (apply Store_E1E2_orutt; eauto with ORUTT;
              unfold dvalue_refine_strict; cbn; try rewrite H1; try rewrite H2; auto).
      - (* va_arg *)
        break_match_goal; subst.
        repeat (intros; run_orutt_bind; auto with ORUTT DVALUE_REFINE).
        { unfold lift_OOM.
          destruct (IP.from_Z 1) eqn:FROM.
          - pose proof intptr_convert_succeeds i as (?&?).
            erewrite IP.from_Z_to_Z in e0; eauto.
            rewrite e0.
            apply orutt_Ret.
            unfold intptr_fin_inf.
            break_match.
            clear Heqs.
            erewrite IP.from_Z_to_Z in e1; eauto.
            rewrite e0 in e1; inv e1; auto.
          - apply orutt_raise_oom.
        }

        { unfold lift_err_oom_RAISE_ERROR_OOM.
          destruct (GEP.handle_gep t r7 [DVALUE_IPTR r11]) eqn:GEP.
          - erewrite handle_gep_err_fin_inf; eauto.
            solve_orutt_raise.
            cbn.
            rewrite fin_to_inf_dvalue_iptr. congruence.
          - destruct o.
            2: {
              apply orutt_raise_oom.
            }
            erewrite handle_gep_fin_inf with (res_addr_inf:=fin_to_inf_dvalue d0); eauto.
            + apply orutt_Ret.
              apply fin_to_inf_dvalue_refine_strict.
            + apply fin_to_inf_dvalue_refine_strict.
            + cbn; rewrite fin_to_inf_dvalue_iptr. congruence.
        }
    }
  Qed.

End InstructionsRefine.
