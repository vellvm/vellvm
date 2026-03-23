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
  Instructions.

From Vellvm.Syntax Require Import
  DynamicTypes
  CFG.

Import MonadNotation.
Import ListNotations.

Module Type FunctionsRefine
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
                 INST_REF).

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
  Import DVC.
  Import TLR2.
  Import IS2.LLVM.MEM.CP.CONCBASE.
  Import ACS.

  Definition function_denotation_refine_strict : IS1.LLVM.D.function_denotation -> IS2.LLVM.D.function_denotation -> Prop.
  Proof.
    intros d1 d2.
    unfold function_denotation in *.
    unfold IS1.LLVM.D.function_denotation in *.

    refine (forall args1 args2,
               Forall2 uvalue_refine_strict args1 args2 ->
               orutt L0'_refine_strict L0'_res_refine_strict uvalue_refine_strict
                 (d1 args1)
                 (d2 args2)
                 (OOM:=OOME)
           ).
  Defined.

  Lemma address_one_function_E1E2_orutt :
    forall dfn,
      orutt event_refine_strict event_res_refine_strict (eq × function_denotation_refine_strict)
        (LLVM1.address_one_function dfn)
        (LLVM2.address_one_function dfn)
        (OOM:=OOME).
  Proof.
    intros dfn.
    cbn.
    eapply orutt_bind with (RR:=dvalue_refine_strict).
    apply rutt_orutt. apply GlobalRead_L0_E1E2_rutt.
    { intros ? s. repeat destruct s; try (solve [ left; intros o CONTRA; inv CONTRA ]); right; eexists; reflexivity. } 

    intros r1 r2 R1R2.
    destruct r2;
      dvalue_refine_strict_inv R1R2;
      try solve_orutt_raise.
    apply orutt_Ret.

    constructor.
    - cbn; auto.
      erewrite AC1.addr_convert_ptoi; eauto.
    - cbn.
      red.
      intros args1 args2 ARGS.
      cbn.
      eapply orutt_bind with (RR:=addr_refine).
      eapply orutt_bind with (RR:=(Forall2 (eq × uvalue_refine_strict)) × Forall2 uvalue_refine_strict).
      { cbn.
        pose proof (Util.Forall2_length ARGS) as LEN.
        destruct (IS1.LLVM.D.combine_lists_varargs (LLVMAst.df_args dfn) args1) eqn:HARGS1.
        { (* Error, means args1 differs in length *)
          assert (combine_lists_varargs (LLVMAst.df_args dfn) args2 = inl s) as HARGS2.
          { clear - ARGS LEN HARGS1.
            remember (LLVMAst.df_args dfn) as names.
            clear Heqnames.
            generalize dependent args1.
            generalize dependent args2.
            induction names; intros args2 args1 ARGS LEN HARGS1; cbn in *.
            - induction ARGS; inv HARGS1.
            - induction ARGS; inv HARGS1; auto.
              break_match_hyp_inv.
              + erewrite IHnames; eauto.
              + destruct p; inv H2.
          }

          rewrite HARGS2.
          cbn.
          apply orutt_raise.
          intros ? ? CONTRA; inv CONTRA.
          repeat constructor.
        }

        {
          assert (exists p', combine_lists_varargs (LLVMAst.df_args dfn) args2 = inr p' /\ (Forall2 (eq × uvalue_refine_strict) × Forall2 uvalue_refine_strict) p p') as (p'&HARGS2&REF).
          { clear - ARGS LEN HARGS1.
            remember (LLVMAst.df_args dfn) as names.
            clear Heqnames.
            generalize dependent args1.
            generalize dependent args2.
            generalize dependent p.
            induction names; intros p args2 args1 ARGS LEN HARGS1; cbn in *.
            - induction ARGS; inv HARGS1.
              + exists ([], []).
                split; eauto.
              + exists ([], y :: l').
                split; eauto.
                constructor; cbn; auto.
            - induction ARGS; inv HARGS1; auto.
              break_match_hyp_inv.
              destruct p0; inv H2.
              assert (Datatypes.length l = Datatypes.length l') as LEN'.
              { inv LEN; auto. }

              pose proof (IHnames (l0, l1) l' l ARGS LEN' Heqs).
              destruct H0 as (?&?&?).
              destruct x0.
              exists ((a, y) :: l2, l3).
              rewrite H0.
              split; auto.
              inv H1; cbn in *.
              constructor; cbn; auto.
          }

          rewrite HARGS2.
          cbn.
          apply orutt_Ret; auto.
        }
      }

      cbn.
      intros [params1 vargs1] [params2 vargs2] [PARAMS VARGS].
      cbn in *.
      eapply orutt_bind with (RR:=eq).
      { unfold LLVMEvents.lift_err.
        induction VARGS.
        - cbn.
          apply orutt_Ret; auto.
        - cbn.
          erewrite dtyp_of_uvalue_fun_fin_inf; eauto.
          break_inner_match_goal.
          apply orutt_raise.
          intros ? ? CONTRA; inv CONTRA.
          repeat constructor.

          repeat break_inner_match_goal.
          + apply orutt_raise.
            intros ? ? CONTRA; inv CONTRA.
            repeat constructor.
          + pinversion IHVARGS.
          + pinversion IHVARGS.
          + apply orutt_Ret.
            apply orutt_inv_Ret in IHVARGS; subst; auto.
      }

      cbn.
      intros ? ? ?; subst.
      eapply orutt_bind with (RR:=eq).
      { apply orutt_trigger.
        cbn; auto.

        constructor.
        constructor.
        intros [] [] _.
        reflexivity.

        intros o CONTRA.
        inv CONTRA.
      }

      intros [] [] _.

      eapply orutt_bind with (RR:=eq).
      { apply orutt_trigger.
        - cbn.
          induction PARAMS.
          + constructor; cbn.
            apply local_refine_strict_empty.
          + destruct x0 as [xid xuv].
            destruct y as [yid yuv].
            inv H0.
            cbn in fst_rel, snd_rel. subst.
            constructor; cbn.
            inv IHPARAMS; subst_existT.
            apply alist_refine_cons; auto.
        - intros [] [] _.
          reflexivity.
        - intros o CONTRA; inv CONTRA.
      }

      intros [] [] _.
      eapply orutt_bind with (RR:=dvalue_refine_strict).
      { apply orutt_trigger.
        repeat constructor.
        intros ? ? ?.
        inv H0.
        subst_existT.
        inv H7.
        apply H1.
        intros ? CONTRA; inv CONTRA.
      }

      intros ? ? ?.
      eapply orutt_bind with (RR:=eq).
      { apply orutt_trigger.
        - cbn.
          repeat constructor; auto.
          red; cbn.
          induction VARGS; cbn; auto.
          rewrite H1.
          break_inner_match_goal; inv IHVARGS; auto.
        - intros [] [] _; auto.
        - intros ? CONTRA; inv CONTRA.
      }

      intros [] [] _.
      destruct r0; dvalue_refine_strict_inv H0;
        try solve [apply orutt_raise; [intros ? ? CONTRA; inv CONTRA|repeat constructor]];
        eauto with ORUTT.

      intros r1 r2 REF.
      eapply orutt_bind with (RR:=uvalue_refine_strict).
      { rewrite translate_bind.
        rewrite translate_bind.

        eapply orutt_bind with (RR:=sum_rel (eq × eq) uvalue_refine_strict).
        { (* ocfg stuff *)
          apply translate_instr_to_L0'_E1E2_orutt_strict.
          apply denote_ocfg_orutt_strict.
          cbn.
          apply REF.
        }

        intros r0 r3 ?.
        inv H0.
        - inv H1.
          destruct a1, a2.
          cbn in *.
          subst.
          unfold LLVMEvents.raise.
          rewrite bind_trigger.
          rewrite bind_trigger.
          rewrite translate_vis.
          rewrite translate_vis.
          cbn.
          apply orutt_Vis; cbn; auto.
          constructor; cbn; auto.
          intros [] [] _.
          intros o CONTRA.
          inv CONTRA.
        - do 2 rewrite translate_ret.
          apply orutt_Ret.
          auto.
      }

      intros r0 r3 R0R3.
      eapply orutt_bind with (RR:=eq).
      { eapply orutt_bind with (RR:=eq).
        eapply orutt_trigger.
        cbn; constructor; cbn; auto.
        intros [] [] _.
        reflexivity.
        intros o CONTRA; inv CONTRA.
        intros [] [] _.
        eapply orutt_trigger.
        cbn; constructor; cbn; auto.
        intros [] [] _.
        reflexivity.
        intros o CONTRA; inv CONTRA.
      }

      intros [] [] _.
      eapply orutt_Ret.
      auto.
  Qed.

  Lemma address_one_functions_E1E2_orutt :
    forall dfns,
      orutt event_refine_strict event_res_refine_strict
        (Forall2 (eq × function_denotation_refine_strict))
        (map_monad LLVM1.address_one_function dfns)
        (map_monad address_one_function dfns)
        (OOM:=OOME).
  Proof.
    intros dfns.
    apply map_monad_orutt.
    intros e.
    apply address_one_function_E1E2_orutt.
  Qed.

  Lemma lookup_defn_some_refine_strict :
    forall dfns1 dfns2 r1 r2 f_den1,
      IM_Refine function_denotation_refine_strict dfns1 dfns2 ->
      dvalue_refine_strict r1 r2 ->
      IS1.LLVM.D.lookup_defn r1 dfns1 = Some f_den1 ->
      exists f_den2,
        IS2.LLVM.D.lookup_defn r2 dfns2 = Some f_den2 /\
          function_denotation_refine_strict f_den1 f_den2.
  Proof.
    intros dfns1 dfns2 r1 r2 f_den1 [MEM DFNS] R1R2 LUP.

    unfold IS1.LLVM.D.lookup_defn in LUP.

    destruct r2;
      dvalue_refine_strict_inv R1R2; cbn in *;
      try discriminate.

    pose proof LUP as M.
    apply lookup_member in M.
    apply MEM in M.
    apply member_lookup in M.
    destruct M as (?&?).
    eapply DFNS in LUP; eauto.
    exists x0; split; eauto.
    erewrite <- AC1.addr_convert_ptoi; eauto.
  Qed.

  (* May not be true with new dvalue_refine *)
  Lemma lookup_defn_none_strict :
    forall dfns1 dfns2 r1 r2,
      IM_Refine function_denotation_refine_strict dfns1 dfns2 ->
      dvalue_refine_strict r1 r2 ->
      IS1.LLVM.D.lookup_defn r1 dfns1 = None ->
      IS2.LLVM.D.lookup_defn r2 dfns2 = None.
  Proof.
    intros dfns1 dfns2 r1 r2 [MEM LUP] REF L.
    unfold IS1.LLVM.D.lookup_defn in L.

    destruct r2;
      dvalue_refine_strict_inv REF; cbn in *;
      try auto.

    destruct (lookup (PTOI.ptr_to_int a) dfns2) eqn:L';
      auto.

    apply lookup_member in L'.
    apply MEM in L'.
    apply member_lookup in L' as (v&L').
    erewrite <- AC1.addr_convert_ptoi in L'; eauto.
    rewrite L in L'.
    discriminate.
  Qed.

  Lemma allocate_arg_E1E2_rutt_strict_sound :
    forall (args : list string),
      rutt event_refine_strict event_res_refine_strict (Forall2 dvalue_refine_strict)
        (map_monad LLVM1.allocate_arg args)
        (map_monad allocate_arg args).
  Proof.
    intros args.
    induction args.
    - cbn; apply rutt_Ret.
      apply Forall2_nil.
    - cbn.
      eapply rutt_bind with (RR:=dvalue_refine_strict).
      { eapply rutt_bind with (RR:=dvalue_refine_strict).
        { apply trigger_alloca_E1E2_rutt_strict_sound.
        }

        intros r1 r2 H.
        eapply rutt_bind with (RR:=eq).
        apply Store_E1E2_rutt'; auto.
        apply i8_array_of_string_fin_inf.

        intros [] [] _.
        apply rutt_Ret; auto.
      }

      intros r1 r2 R1R2.
      eapply rutt_bind with (RR:=Forall2 dvalue_refine_strict); auto.

      intros r1' r2' R1R2'.
      subst.
      apply rutt_Ret.
      constructor; auto.
  Qed.

  Lemma allocate_args_fin_inf :
    forall args,
      rutt event_refine_strict event_res_refine_strict 
        dvalue_refine_strict (LLVM1.allocate_args args) (allocate_args args).
  Proof.
    intros args.
    unfold LLVM1.allocate_args, allocate_args.
    eapply rutt_bind.
    - apply trigger_alloca_E1E2_rutt_strict_sound.
    - intros r1 r2 H.
      eapply rutt_bind.
      apply allocate_arg_E1E2_rutt_strict_sound.

      intros r0 r3 H0.
      eapply rutt_bind.
      { apply Store_E1E2_rutt'; auto.
        change ((DV1.UVALUE_Array (DTYPE_Array (N.of_nat (Datatypes.length args)) DTYPE_Pointer)
                   (map DV1.dvalue_to_uvalue r0))) with
          (DV1.dvalue_to_uvalue (DV1.DVALUE_Array (DTYPE_Array (N.of_nat (Datatypes.length args)) DTYPE_Pointer) r0)).
        change (UVALUE_Array (DTYPE_Array (N.of_nat (Datatypes.length args)) DTYPE_Pointer)
                  (map dvalue_to_uvalue r3)) with
          (DV2.dvalue_to_uvalue
             (DVALUE_Array (DTYPE_Array (N.of_nat (Datatypes.length args)) DTYPE_Pointer)
                r3)).
        apply dvalue_refine_strict_dvalue_to_uvalue.
        red; cbn.
        apply map_monad_oom_Forall2 in H0.
        rewrite H0.
        reflexivity.
      }

      intros [] [] _.
      apply rutt_Ret; auto.
  Qed.

  Lemma build_main_args_fin_inf
    (args : list string) :
    rutt event_refine_strict event_res_refine_strict (Forall2 uvalue_refine_strict) (LLVM1.build_main_args args) (build_main_args args).
  Proof.
    unfold build_main_args, LLVM1.build_main_args.
    eapply rutt_bind.
    - apply allocate_args_fin_inf.
    - intros r1 r2 H.
      apply rutt_Ret.
      constructor; try solve_uvalue_refine_strict.
      constructor; eauto.
      apply dvalue_refine_strict_dvalue_to_uvalue; eauto.
  Qed.

End FunctionsRefine.
