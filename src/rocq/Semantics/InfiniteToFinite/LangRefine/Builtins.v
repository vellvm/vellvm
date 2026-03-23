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
  Functions.

From Vellvm.Syntax Require Import
  DynamicTypes
  CFG.

Import MonadNotation.
Import ListNotations.

Module Type BuiltinsRefine
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
                BLOCK_REF).

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
  Import DVC.
  Import TLR2.
  Import IS2.LLVM.MEM.CP.CONCBASE.
  Import ACS.

  Lemma address_one_builtin_functions_E1E2_orutt :
    forall dfns1 dfns2,
      Forall2 (eq × function_denotation_refine_strict) dfns1 dfns2 ->
      orutt event_refine_strict event_res_refine_strict
        (Forall2 (eq × function_denotation_refine_strict))
        (map_monad LLVM1.address_one_builtin_function dfns1)
        (map_monad address_one_builtin_function dfns2)
        (OOM:=OOME).
  Proof.
    intros dfns1 dfns2 EQV.
    eapply map_monad_orutt2 with (VV:=prod_rel eq function_denotation_refine_strict); eauto.
    intros [id1 f1] [id2 f2] EQV'.
    inv EQV'.
    cbn in *; subst.
    eapply orutt_bind with (RR:=dvalue_refine_strict).
    { eapply rutt_orutt.
      apply GlobalRead_L0_E1E2_rutt.
      intros A e2.
      apply L0_dec_oom.
    }

    intros r1 r2 H.
    destruct r2;
      dvalue_refine_strict_inv H; cbn in *;
      try solve_orutt_raise.
    eapply orutt_Ret.
    constructor; eauto.
    cbn.
    erewrite <- AC1.addr_convert_ptoi; eauto.
  Qed.

  Lemma i8_str_index_refine :
    forall ix addr1 addr2,
      addr_refine addr1 addr2 ->
      orutt (OOM:=OOME) L0'_refine_strict L0'_res_refine_strict eq
        (LLVM1.i8_str_index addr1 ix) (LLVM2.i8_str_index addr2 ix).
  Proof.
    intros ix addr1 addr2 REF.
    unfold LLVM1.i8_str_index, LLVM2.i8_str_index.
    eapply orutt_bind with (RR:=fun ip_inf ip_fin => intptr_fin_inf ip_fin = ip_inf).
    { eapply orutt_L0'_from_Z. }

    intros r1 r2 R1R2.
    eapply orutt_bind with (RR:=addr_refine).
    { cbn.
      unfold intptr_fin_inf in R1R2.
      break_match_hyp.
      clear Heqs.
      subst.

      pose proof AC1.addr_convert_ptoi _ _ REF.
      rewrite H.
      rewrite sizeof_dtyp_fin_inf.
      assert (IS1.LP.IP.to_Z r1 = IP.to_Z r2).
      { eapply IS1.LP.IP.from_Z_to_Z in e.
        eauto.
      }

      (* Finite conversion *)
      destruct (ITOP.int_to_ptr (PTOI.ptr_to_int addr2 + Z.of_N (SZ.sizeof_dtyp (DTYPE_I 8)) * IP.to_Z r2)
                  (PROV.address_provenance addr2)) eqn:HITOP.
      2: apply orutt_raiseOOM.

      cbn.

      pose proof addr_convert_succeeds addr2 as (?&?).
      pose proof addr_convert_succeeds a as (?&?).
      pose proof HITOP as HITOP'.
      eapply addr_convert_int_to_ptr in HITOP'; eauto.

      assert (IS1.LP.PROV.address_provenance x = IS1.LP.PROV.address_provenance addr1).
      { clear - e0 REF.
        pose proof addr_convert_safe _ _ e0.
        pose proof AC1.addr_convert_injective _ _ _ REF H; subst.
        reflexivity.
      }

      rewrite H1 in HITOP'.
      rewrite H0.
      rewrite HITOP'.

      cbn.
      eapply orutt_Ret.
      eapply addr_convert_safe; eauto.
    }

    intros r0 r3 H.
    eapply orutt_bind with (RR:=uvalue_refine_strict).
    { eapply orutt_trigger.
      - repeat constructor.
        rewrite dvalue_refine_strict_equation; cbn.
        rewrite H.
        reflexivity.
      - intros t1 t2 H0.
        repeat red in H0.
        inv H0; subst_existT.
        inv H7; subst_existT.
        destruct H1; auto.
      - intros o CONTRA; inv CONTRA.
    }

    intros r4 r5 H0.
    eapply orutt_bind with (RR:=dvalue_refine_strict).
    { eapply concretize_or_pick_L0'_orutt_strict; eauto. }

    intros r6 r7 H1.
    destruct r6; rewrite dvalue_refine_strict_equation in H1;
      cbn in H1; inv H1; repeat break_match_hyp_inv;
      try solve [eapply orutt_raise; [intros * CONTRA; inv CONTRA | constructor; constructor]].

    repeat break_match_goal;
        try solve [apply orutt_raise; [intros ? ? CONTRA; inv CONTRA|repeat constructor]].
    eapply orutt_Ret.
    reflexivity.
  Qed.

  Opaque LLVM1.i8_str_index.
  Opaque LLVM2.i8_str_index.

  Lemma puts_denotation_refine_strict_helper :
    forall r1 r2,
      dvalue_refine_strict r1 r2 ->
      orutt (OOM:=OOME) L0'_refine_strict L0'_res_refine_strict uvalue_refine_strict
        match r1 with
        | DV1.DVALUE_Addr strptr =>
            ITree.bind (LLVM1.i8_str_index strptr 0)
              (fun (char : @Integers.bit_int 8) =>
                 ITree.bind
                   (ITree.iter
                      (fun '(c, bytes, offset) =>
                         if @Integers.eq 8 c (@Integers.zero 8)
                         then Ret (inr ((@Integers.repr 8 10) :: bytes))
                         else
                           ITree.bind (LLVM1.i8_str_index strptr offset)
                             (fun (next_char : @Integers.bit_int 8) => Ret (inl (next_char, c :: bytes, (offset + 1)%Z))))
                      (char, [], 1%Z))
                   (fun (bytes : list int8) =>
                      ITree.bind (trigger (LLVMEvents.IO_stdout (DList.rev_tail_rec bytes)))
                        (fun _ : unit => Ret (@DV1.UVALUE_I 8 (@Integers.zero 8)))))
        | _ => raiseUB "puts got non-address argument"
        end
        match r2 with
        | DVALUE_Addr strptr =>
            ITree.bind (i8_str_index strptr 0)
              (fun (char : @Integers.bit_int 8) =>
                 ITree.bind
                   (ITree.iter
                      (fun '(c, bytes, offset) =>
                         if @Integers.eq 8 c (@Integers.zero 8)
                         then Ret (inr (@Integers.repr 8 10 :: bytes))
                         else
                           ITree.bind (i8_str_index strptr offset)
                             (fun (next_char : @Integers.bit_int 8) => Ret (inl (next_char, c :: bytes, (offset + 1)%Z))))
                      (char, [], 1%Z))
                   (fun bytes : list int8 =>
                      ITree.bind (trigger (IO_stdout (DList.rev_tail_rec bytes)))
                        (fun _ : unit => Ret (@UVALUE_I 8 Integers.zero))))
        | _ => raiseUB "puts got non-address argument"
        end.
  Proof.
    intros r1 r2 REF.
    destruct r1; rewrite dvalue_refine_strict_equation in REF; cbn in REF;
      inv REF; try break_match_hyp_inv;
      try solve [eapply orutt_raiseUB; [intros * CONTRA; inv CONTRA | constructor; constructor]].

    eapply orutt_bind with (RR:=eq).
    { eapply i8_str_index_refine; eauto. }

    intros r1 r2 R1R2; subst.
    eapply orutt_bind with (RR:=eq).
    { eapply orutt_iter' with (RI:=eq).
      2: reflexivity.

      intros j1 j2 H.
      subst.
      destruct j2 as ((?&?)&?).

      break_match_goal.
      { eapply orutt_Ret.
        constructor; reflexivity.
      }

      eapply orutt_bind with (RR:=eq).
      2: intros; subst; eapply orutt_Ret; constructor; reflexivity.
      eapply i8_str_index_refine; eauto.
    }

    intros r1 r0 H; subst.

    eapply orutt_bind with (RR:=eq).
    { eapply orutt_trigger.
      - repeat constructor.
      - intros [] [] ?.
        reflexivity.
      - intros o CONTRA; inv CONTRA.
    }

    intros [] [] _.
    eapply orutt_Ret.
    rewrite uvalue_refine_strict_equation.
    cbn.
    reflexivity.
  Qed.

  Lemma puts_denotation_refine_strict :
    function_denotation_refine_strict LLVM1.puts_denotation LLVM2.puts_denotation.
  Proof.
    red.
    intros args1 args2 ARGS.
    induction ARGS.
    - cbn.
      apply orutt_raise.
      + intros [] o CONTRA.
        inv CONTRA.
      + repeat red.
        constructor.
        cbn; auto.
    - destruct ARGS.
      2: {
        cbn.
        apply orutt_raise.
        + intros [] o CONTRA.
          inv CONTRA.
        + repeat red.
          constructor.
          cbn; auto.
      }
      destruct x;
        try solve
          [rewrite uvalue_refine_strict_equation in H;
           cbn in H; inv H;
           repeat break_match_hyp_inv;
           cbn;
           try solve
             [ setoid_rewrite bind_ret_l;
               eapply orutt_raiseUB; [intros * CONTRA; inv CONTRA | constructor; constructor]
             | eapply orutt_bind with (RR:=fun r1 r2 => dvalue_refine_strict r1 r2);
               [ eapply concretize_or_pick_L0'_orutt_strict;
                 rewrite uvalue_refine_strict_equation;
                 cbn;
                 rewrite Heqo;
                 reflexivity
               | intros *;
                 eapply puts_denotation_refine_strict_helper; eauto
               ]
             | eapply orutt_bind with (RR:=fun r1 r2 => dvalue_refine_strict r1 r2);
               [ eapply orutt_bind with (RR:=fun r1 r2 => dvalue_refine_strict (proj1_sig r1) (proj1_sig r2))|];
               [ eapply orutt_trigger;
                 [ repeat constructor;
                   cbn;
                   rewrite uvalue_refine_strict_equation;
                   cbn;
                   try rewrite Heqo;
                   try rewrite Heqo0;
                   try rewrite Heqo1;
                   reflexivity
                 | intros * REF;
                   destruct t1, t2; cbn in *;
                   inv REF; subst_existT;
                   inv H5; subst_existT; eauto
                 | intros * CONTRA; inv CONTRA
                 ]
               | intros [r1 ?] [r2 ?] REF;
                 eapply orutt_Ret; eauto
               | intros r1 r2 REF;
                 eapply puts_denotation_refine_strict_helper; eauto
               ]
             ]
          ].

      rewrite uvalue_refine_strict_equation in H;
        cbn in H; inv H;
        repeat break_match_hyp_inv;
        cbn.
      repeat rewrite bind_ret_l.

      eapply orutt_bind with (RR:=eq).
      { eapply i8_str_index_refine; eauto. }

      intros ? ? ?; subst.
      eapply orutt_bind with (RR:=eq).
      { eapply orutt_iter' with (RI:=eq).
        2: reflexivity.

        intros j1 j2 H.
        subst.
        destruct j2 as ((?&?)&?).

        break_match_goal.
        { eapply orutt_Ret.
          constructor; reflexivity.
        }

        eapply orutt_bind with (RR:=eq).
        2: intros; subst; eapply orutt_Ret; constructor; reflexivity.
        eapply i8_str_index_refine; eauto.
      }

      intros ? ? ?; subst.
      eapply orutt_bind with (RR:=eq).
      eapply orutt_trigger;
        [ repeat constructor;
          cbn;
          rewrite uvalue_refine_strict_equation;
          cbn;
          try rewrite Heqo;
          try rewrite Heqo0;
          try rewrite Heqo1;
          reflexivity
        | intros * REF;
          destruct t1, t2; cbn in *;
          inv REF; subst_existT;
          inv H5; subst_existT; eauto
        | intros * CONTRA; inv CONTRA
        ].

      intros [] [] _.
      eapply orutt_Ret.
      rewrite uvalue_refine_strict_equation; cbn; eauto.
  Qed.

  Opaque Pos.eq_dec.

  Lemma putchar_denotation_refine_strict :
    function_denotation_refine_strict LLVM1.putchar_denotation LLVM2.putchar_denotation.
  Proof.
    red.
    intros args1 args2 ARGS.
    induction ARGS.
    - cbn.
      apply orutt_raise.
      + intros [] o CONTRA.
        inv CONTRA.
      + repeat red.
        constructor.
        cbn; auto.
    - destruct ARGS.
      2: {
        cbn.
        apply orutt_raise.
        + intros [] o CONTRA.
          inv CONTRA.
        + repeat red.
          constructor.
          cbn; auto.
      }

      destruct y; uvalue_refine_strict_inv H.
      all:
        try solve
          [ eapply orutt_bind with (RR:=dvalue_refine_strict);
            solve [ eapply orutt_bind with (RR:=fun r1 r2 => dvalue_refine_strict (proj1_sig r1) (proj1_sig r2));
                    [ apply orutt_trigger;
                      [ repeat constructor; cbn;
                        rewrite uvalue_refine_strict_equation; cbn;
                        try rewrite H0; try rewrite H1; try rewrite H2; reflexivity
                      | intros [dv1 []] [dv2 []] REF;
                        inv REF; subst_existT; cbn;
                        match goal with
                        | H: event_res_refine_strict _ _ _ _ _ _ |- _ =>
                            apply H
                        end
                      | intros ? CONTRA; inv CONTRA
                      ]
                    | intros [dv1 []] [dv2 []] REF;
                      eapply orutt_Ret; eauto; solve_uvalue_refine_strict
                    ]
                  | intros r1 r2 REF;
                    destruct r2; dvalue_refine_strict_inv REF;
                    try destruct (Pos.eq_dec 32 sz);
                    try (eapply orutt_raiseUB;
                         [ intros ? ? CONTRA; inv CONTRA
                         | repeat constructor
                      ]);
                    eapply orutt_bind with (RR:=eq); subst; cbn; eauto with ORUTT;
                    break_match; try contradiction; subst; cbn;
                    dependent destruction e; cbn;
                    eapply orutt_trigger; eauto with ORUTT;
                    [ repeat constructor
                    | intros [] [] ?; reflexivity
                    | intros ? CONTRA; inv CONTRA
                    ]
                  | cbn;
                    eapply concretize_or_pick_L0'_orutt_strict;
                    rewrite uvalue_refine_strict_equation; cbn; rewrite H0; reflexivity
              ]
          ].

      all:
        try solve [ cbn;
                    setoid_rewrite bind_ret_l;
                    eapply orutt_raiseUB; [intros * CONTRA; inv CONTRA | constructor; constructor]
          ].

      cbn.
      repeat rewrite bind_ret_l.
      break_match_goal; subst; cbn;
        try solve [eapply orutt_raiseUB; [intros * CONTRA; inv CONTRA | constructor; constructor]].

      break_match_goal; subst; try contradiction; cbn.
      dependent destruction e; cbn.
      eapply orutt_bind with (RR:=eq); eauto with ORUTT.
      { apply orutt_trigger;
          [ solve [repeat constructor]
          | intros [] [] ?; reflexivity
          | intros ? CONTRA; inv CONTRA
          ].
      }
  Qed.

  Lemma builtins_refine_strict :
    forall decs,
      Forall2 (eq × function_denotation_refine_strict)
        (LLVM1.built_in_functions decs)
        (built_in_functions decs).
  Proof.
    intros decs.
    induction decs.
    - cbn; constructor.
    - unfold built_in_functions.
      unfold LLVM1.built_in_functions.
      cbn.

      (* puts *)
      break_match_goal; try constructor; eauto.
      constructor; cbn; auto.
      apply puts_denotation_refine_strict.

      (* putchar *)
      break_match_goal; try constructor; eauto.
      constructor; cbn; auto.
      apply putchar_denotation_refine_strict.

      break_match_goal; try constructor; eauto.
      constructor; eauto.
      cbn.
      apply putchar_denotation_refine_strict.
  Qed.

End BuiltinsRefine.
