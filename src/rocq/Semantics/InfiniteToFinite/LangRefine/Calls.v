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
  Expressions.

From Vellvm.Syntax Require Import
  DynamicTypes
  CFG.

Import MonadNotation.
Import ListNotations.

Module Type CallsRefine
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
               EXP_REF).

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
  Import DVC.
  Import TLR2.
  Import IS2.LLVM.MEM.CP.CONCBASE.
  Import ACS.

  Lemma orutt_trigger_Intrinsic :
    forall E1 E2
      `{OOM1 : OOME -< E1} `{OOM2 : OOME -< E2}
      `{INT1 : IntrinsicE DV1.dvalue DV1.uvalue -< E1} `{INT2 : IntrinsicE DV2.dvalue DV2.uvalue -< E2}
      (pre : prerel E1 E2) (post : postrel E1 E2)
      (INTDISC : forall e (o : OOME _), INT2 _ e <> subevent (DV2.uvalue + DV2.dvalue) o)
      dt s
      (args1 : list DV1.dvalue) (args2 : list DV2.dvalue)
      (REF: pre (DV1.uvalue + DV1.dvalue)%type (DV2.uvalue + DV2.dvalue)%type
                                    (INT1 (DV1.uvalue + DV1.dvalue)%type (@Intrinsic DV1.dvalue DV1.uvalue dt s args1))
                                    (INT2 (DV2.uvalue + DV2.dvalue)%type (@Intrinsic _ _ dt s args2)))
      (POST: forall dt s (t1 : DV1.uvalue + DV1.dvalue) (t2 : DV2.uvalue + DV2.dvalue),
          post (DV1.uvalue + DV1.dvalue)%type (DV2.uvalue + DV2.dvalue)%type
            (INT1 (DV1.uvalue + DV1.dvalue)%type (@Intrinsic _ _ dt s args1)) t1
            (INT2 (DV2.uvalue + DV2.dvalue)%type (@Intrinsic _ _ dt s args2)) t2 ->
          sum_rel uvalue_refine_strict dvalue_refine_strict t1 t2),
      orutt (OOM:=OOME) pre post (sum_rel uvalue_refine_strict dvalue_refine_strict) (trigger (@Intrinsic _ _ dt s args1))
    (trigger (Intrinsic dt s args2)).
  Proof.
    intros.
    apply orutt_trigger; eauto.
  Qed.

  Lemma orutt_trigger_Call :
    forall E1 E2
      `{OOM1 : OOME -< E1} `{OOM2 : OOME -< E2}
      `{CALL1 : CallE DV1.uvalue -< E1} `{CALL2 : CallE DV2.uvalue -< E2}
      (pre : prerel E1 E2) (post : postrel E1 E2)
      (CALLDISC : forall e (o : OOME _), CALL2 _ e <> subevent (DV2.uvalue + DV2.uvalue) o)
      dt (f1 : DV1.uvalue) (f2 : DV2.uvalue)
      (args1 : list DV1.uvalue) (args2 : list DV2.uvalue)
      (REF: pre (DV1.uvalue + DV1.uvalue)%type (DV2.uvalue + DV2.uvalue)%type
              (CALL1 (DV1.uvalue + DV1.uvalue)%type (LLVMEvents.Call dt f1 args1))
              (CALL2 (DV2.uvalue + DV2.uvalue)%type (LLVMEvents.Call dt f2 args2)))
      (POST: forall dt f1 f2 (t1 : DV1.uvalue + DV1.uvalue) (t2 : DV2.uvalue + DV2.uvalue),
          post (DV1.uvalue + DV1.uvalue)%type (DV2.uvalue + DV2.uvalue)%type
            (CALL1 (DV1.uvalue + DV1.uvalue)%type (LLVMEvents.Call dt f1 args1)) t1
            (CALL2 (DV2.uvalue + DV2.uvalue)%type (LLVMEvents.Call dt f2 args2)) t2 ->
          sum_rel uvalue_refine_strict uvalue_refine_strict t1 t2),
      orutt (OOM:=OOME) pre post
        (sum_rel uvalue_refine_strict uvalue_refine_strict)
        (trigger (LLVMEvents.Call dt f1 args1))
        (trigger (LLVMEvents.Call dt f2 args2)).
  Proof.
    intros.
    apply orutt_trigger; eauto.
  Qed.

  #[global] Hint Resolve
    orutt_trigger_Intrinsic
    orutt_trigger_Call : ORUTT.

  Lemma llvm_fabs_f32_agrees_fail :
    forall args1 args2 s,
      Forall2 dvalue_refine_strict args1 args2 ->
      IS1.LLVM.Intrinsics.llvm_fabs_f32 args1 = inl s ->
      IS2.LLVM.Intrinsics.llvm_fabs_f32 args2 = inl s.
  Proof.
    intros args1 args2 s ARGS EXEC.
    destruct ARGS; cbn in *; try congruence.
    destruct x;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct ARGS; cbn in *;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].
  Qed.

  Lemma llvm_fabs_f32_agrees_success :
    forall args1 args2 d1,
      Forall2 dvalue_refine_strict args1 args2 ->
      IS1.LLVM.Intrinsics.llvm_fabs_f32 args1 = inr d1 ->
      exists d2,
        IS2.LLVM.Intrinsics.llvm_fabs_f32 args2 = inr d2 /\
          sum_rel uvalue_refine_strict dvalue_refine_strict d1 d2.
  Proof.
    intros args1 args2 s ARGS EXEC.
    destruct ARGS; cbn in *; try congruence.
    destruct x;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct ARGS; cbn in *;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    inv EXEC.
    unfold_dvalue_refine_strict_in H.
    inv H.
    eexists.
    split; eauto.
    constructor; eauto.
    unfold_dvalue_refine_strict.
    reflexivity.
  Qed.

  Lemma llvm_fabs_f64_agrees_fail :
    forall args1 args2 s,
      Forall2 dvalue_refine_strict args1 args2 ->
      IS1.LLVM.Intrinsics.llvm_fabs_f64 args1 = inl s ->
      IS2.LLVM.Intrinsics.llvm_fabs_f64 args2 = inl s.
  Proof.
    intros args1 args2 s ARGS EXEC.
    destruct ARGS; cbn in *; try congruence.
    destruct x;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct ARGS; cbn in *;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].
  Qed.

  Lemma llvm_fabs_f64_agrees_success :
    forall args1 args2 d1,
      Forall2 dvalue_refine_strict args1 args2 ->
      IS1.LLVM.Intrinsics.llvm_fabs_f64 args1 = inr d1 ->
      exists d2,
        IS2.LLVM.Intrinsics.llvm_fabs_f64 args2 = inr d2 /\
          sum_rel uvalue_refine_strict dvalue_refine_strict d1 d2.
  Proof.
    intros args1 args2 s ARGS EXEC.
    destruct ARGS; cbn in *; try congruence.
    destruct x;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct ARGS; cbn in *;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    inv EXEC.
    unfold_dvalue_refine_strict_in H.
    inv H.
    eexists.
    split; eauto.
    constructor; eauto.
    unfold_dvalue_refine_strict.
    reflexivity.
  Qed.

  Lemma llvm_maxnum_f32_agrees_fail :
    forall args1 args2 s,
      Forall2 dvalue_refine_strict args1 args2 ->
      IS1.LLVM.Intrinsics.llvm_maxnum_f32 args1 = inl s ->
      IS2.LLVM.Intrinsics.llvm_maxnum_f32 args2 = inl s.
  Proof.
    intros args1 args2 s ARGS EXEC.
    destruct ARGS; cbn in *; try congruence.
    destruct x;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct ARGS; cbn in *;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    unfold_dvalue_refine_strict_in H; inv H.

    destruct ARGS; cbn in *; destruct x0;
      try
        solve
        [ unfold_dvalue_refine_strict_in H0;
          cbn in *;
          try break_match_hyp_inv;
          try inv H0;
          try congruence
        ].
  Qed.

  Lemma llvm_maxnum_f32_agrees_success :
    forall args1 args2 d1,
      Forall2 dvalue_refine_strict args1 args2 ->
      IS1.LLVM.Intrinsics.llvm_maxnum_f32 args1 = inr d1 ->
      exists d2,
        IS2.LLVM.Intrinsics.llvm_maxnum_f32 args2 = inr d2 /\
          sum_rel uvalue_refine_strict dvalue_refine_strict d1 d2.
  Proof.
    intros args1 args2 s ARGS EXEC.
    destruct ARGS; cbn in *; try congruence.
    destruct x;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct ARGS; cbn in *;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    unfold_dvalue_refine_strict_in H; inv H.

    destruct ARGS; cbn in *; destruct x0;
      try
        solve
        [ unfold_dvalue_refine_strict_in H0;
          cbn in *;
          try break_match_hyp_inv;
          try inv H0;
          try congruence
        ].

    inv EXEC.
    unfold_dvalue_refine_strict_in H0.
    inv H0.
    eexists.
    split; eauto.
    constructor; eauto.
    unfold_dvalue_refine_strict.
    reflexivity.
  Qed.

  Lemma llvm_maxnum_f64_agrees_fail :
    forall args1 args2 s,
      Forall2 dvalue_refine_strict args1 args2 ->
      IS1.LLVM.Intrinsics.llvm_maxnum_f64 args1 = inl s ->
      IS2.LLVM.Intrinsics.llvm_maxnum_f64 args2 = inl s.
  Proof.
    intros args1 args2 s ARGS EXEC.
    destruct ARGS; cbn in *; try congruence.
    destruct x;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct ARGS; cbn in *;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    unfold_dvalue_refine_strict_in H; inv H.

    destruct ARGS; cbn in *; destruct x0;
      try
        solve
        [ unfold_dvalue_refine_strict_in H0;
          cbn in *;
          try break_match_hyp_inv;
          try inv H0;
          try congruence
        ].
  Qed.

  Lemma llvm_maxnum_f64_agrees_success :
    forall args1 args2 d1,
      Forall2 dvalue_refine_strict args1 args2 ->
      IS1.LLVM.Intrinsics.llvm_maxnum_f64 args1 = inr d1 ->
      exists d2,
        IS2.LLVM.Intrinsics.llvm_maxnum_f64 args2 = inr d2 /\
          sum_rel uvalue_refine_strict dvalue_refine_strict d1 d2.
  Proof.
    intros args1 args2 s ARGS EXEC.
    destruct ARGS; cbn in *; try congruence.
    destruct x;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct ARGS; cbn in *;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    unfold_dvalue_refine_strict_in H; inv H.

    destruct ARGS; cbn in *; destruct x0;
      try
        solve
        [ unfold_dvalue_refine_strict_in H0;
          cbn in *;
          try break_match_hyp_inv;
          try inv H0;
          try congruence
        ].

    inv EXEC.
    unfold_dvalue_refine_strict_in H0.
    inv H0.
    eexists.
    split; eauto.
    constructor; eauto.
    unfold_dvalue_refine_strict.
    reflexivity.
  Qed.

  Lemma llvm_minimum_f32_agrees_fail :
    forall args1 args2 s,
      Forall2 dvalue_refine_strict args1 args2 ->
      IS1.LLVM.Intrinsics.llvm_minimum_f32 args1 = inl s ->
      IS2.LLVM.Intrinsics.llvm_minimum_f32 args2 = inl s.
  Proof.
    intros args1 args2 s ARGS EXEC.
    destruct ARGS; cbn in *; try congruence.
    destruct x;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct ARGS; cbn in *;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    unfold_dvalue_refine_strict_in H; inv H.

    destruct ARGS; cbn in *; destruct x0;
      try
        solve
        [ unfold_dvalue_refine_strict_in H0;
          cbn in *;
          try break_match_hyp_inv;
          try inv H0;
          try congruence
        ].
  Qed.

  Lemma llvm_minimum_f32_agrees_success :
    forall args1 args2 d1,
      Forall2 dvalue_refine_strict args1 args2 ->
      IS1.LLVM.Intrinsics.llvm_minimum_f32 args1 = inr d1 ->
      exists d2,
        IS2.LLVM.Intrinsics.llvm_minimum_f32 args2 = inr d2 /\
          sum_rel uvalue_refine_strict dvalue_refine_strict d1 d2.
  Proof.
    intros args1 args2 s ARGS EXEC.
    destruct ARGS; cbn in *; try congruence.
    destruct x;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct ARGS; cbn in *;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    unfold_dvalue_refine_strict_in H; inv H.

    destruct ARGS; cbn in *; destruct x0;
      try
        solve
        [ unfold_dvalue_refine_strict_in H0;
          cbn in *;
          try break_match_hyp_inv;
          try inv H0;
          try congruence
        ].

    inv EXEC.
    unfold_dvalue_refine_strict_in H0.
    inv H0.
    eexists.
    split; eauto.
    constructor; eauto.
    unfold_dvalue_refine_strict.
    reflexivity.
  Qed.

  Lemma llvm_minimum_f64_agrees_fail :
    forall args1 args2 s,
      Forall2 dvalue_refine_strict args1 args2 ->
      IS1.LLVM.Intrinsics.llvm_minimum_f64 args1 = inl s ->
      IS2.LLVM.Intrinsics.llvm_minimum_f64 args2 = inl s.
  Proof.
    intros args1 args2 s ARGS EXEC.
    destruct ARGS; cbn in *; try congruence.
    destruct x;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct ARGS; cbn in *;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    unfold_dvalue_refine_strict_in H; inv H.

    destruct ARGS; cbn in *; destruct x0;
      try
        solve
        [ unfold_dvalue_refine_strict_in H0;
          cbn in *;
          try break_match_hyp_inv;
          try inv H0;
          try congruence
        ].
  Qed.

  Lemma llvm_minimum_f64_agrees_success :
    forall args1 args2 d1,
      Forall2 dvalue_refine_strict args1 args2 ->
      IS1.LLVM.Intrinsics.llvm_minimum_f64 args1 = inr d1 ->
      exists d2,
        IS2.LLVM.Intrinsics.llvm_minimum_f64 args2 = inr d2 /\
          sum_rel uvalue_refine_strict dvalue_refine_strict d1 d2.
  Proof.
    intros args1 args2 s ARGS EXEC.
    destruct ARGS; cbn in *; try congruence.
    destruct x;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct ARGS; cbn in *;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    unfold_dvalue_refine_strict_in H; inv H.

    destruct ARGS; cbn in *; destruct x0;
      try
        solve
        [ unfold_dvalue_refine_strict_in H0;
          cbn in *;
          try break_match_hyp_inv;
          try inv H0;
          try congruence
        ].

    inv EXEC.
    unfold_dvalue_refine_strict_in H0.
    inv H0.
    eexists.
    split; eauto.
    constructor; eauto.
    unfold_dvalue_refine_strict.
    reflexivity.
  Qed.

  Lemma llvm_ushl_sat_1_agrees_success :
    forall args1 args2 d1,
      Forall2 dvalue_refine_strict args1 args2 ->
      IS1.LLVM.Intrinsics.llvm_ushl_sat_1 args1 = inr d1 ->
      exists d2,
        IS2.LLVM.Intrinsics.llvm_ushl_sat_1 args2 = inr d2 /\
          sum_rel uvalue_refine_strict dvalue_refine_strict d1 d2.
  Proof.
    intros args1 args2 s ARGS EXEC.
    destruct ARGS; cbn in *; try congruence.
    destruct x;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct y;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct ARGS; cbn in *;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    dvalue_refine_strict_inv H; inv H; subst_existT.
    repeat break_match_hyp_inv; subst_existT; cbn; inv ARGS;
      unfold_dvalue_refine_strict; inv H0;
      eexists; split; eauto;
      try rewrite Heqb;
      try rewrite Heqb0;
      try solve_dvalue_refine_strict; auto.
  Qed.

  Lemma llvm_ushl_sat_8_agrees_success :
    forall args1 args2 d1,
      Forall2 dvalue_refine_strict args1 args2 ->
      IS1.LLVM.Intrinsics.llvm_ushl_sat_8 args1 = inr d1 ->
      exists d2,
        IS2.LLVM.Intrinsics.llvm_ushl_sat_8 args2 = inr d2 /\
          sum_rel uvalue_refine_strict dvalue_refine_strict d1 d2.
  Proof.
    intros args1 args2 s ARGS EXEC.
    destruct ARGS; cbn in *; try congruence.
    destruct x;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct y;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct ARGS; cbn in *;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          repeat break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    dvalue_refine_strict_inv H; inv H; subst_existT;
      repeat break_match_hyp_inv; subst_existT; cbn; inv ARGS;
      unfold_dvalue_refine_strict; inv H0;
      eexists; split; eauto;
      try rewrite Heqb;
      try rewrite Heqb0;
      try solve_dvalue_refine_strict; auto.
  Qed.

  Lemma llvm_ushl_sat_16_agrees_success :
    forall args1 args2 d1,
      Forall2 dvalue_refine_strict args1 args2 ->
      IS1.LLVM.Intrinsics.llvm_ushl_sat_16 args1 = inr d1 ->
      exists d2,
        IS2.LLVM.Intrinsics.llvm_ushl_sat_16 args2 = inr d2 /\
          sum_rel uvalue_refine_strict dvalue_refine_strict d1 d2.
  Proof.
    intros args1 args2 s ARGS EXEC.
    destruct ARGS; cbn in *; try congruence.
    destruct x;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct y;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct ARGS; cbn in *;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          repeat break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    dvalue_refine_strict_inv H; inv H; subst_existT;
      repeat break_match_hyp_inv; subst_existT; cbn; inv ARGS;
      unfold_dvalue_refine_strict; inv H0;
      eexists; split; eauto;
      try rewrite Heqb;
      try rewrite Heqb0;
      try solve_dvalue_refine_strict; auto.
  Qed.

  Lemma llvm_ushl_sat_32_agrees_success :
    forall args1 args2 d1,
      Forall2 dvalue_refine_strict args1 args2 ->
      IS1.LLVM.Intrinsics.llvm_ushl_sat_32 args1 = inr d1 ->
      exists d2,
        IS2.LLVM.Intrinsics.llvm_ushl_sat_32 args2 = inr d2 /\
          sum_rel uvalue_refine_strict dvalue_refine_strict d1 d2.
  Proof.
    intros args1 args2 s ARGS EXEC.
    destruct ARGS; cbn in *; try congruence.
    destruct x;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct y;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct ARGS; cbn in *;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          repeat break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    dvalue_refine_strict_inv H; inv H; subst_existT;
      repeat break_match_hyp_inv; subst_existT; cbn; inv ARGS;
      unfold_dvalue_refine_strict; inv H0;
      eexists; split; eauto;
      try rewrite Heqb;
      try rewrite Heqb0;
      try solve_dvalue_refine_strict; auto.
  Qed.

  Lemma llvm_ushl_sat_64_agrees_success :
    forall args1 args2 d1,
      Forall2 dvalue_refine_strict args1 args2 ->
      IS1.LLVM.Intrinsics.llvm_ushl_sat_64 args1 = inr d1 ->
      exists d2,
        IS2.LLVM.Intrinsics.llvm_ushl_sat_64 args2 = inr d2 /\
          sum_rel uvalue_refine_strict dvalue_refine_strict d1 d2.
  Proof.
    intros args1 args2 s ARGS EXEC.
    destruct ARGS; cbn in *; try congruence.
    destruct x;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct y;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct ARGS; cbn in *;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          repeat break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    dvalue_refine_strict_inv H; inv H; subst_existT;
      repeat break_match_hyp_inv; subst_existT; cbn; inv ARGS;
      unfold_dvalue_refine_strict; inv H0;
      eexists; split; eauto;
      try rewrite Heqb;
      try rewrite Heqb0;
      try solve_dvalue_refine_strict; auto.
  Qed.

  Lemma llvm_internal_throw_agrees_success :
    forall args1 args2 d1,
      Forall2 dvalue_refine_strict args1 args2 ->
      IS1.LLVM.Intrinsics.llvm_vellvm_internal_throw args1 = inr d1 ->
      exists d2,
        IS2.LLVM.Intrinsics.llvm_vellvm_internal_throw args2 = inr d2 /\
          sum_rel uvalue_refine_strict dvalue_refine_strict d1 d2.
  Proof.
    intros args1 args2 s ARGS EXEC.
    destruct ARGS; cbn in *; try congruence; inv EXEC.
    eexists; split; eauto.
    constructor; eauto.
    constructor; eauto.
  Qed.

  Lemma llvm_ushl_sat_1_agrees_fail :
    forall args1 args2 s,
      Forall2 dvalue_refine_strict args1 args2 ->
      IS1.LLVM.Intrinsics.llvm_ushl_sat_1 args1 = inl s ->
      IS2.LLVM.Intrinsics.llvm_ushl_sat_1 args2 = inl s.
  Proof.
    intros args1 args2 s ARGS EXEC.
    destruct ARGS; cbn in *; try congruence.
    destruct x;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct y;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    dvalue_refine_strict_inv H; inv H; subst_existT.
    repeat break_match_hyp_inv; subst_existT; cbn; inv ARGS; auto;
      unfold_dvalue_refine_strict; inv H1;
      repeat break_match_hyp_inv; auto.

    inv H3; auto.
  Qed.

  Lemma llvm_ushl_sat_8_agrees_fail :
    forall args1 args2 s,
      Forall2 dvalue_refine_strict args1 args2 ->
      IS1.LLVM.Intrinsics.llvm_ushl_sat_8 args1 = inl s ->
      IS2.LLVM.Intrinsics.llvm_ushl_sat_8 args2 = inl s.
  Proof.
    intros args1 args2 s ARGS EXEC.
    destruct ARGS; cbn in *; try congruence.
    destruct x;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct y;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    dvalue_refine_strict_inv H; inv H; subst_existT.
    repeat break_match_hyp_inv; subst_existT; cbn; inv ARGS; auto;
      unfold_dvalue_refine_strict; inv H1;
      repeat break_match_hyp_inv; auto.

    inv H3; auto.
  Qed.

  Lemma llvm_ushl_sat_16_agrees_fail :
    forall args1 args2 s,
      Forall2 dvalue_refine_strict args1 args2 ->
      IS1.LLVM.Intrinsics.llvm_ushl_sat_16 args1 = inl s ->
      IS2.LLVM.Intrinsics.llvm_ushl_sat_16 args2 = inl s.
  Proof.
    intros args1 args2 s ARGS EXEC.
    destruct ARGS; cbn in *; try congruence.
    destruct x;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct y;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    dvalue_refine_strict_inv H; inv H; subst_existT.
    repeat break_match_hyp_inv; subst_existT; cbn; inv ARGS; auto;
      unfold_dvalue_refine_strict; inv H1;
      repeat break_match_hyp_inv; auto.

    inv H3; auto.
  Qed.

  Lemma llvm_ushl_sat_32_agrees_fail :
    forall args1 args2 s,
      Forall2 dvalue_refine_strict args1 args2 ->
      IS1.LLVM.Intrinsics.llvm_ushl_sat_32 args1 = inl s ->
      IS2.LLVM.Intrinsics.llvm_ushl_sat_32 args2 = inl s.
  Proof.
    intros args1 args2 s ARGS EXEC.
    destruct ARGS; cbn in *; try congruence.
    destruct x;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct y;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    dvalue_refine_strict_inv H; inv H; subst_existT.
    repeat break_match_hyp_inv; subst_existT; cbn; inv ARGS; auto;
      unfold_dvalue_refine_strict; inv H1;
      repeat break_match_hyp_inv; auto.

    inv H3; auto.
  Qed.

  Lemma llvm_ushl_sat_64_agrees_fail :
    forall args1 args2 s,
      Forall2 dvalue_refine_strict args1 args2 ->
      IS1.LLVM.Intrinsics.llvm_ushl_sat_64 args1 = inl s ->
      IS2.LLVM.Intrinsics.llvm_ushl_sat_64 args2 = inl s.
  Proof.
    intros args1 args2 s ARGS EXEC.
    destruct ARGS; cbn in *; try congruence.
    destruct x;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    destruct y;
      try
        solve
        [ unfold_dvalue_refine_strict_in H;
          cbn in *;
          try break_match_hyp_inv;
          try inv H;
          try congruence
        ].

    dvalue_refine_strict_inv H; inv H; subst_existT.
    repeat break_match_hyp_inv; subst_existT; cbn; inv ARGS; auto;
      unfold_dvalue_refine_strict; inv H1;
      repeat break_match_hyp_inv; auto.

    inv H3; auto.
  Qed.

  Lemma llvm_internal_throw_agrees_fail :
    forall args1 args2 s,
      Forall2 dvalue_refine_strict args1 args2 ->
      IS1.LLVM.Intrinsics.llvm_vellvm_internal_throw args1 = inl s ->
      IS2.LLVM.Intrinsics.llvm_vellvm_internal_throw args2 = inl s.
  Proof.
    intros args1 args2 s ARGS EXEC.
    destruct ARGS; cbn in *; try congruence; inv EXEC.
  Qed.

  Lemma orutt_interp_intrinsics_h :
    forall A B e1 e2,
      event_refine_strict A B e1 e2 ->
      orutt event_refine_strict event_res_refine_strict
        (fun (a : A) (b : B) => event_res_refine_strict A B e1 a e2 b)
        (IS1.LLVM.Intrinsics.interp_intrinsics_h e1) (interp_intrinsics_h e2)
        (OOM:=OOME).
  Proof.
    intros A B e1 e2 REF.
    destruct e1; repeat (destruct e); repeat (destruct s).
    try
      solve
        [
          cbn in REF;
          destruct e2; try inv REF;
          repeat (break_match_hyp; try inv REF);
          cbn in *;
          pstep; red; cbn;
          constructor; cbn; auto;
          [ intros ? ? ?;
              left;
            pstep; red; cbn;
            constructor; auto
          | intros o CONTRA; inv CONTRA
          ]
        ].

    all: try
           solve
           [ cbn in REF;
             destruct e2; try inv REF;
             repeat (break_match_hyp; try inv REF);
             cbn in *;
             (pstep; red; cbn;
              constructor; cbn; try tauto;
              [ intros ? ? ?; left; apply orutt_Ret; tauto
              | intros o CONTRA; inv CONTRA
             ])
           |
             cbn in REF;
             destruct e2; try inv REF;
             repeat (break_match_hyp; try inv REF);
             cbn in *;
             (pstep; red; cbn;
              constructor; cbn;
              [ first [red; red; auto | tauto]
              | intros ? ? ?; left; apply orutt_Ret; tauto
              | intros o CONTRA; inv CONTRA
             ])
           ].
    -
      cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF; try red in REF);
        cbn in *.

      destruct H0 as [FEQ REFARGS]; subst.
      repeat break_inner_match_goal;
        try solve_orutt_raise.

      all:
        try solve
          [ pose proof (llvm_fabs_f32_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          |
            pose proof (llvm_fabs_f64_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          |
            pose proof (llvm_maxnum_f32_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          |
            pose proof (llvm_maxnum_f64_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          |
            pose proof (llvm_minimum_f32_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          |
            pose proof (llvm_minimum_f64_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          |
            pose proof (llvm_ushl_sat_1_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          |
            pose proof (llvm_ushl_sat_8_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          |
            pose proof (llvm_ushl_sat_16_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          |
            pose proof (llvm_ushl_sat_32_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          |
            pose proof (llvm_ushl_sat_64_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          |
            pose proof (llvm_internal_throw_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          ].

      all:
        try solve
          [ pose proof (llvm_fabs_f32_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          | pose proof (llvm_fabs_f64_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          | pose proof (llvm_maxnum_f32_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          | pose proof (llvm_maxnum_f64_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          | pose proof (llvm_minimum_f32_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          | pose proof (llvm_minimum_f64_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          | pose proof (llvm_ushl_sat_1_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          | pose proof (llvm_ushl_sat_8_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          | pose proof (llvm_ushl_sat_16_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          | pose proof (llvm_ushl_sat_32_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          | pose proof (llvm_ushl_sat_64_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          | pose proof (llvm_internal_throw_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          ].

      cbn.
      pstep; red; cbn.
      constructor; cbn; try tauto.

      intros a b H.
      left; apply orutt_Ret.
      tauto.

      intros o CONTRA; inv CONTRA.
    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF);
        cbn in *.
      pstep; red; cbn.
      change (inr1 (inr1 (inr1 (inr1 (inl1 o0))))) with
        (@subevent _ _ (ReSum_inr IFun sum1 OOME
                          ((LLVMEnvE DV2.uvalue +' LLVMStackE DV2.uvalue) +' (MemoryE DV2.dvalue DV2.uvalue) +' (PickUvalueE DV2.dvalue DV2.uvalue) +' OOME +' LLVMExcE uvalue +' UBE +' DebugE +' FailureE)
                          (@LLVMGEnvE DV2.dvalue)

           ) B o0).
      rewrite subevent_subevent.
      eapply EqVisOOM.
    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF);
        cbn in *.
      pstep; red; cbn.
      change (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 u0))))))) with
        (@subevent _ _ (ReSum_inr IFun sum1 UBE
                          ((LLVMEnvE DV2.uvalue +' LLVMStackE DV2.uvalue) +' (MemoryE DV2.dvalue DV2.uvalue) +' (PickUvalueE DV2.dvalue DV2.uvalue) +' OOME +' LLVMExcE uvalue +' UBE +' DebugE +' FailureE)
                          (@LLVMGEnvE DV2.dvalue)

           ) B u0).
      rewrite subevent_subevent.
      change (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 u))))))) with
        (@subevent _ _ (ReSum_inr IFun sum1 UBE
                          ((LLVMEnvE DV1.uvalue +'
                            LLVMStackE DV1.uvalue ) +'
                           (MemoryE DV1.dvalue DV1.uvalue) +'
                                                                                                            (PickUvalueE DV1.dvalue DV1.uvalue) +' OOME +' LLVMExcE DV1.uvalue +' UBE +' DebugE +' FailureE)
                          (LLVMGEnvE DV1.dvalue)

           ) A u).
      rewrite subevent_subevent.
      econstructor.
      constructor.

      intros a b H.
      left.
      apply orutt_Ret.
      constructor.
      intros o CONTRA; inv CONTRA.
  Qed.

  Lemma E1E2_interp_intrinsics_orutt_strict :
    forall t1 t2,
      L0_E1E2_orutt_strict t1 t2 ->
      L0_E1E2_orutt_strict (IS1.LLVM.Intrinsics.interp_intrinsics t1) (IS2.LLVM.Intrinsics.interp_intrinsics t2).
  Proof.
    intros t1 t2 RL0.
    red. red in RL0.

    unfold IS1.LLVM.Intrinsics.interp_intrinsics.
    unfold interp_intrinsics.
    cbn.

    eapply orutt_interp; eauto.
    { intros A B e1 e2 H.
      apply orutt_interp_intrinsics_h; auto.
    }
    { intros A o.
      exists (resum IFun A o).
      exists ret.
      reflexivity.
    }
  Qed.

End CallsRefine.
