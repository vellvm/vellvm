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

Module Type MemoryOpsRefine
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
               CONC_REF).

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
  Import DVC.
  Import TLR2.
  Import IS2.LLVM.MEM.CP.CONCBASE.
  Import ACS.

  Lemma trigger_alloca_E1E2_rutt_strict_sound :
    forall dt n osz,
      rutt event_refine_strict event_res_refine_strict dvalue_refine_strict
        (trigger (@Alloca _ _ dt n osz)) (trigger (@Alloca _ _ dt n osz)).
  Proof.
    intros dt n osz.
    apply rutt_trigger.
    - cbn. auto.
    - intros t1 t2 H.
      cbn in *.
      tauto.
  Qed.

  Lemma trigger_globalwrite_E1E2_rutt_strict_sound :
    forall gid r1 r2,
      dvalue_refine_strict r1 r2 ->
      rutt event_refine_strict event_res_refine_strict eq (trigger (GlobalWrite gid r1))
        (trigger (GlobalWrite gid r2)).
  Proof.
    intros gid r1 r2 H.
    apply rutt_trigger.
    - cbn. auto.
    - intros [] [] _.
      auto.
  Qed.

  Lemma allocate_declarations_E1E2_rutt_strict_sound :
    forall a,
      rutt event_refine_strict event_res_refine_strict eq (LLVM1.allocate_declaration a) (allocate_declaration a).
  Proof.
    intros a.
    induction a.
    unfold LLVM1.allocate_declaration, allocate_declaration.
    cbn.
    break_match.
    - apply rutt_Ret; reflexivity.
    - eapply rutt_bind with (RR:=dvalue_refine_strict).
      { apply trigger_alloca_E1E2_rutt_strict_sound.
      }

      intros r1 r2 H.
      apply trigger_globalwrite_E1E2_rutt_strict_sound.
      auto.
  Qed.

  Lemma allocate_one_E1E2_rutt_strict_sound :
    forall (m_declarations : list (LLVMAst.declaration dtyp))
      (m_definitions : list (LLVMAst.definition dtyp (cfg dtyp))),
      rutt event_refine_strict event_res_refine_strict eq
        (map_monad LLVM1.allocate_declaration (m_declarations ++ map LLVMAst.df_prototype m_definitions))
        (map_monad allocate_declaration (m_declarations ++ map LLVMAst.df_prototype m_definitions)).
  Proof.
    intros m_declarations m_definitions.
    remember (m_declarations ++ map LLVMAst.df_prototype m_definitions) as declarations.
    clear m_declarations m_definitions Heqdeclarations.
    induction declarations.
    - cbn.
      apply rutt_Ret.
      reflexivity.
    - cbn.
      eapply rutt_bind with (RR:=eq).
      { apply allocate_declarations_E1E2_rutt_strict_sound.
      }

      intros [] [] _.
      eapply rutt_bind with (RR:=eq); auto.

      intros r1 r2 R1R2.
      subst.
      apply rutt_Ret.
      reflexivity.
  Qed.

  Lemma allocate_global_E1E2_rutt_strict_sound :
    forall (m_global : LLVMAst.global dtyp),
      rutt event_refine_strict event_res_refine_strict eq
        (LLVM1.allocate_global m_global)
        (allocate_global m_global).
  Proof.
    intros m_global.
    unfold LLVM1.allocate_global, allocate_global.
    break_match_goal.
    - apply rutt_Ret; reflexivity.
    - eapply rutt_bind with (RR:=dvalue_refine_strict).
      { apply trigger_alloca_E1E2_rutt_strict_sound.
      }

      intros r1 r2 H.
      apply trigger_globalwrite_E1E2_rutt_strict_sound; auto.
  Qed.


  Lemma allocate_globals_E1E2_rutt_strict_sound :
    forall (m_globals : list (LLVMAst.global dtyp)),
      rutt event_refine_strict event_res_refine_strict eq
        (map_monad LLVM1.allocate_global m_globals)
        (map_monad allocate_global m_globals).
  Proof.
    intros m_globals.
    induction m_globals.
    - cbn; apply rutt_Ret; reflexivity.
    - cbn.
      eapply rutt_bind with (RR:=eq).
      apply allocate_global_E1E2_rutt_strict_sound.

      intros [] [] _.
      eapply rutt_bind with (RR:=eq); auto.

      intros r1 r2 R1R2.
      subst.
      apply rutt_Ret.
      reflexivity.
  Qed.

  Lemma GlobalRead_exp_E_E1E2_rutt :
    forall g,
      rutt exp_E_refine_strict exp_E_res_refine_strict dvalue_refine_strict (trigger (GlobalRead g)) (trigger (GlobalRead g)).
  Proof.
    intros g.
    apply rutt_trigger.
    cbn. auto.

    intros t1 t2 H.
    cbn in H.
    tauto.
  Qed.

  Lemma GlobalRead_L0_E1E2_rutt :
    forall g,
      rutt event_refine_strict event_res_refine_strict dvalue_refine_strict (trigger (GlobalRead g)) (trigger (GlobalRead g)).
  Proof.
    intros g.
    apply rutt_trigger.
    cbn. auto.

    intros t1 t2 H.
    cbn in H.
    tauto.
  Qed.

  Lemma Store_E1E2_rutt :
    forall dt r1 r2 r3 r4,
      dvalue_refine_strict r1 r2 ->
      uvalue_refine_strict r3 r4 ->
      rutt exp_E_refine_strict exp_E_res_refine_strict eq
        (trigger (@Store DV1.dvalue DV1.uvalue dt r1 r3))
        (trigger (@Store _ _ dt r2 r4)).
  Proof.
    intros dt r1 r2 r3 r4 R1R2 R3R4.
    apply rutt_trigger.
    cbn. tauto.

    intros [] [] _.
    reflexivity.
  Qed.


  Lemma GlobalRead_exp_E_E1E2_orutt :
    forall g,
      orutt (OOM:=OOME) exp_E_refine_strict exp_E_res_refine_strict dvalue_refine_strict (trigger (GlobalRead g)) (trigger (GlobalRead g)).
  Proof.
    intros g.
    apply rutt_orutt.
    apply GlobalRead_exp_E_E1E2_rutt.
    intros A e2.
    apply exp_E_dec_oom.
  Qed.

  Lemma GlobalRead_L0_E1E2_orutt :
    forall g,
      orutt (OOM:=OOME) event_refine_strict event_res_refine_strict dvalue_refine_strict (trigger (GlobalRead g)) (trigger (GlobalRead g)).
  Proof.
    intros g.
    apply rutt_orutt.
    apply GlobalRead_L0_E1E2_rutt.
    intros A e2.
    apply L0_dec_oom.
  Qed.

  #[global] Hint Resolve
    GlobalRead_exp_E_E1E2_orutt
    GlobalRead_L0_E1E2_orutt
    : ORUTT.

  Lemma Store_E1E2_orutt :
    forall E1 E2
      `{OOM1 : OOME -< E1} `{OOM2 : OOME -< E2}
      `{MEM1 : MemoryE DV1.dvalue DV1.uvalue -< E1} `{MEM2 : MemoryE _ _ -< E2}
      (pre : prerel E1 E2) (post : postrel E1 E2)
      (MEMPRE : forall dt r1 r2 r3 r4, dvalue_refine_strict r1 r3 -> uvalue_refine_strict r2 r4 -> pre unit unit (MEM1 unit (Store dt r1 r2)) (MEM2 unit (Store dt r3 r4)))
      (MEMDISC : forall e (o : OOME unit), MEM2 unit e <> subevent unit o)
       dt r1 r2 r3 r4,
      dvalue_refine_strict r1 r2 ->
      uvalue_refine_strict r3 r4 ->
      orutt (OOM:=OOME) pre post eq
        (trigger (Store dt r1 r3))
        (trigger (Store dt r2 r4)).
  Proof.
    intros E1 E2 OOM1 OOM2 MEM1 MEM2 pre post MEMPRE MEMDISC dt r1 r2 r3 r4 R1R2 R3R4.
    apply orutt_trigger; eauto.
    intros [] []; auto.
  Qed.

  #[global] Hint Resolve
    Store_E1E2_orutt
    : ORUTT.

  Lemma GlobalWrite_exp_orutt :
    forall g (r1 : DV1.dvalue) (r2 : DV2.dvalue),
      dvalue_refine_strict r1 r2 ->
      orutt (OOM:=OOME) exp_E_refine_strict exp_E_res_refine_strict eq (trigger (GlobalWrite g r1))
        (trigger (GlobalWrite g r2)).
  Proof.
    intros g r1 r2 H.
    apply orutt_trigger.
    repeat constructor; auto.
    intros [] [] ?; auto.
    intros o CONTRA; inv CONTRA.
  Qed.

  #[global] Hint Resolve
    GlobalWrite_exp_orutt
    : ORUTT.

  Lemma initialize_global_E1E2_orutt :
    forall g,
      orutt exp_E_refine_strict exp_E_res_refine_strict eq
        (LLVM1.initialize_global g)
        (LLVM2.initialize_global g)
        (OOM:=OOME).
  Proof.
    intros g.
    unfold LLVM1.initialize_global, initialize_global.
    repeat break_match_goal; cbn; subst; eauto 6 with ORUTT.
  Qed.

  #[global] Hint Resolve
   initialize_global_E1E2_orutt
    : ORUTT.

  Lemma initialize_globals_E1E2_orutt :
    forall m_globals,
      orutt exp_E_refine_strict exp_E_res_refine_strict eq
        (map_monad LLVM1.initialize_global m_globals)
        (map_monad initialize_global m_globals)
        (OOM:=OOME).
  Proof.
    cbn.

    induction m_globals.
    { cbn.
      apply orutt_Ret.
      reflexivity.
    }
    { rewrite map_monad_unfold.
      rewrite map_monad_unfold.

      cbn.
      apply orutt_bind with (RR:=eq); eauto with ORUTT.
      intros [] [] _.
      apply orutt_bind with (RR:=eq).
      apply IHm_globals.

      intros r1 r2 R1R2; subst.
      eauto with ORUTT.
    }
  Qed.

  #[global] Hint Resolve
   initialize_globals_E1E2_orutt
   translate_exp_to_L0_E1E2_orutt
   translate_exp_to_instr_E1E2_orutt_strict
    : ORUTT.

  Lemma build_global_environment_E1E2_orutt_strict_sound :
    forall (m : mcfg dtyp),
      orutt
        event_refine_strict
        event_res_refine_strict
        eq
        (LLVM1.build_global_environment m)
        (LLVM2.build_global_environment m)
        (OOM:=OOME).
  Proof.
    destruct m.
    cbn.
    repeat run_orutt_bind; eauto with ORUTT.
    - (* In the future this allocate_one_E1E2_rutt_strict_sound lemma may be orutt *)
      apply rutt_orutt; [| intros; apply L0_dec_oom].
      apply allocate_one_E1E2_rutt_strict_sound.
    - intros [] [] _.
      repeat run_orutt_bind; eauto with ORUTT.

      apply rutt_orutt; [| intros; apply L0_dec_oom].
      apply allocate_globals_E1E2_rutt_strict_sound.
  Qed.

  #[global] Hint Resolve
    build_global_environment_E1E2_orutt_strict_sound : ORUTT.

  Lemma orutt_trigger_LocalWrite :
    forall E1 E2
      `{OOM1 : OOME -< E1} `{OOM2 : OOME -< E2}
      `{LOC1: LocalE LLVMAst.raw_id DV1.uvalue -< E1} `{LOC2: LocalE LLVMAst.raw_id DV2.uvalue -< E2}
      (pre : prerel E1 E2) (post : postrel E1 E2)
      (LOCALDISC : forall id y (o : OOME unit), LOC2 unit (LocalWrite id y) <> subevent unit o)
      (LOCALPRE : forall id x y (REF: uvalue_refine_strict x y), pre unit unit (LOC1 unit (LocalWrite id x)) (LOC2 unit (LocalWrite id y)))
      (id : LLVMAst.raw_id)
      (x : DV1.uvalue) (y : DV2.uvalue)
      (REF: uvalue_refine_strict x y),
      orutt (OOM:=OOME) pre post eq (trigger (LocalWrite id x)) (trigger (LocalWrite id y)).
  Proof.
    intros E1 E2 OOM1 OOM2 LOC1 LOC2 pre post LOCALDISC LOCALPRE id x y REF.
    apply orutt_trigger; auto.    
    intros [] [] _; reflexivity.      
  Qed.

  #[global] Hint Resolve
   orutt_trigger_LocalWrite : ORUTT.

  Lemma orutt_trigger_Load :
    forall E1 E2
      `{OOM1 : OOME -< E1} `{OOM2 : OOME -< E2}
      `{MEM1 : MemoryE DV1.dvalue DV1.uvalue -< E1} `{MEM2 : MemoryE _ _ -< E2}
      (pre : prerel E1 E2) (post : postrel E1 E2)
      (MEMPRE : forall dt dv1 dv2, dvalue_refine_strict dv1 dv2 -> pre DV1.uvalue DV2.uvalue (MEM1 DV1.uvalue (@Load DV1.dvalue DV1.uvalue dt dv1)) (MEM2 DV2.uvalue (Load dt dv2)))
      (MEMPOST : forall dt dv1 dv2 (t1 : DV1.uvalue) (t2 : DV2.uvalue),
          post DV1.uvalue DV2.uvalue (MEM1 DV1.uvalue (@Load DV1.dvalue DV1.uvalue dt dv1)) t1
            (MEM2 DV2.uvalue (Load dt dv2)) t2 ->
          uvalue_refine_strict t1 t2)
      (MEMDISC : forall dt dv2 (o : OOME DV2.uvalue), MEM2 DV2.uvalue (Load dt dv2) <> subevent DV2.uvalue o)
      dt
      (dv1 : DV1.dvalue) (dv2 : DV2.dvalue)
      (REF: dvalue_refine_strict dv1 dv2),
      orutt (OOM:=OOME) pre post uvalue_refine_strict (trigger (@Load _ _ dt dv1)) (trigger (Load dt dv2)).
  Proof.
    intros E1 E2 OOM1 OOM2 MEM1 MEM2 pre post MEMPRE MEMPOST MEMDISC dt dv1 dv2 REF.
    apply orutt_trigger; eauto.
  Qed.

  #[global] Hint Resolve
   orutt_trigger_Load : ORUTT.

  #[global] Hint Extern 1 (forall (dt : dtyp) (dv1 : DV1.dvalue) (dv2 : dvalue) (t1 : DV1.uvalue)
    (t2 : DV2.uvalue),
  instr_E_res_refine_strict DV1.uvalue DV2.uvalue
    (ReSum_inr IFun sum1 (@MemoryE DV1.dvalue DV1.uvalue) (@IntrinsicE DV1.dvalue DV1.uvalue +' exp_E DV1.dvalue DV1.uvalue)
       CallE DV1.uvalue (@Load DV1.dvalue DV1.uvalue dt dv1))
    t1 (ReSum_inr IFun sum1 MemoryE (IntrinsicE +' exp_E) CallE DV2.uvalue (Load dt dv2)) t2 ->
  uvalue_refine_strict t1 t2) => 
    intros ? ? ? ? ? ?; cbn in *; tauto : ORUTT.


  #[global] Hint Extern 1 ( forall (dt : dtyp) (dv1 : DV1.dvalue) (dv2 : DV2.dvalue) (t1 : DV1.uvalue) (t2 : DV2.uvalue),
  instr_E_res_refine_strict DV1.uvalue DV2.uvalue (MemoryE_instrE (Load dt dv1)) t1 (MemoryE_instrE (Load dt dv2)) t2 -> uvalue_refine_strict t1 t2) => cbn; tauto : ORUTT.

  Lemma orutt_trigger_Alloca :
    forall E1 E2
      `{OOM1 : OOME -< E1} `{OOM2 : OOME -< E2}
      `{MEM1 : MemoryE DV1.dvalue DV1.uvalue -< E1} `{MEM2 : MemoryE DV2.dvalue DV2.uvalue -< E2}
      (pre : prerel E1 E2) (post : postrel E1 E2)
      (MEMPOST : forall dt sz align (t1 : DV1.dvalue) (t2 : DV2.dvalue),
          post DV1.dvalue DV2.dvalue (MEM1 DV1.dvalue (Alloca dt sz align)) t1
            (MEM2 DV2.dvalue (Alloca dt sz align)) t2 ->
          dvalue_refine_strict t1 t2)
      (MEMDISC : forall e (o : OOME DV2.dvalue), MEM2 DV2.dvalue e <> subevent DV2.dvalue o)
      dt sz align
      (MEMPRE : pre DV1.dvalue DV2.dvalue (MEM1 DV1.dvalue (Alloca dt sz align)) (MEM2 DV2.dvalue (Alloca dt sz align))),
      orutt (OOM:=OOME) pre post dvalue_refine_strict (trigger (Alloca dt sz align)) (trigger (Alloca dt sz align)).
  Proof.
    intros.
    apply orutt_trigger; eauto.
  Qed.

  #[global] Hint Resolve
    orutt_trigger_Alloca : ORUTT.

  Lemma Store_E1E2_rutt' :
    forall dt r1 r2 r3 r4,
      dvalue_refine_strict r1 r2 ->
      uvalue_refine_strict r3 r4 ->
      rutt event_refine_strict event_res_refine_strict eq
        (trigger (Store dt r1 r3))
        (trigger (Store dt r2 r4)).
  Proof.
    intros dt r1 r2 r3 r4 R1R2 R3R4.
    apply rutt_trigger.
    cbn. tauto.

    intros [] [] _.
    reflexivity.
  Qed.
End MemoryOpsRefine.
