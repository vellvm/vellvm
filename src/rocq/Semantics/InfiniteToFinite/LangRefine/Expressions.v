From Stdlib Require Import
  Lia
  ZArith
  Program.Equality
  List.

From ExtLib Require Import
  Structures.Monads
  Structures.Functor.

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
  ListUtil
  OOMRutt
  OOMRuttProps
  Monads
  MapMonadExtra.

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
  Concretization.

From ITree Require Import
  ITree
  Basics.HeterogeneousRelations
  Eq.Rutt
  Eq.RuttFacts
  Eq.Eqit.

Module Type ExpressionsRefine
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
                SELECT_REF).

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
  Import DVC.
  Import TLR2.
  Import IS2.LLVM.MEM.CP.CONCBASE.
  Import ACS.
 
  Lemma orutt_denote_exp'_Zero_initializer:
    forall odt : option dtyp,
      orutt exp_E_refine_strict exp_E_res_refine_strict uvalue_refine_strict
        (IS1.LLVM.D.denote_exp' odt LLVMAst.EXP_Zero_initializer)
        (denote_exp' odt LLVMAst.EXP_Zero_initializer) (OOM := OOME).
  Proof.
    intros odt.
    destruct odt as [dt | ];
      cbn;
      try solve [
          solve_orutt_raise
        ].

    unfold denote_exp, IS1.LLVM.D.denote_exp.
    unfold LLVMEvents.lift_err.

    repeat break_match_goal.
    - cbn in *.
      repeat break_match_hyp_inv.
      unfold IS1.LLVM.D.dv_zero_initializer in Heqs0.
      unfold dv_zero_initializer in *.
      apply default_dvalue_of_dtyp_dv1_dv2_same_error in Heqs0.
      rewrite Heqs0 in Heqs1. inversion Heqs1. subst.
      solve_orutt_raise.
    - cbn in *.
      repeat break_match_hyp_inv.
      unfold IS1.LLVM.D.dv_zero_initializer in Heqs0.
      unfold dv_zero_initializer in *.
      apply default_dvalue_of_dtyp_dv1_dv2_same_error in Heqs0.
      rewrite Heqs0 in Heqs1. inversion Heqs1.
    - cbn in *.
      repeat break_match_hyp_inv.
      unfold IS1.LLVM.D.dv_zero_initializer in Heqs0.
      unfold dv_zero_initializer in *.
      apply DVCrev.default_dvalue_of_dtyp_dv1_dv2_equiv' in Heqs0.
      destruct Heqs0 as [y [Hy _]].
      rewrite Hy in Heqs1. inversion Heqs1.
    - cbn in *.
      repeat break_match_hyp_inv.
      unfold IS1.LLVM.D.dv_zero_initializer in Heqs0.
      unfold dv_zero_initializer in *.

      apply default_dvalue_of_dtyp_dv1_dv2_equiv in Heqs0.
      destruct Heqs0 as [y [Hy HR]].
      rewrite Hy in Heqs1. inversion Heqs1; subst.
      apply orutt_Ret.
      apply dvalue_refine_strict_dvalue_to_uvalue; auto.
  Qed.

  #[global] Hint Resolve
    orutt_denote_exp'_Zero_initializer
    : ORUTT.

  Lemma orutt_denote_exp_Zero_initializer:
    forall odt : option dtyp,
      orutt exp_E_refine_strict exp_E_res_refine_strict uvalue_refine_strict
        (IS1.LLVM.D.denote_exp odt LLVMAst.EXP_Zero_initializer)
        (denote_exp odt LLVMAst.EXP_Zero_initializer) (OOM := OOME).
  Proof.
    intros odt.
    unfold denote_exp, IS1.LLVM.D.denote_exp.
    run_orutt_bind; eauto 7 with ORUTT.
  Qed.

  #[global] Hint Resolve
    orutt_denote_exp_Zero_initializer
    : ORUTT.

  Lemma denote_exp'_E1E2_orutt :
    forall e odt,
      orutt exp_E_refine_strict
        exp_E_res_refine_strict uvalue_refine_strict
        (IS1.LLVM.D.denote_exp' odt e)
        (IS2.LLVM.D.denote_exp' odt e)
        (OOM:=OOME).
  Proof.
    intros e.
    induction e using AstLib.exp_ind with
      (Q := fun md =>
              match md with
              | LLVMAst.METADATA_Null                 
              | LLVMAst.METADATA_Id _ 
              | LLVMAst.METADATA_Node _
              | LLVMAst.METADATA_Pair _ _
              | LLVMAst.METADATA_Debug _ _
              | LLVMAst.METADATA_File_info _ => True
              | LLVMAst.METADATA_Const (t, v) =>
                  orutt exp_E_refine_strict
                    exp_E_res_refine_strict uvalue_refine_strict
                    (IS1.LLVM.D.denote_exp' (Some t) v)
                    (IS2.LLVM.D.denote_exp' (Some t) v)
                    (OOM:=OOME)
              end)
    ; try intros odt; cbn;
      try solve
        [ match goal with
                   [ b : bool |- _ ] => destruct b; cbn; apply orutt_Ret; solve_uvalue_refine_strict
                 | _ => try solve [
                           simplify_expr odt; apply orutt_Ret; solve_uvalue_refine_strict
                         | cbn;
                           eapply orutt_bind; eauto;
                           intros r1 r2 H;
                           eapply orutt_bind; eauto;
                           intros r0 r3 H0;
                           apply orutt_Ret;

                           rewrite uvalue_refine_strict_equation; cbn;
                           rewrite uvalue_refine_strict_equation in H, H0;
                           rewrite H, H0;
                           reflexivity]
          end
        ].

    - apply translate_LU_to_exp_lookup_id_orutt.

    - simplify_expr odt.
      + repeat rewrite map_ret;
          apply orutt_Ret;
          rewrite uvalue_refine_strict_equation;
          reflexivity.
      + repeat rewrite map_bind.
        eapply orutt_bind with
          (RR:=(fun (ip1 : IS1.LP.IP.intptr) (ip2 : IS2.LP.IP.intptr) => IS1.LP.IP.to_Z ip1 = IS2.LP.IP.to_Z ip2)).
        unfold lift_OOM.
        { break_match; break_match.
          - apply orutt_Ret.
            rewrite IS1.LP.IP.VMemInt_intptr_mrepr_from_Z in Heqo.
            rewrite IS2.LP.IP.VMemInt_intptr_mrepr_from_Z in Heqo0.
            erewrite IP.from_Z_to_Z; eauto.
            erewrite IS1.LP.IP.from_Z_to_Z; eauto.
          - apply orutt_raise_oom.
          - (* TODO: Maybe this should be a lemma *)
            rewrite IS1.LP.IP.VMemInt_intptr_mrepr_from_Z in Heqo.
            rewrite IS2.LP.IP.VMemInt_intptr_mrepr_from_Z in Heqo0.

            pose proof intptr_convert_succeeds i as [i2 CONV].
            rewrite IP.from_Z_to_Z with (i:=i) (z:=(denote_int_syntax x)) in CONV; eauto.
            unfold IS1.LLVM.D.denote_int_syntax in Heqo.
            unfold denote_int_syntax in CONV.
            rewrite Heqo in CONV.
            inversion CONV.
          - apply orutt_raise_oom.
        }

        intros r1 r2 H.
        do 2 rewrite map_ret.
        apply orutt_Ret.
        cbn.
        rewrite uvalue_refine_strict_equation.
        cbn.
        rewrite H.
        rewrite IP.to_Z_from_Z; auto.

    - simplify_expr odt.
      destruct fp; cbn; try solve_orutt_raise.
      + unfold IS1.LLVM.D.denote_float_syntax_as_float32, denote_float_syntax_as_float32.
        break_match; try solve_orutt_raise.
        apply orutt_Ret.
        rewrite uvalue_refine_strict_equation; cbn.  reflexivity.
      + unfold IS1.LLVM.D.denote_float_syntax_as_float, denote_float_syntax_as_float.
        break_match; try solve_orutt_raise.
        apply orutt_Ret.
        rewrite uvalue_refine_strict_equation; cbn.  reflexivity.
        
    - apply orutt_denote_exp'_Zero_initializer.

    - (* CStrings *)
      eapply orutt_bind with
        (RR:=(fun uvs1 uvs2 =>
                Forall2 uvalue_refine_strict uvs1 uvs2)
        ).
      + unfold uvalue_refine_strict. cbn.
        revert H.
        induction elts; intros; cbn in *.
        * apply orutt_Ret.
          cbn.  constructor.
        * destruct a.
          eapply orutt_bind with (RR:=(fun uvs1 uvs2 => uvalue_refine_strict uvs1 uvs2)).
          -- eapply (H (d,e)). left; auto.
          -- intros.
             eapply orutt_bind with (RR:=(fun uvs1 uvs2 => Forall2 uvalue_refine_strict uvs1 uvs2)).
             ++ apply IHelts.
                intros.
                apply H.
                right. assumption.
             ++ intros.
                apply orutt_Ret.
                constructor; auto.
      + intros.
        apply orutt_Ret.
        unfold uvalue_refine_strict.
        cbn.
        unfold uvalue_refine_strict in H0.
        break_match_goal.
        * rewrite map_monad_oom_Forall2 in Heqo.
          rewrite (Forall2_ext_m _ _ _ _ H0 Heqo).
          reflexivity.
        * apply map_monad_OOM_fail in Heqo.
          destruct Heqo as [v [HI HC]].
          destruct (Forall2_In _ _ _ _ HI H0) as [x [HJ HX]].
          rewrite HC in HX.
          inversion HX.

    - (* Structs *)
      eapply orutt_bind with
        (RR:=(fun uvs1 uvs2 =>
                Forall2 uvalue_refine_strict uvs1 uvs2)
        ).
      + unfold uvalue_refine_strict. cbn.
        revert H.
        induction fields; intros; cbn in *.
        * apply orutt_Ret.
          cbn.  constructor.
        * destruct a.
          eapply orutt_bind with (RR:=(fun uvs1 uvs2 => uvalue_refine_strict uvs1 uvs2)).
          -- eapply (H (d,e)). left; auto.
          -- intros.
             eapply orutt_bind with (RR:=(fun uvs1 uvs2 => Forall2 uvalue_refine_strict uvs1 uvs2)).
             ++ apply IHfields.
                intros.
                apply H.
                right. assumption.
             ++ intros.
                apply orutt_Ret.
                constructor; auto.
      + intros.
        apply orutt_Ret.
        unfold uvalue_refine_strict.
        cbn.
        unfold uvalue_refine_strict in H0.
        break_match_goal.
        * rewrite map_monad_oom_Forall2 in Heqo.
          rewrite (Forall2_ext_m _ _ _ _ H0 Heqo).
          reflexivity.
        * apply map_monad_OOM_fail in Heqo.
          destruct Heqo as [v [HI HC]].
          destruct (Forall2_In _ _ _ _ HI H0) as [x [HJ HX]].
          rewrite HC in HX.
          inversion HX.

    - (* Packed_structs *)
      simplify_expr odt.
      eapply orutt_bind with
        (RR:=(fun uvs1 uvs2 =>
                Forall2 uvalue_refine_strict uvs1 uvs2)
        ).
      + unfold uvalue_refine_strict. cbn.
        revert H.
        induction fields; intros; cbn in *.
        * apply orutt_Ret.
          cbn.  constructor.
        * destruct a.
          eapply orutt_bind with (RR:=(fun uvs1 uvs2 => uvalue_refine_strict uvs1 uvs2)).
          -- eapply (H (d,e)). left; auto.
          -- intros.
             eapply orutt_bind with (RR:=(fun uvs1 uvs2 => Forall2 uvalue_refine_strict uvs1 uvs2)).
             ++ apply IHfields.
                intros.
                apply H.
                right. assumption.
             ++ intros.
                apply orutt_Ret.
                constructor; auto.
      + intros.
        apply orutt_Ret.
        unfold uvalue_refine_strict.
        cbn.
        unfold uvalue_refine_strict in H0.
        break_match_goal.
        * rewrite map_monad_oom_Forall2 in Heqo.
          rewrite (Forall2_ext_m _ _ _ _ H0 Heqo).
          reflexivity.
        * apply map_monad_OOM_fail in Heqo.
          destruct Heqo as [v [HI HC]].
          destruct (Forall2_In _ _ _ _ HI H0) as [x [HJ HX]].
          rewrite HC in HX.
          inversion HX.

    - (* Arrays *)
      eapply orutt_bind with
        (RR:=(fun uvs1 uvs2 =>
                Forall2 uvalue_refine_strict uvs1 uvs2)
        ).
      + unfold uvalue_refine_strict. cbn.
        revert H.
        induction elts; intros; cbn in *.
        * apply orutt_Ret.
          cbn.  constructor.
        * destruct a.
          eapply orutt_bind with (RR:=(fun uvs1 uvs2 => uvalue_refine_strict uvs1 uvs2)).
          -- eapply (H (d,e)). left; auto.
          -- intros.
             eapply orutt_bind with (RR:=(fun uvs1 uvs2 => Forall2 uvalue_refine_strict uvs1 uvs2)).
             ++ apply IHelts.
                intros.
                apply H.
                right. assumption.
             ++ intros.
                apply orutt_Ret.
                constructor; auto.
      + intros.
        apply orutt_Ret.
        unfold uvalue_refine_strict.
        cbn.
        unfold uvalue_refine_strict in H0.
        break_match_goal.
        * rewrite map_monad_oom_Forall2 in Heqo.
          rewrite (Forall2_ext_m _ _ _ _ H0 Heqo).
          reflexivity.
        * apply map_monad_OOM_fail in Heqo.
          destruct Heqo as [v [HI HC]].
          destruct (Forall2_In _ _ _ _ HI H0) as [x [HJ HX]].
          rewrite HC in HX.
          inversion HX.

    - (* Vectors *)
      eapply orutt_bind with
        (RR:=(fun uvs1 uvs2 =>
                Forall2 uvalue_refine_strict uvs1 uvs2)
        ).
      + unfold uvalue_refine_strict. cbn.
        revert H.
        induction elts; intros; cbn in *.
        * apply orutt_Ret.
          cbn.  constructor.
        * destruct a.
          eapply orutt_bind with (RR:=(fun uvs1 uvs2 => uvalue_refine_strict uvs1 uvs2)).
          -- eapply (H (d,e)). left; auto.
          -- intros.
             eapply orutt_bind with (RR:=(fun uvs1 uvs2 => Forall2 uvalue_refine_strict uvs1 uvs2)).
             ++ apply IHelts.
                intros.
                apply H.
                right. assumption.
             ++ intros.
                apply orutt_Ret.
                constructor; auto.
      + intros.
        apply orutt_Ret.
        unfold uvalue_refine_strict.
        cbn.
        unfold uvalue_refine_strict in H0.
        break_match_goal.
        * rewrite map_monad_oom_Forall2 in Heqo.
          rewrite (Forall2_ext_m _ _ _ _ H0 Heqo).
          reflexivity.
        * apply map_monad_OOM_fail in Heqo.
          destruct Heqo as [v [HI HC]].
          destruct (Forall2_In _ _ _ _ HI H0) as [x [HJ HX]].
          rewrite HC in HX.
          inversion HX.

    -  destruct v.
       eapply orutt_bind; eauto.
       intros r1 r2 H.
       eapply orutt_Ret.
       rewrite uvalue_refine_strict_equation; cbn;
         rewrite uvalue_refine_strict_equation in H.
       rewrite H.
       reflexivity.
          
    - (* Conversion *)
      cbn.
      eapply orutt_bind; eauto.
      intros r1 r2 H.
      apply orutt_Ret.
      rewrite uvalue_refine_strict_equation; cbn;
        rewrite uvalue_refine_strict_equation in H.
      rewrite H.
      cbn.
      reflexivity.

    - (* GetElementPtr *)
      destruct ptrval as [ptr_t ptrval].
      cbn.
      eapply orutt_bind; eauto.
      intros r1 r2 H0.

      eapply orutt_bind with
        (RR:=(fun uvs1 uvs2 =>
                Forall2 uvalue_refine_strict uvs1 uvs2)
        ).
      + unfold uvalue_refine_strict. cbn.
        revert H.
        induction idxs; intros; cbn in *.
        * apply orutt_Ret.
          cbn.  constructor.
        * destruct a.
          eapply orutt_bind with (RR:=(fun uvs1 uvs2 => uvalue_refine_strict uvs1 uvs2)).
          -- eapply (H (d,e)). left; auto.
          -- intros.
             eapply orutt_bind with (RR:=(fun uvs1 uvs2 => Forall2 uvalue_refine_strict uvs1 uvs2)).
             ++ apply IHidxs.
                intros.
                apply H.
                right. assumption.
             ++ intros.
                apply orutt_Ret.
                constructor; auto.
      + intros.
        apply orutt_Ret.
        unfold uvalue_refine_strict.
        cbn.
        unfold uvalue_refine_strict in H0.
        rewrite H0.
        break_match_goal.
        * rewrite map_monad_oom_Forall2 in Heqo.
          rewrite (Forall2_ext_m _ _ _ _ H1 Heqo).
          reflexivity.
        * apply map_monad_OOM_fail in Heqo.
          destruct Heqo as [v [HI HC]].
          destruct (Forall2_In _ _ _ _ HI H1) as [x [HJ HX]].
          unfold uvalue_refine_strict in HX.
          rewrite HC in HX.
          inversion HX.

    - (* ExtractElement *)
      destruct vec as [vec_t vec].
      destruct idx as [idx_t idx].
      cbn.

      eapply orutt_bind; eauto.
      intros r1 r2 H.
      eapply orutt_bind; eauto.
      intros r0 r3 H0.
      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation; cbn.
      rewrite uvalue_refine_strict_equation in H0, H.
      cbn.
      rewrite H, H0.
      reflexivity.

    - (* InsertElement *)
      destruct vec as [vec_t vec].
      destruct idx as [idx_t idx].
      destruct elt as [elt_t elt].
      cbn.

      eapply orutt_bind; eauto.
      intros r1 r2 H.

      eapply orutt_bind; eauto.
      intros r0 r3 H0.

      eapply orutt_bind; eauto.
      intros r4 r5 H1.

      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation; cbn.
      rewrite uvalue_refine_strict_equation in H, H0, H1.
      cbn.

      rewrite H, H0, H1.
      reflexivity.

    - (* ShuffleVector *)
      destruct vec1 as [vec1_t vec1].
      destruct vec2 as [vec2_t vec2].
      destruct idxmask as [idxmask_t idxmask].
      cbn.

      eapply orutt_bind; eauto.
      intros r1 r2 H.

      eapply orutt_bind; eauto.
      intros r0 r3 H0.

      eapply orutt_bind; eauto.
      intros r4 r5 H1.

      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation; cbn.
      rewrite uvalue_refine_strict_equation in H, H0, H1.
      cbn.

      rewrite H, H0, H1.
      reflexivity.

    - (* ExtractValue *)
      destruct vec as [vec_t vec].
      cbn.

      eapply orutt_bind; eauto.
      intros r1 r2 H.

      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation; cbn.
      rewrite uvalue_refine_strict_equation in H.
      cbn.

      rewrite H.
      reflexivity.

    - (* InsertValue *)
      destruct vec as [vec_t vec].
      destruct elt as [elt_t elt].
      cbn.

      eapply orutt_bind; eauto.
      intros r1 r2 H.

      eapply orutt_bind; eauto.
      intros r0 r3 H0.

      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation; cbn.
      rewrite uvalue_refine_strict_equation in H, H0.
      cbn.

      rewrite H, H0.
      reflexivity.

    - (* Select *)
      destruct cnd, v1, v2.
      cbn.

      eapply orutt_bind; eauto.
      intros r1 r2 H.

      eapply orutt_bind; eauto.
      intros r0 r3 H0.

      eapply orutt_bind; eauto.
      intros r4 r5 H1.

      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation; cbn.
      rewrite uvalue_refine_strict_equation in H, H0, H1.
      cbn.

      rewrite H, H0, H1.
      reflexivity.

    - (* Freeze *)
      destruct v; cbn.
      eapply orutt_bind; eauto.
      intros r1 r2 H.

      eapply orutt_bind with (RR:=dvalue_refine_strict); eauto.
      apply pick_your_poison_orutt; auto.
      intros r0 r3 H0.
      apply orutt_Ret.
      apply dvalue_refine_strict_dvalue_to_uvalue; auto.
    - destruct m; simpl in *;
        try apply orutt_Ret; try reflexivity.
      rewrite uvalue_refine_strict_equation; cbn.
      rewrite AC1.addr_convert_null.
      reflexivity.
      destruct tv.
      assumption.
    - destruct elt.
      cbn in *.
      destruct odt as [dt | ];
        cbn;
        try solve [
            solve_orutt_raise
          ].
      destruct dt;
        cbn;
        try solve [
            solve_orutt_raise
          ].
      eapply orutt_bind with (RR:=uvalue_refine_strict); eauto.
      intros r0 r3 H0.
      apply orutt_Ret.
      rewrite uvalue_refine_strict_equation; cbn; auto.
      remember (N.to_nat sz) as n.
      clear Heqn.
      induction n; cbn; auto.
      rewrite H0.
      break_match_hyp_inv.
      reflexivity.
    - auto.
    - auto.
    - destruct te.
      simpl in IHe.
      apply IHe.
    - auto.
    - auto.
    - auto.
    - auto.
  Qed.

  #[global] Hint Resolve
    denote_exp'_E1E2_orutt
    : ORUTT.

  Lemma denote_exp_E1E2_orutt :
    forall e odt,
      orutt exp_E_refine_strict
        exp_E_res_refine_strict uvalue_refine_strict
        (IS1.LLVM.D.denote_exp odt e)
        (IS2.LLVM.D.denote_exp odt e)
        (OOM:=OOME).
  Proof.
    intros e odt.
    eapply orutt_bind; eauto with ORUTT.
  Qed.

  #[global] Hint Resolve
    denote_exp_E1E2_orutt
    : ORUTT.
End ExpressionsRefine.
