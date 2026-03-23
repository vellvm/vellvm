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
  OOMRuttProps.

From Vellvm.Semantics.InfiniteToFinite.LangRefine Require Import
  Events
  Sizeof
  Values
  Vectors
  IntegerUtils.

From ITree Require Import
  ITree
  Basics.HeterogeneousRelations
  Eq.Rutt
  Eq.RuttFacts
  Eq.Eqit.

Module Type IntOpsRefine
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
               VAL_REF).

  Import EC.
  Import DV2.
  Import IS2.LP.
  Import DynamicTypes.
  Import IPS.
  Import VAL_REF.
  Import VEC_REF.
  Import DVC.
  Import TLR2.

  (* TODO: Move this *)
  Lemma eval_int_op_ix_fin_inf :
    forall sz v1 v2 iop res_fin res_inf,
      @eval_int_op err_ub_oom (@Integers.bit_int sz) (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@VIntVMemInt (@Integers.bit_int sz) (@VInt_Bounded sz)) (@ToDvalue_Int sz)
        iop v1 v2 = success_unERR_UB_OOM res_fin ->
      DVCrev.dvalue_convert_strict res_fin = NoOom res_inf ->
      @DV1.eval_int_op err_ub_oom (@Integers.bit_int sz)
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@VIntVMemInt (@Integers.bit_int sz) (@VInt_Bounded sz)) (@DV1.ToDvalue_Int sz)
        iop v1 v2 = success_unERR_UB_OOM res_inf.
  Proof.
    intros sz v1 v2 iop res_fin res_inf EVAL CONV.
    destruct iop.
    1-3:
      try solve
        [ cbn in *;
          repeat break_match_hyp_inv; cbn in *;
          inv CONV;
          cbn in *; reflexivity
        ].

    { cbn in *.
      break_match_hyp_inv.
      cbn in CONV; inv CONV; cbn; auto.
      break_match_hyp_inv.
      cbn in CONV; inv CONV; cbn; auto.
      destruct nsw.
      2: {
        cbn in H1; inv H1; cbn.
        cbn in CONV;
          inv CONV; cbn; auto.
      }

      break_match_hyp;
        cbn in H1; inv H1; cbn;
        cbn in CONV;
        inv CONV; cbn; auto.
    }

    all: try solve
           [ cbn in *;
             repeat break_match_hyp_inv; cbn in *;
             cbn in CONV; inv CONV;
             cbn in *; reflexivity
           ].

    all: try solve
           [ cbn in *;
             repeat break_match_hyp_inv; cbn in *; inv EVAL;
             cbn in CONV; inv CONV;
             cbn in *; reflexivity
           ].
  Qed.

  (* TODO: Move this *)
  Lemma eval_int_op_iptr_fin_inf :
    forall v1_fin v2_fin v1_inf v2_inf iop res_fin res_inf,
      @eval_int_op err_ub_oom IP.intptr (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        VMemInt_intptr' ToDvalue_intptr
        iop v1_fin v2_fin = success_unERR_UB_OOM res_fin ->
      IS1.LP.IP.from_Z (IP.to_Z v1_fin) = NoOom v1_inf ->
      IS1.LP.IP.from_Z (IP.to_Z v2_fin) = NoOom v2_inf ->
      DVCrev.dvalue_convert_strict res_fin = NoOom res_inf ->
      @DV1.eval_int_op err_ub_oom IS1.LP.IP.intptr
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        DV1.VMemInt_intptr' DV1.ToDvalue_intptr
        iop v1_inf v2_inf = success_unERR_UB_OOM res_inf.
  Proof.
    intros v1_fin v2_fin v1_inf v2_inf iop res_fin res_inf
      EVAL LIFT1 LIFT2 CONV.

    assert (IP.to_Z v1_fin = IS1.LP.IP.to_Z v1_inf) as V1.
    { erewrite IS1.LP.IP.from_Z_to_Z; eauto. }

    assert (IP.to_Z v2_fin = IS1.LP.IP.to_Z v2_inf) as V2.
    { erewrite IS1.LP.IP.from_Z_to_Z; eauto. }

    destruct iop.
    - (* Add *)
      cbn in *.
      repeat rewrite VMEM_IP_PROP1.madd_carry_zero, VMEM_IP_PROP1.madd_overflow_zero.
      repeat rewrite VMEM_IP_PROP2.madd_carry_zero, VMEM_IP_PROP2.madd_overflow_zero in EVAL.
      setoid_rewrite VMEM_IP_PROP1.mequ_zero_one_false.
      setoid_rewrite VMEM_IP_PROP2.mequ_zero_one_false in EVAL.
      repeat rewrite Bool.andb_false_r.
      repeat rewrite Bool.andb_false_r in EVAL.
      cbn in *.

      remember (lift_OOM (madd v1_fin v2_fin)) as add_result.
      destruct_err_ub_oom add_result; inv EVAL.
      symmetry in Heqadd_result.
      destruct (madd v1_fin v2_fin) eqn:HADD; inv Heqadd_result.

      cbn in CONV.
      break_match_hyp_inv.

      pose proof VMEM_REF.madd_refine _ _ _ v1_inf v2_inf V1 V2 HADD as (?&?&?).
      setoid_rewrite H. cbn.
      rewrite H0 in Heqo.
      rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
      inv Heqo.
      reflexivity.
    - (* Sub *)
      cbn in *.
      repeat rewrite VMEM_IP_PROP1.msub_borrow_zero, VMEM_IP_PROP1.msub_overflow_zero.
      repeat rewrite VMEM_IP_PROP2.msub_borrow_zero, VMEM_IP_PROP2.msub_overflow_zero in EVAL.
      setoid_rewrite VMEM_IP_PROP1.mequ_zero_one_false.
      setoid_rewrite VMEM_IP_PROP2.mequ_zero_one_false in EVAL.
      repeat rewrite Bool.andb_false_r.
      repeat rewrite Bool.andb_false_r in EVAL.
      cbn in *.

      remember (lift_OOM (msub v1_fin v2_fin)) as sub_result.
      destruct_err_ub_oom sub_result; inv EVAL.
      symmetry in Heqsub_result.
      destruct (msub v1_fin v2_fin) eqn:HSUB; inv Heqsub_result.

      cbn in CONV.
      break_match_hyp_inv.

      epose proof VMEM_REF.msub_refine _ _ _ v1_inf v2_inf V1 V2 HSUB as (?&?&?).
      setoid_rewrite H. cbn.
      rewrite H0 in Heqo.
      rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
      inv Heqo.
      reflexivity.
    - (* Mul *)
      cbn in *.
      destruct mbitwidth; cbn in EVAL.
      2: {
        remember (lift_OOM (mmul v1_fin v2_fin)) as mul_result.
        destruct_err_ub_oom mul_result; inv EVAL.
        symmetry in Heqmul_result.
        destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.

        cbn in H0.
        setoid_rewrite IP.VMemInt_intptr_dtyp in H0.
        setoid_rewrite dtyp_eqb_refl in H0.
        break_match_hyp_inv.

        cbn in CONV.
        move CONV after Heqb.
        break_match_hyp_inv.

        epose proof VMEM_REF.mmul_refine _ _ _ v1_inf v2_inf V1 V2 HMUL as (?&?&?&?).
        rewrite H0 in Heqo.
        rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
        inv Heqo.
        repeat setoid_rewrite H. cbn.
        break_match_goal; try reflexivity.
        setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
        setoid_rewrite dtyp_eqb_refl.
        break_match_goal; try reflexivity.
        setoid_rewrite Heqb1 in H1.
        inv H1.
      }

      break_match_hyp_inv.

      { remember (lift_OOM (mmul v1_fin v2_fin)) as mul_result.
        destruct_err_ub_oom mul_result; inv H0.
        symmetry in Heqmul_result.
        destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.

        cbn in CONV.
        move CONV after Heqb.
        repeat break_match_hyp_inv.

        epose proof VMEM_REF.mmul_refine _ _ _ v1_inf v2_inf V1 V2 HMUL as (?&?&?&?).
        rewrite H0 in Heqo.
        rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
        inv Heqo.
        repeat setoid_rewrite H. cbn.
        break_match_goal; try reflexivity.
        setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
        setoid_rewrite dtyp_eqb_refl.
        break_match_goal; try reflexivity.

        setoid_rewrite Heqb0 in H1.
        inv H1.
      }

      break_match_goal.
      {
        remember (lift_OOM (mmul v1_fin v2_fin)) as mul_result.
        destruct_err_ub_oom mul_result; inv H0.
        symmetry in Heqmul_result.
        destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.
        epose proof VMEM_REF.mmul_refine _ _ _ v1_inf v2_inf V1 V2 HMUL as (?&?&?&?).
        setoid_rewrite H.
        cbn.

        setoid_rewrite IP.VMemInt_intptr_dtyp in H1.
        rewrite dtyp_eqb_refl in H1.
        setoid_rewrite VMEM_REF.munsigned_refine in H1; eauto.
        rewrite H2 in H1.
        cbn in *.
        inv H1.

        cbn in CONV.
        break_match_hyp_inv.
        rewrite H0 in Heqo.
        rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
        inv Heqo; auto.
      }

      remember (lift_OOM (mmul v1_fin v2_fin)) as mul_result.
      destruct_err_ub_oom mul_result; inv H0.
      symmetry in Heqmul_result.
      destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.
      epose proof VMEM_REF.mmul_refine _ _ _ v1_inf v2_inf V1 V2 HMUL as (?&?&?&?).
      setoid_rewrite H.
      cbn.
      setoid_rewrite H2.

      setoid_rewrite IP.VMemInt_intptr_dtyp in H1.
      setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
      rewrite dtyp_eqb_refl.
      rewrite dtyp_eqb_refl in H1.
      setoid_rewrite VMEM_REF.munsigned_refine in H1; eauto.
      rewrite H2 in H1.
      cbn in *.
      inv H1.

      cbn in CONV.
      break_match_hyp_inv.
      rewrite H0 in Heqo.
      rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
      inv Heqo; auto.
    - (* Shl *)
      cbn in *.
      destruct (mshl v1_fin v2_fin) eqn:HSHL;
        cbn in *; inv EVAL.

      epose proof VMEM_REF.mshl_refine _ _ _ v1_inf v2_inf V1 V2 HSHL as (?&?&?).
      setoid_rewrite H; cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in H0.
      setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
      setoid_rewrite dtyp_eqb_refl.
      setoid_rewrite dtyp_eqb_refl in H0.
      setoid_rewrite VMEM_REF.munsigned_refine in H0; eauto.
      break_match_hyp_inv.
      setoid_rewrite Heqb.
      cbn.
      cbn in CONV.
      break_match_hyp_inv.
      rewrite H1 in Heqo.
      rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
      inv Heqo; auto.
    - (* UDiv *)
      cbn.
      cbn in EVAL.
      setoid_rewrite VMEM_REF.munsigned_refine in EVAL; eauto.
      break_match_hyp_inv.
      setoid_rewrite Heqb.
      setoid_rewrite VMEM_REF.munsigned_refine in H0; eauto.
      break_match_hyp_inv;
        setoid_rewrite Heqb0;
        cbn in CONV; inv CONV.
      + setoid_rewrite IP.VMemInt_intptr_dtyp;
          setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
        reflexivity.
      + break_match_hyp_inv.
        remember (mdivu v1_fin v2_fin) as div_res.
        symmetry in Heqdiv_res.
        pose proof VMEM_REF.mdivu_refine _ _ _ _ _ V1 V2 Heqdiv_res
          as (?&?&?).
        setoid_rewrite H.
        rewrite H0 in Heqo.
        rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
        inv Heqo.
        auto.
    - (* SDiv *)
      cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL.
      setoid_rewrite dtyp_eqb_refl in EVAL.
      inv EVAL.
    - (* LShr *)
      cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL.
      setoid_rewrite dtyp_eqb_refl in EVAL.
      setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
      setoid_rewrite dtyp_eqb_refl.
      cbn in *.
      rewrite Bool.andb_false_r in *.
      setoid_rewrite VMEM_REF.munsigned_refine in EVAL; eauto.
      break_match_hyp_inv; setoid_rewrite Heqb;
        cbn in CONV; inv CONV.
      + setoid_rewrite IP.VMemInt_intptr_dtyp;
          setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
        reflexivity.
      + break_match_hyp_inv.
        remember (mshru v1_fin v2_fin) as shru_res.
        symmetry in Heqshru_res.
        pose proof VMEM_REF.mshru_refine _ _ _ _ _ V1 V2 Heqshru_res
          as (?&?&?).
        setoid_rewrite H.
        rewrite H0 in Heqo.
        rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
        inv Heqo.
        auto.
    - (* AShr *)
      cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL.
      setoid_rewrite dtyp_eqb_refl in EVAL.
      inv EVAL.
    - (* URem *)
      cbn in *.
      setoid_rewrite VMEM_REF.munsigned_refine in EVAL; eauto.
      break_match_hyp_inv.
      setoid_rewrite Heqb.
      cbn in CONV.
      break_match_hyp_inv.
      remember (mmodu v1_fin v2_fin) as res.
      symmetry in Heqres.
      pose proof VMEM_REF.mmodu_refine _ _ _ _ _ V1 V2 Heqres
        as (?&?&?).
      setoid_rewrite H.
      rewrite H0 in Heqo.
      rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
      inv Heqo.
      auto.
    - (* SRem *)
      cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL.
      setoid_rewrite dtyp_eqb_refl in EVAL.
      inv EVAL.
    - (* And *)
      cbn in *; inv EVAL.
      remember (mand v1_fin v2_fin) as res_fin.
      symmetry in Heqres_fin.

      epose proof VMEM_REF.mand_refine _ _ _ v1_inf v2_inf V1 V2 Heqres_fin as (?&?&?).
      setoid_rewrite H; cbn in *.

      break_match_hyp_inv.
      rewrite H0 in Heqo.
      rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
      inv Heqo.
      reflexivity.
    - (* Or *)
      cbn in *; inv EVAL.
      destruct disjoint.
      + epose proof VMEM_REF.mor_refine _ _ _ v1_inf v2_inf V1 V2 (eq_refl) as (?&?&?).
        setoid_rewrite H.
        epose proof VMEM_REF.mxor_refine _ _ _ v1_inf v2_inf V1 V2 (eq_refl) as (?&?&?).
        setoid_rewrite H2.
        subst.
        erewrite <- VMEM_REF.mequ_refine; eauto.
        pose proof intptr_convert_succeeds (mor v1_fin v2_fin) as (?&?).
        break_match_goal; setoid_rewrite Heqb in H0; inv H0; cbn in CONV.
        * rewrite e in CONV.
          inv CONV.
          setoid_rewrite H1 in e.
          rewrite IS1.LP.IP.to_Z_from_Z in e.
          inv e.
          reflexivity.
        * inv CONV.
          setoid_rewrite IP.VMemInt_intptr_dtyp.
          setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
          reflexivity.
      +
      inversion H0. subst. clear H0.
      remember (mor v1_fin v2_fin) as res_fin.
      symmetry in Heqres_fin.

      epose proof VMEM_REF.mor_refine _ _ _ v1_inf v2_inf V1 V2 Heqres_fin as (?&?&?).
      setoid_rewrite H; cbn in *.

      break_match_hyp_inv.
      rewrite H0 in Heqo.
      rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
      inv Heqo.
      reflexivity.
    - (* Xor *)
      cbn in *; inv EVAL.
      remember (mxor v1_fin v2_fin) as res_fin.
      symmetry in Heqres_fin.

      epose proof VMEM_REF.mxor_refine _ _ _ v1_inf v2_inf V1 V2 Heqres_fin as (?&?&?).
      setoid_rewrite H; cbn in *.

      break_match_hyp_inv.
      rewrite H0 in Heqo.
      rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
      inv Heqo.
      reflexivity.
  Qed.

  Hint Resolve
    eval_int_op_ix_fin_inf
    eval_int_op_iptr_fin_inf
    : EVAL_INT_FIN_INF.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_iop_integer_h_fin_inf :
    forall dv1_fin dv2_fin res_fin iop dv1_inf dv2_inf,
      @eval_iop_integer_h err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        iop dv1_fin dv2_fin = ret res_fin ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @DV1.eval_iop_integer_h err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        iop dv1_inf dv2_inf = ret (fin_to_inf_dvalue res_fin).
  Proof.
    intros dv1_fin dv2_fin res_fin iop dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    unfold eval_iop_integer_h in EVAL.
    (* Nasty case analysis... *)
    repeat break_match_hyp_inv;
      rewrite_fin_to_inf_dvalue;
      cbn in *;
      try setoid_rewrite Heqb; cbn;
      try break_match_goal;
      cbn;
      eauto with EVAL_INT_FIN_INF.
    all: try
           (first
              [ inv Heqs
              | contradiction
           ]); try lia.
    3: {
      unfold intptr_fin_inf in *.
      break_match_hyp_inv.
      clear Heqs.
      eapply IS1.LP.IP.from_Z_to_Z in e0.
      rewrite <- e0 in n.
      lia.
    }

    { (* dv1: ix *)
      cbn in *; subst; try contradiction.
      dependent destruction e; cbn.
      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs.
      destruct p; clear e0.
      unfold intptr_fin_inf.
      repeat break_match_goal.
      eapply eval_int_op_ix_fin_inf; eauto.
    }

    { (* dv1: iptr *)
      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs.
      destruct p; clear e0.
      unfold intptr_fin_inf.
      repeat break_match_goal.
      clear Heqs Heqs0.
      eapply eval_int_op_iptr_fin_inf; eauto.
    }
  Qed.

  Hint Resolve eval_iop_integer_h_fin_inf : EVAL_INT_FIN_INF.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_iop_fin_inf :
    forall dv1_fin dv2_fin res_fin iop dv1_inf dv2_inf,
      @eval_iop err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        iop dv1_fin dv2_fin = ret res_fin ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @DV1.eval_iop err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        iop dv1_inf dv2_inf = ret (fin_to_inf_dvalue res_fin).
  Proof.
    intros dv1_fin dv2_fin res_fin iop dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    unfold eval_iop in EVAL.
    (* Nasty case analysis... *)
    repeat break_match_hyp_inv;
      rewrite_fin_to_inf_dvalue;
      cbn;
      try setoid_rewrite Heqb; eauto with EVAL_INT_FIN_INF.

    all: try
           (first
              [ inv Heqs
              | contradiction
           ]); try lia.

    all:
      try (cbn; break_match_goal; try contradiction; cbn; auto).

    3: {
      unfold intptr_fin_inf in *.
      break_match_hyp_inv.
      clear Heqs.
      eapply IS1.LP.IP.from_Z_to_Z in e0.
      rewrite <- e0 in n.
      lia.
    }

    { (* dv1: ix *)
      unfold fin_to_inf_dvalue.
      break_match_goal; try contradiction.
      dependent destruction e.
      break_match_goal; clear Heqs.
      destruct p; inv Heqp0.
      unfold intptr_fin_inf.
      repeat break_match_goal.
      eapply eval_int_op_ix_fin_inf; eauto.
    }

    { (* dv1: iptr *)
      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs.
      destruct p; clear e0.
      unfold intptr_fin_inf.
      repeat break_match_goal.
      clear Heqs Heqs0.
      eapply eval_int_op_iptr_fin_inf; eauto.
    }

    { (* dv1: Vector *)
      (* dv2 is also a vector *)
      remember (vec_loop (eval_iop_integer_h iop) (combine elts elts0)) as res.
      destruct_err_ub_oom res; cbn in *; inv Heqe; inv H0.
      change (unERR_UB_OOM0) with (unERR_UB_OOM {| unERR_UB_OOM := unERR_UB_OOM0 |}).
      rewrite <- Heqe0.

      symmetry in Heqres.
      erewrite vec_loop_fin_inf; cbn; eauto.

      intros dv1_fin dv2_fin res_fin dv1_inf dv2_inf H H0 H1.
      eapply eval_iop_integer_h_fin_inf; eauto.
    }
  Qed.

  Hint Resolve eval_iop_fin_inf : EVAL_INT_FIN_INF.

  (* TODO: Move this *)
  Lemma eval_int_op_ix_ub_fin_inf :
    forall sz v1 v2 iop ub_msg,
      @eval_int_op err_ub_oom (@Integers.bit_int sz) (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@VIntVMemInt (@Integers.bit_int sz) (@VInt_Bounded sz)) (@ToDvalue_Int sz)
        iop v1 v2 = UB_unERR_UB_OOM ub_msg ->
      @DV1.eval_int_op err_ub_oom (@Integers.bit_int sz)
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@VIntVMemInt (@Integers.bit_int sz) (@VInt_Bounded sz)) (@DV1.ToDvalue_Int sz)
        iop v1 v2 = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros sz v1 v2 iop ub_msg EVAL.
    destruct iop;
      try solve
        [ cbn in *;
          repeat break_match_hyp_inv; cbn in *;
          cbn in CONV; inv CONV;
          cbn in *; reflexivity
        | cbn in *;
          repeat break_match_hyp_inv; cbn in *; inv EVAL;
          cbn in CONV; inv CONV;
          cbn in *; reflexivity
        | cbn in *;
          repeat break_match_hyp_inv; auto
        ].
  Qed.

  (* TODO: Move this *)
  Lemma eval_int_op_iptr_ub_fin_inf :
    forall v1_fin v2_fin v1_inf v2_inf iop ub_msg,
      @eval_int_op err_ub_oom IP.intptr (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        VMemInt_intptr' ToDvalue_intptr
        iop v1_fin v2_fin = UB_unERR_UB_OOM ub_msg ->
      IS1.LP.IP.from_Z (IP.to_Z v1_fin) = NoOom v1_inf ->
      IS1.LP.IP.from_Z (IP.to_Z v2_fin) = NoOom v2_inf ->
      @DV1.eval_int_op err_ub_oom IS1.LP.IP.intptr
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        DV1.VMemInt_intptr' DV1.ToDvalue_intptr
        iop v1_inf v2_inf = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros v1_fin v2_fin v1_inf v2_inf iop ub_msg
      EVAL LIFT1 LIFT2.

    assert (IP.to_Z v1_fin = IS1.LP.IP.to_Z v1_inf) as V1.
    { erewrite IS1.LP.IP.from_Z_to_Z; eauto. }

    assert (IP.to_Z v2_fin = IS1.LP.IP.to_Z v2_inf) as V2.
    { erewrite IS1.LP.IP.from_Z_to_Z; eauto. }

    destruct iop.
    - (* Add *)
      cbn in *.
      repeat rewrite VMEM_IP_PROP1.madd_carry_zero, VMEM_IP_PROP1.madd_overflow_zero.
      repeat rewrite VMEM_IP_PROP2.madd_carry_zero, VMEM_IP_PROP2.madd_overflow_zero in EVAL.
      setoid_rewrite VMEM_IP_PROP1.mequ_zero_one_false.
      setoid_rewrite VMEM_IP_PROP2.mequ_zero_one_false in EVAL.
      repeat rewrite Bool.andb_false_r.
      repeat rewrite Bool.andb_false_r in EVAL.
      cbn in *.

      remember (lift_OOM (madd v1_fin v2_fin)) as add_result.
      destruct_err_ub_oom add_result; inv EVAL.
      symmetry in Heqadd_result.
      destruct (madd v1_fin v2_fin) eqn:HADD; inv Heqadd_result.
    - (* Sub *)
      cbn in *.
      repeat rewrite VMEM_IP_PROP1.msub_borrow_zero, VMEM_IP_PROP1.msub_overflow_zero.
      repeat rewrite VMEM_IP_PROP2.msub_borrow_zero, VMEM_IP_PROP2.msub_overflow_zero in EVAL.
      setoid_rewrite VMEM_IP_PROP1.mequ_zero_one_false.
      setoid_rewrite VMEM_IP_PROP2.mequ_zero_one_false in EVAL.
      repeat rewrite Bool.andb_false_r.
      repeat rewrite Bool.andb_false_r in EVAL.
      cbn in *.

      remember (lift_OOM (msub v1_fin v2_fin)) as sub_result.
      destruct_err_ub_oom sub_result; inv EVAL.
      symmetry in Heqsub_result.
      destruct (msub v1_fin v2_fin) eqn:HSUB; inv Heqsub_result.
    - (* Mul *)
      cbn in *.
      destruct mbitwidth; cbn in EVAL.
      2: {
        remember (lift_OOM (mmul v1_fin v2_fin)) as mul_result.
        destruct_err_ub_oom mul_result; inv EVAL.
        symmetry in Heqmul_result.
        destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.

        cbn in H0.
        setoid_rewrite IP.VMemInt_intptr_dtyp in H0.
        setoid_rewrite dtyp_eqb_refl in H0.
        break_match_hyp_inv.
      }

      break_match_hyp_inv.

      { remember (lift_OOM (mmul v1_fin v2_fin)) as mul_result.
        destruct_err_ub_oom mul_result; inv H0.
        symmetry in Heqmul_result.
        destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.
      }

      break_match_goal.
      {
        remember (lift_OOM (mmul v1_fin v2_fin)) as mul_result.
        destruct_err_ub_oom mul_result; inv H0.
        symmetry in Heqmul_result.
        destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.
        destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.
        epose proof VMEM_REF.mmul_refine _ _ _ v1_inf v2_inf V1 V2 HMUL as (?&?&?&?).
        setoid_rewrite H.
        cbn.

        setoid_rewrite IP.VMemInt_intptr_dtyp in H1.
        rewrite dtyp_eqb_refl in H1.
        setoid_rewrite VMEM_REF.munsigned_refine in H1; eauto.
        rewrite H2 in H1.
        cbn in *.
        inv H1.
      }

      remember (lift_OOM (mmul v1_fin v2_fin)) as mul_result.
      destruct_err_ub_oom mul_result; inv H0.
      symmetry in Heqmul_result.
      destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.
      destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.
      epose proof VMEM_REF.mmul_refine _ _ _ v1_inf v2_inf V1 V2 HMUL as (?&?&?&?).
      setoid_rewrite H.
      cbn.
      setoid_rewrite H2.

      setoid_rewrite IP.VMemInt_intptr_dtyp in H1.
      setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
      rewrite dtyp_eqb_refl.
      rewrite dtyp_eqb_refl in H1.
      setoid_rewrite VMEM_REF.munsigned_refine in H1; eauto.
      rewrite H2 in H1.
      cbn in *.
      inv H1.
    - (* Shl *)
      cbn in *.
      destruct (mshl v1_fin v2_fin) eqn:HSHL;
        cbn in *; inv EVAL.

      epose proof VMEM_REF.mshl_refine _ _ _ v1_inf v2_inf V1 V2 HSHL as (?&?&?).
      setoid_rewrite H; cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in H0.
      setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
      setoid_rewrite dtyp_eqb_refl.
      setoid_rewrite dtyp_eqb_refl in H0.
      setoid_rewrite VMEM_REF.munsigned_refine in H0; eauto.
      break_match_hyp_inv.
    - (* UDiv *)
      cbn.
      cbn in EVAL.
      setoid_rewrite VMEM_REF.munsigned_refine in EVAL; eauto.
      break_match_hyp_inv.
      setoid_rewrite Heqb; auto.
      setoid_rewrite VMEM_REF.munsigned_refine in H0; eauto.
      break_match_hyp_inv;
        setoid_rewrite Heqb0;
        cbn in CONV; inv CONV.
    - (* SDiv *)
      cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL.
      setoid_rewrite dtyp_eqb_refl in EVAL.
      inv EVAL.
    - (* LShr *)
      cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL.
      setoid_rewrite dtyp_eqb_refl in EVAL.
      setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
      setoid_rewrite dtyp_eqb_refl.
      cbn in *.
      rewrite Bool.andb_false_r in *.
      setoid_rewrite VMEM_REF.munsigned_refine in EVAL; eauto.
      break_match_hyp_inv; setoid_rewrite Heqb;
        cbn in CONV; inv CONV.
    - (* AShr *)
      cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL.
      setoid_rewrite dtyp_eqb_refl in EVAL.
      inv EVAL.
    - (* URem *)
      cbn in *.
      setoid_rewrite VMEM_REF.munsigned_refine in EVAL; eauto.
      break_match_hyp_inv.
      setoid_rewrite Heqb.
      auto.
    - (* SRem *)
      cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL.
      setoid_rewrite dtyp_eqb_refl in EVAL.
      inv EVAL.
    - (* And *)
      cbn in *; inv EVAL.
    - (* Or *)
      destruct disjoint; 
      cbn in *; inv EVAL.
      + epose proof VMEM_REF.mor_refine _ _ _ v1_inf v2_inf V1 V2 (eq_refl) as (?&?&?).
        setoid_rewrite H.
        epose proof VMEM_REF.mxor_refine _ _ _ v1_inf v2_inf V1 V2 (eq_refl) as (?&?&?).
        setoid_rewrite H2.
        subst.
        erewrite <- VMEM_REF.mequ_refine; eauto.
        pose proof intptr_convert_succeeds (mor v1_fin v2_fin) as (?&?).
        break_match_goal; setoid_rewrite Heqb in H0; inv H0; cbn in CONV.
    - (* Xor *)
      cbn in *; inv EVAL.
  Qed.

  Hint Resolve
    eval_int_op_ix_ub_fin_inf
    eval_int_op_iptr_ub_fin_inf
    : EVAL_INT_FIN_INF.

  (* TODO: Move this *)
  Lemma eval_int_op_ix_err_fin_inf :
    forall sz v1 v2 iop err_msg,
      @eval_int_op err_ub_oom (@Integers.bit_int sz) (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@VIntVMemInt (@Integers.bit_int sz) (@VInt_Bounded sz)) (@ToDvalue_Int sz)
        iop v1 v2 = ERR_unERR_UB_OOM err_msg ->
      @DV1.eval_int_op err_ub_oom (@Integers.bit_int sz)
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@VIntVMemInt (@Integers.bit_int sz) (@VInt_Bounded sz)) (@DV1.ToDvalue_Int sz)
        iop v1 v2 = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros sz v1 v2 iop ub_msg EVAL.
    destruct iop;
      try solve
        [ cbn in *;
          repeat break_match_hyp_inv; cbn in *;
          cbn in CONV; inv CONV;
          cbn in *; reflexivity
        | cbn in *;
          repeat break_match_hyp_inv; cbn in *; inv EVAL;
          cbn in CONV; inv CONV;
          cbn in *; reflexivity
        | cbn in *;
          repeat break_match_hyp_inv; auto
        ].
  Qed.

  (* TODO: Move this *)
  Lemma eval_int_op_iptr_err_fin_inf :
    forall v1_fin v2_fin v1_inf v2_inf iop err_msg,
      @eval_int_op err_ub_oom IP.intptr (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        VMemInt_intptr' ToDvalue_intptr
        iop v1_fin v2_fin = ERR_unERR_UB_OOM err_msg ->
      IS1.LP.IP.from_Z (IP.to_Z v1_fin) = NoOom v1_inf ->
      IS1.LP.IP.from_Z (IP.to_Z v2_fin) = NoOom v2_inf ->
      @DV1.eval_int_op err_ub_oom IS1.LP.IP.intptr
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        DV1.VMemInt_intptr' DV1.ToDvalue_intptr
        iop v1_inf v2_inf = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros v1_fin v2_fin v1_inf v2_inf iop err_msg
      EVAL LIFT1 LIFT2.

    assert (IP.to_Z v1_fin = IS1.LP.IP.to_Z v1_inf) as V1.
    { erewrite IS1.LP.IP.from_Z_to_Z; eauto. }

    assert (IP.to_Z v2_fin = IS1.LP.IP.to_Z v2_inf) as V2.
    { erewrite IS1.LP.IP.from_Z_to_Z; eauto. }

    destruct iop.
    - (* Add *)
      cbn in *.
      repeat rewrite VMEM_IP_PROP1.madd_carry_zero, VMEM_IP_PROP1.madd_overflow_zero.
      repeat rewrite VMEM_IP_PROP2.madd_carry_zero, VMEM_IP_PROP2.madd_overflow_zero in EVAL.
      setoid_rewrite VMEM_IP_PROP1.mequ_zero_one_false.
      setoid_rewrite VMEM_IP_PROP2.mequ_zero_one_false in EVAL.
      repeat rewrite Bool.andb_false_r.
      repeat rewrite Bool.andb_false_r in EVAL.
      cbn in *.

      remember (lift_OOM (madd v1_fin v2_fin)) as add_result.
      destruct_err_ub_oom add_result; inv EVAL.
      symmetry in Heqadd_result.
      destruct (madd v1_fin v2_fin) eqn:HADD; inv Heqadd_result.
    - (* Sub *)
      cbn in *.
      repeat rewrite VMEM_IP_PROP1.msub_borrow_zero, VMEM_IP_PROP1.msub_overflow_zero.
      repeat rewrite VMEM_IP_PROP2.msub_borrow_zero, VMEM_IP_PROP2.msub_overflow_zero in EVAL.
      setoid_rewrite VMEM_IP_PROP1.mequ_zero_one_false.
      setoid_rewrite VMEM_IP_PROP2.mequ_zero_one_false in EVAL.
      repeat rewrite Bool.andb_false_r.
      repeat rewrite Bool.andb_false_r in EVAL.
      cbn in *.

      remember (lift_OOM (msub v1_fin v2_fin)) as sub_result.
      destruct_err_ub_oom sub_result; inv EVAL.
      symmetry in Heqsub_result.
      destruct (msub v1_fin v2_fin) eqn:HSUB; inv Heqsub_result.
    - (* Mul *)
      cbn in *.
      destruct mbitwidth; cbn in EVAL.
      2: {
        remember (lift_OOM (mmul v1_fin v2_fin)) as mul_result.
        destruct_err_ub_oom mul_result; inv EVAL.
        symmetry in Heqmul_result.
        destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.

        cbn in H0.
        setoid_rewrite IP.VMemInt_intptr_dtyp in H0.
        setoid_rewrite dtyp_eqb_refl in H0.
        break_match_hyp_inv.
      }

      break_match_hyp_inv.

      { remember (lift_OOM (mmul v1_fin v2_fin)) as mul_result.
        destruct_err_ub_oom mul_result; inv H0.
        symmetry in Heqmul_result.
        destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.
      }

      break_match_goal.
      {
        remember (lift_OOM (mmul v1_fin v2_fin)) as mul_result.
        destruct_err_ub_oom mul_result; inv H0.
        symmetry in Heqmul_result.
        destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.
        destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.
        epose proof VMEM_REF.mmul_refine _ _ _ v1_inf v2_inf V1 V2 HMUL as (?&?&?&?).
        setoid_rewrite H.
        cbn.

        setoid_rewrite IP.VMemInt_intptr_dtyp in H1.
        rewrite dtyp_eqb_refl in H1.
        setoid_rewrite VMEM_REF.munsigned_refine in H1; eauto.
        rewrite H2 in H1.
        cbn in *.
        inv H1.
      }

      remember (lift_OOM (mmul v1_fin v2_fin)) as mul_result.
      destruct_err_ub_oom mul_result; inv H0.
      symmetry in Heqmul_result.
      destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.
      destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.
      epose proof VMEM_REF.mmul_refine _ _ _ v1_inf v2_inf V1 V2 HMUL as (?&?&?&?).
      setoid_rewrite H.
      cbn.
      setoid_rewrite H2.

      setoid_rewrite IP.VMemInt_intptr_dtyp in H1.
      setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
      rewrite dtyp_eqb_refl.
      rewrite dtyp_eqb_refl in H1.
      setoid_rewrite VMEM_REF.munsigned_refine in H1; eauto.
      rewrite H2 in H1.
      cbn in *.
      inv H1.
    - (* Shl *)
      cbn in *.
      destruct (mshl v1_fin v2_fin) eqn:HSHL;
        cbn in *; inv EVAL.

      epose proof VMEM_REF.mshl_refine _ _ _ v1_inf v2_inf V1 V2 HSHL as (?&?&?).
      setoid_rewrite H; cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in H0.
      setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
      setoid_rewrite dtyp_eqb_refl.
      setoid_rewrite dtyp_eqb_refl in H0.
      setoid_rewrite VMEM_REF.munsigned_refine in H0; eauto.
      break_match_hyp_inv.
    - (* UDiv *)
      cbn.
      cbn in EVAL.
      setoid_rewrite VMEM_REF.munsigned_refine in EVAL; eauto.
      break_match_hyp_inv.
      setoid_rewrite Heqb; auto.
      setoid_rewrite VMEM_REF.munsigned_refine in H0; eauto.
      break_match_hyp_inv;
        setoid_rewrite Heqb0;
        cbn in CONV; inv CONV.
    - (* SDiv *)
      cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL.
      setoid_rewrite dtyp_eqb_refl in EVAL.
      setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
      setoid_rewrite dtyp_eqb_refl.
      inv EVAL.
      reflexivity.
    - (* LShr *)
      cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL.
      setoid_rewrite dtyp_eqb_refl in EVAL.
      setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
      setoid_rewrite dtyp_eqb_refl.
      cbn in *.
      rewrite Bool.andb_false_r in *.
      setoid_rewrite VMEM_REF.munsigned_refine in EVAL; eauto.
      break_match_hyp_inv; setoid_rewrite Heqb;
        cbn in CONV; inv CONV.
    - (* AShr *)
      cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL.
      setoid_rewrite dtyp_eqb_refl in EVAL.
      setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
      setoid_rewrite dtyp_eqb_refl.
      inv EVAL.
      reflexivity.
    - (* URem *)
      cbn in *.
      setoid_rewrite VMEM_REF.munsigned_refine in EVAL; eauto.
      break_match_hyp_inv.
    - (* SRem *)
      cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL.
      setoid_rewrite dtyp_eqb_refl in EVAL.
      setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
      setoid_rewrite dtyp_eqb_refl.
      inv EVAL.
      reflexivity.
    - (* And *)
      cbn in *; inv EVAL.
    - (* Or *)
      destruct disjoint; 
      cbn in *; inv EVAL.
      + epose proof VMEM_REF.mor_refine _ _ _ v1_inf v2_inf V1 V2 (eq_refl) as (?&?&?).
        setoid_rewrite H.
        epose proof VMEM_REF.mxor_refine _ _ _ v1_inf v2_inf V1 V2 (eq_refl) as (?&?&?).
        setoid_rewrite H2.
        subst.
        erewrite <- VMEM_REF.mequ_refine; eauto.
        pose proof intptr_convert_succeeds (mor v1_fin v2_fin) as (?&?).
        break_match_goal; setoid_rewrite Heqb in H0; inv H0; cbn in CONV.
    - (* Xor *)
      cbn in *; inv EVAL.
  Qed.

  Hint Resolve
    eval_int_op_ix_err_fin_inf
    eval_int_op_iptr_err_fin_inf
    : EVAL_INT_FIN_INF.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_iop_integer_h_ub_fin_inf :
    forall dv1_fin dv2_fin ub_msg iop dv1_inf dv2_inf,
      @eval_iop_integer_h err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        iop dv1_fin dv2_fin = UB_unERR_UB_OOM ub_msg ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @DV1.eval_iop_integer_h err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        iop dv1_inf dv2_inf = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros dv1_fin dv2_fin ub_msg iop dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    unfold eval_iop_integer_h in EVAL.
    (* Nasty case analysis... *)
    repeat break_match_hyp_inv;
      rewrite_fin_to_inf_dvalue;
      cbn;
      try setoid_rewrite Heqb; eauto with EVAL_INT_FIN_INF.

    all: try
           (first
              [ inv Heqs
              | contradiction
           ]); try lia.

    all:
      try (cbn; break_match_goal; try contradiction; cbn; auto).

    { (* dv1: ix *)
      unfold intptr_fin_inf.
      repeat break_match_goal; try contradiction.
      dependent destruction e; cbn in *; subst.
      eapply eval_int_op_ix_ub_fin_inf; eauto.
    }

    { (* dv1: iptr *)
      unfold intptr_fin_inf.
      repeat break_match_goal.
      clear Heqs Heqs0.
      eapply eval_int_op_iptr_ub_fin_inf; eauto.
    }

    exfalso.
    eapply n.
    unfold intptr_fin_inf.
    break_match_goal.
    clear Heqs.
    eapply intptr_convert_safe in e.
    erewrite IP.from_Z_to_Z; eauto.
  Qed.

  Hint Resolve eval_iop_integer_h_ub_fin_inf : EVAL_INT_FIN_INF.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_iop_integer_h_err_fin_inf :
    forall dv1_fin dv2_fin ub_msg iop dv1_inf dv2_inf,
      @eval_iop_integer_h err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        iop dv1_fin dv2_fin = ERR_unERR_UB_OOM ub_msg ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @DV1.eval_iop_integer_h err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        iop dv1_inf dv2_inf = ERR_unERR_UB_OOM ub_msg.
  Proof.
    intros dv1_fin dv2_fin ub_msg iop dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    unfold eval_iop_integer_h in EVAL.
    (* Nasty case analysis... *)
    repeat break_match_hyp_inv;
      rewrite_fin_to_inf_dvalue;
      cbn;
      try setoid_rewrite Heqb; eauto with EVAL_INT_FIN_INF.

    all: try
           (first
              [ inv Heqs
              | contradiction
           ]); try lia.

    all:
      try (cbn; break_match_goal; try contradiction; cbn; auto).
    all: auto.

    { (* dv1: ix *)
      unfold intptr_fin_inf.
      repeat break_match_goal; try contradiction.
      dependent destruction e; cbn in *; subst.
      eapply eval_int_op_ix_err_fin_inf; eauto.
    }

    { (* dv1: iptr *)
      unfold intptr_fin_inf.
      repeat break_match_goal.
      clear Heqs Heqs0.
      eapply eval_int_op_iptr_err_fin_inf; eauto.
    }
  Qed.

  Hint Resolve eval_iop_integer_h_err_fin_inf : EVAL_INT_FIN_INF.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_iop_ub_fin_inf :
    forall dv1_fin dv2_fin ub_msg iop dv1_inf dv2_inf,
      @eval_iop err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        iop dv1_fin dv2_fin = UB_unERR_UB_OOM ub_msg ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @DV1.eval_iop err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        iop dv1_inf dv2_inf = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros dv1_fin dv2_fin res_fin iop dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    unfold eval_iop in EVAL.
    (* Nasty case analysis... *)
    repeat break_match_hyp_inv;
      rewrite_fin_to_inf_dvalue;
      cbn;
      try setoid_rewrite Heqb; eauto with EVAL_INT_FIN_INF.

    all: try inv Heqs.
    all: (try break_match_goal; try contradiction; cbn; auto).

    { (* dv1: ix *)
      unfold intptr_fin_inf.
      repeat break_match_goal; try contradiction.
      dependent destruction e; cbn in *; subst.
      eapply eval_int_op_ix_ub_fin_inf; eauto.
    }

    { (* dv1: iptr *)
      unfold fin_to_inf_dvalue.
      unfold intptr_fin_inf.
      repeat break_match_goal.
      clear Heqs Heqs0.
      eapply eval_int_op_iptr_ub_fin_inf; eauto.
    }

    { exfalso.
      eapply n.
      unfold intptr_fin_inf.
      break_match_goal.
      clear Heqs.
      eapply intptr_convert_safe in e.
      erewrite IP.from_Z_to_Z; eauto.
    }

    { (* dv1: Vector *)
      (* dv2 is also a vector *)
      remember (vec_loop (eval_iop_integer_h iop) (combine elts elts0)) as res.
      destruct_err_ub_oom res; cbn in *; inv Heqe; inv H0.

      change (unERR_UB_OOM0) with (unERR_UB_OOM {| unERR_UB_OOM := unERR_UB_OOM0 |}).
      rewrite <- Heqe0.
      symmetry in Heqres.
      erewrite vec_loop_ub_fin_inf; cbn; eauto.

      intros dv1_fin dv2_fin res_fin' dv1_inf dv2_inf H H0 H1.
      eapply eval_iop_integer_h_fin_inf; eauto.

      intros dv1_fin dv2_fin ub_msg dv1_inf dv2_inf H H0 H1.
      eapply eval_iop_integer_h_ub_fin_inf; eauto.
    }
  Qed.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_iop_err_fin_inf :
    forall dv1_fin dv2_fin err_msg iop dv1_inf dv2_inf,
      @eval_iop err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        iop dv1_fin dv2_fin = ERR_unERR_UB_OOM err_msg ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @DV1.eval_iop err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        iop dv1_inf dv2_inf = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros dv1_fin dv2_fin res_fin iop dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    unfold eval_iop in EVAL.
    (* Nasty case analysis... *)
    repeat break_match_hyp_inv;
      rewrite_fin_to_inf_dvalue;
      cbn;
      try setoid_rewrite Heqb; eauto with EVAL_INT_FIN_INF.

    all: try inv Heqs.
    all: (try break_match_goal; try contradiction; cbn; auto).

    { (* dv1: ix *)
      unfold intptr_fin_inf.
      repeat break_match_goal; try contradiction.
      dependent destruction e; cbn in *; subst.
      eapply eval_int_op_ix_err_fin_inf; eauto.
    }

    { (* dv1: iptr *)
      unfold fin_to_inf_dvalue.
      unfold intptr_fin_inf.
      repeat break_match_goal.
      clear Heqs Heqs0.
      eapply eval_int_op_iptr_err_fin_inf; eauto.
    }

    { (* dv1: Vector *)
      (* dv2 is also a vector *)
      remember (vec_loop (eval_iop_integer_h iop) (combine elts elts0)) as res.
      destruct_err_ub_oom res; cbn in *; inv Heqe; inv H0.

      change (unERR_UB_OOM0) with (unERR_UB_OOM {| unERR_UB_OOM := unERR_UB_OOM0 |}).
      rewrite <- Heqe0.
      symmetry in Heqres.
      erewrite vec_loop_err_fin_inf; cbn; eauto.

      intros dv1_fin dv2_fin res_fin' dv1_inf dv2_inf H H0 H1.
      eapply eval_iop_integer_h_fin_inf; eauto.

      intros dv1_fin dv2_fin ub_msg dv1_inf dv2_inf H H0 H1.
      eapply eval_iop_integer_h_err_fin_inf; eauto.
    }
  Qed.

  Hint Resolve eval_iop_ub_fin_inf : EVAL_INT_FIN_INF.
  Hint Resolve eval_iop_err_fin_inf : EVAL_INT_FIN_INF.

  Lemma orutt_eval_iop :
    forall E1 E2
      `{OOM1 : OOME -< E1} `{OOM2 : OOME -< E2}
      `{UB1 : UBE -< E1} `{UB2 : UBE -< E2}
      `{ERR1: FailureE -< E1} `{ERR2: FailureE -< E2}
      (pre : prerel E1 E2) (post : postrel E1 E2)
      iop dv1_1 dv2_1 dv1_2 dv2_2,
      dvalue_refine_strict dv1_1 dv1_2 ->
      dvalue_refine_strict dv2_1 dv2_2 ->
      (forall e1 e2, @subevent UBE E2 UB2 void e1 <> @subevent OOME E2 OOM2 void e2) ->
      (forall e1 e2, @subevent FailureE E2 ERR2 void e1 <> @subevent OOME E2 OOM2 void e2) ->
      (pre void void (@subevent UBE E1 UB1 void (ThrowUB tt)) (@subevent UBE E2 UB2 void (ThrowUB tt))) ->
      (pre void void (@subevent FailureE E1 ERR1 void (Throw tt)) (@subevent FailureE E2 ERR2 void (Throw tt))) ->
      orutt pre post dvalue_refine_strict
        (DV1.eval_iop iop dv1_1 dv2_1) (eval_iop iop dv1_2 dv2_2)
        (OOM:=OOME).
  Proof.
    intros E1 E2 ? ? ? ? ? ? pre post iop dv1_1 dv2_1 dv1_2 dv2_2 H H0 OOMDISC ERRDISC UBPRE ERRPRE.
    rewrite eval_iop_err_ub_oom_to_itree,
      TLR1.eval_iop_err_ub_oom_to_itree.

    remember (eval_iop iop dv1_2 dv2_2) as e.
    destruct_err_ub_oom e; symmetry in Heqe.
    - apply orutt_raiseOOM.
    - erewrite eval_iop_ub_fin_inf; cbn; eauto;
        try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_raiseUB; cbn; auto.
    - erewrite eval_iop_err_fin_inf; cbn; eauto;
        try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_raise; cbn; auto.
    - erewrite eval_iop_fin_inf; cbn; eauto; subst.
      2-3: try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_Ret; cbn; eauto.
      apply fin_to_inf_dvalue_refine_strict.
  Qed.

  #[global] Hint Resolve
    orutt_eval_iop
    : ORUTT.
End IntOpsRefine.
