From Stdlib Require Import
  Lia
  ZArith
  List
  Relations
  String
  Program.Equality.

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
  LLVMEvents
  Memory.Sizeof.

Import DynamicTypes.

From Vellvm.Semantics.InfiniteToFinite.Conversions Require Import
  BaseConversions
  DvalueConversions
  EventConversions.

From Vellvm.Semantics.InfiniteToFinite.LangRefine Require Import
  Events
  Sizeof
  Values
  Bytes
  PointerOps.

From Vellvm.Utils Require Import
  Error
  Tactics
  Monads
  MapMonadExtra
  OOMRutt
  OOMRuttProps
  ListUtil
  RuttPropsExtra
  VellvmRelations
  ErrOomPoison
  ErrUbOomProp.

From ITree Require Import
  ITree
  Basics.HeterogeneousRelations
  Eq.Rutt
  Eq.RuttFacts
  Eq.Eqit.

Import ListNotations.

Module Type ConversionsRefine
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
  (ER : EventRefine IS1 IS2 LLVM1 LLVM2 AC1 AC2 DVC DVCrev EC)
  (VAL_REF : ValueRefine 
               IS1 IS2
               LLVM1 LLVM2
               AC1 AC2
               IPS ACS
               DVC DVCrev
               EC SIZEOF_REF ER)
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
                 VAL_REF).

  Import DVC.
  Import TLR2.
  Import IS2.LP.
  Import IS2.LP.DV.
  Import IS2.LLVM.D.
  Import ER.
  Import IPS.
  Import ADDR.
  Import VAL_REF.
  Import BYTES_REF.
  Import SIZEOF_REF.

  Lemma get_conv_case_pure_fin_inf:
    forall conv t_from dv t_to res,
      get_conv_case conv t_from dv t_to = Conv_Pure res ->
      IS1.LLVM.MEM.CP.CONC.get_conv_case conv t_from (fin_to_inf_dvalue dv) t_to = DV1.Conv_Pure (fin_to_inf_dvalue res).
  Proof.
    intros conv t_from dv t_to res CONV.
    destruct conv.
    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        unfold fin_to_inf_uvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;
        try (inv H0; subst_existT; try rewrite Heqb; auto; break_match_goal; clear Heqs; destruct p; clear e0;
             cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        unfold fin_to_inf_uvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;
        try (inv H0; subst_existT; try rewrite Heqb; auto; break_match_goal; clear Heqs; destruct p; clear e0;
             cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        unfold fin_to_inf_uvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;
        try (inv H0; subst_existT; try rewrite Heqb; auto; break_match_goal; clear Heqs; destruct p; clear e0;
             cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue, fin_to_inf_uvalue; inv CONV.
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue, fin_to_inf_uvalue; inv CONV.
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        unfold fin_to_inf_uvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;
        try (inv H0; subst_existT; try rewrite Heqb; auto; break_match_goal; clear Heqs; destruct p; clear e0;
             cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        unfold fin_to_inf_uvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;
        try (inv H0; subst_existT; try rewrite Heqb; auto; break_match_goal; clear Heqs; destruct p; clear e0;
             cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        unfold fin_to_inf_uvalue;
        inv CONV.
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        unfold fin_to_inf_uvalue;
        inv CONV.
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        unfold fin_to_inf_uvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;

        try (inv H0; auto; break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        unfold fin_to_inf_uvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;

        try (inv H0; auto; break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; reflexivity).
    }

    { (* Conversions... *)
      unfold get_conv_case in CONV.
      unfold IS1.LLVM.MEM.CP.CONC.get_conv_case.

      repeat rewrite bit_sizeof_dtyp_fin_inf.
      unfold MemHelpers.dtyp_eqb,
        IS1.LLVM.MEM.CP.CONC.MemHelpers.dtyp_eqb in *.

      break_match_hyp.
      2: {
        break_match_hyp.
        - remember (ErrOOMPoison_handle_poison_and_oom DVALUE_Poison
                            (DVALUE_BYTES.dvalue_bytes_to_dvalue
                               (DVALUE_BYTES.dvalue_to_dvalue_bytes dv t_from) t_to)) as x.
          destruct_err_ub_oom x; inv CONV.
          erewrite dvalue_bytes_to_dvalue_fin_inf; eauto.
          cbn; auto.
          rewrite dvalue_to_dvalue_bytes_fin_to_inf_dvalue.
          apply dvalue_bytes_refine_fin_to_inf_dvalue_bytes.
        - inv CONV.
      }
      inv CONV; auto.
    }

    { (* Addrspacecast *)
      cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; inv CONV.
    }
  Qed.

  Lemma get_conv_case_itop_fin_inf:
    forall conv t_from dv t_to res,
      get_conv_case conv t_from dv t_to = Conv_ItoP res ->
      IS1.LLVM.MEM.CP.CONC.get_conv_case conv t_from (fin_to_inf_dvalue dv) t_to = DV1.Conv_ItoP (fin_to_inf_dvalue res).
  Proof.
    intros conv t_from dv t_to res CONV.
    destruct conv.
    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;

        try (inv H0; auto; break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;

        try (inv H0; auto; break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;

        try (inv H0; auto; break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue; inv CONV.
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue; inv CONV.
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;

        try (inv H0; auto; break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;

        try (inv H0; auto; break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        inv CONV.
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        inv CONV.
    }

    { (* inttoptr *)
      cbn in *.
      repeat break_match_hyp_inv; reflexivity.
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;

        try (inv H0; auto; break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; reflexivity).
    }

    { (* Conversions... *)
      unfold get_conv_case in CONV.
      unfold IS1.LLVM.MEM.CP.CONC.get_conv_case.

      repeat rewrite bit_sizeof_dtyp_fin_inf.
      repeat break_match_hyp_inv.
    }

    { (* Addrspacecast *)
      cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; inv CONV.
    }
  Qed.

  Lemma get_conv_case_ptoi_fin_inf:
    forall conv t_from dv t_to res,
      get_conv_case conv t_from dv t_to = Conv_PtoI res ->
      IS1.LLVM.MEM.CP.CONC.get_conv_case conv t_from (fin_to_inf_dvalue dv) t_to = DV1.Conv_PtoI (fin_to_inf_dvalue res).
  Proof.
    intros conv t_from dv t_to res CONV.
    destruct conv.
    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;

        try (inv H0; auto; break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;

        try (inv H0; auto; break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;

        try (inv H0; auto; break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue; inv CONV.
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue; inv CONV.
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;

        try (inv H0; auto; break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;

        try (inv H0; auto; break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        inv CONV.
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        inv CONV.
    }

    { (* inttoptr *)
      cbn in *.
      repeat break_match_hyp_inv; reflexivity.
    }

    { cbn in *.
      repeat break_match_hyp_inv; auto.
    }

    { (* Conversions... *)
      unfold get_conv_case in CONV.
      unfold IS1.LLVM.MEM.CP.CONC.get_conv_case.

      repeat rewrite bit_sizeof_dtyp_fin_inf.
      repeat break_match_hyp_inv.
    }

    { (* Addrspacecast *)
      cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; inv CONV.
    }
  Qed.

  Lemma get_conv_case_bitcast_illegal_fin_inf :
    forall (t_from : dtyp)
      (dv : dvalue)
      (t_to : dtyp)
      (msg : string)
      (CONV : get_conv_case LLVMAst.Bitcast t_from dv t_to = Conv_Illegal msg),
      IS1.LLVM.MEM.CP.CONC.get_conv_case LLVMAst.Bitcast t_from (fin_to_inf_dvalue dv) t_to =
        DV1.Conv_Illegal msg.
  Proof.
    intros t_from dv t_to msg CONV.
    cbn in *; inv CONV; auto.

    unfold MemHelpers.dtyp_eqb,
      IS1.LLVM.MEM.CP.CONC.MemHelpers.dtyp_eqb in *.
    break_match_hyp_inv.
    setoid_rewrite bit_sizeof_dtyp_fin_inf.
    break_match_hyp_inv; auto.
    remember (ErrOOMPoison_handle_poison_and_oom DVALUE_Poison
                          (DVALUE_BYTES.dvalue_bytes_to_dvalue
                             (DVALUE_BYTES.dvalue_to_dvalue_bytes dv t_from) t_to)) as res.
    destruct_err_ub_oom res; inv H0; cbn in *.
    { erewrite dvalue_bytes_to_dvalue_ub_fin_inf; eauto.
      cbn. auto.
      rewrite dvalue_to_dvalue_bytes_fin_to_inf_dvalue.
      apply dvalue_bytes_refine_fin_to_inf_dvalue_bytes.
    }

    { erewrite dvalue_bytes_to_dvalue_err_fin_inf; cbn; eauto.
      rewrite dvalue_to_dvalue_bytes_fin_to_inf_dvalue.
      apply dvalue_bytes_refine_fin_to_inf_dvalue_bytes.
    }
  Qed.

  (* TODO: Move this *)
  Lemma get_conv_case_illegal_fin_inf:
    forall conv t_from dv t_to msg,
      get_conv_case conv t_from dv t_to = Conv_Illegal msg ->
      IS1.LLVM.MEM.CP.CONC.get_conv_case conv t_from (fin_to_inf_dvalue dv) t_to = DV1.Conv_Illegal msg.
  Proof.
    intros conv t_from dv t_to msg CONV.
    destruct conv;
      try solve
        [ cbn in *;
          try inv CONV; try reflexivity;
          repeat break_match_hyp_inv;
          auto;
          rewrite_fin_to_inf_dvalue;
          auto;
          try rewrite Heqb; auto
        ].
    - apply get_conv_case_bitcast_illegal_fin_inf; auto.
  Qed.
End ConversionsRefine.
