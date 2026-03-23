From Stdlib Require Import
  Lia
  ZArith
  Program.Equality
  List.

From ExtLib Require Import
  Structures.Monads
  Structures.Functor.

From Vellvm Require Import
  TopLevelRefinements
  Handlers.MemoryModules.FiniteAddresses
  Handlers.MemoryModules.InfiniteAddresses.

From Vellvm.Semantics Require Import
  MemoryAddress
  VellvmIntegers
  DynamicValues
  InterpretationStack
  TopLevel
  LLVMEvents
  Memory.Sizeof.

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
  PointerOps.

From ITree Require Import
  ITree
  Basics.HeterogeneousRelations
  Eq.Rutt
  Eq.RuttFacts
  Eq.Eqit.

Import DynamicTypes.

Module Type GEPRefine
  (IS1 : InterpreterStack)
  (IS2 : InterpreterStack)
  (LLVM1 : LLVMTopLevel IS1)
  (LLVM2 : LLVMTopLevel IS2)
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
               EC SIZEOF_REF ER).

  Import DVC.
  Import IS2.LP.DV.
  Import IS2.LLVM.D.
  Import EC.
  Import ER.
  Import LLVM2.
  Import VAL_REF.
  Import SIZEOF_REF.
  Import ITOP_REF.

  Lemma handle_gep_h_fin_inf :
    forall  idxs_fin idxs_inf t base res,
      GEP.handle_gep_h t base idxs_fin = inr res ->
      map fin_to_inf_dvalue idxs_fin = idxs_inf ->
      IS1.LLVM.MEM.MP.GEP.handle_gep_h t base idxs_inf = inr res.
  Proof.
    induction idxs_fin;
      intros idxs_inf t base res GEP IDXS.
    - cbn in *; subst; cbn in *; auto.
    - cbn in *.
      (* Split based on index type *)
      break_match_hyp_inv; break_match_hyp_inv;
        try solve [ cbn;
                    rewrite H1;
                    rewrite_fin_to_inf_dvalue;
                    eapply IHidxs_fin in H1; eauto;
                    rewrite sizeof_dtyp_fin_inf;
                    rewrite H1;
                    auto
                  | cbn;
                    rewrite H1;
                    rewrite_fin_to_inf_dvalue;
                    rewrite sizeof_dtyp_fin_inf;
                    eapply IHidxs_fin in H1; eauto;
                    rewrite H1;
                    auto
          ].

      { (* ix *)
        cbn; rewrite_fin_to_inf_dvalue.
        repeat break_match_hyp_inv;
          try
            (try rewrite H0;
             try rewrite H1;
             try erewrite IHidxs_fin; eauto;
             try setoid_rewrite sizeof_dtyp_fin_inf;
             try setoid_rewrite padding_fin_inf;
             auto).

        - cbn.
          replace
            (fun (acc : N) (t : dtyp) => pad_to_align (IS1.LP.SZ.dtyp_alignment t) acc + IS1.LP.SZ.sizeof_dtyp t)%N with
              (fun (acc : N) (t : dtyp) => pad_to_align (IS2.LP.SZ.dtyp_alignment t) acc + IS2.LP.SZ.sizeof_dtyp t)%N; eauto.

          apply FunctionalExtensionality.functional_extensionality.
          intros.
          apply FunctionalExtensionality.functional_extensionality.
          intros.
          rewrite sizeof_dtyp_fin_inf.
          rewrite dtyp_alignment_fin_inf.
          auto.
        - replace
            (fun (acc : N) (t : dtyp) => acc + IS1.LP.SZ.sizeof_dtyp t) with
            (fun (acc : N) (t : dtyp) => acc + IS2.LP.SZ.sizeof_dtyp t); eauto.

          apply FunctionalExtensionality.functional_extensionality.
          intros.
          apply FunctionalExtensionality.functional_extensionality.
          intros.
          rewrite sizeof_dtyp_fin_inf.
          auto.
      }

      { (* Arrays iptr *)
        cbn in *; rewrite_fin_to_inf_dvalue.
        rewrite H1.
        erewrite IHidxs_fin; eauto.
        rewrite sizeof_dtyp_fin_inf; eauto.
        unfold intptr_fin_inf; break_match_goal; clear Heqs.
        rewrite <- (IS1.LP.IP.from_Z_injective _ _ _ e (IS1.LP.IP.to_Z_from_Z x0)).
        auto.
      }

      { (* Vectors iptr *)
        cbn in *; rewrite_fin_to_inf_dvalue.
        rewrite H1.
        erewrite IHidxs_fin; eauto.
        rewrite sizeof_dtyp_fin_inf; eauto.
        unfold intptr_fin_inf; break_match_goal; clear Heqs.
        rewrite <- (IS1.LP.IP.from_Z_injective _ _ _ e (IS1.LP.IP.to_Z_from_Z x0)).
        auto.
      }
  Qed.

  Lemma handle_gep_addr_fin_inf :
    forall t base_addr_fin base_addr_inf idxs_fin idxs_inf res_addr_fin res_addr_inf,
      GEP.handle_gep_addr t base_addr_fin idxs_fin = inr (NoOom res_addr_fin) ->
      AC2.addr_convert base_addr_fin = NoOom base_addr_inf ->
      AC2.addr_convert res_addr_fin = NoOom res_addr_inf ->
      map fin_to_inf_dvalue idxs_fin = idxs_inf ->
      IS1.LLVM.MEM.MP.GEP.handle_gep_addr t base_addr_inf idxs_inf = inr (NoOom res_addr_inf).
  Proof.
    intros t base_addr_fin base_addr_inf
      idxs_fin idxs_inf res_addr_fin res_addr_inf
      GEP CONV_BASE CONV_RES IDXS.

    destruct idxs_fin.
    - cbn in *; subst; inv GEP.
    - cbn in *; subst; cbn.
      break_inner_match_hyp; inv GEP;
        repeat break_match_hyp_inv;
        rewrite_fin_to_inf_dvalue;
        rewrite sizeof_dtyp_fin_inf;
        erewrite AC2.addr_convert_ptoi in Heqs; eauto;
        eapply handle_gep_h_fin_inf in Heqs; eauto;
        try rewrite Heqs; eauto;
        try erewrite addr_convert_int_to_ptr; eauto.

        unfold intptr_fin_inf; break_inner_match_goal; clear Heqs0.
        rewrite <- (IS1.LP.IP.from_Z_injective _ _ _ e (IS1.LP.IP.to_Z_from_Z x0)).

        setoid_rewrite Heqs.
        erewrite addr_convert_int_to_ptr; eauto.
  Qed.

  Lemma handle_gep_h_err_fin_inf :
    forall  idxs_fin idxs_inf t base msg,
      GEP.handle_gep_h t base idxs_fin = inl msg ->
      map fin_to_inf_dvalue idxs_fin = idxs_inf ->
      IS1.LLVM.MEM.MP.GEP.handle_gep_h t base idxs_inf = inl msg.
  Proof.
    induction idxs_fin;
      intros idxs_inf t base msg GEP IDXS.
    - cbn in *; subst; cbn in *; auto.
    - cbn in *.
      (* Split based on index type *)
      break_match_hyp_inv;
        cbn;
        rewrite_fin_to_inf_dvalue;
        auto.

      all: rewrite H0.

      all:
        try solve [break_match_hyp_inv; auto;
                   erewrite IHidxs_fin; eauto;
                   repeat rewrite sizeof_dtyp_fin_inf;
                   repeat rewrite dtyp_alignment_fin_inf;
                   repeat rewrite padded_fin_inf;
                   eauto
          ].

      + break_match_hyp_inv; auto.
        try solve [erewrite IHidxs_fin; eauto;
                   repeat setoid_rewrite sizeof_dtyp_fin_inf;
                   repeat setoid_rewrite dtyp_alignment_fin_inf;
                   repeat setoid_rewrite padding_fin_inf; eauto
                  | break_match_hyp_inv; auto;
                    erewrite IHidxs_fin; eauto;
                    replace (fun (acc : Z) (t : dtyp) => (pad_to_align (IS1.LP.SZ.dtyp_alignment t) acc + IS1.LP.SZ.sizeof_dtyp t))%Z with
                      (fun (acc : Z) (t : dtyp) => (pad_to_align (IS2.LP.SZ.dtyp_alignment t) acc + IS2.LP.SZ.sizeof_dtyp t)%Z); eauto;
                    apply FunctionalExtensionality.functional_extensionality;
                    intros;
                    apply FunctionalExtensionality.functional_extensionality;
                    intros;
                    repeat setoid_rewrite sizeof_dtyp_fin_inf;
                    repeat setoid_rewrite padding_fin_inf;
                    auto

            ].

        repeat break_match_hyp_inv;
          try rewrite H1;
          try rewrite H0;
          repeat setoid_rewrite sizeof_dtyp_fin_inf;
          repeat setoid_rewrite dtyp_alignment_fin_inf;
          repeat setoid_rewrite padding_fin_inf;
          eauto.

        replace
          (fun (acc : N) (t : dtyp) =>
             pad_to_align (IS1.LP.SZ.dtyp_alignment t) acc + IS1.LP.SZ.sizeof_dtyp t) with
          (fun (acc : N) (t : dtyp) =>
             pad_to_align (IS2.LP.SZ.dtyp_alignment t) acc + IS2.LP.SZ.sizeof_dtyp t); eauto;
          apply FunctionalExtensionality.functional_extensionality;
          intros;
          apply FunctionalExtensionality.functional_extensionality;
          intros;
          repeat setoid_rewrite sizeof_dtyp_fin_inf;
          repeat setoid_rewrite dtyp_alignment_fin_inf;
          repeat setoid_rewrite padding_fin_inf;
          auto.

        replace
          (fun (acc : N) (t : dtyp) =>
             acc + IS1.LP.SZ.sizeof_dtyp t) with
          (fun (acc : N) (t : dtyp) =>
             acc + IS2.LP.SZ.sizeof_dtyp t); eauto;
          apply FunctionalExtensionality.functional_extensionality;
          intros;
          apply FunctionalExtensionality.functional_extensionality;
          intros;
          repeat setoid_rewrite sizeof_dtyp_fin_inf;
          repeat setoid_rewrite dtyp_alignment_fin_inf;
          repeat setoid_rewrite padding_fin_inf;
          auto.

      + break_match_hyp_inv; eauto;
          repeat setoid_rewrite sizeof_dtyp_fin_inf;
          repeat setoid_rewrite dtyp_alignment_fin_inf;
          repeat setoid_rewrite padding_fin_inf;
          rewrite H1;
          erewrite IHidxs_fin;
          eauto.

        unfold intptr_fin_inf; break_inner_match_goal; clear Heqs.
        rewrite <- (IS1.LP.IP.from_Z_injective _ _ _ e (IS1.LP.IP.to_Z_from_Z x0)).
        eauto.

        unfold intptr_fin_inf; break_inner_match_goal; clear Heqs.
        rewrite <- (IS1.LP.IP.from_Z_injective _ _ _ e (IS1.LP.IP.to_Z_from_Z x0)).
        eauto.
  Qed.

  Lemma handle_gep_addr_err_fin_inf :
    forall t base_addr_fin base_addr_inf idxs_fin idxs_inf msg,
      GEP.handle_gep_addr t base_addr_fin idxs_fin = inl msg ->
      map fin_to_inf_dvalue idxs_fin = idxs_inf ->
      AC2.addr_convert base_addr_fin = NoOom base_addr_inf ->
      IS1.LLVM.MEM.MP.GEP.handle_gep_addr t base_addr_inf idxs_inf = inl msg.
  Proof.
    intros t base_addr_fin base_addr_inf
      idxs_fin idxs_inf
      msg GEP IDXS BASE_ADDR.

    destruct idxs_fin; cbn in *; subst; inv GEP; auto.
    destruct d; rewrite_fin_to_inf_dvalue; cbn in *; inv H0; auto.
    { repeat break_match_goal; try solve [try inv H0; try inv H1; auto];
        break_match_hyp_inv;
        erewrite handle_gep_h_err_fin_inf in Heqs;
          erewrite AC2.addr_convert_ptoi in Heqs0; eauto;
          try rewrite sizeof_dtyp_fin_inf; eauto;
          inv Heqs; auto.
    }

    { repeat break_match_goal; try solve [try inv H0; try inv H1; auto];
        break_match_hyp_inv;
        erewrite handle_gep_h_err_fin_inf in Heqs;
          erewrite AC2.addr_convert_ptoi in Heqs0; eauto;
          try rewrite sizeof_dtyp_fin_inf; eauto;
          inv Heqs; auto.

      unfold intptr_fin_inf; break_inner_match_goal; clear Heqs1.
      rewrite <- (IS1.LP.IP.from_Z_injective _ _ _ e (IS1.LP.IP.to_Z_from_Z x0)).
      eauto.

      unfold intptr_fin_inf; break_inner_match_goal; clear Heqs.
      rewrite <- (IS1.LP.IP.from_Z_injective _ _ _ e (IS1.LP.IP.to_Z_from_Z x0)).
      eauto.
    }
  Qed.

  (* TODO: Move this *)
  Lemma handle_gep_err_fin_inf :
    forall t base_addr_fin base_addr_inf idxs_fin idxs_inf msg,
      GEP.handle_gep t base_addr_fin idxs_fin = inl msg ->
      map fin_to_inf_dvalue idxs_fin = idxs_inf ->
      dvalue_refine_strict base_addr_inf base_addr_fin ->
      IS1.LLVM.MEM.MP.GEP.handle_gep t base_addr_inf idxs_inf = inl msg.
  Proof.
    intros t base_addr_fin base_addr_inf
      idxs_fin idxs_inf
      msg GEP IDXS BASE_ADDR.

    unfold IS1.LLVM.MEM.MP.GEP.handle_gep, GEP.handle_gep in *.
    break_match_hyp_inv; dvalue_refine_strict_inv BASE_ADDR; auto.
    break_match_hyp_inv.
    eapply handle_gep_addr_err_fin_inf in Heqs; eauto.
    rewrite Heqs; cbn; auto.
    eapply addr_convert_safe_reverse; eauto.
  Qed.

  Lemma handle_gep_fin_inf :
    forall t base_addr_fin base_addr_inf idxs_fin idxs_inf res_addr_fin res_addr_inf,
      GEP.handle_gep t base_addr_fin idxs_fin = inr (NoOom res_addr_fin) ->
      dvalue_refine_strict base_addr_inf base_addr_fin ->
      dvalue_refine_strict res_addr_inf res_addr_fin ->
      map fin_to_inf_dvalue idxs_fin = idxs_inf ->
      IS1.LLVM.MEM.MP.GEP.handle_gep t base_addr_inf idxs_inf = inr (NoOom res_addr_inf).
  Proof.
    intros t base_addr_fin base_addr_inf idxs_fin idxs_inf res_addr_fin res_addr_inf H H0 H1 H2.

    unfold IS1.LLVM.MEM.MP.GEP.handle_gep, GEP.handle_gep in *.
    repeat break_match_hyp_inv.
    dvalue_refine_strict_inv H0; auto.
    dvalue_refine_strict_inv H1; auto.
    eapply handle_gep_addr_fin_inf in Heqs; eauto.
    rewrite Heqs; cbn; auto.
    eapply addr_convert_safe_reverse; eauto.
    eapply addr_convert_safe_reverse; eauto.
  Qed.
End GEPRefine.
