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

Module Type IntCmpsRefine
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

  Lemma eval_int_icmp_fin_inf :
    forall {Int} {VMInt : VellvmIntegers.VMemInt Int} ss icmp a b res_fin,
      @eval_int_icmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) Int VMInt ss icmp a b = ret res_fin  ->
      @DV1.eval_int_icmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) Int VMInt ss icmp a b = ret (fin_to_inf_dvalue res_fin).
  Proof.
    intros Int VMInt ss icmp a b res_fin FIN.
    unfold eval_int_icmp, DV1.eval_int_icmp.
    unfold eval_int_icmp in FIN.
    destruct ss.
    - destruct (true && negb (msamesign a b))%bool.
      + destruct icmp;
          cbn in *;
          repeat break_match_hyp_inv;
          cbn;
          rewrite_fin_to_inf_dvalue; auto;
         try inversion FIN;
          rewrite_fin_to_inf_dvalue; reflexivity.
      + try solve
          [ cbn in *;
            break_match_hyp_inv;
            rewrite_fin_to_inf_dvalue;
            eauto
          | cbn in *;
            repeat break_match_hyp_inv; inv Heqs;
            cbn;
            break_match_goal;
            rewrite_fin_to_inf_dvalue; auto
          ].
    - destruct icmp;
      try solve
        [ cbn in *;
          break_match_hyp_inv;
          rewrite_fin_to_inf_dvalue;
          eauto
        | cbn in *;
          repeat break_match_hyp_inv; inv Heqs;
          cbn;
          break_match_goal;
          rewrite_fin_to_inf_dvalue; auto
        ].
  Qed.

  (* TODO: Move this *)
  Lemma eval_int_icmp_iptr_fin_inf :
    forall v1_fin v2_fin v1_inf v2_inf ss icmp res_fin res_inf,
      @eval_int_icmp err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        IP.intptr
        VMemInt_intptr'
        ss icmp v1_fin v2_fin = success_unERR_UB_OOM res_fin ->
      IS1.LP.IP.from_Z (IP.to_Z v1_fin) = NoOom v1_inf ->
      IS1.LP.IP.from_Z (IP.to_Z v2_fin) = NoOom v2_inf ->
      DVCrev.dvalue_convert_strict res_fin = NoOom res_inf ->
      @DV1.eval_int_icmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        IS1.LP.IP.intptr
        DV1.VMemInt_intptr'
        ss icmp v1_inf v2_inf = success_unERR_UB_OOM res_inf.
  Proof.
    intros v1_fin v2_fin v1_inf v2_inf ss icmp res_fin res_inf EVAL LIFT1 LIFT2 CONV.

    assert (IP.to_Z v1_fin = IS1.LP.IP.to_Z v1_inf) as V1.
    { erewrite IS1.LP.IP.from_Z_to_Z; eauto. }

    assert (IP.to_Z v2_fin = IS1.LP.IP.to_Z v2_inf) as V2.
    { erewrite IS1.LP.IP.from_Z_to_Z; eauto. }

    destruct ss.
    - destruct icmp;
      try
        solve
        [ cbn in *;
          erewrite <- VMEM_REF.mcmpu_refine; eauto;
          break_match_hyp_inv;
          setoid_rewrite Heqb;
          cbn in CONV; inv CONV; auto
        | cbn in *;
          setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL;
          setoid_rewrite dtyp_eqb_refl in EVAL;
          inv EVAL
        ].

      all: cbn in *;
        erewrite <- VMEM_REF.msamesign_refine; eauto;
        unfold VMemInt_intptr' in *;
        break_match_goal; rename Heqb into Heqb';
        [ inv EVAL;
           cbn in *;
           inv CONV;
          reflexivity
        |
          cbn in *;
          erewrite <- VMEM_REF.mcmpu_refine; eauto;
          break_match_hyp_inv;
          try setoid_rewrite Heqb;
          cbn in CONV; inv CONV; auto
        ].
    - destruct icmp;
      try
        solve
        [ cbn in *;
          erewrite <- VMEM_REF.mcmpu_refine; eauto;
          break_match_hyp_inv;
          setoid_rewrite Heqb;
          cbn in CONV; inv CONV; auto
        | cbn in *;
          setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL;
          setoid_rewrite dtyp_eqb_refl in EVAL;
          inv EVAL
        ].
  Qed.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_icmp_fin_inf :
    forall dv1_fin dv2_fin res_fin samesign icmp dv1_inf dv2_inf,
      @eval_icmp err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        samesign icmp dv1_fin dv2_fin = ret res_fin ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @IS1.MEM.CP.CONC.eval_icmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        samesign icmp dv1_inf dv2_inf = ret (fin_to_inf_dvalue res_fin).
  Proof.
    intros dv1_fin dv2_fin res_fin samesign icmp dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    Opaque DV1.eval_int_icmp
      eval_int_icmp.
    unfold eval_icmp in EVAL.
    (* Nasty case analysis... *)
    break_match_hyp_inv;
      try solve
        [ (* Simple integer cases *)
          break_match_hyp_inv;
          repeat rewrite_fin_to_inf_dvalue;
          cbn;
          auto;
          eapply eval_int_icmp_fin_inf in H1;
          auto
        ].

    { (* dv1: addr *)
      break_match_hyp_inv.
      repeat rewrite_fin_to_inf_dvalue.
      cbn.
      eapply eval_int_icmp_fin_inf in H1.
      repeat rewrite ptr_to_int_fin_to_inf_addr.
      auto.
    }

    { (* dv1: ix *)
      break_match_hyp_inv.
      - break_match_hyp_inv; try contradiction; cbn in *; subst.
        repeat rewrite_fin_to_inf_dvalue.
        cbn.
        unfold intptr_fin_inf.
        eapply eval_int_icmp_fin_inf in H0; eauto.
        unfold IS1.MEM.CP.CONC.eval_icmp.
        break_match_goal; try contradiction.
        dependent destruction e; cbn; auto.
      - repeat rewrite_fin_to_inf_dvalue.
        cbn.
        unfold intptr_fin_inf; auto.
    }

    { (* dv1: iptr *)
      break_match_hyp_inv.
      repeat rewrite_fin_to_inf_dvalue.
      cbn.
      unfold intptr_fin_inf.
      do 2 break_match_goal.
      clear Heqs Heqs0.
      eapply eval_int_icmp_iptr_fin_inf in H1; eauto.
      eapply dvalue_convert_strict_fin_inf_succeeds_fin_to_inf_dvalue'.
    }
  Qed.

  Lemma eval_int_icmp_ub_fin_inf :
    forall {Int} {VMInt : VellvmIntegers.VMemInt Int} samesign icmp a b ub_msg,
      @eval_int_icmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) Int VMInt samesign icmp a b = UB_unERR_UB_OOM ub_msg  ->
      @DV1.eval_int_icmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) Int VMInt samesign icmp a b = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros Int VMInt samesign icmp a b ub_msg FIN.
    Transparent eval_int_icmp DV1.eval_int_icmp.
    unfold eval_int_icmp, DV1.eval_int_icmp.
    destruct icmp;
      try solve
        [ cbn in *;
          break_match_hyp_inv;
          rewrite_fin_to_inf_dvalue;
          eauto
        | cbn in *;
          repeat break_match_hyp_inv; inv Heqs;
          cbn;
          break_match_goal;
          rewrite_fin_to_inf_dvalue; auto
        ].
  Qed.

  (* TODO: Move this *)
  Lemma eval_int_icmp_iptr_ub_fin_inf :
    forall v1_fin v2_fin v1_inf v2_inf samesign icmp ub_msg,
      @eval_int_icmp err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        IP.intptr
        VMemInt_intptr'
        samesign icmp v1_fin v2_fin = UB_unERR_UB_OOM ub_msg ->
      IS1.LP.IP.from_Z (IP.to_Z v1_fin) = NoOom v1_inf ->
      IS1.LP.IP.from_Z (IP.to_Z v2_fin) = NoOom v2_inf ->
      @DV1.eval_int_icmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        IS1.LP.IP.intptr
        DV1.VMemInt_intptr'
        samesign icmp v1_inf v2_inf = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros v1_fin v2_fin v1_inf v2_inf samesign icmp ub_msg EVAL LIFT1 LIFT2.

    assert (IP.to_Z v1_fin = IS1.LP.IP.to_Z v1_inf) as V1.
    { erewrite IS1.LP.IP.from_Z_to_Z; eauto. }

    assert (IP.to_Z v2_fin = IS1.LP.IP.to_Z v2_inf) as V2.
    { erewrite IS1.LP.IP.from_Z_to_Z; eauto. }

    destruct icmp;
      try
        solve
        [ cbn in *;
          erewrite <- VMEM_REF.mcmpu_refine; eauto;
          break_match_hyp_inv;
          setoid_rewrite Heqb;
          cbn in CONV; inv CONV; auto
        | cbn in *;
          setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL;
          setoid_rewrite dtyp_eqb_refl in EVAL;
          inv EVAL
        ].
  Qed.

  (* TODO: Move this *)
  Lemma eval_int_icmp_iptr_err_fin_inf :
    forall v1_fin v2_fin v1_inf v2_inf samesign icmp err_msg,
      @eval_int_icmp err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        IP.intptr
        VMemInt_intptr'
        samesign icmp v1_fin v2_fin = ERR_unERR_UB_OOM err_msg ->
      IS1.LP.IP.from_Z (IP.to_Z v1_fin) = NoOom v1_inf ->
      IS1.LP.IP.from_Z (IP.to_Z v2_fin) = NoOom v2_inf ->
      @DV1.eval_int_icmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        IS1.LP.IP.intptr
        DV1.VMemInt_intptr'
        samesign icmp v1_inf v2_inf = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros v1_fin v2_fin v1_inf v2_inf samesign icmp err_msg EVAL LIFT1 LIFT2.

    assert (IP.to_Z v1_fin = IS1.LP.IP.to_Z v1_inf) as V1.
    { erewrite IS1.LP.IP.from_Z_to_Z; eauto. }

    assert (IP.to_Z v2_fin = IS1.LP.IP.to_Z v2_inf) as V2.
    { erewrite IS1.LP.IP.from_Z_to_Z; eauto. }

    destruct icmp;
      try
        solve
        [ cbn in *;
          erewrite <- VMEM_REF.mcmpu_refine; eauto;
          break_match_hyp_inv;
          setoid_rewrite Heqb;
          cbn in CONV; inv CONV; auto
        | cbn in *;
          setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL;
          setoid_rewrite dtyp_eqb_refl in EVAL;
          setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp;
          setoid_rewrite dtyp_eqb_refl;
          inv EVAL;
          auto
        ].
  Qed.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_icmp_ub_fin_inf :
    forall dv1_fin dv2_fin ub_msg samesign icmp dv1_inf dv2_inf,
      @eval_icmp err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        samesign icmp dv1_fin dv2_fin = UB_unERR_UB_OOM ub_msg ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @IS1.MEM.CP.CONC.eval_icmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        samesign icmp dv1_inf dv2_inf = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros dv1_fin dv2_fin ub_msg samesign icmp dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    Opaque DV1.eval_int_icmp
      eval_int_icmp.
    unfold eval_icmp in EVAL.
    (* Nasty case analysis... *)
    break_match_hyp_inv;
      try solve
        [ (* Simple integer cases *)
          break_match_hyp_inv;
          repeat rewrite_fin_to_inf_dvalue;
          cbn;
          auto;
          eapply eval_int_icmp_ub_fin_inf in H1;
          auto
        ].

    { (* dv1: addr *)
      break_match_hyp_inv.
      repeat rewrite_fin_to_inf_dvalue.
      cbn.
      eapply eval_int_icmp_ub_fin_inf in H1.
      repeat rewrite ptr_to_int_fin_to_inf_addr.
      auto.
    }

    { (* dv1: ix *)
      unfold intptr_fin_inf.
      repeat break_match_hyp_inv; try contradiction; cbn in *; subst.
      repeat rewrite_fin_to_inf_dvalue; cbn.
      unfold IS1.MEM.CP.CONC.eval_icmp.
      break_match_goal; try contradiction.
      dependent destruction e; cbn.
      eapply eval_int_icmp_ub_fin_inf; eauto.
    }

    { (* dv1: iptr *)
      break_match_hyp_inv.
      repeat rewrite_fin_to_inf_dvalue.
      cbn.
      unfold intptr_fin_inf.
      do 2 break_match_goal.
      clear Heqs Heqs0.
      eapply eval_int_icmp_iptr_ub_fin_inf in H1; eauto.
    }
  Qed.

  Lemma eval_int_icmp_err_fin_inf :
    forall {Int} {VMInt : VellvmIntegers.VMemInt Int} samesign icmp a b err_msg,
      @eval_int_icmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) Int VMInt samesign icmp a b = ERR_unERR_UB_OOM err_msg  ->
      @DV1.eval_int_icmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) Int VMInt samesign icmp a b = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros Int VMInt samesign icmp a b err_msg FIN.
    Transparent eval_int_icmp DV1.eval_int_icmp.
    unfold eval_int_icmp, DV1.eval_int_icmp.
    destruct icmp;
      try solve
        [ cbn in *;
          break_match_hyp_inv;
          rewrite_fin_to_inf_dvalue;
          eauto
        | cbn in *;
          repeat break_match_hyp_inv; inv Heqs;
          cbn;
          break_match_goal;
          rewrite_fin_to_inf_dvalue;
          auto
        | cbn in *; repeat break_match_hyp_inv; inv Heqs; cbn; auto
        ].
  Qed.


  (* TODO: Move this / generalize monad? *)
  Lemma eval_icmp_err_fin_inf :
    forall dv1_fin dv2_fin err_msg samesign icmp dv1_inf dv2_inf,
      @eval_icmp err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        samesign icmp dv1_fin dv2_fin = ERR_unERR_UB_OOM err_msg ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @IS1.MEM.CP.CONC.eval_icmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        samesign icmp dv1_inf dv2_inf = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros dv1_fin dv2_fin err_msg samesign icmp dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    Opaque DV1.eval_int_icmp
      eval_int_icmp
      DV1.show_dvalue
      show_dvalue.

    unfold eval_icmp in EVAL.
    (* Nasty case analysis... *)
    break_match_hyp_inv;
      try solve
        [ (* Simple integer cases *)
          break_match_hyp_inv;
          try repeat setoid_rewrite <- show_dvalue_fin_inf;
          repeat rewrite_fin_to_inf_dvalue;
          cbn;
          repeat rewrite show_dvalue_fin_inf;
          repeat rewrite_fin_to_inf_dvalue;
          cbn;
          auto;
          eapply eval_int_icmp_err_fin_inf in H1;
          auto
        ].

    { (* dv1: addr *)
      break_match_hyp_inv; cbn in *;
        try repeat setoid_rewrite <- show_dvalue_fin_inf;
        repeat rewrite_fin_to_inf_dvalue;
        cbn;
        repeat rewrite show_dvalue_fin_inf;
        repeat rewrite_fin_to_inf_dvalue;
        try reflexivity;
        eapply eval_int_icmp_err_fin_inf in H1;
        repeat rewrite ptr_to_int_fin_to_inf_addr;
        auto.
    }

    { (* dv1: ix *)
      break_match_hyp_inv;
        try repeat setoid_rewrite <- show_dvalue_fin_inf;
        repeat rewrite_fin_to_inf_dvalue;
        cbn;
        repeat rewrite show_dvalue_fin_inf;
        repeat rewrite_fin_to_inf_dvalue;
        try reflexivity;
        repeat rewrite_fin_to_inf_dvalue.
      cbn.
      unfold intptr_fin_inf.
      unfold IS1.MEM.CP.CONC.eval_icmp.
      break_match_hyp_inv; cbn in *; try contradiction; try reflexivity.
      eapply eval_int_icmp_err_fin_inf in H0; eauto.
    }

    { (* dv1: iptr *)
      break_match_hyp_inv;
        try repeat setoid_rewrite <- show_dvalue_fin_inf;
        repeat rewrite_fin_to_inf_dvalue;
        cbn;
        repeat rewrite show_dvalue_fin_inf;
        repeat rewrite_fin_to_inf_dvalue;
        try reflexivity;
        repeat rewrite_fin_to_inf_dvalue.
      cbn.
      unfold intptr_fin_inf.
      do 2 break_match_goal.
      clear Heqs Heqs0.
      eapply eval_int_icmp_iptr_err_fin_inf in H1; eauto.
    }
  Qed.

  Lemma orutt_eval_icmp :
    forall E1 E2
      `{OOM1 : OOME -< E1} `{OOM2 : OOME -< E2}
      `{UB1 : UBE -< E1} `{UB2 : UBE -< E2}
      `{ERR1: FailureE -< E1} `{ERR2: FailureE -< E2}
      (pre : prerel E1 E2) (post : postrel E1 E2)
      (UBDISC : forall e1 e2, @subevent UBE E2 UB2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (ERRDISC : forall e1 e2, @subevent FailureE E2 ERR2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (UBINJ : pre void void (@subevent UBE E1 UB1 void (ThrowUB tt)) (@subevent UBE E2 UB2 void (ThrowUB tt)))
      (ERRINJ : pre void void (@subevent FailureE E1 ERR1 void (Throw tt)) (@subevent FailureE E2 ERR2 void (Throw tt)))
      samesign cmp dv1_1 dv2_1 dv1_2 dv2_2,
      dvalue_refine_strict dv1_1 dv1_2 ->
      dvalue_refine_strict dv2_1 dv2_2 ->
      orutt pre post dvalue_refine_strict
        (IS1.MEM.CP.CONC.eval_icmp samesign cmp dv1_1 dv2_1) (eval_icmp samesign cmp dv1_2 dv2_2)
        (OOM:=OOME).
  Proof.
    intros.
    rewrite eval_icmp_err_ub_oom_to_itree,
      TLR1.eval_icmp_err_ub_oom_to_itree.

    remember (eval_icmp samesign cmp dv1_2 dv2_2) as e.
    destruct_err_ub_oom e; symmetry in Heqe.
    - apply orutt_raiseOOM.
    - erewrite eval_icmp_ub_fin_inf; cbn; eauto;
        try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_raiseUB; cbn; auto.
    - erewrite eval_icmp_err_fin_inf; cbn; eauto;
        try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_raise; cbn; auto.
    - erewrite eval_icmp_fin_inf; cbn; eauto; subst.
      2-3: try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_Ret; cbn; eauto.
      apply fin_to_inf_dvalue_refine_strict.
  Qed.

  #[global] Hint Resolve
    orutt_eval_icmp
    : ORUTT.

End IntCmpsRefine.
