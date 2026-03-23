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
  LLVMEvents
  Memory.DvalueBytes
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
  OOMRuttProps
  VellvmRelations
  NMaps
  ErrUbOomProp
  ErrOomPoison
  Monads
  MapMonadExtra
  Oomable
  Poisonable.

From Vellvm.Semantics.InfiniteToFinite.LangRefine Require Import
  Events
  Sizeof
  Values
  Utils
  PointerOps.

From Vellvm.Semantics.InfiniteToFinite Require Import
  R2Injective.

From ITree Require Import
  ITree
  Basics.HeterogeneousRelations
  Eq.Rutt
  Eq.RuttFacts
  Eq.Eqit.

Import MonadNotation.
Import ListNotations.

Module Type BytesRefine
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
               EC SIZEOF_REF ER).

  Import EC.
  Import DV2.
  Import IS2.LP.
  Import DynamicTypes.
  Import IPS.
  Import VAL_REF.
  Import DVC.
  Import TLR2.
  Import SIZEOF_REF.
  Import ITOP_REF.
  Import IS2.MEM.ByteM.

  Definition dvalue_byte_refine
    (dvb_inf : IS1.MEM.DVALUE_BYTE.dvalue_byte)
    (dvb_fin : dvalue_byte) : Prop
    :=
    match dvb_inf, dvb_fin with
    | (IS1.MEM.DVALUE_BYTE.DVALUE_ExtractByte dv_inf dt_inf ix_inf),
      (DVALUE_ExtractByte dv_fin dt_fin ix_fin)
      =>
        dvalue_refine_strict dv_inf dv_fin /\
          dt_inf = dt_fin /\
          ix_inf = ix_fin
    end.

  Definition inf_to_fin_dvalue_byte
    (dvb_inf : IS1.MEM.DVALUE_BYTE.dvalue_byte) : OOM dvalue_byte
    :=
    match dvb_inf with
    | (IS1.MEM.DVALUE_BYTE.DVALUE_ExtractByte dv_inf dt ix)
      =>
        dv_fin <- dvalue_convert_strict dv_inf;;
        ret (DVALUE_ExtractByte dv_fin dt ix)
    end.

  Definition fin_to_inf_dvalue_byte
    (dvb_fin : dvalue_byte) : IS1.MEM.DVALUE_BYTE.dvalue_byte
    :=
    match dvb_fin with
    | DVALUE_ExtractByte dv_fin dt ix
      =>
        let dv_inf := fin_to_inf_dvalue dv_fin in
        IS1.MEM.DVALUE_BYTE.DVALUE_ExtractByte dv_inf dt ix
    end.

  Definition dvalue_bytes_refine
    (dvbs_inf : list IS1.MEM.DVALUE_BYTE.dvalue_byte)
    (dvbs_fin : list dvalue_byte) : Prop
    := Forall2 dvalue_byte_refine dvbs_inf dvbs_fin.

  Definition fin_to_inf_dvalue_bytes := map fin_to_inf_dvalue_byte.

  Lemma dvalue_byte_refine_fin_to_inf_dvalue_byte :
    forall a,
      dvalue_byte_refine (fin_to_inf_dvalue_byte a) a.
  Proof.
    intros a.
    red.
    repeat break_match_goal; subst.
    cbn in Heqd.
    inv Heqd.
    split; auto.
    apply fin_to_inf_dvalue_refine_strict.
  Qed.

  Lemma dvalue_bytes_refine_fin_to_inf_dvalue_bytes :
    forall dvs,
      dvalue_bytes_refine (fin_to_inf_dvalue_bytes dvs) dvs.
  Proof.
    induction dvs; cbn; auto.
    - constructor.
    - constructor; auto.
      apply dvalue_byte_refine_fin_to_inf_dvalue_byte.
  Qed.

  Lemma dvalue_to_dvalue_bytes_fin_inf :
    forall dv_fin dv_inf dt dvbs_fin,
      dvalue_refine_strict dv_inf dv_fin ->
      DVALUE_BYTE.dvalue_to_dvalue_bytes dv_fin dt = dvbs_fin ->
      IS1.MEM.DVALUE_BYTE.dvalue_to_dvalue_bytes dv_inf dt = fin_to_inf_dvalue_bytes dvbs_fin.
  Proof.
    intros dv_fin dv_inf dt dvbs_fin DV_REF DV_DVBS.
    unfold dvalue_to_dvalue_bytes in DV_DVBS.
    unfold IS1.MEM.DVALUE_BYTE.dvalue_to_dvalue_bytes.
    rewrite sizeof_dtyp_fin_inf.
    subst.
    unfold fin_to_inf_dvalue_bytes.
    rewrite List.map_map.
    cbn.
    erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
  Qed.

  Lemma all_extract_bytes_from_uvalue_helper_fin_inf :
    forall uv_bytes_inf uv_bytes_fin uv_inf uv_fin ix sid dt,
      uvalue_refine_strict uv_inf uv_fin ->
      map_monad uvalue_convert_strict uv_bytes_inf = NoOom uv_bytes_fin ->
      IS1.MEM.ByteM.all_extract_bytes_from_uvalue_helper ix sid dt uv_inf uv_bytes_inf =
        fmap fin_to_inf_uvalue (all_extract_bytes_from_uvalue_helper ix sid dt uv_fin uv_bytes_fin).
  Proof.
    induction uv_bytes_inf;
      intros uv_bytes_fin uv_inf uv_fin ix sid dt UV_REF HMAPM.
    - inv HMAPM.
      cbn.
      erewrite <- fin_to_inf_uvalue_refine_strict'; eauto.
    - cbn in HMAPM.
      repeat break_match_hyp_inv.
      cbn.
      erewrite IHuv_bytes_inf; eauto.

      destruct a; cbn in Heqo;
        repeat break_match_hyp_inv; try inv Heqo; auto.

      unfold IS1.LLVM.MEM.CP.CONCBASE.MemHelpers.dtyp_eqb, MemHelpers.dtyp_eqb.
      repeat rewrite Util.eq_dec_eq; cbn.
      repeat rewrite N.eqb_refl; cbn.
      repeat (break_inner_match; subst; cbn; auto).
      + destruct (RelDec.rel_dec a uv_inf) eqn:UV_INF; inv Heqo2.
        assert (a = uv_inf) as AUV_INF.
        { eapply RelDec.rel_dec_correct; eauto. }
        subst.
        rewrite UV_REF in Heqo1. inv Heqo1.
        rewrite Util.eq_dec_eq in Heqo6.
        inv Heqo6.
      + destruct (RelDec.rel_dec u0 uv_fin) eqn:UV_FIN; inv Heqo3.
        assert (u0 = uv_fin) as AUV_FIN.
        { eapply RelDec.rel_dec_correct; eauto. }
        subst.

        pose proof uvalue_refine_strict_R2_injective _ _ _ _ UV_REF Heqo1 as (_&?).
        forward H; auto; subst.
        rewrite UV_REF in Heqo1. inv Heqo1.
        rewrite Util.eq_dec_eq in Heqo2; inv Heqo2.
  Qed.

  Lemma all_extract_bytes_from_uvalue_fin_inf :
    forall uv_bytes_inf uv_bytes_fin dt,
      map_monad uvalue_convert_strict uv_bytes_inf = NoOom uv_bytes_fin ->
      IS1.MEM.ByteM.all_extract_bytes_from_uvalue dt uv_bytes_inf =
        fmap fin_to_inf_uvalue (all_extract_bytes_from_uvalue dt uv_bytes_fin).
  Proof.
    intros uv_bytes_inf uv_bytes_fin dt HMAPM.
    unfold IS1.MEM.ByteM.all_extract_bytes_from_uvalue,
      all_extract_bytes_from_uvalue.

    destruct uv_bytes_inf.
    - cbn in HMAPM; inv HMAPM.
      cbn; auto.
    - rewrite map_monad_unfold in HMAPM.
      cbn in HMAPM.
      repeat break_match_hyp_inv.
      destruct u; cbn in Heqo;
        repeat break_match_hyp_inv; try inv Heqo; auto.

      cbn.
      unfold IS1.LLVM.MEM.CP.CONCBASE.MemHelpers.dtyp_eqb, MemHelpers.dtyp_eqb.
      repeat rewrite Util.eq_dec_eq; cbn.
      repeat rewrite N.eqb_refl; cbn.
      do 3 (break_inner_match; subst; cbn; auto).
      erewrite all_extract_bytes_from_uvalue_helper_fin_inf; eauto.
      reflexivity.
  Qed.

  Lemma extract_field_byte_helper_fin_inf :
    forall {M : Type -> Type} {HM: Monad M} {RE: RAISE_ERROR M}
      (field_dts : list dtyp) (field_idx : N) (byte_idx : N),
      @IS1.LLVM.MEM.DVALUE_BYTE.extract_field_byte_helper M HM RE field_dts field_idx byte_idx =
        @extract_field_byte_helper M HM RE field_dts field_idx byte_idx.
  Proof.
    intros M HM RE field_dts.
    induction field_dts;
      intros field_idx byte_idx;
      cbn; auto.
    rewrite sizeof_dtyp_fin_inf.
    rewrite IHfield_dts.
    reflexivity.
  Qed.

  Lemma extract_field_byte_fin_inf :
    forall {M : Type -> Type} {HM: Monad M} {RE: RAISE_ERROR M}
      (field_dts : list dtyp) (byte_idx : N),
      @IS1.LLVM.MEM.DVALUE_BYTE.extract_field_byte M HM RE field_dts byte_idx =
        @extract_field_byte M HM RE field_dts byte_idx.
  Proof.
    intros M HM RE field_dts byte_idx.
    apply extract_field_byte_helper_fin_inf.
  Qed.

  Lemma dvalue_extract_byte_fin_inf :
    forall dv_fin dv_inf dt idx,
      dvalue_refine_strict dv_inf dv_fin ->
      @dvalue_extract_byte ErrOOMPoison
        (@EitherMonad.Monad_eitherT ERR_MESSAGE (OomableT Poisonable)
           (@Monad_OomableT Poisonable MonadPoisonable))
        (@RAISE_ERROR_MonadExc ErrOOMPoison
           (@EitherMonad.Exception_eitherT ERR_MESSAGE (OomableT Poisonable)
              (@Monad_OomableT Poisonable MonadPoisonable)))
        (@RAISE_POISON_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
           (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
              (@Monad_OomableT Poisonable MonadPoisonable))
           (@RAISE_POISON_E_MT Poisonable OomableT (@MonadT_OomableT Poisonable MonadPoisonable)
              RAISE_POISON_Poisonable))
        (@RAISE_OOMABLE_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
           (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
              (@Monad_OomableT Poisonable MonadPoisonable))
           (@RAISE_OOMABLE_OomableT Poisonable MonadPoisonable)) dv_fin dt idx =
        @IS1.LLVM.MEM.DVALUE_BYTE.dvalue_extract_byte ErrOOMPoison
          (@EitherMonad.Monad_eitherT ERR_MESSAGE (OomableT Poisonable)
             (@Monad_OomableT Poisonable MonadPoisonable))
          (@RAISE_ERROR_MonadExc ErrOOMPoison
             (@EitherMonad.Exception_eitherT ERR_MESSAGE (OomableT Poisonable)
                (@Monad_OomableT Poisonable MonadPoisonable)))
          (@RAISE_POISON_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
             (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
                (@Monad_OomableT Poisonable MonadPoisonable))
             (@RAISE_POISON_E_MT Poisonable OomableT (@MonadT_OomableT Poisonable MonadPoisonable)
                RAISE_POISON_Poisonable))
          (@RAISE_OOMABLE_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
             (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
                (@Monad_OomableT Poisonable MonadPoisonable))
             (@RAISE_OOMABLE_OomableT Poisonable MonadPoisonable)) dv_inf dt idx.
  Proof.
    Opaque dvalue_extract_byte.
    Opaque IS1.LLVM.MEM.DVALUE_BYTE.dvalue_extract_byte.
    induction dv_fin;
      intros dv_inf dt idx REF;
      rewrite IS2.LLVM.MEM.DVALUE_BYTE.dvalue_extract_byte_equation,
      IS1.LLVM.MEM.DVALUE_BYTE.dvalue_extract_byte_equation;
      try solve
        [ dvalue_refine_strict_inv REF;
          unfold extract_byte_Z in *;
          try inv VAL;
          solve
            [ reflexivity
            | erewrite AC1.addr_convert_ptoi; eauto
            | erewrite IP.from_Z_to_Z; eauto
            ]
        ].

      { (* Structs *)
        destruct dt;
        dvalue_refine_strict_inv REF; auto.
        rename fields0 into dts.
        rewrite max_preferred_dtyp_alignment_fin_inf.
        generalize (SZ.max_preferred_dtyp_alignment dts) as struct_padding.
        revert dts idx.
        eapply map_monad_oom_Forall2 in H1.
        revert x H1.
        generalize 0 at 3 6 as offset.
        induction fields; intros; inversion H1; subst.
        - cbn. reflexivity.
        - destruct dts; try reflexivity.
          cbn.
          rewrite sizeof_dtyp_fin_inf.
          rewrite dtyp_alignment_fin_inf.
          break_match; try reflexivity.
          break_match.
          + apply H; cbn; auto.
          + forward IHfields; intros; auto.
            apply H; cbn; auto.
            cbn in IHfields.
            specialize (IHfields (offset + pad_amount (preferred_alignment (SZ.dtyp_alignment d)) offset + SZ.sizeof_dtyp d) l H5 dts (idx - Z.of_N (pad_amount (preferred_alignment (SZ.dtyp_alignment d)) offset) - Z.of_N (SZ.sizeof_dtyp d))%Z struct_padding).
            cbn in *.
            erewrite IHfields; intros; eauto.
      } 

      { (* Packed Structs *)
        destruct dt;
        dvalue_refine_strict_inv REF; auto.
        rename fields0 into dts.
        revert dts idx.
        eapply map_monad_oom_Forall2 in H1.
        revert x H1.
        generalize 0 at 3 6 as offset.
        induction fields; intros; inversion H1; subst.
        - reflexivity.
        - destruct dts; try reflexivity.
          cbn.
          rewrite sizeof_dtyp_fin_inf.
          break_match; try reflexivity.
          break_match.
          + apply H. repeat constructor. apply H4.
          + erewrite IHfields; intros; eauto. 
            apply H; auto.
            right. assumption.
      }

      { (* Arrays *)
        destruct dt;
        dvalue_refine_strict_inv REF; auto.
        revert idx.
        eapply map_monad_oom_Forall2 in H1.
        revert x H1.
        induction elts; intros; inversion H1; subst.
        - reflexivity.
        - cbn.
          rewrite sizeof_dtyp_fin_inf.
          destruct (idx <? Z.of_N (SZ.sizeof_dtyp dt))%Z.
          + apply H. repeat constructor. apply H4.
          + erewrite IHelts; intros; eauto.
            apply H; cbn; auto.
      }

      { (* Vectors *)
        destruct dt;
        dvalue_refine_strict_inv REF; auto.
        revert idx.
        eapply map_monad_oom_Forall2 in H1.
        revert x H1.
        induction elts; intros; inversion H1; subst.
        - reflexivity.
        - cbn.
          rewrite sizeof_dtyp_fin_inf.
          destruct (idx <? Z.of_N (SZ.sizeof_dtyp dt))%Z.
          + apply H. repeat constructor. apply H4.
          + apply IHelts; intros; auto.
            apply H; auto.
            right. assumption.
      }
  Qed.

  Lemma dvalue_byte_value_fin_inf :
    forall dvb_inf dvb_fin,
      dvalue_byte_refine dvb_inf dvb_fin ->
      @dvalue_byte_value ErrOOMPoison
        (@EitherMonad.Monad_eitherT ERR_MESSAGE (OomableT Poisonable)
           (@Monad_OomableT Poisonable MonadPoisonable))
        (@RAISE_ERROR_MonadExc ErrOOMPoison
           (@EitherMonad.Exception_eitherT ERR_MESSAGE (OomableT Poisonable)
              (@Monad_OomableT Poisonable MonadPoisonable)))
        (@RAISE_POISON_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
           (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
              (@Monad_OomableT Poisonable MonadPoisonable))
           (@RAISE_POISON_E_MT Poisonable OomableT (@MonadT_OomableT Poisonable MonadPoisonable)
              RAISE_POISON_Poisonable))
        (@RAISE_OOMABLE_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
           (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
              (@Monad_OomableT Poisonable MonadPoisonable))
           (@RAISE_OOMABLE_OomableT Poisonable MonadPoisonable)) dvb_fin =
      (@IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte_value ErrOOMPoison
         (@EitherMonad.Monad_eitherT ERR_MESSAGE
            (OomableT Poisonable)
            (@Monad_OomableT Poisonable
               MonadPoisonable))
         (@RAISE_ERROR_MonadExc ErrOOMPoison
            (@EitherMonad.Exception_eitherT ERR_MESSAGE
               (OomableT Poisonable)
               (@Monad_OomableT Poisonable
                  MonadPoisonable)))
         (@RAISE_POISON_E_MT
            (OomableT Poisonable)
            (EitherMonad.eitherT ERR_MESSAGE)
            (@EitherMonad.MonadT_eitherT ERR_MESSAGE
               (OomableT Poisonable)
               (@Monad_OomableT Poisonable
                  MonadPoisonable))
            (@RAISE_POISON_E_MT Poisonable
               OomableT
               (@MonadT_OomableT Poisonable
                  MonadPoisonable)
               RAISE_POISON_Poisonable))
         (@RAISE_OOMABLE_E_MT
            (OomableT Poisonable)
            (EitherMonad.eitherT ERR_MESSAGE)
            (@EitherMonad.MonadT_eitherT ERR_MESSAGE
               (OomableT Poisonable)
               (@Monad_OomableT Poisonable
                  MonadPoisonable))
            (@RAISE_OOMABLE_OomableT Poisonable
               MonadPoisonable))) dvb_inf.
  Proof.
    intros dvb_inf dvb_fin REF.
    unfold dvalue_byte_value.
    break_match; subst.
    unfold IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte_value.
    break_match_goal; subst.
    red in REF.
    destruct REF as (?&?&?).
    subst.
    eapply dvalue_extract_byte_fin_inf; eauto.
  Qed.

  Lemma map_monad_dvalue_byte_value_fin_inf :
    forall dvbs_inf dvbs_fin,
      dvalue_bytes_refine dvbs_inf dvbs_fin ->
      map_monad (@dvalue_byte_value ErrOOMPoison
        (@EitherMonad.Monad_eitherT ERR_MESSAGE (OomableT Poisonable)
           (@Monad_OomableT Poisonable MonadPoisonable))
        (@RAISE_ERROR_MonadExc ErrOOMPoison
           (@EitherMonad.Exception_eitherT ERR_MESSAGE (OomableT Poisonable)
              (@Monad_OomableT Poisonable MonadPoisonable)))
        (@RAISE_POISON_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
           (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
              (@Monad_OomableT Poisonable MonadPoisonable))
           (@RAISE_POISON_E_MT Poisonable OomableT (@MonadT_OomableT Poisonable MonadPoisonable)
              RAISE_POISON_Poisonable))
        (@RAISE_OOMABLE_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
           (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
              (@Monad_OomableT Poisonable MonadPoisonable))
           (@RAISE_OOMABLE_OomableT Poisonable MonadPoisonable))) dvbs_fin =
      map_monad (@IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte_value ErrOOMPoison
         (@EitherMonad.Monad_eitherT ERR_MESSAGE
            (OomableT Poisonable)
            (@Monad_OomableT Poisonable
               MonadPoisonable))
         (@RAISE_ERROR_MonadExc ErrOOMPoison
            (@EitherMonad.Exception_eitherT ERR_MESSAGE
               (OomableT Poisonable)
               (@Monad_OomableT Poisonable
                  MonadPoisonable)))
         (@RAISE_POISON_E_MT
            (OomableT Poisonable)
            (EitherMonad.eitherT ERR_MESSAGE)
            (@EitherMonad.MonadT_eitherT ERR_MESSAGE
               (OomableT Poisonable)
               (@Monad_OomableT Poisonable
                  MonadPoisonable))
            (@RAISE_POISON_E_MT Poisonable
               OomableT
               (@MonadT_OomableT Poisonable
                  MonadPoisonable)
               RAISE_POISON_Poisonable))
         (@RAISE_OOMABLE_E_MT
            (OomableT Poisonable)
            (EitherMonad.eitherT ERR_MESSAGE)
            (@EitherMonad.MonadT_eitherT ERR_MESSAGE
               (OomableT Poisonable)
               (@Monad_OomableT Poisonable
                  MonadPoisonable))
            (@RAISE_OOMABLE_OomableT Poisonable
               MonadPoisonable))) dvbs_inf.
  Proof.
    induction dvbs_inf;
      intros dvbs_fin REF.
    + inv REF.
      cbn in *; auto.
    + inv REF.
      rewrite map_monad_unfold.
      cbn.
      repeat erewrite dvalue_byte_value_fin_inf; eauto.
      rewrite IHdvbs_inf; eauto.
  Qed.


  Lemma list_dvalue_bytes_to_dvalue_fin_inf :
    forall (dts : list dtyp) (pad : option N) (offset : N) (dvbs_fin : list dvalue_byte) (dvbs_inf : list IS1.MEM.DVALUE_BYTE.dvalue_byte) (res : ErrOOMPoison (list dvalue))
      (IH : forall u : dtyp,
          In u dts ->
          forall (dvbs_fin : list dvalue_byte) (dvbs_inf : list IS1.MEM.DVALUE_BYTE.dvalue_byte)
            (res : ErrOOMPoison dvalue),
            dvalue_bytes_refine dvbs_inf dvbs_fin ->
            (forall x : dtyp, res <> raise_oomable x) ->
            dvalue_bytes_to_dvalue dvbs_fin u = res ->
            IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue dvbs_inf u = fmap fin_to_inf_dvalue res),
      dvalue_bytes_refine dvbs_inf dvbs_fin ->
      (forall x : dtyp, res <> raise_oomable x) ->
      (fix go (offset : N) (dts : list dtyp) (dbs : list dvalue_byte) {struct dts} :
         ErrOOMPoison (list dvalue) :=
         match dts with
         | [] =>
             (* TODO: should we check that we have the appropriate number of extra padding bytes here? *)
             (* Long term we'll have to include padding bytes in the dvalue *)
             ret []
         | (dt::dts) =>
             let padding :=
               if pad
               then pad_amount (preferred_alignment (SZ.dtyp_alignment dt)) offset
               else 0%N
             in
             let zpadding := Z.of_N padding in
             let sz := SZ.sizeof_dtyp dt in
             (* Skip any padding bytes *)
             let dbs' := drop padding dbs in
             let init_bytes := take sz dbs' in
             let rest_bytes := drop sz dbs' in
             let offset' := (offset + padding)%N in
             f <- dvalue_bytes_to_dvalue init_bytes dt;;
             rest <- go (offset' + sz) dts rest_bytes;;
             ret (f :: rest)
         end) offset dts dvbs_fin = res ->
      (fix go (offset : N) (dts : list dtyp) (dbs : list IS1.MEM.DVALUE_BYTE.dvalue_byte) {struct dts} :=
         match dts with
         | [] =>
             (* TODO: should we check that we have the appropriate number of extra padding bytes here? *)
             (* Long term we'll have to include padding bytes in the dvalue *)
             ret []
         | (dt::dts) =>
             let padding :=
               if pad
               then pad_amount (preferred_alignment (IS1.LP.SZ.dtyp_alignment dt)) offset
               else 0%N
             in
             let zpadding := Z.of_N padding in
             let sz := IS1.LP.SZ.sizeof_dtyp dt in
             (* Skip any padding bytes *)
             let dbs' := drop padding dbs in
             let init_bytes := take sz dbs' in
             let rest_bytes := drop sz dbs' in
             let offset' := offset + padding in
             f <- IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue init_bytes dt;;
             rest <- go (offset' + sz) dts rest_bytes;;
             ret (f :: rest)
         end) offset dts dvbs_inf = fmap (map fin_to_inf_dvalue) res.
  Proof.
    induction dts; intros pad offset dvbs_fin dvbs_inf res IH REF NOOM FIN.
    - inv FIN; reflexivity.
    - Opaque bind.
      cbn in *.
      rewrite sizeof_dtyp_fin_inf.
      rewrite dtyp_alignment_fin_inf.
      erewrite IH; eauto.
      2: {
        apply Forall2_take; eauto.
        apply Forall2_drop; eauto.
      }
      2: {
        intros x CONTRA.
        eapply (NOOM x).
        subst.
        setoid_rewrite CONTRA.
        Transparent bind.
        cbn.
        reflexivity.
      }

      remember (dvalue_bytes_to_dvalue
                  (take (SZ.sizeof_dtyp a)
                     (drop (if pad then pad_amount (preferred_alignment (SZ.dtyp_alignment a)) offset else 0)
                        dvbs_fin)) a) as init.
      destruct_err_oom_poison init;
        try solve [subst; cbn; eauto].

      remember
        ((fix go (offset : N) (dts : list dtyp) (dbs : list dvalue_byte) {struct dts} :
           ErrOOMPoison (list dvalue) :=
            match dts with
            | [] => {| EitherMonad.unEitherT := {| unMkOomableT := Unpoisoned (Unoomed (inr [])) |} |}
            | dt :: dts0 =>
                f0 <-
                  dvalue_bytes_to_dvalue
                    (take (SZ.sizeof_dtyp dt)
                       (drop
                          (if pad
                           then pad_amount (preferred_alignment (SZ.dtyp_alignment dt)) offset
                           else 0) dbs)) dt;;
                rest <-
                  go
                    (offset +
                       (if pad then pad_amount (preferred_alignment (SZ.dtyp_alignment dt)) offset else 0) +
                       SZ.sizeof_dtyp dt) dts0
                    (drop (SZ.sizeof_dtyp dt)
                       (drop
                          (if pad
                           then pad_amount (preferred_alignment (SZ.dtyp_alignment dt)) offset
                           else 0) dbs));;
                {|
                  EitherMonad.unEitherT := {| unMkOomableT := Unpoisoned (Unoomed (inr (f0 :: rest))) |}
                |}
            end)
           (offset + (if pad then pad_amount (preferred_alignment (SZ.dtyp_alignment a)) offset else 0) +
              SZ.sizeof_dtyp a) dts
           (drop (SZ.sizeof_dtyp a)
              (drop (if pad then pad_amount (preferred_alignment (SZ.dtyp_alignment a)) offset else 0)
                 dvbs_fin))) as rest.

      erewrite IHdts with (res:=rest).
      + destruct_err_oom_poison rest;
          try solve [subst; cbn; eauto].
      + eauto.
      + eapply Forall2_drop; eauto.
        eapply Forall2_drop; eauto.
      + intros x CONTRA; subst.
        specialize (NOOM x).
        eapply NOOM.
        rewrite CONTRA.
        Transparent bind.
        cbn.
        reflexivity.
      + subst.
        reflexivity.
  Qed.

  Lemma dvalue_bytes_fin_to_dvalue_fin_inf :
    forall dt dvbs_fin dvbs_inf res,
      dvalue_bytes_refine dvbs_inf dvbs_fin ->
      (forall x, res <> raise_oomable x) ->
      (@dvalue_bytes_to_dvalue ErrOOMPoison
         (@EitherMonad.Monad_eitherT ERR_MESSAGE
            (OomableT Poisonable)
            (@Monad_OomableT Poisonable MonadPoisonable))
         (@RAISE_ERROR_MonadExc ErrOOMPoison
            (@EitherMonad.Exception_eitherT ERR_MESSAGE
               (OomableT Poisonable)
               (@Monad_OomableT Poisonable MonadPoisonable)))
         (@RAISE_POISON_E_MT (OomableT Poisonable)
            (EitherMonad.eitherT ERR_MESSAGE)
            (@EitherMonad.MonadT_eitherT ERR_MESSAGE
               (OomableT Poisonable)
               (@Monad_OomableT Poisonable MonadPoisonable))
            (@RAISE_POISON_E_MT Poisonable OomableT
               (@MonadT_OomableT Poisonable MonadPoisonable)
               RAISE_POISON_Poisonable))
         (@RAISE_OOMABLE_E_MT (OomableT Poisonable)
            (EitherMonad.eitherT ERR_MESSAGE)
            (@EitherMonad.MonadT_eitherT ERR_MESSAGE
               (OomableT Poisonable)
               (@Monad_OomableT Poisonable MonadPoisonable))
            (@RAISE_OOMABLE_OomableT Poisonable MonadPoisonable)) dvbs_fin dt) = res ->
      (@IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue ErrOOMPoison
         (@EitherMonad.Monad_eitherT ERR_MESSAGE
            (OomableT Poisonable)
            (@Monad_OomableT Poisonable
               MonadPoisonable))
         (@RAISE_ERROR_MonadExc ErrOOMPoison
            (@EitherMonad.Exception_eitherT ERR_MESSAGE
               (OomableT Poisonable)
               (@Monad_OomableT Poisonable
                  MonadPoisonable)))
         (@RAISE_POISON_E_MT
            (OomableT Poisonable)
            (EitherMonad.eitherT ERR_MESSAGE)
            (@EitherMonad.MonadT_eitherT ERR_MESSAGE
               (OomableT Poisonable)
               (@Monad_OomableT Poisonable
                  MonadPoisonable))
            (@RAISE_POISON_E_MT Poisonable
               OomableT
               (@MonadT_OomableT Poisonable
                  MonadPoisonable)
               RAISE_POISON_Poisonable))
         (@RAISE_OOMABLE_E_MT
            (OomableT Poisonable)
            (EitherMonad.eitherT ERR_MESSAGE)
            (@EitherMonad.MonadT_eitherT ERR_MESSAGE
               (OomableT Poisonable)
               (@Monad_OomableT Poisonable
                  MonadPoisonable))
            (@RAISE_OOMABLE_OomableT Poisonable
               MonadPoisonable)) dvbs_inf dt) = fmap fin_to_inf_dvalue res.
  Proof.
    induction dt;
      intros dvbs_fin dvbs_inf res REF NOOM FIN;
      try
        solve
        [ rewrite dvalue_bytes_to_dvalue_equation in FIN;
          rewrite IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue_equation;
          subst;
          erewrite map_monad_dvalue_byte_value_fin_inf; eauto;
          remember (map_monad IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte_value dvbs_inf) as res;
          destruct_err_oom_poison res; cbn; auto;
          cbn;
          repeat break_match_goal;
          try inv Heqp0;
          try inv Heqp1;
          try inv Heqp2;
          try inv Heqp3;
          try inv Heqp4;
          try inv Heqp5;
          try inv Heqp6;
          try inv Heqp7;
          try inv Heqp;
          try reflexivity;
          rewrite_fin_to_inf_dvalue; auto
        | rewrite dvalue_bytes_to_dvalue_equation in FIN;
          rewrite IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue_equation;
          subst;
          reflexivity
        ].

    { rewrite dvalue_bytes_to_dvalue_equation in FIN;
        rewrite IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue_equation;
        subst.
      erewrite map_monad_dvalue_byte_value_fin_inf in NOOM; eauto.
      erewrite map_monad_dvalue_byte_value_fin_inf; eauto;
        remember (map_monad IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte_value dvbs_inf) as res.
      destruct_err_oom_poison res; cbn; auto.
      remember (lift_OOMABLE DTYPE_IPTR (IP.from_Z (concat_bytes_Z res0))) as y.
      destruct_err_oom_poison y; cbn; auto;
        unfold lift_OOMABLE in Heqy; break_match_hyp_inv.
      2: {
        cbn in *.
        specialize (NOOM DTYPE_IPTR).
        rewrite Heqo in NOOM.
        contradiction.
      }

      pose proof intptr_convert_succeeds i as (?&?).
      eapply intptr_convert_safe in e.
      pose proof IP.from_Z_injective _ _ _ Heqo e.
      rewrite H.
      rewrite IS1.LP.IP.to_Z_from_Z; cbn.
      rewrite_fin_to_inf_dvalue.
      unfold intptr_fin_inf.
      break_match_goal.
      clear Heqs.
      eapply intptr_convert_safe in e0.
      pose proof IP.from_Z_injective _ _ _ e e0.
      apply IS1.LP.IP.to_Z_inj in H0; subst; auto.
    }

    { rewrite dvalue_bytes_to_dvalue_equation in FIN;
        rewrite IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue_equation;
        subst.
      erewrite map_monad_dvalue_byte_value_fin_inf in NOOM; eauto.
      erewrite map_monad_dvalue_byte_value_fin_inf; eauto;
        remember (map_monad IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte_value dvbs_inf) as res.
      destruct_err_oom_poison res; cbn; auto.
      specialize (NOOM DTYPE_Pointer).
      cbn in NOOM.
      break_match_hyp; try contradiction.
      clear NOOM.
      erewrite int_to_ptr_fin_inf_wildcard; eauto.
      cbn.
      rewrite_fin_to_inf_dvalue.
      reflexivity.

      unfold fin_to_inf_addr.
      break_match_goal; clear Heqs; auto.
    }

    { (* Arrays *)
      rewrite dvalue_bytes_to_dvalue_equation in FIN;
        rewrite IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue_equation;
        subst.
      rewrite sizeof_dtyp_fin_inf.
      Opaque IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue
        dvalue_bytes_to_dvalue.
      cbn in *.
      destruct ((SZ.sizeof_dtyp dt =? 0)%N) eqn:HSIZE.
      { clear - IHdt NOOM.
        induction sz using N.peano_ind.
        - cbn.
          rewrite_fin_to_inf_dvalue.
          reflexivity.
        - setoid_rewrite repeatN_succ.
          cbn.
          repeat rewrite_fin_to_inf_dvalue.
          remember (dvalue_bytes_to_dvalue [] dt) as res.
          symmetry in Heqres.
          pose proof (IHdt nil nil res).
          forward H; [constructor|].
          destruct_err_oom_poison res; cbn in *;
            try solve [setoid_rewrite H; cbn; eauto; try discriminate].
          + (* Success *)
            setoid_rewrite H; cbn; eauto; try discriminate.
            forward IHsz.
            { intros x CONTRA.
              eapply NOOM.
              rewrite repeatN_succ.
              cbn.
              rewrite Heqres.
              cbn.
              remember (map_monad (fun es : list dvalue_byte => dvalue_bytes_to_dvalue es dt)
                          (repeatN sz [])) as m.
              destruct_err_oom_poison m; cbn in *; try discriminate; eauto.
            }

            remember (map_monad
                      (fun es : list IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte =>
                       IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue es dt) 
                      (repeatN sz [])) as m1.
            remember (map_monad (fun es : list dvalue_byte => dvalue_bytes_to_dvalue es dt)
               (repeatN sz [])) as m2.
            destruct_err_oom_poison m1;
              destruct_err_oom_poison m2; cbn in *; try discriminate; eauto.
            rewrite_fin_to_inf_dvalue.
            cbn.
            inv IHsz.
            rewrite fin_to_inf_dvalue_array in H1.
            inv H1.
            auto.
          + (* OOM *)
            exfalso.
            clear H IHdt.
            eapply NOOM.
            rewrite repeatN_succ.
            cbn.
            rewrite Heqres.
            cbn.
            reflexivity.
      }

      remember (split_every_nil (SZ.sizeof_dtyp dt) dvbs_fin) as split_fin.
      remember (split_every_nil (SZ.sizeof_dtyp dt) dvbs_inf) as split_inf.
      symmetry in Heqsplit_fin, Heqsplit_inf.

      pose proof split_every_nil_Forall2 _ _ _ _ _ _ REF Heqsplit_inf Heqsplit_fin as ALL.
      subst.
      induction ALL.
      - cbn.
        rewrite_fin_to_inf_dvalue; reflexivity.
      - repeat rewrite map_monad_unfold.
        cbn.
        erewrite IHdt.
        2: apply H.
        3: eauto.
        2: {
          clear - NOOM.
          rewrite map_monad_unfold in *.
          cbn in *.
          remember (dvalue_bytes_to_dvalue y dt) as r.
          intros x CONTRA.
          destruct_err_oom_poison r; inv CONTRA.
          cbn in NOOM.
          specialize (NOOM x); contradiction.
        }

        remember (dvalue_bytes_to_dvalue y dt) as r.
        destruct_err_oom_poison r; cbn; auto.
        remember (map_monad (fun x0 : list dvalue_byte => dvalue_bytes_to_dvalue x0 dt) l') as m.
        forward IHALL.
        { intros x0.
          destruct_err_oom_poison m; cbn; intros CONTRA; inv CONTRA.
          cbn in NOOM.
          repeat rewrite <- Heqr, <- Heqm in NOOM.
          cbn in NOOM.
          specialize (NOOM x0).
          contradiction.
        }

        destruct_err_oom_poison m; cbn; auto.
        + cbn in IHALL.
          remember (map_monad
                            (fun es : list IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte =>
                               IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue es dt) l) as w.
          destruct_err_oom_poison w; cbn in *; auto; inv IHALL.
        + cbn in IHALL.
          remember (map_monad
                            (fun es : list IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte =>
                               IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue es dt) l) as w.
          destruct_err_oom_poison w; cbn in *; auto; inv IHALL.
          rewrite_fin_to_inf_dvalue; auto.
          cbn.
          rewrite fin_to_inf_dvalue_array in H1.
          inv H1.
          reflexivity.
        + cbn in IHALL.
          remember (map_monad
                            (fun es : list IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte =>
                               IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue es dt) l) as w.
          destruct_err_oom_poison w; cbn in *; auto; inv IHALL.
        + cbn in IHALL.
          remember (map_monad
                            (fun es : list IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte =>
                               IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue es dt) l) as w.
          destruct_err_oom_poison w; cbn in *; auto; inv IHALL.
    }

    { (* Structs *)
      Opaque IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue
        dvalue_bytes_to_dvalue.

      subst.
      rewrite IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue_equation,
        dvalue_bytes_to_dvalue_equation.

      remember
        (fun pad : option N => fix go
           (offset : N) (dts : list dtyp) (dbs : list IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte) {struct dts} :
          ErrOOMPoison (list DV1.dvalue) :=
           match dts with
           | [] => ret []
           | dt :: dts0 =>
               let padding :=
                 if pad
                 then pad_amount (preferred_alignment (IS1.LP.SZ.dtyp_alignment dt)) offset
                 else 0 in
               let zpadding := Z.of_N padding in
               let sz := IS1.LP.SZ.sizeof_dtyp dt in
               let dbs' := drop padding dbs in
               let init_bytes := take sz dbs' in
               let rest_bytes := drop sz dbs' in
               let offset' := offset + padding in
               f <- IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue init_bytes dt;;
               rest <- go (offset' + sz) dts0 rest_bytes;; ret (f :: rest)
           end) as f1.

      remember
        (fun pad : option N =>
           fix go (offset : N) (dts : list dtyp) (dbs : list dvalue_byte) {struct dts} :
           ErrOOMPoison (list dvalue) :=
           match dts with
           | [] => ret []
           | dt :: dts0 =>
               let padding :=
                 if pad then pad_amount (preferred_alignment (SZ.dtyp_alignment dt)) offset else 0
               in
               let zpadding := Z.of_N padding in
               let sz := SZ.sizeof_dtyp dt in
               let dbs' := drop padding dbs in
               let init_bytes := take sz dbs' in
               let rest_bytes := drop sz dbs' in
               let offset' := offset + padding in
               f <- dvalue_bytes_to_dvalue init_bytes dt;;
               rest <- go (offset' + sz) dts0 rest_bytes;; ret (f :: rest)
           end) as f2.
      Opaque bind.
      cbn.
      subst.
      erewrite list_dvalue_bytes_to_dvalue_fin_inf with (pad:=Some 1); eauto.
      { Transparent bind.
        remember
          (((fix go (offset : N) (dts : list dtyp) (dbs : list dvalue_byte) {struct dts} :
             ErrOOMPoison (list dvalue) :=
           match dts with
           | [] => ret []
           | dt :: dts0 =>
               let padding := pad_amount (preferred_alignment (SZ.dtyp_alignment dt)) offset in
               let zpadding := Z.of_N padding in
               let sz := SZ.sizeof_dtyp dt in
               let dbs' := drop padding dbs in
               let init_bytes := take sz dbs' in
               let rest_bytes := drop sz dbs' in
               let offset' := offset + padding in
               f <- dvalue_bytes_to_dvalue init_bytes dt;;
               rest <- go (offset' + sz) dts0 rest_bytes;; ret (f :: rest)
           end) 0 fields dvbs_fin)) as res.
        destruct_err_oom_poison res; cbn; auto.
        rewrite_fin_to_inf_dvalue.
        reflexivity.
      }

      intros x CONTRA.
      eapply (NOOM x).
      cbn.
      rewrite dvalue_bytes_to_dvalue_equation.
      remember
        ((fun pad : option N =>
           fix go (offset : N) (dts : list dtyp) (dbs : list dvalue_byte) {struct dts} :
           ErrOOMPoison (list dvalue) :=
           match dts with
           | [] => ret []
           | dt :: dts0 =>
               let padding :=
                 if pad then pad_amount (preferred_alignment (SZ.dtyp_alignment dt)) offset else 0 in
               let zpadding := Z.of_N padding in
               let sz := SZ.sizeof_dtyp dt in
               let dbs' := drop padding dbs in
               let init_bytes := take sz dbs' in
               let rest_bytes := drop sz dbs' in
               let offset' := offset + padding in
               f <- dvalue_bytes_to_dvalue init_bytes dt;;
               rest <- go (offset' + sz) dts0 rest_bytes;; ret (f :: rest)
           end) (Some (SZ.max_preferred_dtyp_alignment fields)) 0 fields dvbs_fin) as res.
      destruct_err_oom_poison res; inv CONTRA; cbn in *; auto;
      setoid_rewrite H1;
      cbn;
      auto.
    }

    { (* Packed structs *)
      Opaque IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue
        dvalue_bytes_to_dvalue.

      subst.
      rewrite IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue_equation,
        dvalue_bytes_to_dvalue_equation.

      remember
        (fun pad : option N => fix go
           (offset : N) (dts : list dtyp) (dbs : list IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte) {struct dts} :
          ErrOOMPoison (list DV1.dvalue) :=
           match dts with
           | [] => ret []
           | dt :: dts0 =>
               let padding :=
                 if pad
                 then pad_amount (preferred_alignment (IS1.LP.SZ.dtyp_alignment dt)) offset
                 else 0 in
               let zpadding := Z.of_N padding in
               let sz := IS1.LP.SZ.sizeof_dtyp dt in
               let dbs' := drop padding dbs in
               let init_bytes := take sz dbs' in
               let rest_bytes := drop sz dbs' in
               let offset' := offset + padding in
               f <- IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue init_bytes dt;;
               rest <- go (offset' + sz) dts0 rest_bytes;; ret (f :: rest)
           end) as f1.

      remember
        (fun pad : option N =>
           fix go (offset : N) (dts : list dtyp) (dbs : list dvalue_byte) {struct dts} :
           ErrOOMPoison (list dvalue) :=
           match dts with
           | [] => ret []
           | dt :: dts0 =>
               let padding :=
                 if pad then pad_amount (preferred_alignment (SZ.dtyp_alignment dt)) offset else 0
               in
               let zpadding := Z.of_N padding in
               let sz := SZ.sizeof_dtyp dt in
               let dbs' := drop padding dbs in
               let init_bytes := take sz dbs' in
               let rest_bytes := drop sz dbs' in
               let offset' := offset + padding in
               f <- dvalue_bytes_to_dvalue init_bytes dt;;
               rest <- go (offset' + sz) dts0 rest_bytes;; ret (f :: rest)
           end) as f2.
      Opaque bind.
      cbn.
      subst.
      erewrite list_dvalue_bytes_to_dvalue_fin_inf with (pad:=None); eauto.
      { Transparent bind.
        remember
          (((fix go (offset : N) (dts : list dtyp) (dbs : list dvalue_byte) {struct dts} :
             ErrOOMPoison (list dvalue) :=
           match dts with
           | [] => ret []
           | dt :: dts0 =>
               let padding := 0 in
               let zpadding := Z.of_N padding in
               let sz := SZ.sizeof_dtyp dt in
               let dbs' := drop padding dbs in
               let init_bytes := take sz dbs' in
               let rest_bytes := drop sz dbs' in
               let offset' := offset + padding in
               f <- dvalue_bytes_to_dvalue init_bytes dt;;
               rest <- go (offset' + sz) dts0 rest_bytes;; ret (f :: rest)
           end) 0 fields dvbs_fin)) as res.
        destruct_err_oom_poison res; cbn; auto.
        rewrite_fin_to_inf_dvalue.
        reflexivity.
      }

      intros x CONTRA.
      eapply (NOOM x).
      cbn.
      rewrite dvalue_bytes_to_dvalue_equation.
      remember
        ((fun pad : option N =>
           fix go (offset : N) (dts : list dtyp) (dbs : list dvalue_byte) {struct dts} :
           ErrOOMPoison (list dvalue) :=
           match dts with
           | [] => ret []
           | dt :: dts0 =>
               let padding :=
                 if pad then pad_amount (preferred_alignment (SZ.dtyp_alignment dt)) offset else 0 in
               let zpadding := Z.of_N padding in
               let sz := SZ.sizeof_dtyp dt in
               let dbs' := drop padding dbs in
               let init_bytes := take sz dbs' in
               let rest_bytes := drop sz dbs' in
               let offset' := offset + padding in
               f <- dvalue_bytes_to_dvalue init_bytes dt;;
               rest <- go (offset' + sz) dts0 rest_bytes;; ret (f :: rest)
           end) None 0 fields dvbs_fin) as res.
      destruct_err_oom_poison res; inv CONTRA; cbn in *; auto;
      setoid_rewrite H1;
      cbn;
      auto.
    }

    { (* Vectors *)
      rewrite dvalue_bytes_to_dvalue_equation in FIN;
        rewrite IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue_equation;
        subst.
      rewrite sizeof_dtyp_fin_inf.
      Opaque IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue
        dvalue_bytes_to_dvalue.
      cbn in *.
      destruct ((SZ.sizeof_dtyp dt =? 0)%N) eqn:HSIZE.
      { clear - IHdt NOOM.
        induction sz using N.peano_ind.
        - cbn.
          rewrite_fin_to_inf_dvalue.
          reflexivity.
        - setoid_rewrite repeatN_succ.
          cbn.
          repeat rewrite_fin_to_inf_dvalue.
          remember (dvalue_bytes_to_dvalue [] dt) as res.
          symmetry in Heqres.
          pose proof (IHdt nil nil res).
          forward H; [constructor|].
          destruct_err_oom_poison res; cbn in *;
            try solve [setoid_rewrite H; cbn; eauto; try discriminate].
          + (* Success *)
            setoid_rewrite H; cbn; eauto; try discriminate.
            forward IHsz.
            { intros x CONTRA.
              eapply NOOM.
              rewrite repeatN_succ.
              cbn.
              rewrite Heqres.
              cbn.
              remember (map_monad (fun es : list dvalue_byte => dvalue_bytes_to_dvalue es dt)
                          (repeatN sz [])) as m.
              destruct_err_oom_poison m; cbn in *; try discriminate; eauto.
            }

            remember (map_monad
                      (fun es : list IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte =>
                       IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue es dt) 
                      (repeatN sz [])) as m1.
            remember (map_monad (fun es : list dvalue_byte => dvalue_bytes_to_dvalue es dt)
               (repeatN sz [])) as m2.
            destruct_err_oom_poison m1;
              destruct_err_oom_poison m2; cbn in *; try discriminate; eauto.
            rewrite_fin_to_inf_dvalue.
            cbn.
            inv IHsz.
            rewrite fin_to_inf_dvalue_vector in H1.
            inv H1.
            auto.
          + (* OOM *)
            exfalso.
            clear H IHdt.
            eapply NOOM.
            rewrite repeatN_succ.
            cbn.
            rewrite Heqres.
            cbn.
            reflexivity.
      }

      remember (split_every_nil (SZ.sizeof_dtyp dt) dvbs_fin) as split_fin.
      remember (split_every_nil (SZ.sizeof_dtyp dt) dvbs_inf) as split_inf.
      symmetry in Heqsplit_fin, Heqsplit_inf.

      pose proof split_every_nil_Forall2 _ _ _ _ _ _ REF Heqsplit_inf Heqsplit_fin as ALL.
      subst.
      induction ALL.
      - cbn.
        rewrite_fin_to_inf_dvalue; reflexivity.
      - repeat rewrite map_monad_unfold.
        cbn.
        erewrite IHdt.
        2: apply H.
        3: eauto.
        2: {
          clear - NOOM.
          rewrite map_monad_unfold in *.
          cbn in *.
          remember (dvalue_bytes_to_dvalue y dt) as r.
          intros x CONTRA.
          destruct_err_oom_poison r; inv CONTRA.
          cbn in NOOM.
          specialize (NOOM x); contradiction.
        }

        remember (dvalue_bytes_to_dvalue y dt) as r.
        destruct_err_oom_poison r; cbn; auto.
        remember (map_monad (fun x0 : list dvalue_byte => dvalue_bytes_to_dvalue x0 dt) l') as m.
        forward IHALL.
        { intros x0.
          destruct_err_oom_poison m; cbn; intros CONTRA; inv CONTRA.
          cbn in NOOM.
          repeat rewrite <- Heqr, <- Heqm in NOOM.
          cbn in NOOM.
          specialize (NOOM x0).
          contradiction.
        }

        destruct_err_oom_poison m; cbn; auto.
        + cbn in IHALL.
          remember (map_monad
                            (fun es : list IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte =>
                               IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue es dt) l) as w.
          destruct_err_oom_poison w; cbn in *; auto; inv IHALL.
        + cbn in IHALL.
          remember (map_monad
                            (fun es : list IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte =>
                               IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue es dt) l) as w.
          destruct_err_oom_poison w; cbn in *; auto; inv IHALL.
          rewrite_fin_to_inf_dvalue; auto.
          cbn.
          rewrite fin_to_inf_dvalue_vector in H1.
          inv H1.
          reflexivity.
        + cbn in IHALL.
          remember (map_monad
                            (fun es : list IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte =>
                               IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue es dt) l) as w.
          destruct_err_oom_poison w; cbn in *; auto; inv IHALL.
        + cbn in IHALL.
          remember (map_monad
                            (fun es : list IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte =>
                               IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue es dt) l) as w.
          destruct_err_oom_poison w; cbn in *; auto; inv IHALL.
    }
  Qed.

  Lemma dvalue_bytes_to_dvalue_fin_inf :
    forall τ dvbs_inf dvbs_fin res,
      dvalue_bytes_refine dvbs_inf dvbs_fin ->
      @ErrOOMPoison_handle_poison_and_oom (err_ub_oom_T IdentityMonad.ident)
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident) dvalue
        DVALUE_Poison (DVALUE_BYTES.dvalue_bytes_to_dvalue dvbs_fin τ) = success_unERR_UB_OOM res ->
      @ErrOOMPoison_handle_poison_and_oom (err_ub_oom_T IdentityMonad.ident)
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        DV1.dvalue DV1.DVALUE_Poison (IS1.LLVM.MEM.MP.DVALUE_BYTES.dvalue_bytes_to_dvalue dvbs_inf τ) = success_unERR_UB_OOM (fin_to_inf_dvalue res).
  Proof.
    intros τ dvbs_inf dvbs_fin res H H0.
    remember (@DVALUE_BYTES.dvalue_bytes_to_dvalue ErrOOMPoison
            (@EitherMonad.Monad_eitherT ERR_MESSAGE (OomableT Poisonable)
               (@Monad_OomableT Poisonable MonadPoisonable))
            (@RAISE_ERROR_MonadExc ErrOOMPoison
               (@EitherMonad.Exception_eitherT ERR_MESSAGE (OomableT Poisonable)
                  (@Monad_OomableT Poisonable MonadPoisonable)))
            (@RAISE_POISON_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
               (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
                  (@Monad_OomableT Poisonable MonadPoisonable))
               (@RAISE_POISON_E_MT Poisonable OomableT (@MonadT_OomableT Poisonable MonadPoisonable)
                  RAISE_POISON_Poisonable))
            (@RAISE_OOMABLE_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
               (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
                  (@Monad_OomableT Poisonable MonadPoisonable))
               (@RAISE_OOMABLE_OomableT Poisonable MonadPoisonable)) dvbs_fin τ).
    destruct e.
    destruct unEitherT.
    destruct unMkOomableT; inv H0.
    2: {
      unfold ErrOOMPoison_handle_poison_and_oom.
      symmetry in Heqe.
      erewrite dvalue_bytes_fin_to_dvalue_fin_inf; eauto.
      cbn; rewrite_fin_to_inf_dvalue; eauto.
      intros ? CONTRA; inv CONTRA.
    }
    destruct o; inv H2.
    repeat red in H1.
    unfold ErrOOMPoison_handle_poison_and_oom in H1.
    cbn in H1.
    destruct s; inv H1.
    destruct e; inv H2.
    unfold ErrOOMPoison_handle_poison_and_oom.
    erewrite dvalue_bytes_fin_to_dvalue_fin_inf; eauto.
    2: {
      intros ? CONTRA.
      rewrite <- Heqe in CONTRA.
      inv CONTRA.
    }
    rewrite <- Heqe.
    cbn; reflexivity.
  Qed.

  Lemma dvalue_to_dvalue_bytes_fin_to_inf_dvalue :
    forall dv_fin t,
      IS1.LLVM.MEM.MP.DVALUE_BYTES.dvalue_to_dvalue_bytes (fin_to_inf_dvalue dv_fin) t =
        fin_to_inf_dvalue_bytes (dvalue_to_dvalue_bytes dv_fin t).
  Proof.
    intros dv_fin t.
    destruct dv_fin;
      rewrite_fin_to_inf_dvalue;
      try
        solve
        [ erewrite <- dvalue_to_dvalue_bytes_fin_inf; eauto;
          reflexivity
        ].

    - erewrite <- dvalue_to_dvalue_bytes_fin_inf; eauto.
      red.
      cbn.
      rewrite addr_refine_fin_to_inf_addr.
      reflexivity.
    - erewrite <- dvalue_to_dvalue_bytes_fin_inf; eauto.
      red.
      cbn.
      pose proof intptr_convert_succeeds x as (?&?).
      eapply intptr_convert_safe in e.
      erewrite intptr_convert_safe.
      reflexivity.
      unfold intptr_fin_inf.
      break_match_goal.
      clear Heqs.
      auto.
    - erewrite <- dvalue_to_dvalue_bytes_fin_inf; eauto.
      red.
      cbn.
      induction fields.
      + cbn; reflexivity.
      + cbn.
        break_match_hyp_inv.
        rewrite fin_to_inf_dvalue_refine_strict.
        reflexivity.
    - erewrite <- dvalue_to_dvalue_bytes_fin_inf; eauto.
      red.
      cbn.
      induction fields.
      + cbn; reflexivity.
      + cbn.
        break_match_hyp_inv.
        rewrite fin_to_inf_dvalue_refine_strict.
        reflexivity.
    - erewrite <- dvalue_to_dvalue_bytes_fin_inf; eauto.
      red.
      cbn.
      induction elts.
      + cbn; reflexivity.
      + cbn.
        break_match_hyp_inv.
        rewrite fin_to_inf_dvalue_refine_strict.
        reflexivity.
    - erewrite <- dvalue_to_dvalue_bytes_fin_inf; eauto.
      red.
      cbn.
      induction elts.
      + cbn; reflexivity.
      + cbn.
        break_match_hyp_inv.
        rewrite fin_to_inf_dvalue_refine_strict.
        reflexivity.
  Qed.


  Lemma dvalue_bytes_to_dvalue_ub_fin_inf :
    forall τ dvbs_inf dvbs_fin ub_msg,
      dvalue_bytes_refine dvbs_inf dvbs_fin ->
      @ErrOOMPoison_handle_poison_and_oom (err_ub_oom_T IdentityMonad.ident)
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident) dvalue
        DVALUE_Poison (DVALUE_BYTES.dvalue_bytes_to_dvalue dvbs_fin τ) = UB_unERR_UB_OOM ub_msg ->
      @ErrOOMPoison_handle_poison_and_oom (err_ub_oom_T IdentityMonad.ident)
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        DV1.dvalue DV1.DVALUE_Poison (IS1.LLVM.MEM.MP.DVALUE_BYTES.dvalue_bytes_to_dvalue dvbs_inf τ) = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros τ dvbs_inf dvbs_fin ub_msg H H0.
    remember (@DVALUE_BYTES.dvalue_bytes_to_dvalue ErrOOMPoison
            (@EitherMonad.Monad_eitherT ERR_MESSAGE (OomableT Poisonable)
               (@Monad_OomableT Poisonable MonadPoisonable))
            (@RAISE_ERROR_MonadExc ErrOOMPoison
               (@EitherMonad.Exception_eitherT ERR_MESSAGE (OomableT Poisonable)
                  (@Monad_OomableT Poisonable MonadPoisonable)))
            (@RAISE_POISON_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
               (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
                  (@Monad_OomableT Poisonable MonadPoisonable))
               (@RAISE_POISON_E_MT Poisonable OomableT (@MonadT_OomableT Poisonable MonadPoisonable)
                  RAISE_POISON_Poisonable))
            (@RAISE_OOMABLE_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
               (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
                  (@Monad_OomableT Poisonable MonadPoisonable))
               (@RAISE_OOMABLE_OomableT Poisonable MonadPoisonable)) dvbs_fin τ).
    destruct e.
    destruct unEitherT.
    destruct unMkOomableT; inv H0.
    destruct o; inv H2.
    destruct s; inv H1.
    destruct e; inv H2.
  Qed.

  (* Lemma extractbytes_to_dvalue_ub_fin_inf : *)
  (*   forall uvs l ub_msg dt *)
  (*     (Heqo : map_monad uvalue_convert_strict uvs = NoOom l) *)
  (*     (IH : forall (u : DV1.uvalue), *)
  (*         Exists (DV1.uvalue_subterm u) uvs -> *)
  (*         forall uv_fin : DV2.uvalue, *)
  (*           uvalue_refine_strict u uv_fin -> *)
  (*           forall ub_msg, *)
  (*             IS2.MEM.CP.CONC.concretize_u uv_fin (UB_unERR_UB_OOM ub_msg) -> *)
  (*             IS1.MEM.CP.CONC.concretize_u u (UB_unERR_UB_OOM ub_msg)), *)
  (*     @extractbytes_to_dvalue ErrUbOomProp Monad_ErrUbOomProp *)
  (*       (fun (dt : dtyp) (edv : err_ub_oom dvalue) => *)
  (*          match @unERR_UB_OOM IdentityMonad.ident dvalue edv with *)
  (*          | {| *)
  (*              EitherMonad.unEitherT := *)
  (*                {| *)
  (*                  EitherMonad.unEitherT := *)
  (*                    {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |} *)
  (*                |} *)
  (*            |} => dvalue_has_dtyp dv dt /\ dv <> DVALUE_Poison dt *)
  (*          | _ => True *)
  (*          end) err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) *)
  (*       (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) *)
  (*       (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident) *)
  (*       (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident) *)
  (*       (fun (A : Type) (x ue : err_ub_oom A) => x = ue) l dt (UB_unERR_UB_OOM ub_msg) -> *)
  (*     @IS1.LLVM.MEM.CP.CONCBASE.extractbytes_to_dvalue ErrUbOomProp Monad_ErrUbOomProp *)
  (*       (fun (dt0 : dtyp) (edv : err_ub_oom DV1.dvalue) => *)
  (*          match @unERR_UB_OOM IdentityMonad.ident DV1.dvalue edv with *)
  (*          | {| *)
  (*              EitherMonad.unEitherT := *)
  (*                {| *)
  (*                  EitherMonad.unEitherT := *)
  (*                    {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |} *)
  (*                |} *)
  (*            |} => DV1.dvalue_has_dtyp dv dt0 /\ dv <> DV1.DVALUE_Poison dt0 *)
  (*          | _ => True *)
  (*          end) err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) *)
  (*       (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) *)
  (*       (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident) *)
  (*       (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident) *)
  (*       (fun (A : Type) (x ue : err_ub_oom A) => x = ue) uvs dt *)
  (*       (UB_unERR_UB_OOM ub_msg). *)
  (* Proof. *)
  (*   intros uvs l ub_msg dt Heqo IH EXTRACT. *)
  (*   rewrite IS1.LLVM.MEM.CP.CONCBASE.extractbytes_to_dvalue_equation. *)
  (*   rewrite extractbytes_to_dvalue_equation in EXTRACT. *)
  (*   repeat red in EXTRACT. *)
  (*   destruct EXTRACT as (?&?&?&?&?). *)
  (*   destruct_err_ub_oom x; inv H0. *)
  (*   { exists (UB_unERR_UB_OOM ub_msg). *)
  (*     exists (fun _ => UB_unERR_UB_OOM ub_msg). *)
  (*     split; cbn; eauto. *)
  (*     eapply concretize_uvalue_bytes_ub_fin_inf; eauto. *)
  (*     eapply map_monad_oom_Forall2; eauto. *)
  (*   } *)

  (*   destruct H1 as [[] | H1]. *)
  (*   specialize (H1 x1). *)
  (*   forward H1; [cbn; auto|]. *)
  (*   remember (x0 x1) as x0x1. *)
  (*   destruct_err_ub_oom x0x1; inv H3. *)

  (*   eapply concretize_uvalue_bytes_fin_inf in H; eauto. *)
  (*   3: eapply map_monad_oom_Forall2; eauto. *)
  (*   2: { *)
  (*     intros u H0 uv_fin H2 dv_fin H3. *)
  (*     eapply uvalue_concretize_strict_concretize_inclusion; eauto. *)
  (*   } *)

  (*   exists (ret (fin_to_inf_dvalue_bytes x1)). *)
  (*   exists (fun _ => UB_unERR_UB_OOM ub_msg). *)
  (*   split; eauto. *)
  (*   split; eauto. *)
  (*   right. *)
  (*   intros a RETa. *)
  (*   inv RETa. *)
  (*   eapply dvalue_bytes_to_dvalue_ub_fin_inf; eauto. *)
  (*   apply dvalue_bytes_refine_fin_to_inf_dvalue_bytes. *)
  (* Qed. *)


  Lemma dvalue_bytes_to_dvalue_err_fin_inf :
    forall τ dvbs_inf dvbs_fin err_msg,
      dvalue_bytes_refine dvbs_inf dvbs_fin ->
      @ErrOOMPoison_handle_poison_and_oom (err_ub_oom_T IdentityMonad.ident)
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident) dvalue
        DVALUE_Poison (DVALUE_BYTES.dvalue_bytes_to_dvalue dvbs_fin τ) = ERR_unERR_UB_OOM err_msg ->
      @ErrOOMPoison_handle_poison_and_oom (err_ub_oom_T IdentityMonad.ident)
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        DV1.dvalue DV1.DVALUE_Poison (IS1.LLVM.MEM.MP.DVALUE_BYTES.dvalue_bytes_to_dvalue dvbs_inf τ) = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros τ dvbs_inf dvbs_fin err_msg H H0.
    remember (@DVALUE_BYTES.dvalue_bytes_to_dvalue ErrOOMPoison
                (@EitherMonad.Monad_eitherT ERR_MESSAGE (OomableT Poisonable)
                   (@Monad_OomableT Poisonable MonadPoisonable))
                (@RAISE_ERROR_MonadExc ErrOOMPoison
                   (@EitherMonad.Exception_eitherT ERR_MESSAGE (OomableT Poisonable)
                      (@Monad_OomableT Poisonable MonadPoisonable)))
                (@RAISE_POISON_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
                   (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
                      (@Monad_OomableT Poisonable MonadPoisonable))
                   (@RAISE_POISON_E_MT Poisonable OomableT (@MonadT_OomableT Poisonable MonadPoisonable)
                      RAISE_POISON_Poisonable))
                (@RAISE_OOMABLE_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
                   (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
                      (@Monad_OomableT Poisonable MonadPoisonable))
                   (@RAISE_OOMABLE_OomableT Poisonable MonadPoisonable)) dvbs_fin τ).
    destruct_err_oom_poison e; inv H0.
    cbn in *.
    break_match_hyp_inv.
    erewrite dvalue_bytes_fin_to_dvalue_fin_inf; cbn; eauto.
    rewrite <- Heqe; cbn.
    reflexivity.

    intros x CONTRA.
    rewrite CONTRA in Heqe.
    inv Heqe.
  Qed.

  Lemma orutt_dvalue_bytes_to_dvalue :
    forall E1 E2
      `{OOM1 : OOME -< E1} `{OOM2 : OOME -< E2}
      `{UB1 : UBE -< E1} `{UB2 : UBE -< E2}
      `{ERR1: FailureE -< E1} `{ERR2: FailureE -< E2}
      (pre : prerel E1 E2) (post : postrel E1 E2)
      (UBDISC : forall e1 e2, @subevent UBE E2 UB2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (ERRDISC : forall e1 e2, @subevent FailureE E2 ERR2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (UBINJ : pre void void (@subevent UBE E1 UB1 void (ThrowUB tt)) (@subevent UBE E2 UB2 void (ThrowUB tt)))
      (ERRINJ : pre void void (@subevent FailureE E1 ERR1 void (Throw tt)) (@subevent FailureE E2 ERR2 void (Throw tt)))
      dt (r1 : list IS1.MEM.DVALUE_BYTE.dvalue_byte) (r2 : list dvalue_byte),
      dvalue_bytes_refine r1 r2 ->
      orutt (OOM:=OOME) pre post dvalue_refine_strict
        (ErrOOMPoison_handle_poison_and_oom DV1.DVALUE_Poison
           (IS1.LLVM.MEM.MP.DVALUE_BYTES.dvalue_bytes_to_dvalue r1 dt))
        (ErrOOMPoison_handle_poison_and_oom DVALUE_Poison (DVALUE_BYTES.dvalue_bytes_to_dvalue r2 dt)).
  Proof.
    intros E1 E2 OOM1 OOM2 UB1 UB2 ERR1 ERR2 pre post UBDISC ERRDISC UBINJ ERRINJ dt r1 r2 H.
    rewrite TLR1.handle_poison_and_oom_dvalue_bytes_to_dvalue_err_ub_oom_to_itree,
      TLR2.handle_poison_and_oom_dvalue_bytes_to_dvalue_err_ub_oom_to_itree.
    remember (ErrOOMPoison_handle_poison_and_oom DVALUE_Poison (DVALUE_BYTES.dvalue_bytes_to_dvalue r2 dt)) as res.
    destruct_err_ub_oom res; symmetry in Heqres.
    - apply orutt_raiseOOM.
    - erewrite dvalue_bytes_to_dvalue_ub_fin_inf; eauto.
      apply orutt_raiseUB; auto.
    - erewrite dvalue_bytes_to_dvalue_err_fin_inf; eauto.
      apply orutt_raise; auto.
    - erewrite dvalue_bytes_to_dvalue_fin_inf; eauto.
      apply orutt_Ret.
      apply fin_to_inf_dvalue_refine_strict.
  Qed.

  #[global] Hint Resolve
    orutt_dvalue_bytes_to_dvalue
    : ORUTT.
End BytesRefine.
