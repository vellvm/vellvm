From Stdlib Require Import
  Lia
  ZArith
  Program.Equality
  Relations
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
  VellvmRelations
  NMaps
  ErrUbOomProp
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
  Utils.

From Vellvm.Semantics.InfiniteToFinite Require Import
  R2Injective.

From ITree Require Import
  ITree
  Basics.HeterogeneousRelations
  Eq.Rutt
  Eq.RuttFacts
  Eq.Eqit.

Import Classical.
Import MonadNotation.
Import ListNotations.

Module Type ConcretizationRefine
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
                  VAL_REF).


  Import EC.
  Import DV2.
  Import IS2.LP.
  Import DynamicTypes.
  Import IPS.
  Import ER.
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

  Definition uvalue_concretize_u_fin_inf_inclusion uv_inf uv_fin :=
    forall res,
      IS2.MEM.CP.CONC.concretize_u uv_fin res ->
      IS1.MEM.CP.CONC.concretize_u uv_inf (fmap fin_to_inf_dvalue res).

  Definition uvalue_concretize_fin_inf_inclusion uv_inf uv_fin :=
    forall dv_fin,
      IS2.MEM.CP.CONC.concretize uv_fin dv_fin ->
      IS1.MEM.CP.CONC.concretize uv_inf (fin_to_inf_dvalue dv_fin).

  Definition uvalue_concretize_inf_fin_inclusion uv_inf uv_fin :=
    forall dv_inf,
      IS1.MEM.CP.CONC.concretize uv_inf dv_inf ->
      exists dv_fin,
        dvalue_refine_strict dv_inf dv_fin /\
          IS2.MEM.CP.CONC.concretize uv_fin dv_fin.

  Definition concretization_list_refine : (list (DV1.uvalue * DV1.dvalue)) -> (list (uvalue * dvalue)) -> Prop
    :=
    Forall2 (uvalue_refine_strict × dvalue_refine_strict).

  Definition concretization_map_refine
    (inf_map : NMap (list (DV1.uvalue * DV1.dvalue)))
    (fin_map : NMap (list (uvalue * dvalue))) : Prop
    :=
    NM_Refine concretization_list_refine inf_map fin_map.

  Lemma concretization_map_refine_empty :
    concretization_map_refine (NM.empty (list (DV1.uvalue * DV1.dvalue))) (NM.empty (list (uvalue * dvalue))).
  Proof.
    repeat red.
    split.
    - intros k.
      split; intros CONTRA;
        eapply NM_In_empty_contra in CONTRA; contradiction.
    - intros k e e' H H0.
      repeat red in H.
      eapply NM.Raw.Proofs.empty_1 in H; contradiction.
  Qed.

  Lemma concretize_map_refine_find_none_inf_fin :
    forall acc_inf acc_fin sid,
      concretization_map_refine acc_inf acc_fin ->
      NM.find (elt:=list (DV1.uvalue * DV1.dvalue)) sid acc_inf = None ->
      NM.find (elt:=list (uvalue * dvalue)) sid acc_fin = None.
  Proof.
    intros acc_inf acc_fin sid ACC_REF FIND.
    destruct (NM.find (elt:=list (uvalue * dvalue)) sid acc_fin) eqn:FIND_FIN; auto.
    exfalso.

    destruct ACC_REF as (ACC_IN & ACC_MAPSTO).
    apply NM_find_In in FIND_FIN.
    apply ACC_IN in FIND_FIN.
    apply NM_find_not_In in FIND.
    contradiction.
  Qed.

  Lemma concretize_map_refine_find_some_inf_fin :
    forall acc_inf acc_fin sid conc_list_inf,
      concretization_map_refine acc_inf acc_fin ->
      NM.find (elt:=list (DV1.uvalue * DV1.dvalue)) sid acc_inf = Some conc_list_inf ->
      exists conc_list_fin,
        NM.find (elt:=list (uvalue * dvalue)) sid acc_fin = Some conc_list_fin /\
          concretization_list_refine conc_list_inf conc_list_fin.
  Proof.
    intros acc_inf acc_fin sid conc_list_inf ACC_REF FIND.
    destruct ACC_REF as (ACC_IN & ACC_MAPSTO).
    pose proof FIND as IN.
    apply NM_find_In in IN.
    apply ACC_IN in IN.
    destruct IN.
    exists x.
    apply NM.find_2 in FIND.
    split.
    - apply NM.find_1; auto.
    - eapply ACC_MAPSTO; eauto.
  Qed.

  Lemma concretize_map_refine_new_concretized_byte_fin_inf :
    forall acc_inf acc_fin uv_inf uv_fin dv_inf dv_fin sid,
      concretization_map_refine acc_inf acc_fin ->
      uvalue_refine_strict uv_inf uv_fin ->
      dvalue_refine_strict dv_inf dv_fin ->
      concretization_map_refine
        (IS1.LLVM.MEM.CP.CONCBASE.new_concretized_byte acc_inf uv_inf dv_inf sid)
        (new_concretized_byte acc_fin uv_fin dv_fin sid).
  Proof.
    intros acc_inf acc_fin uv_inf uv_fin dv_inf dv_fin
      sid ACC_REF UV_REF DV_REF.
    repeat red.
    split.
    { (* In *)
      intros k.
      unfold IS1.LLVM.MEM.CP.CONCBASE.new_concretized_byte,
        new_concretized_byte in *.
      split; intros IN.
      - break_match_hyp.
        + eapply concretize_map_refine_find_some_inf_fin in Heqo; eauto.
          destruct Heqo as (?&?&?).
          rewrite H.
          break_match_hyp.
          * eapply assoc_similar_lookup in Heqo.
            3: apply H0.
            2: apply uvalue_refine_strict_R2_injective.
            destruct Heqo as (?&?&?&?&?&?).
            assert (x0 = uv_fin).
            { pose proof Util.Forall2_Nth H2 H3 H0.
              destruct H4.
              cbn in *.
              red in UV_REF, fst_rel.
              rewrite UV_REF in fst_rel.
              inv fst_rel; auto.
            }
            subst.

            rewrite H1.
            apply ACC_REF; auto.
          * assert (Util.assoc uv_fin x = None).
            { eapply assoc_similar_no_lookup
                with (xs:=l); eauto.
              apply uvalue_refine_strict_R2_injective.
            }
            rewrite H1.

            assert ((k = sid) \/ (k <> sid)) as [EQ | NEQ] by lia.
            -- subst.
               apply NM_In_add_eq.
            -- apply NM_In_add_neq; eauto.
               apply NM_In_add_neq in IN; eauto.
               apply ACC_REF; auto.
        + eapply concretize_map_refine_find_none_inf_fin in Heqo; eauto.
          rewrite Heqo.

          assert ((k = sid) \/ (k <> sid)) as [EQ | NEQ] by lia.
          -- subst.
             apply NM_In_add_eq.
          -- apply NM_In_add_neq; eauto.
             apply NM_In_add_neq in IN; eauto.
             apply ACC_REF; auto.
      - break_match_goal.
        + eapply concretize_map_refine_find_some_inf_fin in Heqo; eauto.
          destruct Heqo as (?&?&?).
          rewrite H in IN.
          break_match_goal.
          * eapply assoc_similar_lookup in Heqo.
            3: apply H0.
            2: apply uvalue_refine_strict_R2_injective.
            destruct Heqo as (?&?&?&?&?&?).
            assert (x0 = uv_fin).
            { pose proof Util.Forall2_Nth H2 H3 H0.
              destruct H4.
              cbn in *.
              red in UV_REF, fst_rel.
              rewrite UV_REF in fst_rel.
              inv fst_rel; auto.
            }
            subst.

            rewrite H1 in IN.
            apply ACC_REF; auto.
          * assert (Util.assoc uv_fin x = None).
            { eapply assoc_similar_no_lookup
                with (xs:=l); eauto.
              apply uvalue_refine_strict_R2_injective.
            }
            rewrite H1 in IN.

            assert ((k = sid) \/ (k <> sid)) as [EQ | NEQ] by lia.
            -- subst.
               apply NM_In_add_eq.
            -- apply NM_In_add_neq; eauto.
               apply NM_In_add_neq in IN; eauto.
               apply ACC_REF; auto.
        + eapply concretize_map_refine_find_none_inf_fin in Heqo; eauto.
          rewrite Heqo in IN.

          assert ((k = sid) \/ (k <> sid)) as [EQ | NEQ] by lia.
          -- subst.
             apply NM_In_add_eq.
          -- apply NM_In_add_neq; eauto.
             apply NM_In_add_neq in IN; eauto.
             apply ACC_REF; auto.
    }

    { (* MapsTo *)
      intros k e e' MAPS1 MAPS2.
      unfold IS1.LLVM.MEM.CP.CONCBASE.new_concretized_byte,
        new_concretized_byte in *.
      red.
      pose proof ACC_REF as [_ ACC_MAPS].
      destruct (NM.find (elt:=list (DV1.uvalue * DV1.dvalue)) sid acc_inf) eqn:FIND_INF.
      - eapply concretize_map_refine_find_some_inf_fin in FIND_INF; eauto.
        destruct FIND_INF as (?&?&?).
        rewrite H in MAPS2.
        destruct (Util.assoc uv_inf l) eqn:ASSOC.
        + eapply assoc_similar_lookup
            with (xs:=l) in ASSOC; eauto.
          2: apply uvalue_refine_strict_R2_injective.

          destruct ASSOC as (?&?&?&?&?&?).
          assert (x0 = uv_fin).
          { pose proof Util.Forall2_Nth H2 H3 H0.
            destruct H4.
            cbn in *.
            red in UV_REF, fst_rel.
            rewrite UV_REF in fst_rel.
            inv fst_rel; auto.
          }
          subst.
          rewrite H1 in MAPS2.
          eapply ACC_MAPS; eauto.
        + assert (Util.assoc uv_fin x = None).
          { eapply assoc_similar_no_lookup
              with (xs:=l); eauto.
            apply uvalue_refine_strict_R2_injective.
          }
          rewrite H1 in MAPS2.

          assert ((k = sid) \/ (k <> sid)) as [EQ | NEQ] by lia.
          -- subst.
             apply NM_MapsTo_eq in MAPS1, MAPS2; subst.
             apply Forall2_app; auto.
          -- apply NM.add_3 in MAPS1, MAPS2; auto.
             eapply ACC_MAPS; eauto.
      - eapply concretize_map_refine_find_none_inf_fin in FIND_INF; eauto.
        rewrite FIND_INF in MAPS2.
        assert ((k = sid) \/ (k <> sid)) as [EQ | NEQ] by lia.
        -- subst.
           apply NM_MapsTo_eq in MAPS1, MAPS2; subst.
           repeat constructor; cbn; auto.
        -- apply NM.add_3 in MAPS1, MAPS2; auto.
           eapply ACC_MAPS; eauto.
    }
  Qed.

  Lemma pre_concretized_fin_inf :
    forall uv_inf uv_fin acc_inf acc_fin sid,
      concretization_map_refine acc_inf acc_fin ->
      uvalue_refine_strict uv_inf uv_fin ->
      IS1.LLVM.MEM.CP.CONCBASE.pre_concretized acc_inf uv_inf sid =
        fmap fin_to_inf_dvalue (pre_concretized acc_fin uv_fin sid).
  Proof.
    intros uv_inf uv_fin acc_inf acc_fin sid ACC_REF REF.
    unfold pre_concretized,
      IS1.LLVM.MEM.CP.CONCBASE.pre_concretized.
    cbn.
    break_match_goal.
    - eapply concretize_map_refine_find_some_inf_fin in Heqo;
        eauto.
      destruct Heqo as (?&?&?).
      rewrite H.
      destruct (Util.assoc uv_inf l) eqn:ASSOC.
      + eapply assoc_similar_lookup
            with (xs:=l) in ASSOC; eauto.
        2: apply uvalue_refine_strict_R2_injective.

        destruct ASSOC as (?&?&?&?&?&?).
        pose proof Util.Forall2_Nth H2 H3 H0.
        destruct H4; cbn in *.
        red in REF, fst_rel.
        rewrite REF in fst_rel.
        inv fst_rel; auto.

        rewrite H1.
        erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      + assert (Util.assoc uv_fin x = None).
        { eapply assoc_similar_no_lookup
            with (xs:=l); eauto.
          apply uvalue_refine_strict_R2_injective.
        }
        rewrite H1; auto.
    - eapply concretize_map_refine_find_none_inf_fin in Heqo;
        eauto.
      rewrite Heqo.
      auto.
  Qed.

  Lemma concretize_uvalue_bytes_helper_fin_inf :
    forall uvs_inf uvs_fin acc_inf acc_fin res
      (IH : forall (u : DV1.uvalue),
          Exists (DV1.uvalue_subterm u) uvs_inf ->
          forall uv_fin : DV2.uvalue,
            uvalue_refine_strict u uv_fin ->
            forall dv_fin : dvalue,
              IS2.MEM.CP.CONC.concretize uv_fin dv_fin ->
              IS1.MEM.CP.CONC.concretize u (fin_to_inf_dvalue dv_fin)),
      Forall2 uvalue_refine_strict uvs_inf uvs_fin ->
      concretization_map_refine acc_inf acc_fin ->
      @IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalue_bytes_helper ErrUbOomProp Monad_ErrUbOomProp
        (fun (dt : dtyp) (edv : err_ub_oom dvalue) =>
           match @unERR_UB_OOM IdentityMonad.ident dvalue edv with
           | {|
               EitherMonad.unEitherT :=
                 {|
                   EitherMonad.unEitherT :=
                     {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |}
                 |}
             |} => dvalue_has_dtyp dv dt /\ dv <> DVALUE_Poison dt
           | _ => True
           end) err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (fun (A : Type) (x ue : err_ub_oom A) => x = ue) acc_fin uvs_fin (ret res) ->
      @IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalue_bytes_helper ErrUbOomProp Monad_ErrUbOomProp
        (fun (dt0 : dtyp) (edv : err_ub_oom DV1.dvalue) =>
           match @unERR_UB_OOM IdentityMonad.ident DV1.dvalue edv with
           | {|
               EitherMonad.unEitherT :=
                 {|
                   EitherMonad.unEitherT :=
                     {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |}
                 |}
             |} => DV1.dvalue_has_dtyp dv dt0 /\ dv <> DV1.DVALUE_Poison dt0
           | _ => True
           end) err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (fun (A : Type) (x ue : err_ub_oom A) => x = ue) acc_inf uvs_inf (ret (map fin_to_inf_dvalue_byte res)).
  Proof.
    (* Will need something about acc_inf and acc_fin *)
    induction uvs_inf;
      intros uvs_fin acc_inf acc_fin res IH REF ACC_REF CONC.
    - inv REF.
      cbn in CONC; inv CONC; cbn.
      reflexivity.
    - inv REF.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalue_bytes_helper_equation in CONC.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalue_bytes_helper_equation.
      destruct y; uvalue_refine_strict_inv H1; try inv CONC.
      rewrite pre_concretized_fin_inf with (uv_fin:=y) (acc_fin:=acc_fin); eauto.
      break_match_hyp_inv; repeat red.
      + (* pre-concretization exists *)
        destruct H as (?&?&?&?).
        destruct_err_ub_oom x0; inv H1.
        destruct H2 as [[] | H2].
        specialize (H2 x2).
        forward H2; [cbn; auto|].
        cbn in H2.
        rewrite <- H2 in H5.
        inv H5.

        specialize (IHuvs_inf l' acc_inf acc_fin x2).
        repeat (forward IHuvs_inf; eauto).

        exists (ret (map fin_to_inf_dvalue_byte x2)).
        exists (fun _ => ret (map fin_to_inf_dvalue_byte (DVALUE_ExtractByte d dt idx :: x2))).
        split; eauto.
        split; eauto.

        right.
        intros a RETa.
        inv RETa.
        cbn.
        reflexivity.
      + (* No pre-concretization exists *)
        destruct H as (?&?&?&?).
        destruct_err_ub_oom x0; inv H1.
        destruct H2 as [[] | H2].
        specialize (H2 x2).
        forward H2; [cbn; auto|].
        cbn in H2.
        repeat red in H2.
        destruct H2 as (?&?&?&?&?).
        rewrite <- H2 in H5.
        destruct_err_ub_oom x0; inv H5.
        destruct H4 as [[] | H4].
        specialize (H4 x4).
        forward H4; [cbn; auto|].
        rewrite <- H4 in H7.
        inv H7.

        eapply IH in H; eauto.
        2: solve [repeat constructor].
        exists (ret (fin_to_inf_dvalue x2)).
        exists (fun _ => ret (map fin_to_inf_dvalue_byte (DVALUE_ExtractByte x2 dt idx :: x4))).
        split; eauto.
        split; eauto.

        right.
        intros a RETa.
        inv RETa.
        cbn in H2.
        rewrite <- H4 in H2.
        inv H2.
        repeat red.

        specialize
          (IHuvs_inf l'
             (IS1.LLVM.MEM.CP.CONCBASE.new_concretized_byte acc_inf x (fin_to_inf_dvalue x2) sid)
             (new_concretized_byte acc_fin y x2 sid) x4).
        forward IHuvs_inf; eauto.
        forward IHuvs_inf; eauto.
        forward IHuvs_inf.
        eapply concretize_map_refine_new_concretized_byte_fin_inf; eauto.
        apply fin_to_inf_dvalue_refine_strict.
        forward IHuvs_inf; eauto.

        exists (ret (map fin_to_inf_dvalue_byte x4)).
        exists (fun _ =>
             ret (map fin_to_inf_dvalue_byte (DVALUE_ExtractByte x2 dt idx :: x4))).
        split; eauto.
        split; eauto.

        right.
        intros a RETa.
        inv RETa.
        cbn.
        reflexivity.
  Qed.

  Lemma uvalue_concretize_strict_concretize_inclusion :
    forall uv_inf uv_fin,
      uvalue_refine_strict uv_inf uv_fin ->
      uvalue_concretize_fin_inf_inclusion uv_inf uv_fin.
  Proof.
    induction uv_inf using DV1.uvalue_strong_ind;
      intros uv_fin REF;
      try solve
        [ red; intros dv_fin CONC_FIN;
          red in REF;
          cbn in REF; inv REF;

          rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN;
          red in CONC_FIN;
          rewrite CONCBASE.concretize_uvalueM_equation in CONC_FIN;
          cbn in CONC_FIN; inv CONC_FIN;

          rewrite IS1.MEM.CP.CONC.concretize_equation;
          red;
          rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation;
          cbn;
          unfold fin_to_inf_dvalue;
          break_match_goal; clear Heqs; destruct p; clear e0;
            cbn in e; inv e;
          reflexivity
        ].
    - (* Addresses *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite CONCBASE.concretize_uvalueM_equation in CONC_FIN.
      cbn in CONC_FIN; inv CONC_FIN.

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.
      cbn.
      unfold fin_to_inf_dvalue.
      break_match_goal.
      clear Heqs; destruct p; clear e0.
      cbn in e.
      break_match_hyp_inv.
      pose proof (ACS.addr_convert_safe _ _ Heqo0).
      pose proof (AC1.addr_convert_injective _ _ _ Heqo H); subst.
      reflexivity.
    - (* IPTR *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.
      cbn.
      unfold fin_to_inf_dvalue.
      break_match_goal.
      clear Heqs; destruct p; clear e0.
      cbn in CONC_FIN.
      inv CONC_FIN.
      cbn in e.
      break_match_hyp_inv.
      pose proof (intptr_convert_safe _ _ Heqo0).
      pose proof IP.from_Z_injective _ _ _ Heqo H.
      apply IS1.LP.IP.to_Z_inj in H0; subst.
      reflexivity.
    - (* Undef *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF; inv REF.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite CONCBASE.concretize_uvalueM_equation in CONC_FIN.
      cbn in CONC_FIN.

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.
      cbn.

      destruct CONC_FIN.
      split.
      eapply dvalue_has_dtyp_fin_to_inf_dvalue; eauto.
      eapply fin_to_inf_dvalue_not_poison; auto.
    - (* Subterms *)
      { destruct uv_inf;
          try solve
            [ red; intros dv_fin CONC_FIN;
              red in REF;
              cbn in REF; inv REF;

              rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN;
              red in CONC_FIN;
              rewrite CONCBASE.concretize_uvalueM_equation in CONC_FIN;
              cbn in CONC_FIN; inv CONC_FIN;

              rewrite IS1.MEM.CP.CONC.concretize_equation;
              red;
              rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation;
              cbn;
              unfold fin_to_inf_dvalue;
              break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e;
              reflexivity
            ].

        22: {
          cbn in *.
          rename uvs into uv_bytes_inf.
          unfold uvalue_concretize_fin_inf_inclusion in *.
          intros dv_fin H0.

          red in REF.
          cbn in REF.
          break_match_hyp_inv.
          rename l into uv_bytes_fin.

          Opaque Datatypes.length N.eqb.

          rewrite IS1.MEM.CP.CONC.concretize_equation;
            red; rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation;
            cbn; repeat red.

          rewrite IS2.MEM.CP.CONC.concretize_equation in H0;
            red in H0; rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in H0;
            cbn in H0; repeat red in H0.

          replace (Datatypes.length uv_bytes_inf) with (Datatypes.length uv_bytes_fin).
          2: {
            clear - Heqo.
            symmetry.
            eapply map_monad_oom_length; eauto.
          }
          rewrite sizeof_dtyp_fin_inf.

          break_match_hyp.
          2: {
            (* Size mismatch *)
            repeat red in H0.
            destruct H0 as (?&?&?&?&?).
            destruct_err_ub_oom x; inv H1.
            destruct H2 as [[] | H2].
            specialize (H2 x1).
            forward H2; [cbn; auto|].
            remember (x0 x1) as x0x1.
            destruct_err_ub_oom x0x1; inv H4.

            eapply concretize_uvalue_bytes_helper_fin_inf in H0; eauto.
            3: eapply map_monad_oom_Forall2; eauto.

            exists (ret (fin_to_inf_dvalue_bytes x1)).
            exists (fun _ => ret (fin_to_inf_dvalue dv_fin)).
            split; eauto.
            split; eauto.
            right.
            intros a RETa.
            inv RETa.
            eapply dvalue_bytes_to_dvalue_fin_inf; eauto.
            apply dvalue_bytes_refine_fin_to_inf_dvalue_bytes.

            intros u H1 uv_fin H3 dv_fin0 H4.
            eapply H; eauto.
            eapply DVCrev.DV2.uvalue_concat_bytes_strict_subterm; eauto.

            apply concretization_map_refine_empty.
          }

          (* all_extract_bytes_from_uvalue should agree... *)
          pose proof all_extract_bytes_from_uvalue_fin_inf uv_bytes_inf uv_bytes_fin dt Heqo.
          rewrite H1.
          break_match_hyp; cbn.
          { (* This isn't structurally recursive...
           Cannot use the induction principle H to solve this goal...

           - u is the finite uvalue we get after combining all of the uvalue bytes...
           - dv_fin is the result of concretizing that uvalue...


           That said... If all bytes are from the same uvalue...
           They should be ExtractByte values that are in
           uv_bytes_inf... And `u` should be the uvalue contained in
           that ExtractByte structure... So it should be structurally
           recursive, actually?

           Nope. Failure. ExtractByte values aren't
           concretized... Could probably change this in
           concretize_uvalueM to make the induction work better, or I
           might be able to change the induction principle a bit.
             *)

            pose proof all_extract_bytes_from_uvalue_success_inv _ _ _ Heqo0 as (?&?&?).
            subst.
            cbn in H1.
            pose proof IS1.MEM.ByteM.all_extract_bytes_from_uvalue_success_inv _ _ _ H1 as (?&?&?).
            subst.
            eapply H; eauto.
            2: apply convert_fin_to_inf_uvalue_succeeds.

            pose proof Heqo0 as SUB.
            apply all_extract_bytes_from_uvalue_strict_subterm in SUB.

            eapply uvalue_strict_subterm_fin_inf.
            apply convert_fin_to_inf_uvalue_succeeds.
            repeat red.
            cbn.
            cbn in Heqo.
            rewrite Heqo.
            reflexivity.
            auto.
          }

          repeat red in H0.
          destruct H0 as (?&?&?&?&?).
          destruct_err_ub_oom x; inv H2.
          destruct H3 as [[] | H3].
          specialize (H3 x1).
          forward H3; [cbn; auto|].
          remember (x0 x1) as x0x1.
          destruct_err_ub_oom x0x1; inv H5.

          eapply concretize_uvalue_bytes_helper_fin_inf in H0; eauto.
          3: eapply map_monad_oom_Forall2; eauto.
          3: apply concretization_map_refine_empty.

          exists (ret (fin_to_inf_dvalue_bytes x1)).
          exists (fun _ => ret (fin_to_inf_dvalue dv_fin)).
          split; eauto.
          split; eauto.
          right.
          intros a RETa.
          inv RETa.
          eapply dvalue_bytes_to_dvalue_fin_inf; eauto.
          apply dvalue_bytes_refine_fin_to_inf_dvalue_bytes.

          intros * ? ? ? ? ?.
          eapply H; eauto.
          eapply DVCrev.DV2.uvalue_concat_bytes_strict_subterm; eauto.
        }

        - (* Addresses *)
          red; intros dv_fin CONC_FIN.
          red in REF.
          cbn in REF.
          break_match_hyp_inv.
          rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
          red in CONC_FIN.
          rewrite CONCBASE.concretize_uvalueM_equation in CONC_FIN.
          cbn in CONC_FIN; inv CONC_FIN.

          rewrite IS1.MEM.CP.CONC.concretize_equation.
          red.
          rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.
          cbn.
          unfold fin_to_inf_dvalue.
          break_match_goal.
          clear Heqs; destruct p; clear e0.
          cbn in e.
          break_match_hyp_inv.
          pose proof (addr_convert_safe _ _ Heqo0).
          pose proof (AC1.addr_convert_injective _ _ _ Heqo H0); subst.
          reflexivity.
        - (* IPTR *)
          red; intros dv_fin CONC_FIN.
          red in REF.
          cbn in REF.
          break_match_hyp_inv.

          rewrite IS1.MEM.CP.CONC.concretize_equation.
          red.
          rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.
          cbn.
          unfold fin_to_inf_dvalue.
          break_match_goal.
          clear Heqs; destruct p; clear e0.
          cbn in CONC_FIN.
          inv CONC_FIN.
          cbn in e.
          break_match_hyp_inv.
          pose proof (intptr_convert_safe _ _ Heqo0).
          pose proof IP.from_Z_injective _ _ _ Heqo H0.
          apply IS1.LP.IP.to_Z_inj in H1; subst.
          reflexivity.
        - (* Undef *)
          red; intros dv_fin CONC_FIN.
          red in REF.
          cbn in REF; inv REF.

          rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
          red in CONC_FIN.
          rewrite CONCBASE.concretize_uvalueM_equation in CONC_FIN.
          cbn in CONC_FIN.

          rewrite IS1.MEM.CP.CONC.concretize_equation.
          red.
          rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.
          cbn.

          destruct CONC_FIN.
          split.
          eapply dvalue_has_dtyp_fin_to_inf_dvalue; eauto.
          eapply fin_to_inf_dvalue_not_poison; auto.
        - (* Struct *)
          red; intros dv_fin CONC_FIN.
          red in REF.
          cbn in REF.
          break_match_hyp_inv.

          unfold uvalue_concretize_fin_inf_inclusion in H.
          apply map_monad_oom_Forall2 in Heqo.

          rewrite IS1.MEM.CP.CONC.concretize_equation.
          red.
          rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

          rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
          red in CONC_FIN.
          rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.

          repeat red in CONC_FIN.
          destruct CONC_FIN as (?&?&?&?&?).
          destruct_err_ub_oom x; cbn in H1; inv H1.
          destruct H2 as [[] | H2].
          specialize (H2 x1 eq_refl).
          cbn in H2.
          rewrite <- H2 in H4.
          cbn in H4. inv H4.

          rename H0 into MAP.

          repeat red.
          exists (ret (map fin_to_inf_dvalue x1)).
          exists (fun fields => ret (DV1.DVALUE_Struct fields)).
          split.
          { eapply map_monad_ErrUbOomProp_forall2.
            apply Util.Forall2_forall.
            split.
            - rewrite length_map.

              apply map_monad_ErrUbOomProp_length in MAP.
              apply Util.Forall2_length in Heqo.
              congruence.
            - intros i a b NTH_fields NTH_res.

              epose proof Util.Forall2_Nth_left NTH_fields Heqo as (x&NTHl&CONV).

              apply Util.Nth_In in NTH_fields.
              specialize (H a).
              forward H; [constructor; constructor; auto|].
              specialize (H x CONV).

              eapply map_monad_ErrUbOomProp_forall2 in MAP.
              epose proof Util.Forall2_Nth_left NTHl MAP as (?&NTH_CONC&CONC).
              specialize (H _ CONC).

              apply Nth_map_iff in NTH_res as (?&?&?).
              subst.

              red in NTH_CONC, H1.
              rewrite H1 in NTH_CONC.
              inv NTH_CONC.
              apply H.
          }

          cbn.
          split.
          { unfold fin_to_inf_dvalue at 2.
            break_match_goal.
            clear Heqs; destruct p; clear e0.

            erewrite <- dvalue_convert_strict_struct_map; eauto.
          }

          right.
          intros a H0.
          reflexivity.
    - (* Packed structs *)
          red; intros dv_fin CONC_FIN.
          red in REF.
          cbn in REF.
          break_match_hyp_inv.

          unfold uvalue_concretize_fin_inf_inclusion in H.
          apply map_monad_oom_Forall2 in Heqo.

          rewrite IS1.MEM.CP.CONC.concretize_equation.
          red.
          rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

          rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
          red in CONC_FIN.
          rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.

          repeat red in CONC_FIN.
          destruct CONC_FIN as (?&?&?&?&?).
          destruct_err_ub_oom x; cbn in H1; inv H1.
          destruct H2 as [[] | H2].
          specialize (H2 x1 eq_refl).
          cbn in H2.
          rewrite <- H2 in H4.
          cbn in H4. inv H4.

          rename H0 into MAP.

          repeat red.
          exists (ret (map fin_to_inf_dvalue x1)).
          exists (fun fields => ret (DV1.DVALUE_Packed_struct fields)).
          split.
          { eapply map_monad_ErrUbOomProp_forall2.
            apply Util.Forall2_forall.
            split.
            - rewrite length_map.

              apply map_monad_ErrUbOomProp_length in MAP.
              apply Util.Forall2_length in Heqo.
              congruence.
            - intros i a b NTH_fields NTH_res.

              epose proof Util.Forall2_Nth_left NTH_fields Heqo as (x&NTHl&CONV).

              apply Util.Nth_In in NTH_fields.
              specialize (H a).
              forward H; [constructor; constructor; auto|].
              specialize (H x CONV).

              eapply map_monad_ErrUbOomProp_forall2 in MAP.
              epose proof Util.Forall2_Nth_left NTHl MAP as (?&NTH_CONC&CONC).
              specialize (H _ CONC).

              apply Nth_map_iff in NTH_res as (?&?&?).
              subst.

              red in NTH_CONC, H1.
              rewrite H1 in NTH_CONC.
              inv NTH_CONC.
              apply H.
          }

          cbn.
          split.
          { unfold fin_to_inf_dvalue at 2.
            break_match_goal.
            clear Heqs; destruct p; clear e0.

            erewrite <- dvalue_convert_strict_packed_struct_map; eauto.
          }

          right.
          intros a H0.
          reflexivity.
    - (* Array *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.

      unfold uvalue_concretize_fin_inf_inclusion in H.
      apply map_monad_oom_Forall2 in Heqo.

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.

      repeat red in CONC_FIN.
      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      destruct H2 as [[] | H2].
      specialize (H2 x1 eq_refl).
      cbn in H2.
      rewrite <- H2 in H4.
      cbn in H4. inv H4.

      rename H0 into MAP.

      repeat red.
      exists (ret (map fin_to_inf_dvalue x1)).
      exists (fun fields => ret (DV1.DVALUE_Array t fields)).
      split.
      { eapply map_monad_ErrUbOomProp_forall2.
        apply Util.Forall2_forall.
        split.
        - rewrite length_map.

          apply map_monad_ErrUbOomProp_length in MAP.
          apply Util.Forall2_length in Heqo.
          congruence.
        - intros i a b NTH_fields NTH_res.

          epose proof Util.Forall2_Nth_left NTH_fields Heqo as (x&NTHl&CONV).

          apply Util.Nth_In in NTH_fields.
          specialize (H a).
          forward H; [constructor; constructor; auto|].
          specialize (H x CONV).

          eapply map_monad_ErrUbOomProp_forall2 in MAP.
          epose proof Util.Forall2_Nth_left NTHl MAP as (?&NTH_CONC&CONC).
          specialize (H _ CONC).

          apply Nth_map_iff in NTH_res as (?&?&?).
          subst.

          red in NTH_CONC, H1.
          rewrite H1 in NTH_CONC.
          inv NTH_CONC.
          apply H.
      }

      cbn.
      split.
      { unfold fin_to_inf_dvalue at 2.
        break_match_goal.
        clear Heqs; destruct p; clear e0.

        erewrite <- dvalue_convert_strict_array_map; eauto.
      }

      right.
      intros a H0.
      reflexivity.
    - (* Vector *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.

      unfold uvalue_concretize_fin_inf_inclusion in H.
      apply map_monad_oom_Forall2 in Heqo.

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.

      repeat red in CONC_FIN.
      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      destruct H2 as [[] | H2].
      specialize (H2 x1 eq_refl).
      cbn in H2.
      rewrite <- H2 in H4.
      cbn in H4. inv H4.

      rename H0 into MAP.

      repeat red.
      exists (ret (map fin_to_inf_dvalue x1)).
      exists (fun fields => ret (DV1.DVALUE_Vector t fields)).
      split.
      { eapply map_monad_ErrUbOomProp_forall2.
        apply Util.Forall2_forall.
        split.
        - rewrite length_map.

          apply map_monad_ErrUbOomProp_length in MAP.
          apply Util.Forall2_length in Heqo.
          congruence.
        - intros i a b NTH_fields NTH_res.

          epose proof Util.Forall2_Nth_left NTH_fields Heqo as (x&NTHl&CONV).

          apply Util.Nth_In in NTH_fields.
          specialize (H a).
          forward H; [constructor; constructor; auto|].
          specialize (H x CONV).

          eapply map_monad_ErrUbOomProp_forall2 in MAP.
          epose proof Util.Forall2_Nth_left NTHl MAP as (?&NTH_CONC&CONC).
          specialize (H _ CONC).

          apply Nth_map_iff in NTH_res as (?&?&?).
          subst.

          red in NTH_CONC, H1.
          rewrite H1 in NTH_CONC.
          inv NTH_CONC.
          apply H.
      }

      cbn.
      split.
      { unfold fin_to_inf_dvalue at 2.
        break_match_goal.
        clear Heqs; destruct p; clear e0.

        erewrite <- dvalue_convert_strict_vector_map; eauto.
      }

      right.
      intros a H0.
      reflexivity.
    - (* IBinop *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.

      unfold uvalue_concretize_fin_inf_inclusion in H.

      pose proof (H uv_inf1) as IHuv_inf1.
      forward IHuv_inf1; [constructor; constructor; auto|].

      pose proof (H uv_inf2) as IHuv_inf2.
      forward IHuv_inf2; [constructor; constructor; auto|].

      specialize (IHuv_inf1 u Heqo).
      specialize (IHuv_inf2 u0 Heqo0).

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.

      repeat red in CONC_FIN.
      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).
      cbn in H2.
      repeat red in H2.
      destruct H2 as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H2; rewrite <- H2 in H4; inv H4.
      destruct H3 as [[] | H3].
      specialize (H3 _ eq_refl).
      rewrite <- H3 in H6, H2.

      remember (eval_iop iop x1 x3) as x1x3.
      destruct_err_ub_oom x1x3; inv H6.
      cbn in H2.

      apply IHuv_inf1 in H0.
      apply IHuv_inf2 in H1.

      repeat red.
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))).
      cbn.
      rewrite <- H2.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a H4.
      repeat red.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))).
      cbn.
      rewrite <- H3.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a0 H5.

      eapply eval_iop_fin_inf; eauto.
    - (* ICmp *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.

      unfold uvalue_concretize_fin_inf_inclusion in H.

      pose proof (H uv_inf1) as IHuv_inf1.
      forward IHuv_inf1; [constructor; constructor; auto|].

      pose proof (H uv_inf2) as IHuv_inf2.
      forward IHuv_inf2; [constructor; constructor; auto|].

      specialize (IHuv_inf1 u Heqo).
      specialize (IHuv_inf2 u0 Heqo0).

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.

      repeat red in CONC_FIN.
      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).
      cbn in H2.
      repeat red in H2.
      destruct H2 as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H2; rewrite <- H2 in H4; inv H4.
      destruct H3 as [[] | H3].
      specialize (H3 _ eq_refl).
      rewrite <- H3 in H6, H2.

      remember (eval_icmp samesign cmp x1 x3) as x1x3.
      destruct_err_ub_oom x1x3; inv H6.
      cbn in H2.

      apply IHuv_inf1 in H0.
      apply IHuv_inf2 in H1.

      repeat red.
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))).
      cbn.
      rewrite <- H2.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a H4.
      repeat red.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))).
      cbn.
      rewrite <- H3.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a0 H5.

      eapply eval_icmp_fin_inf; eauto.
    - (* FBinop *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.

      unfold uvalue_concretize_fin_inf_inclusion in H.

      pose proof (H uv_inf1) as IHuv_inf1.
      forward IHuv_inf1; [constructor; constructor; auto|].

      pose proof (H uv_inf2) as IHuv_inf2.
      forward IHuv_inf2; [constructor; constructor; auto|].

      specialize (IHuv_inf1 u Heqo).
      specialize (IHuv_inf2 u0 Heqo0).


      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.

      repeat red in CONC_FIN.
      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).
      cbn in H2.
      repeat red in H2.
      destruct H2 as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H2; rewrite <- H2 in H4; inv H4.
      destruct H3 as [[] | H3].
      specialize (H3 _ eq_refl).
      rewrite <- H3 in H6, H2.

      remember (eval_fop fop x1 x3) as x1x3.
      destruct_err_ub_oom x1x3; inv H6.
      cbn in H2.

      apply IHuv_inf1 in H0.
      apply IHuv_inf2 in H1.

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      
      repeat red.
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))).
      cbn.
      rewrite <- H2.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a H4.
      repeat red.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))).
      cbn.
      rewrite <- H3.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a0 H5.

      eapply eval_fop_fin_inf; eauto.

    - (* Fneg *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      unfold uvalue_concretize_fin_inf_inclusion in H.
      
      pose proof (H uv_inf) as IHuv_inf.
      forward IHuv_inf; [constructor; constructor; auto|].

      specialize (IHuv_inf u Heqo).

      
      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.
      cbn in CONC_FIN.
      repeat red in CONC_FIN. 

      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).
      
      apply IHuv_inf in H0.
      rewrite <- H2 in H4.
      remember (eval_fneg x1) as x1h.
      destruct_err_ub_oom x1h; inv H4.

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.
      cbn.
      repeat red.
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))).
      rewrite <- H2.
      cbn.
      split; eauto.
      split; eauto.
      right.
      intros a0 H4.
      rewrite <- H4.
      eapply eval_fneg_fin_inf; eauto.
      
    - (* fcmp *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.

      unfold uvalue_concretize_fin_inf_inclusion in H.

      pose proof (H uv_inf1) as IHuv_inf1.
      forward IHuv_inf1; [constructor; constructor; auto|].

      pose proof (H uv_inf2) as IHuv_inf2.
      forward IHuv_inf2; [constructor; constructor; auto|].

      specialize (IHuv_inf1 u Heqo).
      specialize (IHuv_inf2 u0 Heqo0).

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.

      repeat red in CONC_FIN.
      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).
      cbn in H2.
      repeat red in H2.
      destruct H2 as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H2; rewrite <- H2 in H4; inv H4.
      destruct H3 as [[] | H3].
      specialize (H3 _ eq_refl).
      rewrite <- H3 in H6, H2.

      remember (eval_fcmp cmp x1 x3) as x1x3.
      destruct_err_ub_oom x1x3; inv H6.
      cbn in H2.

      apply IHuv_inf1 in H0.
      apply IHuv_inf2 in H1.

      repeat red.
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))).
      cbn.
      rewrite <- H2.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a H4.
      repeat red.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))).
      cbn.
      rewrite <- H3.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a0 H5.

      eapply eval_fcmp_fin_inf; eauto.
    - (* Conversion *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.

      rename H into IH.
      pose proof (IH uv_inf) as IHuv_inf.
      forward IHuv_inf; [constructor; constructor; auto|].

      specialize (IHuv_inf _ Heqo).
      unfold uvalue_concretize_fin_inf_inclusion in IHuv_inf.

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.

      repeat red in CONC_FIN.
      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H0; inv H0.
      destruct H1 as [[] | H1].
      specialize (H1 _ eq_refl).
      cbn in H1.

      specialize (IHuv_inf _ H).
      repeat red.
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => (fmap fin_to_inf_dvalue (x0 x1))).
      cbn; rewrite H3; cbn.
      split; eauto.
      split; eauto.

      right; intros ? ?; subst.
      break_match_hyp.
      { (* Conv_Pure *)
        pose proof get_conv_case_pure_fin_inf _ _ _ _ _ Heqc as CONV.
        rewrite CONV.
        remember (x0 x1) as x0x1.
        destruct_err_ub_oom x0x1; inv H3.
        inv H1; auto.
      }

      { (* Conv_ItoP *)
        break_match_hyp;
          rewrite <- H1 in H3; inv H3.

        pose proof get_conv_case_itop_fin_inf _ _ _ _ _ Heqc as CONV.
        rewrite CONV.
        cbn.

        erewrite dvalue_int_unsigned_E1E2;
          [|apply fin_to_inf_dvalue_refine_strict].

        erewrite int_to_ptr_fin_inf_wildcard; eauto.
        rewrite_fin_to_inf_dvalue; reflexivity.

        unfold fin_to_inf_addr.
        break_match_goal; clear Heqs; auto.
      }

      { (* Conv_PtoI *)
        remember (x0 x1) as x0x1.
        destruct_err_ub_oom x0x1; inv H3.
        break_match_hyp; try inv H1.
        pose proof get_conv_case_ptoi_fin_inf _ _ _ _ _ Heqc as CONV.
        break_match_hyp_inv.
        { repeat break_match_hyp_inv;
            rewrite CONV; rewrite_fin_to_inf_dvalue;
            rewrite ptr_to_int_fin_to_inf_addr; auto.
        }

        remember (lift_OOM (mrepr (PTOI.ptr_to_int a))) as ptoi.
        destruct_err_ub_oom ptoi; cbn in H2; inv H2.
        rewrite CONV; rewrite_fin_to_inf_dvalue.
        erewrite ptr_to_int_fin_to_inf_addr; eauto.
        destruct (mrepr (PTOI.ptr_to_int a)) eqn:HREPR; inv Heqptoi.
        erewrite VMEM_REF.mrepr_refine with (x_inf:=(intptr_fin_inf i)).
        3: apply HREPR.
        2: {
          unfold intptr_fin_inf.
          break_match_goal.
          clear Heqs.
          eapply intptr_convert_safe in e.
          erewrite IP.from_Z_to_Z; eauto.
        }
        cbn.
        reflexivity.
      }

      { (* Conv_Oom *)
        exfalso.
        rewrite <- H1 in H3; inv H3.
      }

      { (* Conv_Illegal *)
        exfalso.
        rewrite <- H1 in H3; inv H3.
      }
    - (* GetElementPtr *)
      rename H into IH.
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.

      pose proof (IH uv_inf) as IHuv_inf.
      forward IHuv_inf; [constructor; constructor; auto|].

      pose proof (IHuv_inf u Heqo) as IHuv_inf_u.
      unfold uvalue_concretize_fin_inf_inclusion in IHuv_inf_u.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.

      repeat red in CONC_FIN.
      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H0; inv H0.
      destruct H1 as [[] | H1].
      specialize (H1 _ eq_refl).
      cbn in H1.
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; rewrite <- H1 in H3; inv H3.
      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).
      break_match_hyp; try rewrite <- H2 in H5; inv H5.
      break_match_hyp; try rewrite <- H2 in H4; inv H4.
      rewrite <- H2 in H1; cbn in H1.

      specialize (IHuv_inf_u _ H).
      destruct x1; cbn in Heqs; inv Heqs.
      break_match_hyp_inv.
      break_match_hyp_inv.

      pose proof addr_convert_succeeds a as (a'&AA').
      pose proof addr_convert_succeeds a0 as (a0'&A0A0').
      epose proof (handle_gep_addr_fin_inf _ _ _ _ _ _ _ Heqs AA' A0A0' eq_refl).

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red.
      exists (ret (fin_to_inf_dvalue (DVALUE_Addr a))).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 (DVALUE_Addr a)))).
      rewrite <- H1.
      split; eauto.
      split; cbn; eauto.

      right.
      intros a1 ?; subst.
      repeat red.
      exists (ret (fmap fin_to_inf_dvalue x3)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))).
      cbn.
      split; eauto.
      { clear - IH H0 Heqo0.
        rename IH into H.
        apply map_monad_oom_Forall2 in Heqo0.
        generalize dependent x3.
        induction Heqo0; intros x3 H1.
        - cbn in *; inv H1; cbn; auto.
        - forward IHHeqo0.
          { intros idx H2 uv_fin H3.
            eapply H; eauto.
            eapply DV1.uvalue_strict_subterm_inv in H2
                as (?&?&?).
            inv H2.
            - eapply clos_rt_t; [apply H4|].
              constructor; constructor; auto.
            - eapply clos_rt_t; [apply H4|].
              constructor.
              eapply DV1.UVALUE_GetElementPtr_subterm_idxs.
              right; auto.
          }

          rewrite map_monad_unfold in H1.
          repeat red in H1.
          destruct H1 as (?&?&?&?&?).
          destruct_err_ub_oom x0; inv H2.
          destruct H3 as [[] | H3].
          specialize (H3 _ eq_refl).

          repeat red in H3.
          destruct H3 as (?&?&?&?&?).
          rewrite <- H3 in H5.
          destruct_err_ub_oom x0; inv H5.

          destruct H4 as [[] | H4].
          specialize (H4 _ eq_refl).
          cbn in H4.

          rewrite <- H4 in H7; inv H7.
          cbn in H3; rewrite <- H4 in H3; inv H3.

          specialize (IHHeqo0 _ H2).
          rewrite map_monad_unfold.
          repeat red.

          pose proof (H x).
          forward H3.
          constructor.
          eapply DV1.UVALUE_GetElementPtr_subterm_idxs; left; eauto.
          specialize (H3 _ H0 _ H1).

          exists (ret (fin_to_inf_dvalue x2)).
          exists (fun dv_inf => fmap (fmap fin_to_inf_dvalue) (x1 x2)).

          cbn; rewrite <- H6; cbn.
          split; eauto.
          split; eauto.

          right.
          intros a ?; subst.
          repeat red.
          exists (ret (fmap fin_to_inf_dvalue x5)).
          exists (fun dv_inf => (fmap (fmap fin_to_inf_dvalue) (x4 x5))).

          cbn; rewrite <- H4; cbn.
          split; eauto.
          split; eauto.

          right.
          intros a ?; subst.
          auto.
      }

      cbn; rewrite <- H2; cbn.
      split; eauto.

      right.
      intros a1 ?; subst.
      unfold fin_to_inf_dvalue at 1.
      break_inner_match_goal; clear Heqs0; destruct p; clear e0.
      cbn in e.
      rewrite AA' in e.
      inv e.
      cbn.

      replace (map fin_to_inf_dvalue x3) with (fmap fin_to_inf_dvalue x3) in H3 by reflexivity.
      cbn in H3.
      rewrite H3.

      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs0; destruct p; clear e0.
      cbn in e.
      rewrite A0A0' in e.
      inv e.
      reflexivity.
    - (* ExtractElement *)
      rename H into IH.
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.

      pose proof (IH uv_inf1) as IHuv_inf1.
      forward IHuv_inf1; [constructor; constructor; auto|].

      pose proof (IH uv_inf2) as IHuv_inf2.
      forward IHuv_inf2; [constructor; constructor; auto|].

      pose proof (IHuv_inf1 u Heqo) as IHuv_inf_u.
      pose proof (IHuv_inf2 u0 Heqo0) as IHuv_inf_u0.

      unfold uvalue_concretize_fin_inf_inclusion in IHuv_inf_u, IHuv_inf_u0.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.

      repeat red in CONC_FIN.
      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      destruct H1 as [[] | H1].
      specialize (H1 _ eq_refl).
      cbn in H1.
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; rewrite <- H1 in H3; inv H3.
      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).

      repeat red in H2.
      destruct H2 as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H3; rewrite <- H3 in H5; inv H5.
      destruct H4 as [[] | H4].
      specialize (H4 _ eq_refl).

      remember (x4 x5) as x4x5.
      destruct_err_ub_oom x4x5; inv H7.
      cbn in H3.
      rewrite <- H3 in H1.
      cbn in H1.

      break_match_hyp_inv.

      specialize (IHuv_inf_u _ H).
      specialize (IHuv_inf_u0 _ H0).

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red.
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))).
      cbn.
      rewrite <- H1.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a ?; subst.
      repeat red.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))).
      cbn; rewrite <- H3; cbn.
      split; eauto.
      split; eauto.

      right.
      intros a ?; subst.
      repeat red.
      exists (ret x5).
      exists (fun x5 => fmap fin_to_inf_dvalue (x4 x5)).
      cbn; rewrite <- Heqx4x5; cbn.
      split; eauto.
      split; eauto.

      right.
      intros a ?; subst.
      cbn; rewrite <- Heqx4x5; cbn.

      eapply index_into_vec_dv_fin_inf; eauto.
    - (* InsertElement *)
      rename H into IH.
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.
      break_match_hyp_inv.

      pose proof (IH uv_inf1) as IHuv_inf1.
      forward IHuv_inf1; [constructor; constructor; auto|].

      pose proof (IH uv_inf2) as IHuv_inf2.
      forward IHuv_inf2; [constructor; constructor; auto|].

      pose proof (IH uv_inf3) as IHuv_inf3.
      forward IHuv_inf3; [constructor; constructor; auto|].

      pose proof (IHuv_inf1 u Heqo) as IHuv_inf_u.
      pose proof (IHuv_inf2 u0 Heqo0) as IHuv_inf_u0.
      pose proof (IHuv_inf3 u1 Heqo1) as IHuv_inf_u1.

      unfold uvalue_concretize_fin_inf_inclusion in IHuv_inf_u, IHuv_inf_u0, IHuv_inf_u1.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.

      repeat red in CONC_FIN.
      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      destruct H1 as [[] | H1].
      specialize (H1 _ eq_refl).
      cbn in H1.

      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; rewrite <- H1 in H3; inv H3.
      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).

      repeat red in H2.
      destruct H2 as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H3; rewrite <- H3 in H5; inv H5.
      destruct H4 as [[] | H4].
      specialize (H4 _ eq_refl).

      remember (x4 x5) as x4x5.
      destruct_err_ub_oom x4x5; inv H7.
      cbn in H3.
      rewrite <- H3 in H1.
      cbn in H1.

      specialize (IHuv_inf_u _ H).
      specialize (IHuv_inf_u0 _ H2).
      specialize (IHuv_inf_u1 _ H0).

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red.
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))).
      cbn.
      rewrite <- H1.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a ?; subst.
      repeat red.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))).
      cbn; rewrite <- H3; cbn.
      split; eauto.
      split; eauto.

      right.
      intros a ?; subst.
      repeat red.
      exists (ret (fin_to_inf_dvalue x5)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x4 x5))).
      cbn; rewrite <- Heqx4x5; cbn.
      split; eauto.
      split; eauto.

      right.
      intros a ?; subst.

      eapply insert_into_vec_dv_fin_inf; eauto.
    - (* ShuffleVector *)
      rename H into IH.
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.
      break_match_hyp_inv.

      pose proof (IH uv_inf1) as IHuv_inf1.
      forward IHuv_inf1; [constructor; constructor; auto|].

      pose proof (IH uv_inf2) as IHuv_inf2.
      forward IHuv_inf2; [constructor; constructor; auto|].

      pose proof (IH uv_inf3) as IHuv_inf3.
      forward IHuv_inf3; [constructor; constructor; auto|].

      pose proof (IHuv_inf1 u Heqo) as IHuv_inf_u.
      pose proof (IHuv_inf2 u0 Heqo0) as IHuv_inf_u0.
      pose proof (IHuv_inf3 u1 Heqo1) as IHuv_inf_u1.

      unfold uvalue_concretize_fin_inf_inclusion in IHuv_inf_u, IHuv_inf_u0, IHuv_inf_u1.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.
      inv CONC_FIN.
    - (* ExtractValue *)
      rename H into IH.
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.
      cbn in CONC_FIN.
      repeat red in CONC_FIN.

      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      destruct H1 as [[] | H1].
      specialize (H1 _ eq_refl).

      remember (x0 x1) as x0x1.
      destruct_err_ub_oom x0x1; inv H3.
      apply extract_value_loop_fin_inf_succeeds in H1.

      rewrite IS1.MEM.CP.CONC.concretize_equation;
        red; rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation;
        cbn; repeat red.

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))).
      cbn; rewrite <- Heqx0x1; cbn.
      split.
      eapply IH; eauto.
      constructor; constructor; auto.
      split; eauto.

      right.
      intros a ?; subst.
      auto.
    - (* InsertValue *)
      rename H into IH.
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.

      pose proof (IH uv_inf1) as IHuv_inf1.
      forward IHuv_inf1; [constructor; constructor; auto|].

      pose proof (IH uv_inf2) as IHuv_inf2.
      forward IHuv_inf2; [constructor; constructor; auto|].

      pose proof (IHuv_inf1 u Heqo) as IHuv_inf_u.
      pose proof (IHuv_inf2 u0 Heqo0) as IHuv_inf_u0.
      red in IHuv_inf_u, IHuv_inf_u0.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.
      cbn in CONC_FIN.

      repeat red in CONC_FIN.
      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      destruct H1 as [[] | H1].
      specialize (H1 _ eq_refl).

      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.
      cbn in H1.
      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).

      specialize (IHuv_inf_u _ H).
      specialize (IHuv_inf_u0 _ H0).

      rewrite IS1.MEM.CP.CONC.concretize_equation;
        red; rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation;
        cbn; repeat red.

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))).
      cbn; rewrite <- H1, H5; cbn.
      split; eauto.
      split; eauto.

      right.
      intros a ?; subst.
      repeat red.

      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))).
      cbn; rewrite H5; cbn.
      split; eauto.
      split; eauto.

      right.
      intros a ?; subst.
      eapply insert_value_loop_fin_inf_succeeds in H2.
      setoid_rewrite H2.
      remember (x2 x3) as x2x3.
      destruct_err_ub_oom x2x3; inv H5.
      reflexivity.
    - (* Select *)
      rename H into IH.
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.
      break_match_hyp_inv.

      pose proof (IH uv_inf1) as IHuv_inf1.
      forward IHuv_inf1; [constructor; constructor; auto|].

      pose proof (IH uv_inf2) as IHuv_inf2.
      forward IHuv_inf2; [constructor; constructor; auto|].

      pose proof (IH uv_inf3) as IHuv_inf3.
      forward IHuv_inf3; [constructor; constructor; auto|].

      pose proof (IHuv_inf1 u Heqo) as IHuv_inf_u.
      pose proof (IHuv_inf2 u0 Heqo0) as IHuv_inf_u0.
      pose proof (IHuv_inf3 u1 Heqo1) as IHuv_inf_u1.
      red in IHuv_inf_u, IHuv_inf_u0, IHuv_inf_u1.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.
      cbn in CONC_FIN.

      repeat red in CONC_FIN.
      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      destruct H1 as [[] | H1].
      specialize (H1 _ eq_refl).

      remember (x0 x1) as x0x1.
      destruct_err_ub_oom x0x1; inv H3.
      pose proof eval_select_fin_inf x1 u0 u1 _ _ dv_fin IHuv_inf_u0 IHuv_inf_u1 as EVAL.
      forward EVAL.
      { cbn.
        rewrite eval_select_equation.
        apply H1.
      }

      rewrite IS1.MEM.CP.CONC.concretize_equation;
        red; rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation;
        cbn; repeat red.

      specialize (IHuv_inf_u _ H).

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))).
      split; eauto.
      split; cbn; rewrite <- Heqx0x1; cbn; eauto.

      right.
      intros a ?; subst.
      rewrite IS1.MEM.CP.CONC.eval_select_equation in EVAL.
      apply EVAL.
    - (* ExtractByte *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      cbn in *.
      inv CONC_FIN.
      }
  Qed.

  (* Couldn't put this in LangRefine/Select.v because of dependency on concretization. *)
  Lemma eval_select_ub_fin_inf :
    forall cond uv1_fin uv2_fin uv1_inf uv2_inf ub_msg
      (IH1 : forall ub_msg,
          IS2.MEM.CP.CONC.concretize_u uv1_fin (UB_unERR_UB_OOM ub_msg) ->
          IS1.MEM.CP.CONC.concretize_u uv1_inf (UB_unERR_UB_OOM ub_msg))
      (IH2 : forall ub_msg,
          IS2.MEM.CP.CONC.concretize_u uv2_fin (UB_unERR_UB_OOM ub_msg) ->
          IS1.MEM.CP.CONC.concretize_u uv2_inf (UB_unERR_UB_OOM ub_msg)),
      uvalue_refine_strict uv1_inf uv1_fin ->
      uvalue_refine_strict uv2_inf uv2_fin ->
      @IS2.MEM.CP.CONC.eval_select ErrUbOomProp Monad_ErrUbOomProp
        (fun (dt : dtyp) (edv : err_ub_oom dvalue) =>
           match unERR_UB_OOM edv with
           | {|
               EitherMonad.unEitherT :=
                 {|
                   EitherMonad.unEitherT :=
                     {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |}
                 |}
             |} => dvalue_has_dtyp dv dt /\ dv <> DVALUE_Poison dt
           | _ => True
           end) err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (fun (A : Type) (x ue : err_ub_oom A) => x = ue) cond uv1_fin uv2_fin (UB_unERR_UB_OOM ub_msg) ->
      @IS1.MEM.CP.CONC.eval_select ErrUbOomProp Monad_ErrUbOomProp
        (fun (dt : dtyp) (edv : err_ub_oom DVCrev.DV2.dvalue) =>
           match unERR_UB_OOM edv with
           | {|
               EitherMonad.unEitherT :=
                 {|
                   EitherMonad.unEitherT :=
                     {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |}
                 |}
             |} => DV1.dvalue_has_dtyp dv dt /\ dv <> DV1.DVALUE_Poison dt
           | _ => True
           end) err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (fun (A : Type) (x ue : err_ub_oom A) => x = ue) (fin_to_inf_dvalue cond) uv1_inf uv2_inf (UB_unERR_UB_OOM ub_msg).
  Proof.
    intros cond uv1_fin uv2_fin uv1_inf uv2_inf ub_msg IH1 IH2 REF1 REF2 EVAL.
    destruct cond.
    { unfold fin_to_inf_dvalue at 1.
      break_match_goal; clear Heqs; destruct p; clear e0;
      cbn in e; break_match_hyp_inv;
        cbn in *; subst; cbn in *; auto; inv EVAL.
    }

    { (* i1 conditional *)
      rewrite IS2.MEM.CP.CONC.eval_select_equation in *.
      rewrite IS1.MEM.CP.CONC.eval_select_equation.
      rewrite fin_to_inf_dvalue_ix.

      break_match; try inv EVAL.
      break_match.
      - eapply IH1; eauto.
      - eapply IH2; eauto.
    }

    all: try solve
           [ unfold fin_to_inf_dvalue at 1;
             break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e;
             cbn in *; subst; cbn in *; inv EVAL; auto
           | unfold fin_to_inf_dvalue at 1;
             break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e;
             cbn in *; subst; cbn in *; reflexivity
           | unfold fin_to_inf_dvalue at 1;
             break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; break_match_hyp_inv;
             cbn in *; subst; cbn in *; auto; inv EVAL
           ].

    { (* Vector conditional *)
      rewrite IS2.MEM.CP.CONC.eval_select_equation in *.
      rewrite IS1.MEM.CP.CONC.eval_select_equation.

      rewrite_fin_to_inf_dvalue.
      repeat red.

      repeat red in EVAL.
      destruct EVAL as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { clear H1.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        eapply IH1; eauto.
      }

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).
      split.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.
      intros a ?; subst.
      repeat red.

      destruct H1 as [[] | H1].
      specialize (H1 _ eq_refl).
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { clear H2.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        eapply IH2; eauto.
      }

      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).
      split.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.
      intros a ?; subst.

      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).

      destruct x1;
        try (rewrite <- H2 in H5; inv H5).

      destruct x3;
        try (rewrite <- H2 in H5; inv H5).
      rewrite_fin_to_inf_dvalue.

      repeat red in H2.
      repeat red.

      destruct H2 as (?&?&?&?&?).
      rewrite <- H3 in H5.
      destruct_err_ub_oom x; inv H5.
      { exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        pose proof eval_select_loop_fin_inf elts elts0 elts1 (UB_unERR_UB_OOM ub_msg) as LOOP.
        specialize (LOOP H2).
        auto.
      }

      destruct H4 as [[] | H4].
      specialize (H4 _ eq_refl).
      cbn in H4.
      rewrite <- H4 in H7; inv H7.
    }
  Qed.

  (* Couldn't put this in LangRefine/Select.v because of dependency on concretization. *)
  Lemma eval_select_err_fin_inf :
    forall cond uv1_fin uv2_fin uv1_inf uv2_inf msg
      (IH1 : forall msg,
          IS2.MEM.CP.CONC.concretize_u uv1_fin (ERR_unERR_UB_OOM msg) ->
          IS1.MEM.CP.CONC.concretize_u uv1_inf (ERR_unERR_UB_OOM msg))
      (IH2 : forall msg,
          IS2.MEM.CP.CONC.concretize_u uv2_fin (ERR_unERR_UB_OOM msg) ->
          IS1.MEM.CP.CONC.concretize_u uv2_inf (ERR_unERR_UB_OOM msg)),
      uvalue_refine_strict uv1_inf uv1_fin ->
      uvalue_refine_strict uv2_inf uv2_fin ->
      @eval_select ErrUbOomProp Monad_ErrUbOomProp
        (fun (dt : dtyp) (edv : err_ub_oom dvalue) =>
           match unERR_UB_OOM edv with
           | {|
               EitherMonad.unEitherT :=
                 {|
                   EitherMonad.unEitherT :=
                     {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |}
                 |}
             |} => dvalue_has_dtyp dv dt /\ dv <> DVALUE_Poison dt
           | _ => True
           end) err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (fun (A : Type) (x ue : err_ub_oom A) => x = ue) cond uv1_fin uv2_fin (ERR_unERR_UB_OOM msg) ->
      @IS1.MEM.CP.CONC.eval_select ErrUbOomProp Monad_ErrUbOomProp
        (fun (dt : dtyp) (edv : err_ub_oom DVCrev.DV2.dvalue) =>
           match unERR_UB_OOM edv with
           | {|
               EitherMonad.unEitherT :=
                 {|
                   EitherMonad.unEitherT :=
                     {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |}
                 |}
             |} => DV1.dvalue_has_dtyp dv dt /\ dv <> DV1.DVALUE_Poison dt
           | _ => True
           end) err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (fun (A : Type) (x ue : err_ub_oom A) => x = ue) (fin_to_inf_dvalue cond) uv1_inf uv2_inf (ERR_unERR_UB_OOM msg).
  Proof.
    intros cond uv1_fin uv2_fin uv1_inf uv2_inf msg IH1 IH2 REF1 REF2 EVAL.
    destruct cond.
    { unfold fin_to_inf_dvalue at 1.
      break_match_goal; clear Heqs; destruct p; clear e0;
      cbn in e; break_match_hyp_inv;
        cbn in *; subst; cbn in *; auto; inv EVAL; auto.
    }

    { (* integer conditional *)
      rewrite eval_select_equation in *.
      rewrite IS1.MEM.CP.CONC.eval_select_equation.
      rewrite fin_to_inf_dvalue_ix.

      repeat break_match_hyp; cbn in *;
        try inv EVAL; auto.
      - eapply IH1; eauto.
      - eapply IH2; eauto.
    }

    all: try solve
           [ unfold fin_to_inf_dvalue at 1;
             break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e;
             cbn in *; subst; cbn in *; inv EVAL; auto
           | unfold fin_to_inf_dvalue at 1;
             break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e;
             cbn in *; subst; cbn in *; reflexivity
           | unfold fin_to_inf_dvalue at 1;
             break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; break_match_hyp_inv;
             cbn in *; subst; cbn in *; auto; inv EVAL; auto
           ].

    { (* Vector conditional *)
      rewrite eval_select_equation in *.
      rewrite IS1.MEM.CP.CONC.eval_select_equation.

      rewrite_fin_to_inf_dvalue.
      repeat red.

      repeat red in EVAL.
      destruct EVAL as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { clear H1.
        exists (ERR_unERR_UB_OOM msg).
        exists (fun _ => ERR_unERR_UB_OOM msg).
        split; cbn; eauto.
        eapply IH1; eauto.
      }

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => ERR_unERR_UB_OOM msg).
      split.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.
      intros a ?; subst.
      repeat red.

      destruct H1 as [[] | H1].
      specialize (H1 _ eq_refl).
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { clear H2.
        exists (ERR_unERR_UB_OOM msg).
        exists (fun _ => ERR_unERR_UB_OOM msg).
        split; cbn; eauto.
        eapply IH2; eauto.
      }

      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => ERR_unERR_UB_OOM msg).
      split.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.
      intros a ?; subst.

      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).

      destruct x1;
        try (rewrite <- H2 in H5; inv H5);
        rewrite_fin_to_inf_dvalue; auto.

      destruct x3;
        try (rewrite <- H2 in H5; inv H5);
        rewrite_fin_to_inf_dvalue; auto.

      repeat red in H2.
      repeat red.

      destruct H2 as (?&?&?&?&?).
      rewrite <- H3 in H5.
      destruct_err_ub_oom x; inv H5.
      { exists (ERR_unERR_UB_OOM msg).
        exists (fun _ => ERR_unERR_UB_OOM msg).
        split; cbn; eauto.
        pose proof eval_select_loop_fin_inf elts elts0 elts1 (ERR_unERR_UB_OOM msg) as LOOP.
        specialize (LOOP H2).
        auto.
      }

      destruct H4 as [[] | H4].
      specialize (H4 _ eq_refl).
      cbn in H4.
      rewrite <- H4 in H7; inv H7.
    }
  Qed.

  (* Could be the case that OOM happens...

     If uv_inf is an IBinop, for instance...

     64_bit_intmax + 1

     Then the infinite concretization will produce a value, but the
     finite concretization should OOM.
   *)
  Lemma concretize_inf_excluded_middle :
    forall uv_fin,
      (exists dv_fin,
          IS2.LLVM.MEM.CP.CONC.concretize uv_fin dv_fin) \/
          (* Should actually only be OOM in concretization... *)
          (forall dv_fin, ~ IS2.LLVM.MEM.CP.CONC.concretize uv_fin dv_fin).
  Proof.
    intros uv_fin.
    assert ((exists dv_fin : dvalue, concretize uv_fin dv_fin) \/ (~ exists dv_fin : dvalue, concretize uv_fin dv_fin)).
    apply Classical_Prop.classic.
    destruct H; auto.
    right.
    apply not_ex_all_not; eauto.
  Qed.

  Lemma concretize_fails_inf_fin :
    forall uv_inf uv_fin
      (REF : uvalue_refine_strict uv_inf uv_fin)
      (FAILS : forall dv : DV1.dvalue, ~ IS1.LLVM.MEM.CP.CONC.concretize uv_inf dv),
    forall dv : dvalue, ~ concretize uv_fin dv.
  Proof.
    intros uv_inf uv_fin REF FAILS dv CONC.
    eapply FAILS.
    eapply uvalue_concretize_strict_concretize_inclusion; eauto.
  Qed.

  Lemma concretize_uvalue_bytes_helper_ub_fin_inf :
    forall uvs_inf uvs_fin acc_inf acc_fin ub_msg
      (IH : forall (u : DV1.uvalue),
          Exists (DV1.uvalue_subterm u) uvs_inf ->
          forall uv_fin : DV2.uvalue,
            uvalue_refine_strict u uv_fin ->
            forall ub_msg,
              IS2.MEM.CP.CONC.concretize_u uv_fin (UB_unERR_UB_OOM ub_msg) ->
              IS1.MEM.CP.CONC.concretize_u u (UB_unERR_UB_OOM ub_msg)),
      Forall2 uvalue_refine_strict uvs_inf uvs_fin ->
      concretization_map_refine acc_inf acc_fin ->
      @concretize_uvalue_bytes_helper ErrUbOomProp Monad_ErrUbOomProp
        (fun (dt : dtyp) (edv : err_ub_oom dvalue) =>
           match @unERR_UB_OOM IdentityMonad.ident dvalue edv with
           | {|
               EitherMonad.unEitherT :=
                 {|
                   EitherMonad.unEitherT :=
                     {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |}
                 |}
             |} => dvalue_has_dtyp dv dt /\ dv <> DVALUE_Poison dt
           | _ => True
           end) err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (fun (A : Type) (x ue : err_ub_oom A) => x = ue) acc_fin uvs_fin (UB_unERR_UB_OOM ub_msg) ->
      @IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalue_bytes_helper ErrUbOomProp Monad_ErrUbOomProp
        (fun (dt0 : dtyp) (edv : err_ub_oom DV1.dvalue) =>
           match @unERR_UB_OOM IdentityMonad.ident DV1.dvalue edv with
           | {|
               EitherMonad.unEitherT :=
                 {|
                   EitherMonad.unEitherT :=
                     {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |}
                 |}
             |} => DV1.dvalue_has_dtyp dv dt0 /\ dv <> DV1.DVALUE_Poison dt0
           | _ => True
           end) err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (fun (A : Type) (x ue : err_ub_oom A) => x = ue) acc_inf uvs_inf (UB_unERR_UB_OOM ub_msg).
  Proof.
    (* Will need something about acc_inf and acc_fin *)
    induction uvs_inf;
      intros uvs_fin acc_inf acc_fin ub_msg IH REF ACC_REF CONC.
    - inv REF.
      cbn in CONC; inv CONC; cbn.
    - inv REF.
      rewrite concretize_uvalue_bytes_helper_equation in CONC.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalue_bytes_helper_equation.
      destruct y; uvalue_refine_strict_inv H1; try inv CONC.
      rewrite pre_concretized_fin_inf with (uv_fin:=y) (acc_fin:=acc_fin); eauto.
      break_match_hyp_inv; repeat red.
      + (* pre-concretization exists *)
        destruct H as (?&?&?&?).
        destruct_err_ub_oom x0; inv H1.
        { exists (UB_unERR_UB_OOM ub_msg).
          exists (fun _ => UB_unERR_UB_OOM ub_msg).
          split; cbn; eauto.
        }

        destruct H2 as [[] | H2].
        specialize (H2 x2).
        forward H2; [cbn; auto|].
        rewrite <- H2 in H5.
        inv H5.
      + (* No pre-concretization exists *)
        destruct H as (?&?&?&?).
        destruct_err_ub_oom x0; inv H1.
        { exists (UB_unERR_UB_OOM ub_msg).
          exists (fun _ => UB_unERR_UB_OOM ub_msg).
          split; cbn; eauto.
          eapply IH; eauto.
          repeat constructor.
        }

        exists (ret (fin_to_inf_dvalue x2)).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        split; cbn; eauto.
        right.
        intros ? ?; subst.
        repeat red.

        destruct H2 as [[] | H2].
        specialize (H2 x2).
        forward H2; [cbn; auto|].
        cbn in H2.
        repeat red in H2.
        destruct H2 as (?&?&?&?&?).
        rewrite <- H2 in H5.
        destruct_err_ub_oom x0; inv H5.
        { exists (UB_unERR_UB_OOM ub_msg).
          exists (fun _ => UB_unERR_UB_OOM ub_msg).
          split; cbn; eauto.
          eapply IHuvs_inf; eauto.
          eapply concretize_map_refine_new_concretized_byte_fin_inf; eauto.
          eapply fin_to_inf_dvalue_refine_strict.
        }

        exists (ret (fin_to_inf_dvalue_bytes x4)).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split.
        eapply concretize_uvalue_bytes_helper_fin_inf; eauto.
        intros u H5 uv_fin H6 dv_fin H8.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        eapply concretize_map_refine_new_concretized_byte_fin_inf; eauto.
        eapply fin_to_inf_dvalue_refine_strict.

        destruct H4 as [[] | H4].
        specialize (H4 x4).
        forward H4; [cbn; auto|].
        rewrite <- H4 in H7.
        inv H7.
  Qed.

  (* Lemma concretize_uvalue_bytes_ub_fin_inf : *)
  (*   forall uvs_inf uvs_fin ub_msg *)
  (*     (IH : forall (u : DV1.uvalue), *)
  (*         Exists (DV1.uvalue_subterm u) uvs_inf -> *)
  (*         forall uv_fin : DV2.uvalue, *)
  (*           uvalue_refine_strict u uv_fin -> *)
  (*           forall ub_msg, *)
  (*             IS2.MEM.CP.CONC.concretize_u uv_fin (UB_unERR_UB_OOM ub_msg) -> *)
  (*             IS1.MEM.CP.CONC.concretize_u u (UB_unERR_UB_OOM ub_msg)), *)
  (*     Forall2 uvalue_refine_strict uvs_inf uvs_fin -> *)
  (*     @concretize_uvalue_bytes ErrUbOomProp Monad_ErrUbOomProp *)
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
  (*       (fun (A : Type) (x ue : err_ub_oom A) => x = ue) uvs_fin (UB_unERR_UB_OOM ub_msg) -> *)
  (*     @IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalue_bytes ErrUbOomProp Monad_ErrUbOomProp *)
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
  (*       (fun (A : Type) (x ue : err_ub_oom A) => x = ue) uvs_inf (UB_unERR_UB_OOM ub_msg). *)
  (* Proof. *)
  (*   intros uvs_inf uvs_fin ub_msg IH REF CONC. *)
  (*   rewrite concretize_uvalue_bytes_equation in CONC. *)
  (*   rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalue_bytes_equation. *)
  (*   eapply concretize_uvalue_bytes_helper_ub_fin_inf; eauto. *)
  (*   eapply concretization_map_refine_empty. *)
  (* Qed. *)


  Lemma concretize_ub_fin_inf :
    forall uv_inf uv_fin ub_msg
      (REF : uvalue_refine_strict uv_inf uv_fin)
      (UB: concretize_u uv_fin (UB_unERR_UB_OOM ub_msg)),
      IS1.LLVM.MEM.CP.CONC.concretize_u uv_inf (UB_unERR_UB_OOM ub_msg).
  Proof.
    induction uv_inf using DV1.uvalue_strong_ind;
      intros uv_fin ub_msg REF UB;
      try
        solve
        [ unfold_uvalue_refine_strict;
          try inv REF;
          repeat break_match_hyp_inv;
          repeat red in UB;
          rewrite CONC.concretize_uvalueM_equation in UB; inv UB
        | cbn; auto
        ].

    destruct uv_inf;
      try
        solve
        [ unfold_uvalue_refine_strict;
          try inv REF;
          repeat break_match_hyp_inv;
          repeat red in UB;
          rewrite CONC.concretize_uvalueM_equation in UB; inv UB
        | cbn; auto
        ].

    - (* Structs *)
      unfold_uvalue_refine_strict_in REF.
      break_match_hyp_inv.
      eapply map_monad_oom_Forall2 in Heqo.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      { (* UB when concretizing l *)
        clear H2.
        induction Heqo.
        - cbn in H0; inv H0.
        - rewrite map_monad_unfold in H0.
          repeat red in H0.
          destruct H0 as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H2.
          { clear H3.
            pose proof (H x).
            forward H2.
            repeat constructor.
            specialize (H2 y ub_msg H1 H0).
            rewrite map_monad_unfold.
            repeat red.
            exists (UB_unERR_UB_OOM ub_msg).
            exists (fun _ => (UB_unERR_UB_OOM ub_msg)).

            split; cbn; eauto.
            exists (UB_unERR_UB_OOM ub_msg).
            exists (fun _ => (UB_unERR_UB_OOM ub_msg)).

            split; cbn; eauto.
          }

          (* No UB on first element *)
          destruct H3 as [[] | H3].
          specialize (H3 x3).
          forward H3; [cbn; auto|].
          destruct H3 as (?&?&?&?&?).
          rewrite <- H3 in H5.
          destruct_err_ub_oom x1; inv H5.
          2: {
            destruct H4 as [[] | H4].
            specialize (H4 x5); forward H4; [cbn;auto|].

            cbn in H4.
            rewrite <- H4 in H7.
            inv H7.
          }

          repeat red.
          exists (UB_unERR_UB_OOM ub_msg).
          exists (fun _ => (UB_unERR_UB_OOM ub_msg)).
          split; cbn; eauto.

          repeat red.
          pose proof uvalue_concretize_strict_concretize_inclusion _ _ H1 as INC.
          red in INC.
          specialize (INC _ H0).

          exists (ret (fin_to_inf_dvalue x3)).
          exists (fun _ => (UB_unERR_UB_OOM ub_msg)).
          split; cbn; eauto.
          split; cbn; eauto.
          right.
          intros a H5; subst.

          repeat red.
          exists (UB_unERR_UB_OOM ub_msg).
          exists (fun _ => (UB_unERR_UB_OOM ub_msg)).
          split; cbn; eauto.

          forward IHHeqo.
          intros u H5 uv_fin ub_msg0 REF UB.
          eapply H; try right; eauto.
          { clear - H5.
            dependent induction H5.
            - inv H.
              constructor.
              constructor.
              right; auto.
            - specialize (IHclos_trans2 l eq_refl).
              eapply t_trans.
              apply H5_.
              apply IHclos_trans2.
          }

          forward IHHeqo; eauto.
          repeat red in IHHeqo.
          destruct IHHeqo as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H6; eauto.

          destruct H7 as [[] | H7].
          specialize (H7 x6); forward H7; [cbn;auto|].

          cbn in H7.
          rewrite <- H7 in H9.
          inv H9.
      }

      (* Concretizing fields succeeds, should be a contradiction *)
      destruct H2 as [[] | H2].
      specialize (H2 x1 eq_refl).
      cbn in H2.
      rewrite <- H2 in H4.
      cbn in H4. inv H4.
    - (* Packed structs *)
      unfold_uvalue_refine_strict_in REF.
      break_match_hyp_inv.
      eapply map_monad_oom_Forall2 in Heqo.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      { (* UB when concretizing l *)
        clear H2.
        induction Heqo.
        - cbn in H0; inv H0.
        - rewrite map_monad_unfold in H0.
          repeat red in H0.
          destruct H0 as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H2.
          { clear H3.
            pose proof (H x).
            forward H2.
            repeat constructor.
            specialize (H2 y ub_msg H1 H0).

            rewrite map_monad_unfold.
            repeat red.
            exists (UB_unERR_UB_OOM ub_msg).
            exists (fun _ => (UB_unERR_UB_OOM ub_msg)).

            split; cbn; eauto.
            exists (UB_unERR_UB_OOM ub_msg).
            exists (fun _ => (UB_unERR_UB_OOM ub_msg)).

            split; cbn; eauto.
          }

          (* No UB on first element *)
          destruct H3 as [[] | H3].
          specialize (H3 x3).
          forward H3; [cbn; auto|].
          destruct H3 as (?&?&?&?&?).
          rewrite <- H3 in H5.
          destruct_err_ub_oom x1; inv H5.
          2: {
            destruct H4 as [[] | H4].
            specialize (H4 x5); forward H4; [cbn;auto|].

            cbn in H4.
            rewrite <- H4 in H7.
            inv H7.
          }

          repeat red.
          exists (UB_unERR_UB_OOM ub_msg).
          exists (fun _ => (UB_unERR_UB_OOM ub_msg)).
          split; cbn; eauto.

          repeat red.
          pose proof uvalue_concretize_strict_concretize_inclusion _ _ H1 as INC.
          red in INC.
          specialize (INC _ H0).

          exists (ret (fin_to_inf_dvalue x3)).
          exists (fun _ => (UB_unERR_UB_OOM ub_msg)).
          split; cbn; eauto.
          split; cbn; eauto.
          right.
          intros a H5; subst.

          repeat red.
          exists (UB_unERR_UB_OOM ub_msg).
          exists (fun _ => (UB_unERR_UB_OOM ub_msg)).
          split; cbn; eauto.

          forward IHHeqo.
          intros u H5 uv_fin ub_msg0 REF UB.
          eapply H; try right; eauto.
          { clear - H5.
            dependent induction H5.
            - inv H.
              constructor.
              constructor.
              right; auto.
            - specialize (IHclos_trans2 l eq_refl).
              eapply t_trans.
              apply H5_.
              apply IHclos_trans2.
          }

          forward IHHeqo; eauto.
          repeat red in IHHeqo.
          destruct IHHeqo as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H6; eauto.

          destruct H7 as [[] | H7].
          specialize (H7 x6); forward H7; [cbn;auto|].

          cbn in H7.
          rewrite <- H7 in H9.
          inv H9.
      }

      (* Concretizing fields succeeds, should be a contradiction *)
      destruct H2 as [[] | H2].
      specialize (H2 x1 eq_refl).
      cbn in H2.
      rewrite <- H2 in H4.
      cbn in H4. inv H4.
    - (* Arrays *)
      unfold_uvalue_refine_strict_in REF.
      break_match_hyp_inv.
      eapply map_monad_oom_Forall2 in Heqo.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      { (* UB when concretizing l *)
        clear H2.
        induction Heqo.
        - cbn in H0; inv H0.
        - rewrite map_monad_unfold in H0.
          repeat red in H0.
          destruct H0 as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H2.
          { clear H3.
            pose proof (H x).
            forward H2.
            repeat constructor.
            specialize (H2 y ub_msg H1 H0).
            rewrite map_monad_unfold.
            repeat red.
            exists (UB_unERR_UB_OOM ub_msg).
            exists (fun _ => (UB_unERR_UB_OOM ub_msg)).

            split; cbn; eauto.
            exists (UB_unERR_UB_OOM ub_msg).
            exists (fun _ => (UB_unERR_UB_OOM ub_msg)).

            split; cbn; eauto.
          }

          (* No UB on first element *)
          destruct H3 as [[] | H3].
          specialize (H3 x3).
          forward H3; [cbn; auto|].
          destruct H3 as (?&?&?&?&?).
          rewrite <- H3 in H5.
          destruct_err_ub_oom x1; inv H5.
          2: {
            destruct H4 as [[] | H4].
            specialize (H4 x5); forward H4; [cbn;auto|].

            cbn in H4.
            rewrite <- H4 in H7.
            inv H7.
          }

          repeat red.
          exists (UB_unERR_UB_OOM ub_msg).
          exists (fun _ => (UB_unERR_UB_OOM ub_msg)).
          split; cbn; eauto.

          repeat red.
          pose proof uvalue_concretize_strict_concretize_inclusion _ _ H1 as INC.
          red in INC.
          specialize (INC _ H0).

          exists (ret (fin_to_inf_dvalue x3)).
          exists (fun _ => (UB_unERR_UB_OOM ub_msg)).
          split; cbn; eauto.
          split; cbn; eauto.
          right.
          intros a H5; subst.

          repeat red.
          exists (UB_unERR_UB_OOM ub_msg).
          exists (fun _ => (UB_unERR_UB_OOM ub_msg)).
          split; cbn; eauto.

          forward IHHeqo.
          intros u H5 uv_fin ub_msg0 REF UB.
          eapply H; try right; eauto.
          { clear - H5.
            dependent induction H5.
            - inv H.
              constructor.
              constructor.
              right; auto.
            - specialize (IHclos_trans2 t l eq_refl).
              eapply t_trans.
              apply H5_.
              apply IHclos_trans2.
          }
          forward IHHeqo; eauto.
          repeat red in IHHeqo.
          destruct IHHeqo as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H6; eauto.

          destruct H7 as [[] | H7].
          specialize (H7 x6); forward H7; [cbn;auto|].

          cbn in H7.
          rewrite <- H7 in H9.
          inv H9.
      }

      (* Concretizing fields succeeds, should be a contradiction *)
      destruct H2 as [[] | H2].
      specialize (H2 x1 eq_refl).
      cbn in H2.
      rewrite <- H2 in H4.
      cbn in H4. inv H4.
    - (* Vectors *)
      unfold_uvalue_refine_strict_in REF.
      break_match_hyp_inv.
      eapply map_monad_oom_Forall2 in Heqo.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      { (* UB when concretizing l *)
        clear H2.
        induction Heqo.
        - cbn in H0; inv H0.
        - rewrite map_monad_unfold in H0.
          repeat red in H0.
          destruct H0 as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H2.
          { clear H3.
            pose proof (H x).
            forward H2.
            repeat constructor.
            specialize (H2 y ub_msg H1 H0).
            rewrite map_monad_unfold.
            repeat red.
            exists (UB_unERR_UB_OOM ub_msg).
            exists (fun _ => (UB_unERR_UB_OOM ub_msg)).

            split; cbn; eauto.
            exists (UB_unERR_UB_OOM ub_msg).
            exists (fun _ => (UB_unERR_UB_OOM ub_msg)).

            split; cbn; eauto.
          }

          (* No UB on first element *)
          destruct H3 as [[] | H3].
          specialize (H3 x3).
          forward H3; [cbn; auto|].
          destruct H3 as (?&?&?&?&?).
          rewrite <- H3 in H5.
          destruct_err_ub_oom x1; inv H5.
          2: {
            destruct H4 as [[] | H4].
            specialize (H4 x5); forward H4; [cbn;auto|].

            cbn in H4.
            rewrite <- H4 in H7.
            inv H7.
          }

          repeat red.
          exists (UB_unERR_UB_OOM ub_msg).
          exists (fun _ => (UB_unERR_UB_OOM ub_msg)).
          split; cbn; eauto.

          repeat red.
          pose proof uvalue_concretize_strict_concretize_inclusion _ _ H1 as INC.
          red in INC.
          specialize (INC _ H0).

          exists (ret (fin_to_inf_dvalue x3)).
          exists (fun _ => (UB_unERR_UB_OOM ub_msg)).
          split; cbn; eauto.
          split; cbn; eauto.
          right.
          intros a H5; subst.

          repeat red.
          exists (UB_unERR_UB_OOM ub_msg).
          exists (fun _ => (UB_unERR_UB_OOM ub_msg)).
          split; cbn; eauto.

          forward IHHeqo.
          intros u H5 uv_fin ub_msg0 REF UB.
          eapply H; try right; eauto.
          { clear - H5.
            dependent induction H5.
            - inv H.
              constructor.
              constructor.
              right; auto.
            - specialize (IHclos_trans2 t l eq_refl).
              eapply t_trans.
              apply H5_.
              apply IHclos_trans2.
          }
          forward IHHeqo; eauto.
          repeat red in IHHeqo.
          destruct IHHeqo as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H6; eauto.

          destruct H7 as [[] | H7].
          specialize (H7 x6); forward H7; [cbn;auto|].

          cbn in H7.
          rewrite <- H7 in H9.
          inv H9.
      }

      (* Concretizing fields succeeds, should be a contradiction *)
      destruct H2 as [[] | H2].
      specialize (H2 x1 eq_refl).
      cbn in H2.
      rewrite <- H2 in H4.
      cbn in H4. inv H4.
    - (* UVALUE_ICmp *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* UB when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No UB on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* UB in second operand *)
        eapply IH in H0; eauto.
        repeat red.
        exists (ret (fin_to_inf_dvalue x1)).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        split; eauto.
        right.
        intros a H3.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* UB in evaluating operation? *)
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      rewrite <- H2 in H5.

      remember (eval_iop iop x1 x3) as res.
      destruct_err_ub_oom res; inv H5.

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      eapply eval_iop_ub_fin_inf; eauto.
    - (* UVALUE_ICmp *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* UB when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No UB on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* UB in second operand *)
        eapply IH in H0; eauto.
        repeat red.
        exists (ret (fin_to_inf_dvalue x1)).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        split; eauto.
        right.
        intros a H3.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* UB in evaluating operation? *)
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      rewrite <- H2 in H5.

      remember (eval_icmp samesign cmp x1 x3) as res.
      destruct_err_ub_oom res; inv H5.

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      eapply eval_icmp_ub_fin_inf; eauto.
    - (* UVALUE_FBinop *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* UB when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No UB on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* UB in second operand *)
        eapply IH in H0; eauto.
        repeat red.
        exists (ret (fin_to_inf_dvalue x1)).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        split; eauto.
        right.
        intros a H3.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* UB in evaluating operation? *)
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      rewrite <- H2 in H5.

      remember (eval_fop fop x1 x3) as res.
      destruct_err_ub_oom res; inv H5.

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      eapply eval_fop_ub_fin_inf; eauto.

    - rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.
      cbn. 
      
      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* UB when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      rewrite <- H1 in H3.

      remember (eval_fneg x1) as res.
      destruct_err_ub_oom res; inv H3.

      red.

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a Ha.
      subst.
      eapply eval_fneg_ub_fin_inf; eauto.
      
    - (* UVALUE_FCmp *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* UB when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No UB on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* UB in second operand *)
        eapply IH in H0; eauto.
        repeat red.
        exists (ret (fin_to_inf_dvalue x1)).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        split; eauto.
        right.
        intros a H3.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* UB in evaluating operation? *)
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      rewrite <- H2 in H5.

      remember (eval_fcmp cmp x1 x3) as res.
      destruct_err_ub_oom res; inv H5.

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      eapply eval_fcmp_ub_fin_inf; eauto.
    - (* UVALUE_Conversion *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* UB when concretizing uv *)
        eapply IH in H; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No UB on concretizing uv. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).
      split.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.
      intros a H0; subst.
      break_match_hyp.

      { (* Pure *)
        cbn in H1.
        rewrite <- H1 in H3; inv H3.
      }

      { (* ItoP *)
        break_match_hyp;
        cbn in H1;
        rewrite <- H1 in H3; inv H3.
      }

      { (* PtoI *)
        exfalso.
        repeat break_match_hyp;
        cbn in H1;
          rewrite <- H1 in H3; inv H3.
        repeat break_match_hyp_inv.
        repeat break_match_hyp_inv.
        unfold lift_OOM in Heqe.
        repeat break_match_hyp_inv; inv Heqs.
      }

      { (* Oom *)
        rewrite <- H1 in H3; inv H3.
      }

      { (* Illegal *)
        rewrite <- H1 in H3; inv H3.
      }
    - (* UVALUE_GetElementPtr *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* UB when concretizing base address *)
        eapply IH in H; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No UB on base address. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).
      split; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.
      intros a ?; subst.
      repeat red.

      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* UB in concretization of indices *)
        generalize dependent l.
        induction idxs; intros l H3 Heqo0.
        - inv Heqo0. cbn in H3. inv H3.
        - forward IHidxs.
          { intros idx H4 uv_fin ub_msg0 REF UB.
            eapply IH; eauto.
            { clear - H4.
              dependent induction H4.
              - inv H.
                constructor.
                constructor.
                constructor.
                constructor.
                right; auto.
              - specialize (IHclos_trans2 _ _ _ eq_refl).
                eapply t_trans.
                apply H4_.
                apply IHclos_trans2.
            }
          }
          rewrite map_monad_unfold in Heqo0.
          cbn in Heqo0.
          repeat break_match_hyp_inv.
          rewrite map_monad_unfold in H3.
          cbn in H3.
          repeat red in H3.
          destruct H3 as (?&?&?&?&?).
          destruct_err_ub_oom x; inv H3.
          + (* UB in first index *)
            exists (UB_unERR_UB_OOM ub_msg).
            exists (fun _ => UB_unERR_UB_OOM ub_msg).
            split.
            * rewrite map_monad_unfold.
              cbn.
              exists (UB_unERR_UB_OOM ub_msg).
              exists (fun _ => UB_unERR_UB_OOM ub_msg).
              split.
              eapply IH; cbn; eauto.
              repeat constructor.
              split; cbn; eauto.
            * split; cbn; eauto.
          + (* No UB on first index *)
            destruct H4 as [[] | H4].
            specialize (H4 x4).
            forward H4; [cbn; auto|].
            repeat red in H4.
            destruct H4 as (?&?&?&?&?).
            rewrite <- H4 in H6.

            rewrite map_monad_unfold.
            exists (UB_unERR_UB_OOM ub_msg).
            exists (fun _ => UB_unERR_UB_OOM ub_msg).
            split; cbn; eauto.

            exists (ret (fin_to_inf_dvalue x4)).
            exists (fun _ => UB_unERR_UB_OOM ub_msg).
            split; cbn; eauto.
            eapply uvalue_concretize_strict_concretize_inclusion; eauto.
            split; cbn; eauto.
            right.
            intros a0 H8; subst.
            destruct_err_ub_oom x; inv H6.
            * (* UB in map *)
              specialize (IHidxs l0 H3 eq_refl).
              destruct IHidxs as (?&?&?&?&?).
              destruct_err_ub_oom x; inv H7.
              { exists (UB_unERR_UB_OOM ub_msg).
                exists (fun _ => UB_unERR_UB_OOM ub_msg).
                split; cbn; eauto.
              }
              destruct H8 as [[] | H8].
              specialize (H8 x7).
              forward H8; [cbn; auto|].
              destruct (IS1.LLVM.MEM.MP.GEP.handle_gep t (fin_to_inf_dvalue x1) x7);
                try rewrite <- H8 in H10; try inv H10.
              destruct o;
                rewrite <- H8 in H9; inv H9.
            * destruct H5 as [[] | H5].
              specialize (H5 x6).
              forward H5; [cbn; auto|].
              rewrite <- H5 in H8.
              inv H8.
      }

      (* No UB when concretizing indices... *)
      exfalso.
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      repeat break_match_hyp;
        rewrite <- H2 in H5; inv H5.
    - (* UVALUE_ExtractElement *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* UB when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No UB on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* UB in second operand *)
        eapply IH in H0; eauto.
        repeat red.
        exists (ret (fin_to_inf_dvalue x1)).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        split; eauto.
        right.
        intros a H3.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* UB in evaluating operation? *)
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      repeat red in H2.
      destruct H2 as (?&?&?&?&?).
      rewrite <- H3 in H5.
      destruct vec_typ; inv H2; inv H5.

      destruct H4 as [[] | H4].
      specialize (H4 vec_typ).
      forward H4; [cbn; auto|].
      remember (index_into_vec_dv vec_typ x1 x3) as res.
      rewrite <- H4 in H6.
      destruct_err_ub_oom res; inv H6.
      symmetry in Heqres.
      eapply index_into_vec_dv_no_ub in Heqres; contradiction.
    - (* UVALUE_InsertElement *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* UB when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).
      split; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a H0.
      inv H0.

      (* No UB on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* UB uv_inf3 *)
        eapply IH in H0; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No UB on uv_inf3 *)
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).
      split; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a ?.
      inv H3.

      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      repeat red in H2.
      destruct H2 as (?&?&?&?&?).
      rewrite <- H3 in H5.
      destruct_err_ub_oom x; inv H5.

      { (* UB in uv_inf2 *)
        eapply IH in H2; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No UB on uv_inf2 *)
      exists (ret (fin_to_inf_dvalue x5)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).
      split; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a ?.
      inv H5.

      (* UB in evaluating... *)
      destruct H4 as [[] | H4].
      specialize (H4 x5).
      forward H4; [cbn; auto|].
      rewrite <- H4 in H7.
      remember (insert_into_vec_dv vec_typ x1 x5 x3) as res.
      destruct_err_ub_oom res; inv H7.
      symmetry in Heqres.
      eapply insert_into_vec_dv_no_ub_fin_inf in Heqres; contradiction.
    - (* UVALUE_ExtractValue *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* UB when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).
      split; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a H0.
      inv H0.

      (* No UB on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      rewrite <- H1 in H3.
      remember (((fix loop (str : dvalue) (idxs : list LLVMAst.int_ast) {struct idxs} :
                        err_ub_oom dvalue :=
                      match idxs with
                      | [] => ret str
                      | i :: tl => v <- index_into_str_dv str i;; loop v tl
                      end) x1 idxs)) as res.
      destruct_err_ub_oom res; inv H3.
      (* Here's should be a contradiction --- no way to get UB *)
      clear - Heqres.
      symmetry in Heqres.
      exfalso.

      generalize dependent x1.
      induction idxs; intros x1 CONTRA.
      + inv CONTRA.
      + remember (index_into_str_dv x1 a) as init.
        remember (fix loop (str : dvalue) (idxs : list LLVMAst.int_ast) {struct idxs} : err_ub_oom dvalue :=
                    match idxs with
                    | [] => ret str
                    | i :: tl => v0 <- index_into_str_dv str i;; loop v0 tl
                    end) as loop.
        clear Heqloop.

        destruct_err_ub_oom init; try solve [inv CONTRA].
        * (* UB in index_into_str_dv *)
          eapply index_into_str_dv_no_ub_fin_inf; eauto.
        * cbn in CONTRA.
          remember (loop init0 idxs) as res.
          destruct_err_ub_oom res; inv CONTRA.
          eapply IHidxs; eauto.
    - (* UVALUE_InsertValue *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* UB when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No UB on first operand. *)
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).
      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a ?; subst.
      repeat red.

      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* UB in second operand *)
        eapply IH in H0; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No UB on second operand. *)
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).
      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a ?; subst.
      repeat red.


      (* UB in evaluating operation? *)
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      repeat red in H2.

      pose proof H2 as LOOP.
      apply insert_value_loop_fin_inf_succeeds in LOOP.
      cbn in LOOP.
      rewrite LOOP.
      remember (x2 x3) as res.
      destruct_err_ub_oom res; inv H5.
      reflexivity.
    - (* UVALUE_Select *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* UB when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).
      split; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a H0.
      inv H0.

      (* No UB on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      remember (x0 x1) as res.
      destruct_err_ub_oom res; inv H3; eauto.

      epose proof eval_select_ub_fin_inf x1 u0 u1 uv_inf2 uv_inf3 _ as EVAL.
      forward EVAL; [intros ? ?; eapply IH; eauto; repeat constructor|].
      forward EVAL; [intros ? ?; eapply IH; eauto; repeat constructor|].
      forward EVAL; eauto.
      forward EVAL; eauto.
      forward EVAL.
      { rewrite eval_select_equation.
        eauto.
      }

      rewrite IS1.MEM.CP.CONC.eval_select_equation in EVAL.
      auto.
    - (* UVALUE_ConcatBytes *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      erewrite map_monad_oom_length; eauto.
      erewrite sizeof_dtyp_fin_inf; eauto.
      erewrite all_extract_bytes_from_uvalue_fin_inf; eauto.
      break_match_hyp.
      2: {
        cbn.
        cbn in UB.
        repeat red in UB.
        destruct UB as (?&?&?&?&?).
        destruct_err_ub_oom x; inv H0.
        { exists (UB_unERR_UB_OOM ub_msg).
          exists (fun _ => UB_unERR_UB_OOM ub_msg).
          split; cbn; eauto.
          eapply concretize_uvalue_bytes_helper_ub_fin_inf; eauto.
          2: eapply map_monad_oom_Forall2; eauto.
          2: apply concretization_map_refine_empty.

          intros u H0 uv_fin H2 ub_msg0 H3.
          eapply IH; eauto.
          eapply DV1.uvalue_concat_bytes_strict_subterm; eauto.
        }

        destruct H1 as [[] | H1].
        specialize (H1 x1).
        forward H1; [cbn; auto|].
        remember (x0 x1) as x0x1.
        destruct_err_ub_oom x0x1; inv H3.

        eapply concretize_uvalue_bytes_helper_fin_inf in H; eauto.
        3: eapply map_monad_oom_Forall2; eauto.
        2: {
          intros u H0 uv_fin H2 dv_fin H3.
          eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        }

        exists (ret (fin_to_inf_dvalue_bytes x1)).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; eauto.
        split; eauto.
        right.
        intros a RETa.
        inv RETa.
        eapply dvalue_bytes_to_dvalue_ub_fin_inf; eauto.
        apply dvalue_bytes_refine_fin_to_inf_dvalue_bytes.
        apply concretization_map_refine_empty.
      }
      pose proof (map_monad_oom_length _ _ _ Heqo) as LEN.

      break_match_hyp.
      { (* UB when concretizing first operand *)
        destruct uvs.
        { inv Heqo.
          cbn in Heqo0; inv Heqo0.
        }
        rewrite map_monad_unfold in Heqo.
        cbn in Heqo.
        repeat break_match_hyp_inv.
        destruct u1; inv Heqo0.
        repeat break_match_hyp_inv.
        unfold OptionUtil.guard_opt in *.
        repeat break_match_hyp_inv.
        apply dtyp_eqb_eq in Heqb4; subst.
        rewrite H1; cbn.

        uvalue_convert_strict_inv Heqo1.
        eapply IH; eauto.
        eapply DV1.uvalue_concat_bytes_strict_subterm; eauto.
        repeat constructor.
      }

      cbn.
      cbn in UB.
      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        eapply concretize_uvalue_bytes_helper_ub_fin_inf; eauto.
        2: eapply map_monad_oom_Forall2; eauto.
        2: eapply concretization_map_refine_empty.

        intros u H0 uv_fin H2 ub_msg0 H3.
        eapply IH; eauto.
        eapply DV1.uvalue_concat_bytes_strict_subterm; auto.
      }

      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      remember (x0 x1) as x0x1.
      destruct_err_ub_oom x0x1; inv H3.

      eapply concretize_uvalue_bytes_helper_fin_inf in H; eauto.
      3: eapply map_monad_oom_Forall2; eauto.
      2: {
        intros u H0 uv_fin H2 dv_fin H3.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      }

      exists (ret (fin_to_inf_dvalue_bytes x1)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).
      split; eauto.
      split; eauto.
      right.
      intros a RETa.
      inv RETa.
      eapply dvalue_bytes_to_dvalue_ub_fin_inf; eauto.
      apply dvalue_bytes_refine_fin_to_inf_dvalue_bytes.

      apply concretization_map_refine_empty.
  Qed.

  From Stdlib Require Import String.

  Lemma concretize_no_ub_inf_fin :
    forall uv_inf uv_fin
      (REF : uvalue_refine_strict uv_inf uv_fin)
      (UB : forall ub_msg : string, ~ IS1.LLVM.MEM.CP.CONC.concretize_u uv_inf (UB_unERR_UB_OOM ub_msg)),
    forall ub_msg : string, ~ concretize_u uv_fin (UB_unERR_UB_OOM ub_msg).
  Proof.
    intros uv_inf uv_fin REF UB ub_msg.
    intros CONC.
    eapply UB;
      eapply concretize_ub_fin_inf; eauto.
  Qed.

  Lemma concretize_uvalue_bytes_helper_err_fin_inf :
    forall uvs_inf uvs_fin acc_inf acc_fin msg
      (IH : forall (u : DV1.uvalue),
          Exists (DV1.uvalue_subterm u) uvs_inf ->
          forall uv_fin : DV2.uvalue,
            uvalue_refine_strict u uv_fin ->
            forall msg,
              IS2.MEM.CP.CONC.concretize_u uv_fin (ERR_unERR_UB_OOM msg) ->
              IS1.MEM.CP.CONC.concretize_u u (ERR_unERR_UB_OOM msg)),
      Forall2 uvalue_refine_strict uvs_inf uvs_fin ->
      concretization_map_refine acc_inf acc_fin ->
      @concretize_uvalue_bytes_helper ErrUbOomProp Monad_ErrUbOomProp
        (fun (dt : dtyp) (edv : err_ub_oom dvalue) =>
           match @unERR_UB_OOM IdentityMonad.ident dvalue edv with
           | {|
               EitherMonad.unEitherT :=
                 {|
                   EitherMonad.unEitherT :=
                     {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |}
                 |}
             |} => dvalue_has_dtyp dv dt /\ dv <> DVALUE_Poison dt
           | _ => True
           end) err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (fun (A : Type) (x ue : err_ub_oom A) => x = ue) acc_fin uvs_fin (ERR_unERR_UB_OOM msg) ->
      @IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalue_bytes_helper ErrUbOomProp Monad_ErrUbOomProp
        (fun (dt0 : dtyp) (edv : err_ub_oom DV1.dvalue) =>
           match @unERR_UB_OOM IdentityMonad.ident DV1.dvalue edv with
           | {|
               EitherMonad.unEitherT :=
                 {|
                   EitherMonad.unEitherT :=
                     {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |}
                 |}
             |} => DV1.dvalue_has_dtyp dv dt0 /\ dv <> DV1.DVALUE_Poison dt0
           | _ => True
           end) err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (fun (A : Type) (x ue : err_ub_oom A) => x = ue) acc_inf uvs_inf (ERR_unERR_UB_OOM msg).
  Proof.
    (* Will need something about acc_inf and acc_fin *)
    induction uvs_inf;
      intros uvs_fin acc_inf acc_fin msg IH REF ACC_REF CONC.
    - inv REF.
      cbn in CONC; inv CONC; cbn.
    - inv REF.
      rewrite concretize_uvalue_bytes_helper_equation in CONC.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalue_bytes_helper_equation.
      destruct y; uvalue_refine_strict_inv H1; try inv CONC; auto.
      rewrite pre_concretized_fin_inf with (uv_fin:=y) (acc_fin:=acc_fin); eauto.
      break_match_hyp_inv; repeat red.
      + (* pre-concretization exists *)
        destruct H as (?&?&?&?).
        destruct_err_ub_oom x0; inv H1.
        { exists (ERR_unERR_UB_OOM msg).
          exists (fun _ => ERR_unERR_UB_OOM msg).
          split; cbn; eauto.
        }

        destruct H2 as [[] | H2].
        specialize (H2 x2).
        forward H2; [cbn; auto|].
        rewrite <- H2 in H5.
        inv H5.
      + (* No pre-concretization exists *)
        destruct H as (?&?&?&?).
        destruct_err_ub_oom x0; inv H1.
        { exists (ERR_unERR_UB_OOM msg).
          exists (fun _ => ERR_unERR_UB_OOM msg).
          split; cbn; eauto.
          eapply IH; eauto.
          repeat constructor.
        }

        exists (ret (fin_to_inf_dvalue x2)).
        exists (fun _ => ERR_unERR_UB_OOM msg).
        split.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        split; cbn; eauto.
        right.
        intros ? ?; subst.
        repeat red.

        destruct H2 as [[] | H2].
        specialize (H2 x2).
        forward H2; [cbn; auto|].
        cbn in H2.
        repeat red in H2.
        destruct H2 as (?&?&?&?&?).
        rewrite <- H2 in H5.
        destruct_err_ub_oom x0; inv H5.
        { exists (ERR_unERR_UB_OOM msg).
          exists (fun _ => ERR_unERR_UB_OOM msg).
          split; cbn; eauto.
          eapply IHuvs_inf; eauto.
          eapply concretize_map_refine_new_concretized_byte_fin_inf; eauto.
          eapply fin_to_inf_dvalue_refine_strict.
        }

        exists (ret (fin_to_inf_dvalue_bytes x4)).
        exists (fun _ => ERR_unERR_UB_OOM msg).
        split.
        eapply concretize_uvalue_bytes_helper_fin_inf; eauto.
        intros u H5 uv_fin H6 dv_fin H8.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        eapply concretize_map_refine_new_concretized_byte_fin_inf; eauto.
        eapply fin_to_inf_dvalue_refine_strict.

        destruct H4 as [[] | H4].
        specialize (H4 x4).
        forward H4; [cbn; auto|].
        rewrite <- H4 in H7.
        inv H7.
  Qed.

  Lemma concretize_err_fin_inf :
    forall uv_inf uv_fin err_msg
      (REF : uvalue_refine_strict uv_inf uv_fin)
      (ERR: concretize_u uv_fin (ERR_unERR_UB_OOM err_msg)),
      IS1.LLVM.MEM.CP.CONC.concretize_u uv_inf (ERR_unERR_UB_OOM err_msg).
  Proof.
    induction uv_inf using DV1.uvalue_strong_ind;
      intros uv_fin err_msg REF ERR;
      try
        solve
        [ unfold_uvalue_refine_strict;
          try inv REF;
          repeat break_match_hyp_inv;
          repeat red in ERR;
          rewrite CONC.concretize_uvalueM_equation in ERR; inv ERR
        | cbn; auto
        ].

    destruct uv_inf;
      try
        solve
        [ unfold_uvalue_refine_strict;
          try inv REF;
          repeat break_match_hyp_inv;
          repeat red in ERR;
          rewrite CONC.concretize_uvalueM_equation in ERR; inv ERR
        | cbn; auto
        ].

    - (* Structs *)
      unfold_uvalue_refine_strict_in REF.
      break_match_hyp_inv.
      eapply map_monad_oom_Forall2 in Heqo.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      { (* ERR when concretizing l *)
        clear H2.
        induction Heqo.
        - cbn in H0; inv H0.
        - rewrite map_monad_unfold in H0.
          repeat red in H0.
          destruct H0 as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H2.
          { clear H3.
            pose proof (H x).
            forward H2.
            repeat constructor.
            specialize (H2 y err_msg H1 H0).
            rewrite map_monad_unfold.
            repeat red.
            exists (ERR_unERR_UB_OOM err_msg).
            exists (fun _ => (ERR_unERR_UB_OOM err_msg)).

            split; cbn; eauto.
            exists (ERR_unERR_UB_OOM err_msg).
            exists (fun _ => (ERR_unERR_UB_OOM err_msg)).

            split; cbn; eauto.
          }

          (* No UB on first element *)
          destruct H3 as [[] | H3].
          specialize (H3 x3).
          forward H3; [cbn; auto|].
          destruct H3 as (?&?&?&?&?).
          rewrite <- H3 in H5.
          destruct_err_ub_oom x1; inv H5.
          2: {
            destruct H4 as [[] | H4].
            specialize (H4 x5); forward H4; [cbn;auto|].

            cbn in H4.
            rewrite <- H4 in H7.
            inv H7.
          }

          repeat red.
          exists (ERR_unERR_UB_OOM err_msg).
          exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
          split; cbn; eauto.

          repeat red.
          pose proof uvalue_concretize_strict_concretize_inclusion _ _ H1 as INC.
          red in INC.
          specialize (INC _ H0).

          exists (ret (fin_to_inf_dvalue x3)).
          exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
          split; cbn; eauto.
          split; cbn; eauto.
          right.
          intros a H5; subst.

          repeat red.
          exists (ERR_unERR_UB_OOM err_msg).
          exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
          split; cbn; eauto.

          forward IHHeqo.
          intros u H5 uv_fin err_msg0 REF UB.
          eapply H; try right; eauto.
          { clear - H5.
            dependent induction H5.
            - inv H.
              constructor.
              constructor.
              right; auto.
            - specialize (IHclos_trans2 l eq_refl).
              eapply t_trans.
              apply H5_.
              apply IHclos_trans2.
          }

          forward IHHeqo; eauto.
          repeat red in IHHeqo.
          destruct IHHeqo as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H6; eauto.

          destruct H7 as [[] | H7].
          specialize (H7 x6); forward H7; [cbn;auto|].

          cbn in H7.
          rewrite <- H7 in H9.
          inv H9.
      }

      (* Concretizing fields succeeds, should be a contradiction *)
      destruct H2 as [[] | H2].
      specialize (H2 x1 eq_refl).
      cbn in H2.
      rewrite <- H2 in H4.
      cbn in H4. inv H4.
    - (* Packed structs *)
      unfold_uvalue_refine_strict_in REF.
      break_match_hyp_inv.
      eapply map_monad_oom_Forall2 in Heqo.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      { (* ERR when concretizing l *)
        clear H2.
        induction Heqo.
        - cbn in H0; inv H0.
        - rewrite map_monad_unfold in H0.
          repeat red in H0.
          destruct H0 as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H2.
          { clear H3.
            pose proof (H x).
            forward H2.
            repeat constructor.
            specialize (H2 y err_msg H1 H0).

            rewrite map_monad_unfold.
            repeat red.
            exists (ERR_unERR_UB_OOM err_msg).
            exists (fun _ => (ERR_unERR_UB_OOM err_msg)).

            split; cbn; eauto.
            exists (ERR_unERR_UB_OOM err_msg).
            exists (fun _ => (ERR_unERR_UB_OOM err_msg)).

            split; cbn; eauto.
          }

          (* No ERR on first element *)
          destruct H3 as [[] | H3].
          specialize (H3 x3).
          forward H3; [cbn; auto|].
          destruct H3 as (?&?&?&?&?).
          rewrite <- H3 in H5.
          destruct_err_ub_oom x1; inv H5.
          2: {
            destruct H4 as [[] | H4].
            specialize (H4 x5); forward H4; [cbn;auto|].

            cbn in H4.
            rewrite <- H4 in H7.
            inv H7.
          }

          repeat red.
          exists (ERR_unERR_UB_OOM err_msg).
          exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
          split; cbn; eauto.

          repeat red.
          pose proof uvalue_concretize_strict_concretize_inclusion _ _ H1 as INC.
          red in INC.
          specialize (INC _ H0).

          exists (ret (fin_to_inf_dvalue x3)).
          exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
          split; cbn; eauto.
          split; cbn; eauto.
          right.
          intros a H5; subst.

          repeat red.
          exists (ERR_unERR_UB_OOM err_msg).
          exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
          split; cbn; eauto.

          forward IHHeqo.
          intros u H5 uv_fin err_msg0 REF ERR.
          eapply H; try right; eauto.
          { clear - H5.
            dependent induction H5.
            - inv H.
              constructor.
              constructor.
              right; auto.
            - specialize (IHclos_trans2 l eq_refl).
              eapply t_trans.
              apply H5_.
              apply IHclos_trans2.
          }

          forward IHHeqo; eauto.
          repeat red in IHHeqo.
          destruct IHHeqo as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H6; eauto.

          destruct H7 as [[] | H7].
          specialize (H7 x6); forward H7; [cbn;auto|].

          cbn in H7.
          rewrite <- H7 in H9.
          inv H9.
      }

      (* Concretizing fields succeeds, should be a contradiction *)
      destruct H2 as [[] | H2].
      specialize (H2 x1 eq_refl).
      cbn in H2.
      rewrite <- H2 in H4.
      cbn in H4. inv H4.
    - (* Arrays *)
      unfold_uvalue_refine_strict_in REF.
      break_match_hyp_inv.
      eapply map_monad_oom_Forall2 in Heqo.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      { (* ERR when concretizing l *)
        clear H2.
        induction Heqo.
        - cbn in H0; inv H0.
        - rewrite map_monad_unfold in H0.
          repeat red in H0.
          destruct H0 as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H2.
          { clear H3.
            pose proof (H x).
            forward H2.
            repeat constructor.
            specialize (H2 y err_msg H1 H0).
            rewrite map_monad_unfold.
            repeat red.
            exists (ERR_unERR_UB_OOM err_msg).
            exists (fun _ => (ERR_unERR_UB_OOM err_msg)).

            split; cbn; eauto.
            exists (ERR_unERR_UB_OOM err_msg).
            exists (fun _ => (ERR_unERR_UB_OOM err_msg)).

            split; cbn; eauto.
          }

          (* No ERR on first element *)
          destruct H3 as [[] | H3].
          specialize (H3 x3).
          forward H3; [cbn; auto|].
          destruct H3 as (?&?&?&?&?).
          rewrite <- H3 in H5.
          destruct_err_ub_oom x1; inv H5.
          2: {
            destruct H4 as [[] | H4].
            specialize (H4 x5); forward H4; [cbn;auto|].

            cbn in H4.
            rewrite <- H4 in H7.
            inv H7.
          }

          repeat red.
          exists (ERR_unERR_UB_OOM err_msg).
          exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
          split; cbn; eauto.

          repeat red.
          pose proof uvalue_concretize_strict_concretize_inclusion _ _ H1 as INC.
          red in INC.
          specialize (INC _ H0).

          exists (ret (fin_to_inf_dvalue x3)).
          exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
          split; cbn; eauto.
          split; cbn; eauto.
          right.
          intros a H5; subst.

          repeat red.
          exists (ERR_unERR_UB_OOM err_msg).
          exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
          split; cbn; eauto.

          forward IHHeqo.
          intros u H5 uv_fin err_msg0 REF ERR.
          eapply H; try right; eauto.
          { clear - H5.
            dependent induction H5.
            - inv H.
              constructor.
              constructor.
              right; auto.
            - specialize (IHclos_trans2 t l eq_refl).
              eapply t_trans.
              apply H5_.
              apply IHclos_trans2.
          }
          forward IHHeqo; eauto.
          repeat red in IHHeqo.
          destruct IHHeqo as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H6; eauto.

          destruct H7 as [[] | H7].
          specialize (H7 x6); forward H7; [cbn;auto|].

          cbn in H7.
          rewrite <- H7 in H9.
          inv H9.
      }

      (* Concretizing fields succeeds, should be a contradiction *)
      destruct H2 as [[] | H2].
      specialize (H2 x1 eq_refl).
      cbn in H2.
      rewrite <- H2 in H4.
      cbn in H4. inv H4.
    - (* Vectors *)
      unfold_uvalue_refine_strict_in REF.
      break_match_hyp_inv.
      eapply map_monad_oom_Forall2 in Heqo.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      { (* ERR when concretizing l *)
        clear H2.
        induction Heqo.
        - cbn in H0; inv H0.
        - rewrite map_monad_unfold in H0.
          repeat red in H0.
          destruct H0 as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H2.
          { clear H3.
            pose proof (H x).
            forward H2.
            repeat constructor.
            specialize (H2 y err_msg H1 H0).
            rewrite map_monad_unfold.
            repeat red.
            exists (ERR_unERR_UB_OOM err_msg).
            exists (fun _ => (ERR_unERR_UB_OOM err_msg)).

            split; cbn; eauto.
            exists (ERR_unERR_UB_OOM err_msg).
            exists (fun _ => (ERR_unERR_UB_OOM err_msg)).

            split; cbn; eauto.
          }

          (* No ERR on first element *)
          destruct H3 as [[] | H3].
          specialize (H3 x3).
          forward H3; [cbn; auto|].
          destruct H3 as (?&?&?&?&?).
          rewrite <- H3 in H5.
          destruct_err_ub_oom x1; inv H5.
          2: {
            destruct H4 as [[] | H4].
            specialize (H4 x5); forward H4; [cbn;auto|].

            cbn in H4.
            rewrite <- H4 in H7.
            inv H7.
          }

          repeat red.
          exists (ERR_unERR_UB_OOM err_msg).
          exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
          split; cbn; eauto.

          repeat red.
          pose proof uvalue_concretize_strict_concretize_inclusion _ _ H1 as INC.
          red in INC.
          specialize (INC _ H0).

          exists (ret (fin_to_inf_dvalue x3)).
          exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
          split; cbn; eauto.
          split; cbn; eauto.
          right.
          intros a H5; subst.

          repeat red.
          exists (ERR_unERR_UB_OOM err_msg).
          exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
          split; cbn; eauto.

          forward IHHeqo.
          intros u H5 uv_fin err_msg0 REF ERR.
          eapply H; try right; eauto.
          { clear - H5.
            dependent induction H5.
            - inv H.
              constructor.
              constructor.
              right; auto.
            - specialize (IHclos_trans2 t l eq_refl).
              eapply t_trans.
              apply H5_.
              apply IHclos_trans2.
          }
          forward IHHeqo; eauto.
          repeat red in IHHeqo.
          destruct IHHeqo as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H6; eauto.

          destruct H7 as [[] | H7].
          specialize (H7 x6); forward H7; [cbn;auto|].

          cbn in H7.
          rewrite <- H7 in H9.
          inv H9.
      }

      (* Concretizing fields succeeds, should be a contradiction *)
      destruct H2 as [[] | H2].
      specialize (H2 x1 eq_refl).
      cbn in H2.
      rewrite <- H2 in H4.
      cbn in H4. inv H4.
    - (* UVALUE_ICmp *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* ERR when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No ERR on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* ERR in second operand *)
        eapply IH in H0; eauto.
        repeat red.
        exists (ret (fin_to_inf_dvalue x1)).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        split; eauto.
        right.
        intros a H3.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* ERR in evaluating operation? *)
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      rewrite <- H2 in H5.

      remember (eval_iop iop x1 x3) as res.
      destruct_err_ub_oom res; inv H5.

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      eapply eval_iop_err_fin_inf; eauto.
    - (* UVALUE_ICmp *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* ERR when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No ERR on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* ERR in second operand *)
        eapply IH in H0; eauto.
        repeat red.
        exists (ret (fin_to_inf_dvalue x1)).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        split; eauto.
        right.
        intros a H3.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* ERR in evaluating operation? *)
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      rewrite <- H2 in H5.

      remember (eval_icmp samesign cmp x1 x3) as res.
      destruct_err_ub_oom res; inv H5.

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      eapply eval_icmp_err_fin_inf; eauto.
    - (* UVALUE_FBinop *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* ERR when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No ERR on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* ERR in second operand *)
        eapply IH in H0; eauto.
        repeat red.
        exists (ret (fin_to_inf_dvalue x1)).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        split; eauto.
        right.
        intros a H3.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* ERR in evaluating operation? *)
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      rewrite <- H2 in H5.

      remember (eval_fop fop x1 x3) as res.
      destruct_err_ub_oom res; inv H5.

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      eapply eval_fop_err_fin_inf; eauto.

    - (* UVALUE_Fneg *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.
      cbn. 

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* ERR when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No ERR on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      rewrite <- H1 in H3.

      remember (eval_fneg x1) as res.
      destruct_err_ub_oom res; inv H3.
      red.

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a Ha.
      eapply eval_fneg_err_fin_inf; eauto.
      
    - (* UVALUE_FCmp *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* ERR when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No ERR on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* ERR in second operand *)
        eapply IH in H0; eauto.
        repeat red.
        exists (ret (fin_to_inf_dvalue x1)).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        split; eauto.
        right.
        intros a H3.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* ERR in evaluating operation? *)
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      rewrite <- H2 in H5.

      remember (eval_fcmp cmp x1 x3) as res.
      destruct_err_ub_oom res; inv H5.

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      eapply eval_fcmp_err_fin_inf; eauto.
    - (* UVALUE_Conversion *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* ERR when concretizing uv *)
        eapply IH in H; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No ERR on concretizing uv. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).
      split.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.
      intros a H0; subst.
      break_match_hyp.

      { (* Pure *)
        cbn in H1.
        rewrite <- H1 in H3; inv H3.
      }

      { (* ItoP *)
        break_match_hyp;
        cbn in H1;
        rewrite <- H1 in H3; inv H3.
      }

      { (* PtoI *)
        erewrite get_conv_case_ptoi_fin_inf; eauto.
        cbn.
        repeat break_match_hyp;
          cbn in H1;
          rewrite <- H1 in H3; inv H3;
          rewrite_fin_to_inf_dvalue; auto.
        - erewrite ptr_to_int_fin_to_inf_addr; eauto.
          unfold lift_OOM in *.
          break_inner_match_hyp;
            cbn in *; inv H2.
      }

      { (* Oom *)
        rewrite <- H1 in H3; inv H3.
      }

      { (* Illegal *)
        rewrite <- H1 in H3; inv H3.
        erewrite get_conv_case_illegal_fin_inf; eauto.
      }
    - (* UVALUE_GetElementPtr *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* ERR when concretizing base address *)
        eapply IH in H; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No ERR on base address. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).
      split; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.
      intros a ?; subst.
      repeat red.

      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.
      { (* ERR in concretization of indices *)
        clear H2.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split.
        (* TODO: Probably make a map_monad lemma *)
        { clear - IH H0 Heqo0.
          generalize dependent l.
          induction idxs;
            intros l H0 Heqo0.
          - inv Heqo0. inv H0.
          - rewrite map_monad_unfold in *.
            cbn in Heqo0.
            repeat break_match_hyp_inv.

            rewrite map_monad_unfold in H0.
            repeat red in H0.

            destruct H0 as (?&?&?&?&?).
            destruct_err_ub_oom x; inv H0.
            { (* ERR in first index *)
              clear H1.
              repeat red.
              exists (ERR_unERR_UB_OOM err_msg).
              exists (fun _ => ERR_unERR_UB_OOM err_msg).
              split; cbn; eauto.
              eapply IH; eauto.
              repeat constructor.
            }

            (* ERR in map *)
            exists (ret (fin_to_inf_dvalue x1)).
            exists (fun _ => ERR_unERR_UB_OOM err_msg).
            split; cbn; eauto.
            eapply uvalue_concretize_strict_concretize_inclusion; eauto.
            split; cbn; eauto.
            right.
            intros a0 H8; subst.

            destruct H1 as [[] | H1].
            specialize (H1 x1).
            forward H1; [cbn; auto|].
            repeat red in H1.
            destruct H1 as (?&?&?&?&?).
            rewrite <- H1 in H3.
            destruct_err_ub_oom x; inv H3.
            { clear H2.
              repeat red.
              exists (ERR_unERR_UB_OOM err_msg).
              exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
              split.
              { eapply IHidxs; eauto.
                intros u0 H2 uv_fin err_msg0 REF ERR.
                eapply IH; eauto.
                clear - H2.
                dependent induction H2.
                - inv H.
                  repeat constructor; auto.
                  constructor.
                  constructor.
                  right; auto.
                - specialize (IHclos_trans2 t uv_inf idxs eq_refl).
                  eapply t_trans.
                  apply H2_.
                  apply IHclos_trans2.
              }

              split; cbn; eauto.
            }

            exfalso.
            destruct H2 as [[] | H2].
            specialize (H2 x3).
            forward H2; [cbn; auto|].
            rewrite <- H2 in H5.
            inv H5.
        }

        split; cbn; eauto.
      }

      (* No ERR when concretizing indices... *)
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      repeat break_match_hyp;
        rewrite <- H2 in H5; inv H5.

      (* Error in handle_gep *)
      exists (ret (fmap fin_to_inf_dvalue x3)).
      exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
      split; cbn; eauto.

      (* TODO: Probably make a map_monad lemma *)
      { clear - IH H0 Heqo0.
        generalize dependent l.
        generalize dependent x3.
        induction idxs;
          intros x3 l H0 Heqo0.
        - inv Heqo0. inv H0.
          cbn.
          reflexivity.
        - rewrite map_monad_unfold in *.
          cbn in Heqo0.
          repeat break_match_hyp_inv.

          rewrite map_monad_unfold in H0.
          repeat red in H0.

          destruct H0 as (?&?&?&?&?).
          destruct_err_ub_oom x; inv H0.
          repeat red.
          exists (ret (fin_to_inf_dvalue x1)).
          exists (fun _ => ret (flat_map (fun x : DVCrev.DV1.dvalue => [fin_to_inf_dvalue x]) x3)).
          split; cbn; eauto.
          eapply uvalue_concretize_strict_concretize_inclusion; eauto.
          split; cbn; eauto.
          right.
          intros a0 H8; subst.

          destruct H1 as [[] | H1].
          specialize (H1 x1).
          forward H1; [cbn; auto|].
          repeat red in H1.
          destruct H1 as (?&?&?&?&?).
          rewrite <- H1 in H3.
          destruct_err_ub_oom x; inv H3.

          destruct H2 as [[] | H2].
          specialize (H2 x4).
          forward H2; [cbn; auto|].
          rewrite <- H2 in H5.
          inv H5.
          cbn in H2.

          repeat red.
          exists (ret (fmap fin_to_inf_dvalue x4)).
          exists (fun _ => ret (flat_map (fun x : DVCrev.DV1.dvalue => [fin_to_inf_dvalue x]) (x1 :: x4))).
          split; cbn; eauto.
          2: {
            split; cbn; eauto.
            right.
            intros a0 H3; subst.
            reflexivity.
          }

          eapply IHidxs; eauto.
          intros u0 H3 uv_fin err_msg REF ERR.
          eapply IH; eauto.

          { clear - H3.
            dependent induction H3.
            - inv H.
              repeat constructor; auto.
              constructor.
              constructor.
              right; auto.
            - specialize (IHclos_trans2 t uv_inf idxs eq_refl).
              eapply t_trans.
              apply H3_.
              apply IHclos_trans2.
          }
      }

      split; cbn; eauto.
      right.
      intros ? ?; subst.
      destruct x1;
        rewrite_fin_to_inf_dvalue;
        try solve [cbn; inv Heqs; auto].
      cbn in *.
      break_match_hyp_inv.
      erewrite handle_gep_addr_err_fin_inf; eauto.
      unfold fin_to_inf_addr.
      break_match_goal.
      clear Heqs; auto.
    - (* UVALUE_ExtractElement *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* ERR when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).
      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a ?; subst.
      repeat red.

      (* No ERR on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* ERR in second operand *)
        eapply IH in H0; eauto.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).
      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a ?; subst.
      repeat red.

      (* ERR in evaluating operation? *)
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      repeat red in H2.
      destruct H2 as (?&?&?&?&?).
      rewrite <- H3 in H5.
      destruct_err_ub_oom x; inv H5.
      { (* non-vector type... *)
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
      }

      exists (ret x5).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).
      split; cbn; eauto.
      split; eauto.
      right.
      intros ? ?; subst. 

      destruct H4 as [[] | H4].
      specialize (H4 a).
      forward H4; [cbn; auto|].
      cbn in H3.
      remember (index_into_vec_dv a x1 x3) as res.
      rewrite <- H4 in H7.
      destruct_err_ub_oom res; inv H7.
      symmetry in Heqres.
      eapply index_into_vec_dv_err_fin_inf in Heqres; eauto.
    - (* UVALUE_InsertElement *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* ERR when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).
      split; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a H0.
      inv H0.

      (* No ERR on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* ERR uv_inf3 *)
        eapply IH in H0; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No ERR on uv_inf3 *)
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).
      split; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a ?.
      inv H3.

      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      repeat red in H2.
      destruct H2 as (?&?&?&?&?).
      rewrite <- H3 in H5.
      destruct_err_ub_oom x; inv H5.

      { (* ERR in uv_inf2 *)
        eapply IH in H2; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No ERR on uv_inf2 *)
      exists (ret (fin_to_inf_dvalue x5)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).
      split; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a ?.
      inv H5.

      (* ERR in evaluating... *)
      destruct H4 as [[] | H4].
      specialize (H4 x5).
      forward H4; [cbn; auto|].
      rewrite <- H4 in H7.
      remember (insert_into_vec_dv vec_typ x1 x5 x3) as res.
      destruct_err_ub_oom res; inv H7.
      symmetry in Heqres.
      eapply insert_into_vec_dv_err_fin_inf in Heqres; eauto.
    - (* UVALUE_ShuffleVector *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR; inv ERR.
      reflexivity.
    - (* UVALUE_ExtractValue *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* ERR when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No ERR on first operand. *)
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).
      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a ?; subst.
      repeat red.

      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      remember (x0 x1) as x0x1.
      destruct_err_ub_oom x0x1; inv H3.
      eapply extract_value_loop_fin_inf_err in H1.
      setoid_rewrite H1.
      reflexivity.
    - (* UVALUE_InsertValue *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* ERR when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No ERR on first operand. *)
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).
      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a ?; subst.
      repeat red.

      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* UB in second operand *)
        eapply IH in H0; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No UB on second operand. *)
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).
      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a ?; subst.
      repeat red.

      (* UB in evaluating operation? *)
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      repeat red in H2.

      pose proof H2 as LOOP.
      apply insert_value_loop_fin_inf_succeeds in LOOP.
      cbn in LOOP.
      rewrite LOOP.
      remember (x2 x3) as res.
      destruct_err_ub_oom res; inv H5.
      reflexivity.
    - (* UVALUE_Select *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* ERR when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).
      split; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a H0.
      inv H0.

      (* No ERR on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      remember (x0 x1) as res.
      destruct_err_ub_oom res; inv H3; eauto.
      epose proof eval_select_err_fin_inf x1 u0 u1 uv_inf2 uv_inf3 _ as EVAL.
      forward EVAL; [intros ? ?; eapply IH; eauto; repeat constructor|].
      forward EVAL; [intros ? ?; eapply IH; eauto; repeat constructor|].
      forward EVAL; eauto.
      forward EVAL; eauto.
      forward EVAL.
      { rewrite eval_select_equation.
        cbn in *; eauto.
      }

      rewrite IS1.MEM.CP.CONC.eval_select_equation in EVAL.
      auto.
    - (* UVALUE_ExtractByte *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.
      inv ERR.
      cbn. auto.
    - (* UVALUE_ConcatBytes *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.
      auto.

      erewrite map_monad_oom_length; eauto.
      erewrite sizeof_dtyp_fin_inf; eauto.
      erewrite all_extract_bytes_from_uvalue_fin_inf; eauto.
      break_match_hyp.
      2: {
        cbn.
        cbn in ERR.
        repeat red in ERR.
        destruct ERR as (?&?&?&?&?).
        destruct_err_ub_oom x; inv H0.
        { exists (ERR_unERR_UB_OOM err_msg).
          exists (fun _ => ERR_unERR_UB_OOM err_msg).
          split; cbn; eauto.
          eapply concretize_uvalue_bytes_helper_err_fin_inf; eauto.
          2: eapply map_monad_oom_Forall2; eauto.
          2: apply concretization_map_refine_empty.

          intros u H0 uv_fin H2 ub_msg0 H3.
          eapply IH; eauto.
          eapply DV1.uvalue_concat_bytes_strict_subterm; eauto.
        }

        destruct H1 as [[] | H1].
        specialize (H1 x1).
        forward H1; [cbn; auto|].
        remember (x0 x1) as x0x1.
        destruct_err_ub_oom x0x1; inv H3.

        eapply concretize_uvalue_bytes_helper_fin_inf in H; eauto.
        3: eapply map_monad_oom_Forall2; eauto.
        2: {
          intros u H0 uv_fin H2 dv_fin H3.
          eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        }

        exists (ret (fin_to_inf_dvalue_bytes x1)).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; eauto.
        split; eauto.
        right.
        intros a RETa.
        inv RETa.
        eapply dvalue_bytes_to_dvalue_err_fin_inf; eauto.
        apply dvalue_bytes_refine_fin_to_inf_dvalue_bytes.
        apply concretization_map_refine_empty.
      }
      pose proof (map_monad_oom_length _ _ _ Heqo) as LEN.

      break_match_hyp.
      { (* ERR when concretizing first operand *)
        destruct uvs.
        { inv Heqo.
          cbn in Heqo0; inv Heqo0.
        }
        rewrite map_monad_unfold in Heqo.
        cbn in Heqo.
        repeat break_match_hyp_inv.
        destruct u1; inv Heqo0.
        repeat break_match_hyp_inv.
        unfold OptionUtil.guard_opt in *.
        repeat break_match_hyp_inv.
        apply dtyp_eqb_eq in Heqb4; subst.
        rewrite H1; cbn.

        uvalue_convert_strict_inv Heqo1.
        eapply IH; eauto.
        eapply DV1.uvalue_concat_bytes_strict_subterm; eauto.
        repeat constructor.
      }

      cbn.
      cbn in ERR.
      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => UB_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        eapply concretize_uvalue_bytes_helper_err_fin_inf; eauto.
        2: eapply map_monad_oom_Forall2; eauto.
        2: eapply concretization_map_refine_empty.

        intros u H0 uv_fin H2 ub_msg0 H3.
        eapply IH; eauto.
        eapply DV1.uvalue_concat_bytes_strict_subterm; auto.
      }

      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      remember (x0 x1) as x0x1.
      destruct_err_ub_oom x0x1; inv H3.

      eapply concretize_uvalue_bytes_helper_fin_inf in H; eauto.
      3: eapply map_monad_oom_Forall2; eauto.
      2: {
        intros u H0 uv_fin H2 dv_fin H3.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      }

      exists (ret (fin_to_inf_dvalue_bytes x1)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).
      split; eauto.
      split; eauto.
      right.
      intros a RETa.
      inv RETa.
      eapply dvalue_bytes_to_dvalue_err_fin_inf; eauto.
      apply dvalue_bytes_refine_fin_to_inf_dvalue_bytes.

      apply concretization_map_refine_empty.
  Qed.

  Lemma concretize_no_err_inf_fin :
    forall uv_inf uv_fin
      (REF : uvalue_refine_strict uv_inf uv_fin)
      (ERR : forall err_msg : string, ~ IS1.LLVM.MEM.CP.CONC.concretize_u uv_inf (ERR_unERR_UB_OOM err_msg)),
    forall err_msg : string, ~ concretize_u uv_fin (ERR_unERR_UB_OOM err_msg).
  Proof.
    intros uv_inf uv_fin REF ERR err_msg.
    intros CONC.
    eapply ERR;
      eapply concretize_err_fin_inf; eauto.
  Qed.

  Lemma concretize_or_pick_exp_E_orutt_strict :
    forall uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      orutt exp_E_refine_strict exp_E_res_refine_strict dvalue_refine_strict
        (IS1.LLVM.D.concretize_or_pick uv1) (concretize_or_pick uv2)
        (OOM:=OOME).
  Proof.
    intros uv1 uv2 REF.
    unfold IS1.LLVM.D.concretize_or_pick_unique, IS1.LLVM.D.concretize_or_pick.
    unfold concretize_or_pick_unique, concretize_or_pick.
    cbn.
    break_match;
      eapply uvalue_refine_strict_preserves_is_concrete with (uvc:=uv2) in Heqb; eauto;
      rewrite Heqb.

    apply lift_err_uvalue_to_dvalue_orutt_strict; eauto with ORUTT.

    repeat rewrite bind_trigger.
    apply orutt_Vis.

    { cbn; auto. }

    intros t1 t2 H.
    apply orutt_Ret.
    destruct t1 as [dv1 []].
    destruct t2 as [dv2 []].
    cbn in *.
    inv H; subst_existT; cbn in *.
    tauto.

    intros o CONTRA; inv CONTRA.
  Qed.

  Lemma concretize_or_pick_L0'_orutt_strict :
    forall uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      orutt L0'_refine_strict L0'_res_refine_strict dvalue_refine_strict
        (IS1.LLVM.D.concretize_or_pick uv1) (concretize_or_pick uv2)
        (OOM:=OOME).
  Proof.
    intros uv1 uv2 REF.
    unfold IS1.LLVM.D.concretize_or_pick_unique, IS1.LLVM.D.concretize_or_pick.
    unfold concretize_or_pick_unique, concretize_or_pick.
    cbn.
    break_match;
      eapply uvalue_refine_strict_preserves_is_concrete with (uvc:=uv2) in Heqb; eauto;
      rewrite Heqb.

    apply lift_err_uvalue_to_dvalue_orutt_strict; eauto with ORUTT.
    repeat constructor.

    repeat rewrite bind_trigger.
    apply orutt_Vis.

    constructor; cbn; eauto.

    intros t1 t2 H.
    apply orutt_Ret.
    destruct t1 as [dv1 []].
    destruct t2 as [dv2 []].
    cbn in *.
    inv H; subst_existT; cbn in *.
    tauto.

    intros o CONTRA; inv CONTRA.
  Qed.

  Lemma uvalue_refine_strict_unique_prop :
    forall uv_inf uv_fin,
      uvalue_refine_strict uv_inf uv_fin ->
      IS1.LLVM.Pick.unique_prop uv_inf ->
      unique_prop uv_fin.
  Proof.
    intros uv_inf uv_fin REF UNIQUE_INF.

    unfold unique_prop.
    unfold IS1.LLVM.Pick.unique_prop in UNIQUE_INF.
    destruct UNIQUE_INF as [NUB [NERR [[dv_inf [CONC UNIQUE_INF]] | NO_CONC]]].
    2: {
      split.
      eapply concretize_no_ub_inf_fin; eauto.
      split.
      eapply concretize_no_err_inf_fin; eauto.
      right.
      eapply concretize_fails_inf_fin; eauto.
    }

    pose proof uvalue_concretize_strict_concretize_inclusion _ _ REF.
    red in H.

    pose proof concretize_inf_excluded_middle uv_fin.
    destruct H0 as [(dv_fin & CONC_FIN) | H0]; auto.
    all:
      split;
      [ eapply concretize_no_ub_inf_fin; eauto
      | split;
        [eapply concretize_no_err_inf_fin|];
        eauto].

    left.
    exists dv_fin.
    split; eauto.
    intros dv H1.
    apply H in H1, CONC_FIN.
    apply UNIQUE_INF in H1, CONC_FIN.
    subst.
    apply fin_to_inf_dvalue_injective in H1;
      subst; auto.
  Qed.

  (*
    - fin_to_inf_dvalue_injective
    - concretize_no_err_inf_fin
    - concretize_no_err_inf_fin
   *)

  Lemma uvalue_refine_strict_non_poison_prop :
    forall uv_inf uv_fin,
      uvalue_refine_strict uv_inf uv_fin ->
      IS1.LLVM.Pick.non_poison_prop uv_inf ->
      non_poison_prop uv_fin.
  Proof.
    intros uv_inf uv_fin REF NON_POISON_INF.

    unfold non_poison_prop.
    unfold IS1.LLVM.Pick.non_poison_prop in NON_POISON_INF.
    destruct NON_POISON_INF as [NUB [NERR NON_POISON_INF]].
    split.
    eapply concretize_no_ub_inf_fin; eauto.
    split.
    eapply concretize_no_err_inf_fin; eauto.

    intros dt CONTRA.
    eapply (NON_POISON_INF dt).

    replace (DV1.DVALUE_Poison dt) with
      (fin_to_inf_dvalue (DVALUE_Poison dt)).
    2: {
      unfold fin_to_inf_dvalue.
      break_match_goal; subst.
      destruct p.
      unfold DVCrev.dvalue_convert_strict in e.
      cbn in *.
      clear Heqs.
      inv e.
      auto.
    }

    eapply uvalue_concretize_strict_concretize_inclusion.
    apply REF.
    apply CONTRA.
  Qed.

  Lemma concretize_or_pick_unique_orutt_strict :
    forall E1 E2
      `{OOM1 : OOME -< E1} `{OOM2 : OOME -< E2}
      `{ERR1: FailureE -< E1} `{ERR2: FailureE -< E2}
      `{PICK1: PickE -< E1} `{PICK2: PickE -< E2}
      (pre : prerel E1 E2) (post : postrel E1 E2)
      (ERRDISC : forall e1 e2, @subevent FailureE E2 ERR2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (PICKDISC : forall e1 e2, @subevent PickE E2 PICK2 {_ : dvalue | True} e1 <> @subevent OOME E2 OOM2 {_ : dvalue | True} e2)
      (ERRPRE : pre void void (@subevent FailureE E1 ERR1 void (Throw tt)) (@subevent FailureE E2 ERR2 void (Throw tt)))
      (PICKPRE : forall uv1 uv2, uvalue_refine_strict uv1 uv2 -> pre {_ : DV1.dvalue | True} {_ : dvalue | True}     
    (subevent {_ : DV1.dvalue | True} (IS1.LLVM.MEM.CP.CONC.pick_unique_uvalue uv1))
    (subevent {_ : dvalue | True} (pick_unique_uvalue uv2)))
(POSTREF : forall uv1 uv2 dv1 dv2, post {_ : DV1.dvalue | True} {_ : dvalue | True}
      (subevent {_ : DV1.dvalue | True} (IS1.LLVM.MEM.CP.CONC.pick_unique_uvalue uv1))
      (exist (fun _ : DV1.dvalue => True) dv1 I)
      (subevent {_ : dvalue | True} (pick_unique_uvalue uv2)) (exist (fun _ : dvalue => True) dv2 I) -> dvalue_refine_strict dv1 dv2)
      uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      orutt pre post dvalue_refine_strict
        (IS1.LLVM.D.concretize_or_pick_unique uv1) (concretize_or_pick_unique uv2)
        (OOM:=OOME).
  Proof.
    intros E1 E2 OOM1 OOM2 ERR1 ERR2 PICK1 PICK2 pre post ERRDISC PICKDISC ERRPRE PICKPRE POSTREF uv1 uv2 REF.

    unfold IS1.LLVM.D.concretize_or_pick_unique, IS1.LLVM.D.concretize_or_pick.
    unfold concretize_or_pick_unique, concretize_or_pick.
    cbn.
    break_match;
      eapply uvalue_refine_strict_preserves_is_concrete with (uvc:=uv2) in Heqb; eauto;
      rewrite Heqb.

    apply lift_err_uvalue_to_dvalue_orutt_strict; try typeclasses eauto; auto.
    repeat rewrite bind_trigger.
    apply orutt_Vis; eauto.

    intros t1 t2 H.
    apply orutt_Ret.
    destruct t1 as [dv1 []].
    destruct t2 as [dv2 []].
    cbn in *.

    eauto.
  Qed.

  #[global] Hint Resolve
    concretize_or_pick_unique_orutt_strict
    : ORUTT.

  Lemma orutt_concretize_uvalue_bytes_helper :
    forall E1 E2
      `{OOM1 : OOME -< E1} `{OOM2 : OOME -< E2}
      `{UB1 : UBE -< E1} `{UB2 : UBE -< E2}
      `{ERR1: FailureE -< E1} `{ERR2: FailureE -< E2}
      (pre : prerel E1 E2) (post : postrel E1 E2)
      (UBDISC : forall e1 e2, @subevent UBE E2 UB2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (ERRDISC : forall e1 e2, @subevent FailureE E2 ERR2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (UBINJ : pre void void (@subevent UBE E1 UB1 void (ThrowUB tt)) (@subevent UBE E2 UB2 void (ThrowUB tt)))
      (ERRINJ : pre void void (@subevent FailureE E1 ERR1 void (Throw tt)) (@subevent FailureE E2 ERR2 void (Throw tt)))
      uvs1 uvs2 acc1 acc2
      (IH : forall (uv_fin : DV2.uvalue),
          Exists (DV2.uvalue_subterm uv_fin) uvs2 ->
          forall u : DV1.uvalue,
            uvalue_refine_strict u uv_fin ->
            orutt (OOM:=OOME) pre post dvalue_refine_strict
              (IS1.LLVM.MEM.CP.CONC.concretize_uvalue u) (concretize_uvalue uv_fin)),
      Forall2 uvalue_refine_strict uvs1 uvs2 ->
      concretization_map_refine acc1 acc2 ->
      orutt (OOM:=OOME) pre post dvalue_bytes_refine
        ((fix concretize_uvalue_bytes_helper
            (acc : NMap (list (DV1.uvalue * DV1.dvalue)))
            (uvs0 : list DV1.uvalue) {struct uvs0} :
           itree E1 (list IS1.LLVM.MEM.MP.DVALUE_BYTES.dvalue_byte) :=
            match uvs0 with
            | [] => Ret []
            | DV1.UVALUE_ExtractByte byte_uv dt0 idx sid :: uvs1 =>
                match
                  match
                    NM.find (elt:=list (DV1.uvalue * DV1.dvalue)) sid acc
                  with
                  | Some v => Util.assoc byte_uv v
                  | None => None
                  end
                with
                | Some dv =>
                    ITree.bind (concretize_uvalue_bytes_helper acc uvs1)
                      (fun rest : list IS1.LLVM.MEM.MP.DVALUE_BYTES.dvalue_byte =>
                         Ret (IS1.LLVM.MEM.MP.DVALUE_BYTES.DVALUE_ExtractByte dv dt0 idx :: rest))
                | None =>
                    ITree.bind
                      (IS1.LLVM.MEM.CP.CONC.concretize_uvalueM (itree E1)
                         (fun dt1 : dtyp =>
                            lift_err_RAISE_ERROR (DV1.default_dvalue_of_dtyp dt1))
                         (itree E1)
                         (fun (A : Type) (x0 : itree E1 A) => x0) byte_uv)
                      (fun dv : DV1.dvalue =>
                         ITree.bind
                           (concretize_uvalue_bytes_helper
                              (IS1.LLVM.MEM.CP.CONCBASE.new_concretized_byte acc byte_uv dv sid) uvs1)
                           (fun rest : list IS1.LLVM.MEM.MP.DVALUE_BYTES.dvalue_byte =>
                              Ret (IS1.LLVM.MEM.MP.DVALUE_BYTES.DVALUE_ExtractByte dv dt0 idx :: rest)))
                end
            | _ => LLVMEvents.raise "concretize_uvalue_bytes_helper: non-byte in uvs."
            end) acc1 uvs1)
        ((fix concretize_uvalue_bytes_helper
            (acc : NMap (list (uvalue * dvalue))) (uvs0 : list uvalue) {struct uvs0} :
           itree E2 (list DVALUE_BYTES.dvalue_byte) :=
            match uvs0 with
            | [] => Ret []
            | UVALUE_ExtractByte byte_uv dt0 idx sid :: uvs1 =>
                match
                  match NM.find (elt:=list (uvalue * dvalue)) sid acc with
                  | Some v => Util.assoc byte_uv v
                  | None => None
                  end
                with
                | Some dv =>
                    ITree.bind (concretize_uvalue_bytes_helper acc uvs1)
                      (fun rest : list DVALUE_BYTES.dvalue_byte =>
                         Ret (DVALUE_BYTES.DVALUE_ExtractByte dv dt0 idx :: rest))
                | None =>
                    ITree.bind
                      (CONC.concretize_uvalueM (itree E2)
                         (fun dt1 : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt1))
                         (itree E2) (fun (A : Type) (x0 : itree E2 A) => x0) byte_uv)
                      (fun dv : dvalue =>
                         ITree.bind
                           (concretize_uvalue_bytes_helper (new_concretized_byte acc byte_uv dv sid) uvs1)
                           (fun rest : list DVALUE_BYTES.dvalue_byte =>
                              Ret (DVALUE_BYTES.DVALUE_ExtractByte dv dt0 idx :: rest)))
                end
            | _ => LLVMEvents.raise "concretize_uvalue_bytes_helper: non-byte in uvs."
            end) acc2 uvs2).
  Proof.
    intros E1 E2 OOM1 OOM2 UB1 UB2 ERR1 ERR2 pre post UBDISC ERRDISC UBINJ ERRINJ uvs1 uvs2 acc1 acc2 IH REF ACC_REF.
    revert acc1 acc2 ACC_REF.
    induction REF; intros acc1 acc2 ACC_REF.
    - apply orutt_Ret.
      constructor.
    - destruct y; uvalue_refine_strict_inv H;
        try solve
          [ apply orutt_raise; auto
          ].
      cbn.
      cbn.

      pose proof ACC_REF as (?&?).
      break_inner_match.
      2: {
        destruct (NM.find (elt:=list (uvalue * dvalue)) sid acc2) eqn:FIND2.
        { exfalso.
          apply NM_find_not_In in Heqo.
          apply Heqo.
          apply H.
          eapply NM_find_In; eauto.
        }

        eapply orutt_bind with (RR:=dvalue_refine_strict).
        { apply IH; auto.
          repeat constructor.
        }

        intros ? ? ?.
        eapply orutt_bind with (RR:=dvalue_bytes_refine).
        eapply IHREF; eauto.
        apply concretize_map_refine_new_concretized_byte_fin_inf; eauto.

        intros ? ? ?.
        apply orutt_Ret.
        red.
        constructor; cbn; eauto.
      }

      eapply concretize_map_refine_find_some_inf_fin in Heqo; eauto.
      destruct Heqo as (?&?&?).
      rewrite H2.
      break_match.
      { eapply assoc_similar_lookup in Heqo.
        2: apply uvalue_refine_strict_R2_injective.
        2: apply H3.

        destruct Heqo as (?&?&?&?&?&?).
        pose proof (Util.Forall2_Nth H5 H6 H3).
        destruct H7.
        cbn in *.
        red in fst_rel.
        setoid_rewrite H0 in fst_rel.
        inv fst_rel.

        subst.
        rewrite H4.

        eapply orutt_bind with (RR:=dvalue_bytes_refine).
        eapply IHREF; auto.

        intros ? ? ?.
        apply orutt_Ret.
        red.
        constructor; cbn; eauto.
      }

      { eapply (assoc_similar_no_lookup uvalue_refine_strict dvalue_refine_strict l0 x) in Heqo.
        2: apply uvalue_refine_strict_R2_injective.
        2: apply H3.
        2: eauto.

        rewrite Heqo.

        eapply orutt_bind with (RR:=dvalue_refine_strict).
        { apply IH; auto.
          repeat constructor.
        }

        intros ? ? ?.
        eapply orutt_bind with (RR:=dvalue_bytes_refine).
        eapply IHREF; eauto.
        apply concretize_map_refine_new_concretized_byte_fin_inf; eauto.

        intros ? ? ?.
        apply orutt_Ret.
        red.
        constructor; cbn; eauto.
      }
  Qed.

  Lemma orutt_concretize_uvalue :
    forall E1 E2
      `{OOM1 : OOME -< E1} `{OOM2 : OOME -< E2}
      `{UB1 : UBE -< E1} `{UB2 : UBE -< E2}
      `{ERR1: FailureE -< E1} `{ERR2: FailureE -< E2}
      (pre : prerel E1 E2) (post : postrel E1 E2)
      (UBDISC : forall e1 e2, @subevent UBE E2 UB2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (ERRDISC : forall e1 e2, @subevent FailureE E2 ERR2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (UBINJ : pre void void (@subevent UBE E1 UB1 void (ThrowUB tt)) (@subevent UBE E2 UB2 void (ThrowUB tt)))
      (ERRINJ : pre void void (@subevent FailureE E1 ERR1 void (Throw tt)) (@subevent FailureE E2 ERR2 void (Throw tt)))
      u2 u1,
      uvalue_refine_strict u1 u2 ->
      orutt pre post dvalue_refine_strict
        (IS1.LLVM.MEM.CP.CONC.concretize_uvalue u1)
        (concretize_uvalue u2)
        (OOM:=OOME).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? u2.
    induction u2 using DV2.uvalue_strong_ind; intros u1 REF;
      try DVC.uvalue_refine_strict_inv REF;
      try solve
        [ cbn;
          eapply orutt_Ret;
          rewrite dvalue_refine_strict_equation;
          cbn; try rewrite H; auto
        ].
    - cbn.
      unfold lift_err_RAISE_ERROR.
      cbn.
      break_match.
      + apply DVCrev.default_dvalue_of_dtyp_dv1_dv2_same_error in Heqs.
        rewrite Heqs.
        apply orutt_raise; cbn; auto.
      + apply DVC.default_dvalue_of_dtyp_dv1_dv2_equiv in Heqs.
        destruct Heqs as (?&?&?).
        rewrite H.
        apply orutt_Ret; auto.
    - destruct u2;
        try DVC.uvalue_refine_strict_inv REF;
        try solve
          [ cbn;
            eapply orutt_Ret;
            rewrite dvalue_refine_strict_equation;
            cbn; try rewrite H0; auto
          ].
      + cbn.
        unfold lift_err_RAISE_ERROR.
        cbn.
        break_match.
        * apply DVCrev.default_dvalue_of_dtyp_dv1_dv2_same_error in Heqs.
          rewrite Heqs.
          apply orutt_raise; cbn; auto.
        * apply DVC.default_dvalue_of_dtyp_dv1_dv2_equiv in Heqs.
          destruct Heqs as (?&?&?).
          rewrite H0.
          apply orutt_Ret; auto.
      + (* Struct *) cbn.
        eapply map_monad_oom_Forall2 in H1.
        assert (Forall2 (fun (a : DV1.uvalue) (b : DV2.uvalue) => uvalue_convert_strict a = NoOom b /\ DV2.uvalue_strict_subterm b (DV2.UVALUE_Struct fields)) x fields).
        { induction H1; cbn; auto.
          constructor.
          - split; eauto.
            repeat constructor.            
          - forward IHForall2.
            { intros u H2 u1 H3.
              apply H; eauto.
              eapply uvalue_strict_subterm_struct; eauto.
            }

            eapply Forall2_impl; eauto.
            intros a b H2.
            cbn in H2.
            destruct H2.
            split; eauto.
            eapply uvalue_strict_subterm_struct; eauto.
        }

        eapply orutt_bind with (RR:=Forall2 dvalue_refine_strict).
        { eapply map_monad_orutt2.
          apply H0.

          intros ? ? ?; cbn in *.
          destruct H2 as (?&?).
          eapply H; eauto.
        }
        intros r1 r2 H2.
        apply orutt_Ret.
        eapply map_monad_oom_Forall2 in H2.
        rewrite dvalue_refine_strict_equation; cbn;
          rewrite H2; cbn.
        reflexivity.
      + (* Packed Structs *)
        cbn.
        eapply map_monad_oom_Forall2 in H1.
        assert (Forall2 (fun (a : DV1.uvalue) (b : DV2.uvalue) => uvalue_convert_strict a = NoOom b /\ DV2.uvalue_strict_subterm b (DV2.UVALUE_Packed_struct fields)) x fields).
        { induction H1; cbn; auto.
          constructor.
          - split; eauto.
            repeat constructor.            
          - forward IHForall2.
            { intros u H2 u1 H3.
              apply H; eauto.
              eapply uvalue_strict_subterm_packed_struct; eauto.
            }

            eapply Forall2_impl; eauto.
            intros a b H2.
            cbn in H2.
            destruct H2.
            split; eauto.
            eapply uvalue_strict_subterm_packed_struct; eauto.
        }

        eapply orutt_bind with (RR:=Forall2 dvalue_refine_strict).
        { eapply map_monad_orutt2.
          apply H0.

          intros ? ? ?; cbn in *.
          destruct H2 as (?&?).
          eapply H; eauto.
        }
        intros r1 r2 H2.
        apply orutt_Ret.
        eapply map_monad_oom_Forall2 in H2.
        rewrite dvalue_refine_strict_equation; cbn;
          rewrite H2; cbn.
        reflexivity.
      + (* Arrays *)
        cbn.
        eapply map_monad_oom_Forall2 in H1.
        assert (Forall2 (fun (a : DV1.uvalue) (b : DV2.uvalue) => uvalue_convert_strict a = NoOom b /\ DV2.uvalue_strict_subterm b (DV2.UVALUE_Array t elts)) x elts).
        { induction H1; cbn; auto.
          constructor.
          - split; eauto.
            repeat constructor.            
          - forward IHForall2.
            { intros u H2 u1 H3.
              apply H; eauto.
              eapply uvalue_strict_subterm_array; eauto.
            }

            eapply Forall2_impl; eauto.
            intros a b H2.
            cbn in H2.
            destruct H2.
            split; eauto.
            eapply uvalue_strict_subterm_array; eauto.
        }

        eapply orutt_bind with (RR:=Forall2 dvalue_refine_strict).
        { eapply map_monad_orutt2.
          apply H0.

          intros ? ? ?; cbn in *.
          destruct H2 as (?&?).
          eapply H; eauto.
        }
        intros r1 r2 H2.
        apply orutt_Ret.
        eapply map_monad_oom_Forall2 in H2.
        rewrite dvalue_refine_strict_equation; cbn;
          rewrite H2; cbn.
        reflexivity.
      + (* Vectors *)
        cbn.
        eapply map_monad_oom_Forall2 in H1.
        assert (Forall2 (fun (a : DV1.uvalue) (b : DV2.uvalue) => uvalue_convert_strict a = NoOom b /\ DV2.uvalue_strict_subterm b (DV2.UVALUE_Vector t elts)) x elts).
        { induction H1; cbn; auto.
          constructor.
          - split; eauto.
            repeat constructor.            
          - forward IHForall2.
            { intros u H2 u1 H3.
              apply H; eauto.
              eapply uvalue_strict_subterm_vector; eauto.
            }

            eapply Forall2_impl; eauto.
            intros a b H2.
            cbn in H2.
            destruct H2.
            split; eauto.
            eapply uvalue_strict_subterm_vector; eauto.
        }

        eapply orutt_bind with (RR:=Forall2 dvalue_refine_strict).
        { eapply map_monad_orutt2.
          apply H0.

          intros ? ? ?; cbn in *.
          destruct H2 as (?&?).
          eapply H; eauto.
        }
        intros r1 r2 H2.
        apply orutt_Ret.
        eapply map_monad_oom_Forall2 in H2.
        rewrite dvalue_refine_strict_equation; cbn;
          rewrite H2; cbn.
        reflexivity.
      + (* IBinop *)
        cbn.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? ?.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? ?.
        apply orutt_eval_iop; auto.
      + (* ICmp *)
        cbn.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? ?.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? ?.
        eapply orutt_eval_icmp; eauto.
      + (* FBinop *)
        cbn.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? ?.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? ?.
        apply orutt_eval_fop; auto.

      + cbn.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? ?.
        apply orutt_eval_fneg; auto.
        
      + (* FCmp *)
        cbn.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? ?.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? ?.
        eapply orutt_eval_fcmp; auto.
      + (* Conversion *)
        cbn.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? ?.
        erewrite (fin_to_inf_dvalue_refine_strict' r1); eauto.
        remember (get_conv_case conv t_from r2 t_to) as c.
        destruct c; symmetry in Heqc.
        * erewrite get_conv_case_pure_fin_inf; eauto.
          apply orutt_Ret.
          apply fin_to_inf_dvalue_refine_strict.
        * erewrite get_conv_case_itop_fin_inf; eauto.
          remember (ITOP.int_to_ptr (dvalue_int_unsigned x0) PROV.wildcard_prov) as p.
          destruct p; symmetry in Heqp.
          { erewrite int_to_ptr_fin_inf_wildcard with (a_inf:=fin_to_inf_addr a) (a_fin:=a); eauto.
            2: {
              unfold fin_to_inf_addr.
              break_match; clear Heqs; auto.
            }

            apply orutt_Ret.
            red.
            cbn.
            rewrite addr_convert_fin_to_inf_addr; reflexivity.
            rewrite fin_to_inf_dvalue_dvalue_int_unsigned; auto.
          }

          apply orutt_raiseOOM.
        * erewrite get_conv_case_ptoi_fin_inf; eauto.
          destruct x0; cbn;
            rewrite_fin_to_inf_dvalue; cbn;
            try solve
              [ apply orutt_raise; auto
              ].

          destruct t_to;
            try solve
              [ apply orutt_raise; auto
              ].
          { all: apply orutt_Ret;
              rewrite dvalue_refine_strict_equation; cbn;
              rewrite ptr_to_int_fin_to_inf_addr;
              reflexivity.
          }

          rewrite ptr_to_int_fin_to_inf_addr.
          eapply orutt_bind with (RR:=(fun a b => a = intptr_fin_inf b)).
          { unfold lift_OOM.
            break_match.
            - rewrite IS1.LP.IP.VMemInt_intptr_mrepr_from_Z in Heqo.
              rewrite IS2.LP.IP.VMemInt_intptr_mrepr_from_Z.
              apply IS1.LP.IP.from_Z_to_Z in Heqo.
              break_match.
              + apply IP.from_Z_to_Z in Heqo0.
                apply orutt_Ret.
                unfold intptr_fin_inf.
                break_match.
                clear Heqs.
                apply IS1.LP.IP.from_Z_to_Z in e.
                rewrite Heqo0 in e.
                rewrite <- Heqo in e.
                apply IS1.LP.IP.to_Z_inj in e; auto.
              + apply orutt_raiseOOM.
            - break_match.
              + eapply VMEM_REF.mrepr_refine in Heqo0.
                setoid_rewrite Heqo in Heqo0; inv Heqo0.
                rewrite IS1.LP.IP.VMemInt_intptr_mrepr_from_Z in Heqo.
                rewrite IS2.LP.IP.VMemInt_intptr_mrepr_from_Z in Heqo0.
                apply IP.from_Z_to_Z in Heqo0.
                rewrite <- Heqo0 in Heqo.
                pose proof intptr_convert_succeeds i.
                destruct H2.
                rewrite e in Heqo.
                inv Heqo.
              + apply orutt_raiseOOM.
          }

          intros ? ? ?; subst.
          apply orutt_Ret.
          rewrite dvalue_refine_strict_equation.
          cbn.
          unfold intptr_fin_inf.
          break_inner_match.
          clear Heqs.
          apply intptr_convert_safe in e.
          rewrite e.
          reflexivity.
        * (* OOM *)
          apply orutt_raiseOOM.
        * (* Conv_Illegal *)
          erewrite get_conv_case_illegal_fin_inf; eauto.
          apply orutt_raise; auto.
      + (* GetElementPtr *)
        cbn.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? REF.

        eapply map_monad_oom_Forall2 in H2.
        assert (Forall2 (fun (a : DV1.uvalue) (b : DV2.uvalue) => uvalue_convert_strict a = NoOom b /\ DV2.uvalue_strict_subterm b (DV2.UVALUE_GetElementPtr t u2 idxs)) x0 idxs).
        { induction H2; cbn; auto.
          constructor.
          - split; eauto.
            repeat constructor.
          - forward IHForall2.
            { intros ? ? ? ?.
              apply H; eauto.
              eapply uvalue_strict_subterm_gep_cons; eauto.
            }

            eapply Forall2_impl; eauto.
            intros a b P.
            cbn in P.
            destruct P.
            split; eauto.
            eapply uvalue_strict_subterm_gep_cons; eauto.
        }

        eapply orutt_bind with (RR:=Forall2 dvalue_refine_strict).
        { eapply map_monad_orutt2.
          apply H0.

          intros ? ? ?; cbn in *.
          destruct H3 as (?&?).
          eapply H; eauto.
        }

        intros ? ? ?.
        unfold GEP.handle_gep,
          IS1.LLVM.MEM.MP.GEP.handle_gep.
        destruct r2;
          dvalue_refine_strict_inv REF;
          try solve
            [ apply orutt_raise; auto
            ].

        remember (GEP.handle_gep_addr t a r3) as res.
        destruct res as [res_err | [res | res_oom]];
          symmetry in Heqres.
        * eapply handle_gep_addr_err_fin_inf with (base_addr_inf:=x1) in Heqres; eauto.
          2: {
            apply addr_convert_safe_reverse; auto.
          }

          erewrite <- dvalue_refine_strict_map_fin_to_inf_dvalue in Heqres; eauto.
          rewrite Heqres.
          cbn.
          apply orutt_raise; auto.
        * eapply handle_gep_addr_fin_inf
            with (base_addr_inf:=x1) (res_addr_inf:=fin_to_inf_addr res)
            in Heqres; eauto.
          2: apply addr_convert_safe_reverse; auto.
          2: apply addr_convert_safe_reverse; auto; apply addr_refine_fin_to_inf_addr.

          erewrite <- dvalue_refine_strict_map_fin_to_inf_dvalue in Heqres; eauto.
          rewrite Heqres.
          cbn.
          apply orutt_Ret.
          rewrite dvalue_refine_strict_equation.
          cbn.
          rewrite addr_refine_fin_to_inf_addr; reflexivity.
        * cbn.
          apply orutt_raiseOOM.
      + (* ExtractElement *)
        cbn.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? REF.

        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? REF2.

        eapply orutt_bind with (RR:=eq).
        { destruct vec_typ;
            try solve
              [ apply orutt_raise; auto
              ].
          apply orutt_Ret; auto.
        }

        intros ? ? ?; subst.
        eapply orutt_index_into_vec_dv; auto.
      + (* InsertElement *)
        cbn.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? REF.

        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? REF2.

        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? REF3.

        eapply orutt_insert_into_vec_dv; auto.
      + (* ShuffleVector *)
        cbn.
        (* Currently unimplemented, but will be similar to insert case above *)
        apply orutt_raise; auto.
      + (* ExtractValue *)
        cbn.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? REF.
        eapply orutt_extractvalue_loop; auto.
      + (* InsertValue *)
        cbn.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? REF.

        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? REF2.
        eapply orutt_insert_value_loop; auto.
      + (* Select *)
        cbn.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? REF.
        destruct r2; dvalue_refine_strict_inv REF;
          try solve
            [ apply orutt_raise; auto
            ].
        { (* ix *)
          repeat break_match_goal;
            try solve
              [ apply orutt_raise; auto
              ];
            eapply H; eauto; repeat constructor.
        }

        { (* poison *)
          apply orutt_Ret.
          solve_dvalue_refine_strict.
        }

        { (* vector *)
          eapply orutt_bind;
            [ eapply H; eauto; repeat constructor | ].
          intros ? ? REF.

          eapply orutt_bind;
            [ eapply H; eauto; repeat constructor | ].
          intros ? ? REF2.

          destruct r2; dvalue_refine_strict_inv REF;
            try solve
              [ apply orutt_raise; auto
              ].

          { (* Poison *)
            apply orutt_Ret;
              solve_dvalue_refine_strict.
          }

          destruct r3;
            dvalue_refine_strict_inv REF2;
            try solve
              [ apply orutt_raise; auto
              ].

          { (* Poison *)
            apply orutt_Ret;
              solve_dvalue_refine_strict.
          }

          eapply orutt_bind with (RR:=Forall2 dvalue_refine_strict).
          {
            eapply orutt_eval_select_loop; auto.
          }

          intros ? ? REF.
          apply orutt_Ret.
          rewrite dvalue_refine_strict_equation.
          cbn.
          apply map_monad_oom_Forall2 in REF.
          rewrite REF.
          auto.
        }
      + (* ExtractByte *)
        cbn.
        apply orutt_raise; auto.
      + (* ConcatBytes *)
        Opaque concretize_uvalue_bytes_helper.
        Opaque IS2.MEM.CP.CONCBASE.concretize_uvalue_bytes_helper.
        Opaque IS1.MEM.CP.CONCBASE.concretize_uvalue_bytes_helper.
        cbn.
        pose proof (map_monad_oom_length _ _ _ H1) as LEN.
        setoid_rewrite LEN.
        rewrite sizeof_dtyp_fin_inf.
        break_match_goal.
        { (* Size and type match *)
          setoid_rewrite all_extract_bytes_from_uvalue_fin_inf; eauto.
          destruct (all_extract_bytes_from_uvalue dt uvs) eqn:HExtract;
            cbn.
          - apply all_extract_bytes_from_uvalue_success_inv in HExtract.
            destruct HExtract as (?&?&?); subst.
            destruct x; inv H1.
            repeat break_match_hyp_inv.
            uvalue_convert_strict_inv Heqo.
            apply H; auto.
            eapply uvalue_concat_bytes_strict_subterm.
            repeat constructor.
          - eapply orutt_bind with (RR:=dvalue_bytes_refine).
            2: { eapply orutt_dvalue_bytes_to_dvalue; eauto. }

            apply orutt_concretize_uvalue_bytes_helper; eauto.
            { intros u H0 uv_fin H2.
              apply H; auto.
              eapply uvalue_concat_bytes_strict_subterm; auto.
            }
            apply map_monad_oom_Forall2; auto.
            apply concretization_map_refine_empty.
        }

        { (* Size or type mismatch *)
          eapply orutt_bind with (RR:=dvalue_bytes_refine).
          2: eapply orutt_dvalue_bytes_to_dvalue; eauto.
          apply orutt_concretize_uvalue_bytes_helper; eauto.
          { intros u H0 uv_fin H2.
            apply H; auto.
            eapply uvalue_concat_bytes_strict_subterm; auto.
          }
          apply map_monad_oom_Forall2; auto.
          apply concretization_map_refine_empty.
        }

        Unshelve.
        eapply intptr_fin_inf; eauto.
  Qed.

  #[global] Hint Resolve
    orutt_concretize_uvalue
    : ORUTT.

  Lemma orutt_denote_concretize_if_no_undef_or_poison :
    forall E1 E2
      `{OOM1 : OOME -< E1} `{OOM2 : OOME -< E2}
      `{UB1 : UBE -< E1} `{UB2 : UBE -< E2}
      `{ERR1: FailureE -< E1} `{ERR2: FailureE -< E2}
      (pre : prerel E1 E2) (post : postrel E1 E2)
      (UBDISC : forall e1 e2, @subevent UBE E2 UB2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (ERRDISC : forall e1 e2, @subevent FailureE E2 ERR2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (UBINJ : pre void void (@subevent UBE E1 UB1 void (ThrowUB tt)) (@subevent UBE E2 UB2 void (ThrowUB tt)))
      (ERRINJ : pre void void (@subevent FailureE E1 ERR1 void (Throw tt)) (@subevent FailureE E2 ERR2 void (Throw tt)))
      u1 u2,
      uvalue_refine_strict u1 u2 ->
      orutt pre post uvalue_refine_strict
        (IS1.LLVM.D.concretize_if_no_undef_or_poison u1)
        (concretize_if_no_undef_or_poison u2)
        (OOM:=OOME).
  Proof.
    intros E1 E2 OOM1 OOM2 UB1 UB2 ERR1 ERR2 pre post UBDISC ERRDISC UBINJ ERRINJ u1 u2 REF.
    unfold IS1.LLVM.D.concretize_if_no_undef_or_poison,
      concretize_if_no_undef_or_poison.
    setoid_rewrite <- contains_undef_or_poison_E1_E2; eauto.
    break_match; break_match; try inv Heqb.
    - apply orutt_Ret; auto.
    - eapply orutt_bind with (RR:=dvalue_refine_strict).
      { apply orutt_concretize_uvalue; auto.
      }

      intros r1 r2 H.
      cbn.
      apply orutt_Ret.
      apply dvalue_refine_strict_dvalue_to_uvalue; auto.
  Qed.

  #[global] Hint Resolve
    orutt_denote_concretize_if_no_undef_or_poison
    : ORUTT.

  Ltac solve_orutt_denote_concretize_if_no_undef_or_poison :=
    eapply orutt_denote_concretize_if_no_undef_or_poison;
      try solve [ intros * CONTRA; inv CONTRA | constructor | auto ].

End ConcretizationRefine.
