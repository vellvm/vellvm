From Stdlib Require Import
  Lia
  ZArith
  Program.Equality
  List.

From ExtLib Require Import
  Structures.Monads
  Structures.Functor.

From Vellvm.Semantics Require Import
  MemoryAddress
  VellvmIntegers
  DynamicValues
  InterpretationStack
  TopLevel.

From Vellvm.Semantics.InfiniteToFinite.Conversions Require Import
  BaseConversions
  DvalueConversions
  EventConversions.

From Vellvm.Utils Require Import
  Error
  Tactics
  ListUtil.

From Vellvm.Semantics.InfiniteToFinite.LangRefine Require Import
  Events
  Sizeof
  Values.

Import MonadNotation.

Module Type VectorsRefine
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
  Import VAL_REF.

  Lemma vec_loop_fin_inf :
    forall f_fin f_inf xs ys res,
      (forall dv1_fin dv2_fin res_fin dv1_inf dv2_inf,
          f_fin dv1_fin dv2_fin = ret res_fin ->
          fin_to_inf_dvalue dv1_fin = dv1_inf ->
          fin_to_inf_dvalue dv2_fin = dv2_inf ->
          f_inf dv1_inf dv2_inf = ret (fin_to_inf_dvalue res_fin)) ->
      @vec_loop _ err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) f_fin (combine xs ys) = ret res ->
      @DV1.vec_loop _ err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) f_inf (combine (map fin_to_inf_dvalue xs) (map fin_to_inf_dvalue ys)) = ret (map fin_to_inf_dvalue res).
  Proof.
    intros f_fin f_inf xs ys res F RES.

    remember (xs, ys) as ZIP.
    replace xs with (fst ZIP) by (subst; cbn; auto).
    replace ys with (snd ZIP) by (subst; cbn; auto).
    replace xs with (fst ZIP) in RES by (subst; cbn; auto).
    replace ys with (snd ZIP) in RES by (subst; cbn; auto).
    clear HeqZIP xs ys.

    generalize dependent res.
    induction ZIP using double_list_rect; intros res RES;
      try solve [cbn in *; inv RES; auto].
    - (* Both cons *)
      unfold fst, snd in *.
      repeat rewrite map_cons.
      repeat rewrite combine_cons.
      repeat rewrite vec_loop_cons.
      rewrite combine_cons in RES.
      rewrite vec_loop_cons in RES.
      cbn in RES.
      remember (vec_loop f_fin (combine xs ys)) as res'.
      destruct_err_ub_oom res';
        cbn in RES; inv RES.
      specialize (IHZIP _ eq_refl).
      cbn.
      (* Not sure why rewrite won't work... *)
      replace
        (@vec_loop DVCrev.DV2.dvalue err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) f_inf
           (@combine DVCrev.DV2.dvalue DVCrev.DV2.dvalue (@map DVCrev.DV1.dvalue DVCrev.DV2.dvalue fin_to_inf_dvalue xs)
              (@map DVCrev.DV1.dvalue DVCrev.DV2.dvalue fin_to_inf_dvalue ys)))
        with (@ret err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
                (list DVCrev.DV2.dvalue) (@map DVCrev.DV1.dvalue DVCrev.DV2.dvalue fin_to_inf_dvalue res'0)); cbn; eauto.

      remember (f_fin x y) as res_start.
      destruct_err_ub_oom res_start; inv H0.
      symmetry in Heqres_start.
      eapply F in Heqres_start; eauto.

      rewrite Heqres_start.
      cbn.
      reflexivity.
  Qed.

  Lemma vec_loop_ub_fin_inf :
    forall f_fin f_inf xs ys ub_msg,
      (forall dv1_fin dv2_fin res_fin dv1_inf dv2_inf,
          f_fin dv1_fin dv2_fin = ret res_fin ->
          fin_to_inf_dvalue dv1_fin = dv1_inf ->
          fin_to_inf_dvalue dv2_fin = dv2_inf ->
          f_inf dv1_inf dv2_inf = ret (fin_to_inf_dvalue res_fin)) ->
      (forall dv1_fin dv2_fin ub_msg dv1_inf dv2_inf,
          f_fin dv1_fin dv2_fin = UB_unERR_UB_OOM ub_msg ->
          fin_to_inf_dvalue dv1_fin = dv1_inf ->
          fin_to_inf_dvalue dv2_fin = dv2_inf ->
          f_inf dv1_inf dv2_inf = UB_unERR_UB_OOM ub_msg) ->
      @vec_loop _ err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) f_fin (combine xs ys) = UB_unERR_UB_OOM ub_msg ->
      @DV1.vec_loop _ err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) f_inf (combine (map fin_to_inf_dvalue xs) (map fin_to_inf_dvalue ys)) = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros f_fin f_inf xs ys res SUCCESS UB RES.

    remember (xs, ys) as ZIP.
    replace xs with (fst ZIP) by (subst; cbn; auto).
    replace ys with (snd ZIP) by (subst; cbn; auto).
    replace xs with (fst ZIP) in RES by (subst; cbn; auto).
    replace ys with (snd ZIP) in RES by (subst; cbn; auto).
    clear HeqZIP xs ys.

    generalize dependent res.
    induction ZIP using double_list_rect; intros res RES;
      try solve [cbn in *; inv RES; auto].
    - (* Both cons *)
      unfold fst, snd in *.
      repeat rewrite map_cons.
      repeat rewrite combine_cons.
      repeat rewrite vec_loop_cons.
      rewrite combine_cons in RES.
      rewrite vec_loop_cons in RES.
      cbn in RES.
      remember (@vec_loop DVCrev.DV1.dvalue err_ub_oom
                  (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) f_fin
                  (@combine DVCrev.DV1.dvalue DVCrev.DV1.dvalue xs ys)) as res'.
      destruct_err_ub_oom res';
        cbn in RES; inv RES;
        symmetry in Heqres'.
      { specialize (IHZIP res eq_refl).
        unfold DV1.vec_loop in *.
        unfold vec_loop.
        rewrite IHZIP; reflexivity.
      }


      clear IHZIP.
      remember (f_fin x y) as fin.
      destruct_err_ub_oom fin; inv H0.
      erewrite vec_loop_fin_inf; eauto.
      2: apply Heqres'.
      cbn.

      erewrite UB; cbn; eauto.
  Qed.

  Lemma vec_loop_err_fin_inf :
    forall f_fin f_inf xs ys err_msg,
      (forall dv1_fin dv2_fin res_fin dv1_inf dv2_inf,
          f_fin dv1_fin dv2_fin = ret res_fin ->
          fin_to_inf_dvalue dv1_fin = dv1_inf ->
          fin_to_inf_dvalue dv2_fin = dv2_inf ->
          f_inf dv1_inf dv2_inf = ret (fin_to_inf_dvalue res_fin)) ->
      (forall dv1_fin dv2_fin ub_msg dv1_inf dv2_inf,
          f_fin dv1_fin dv2_fin = ERR_unERR_UB_OOM ub_msg ->
          fin_to_inf_dvalue dv1_fin = dv1_inf ->
          fin_to_inf_dvalue dv2_fin = dv2_inf ->
          f_inf dv1_inf dv2_inf = ERR_unERR_UB_OOM ub_msg) ->
      @vec_loop _ err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) f_fin (combine xs ys) = ERR_unERR_UB_OOM err_msg ->
      @DV1.vec_loop _ err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) f_inf (combine (map fin_to_inf_dvalue xs) (map fin_to_inf_dvalue ys)) = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros f_fin f_inf xs ys res SUCCESS UB RES.

    remember (xs, ys) as ZIP.
    replace xs with (fst ZIP) by (subst; cbn; auto).
    replace ys with (snd ZIP) by (subst; cbn; auto).
    replace xs with (fst ZIP) in RES by (subst; cbn; auto).
    replace ys with (snd ZIP) in RES by (subst; cbn; auto).
    clear HeqZIP xs ys.

    generalize dependent res.
    induction ZIP using double_list_rect; intros res RES;
      try solve [cbn in *; inv RES; auto].
    - (* Both cons *)
      unfold fst, snd in *.
      repeat rewrite map_cons.
      repeat rewrite combine_cons.
      repeat rewrite vec_loop_cons.
      rewrite combine_cons in RES.
      rewrite vec_loop_cons in RES.
      cbn in RES.
      remember (@vec_loop DVCrev.DV1.dvalue err_ub_oom
                  (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) f_fin
                  (@combine DVCrev.DV1.dvalue DVCrev.DV1.dvalue xs ys)) as res'.
      destruct_err_ub_oom res';
        cbn in RES; inv RES;
        symmetry in Heqres'.
      { specialize (IHZIP res eq_refl).
        unfold DV1.vec_loop in *.
        unfold vec_loop.
        rewrite IHZIP; reflexivity.
      }


      clear IHZIP.
      remember (f_fin x y) as fin.
      destruct_err_ub_oom fin; inv H0.
      erewrite vec_loop_fin_inf; eauto.
      2: apply Heqres'.
      cbn.

      erewrite UB; cbn; eauto.
  Qed.
End VectorsRefine.
