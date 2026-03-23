From Stdlib Require Import
  Lia
  ZArith
  Program.Equality
  String
  List.

From ExtLib Require Import
  Structures.Monads
  Structures.Functor.

From Vellvm.Semantics Require Import
  MemoryAddress
  VellvmIntegers
  DynamicValues
  InterpretationStack
  TopLevel
  LLVMEvents.

From Vellvm Require Import
  TopLevelRefinements.

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
  ErrUbOomProp
  Monads
  MapMonadExtra.

From Vellvm.Semantics.InfiniteToFinite.LangRefine Require Import
  Events
  Sizeof
  Values
  Utils.

Import DynamicTypes.

From ITree Require Import
  ITree
  Basics
  Basics.HeterogeneousRelations
  Eq.Rutt
  Eq.RuttFacts
  Eq.Eqit
  Eq.EqAxiom.

Import MonadNotation.
Import ListNotations.
Open Scope list.

Module Type SelectRefine
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
  Import DVC.
  Import VAL_REF.

  Lemma eval_select_cond_fin_inf :
    forall a d d0 x,
      match a with
      | @DVALUE_I 1 i =>
          if (@Integers.unsigned 1 i =? 1)%Z
          then fun y : err_ub_oom dvalue => success_unERR_UB_OOM d = y
          else fun y : err_ub_oom dvalue => success_unERR_UB_OOM d0 = y
      | DVALUE_Poison t => fun y : err_ub_oom dvalue => success_unERR_UB_OOM (DVALUE_Poison t) = y
      | _ =>
          fun ue : err_ub_oom dvalue =>
            ERR_unERR_UB_OOM
              "concretize_uvalueM: ill-typed select, condition in vector was not poison or i1." = ue
      end x ->
      match fin_to_inf_dvalue a with
      | @DV1.DVALUE_I 1 i =>
          if (@Integers.unsigned 1 i =? 1)%Z
          then fun y : err_ub_oom DVCrev.DV2.dvalue => success_unERR_UB_OOM (fin_to_inf_dvalue d) = y
          else fun y : err_ub_oom DVCrev.DV2.dvalue => success_unERR_UB_OOM (fin_to_inf_dvalue d0) = y
      | DV1.DVALUE_Poison t => fun y : err_ub_oom DVCrev.DV2.dvalue => success_unERR_UB_OOM (DV1.DVALUE_Poison t) = y
      | _ =>
          fun ue : err_ub_oom DVCrev.DV2.dvalue =>
            ERR_unERR_UB_OOM
              "concretize_uvalueM: ill-typed select, condition in vector was not poison or i1." = ue
      end (fmap fin_to_inf_dvalue x).
  Proof.
    intros a d d0 x H.
    destruct a; subst.

    all:
      try solve
        [ unfold fin_to_inf_dvalue; break_match_goal; cbn; auto;
          break_match_hyp; clear Heqs; destruct p; clear e0;
          subst; cbn in e; inv e
        | unfold fin_to_inf_dvalue; break_match_goal; cbn; auto;
          break_match_hyp; clear Heqs; destruct p; clear e0;
          subst; cbn in e; break_match_hyp_inv
        ].

    { (* i1 *)
      rewrite_fin_to_inf_dvalue.
      break_match_hyp; subst; cbn; auto.
      break_match_hyp; subst; cbn; auto.
    }

    { (* Poison *)
      rewrite fin_to_inf_dvalue_poison.
      cbn.
      rewrite fin_to_inf_dvalue_poison.
      reflexivity.
    }
  Qed.

  Lemma eval_select_loop_fin_inf :
    forall (conds xs ys : list dvalue) (res : err_ub_oom (list dvalue)),
      (fix loop conds xs ys {struct conds} : ErrUbOomProp (list dvalue) :=
         match conds, xs, ys with
         | [], [], [] => @ret ErrUbOomProp Monad_ErrUbOomProp _ []
         | (c::conds), (x::xs), (y::ys) =>
             @bind ErrUbOomProp Monad_ErrUbOomProp _ _
               (match c with
                | DVALUE_Poison t =>
                    (* TODO: Should be the type of the result of the select... *)
                    @ret ErrUbOomProp Monad_ErrUbOomProp _ (DVALUE_Poison t)
                | @DVALUE_I 1 i =>
                    if (@Integers.unsigned 1 i =? 1)%Z
                    then @ret ErrUbOomProp Monad_ErrUbOomProp _ x
                    else @ret ErrUbOomProp Monad_ErrUbOomProp _ y
                | _ =>
                    fun ue =>
                      (raise_error "concretize_uvalueM: ill-typed select, condition in vector was not poison or i1." = ue)
                end)
               (fun selected =>
                  @bind ErrUbOomProp Monad_ErrUbOomProp _ _
                    (loop conds xs ys)
                    (fun rest =>
                       @ret ErrUbOomProp Monad_ErrUbOomProp _ (selected :: rest)))
         | _, _, _ =>
             fun ue => (raise_error "concretize_uvalueM: ill-typed vector select, length mismatch." = ue)
         end) conds xs ys res ->
      (fix loop conds xs ys {struct conds} : ErrUbOomProp (list DVCrev.DV2.dvalue) :=
         match conds, xs, ys with
         | [], [], [] => @ret ErrUbOomProp Monad_ErrUbOomProp _ []
         | (c::conds), (x::xs), (y::ys) =>
             @bind ErrUbOomProp Monad_ErrUbOomProp _ _
               (match c with
                | DV1.DVALUE_Poison t =>
                    (* TODO: Should be the type of the result of the select... *)
                    @ret ErrUbOomProp Monad_ErrUbOomProp _ (DV1.DVALUE_Poison t)
                | @DV1.DVALUE_I 1 i =>
                    if (@Integers.unsigned 1 i =? 1)%Z
                    then @ret ErrUbOomProp Monad_ErrUbOomProp _ x
                    else @ret ErrUbOomProp Monad_ErrUbOomProp _ y
                | _ =>
                    fun ue =>
                      (raise_error "concretize_uvalueM: ill-typed select, condition in vector was not poison or i1." = ue)
                end)
               (fun selected =>
                  @bind ErrUbOomProp Monad_ErrUbOomProp _ _
                    (loop conds xs ys)
                    (fun rest =>
                       @ret ErrUbOomProp Monad_ErrUbOomProp _ (selected :: rest)))
         | _, _, _ =>
             fun ue => (raise_error "concretize_uvalueM: ill-typed vector select, length mismatch." = ue)
         end) (map fin_to_inf_dvalue conds) (map fin_to_inf_dvalue xs) (map fin_to_inf_dvalue ys) (fmap (map fin_to_inf_dvalue) res).
  Proof.
    induction conds, xs, ys;
      intros res LOOP;
      cbn in *; subst; auto.

    repeat red in LOOP.
    destruct LOOP as (?&?&?&?&?).
    repeat red.

    exists (fmap fin_to_inf_dvalue x).
    exists (fun _ => fmap (fmap fin_to_inf_dvalue) res).
    split.
    apply (eval_select_cond_fin_inf _ _ _ _ H).
    split.
    subst; cbn.
    { destruct_err_ub_oom x; cbn; auto. }

    destruct_err_ub_oom x; cbn; auto.
    right; intros a0 ?; subst.
    repeat red.

    destruct H1 as [[] | H1].
    specialize (H1 _ eq_refl).

    repeat red in H1.
    destruct H1 as (?&?&?&?&?).

    pose proof H0 as LOOP.
    eapply IHconds in LOOP.
    exists ({|
             unERR_UB_OOM :=
               {|
                 EitherMonad.unEitherT :=
                   {|
                     EitherMonad.unEitherT :=
                       {|
                         EitherMonad.unEitherT :=
                           match
                             IdentityMonad.unIdent
                               (EitherMonad.unEitherT
                                  (EitherMonad.unEitherT (EitherMonad.unEitherT (unERR_UB_OOM x))))
                           with
                           | inl x => {| IdentityMonad.unIdent := inl x |}
                           | inr x =>
                               EitherMonad.unEitherT
                                 match x with
                                 | inl x0 =>
                                     {|
                                       EitherMonad.unEitherT :=
                                         {| IdentityMonad.unIdent := inr (inl x0) |}
                                     |}
                                 | inr x0 =>
                                     EitherMonad.unEitherT
                                       match x0 with
                                       | inl x1 =>
                                           {|
                                             EitherMonad.unEitherT :=
                                               {|
                                                 EitherMonad.unEitherT :=
                                                   {| IdentityMonad.unIdent := inr (inr (inl x1)) |}
                                               |}
                                           |}
                                       | inr x1 =>
                                           {|
                                             EitherMonad.unEitherT :=
                                               {|
                                                 EitherMonad.unEitherT :=
                                                   {|
                                                     IdentityMonad.unIdent :=
                                                       inr (inr (inr (map fin_to_inf_dvalue x1)))
                                                   |}
                                               |}
                                           |}
                                       end
                                 end
                           end
                       |}
                   |}
               |}
        |}).
    exists (fun elts => fmap (fmap fin_to_inf_dvalue) (x0 x1)).
    { destruct_err_ub_oom x; cbn; rewrite <- H1; cbn; auto.
      split; eauto.
      cbn in H1.
      split; eauto.

      right; intros ??; subst.
      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).
      rewrite <- H2.
      cbn.

      reflexivity.
    }
  Qed.

  Lemma eval_select_fin_inf :
    forall cond uv1_fin uv2_fin uv1_inf uv2_inf res
      (IH1 : forall dv_fin : dvalue,
          IS2.MEM.CP.CONC.concretize uv1_fin dv_fin ->
          IS1.MEM.CP.CONC.concretize uv1_inf (fin_to_inf_dvalue dv_fin))
      (IH2 : forall dv_fin : dvalue,
          IS2.MEM.CP.CONC.concretize uv2_fin dv_fin ->
          IS1.MEM.CP.CONC.concretize uv2_inf (fin_to_inf_dvalue dv_fin)),
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
        (fun (A : Type) (x ue : err_ub_oom A) => x = ue) cond uv1_fin uv2_fin (ret res) ->
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
        (fun (A : Type) (x ue : err_ub_oom A) => x = ue) (fin_to_inf_dvalue cond) uv1_inf uv2_inf (fmap fin_to_inf_dvalue (ret res)).
  Proof.
    intros cond uv1_fin uv2_fin uv1_inf uv2_inf res IH1 IH2 EVAL.
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

    { (* Poison *)
      rewrite fin_to_inf_dvalue_poison.
      cbn in *; subst; cbn; inv EVAL.
      rewrite fin_to_inf_dvalue_poison.
      reflexivity.
    }

    { (* Vector conditional *)
      rewrite IS2.MEM.CP.CONC.eval_select_equation in *.
      rewrite IS1.MEM.CP.CONC.eval_select_equation.

      repeat red in EVAL.
      destruct EVAL as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      destruct H1 as [[] | H1].
      specialize (H1 _ eq_refl).

      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.
      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).

      destruct x1;
        try (rewrite <- H2 in H5; inv H5).
      { (* Poison *)
        rewrite fin_to_inf_dvalue_vector.
        cbn.
        repeat red.

        exists (ret (fin_to_inf_dvalue (DVALUE_Poison t0))).
        exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 (DVALUE_Poison t0)))).

        split.
        eapply IH1; eauto.

        split.
        cbn in *; rewrite <- H2 in H1; inv H1; cbn.
        auto.

        right; intros ? ?; subst.
        repeat red.
        cbn in *.
        rewrite <- H2 in H1.
        cbn in H1.
        subst.

        exists (ret (fin_to_inf_dvalue x3)).
        exists (fun _ => (fmap fin_to_inf_dvalue (x2 x3))).
        cbn; rewrite <- H2, <- H1; cbn.

        split.
        eapply IH2; eauto.

        split; eauto.
        right; intros ? ?; subst.
        rewrite fin_to_inf_dvalue_poison.
        reflexivity.
      }

      (* Vector *)
      destruct x3;
        try (rewrite <- H2 in H5; inv H5).
      { (* Poison *)
        rewrite fin_to_inf_dvalue_vector.
        cbn.
        repeat red.

        exists (ret (fin_to_inf_dvalue (DVALUE_Vector t0 elts0))).
        exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 (DVALUE_Vector t0 elts0)))).

        split.
        eapply IH1; eauto.

        split.
        cbn in *; rewrite <- H2 in H1; inv H1; cbn.
        auto.

        right; intros ? ?; subst.
        repeat red.
        cbn in *.
        rewrite <- H2 in H1.
        cbn in H1.
        subst.

        exists (ret (fin_to_inf_dvalue (DVALUE_Poison t1))).
        exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 (DVALUE_Poison t1)))).

        split.
        eapply IH2; eauto.

        rewrite fin_to_inf_dvalue_poison, <- H2, <- H1; cbn.
        split; eauto.
        right; intros ? ?; subst.
        rewrite fin_to_inf_dvalue_vector, fin_to_inf_dvalue_poison.
        reflexivity.
      }

      repeat red in H2.
      destruct H2 as (?&?&?&?&?).

      rename elts0 into elts1_fin.
      rename elts1 into elts2_fin.
      pose proof (eval_select_loop_fin_inf elts elts1_fin elts2_fin x H2) as EVAL.

      subst.
      rewrite fin_to_inf_dvalue_vector.
      cbn.

      pose proof (IH1 _ H) as IHelts1.
      pose proof (IH2 _ H0) as IHelts2.

      cbn in H1.
      remember (x2 (DVALUE_Vector t1 elts2_fin)) as x2elts.
      destruct_err_ub_oom x2elts; inv H5.
      cbn in H1.

      repeat red.
      exists (ret (fin_to_inf_dvalue (DVALUE_Vector t0 elts1_fin))).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 (DVALUE_Vector t0 elts1_fin)))).
      cbn; rewrite <- H1; cbn.
      split; eauto.
      split; eauto.

      right; intros a ?; subst.
      repeat red.
      exists (ret (fin_to_inf_dvalue (DVALUE_Vector t1 elts2_fin))).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 (DVALUE_Vector t1 elts2_fin)))).
      cbn; rewrite <- Heqx2elts; cbn.
      split; eauto.
      split; eauto.

      right; intros a ?; subst.
      do 2 rewrite fin_to_inf_dvalue_vector.
      repeat red.
      exists (fmap (map fin_to_inf_dvalue) x).
      exists (fun elts => ret (DV1.DVALUE_Vector t0 elts)).
      split; eauto.
      split; eauto.

      destruct_err_ub_oom x; inv H3.
      destruct H4 as [[] | H4].
      specialize (H4 _ eq_refl).
      rewrite <- H4 in H6.
      inv H6.
      cbn.
      rewrite fin_to_inf_dvalue_vector.
      reflexivity.
    }
  Qed.

  (* TODO: Move this *)
  Lemma orutt_eval_select_loop :
    forall E1 E2
      `{OOM1 : OOME -< E1} `{OOM2 : OOME -< E2}
      `{UB1 : UBE -< E1} `{UB2 : UBE -< E2}
      `{ERR1: FailureE -< E1} `{ERR2: FailureE -< E2}
      (pre : prerel E1 E2) (post : postrel E1 E2)
      (UBDISC : forall e1 e2, @subevent UBE E2 UB2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (ERRDISC : forall e1 e2, @subevent FailureE E2 ERR2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (UBINJ : pre void void (@subevent UBE E1 UB1 void (ThrowUB tt)) (@subevent UBE E2 UB2 void (ThrowUB tt)))
      (ERRINJ : pre void void (@subevent FailureE E1 ERR1 void (Throw tt)) (@subevent FailureE E2 ERR2 void (Throw tt)))
      cnds1 xs1 ys1 cnds2 xs2 ys2,
      map_monad dvalue_convert_strict cnds1 = NoOom cnds2 ->
      map_monad dvalue_convert_strict xs1 = NoOom xs2 ->
      map_monad dvalue_convert_strict ys1 = NoOom ys2 ->
      orutt (OOM:=OOME) pre post (Forall2 dvalue_refine_strict)
        ((fix loop (conds xs ys : list DV1.dvalue) {struct conds} :
           itree _ (list DV1.dvalue) :=
            match conds with
            | [] =>
                match xs with
                | [] =>
                    fun ys0 : list DV1.dvalue =>
                      match ys0 with
                      | [] => Ret []
                      | _ :: _ =>
                          LLVMEvents.raise "concretize_uvalueM: ill-typed vector select, length mismatch."
                      end
                | _ :: _ =>
                    fun _ : list DV1.dvalue =>
                      LLVMEvents.raise "concretize_uvalueM: ill-typed vector select, length mismatch."
                end ys
            | c :: conds0 =>
                match xs with
                | [] => LLVMEvents.raise "concretize_uvalueM: ill-typed vector select, length mismatch."
                | x5 :: xs0 =>
                    match ys with
                    | [] =>
                        LLVMEvents.raise "concretize_uvalueM: ill-typed vector select, length mismatch."
                    | y :: ys0 =>
                        ITree.bind
                          match c with
                          | @DV1.DVALUE_I 1 i =>
                              if (@Integers.unsigned 1 i =? 1)%Z then Ret x5 else Ret y
                          | DV1.DVALUE_Poison t => Ret (DV1.DVALUE_Poison t)
                          | _ =>
                              LLVMEvents.raise
                                "concretize_uvalueM: ill-typed select, condition in vector was not poison or i1."
                          end
                          (fun selected : DV1.dvalue =>
                             ITree.bind (loop conds0 xs0 ys0)
                               (fun rest : list DV1.dvalue => Ret (selected :: rest)))
                    end
                end
            end) cnds1 xs1 ys1)
        ((fix loop (conds xs ys : list dvalue) {struct conds} : itree _ (list dvalue) :=
            match conds with
            | [] =>
                match xs with
                | [] =>
                    fun ys0 : list dvalue =>
                      match ys0 with
                      | [] => Ret []
                      | _ :: _ =>
                          LLVMEvents.raise "concretize_uvalueM: ill-typed vector select, length mismatch."
                      end
                | _ :: _ =>
                    fun _ : list dvalue =>
                      LLVMEvents.raise "concretize_uvalueM: ill-typed vector select, length mismatch."
                end ys
            | c :: conds0 =>
                match xs with
                | [] => LLVMEvents.raise "concretize_uvalueM: ill-typed vector select, length mismatch."
                | x5 :: xs0 =>
                    match ys with
                    | [] =>
                        LLVMEvents.raise "concretize_uvalueM: ill-typed vector select, length mismatch."
                    | y :: ys0 =>
                        ITree.bind
                          match c with
                          | @DVALUE_I 1 i => if (@Integers.unsigned 1 i =? 1)%Z then Ret x5 else Ret y
                          | DVALUE_Poison t => Ret (DVALUE_Poison t)
                          | _ =>
                              LLVMEvents.raise
                                "concretize_uvalueM: ill-typed select, condition in vector was not poison or i1."
                          end
                          (fun selected : dvalue =>
                             ITree.bind (loop conds0 xs0 ys0)
                               (fun rest : list dvalue => Ret (selected :: rest)))
                    end
                end
            end) cnds2 xs2 ys2).
  Proof.
    intros E1 E2 OOM1 OOM2 UB1 UB2 ERR1 ERR2 pre post UBDISC ERRDISC UBINJ ERRINJ cnds1.
    induction cnds1, xs1, ys1;
      intros cnds2 xs2 ys2 REF_CNDS REF_XS REF_YS;
      cbn in *; subst; inv REF_CNDS; inv REF_XS; inv REF_YS;
      repeat break_match_hyp_inv; cbn;
      try solve
        [ apply orutt_raise; auto
        ].

    apply orutt_Ret; constructor.

    specialize (IHcnds1 xs1 ys1 l1 l0 l eq_refl Heqo2 Heqo0).
    eapply orutt_bind with (RR:=dvalue_refine_strict).
    { destruct d3;
        dvalue_convert_strict_inv Heqo3; cbn;
        try solve
          [ repeat break_match; (apply orutt_raise; auto)
          ].
      - repeat break_match; try (apply orutt_raise; auto);
          apply orutt_Ret; eauto.
      - apply orutt_Ret; eauto.
        solve_dvalue_refine_strict.
    }

    intros ? ? ?.
    eapply orutt_bind with (RR:=Forall2 dvalue_refine_strict); eauto.
    intros ? ? ?.
    eapply orutt_Ret.
    apply Forall2_cons; eauto.
  Qed.

End SelectRefine.
