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
  Sizeof.

From Vellvm.Utils Require Import
  Error
  Tactics
  Monads
  MapMonadExtra
  OOMRutt
  OOMRuttProps
  ListUtil
  RuttPropsExtra
  VellvmRelations.

From ITree Require Import
  ITree
  Basics.HeterogeneousRelations
  Eq.Rutt
  Eq.RuttFacts
  Eq.Eqit.

Import ListNotations.

Module Type ValueRefine
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
  (ER : EventRefine IS1 IS2 LLVM1 LLVM2 AC1 AC2 DVC DVCrev EC).
  Import DVC.
  Import IS2.LP.
  Import IS2.LP.DV.
  Import IS2.LLVM.D.
  Import ER.
  Import IPS.
  Import ADDR.

  Module DVCSafe := DVConvertSafe IS2.LP IS1.LP AC2 AC1 ACS IPS DVCrev DVC.
  Import DVCSafe.

  Import SIZEOF_REF.

  (* A lot of these seem to belong in DvalueConversions.v, but those modules are a mess *)

  (* TODO: Move this? *)
  Ltac unfold_dvalue_refine_strict :=
    rewrite dvalue_refine_strict_equation in *; cbn in *.

  Ltac unfold_dvalue_refine_strict_goal :=
    rewrite dvalue_refine_strict_equation; cbn.

  Ltac unfold_dvalue_refine_strict_in H :=
    rewrite dvalue_refine_strict_equation in H; cbn in H.

  Ltac unfold_uvalue_refine_strict :=
    rewrite uvalue_refine_strict_equation in *; cbn in *.

  Ltac unfold_uvalue_refine_strict_goal :=
    rewrite uvalue_refine_strict_equation; cbn.

  Ltac unfold_uvalue_refine_strict_in H :=
    rewrite uvalue_refine_strict_equation in H; cbn in H.

  (* TODO: move this ltac, and probably use more *)
  Ltac rewrite_uvalue_convert_strict :=
    repeat
      match goal with
      | H: uvalue_convert_strict _ = _ |- _ =>
          rewrite H; clear H
      end.


  Ltac solve_pick_uvalue_orutt :=
    apply orutt_trigger; cbn;
    [ cbn;
      unfold uvalue_refine_strict; cbn;
      repeat rewrite_uvalue_convert_strict; auto
    | intros [t1] [t2] [REF1 REF2];
      cbn; auto
    | intros o CONTRA;
      inv CONTRA
    ].


  Lemma is_concrete_l:
    forall (l : list DV1.uvalue) (l' : list DV2.uvalue),
      Forall2 (fun (a : DV1.uvalue) (b : DV2.uvalue) => uvalue_convert_strict a = NoOom b) l l' ->
      forallb DV1.is_concrete l = true ->
      forallb is_concrete l' = true.
  Proof.
    intros l l' H.
    induction H; intros HL.
    - reflexivity.
    - cbn in *.
      apply andb_prop in HL.
      destruct HL as [HX HL].
      specialize (uvalue_refine_strict_preserves_is_concrete x y _ H HX) as HY.
      rewrite HY. clear H HX HY.
      rewrite IHForall2; auto.
  Qed.


  Lemma is_concrete_l_false:
    forall (fields : list DV1.uvalue) (l : list DV2.uvalue),
      Forall2 (fun (a : DV1.uvalue) (b : DV2.uvalue) => uvalue_convert_strict a = NoOom b) fields l ->
      forallb DV1.is_concrete fields = false ->
      forallb is_concrete l = true
      -> False.
  Proof.
    intros fields l H.
    induction H; intros HF HL.
    - inversion HF.
    - simpl in *.
      apply Bool.andb_false_elim in HF.
      apply andb_prop in HL.
      destruct HL as [HY HL].
      destruct HF as [HF | HF].
      + rewrite (uvalue_refine_strict_preserves_is_concrete _ _ false H HF) in HY.
        inversion HY.
      + eapply IHForall2; eauto.
  Qed.

  (* SAZ: This could be significantly generalized. *)
  Lemma map_dvalue_convert_strict_succeeds:
    forall (fields : list DV1.uvalue) (l : list DV2.uvalue),
      Forall2 (fun (a : DV1.uvalue) (b : DV2.uvalue) => uvalue_convert_strict a = NoOom b) fields l ->
      forall l0 : list DV1.dvalue,
        Forall2
          (fun (a : DV1.uvalue) (b : DV1.dvalue) =>
             DV1.uvalue_to_dvalue a = inr b) fields l0 ->
        forall l1 : list dvalue,
          map_monad uvalue_to_dvalue l = inr l1 -> map_monad dvalue_convert_strict l0 = NoOom l1.
  Proof.
    intros fields l Heqo l0 Heqs l1 Heqs0.
    rewrite map_monad_err_Forall2 in Heqs0.
    rewrite map_monad_oom_Forall2.
    revert l0 Heqs l1 Heqs0.
    induction Heqo; intros; inversion Heqs; inversion Heqs0; subst.
    - constructor.
    - constructor; eauto.
      clear Heqo IHHeqo Heqs Heqs0 H4 H9 l l' l'0 l'1.
      destruct (uvalue_to_dvalue_dvalue_refine_strict _ _ _ H H2) as [z [HZ HRZ]].
      unfold dvalue_refine_strict in HRZ.
      rewrite H7 in HZ. inversion HZ.
      auto.
  Qed.


  (* TODO: Should I move this out of LangRefine and into some kind of
     utility module based on DvalueConversions.v? *)
  Lemma pick_your_poison_orutt :
    forall r1 r2,
      uvalue_refine_strict r1 r2 ->
      orutt exp_E_refine_strict exp_E_res_refine_strict
        dvalue_refine_strict (IS1.LLVM.D.pick_your_poison r1)
        (pick_your_poison r2)
        (OOM:=OOME).
  Proof.
    intros r1.
    unfold pick_your_poison, IS1.LLVM.D.pick_your_poison.
    destruct r1; intros r2 HRS;
    rewrite uvalue_refine_strict_equation in HRS; cbn in HRS;
      try solve
        [
          inv HRS; cbn;
          apply orutt_Ret;
          rewrite dvalue_refine_strict_equation; cbn; auto
        | break_match_hyp_inv;
          cbn;
          apply orutt_Ret;
          rewrite dvalue_refine_strict_equation;
          cbn;
          rewrite Heqo;
          reflexivity
        | repeat break_match_hyp_inv;
          cbn in *;
          eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2));
            cbn;
          [ solve_pick_uvalue_orutt
          | intros [?r1] [?r2] ?H0;
            cbn in *;
            apply orutt_Ret; auto
          ]
        ].
    - (* Poison *)
      inv HRS; cbn.
      eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)); eauto.
      { (* pick_uvalue *)
        apply orutt_trigger; cbn.
        unfold uvalue_refine_strict; cbn; reflexivity.
        intros [t1] [t2] [REF1 REF2].
        cbn; auto.
        intros o CONTRA.
        inv CONTRA.
      }

      intros r1 r2 H.
      destruct r1, r2.
      cbn in *.
      apply orutt_Ret; auto.

    - (* Undef *)
      inv HRS; cbn.
      eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)); eauto.
      { (* pick_uvalue *)
        apply orutt_trigger; cbn.
        unfold uvalue_refine_strict; cbn; reflexivity.
        intros [t1] [t2] [REF1 REF2].
        cbn; auto.
        intros o CONTRA.
        inv CONTRA.
      }

      intros r1 r2 H.
      destruct r1, r2.
      cbn in *.
      apply orutt_Ret; auto.

    - (* Structs *)
      break_match_hyp; inv HRS; cbn.
      rewrite map_monad_oom_Forall2 in Heqo.
      unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick.
      cbn.
      break_match_goal.
      + specialize (is_concrete_l fields l Heqo Heqb) as HL.
        rewrite HL.
        clear Heqb HL.
        break_match_goal.
        * assert (exists v, map_monad uvalue_to_dvalue l = inl v).
          { revert s Heqs.
            induction Heqo; intros; [inversion Heqs|].
            cbn in Heqs.
            cbn.
            repeat break_match_hyp_inv.
            -- destruct (uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ H Heqs0).
               exists x0. rewrite H0. reflexivity.
            -- break_match_goal; [eexists; eauto|].
               destruct (IHHeqo s eq_refl) as [s' EQ].
               exists s'. rewrite EQ. reflexivity.
          }
          destruct H as [s' EQ].
          rewrite EQ.
          cbn.
          apply orutt_raise; [intros; intro C; inversion C | cbn; auto].
        * cbn.
          rewrite map_monad_err_Forall2 in Heqs.
          break_match_goal; cbn.
          -- assert False.
             { revert s l0 Heqs Heqs0.
               induction Heqo; intros; [inversion Heqs0|].
               cbn in Heqs0.
               inversion Heqs; subst.
               repeat break_match_hyp_inv.
               ++ destruct (uvalue_to_dvalue_dvalue_refine_strict _ _ _ H H2) as [v [C _]].
                  rewrite Heqs1 in C.
                  inversion C.
               ++ eapply IHHeqo; eauto.
             }
             inversion H.
          -- apply orutt_Ret.
             unfold dvalue_refine_strict.
             cbn.
             erewrite map_dvalue_convert_strict_succeeds; eauto.
      + break_match_goal.
        * assert False by (eapply is_concrete_l_false; eauto).
          inversion H.
        * apply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
          { (* Pick uvalue *)
            apply orutt_trigger; cbn.
            -- unfold uvalue_refine_strict; cbn.
               break_match_goal.
               ++ rewrite map_monad_oom_Forall2 in Heqo0.
                  clear Heqb Heqb0.
                  assert (l0 = l).
                  { revert l0 Heqo0.
                    induction Heqo; intros; inversion Heqo0; subst; auto.
                    specialize (uvalue_refine_strict_R2_injective _ _ _ _ H H2) as [EQ _].
                    rewrite (EQ eq_refl) in *; clear EQ.
                    erewrite (IHHeqo l'0); eauto.
                  }
                  rewrite H; auto.
               ++  apply map_monad_OOM_fail in Heqo0.
                   destruct Heqo0 as [dv [HI HS]].
                   destruct (Forall2_In _ _ _ _ HI Heqo) as [dv' [_ C]].
                   rewrite HS in C. inversion C.
            -- intros [t1] [t2] [REF1 REF2].
               cbn; auto.
            --  intros o.
                intro C.
                inv C.
          }

          intros [r1] [r2] H0.
          cbn in *.
          apply orutt_Ret; auto.

    - (* Packed Structs *)
      break_match_hyp; inv HRS; cbn.
      rewrite map_monad_oom_Forall2 in Heqo.
      unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick.
      cbn.
      break_match_goal.
      + specialize (is_concrete_l fields l Heqo Heqb) as HL.
        rewrite HL.
        clear Heqb HL.
        break_match_goal.
        * assert (exists v, map_monad uvalue_to_dvalue l = inl v).
          { revert s Heqs.
            induction Heqo; intros; [inversion Heqs|].
            cbn in Heqs.
            cbn.
            repeat break_match_hyp_inv.
            -- destruct (uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ H Heqs0).
               exists x0. rewrite H0. reflexivity.
            -- break_match_goal; [eexists; eauto|].
               destruct (IHHeqo s eq_refl) as [s' EQ].
               exists s'. rewrite EQ. reflexivity.
          }
          destruct H as [s' EQ].
          rewrite EQ.
          cbn.
          apply orutt_raise; [intros; intro C; inversion C | cbn; auto].
        * cbn.
          rewrite map_monad_err_Forall2 in Heqs.
          break_match_goal; cbn.
          -- assert False.
             { revert s l0 Heqs Heqs0.
               induction Heqo; intros; [inversion Heqs0|].
               cbn in Heqs0.
               inversion Heqs; subst.
               repeat break_match_hyp_inv.
               ++ destruct (uvalue_to_dvalue_dvalue_refine_strict _ _ _ H H2) as [v [C _]].
                  rewrite Heqs1 in C.
                  inversion C.
               ++ eapply IHHeqo; eauto.
             }
             inversion H.
          -- apply orutt_Ret.
             unfold dvalue_refine_strict.
             cbn.
             erewrite map_dvalue_convert_strict_succeeds; eauto.
      + break_match_goal.
        * assert False by (eapply is_concrete_l_false; eauto).
          inversion H.
        * apply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
          { (* Pick uvalue *)
            apply orutt_trigger; cbn.
            -- unfold uvalue_refine_strict. cbn.

               break_match_goal.
               ++ rewrite map_monad_oom_Forall2 in Heqo0.
                  clear Heqb Heqb0.
                  assert (l0 = l).
                  { revert l0 Heqo0.
                    induction Heqo; intros; inversion Heqo0; subst; auto.
                    specialize (uvalue_refine_strict_R2_injective _ _ _ _ H H2) as [EQ _].
                    rewrite (EQ eq_refl) in *; clear EQ.
                    erewrite (IHHeqo l'0); eauto.
                  }
                  rewrite H; auto.
               ++  apply map_monad_OOM_fail in Heqo0.
                   destruct Heqo0 as [dv [HI HS]].
                   destruct (Forall2_In _ _ _ _ HI Heqo) as [dv' [_ C]].
                   rewrite HS in C. inversion C.
            -- intros [t1] [t2] [REF1 REF2].
               cbn; auto.
            --  intros o.
                intro C.
                inv C.
          }

          intros [r1] [r2] H0.
          cbn in *.
          apply orutt_Ret; auto.

    - (* Arrays *)
      break_match_hyp; inv HRS; cbn.
      rewrite map_monad_oom_Forall2 in Heqo.
      unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick.
      cbn.
      break_match_goal.
      + specialize (is_concrete_l elts l Heqo Heqb) as HL.
        rewrite HL.
        clear Heqb HL.
        break_match_goal.
        * assert (exists v, map_monad uvalue_to_dvalue l = inl v).
          { revert s Heqs.
            induction Heqo; intros; [inversion Heqs|].
            cbn in Heqs.
            cbn.
            repeat break_match_hyp_inv.
            -- destruct (uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ H Heqs0).
               exists x0. rewrite H0. reflexivity.
            -- break_match_goal; [eexists; eauto|].
               destruct (IHHeqo s eq_refl) as [s' EQ].
               exists s'. rewrite EQ. reflexivity.
          }
          destruct H as [s' EQ].
          rewrite EQ.
          cbn.
          apply orutt_raise; [intros; intro C; inversion C | cbn; auto].
        * cbn.
          rewrite map_monad_err_Forall2 in Heqs.
          break_match_goal; cbn.
          -- assert False.
             { revert s l0 Heqs Heqs0.
               induction Heqo; intros; [inversion Heqs0|].
               cbn in Heqs0.
               inversion Heqs; subst.
               repeat break_match_hyp_inv.
               ++ destruct (uvalue_to_dvalue_dvalue_refine_strict _ _ _ H H2) as [v [C _]].
                  rewrite Heqs1 in C.
                  inversion C.
               ++ eapply IHHeqo; eauto.
             }
             inversion H.
          -- apply orutt_Ret.
             unfold dvalue_refine_strict.
             cbn.
             erewrite map_dvalue_convert_strict_succeeds; eauto.
      + break_match_goal.
        * assert False by (eapply is_concrete_l_false; eauto).
          inversion H.
        * apply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
          { (* Pick uvalue *)
            apply orutt_trigger; cbn.
            -- unfold uvalue_refine_strict. cbn.

               break_match_goal.
               ++ rewrite map_monad_oom_Forall2 in Heqo0.
                  clear Heqb Heqb0.
                  assert (l0 = l).
                  { revert l0 Heqo0.
                    induction Heqo; intros; inversion Heqo0; subst; auto.
                    specialize (uvalue_refine_strict_R2_injective _ _ _ _ H H2) as [EQ _].
                    rewrite (EQ eq_refl) in *; clear EQ.
                    erewrite (IHHeqo l'0); eauto.
                  }
                  rewrite H; auto.
               ++  apply map_monad_OOM_fail in Heqo0.
                   destruct Heqo0 as [dv [HI HS]].
                   destruct (Forall2_In _ _ _ _ HI Heqo) as [dv' [_ C]].
                   rewrite HS in C. inversion C.
            -- intros [t1] [t2] [REF1 REF2].
               cbn; auto.
            --  intros o.
                intro C.
                inv C.
          }

          intros [r1] [r2] H0.
          cbn in *.
          apply orutt_Ret; auto.

    - (* Arrays *)
      break_match_hyp; inv HRS; cbn.
      rewrite map_monad_oom_Forall2 in Heqo.
      unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick.
      cbn.
      break_match_goal.
      + specialize (is_concrete_l elts l Heqo Heqb) as HL.
        rewrite HL.
        clear Heqb HL.
        break_match_goal.
        * assert (exists v, map_monad uvalue_to_dvalue l = inl v).
          { revert s Heqs.
            induction Heqo; intros; [inversion Heqs|].
            cbn in Heqs.
            cbn.
            repeat break_match_hyp_inv.
            -- destruct (uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ H Heqs0).
               exists x0. rewrite H0. reflexivity.
            -- break_match_goal; [eexists; eauto|].
               destruct (IHHeqo s eq_refl) as [s' EQ].
               exists s'. rewrite EQ. reflexivity.
          }
          destruct H as [s' EQ].
          rewrite EQ.
          cbn.
          apply orutt_raise; [intros; intro C; inversion C | cbn; auto].
        * cbn.
          rewrite map_monad_err_Forall2 in Heqs.
          break_match_goal; cbn.
          -- assert False.
             { revert s l0 Heqs Heqs0.
               induction Heqo; intros; [inversion Heqs0|].
               cbn in Heqs0.
               inversion Heqs; subst.
               repeat break_match_hyp_inv.
               ++ destruct (uvalue_to_dvalue_dvalue_refine_strict _ _ _ H H2) as [v [C _]].
                  rewrite Heqs1 in C.
                  inversion C.
               ++ eapply IHHeqo; eauto.
             }
             inversion H.
          -- apply orutt_Ret.
             unfold dvalue_refine_strict.
             cbn.
             erewrite map_dvalue_convert_strict_succeeds; eauto.
      + break_match_goal.
        * assert False by (eapply is_concrete_l_false; eauto).
          inversion H.
        * apply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
          { (* Pick uvalue *)
            apply orutt_trigger; cbn.
            -- unfold uvalue_refine_strict. cbn.

               break_match_goal.
               ++ rewrite map_monad_oom_Forall2 in Heqo0.
                  clear Heqb Heqb0.
                  assert (l0 = l).
                  { revert l0 Heqo0.
                    induction Heqo; intros; inversion Heqo0; subst; auto.
                    specialize (uvalue_refine_strict_R2_injective _ _ _ _ H H2) as [EQ _].
                    rewrite (EQ eq_refl) in *; clear EQ.
                    erewrite (IHHeqo l'0); eauto.
                  }
                  rewrite H; auto.
               ++  apply map_monad_OOM_fail in Heqo0.
                   destruct Heqo0 as [dv [HI HS]].
                   destruct (Forall2_In _ _ _ _ HI Heqo) as [dv' [_ C]].
                   rewrite HS in C. inversion C.
            -- intros [t1] [t2] [REF1 REF2].
               cbn; auto.
            --  intros o.
                intro C.
                inv C.
          }

          intros [r1] [r2] H0.
          cbn in *.
          apply orutt_Ret; auto.

    - (* GEP *)
      repeat break_match_hyp_inv.
      unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick in *;
      cbn;
      eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
      {
        apply orutt_trigger; cbn;
          [ first [ tauto
            | idtac
            ]
          | intros [t1] [t2] [REF1 REF2];
            cbn; auto
          | intros o CONTRA;
            inv CONTRA
          ].
        unfold uvalue_refine_strict.
        cbn.  rewrite Heqo.
        rewrite Heqo0.
        reflexivity.
      }

      intros [?r1] [?r2] H0;
        cbn in *;
        apply orutt_Ret; auto.

    - (* InsertElement *)
      repeat break_match_hyp_inv;
      unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick in *;
      cbn.

      eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
      { (* Pick uvalue *)
        apply orutt_trigger; cbn.
        { unfold uvalue_refine_strict. cbn.
          rewrite Heqo.
          reflexivity.
        }
        intros [t1] [t2] [REF1 REF2].
        cbn; auto.
        intros o CONTRA.
        inv CONTRA.
      }

      intros [r1] [r2] H0.
      cbn in *.
      apply orutt_Ret; auto.

  Qed.


  Ltac simplify_expr odt :=
    destruct odt as [dt | ];
    cbn;
    try solve [
        solve_orutt_raise
      ];
    try (destruct dt; cbn;
         try solve [
             solve_orutt_raise
      ]).

  Lemma contains_undef_or_poison_E1_E2 :
    forall u2 u1,
      uvalue_refine_strict u1 u2 ->
      DV1.contains_undef_or_poison u1 = contains_undef_or_poison u2.
  Proof.
    intros u2.
    induction u2; intros u1 REF;
      DVC.uvalue_refine_strict_inv REF;
      cbn; auto;
      try solve
        [ apply map_monad_oom_Forall2 in H1;
          induction H1; cbn; auto;
          setoid_rewrite H; cbn; auto;
          break_match; auto;
          eapply IHForall2;
          intros u H2 u1 H3;
          apply H;
          [right; auto| auto]
        | rewrite IHu2_1; eauto;
          rewrite IHu2_2; eauto
        | rewrite IHu2_1; eauto;
          rewrite IHu2_2; eauto;
          rewrite IHu2_3; eauto
        ].

    - rewrite IHu2; eauto.
      destruct (contains_undef_or_poison u2); cbn; auto.
      apply map_monad_oom_Forall2 in H2;
        induction H2; auto.
      cbn.
      erewrite H; cbn; auto.
      break_match; cbn; auto.
      apply IHForall2.
      intros idx H3 u1 H4.
      apply H; cbn; auto.
  Qed.

  Lemma dvalue_convert_strict_fin_inf_succeeds :
    forall dv_fin,
    {dv_inf & DVCrev.dvalue_convert_strict dv_fin = NoOom dv_inf}.
  Proof.
    intros dv_fin.
    induction dv_fin;
      try solve
        [eexists;
         cbn; eauto
        ].
    - pose proof (ACS.addr_convert_succeeds a) as (a_inf & CONV).
      exists (DVCrev.DV2.DVALUE_Addr a_inf).
      cbn.
      rewrite CONV; cbn; eauto.
    - pose proof (IPS.intptr_convert_succeeds x) as (x_inf & CONV).
      eexists.
      cbn.
      rewrite CONV; cbn; eauto.
    - induction fields.
      + exists (DVCrev.DV2.DVALUE_Struct []).
        cbn.
        reflexivity.
      + forward IHfields.
        { intros u X0.
          eapply X.
          right; auto.
        }

        destruct IHfields.
        cbn in e.
        break_match_hyp_inv.

        pose proof (X a).
        forward X0; cbn; auto.
        destruct X0 as (a'&A).
        exists (DVCrev.DV2.DVALUE_Struct (a' :: l)).

        cbn.
        rewrite A.
        rewrite Heqo.
        reflexivity.
    - induction fields.
      + exists (DVCrev.DV2.DVALUE_Packed_struct []).
        cbn.
        reflexivity.
      + forward IHfields.
        { intros u X0.
          eapply X.
          right; auto.
        }

        destruct IHfields.
        cbn in e.
        break_match_hyp_inv.

        pose proof (X a).
        forward X0; cbn; auto.
        destruct X0 as (a'&A).
        exists (DVCrev.DV2.DVALUE_Packed_struct (a' :: l)).

        cbn.
        rewrite A.
        rewrite Heqo.
        reflexivity.
    - induction elts.
      + exists (DVCrev.DV2.DVALUE_Array t []).
        cbn.
        reflexivity.
      + forward IHelts.
        { intros u X0.
          eapply X.
          right; auto.
        }

        destruct IHelts.
        cbn in e.
        break_match_hyp_inv.

        pose proof (X a).
        forward X0; cbn; auto.
        destruct X0 as (a'&A).
        exists (DVCrev.DV2.DVALUE_Array t (a' :: l)).

        cbn.
        rewrite A.
        rewrite Heqo.
        reflexivity.
    - induction elts.
      + exists (DVCrev.DV2.DVALUE_Vector t []).
        cbn.
        reflexivity.
      + forward IHelts.
        { intros u X0.
          eapply X.
          right; auto.
        }

        destruct IHelts.
        cbn in e.
        break_match_hyp_inv.

        pose proof (X a).
        forward X0; cbn; auto.
        destruct X0 as (a'&A).
        exists (DVCrev.DV2.DVALUE_Vector t (a' :: l)).

        cbn.
        rewrite A.
        rewrite Heqo.
        reflexivity.
  Qed.

  (* TODO: Should we move this? *)
  Definition fin_to_inf_dvalue (dv_fin : DVCrev.DV1.dvalue) : DVCrev.DV2.dvalue.
    pose proof dvalue_convert_strict_safe dv_fin as [dvi [CONV RCONV]].
    apply dvi.
  Defined.

  Lemma fin_to_inf_dvalue_ix :
    forall sz x,
      fin_to_inf_dvalue (@DVALUE_I sz x) =
        @DVCrev.DV2.DVALUE_I sz x.
  Proof.
    intros sz x.
    unfold fin_to_inf_dvalue.
    break_match_goal; clear Heqs; destruct p; clear e0;
      cbn in e; subst; inv e.
    auto.
  Qed.

  Definition intptr_fin_inf (x : IP.intptr) : IS1.LP.IP.intptr.
    pose proof intptr_convert_succeeds x.
    destruct H.
    apply x0.
  Defined.

  Lemma fin_to_inf_dvalue_iptr :
    forall x,
      fin_to_inf_dvalue (DVALUE_IPTR x) =
        DVCrev.DV2.DVALUE_IPTR (intptr_fin_inf x).
  Proof.
    intros x.
    unfold fin_to_inf_dvalue.
    break_match_goal; clear Heqs; destruct p; clear e0;
      cbn in e; subst; inv e.

    pose proof intptr_convert_succeeds x.
    destruct H.
    rewrite e in H0.
    inv H0.

    unfold intptr_fin_inf.
    break_match_goal.
    clear Heqs.
    congruence.
  Qed.

  (* TODO: Should we move this? *)
  Definition addr_refine addr_inf (addr_fin : addr) := AC1.addr_convert addr_inf = NoOom addr_fin.

  (* TODO: Should we move this? *)
  Definition fin_to_inf_addr (a : addr) : IS1.LP.ADDR.addr.
    unfold FinAddr.addr in a.
    unfold FiniteAddresses.Iptr in a.
    pose proof ACS.addr_convert_succeeds a as [a' _].
    exact a'.
  Defined.

  (* TODO: Move this *)
  Lemma addr_refine_fin_to_inf_addr :
    forall addr_fin,
      addr_refine (fin_to_inf_addr addr_fin) addr_fin.
  Proof.
    intros addr_fin.
    red. unfold fin_to_inf_addr.
    break_match_goal.
    clear Heqs.
    apply ACS.addr_convert_safe in e.
    auto.
  Qed.

  Lemma addr_convert_fin_to_inf_addr :
    forall addr_fin,
      AC1.addr_convert (fin_to_inf_addr addr_fin) = NoOom addr_fin.
  Proof.
    intros addr_fin.
    unfold fin_to_inf_addr in *.
    destruct (ACS.addr_convert_succeeds addr_fin).
    apply ACS.addr_convert_safe in e.
    auto.
  Qed.

  Lemma fin_to_inf_dvalue_addr :
    forall a,
      fin_to_inf_dvalue (DVALUE_Addr a) =
        DVCrev.DV2.DVALUE_Addr (fin_to_inf_addr a).
  Proof.
    intros a.
    unfold fin_to_inf_dvalue.
    break_match_goal; clear Heqs; destruct p; clear e0.
    cbn in e.
    break_match_hyp_inv.
    unfold fin_to_inf_addr.
    break_match_goal.
    clear Heqs.
    rewrite Heqo in e.
    inv e.
    auto.
  Qed.

  Lemma fin_to_inf_dvalue_float :
    forall f,
      fin_to_inf_dvalue (DVALUE_Float f) =
        DVCrev.DV2.DVALUE_Float f.
  Proof.
    intros a.
    unfold fin_to_inf_dvalue.
    break_match_goal; clear Heqs; destruct p; clear e0.
    cbn in e. inv e.
    reflexivity.
  Qed.

  Lemma fin_to_inf_dvalue_double :
    forall f,
      fin_to_inf_dvalue (DVALUE_Double f) =
        DVCrev.DV2.DVALUE_Double f.
  Proof.
    intros a.
    unfold fin_to_inf_dvalue.
    break_match_goal; clear Heqs; destruct p; clear e0.
    cbn in e. inv e.
    reflexivity.
  Qed.

  Lemma fin_to_inf_dvalue_poison :
    forall t,
      fin_to_inf_dvalue (DVALUE_Poison t) =
        DVCrev.DV2.DVALUE_Poison t.
  Proof.
    intros x.
    unfold fin_to_inf_dvalue.
    break_match_goal; clear Heqs; destruct p; clear e0;
      cbn in e; subst; inv e.
    auto.
  Qed.

  Lemma fin_to_inf_dvalue_oom :
    forall t,
      fin_to_inf_dvalue (DVALUE_Oom t) =
        DVCrev.DV2.DVALUE_Oom t.
  Proof.
    intros x.
    unfold fin_to_inf_dvalue.
    break_match_goal; clear Heqs; destruct p; clear e0;
      cbn in e; subst; inv e.
    auto.
  Qed.

  Lemma fin_to_inf_dvalue_none :
      fin_to_inf_dvalue DVALUE_None =
        DVCrev.DV2.DVALUE_None.
  Proof.
    unfold fin_to_inf_dvalue.
    break_match_goal; clear Heqs; destruct p; clear e0;
      cbn in e; subst; inv e.
    auto.
  Qed.

  Lemma fin_to_inf_dvalue_struct :
    forall elts,
      fin_to_inf_dvalue (DVALUE_Struct elts) =
        DVCrev.DV2.DVALUE_Struct (map fin_to_inf_dvalue elts).
  Proof.
    induction elts.
    - cbn.
      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs; destruct p; clear e0;
        cbn in e; subst; inv e.
      auto.
    - unfold fin_to_inf_dvalue in *.
      break_match_goal; clear Heqs; destruct p; clear e0;
        cbn in e; subst; inv e.
      break_match_hyp_inv.
      break_match_hyp_inv.
      break_match_hyp_inv.

      break_match_hyp_inv; clear Heqs; destruct p; clear e0.
      cbn in e; subst; inv e.

      break_match_hyp_inv.
      rewrite map_cons.
      inv Heqo.

      break_match_goal; clear Heqs; destruct p; clear e0.
      rewrite Heqo0 in e.
      inv e.
      auto.
  Qed.

  Lemma fin_to_inf_dvalue_packed_struct :
    forall elts,
      fin_to_inf_dvalue (DVALUE_Packed_struct elts) =
        DVCrev.DV2.DVALUE_Packed_struct (map fin_to_inf_dvalue elts).
  Proof.
    induction elts.
    - cbn.
      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs; destruct p; clear e0;
        cbn in e; subst; inv e.
      auto.
    - unfold fin_to_inf_dvalue in *.
      break_match_goal; clear Heqs; destruct p; clear e0;
        cbn in e; subst; inv e.
      break_match_hyp_inv.
      break_match_hyp_inv.
      break_match_hyp_inv.

      break_match_hyp_inv; clear Heqs; destruct p; clear e0.
      cbn in e; subst; inv e.

      break_match_hyp_inv.
      rewrite map_cons.
      inv Heqo.

      break_match_goal; clear Heqs; destruct p; clear e0.
      rewrite Heqo0 in e.
      inv e.
      auto.
  Qed.

  Lemma fin_to_inf_dvalue_array :
    forall elts t,
      fin_to_inf_dvalue (DVALUE_Array t elts) =
        DVCrev.DV2.DVALUE_Array t (map fin_to_inf_dvalue elts).
  Proof.
    induction elts; intros t.
    - cbn.
      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs; destruct p; clear e0;
        cbn in e; subst; inv e.
      auto.
    - unfold fin_to_inf_dvalue in *.
      break_match_goal; clear Heqs; destruct p; clear e0;
        cbn in e; subst; inv e.
      break_match_hyp_inv.
      break_match_hyp_inv.
      break_match_hyp_inv.
      rewrite map_cons.

      specialize (IHelts t).

      break_match_hyp_inv; clear Heqs; destruct p; clear e0.
      cbn in e; subst; inv e.

      break_match_hyp_inv.
      inv Heqo.

      break_match_goal; clear Heqs; destruct p; clear e0.
      rewrite Heqo0 in e.
      inv e.
      auto.
  Qed.

  Lemma fin_to_inf_dvalue_vector :
    forall elts t,
      fin_to_inf_dvalue (DVALUE_Vector t elts) =
        DVCrev.DV2.DVALUE_Vector t (map fin_to_inf_dvalue elts).
  Proof.
    induction elts; intros t.
    - cbn.
      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs; destruct p; clear e0;
        cbn in e; subst; inv e.
      auto.
    - unfold fin_to_inf_dvalue in *.
      break_match_goal; clear Heqs; destruct p; clear e0;
        cbn in e; subst; inv e.
      break_match_hyp_inv.
      break_match_hyp_inv.
      break_match_hyp_inv.
      rewrite map_cons.

      specialize (IHelts t).

      break_match_hyp_inv; clear Heqs; destruct p; clear e0.
      cbn in e; subst; inv e.

      break_match_hyp_inv.

      break_match_goal; clear Heqs; destruct p; clear e0.
      rewrite Heqo0 in e.
      inv e.

      inv Heqo.
      auto.
  Qed.

  Ltac rewrite_fin_to_inf_dvalue :=
    repeat
      first
      [ rewrite fin_to_inf_dvalue_ix
      | rewrite fin_to_inf_dvalue_iptr
      | rewrite fin_to_inf_dvalue_addr
      | rewrite fin_to_inf_dvalue_float
      | rewrite fin_to_inf_dvalue_double
      | rewrite fin_to_inf_dvalue_poison
      | rewrite fin_to_inf_dvalue_oom
      | rewrite fin_to_inf_dvalue_none
      | rewrite fin_to_inf_dvalue_array
      | rewrite fin_to_inf_dvalue_vector
      | rewrite fin_to_inf_dvalue_struct
      | rewrite fin_to_inf_dvalue_packed_struct
      ].

  Lemma dvalue_has_dtyp_fin_to_inf_dvalue :
    forall dv_fin t,
      dvalue_has_dtyp dv_fin t ->
      DV1.dvalue_has_dtyp (fin_to_inf_dvalue dv_fin) t.
  Proof.
    intros dv_fin t TYP.
    induction TYP;
      rewrite_fin_to_inf_dvalue;
      try solve [ constructor; eauto ].
    - (* Structs *)
      induction H; cbn.
      + constructor; constructor.
      + constructor.
        constructor; eauto.
        inv IHForall2.
        auto.
    - (* Packed Structs *)
      induction H; cbn.
      + constructor; constructor.
      + constructor.
        constructor; eauto.
        inv IHForall2.
        auto.
    - (* Arrays *)
      constructor; eauto.
      { apply Forall_forall; eauto.
        intros x H2.
        apply in_map_iff in H2.
        destruct H2 as (?&?&?); subst.
        eauto.
      }

      rewrite length_map.
      auto.
    - (* Vectors *)
      constructor; eauto.
      { apply Forall_forall; eauto.
        intros x H3.
        apply in_map_iff in H3.
        destruct H3 as (?&?&?); subst.
        eauto.
      }

      rewrite length_map.
      auto.
  Qed.

  (* TODO: Should we move this? *)
  Definition fin_to_inf_uvalue (uv_fin : DVCrev.DV1.uvalue) : DVCrev.DV2.uvalue.
    pose proof uvalue_convert_strict_safe uv_fin as [uvi [CONV RCONV]].
    apply uvi.
  Defined.

  Lemma convert_fin_to_inf_uvalue_succeeds :
    forall {uv_fin},
      DVC.uvalue_convert_strict (fin_to_inf_uvalue uv_fin) = NoOom uv_fin.
  Proof.
    intros.
    unfold fin_to_inf_uvalue.
    destruct (uvalue_convert_strict_safe uv_fin).
    destruct p.
    rewrite e0.
    reflexivity.
  Qed.

  Lemma fin_to_inf_uvalue_refine_strict' :
    forall d_inf d_fin,
      DVC.uvalue_refine_strict d_inf d_fin ->
      d_inf = fin_to_inf_uvalue d_fin.
  Proof.
    intros d_inf d_fin H.
    rewrite DVC.uvalue_refine_strict_equation in H.
    unfold fin_to_inf_uvalue.
    break_match; cbn in *.
    destruct p.
    clear Heqs.

    revert d_fin H x e e0.
    induction d_inf; intros d_fin H' x' e e0; try rename H into H''; rename H' into H;
      try solve
        [ cbn in *; inv H;
          cbn in *; inv e;
          auto
        ].
    - cbn in *.
      break_match_hyp; inv H.
      cbn in *.
      break_match_hyp; inv e.
      cbn in *.
      break_match_hyp; inv e0.

      pose proof AC1.addr_convert_injective a a1 a0 Heqo Heqo1.
      subst.
      auto.
    - cbn in *; break_match_hyp; inv H.
      cbn in *; inv e.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; inv e0.
      cbn in *; break_match_hyp; inv H0.

      pose proof (IP.from_Z_injective _ _ _ Heqo Heqo1).
      apply IS1.LP.IP.to_Z_inj in H.
      subst.
      reflexivity.
    - cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv e0.

      revert l Heqo l0 Heqo1 H'' Heqo0.
      induction fields; intros l Heqo l0 Heqo1 H'' Heqo0.
      + cbn in *. inv Heqo.
        cbn in *. inv Heqo0.
        reflexivity.
      + rewrite map_monad_unfold in Heqo.
        cbn in *.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo0.
        cbn in *.
        break_match_hyp; inv Heqo0.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo1.
        cbn in *.
        break_match_hyp; inv Heqo1.
        break_match_hyp; inv H0.

        (* Show that a = u0 *)
        pose proof (H'' a (or_introl eq_refl) _ Heqo2 _ Heqo3 Heqo4); subst.

        specialize (IHfields _ eq_refl l Heqo1).
        forward IHfields; eauto.
        forward IHfields; eauto.
        inv IHfields.
        reflexivity.
    - cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv e0.

      revert l Heqo l0 Heqo1 H'' Heqo0.
      induction fields; intros l Heqo l0 Heqo1 H'' Heqo0.
      + cbn in *. inv Heqo.
        cbn in *. inv Heqo0.
        reflexivity.
      + rewrite map_monad_unfold in Heqo.
        cbn in *.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo0.
        cbn in *.
        break_match_hyp; inv Heqo0.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo1.
        cbn in *.
        break_match_hyp; inv Heqo1.
        break_match_hyp; inv H0.

        (* Show that a = u0 *)
        pose proof (H'' a (or_introl eq_refl) _ Heqo2 _ Heqo3 Heqo4); subst.

        specialize (IHfields _ eq_refl l Heqo1).
        forward IHfields; eauto.
        forward IHfields; eauto.
        inv IHfields.
        reflexivity.
    - cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv e0.

      revert l Heqo l0 Heqo1 H'' Heqo0.
      induction elts; intros l Heqo l0 Heqo1 H'' Heqo0.
      + cbn in *. inv Heqo.
        cbn in *. inv Heqo0.
        reflexivity.
      + rewrite map_monad_unfold in Heqo.
        cbn in *.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo0.
        cbn in *.
        break_match_hyp; inv Heqo0.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo1.
        cbn in *.
        break_match_hyp; inv Heqo1.
        break_match_hyp; inv H0.

        (* Show that a = u0 *)
        pose proof (H'' a (or_introl eq_refl) _ Heqo2 _ Heqo3 Heqo4); subst.

        specialize (IHelts _ eq_refl l Heqo1).
        forward IHelts; eauto.
        forward IHelts; eauto.
        inv IHelts.
        reflexivity.
    - cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv e0.

      revert l Heqo l0 Heqo1 H'' Heqo0.
      induction elts; intros l Heqo l0 Heqo1 H'' Heqo0.
      + cbn in *. inv Heqo.
        cbn in *. inv Heqo0.
        reflexivity.
      + rewrite map_monad_unfold in Heqo.
        cbn in *.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo0.
        cbn in *.
        break_match_hyp; inv Heqo0.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo1.
        cbn in *.
        break_match_hyp; inv Heqo1.
        break_match_hyp; inv H0.

        (* Show that a = u0 *)
        pose proof (H'' a (or_introl eq_refl) _ Heqo2 _ Heqo3 Heqo4); subst.

        specialize (IHelts _ eq_refl l Heqo1).
        forward IHelts; eauto.
        forward IHelts; eauto.
        inv IHelts.
        reflexivity.
    - (* IBinop *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv H1.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv e0.
      cbn in *; break_match_hyp; inv H0.

      erewrite IHd_inf1; eauto.
      erewrite IHd_inf2; eauto.
    - (* ICmp *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv H1.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv e0.
      cbn in *; break_match_hyp; inv H0.

      erewrite IHd_inf1; eauto.
      erewrite IHd_inf2; eauto.
    - (* FBinop *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv H1.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv e0.
      cbn in *; break_match_hyp; inv H0.

      erewrite IHd_inf1; eauto.
      erewrite IHd_inf2; eauto.
    - (* Fneg *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; inv e.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv e0.
      
      erewrite IHd_inf; eauto.
    - (* FCmp *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv H1.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv e0.
      cbn in *; break_match_hyp; inv H0.

      erewrite IHd_inf1; eauto.
      erewrite IHd_inf2; eauto.
    - (* Conversion *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv e0.

      erewrite IHd_inf; eauto.
    - (* GEP *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv H1.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv e0.
      cbn in *; break_match_hyp; inv H0.

      revert l Heqo l0 u0 Heqo1 H'' Heqo0 Heqo2 Heqo4 Heqo3.
      induction idxs; intros l Heqo l0 u0 Heqo1 H'' Heqo0 Heqo2 Heqo4 Heqo3.
      + cbn in *. inv Heqo0.
        cbn in *. inv Heqo2.
        erewrite IHd_inf; eauto.
      + rewrite map_monad_unfold in Heqo0.
        cbn in *.
        break_match_hyp; inv Heqo0.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo2.
        cbn in *.
        break_match_hyp; inv Heqo2.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo4.
        cbn in *.
        break_match_hyp; inv Heqo4.
        break_match_hyp; inv H0.

        (* Show that a = u0 *)
        pose proof (H'' a (or_introl eq_refl)_ Heqo5 _ Heqo6 Heqo7); subst.

        specialize (IHidxs l1 Heqo l _ Heqo1).
        repeat (forward IHidxs; eauto).
        inv IHidxs.
        reflexivity.
    - (* ExtractElement *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv H1.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv e0.
      cbn in *; break_match_hyp; inv H0.

      erewrite IHd_inf1; eauto.
      erewrite IHd_inf2; eauto.
    - (* InsertElement *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv H1.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv H1.
      cbn in *; break_match_hyp; inv e0.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv H1.

      erewrite IHd_inf1; eauto.
      erewrite IHd_inf2; eauto.
      erewrite IHd_inf3; eauto.
    - (* ShuffleVector *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv H1.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv H1.
      cbn in *; break_match_hyp; inv e0.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv H1.

      erewrite IHd_inf1; eauto.
      erewrite IHd_inf2; eauto.
      erewrite IHd_inf3; eauto.
    - (* ExtractValue *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv e0.

      erewrite IHd_inf; eauto.
    - (* InsertValue *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv H1.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv e0.
      cbn in *; break_match_hyp; inv H0.

      erewrite IHd_inf1; eauto.
      erewrite IHd_inf2; eauto.
    - (* Select *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv H1.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv H1.
      cbn in *; break_match_hyp; inv e0.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv H1.

      erewrite IHd_inf1; eauto.
      erewrite IHd_inf2; eauto.
      erewrite IHd_inf3; eauto.
    - (* ExtractByte *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv e0.

      erewrite IHd_inf; eauto.
    - (* ConcatBytes *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv e0.

      revert l Heqo l0 Heqo1 H'' Heqo0 Heqo.
      induction uvs; intros l Heqo l0 Heqo1 H'' Heqo0 Heqo2.
      + cbn in *. inv Heqo2.
        cbn in *. inv Heqo0.
        reflexivity.
      + rewrite map_monad_unfold in Heqo2.
        cbn in *.
        break_match_hyp; inv Heqo2.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo0.
        cbn in *.
        break_match_hyp; inv Heqo0.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo1.
        cbn in *.
        break_match_hyp; inv Heqo1.
        break_match_hyp; inv H0.

        (* Show that a = u0 *)
        pose proof (H'' a (or_introl eq_refl) _ Heqo3 _ Heqo4 Heqo5); subst.

        specialize (IHuvs l1 eq_refl l Heqo1).
        repeat (forward IHuvs; eauto).
        inv IHuvs.
        reflexivity.
  Qed.

  (* TODO: Move these *)
  Lemma fin_to_inf_dvalue_refine_strict :
    forall d,
      dvalue_refine_strict (fin_to_inf_dvalue d) d.
  Proof.
    intros d.
    rewrite dvalue_refine_strict_equation.
    unfold fin_to_inf_dvalue.
    break_match; cbn in *.
    destruct p.
    auto.
  Qed.

  Lemma fin_to_inf_uvalue_refine_strict :
    forall u,
      uvalue_refine_strict (fin_to_inf_uvalue u) u.
  Proof.
    intros u.
    rewrite uvalue_refine_strict_equation.
    unfold fin_to_inf_uvalue.
    break_match; cbn in *.
    destruct p.
    auto.
  Qed.

  Lemma fin_to_inf_dvalue_refine_strict' :
    forall d_inf d_fin,
      DVC.dvalue_refine_strict d_inf d_fin ->
      d_inf = fin_to_inf_dvalue d_fin.
  Proof.
    intros d_inf d_fin H.
    rewrite DVC.dvalue_refine_strict_equation in H.
    unfold fin_to_inf_dvalue.
    break_match; cbn in *.
    destruct p.
    clear Heqs.

    revert d_fin H x e e0.
    induction d_inf; intros d_fin H' x' e e0; try rename H into H''; rename H' into H;
      try solve
        [ cbn in *; inv H;
          cbn in *; inv e;
          auto
        ].
    - cbn in *.
      break_match_hyp; inv H.
      cbn in *.
      break_match_hyp; inv e.
      cbn in *.
      break_match_hyp; inv e0.

      pose proof AC1.addr_convert_injective a a1 a0 Heqo Heqo1.
      subst.
      auto.
    - cbn in *; break_match_hyp; inv H.
      cbn in *; inv e.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv e0.

      pose proof (IP.from_Z_injective _ _ _ Heqo Heqo1).
      apply IS1.LP.IP.to_Z_inj in H.
      subst.
      reflexivity.
    - cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv e0.

      revert l Heqo l0 Heqo1 H'' Heqo0.
      induction fields; intros l Heqo l0 Heqo1 H'' Heqo0.
      + cbn in *. inv Heqo.
        cbn in *. inv Heqo0.
        reflexivity.
      + rewrite map_monad_unfold in Heqo.
        cbn in *.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo0.
        cbn in *.
        break_match_hyp; inv Heqo0.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo1.
        cbn in *.
        break_match_hyp; inv Heqo1.
        break_match_hyp; inv H0.

        (* Show that a = u0 *)
        pose proof (H'' a (or_introl eq_refl) _ Heqo2 _ Heqo3 Heqo4); subst.

        specialize (IHfields _ eq_refl l Heqo1).
        forward IHfields; eauto.
        forward IHfields; eauto.
        inv IHfields.
        reflexivity.
    - cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv e0.

      revert l Heqo l0 Heqo1 H'' Heqo0.
      induction fields; intros l Heqo l0 Heqo1 H'' Heqo0.
      + cbn in *. inv Heqo.
        cbn in *. inv Heqo0.
        reflexivity.
      + rewrite map_monad_unfold in Heqo.
        cbn in *.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo0.
        cbn in *.
        break_match_hyp; inv Heqo0.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo1.
        cbn in *.
        break_match_hyp; inv Heqo1.
        break_match_hyp; inv H0.

        (* Show that a = u0 *)
        pose proof (H'' a (or_introl eq_refl) _ Heqo2 _ Heqo3 Heqo4); subst.

        specialize (IHfields _ eq_refl l Heqo1).
        forward IHfields; eauto.
        forward IHfields; eauto.
        inv IHfields.
        reflexivity.
    - cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv e0.

      revert l Heqo l0 Heqo1 H'' Heqo0.
      induction elts; intros l Heqo l0 Heqo1 H'' Heqo0.
      + cbn in *. inv Heqo.
        cbn in *. inv Heqo0.
        reflexivity.
      + rewrite map_monad_unfold in Heqo.
        cbn in *.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo0.
        cbn in *.
        break_match_hyp; inv Heqo0.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo1.
        cbn in *.
        break_match_hyp; inv Heqo1.
        break_match_hyp; inv H0.

        (* Show that a = u0 *)
        pose proof (H'' a (or_introl eq_refl) _ Heqo2 _ Heqo3 Heqo4); subst.

        specialize (IHelts _ eq_refl l Heqo1).
        forward IHelts; eauto.
        forward IHelts; eauto.
        inv IHelts.
        reflexivity.
    - cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv e0.

      revert l Heqo l0 Heqo1 H'' Heqo0.
      induction elts; intros l Heqo l0 Heqo1 H'' Heqo0.
      + cbn in *. inv Heqo.
        cbn in *. inv Heqo0.
        reflexivity.
      + rewrite map_monad_unfold in Heqo.
        cbn in *.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo0.
        cbn in *.
        break_match_hyp; inv Heqo0.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo1.
        cbn in *.
        break_match_hyp; inv Heqo1.
        break_match_hyp; inv H0.

        (* Show that a = u0 *)
        pose proof (H'' a (or_introl eq_refl) _ Heqo2 _ Heqo3 Heqo4); subst.

        specialize (IHelts _ eq_refl l Heqo1).
        forward IHelts; eauto.
        forward IHelts; eauto.
        inv IHelts.
        reflexivity.
  Qed.

  (* TODO: Move this *)
  Lemma dvalue_convert_strict_fin_inf_succeeds_fin_to_inf_dvalue :
    forall x y,
      DVCrev.dvalue_convert_strict x = NoOom y ->
      fin_to_inf_dvalue x = y.
  Proof.
    intros x y CONV.
    unfold fin_to_inf_dvalue.
    break_match_goal.
    break_match_goal.
    clear Heqs.
    subst.
    rewrite CONV in e.
    inv e; auto.
  Qed.

  (* TODO: Move this *)
  Lemma dvalue_convert_strict_struct_map :
    forall fields_fin res,
      DVCrev.dvalue_convert_strict (DVALUE_Struct fields_fin) = NoOom res ->
      res = (DV1.DVALUE_Struct (map fin_to_inf_dvalue fields_fin)).
  Proof.
    intros fields_fin res CONV.
    cbn in CONV.
    break_match_hyp_inv.
    apply map_monad_oom_Forall2 in Heqo.
    induction Heqo.
    - cbn. reflexivity.
    - rewrite map_cons.
      apply dvalue_convert_strict_fin_inf_succeeds_fin_to_inf_dvalue in H.
      rewrite H.
      inv IHHeqo.
      reflexivity.
  Qed.

  (* TODO: Move this *)
  Lemma dvalue_convert_strict_packed_struct_map :
    forall fields_fin res,
      DVCrev.dvalue_convert_strict (DVALUE_Packed_struct fields_fin) = NoOom res ->
      res = (DV1.DVALUE_Packed_struct (map fin_to_inf_dvalue fields_fin)).
  Proof.
    intros fields_fin res CONV.
    cbn in CONV.
    break_match_hyp_inv.
    apply map_monad_oom_Forall2 in Heqo.
    induction Heqo.
    - cbn. reflexivity.
    - rewrite map_cons.
      apply dvalue_convert_strict_fin_inf_succeeds_fin_to_inf_dvalue in H.
      rewrite H.
      inv IHHeqo.
      reflexivity.
  Qed.

  (* TODO: Move this *)
  Lemma dvalue_convert_strict_array_map :
    forall fields_fin res t,
      DVCrev.dvalue_convert_strict (DVALUE_Array t fields_fin) = NoOom res ->
      res = (DV1.DVALUE_Array t (map fin_to_inf_dvalue fields_fin)).
  Proof.
    intros fields_fin res t CONV.
    cbn in CONV.
    break_match_hyp_inv.
    apply map_monad_oom_Forall2 in Heqo.
    induction Heqo.
    - cbn. reflexivity.
    - rewrite map_cons.
      apply dvalue_convert_strict_fin_inf_succeeds_fin_to_inf_dvalue in H.
      rewrite H.
      inv IHHeqo.
      reflexivity.
  Qed.

  (* TODO: Move this *)
  Lemma dvalue_convert_strict_vector_map :
    forall fields_fin res t,
      DVCrev.dvalue_convert_strict (DVALUE_Vector t fields_fin) = NoOom res ->
      res = (DV1.DVALUE_Vector t (map fin_to_inf_dvalue fields_fin)).
  Proof.
    intros fields_fin res t CONV.
    cbn in CONV.
    break_match_hyp_inv.
    apply map_monad_oom_Forall2 in Heqo.
    induction Heqo.
    - cbn. reflexivity.
    - rewrite map_cons.
      apply dvalue_convert_strict_fin_inf_succeeds_fin_to_inf_dvalue in H.
      rewrite H.
      inv IHHeqo.
      reflexivity.
  Qed.

  Lemma dvalue_convert_strict_fin_inf_succeeds_fin_to_inf_dvalue' :
    forall res,
      DVCrev.dvalue_convert_strict res = NoOom (fin_to_inf_dvalue res).
  Proof.
    intros res.
    unfold fin_to_inf_dvalue.
    break_match_goal.
    destruct p.
    clear Heqs.
    auto.
  Qed.

  Hint Resolve
    dvalue_convert_strict_fin_inf_succeeds_fin_to_inf_dvalue'
    : EVAL_INT_FIN_INF.

  Lemma ptr_to_int_fin_to_inf_addr :
    forall a,
      IS1.LP.PTOI.ptr_to_int (fin_to_inf_addr a) = PTOI.ptr_to_int a.
  Proof.
    intros a.
    unfold fin_to_inf_addr.
    break_match_goal.
    clear Heqs.
    erewrite AC2.addr_convert_ptoi; eauto.
  Qed.

  Lemma uvalue_direct_subterm_fin_inf :
    forall u_fin uv_fin u_inf uv_inf,
      uvalue_refine_strict u_inf u_fin ->
      uvalue_refine_strict uv_inf uv_fin ->
      DV2.uvalue_direct_subterm u_fin uv_fin ->
      DV1.uvalue_direct_subterm u_inf uv_inf.
  Proof.
    intros u_fin uv_fin u_inf uv_inf REF_U REF_UV SUB.
    revert u_fin u_inf REF_U SUB.
    induction uv_inf using DV1.uvalue_strong_ind;
      intros u_fin u_inf REF_U SUB;
      try
        solve
        [ repeat red in REF_UV; cbn in REF_UV;
          try break_match_hyp_inv;
          try inv REF_UV;
          inv SUB
        ].

    inv SUB;
      DVC.uvalue_refine_strict_inv REF_UV;
      try
        solve
        [ (* Struct cases *)
          constructor;
          match goal with
          | H : map_monad uvalue_convert_strict _ = NoOom ?fields,
              HIN : In _ ?fields |-
              _ =>
              apply map_monad_oom_Forall2 in H;
              pose proof Forall2_In_exists2 _ _ _ _ H HIN as (?&?&CONV_u_fin);
              red in REF_U;
              pose proof uvalue_refine_strict_R2_injective _ _ _ _ REF_U CONV_u_fin as (_&INJ);
              forward INJ; subst; auto
          end
        | (* Binop cases *)
          match goal with
          | H2 : uvalue_convert_strict _ = NoOom ?u_fin,
              REF_U : uvalue_refine_strict _ ?u_fin |-
              _ =>
              pose proof uvalue_refine_strict_R2_injective _ _ _ _ REF_U H2 as (_&INJ);
              forward INJ; subst; auto;
              constructor
          end
        ].
  Qed.

  Lemma uvalue_strict_subterm_fin_inf :
    forall u_fin uv_fin u_inf uv_inf,
      uvalue_refine_strict u_inf u_fin ->
      uvalue_refine_strict uv_inf uv_fin ->
      DV2.uvalue_strict_subterm u_fin uv_fin ->
      DV1.uvalue_strict_subterm u_inf uv_inf.
  Proof.
    intros u_fin uv_fin u_inf uv_inf H H0 H1.
    eapply clos_trans_t1n_iff.
    revert u_inf uv_inf H H0.
    eapply clos_trans_t1n_iff in H1.
    induction H1; intros u_inf uv_inf H' H0.
    - apply t1n_step.
      eapply uvalue_direct_subterm_fin_inf; eauto.
    - eapply Relation_Operators.t1n_trans with (y:=fin_to_inf_uvalue y).
      + eapply uvalue_direct_subterm_fin_inf; eauto.
        apply convert_fin_to_inf_uvalue_succeeds.
      + eapply IHclos_trans_1n; auto.
        apply convert_fin_to_inf_uvalue_succeeds.
  Qed.


  (* TODO: Move this *)
  Lemma fin_to_inf_dvalue_not_poison :
    forall dv_fin t,
      dv_fin <> DVALUE_Poison t ->
      fin_to_inf_dvalue dv_fin <> DV1.DVALUE_Poison t.
  Proof.
    intros dv_fin t NPOISON CONTRA.
    eapply NPOISON.
    destruct dv_fin; cbn in CONTRA;
      unfold fin_to_inf_dvalue in *;
      break_match_hyp_inv; subst_existT; clear Heqs; destruct p; clear e0;
      cbn in *;
      try break_match_hyp_inv; try inv e; try discriminate.
    inv H1.
    auto.
  Qed.

  Lemma dvalue_int_unsigned_E1E2 :
    forall x y,
      dvalue_refine_strict x y ->
      DV1.dvalue_int_unsigned x = dvalue_int_unsigned y.
  Proof.
    induction x; intros y REF;
      try
        solve
        [ unfold dvalue_refine_strict in *;
          cbn in *; inv REF; cbn; auto
        | unfold dvalue_refine_strict in *;
          cbn in *;
          break_match_hyp; inv REF;
          cbn; auto
        ].
    - unfold dvalue_refine_strict in *.
      cbn in *.
      break_match_hyp_inv.
      unfold dvalue_int_unsigned.
      apply IP.from_Z_to_Z in Heqo.
      rewrite <- IP.to_Z_to_unsigned.
      rewrite <- IS1.LP.IP.to_Z_to_unsigned.
      auto.
  Qed.

  Lemma fin_to_inf_dvalue_injective :
    forall dv1 dv2,
      fin_to_inf_dvalue dv1 = fin_to_inf_dvalue dv2 ->
      dv1 = dv2.
  Proof.
    induction dv1;
      intros dv2 LIFT.
    - unfold fin_to_inf_dvalue in *.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      break_match_hyp_inv.
      eapply DVCrev.dvalue_convert_strict_addr_inv in e0.
      destruct e0 as (?&?&?).
      subst.
      pose proof AC2.addr_convert_injective _ _ _ H0 Heqo; subst; auto.
    - unfold fin_to_inf_dvalue in *.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      inv e.
      eapply DVCrev.dvalue_convert_strict_ix_inv in e0.
      subst; auto.
    - unfold fin_to_inf_dvalue in *.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      break_match_hyp_inv.
      eapply DVCrev.dvalue_convert_strict_iptr_inv in e0.
      destruct e0 as (?&?&?); subst.
      pose proof IS1.LP.IP.from_Z_injective _ _ _ H0 Heqo.
      apply IP.to_Z_inj in H1; subst; auto.
    - unfold fin_to_inf_dvalue in *.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      inv e.
      eapply DVCrev.dvalue_convert_strict_double_inv in e0.
      subst; auto.
    - unfold fin_to_inf_dvalue in *.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      inv e.
      eapply DVCrev.dvalue_convert_strict_float_inv in e0.
      subst; auto.
    - unfold fin_to_inf_dvalue in *.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      inv e.
      eapply DVCrev.dvalue_convert_strict_poison_inv in e0.
      subst; auto.
    - unfold fin_to_inf_dvalue in *.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      inv e.
      eapply DVCrev.dvalue_convert_strict_oom_inv in e0.
      subst; auto.
    - unfold fin_to_inf_dvalue in *.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      inv e.
      eapply DVCrev.dvalue_convert_strict_none_inv in e0.
      subst; auto.
    - unfold fin_to_inf_dvalue in LIFT.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      break_match_hyp_inv.
      clear H0.
      eapply DVCrev.dvalue_convert_strict_struct_inv in e0.
      destruct e0 as (?&?&?).
      subst.
      eapply map_monad_oom_Forall2 in H1, Heqo.
      assert (fields=x) as FX.
      { eapply Forall2_inj_OOM_l; eauto.
        intros a H0 a' b H2 H3.
        pose proof DVCrev.dvalue_refine_strict_R2_injective _ _ _ _ H2 H3 as (_&?).
        forward H4; auto; subst.
      }
      subst.
      reflexivity.
    - unfold fin_to_inf_dvalue in LIFT.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      break_match_hyp_inv.
      clear H0.
      eapply DVCrev.dvalue_convert_strict_packed_struct_inv in e0.
      destruct e0 as (?&?&?).
      subst.
      eapply map_monad_oom_Forall2 in H1, Heqo.
      assert (fields=x) as FX.
      { eapply Forall2_inj_OOM_l; eauto.
        intros a H0 a' b H2 H3.
        pose proof DVCrev.dvalue_refine_strict_R2_injective _ _ _ _ H2 H3 as (_&?).
        forward H4; auto; subst.
      }
      subst.
      reflexivity.
    - unfold fin_to_inf_dvalue in LIFT.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      break_match_hyp_inv.
      clear H0.
      eapply DVCrev.dvalue_convert_strict_array_inv in e0.
      destruct e0 as (?&?&?).
      subst.
      eapply map_monad_oom_Forall2 in H1, Heqo.
      assert (elts=x) as EX.
      { eapply Forall2_inj_OOM_l; eauto.
        intros a H0 a' b H2 H3.
        pose proof DVCrev.dvalue_refine_strict_R2_injective _ _ _ _ H2 H3 as (_&?).
        forward H4; auto; subst.
      }
      subst.
      reflexivity.
    - unfold fin_to_inf_dvalue in LIFT.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      break_match_hyp_inv.
      clear H0.
      eapply DVCrev.dvalue_convert_strict_vector_inv in e0.
      destruct e0 as (?&?&?).
      subst.
      eapply map_monad_oom_Forall2 in H1, Heqo.
      assert (elts=x) as EX.
      { eapply Forall2_inj_OOM_l; eauto.
        intros a H0 a' b H2 H3.
        pose proof DVCrev.dvalue_refine_strict_R2_injective _ _ _ _ H2 H3 as (_&?).
        forward H4; auto; subst.
      }
      subst.
      reflexivity.
  Qed.


  Lemma show_dvalue_fin_inf_helper :
    forall fields,
      (forall dv,
          In dv fields ->
          show_dvalue dv = DV1.show_dvalue (fin_to_inf_dvalue dv)) ->
      map show_dvalue fields = map DV1.show_dvalue (map fin_to_inf_dvalue fields).
  Proof.
    induction fields; intros SHOW.
    - reflexivity.
    - repeat rewrite map_cons.
      rewrite SHOW; cbn; auto.
      rewrite IHfields; eauto.
      intros dv H.
      eapply SHOW.
      right; auto.
  Qed.

  Lemma show_intptr_fin_inf :
    forall x,
      Show.show_Z (IP.to_Z x) = Show.show_Z (IS1.LP.IP.to_Z (intptr_fin_inf x)).
  Proof.
    intros x.
    unfold intptr_fin_inf.
  Admitted.

  Lemma show_addr_fin_inf :
    forall a,
      show_addr a = IS1.LP.ADDR.show_addr (fin_to_inf_addr a).
  Proof.
    intros a.
  Admitted.

  Lemma show_dvalue_fin_inf :
    forall dv,
      show_dvalue dv = DV1.show_dvalue (fin_to_inf_dvalue dv).
  Proof.
    intros dv.
    induction dv; cbn; rewrite_fin_to_inf_dvalue; cbn; auto;
      try rewrite show_dvalue_fin_inf_helper; auto.

    rewrite show_addr_fin_inf; reflexivity.
    rewrite show_intptr_fin_inf; reflexivity.
  Qed.

  Lemma ceres_to_sexp_fin_inf :
    forall dv_fin dv_inf,
      dvalue_refine_strict dv_inf dv_fin ->
      CeresSerialize.to_sexp dv_fin = CeresSerialize.to_sexp dv_inf.
  Proof.
    induction dv_fin using DV2.dvalue_strong_ind;
      intros dv_inf REF;
      try dvalue_refine_strict_inv REF;
      try reflexivity.

    destruct dv_fin;
      try dvalue_refine_strict_inv REF;
      try reflexivity.

    - (* Structs *)
      cbn.
      assert ((map
         (fun x0 : DV2.dvalue =>
            CeresS.List [CeresSerialize.to_sexp x0; CeresS.Atom_ (CeresS.Raw ",")]) fields) =
                (map
         (fun x0 : DV1.dvalue =>
            CeresS.List [CeresSerialize.to_sexp x0; CeresS.Atom_ (CeresS.Raw ",")]) x)).
      { generalize dependent fields.
        induction x; intros fields H H1;
          cbn in H1; inv H1; auto.

        repeat break_match_hyp_inv.
        cbn.
        erewrite H; eauto.
        2: repeat constructor.

        rewrite IHx; eauto.

        intros u H0 dv_inf H1.
        eapply H; eauto.
        clear - H0.
        dependent induction H0.
        - inv H.
          constructor.
          constructor.
          right; auto.
        - specialize (IHclos_trans2 _ eq_refl).
          eapply t_trans.
          apply H0_.
          apply IHclos_trans2.        
      }

      rewrite H0.
      reflexivity.
    - (* Packed structs *)
      cbn.
      assert ((map
         (fun x0 : DV2.dvalue =>
            CeresS.List [CeresSerialize.to_sexp x0; CeresS.Atom_ (CeresS.Raw ",")]) fields) =
                (map
         (fun x0 : DV1.dvalue =>
            CeresS.List [CeresSerialize.to_sexp x0; CeresS.Atom_ (CeresS.Raw ",")]) x)).
      { generalize dependent fields.
        induction x; intros fields H H1;
          cbn in H1; inv H1; auto.

        repeat break_match_hyp_inv.
        cbn.
        erewrite H; eauto.
        2: repeat constructor.

        rewrite IHx; eauto.

        intros u H0 dv_inf H1.
        eapply H; eauto.
        clear - H0.
        dependent induction H0.
        - inv H.
          constructor.
          constructor.
          right; auto.
        - specialize (IHclos_trans2 _ eq_refl).
          eapply t_trans.
          apply H0_.
          apply IHclos_trans2.        
      }

      rewrite H0.
      reflexivity.
    - (* Arrays *)
      cbn.
      assert ((map
         (fun x0 : DV2.dvalue =>
            CeresS.List [CeresSerialize.to_sexp x0; CeresS.Atom_ (CeresS.Raw ",")]) elts) =
                (map
         (fun x0 : DV1.dvalue =>
            CeresS.List [CeresSerialize.to_sexp x0; CeresS.Atom_ (CeresS.Raw ",")]) x)).
      { generalize dependent elts.
        induction x; intros elts H H1;
          cbn in H1; inv H1; auto.

        repeat break_match_hyp_inv.
        cbn.
        erewrite H; eauto.
        2: repeat constructor.

        rewrite IHx; eauto.

        intros u H0 dv_inf H1.
        eapply H; eauto.
        clear - H0.
        dependent induction H0.
        - inv H.
          constructor.
          constructor.
          right; auto.
        - specialize (IHclos_trans2 t _ eq_refl).
          eapply t_trans.
          apply H0_.
          apply IHclos_trans2.        
      }

      rewrite H0.
      reflexivity.
    - (* Vectors *)
      cbn.
      assert ((map
         (fun x0 : DV2.dvalue =>
            CeresS.List [CeresSerialize.to_sexp x0; CeresS.Atom_ (CeresS.Raw ",")]) elts) =
                (map
         (fun x0 : DV1.dvalue =>
            CeresS.List [CeresSerialize.to_sexp x0; CeresS.Atom_ (CeresS.Raw ",")]) x)).
      { generalize dependent elts.
        induction x; intros elts H H1;
          cbn in H1; inv H1; auto.

        repeat break_match_hyp_inv.
        cbn.
        erewrite H; eauto.
        2: repeat constructor.

        rewrite IHx; eauto.

        intros u H0 dv_inf H1.
        eapply H; eauto.
        clear - H0.
        dependent induction H0.
        - inv H.
          constructor.
          constructor.
          right; auto.
        - specialize (IHclos_trans2 t _ eq_refl).
          eapply t_trans.
          apply H0_.
          apply IHclos_trans2.        
      }

      rewrite H0.
      reflexivity.
  Qed.

  Lemma ceres_to_string_fin_inf :
    forall dv_fin dv_inf,
      dvalue_refine_strict dv_inf dv_fin ->
      CeresSerialize.to_string dv_fin = CeresSerialize.to_string dv_inf.
  Proof.
    intros dv_fin dv_inf REF.
    unfold CeresSerialize.to_string.
    erewrite ceres_to_sexp_fin_inf; eauto.
  Qed.

  Lemma lift_err_uvalue_to_dvalue_rutt_strict :
    forall uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      rutt (sum_prerel call_refine_strict event_refine_strict) (sum_postrel call_res_refine_strict event_res_refine_strict) dvalue_refine_strict
        (LLVMEvents.lift_err (fun x : DV1.dvalue => Ret x) (DV1.uvalue_to_dvalue uv1))
        (LLVMEvents.lift_err (fun x : dvalue => Ret x) (uvalue_to_dvalue uv2)).
  Proof.
    intros uv1 uv2 H.
    destruct uv1; cbn in *;
      try solve
        [ unfold uvalue_refine_strict in *;
          cbn in *; inv H; cbn;
          apply rutt_Ret;
          unfold dvalue_refine_strict; reflexivity
        | unfold uvalue_refine_strict in *;
          cbn in *; inv H; cbn;
          apply rutt_raise; constructor; cbn; auto
        | unfold uvalue_refine_strict in *;
          cbn in *;
          repeat break_match_hyp_inv;
          cbn;
          apply rutt_Ret;
          unfold dvalue_refine_strict;
          cbn;
          rewrite Heqo;
          reflexivity
        | unfold uvalue_refine_strict in *;
          cbn in *;
          repeat break_match_hyp_inv;
          cbn;
          apply rutt_raise;
          constructor;
          constructor
        ].

    - (* Structs *)
      unfold uvalue_refine_strict in H.
      cbn in *.
      break_match_hyp_inv.
      assert (uvalue_refine_strict (DV1.UVALUE_Struct fields) (DV2.UVALUE_Struct l)) as REF.
      { unfold uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }
      break_match_goal; cbn.
      { epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp_inv.

        cbn.
        apply rutt_raise.
        constructor.
        constructor.
      }
      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply rutt_Ret.
      unfold dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp_inv.
      unfold dvalue_refine_strict in H2.
      cbn in H2.
      break_match_hyp_inv.
      inversion Heqs0.
      reflexivity.

    - (* Packed Structs *)
      unfold uvalue_refine_strict in H.
      cbn in *.
      break_match_hyp_inv.

      assert (uvalue_refine_strict (DV1.UVALUE_Struct fields) (DV2.UVALUE_Struct l)) as REF.
      { unfold uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal; cbn.
      { epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp_inv.

        cbn.
        apply rutt_raise.
        constructor.
        constructor.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply rutt_Ret.
      unfold dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp_inv.
      unfold dvalue_refine_strict.
      unfold dvalue_refine_strict in H2.
      cbn in H2.
      break_match_hyp_inv.
      inversion Heqs0.
      reflexivity.

    - (* Arrays *)
      unfold uvalue_refine_strict in H.
      cbn in *.
      break_match_hyp_inv.

      assert (uvalue_refine_strict (DV1.UVALUE_Array t elts) (DV2.UVALUE_Array t l)) as REF.
      { unfold uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal; cbn.
      { epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp_inv.

        cbn.
        apply rutt_raise.
        constructor.
        constructor.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply rutt_Ret.
      unfold dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp_inv.
      unfold dvalue_refine_strict.
      unfold dvalue_refine_strict in H2.
      cbn in H2.
      break_match_hyp_inv.
      inversion Heqs0.
      reflexivity.

    - (* Vectors *)
      unfold uvalue_refine_strict in H.
      cbn in *.
      break_match_hyp_inv.

      assert (uvalue_refine_strict (DV1.UVALUE_Array t elts) (DV2.UVALUE_Array t l)) as REF.
      { unfold uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal; cbn.
      { epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp_inv.

        cbn.
        apply rutt_raise.
        constructor.
        constructor.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply rutt_Ret.
      unfold dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp_inv.
      unfold dvalue_refine_strict.
      unfold dvalue_refine_strict in H2.
      cbn in H2.
      break_match_hyp_inv.
      inversion Heqs0.
      reflexivity.
  Qed.

  Lemma lift_err_orutt_strict :
    forall E1 E2
      `{OOM1 : OOME -< E1} `{OOM2 : OOME -< E2}
      `{ERR1: FailureE -< E1} `{ERR2: FailureE -< E2}
      {A B}
      (pre : prerel E1 E2) (post : postrel E1 E2) RR (a : err A) (b : err B),
      (forall e1 e2, @subevent FailureE E2 ERR2 void e1 <> @subevent OOME E2 OOM2 void e2) ->
      (pre void void (@subevent FailureE E1 ERR1 void (Throw tt)) (@subevent FailureE E2 ERR2 void (Throw tt))) ->
      sum_rel VellvmRelations.TT RR a b ->
      orutt pre post RR
        (LLVMEvents.lift_err (fun x => Ret x) a)
        (LLVMEvents.lift_err (fun x => Ret x) b)
        (OOM:=OOME).
  Proof.
    intros E1 E2 OOM1 OOM2 ERR1 ERR2 A B pre post RR a b ERRDISC PRETHROW RAB.
    destruct a, b; destruct RAB; cbn in *; eauto with ORUTT.
  Qed.

  #[global] Hint Resolve
   lift_err_orutt_strict
    : ORUTT.

  Lemma lift_err_uvalue_to_dvalue_orutt_strict :
    forall E1 E2
      `{OOM1 : OOME -< E1} `{OOM2 : OOME -< E2}
      `{ERR1: FailureE -< E1} `{ERR2: FailureE -< E2}
      (pre : prerel E1 E2) (post : postrel E1 E2)
      (ERRDISC : forall e1 e2, @subevent FailureE E2 ERR2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (ERRPRE : pre void void (@subevent FailureE E1 ERR1 void (Throw tt)) (@subevent FailureE E2 ERR2 void (Throw tt)))
      uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      orutt pre post dvalue_refine_strict
        (LLVMEvents.lift_err (fun x : DV1.dvalue => Ret x) (DV1.uvalue_to_dvalue uv1))
        (LLVMEvents.lift_err (fun x : dvalue => Ret x) (uvalue_to_dvalue uv2))
        (OOM:=OOME).
  Proof.
    intros E1 E2 OOM1 OOM2 ERR1 ERR2 pre post ERRDISC ERRPRE uv1 uv2 H.
    apply lift_err_orutt_strict; try typeclasses eauto; eauto; repeat constructor.
    destruct (DV1.uvalue_to_dvalue uv1) eqn:Huv1.
    - pose proof Huv1 as Huv1'.
      eapply uvalue_to_dvalue_dvalue_refine_strict_error in Huv1; eauto.
      destruct Huv1 as (?&Huv1); rewrite Huv1.
      repeat constructor.
    - pose proof Huv1 as Huv1'.
      eapply uvalue_to_dvalue_dvalue_refine_strict in Huv1; eauto.
      destruct Huv1 as (?&Huv1&HREF); rewrite Huv1.
      repeat constructor; auto.
  Qed.

  #[global] Hint Resolve
   lift_err_uvalue_to_dvalue_orutt_strict
    : ORUTT.

  Lemma fin_to_inf_dvalue_dvalue_int_unsigned :
    forall dv,
      DV1.dvalue_int_unsigned (fin_to_inf_dvalue dv) = dvalue_int_unsigned dv.
  Proof.
    intros dv.
    destruct dv; cbn;
      rewrite_fin_to_inf_dvalue;
      cbn;
      auto.

    unfold intptr_fin_inf.
    break_match; clear Heqs.
    apply IS1.LP.IP.from_Z_to_Z in e.
    rewrite <- IP.to_Z_to_unsigned.
    rewrite <- IS1.LP.IP.to_Z_to_unsigned.
    auto.
  Qed.

  (* TODO: Move this *)
  Lemma addr_convert_safe_reverse :
    forall a1 a2,
      AC1.addr_convert a1 = NoOom a2 ->
      AC2.addr_convert a2 = NoOom a1.
  Proof.
    intros a1 a2 H.
    pose proof addr_refine_fin_to_inf_addr a2 as REF.
    red in REF.
    unfold fin_to_inf_addr in REF.
    break_match_hyp.
    clear Heqs.
    rewrite e.
    pose proof (AC1.addr_convert_injective _ _ _ H REF); subst; auto.
  Qed.

  Lemma dvalue_refine_strict_map_fin_to_inf_dvalue :
    forall a b,
      Forall2 dvalue_refine_strict a b ->
      a = map fin_to_inf_dvalue b.
  Proof.
    intros a b H.
    induction H; cbn; auto.

    subst.
    unfold fin_to_inf_dvalue at 2.
    break_match; clear Heqs.
    destruct p.
    red in H.
    pose proof dvalue_refine_strict_R2_injective x y x0 y H e0 as (_&?).
    rewrite H1; auto.
  Qed.

  Ltac run_orutt_bind :=
    first [ apply orutt_bind with (RR:=eq)
          | apply orutt_bind with (RR:=uvalue_refine_strict)
          | apply orutt_bind with (RR:=dvalue_refine_strict)
          | apply orutt_bind with (RR:=Forall2 uvalue_refine_strict)
          | apply orutt_bind with (RR:=Forall2 dvalue_refine_strict)
          | apply orutt_bind with (RR:=eq × uvalue_refine_strict)
          | apply orutt_bind with (RR:=Forall2 (eq × uvalue_refine_strict))
          | apply orutt_bind with (RR:=sum_rel uvalue_refine_strict uvalue_refine_strict)
          | apply orutt_bind with (RR:=sum_rel uvalue_refine_strict dvalue_refine_strict)
          | apply orutt_bind with (RR:= fun a b => intptr_fin_inf b = a)
      ].

  #[global] Hint Extern 0 (orutt _ _ _ (bind _ _) (bind _ _)) => run_orutt_bind : ORUTT.
  #[global] Hint Extern 0 (orutt _ _ _ (ITree.bind _ _) (ITree.bind _ _)) => run_orutt_bind : ORUTT.

  Lemma dvalue_refine_strict_preserves_dvalue_is_poison :
    forall x y,
      dvalue_refine_strict x y ->
      DV1.dvalue_is_poison x = DV2.dvalue_is_poison y.
  Proof.
    intros x y H.
    destruct x;
      unfold dvalue_refine_strict in *; cbn in *; try break_match_hyp; inv H; cbn; auto.
  Qed.

  Lemma dtyp_of_uvalue_fun_fin_inf :
    forall uv_fin uv_inf,
      uvalue_refine_strict uv_inf uv_fin ->
      DV1.dtyp_of_uvalue_fun uv_inf = dtyp_of_uvalue_fun uv_fin.
  Proof.
    intros uv_fin.
    induction uv_fin using uvalue_ind;
      intros uv_inf REF;
      uvalue_refine_strict_inv REF;
      try solve
        [ cbn; auto
        | cbn;
          erewrite IHuv_fin1; eauto;
          erewrite IHuv_fin2; eauto
        ].
    - apply map_monad_oom_Forall2 in H1.
      induction H1.
      + cbn; auto.
      + cbn.
        erewrite H; cbn; eauto.
        break_inner_match; auto.
        forward IHForall2.
        { intros u H2 uv_inf H3.
          apply H; cbn; eauto.
        }
        cbn in IHForall2.
        repeat break_match_hyp; inv IHForall2; auto.
    - apply map_monad_oom_Forall2 in H1.
      induction H1.
      + cbn; auto.
      + cbn.
        erewrite H; cbn; eauto.
        break_inner_match; auto.
        forward IHForall2.
        { intros u H2 uv_inf H3.
          apply H; cbn; eauto.
        }
        cbn in IHForall2.
        repeat break_match_hyp; inv IHForall2; auto.
    - apply map_monad_oom_Forall2 in H1.
      induction H1.
      + cbn; auto.
      + cbn.
        erewrite H; cbn; eauto.
        break_inner_match; auto.
        pose proof H1 as FORALL.
        apply Forall2_length in H1; subst.
        forward IHForall2.
        intros e H2 uv_inf H3.
        apply H; cbn; eauto.
        cbn in IHForall2.
        Transparent Datatypes.length.
        cbn.
        Opaque Datatypes.length.
        repeat break_match_goal;
          try congruence; exfalso.

        * invert_bools.
          rewrite <- H1, H2, H3 in Heqb0.
          cbn in Heqb0.
          rewrite <- H1, H4 in IHForall2.
          cbn in IHForall2.
          repeat break_match_hyp_inv.
          inv Heqb0.
          rewrite Bool.andb_true_r in Heqb0.
          clear Heqb1.
          apply dtyp_eqb_eq in H6; subst.

          apply forallb_false in Heqb0 as (?&?&?).
          erewrite <- H in H5; cbn; eauto.
          2: apply fin_to_inf_uvalue_refine_strict.
          eapply forallb_forall with (x:=(fin_to_inf_uvalue x0)) in H4.
          rewrite H4 in H5; discriminate.
          eapply Forall2_In_exists2 in FORALL; eauto.
          destruct FORALL as (?&?&?).
          erewrite <- fin_to_inf_uvalue_refine_strict'; eauto.
        * invert_bools.
          rewrite H1, H2, H3 in Heqb.
          cbn in Heqb.
          rewrite <- H1, H4 in IHForall2.
          cbn in IHForall2.
          rewrite Bool.andb_true_r in Heqb.
          repeat break_match_hyp_inv;
            rewrite Heqb in Heqb0.
          inv Heqb0.
          apply dtyp_eqb_eq in H6; subst.

          apply forallb_false in Heqb as (?&?&?).
          eapply Forall2_In in FORALL; eauto.
          destruct FORALL as (?&?&?).
          erewrite H in H5; cbn; eauto.
          eapply forallb_forall with (x:=x1) in H4; auto.
          rewrite H4 in H5; discriminate.
    - apply map_monad_oom_Forall2 in H1.
      induction H1.
      + cbn; auto.
      + cbn.
        erewrite H; cbn; eauto.
        break_inner_match; auto.
        pose proof H1 as FORALL.
        apply Forall2_length in H1; subst.
        forward IHForall2.
        intros e H2 uv_inf H3.
        apply H; cbn; eauto.
        cbn in IHForall2.
        Transparent Datatypes.length.
        cbn.
        Opaque Datatypes.length.
        repeat break_match_goal;
          try congruence; exfalso.

        * invert_bools.
          rewrite <- H1, H2, H3 in Heqb0.
          cbn in Heqb0.
          rewrite <- H1, H4 in IHForall2.
          cbn in IHForall2.
          repeat break_match_hyp_inv.
          inv Heqb0.
          rewrite Bool.andb_true_r in Heqb0.
          clear Heqb1.
          apply dtyp_eqb_eq in H6; subst.

          apply forallb_false in Heqb0 as (?&?&?).
          erewrite <- H in H5; cbn; eauto.
          2: apply fin_to_inf_uvalue_refine_strict.
          eapply forallb_forall with (x:=(fin_to_inf_uvalue x0)) in H4.
          rewrite H4 in H5; discriminate.
          eapply Forall2_In_exists2 in FORALL; eauto.
          destruct FORALL as (?&?&?).
          erewrite <- fin_to_inf_uvalue_refine_strict'; eauto.
        * invert_bools.
          rewrite <- H1, H2, H3 in Heqb0.
          cbn in Heqb0.
          rewrite <- H1, H4 in IHForall2.
          cbn in IHForall2.
          repeat break_match_hyp_inv.
          inv Heqb0.
          rewrite Bool.andb_true_r in Heqb0.
          clear Heqb1.
          apply dtyp_eqb_eq in H6; subst.

          apply forallb_false in Heqb0 as (?&?&?).
          erewrite <- H in H5; cbn; eauto.
          2: apply fin_to_inf_uvalue_refine_strict.
          eapply forallb_forall with (x:=(fin_to_inf_uvalue x0)) in H4.
          rewrite H4 in H5; discriminate.
          eapply Forall2_In_exists2 in FORALL; eauto.
          destruct FORALL as (?&?&?).
          erewrite <- fin_to_inf_uvalue_refine_strict'; eauto.
        * invert_bools.
          rewrite H1, H2, H3 in Heqb.
          cbn in Heqb.
          rewrite <- H1, H4 in IHForall2.
          cbn in IHForall2.
          rewrite Bool.andb_true_r in Heqb.
          repeat break_match_hyp_inv;
            rewrite Heqb in Heqb0.
          inv Heqb0.
          apply dtyp_eqb_eq in H6; subst.

          apply forallb_false in Heqb as (?&?&?).
          eapply Forall2_In in FORALL; eauto.
          destruct FORALL as (?&?&?).
          erewrite H in H5; cbn; eauto.
          eapply forallb_forall with (x:=x1) in H4; auto.
          rewrite H4 in H5; discriminate.
        * invert_bools.
          rewrite H1, H2, H3 in Heqb.
          cbn in Heqb.
          rewrite <- H1, H4 in IHForall2.
          cbn in IHForall2.
          rewrite Bool.andb_true_r in Heqb.
          repeat break_match_hyp_inv;
            rewrite Heqb in Heqb0.
          inv Heqb0.
          apply dtyp_eqb_eq in H6; subst.

          apply forallb_false in Heqb as (?&?&?).
          eapply Forall2_In in FORALL; eauto.
          destruct FORALL as (?&?&?).
          erewrite H in H5; cbn; eauto.
          eapply forallb_forall with (x:=x1) in H4; auto.
          rewrite H4 in H5; discriminate.
    - cbn.
      erewrite IHuv_fin; eauto.
    - cbn.
      erewrite IHuv_fin; eauto.
    - cbn.
      erewrite IHuv_fin2; eauto.
      erewrite IHuv_fin1; eauto.
    - cbn.
      erewrite IHuv_fin3; eauto.
      erewrite IHuv_fin1; eauto.
      erewrite IHuv_fin2; eauto.
    - cbn.
      erewrite IHuv_fin3; eauto.
      erewrite IHuv_fin1; eauto.
      erewrite IHuv_fin2; eauto.
    - cbn.
      erewrite IHuv_fin; eauto.
    - cbn.
      erewrite IHuv_fin1; eauto.
      erewrite IHuv_fin2; eauto.
      erewrite IHuv_fin3; eauto.
    - apply map_monad_oom_Forall2 in H1.
      induction H1.
      + cbn; auto.
        rewrite sizeof_dtyp_fin_inf.
        auto.
      + cbn.
        rewrite sizeof_dtyp_fin_inf.
        pose proof H1 as FORALL.
        apply Forall2_length in H1; subst.
        forward IHForall2.
        intros e H2 uv_inf H3.
        apply H; cbn; eauto.
        cbn in IHForall2.
        Transparent Datatypes.length.
        cbn.
        Opaque Datatypes.length.
        repeat break_match_goal;
          try congruence; exfalso.

        * invert_bools.
          rewrite <- H1, H2 in Heqb0.
          cbn in Heqb0.
          destruct x; inv H3.
          cbn in H0.
          destruct (uvalue_convert_strict x) eqn:?; inv H0.
          cbn in Heqb0.
          rewrite <- H1, H4, Heqb0, sizeof_dtyp_fin_inf in IHForall2.
          destruct ((N.of_nat (Datatypes.length l) =? SZ.sizeof_dtyp dt)%N); inv IHForall2.
          apply forallb_false in Heqb0 as (?&?&?).
          eapply Forall2_In_exists2 in FORALL; eauto.
          destruct FORALL as (?&?&?).
          eapply forallb_forall in H4; eauto.
          destruct x0; inv H3; uvalue_convert_strict_inv H6; discriminate.
        * invert_bools.
          rewrite H1, H2 in Heqb.
          cbn in Heqb.
          destruct y; inv H3.
          uvalue_convert_strict_inv H0.
          cbn in Heqb.
          apply forallb_false in Heqb as (?&?&?).
          eapply Forall2_In in FORALL; eauto.
          destruct FORALL as (?&?&?).
          eapply forallb_forall in H4; eauto.
          destruct x1; inv H4; uvalue_convert_strict_inv H7; discriminate.
  Qed.

  Lemma orutt_L0'_from_Z :
    forall ix,
      orutt (OOM:=OOME) L0'_refine_strict L0'_res_refine_strict
        (fun (ip_inf : IS1.LP.IP.intptr) (ip_fin : IP.intptr) => intptr_fin_inf ip_fin = ip_inf)
        (lift_OOM (IS1.LP.IP.from_Z ix)) (lift_OOM (IP.from_Z ix)).
  Proof.
    intros ix.
    unfold lift_OOM.
    destruct (IP.from_Z ix) eqn:HIX.
    2: {
      eapply orutt_raise_oom.
    }

    pose proof IP.from_Z_to_Z _ _ HIX.
    subst.
    pose proof (intptr_convert_succeeds i) as (?&?).
    rewrite e.
    eapply orutt_Ret.
    unfold intptr_fin_inf.
    break_match_goal.
    clear Heqs.
    rewrite e in e0.
    inv e0; auto.
  Qed.

  Lemma i8_array_of_string_fin_inf :
    forall str,
      uvalue_refine_strict (LLVM1.i8_array_of_string str) (LLVM2.i8_array_of_string str).
  Proof.
    intros str.
    unfold LLVM1.i8_array_of_string, LLVM2.i8_array_of_string.
    induction str.
    - cbn.
      solve_uvalue_refine_strict.
    - uvalue_refine_strict_inv IHstr.
      inv H.
      red; cbn.
      rewrite H0.
      reflexivity.
  Qed.
End ValueRefine.
