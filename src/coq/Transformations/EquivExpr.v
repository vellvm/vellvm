From Coq Require Import
     Lia
     String
     Morphisms.

Require Import Paco.paco.

Require Import List.
Import ListNotations.
Require Import ZArith.

From ITree Require Import
     ITree
     Basics.Monad
     Eq.Eq
     InterpFacts
     TranslateFacts.

From Vellvm Require Import
     Utils.Util
     Utils.Tactics
     Utils.PostConditions
     Syntax.Scope
     Syntax.ScopeTheory
     Syntax.LLVMAst
     Syntax.Traversal
     Syntax.CFG
     Syntax.AstLib
     Syntax.DynamicTypes
     Handlers.Handlers
     Semantics.LLVMEvents
     Semantics.InterpretationStack
     Semantics.TopLevel
     Theory.InterpreterCFG
     Theory.DenotationTheory.

Import ITreeNotations.
Import SemNotations.

Section ExpOptim.

  Definition exp_optimization := exp dtyp -> exp dtyp.

  Variable opt : exp_optimization.
  Instance opt_exp_endo_exp : Endo (exp dtyp) := opt.

  Definition opt_exp_instr  : Endo (instr dtyp) := endo.
  Definition opt_exp_cfg  : Endo (cfg dtyp) := endo.
  Definition opt_exp_mcfg : Endo (mcfg dtyp) := endo.

  Lemma map_monad_eutt_ind :
    forall {E A B} (f g : A -> itree E B) (h : A -> A) (l : list A),
      (forall a, In a l -> f a ≈ g (h a)) ->
      map_monad f l ≈ map_monad g (map h l).
  Proof.
    induction l as [| x l IH]; intros EQ; [reflexivity | cbn].
    apply eutt_clo_bind with (UU := eq).
    apply EQ; left; auto.
    intros ? ? <-.
    rewrite IH.
    reflexivity.
    intros; apply EQ; right; auto.
  Qed.

  Section ExpOptimCorrect.

    Variable opt_correct: forall e τ g l m, ⟦ e at? τ ⟧e3 g l m ≈ ⟦ opt e at? τ ⟧e3 g l m.
    Variable opt_respect_int: forall e, intrinsic_exp e = intrinsic_exp (opt e).

    Ltac intro3 := first [intros (? & ? & ? & ?) ? <- | intros (? & ? & ? & ?)].

    Lemma exp_optim_correct_instr : forall x i g l m,
        ⟦ (x,i) ⟧i3 g l m ≈ ⟦ (x, endo i) ⟧i3 g l m.
    Proof.
      intros *.
      destruct i; try reflexivity.
      - destruct x; simpl; try reflexivity.
        unfold denote_op.
        rewrite !interp_cfg3_bind.
        rewrite opt_correct; reflexivity.
      - destruct x; simpl.
        + destruct fn.
          simpl.
          rewrite !interp_cfg3_bind.
          apply eutt_clo_bind with (UU := eq).
          * revert g l m.
            induction args as [| a args IH]; intros; [reflexivity |].
            cbn.
            rewrite !interp_cfg3_bind; apply eutt_clo_bind with (UU := eq).
            destruct a; cbn; rewrite opt_correct; reflexivity.
            intro3.
            rewrite !interp_cfg3_bind; apply eutt_clo_bind with (UU := eq); [apply IH |].
            intro3.
            reflexivity.
          * intro3.
            rewrite !interp_cfg3_bind; apply eutt_clo_bind with (UU := eq).
            rewrite opt_respect_int.
            unfold endo, opt_exp_endo_exp.
            break_match_goal; [reflexivity |].
            rewrite !interp_cfg3_bind, opt_correct; reflexivity.
            intro3.
            reflexivity.
        + destruct fn.
          simpl.
          rewrite !interp_cfg3_bind.
          apply eutt_clo_bind with (UU := eq).
          * revert g l m.
            induction args as [| a args IH]; intros; [reflexivity |].
            cbn.
            rewrite !interp_cfg3_bind; apply eutt_clo_bind with (UU := eq).
            destruct a; cbn; rewrite opt_correct; reflexivity.
            intro3.
            rewrite !interp_cfg3_bind; apply eutt_clo_bind with (UU := eq); [apply IH |].
            intro3.
            reflexivity.
          * intro3.
            rewrite !interp_cfg3_bind; apply eutt_clo_bind with (UU := eq).
            rewrite opt_respect_int.
            unfold endo, opt_exp_endo_exp.
            break_match_goal; [reflexivity |].
            rewrite !interp_cfg3_bind, opt_correct; reflexivity.
            intro3.
            reflexivity.
      - destruct x; cbn; try reflexivity.
        destruct ptr; cbn.
        rewrite !interp_cfg3_bind; apply eutt_clo_bind with (UU := eq).
        rewrite opt_correct; reflexivity.
        intro3.
        rewrite !interp_cfg3_bind; apply eutt_eq_bind.
        intro3.
        reflexivity.
      - destruct x; cbn; try reflexivity.
        destruct ptr, val; cbn.
        rewrite !interp_cfg3_bind; apply eutt_clo_bind with (UU := eq).
        rewrite opt_correct; reflexivity.
        intro3.
        rewrite !interp_cfg3_bind; apply eutt_eq_bind.
        intro3.
        rewrite !interp_cfg3_bind; apply eutt_clo_bind with (UU := eq).
        rewrite opt_correct; reflexivity.
        intro3.
        reflexivity.
    Qed.
    
    Lemma exp_optim_correct_term : forall t g l m,
        ⟦ t ⟧t3 g l m ≈ ⟦ endo t ⟧t3 g l m.
    Proof.
      intros *.
      destruct t; try reflexivity.
      - destruct v.
        cbn.
        rewrite !translate_bind, !interp_cfg3_bind.
        rewrite opt_correct; apply eutt_eq_bind.
        intro3; reflexivity.
      - destruct v; cbn.
        rewrite !translate_bind, !interp_cfg3_bind.
        rewrite opt_correct; apply eutt_eq_bind.
        intro3.
        rewrite !translate_bind, !interp_cfg3_bind.
        apply eutt_eq_bind.
        intro3.
        break_match_goal; try reflexivity.
      - destruct v.
        cbn.
        rewrite !translate_bind, !interp_cfg3_bind.
        rewrite opt_correct; apply eutt_eq_bind.
        intro3.
        rewrite !translate_bind, !interp_cfg3_bind.
        apply eutt_eq_bind.
        intro3.
        assert (EQ:
                  ℑ3 (translate exp_to_instr (switches <- map_monad (fun '(t, e0, id) => us <- ⟦ e0 at t ⟧e;; s <- pickUnique us;; Ret1 s id) brs;; lift_err (fun b : block_id => Ret (@inl block_id uvalue b)) (select_switch d0 default_dest switches))) g1 l1 m1
  ≈ ℑ3
      (translate exp_to_instr
         (switches <- map_monad (fun '(t, e0, id) => us <- ⟦ e0 at t ⟧e;; s <- pickUnique us;; Ret1 s id) (endo brs);; lift_err (fun b : block_id => Ret (inl b)) (select_switch d0 (endo default_dest) switches)
      )) g1 l1 m1).
        { 
          rewrite !translate_bind,!interp_cfg3_bind; apply eutt_clo_bind with (UU := eq); [| intro3; reflexivity].
          revert g1 l1 m1; induction brs as [| x brs IH]; intros; [reflexivity |].
          cbn.
          rewrite !translate_bind,!interp_cfg3_bind; apply eutt_clo_bind with (UU := eq).
          destruct x,t; cbn.
          rewrite !translate_bind,!interp_cfg3_bind.
          apply eutt_clo_bind with (UU := eq).
          rewrite opt_correct; reflexivity.
          intro3.
          reflexivity. 
          intro3.
          rewrite !translate_bind,!interp_cfg3_bind; apply eutt_clo_bind with (UU := eq).
          rewrite IH; reflexivity.
          intro3; reflexivity.
        }
        break_match_goal; try apply EQ; reflexivity.
    Qed.

    Lemma exp_optim_correct_code : forall c g l m,
        ⟦ c ⟧c3 g l m ≈ ⟦ endo c ⟧c3 g l m.
    Proof.
      induction c as [| i c IH]; intros; [reflexivity |].
      unfold endo; simpl.
      rewrite 2denote_code_cons, 2interp_cfg3_bind.
      apply eutt_clo_bind with (UU := eq).
      destruct i as [[] ?]; apply exp_optim_correct_instr.
      intro3.
      apply IH.
    Qed.

    Lemma exp_optim_correct_phi : forall phi f g l m,
        ℑ3 (translate exp_to_instr ⟦ phi ⟧Φ (f)) g l m ≈ ℑ3 (translate exp_to_instr ⟦ endo phi ⟧Φ (f)) g l m.
    Proof.
      intros [id []] f.
      induction args as [| [] args Ih]; intros; [reflexivity |].
      cbn.
      do 2 break_match_goal.
      - unfold endo,Endo_id in Heqo0.
        break_match_hyp.
        + inv Heqo; inv Heqo0.
          rewrite 2translate_bind, 2interp_cfg3_bind.
          apply eutt_clo_bind with (UU := eq); [| intro3].
    Admitted.
            
    Lemma exp_optim_correct_phis : forall phis f g l m,
        ⟦ phis ⟧Φs3 f g l m ≈ ⟦ endo phis ⟧Φs3 f g l m.
    Proof.
      intros.
      unfold endo; simpl.
      cbn.
      rewrite !interp_cfg3_bind. 
      apply eutt_clo_bind with (UU := eq); [| intro3].
      {
        revert g l m.
        induction phis as [| phi phis IH]; intros; [reflexivity |].
        cbn.
        rewrite !interp_cfg3_bind. 
        apply eutt_clo_bind with (UU := eq); [| intro3].
        apply exp_optim_correct_phi.
        rewrite !interp_cfg3_bind. 
        apply eutt_clo_bind with (UU := eq); [| intro3; reflexivity].
        apply IH.
      }
      reflexivity.
    Qed.

    Arguments denote_block : simpl never.
    Lemma exp_optim_correct_block : forall bk f g l m,
        ⟦ bk ⟧b3 f g l m ≈ ⟦ endo bk ⟧b3 f g l m.
    Proof.
      intros *.
      destruct bk; unfold endo, Endo_block; cbn.
      rewrite !denote_block_unfold.
      rewrite 2interp_cfg3_bind.
      apply eutt_clo_bind with (UU := eq).
      apply exp_optim_correct_phis.
      intro3.
      rewrite 2interp_cfg3_bind.
      apply eutt_clo_bind with (UU := eq).
      apply exp_optim_correct_code.
      intro3.
      apply exp_optim_correct_term.
    Qed.

    Lemma denote_ocfg_proper :
      forall bks1 bks2 fto g l m,
        (forall b, find_block bks1 b = None <-> find_block bks2 b = None) ->
        (forall f g l m b bk1 bk2,
            find_block bks1 b = Some bk1 ->
            find_block bks2 b = Some bk2 ->
            ⟦ bk1 ⟧b3 f g l m ≈ ⟦ bk2 ⟧b3 f g l m) ->
        ⟦ bks1 ⟧bs3 fto g l m ≈ ⟦ bks2 ⟧bs3 fto g l m. 
    Proof.
      intros * BIJ EQ.
      (* Arg need to commut [interp_cfg3] with [iter], need a lemma for that *)

      (* rewrite interp_iter. *)
      (* apply eutt_interp_cfg3; auto. *)
      (* apply KTreeFacts.eutt_iter. *)
      (* intros [f to]. *)
      (* do 2 break_match_goal; try reflexivity. *)
      (* 2: apply BIJ in Heqo0; rewrite Heqo0 in Heqo; inv Heqo. *)
      (* 2: apply BIJ in Heqo; rewrite Heqo in Heqo0; inv Heqo0. *)
      (* cbn. *)
    Admitted.

    Lemma exp_optim_correct :
      forall G g l m, ⟦ G ⟧cfg3 g l m ≈ ⟦ opt_exp_cfg G ⟧cfg3 g l m.
    Proof.
      intros.
      unfold denote_cfg.
      cbn.
      rewrite !interp_cfg3_bind.
      eapply eutt_clo_bind with (UU := eq); [| intro3; reflexivity].
      apply denote_ocfg_proper.
      - intros.
        remember (blks G) as bks.
        clear - opt_correct opt_respect_int.
        induction bks as [| bk bks IH]; [cbn; split; auto |].
        split.
        + intros LU; cbn in *.
          unfold endo, Endo_id.
          break_match_goal; [inv LU |].
          break_match_hyp; intuition.
        + intros LU; cbn in *.
          unfold endo, Endo_id in LU.
          break_match_goal; [inv LU |].
          break_match_hyp; intuition.
      - intros * FIND1 FIND2.
        assert (bk2 = endo bk1).
        {
          remember (blks G) as bks.
          clear - FIND1 FIND2 opt_respect_int opt_correct.
          revert bk1 bk2 FIND1 FIND2.
          induction bks as [| bk bks IH]; intros; [inv FIND1 |].
          cbn in *.
          unfold endo, Endo_id at 1 in FIND2.
          destruct (Eqv.eqv_dec_p (blk_id bk) b) eqn:EQ.
          - inv FIND1; inv FIND2; auto.
          - apply IH; auto.
        }
        subst; apply exp_optim_correct_block.
    Qed.

End ExpOptim.
