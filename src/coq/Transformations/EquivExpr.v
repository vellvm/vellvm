(* begin hide *)
From Coq Require Import
     Lia
     String
     Morphisms.

Require Import List.

Import ListNotations.
Require Import ZArith.

From ITree Require Import
     ITree
     Basics.Monad
     Eq.Eqit
     InterpFacts
     TranslateFacts.

From Vellvm Require Import
     Utilities
     Utils.MapMonadExtra
     Syntax
     Semantics
     Theory
     Theory.Refinement.

Import ITreeNotations.
(* end hide *)

(** * Substitution of equivalent expressions
    Substitution of expressions impact neither the control flow nor the
    liveness information of the graph. Their equivalence can therefore
    be lifted with no restriction to any context: we establish this
    generic fact as [exp_optim_correct].

    Practically, this means that we can define concrete sound optimizations
    of this nature purely by proving rewrite rules over expressions.

    Note: The currently justified optimization is stupid: it fmaps
    a substitution of expressions over the graph.
    We will naturally want to define ways to iterate rewrites locally
    rather than over the whole structure.
 *)
Module Type EquivExpr (IS : InterpreterStack) (TOP : LLVMTopLevel IS) (DT : DenotationTheory IS TOP).
  Import IS.
  Import SemNotations.

  Import DT.

  Module CFGT := CFGTheory IS TOP.
  Import CFGT.

  Module R := Refinement.Make LP LLVM.
  Import R.

  Section MetadataInd.
    Context {T : Set}.
    Variable P : metadata T -> Prop.

    Hypothesis IH_METADATA_Const  : forall tv, P (METADATA_Const tv).
    Hypothesis IH_METADATA_Null : P METADATA_Null.
    Hypothesis IH_METADATA_Nontemporal : P METADATA_Nontemporal.
    Hypothesis IH_METADATA_Invariant_load : P METADATA_Invariant_load.
    Hypothesis IH_METADATA_Invariant_group : P METADATA_Invariant_group.
    Hypothesis IH_METADATA_Nonnull : P METADATA_Nonnull.
    Hypothesis IH_METADATA_Dereferenceable : P METADATA_Dereferenceable.
    Hypothesis IH_METADATA_Dereferenceable_or_null : P METADATA_Dereferenceable_or_null.
    Hypothesis IH_METADATA_Align : P METADATA_Align.
    Hypothesis IH_METADATA_Noundef : P METADATA_Noundef.
    Hypothesis IH_METADATA_Id    : forall id, P (METADATA_Id id).
    Hypothesis IH_METADATA_String : forall str, P (METADATA_String str).
    Hypothesis IH_METADATA_Named : forall strs, P (METADATA_Named strs).
    Hypothesis IH_METADATA_Node : forall (mds : list (metadata T)),
        (forall md, In md mds -> P md) ->
        P (METADATA_Node mds).

    Lemma metadata_ind : forall (md:metadata T), P md.
      fix IH 1.
      remember P as P0 in IH.
      destruct md; auto; subst.
      - apply IH_METADATA_Node.
        { revert mds.
          fix IHMetadata 1. intros [|u mds']. intros. inversion H.
          intros u' [<-|Hin]. apply IH. eapply IHMetadata. apply Hin.
        }
    Qed.
  End MetadataInd.


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
    Proof using Type.
      induction l as [| x l IH]; intros EQ; [reflexivity | cbn].
      apply eutt_clo_bind with (UU := eq).
      apply EQ; left; auto.
      intros ? ? <-.
      rewrite IH.
      reflexivity.
      intros; apply EQ; right; auto.
    Qed.

    Lemma find_num_elements_annotation_endo :
      forall anns,
        find (fun x : annotation dtyp =>
                match x with
                | ANN_num_elements _ => true
                | _ => false
                end) anns = 
          find (fun x : annotation dtyp =>
                  match x with
                  | ANN_num_elements _ => true
                  | _ => false
                  end) (endo anns).
    Proof using Type.
      induction anns; cbn; auto.
      - destruct a; cbn; auto.
    Qed.

    Lemma find_align_annotation_endo :
      forall anns,
        find (fun x : annotation dtyp =>
                match x with
                | ANN_align _ => true
                | _ => false
                end) anns = 
          find (fun x : annotation dtyp =>
                  match x with
                  | ANN_align _ => true
                  | _ => false
                  end) (endo anns).
    Proof using Type.
      induction anns; cbn; auto.
      - destruct a; cbn; auto.
    Qed.

    Section ExpOptimCorrect.

      Variable opt_correct: forall e τ g l, ⟦ e at? τ ⟧e2 g l ≈ ⟦ opt e at? τ ⟧e2 g l.
      Variable opt_respect_int: forall e, intrinsic_exp e = intrinsic_exp (opt e).

      Ltac intro2 := first [intros (? & ? & ?) ? <- | intros (? & ? & ?)].
      Ltac intro3 := first [intros (? & ? & ? & ?) ? <- | intros (? & ? & ? & ?)].

      Lemma exp_optim_correct_instr : forall varargs x i g l,
          ⟦ (x,i) at varargs ⟧i2 g l ≈ ⟦ (x, endo i) at varargs ⟧i2 g l.
      Proof using opt_correct opt_respect_int.
        intros *.
        destruct i; try reflexivity.
        - destruct x; simpl; try reflexivity.
          unfold denote_op.
          rewrite !interp_cfg2_bind.
          rewrite opt_correct; reflexivity.
        - destruct x; simpl.
          + destruct fn.
            simpl.
            rewrite !interp_cfg2_bind.
            apply eutt_clo_bind with (UU := eq).
            * revert g l.
              induction args as [| a args IH]; intros; [reflexivity |].
              cbn.
              rewrite !interp_cfg2_bind; apply eutt_clo_bind with (UU := eq).
              destruct a; destruct t; cbn;
                setoid_rewrite opt_correct at 1;
                reflexivity.
              intro2.
              rewrite !interp_cfg2_bind; apply eutt_clo_bind with (UU := eq); [apply IH |].
              intro2.
              reflexivity.
            * intro2.
              rewrite !interp_cfg2_bind; apply eutt_clo_bind with (UU := eq).
              rewrite opt_respect_int.
              unfold endo, opt_exp_endo_exp.
              break_match_goal.
              { break_match_goal; try reflexivity.
                Opaque denote_exp.
                repeat (break_match_goal; cbn; try reflexivity).
                rewrite !interp_cfg2_bind, opt_correct.
                eapply eutt_clo_bind; try reflexivity.
                intros; subst.
                reflexivity.

                repeat (break_match_goal; cbn; try reflexivity).
                (* va_copy *)
                rewrite !interp_cfg2_bind, opt_correct.
                eapply eutt_clo_bind; try reflexivity.
                intros; subst.
                destruct u2, p.
                rewrite !interp_cfg2_bind.
                eapply eutt_clo_bind; try reflexivity.
                intros ? ? ?; subst.
                destruct u2, p.
                rewrite !interp_cfg2_bind, opt_correct.
                eapply eutt_clo_bind; try reflexivity.
                intros ? ? ?; subst.
                destruct u2, p.
                rewrite !interp_cfg2_bind.
                eapply eutt_clo_bind; try reflexivity.
                intros ? ? ?; subst.
                destruct u2, p.
                reflexivity.
              }
              rewrite !interp_cfg2_bind, opt_correct; reflexivity.
              intro2.
              reflexivity.
          + destruct fn.
            simpl.
            rewrite !interp_cfg2_bind.
            apply eutt_clo_bind with (UU := eq).
            * revert g l.
              induction args as [| a args IH]; intros; [reflexivity |].
              cbn.
              rewrite !interp_cfg2_bind; apply eutt_clo_bind with (UU := eq).
              destruct a; destruct t; cbn; setoid_rewrite opt_correct at 1; reflexivity.
              intro2.
              rewrite !interp_cfg2_bind; apply eutt_clo_bind with (UU := eq); [apply IH |].
              intro2.
              reflexivity.
            * intro2.
              rewrite !interp_cfg2_bind; apply eutt_clo_bind with (UU := eq).
              rewrite opt_respect_int.
              unfold endo, opt_exp_endo_exp.
              break_match_goal.
              { break_match_goal; try reflexivity.
                Opaque denote_exp.
                repeat (break_match_goal; cbn; try reflexivity).
                rewrite !interp_cfg2_bind, opt_correct.
                eapply eutt_clo_bind; try reflexivity.
                intros; subst.
                reflexivity.

                repeat (break_match_goal; cbn; try reflexivity).
                (* va_copy *)
                rewrite !interp_cfg2_bind, opt_correct.
                eapply eutt_clo_bind; try reflexivity.
                intros; subst.
                destruct u2, p.
                rewrite !interp_cfg2_bind.
                eapply eutt_clo_bind; try reflexivity.
                intros ? ? ?; subst.
                destruct u2, p.
                rewrite !interp_cfg2_bind, opt_correct.
                eapply eutt_clo_bind; try reflexivity.
                intros ? ? ?; subst.
                destruct u2, p.
                rewrite !interp_cfg2_bind.
                eapply eutt_clo_bind; try reflexivity.
                intros ? ? ?; subst.
                destruct u2, p.
                reflexivity.
              }
              rewrite !interp_cfg2_bind, opt_correct; reflexivity.
              intro2.
              reflexivity.
        - destruct x; cbn; try reflexivity.
          rewrite <- find_align_annotation_endo.
          rewrite <- find_num_elements_annotation_endo.
          reflexivity.
        - destruct x; cbn; try reflexivity.
          destruct ptr; cbn.
          rewrite !interp_cfg2_bind; apply eutt_clo_bind with (UU := eq).
          setoid_rewrite opt_correct at 1; reflexivity.
          intro2.
          rewrite !interp_cfg2_bind; apply eutt_clo_bind with (UU := eq).
          reflexivity.
          intro2.
          rewrite !interp_cfg2_bind; apply eutt_clo_bind with (UU := eq).
          reflexivity.
          intro2.
          reflexivity.
        - destruct x; cbn; try reflexivity.
          destruct ptr, val; cbn.
          rewrite !interp_cfg2_bind; apply eutt_clo_bind with (UU := eq).
          setoid_rewrite opt_correct at 1; reflexivity.
          intro2.
          rewrite !interp_cfg2_bind; apply eutt_clo_bind with (UU := eq).
          setoid_rewrite opt_correct at 1; reflexivity.
          intro2.
          rewrite !interp_cfg2_bind; apply eutt_clo_bind with (UU := eq).
          reflexivity.
          intro2.
          reflexivity.
      Qed.

      Opaque denote_exp.
      Lemma exp_optim_correct_term : forall t g l,
          ⟦ t ⟧t2 g l ≈ ⟦ endo t ⟧t2 g l.
      Proof using opt_correct.
        intros *.
        destruct t; try reflexivity.
        - destruct v.
          cbn.
          rewrite !translate_bind, !interp_cfg2_bind.
          rewrite opt_correct.
          cbn.

          apply eutt_eq_bind.
          intro2; reflexivity.
        - destruct v; cbn.
          rewrite !translate_bind, !interp_cfg2_bind.
          rewrite opt_correct; apply eutt_eq_bind.
          intro2.
          rewrite !translate_bind, !interp_cfg2_bind.
          apply eutt_eq_bind.
          intro2.
          break_match_goal; try reflexivity.
        - destruct v.
          cbn.
          rewrite !translate_bind, !interp_cfg2_bind.
          rewrite opt_correct; apply eutt_eq_bind.
          intro2.
          rewrite !translate_bind, !interp_cfg2_bind.
          apply eutt_eq_bind.
          intro2.
          assert (EQbrs: (brs = endo brs)).
          { induction brs; cbn; try reflexivity. rewrite <- IHbrs. destruct a; cbn. unfold endo, Endo_id, Endo_tint_literal, id. reflexivity. }

          setoid_rewrite <- EQbrs.
          unfold endo, Endo_id.
          reflexivity.
      Qed.

      Lemma exp_optim_correct_code : forall varargs c g l,
          ⟦ c at varargs ⟧c2 g l ≈ ⟦ endo c at varargs ⟧c2 g l.
      Proof using opt_correct opt_respect_int.
        induction c as [| i c IH]; intros; [reflexivity |].
        unfold endo; simpl.
        rewrite 2denote_code_cons, 2interp_cfg2_bind.
        apply eutt_clo_bind with (UU := eq).
        destruct i as [[] ?]; apply exp_optim_correct_instr.
        intro2.
        apply IH.
      Qed.

      Lemma exp_optim_correct_phi : forall phi f g l,
          ℑ2 (translate exp_to_instr ⟦ phi ⟧Φ (f)) g l ≈ ℑ2 (translate exp_to_instr ⟦ endo phi ⟧Φ (f)) g l.
      Proof using opt_correct.
        intros [id []] f.
        induction args as [| [] args IH]; intros; [reflexivity |].
        cbn.
        do 2 break_match_goal.
        - unfold endo,Endo_id in Heqo0.
          break_match_hyp.
          + inv Heqo; inv Heqo0.
            rewrite 2translate_bind, 2interp_cfg2_bind.
            apply eutt_clo_bind with (UU := eq); [| intro2].
            rewrite opt_correct; reflexivity.
            reflexivity.
          +
            rewrite 2translate_bind, 2interp_cfg2_bind.
            apply eutt_clo_bind with (UU := eq); [rewrite opt_correct | intro2; reflexivity].
            assert (e1 = endo e0).
            { clear - Heqo Heqo0.
              revert Heqo Heqo0.
              induction args as [| [] args IH]; intros LU1 LU2; [inv LU1 |].
              cbn in *; unfold endo at 1 in LU2.
              break_match_hyp; auto.
              inv LU1; inv LU2; auto.
            }
            subst.
            reflexivity.
        - cbn in *; unfold endo, Endo_id at 1 in Heqo0.
          break_match_hyp; [inv Heqo0 |].
          exfalso; revert Heqo Heqo0.
          clear.
          induction args as [| [] args IH]; intros LU1 LU2; [inv LU1 |].
          cbn in *; unfold endo, Endo_id at 1 in LU2.
          break_match_hyp; auto.
          inv LU2.
        - cbn in *; unfold endo, Endo_id at 1 in Heqo0.
          break_match_hyp; [inv Heqo |].
          exfalso; revert Heqo Heqo0.
          clear.
          induction args as [| [] args IH]; intros LU1 LU2; [inv LU2 |].
          cbn in *; unfold endo, Endo_id at 1 in LU2.
          break_match_hyp; auto.
          inv LU1.
        - cbn in *; unfold endo, Endo_id at 1 in Heqo0.
          break_match_hyp; [inv Heqo |].
          reflexivity.
      Qed.

      Lemma exp_optim_correct_phis : forall phis f g l,
          ⟦ phis ⟧Φs2 f g l ≈ ⟦ endo phis ⟧Φs2 f g l.
      Proof using opt_correct.
        intros.
        unfold endo; simpl.
        cbn.
        rewrite !interp_cfg2_bind.
        apply eutt_clo_bind with (UU := eq); [| intro2].
        {
          revert g l.
          induction phis as [| phi phis IH]; intros; [reflexivity |].
          cbn.
          rewrite !interp_cfg2_bind.
          apply eutt_clo_bind with (UU := eq); [| intro2].
          apply exp_optim_correct_phi.
          rewrite !interp_cfg2_bind.
          apply eutt_clo_bind with (UU := eq); [| intro2; reflexivity].
          apply IH.
        }
        reflexivity.
      Qed.

      Arguments denote_block : simpl never.
      Lemma exp_optim_correct_block : forall varargs bk f g l,
          ⟦ bk ⟧b2 f varargs g l ≈ ⟦ endo bk ⟧b2 f varargs g l.
      Proof using opt_correct opt_respect_int.
        intros *.
        destruct bk; unfold endo, Endo_block; cbn.
        rewrite !denote_block_unfold.
        rewrite 2interp_cfg2_bind.
        apply eutt_clo_bind with (UU := eq).
        apply exp_optim_correct_phis.
        intro2.
        rewrite 2interp_cfg2_bind.
        apply eutt_clo_bind with (UU := eq).
        apply exp_optim_correct_code.
        intro2.
        apply exp_optim_correct_term.
      Qed.

      #[global] Instance eq_itree_interp_cfg2: forall {T : Type}, Proper (eq_itree eq ==> eq ==> eq ==> eq_itree eq) (@ℑ2 T).
      Proof using Type.
        repeat intro.
        unfold ℑ2.
        subst; rewrite H.
        reflexivity.
      Qed.

      Lemma interp_cfg2_ret_eq_itree:
        forall (R : Type) (g : global_env) (l : local_env) (x : R),
          ℑ2 (Ret x) g l ≅ Ret2 g l x.
      Proof using Type.
        intros.
        unfold interp_cfg2.
        rewrite interp_intrinsics_ret, interp_global_ret, interp_local_ret.
        reflexivity.
      Qed.

      Lemma interp_cfg2_bind_eq_itree :
        forall {R S} (t: itree instr_E R) (k: R -> itree instr_E S) g l,
          ℑ2 (t >>= k) g l ≅
             '(l',(g',x)) <- ℑ2 t g l ;; ℑ2 (k x) g' l'.
      Proof using Type.
        intros.
        unfold ℑ2.
        rewrite interp_intrinsics_bind, interp_global_bind, interp_local_bind.
        eapply eq_itree_clo_bind; [reflexivity | intro2; reflexivity].
      Qed.

      Lemma interp_cfg2_Tau :
        forall {R} (t: itree instr_E R) g l,
          ℑ2 (Tau t) g l ≅ Tau (ℑ2 t g l).
      Proof using Type.
        intros.
        unfold ℑ2.
        rewrite interp_intrinsics_Tau, interp_global_Tau, interp_local_Tau.
        reflexivity.
      Qed.

      Lemma denote_ocfg_proper :
        forall varargs bks1 bks2 fto g l,
          (forall b, find_block bks1 b = None <-> find_block bks2 b = None) ->
          (forall f g l b bk1 bk2,
              find_block bks1 b = Some bk1 ->
              find_block bks2 b = Some bk2 ->
              ⟦ bk1 ⟧b2 f varargs g l ≈ ⟦ bk2 ⟧b2 f varargs g l) ->
          ⟦ bks1 ⟧bs2 varargs fto g l ≈ ⟦ bks2 ⟧bs2 varargs fto g l.
      Proof using Type.
        intros * BIJ EQ.
        einit.
        destruct fto as [f to].
        revert g l f to.
        ecofix CIH.
        intros.
        destruct (find_block bks1 to) eqn:LU1.
        - destruct (find_block bks2 to) eqn:LU2; [| apply BIJ in LU2; rewrite LU2 in LU1; inv LU1].
          rewrite 2denote_ocfg_unfold_in_eq_itree; eauto.
          rewrite 2interp_cfg2_bind_eq_itree.
          ebind; econstructor.
          eapply EQ; eauto.
          intro2.
          destruct s.
          + rewrite 2interp_cfg2_Tau.
            estep.
          + rewrite interp_cfg2_ret_eq_itree.
            reflexivity.
        - pose proof LU1 as LU2; apply BIJ in LU2.
          rewrite 2denote_ocfg_unfold_not_in_eq_itree, interp_cfg2_ret_eq_itree; auto.
          reflexivity.
      Qed.

      Lemma exp_optim_correct :
        forall G varargs g l, ⟦ G ⟧cfg2 varargs g l ≈ ⟦ opt_exp_cfg G ⟧cfg2 varargs g l.
      Proof using opt_correct opt_respect_int.
        intros.
        unfold denote_cfg.
        cbn.
        rewrite !interp_cfg2_bind.
        eapply eutt_clo_bind with (UU := eq); [| intro2; reflexivity].
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

    End ExpOptimCorrect.

  End ExpOptim.

  (* Thinking about [Transforms/InstCombine/InstructionCombining.cpp] in LLVM *)

  (* // This pass guarantees that the following canonicalizations are performed on *)
  (* // the program: *)
  (* //    1. If a binary operator has a constant operand, it is moved to the RHS *)
  (* //    2. Bitwise operators with constant operands are always grouped so that *)
  (* //       shifts are performed first, then or's, then and's, then xor's. *)
  (* //    3. Compare instructions are converted from <,>,<=,>= to ==,!= if possible *)
  (* //    4. All cmp instructions on boolean values are replaced with logical ops *)
  (* //    5. add X, X is represented as (X*2) => (X << 1) *)
  (* //    6. Multiplies with a power-of-two constant argument are transformed into *)
  (* //       shifts. *)
  (* //   ... etc. *)

  (*  *)

  Import Monads.
  Import Monad.
  Import MonadNotation.
  Open Scope monad_scope.
  Open Scope monad.

  (* Define an appropriate notion of equivalence of expressions after interpretation at level 2 *)
  Definition eq_l2 (t:dtyp) (exp1 : exp dtyp)  (exp2 : exp dtyp) : Prop :=
    forall g l,   (eutt (fun '(g1, (l1, u1)) '(g2, (l2, u2)) => g1 = g2 /\ l1 = l2 /\ uvalue_eq u1 u2) (⟦ exp1 at t ⟧e2 g l) (⟦ exp2 at t ⟧e2 g l)).

  Infix "≐ [ t ]" := (@eq_l2 t) (at level 60).


  (* This hint database has a bunch of relevant monad laws that can be used for rewriting *)
  #[global] Hint Rewrite @interp_cfg2_bind @interp_cfg2_ret @bind_ret_l @bind_bind @translate_bind @map_ret @translate_ret: opt.

  (* This is the analog of the "norm" tactic from the Softare Foundations RIP tutorial. *)
  Ltac norm := autorewrite with opt.

  (* Induction on u *)
  Lemma uvalue_poison_cases : forall u, exists dt,
      (concretize u (DVALUE_Poison dt)) \/ (~ concretize u (DVALUE_Poison dt)).
  Proof. Admitted.

  Section MonadContext.

    Context (M: Type -> Type).
    Context {MM: Monad M}.
    Context {EQM : Monad.Eq1 M}.
    Context {EE : Eq1Equivalence M}.
    Context {Laws_M : MonadLawsE M}.
    Context {EQM_Laws_M  : MonadEq1Laws.Eq1_ret_inv M}.
    Context (D : dtyp -> M dvalue).
    Context (ERR_M : Type -> Type).
    Context (err : forall A : Type, ERR_M A -> M A).
    Context {M_ERR_M : Monad ERR_M}.
    Context {RAISE_ERR : RAISE_ERROR ERR_M}.
    Context (r_ub : RAISE_UB ERR_M).
    Context (r_oom : RAISE_OOM ERR_M).

    Existing Instance EQM.
    Existing Instance EQM_Laws_M.

      (* Induction on d  *)

(* Lemma
eq1 (bind f l (fun ys=> ret (DValue_Struct ys))) (ret xs) ->
        eq1 (bind f l (fun y => ret (Dvalue_Struct (a::ys)))) (ret (a::xs).
      *)
    Lemma uvalue_dvalue_to_uvalue_M : forall d,
       eq1 (concretize_uvalueM M D ERR_M err (dvalue_to_uvalue d)) (ret d).
    Proof using EE Laws_M.
      intros.
      induction d; simpl; try reflexivity.
      - rewrite map_monad_map.
        apply map_monad_g;
        induction fields; simpl; auto.
       + rewrite bind_ret_l.
         reflexivity.
       + rewrite H.
          rewrite bind_ret_l.
          rewrite bind_bind.
          setoid_rewrite bind_ret_l.
          apply map_monad_cons_ret.
          exact a.
          apply IHfields.
          intros. apply H. apply in_cons. assumption.
          apply in_eq.

       (* TODO: automate this *)
      -  rewrite map_monad_map;
          apply map_monad_g;
          induction fields; simpl.
        + rewrite bind_ret_l.
          reflexivity.
        + rewrite H.
          rewrite bind_ret_l.
          rewrite bind_bind.
          setoid_rewrite bind_ret_l.
          apply map_monad_cons_ret.
          exact a.
          apply IHfields.
          intros. apply H. apply in_cons. assumption.
          apply in_eq.


      - destruct Laws_M.
        rewrite map_monad_map;
          apply map_monad_g;
          induction elts; simpl.
        + rewrite bind_ret_l.
          reflexivity.
        + rewrite H.
          rewrite bind_ret_l.
          rewrite bind_bind.
          setoid_rewrite bind_ret_l.
          apply map_monad_cons_ret.
          exact a.
          apply IHelts.
          intros. apply H. apply in_cons. assumption.
          apply in_eq.


      - destruct Laws_M.
        rewrite map_monad_map;
          apply map_monad_g;
          induction elts; simpl.
        + rewrite bind_ret_l.
          reflexivity.
        + rewrite H.
          rewrite bind_ret_l.
          rewrite bind_bind.
          setoid_rewrite bind_ret_l.
          apply map_monad_cons_ret.
          exact a.
          apply IHelts.
          intros. apply H. apply in_cons. assumption.
          apply in_eq.
     Qed.

    End MonadContext.

  Lemma uvalue_dvalue_to_uvalue : forall (d : dvalue) d',
      concretize (dvalue_to_uvalue d) d' -> d = d'.
  Proof.
    (* clean attempt *)
    intros. induction d.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - unfold concretize in H.
      unfold concretize_u in H.
      rewrite concretize_uvalueM_equation in H.
      simpl in H. unfold eq1 in H.
      Admitted.


  Lemma add_zero : forall b1 b2 (e:exp dtyp),
    (OP_IBinop (Add b1 b2) (DTYPE_I 32) (EXP_Integer (0)%Z) e) ≐ [DTYPE_I 32] e.
  Proof.
    unfold eq_l2.
    intros.
    cbn. (* SAZ: Something about the new monad stuff broke the automation. *)
(*
    norm.
    cbn.
    bind_ret_r2.          (* <- note how this adds a "ret" on the right *)
    eapply eutt_clo_bind.  (* <- this is the key lemma!! *)
    reflexivity.
    intros.
    subst.
    destruct u2, p.
    norm.
    apply eutt_Ret.       (* <- this lets relate the returned values *)
    intuition.
    unfold uvalue_eq.
    split.
    -
    (* TODO: Need some facts about [refine_uvalue]. *) *)
  Abort.


  (** * Commutative expressions *)
  (*  *)


  Lemma add_commutative : forall b1 b2 τ e1 e2,
      ( OP_IBinop (Add b1 b2) τ e1 e2 )  ≐ [τ] ( OP_IBinop (Add b1 b2) τ e2 e1 ).
  Proof.
    unfold eq_l2.
    intros.
    cbn.
    norm.
    (* To prove this, we need some lemma about the purity of e1 and e2 - it should be the case
       that they evaluate to [Ret u1] and [Ret u2] so that we can make progress.  If it is _not_
       the case that they are pure, e.g., if [e1] divides by 0, then this commutativity result
       does not hold in general, and we'd have to add some assumptions about when it is OK. *)

  Admitted.

End EquivExpr.
