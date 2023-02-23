(* begin hide *)
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
     Eq.Eqit
     InterpFacts
     TranslateFacts.

From Vellvm Require Import
     Utilities
     Syntax
     Semantics
     Theory
     Utils.PostConditions.

Import ITreeNotations.
Import SemNotations.

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
        assert (EQbrs: (brs = endo brs)).
        { induction brs; cbn; try reflexivity. rewrite <- IHbrs. destruct a; cbn. unfold endo, Endo_id, Endo_tint_literal, id. reflexivity. }
        assert (EQ1:
                  (map_monad
                (fun '(TInt_Literal sz x0, id) =>
                 {|
                 EitherMonad.unEitherT := match EitherMonad.unEitherT (coerce_integer_to_int sz x0) with
                                          | inl v => inl v
                                          | inr (inl x1) => inr (inl x1)
                                          | inr (inr x1) => inr (inr (x1, id))
                                          end |}) brs) =
                  (map_monad
                (fun '(TInt_Literal sz x0, id) =>
                 {|
                 EitherMonad.unEitherT := match EitherMonad.unEitherT (coerce_integer_to_int sz x0) with
                                          | inl v => inl v
                                          | inr (inl x1) => inr (inl x1)
                                          | inr (inr x1) => inr (inr (x1, id))
                                          end |}) (endo brs))).
        { rewrite <- EQbrs. reflexivity. }
        assert (EQ:
                  ℑ3
    (translate exp_to_instr
       (switches <-
        lift_undef_or_err (fun x : list (dvalue * block_id) => Ret x)
          (map_monad
             (fun '(TInt_Literal sz x, id) =>
              {|
              EitherMonad.unEitherT := match EitherMonad.unEitherT (coerce_integer_to_int sz x) with
                                       | inl v => inl v
                                       | inr (inl x0) => inr (inl x0)
                                       | inr (inr x0) => inr (inr (x0, id))
                                       end |}) brs);; lift_err (fun b : block_id => Ret (@inl block_id uvalue b)) (select_switch d0 default_dest switches)))
    g1 l1 m1
  ≈ ℑ3
      (translate exp_to_instr
         (switches <-
          lift_undef_or_err (fun x : list (dvalue * block_id) => Ret x)
            (map_monad
               (fun '(TInt_Literal sz x, id) =>
                {|
                EitherMonad.unEitherT := match EitherMonad.unEitherT (coerce_integer_to_int sz x) with
                                         | inl v => inl v
                                         | inr (inl x0) => inr (inl x0)
                                         | inr (inr x0) => inr (inr (x0, id))
                                         end |}) (endo brs));;
          lift_err (fun b : block_id => Ret (inl b)) (select_switch d0 (endo default_dest) switches))) g1 l1 m1).
        { 
          rewrite !translate_bind,!interp_cfg3_bind; apply eutt_clo_bind with (UU := eq); [| intro3; reflexivity].
          setoid_rewrite EQ1. reflexivity. }
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
      induction args as [| [] args IH]; intros; [reflexivity |].
      cbn.
      do 2 break_match_goal.
      - unfold endo,Endo_id in Heqo0.
        break_match_hyp.
        + inv Heqo; inv Heqo0.
          rewrite 2translate_bind, 2interp_cfg3_bind.
          apply eutt_clo_bind with (UU := eq); [| intro3].
          rewrite opt_correct; reflexivity.
          reflexivity.
        + 
          rewrite 2translate_bind, 2interp_cfg3_bind.
          apply eutt_clo_bind with (UU := eq); [rewrite opt_correct | intro3; reflexivity].
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

    #[global] Instance eq_itree_interp_cfg3: forall {T : Type}, Proper (eq_itree eq ==> eq ==> eq ==> eq ==> eq_itree eq) (@ℑ3 T).
    Proof.
      repeat intro.
      unfold ℑ3.
      subst; rewrite H.
      reflexivity.
    Qed.

    Lemma interp_cfg3_ret_eq_itree:
      forall (R : Type) (g : global_env) (l : local_env) (m : memory_stack) (x : R),
        ℑ3 (Ret x) g l m ≅ Ret3 g l m x.
    Proof.
      intros.
      unfold interp_cfg3.
      rewrite interp_intrinsics_ret, interp_global_ret, interp_local_ret, interp_memory_ret.
      reflexivity.
    Qed.

    Lemma interp_cfg3_bind_eq_itree :
      forall {R S} (t: itree instr_E R) (k: R -> itree instr_E S) g l m,
        ℑ3 (t >>= k) g l m ≅
           '(m',(l',(g',x))) <- ℑ3 t g l m ;; ℑ3 (k x) g' l' m'.
    Proof.
      intros.
      unfold ℑ3.
      rewrite interp_intrinsics_bind, interp_global_bind, interp_local_bind, interp_memory_bind.
      eapply eq_itree_clo_bind; [reflexivity | intro3; reflexivity].
    Qed.

    Lemma interp_cfg3_Tau :
      forall {R} (t: itree instr_E R) g l m,
        ℑ3 (Tau t) g l m ≅ Tau (ℑ3 t g l m).
    Proof.
      intros.
      unfold ℑ3.
      rewrite interp_intrinsics_Tau, interp_global_Tau, interp_local_Tau, interp_memory_Tau.
      reflexivity.
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
      einit.
      destruct fto as [f to].
      revert g l m f to.
      ecofix CIH.
      intros.
      destruct (find_block bks1 to) eqn:LU1.
      - destruct (find_block bks2 to) eqn:LU2; [| apply BIJ in LU2; rewrite LU2 in LU1; inv LU1].
        rewrite 2denote_ocfg_unfold_in_eq_itree; eauto.
        rewrite 2interp_cfg3_bind_eq_itree.
        ebind; econstructor.
        eapply EQ; eauto.
        intro3.
        destruct s.
        + rewrite 2interp_cfg3_Tau.
          estep.
        + rewrite interp_cfg3_ret_eq_itree.
          reflexivity.
      - pose proof LU1 as LU2; apply BIJ in LU2.
        rewrite 2denote_ocfg_unfold_not_in_eq_itree, interp_cfg3_ret_eq_itree; auto.
        reflexivity.
    Qed.

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

  End ExpOptimCorrect.

End ExpOptim.

(* Thinking about [Transforms/InstCombine/InstructionCombining.cpp] in LLVM

// This pass guarantees that the following canonicalizations are performed on
// the program:
//    1. If a binary operator has a constant operand, it is moved to the RHS
//    2. Bitwise operators with constant operands are always grouped so that
//       shifts are performed first, then or's, then and's, then xor's.
//    3. Compare instructions are converted from <,>,<=,>= to ==,!= if possible
//    4. All cmp instructions on boolean values are replaced with logical ops
//    5. add X, X is represented as (X*2) => (X << 1)
//    6. Multiplies with a power-of-two constant argument are transformed into
//       shifts.
//   ... etc.

 *)

(** * Associative expressions
 *)

Lemma add_associate : forall b1 b2 τ e1 e2,
    ⟦ OP_IBinop (Add b1 b2) τ e1 e2 ⟧e ≈ ⟦ OP_IBinop (Add b1 b2) τ e2 e1 ⟧e.
Proof.
  intros.
  cbn.
Admitted.  

