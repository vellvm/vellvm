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
     Syntax.CFG
     Syntax.AstLib
     Syntax.DynamicTypes
     Semantics.LLVMEvents
     Semantics.InterpretationStack
     Semantics.TopLevel
     Theory.DenotationTheory
     Transformations.BlockFusion.

Import SemNotations.
Import ITreeNotations.

(** * Elimination of unreachable blocks
    A block that admits no predecessor can be eliminated.

    YZ TODO: prove a VIR reasoning principle for such proofs that do not require to build the simulation manually.
 *)
Lemma remove_predecessorless_correct :
  forall (bks : ocfg dtyp) dead,
    predecessors dead bks = [] ->
    forall f to, to <> dead ->
          ⟦ bks ⟧bs (f,to) ≈ ⟦ bks ∖ dead ⟧bs (f,to).
Proof.
  intros * DEAD.
  einit; ecofix CIH.
  intros f to INEQ.
  rewrite 2denote_ocfg_unfold_eq_itree.
  rewrite remove_block_find_block_ineq; auto.
  break_match_goal; [| reflexivity].
  ebind; econstructor.
  - (* YZ TODO: exploiting the strong version of HasPost should be painless, maybe the default. *)
    pose proof denote_bk_exits_in_outputs b f.
    apply has_post_post_strong in H.
    apply H.
  - intros ? ? [<- SUCC]. 
    destruct u1; [| reflexivity].
    estep; ebase; right.
    apply CIH.
    cbn in SUCC.
    clear - Heqo SUCC DEAD.
    pose proof find_block_has_id _ _ Heqo; subst.
    eapply successor_predecessor in SUCC; eauto.
    intros ->; rewrite DEAD in SUCC; inv SUCC.
Qed.


