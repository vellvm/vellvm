From Stdlib Require Export
  Morphisms
  Setoid
  Program.Equality
  Lists.List
  Logic.EqdepFacts
  Eqdep EqdepFacts.

Require Import  ExtLib.Structures.Monad.

From ITree Require Import
  Basics.HeterogeneousRelations
  Core.ITreeDefinition
  Eq.Eqit.

From ITreeSpec Require Import
  ITreeSpecDefinition
  ITreeSpecFacts
  ITreeSpecCombinatorFacts
  MRecSpec
  RecSpecFix.

Open Scope entree_scope.
Import Monad.
Import MonadNotation.
Local Open Scope monad_scope.
From Paco Require Import paco.
Fixpoint trepeat {E R: Type} `{EncodingType E} (n : nat) (t : entree E R) :=
  match n with
  | 0 => ret tt
  | S n => t;; trepeat n t end.

Section total_spec_fix.
Context {A B : Type} `{QuantType A} `{QuantType B}.
Context {E : Type} `{EncodingType E}.

Context (Pre : A -> Prop) (Post : A -> B -> Prop).


Definition total_spec' (a : A) : entree_spec E B :=
  assume_spec (Pre a);;
  b <- exists_spec B;;
  assert_spec (Post a b);;
  ret b.
  

Context (Rdec : Rel A A).
Context (Hwf : well_founded Rdec).

Definition total_spec_fix : A -> entree_spec E B :=
  rec_fix_spec 
    (fun rec a =>
       assume_spec (Pre a);;
       n <- exists_spec nat;;
       trepeat n (
         a' <- exists_spec A;;
         assert_spec (Pre a' /\ Rdec a' a);;
         rec a');;
       b <- exists_spec B;;
       assert_spec (Post a b);;
       ret b
    ).
Theorem total_spec_fix_refines_total_spec' (a : A) : strict_refines (total_spec_fix a) (total_spec' a).
Proof.
  revert a. eapply well_founded_ind; eauto.
  intros a Hind. unfold total_spec_fix, total_spec'.
  quantr. intros. quantl. auto.
  match goal with |- padded_refines eq PostRelEq eq (interp_mrec_spec ?b _ ) _ => set b as body end.
  quantl. intros n. induction n.
  - cbn. quantl. intros b. quantr. exists b. quantl. intros. quantr. auto.
    apply padded_refines_ret. auto.
  - cbn. do 2 rewrite interp_mrec_spec_bind. repeat apply padded_refines_bind_bind_l.
    match goal with |- padded_refines eq PostRelEq eq _ ?t => assert (t ≅ Ret tt;; t) end.
    cbn. 
    (* some rewriting fails here for some reason *)
    { pstep. red. cbn. rewrite itree_eta' at 1. rewrite itree_eta'. pstep_reverse.
      apply Reflexive_eqit. auto. }
    rewrite H3. eapply padded_refines_bind with (RR := fun _ _ => True).
    + quantl. intros. quantl. intros [Hpre Hdec].
      eapply padded_refines_weaken_l with (phi2 := total_spec' a0;; Ret tt).
      * cbn. apply padded_refines_bind_bind_l.
        quantl. auto. apply padded_refines_bind_bind_l.
        quantl. intros. apply padded_refines_bind_bind_l. quantl.
        intros. apply padded_refines_ret. auto.
      * specialize (Hind a0 Hdec).
        unfold call_spec. setoid_rewrite interp_mrec_spec_inl. rewrite tau_eutt.
        rewrite interp_mrec_spec_bind. eapply padded_refines_bind; intros; try apply padded_refines_ret; eauto.
    + intros b0 [] _. eapply padded_refines_weaken_l; try eapply IHn.
      setoid_rewrite interp_mrec_spec_bind. 
      eapply padded_refines_bind; intros; subst; try reflexivity.
      quantl. intros. cbn.  eapply interp_mrec_spec_exists_specr. Unshelve. 2: eauto. 
      quantl. intros. subst. quantr. auto. apply padded_refines_ret. auto.
Qed.

End total_spec_fix.
