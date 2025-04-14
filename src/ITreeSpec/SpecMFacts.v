From Coq Require Export
     Morphisms
     Setoid
     Program.Equality
     Lists.List
     Logic.EqdepFacts
     Eqdep EqdepFacts
.

From EnTree Require Import
     Basics.HeterogeneousRelations
     Basics.QuantType
     Core.EnTreeDefinition
     Core.SubEvent
     Ref.EnTreeSpecDefinition
     Ref.EnTreeSpecFacts
     Ref.EnTreeSpecCombinatorFacts
     Ref.SpecM
     Eq.Eqit
     Ref.MRecSpec
.

Import SpecMNotations.
Local Open Scope entree_scope.

From Paco Require Import paco.

Section interp_mrec_spec_quantl.
Context (D E F: Type) `{EncodingType D} `{EncodingType E} `{EncodingType F}.
Context (body : forall d : D, entree_spec (D + E) (encodes d)).
Context (RPre : Rel E F ) (RPost : PostRel E F).
Context (R1 R2 : Type) (RR : Rel R1 R2).

Lemma interp_mrec_spec_forall A `{QuantType A} : 
  interp_mrec_spec body (forall_spec A) ≅ forall_spec A.
Proof.
  pstep. red. cbn. constructor. intros. left. pstep. constructor.
  auto.
Qed.

Lemma interp_mrec_spec_exists A `{QuantType A} : 
  interp_mrec_spec body (exists_spec A) ≅ exists_spec A.
Proof.
  pstep. red. cbn. constructor. intros. left. pstep. constructor.
  auto.
Qed.

Lemma interp_mrec_spec_assume P : 
  interp_mrec_spec body (assume_spec P) ≅ assume_spec P.
Proof.
  pstep. red. cbn. constructor. intros. left. pstep. constructor.
  auto.
Qed.

Lemma interp_mrec_spec_assert P : 
  interp_mrec_spec body (assert_spec P) ≅ assert_spec P.
Proof.
  pstep. red. cbn. constructor. intros. left. pstep. constructor.
  auto.
Qed.

Lemma padded_refines_assumel (P : Prop) (HP : P) k phi:
  padded_refines RPre RPost RR (k tt) phi ->
  padded_refines RPre RPost RR (EnTree.bind (assume_spec P) k) phi.
Proof.
  intros. setoid_rewrite bind_bind. apply padded_refines_forall_specl.
  eauto.
Qed.

Lemma padded_refines_assertl (P : Prop)  k phi:
  (P -> padded_refines RPre RPost RR (k tt) phi) ->
  padded_refines RPre RPost RR (EnTree.bind (assert_spec P) k) phi.
Proof.
  intros. setoid_rewrite bind_bind. apply padded_refines_exists_specl.
  eauto.
Qed.

Lemma interp_mrec_spec_forall_specl (A : Type) `{QuantType A} k phi (a : A) : 
  padded_refines RPre RPost RR (interp_mrec_spec body (k a)) phi ->
  padded_refines RPre RPost RR (interp_mrec_spec body (EnTree.bind (forall_spec A) k )) phi.
Proof.
  intros. setoid_rewrite interp_mrec_spec_bind.
  rewrite interp_mrec_spec_forall. apply padded_refines_forall_specl.
  eauto.
Qed.

Lemma interp_mrec_spec_exists_specl (A : Type) `{QuantType A} k phi : 
  (forall (a : A), padded_refines RPre RPost RR (interp_mrec_spec body (k a)) phi) ->
  padded_refines RPre RPost RR (interp_mrec_spec body (EnTree.bind (exists_spec A) k )) phi.
Proof.
  intros. setoid_rewrite interp_mrec_spec_bind.
  rewrite interp_mrec_spec_exists. apply padded_refines_exists_specl.
  eauto.
Qed.

Lemma interp_mrec_spec_assumel (P : Prop) (HP : P) k phi:
  padded_refines RPre RPost RR (interp_mrec_spec body (k tt)) phi ->
  padded_refines RPre RPost RR (interp_mrec_spec body (EnTree.bind (assume_spec P) k) ) phi.
Proof.
  intros. rewrite interp_mrec_spec_bind.
  rewrite interp_mrec_spec_assume.
  setoid_rewrite bind_bind. apply padded_refines_forall_specl.
  exists HP. rewrite bind_ret_l. auto.
Qed.

Lemma interp_mrec_spec_assertl (P : Prop) k phi : 
  (P -> padded_refines RPre RPost RR (interp_mrec_spec body (k tt)) phi) -> 
  padded_refines RPre RPost RR (interp_mrec_spec body (EnTree.bind (assert_spec P) k) ) phi.
Proof.
  intros. rewrite interp_mrec_spec_bind.
  rewrite interp_mrec_spec_assert. setoid_rewrite bind_bind.
  apply padded_refines_exists_specl. auto.
Qed.



End interp_mrec_spec_quantl.

Section interp_mrec_spec_quantr.

Context (D E F: Type) `{EncodingType D} `{EncodingType E} `{EncodingType F}.
Context (body : forall d : D, entree_spec (D + F) (encodes d)).
Context (RPre : Rel E F ) (RPost : PostRel E F).
Context (R1 R2 : Type) (RR : Rel R1 R2).


Lemma interp_mrec_spec_forall_specr (A : Type) `{QuantType A} k phi : 
  (forall (a : A), padded_refines RPre RPost RR phi (interp_mrec_spec body (k a))) ->
  padded_refines RPre RPost RR phi (interp_mrec_spec body (EnTree.bind (forall_spec A) k )).
Proof.
  intros. setoid_rewrite interp_mrec_spec_bind.
  rewrite interp_mrec_spec_forall. apply padded_refines_forall_specr.
  eauto.
Qed.

Lemma interp_mrec_spec_exists_specr (A : Type) `{QuantType A} k phi (a : A) : 
  (padded_refines RPre RPost RR phi (interp_mrec_spec body (k a))) ->
  padded_refines RPre RPost RR phi (interp_mrec_spec body (EnTree.bind (exists_spec A) k )).
Proof.
  intros. setoid_rewrite interp_mrec_spec_bind.
  rewrite interp_mrec_spec_exists. apply padded_refines_exists_specr.
  eauto.
Qed.

Lemma padded_refines_assumer (P : Prop) k phi :
  (P -> padded_refines RPre RPost RR phi (k tt)) ->
  padded_refines RPre RPost RR phi ((EnTree.bind (assume_spec P) k)).
Proof.
  intros. setoid_rewrite bind_bind.
  apply padded_refines_forall_specr. auto.
Qed.

Lemma padded_refines_assertr (P : Prop) (HP : P) k phi :
  padded_refines RPre RPost RR phi (k tt) ->
  padded_refines RPre RPost RR phi ((EnTree.bind (assert_spec P) k)).
Proof.
  intros. setoid_rewrite bind_bind.
  apply padded_refines_exists_specr. eauto.
Qed.

Lemma interp_mrec_spec_assumer (P : Prop) k phi :
  (P -> padded_refines RPre RPost RR phi (interp_mrec_spec body (k tt))) ->
  padded_refines RPre RPost RR phi (interp_mrec_spec body (EnTree.bind (assume_spec P) k)).
Proof.
  intros. rewrite interp_mrec_spec_bind.
  rewrite interp_mrec_spec_assume.
  setoid_rewrite bind_bind.
  apply padded_refines_forall_specr. auto.
Qed.

Lemma interp_mrec_spec_assertr (P : Prop) (HP : P) k phi :
  padded_refines RPre RPost RR phi (interp_mrec_spec body (k tt)) ->
  padded_refines RPre RPost RR phi (interp_mrec_spec body (EnTree.bind (assert_spec P) k)).
Proof.
  intros. rewrite interp_mrec_spec_bind.
  rewrite interp_mrec_spec_assert.
  setoid_rewrite bind_bind.
  apply padded_refines_exists_specr. exists HP.
  auto.
Qed.

End interp_mrec_spec_quantr.

(*
Lemma refines_liftStackS_proper:
  forall (E1 : EncType) (Γ1 : list RecFrame) (frame1 : RecFrame) (R1 : Type) (t1 t2 : SpecM E1 nil R1),
    refines eq PostRelEq eq t1 t2 ->
    refines eq PostRelEq eq (@liftStackS E1 (frame1 :: Γ1) R1 t1) (liftStackS R1 t2).
Proof.
  intros E1 Γ1 frame1 R1. unfold liftStackS. pcofix CIH. intros t1 t2 Ht12.
  unfold resumEntree. punfold Ht12. red in Ht12.
  pstep. red. hinduction Ht12 before r; intros.
  - constructor. auto.
  - constructor. pclearbot. right. eauto.
  - simpl. subst. unfold resum. unfold ReSum_nil_FunStack. destruct e2; constructor;
      auto; intros; pclearbot; right; eauto. 
    dependent destruction H. eapply CIH. 
    cbn in H0. cbn in b.
    match goal with |- refines _ _ _ (k1 ?a) _ => remember a as b' end.
    cbn in b'. specialize (H0 b' b' (PostRelEq_intro _ _)). pclearbot. auto.
    dependent destruction H.  eapply CIH. 
    cbn in H0. cbn in b.
    match goal with |- refines _ _ _ (k1 ?a) _ => remember a as b' end.
    cbn in b'. specialize (H0 b' b' (PostRelEq_intro _ _)). pclearbot. auto.
  - constructor. eauto.
  - constructor. eauto.
  - cbn. constructor. intros. eauto.
  - econstructor. eauto.
  - econstructor. eauto.
  - constructor. eauto.
Qed.
*)

Lemma pad_resumEntree_comm E1 E2 `{resret : ReSumRet E1 E2} R (t : entree E1 R) :
      resumEntree (Padded.pad t) ≅ Padded.pad (resumEntree t).
Proof.
  revert t. ginit. gcofix CIH.
  intros. unfold resumEntree at 2. unfold Padded.pad at 1.
  destruct (observe t).
  - setoid_rewrite Padded.pad_ret. rewrite resumEntree_Ret.
    gstep. constructor. auto.
  - setoid_rewrite Padded.pad_tau. rewrite resumEntree_Tau.
    gstep. constructor. gfinal. eauto.
  - setoid_rewrite Padded.pad_vis. rewrite resumEntree_Vis.
    gstep. constructor. intros. red. rewrite resumEntree_Tau.
    gstep. constructor. gfinal. eauto.
Qed.

(*
Lemma padded_refines_liftStackS_proper:
  forall (E1 : EncType) (Γ1 : list RecFrame) (frame1 : RecFrame) (R1 : Type) (t1 t2 : SpecM E1 nil R1),
    padded_refines eq PostRelEq eq t1 t2 ->
    padded_refines eq PostRelEq eq (@liftStackS E1 (frame1 :: Γ1) R1 t1) (liftStackS R1 t2).
Proof.
  unfold padded_refines.
  intros.
  eapply refines_eutt_padded_l with (t1 := liftStackS R1 (Padded.pad t1)); try apply Padded.pad_is_padded.
  setoid_rewrite pad_resumEntree_comm. reflexivity.
  eapply refines_eutt_padded_r with (t2 := liftStackS R1 (Padded.pad t2));
    try apply Padded.pad_is_padded.
  setoid_rewrite pad_resumEntree_comm. apply Padded.pad_is_padded.
  setoid_rewrite pad_resumEntree_comm. reflexivity.
  apply refines_liftStackS_proper. auto.
Qed.
*)

