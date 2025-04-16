From Stdlib Require Import
     Program
     Setoid
     Morphisms
     Relations.

From ITree Require Import
     Basics.Basics
     Basics.Utils
     Basics.HeterogeneousRelations
     Core.ITreeDefinition
     Eq.EqAxiom
     ITree
     Eqit.

From ITreeSpec Require Import
     Padded
     ITreeSpecDefinition
     MRecSpec
     ITreeSpecFacts
     Relations.

From Paco Require Import paco.
Axiom bisimulation_is_eq : forall (E : Type -> Type) (R: Type)
  (t1 t2 : itree E R), eq_itree eq t1 t2 -> t1 = t2.

Ltac use_simpobs := repeat match goal with
                           | H : RetF _ = observe ?t |- _ => apply simpobs in H
                           | H : TauF _ = observe ?t |- _ => apply simpobs in H
                           | H : VisF _ _ = observe ?t |- _ => apply simpobs in H
                           | H : observe ?t = RetF _ |- _ => apply simpobs in H
                           | H : observe ?t = TauF _ |- _ => apply simpobs in H
                           | H : observe ?t = VisF _ _ |- _ => apply simpobs in H
                           end.

Global Instance eq_itree_refines_Proper1 {E1 E2 R1 R2 RR}
  {RPre : prerel E1 E2} {RPost : postrel E1 E2} {r} : 
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
    (@refines_ E1 E2 R1 R2 RPre RPost RR (upaco2 (refines_ RPre RPost RR) r)).
Proof.
  repeat intro. apply bisimulation_is_eq in H. apply bisimulation_is_eq in H0.
  subst. auto.
Qed.

Global Instance eq_itree_refines_Proper2 {E1 E2 R1 R2 RR}
  {RPre : prerel E1 E2} {RPost : postrel E1 E2} {r} : 
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
    (paco2 (@refines_ E1 E2 R1 R2 RPre RPost RR) r).
Proof.
  repeat intro. apply bisimulation_is_eq in H. apply bisimulation_is_eq in H0.
  subst. auto.
Qed.

Theorem refines_ret (E1 E2 : Type -> Type) (R1 R2 : Type)
        (RPre : prerel E1 E2) (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop) r1 r2 : 
  RR r1 r2 -> refines RPre RPost RR (Ret r1) (Ret r2).
Proof.
  intros. pstep. constructor. auto.
Qed.

Theorem padded_refines_ret (E1 E2 : Type -> Type) (R1 R2 : Type)
        (RPre : prerel E1 E2) (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop) r1 r2 : 
  RR r1 r2 -> padded_refines RPre RPost RR (Ret r1) (Ret r2).
Proof.
  intros. red. pstep. red. cbn. constructor. auto.
Qed.

Theorem refines_vis (E1 E2 : Type -> Type) (R1 R2 : Type)
  (RPre : prerel E1 E2) (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop) X Y (e1 : E1 X) (e2 : E2 Y) 
  (k1 : X -> itree_spec E1 R1) (k2 : Y -> itree_spec E2 R2) :
  RPre _ _ e1 e2 -> (forall a b, RPost _ _ e1 a e2 b -> refines RPre RPost RR (k1 a) (k2 b)) ->
  refines RPre RPost RR (Vis (Spec_vis e1) k1) (Vis (Spec_vis e2) k2).
Proof.
  intros. pstep. constructor. auto. left. apply H0. auto.
Qed.

Theorem padded_refines_vis (E1 E2 : Type -> Type) (R1 R2 : Type)
  (RPre : prerel E1 E2) (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop) X Y (e1 : E1 X) (e2 : E2 Y) 
  (k1 : X -> itree_spec E1 R1) (k2 : Y -> itree_spec E2 R2) :
  RPre _ _ e1 e2 -> (forall a b, RPost _ _ e1 a e2 b -> padded_refines RPre RPost RR (k1 a) (k2 b)) ->
  padded_refines RPre RPost RR (Vis (Spec_vis e1) k1) (Vis (Spec_vis e2) k2).
Proof.
  intros. pstep. red. cbn. constructor. auto. left. pstep. constructor. left. apply H0. auto.
Qed.


Theorem refines_bind (E1 E2 : Type -> Type) (R1 R2 S1 S2: Type)
        (RPre : prerel E1 E2) (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop) (RS : S1 -> S2 -> Prop) 
        (t1 : itree_spec E1 R1) (t2 : itree_spec E2 R2)
        (k1 : R1 -> itree_spec E1 S1) (k2 : R2 -> itree_spec E2 S2) :
  refines RPre RPost RR t1 t2 ->
  (forall r1 r2, RR r1 r2 -> refines RPre RPost RS (k1 r1) (k2 r2)) ->
  refines RPre RPost RS (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  revert t1 t2. pcofix CIH. intros t1 t2 Ht12 Hk.
  punfold Ht12. red in Ht12. remember (observe t1) as ot1. remember (observe t2) as ot2.
  hinduction Ht12 before r; intros; use_simpobs.
  - rewrite Heqot1, Heqot2. repeat rewrite bind_ret_l. eapply paco2_mon; try eapply Hk; eauto.
    intros. contradiction.
  - rewrite Heqot1, Heqot2. repeat rewrite bind_tau. pstep. constructor. right.
    pclearbot. eapply CIH; eauto.
  - rewrite Heqot1, Heqot2. repeat rewrite bind_vis. pstep. constructor. auto. intros. right.
    eapply H0 in H1. pclearbot. eapply CIH; eauto.
  - rewrite Heqot1. rewrite bind_tau. pstep. constructor. pstep_reverse.
  - rewrite Heqot2. rewrite bind_tau. pstep. constructor. pstep_reverse.
  - rewrite Heqot2. rewrite bind_vis. pstep. constructor. intros. pstep_reverse.
  - rewrite Heqot2. rewrite bind_vis. pstep. econstructor. intros. pstep_reverse.
  - rewrite Heqot1. rewrite bind_vis. pstep. econstructor. intros. pstep_reverse.
  - rewrite Heqot1. rewrite bind_vis. pstep. constructor. intros. pstep_reverse.
Qed.

Theorem padded_refines_bind (E1 E2 : Type -> Type) (R1 R2 S1 S2: Type)
        (RPre : prerel E1 E2) (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop) (RS : S1 -> S2 -> Prop) 
        (t1 : itree_spec E1 R1) (t2 : itree_spec E2 R2)
        (k1 : R1 -> itree_spec E1 S1) (k2 : R2 -> itree_spec E2 S2) :
  padded_refines RPre RPost RR t1 t2 ->
  (forall r1 r2, RR r1 r2 -> padded_refines RPre RPost RS (k1 r1) (k2 r2)) ->
  padded_refines RPre RPost RS (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros. unfold padded_refines. repeat rewrite pad_bind.
  eapply refines_bind; eauto.
Qed.

Global Instance padded_refines_bind_proper {E S R} :
  Proper (strict_refines ==> pointwise_relation S strict_refines ==>
            @strict_refines E R) ITree.bind.
Proof.
  repeat intro. eapply padded_refines_bind; intros; subst; eauto. subst. apply H0.
Qed.


Lemma padded_refines_forall_specr {E1 E2} 
      (A : Type) R1 R2  RPre RPost RR
      (k : A -> itree_spec E2 R1) (t : itree_spec E1 R2) :
  (forall a : A, padded_refines RPre RPost RR t (k a)) ->
  padded_refines RPre RPost RR t (ITree.bind (forall_spec A) k).
Proof.
  intros. 
  assert (t≈  ITree.bind (Ret tt) (fun _ => t)). rewrite bind_ret_l. reflexivity.
  rewrite H0. eapply padded_refines_bind with (RR := fun _ _ => True); auto.
  unfold padded_refines. pstep. red. cbn. constructor.
  intros. repeat constructor.
  cbn.
  constructor; auto.
Qed.

Lemma padded_refines_forall_specl {E1 E2} 
      (A : Type) R1 R2  RPre RPost RR
      (k : A -> itree_spec E2 R1) (t : itree_spec E1 R2) :
  (exists a : A, padded_refines RPre RPost RR (k a) t) ->
  padded_refines RPre RPost RR (ITree.bind (forall_spec A) k) t.
Proof.
  intros. destruct H as [a Ha]. 
  assert (t≈  ITree.bind (Ret tt) (fun _ => t)). rewrite bind_ret_l. reflexivity.
  rewrite H.
  apply padded_refines_bind with (RR := fun b _ => b = a); intros; subst; auto.
  red. pstep. red. cbn. repeat (cbn; econstructor).
Qed.

Lemma padded_refines_exists_specr {E1 E2} 
      (A : Type) R1 R2  RPre RPost RR
      (k : A -> itree_spec E2 R1) (t : itree_spec E1 R2) :
  (exists a : A, padded_refines RPre RPost RR t (k a)) ->
  padded_refines RPre RPost RR t (ITree.bind (exists_spec A) k).
Proof.
  intros. destruct H as [a Ha]. 
  assert (t≈  ITree.bind (Ret tt) (fun _ => t)). rewrite bind_ret_l. reflexivity.
  rewrite H.
  apply padded_refines_bind with (RR := fun _ b => b = a); intros; subst; auto.
  red. pstep. red. cbn. repeat (cbn; econstructor).
Qed.

Lemma padded_refines_exists_specl {E1 E2} 
      (A : Type) R1 R2  RPre RPost RR
      (k : A -> itree_spec E2 R1) (t : itree_spec E1 R2) :
  (forall a : A, padded_refines RPre RPost RR (k a) t) ->
  padded_refines RPre RPost RR (ITree.bind (exists_spec A) k) t.
Proof.
  intros. 
  assert (t≈  ITree.bind (Ret tt) (fun _ => t)). rewrite bind_ret_l. reflexivity.
  rewrite H0. eapply padded_refines_bind with (RR := fun _ _ => True); auto.
  unfold padded_refines. pstep. red. cbn. constructor.
  intros. repeat (cbn; constructor).
Qed.


Lemma refines_iter_aux:
  forall (E2 : Type -> Type) (S2 : Type) (E1 : Type -> Type) (S1 R1 R2 : Type) (RPre : prerel E1 E2)
    (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop) (RS : S1 -> S2 -> Prop) (body1 : R1 -> itree_spec E1 (R1 + S1))
    (body2 : R2 -> itree_spec E2 (R2 + S2)) (t1 : itree_spec E1 (R1 + S1)) (t2 : itree_spec E2 (R2 + S2))
    (r : (itree_spec E1 S1) -> (itree_spec E2 S2) -> Prop),
    paco2 (refines_ RPre RPost (sum_rel RR RS)) bot2 t1 t2 ->
    (forall (r2 : R2) (r1 : R1), RR r1 r2 -> r (ITree.iter body1 r1) (ITree.iter body2 r2)) ->
    paco2 (refines_ RPre RPost RS) r
          (ITree.bind t1 (fun rs : R1 + S1 => match rs with
                                            | inl r0 => Tau (ITree.iter body1 r0)
                                            | inr s => Ret s
                                            end))
          (ITree.bind t2 (fun rs : R2 + S2 => match rs with
                                            | inl r0 => Tau (ITree.iter body2 r0)
                                            | inr s => Ret s
                                            end)).
Proof.
  intros E2 S2 E1 S1 R1 R2 RPre RPost RR RS body1 body2 t1 t2 r.
  revert t1 t2. pcofix CIH. intros t1 t2 Ht12 CIH1.
  punfold Ht12. red in Ht12. remember (observe t1) as ot1. remember (observe t2) as ot2.
  hinduction Ht12 before r; intros; use_simpobs; try rewrite Heqot1; try rewrite Heqot2.
  - repeat rewrite bind_ret_l.
    destruct H.
    + pstep. constructor. eauto.
    + pstep. constructor. auto.
  - repeat rewrite bind_tau. pstep. constructor. pclearbot. eauto.
  - repeat  rewrite bind_vis. pstep. constructor. pclearbot. auto.
    intros. apply H0 in H1. pclearbot. eauto.
  - rewrite bind_tau. pstep. constructor. pstep_reverse.
  - rewrite bind_tau. pstep. constructor. pstep_reverse.
  - rewrite bind_vis. pstep. econstructor. intros. pstep_reverse.
  - rewrite bind_vis. pstep. econstructor. intros. pstep_reverse.
  - rewrite bind_vis. pstep. econstructor. intros. pstep_reverse.
  - rewrite bind_vis. pstep. econstructor. intros. pstep_reverse.
Qed.

Theorem refines_iter (E1 E2 : Type -> Type) (R1 R2 S1 S2: Type)
        (RPre : prerel E1 E2) (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop) (RS : S1 -> S2 -> Prop) 
        (body1 : R1 -> itree_spec E1 (R1 + S1)) (body2 : R2 -> itree_spec E2 (R2 + S2)) r1 r2:
  (forall r1 r2, RR r1 r2 -> refines RPre RPost (sum_rel RR RS) (body1 r1) (body2 r2) ) ->
  RR r1 r2 ->
  refines RPre RPost RS (ITree.iter body1 r1) (ITree.iter body2 r2).
Proof.
  intros Hbody. revert r2 r1.
  pcofix CIH. intros.
  rewrite unfold_iter. rewrite unfold_iter. specialize (Hbody r1 r2 H0). punfold Hbody.
  red in Hbody. remember (observe (body1 r1)) as ob1. remember (observe (body2 r2)) as ob2.
  hinduction Hbody before r; intros; use_simpobs; try rewrite Heqob1; try rewrite Heqob2.
  - repeat rewrite bind_ret_l. destruct H.
    + pstep. constructor. eauto.
    + pstep. constructor. auto.
  - repeat rewrite bind_tau. pstep. constructor.  pclearbot. left.
    eapply refines_iter_aux; eauto.
  - repeat rewrite bind_vis. pstep. constructor. auto. pclearbot. intros * H5. left.
    apply H0 in H5. pclearbot.
    eapply refines_iter_aux; eauto.
  - rewrite bind_tau. pstep. constructor. pstep_reverse.
    eapply refines_iter_aux; eauto. pstep. red. rewrite <- Heqob2.
    eauto.
  - rewrite bind_tau. pstep. constructor. pstep_reverse.
    eapply refines_iter_aux; eauto. pstep. red.
    rewrite <- Heqob1. auto.
  - rewrite bind_vis. pstep. constructor. intros. pstep_reverse.
    eapply refines_iter_aux; eauto. pstep. red. rewrite <- Heqob1.
    auto.
  - rewrite bind_vis. pstep. econstructor. pstep_reverse. 
    eapply refines_iter_aux; eauto. pstep. red. rewrite <- Heqob1.
    eauto.
  - rewrite bind_vis. pstep. econstructor. pstep_reverse. 
    eapply refines_iter_aux; eauto. pstep. red. rewrite <- Heqob2.
    eauto.
  - rewrite bind_vis. pstep. constructor. intros. pstep_reverse.
    eapply refines_iter_aux; eauto. pstep. red. rewrite <- Heqob2.
    auto.
Qed.

Theorem padded_refines_iter (E1 E2 : Type -> Type) (R1 R2 S1 S2: Type)
        (RPre : prerel E1 E2) (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop) (RS : S1 -> S2 -> Prop) 
        (body1 : R1 -> itree_spec E1 (R1 + S1)) (body2 : R2 -> itree_spec E2 (R2 + S2)) r1 r2:
  (forall r1 r2, RR r1 r2 -> padded_refines RPre RPost (sum_rel RR RS) (body1 r1) (body2 r2) ) ->
  RR r1 r2 ->
  padded_refines RPre RPost RS (ITree.iter body1 r1) (ITree.iter body2 r2).
Proof.
  unfold padded_refines. intros.
  repeat rewrite pad_iter. eapply refines_iter; eauto.
Qed.

Section refines_mrec.
Context (D1 D2 E1 E2 : Type -> Type).
Context (bodies1 : forall X, itree_spec (D1 +' E1) X).
Context (bodies2 : forall Y, itree_spec (D2 +' E2) Y).
Context (RPreInv : prerel D1 D2) (RPre : prerel E1 E2)
  (RPostInv : postrel D1 D2) (RPost : postrel E1 E2).
Context
  (Hbodies : forall {X Y} (d1 : D1 X) (d2 : D2 Y),
      RPreInv _ _ d1 d2 -> 
      refines (SumPreRel RPreInv RPre) (SumPostRel RPostInv RPost) (fun x y => RPostInv _ _ d1 x d2 y)
        (bodies1 _) (bodies2 _)).

Theorem refines_interp_mrec_spec (R1 R2 : Type) (RR : R1 -> R2 -> Prop) : forall t1 t2, 
    refines (SumPreRel RPreInv RPre) (SumPostRel RPostInv RPost) RR t1 t2 ->
    refines RPre RPost RR (interp_mrec_spec bodies1 t1) (interp_mrec_spec bodies2 t2).
Proof.
  pcofix CIH. intros t1 t2 Ht12. unfold interp_mrec_spec.
  punfold Ht12. red in Ht12. pstep. red. hinduction Ht12 before r; intros; pclearbot;
    try (cbn; econstructor; eauto; fail).
  destruct H.
  - cbn. constructor. right. eapply CIH.
    eapply refines_bind; eauto. intros. pclearbot.
    assert (SumPostRel RPostInv RPost _ _ (inl1 e1) r1 (inl1 e2) r2). constructor. auto.
    apply H0 in H2. pclearbot. auto.
  - cbn. constructor. auto. right.
    assert (SumPostRel RPostInv RPost _ _ (inr1 d1) a (inr1 d2) b).
    constructor. auto. eapply H0 in H2. pclearbot. eauto.
Qed.

Theorem refines_mrec_spec {X Y} (d1 : D1 X) (d2 : D2 Y) :
  RPreInv _ _ d1 d2 -> 
  refines RPre RPost (fun x y => RPostInv _ _ d1 x d2 y) (mrec_spec bodies1 _) (mrec_spec bodies2 _).
Proof.
  intros. apply refines_interp_mrec_spec. auto.
Qed.

End refines_mrec.

Theorem interp_mrec_spec_tau 
        D E R 
        (bodies : forall X,  itree_spec (D +' E) X) :
        forall (t : itree_spec (D +' E) R), (interp_mrec_spec bodies (Tau t) ≅ Tau (interp_mrec_spec bodies t)).
Proof.
  intros. pstep. red. cbn. constructor. left. apply Reflexive_eqit.
  auto.
Qed.

Theorem padded_interp_mrec_spec_eutt D E R 
        (bodies : forall X,  itree_spec (D +' E) X) :
  forall t1 t2 : itree_spec (D +' E) R,
    t1 ≈ t2 ->
    pad (interp_mrec_spec bodies t1)
        ≈ interp_mrec_spec
        (fun  d =>
           pad (bodies d)) t2.
Proof.
  ginit. gcofix CIH. intros t1 t2 Ht12.
  punfold Ht12. red in Ht12.
  unfold interp_mrec_spec.
  hinduction Ht12 before r; intros; use_simpobs.
  - gstep. red. cbn. constructor. auto.
  - gstep. red. cbn. constructor. gfinal. pclearbot. eauto.
  - gstep. red. cbn. destruct e; try destruct e; cbn.
    + constructor. gfinal. left. eapply CIH. pclearbot. eapply eqit_bind; eauto.
      apply pad_eutt.
    + constructor. unfold id at 1. setoid_rewrite tau_euttge. gfinal. pclearbot.
      left. eapply CIH. cbn in *. apply REL.
    + constructor. unfold id at 1. setoid_rewrite tau_euttge. gfinal.
      pclearbot. left. cbn in *. eapply CIH. apply REL.
    + constructor. unfold id at 1. setoid_rewrite tau_euttge. gfinal.
      pclearbot. left. cbn in *. eapply CIH. apply REL.
  - setoid_rewrite interp_mrec_spec_tau. rewrite pad_tau. rewrite tau_euttge.
    auto.
  - setoid_rewrite interp_mrec_spec_tau. rewrite tau_euttge. auto.
Qed.

Theorem padded_interp_mrec_spec D E R 
        (bodies : forall X,  itree_spec (D +' E) X) (t : itree_spec (D +' E) R) :
  pad (interp_mrec_spec bodies t) ≈ interp_mrec_spec (fun d => pad (bodies d)) (pad t).
Proof.
  apply padded_interp_mrec_spec_eutt. apply pad_eutt.
Qed.

Global Instance padded_eq_itree_proper_r {E R} r : Proper (@eq_itree E _ R eq ==> flip impl) (paco1 (padded_) r).
Proof.
  repeat intro. eapply bisimulation_is_eq in H. subst. auto.
Qed.

Theorem padded_bind {E : Type -> Type} R S (k : R -> itree E S) : 
  forall (t : itree E R), padded t -> (forall r, padded (k r)) -> padded (ITree.bind t k).
Proof.
  pcofix CIH. intros t Ht Hk. pstep. red. unfold ITree.bind, ITree.subst.
  punfold Ht. red in Ht. inversion Ht; cbn; simpl; try rewrite <- H0; try rewrite <- H.
  - pstep_reverse. eapply paco1_mon; try apply Hk. intros. contradiction.
  - constructor. pclearbot. right. eapply CIH; eauto.
  - rewrite itree_eta'. pstep_reverse.
    match goal with |- paco1 _ _ ?t => assert (t ≅ Vis e (fun x => Tau (ITree.bind (k0 x) k))) end. 
    pstep. constructor. left. setoid_rewrite bind_tau. apply Reflexive_eqit.
    auto.
    rewrite H1. pstep. red. cbn. constructor. right. pclearbot. eapply CIH. apply H0.
    apply Hk.
Qed.

Lemma padded_interp_mrec_spec_padded  D E R 
        (bodies : forall X,  itree_spec (D +' E) X) (t : itree_spec (D +' E) R) : 
  padded t -> (forall d, padded (bodies d)) -> padded (interp_mrec_spec bodies t).
Proof.
  revert t. pcofix CIH. intros t Ht Hbodies. punfold Ht. red in Ht.
  pstep. red. unfold interp_mrec_spec. inv Ht; cbn.
  - constructor.
  - pclearbot. cbn. constructor. eauto.
  - destruct e; try destruct e; cbn.
    + constructor. pclearbot. right. eapply CIH; auto.
      apply padded_bind. auto. intros. pstep. constructor. auto.
    + rewrite itree_eta'. pstep_reverse.
      match goal with |- paco1 _ _ ?t => assert (t ≅ Vis (Spec_vis e) (fun x => Tau (interp_mrec_spec bodies (k x)) ) )
                      end.
      pstep. constructor. intros. left. setoid_rewrite interp_mrec_spec_tau.
      apply Reflexive_eqit. auto.
      rewrite H1. pstep. constructor. right. pclearbot. eapply CIH; eauto.
      apply H0.
    + rewrite itree_eta'. pstep_reverse.
      match goal with |- paco1 _ _ ?t => assert (t ≅ Vis (@Spec_forall E _) (fun x => Tau (interp_mrec_spec bodies (k x)) ) )
                      end.
      pstep. constructor. intros. left. setoid_rewrite interp_mrec_spec_tau.
      apply Reflexive_eqit. auto.
      rewrite H1. pstep. constructor. right. pclearbot. eapply CIH; eauto.
      apply H0.
    + rewrite itree_eta'. pstep_reverse.
      match goal with |- paco1 _ _ ?t => assert (t ≅ Vis (@Spec_exists E _) (fun x => Tau (interp_mrec_spec bodies (k x)) ) )
                      end.
      pstep. constructor. intros. left. setoid_rewrite interp_mrec_spec_tau.
      apply Reflexive_eqit. auto.
      rewrite H1. pstep. constructor. right. pclearbot. eapply CIH; eauto.
      apply H0.
Qed.
    
Section padded_refines_mrec.
Context (D1 D2 E1 E2 : Type -> Type).
Context (bodies1 : forall X, itree_spec (D1 +' E1) X).
Context (bodies2 : forall X, itree_spec (D2 +' E2) X).
Context (RPreInv : prerel D1 D2) (RPre : prerel E1 E2) (RPostInv : postrel D1 D2) (RPost : postrel E1 E2).

Context
  (Hbodies : forall {X Y} (d1 : D1 X) (d2 : D2 Y),
      RPreInv _ _ d1 d2 -> 
      padded_refines (SumPreRel RPreInv RPre) (SumPostRel RPostInv RPost) (fun x y => RPostInv _ _ d1 x d2 y)
        (bodies1 _) (bodies2 _)).

Theorem padded_refines_interp_mrec_spec (R1 R2 : Type) (RR : R1 -> R2 -> Prop) : forall t1 t2, 
    padded_refines (SumPreRel RPreInv RPre) (SumPostRel RPostInv RPost) RR t1 t2 ->
    padded_refines RPre RPost RR (interp_mrec_spec bodies1 t1) (interp_mrec_spec bodies2 t2).
Proof.
  unfold padded_refines. intros.
  eapply refines_eutt_padded_r; try apply pad_is_padded. symmetry. apply padded_interp_mrec_spec.
  eapply refines_eutt_padded_l; try apply pad_is_padded. 2 : symmetry; apply padded_interp_mrec_spec.
  apply padded_interp_mrec_spec_padded; intros; apply pad_is_padded.
  eapply refines_interp_mrec_spec; eauto.
Qed.

Theorem padded_refines_mrec {X Y} (d1 : D1 X) (d2 : D2 Y) :
  RPreInv _ _ d1 d2 ->
  padded_refines RPre RPost (fun x y => RPostInv _ _ d1 x d2 y) 
    (mrec_spec bodies1 _) (mrec_spec bodies2 _).
Proof.
  intros. apply padded_refines_interp_mrec_spec. auto.
Qed.

Theorem padded_refines_mrec_spec {X Y} (d1: D1 X) (d2: D2 Y) RR : 
  (forall x y, RPostInv _ _ d1 x d2 y -> (RR x y : Prop)) ->
  RPreInv _ _ d1 d2 -> 
  padded_refines RPre RPost RR (mrec_spec bodies1 _) (mrec_spec bodies2 _).
Proof.
  intros. eapply padded_refines_monot; try eapply padded_refines_mrec; cbn; eauto.
Qed.

End padded_refines_mrec.        

Section interp_mrec_spec_ev.
Context (D E : Type -> Type).
Context (body : forall X, itree_spec (D +' E) X).

Lemma interp_mrec_spec_forall R X (k : X -> itree_spec (D +' E) R)  :
  interp_mrec_spec body (Vis (Spec_forall X) k) ≅
                   Vis (Spec_forall X) (fun x => interp_mrec_spec body (k x)).
Proof.
  pstep. red. cbn. constructor. left. apply Reflexive_eqit. auto.
Qed.

Lemma interp_mrec_spec_exists R X (k : X -> itree_spec (D +' E) R)  :
  interp_mrec_spec body (Vis (Spec_exists X) k) ≅
                   Vis (Spec_exists X) (fun x => interp_mrec_spec body (k x)).
Proof.
  pstep. red. cbn. constructor. left. apply Reflexive_eqit. auto.
Qed.

Lemma interp_mrec_spec_inr R {X} e (k : X -> itree_spec (D +' E) R) : 
  interp_mrec_spec body (Vis (Spec_vis (inr1 e)) k) ≅
                   Vis (Spec_vis e) (fun x => interp_mrec_spec body (k x)).
Proof.
  pstep. red. cbn. constructor. left. apply Reflexive_eqit. auto.
Qed.

Lemma interp_mrec_spec_inl R {X} (d : D X) (k : X -> itree_spec (D +' E) R) : 
  interp_mrec_spec body (Vis (Spec_vis (inl1 d)) k) ≅
                   Tau (interp_mrec_spec body (ITree.bind (body _) k)).
Proof.
  pstep. red. cbn. constructor. left. apply Reflexive_eqit. auto.
Qed.

Lemma interp_mrec_spec_ret R (r : R) :
  interp_mrec_spec body (Ret r) ≅ Ret r.
Proof.
  pstep. red; cbn; constructor. auto.
Qed.

Lemma interp_mrec_spec_proper1 R : Proper (eq_itree eq ==> @eq_itree _ _ R eq) (interp_mrec_spec body).
Proof.
  ginit. gcofix CIH. intros. unfold interp_mrec_spec. pinversion H0; try inv CHECK.
  - gstep. red; cbn; constructor. auto.
  - gstep. red. cbn. constructor. gfinal. eauto.
  - destruct e; try destruct e.
    + setoid_rewrite interp_mrec_spec_inl. gstep. constructor.
      gfinal. left. eapply CIH. eapply eqit_bind. reflexivity.
      red.
      intros. subst. apply REL.
    + gstep. red. cbn. constructor. gfinal. intros. left.
      eapply CIH. apply REL.
    + gstep. red. cbn. constructor. gfinal. intros. left.
      eapply CIH. apply REL.
    + gstep. red. cbn. constructor. gfinal. intros. left.
      eapply CIH. apply REL.
Qed.
End interp_mrec_spec_ev.

Global Instance interp_mrec_spec_proper1_inst (D E : Type -> Type) (R : Type)
 (body : forall X, itree_spec (D +' E) X) :
  Proper (eq_itree eq ==> @eq_itree _ _ R eq) (interp_mrec_spec body).
Proof.
  apply interp_mrec_spec_proper1.
Qed.

Section interp_mrec_spec_bind.
Context (D E : Type -> Type).
Context (body : forall X, itree_spec (D +' E) X).

Lemma interp_mrec_spec_bind R S : forall (t : itree_spec (D +' E) R ) (k : R -> itree_spec (D +' E) S),
    interp_mrec_spec body (ITree.bind t k) ≅
                     ITree.bind (interp_mrec_spec body t) (fun r => interp_mrec_spec body (k r)).
Proof.
  ginit. gcofix CIH. intros. destruct (observe t) eqn : Ht; use_simpobs.
  - symmetry in Ht. apply simpobs in Ht. rewrite Ht.
    rewrite interp_mrec_spec_ret. repeat rewrite bind_ret_l.
    apply Reflexive_eqit_gen. auto.
  - symmetry in Ht. apply simpobs in Ht. 
    rewrite Ht. rewrite interp_mrec_spec_tau. repeat rewrite bind_tau.
    rewrite interp_mrec_spec_tau. gstep. constructor. gfinal. eauto.
  - symmetry in Ht. apply simpobs in Ht. 
    rewrite Ht. destruct e; try destruct e.
    + rewrite bind_vis. repeat rewrite interp_mrec_spec_inl. rewrite bind_tau.
      cbn.
      gstep. constructor.
      assert (ITree.bind (body _) (fun x => ITree.bind (k0 x) k) ≅ 
              ITree.bind (ITree.bind (body _) (fun x => (k0 x))) k).
      rewrite bind_bind. reflexivity.
      rewrite H.
      gfinal. eauto. 
    + rewrite bind_vis. repeat rewrite interp_mrec_spec_inr. rewrite bind_vis.
      gstep. constructor. gfinal. eauto.
    + rewrite bind_vis. repeat rewrite interp_mrec_spec_forall. rewrite bind_vis.
      gstep. constructor. gfinal. eauto.
    + rewrite bind_vis. repeat rewrite interp_mrec_spec_exists. rewrite bind_vis.
      gstep. constructor. gfinal. eauto.
Qed.

 

End interp_mrec_spec_bind.

Lemma refines_strengthen_RR :
  forall E1 E2 X Y PRE POST RR1 RR2 t1 t2,
    (forall x y, RR1 x y -> RR2 x y) ->
    @refines E1 E2 X Y
                    PRE POST RR1 t1 t2 ->
    @refines E1 E2 X Y
      PRE POST RR2 t1 t2.
Proof.
  intros E1 E2 X Y PRE POST RR1 RR2 t1 t2 STRENGTHEN REF.
  punfold REF; red in REF; cbn in REF.
  setoid_rewrite itree_eta.
  genobs t1 ot1.
  genobs t2 ot2.
  clear t1 t2 Heqot1 Heqot2.
  revert ot1 ot2 REF.
  pcofix CIH; intros ot1 ot2 REF.
  induction REF; cbn in *; subst; pclearbot;
    try solve
      [pstep; red; cbn;
       constructor; eauto with paco].
  - pstep; red; cbn;
    constructor; eauto.
    right.
    setoid_rewrite EqAxiom.itree_eta_.
    punfold H.
  - pstep; red; cbn;
    constructor; eauto.
    right.
    apply H0 in H1.
    setoid_rewrite EqAxiom.itree_eta_.
    eapply CIH; eauto.
    punfold H1.
  - pstep; red; cbn;
    constructor; eauto.
    punfold IHREF.
  - pstep; red; cbn;    
    constructor; eauto.
    punfold IHREF.
  - pstep; red; cbn;    
    constructor; eauto.

    intros a.
    specialize (H0 a).
    punfold H0.
  - pstep; red; cbn.
    econstructor; eauto.
    punfold IHREF.
  - pstep; red; cbn.
    econstructor; eauto.
    punfold IHREF.
  - pstep; red; cbn;    
    constructor; eauto.

    intros a.
    specialize (H0 a).
    punfold H0.
Qed.

Lemma padded_refines_strengthen_RR :
  forall E1 E2 X Y PRE POST RR1 RR2 t1 t2,
    (forall x y, RR1 x y -> RR2 x y) ->
    @padded_refines E1 E2 X Y
                    PRE POST RR1 t1 t2 ->
    @padded_refines E1 E2 X Y
      PRE POST RR2 t1 t2.
Proof.
  intros E1 E2 X Y PRE POST RR1 RR2 t1 t2 H H0.
  eapply refines_strengthen_RR; eauto.
Qed.
