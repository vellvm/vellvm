From Coq Require Import
     Morphisms
.

From ITree Require Import
     Basics.Utils
     Axioms
     ITree
     ITreeFacts
     Eq.Rutt
     Props.Infinite
     Props.EuttNoRet.

From ITree.Extra Require Import
     ITrace.ITraceDefinition
     ITrace.ITraceFacts
     ITrace.ITracePrefix
.


From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

(* Contains the proof of peel_lemma which allows us
   to decompose a trace of bind t f into a head that refines t and a tail
   that refines f *)

Section Peel.
Context (classicT : forall (P : Type), P + (P -> False)).

Definition peel_vis {E R S A B} (e0 : E A) (a : A) (k0 : unit -> itrace E R)
           (e1 : E B) (k1 : B -> itree E S)
           (peel : itrace' E R -> itree' E S -> itrace E S) : itrace E S.
Proof.
  destruct (classicT (A = B)).
  - subst. apply (Vis (evans _ e0 a) (fun _ => peel (observe (k0 tt)) (observe (k1 a) ) ) ).
  - apply ITree.spin.
Defined.

CoFixpoint peel_ {E R S} (ob : itrace' E R) (ot : itree' E S) : itrace E S :=
  match ob, ot with
  | TauF b, TauF t => Tau (peel_ (observe b) (observe t))
  | _, RetF s => Ret s
  | TauF b, ot => Tau (peel_ (observe b) ot )
  | ob, TauF t => Tau (peel_ ob (observe t) )
  | VisF (evempty _ Hempty e) _ , _ => Vis (evempty _ Hempty e) (fun v : void => match v with end)
  (* The type of this is problematic need some tricky dependently typed programming
     in order to have this work
   *)

  | VisF (evans _ e0 a) k0, VisF e1 k1 => peel_vis e0 a k0 e1 k1 peel_
  | _, _ => ITree.spin
  end.

Definition peel {E R S} (b : itrace E R) (t : itree E S) : itrace E S :=
  peel_ (observe b) (observe t).
(* here is a sketchy axiom use *)
Definition peel_cont_vis {E R S A B} (e0 : E A) (a : A) (k0 : unit -> itrace E R)
           (e1 : E B) (k1 : B -> itree E S)
           (peel : itrace' E R -> itree' E S -> itrace E R) : itrace E R.
Proof.
  destruct (classicT (A = B) ).
  - subst. apply (Tau (peel (observe (k0 tt)) (observe (k1 a) ) ) ).
  - apply ITree.spin.
Defined.

(*Actually I may be able to remove this ugly bs. I think I really only use peel*)
CoFixpoint peel_cont_ {E R S} (ob : itrace' E R) (ot : itree' E S) : itrace E R :=
  match ot with
  | RetF _ => go ob
  | TauF t => match ob with
             | TauF b => Tau (peel_cont_ (observe b) (observe t))
             | ob => Tau (peel_cont_ ob (observe t)  )
             end
  | VisF e1 k1 => match ob with
                 | TauF b => Tau (peel_cont_ (observe b) ot)
                 | VisF (evempty _ Hempty e) _ =>
                     ITree.spin
                 | VisF (evans _ e0 a) k0 => peel_cont_vis e0 a k0 e1 k1 peel_cont_
                 | _ => ITree.spin
                 end
  end.

Definition peel_cont {E R S} (b : itrace E R) (t : itree E S) : S -> itrace E R :=
  fun s => peel_cont_ (observe b) (observe t).

Lemma refine_ret_vis_contra : forall (E: Type -> Type) (R A: Type)
                                (r : R) (e : E A) (k : A -> itree E R),
    ~ (Ret r ⊑ Vis e k).
Proof.
  intros. intro Hcontra. pinversion Hcontra.
Qed.

(* maybe a better way of doing it is to use strong LEM to see if X = A in the vis case
   then I can remove that if statement given

 *)

Lemma peel_t_ret : forall E R S (b : itrace E S) (t : itree E R) r, t ≅ Ret r -> (peel b t ≅ Ret r).
Proof.
  intros.  unfold peel.
  pinversion H; subst; try inv CHECK.
  destruct (observe b); cbn; auto.
  - pfold. red. cbn. constructor. auto.
  - pfold. red. cbn. constructor; auto.
  - pfold. red. cbn. simpl. destruct e.
    + cbn. constructor. auto.
    + cbn. constructor. auto.
Qed.

(*doing these proofs, may require some techniques you don't really know*)

Lemma peel_refine_t : forall (E : Type -> Type) (R S : Type)
                        (b : itrace E S) (t : itree E R) (f : R -> itree E S)
                        (Hrutt : b ⊑ ITree.bind t f),
    peel b t ⊑ t.
Proof.
  intros E R S b t f. generalize dependent b. generalize dependent t.
  pcofix CIH. intros.
  punfold Hrutt. red in Hrutt. cbn in Hrutt. pfold. red.
  unfold peel.
  destruct (observe t) eqn : Heq.
  - destruct (observe b); cbn; try (constructor; auto).
    destruct e; cbn; constructor; auto.
  - dependent induction Hrutt.
    + exfalso. symmetry in Heq. apply simpobs in Heq. apply simpobs in x.
      rewrite Heq in x. rewrite bind_tau in x. pinversion x.
      inv CHECK.
    + rewrite <- x0. cbn. constructor. right. eapply CIH.
      pclearbot. symmetry in Heq. apply simpobs in x0.
      apply simpobs in x. apply simpobs in Heq.
      apply eq_sub_eutt in x0. apply eq_sub_eutt in Heq.
      rewrite tau_eutt in Heq. rewrite tau_eutt in x0.
      rewrite <- Heq. rewrite x. rewrite tau_eutt. auto.
    + exfalso. symmetry in Heq. apply simpobs in Heq.
      apply simpobs in x.
      rewrite Heq in x. rewrite bind_tau in x. pinversion x.
      inv CHECK.
    + rewrite <- x. cbn. constructor. right. eapply CIH.
      clear IHHrutt. symmetry in Heq. apply simpobs in Heq.
      apply eq_sub_eutt in Heq. rewrite tau_eutt in Heq.
      rewrite <- Heq. pfold. auto.
    + cbn. destruct (observe b) eqn : Heq'.
      * cbn. rewrite <- Heq'. constructor. right. eapply CIH.
        symmetry in Heq'.
        apply simpobs in Heq'. rewrite Heq'.
        symmetry in Heq. apply simpobs in Heq.
        apply eq_sub_eutt in Heq. rewrite tau_eutt in Heq.
        rewrite <- Heq. apply simpobs in x. rewrite x.
        rewrite tau_eutt. pfold. auto.
      * cbn. clear IHHrutt.
        constructor. right. eapply CIH.
        symmetry in Heq. apply simpobs in Heq.
        apply eq_sub_eutt in Heq. rewrite tau_eutt in Heq.
        rewrite <- Heq.
        apply simpobs in x. apply eq_sub_eutt in x.
        rewrite tau_eutt in x. rewrite x.
        enough (Tau t1 ⊑ t2).
        { rewrite tau_eutt in H. auto. }
        pfold. auto.
      * destruct e; cbn.
        ++ constructor. right. rewrite <- Heq'. clear IHHrutt.
           eapply CIH. symmetry in Heq.
           apply simpobs in Heq. apply eq_sub_eutt in Heq.
           rewrite tau_eutt in Heq. apply simpobs in x.
           apply eq_sub_eutt in x. rewrite tau_eutt in x.
           rewrite <- Heq. rewrite x. pfold. red.
           rewrite Heq'. auto.
        ++ constructor. right. rewrite <- Heq'. clear IHHrutt.
           eapply CIH. symmetry in Heq.
           apply simpobs in Heq. apply eq_sub_eutt in Heq.
           rewrite tau_eutt in Heq. apply simpobs in x.
           apply eq_sub_eutt in x. rewrite tau_eutt in x.
           rewrite <- Heq. rewrite x. pfold. red.
           rewrite Heq'. auto.
  - dependent induction Hrutt.
    + exfalso. symmetry in Heq. apply simpobs in Heq. apply simpobs in x.
      rewrite Heq in x. rewrite bind_vis in x.
      pinversion x.
    + exfalso. symmetry in Heq. apply simpobs in Heq. apply simpobs in x.
      rewrite Heq in x. rewrite bind_vis in x.
      pinversion x; inv CHECK.
    + rewrite <- x0.
      symmetry in Heq. apply simpobs in Heq. apply simpobs in x.
      rewrite Heq in x. rewrite bind_vis in x. pinversion x.
      ddestruction. inversion H; ddestruction.
      * unfold observe. cbn. unfold peel_vis.
        destruct (classicT (B = B) ); try contradiction.
        unfold eq_rect_r, eq_rect.
        remember (eq_sym _) as He. clear HeqHe.
        dependent destruction He. cbn. constructor; eauto.
        intros. inversion H1. ddestruction.
        apply H0 in H1. pclearbot. unfold id. right. eapply CIH.
        red in x1. cbn in x1. inversion x1. ddestruction.
        specialize (H0 tt a (rar _ _ _)).
        specialize (REL0 a). pclearbot.
        change (paco2 ?x ?y ?t ?u) with (eq_itree eq t u) in REL0.
        rewrite REL0. apply H0.
      * cbn. constructor; eauto. intros. contradiction.
    + rewrite <- x. cbn. constructor. eapply IHHrutt; eauto.
    + exfalso. symmetry in Heq. apply simpobs in x. apply simpobs in Heq.
      rewrite Heq in x. rewrite bind_vis in x.
      pinversion x; inv CHECK.
Qed.

Lemma not_spin_eutt_ret : forall E R (r : R), ~ (@ITree.spin E R ≈ Ret r).
Proof.
  intros. intros Hcontra. specialize (@spin_infinite E R) as Hdiv.
  rewrite Hcontra in Hdiv. pinversion Hdiv.
Qed.


Lemma proper_peel_eutt_l : forall (E : Type -> Type) (R S : Type)
                                  (b b': itrace E R) (t : itree E S),
    (b ≈ b') -> (peel b t ≈ peel b' t).
Proof.
  intros E R S. pcofix CIH. intros. unfold peel.
  destruct (observe t).
  - pfold. red. destruct (observe b); destruct (observe b'); cbn;
      try (destruct e); try (destruct e0); cbn;
      try (constructor; auto; fail).
  - pfold. punfold H0. red in H0. dependent induction H0.
    + rewrite <- x0. rewrite <- x. red. cbn. constructor.
      right. rewrite x0. eapply CIH. reflexivity.
    + rewrite <- x0. rewrite <- x. red. cbn. constructor. right.
      pclearbot. eapply CIH. auto.
    + rewrite <- x0. rewrite <- x. destruct e; cbn.
      * red. cbn. constructor. right. rewrite x. rewrite x0.
        eapply CIH. pfold. red. rewrite <- x. rewrite <- x0.
        constructor. auto.
      * red. cbn. constructor. right. rewrite x0. rewrite x.
        eapply CIH. pfold. red. rewrite <- x0. rewrite <- x.
        constructor. auto.
    + destruct (observe b); destruct (observe b'); dependent destruction x.
      * red. cbn. constructor. right. remember (@go (EvAns E) _ (RetF r0)) as t1.
        assert (RetF r0 = observe t1).
        { rewrite Heqt1. auto. }
        rewrite H. eapply CIH. rewrite Heqt1. pfold. auto.
      * red. cbn. constructor. right. eapply CIH.
        enough (t2 ≈ Tau t3).
        { rewrite tau_eutt in H. auto. }
        pfold. auto.
      * red. destruct e; cbn.
        ++ constructor. right.
           remember (@go (EvAns E) _ (VisF (evans A ev ans) k )  ) as t1.
           assert (VisF (evans A ev ans) k  = observe t1).
           { rewrite Heqt1. auto. }
           rewrite H. eapply CIH. subst. pfold. auto.
        ++ constructor. right.
           remember (go (VisF (evempty A Hempty ev) k )  ) as t1.
           assert (VisF (evempty A Hempty ev) k = observe t1 ).
           { subst. auto. }
           rewrite H. eapply CIH. subst. pfold. auto.
    + destruct (observe b); destruct (observe b'); dependent destruction x.
      * red. cbn. constructor. right. remember (@go (EvAns E) _ (RetF r0)) as t2.
        assert (RetF r0 = observe t2).
        { subst. auto. }
        rewrite H. eapply CIH. rewrite Heqt2. pfold. auto.
      * red. cbn. constructor. right. eapply CIH.
        enough (Tau t1 ≈ t3).
        { rewrite tau_eutt in H. auto. }
        pfold. auto.
      * red. destruct e; cbn.
        ++ constructor. right.
           remember (@go (EvAns E) _ (VisF (evans A ev ans) k )  ) as t2.
           assert (VisF (evans A ev ans) k  = observe t2).
           { subst. auto. }
           rewrite H. eapply CIH. subst. pfold. auto.
        ++ constructor. right.
           remember (go (VisF (evempty A Hempty ev) k )  ) as t2.
           assert (VisF (evempty A Hempty ev) k = observe t2 ).
           { subst. auto. }
           rewrite H. eapply CIH. subst. pfold. auto.
  - pfold. punfold H0. red in H0. dependent induction H0.
    + rewrite <- x0. rewrite <- x. red. cbn. constructor.
      left. apply pacobot2.
      enough (@ITree.spin (EvAns E) S  ≈ ITree.spin); auto.
      reflexivity.
    + rewrite <- x. rewrite <- x0. red. cbn. constructor. right.
      remember (go (VisF e k) ) as t0.
      assert (VisF e k = observe t0).
      { subst. auto. }
      rewrite H. eapply CIH. pclearbot. auto.
    + rewrite <- x0. rewrite <- x. red. destruct e; cbn.
      * unfold observe. cbn. unfold peel_vis.
        destruct (classicT (A = X) ).
        ++ unfold eq_rect_r, eq_rect. remember (eq_sym e) as He.
           dependent destruction He. cbn. constructor. intros.
           right. eapply CIH. pclearbot. auto with itree.
        ++ cbn. constructor. left. apply pacobot2.
           enough (@ITree.spin (EvAns E) S ≈ ITree.spin ); auto.
           reflexivity.
      * constructor. left. contradiction.
    + rewrite <- x. red. destruct (observe b') eqn : Heq.
      * rewrite <- Heq. cbn. constructor; auto. eapply IHeqitF; eauto. rewrite Heq. auto.
      * cbn. constructor. right.
        remember (go (VisF e k) ) as t2.
        assert (VisF e k = observe t2).
        { subst. auto. }
        rewrite H. eapply CIH.
        enough (t1 ≈ Tau t0).
        { rewrite tau_eutt in H1. auto. }
        pfold; auto.
      * cbn. constructor; eauto. rewrite <- Heq. eapply IHeqitF; eauto.
        rewrite Heq. auto.
    + rewrite <- x. red. destruct (observe b) eqn : Heq.
      * rewrite <- Heq. cbn. constructor; auto. eapply IHeqitF; eauto. rewrite Heq. auto.
      * cbn. constructor. right.
        remember (go (VisF e k) ) as t1.
        assert (VisF e k = observe t1).
        { subst. auto. }
        rewrite H. eapply CIH.
        enough (Tau t0 ≈ t2).
        { rewrite tau_eutt in H1. auto. }
        pfold; auto.
      * cbn. constructor; eauto. rewrite <- Heq. eapply IHeqitF; eauto.
        rewrite Heq. auto.
Qed.



Lemma proper_peel_eutt_r : forall (E : Type -> Type) (R S : Type)
                                  (b: itrace E R) (t t': itree E S),
    (t ≈ t') -> (peel b t ≈ peel b t').
Proof.
  intros E R S. pcofix CIH. intros.
  pfold. red. unfold peel. destruct (observe b) eqn : Heqb.
  - punfold H0. red in H0. dependent induction H0.
    + rewrite <- x. rewrite <- x0.  cbn. constructor. auto.
    + rewrite <- x. rewrite <- x0. cbn. constructor. right. rewrite <- Heqb.
      eapply CIH. pclearbot. auto.
    + rewrite <- x0. rewrite <- x. cbn. constructor.
      left. apply paco2_eqit_refl.
    + rewrite <- x.  cbn. constructor; auto. eapply IHeqitF; eauto.
    + rewrite <- x. cbn. constructor; auto. eapply IHeqitF; eauto.
  - punfold H0. red in H0. dependent induction H0.
    + rewrite <- x. rewrite <- x0. cbn. constructor. auto.
    + rewrite <- x0. rewrite <- x. cbn. constructor. right.
      pclearbot. eapply CIH; auto.
    + rewrite <- x0. rewrite <- x. cbn. constructor. right.
      rewrite x0. rewrite x. eapply CIH.
      pfold. red. rewrite <- x0. rewrite <- x.
      constructor. auto.
    + rewrite <- x. destruct (observe t') eqn : Heqt'.
      * cbn.  constructor; auto. clear IHeqitF.
        dependent induction H0.
        ++ rewrite <- x. destruct (observe t0); cbn; try (constructor; auto; fail).
           destruct e; cbn; constructor; auto.
        ++ rewrite <- x. cbn. destruct (observe t2) eqn : Heqt2; cbn.
           ** constructor; eauto. rewrite <- Heqt2.  eapply IHeqitF; eauto.
           ** constructor; auto. eapply IHeqitF; eauto.
           ** destruct e; cbn;
                try (constructor; auto; rewrite <- Heqt2; eapply IHeqitF; eauto).
      * cbn. constructor. right. eapply CIH; eauto.
        enough (t1 ≈ Tau t2).
        { rewrite tau_eutt in H. auto. }
        pfold. auto.
      * cbn. constructor. rewrite <- Heqt'. right. eapply CIH.
        pfold. red. rewrite Heqt'. auto.
    + rewrite <- x. destruct (observe t).
      * cbn. constructor; auto. clear IHeqitF.
        dependent induction H0.
        ++ rewrite <- x. destruct (observe t0); try (destruct e); cbn; constructor; auto.
        ++ rewrite <- x. destruct (observe t1) eqn : Heqt1; cbn.
           ** constructor; auto. rewrite <- Heqt1. eapply IHeqitF; eauto.
           ** constructor; auto. eapply IHeqitF; eauto.
           ** destruct e; cbn; try (constructor; auto; rewrite <- Heqt1; eapply IHeqitF; eauto).
      * cbn. constructor. right. eapply CIH; eauto.
        rewrite <- tau_eutt at 1. pfold. auto.
      * cbn. constructor. right. remember ((Vis e k) ) as t1.
        assert (VisF e k = observe t1).
        { subst. auto. }
        rewrite H. eapply CIH. subst. pfold. auto.
  - punfold H0. red in H0. dependent induction H0.
    + rewrite <- x. rewrite <- x0. destruct e; cbn; constructor; auto.
    + rewrite <- x. rewrite <- x0. destruct e; cbn; constructor; right; rewrite <- Heqb;
        eapply CIH; pclearbot; eauto.
    + rewrite <- x. rewrite <- x0. destruct e0; cbn.
      * unfold observe. cbn. unfold peel_vis.
        destruct (classicT (A = u) ).
        ++ unfold eq_rect_r, eq_rect. remember (eq_sym e0) as He.
           dependent destruction He. cbn. constructor. intros.
           right. eapply CIH. pclearbot. auto with itree.
        ++ cbn. constructor. left. apply paco2_eqit_refl.
      * constructor. contradiction.
    + rewrite <- x. destruct (observe t'); destruct e; cbn.
      * constructor; auto. clear IHeqitF. dependent induction H0.
        ++ rewrite <- x. cbn. constructor; auto.
        ++ rewrite <- x. cbn. constructor; eauto.
      * constructor; auto. clear IHeqitF. dependent induction H0.
        ++ rewrite <- x. cbn. constructor; auto.
        ++ rewrite <- x. cbn. constructor; eauto.
      * constructor. rewrite <- Heqb. right. eapply CIH.
        setoid_rewrite <- tau_eutt at 2. pfold. auto.
      * rewrite <- Heqb. constructor. right. eapply CIH.
        setoid_rewrite <- tau_eutt at 2. pfold. auto.
      * constructor; auto. clear IHeqitF.
        dependent induction H0.
        ++ rewrite <- x. unfold observe. cbn.
           unfold peel_vis. destruct (classicT (A = X0) ).
           ** unfold eq_rect_r, eq_rect.
              remember (eq_sym e) as He. dependent destruction He.
              cbn. constructor. intros. right. pclearbot. eapply CIH; eauto with itree.
           ** cbn. constructor. left. apply paco2_eqit_refl.
        ++ rewrite <- x. cbn. constructor; auto; eapply IHeqitF; eauto.
      * constructor; auto. clear IHeqitF.
        dependent induction H0.
        ++ rewrite <- x. cbn. constructor. contradiction.
        ++ rewrite <- x. cbn. constructor; auto; eapply IHeqitF; eauto.
    + rewrite <- x. cbn. destruct (observe t) eqn : Heqt; destruct e; cbn.
      * constructor; auto. clear IHeqitF. dependent induction H0.
        ++ rewrite <- x. cbn. constructor; auto.
        ++ rewrite <- x. cbn. constructor; eauto.
      * constructor; auto. clear IHeqitF. dependent induction H0.
        ++ rewrite <- x. cbn. constructor; auto.
        ++ rewrite <- x. cbn. constructor; eauto.
      * constructor. right. rewrite <- Heqb. eapply CIH; eauto. rewrite <- tau_eutt.
        pfold. auto.
      * constructor. rewrite <- Heqb. right. eapply CIH; eauto. rewrite <- tau_eutt.
        pfold. auto.
      * constructor; auto. clear IHeqitF. dependent induction H0.
        ++ rewrite <- x. unfold observe. cbn.
           unfold peel_vis.
           destruct (classicT (A = X0) ).
           ** unfold eq_rect_r, eq_rect.
              remember (eq_sym e) as He. dependent destruction He.
              cbn. constructor. intros. right. pclearbot. eapply CIH; apply REL.
           ** cbn. constructor. left. apply paco2_eqit_refl.
        ++ rewrite <- x. cbn. constructor; eauto.
      * constructor; auto. clear IHeqitF. dependent induction H0.
        ++ rewrite <- x. cbn. constructor. contradiction.
        ++ rewrite <- x. cbn. constructor; eauto.
Qed.

#[global] Instance proper_eutt_peel {E R S} : Proper (eutt eq ==> eutt eq ==> eutt eq) (@peel E R S).
Proof.
  intros ? ? ? ? ? ?. rewrite proper_peel_eutt_l with (t := x0); eauto.
  eapply proper_peel_eutt_r; eauto.
Qed.

Lemma not_peel_vis_ret: forall (R : Type) (E : Type -> Type) (S X : Type) (e : E X) (k : X -> itree E R)
                               (r : R) (t1 : itree (EvAns E) S),
    ~ (peel t1 (Vis e k) ≈ Ret r).
Proof.
  intros R E S X e k r t1 Heutt.
  punfold Heutt. unfold peel in *. red in Heutt. cbn in *.
  dependent induction  Heutt.
  - destruct (observe t1); cbn in x; try discriminate.
    destruct e0; cbn in *; try discriminate.
    unfold observe in x. cbn in x. unfold peel_vis in x.
    destruct (classicT (A = X)); try discriminate.
    unfold eq_rect_r, eq_rect in x. remember (eq_sym e0) as He.
    dependent destruction He. discriminate.
  - destruct (observe t1); cbn in x; try discriminate.
    + injection x as Hspin. rewrite Hspin in Heutt.
      eapply not_spin_eutt_ret. pfold. eauto.
    + injection x as Ht0. eapply IHHeutt; eauto. rewrite Ht0. reflexivity.
    + destruct e0; cbn in *; try discriminate.
      unfold observe in x. cbn in x. unfold peel_vis in *.
      destruct (classicT (A = X) ).
      * unfold eq_rect_r, eq_rect in x. remember (eq_sym e0) as He.
        dependent destruction He. discriminate.
      * cbn in x. injection x as Hspin. rewrite Hspin in Heutt.
        eapply not_spin_eutt_ret. pfold. eauto.
Qed.

Lemma peel_ret_inv:
  forall (R : Type) (r : R) (E : Type -> Type) (S : Type) (b : itrace E S) (t : itree E R),
    (peel b t ≈ Ret r) -> (t ≈ Ret r).
Proof.
  intros R r E S b t H. unfold peel in H.
  punfold H. red in H. cbn in H. pfold. red. cbn.
  dependent induction H.
  - unfold peel in x. destruct (observe b); destruct (observe t); cbn in *;
      dependent destruction x; try (constructor; auto; fail).
    + destruct e; dependent destruction x; try (constructor; auto).
    + destruct e; dependent destruction x.
    + destruct e; dependent destruction x.
      unfold observe in x. cbn in x. unfold peel_vis in x.
      destruct (classicT (A = X0) ) eqn : Heq.
      * unfold eq_rect_r, eq_rect in x. subst. remember (eq_sym eq_refl) as He.
        dependent destruction He. cbn in x0. discriminate.
      * discriminate.
  - destruct (observe b); destruct (observe t); cbn in x; dependent destruction x.
    + constructor; auto. eapply IHeqitF with (b := Ret r0); eauto.
    + exfalso. eapply not_spin_eutt_ret. pfold. eauto.
    + constructor; auto. eapply IHeqitF; eauto.
    + exfalso. destruct (observe t0).
      * cbn in H. eapply not_spin_eutt_ret.
        inv  H. pfold. eauto.
      * cbn in H. inv H. eapply not_peel_vis_ret.
        pfold. eauto.
      * destruct e0.
        ++ clear IHeqitF. unfold observe in H. cbn in H. unfold peel_vis in H.
           destruct (classicT (A = X) ).
           ** unfold eq_rect_r, eq_rect in H. remember (eq_sym e0) as He.
              dependent destruction He. inv H.
           ** eapply not_spin_eutt_ret. pfold. eauto.
        ++ cbn in H. inv H.
    + destruct e; cbn in x; try discriminate.
    + constructor; auto. eapply IHeqitF with (b := Vis e k); eauto. cbn.
      destruct e; cbn in x; dependent destruction x; auto.
    + destruct e; cbn in x; try discriminate.
      unfold observe in x. cbn in x. unfold peel_vis in x.
      destruct (classicT (A = X0) ).
      * unfold eq_rect_r, eq_rect in x. remember (eq_sym e) as He.
        dependent destruction He. discriminate.
      * injection x as Hspin. cbn in Hspin. exfalso.
        assert (t1 ≈ Ret r).
        { pfold. auto. }
        rewrite Hspin in H0. eapply not_spin_eutt_ret; eauto.
Qed.

Lemma eqitF_r_refl: forall (E : Type -> Type) (R: Type) r
                           (ot: itree' E R),
    eqitF eq true true id (upaco2 (eqit_ eq true true id) r)
          ot ot.
Proof.
  intros E R r ot.
  destruct ot; constructor; auto.
  - left. apply pacobot2, reflexivity.
  - left. apply pacobot2, reflexivity.
Qed.

Lemma eqitF_mon:
  forall (E : Type -> Type) (R : Type) (r : itree (EvAns E) R -> itree (EvAns E) R -> Prop)
         (t1 : itree' (EvAns E) R) (t0 : itree' (EvAns E) R),
    eqitF eq true true id (upaco2 (eqit_ eq true true id) bot2) t1 t0 ->
    eqitF eq true true id (upaco2 (eqit_ eq true true id) r) t1 t0.
Proof.
  intros E R r t1 t0' REL.
  induction REL; constructor; eauto.
  - pclearbot. left. apply pacobot2; auto.
  - pclearbot. intros. left. apply pacobot2; auto.
Qed.

Lemma eqitF_observe_peel_cont_vis:
  forall (E : Type -> Type) (R S A : Type) (ev : E A) (ans : A)
         (k1 k2 : unit -> itree (EvAns E) R),
    (forall v : unit, id (upaco2 (eqit_ eq true true id) bot2) (k1 v) (k2 v)) ->
    forall r : itree (EvAns E) R -> itree (EvAns E) R -> Prop,
      (forall (b b' : itrace E R) (t : itree E S),
          (b ≈ b') ->
          r (peel_cont_ (observe b) (observe t)) (peel_cont_ (observe b') (observe t))) ->
      forall (X : Type) (e : E X) (k : X -> itree E S),
        eqitF eq true true id (upaco2 (eqit_ eq true true id) r)
              (observe (peel_cont_ (VisF (evans A ev ans) k1) (VisF e k)))
              (observe (peel_cont_ (VisF (evans A ev ans) k2) (VisF e k))).
Proof.
  intros E R S A ev ans k1 k2 REL r CIH X e k.
  unfold observe. cbn. unfold peel_cont_vis.
  destruct (classicT (A = X) ).
  - unfold eq_rect_r, eq_rect. remember (eq_sym e0) as He.
    dependent destruction He. cbn. constructor.
    intros. right. pclearbot. eapply CIH. auto with itree.
  - cbn. apply eqitF_r_refl.
Qed.


Lemma proper_peel_cont_eutt_l : forall (E : Type -> Type) (R S : Type)
                                       (b b': itrace E R) (t : itree E S) (s : S),
    (b ≈ b') -> (peel_cont b t s ≈ peel_cont b' t s).
Proof.
  intros E R S. unfold peel_cont. intros b b' t _.
  revert b b' t. pcofix CIH. intros. pfold. punfold H0. red in H0.
  destruct (observe t) eqn : Heqt.
  - red. destruct (observe b') eqn : Hb; destruct (observe b) eqn : Hb'; inversion H0; cbn;
      try (constructor; auto; fail);
      try (constructor; auto; eapply eqitF_mon; eauto; fail);
      try (destruct e; cbn);
      try (constructor; auto; eapply eqitF_mon; eauto; fail).
    + constructor. pclearbot. left. apply pacobot2; auto.
    + subst. ddestruction. subst. cbn. constructor. intros. left. inv H0.
      ddestruction. subst. pclearbot. apply pacobot2; auto.
    + ddestruction. subst. ddestruction. subst. cbn. constructor; auto. intros [].
  (*looks like I didn't actually need to induct here ... *)
  - dependent induction H0; try clear IHeqitF.
    + rewrite <- x0. rewrite <- x. red. cbn. constructor. right.
      rewrite x. eapply CIH; eauto. pfold. red. rewrite <- x. constructor; auto.
    + rewrite <- x0. rewrite <- x. red. cbn. constructor. right.
      eapply CIH. pclearbot. auto.
    + rewrite <- x0. rewrite <- x. red. destruct e; cbn; constructor; right.
      * rewrite x. rewrite x0. eapply CIH; eauto. pfold. red.
        rewrite <- x0. rewrite <- x. constructor. auto.
      * rewrite x. rewrite x0. eapply CIH; eauto. pfold. red.
        rewrite <- x0. rewrite <- x. constructor. auto.
    + rewrite <- x. red. cbn.
      destruct (observe b') eqn : Heqb'; cbn.
      * constructor. right. rewrite <- Heqb'. eapply CIH.
        symmetry in Heqb'. apply simpobs in Heqb'. rewrite Heqb'.
        pfold. auto.
      * constructor. right. eapply CIH. setoid_rewrite <- tau_eutt at 2.
        pfold. auto.
      * constructor. right. rewrite <- Heqb'. eapply CIH.
        symmetry in Heqb'. apply simpobs in Heqb'. rewrite Heqb'. pfold. auto.
    + rewrite <- x. red. cbn. destruct (observe b) eqn : Heqb; cbn.
      * constructor; auto. right. rewrite <- Heqb. eapply CIH.
        pfold. red. rewrite Heqb. auto.
      * constructor. right. eapply CIH. rewrite <- tau_eutt at 1. pfold. auto.
      * constructor. right. rewrite <- Heqb. eapply CIH. pfold.
        red. rewrite Heqb. auto.
  - red. dependent induction H0; cbn.
    +  rewrite <- x0. rewrite <- x. cbn. constructor. left. pfold. apply eqitF_r_refl.
    + rewrite <- x0. rewrite <- x. cbn. constructor. right. rewrite <- Heqt. eapply CIH.
      pclearbot. auto.
    + rewrite <- x. rewrite <- x0. destruct e; cbn; try (apply eqitF_observe_peel_cont_vis; auto).
      apply eqitF_r_refl.
    + rewrite <- x. cbn. constructor; eauto.
    + rewrite <- x. cbn. constructor; eauto.
Qed.

Lemma peel_cont_ret_inv : forall E R S (b : itrace E R) (t : itree E S) (s : S),
    t ≈ Ret s -> (peel_cont_ (observe b) (observe t) ≈ b).
Proof.
  intros E R S. pcofix CIH. intros. punfold H0. red in H0. cbn in H0. dependent induction H0; subst.
  - rewrite <- x. cbn. pfold. red. cbn. apply eqitF_r_refl.
  - rewrite <- x. destruct (observe b) eqn : Hb.
    + pfold. red. cbn. constructor; auto.

      specialize (IHeqitF r CIH (Ret r0) t1 s ); auto.
      assert (S = S). auto. apply IHeqitF in H; auto. rewrite Hb.
      punfold H.
    + pfold. red. rewrite Hb. cbn.   constructor. right. eapply CIH with (s := s).
      pfold. auto.
    + pfold. red. rewrite Hb. cbn. rewrite <- Hb. constructor; auto.
      specialize (IHeqitF r CIH b t1 s ); auto.
      assert (S = S). auto. apply IHeqitF in H; auto. punfold H.
Qed.

Lemma proper_peel_cont_eutt_r : forall (E : Type -> Type) (R S : Type)
                                       (b: itrace E R) (t t': itree E S) (s : S),
    (t ≈ t') -> (peel_cont b t s ≈ peel_cont b t' s).
Proof.
  intros E R S. unfold peel_cont. intros b t t' _.
  revert b t t'. pcofix CIH. intros. pfold. punfold H0. red in H0. dependent induction H0.
  - rewrite <- x. rewrite <- x0. red. cbn. apply eqitF_r_refl.
  - rewrite <- x. rewrite <- x0. red. destruct (observe b) eqn : Heqb; cbn.
    + constructor. right. rewrite <- Heqb. eapply CIH. pclearbot. auto.
    + constructor. right. eapply CIH. pclearbot. auto.
    + constructor. right. rewrite <- Heqb. eapply CIH; pclearbot; auto.
  - rewrite <- x. rewrite <- x0. pclearbot. destruct (observe b) eqn : Heqb; red; cbn.
    + apply eqitF_r_refl.
    + constructor. rewrite x. rewrite x0. right. eapply CIH.
      pfold. red. rewrite <- x. rewrite <- x0. constructor. intros.
      left. auto.
    + destruct e0; cbn.
      * unfold observe. cbn. unfold peel_cont_vis.
        destruct (classicT (A = u) ); try apply eqitF_r_refl.
        unfold eq_rect_r, eq_rect. remember (eq_sym e0) as He.
        dependent destruction He. cbn. constructor. intros. right.
        eapply CIH. auto with itree.
      * apply eqitF_r_refl.
  - rewrite <- x. destruct (observe b) eqn : Heqb; red; cbn.
    + constructor; eauto. rewrite <- Heqb. eapply IHeqitF; eauto.
    + cbn. destruct (observe t') eqn : Heqt'; cbn.
      * constructor. left. apply pacobot2.
        eapply peel_cont_ret_inv with (s := r0). pfold. auto.
      * constructor. right. eapply CIH; eauto. setoid_rewrite <- tau_eutt at 2.
        pfold. auto.
      * constructor. right. rewrite <- Heqt'. eapply CIH.
        pfold. red. rewrite Heqt'. auto.
    + rewrite <- Heqb. constructor; auto. eapply IHeqitF; eauto.
  - rewrite <- x. destruct (observe b) eqn : Heqb; red; cbn.
    + constructor; auto. rewrite <- Heqb. eapply IHeqitF; eauto.
    + destruct (observe t) eqn : Heqt; cbn.
      * constructor. left. apply pacobot2.
        enough (t0 ≈ peel_cont_ (observe t0) (observe t2) ). auto.
        symmetry.
        eapply peel_cont_ret_inv with (s := r0). symmetry. pfold. auto.
      * constructor. right. eapply CIH. rewrite <- tau_eutt at 1. pfold. auto.
      * constructor. right. rewrite <- Heqt. eapply CIH.
        pfold. red. rewrite Heqt. auto.
    + rewrite <- Heqb. constructor; auto. eapply IHeqitF; eauto.
Qed.

#[global] Instance proper_eutt_peel_cont {E R S} : Proper (eutt eq ==> eutt eq ==> eq ==> eutt eq) (@peel_cont E R S).
Proof.
  repeat intro. subst. rewrite proper_peel_cont_eutt_l; eauto.
  rewrite proper_peel_cont_eutt_r; eauto. reflexivity.
Qed.
(*
Lemma peel_cont_bind : forall (E : Type -> Type) (R S : Type) (b : itrace E S) (t : itree E R) (f : R -> itree E S),
    b ⊑ ITree.bind t f -> (ITree.bind (peel b t) (peel_cont b t) ≈ b).
Proof.
  intros E R S. pcofix CIH. intros. punfold H0. pfold. red. red in H0. cbn in *.
  unfold ITree.bind in H0. unfold ITree.bind. cbn in *.
  unfold observe at 1. cbn.
 *)
(*may need an analgous lemma for *)
Lemma vis_refine_peel : forall (E : Type -> Type) (R S A : Type) (e : E A) (a : A)
                               (k1: unit -> itrace E S) (k2 : A -> itree E R) (k3 : unit -> itrace E R),
    (peel (Vis (evans _ e a) k1) (Vis e k2) ≈ Vis (evans _ e a) k3) ->
    (k3 tt ≈ peel (k1 tt) (k2 a)).
Proof.
  intros E R S A. (* pcofix CIH. *) intros e a k1 k2 k3 Hpeel.
  unfold peel in *. cbn in *. punfold Hpeel.
  red in Hpeel. cbn in *. cbn in Hpeel.
  unfold observe in Hpeel. cbn in Hpeel.
  unfold peel_vis in Hpeel.
  assert (A = A). auto.
  destruct (classicT (A = A) ); try contradiction. unfold eq_rect_r, eq_rect in Hpeel.
  remember (eq_sym e0) as He. dependent destruction He. cbn in *.
  clear HeqHe e0 H. pfold. red. cbn. inv Hpeel. ddestruction.
  pclearbot. specialize (REL tt).
  assert (peel_ (observe (k1 tt)) (observe (k2 a)) ≈ k3 tt ). auto.
  symmetry in H. punfold H.
Qed.

Lemma vis_refine_peel_cont :  forall (E : Type -> Type) (R S A : Type) (e : E A) (a : A)
                                     (k1: unit -> itrace E S) (k2 : A -> itree E R) (t : itrace E S),
    (peel_cont_ (VisF (evans _ e a) k1) (VisF e k2) ≈ t) ->
    (t ≈ peel_cont_ (observe (k1 tt)) (observe (k2 a))).
Proof.
  intros E R S A e a k1 k2 t Hpeelcont. punfold Hpeelcont. red in Hpeelcont.
  unfold observe in Hpeelcont at 1. cbn in *. unfold peel_cont_vis in *.
  assert (A = A); auto. destruct (classicT (A = A) ); try contradiction.
  unfold eq_rect_r, eq_rect in *. remember (eq_sym e0) as He.
  dependent destruction He. cbn in *. symmetry.
  assert (Tau (peel_cont_ (observe (k1 tt)) (observe (k2 a) ) )  ≈ t ).
  { pfold. auto. }
  rewrite tau_eutt in H0. auto.
Qed.

Lemma spin_not_vis : forall (E : Type -> Type) (R A : Type)
                            (e : E A) (k : A -> itree E R),
    ~ ITree.spin ≈ Vis e k.
Proof.
  intros E R A e k Hcontra. punfold Hcontra. red in Hcontra. cbn in *.
  dependent induction Hcontra.
  eapply IHHcontra; eauto.
Qed.

Lemma peel_vis_empty_contra: forall (R : Type) (E : Type -> Type) (S A0 : Type) (Hempty : A0 -> void)
                                    (ev : E A0) (k0 : void -> itree (EvAns E) S) (t0 : itree E R) (A : Type)
                                    (a : A) (e : E A) (k : unit -> itrace E R),
    eqitF eq true true id (upaco2 (eqit_ eq true true id) bot2)
          (observe (peel_ (VisF (evempty A0 Hempty ev) k0) (observe t0)))
          (VisF (evans A e a) k) -> False.
Proof.
  intros R E S A0 Hempty ev k0 t0 A a e k Hpeel.
  dependent induction Hpeel.
  - destruct (observe t0) eqn : Heqt0; discriminate.
  - destruct (observe t0) eqn : Heqt0; try discriminate. cbn in x. injection x as Ht1.
    rewrite Ht1 in IHHpeel. eapply IHHpeel; eauto.
Qed.


Lemma vis_peel_l : forall (E : Type -> Type) (R S A : Type) (e : E A) (a : A)
                          (b : itrace E S) (t : itree E R) (f : R -> itree E S) (k : unit -> itrace E R),
    b ⊑ ITree.bind t f ->
    (peel b t ≈ Vis (evans _ e a) k) -> exists k', (b ≈ Vis (evans _ e a) k').
Proof.
  intros E R S A e a b t f k Href Hpeel.
  punfold Hpeel. red in Hpeel. cbn in Hpeel. dependent induction Hpeel.
  - unfold peel in x.
    destruct (observe b) eqn : Heqb; destruct (observe t) eqn : Heqt; try destruct e0; cbn in *;
      dependent destruction x. unfold observe in x. cbn in x.
    unfold peel_vis in x.
    assert (A0 = X0).
    {
      clear x.
      symmetry in Heqb. symmetry in Heqt. apply simpobs in Heqb. apply simpobs in Heqt.
      rewrite Heqb in Href. rewrite Heqt in Href.
      rewrite bind_vis in Href.
      punfold Href. red in Href. cbn in *. inv Href.
      ddestruction. subst. inv H1. auto.
    }
    destruct (classicT (A0 = X0)); try (exfalso; auto; fail).
    unfold eq_rect_r, eq_rect in x. remember (eq_sym e0) as He.
    dependent destruction He. cbn in x. injection x as Hevans.
    ddestruction. subst. ddestruction. subst. exists k0.
    symmetry in Heqb. apply simpobs in Heqb. rewrite Heqb. reflexivity.
  - unfold peel in x. destruct (observe b) eqn : Heqb; destruct (observe t) eqn : Heqt;
      try destruct e0; cbn in *; dependent destruction x.
    + symmetry in Heqt. apply simpobs in Heqt. rewrite Heqt in Href.
      rewrite tau_eutt in Href. eapply IHHpeel in Href; eauto. unfold peel.
      rewrite Heqb. auto.
    + exfalso. eapply spin_not_vis. pfold. eauto.
    + symmetry in Heqb. symmetry in Heqt. apply simpobs in Heqt.
      apply simpobs in Heqb. setoid_rewrite Heqb. setoid_rewrite tau_eutt.
      rewrite Heqb in Href. rewrite Heqt in Href. repeat rewrite tau_eutt in Href.
      eapply IHHpeel in Href; eauto.
    + symmetry in Heqb. symmetry in Heqt. apply simpobs in Heqb. apply simpobs in Heqt.
      setoid_rewrite Heqb. setoid_rewrite tau_eutt. rewrite Heqb in Href.
      rewrite Heqt in Href. repeat rewrite tau_eutt in Href.
      eapply IHHpeel in Href; eauto.
    + symmetry in Heqt. apply simpobs in Heqt. rewrite Heqt in Href.
      rewrite tau_eutt in Href.
      symmetry in Heqb. apply simpobs in Heqb. rewrite Heqb in Href.
      setoid_rewrite Heqb. eapply IHHpeel in Href; eauto.
    + exfalso. eapply peel_vis_empty_contra; eauto.
    + unfold observe in x. cbn in x. unfold peel_vis in x.
      symmetry in Heqb. symmetry in Heqt. apply simpobs in Heqt.
      apply simpobs in Heqb. rewrite Heqb in Href. rewrite Heqt in Href.
      rewrite bind_vis in Href. punfold Href. red in Href. cbn in *.
      inv Href. ddestruction. subst. inv H1. subst; ddestruction; subst.
      assert (A0 = A0); auto. destruct (classicT (A0 = A0) ); try contradiction.
      unfold eq_rect_r, eq_rect in *. remember (eq_sym e0) as He.
      dependent destruction He. cbn in *. discriminate.
Qed.

Lemma vis_peel_r : forall (E : Type -> Type) (R S A : Type) (e : E A) (a : A)
                          (b : itrace E S) (t : itree E R) (f : R -> itree E S) (k : unit -> itrace E R),
    b ⊑ ITree.bind t f ->
    (peel b t ≈ Vis (evans _ e a) k) -> exists k', (t ≈ Vis e k').
Proof.
  intros E R S A e a b t f k Href Hpeel.
  eapply vis_peel_l in Hpeel as Hpeell; eauto. destruct Hpeell as [k' Hb].
  rewrite Hb in Href. rewrite Hb in Hpeel. clear Hb b. punfold Hpeel. red in Hpeel. cbn in *.
  unfold peel in Hpeel. cbn in *. dependent induction Hpeel.
  - destruct (observe t) eqn : Heqt; dependent destruction x.
    symmetry in Heqt. apply simpobs in Heqt. setoid_rewrite Heqt.
    unfold observe in x. cbn in *. unfold peel_vis in x. destruct (classicT (A = X));
      cbn in *; try discriminate.
    unfold eq_rect_r, eq_rect in x. remember (eq_sym e1) as He.
    dependent destruction He. cbn in *. exists k0.
    rewrite Heqt in Href. rewrite bind_vis in Href. punfold Href. red in Href.
    cbn in *. inv Href. ddestruction; subst. inv H1. ddestruction; subst. reflexivity.
  - destruct (observe t) eqn : Heqt; cbn in *; dependent destruction x.
    + symmetry in Heqt. apply simpobs in Heqt. rewrite Heqt in Href. rewrite tau_eutt in Href.
      setoid_rewrite Heqt. setoid_rewrite tau_eutt. eapply IHHpeel; eauto.
    + unfold observe in x. cbn in x. unfold peel_vis in x.
      destruct (classicT (A = X) ).
      * unfold eq_rect_r, eq_rect in x. remember (eq_sym e1) as He. dependent destruction He.
        cbn in *. discriminate.
      * cbn in x. injection x as Ht1. rewrite Ht1 in Hpeel.
        exfalso. eapply spin_not_vis. pfold. eauto.
Qed.

Lemma peel_cont_vis_eutt: forall (R : Type) (r : R) (E : Type -> Type) (S A : Type) (ev : E A)
                                 (ans : A) (kb : unit -> itree (EvAns E) S) (kt : A -> itree E R),
    (peel_cont (Vis (evans A ev ans) kb) (Vis ev kt) r ≈ peel_cont (kb tt) (kt ans) r).
Proof.
  intros R r E S A ev ans kb kt.
  pfold. cbn. red. unfold observe at 1. cbn in *. unfold peel_cont_vis.
  assert (A = A); auto. destruct (classicT (A = A)); try contradiction.
  unfold eq_rect_r, eq_rect. remember (eq_sym e) as He.
  dependent destruction He. cbn. constructor; auto. unfold peel_cont.
  apply eqitF_r_refl.
Qed.

Lemma peel_cont_refine_t : forall (E : Type -> Type) (R S : Type)
                                  (b : itrace E S) (t : itree E R) (f : R -> itree E S) (r : R)
                                  (Hrutt : b ⊑ ITree.bind t f),
    may_converge r (peel b t) -> peel_cont b t r ⊑ f r.
Proof.
  intros. remember (peel b t) as t'. assert (peel b t ≈ t').
  { subst. reflexivity. }
  clear Heqt'. generalize dependent b. generalize dependent t.
  induction H; intros.
  - rewrite <- H0 in H. clear H0. apply peel_ret_inv in H as Ht.
    rewrite Ht in Hrutt.
    rewrite bind_ret_l in Hrutt.
    rewrite Ht in H.
    unfold peel_cont. cbn. rewrite peel_cont_ret_inv; eauto.
  - rewrite H in H1. clear H.
    destruct e; try contradiction. eapply vis_peel_l in H1 as Hb; eauto.
    eapply vis_peel_r in H1 as Ht; eauto.
    destruct Hb as [kb Hkb]. destruct Ht as [kt Htk].
    rewrite Htk. rewrite Hkb.
    rewrite Hkb in Hrutt. rewrite Htk in Hrutt.
    rewrite Hkb in H1. rewrite Htk in H1.
    apply vis_refine_peel in H1 as Hk.
    rewrite peel_cont_vis_eutt. apply IHmay_converge; auto.
    + rewrite bind_vis in Hrutt. punfold Hrutt. red in Hrutt. cbn in *.
      inv Hrutt. ddestruction; subst.
      assert (RAnsRef E unit A (evans A ev ans) tt ev ans ); auto with itree.
      apply H8 in H. pclearbot. auto.
    + destruct b. symmetry. auto.
Qed.

Ltac fold_eutt := match goal with |- paco2 _ _ ?t1 ?t2 =>
                                    apply pacobot2; change (t1 ≈ t2); auto end.

Ltac fold_peel_cont r := match goal with |- context [peel_cont_ (observe ?b) (observe ?t) ] =>
                                           assert (Hfpc : forall r, peel_cont_ (observe b) (observe t) = peel_cont b t r ); auto; rewrite (Hfpc r);
                                           clear Hfpc end.

Lemma trace_prefix_tau_ret:
  forall (E : Type -> Type) (R S : Type) (r : itrace E S -> itrace E R -> Prop)
         (b : itrace E R) (t : itree E S) (f : S -> itree E R) (r0 : R),
    b ⊑ ITree.bind t f ->
    observe b = RetF r0 ->
    forall t0 : itree E S,
      observe t = TauF t0 ->
      trace_prefixF (upaco2 trace_prefix_ r) (TauF (peel_ (RetF r0) (observe t0))) (RetF r0).
Proof.
  intros E R S r b t f r0 Hrutt Heqb t0 Heqt.
  symmetry in Heqb. symmetry in Heqt.
  apply simpobs in Heqb. apply simpobs in Heqt. rewrite Heqb in Hrutt.
  rewrite Heqt in Hrutt. rewrite tau_eutt in Hrutt.
  apply trace_refine_ret_inv_r in Hrutt. constructor.
  assert (exists s, t0 ≈ Ret s).
  {
    punfold Hrutt. red in Hrutt. dependent induction Hrutt.
    - unfold observe in x. cbn in *. destruct (observe t0) eqn : Ht0; cbn in *; try discriminate.
      exists r1. pfold. red. rewrite Ht0. cbn. auto with itree.
    - unfold observe in x. cbn in *. destruct (observe t0) eqn : Ht0; cbn in *; try discriminate.
      + exists r1. pfold. red. rewrite Ht0. cbn. auto with itree.
      + injection x as Ht1. symmetry in Ht0. apply simpobs in Ht0.
        apply eq_sub_eutt in Ht0 as Ht0'. setoid_rewrite Ht0'.
        setoid_rewrite tau_eutt. eapply IHHrutt; eauto.
        rewrite Ht1. eauto. subst. cbn. unfold ITree.bind. reflexivity.
  }
  destruct H as [s Ht0]. punfold Ht0. red in Ht0. cbn in Ht0.
  clear Heqt Hrutt.
  dependent induction Ht0.
  - rewrite <- x. cbn. punfold Heqb. red in Heqb. cbn in *. inv Heqb; try inv CHECK.
    rewrite H0. auto with itree.
  - rewrite <- x. cbn. constructor. eapply IHHt0; eauto.
Qed.

Lemma trace_prefix_vis_evans: forall (E : Type -> Type) (R S : Type) (r : itrace E S -> itrace E R -> Prop)
                                     (A0 : Type) (ev : E A0) (ans : A0) (k : unit -> itree (EvAns E) R)
                                     (k' : A0 -> itree E S)
                                     (t0 : itree E S) (f : S -> itree E R),
    (forall (a : unit) (b : A0),
        RAnsRef E unit A0 (evans A0 ev ans) a ev b ->
        id
          (upaco2 (rutt_ (REvRef E) (RAnsRef E) eq)
                  bot2) (k a) (ITree.bind (k' b) f)) ->
    (t0 ≈ Vis ev k') ->
    (forall (b : itrace E R) (t : itree E S)
            (f : S -> itree E R),
        b ⊑ ITree.bind t f -> r (peel b t) b) ->
    trace_prefixF (upaco2 trace_prefix_ r)
                  (observe (peel_ (VisF (evans A0 ev ans) k) (observe t0))) (VisF (evans A0 ev ans) k).
Proof.
  intros E R S r A0 ev ans k k' t0 f Hk' Ht0 CIH.
  punfold Ht0. red in Ht0. cbn in *. dependent induction Ht0.
  - rewrite <- x. unfold observe. cbn. unfold peel_vis.
    assert (A0 = A0); auto. destruct (classicT (A0 = A0)); try contradiction.
    unfold eq_rect_r, eq_rect. remember (eq_sym e) as He.
    dependent destruction He. cbn. constructor. right. eapply CIH.
    assert (RAnsRef E unit A0 (evans A0 ev ans) tt ev ans); auto with itree.
    apply Hk' in H0. pclearbot. assert (k1 ans ≈ k' ans); try apply REL.
    rewrite H1. eauto.
  - rewrite <- x. cbn. constructor. eapply IHHt0; eauto.
Qed.

Lemma trace_prefix_vis_evempty: forall (E : Type -> Type) (R S : Type)
                                       (r : itrace E S -> itrace E R -> Prop)
                                       (A0 : Type) (Hempty : A0 -> void) (ev : E A0)
                                       (k : void -> itree (EvAns E) R) (A : Type)
                                       (e0 : E A) (t0 : itree E S) (k' : A -> itree E S),
    eqitF eq true true id
          (upaco2 (eqit_ eq true true id) bot2)
          (observe t0) (VisF e0 k') ->
    trace_prefixF (upaco2 trace_prefix_ r)
                  (observe
                     (peel_ (VisF (evempty A0 Hempty ev) k) (TauF t0)))
                  (VisF (evempty A0 Hempty ev) k).
Proof.
  intros E R S r A0 Hempty ev k A e0 t0 k' Ht0.
  cbn. constructor.
  dependent induction Ht0.
  - rewrite <- x. cbn. constructor.
  - rewrite <- x. cbn. constructor. eapply IHHt0; eauto.
Qed.


Lemma trace_prefix_peel_ret_vis:  forall (E : Type -> Type) (R S : Type)
                                         (r : itrace E S -> itrace E R -> Prop)
                                         (A0 : Type) (ev : E A0) (ans : A0)
                                         (k : unit -> itree (EvAns E) R) (t0 : itree E S)
                                         (s : S),
    t0 ≈ Ret s ->
    trace_prefixF (upaco2 trace_prefix_ r)
                  (observe
                     (peel_ (VisF (evans A0 ev ans) k) (observe t0)))
                  (VisF (evans A0 ev ans) k).
Proof.
  intros E R S r A0 ev ans k t0 s Ht0.
  punfold Ht0. red in Ht0. cbn in *. dependent induction Ht0.
  - rewrite <- x. cbn. remember (go (VisF (evans A0 ev ans) k ) ) as t.
    enough (trace_prefixF (upaco2 trace_prefix_ r) (RetF s) (observe t) ).
    { subst. auto. }
    constructor.
  - rewrite <- x. cbn. constructor. eapply IHHt0; eauto.
Qed.

Lemma trace_prefix_peel_ret_vis_empty: forall (E : Type -> Type) (R S : Type)
                                              (r : itrace E S -> itrace E R -> Prop)
                                              (A0 : Type) (Hempty : A0 -> void) (ev : E A0)
                                              (k : void -> itree (EvAns E) R) (t0 : itree E S)
                                              (s : S),
    t0 ≈ Ret s ->
    trace_prefixF (upaco2 trace_prefix_ r)
                  (observe
                     (peel_ (VisF (evempty A0 Hempty ev) k) (observe t0)))
                  (VisF (evempty A0 Hempty ev) k).
Proof.
  intros E R S r A0 Hempty ev k t0 s Ht0.
  punfold Ht0. red in Ht0. cbn in *. dependent induction Ht0.
  - rewrite <- x. cbn. remember (go (VisF (evempty A0 Hempty ev) k ) ) as t.
    enough (trace_prefixF (upaco2 trace_prefix_ r) (RetF s) (observe t) ).
    { subst. auto. }
    constructor.
  - rewrite <- x. cbn. constructor. eapply IHHt0; eauto.
Qed.

Lemma trace_prefix_peel : forall (E : Type -> Type) (S R : Type) (b : itrace E R) (t : itree E S)
                                 (f : S -> itree E R),
    b ⊑ ITree.bind t f ->
    trace_prefix (peel b t) b.
Proof.
  intros E S R. pcofix CIH. intros b t f Href. pfold. red. unfold peel.
  destruct (observe b) eqn : Heqb; destruct (observe t) eqn : Heqt; cbn.
  - rewrite <- Heqb. auto with itree.
  - eapply trace_prefix_tau_ret; eauto.
  - symmetry in Heqb. symmetry in Heqt. apply simpobs in Heqb. apply simpobs in Heqt.
    rewrite Heqb in Href. rewrite Heqt in Href. rewrite bind_vis in Href.
    pinversion Href.
  - rewrite <- Heqb. auto with itree.
  - constructor. right. eapply CIH. symmetry in Heqb. symmetry in Heqt.
    apply simpobs in Heqb. apply simpobs in Heqt. rewrite Heqb in Href. rewrite Heqt in Href.
    repeat rewrite tau_eutt in Href. eauto.
  - constructor. rewrite <- Heqt. right. eapply CIH.
    symmetry in Heqb. apply simpobs in Heqb. rewrite Heqb in Href.
    rewrite tau_eutt in Href. eauto.
  - destruct e; cbn; rewrite <- Heqb; auto with itree.
  - symmetry in Heqb. apply simpobs in Heqb.
    rewrite Heqb in Href.
    apply trace_refine_vis_l in Href as Hbt. destruct Hbt as [A [e0 [k0 Hvis] ]  ].
    symmetry in Heqt. apply simpobs in Heqt. rewrite Heqt in Hvis.
    rewrite tau_eutt in Hvis.
    assert ((exists B, exists k', exists (e1 : E B) , t0 ≈ Vis e1 k') \/ exists s, t0 ≈ Ret s).
    {
      punfold Hvis. red in Hvis. clear Heqb Heqt.
      dependent induction Hvis.
      - unfold observe in x. cbn in *. destruct (observe t0) eqn : Heqt0; try discriminate.
        + right. exists r0. pfold. red. cbn. rewrite Heqt0. auto with itree.
        + cbn in x. left. exists X0. exists k2. exists e1. symmetry in Heqt0.
          apply simpobs in Heqt0. rewrite Heqt0. reflexivity.
      - unfold observe in x. cbn in *. destruct (observe t0) eqn : Heqt0; try discriminate.
        + right. exists r0. pfold. red. cbn. rewrite Heqt0. auto with itree.
        + injection x as Ht1. symmetry in Heqt0. apply simpobs in Heqt0.
          setoid_rewrite Heqt0. setoid_rewrite tau_eutt. eapply IHHvis; eauto.
          rewrite Ht1. auto.
    }
    destruct H as [ [B [k' [e1 Ht0] ] ] | [s Ht0] ].
    + rewrite Heqt in Href. rewrite tau_eutt in Href.
      rewrite Ht0 in Href. rewrite bind_vis in Href.
      pinversion Href. subst; ddestruction; subst.
      rewrite Ht0 in Hvis. rewrite bind_vis in Hvis. pinversion Hvis.
      subst; ddestruction; subst. clear Heqt Heqb.
      punfold Ht0. red in Ht0. cbn in *.
      destruct e.
      * inv H1. ddestruction; subst. cbn. constructor.
        eapply trace_prefix_vis_evans; eauto with itree.
      * eapply trace_prefix_vis_evempty; eauto.
    + rewrite Heqt in Href. rewrite Ht0 in Href.
      rewrite tau_eutt in Href. rewrite bind_ret_l in Href. clear Hvis.
      destruct e.
      * cbn. constructor. eapply trace_prefix_peel_ret_vis; eauto.
      * cbn. constructor. eapply trace_prefix_peel_ret_vis_empty; eauto.
  - destruct e; cbn; [ | constructor ].
    symmetry in Heqt. apply simpobs in Heqt. rewrite Heqt in Href.
    rewrite bind_vis in Href. symmetry in Heqb. apply simpobs in Heqb.
    rewrite Heqb in Href. pinversion Href. subst; ddestruction; subst.
    inversion H1. ddestruction; subst.
    unfold observe at 1. cbn. unfold peel_vis. assert (A = A); auto.
    destruct (classicT (A = A) ); try contradiction.
    unfold eq_rect_r, eq_rect. remember (eq_sym e) as He.
    dependent destruction He. cbn. constructor. right. eapply CIH.
    ddestruction; subst.
    assert (RAnsRef E unit A (evans A ev ans) tt ev ans ); auto with itree.
    apply H6 in H0. pclearbot. eauto.
Qed.

Lemma peel_bind : forall (E : Type -> Type) (S R : Type) (b : itrace E R) (t : itree E S)
                         (f : S -> itree E R),
    b ⊑ ITree.bind t f -> exists g, (ITree.bind (peel b t) g ≈ b).
Proof.
  intros. apply trace_prefix_bind. eapply trace_prefix_peel; eauto.
Qed.

Lemma peel_lemma : forall E R S (b : itrace E R) (t : itree E S) (f : S -> itree E R),
    (b ⊑ ITree.bind t f) -> trace_prefix (peel b t) b /\ (peel b t ⊑ t).
Proof.
  intros. split; try eapply peel_refine_t; eauto; eapply trace_prefix_peel; eauto.
Qed.

End Peel.

Lemma bind_peel_ret_tau_aux:
  forall (E : Type -> Type) (S R : Type) (f : R -> itree E S)
    (r0 : S) (t0 : itree E R),
    Ret r0 ⊑ ITree.bind t0 f -> exists r : R, t0 ≈ Ret r.
Proof.
  intros E S R f r0 t0 Hrutt.
  punfold Hrutt. red in Hrutt. cbn in *. dependent induction Hrutt.
  - unfold ITree.bind in x. unfold observe in x at 1. cbn in *.
    destruct (observe t0) eqn : Ht0; try discriminate.
    exists r. pfold. red. rewrite Ht0. constructor. auto.
  - unfold observe in x. cbn in x. destruct (observe t0) eqn : Ht0; try discriminate.
    + exists r. pfold. red. rewrite Ht0. constructor. auto.
    + symmetry in Ht0. apply simpobs in Ht0. setoid_rewrite Ht0. setoid_rewrite tau_eutt.
      cbn in x. injection x as Ht2. eapply IHHrutt; auto.
      subst. reflexivity.
Qed.

Lemma decompose_trace_refine_bind : forall (E : Type -> Type) (R S : Type)
                                      (b : itrace E S) (t : itree E R) (f : R -> itree E S),
    b ⊑ t >>= f -> exists b', exists g', (ITree.bind b' g' ≈ b) /\ b' ⊑ t.
Proof.
  destruct classicT_inhabited as [classicT].
  intros. exists (peel classicT b t).
  apply (peel_bind classicT) in H as Heutt. destruct Heutt as [g Heutt].
  exists g. split; auto; eapply (peel_refine_t classicT); apply H.
Qed.

Lemma bind_trigger_refine : forall (E : Type -> Type) (A R : Type) (b : itree (EvAns E) R)
                              (e : E A) (k : A -> itree E R),
    (exists a : A, True) ->
    b ⊑ ITree.bind (ITree.trigger e) k ->
    exists a : A, exists (k' : unit -> itrace E R), b ≈ Vis (evans A e a) k' /\ k' tt ⊑ k a.
Proof.
  intros. rewrite bind_trigger in H0. apply trace_refine_vis in H0 as Hvis.
  destruct Hvis as [X [e' [k' Hbvis] ] ]. setoid_rewrite Hbvis.
  rewrite Hbvis in H0.
  punfold H0. red in H0. cbn in *. inv H0. ddestruction. subst. inv H3; ddestruction; subst.
  - exists a. exists k'. split; try reflexivity. pclearbot.
    assert (RAnsRef E unit A (evans A e a) tt e a ); auto with itree.
    apply H8 in H0. pclearbot. auto.
  - destruct H as [a _]. contradiction.
Qed.
