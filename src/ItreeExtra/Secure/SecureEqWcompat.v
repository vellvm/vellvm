From Coq Require Import Morphisms.

From ITree Require Import
     Axioms
     ITree
     ITreeFacts.

From ITree.Extra Require Import
     Secure.SecureEqHalt
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.


Lemma eqit_secureC_wcompat_id :  forall b1 b2 E R1 R2 (RR : R1 -> R2 -> Prop )
      Label priv l
, wcompatible2 (@secure_eqit_ E R1 R2 Label priv RR b1 b2 l id)
                                         (eqitC RR b1 b2) .
Proof.
  econstructor. pmonauto_itree.
  intros. destruct PR.
  punfold EQVl. punfold EQVr. unfold_eqit. red in REL. red.
  hinduction REL before r; intros; clear t1' t2'; try inv CHECK.
  - genobs_clear t1 ot1. genobs_clear t2 ot2.
    remember (RetF r1) as x.
    hinduction EQVl before r; intros; inv Heqx; eauto with itree.
    remember (RetF r3) as y.
    hinduction EQVr before r; intros; inv Heqy; eauto with itree.
  - remember (TauF t1) as y.
    hinduction EQVl before r; intros; inv Heqy; try inv CHECK; subst; eauto with itree.
    remember (TauF t2) as x.
    hinduction EQVr before r; intros; inv Heqx; try inv CHECK; subst; eauto with itree.
    pclearbot. constructor. gclo. econstructor; eauto with paco.
  - eapply IHREL; eauto.
    remember (TauF t1) as x.
    hinduction EQVl before r; intros; inv Heqx; try inv CHECK; eauto with itree.
    constructor; auto. pclearbot. pstep_reverse.
  - eapply IHREL; eauto.
    remember (TauF t2) as x.
    hinduction EQVr before r; intros; inv Heqx; try inv CHECK; eauto with itree.
    constructor; auto. pclearbot. pstep_reverse.
  - remember (VisF e k1) as x.
    hinduction EQVl before r; intros; inv Heqx; try inv CHECK; eauto with itree.
    ddestruction. subst. remember (VisF e0 k3) as y.
    hinduction EQVr before r; intros; inv Heqy; try inv CHECK; eauto with itree.
    ddestruction. subst. constructor; auto.
    intros. apply gpaco2_clo. pclearbot. econstructor; eauto with itree. apply H.
  - remember (VisF e k1) as x.
    hinduction EQVl before r; intros; inv Heqx; try inv CHECK; subst; eauto with itree.
    ddestruction. subst. pclearbot. remember (TauF t2) as y.
    hinduction EQVr before r; intros; inv Heqy; try inv CHECK; subst; eauto with itree.
    pclearbot.
    unpriv_co. gclo. econstructor; eauto with paco itree. gfinal.
    left. apply H.
  - remember (TauF t1) as x.
    hinduction EQVl before r; intros; inv Heqx; try inv CHECK; subst; eauto with itree.
    remember (VisF e k2) as y.
    hinduction EQVr before r; intros; inv Heqy; try inv CHECK; subst; eauto with itree.
    ddestruction. subst.
    pclearbot. unpriv_co. gclo. econstructor; eauto with paco itree.
    gfinal. left. apply H.
  - remember (VisF e1 k1) as x.
    hinduction EQVl before r; intros; inv Heqx; try inv CHECK; subst; eauto with itree.
    ddestruction. subst. remember (VisF e2 k3) as y.
    hinduction EQVr before r; intros; inv Heqy; try inv CHECK; subst; eauto with itree.
    ddestruction. subst. unpriv_co. gclo. pclearbot.
    econstructor; eauto with itree paco. gfinal. left. apply H.
  - remember (VisF e k1) as x.
    hinduction EQVl before r; intros; inv Heqx; try inv CHECK; eauto with itree.
    ddestruction. subst. pclearbot. unpriv_ind.
    eapply H0; eauto. pstep_reverse.
  - remember (VisF e k2) as x.
    hinduction EQVr before r; intros; inv Heqx; try inv CHECK; eauto with itree.
    ddestruction. subst. pclearbot. unpriv_ind.
    eapply H0; eauto. pstep_reverse.
  - remember (VisF e k1) as x.
    hinduction EQVl before r; intros; inv Heqx; try inv CHECK; eauto with itree.
    ddestruction. subst. remember (TauF t2) as y.
    hinduction EQVr before r; intros; inv Heqy; try inv CHECK; eauto with itree.
    pclearbot. unpriv_halt. gclo. econstructor; eauto with paco.
    pfold. constructor. red; auto.
  - remember (VisF e k2) as x.
    hinduction EQVr before r; intros; inv Heqx; try inv CHECK; eauto with itree.
    ddestruction. subst. remember (TauF t1) as y.
    hinduction EQVl before r; intros; inv Heqy; try inv CHECK; eauto with itree.
    pclearbot. unpriv_halt. gclo. econstructor; eauto with paco.
    pfold. constructor. red; auto.
  - remember (VisF e1 k1) as x.
    hinduction EQVl before r; intros; inv Heqx; try inv CHECK; try contra_size; eauto with itree.
    ddestruction. subst. remember (VisF e2 k3) as y.
    hinduction EQVr before r; intros; inv Heqy; try inv CHECK; eauto with itree.
    ddestruction. subst. unpriv_halt. pclearbot.
    gclo. econstructor 1 with (t1' := Vis e1 k0); eauto with paco itree.
    + pfold. constructor; left; auto.
    + gfinal. left. apply H.
  - remember (VisF e1 k1) as x.
    hinduction EQVl before r; intros; inv Heqx; try inv CHECK; try contra_size; eauto with itree.
    ddestruction. subst. remember (VisF e2 k3) as y.
    hinduction EQVr before r; intros; inv Heqy; try inv CHECK; eauto with itree.
    ddestruction. subst. unpriv_halt. pclearbot.
    gclo. econstructor 1 with (t2' := Vis e2 k4); eauto with paco itree.
    + pfold. constructor. left. auto.
    + gfinal. left. apply H.
Qed.

#[export] Hint Resolve eqit_secureC_mon : paco.

Lemma eqit_secure_shalt_refl : forall E R1 R2 b1 b2 (RR : R1 -> R2 -> Prop) Label priv l A (e : E A) k1 k2,
    (~ leq (priv _ e) l) -> empty A ->
    eqit_secure Label priv RR b1 b2 l (Vis e k1) (Vis e k2).
Proof.
  intros. pfold. red. cbn. unpriv_halt. contra_size.
Qed.

Ltac inv_vis_secure := ddestruction; subst;
   try contradiction; try contra_size.
Ltac clear_trivial :=
  repeat match goal with
  | H : empty ?A, H' : forall a : ?A, ?P |- _ => clear H' end.
Ltac eqit_secureC_halt_cases E := repeat (pclearbot; clear_trivial; match goal with
     | |- _ (TauF _ ) (TauF _) => constructor; gclo; pclearbot
     | |- eqit_secureC ?RR ?Label ?priv ?l ?b1 ?b2 _ ?t1 ?t2 => econstructor; clear_trivial; eauto with paco
     | H : secure_eqitF ?Label ?priv ?RR ?b1 ?b2 ?l _ _ (observe ?t1) _ |- eqit_secure ?Label ?priv ?RR ?b1 ?b2 ?l ?t1 ?t2 => pfold; eauto with itree
     |  H : nonempty ?A |- _ _ (@VisF _ _ _ ?A ?e _ ) => unpriv_co; gclo ; pclearbot
     |  H : nonempty ?A |- _  (@VisF _ _ _ ?A ?e _ ) _ => unpriv_co; gclo ; pclearbot
     |  H : empty ?A |- _ _ (@VisF _ _ _ ?A ?e _ ) => unpriv_halt; gclo ; pclearbot
     |  H : empty ?A |- _ (@VisF _ _ _ ?A ?e _ ) _ => unpriv_halt; gclo ; pclearbot
     | |- eqit_secureC ?RR ?Label ?priv ?l ?b1 ?b2 _ ?t1 ?t2 => econstructor; eauto with paco

     | H : forall a, secure_eqitF ?Label ?priv ?RR ?b1 ?b2 ?l _ _ _ (observe ?t2),
       H1 : observe ?t2 = VisF ?e ?k |- eqit_secure _ _ _ _ _ _ _ (Vis ?e ?k) =>
       rewrite H1 in H; pfold; apply H
     |  HA : empty ?A, HB : empty ?B, ev1 : E ?A |-
                       eqit_secure _ _ _ _ _ _ (go (@VisF _ _ _ ?A _ _ )) (go (@VisF _ _ _ ?B _ _ ))
                       => pfold; red; cbn; unpriv_halt; try contra_size
     |  H : forall a : ?A, paco2 _ bot2 (?k a) ?t |- eqit_secure _ _ _ _ _ _ (?k ?a) (?t)  => red; eauto with itree
     |  H : forall a : ?A, paco2 _ bot2 ?t (?k a) |- eqit_secure _ _ _ _ _ _ ?t (?k ?a)   => red; eauto with itree
     |  H : forall (a : ?A) (b : ?B), paco2 _ bot2 (?k1 a) (?k2 b) |-
                                                                        eqit_secure _ _ _ _ _ _ (?k1 ?a) (?k2 ?b)   => red; eauto with itree
     | H : _ (observe ?t) (VisF ?e1 ?k1) |- _ ?t ?t1 => rewrite itree_eta' in H; apply H
     | a : ?A, H : empty ?A |- _ => contra_size
     | a : ?A |- nonempty ?A => constructor; auto
     | HA : empty ?A, HB : empty ?B, Heq : observe ?t = (@VisF _ _ _ ?A _ _)   |-
         gpaco2 _ _ _ _ (?t ) (go (@VisF _ _ _ ?B _ _))  => gfinal; right; pstep; red; cbn; rewrite Heq; unpriv_halt
     | HA : empty ?A, HB : empty ?B |-
         gpaco2 _ _ _ _ (go (@VisF _ _ _ ?A _ _) ) (go (@VisF _ _ _ ?B _ _))  => gfinal; right; pstep; red; cbn; unpriv_halt
     | H : forall (a : ?A), _ (observe (?k a) ) observe (?t), Heq : observe ?t = VisF ?e ?k1 |-
        eqit_secure _ _ _ _ _ _ (?k ?a) _ => rewrite itree_eta' in Heq; rewrite Heq in H; pfold; apply H
     | H : forall a : ?A, ?P (observe (?k a) ) (observe ?t), Heq : observe ?t = VisF ?e ?k2 |-
                                                        eqit_secure _ _ _ _ _ _ (?k ?a) _ =>
                                          rewrite itree_eta' in Heq; rewrite Heq in H; pfold; apply H
  end;
  clear_trivial)
.

Ltac find_size A :=
  match goal with
  | H : nonempty A |- _ => idtac
  | H : empty A |- _ => idtac
  | |- _ => destruct (classic_empty A); try contra_size end.


Ltac produce_elem H A := inv H; assert (nonempty A); try (constructor; auto with itree; fail).

Ltac fold_secure :=
  change (paco2 (_ ?LB ?priv ?RR ?b ?fls ?l _) ?a) with (eqit_secure LB priv RR b fls l) in *.

(* Specialize some hypothesis with the assumption x *)
Ltac spew x :=
  let T := type of x in
  repeat lazymatch goal with
  | [ H0 : forall (_ : T), _ |- _ ] => specialize (H0 x)
  end.

Lemma eqit_secureC_wcompat_id' :  forall b1 b2 E R1 R2 (RR : R1 -> R2 -> Prop )
      Label priv l,
    wcompatible2 (@secure_eqit_ E R1 R2 Label priv RR b1 b2 l id)
                                         (eqit_secureC RR Label priv l b1 b2) .
Proof.
  econstructor.
  { red. intros. eauto with paco. }
  intros. dependent destruction PR.
  punfold EQVl. punfold EQVr. red in EQVl. red in EQVr. red in REL. red.
  hinduction REL before r; intros; clear t1' t2'; try inv CHECK.
  - remember (RetF r1) as x. hinduction EQVl before r; intros; subst; try inv Heqx; eauto with itree.
    remember (RetF r3) as y. hinduction EQVr before r; intros; subst; try inv Heqy; eauto with itree.
    rewrite itree_eta' at 1. unpriv_ind. eapply H0; eauto.
  - remember (TauF t1) as x. hinduction EQVl before r; intros; subst; try inv Heqx;
    try inv CHECK; eauto with itree.
    + remember (TauF t4) as y. pclearbot.
      (* think I might have a lead on the problem, should H0 have vclo not id here?*)
      hinduction EQVr before r; intros; subst; try inv Heqy;
      try inv CHECK; pclearbot; try fold_secure; eauto with itree.
      * constructor. gclo. econstructor; eauto. gfinal; eauto.
      * unpriv_co. gclo. econstructor; eauto. gfinal; eauto.
      * rewrite itree_eta' at 1. unpriv_ind. eauto.
      * unpriv_halt. gclo. econstructor; eauto. gfinal; eauto.
    + remember (TauF t3) as y. pclearbot.
      hinduction EQVr before r; intros; subst; try inv Heqy;
      try inv CHECK; pclearbot; repeat fold_secure; eauto with itree.
      * unpriv_co. gclo. econstructor; eauto. gfinal; eauto.
      * unpriv_co. gclo. econstructor; eauto. gfinal; eauto.
      * rewrite itree_eta' at 1. unpriv_ind. eauto.
      * unpriv_halt. gclo. econstructor; eauto. gfinal; eauto.
   + remember (TauF t3) as y. pclearbot.
      hinduction EQVr before r; intros; subst; try inv Heqy;
      try inv CHECK; pclearbot; repeat fold_secure; eauto with itree.
      * unpriv_halt. gclo. econstructor; eauto. gfinal; eauto.
      * unpriv_halt. gclo. econstructor; eauto. gfinal; eauto.
      * rewrite itree_eta' at 1. unpriv_ind. eauto.
      * unpriv_halt. contra_size.
 - eapply IHREL; eauto.
   remember (TauF t1) as y. hinduction EQVl before r; intros; inv Heqy; try inv CHECK; eauto with itree.
   + constructor; auto. pclearbot. pstep_reverse.
   + unpriv_ind. pclearbot. pstep_reverse.
   + pclearbot. punfold H.
 - eapply IHREL; eauto.
   remember (TauF t2) as y. hinduction EQVr before r; intros; inv Heqy; try inv CHECL; eauto with itree.
   + constructor; auto. pclearbot. pstep_reverse.
   + unpriv_ind. pclearbot. pstep_reverse.
   + pclearbot. punfold H.
 - remember (VisF e k1) as x.
   hinduction EQVl before r; intros; inv Heqx; try inv CHECK; inv_vis_secure; eauto with itree.
   remember (VisF e0 k3) as y.
   hinduction EQVr before r; intros; inv Heqy; try inv CHECK; inv_vis_secure; eauto with itree.
   + pclearbot. constructor; auto. intros. gclo. econstructor; eauto.
     apply H0. apply H. gfinal; left; apply H1.
   + rewrite itree_eta' at 1. unpriv_ind. eapply H0; eauto.
 - unfold id in H. remember (VisF e k1) as x.
   hinduction EQVl before r; intros; inv Heqx; try inv CHECK; inv_vis_secure; eauto with itree.
   + pclearbot. remember (TauF t2) as y.
     hinduction EQVr before r; intros; inv Heqy; try inv CHECK; repeat fold_secure; eauto with itree.
     * constructor. gclo. pclearbot. inv SIZECHECK. spew a. econstructor; eauto. gfinal; eauto.
     * unpriv_co. gclo. pclearbot. inv SIZECHECK0. spew a0; spew a. econstructor; eauto.
       gfinal; eauto.
     * rewrite itree_eta' at 1. unpriv_ind. eauto.
     * unpriv_halt. pclearbot. inv SIZECHECK0.
       gclo. spew a. econstructor; eauto. gfinal; eauto.
   + pclearbot. pclearbot. inv SIZECHECK. remember (TauF t2) as y.
     hinduction EQVr before r; intros; inv Heqy; try inv CHECK; repeat fold_secure; eauto with itree.
     * unpriv_co. gclo. pclearbot. spew a0. spew a. econstructor; eauto. gfinal; eauto.
     * unpriv_co. gclo. pclearbot. fold_secure. spew a0; spew a. econstructor; eauto. gfinal; eauto.
     * rewrite itree_eta' at 1. unpriv_ind. eauto.
     * pclearbot. unpriv_halt. gclo. spew a0. spew a. econstructor; eauto. gfinal; eauto.
  + pclearbot. inv SIZECHECK0. remember (TauF t2) as y.
     hinduction EQVr before r; intros; inv Heqy; try inv CHECK; repeat fold_secure; eauto with itree.
     * unpriv_halt. gclo. pclearbot. spew a; econstructor; eauto.
       gfinal; eauto.
     * unpriv_halt. gclo. pclearbot. fold_secure. spew a. econstructor; eauto. gfinal; eauto.
     * rewrite itree_eta' at 1. unpriv_ind. eauto.
     * pclearbot. unpriv_halt. contra_size.
 - unfold id in H. remember (VisF e k2) as x.
   hinduction EQVr before r; intros; inv Heqx; try inv CHECK; inv_vis_secure; eauto with itree.
   + pclearbot. remember (TauF t0) as y.
     hinduction EQVl before r; intros; inv Heqy; try inv CHECK; eauto with itree; repeat fold_secure.
     * constructor. gclo. pclearbot. fold_secure. inv SIZECHECK.
       spew a; econstructor; eauto. gfinal; eauto.
     * unpriv_co. gclo. pclearbot. fold_secure. inv SIZECHECK0. spew a; spew a0. econstructor; eauto.
       gfinal; eauto.
     * rewrite itree_eta'. unpriv_ind. eauto.
     * unpriv_halt. pclearbot. inv SIZECHECK0.
       gclo. spew a; econstructor; eauto. gfinal; eauto.
   + pclearbot. pclearbot. inv SIZECHECK. remember (TauF t1) as y.
     hinduction EQVl before r; intros; inv Heqy; try inv CHECK; repeat fold_secure; eauto with itree.
     * unpriv_co. gclo. pclearbot. spew a0; spew a. econstructor; eauto. gfinal; eauto.
     * unpriv_co. gclo. pclearbot. spew b; spew a; spew a0; econstructor; eauto.
       gfinal; eauto.
     * rewrite itree_eta'. unpriv_ind. eauto.
     * pclearbot. unpriv_halt. gclo. spew a. econstructor; eauto. gfinal; eauto.
  + pclearbot. inv SIZECHECK0. remember (TauF t1) as y.
     hinduction EQVl before r; intros; inv Heqy; try inv CHECK; eauto with itree.
     * unpriv_halt. gclo. pclearbot. fold_secure. spew a. econstructor; eauto.
       gfinal; eauto.
     * unpriv_halt. gclo. pclearbot. fold_secure. spew a. econstructor; eauto.
       gfinal; eauto.
     * rewrite itree_eta'. unpriv_ind. eauto.
     * pclearbot. unpriv_halt. contra_size.
 - unfold id in H. remember (VisF e2 k2) as x.
   hinduction EQVr before r; intros; inv Heqx; try inv CHECK; inv_vis_secure; eauto with itree; pclearbot; fold_secure.
   1: inv SIZECHECK1; inv SIZECHECK2; remember (VisF e1 k1) as y.
   2: inv SIZECHECK0; inv SIZECHECK3; remember (VisF e0 k0) as y.
   3: inv SIZECHECK1; inv SIZECHECK2; remember (VisF e0 k0) as y.
   all: spew a; spew a0.
   all: hinduction EQVl before r; intros; inv Heqy; try inv CHECK; inv_vis_secure; subst;
     eauto with itree; try (eqit_secureC_halt_cases E; fail).
   all: rewrite itree_eta'; unpriv_ind; auto with itree; eauto.
 - inv SIZECHECK. eapply H0; eauto. Unshelve. all : auto.
   remember (VisF e k1) as x. clear H0.
   hinduction EQVl before r; intros; inv Heqx; inv_vis_secure; try inv CHECK; pclearbot; eauto with itree.
   + constructor; auto. pstep_reverse.
   + unpriv_ind. pstep_reverse.
   + rewrite itree_eta' at 1 . pstep_reverse.
 - inv SIZECHECK. eapply (H0 a); eauto.
   remember (VisF e k2) as x. clear H0.
   hinduction EQVr before r; intros; inv Heqx; inv_vis_secure; try inv CHECK; pclearbot; eauto with itree.
   + constructor; auto. pstep_reverse.
   + unpriv_ind. pstep_reverse.
   + rewrite itree_eta' at 1 . pstep_reverse.
 - remember (TauF t2) as x.
   hinduction EQVr before r; intros; inv Heqx; try inv CHECK; pclearbot; eauto with itree;
   inv EQVl; inv_vis_secure; eqit_secureC_halt_cases E.
   + pclearbot. find_size A0; eqit_secureC_halt_cases E.
   + pclearbot. find_size A1; eqit_secureC_halt_cases E.
 - remember (TauF t1) as x.
   hinduction  EQVl before r; intros; inv Heqx; try inv CHECK; pclearbot; eauto with itree;
   inv EQVr; inv_vis_secure;
   eqit_secureC_halt_cases E.
   + find_size A0; eqit_secureC_halt_cases E.
   + find_size A1; eqit_secureC_halt_cases E.
 - unfold id in H. remember (VisF e2 k2) as x.
   hinduction EQVr before r; intros; inv Heqx; try inv CHECK; inv_vis_secure;  pclearbot; eauto with itree;
   inv EQVl; inv_vis_secure;
   (* maybe I should just write a new one *)
   do 2 (
   repeat match goal with | H : nonempty ?A |- _ => inv H end;
   match goal with
   | e1 : E ?A, e2 : E ?B, e3 : E ?C, e4 : E ?D |- _ =>
     find_size A ; find_size B; find_size C ; find_size D ; try contra_size
   | e1 : E ?A, e2 : E ?B, e3 : E ?C |- _ =>
     find_size A ; find_size B; find_size C ; try contra_size
   | e1 : E ?A, e2 : E ?B |- _ =>
      find_size A ; find_size B; try contra_size
   | e1 : E ?A |- _ =>
     find_size A ; try contra_size
   end);
   eqit_secureC_halt_cases E; try (eapply eqit_secure_shalt_refl; eauto); eqit_secureC_halt_cases E;
   try apply H3; try apply H; eqit_secureC_halt_cases E.
   Unshelve. all : auto.
 - unfold id in H. remember (VisF e1 k1) as x.
   hinduction EQVl before r; intros; inv Heqx; try inv CHECK; inv_vis_secure; pclearbot; eauto with itree;
     inv EQVr; inv_vis_secure;
       do 2 (
            repeat match goal with | H : nonempty ?A |- _ => inv H end;
            match goal with
            | e1 : E ?A, e2 : E ?B, e3 : E ?C, e4 : E ?D |- _ =>
              find_size A ; find_size B; find_size C ; find_size D ; try contra_size
            | e1 : E ?A, e2 : E ?B, e3 : E ?C |- _ =>
              find_size A ; find_size B; find_size C ; try contra_size
            | e1 : E ?A, e2 : E ?B |- _ =>
              find_size A ; find_size B; try contra_size
            | e1 : E ?A |- _ =>
              find_size A ; try contra_size
            end);
       eqit_secureC_halt_cases E; try (eapply eqit_secure_shalt_refl; eauto); eqit_secureC_halt_cases E;
   try apply H3; try apply H; eqit_secureC_halt_cases E.
   Unshelve. all: auto.
Qed.

#[export] Hint Resolve eqit_secureC_wcompat_id : paco.

#[global] Instance geuttgen_cong_secure_eqit {E} {Label priv l} {R1 R2 : Type} {RR1 : R1 -> R1 -> Prop}
    {RR2 : R2 -> R2 -> Prop} {RS : R1 -> R2 -> Prop} (b1 b2 : bool) {r rg} :
    (forall (x x' : R1) (y : R2), (RR1 x x' : Prop) -> (RS x' y : Prop) -> RS x y) ->
    (forall (x : R1) (y y' : R2), (RR2 y y' : Prop) -> RS x y' -> RS x y) ->
    Proper (@eq_itree E R1 R1 RR1 ==> eq_itree RR2 ==> flip impl)
           (gpaco2 (secure_eqit_ Label priv RS b1 b2 l id) (eqitC RS b1 b2) r rg ).
Proof.
  repeat intro. gclo. econstructor; eauto.
  - eapply eqit_mon, H1; eauto; discriminate.
  - eapply eqit_mon, H2; eauto; discriminate.
Qed.

#[global] Instance geuttgen_cong_secure_eqit' {E} {Label priv l} {R1 R2 : Type} {RR1 : R1 -> R1 -> Prop}
    {RR2 : R2 -> R2 -> Prop} {RS : R1 -> R2 -> Prop} (b1 b2 : bool) {r rg} :
    (forall (x x' : R1) (y : R2), (RR1 x x' : Prop) -> (RS x' y : Prop) -> RS x y) ->
    (forall (x : R1) (y y' : R2), (RR2 y y' : Prop) -> RS x y' -> RS x y) ->
    Proper (@eqit_secure E R1 R1 Label priv RR1 false false l ==>
             eqit_secure Label priv RR2 false false l ==> flip impl)
           (gpaco2 (secure_eqit_ Label priv RS b1 b2 l id) (eqit_secureC RS Label priv l b1 b2) r rg ).
Proof.
  repeat intro. gclo. econstructor; eauto.
  - eapply secure_eqit_mon, H1; eauto. intros; discriminate.
  - eapply secure_eqit_mon, H2; eauto. intros; discriminate.
Qed.

#[global] Instance geutt_cong_euttge:
  forall {E : Type -> Type} Label priv l b1 b2 {R1 R2 : Type} {RR1 : R1 -> R1 -> Prop}
    {RR2 : R2 -> R2 -> Prop} {RS : R1 -> R2 -> Prop}
    (r rg : forall x : itree E R1, (fun _ : itree E R1 => itree E R2) x -> Prop),
  (forall (x x' : R1) (y : R2), (RR1 x x' : Prop) -> (RS x' y : Prop) -> RS x y) ->
  (forall (x : R1) (y y' : R2), (RR2 y y' : Prop) -> RS x y' -> RS x y) ->
  Proper (euttge RR1 ==> euttge RR2 ==> flip impl)
    (gpaco2 (secure_eqit_ Label priv RS b1 b2 l id) (eqitC RS true true) r rg).
Proof.
  repeat intro. gclo. econstructor; eauto.
Qed.

#[global] Instance geutt_eq_cong_euttge:
  forall {E : Type -> Type} Label priv l b1 b2 {R1 R2 : Type} r rg RS ,
    Proper ( @euttge E R1 R1 eq ==> @euttge E R2 R2 eq ==> flip impl)
           (gpaco2 (secure_eqit_ Label priv RS b1 b2 l id) (eqitC RS true true) r rg ).
Proof.
  repeat intro. eapply geutt_cong_euttge; eauto; intros; subst; auto.
Qed.
