(* begin hide *)
From ITree Require Import
     ITree
     ITreeFacts
     Basics.HeterogeneousRelations
     Events.State
     Events.StateFacts
     InterpFacts
     KTreeFacts
     Core.ITreeMonad
     CategoryKleisli
     CategoryKleisliFacts
     Eq.Eq.

From ExtLib Require Import
     Structures.Functor.

From Coq Require Import
     RelationClasses
     Strings.String
     Logic
     Morphisms
     Relations
     List
     Program.Tactics.

From ITree Require Import
     Basics.Monad
     Basics.MonadState.

From Vellvm Require Import
     Utils.PropT.
Require Import Paco.paco.

Import ListNotations.
Import ITree.Basics.Basics.Monads.


Import MonadNotation.
Import CatNotations.
Local Open Scope monad_scope.
Local Open Scope cat_scope.
(* end hide *)

Section interp_prop.

  (* Definition 5.3: Handler Correctness *)
  Definition handler_correct {E F} (h_spec: E ~> PropT F) (h: E ~> itree F) :=
    (forall T e, h_spec T e (h T e)).

  Lemma case_prop_handler_correct:
    forall {E1 E2 F}
      (h1_spec: E1 ~> PropT F)
      (h2_spec: E2 ~> PropT F)
      (h1: E1 ~> itree F)
      (h2: E2 ~> itree F)
      (C1: handler_correct h1_spec h1)
      (C2: handler_correct h2_spec h2),
      handler_correct (case_ h1_spec h2_spec) (case_ h1 h2).
  Proof.
    intros E1 E2 F h1_spec h2_spec h1 h2 C1 C2.
    unfold handler_correct in *.
    intros T e.
    destruct e. apply C1. apply C2.
  Qed.

  Definition k_spec_correct
             {E F}
             (h: E ~> itree F)
             (k_spec : forall T R, E T -> itree F T -> (T -> itree E R) -> (T -> itree F R) -> itree F R -> Prop) : Prop
    := forall T R e k1 k2 t2, t2 ≈ bind (h T e) k2 -> k_spec T R e (h T e) k1 k2 t2.

  Inductive interp_PropTF {E F}
            (h_spec : E ~> PropT F)
            (k_spec : forall T R, E T -> itree F T -> (T -> itree E R) -> (T -> itree F R) -> itree F R -> Prop)
            {R : Type} (RR : relation R) (sim : itree E R -> itree F R -> Prop)
            : itree' E R -> itree F R -> Prop :=
  | Interp_PropT_Ret : forall r1 r2 (REL: RR r1 r2),
      interp_PropTF h_spec k_spec RR sim (RetF r1) (Ret r2)

  | Interp_PropT_Tau : forall t1 t2 (HS: sim t1 t2),
      interp_PropTF h_spec k_spec RR sim (TauF t1) (Tau t2)

  | Interp_PropT_TauP : forall t1 t2 (HS: interp_PropTF h_spec k_spec RR sim (observe t1) t2),
      interp_PropTF h_spec k_spec RR sim (TauF t1) t2

  | Interp_PropT_Vis : forall A (e : E A) (k1 : A -> itree E R)
                         (t2 : itree F R)

                         (ta :itree F A)
                         (k2 : A -> itree F R)

                         (HTA: h_spec A e ta)
                         (HK : forall (a : A), Returns a ta ->  sim (k1 a) (k2 a))

                         (* k_spec => t2 ≈ bind ta k2 *)
                         (* k_spec => True *)
                         (KS : k_spec A R e ta k1 k2 t2), 
      interp_PropTF h_spec k_spec RR sim (VisF e k1) t2.

  Hint Constructors interp_PropTF : core.

  Lemma interp_PropTF_mono E F h_spec k_spec R RR  (t0 : itree' E R) (t1 : itree F R) sim sim'
        (IN : interp_PropTF h_spec k_spec RR sim t0 t1)
        (LE : sim <2= sim') : 
    (interp_PropTF h_spec k_spec RR sim' t0 t1).
  Proof.
    induction IN; eauto.
  Qed.

  Hint Resolve interp_PropTF_mono : paco.

  Definition interp_PropT_ E F h_spec k_spec R RR sim (t0 : itree E R) (t1 : itree F R) :=
    interp_PropTF h_spec k_spec RR sim (observe t0) t1.
  Hint Unfold interp_PropT_ : core.

  Lemma interp_PropT__mono E F h_spec k_spec R RR : monotone2 (interp_PropT_ E F h_spec k_spec R RR).
  Proof.
    do 2 red. intros. eapply interp_PropTF_mono; eauto.
  Qed.
  Hint Resolve interp_PropT__mono : paco.

  (* Definition 5.2 *)
  Definition interp_prop {E F}
            (h_spec : E ~> PropT F)
            (k_spec : forall T R, E T -> itree F T -> (T -> itree E R) -> (T -> itree F R) -> itree F R -> Prop)
    :
    forall R (RR: relation R), itree E R -> PropT F R :=
      fun R (RR: relation R) =>  paco2 (interp_PropT_ E F h_spec k_spec R RR) bot2.

  (* #[global] Instance interp_PropTF_Proper *)
  (*  {E F} *)
  (*  (h_spec : E ~> PropT F) *)
  (*  (k_spec : forall T R, E T -> itree F T -> (T -> itree E R) -> (T -> itree F R) -> itree F R -> Prop) *)
  (*  R RR (t : itree' E R) *)
  (*        (sim : itree E R -> itree F R -> Prop) *)
  (*        (HS: forall t, Proper(eutt eq ==> flip impl) (sim t)) *)
  (*        (KS: forall A R e ta k1 k2, Proper (eutt eq ==> flip impl) (k_spec A R e ta k1 k2)) *)
  (*   :  *)
  (*   Proper(eutt eq ==> iff) (interp_PropTF h_spec k_spec RR sim t). *)
  (* Proof. *)
  (*   do 2 red. *)
  (*   intros. *)
  (*   split; intros. *)
  (*   - inversion H0; subst; econstructor; eauto. *)
  (*     + rewrite <- H. assumption. *)
  (*     + specialize (HS t1). rewrite <- H. assumption. *)
  (*     + (* h_spec now depends on the tree `t2`, so we need to show that it respects x ≈ y *) *)
  (*       (* Not a guarantee, depends on what h_spec is... So we need a proper instance for that *) *)
  (*       rewrite <- H; auto. *)
  (*   - inversion H0; subst; econstructor; eauto. *)
  (*     rewrite H. assumption. specialize (HS t1). rewrite H. assumption. *)
  (*     rewrite H. assumption. *)
  (* Qed. *)
  (* Figure 7: Interpreter law for Ret *)
  Lemma interp_prop_ret :
    forall R E F
      (h_spec : E ~> PropT F)
      (k_spec : forall T R, E T -> itree F T -> (T -> itree E R) -> (T -> itree F R) -> itree F R -> Prop)
      (r : R)
    , Eq1_PropT _ (interp_prop h_spec k_spec R eq (ret r)) (ret r).
  Proof.
    intros.
    repeat red.
    split; [| split].
    - intros. split; intros.
      + unfold interp_prop in H0.
        pinversion H0. subst.
        cbn. rewrite <- H. reflexivity.
      + pstep. red. do 2 red in H0.
        rewrite H0 in H.

   (*      rewrite H. eapply Interp_PropT_Ret. cbn. econstructor. reflexivity. rewrite H. cbn in H0. assumption. *)
   (*  - do 3 red. *)
   (*    intros t1 t2 eq; split; intros H; pinversion H; subst. *)
   (*    + red. pstep. econstructor. reflexivity. rewrite <- eq. assumption. *)
   (*    + red. pstep. econstructor. reflexivity. rewrite eq. assumption. *)
   (* - do 3 red. intros. split; intros; cbn in *. rewrite <- H. assumption. rewrite H; assumption. *)
  Admitted.

  #[global] Instance interp_prop_Proper
   {E F}
   (h_spec : E ~> PropT F)
   (k_spec : forall T R, E T -> itree F T -> (T -> itree E R) -> (T -> itree F R) -> itree F R -> Prop)
   R RR (t : itree E R)
   (KS: forall A R e ta k1 k2, Proper (eutt eq ==> flip impl) (k_spec A R e ta k1 k2)) :
    Proper(eq_itree Logic.eq ==> iff) (interp_prop h_spec k_spec R RR t).
  Proof.
    do 2 red.
    intros.
    split.
    - revert t x y H.
      pcofix CIH.
      intros t x y eq HI.
      red in HI. punfold HI. red in HI.
      pstep. red. genobs t ot.
    (*   inversion HI; subst; econstructor; eauto. *)
    (*   + rewrite <- eq. assumption. *)
    (*   + pclearbot. right. eapply CIH; eauto. *)
    (*   + intros. specialize (HK a H0). pclearbot. right. eapply CIH. 2 : { apply HK. } reflexivity. *)
    (*   + rewrite <- eq. eauto. *)
    (* - revert t x y H. *)
    (*   pcofix CIH. *)
    (*   intros t x y eq HI. *)
    (*   red in HI. punfold HI. red in HI. *)
    (*   pstep. red. genobs t ot. *)
    (*   inversion HI; subst; econstructor; eauto. *)
    (*   + rewrite eq. assumption. *)
    (*   + pclearbot. right. eapply CIH; eauto. *)
    (*   + intros. specialize (HK a H0). pclearbot. right. eapply CIH. 2 : { apply HK. } reflexivity. *)
      (*   + rewrite eq. eauto. *)
  Admitted.

  #[global] Instance interp_prop_Proper2
   {E F}
   (h_spec : E ~> PropT F)
   (k_spec : forall T R, E T -> itree F T -> (T -> itree E R) -> (T -> itree F R) -> itree F R -> Prop)
   R RR (t : itree E R)
   (KS: forall A R e ta k1 k2, Proper (eutt eq ==> flip impl) (k_spec A R e ta k1 k2)) :
    Proper(eutt Logic.eq ==> iff) (interp_prop h_spec k_spec R RR t).
  Proof.
    do 2 red.
    intros.
    split.
    - revert t x y H.
      pcofix CIH.
      intros t x y eq HI.
      red in HI. punfold HI. red in HI.
      pstep. red. genobs t ot.
    (*   inversion HI; subst; econstructor; eauto. *)
    (*   + rewrite <- eq. assumption. *)
    (*   + pclearbot. right. eapply CIH; eauto. *)
    (*   + intros. specialize (HK a H0). pclearbot. right. eapply CIH. 2 : { apply HK. } reflexivity. *)
    (*   + rewrite <- eq. eauto. *)
    (* - revert t x y H. *)
    (*   pcofix CIH. *)
    (*   intros t x y eq HI. *)
    (*   red in HI. punfold HI. red in HI. *)
    (*   pstep. red. genobs t ot. *)
    (*   inversion HI; subst; econstructor; eauto. *)
    (*   + rewrite eq. assumption. *)
    (*   + pclearbot. right. eapply CIH; eauto. *)
    (*   + intros. specialize (HK a H0). pclearbot. right. eapply CIH. 2 : { apply HK. } reflexivity. *)
      (*   + rewrite eq. eauto. *)
  Admitted.

  (* TODO: Move this *)
  Lemma eqit_flip_symmetric {E R} (RR : R -> R -> Prop) `{Symmetric R RR} b1 b2:
    forall (u : itree E R) (v : itree E R),
      eqit RR b1 b2 u v -> eqit (flip RR) b1 b2 u v.
  Proof.
    pcofix self; pstep. intros u v euv. punfold euv.
    red in euv |- *. induction euv; pclearbot; eauto 7 with paco.
  Qed.

  #[global] Instance interp_prop_Proper3
   {E F} {a b}
   (h_spec : E ~> PropT F)
   (k_spec : forall T R, E T -> itree F T -> (T -> itree E R) -> (T -> itree F R) -> itree F R -> Prop)
   (KP : forall T R RR b a, Proper (eq ==> eq ==> (fun k1 k2 => forall x, eqit RR b a (k1 x) (k2 x)) ==> eq ==> eq ==> iff) (k_spec T R))
   R RR :
    Proper(eqit eq a b ==> eq  ==> iff) (interp_prop h_spec k_spec R RR).
  Proof.
    do 4 red.
    intros; split.
    - subst.
      revert x y H y0.
      pcofix CIH.
      intros x y eq t H.
      pstep; red.
      punfold H. red in H.

      punfold eq. red in eq.
      genobs x obsx.
      genobs y obsy.
      revert x y Heqobsx Heqobsy t H.

      induction eq; intros x y Heqobsx Heqobsy t H; inversion H; subst; pclearbot.
      + econstructor; eauto.
      + econstructor. right. eapply CIH. apply REL. apply HS.
   (*    + apply inj_pair2 in H2. *)
   (*      apply inj_pair2 in H3. subst. *)
   (*      econstructor; eauto. intros X HX. specialize (REL X). specialize (HK X HX). pclearbot. *)
   (*      right. *)

   (*      eapply CIH; eauto. *)
   (*      eapply KP; eauto. *)
   (*      intros. *)
   (*      eapply eqit_flip; *)
   (*      eapply eqit_flip_symmetric; eauto; typeclasses eauto. *)
   (*    + eapply IHeq.  reflexivity. reflexivity. *)
   (*      punfold HS. *)
   (*    + econstructor. left. pstep. eapply IHeq. reflexivity. reflexivity. assumption. *)
   (*    + econstructor. left.  pstep. eapply IHeq. reflexivity. reflexivity. assumption. *)
   (*    + econstructor. left.  pstep. eapply IHeq. reflexivity. reflexivity. assumption. *)

   (* - subst. *)
   (*    revert x y H y0. *)
   (*    pcofix CIH. *)
   (*    intros x y eq t H. *)
   (*    pstep; red. *)
   (*    punfold H. red in H. *)

   (*    punfold eq. red in eq. *)
   (*    genobs x obsx. *)
   (*    genobs y obsy. *)
   (*    revert x y Heqobsx Heqobsy t H. *)

   (*    induction eq; intros x y Heqobsx Heqobsy t H; inversion H; subst; pclearbot. *)
   (*    + econstructor; eauto. *)
   (*    + econstructor. right. eapply CIH. apply REL. apply HS. *)
   (*    + apply inj_pair2 in H2. *)
   (*      apply inj_pair2 in H3. subst. *)
   (*      econstructor; eauto. intros X HX. specialize (REL X). specialize (HK X HX). pclearbot. *)
   (*      right. *)

   (*      eapply CIH; eauto. *)
   (*      eapply KP; eauto. *)
   (*    + econstructor. left. pstep. eapply IHeq. reflexivity. reflexivity. assumption. *)
   (*    + econstructor. left. pstep. eapply IHeq. reflexivity. reflexivity. assumption. *)
   (*    + econstructor. left. pstep. eapply IHeq. reflexivity. reflexivity. assumption. *)
        (*    + eapply IHeq. reflexivity. reflexivity.   punfold HS. *)
  Admitted.

    Lemma interp_prop_ret_pure :
      forall {T E F} (RR : relation T) `{REF: Reflexive _ RR} (x : T)
        (h : E ~> PropT F)
        (k_spec : forall T R, E T -> itree F T -> (T -> itree E R) -> (T -> itree F R) -> itree F R -> Prop),
      interp_prop h k_spec _ RR (ret x) (ret x).
    Proof.
      intros T E F RR REF x h k_spec.
      generalize dependent x.
      pcofix CIH.
      intros x.
      pstep.
      cbn.
      econstructor.
      reflexivity.
    Qed.
 
    Lemma interp_prop_ret_refine :
      forall {T E F} (RR : relation T) (x y : T)
        (h : E ~> PropT F)
        (k_spec : forall T R, E T -> itree F T -> (T -> itree E R) -> (T -> itree F R) -> itree F R -> Prop),
        RR x y ->
        interp_prop h k_spec _ RR (ret x) (ret y).
    Proof.
      intros T E F RR x y h k_spec RRxy.
      generalize dependent y.
      generalize dependent x.
      pcofix CIH.
      intros x y RRxy.
      pstep.
      cbn.
      econstructor; eauto.
    Qed.

    Lemma interp_prop_refl_h :
      forall {T E} (RR : relation T) `{REF: Reflexive _ RR} (t1 t2 : itree E T)
        (h : E ~> PropT E)
        (k_spec : forall T R, E T -> itree E T -> (T -> itree E R) -> (T -> itree E R) -> itree E R -> Prop),
        (forall {X : Type} (e : E X), h X e (trigger e)) ->
        (k_spec_correct (fun T e => trigger e) k_spec) ->
        t1 ≈ t2 ->
        interp_prop h k_spec _ RR t1 t2.
    Proof.
      intros T E RR REF t1 t2 h k_spec H_SPEC K_SPEC EQ.
      generalize dependent t2.
      generalize dependent t1.
      pcofix CIH.
      intros t1 t2 EQ.
      pose proof (itree_eta t1) as ETA.
      destruct (observe t1) eqn:Ht1.
      - pstep.
        red.
        rewrite Ht1.
      (*   econstructor. *)
      (*   reflexivity. *)
      (*   rewrite <- EQ. *)
      (*   rewrite ETA. *)
      (*   reflexivity. *)
      (* - pstep. *)
      (*   red. *)
      (*   rewrite Ht1. *)
      (*   econstructor. *)
      (*   right. *)
      (*   apply CIH; auto. *)
      (*   rewrite <- tau_eutt. *)
      (*   rewrite <- ETA. *)
      (*   auto. *)
      (* - pstep. *)
      (*   red. *)
      (*   rewrite Ht1. *)
      (*   eapply Interp_PropT_Vis with (k2 := k). *)
      (*   + eauto. *)
      (*   + intros a RET. *)
      (*     right. *)
      (*     apply CIH. *)
      (*     reflexivity. *)
      (*   + eapply K_SPEC. rewrite <- EQ. *)
      (*     setoid_rewrite bind_trigger. *)
      (*     cbn. *)
      (*     rewrite ETA. *)
        (*     reflexivity. *)
    Admitted.

    Lemma interp_prop_refl :
      forall {T E} (RR : relation T) `{REF: Reflexive _ RR} (t : itree E T)
        (h : forall X : Type, E X -> PropT E X)
        (k_spec : forall T R, E T -> itree E T -> (T -> itree E R) -> (T -> itree E R) -> itree E R -> Prop),
        (forall {X : Type} (e : E X), h X e (trigger e)) ->
        (k_spec_correct (fun T e => trigger e) k_spec) ->
        interp_prop h k_spec _ RR t t.
    Proof.
      intros T E RR REF t h k_spec H_SPEC K_SPEC.
      apply interp_prop_refl_h; eauto.
      reflexivity.
    Qed.

  (* Lemma 5.4: interp_prop_correct - note that the paper presents a slightly simpler formulation where t = t' *)
  Lemma interp_prop_correct_exec:
    forall {E F}
      (h_spec : E ~> PropT F)
      (k_spec : forall T R, E T -> itree F T -> (T -> itree E R) -> (T -> itree F R) -> itree F R -> Prop)
      (h: E ~> itree F)
      (HC : handler_correct h_spec h)
      (KC : k_spec_correct h k_spec),
      forall R RR `{Reflexive _ RR} t t', t ≈ t' -> interp_prop h_spec k_spec R RR t (interp h t').
  Proof.
    intros E F h_spec k_spec h HC KC R RR H t t' H1.
    revert t t' H1.
    pcofix CIH.
    intros t t' eq.
    pstep.
    red.
    unfold interp, Basics.iter, MonadIter_itree.
    rewrite (itree_eta t) in eq.
    destruct (observe t).
    (* - econstructor. reflexivity. rewrite <- eq. rewrite unfold_iter. cbn. rewrite Eq.bind_ret_l. cbn.  reflexivity. *)
    (* - econstructor. right. *)
    (*   eapply CIH. rewrite tau_eutt in eq. rewrite eq. reflexivity. *)
    (* - econstructor. *)
    (*   apply HC. *)
    (*   intros a. cbn.   *)
    (*   right. *)
    (*   unfold interp, Basics.iter, MonadIter_itree in CIH. unfold fmap, Functor_itree, ITree.map in CIH. *)
    (*   specialize (CIH (k a) (k a)). *)
    (*   apply CIH. *)
    (*   reflexivity. *)

    (*   unfold k_spec_correct in KC. *)
      
    (*   eapply KC. *)
    (*   rewrite <- eq. *)
    (*   rewrite unfold_iter. *)
    (*   cbn. *)

    (*   rewrite bind_map. *)
    (*   eapply eutt_clo_bind. *)
    (*   reflexivity. *)
    (*   intros u1 u2 H0; subst. *)

    (*   rewrite tau_eutt. *)
    (*   reflexivity. *)
  Admitted.

  (* Lemma 5.5 - note that the paper presents this lemma after unfolding the definition of Proper.
   *)
  Instance interp_prop_Proper_eq :
    forall R (RR : relation R) (HR: Reflexive RR) (HT : Transitive RR) E F
      (h_spec : E ~> PropT F)
      (k_spec : forall T R, E T -> itree F T -> (T -> itree E R) -> (T -> itree F R) -> itree F R -> Prop)
      (KP : forall T R RR b a, Proper (eq ==> eq ==> (fun k1 k2 => forall x, eqit RR b a (k1 x) (k2 x)) ==> eq ==> eq ==> iff) (k_spec T R)),
      Proper (@eutt _ _ _ RR ==> eq ==> flip Basics.impl) (@interp_prop E _ h_spec k_spec R RR).
  Proof.
    intros.

    do 5 red.
    intros t1 t2 eqt s' s eqs HI.
    subst.

    revert t1 t2 eqt s HI.

    pcofix CIH.

    intros.

    pstep. red.
    punfold HI. red in HI.

    punfold eqt. red in eqt.
    genobs t1 obst1.
    genobs t2 obst2.
    revert t1 t2 Heqobst1 Heqobst2 s HI.

    induction eqt; intros.
    - inversion HI; subst.
      econstructor. etransitivity; eauto.
    (*   assumption. *)
    (* - inversion HI; subst. *)
    (*   econstructor. pclearbot. right.  eapply CIH; eauto. *)
    (* - inversion HI. *)
    (*   subst. *)
    (*   apply inj_pair2 in H1. *)
    (*   apply inj_pair2 in H2. *)
    (*   subst. *)
    (*   econstructor. *)
    (*   apply HTA. *)
    (*   intros a Ha. specialize (REL a). specialize (HK a Ha). red in REL. pclearbot. *)
    (*   right. eapply CIH. apply REL. apply HK. *)
    (*   eapply KP; eauto. *)
    (*   pclearbot. *)
    (*   intros x. *)
    (*   eapply REL. *)
    (* - econstructor. *)
    (*   left. pstep. red. eapply IHeqt. reflexivity. eassumption. assumption. *)
    (* - inversion HI; subst. *)
    (*   pclearbot. *)
    (*   eapply IHeqt. reflexivity. reflexivity. *)
    (*   pinversion HS. *)
      Admitted.
  (* Qed. *)

    Lemma interp_prop_trans :
      forall {T E} (RR : relation T) `{REF: Reflexive _ RR} `{TRANS: Transitive _ RR} (x y z : itree E T)
        (h : forall X : Type, E X -> PropT E X)
        (k_spec : forall T R, E T -> itree E T -> (T -> itree E R) -> (T -> itree E R) -> itree E R -> Prop),
        (forall {X : Type} (e : E X), h X e (trigger e)) ->
        (k_spec_correct (fun T e => trigger e) k_spec) ->
        interp_prop h k_spec _ RR x y ->
        interp_prop h k_spec _ RR y z ->
        interp_prop h k_spec _ RR x z.
    Proof.
      intros T E RR REF TRANS x y z h k_spec H_SPEC K_SPEC XY YZ.
      revert x y z XY YZ.
      pcofix CIH; intros x y z XY YZ.

      punfold XY; punfold YZ; pfold; red in XY, YZ |- *.
      genobs x xo.
      genobs y yo.
      genobs z zo.
    Abort.


  (* Figure 7: interp Trigger law *)
  (* morally, we should only work with "proper" triggers everywhere *)
  (* Lemma interp_prop_trigger : *)
  (*   forall E F *)
  (*     (h_spec : E ~> PropT F) *)
  (*     R (e : E R) *)
  (*     (HP : forall T R k t2, Proper (eq ==> Eq1_PropT T) (fun e ift => h_spec T R e ift k t2)) *)
  (*   , (forall k t2, Eq1_PropT _ (interp_prop h_spec k_spec R eq (trigger e)) (fun ifr => h_spec R R R e ifr k t2)). *)
  (* Proof. *)
  (*   intros. *)
  (*   red. *)
  (*   split; [| split]. *)
  (*   - intros; split; intros. *)
  (*     + unfold trigger in H0. red in H0. *)
  (*       pinversion H0; subst. *)
  (*       apply inj_pair2 in H3. apply inj_pair2 in H4. *)
  (*       subst. *)
  (*       unfold subevent, resum, ReSum_id, Id_IFun, id_ in HTA. *)
  (*       rewrite eq2 in H. *)
  (*       assert (x <- ta ;; k2 x ≈ ta). *)
  (*       { rewrite <- (Eq.bind_ret_r ta). *)
  (*         apply eutt_clo_bind with (UU := fun u1 u2 => u1 = u2 /\ Returns u1 ta). *)
  (*         rewrite Eq.bind_ret_r. apply eutt_Returns. *)
  (*         intros. destruct H1. subst. specialize (HK u2 H2). pclearbot. pinversion HK. subst. assumption. *)
  (*       } *)
  (*       rewrite H1 in H. *)
  (*       specialize (HP R e e eq_refl).  unfold Eq1_PropT in HP. destruct HP as (P & _ & _). *)
  (*       rewrite P. apply HTA. symmetry. assumption. *)
  (*     + unfold trigger, subevent, resum, ReSum_id, Id_IFun, id_. *)
  (*       red. pstep. eapply Interp_PropT_Vis with (k2 := (fun x : R => Ret x)). *)
  (*       * apply H0. *)
  (*       * unfold bind, Monad_itree. rewrite Eq.bind_ret_r. assumption. *)
  (*       * intros a. left. pstep. red. econstructor. reflexivity.  reflexivity. *)
  (*   - do 4 red. intros; split; intros. *)
  (*     rewrite <- H. assumption. *)
  (*     rewrite H. assumption. *)
  (*   - do 4 red. *)
  (*     intros; split; intros. *)
  (*     specialize (HP R e e eq_refl). destruct HP as (P & _ & _). *)
  (*     rewrite P; eauto. symmetry. assumption. *)
  (*     specialize (HP R e e eq_refl). destruct HP as (P & _ & _). *)
  (*     rewrite P; eauto.  *)
  (* Qed. *)

  (* Figure 7: Structural law for tau *)
  Lemma interp_prop_tau :
    forall E F
      (h_spec : E ~> PropT F)
      (k_spec : forall T R, E T -> itree F T -> (T -> itree E R) -> (T -> itree F R) -> itree F R -> Prop)
      R RR
      (t_spec : itree E R)
      (KP : forall T R e t k1 k2, Proper (eutt eq ==> flip impl) (k_spec T R e t k1 k2)),
      Eq1_PropT _ (interp_prop h_spec k_spec R RR t_spec) (interp_prop h_spec k_spec R RR (Tau t_spec)).
  Proof.
    intros.
    split; [| split].
    - intros; split; intros.
      + rewrite <- H.
        pstep. red. econstructor.
    (*     left. *)
    (*     apply H0. *)
    (*   + rewrite H. *)
    (*     pinversion H0. subst. *)
    (*     apply HS. *)
    (* - red. typeclasses eauto. *)
        (* - red. typeclasses eauto. *)
  Admitted.

  Lemma interp_prop_ret_inv :
    forall E F
      (h_spec : E ~> PropT F)
      (k_spec : forall T R, E T -> itree F T -> (T -> itree E R) -> (T -> itree F R) -> itree F R -> Prop)
      R RR
      (r1 : R)
      (t : itree F R)
      (H : interp_prop h_spec k_spec R RR (ret r1) t),
       exists  r2, RR r1 r2 /\ t ≈ ret r2.
  Proof.
    intros.
    punfold H.
    red in H. inversion H; subst.
    exists r2; eauto.
  Admitted.

  Lemma interp_prop_vis_inv :
    forall E F
      (h_spec : E ~> PropT F)
      (k_spec : forall T R, E T -> itree F T -> (T -> itree E R) -> (T -> itree F R) -> itree F R -> Prop)
      R RR S
      (e : E S)
      (k : S -> itree E R)
      (t : itree F R)
      (H : interp_prop h_spec k_spec R RR (vis e k) t), 
    exists  ms, exists (ks : S -> itree F R),
      h_spec S e ms /\ k_spec S R e ms k ks t.
  Proof.
    intros.
    punfold H.
    red in H. inversion H; subst.
    apply inj_pair2 in H2.
    apply inj_pair2 in H3.
    subst.
    exists ta. exists k2. auto.
  Qed.

  Lemma interp_prop_tau_inv :
    forall E F
      (h_spec : E ~> PropT F)
      (k_spec : forall T R, E T -> itree F T -> (T -> itree E R) -> (T -> itree F R) -> itree F R -> Prop)
      R RR 
      (s : itree E R)
      (t : itree F R)
      (H : interp_prop h_spec k_spec R RR (Tau s) t), 
      interp_prop h_spec k_spec R RR s t.
  Proof.
    intros.
    punfold H.
    red in H. inversion H; subst.
    pclearbot.
    (* apply HS. *)
  Admitted.
  (* Qed. *)

End interp_prop.
