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
     Eq.Eqit.

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

Require Import Paco.paco.

Import ListNotations.
Import ITree.Basics.Basics.Monads.


Import MonadNotation.
Import CatNotations.
Local Open Scope monad_scope.
Local Open Scope cat_scope.
(* end hide *)

(* This file is a version of [PropT] still containing all the comments
    and experiments conducted.
    The first release contains a curated and cleaned up version, but this
    should probably be kept as a starting point for further improvement.
   *)

(* LLVM IR is a non-deterministic language: the [undef] value can be refined
  into any dynamic value at the concerned type, and [Undefined Behaviors] can
  be refined into any computation.
  
  Our semantic domain hence need to account for this diffuculty. We define
  in this file [PropT], a model for a set of monadic computations.
  This domain is almost a monad, it lacks the associativity to the left
  of its [bind] construct.

  *)

Section ITreeMisc.

  (* Auxiliary results on [itree]s. *)

  Lemma eutt_iter'' {E I1 I2 R1 R2}
        (RI1 RI2 : I1 -> I2 -> Prop)
        (HSUB: RI2 <2= RI1)
        (RR : R1 -> R2 -> Prop)
        (body1 : I1 -> itree E (I1 + R1))
        (body2 : I2 -> itree E (I2 + R2))
        (eutt_body
        : forall j1 j2, RI1 j1 j2 -> eutt (sum_rel RI2 RR) (body1 j1) (body2 j2))
    : forall (i1 : I1) (i2 : I2) (RI_i : RI1 i1 i2),
      @eutt E _ _ RR (ITree.iter body1 i1) (ITree.iter body2 i2).
  Proof using.
    einit. ecofix CIH. intros.
    specialize (eutt_body i1 i2 RI_i).
    do 2 rewrite unfold_iter.
    ebind; econstructor; eauto with paco.
    intros ? ? [].
    - etau.
    - eauto with paco.
  Qed.

  Definition eutt_iter_gen' {F A B R1 R2 S} (HS : R2 <2= R1) :
    @Proper ((A -> itree F (A + B)) -> A -> itree F B)
            ((R1 ==> eutt (sum_rel R2 S)) ==> R1 ==> (eutt S))
            (iter (C := ktree F)).
  Proof using.
    do 3 red;
    intros body1 body2 EQ_BODY x y Hxy. red in EQ_BODY.
    eapply eutt_iter''; eauto.
  Qed.

  Lemma tau_eutt_RR_l : forall E R (RR : relation R) (HRR: Reflexive RR) (HRT: Transitive RR) (t s : itree E R),
      eutt RR (Tau t) s <-> eutt RR t s.
  Proof using.
    intros.
    split; intros H.
    - eapply transitivity. 2 : { apply H. }
      red. apply eqit_tauR. reflexivity.
    - red. red. pstep. econstructor. auto. punfold H.
  Qed.  

  Lemma tau_eqit_RR_l : forall E R (RR : relation R) (HRR: Reflexive RR) (HRT: Transitive RR) (t s : itree E R),
      eqit RR true false t s -> eqit RR true false (Tau t) s.
  Proof using.
    intros.
    red. pstep. econstructor. auto. punfold H.
  Qed.  

  Lemma tau_eutt_RR_r : forall E R (RR : relation R) (HRR: Reflexive RR) (HRT: Transitive RR) (t s : itree E R),
      eutt RR t (Tau s) <-> eutt RR t s.
  Proof using.
    intros.
    split; intros H.
    - eapply transitivity. apply H.
      red. apply eqit_tauL. reflexivity.
    - red. red. pstep. econstructor. auto. punfold H.
  Qed.  

  Lemma eutt_flip : forall E R (RR : relation R) (t1 t2 : itree E R),
      eutt RR t1 t2 -> eutt (flip RR) t2 t1.
  Proof using.
    intros E R RR.
    einit.
    ecofix CIH.
    intros.
    punfold H0. red in H0.
    rewrite (itree_eta t2). rewrite (itree_eta t1).
    genobs t1 ot1.
    genobs t2 ot2.
    revert t1 t2 Heqot1 Heqot2.
    induction H0; intros; pclearbot; try estep.
    - intros. ebase.
    - specialize (IHeqitF t1 t2 eq_refl Heqot2).
      eapply euttG_cong_euttge. reflexivity. apply tau_euttge.
      rewrite (itree_eta t1). assumption.
    - specialize (IHeqitF t1 t2 Heqot1 eq_refl).
      eapply euttG_cong_euttge. apply tau_euttge. reflexivity.
      rewrite (itree_eta t2). assumption.
  Qed.

End ITreeMisc.
  
(* The [PropT] "monad", used to represent a set of computations.
  We currently specialize it to [itree E X -> Prop] instead of defining a 
  proper monad transformer due to complexities in the theory.
*)

Section PropMonad.

  Definition PropT (E: Type -> Type) (X: Type): Type :=
    itree E X -> Prop.

  Definition eutt_closed {E X} (P: itree E X -> Prop): Prop :=
    Proper (eutt eq ==> iff) P.

  Global Polymorphic Instance Eq1_PropT {E} : Eq1 (PropT E) :=
    fun a PA PA' =>
      (forall x y, x ≈ y -> (PA x <-> PA' y)) /\
      eutt_closed PA /\ eutt_closed PA'.
  
  Global Instance Functor_Prop {E}
    : Functor (PropT E) :=
    {| fmap := fun A B f PA b => exists (a: itree E A), PA a /\ b = fmap f a |}.

  Inductive Returns {E} {A: Type} (a: A) : itree E A -> Prop :=
  | ReturnsRet: forall t, t ≈ Ret a -> Returns a t
  | ReturnsTau: forall t u, t ≈ Tau u -> Returns a u -> Returns a t
  | ReturnsVis: forall {X} (e: E X) (x: X) t k, t ≈ Vis e k -> Returns a (k x) -> Returns a t
  .
  Hint Constructors Returns: core.

  Definition subtree {E} {A B} (ta : itree E A) (tb : itree E B) := exists (k : A -> itree E B), tb ≈ bind ta k.

  Definition bind_PropT {E} :=
    fun A B (PA: PropT E A) (K: A -> PropT E B) (tb: itree E B) =>
      exists (ta: itree E A) (k: A -> itree E B),
        PA ta /\
        tb ≈ bind ta k /\
        (forall a, Returns a ta -> K a (k a)).

  (*
  (*  ------------------------------------------------------------------------- *)
  (* SZ: Here is a coinductive version of bind_propT that might work out better *)
  Inductive bind_PropTF {E} {A B} (PA: PropT E A) (K: A -> PropT E B) (sim : itree E B -> Prop) : itree' E B -> Prop :=
    (* If we bind and get a Ret then both the first and second parts of the computation must be (equivalent to) ret *)
  | bind_PropTF_Ret : forall (b:B) (ta : itree E A) (HP : PA ta) (a:A) (eqA: ta ≈ ret a) (tb : itree E B) (eqB : tb ≈ ret b) (HB : K a tb),
      bind_PropTF PA K sim (RetF b)

    (* If we bind and get [Tau tb] then we don't know how to break up the tree, so just corecurse *)
  | bind_PropTF_Tau : forall tb, sim tb -> bind_PropTF PA K sim (TauF tb)

    (* If we bind and get [Vis e k] then either the event is raised in the first part of the compuation: *)                                            
  | bind_PropTF_Vis_l : forall X (e : E X) (k : X -> itree E B) (ta : itree E A) (HP : PA ta) (ka : X -> itree E A) (eqA : ta ≈ Vis e ka)
                        (k' : A -> itree E B)
                        (Hks : forall (x:X), (k x) ≈ (ITree.bind (ka x) k'))
                        (HK : forall (a : A), Returns a ta -> (K a (k' a))),
      bind_PropTF PA K sim (VisF e k)
    (* ... or, it was raised in the second part, and the first part was pure *)
  | bind_PropTF_Vis_r :  forall X (e : E X) (k : X -> itree E B) (ta : itree E A) (HP : PA ta) (a : A) (eqA : ta ≈ ret a)
                        (k' : A -> itree E B)
                        (Hks : (ITree.bind ta k') ≈ (Vis e k))
                        (HK : K a (Vis e k)),
      bind_PropTF PA K sim (VisF e k).

  Hint Constructors bind_PropTF : core.
  
  Lemma bind_PropTF_mono E A B (PA : PropT E A) (K : A -> PropT E B) sim sim' (t : itree' E B)
        (IN : bind_PropTF PA K sim t)
        (LE : sim <1= sim') : 
    (bind_PropTF PA K sim' t).
  Proof using.
    induction IN; eauto.
  Qed.

  Hint Resolve bind_PropTF_mono : paco.

  Definition bind_PropT_ E A B (PA : PropT E A) (K : A -> PropT E B) sim (t : itree E B) :=
    bind_PropTF PA K sim (observe t).
  Hint Unfold bind_PropT_ : core.

  Lemma bind_PropT__mono E A B (PA : PropT E A) (K : A -> PropT E B) : monotone1 (bind_PropT_ E A B PA K).
  Proof using.
    do 2 red. intros. eapply bind_PropTF_mono; eauto.
  Qed.
  Hint Resolve bind_PropT__mono : paco.  
  
  Definition bind_prop {E A B} (PA : PropT E A) (K : A -> PropT E B) : PropT E B :=
    paco1 (bind_PropT_ E A B PA K) bot1.


  Lemma bind_prop_eutt :
    forall {E} {A B} (PA: PropT E A) (K: A -> PropT E B)
      (HK: forall a, Eq1_PropT _ (K a) (K a))
      
      (t1 t2 : itree E B) (eq : t1 ≈ t2),
      bind_prop PA K t1 -> bind_prop PA K t2.
  Proof using.
    intros E A B PA K HK.
    pcofix CIH.
    intros t1 t2 eq H.
    punfold H. red in H.
    punfold eq. red in eq.
    pstep. red.
    genobs t1 obt1. genobs t2 obt2.
    revert t1 t2 Heqobt1 Heqobt2 H.
    induction eq; intros; subst; inv H; subst.
    - econstructor; eauto.
    - econstructor. pclearbot. right. eapply CIH. apply REL. apply H1.
    - apply inj_pair2 in H2. apply inj_pair2 in H3. subst.
      eapply bind_PropTF_Vis_l; eauto. intros. specialize (Hks x). specialize (REL x). pclearbot. rewrite <- REL. assumption.
    - apply inj_pair2 in H2. apply inj_pair2 in H3. subst.
      assert (Vis e k1 ≈ Vis e k2).
      { apply eqit_Vis. intros. specialize (REL u0). pclearbot. apply REL. }
      eapply bind_PropTF_Vis_r; eauto.
      + etransitivity. apply Hks. assumption.
      + specialize (HK a). destruct HK as (HX & _ & _). specialize (HX _ _ H). apply HX. assumption.
    - eapply IHeq. reflexivity. reflexivity. pclearbot. pinversion H1.
    - econstructor. left. pstep. red. eapply IHeq. reflexivity. reflexivity. rewrite <- H1.
      econstructor; eauto.
    - pclearbot. econstructor. left. pstep. red. eapply IHeq. reflexivity. reflexivity. rewrite <- H0.
      econstructor. left. assumption.
    - econstructor. left. pstep. red. eapply IHeq. reflexivity. reflexivity. rewrite <- H1.
      eapply bind_PropTF_Vis_l; eauto.
    - econstructor. left. pstep. red. eapply IHeq. reflexivity. reflexivity. rewrite <- H1.
      eapply bind_PropTF_Vis_r; eauto.
  Qed.


  (* This more general version seems much harder *)
  Lemma bind_prop_Proper {E} {A B} :
     Proper (eq1 ==> (eq ==> eq1) ==> eutt eq ==> iff) (@bind_prop E A B).
  Proof using.
    do 5 red.
    intros PA PA' EQA K1 K2 EQK t1 t2 eq.
    split.
    - destruct EQA as (PPA & PX & PY).
      intros H.
      punfold H. red in H.
      punfold eq. red in eq.
      pstep. red.
      genobs t1 obt1. genobs t2 obt2.
      revert t1 t2 Heqobt1 Heqobt2 H.
      induction eq; intros; subst; inv H; subst.
      + econstructor. rewrite <- PPA. apply HP. reflexivity. eauto. eauto. specialize (EQK a a eq_refl). destruct EQK as (XK & _ & _). rewrite <- XK. apply HB. reflexivity.
(*        
    + econstructor. left. pclearbot. right. eapply CIH. apply REL. apply H1.
    - apply inj_pair2 in H2. apply inj_pair2 in H3. subst.
      eapply bind_PropTF_Vis_l; eauto. intros. specialize (Hks x). specialize (REL x). pclearbot. rewrite <- REL. assumption.
    - apply inj_pair2 in H2. apply inj_pair2 in H3. subst.
      assert (Vis e k1 ≈ Vis e k2).
      { apply eqit_Vis. intros. specialize (REL u0). pclearbot. apply REL. }
      eapply bind_PropTF_Vis_r; eauto.
      + etransitivity. apply Hks. assumption.
      + specialize (HK a). destruct HK as (HX & _ & _). specialize (HX _ _ H). apply HX. assumption.
    - eapply IHeq. reflexivity. reflexivity. pclearbot. pinversion H1.
    - econstructor. left. pstep. red. eapply IHeq. reflexivity. reflexivity. rewrite <- H1.
      econstructor; eauto.
    - pclearbot. econstructor. left. pstep. red. eapply IHeq. reflexivity. reflexivity. rewrite <- H0.
      econstructor. left. assumption.
    - econstructor. left. pstep. red. eapply IHeq. reflexivity. reflexivity. rewrite <- H1.
      eapply bind_PropTF_Vis_l; eauto.
    - econstructor. left. pstep. red. eapply IHeq. reflexivity. reflexivity. rewrite <- H1.
      eapply bind_PropTF_Vis_r; eauto.
 *)
  Abort.
  *)

  (* end coinductive bind ----------------------------------------------------- *)
  
  Definition bind_PropT_stronger {E} :=
    fun A B (PA: PropT E A) (K: A -> PropT E B) (tb: itree E B) =>
      exists (ta: itree E A) (k: A -> itree E B),
        PA ta /\
        tb ≈ bind ta k /\
        (forall a, Returns a ta -> K a (k a)).

  Definition bind_PropT' {E} := 
    fun A B (PA: PropT E A) (K: A -> PropT E B) (tb: itree E B) =>
      exists (ta: itree E A),  PA ta /\
                          ((exists (k: A -> itree E B),
                               (forall a, Returns a ta -> K a (k a))
                               /\ tb ≈ bind ta k)
                           \/ (forall k, (forall a, K a (k a)) /\ tb ≈ bind ta k)).

  (* Definition bind_PropT {E} := *)
  (*   fun A B (PA: PropT E A) (K: A -> PropT E B) (tb: itree E B) => *)
  (*     exists (ta: itree E A) (k: A -> itree E B), *)
  (*       (exists a, Returns a ta /\ *)
  (*             PA ta /\ tb ≈ bind ta k /\ *)
  (*             (forall a', Returns a' ta -> K a' (k a'))). *)
        (* (~ (exists a, Returns a ta)).  *)
  (* SAZ: Here is the proof that the two version of bind are logically equivalent, so
     it should not matter which one we use. Since bind_PropT has fewer cases, we should
     use it.*)
  Lemma bind_PropT_bind_PropT' {E}:
    forall A B PA K (tb : itree E B), bind_PropT A B PA K tb <-> bind_PropT' A B PA K tb.
  Proof using.
    intros. split.
    intros.
    - red. red in H.
      destruct H as (ta & ka & HPA & eq & HR).
      exists ta. split; auto.
      left.  exists ka. split; auto.
    - intros.
      red. red in H.
      destruct H as  (ta & EQ1 & [(k & KA & EQ2) | HX]).
      + exists ta. exists k. auto.
      + exists ta. exists (fun _ => ITree.spin).
        split; auto.
        specialize (HX (fun _ => ITree.spin)).
        destruct HX as (HA & H).
        split; auto.
  Qed.

  Global Instance Monad_Prop {E} : Monad (PropT E) :=
    {|
      ret := fun _ x y => y ≈ ret x
      ; bind := bind_PropT
    |}.

  Definition handler_correct {E F} (h_spec: E ~> PropT F) (h: E ~> itree F) :=
    (forall T e, h_spec T e (h T e)).


  (*
  (* SAZ: This definition isn't quite correct because it fails in the case of a 
     vacuous h_spec (i.e. fun e t => False), since there can not exist such
     a handler _but_ the iterpreter should still succeed on trees without
     Vis events.
  *)
  Definition interp_PropT {E F : Type -> Type} (h_spec : E ~> PropT F) :
    forall R (RR: relation R), itree E R -> PropT F R :=
    fun R RR (t : itree E R) s =>
      exists h, handler_correct h_spec h /\ eutt RR (interp h t) s.
                                                     
  Definition interp_prop_old {E F} (h : E ~> PropT F) :
    forall R (RR: relation R), itree E R -> PropT F R := interp_PropT h.


  Lemma interp_prop_old_correct_exec:
    forall {E F} (h_spec: E ~> PropT F) (h: E ~> itree F),
      handler_correct h_spec h ->
      forall R RR `{Reflexive _ RR} t, interp_prop_old h_spec R RR t (interp h t).
  Proof using.
    intros.
    exists h; split; auto. reflexivity.
  Qed.


  Instance interp_prop_old_Proper_eq :
    forall R (RR : relation R) (HR: Reflexive RR) (HT : Transitive RR) E F (h_spec : E ~> PropT F),
      Proper (@eutt _ _ _ RR ==> eq ==> flip Basics.impl) (@interp_prop_old E _ h_spec R RR).
  Proof using.
    intros.
    do 5 red.
    intros t1 t2 eqt s' s eqs HI.
    subst.
    unfold interp_prop_old, interp in HI. red in HI.

    destruct HI as (h & HC & HE).

    exists h. split; auto.

    eapply transitivity. 2 : { apply HE. } clear HE s.

    revert t1 t2 eqt.

    einit.
    ecofix CIH.

    intros.

    unfold interp. 
    unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree in *.

    rewrite (itree_eta t1). rewrite (itree_eta t2).
    punfold eqt. red in eqt.
    
    genobs t1 obt1.
    genobs t2 obt2.

    revert t1 t2 Heqobt1 Heqobt2.
    induction eqt; intros; cbn in *.
    
    - do 2 rewrite unfold_iter. cbn.
      do 2 rewrite Eq.bind_ret_l. cbn.
      estep.

    - do 2 rewrite unfold_iter. cbn.
      do 2 rewrite Eq.bind_ret_l. cbn.
      estep.
      econstructor.
      change (ITree.iter
                (fun t : itree (fun H : Type => E H) R =>
                   match observe t with
                   | RetF r0 => Ret (inr r0)
                   | TauF t0 => Ret (inl t0)
                   | @VisF _ _ _ X e k => ITree.map (fun x : X => inl (k x)) (h X e)
                   end) m1) with (interp h m1).
      change (ITree.iter
                (fun t : itree (fun H : Type => E H) R =>
                   match observe t with
                   | RetF r0 => Ret (inr r0)
                   | TauF t0 => Ret (inl t0)
                   | @VisF _ _ _ X e k => ITree.map (fun x : X => inl (k x)) (h X e)
                   end) m2) with (interp h m2).
      gfinal. left. right. apply CIH. pclearbot. apply REL.

    - do 2 rewrite unfold_iter. cbn.
      unfold ITree.map.
      do 2 rewrite Eq.bind_bind.
      apply euttG_bind. eapply Eq.pbc_intro_h with (RU := eq).
      + reflexivity.
      + intros; subst.
        do 2 rewrite Eq.bind_ret_l. cbn.
        econstructor.
        gstep. red. econstructor.
        gfinal. left.
        specialize (REL u2). pclearbot. pinversion REL.  
    - rewrite unfold_iter. cbn.
      rewrite Eq.bind_ret_l.
      cbn.
      specialize (IHeqt t1 t2 eq_refl Heqobt2).
      eapply euttG_cong_euttge. apply tau_euttge. reflexivity.
      rewrite (itree_eta t1). assumption.
    - match goal with
      | [ |- euttG _ _ _ _ _ ?X _ ] => remember X as XX
      end.
      rewrite unfold_iter.
      rewrite HeqXX in *. clear XX HeqXX.
      cbn. rewrite Eq.bind_ret_l. cbn.
      specialize (IHeqt t1 t2 Heqobt1 eq_refl).
      eapply euttG_cong_euttge. reflexivity. apply tau_euttge.
      rewrite (itree_eta t2). assumption.
  Qed.

  (* SAZ: This is where the bad definition of interp_prop_old bites... *)
  Lemma interp_prop_ret :
    forall R E F (h_spec : E ~> PropT F)
      (r : R)
    , eq1 (interp_prop_old h_spec R eq (ret r)) (ret r).
  Proof using.
    intros.
    repeat red. split; [|split].
    - intros.
      split; intros.
      + repeat red in H0. destruct H0 as (h & HC & eq).
        cbn in eq. rewrite interp_ret in eq. red. red. rewrite <- H. symmetry.  apply eq.
      + cbn. repeat red. (* There may not exist such a handler but that shouldn't matter *)
  Abort.        

  
  (* SAZ: maybe define directly by coinduction  *)
  (* SAZ: For some reason, if this definition is moved below case_prop_handler_correct, I get a universe inconsistency(!) *)
  (* This definition of monad_iter suffers from the same problem of vacous specs as the interp_prop_old above *)
  Definition MonadIter_Prop_itree' {E F} :=
    fun R (RR: relation R) (step : itree E R -> PropT F (itree E R + R)) i =>
      fun (r : itree F R) =>
        (exists step' : itree E R  -> itree F (itree E R + R)%type,
            (* How do we state that something is out of bounds? *)
            (forall j, step j (step' j)) /\
            eutt RR (CategoryOps.iter step' i) r).

  Definition interp_PropT' {E F : Type -> Type} (h : E ~> PropT F) :
  forall R (RR: relation R), itree E R -> PropT F R := fun R RR =>
  MonadIter_Prop_itree' _ RR (fun t =>
    match observe t with
    | RetF r => ret (inr r)
    | TauF t => ret (inl t)
    | VisF e k => fmap (fun x => inl (k x)) (h _ e)
    end).


  (* SAZ: This lemma proves that the definition of interp_prop_old given above
  refines the more liberal one, which allows a different choice of handler for
  each iteration. *)
  Lemma interp_PropT_OK : forall {E F} (h_spec : E ~> PropT F) R RR t u,
      interp_prop_old h_spec R RR t u -> interp_PropT' h_spec R RR t u.
  Proof using.
    intros.
    do 2 red in H.
    do 2 red. destruct H as (h & HC & eq).
    unfold interp in eq.
    exists (fun t : itree (fun H : Type => E H) R =>
             match observe t with
             | RetF r => ret (inr r)
             | TauF t0 => ret (inl t0)
             | @VisF _ _ _ X e k => fmap (fun x : X => inl (k x)) (h X e)
             end).
    split.
    - unfold handler_correct in HC.
      intros j.
      destruct (observe j).
      * cbn. reflexivity.
      * cbn. reflexivity.
      * cbn. exists (h X e). split. apply HC. reflexivity.
    - assumption.
  Qed.

*)

  (*  ------------------------------------------------------------------------- *)
  (* STARTING HERE IS THE BETTER DEFINITION OF INTERP_PROP -------------------- *)
  
  Inductive interp_PropTF {E F} (h_spec : forall T, E T -> itree F T -> Prop)
            {R : Type} (RR : relation R) (sim : itree E R -> itree F R -> Prop)
            : itree' E R -> itree F R -> Prop := 
  | Interp_PropT_Ret : forall r1 r2 (REL: RR r1 r2)
                     (t2 : itree F R)
                     (eq2 : t2 ≈ (Ret r2)),
      interp_PropTF h_spec RR sim (RetF r1) t2

  | Interp_PropT_Tau : forall t1 t2 (HS: sim t1 t2), interp_PropTF h_spec RR sim (TauF t1) t2
                    
  | Interp_PropT_Vis : forall A (e : E A) (k1 : A -> itree E R)
                         (t2 : itree F R)
                         (ta :itree F A)  (k2 : A -> itree F R) (HTA: h_spec A e ta)
                         (eq2 : t2 ≈ (bind ta k2))
                         (HK : forall (a : A), Returns a ta ->  sim (k1 a) (k2 a)), 
      interp_PropTF h_spec RR sim (VisF e k1) t2.

  Hint Constructors interp_PropTF : core.
  
  Lemma interp_PropTF_mono E F h_spec R RR  (t0 : itree' E R) (t1 : itree F R) sim sim'
        (IN : interp_PropTF h_spec RR sim t0 t1)
        (LE : sim <2= sim') : 
    (interp_PropTF h_spec RR sim' t0 t1).
  Proof using.
    induction IN; eauto.
  Qed.

  Hint Resolve interp_PropTF_mono : paco.

  Definition interp_PropT_ E F h_spec R RR sim (t0 : itree E R) (t1 : itree F R) :=
    interp_PropTF h_spec RR sim (observe t0) t1.
  Hint Unfold interp_PropT_ : core.

  Lemma interp_PropT__mono E F h_spec R RR : monotone2 (interp_PropT_ E F h_spec R RR).
  Proof using.
    do 2 red. intros. eapply interp_PropTF_mono; eauto.
  Qed.
  Hint Resolve interp_PropT__mono : paco.  
  
  Definition interp_prop {E F} (h_spec : E ~> PropT F) :
    forall R (RR: relation R), itree E R -> PropT F R :=
      fun R (RR: relation R) =>  paco2 (interp_PropT_ E F h_spec R RR) bot2.

  (* Figure 8: Interpreter law for Ret *)
  Lemma interp_prop_ret :
    forall R E F (h_spec : E ~> PropT F)
      (r : R)
    , Eq1_PropT _ (interp_prop h_spec R eq (ret r)) (ret r).
  Proof using.
    intros.
    repeat red.
    split; [| split].
    - intros. split; intros.
      + unfold interp_prop in H0.
        pinversion H0. subst.
        cbn. rewrite <- H. assumption.
      + pstep. econstructor. reflexivity. rewrite H. cbn in H0. assumption.
    - do 3 red.
      intros t1 t2 eq; split; intros H; pinversion H; subst.
      + red. pstep. econstructor. reflexivity. rewrite <- eq. assumption.
      + red. pstep. econstructor. reflexivity. rewrite eq. assumption.
   - do 3 red. intros. split; intros; cbn in *. rewrite <- H. assumption. rewrite H; assumption.
  Qed.      

  Global Instance interp_PropTF_Proper
         {E F} (h_spec : E ~> PropT F) R RR (t : itree' E R)
         (sim : itree E R -> itree F R -> Prop)
         (HS: forall t, Proper(eutt eq ==> flip impl) (sim t))
    : 
    Proper(eutt eq ==> iff) (interp_PropTF h_spec RR sim t).
  Proof using.
    do 2 red.
    intros.
    split; intros.
    - inversion H0; subst; econstructor; eauto.
      + rewrite <- H. assumption.
      + specialize (HS t1). rewrite <- H. assumption.
      + rewrite <- H. assumption.
        
    - inversion H0; subst; econstructor; eauto.
      rewrite H. assumption. specialize (HS t1). rewrite H. assumption.
      rewrite H. assumption.
  Qed.

  Global Instance interp_prop_Proper
         {E F} (h_spec : E ~> PropT F) R RR (t : itree E R) :
    Proper(eq_itree Logic.eq ==> iff) (interp_prop h_spec R RR t).
  Proof using.
    do 2 red.
    intros.
    split.
    - revert t x y H.
      pcofix CIH.
      intros t x y eq HI. 
      red in HI. punfold HI. red in HI.
      pstep. red. genobs t ot.
      inversion HI; subst; econstructor; eauto.
      + rewrite <- eq. assumption.
      + pclearbot. right. eapply CIH; eauto.
      + rewrite <- eq. apply eq2.
      + intros. specialize (HK a H0). pclearbot. right. eapply CIH. 2 : { apply HK. } reflexivity.
    - revert t x y H.
      pcofix CIH.
      intros t x y eq HI. 
      red in HI. punfold HI. red in HI.
      pstep. red. genobs t ot.
      inversion HI; subst; econstructor; eauto.
      + rewrite eq. assumption.
      + pclearbot. right. eapply CIH; eauto.
      + rewrite eq. apply eq2.
      + intros. specialize (HK a H0). pclearbot. right. eapply CIH. 2 : { apply HK. } reflexivity.
  Qed.
  
  Global Instance interp_prop_Proper2
         {E F} (h_spec : E ~> PropT F) R RR (t : itree E R) :
    Proper(eutt Logic.eq ==> iff) (interp_prop h_spec R RR t).
  Proof using.
    do 2 red.
    intros.
    split.
    - revert t x y H.
      pcofix CIH.
      intros t x y eq HI. 
      red in HI. punfold HI. red in HI.
      pstep. red. genobs t ot.
      inversion HI; subst; econstructor; eauto.
      + rewrite <- eq. assumption.
      + pclearbot. right. eapply CIH; eauto.
      + rewrite <- eq. apply eq2.
      + intros. specialize (HK a H0). pclearbot. right. eapply CIH. 2 : { apply HK. } reflexivity.
    - revert t x y H.
      pcofix CIH.
      intros t x y eq HI. 
      red in HI. punfold HI. red in HI.
      pstep. red. genobs t ot.
      inversion HI; subst; econstructor; eauto.
      + rewrite eq. assumption.
      + pclearbot. right. eapply CIH; eauto.
      + rewrite eq. apply eq2.
      + intros. specialize (HK a H0). pclearbot. right. eapply CIH. 2 : { apply HK. } reflexivity.
  Qed.



  Global Instance interp_prop_Proper3
         {E F} (h_spec : E ~> PropT F) R RR :
    Proper(eq_itree eq ==> eq  ==> iff) (interp_prop h_spec R RR).
  Proof using.
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
      + apply inj_pair2 in H2.
        apply inj_pair2 in H3. subst.
        econstructor; eauto. intros X HX. specialize (REL X). specialize (HK X HX). pclearbot.
        right. eapply CIH; eauto.
      + eapply IHeq.  reflexivity. reflexivity.
        punfold HS.
      + econstructor. left. pstep. eapply IHeq. reflexivity. reflexivity. assumption.
      + econstructor. left.  pstep. eapply IHeq. reflexivity. reflexivity. assumption.
      + econstructor. left.  pstep. eapply IHeq. reflexivity. reflexivity. assumption.

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
      + apply inj_pair2 in H2.
        apply inj_pair2 in H3. subst.
        econstructor; eauto. intros X HX. specialize (REL X). specialize (HK X HX). pclearbot.
        right. eapply CIH; eauto.
      + econstructor. left. pstep. eapply IHeq. reflexivity. reflexivity. assumption.
      + econstructor. left. pstep. eapply IHeq. reflexivity. reflexivity. assumption.
      + econstructor. left. pstep. eapply IHeq. reflexivity. reflexivity. assumption.
      + eapply IHeq. reflexivity. reflexivity.   punfold HS.
  Qed.
  
  Lemma interp_prop_correct_exec:
    forall {E F} (h_spec: E ~> PropT F) (h: E ~> itree F),
      handler_correct h_spec h ->
      forall R RR `{Reflexive _ RR} t t', t ≈ t' -> interp_prop h_spec R RR t (interp h t').
  Proof using.
    intros.
    revert t t' H1.
    pcofix CIH.
    intros t t' eq.
    pstep.
    red.
    unfold interp, Basics.iter, MonadIter_itree.
    rewrite (itree_eta t) in eq. 
    destruct (observe t).
    - econstructor. reflexivity. rewrite <- eq. rewrite unfold_iter. cbn. rewrite Eq.bind_ret_l. cbn.  reflexivity.
    - econstructor. right.
      eapply CIH. rewrite tau_eutt in eq. rewrite eq. reflexivity.
    - econstructor. 
      2 : { rewrite <- eq. rewrite unfold_iter. cbn.
            red. red. unfold ITree.map. rewrite Eq.bind_bind.
            setoid_rewrite Eq.bind_ret_l at 1. cbn. setoid_rewrite tau_eutt.
            reflexivity. }
      apply H.
      intros a. cbn.  
      right.
      unfold interp, Basics.iter, MonadIter_itree in CIH. unfold fmap, Functor_itree, ITree.map in CIH.
      specialize (CIH (k a) (k a)).
      apply CIH.
      reflexivity.
  Qed.


  Instance interp_prop_Proper_eq :
    forall R (RR : relation R) (HR: Reflexive RR) (HT : Transitive RR) E F (h_spec : E ~> PropT F),
      Proper (@eutt _ _ _ RR ==> eq ==> flip Basics.impl) (@interp_prop E _ h_spec R RR).
  Proof using.
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
      econstructor. etransitivity; eauto. assumption.
    - inversion HI; subst.
      econstructor. pclearbot. right.  eapply CIH; eauto.
    - inversion HI.
      subst.
      apply inj_pair2 in H1.
      apply inj_pair2 in H2.
      subst.
      econstructor.
      apply HTA.
      apply eq2.
      intros a Ha. specialize (REL a). specialize (HK a Ha). red in REL. pclearbot.
      right. eapply CIH. apply REL. apply HK.
    - econstructor.
      left. pstep. red. eapply IHeqt. reflexivity. eassumption. assumption.
    - inversion HI; subst.
      pclearbot.
      eapply IHeqt. reflexivity. reflexivity.
      pinversion HS.
  Qed.

    Global Instance Returns_eutt {E A} a: Proper (eutt eq ==> iff) (@Returns E A a).
  Proof using.
    repeat intro; split; intros HRet.
    - revert y H. induction HRet; intros.
      constructor; rewrite <- H, H0; reflexivity.
      apply IHHRet, eqit_inv_tauL; auto.
      rewrite <- H0. rewrite H. reflexivity.
      econstructor 3; [rewrite <- H0, H; reflexivity | apply IHHRet; reflexivity].
    - revert x H; induction HRet; intros ? EQ.
      constructor; rewrite EQ; eauto.
      apply IHHRet, eqit_inv_tauR; auto.
      rewrite EQ. rewrite <- H. reflexivity.
      econstructor 3; [rewrite EQ, H; reflexivity | apply IHHRet; reflexivity].
  Qed.

  Lemma Returns_Vis_sub :  forall {E} {R} X (e : E X) (k : X -> itree E R) u x, Returns u (k x) -> Returns u (Vis e k).
  Proof using.
    intros.
    eapply ReturnsVis. reflexivity. apply H.
  Qed.

  Lemma eutt_Returns_ : forall {E} {R} (RR : R -> Prop) (ta : itree E R) 
     (IN: forall (a : R), Returns a ta -> RR a), eutt (fun u1 u2 => u1 = u2 /\ RR u1) ta ta.
  Proof using.
    intros E R.
    ginit.
    gcofix CIH; intros.

    setoid_rewrite (itree_eta ta) in IN.

    gstep. red.

    destruct (observe ta).
    - econstructor.  split; auto. apply IN. econstructor. reflexivity.
    - econstructor. gfinal. left. apply CIH. intros. eapply IN. rewrite tau_eutt. assumption.
    - econstructor. intros. red.
      gfinal. left. apply CIH. intros. eapply IN. eapply Returns_Vis_sub. apply H.
  Qed.

  Lemma eutt_Returns : forall E R (ta : itree E R), eutt (fun u1 u2 => u1 = u2 /\ Returns u1 ta) ta ta.
  Proof using.
    intros.
    apply eutt_Returns_. auto.
  Qed.

  (* Figure 8: interp Trigger law *)
  (* SAZ : morally, we should only work with "proper" triggers everywhere *)
  Lemma interp_prop_trigger :
    forall E F (h_spec : E ~> PropT F) R (e : E R)
      (HP : forall T, Proper (eq ==> Eq1_PropT T) (h_spec T))
    , Eq1_PropT _ (interp_prop h_spec R eq (trigger e)) (h_spec R e).
  Proof using.
    intros.
    red.
    split; [| split].
    - intros; split; intros.
      + unfold trigger in H0. red in H0.
        pinversion H0; subst.
        apply inj_pair2 in H3. apply inj_pair2 in H4.
        subst.
        unfold subevent, resum, ReSum_id, Id_IFun, id_ in HTA.
        rewrite eq2 in H.
        assert (x <- ta ;; k2 x ≈ ta).
        { rewrite <- (Eq.bind_ret_r ta).
          apply eutt_clo_bind with (UU := fun u1 u2 => u1 = u2 /\ Returns u1 ta).
          rewrite Eq.bind_ret_r. apply eutt_Returns.
          intros. destruct H1. subst. specialize (HK u2 H2). pclearbot. pinversion HK. subst. assumption.
        }
        rewrite H1 in H.
        specialize (HP R e e eq_refl).  unfold Eq1_PropT in HP. destruct HP as (P & _ & _).
        rewrite P. apply HTA. symmetry. assumption.
      + unfold trigger, subevent, resum, ReSum_id, Id_IFun, id_.
        red. pstep. eapply Interp_PropT_Vis with (k2 := (fun x : R => Ret x)).
        * apply H0.
        * unfold bind, Monad_itree. rewrite Eq.bind_ret_r. assumption.
        * intros a. left. pstep. red. econstructor. reflexivity.  reflexivity.
    - do 4 red. intros; split; intros.
      rewrite <- H. assumption.
      rewrite H. assumption.
    - do 4 red.
      intros; split; intros.
      specialize (HP R e e eq_refl). destruct HP as (P & _ & _).
      rewrite P; eauto. symmetry. assumption.
      specialize (HP R e e eq_refl). destruct HP as (P & _ & _).
      rewrite P; eauto. 
  Qed.

  (*  Interesting observations about interp_prop:

      Suppose h_spec : E ~> Prop T F
      then (interp_prop h_spec _ eq spin) : PropT F
      which itrees should be accepted by that predicate?  
     
      - we know by interp_prop_correct_exe that if there is an h such that handler_correct h_spec h then spin is accepted.
        (I believe we could eliminate the requirement that there is such an h)
      - what other trees are accepted?  

      Answer: all of them!
   *)
  Lemma interp_prop_spin_accepts_anything :
    forall E F (h_spec : E ~> PropT F) R RR (t : itree F R),
      interp_prop h_spec R RR ITree.spin t.
  Proof using.
    intros.
    pcofix CIH.
    pstep. red. cbn. econstructor. right. apply CIH.
  Qed.

  (* Figure 8: Structural law for tau *)
  Lemma interp_prop_tau :
    forall E F (h_spec : E ~> PropT F) R RR
      (t_spec : itree E R),
      Eq1_PropT _ (interp_prop h_spec R RR t_spec) (interp_prop h_spec R RR (Tau t_spec)).
  Proof using.
    intros.
    split; [| split].
    - intros; split; intros.
      + rewrite <- H. 
        pstep. red. econstructor. left. apply H0.
      + rewrite H.
        pinversion H0. subst.
        apply HS.
    - red. typeclasses eauto.
    - red. typeclasses eauto.
  Qed.

  Lemma interp_prop_ret_inv :
    forall E F (h_spec : E ~> PropT F) R RR
      (r1 : R)
      (t : itree F R)
      (H : interp_prop h_spec R RR (ret r1) t),
       exists  r2, RR r1 r2 /\ t ≈ ret r2.
  Proof using.
    intros.
    punfold H.
    red in H. inversion H; subst.
    exists r2; eauto.
  Qed.

  Lemma interp_prop_vis_inv :
    forall E F (h_spec : E ~> PropT F) R RR S
      (e : E S)
      (k : S -> itree E R)
      (t : itree F R)
      (H : interp_prop h_spec R RR (vis e k) t), 
    exists  ms, exists (ks : S -> itree F R),
        h_spec S e ms /\ t ≈ (bind ms ks).
  Proof using.
    intros.
    punfold H.
    red in H. inversion H; subst.
    apply inj_pair2 in H2.
    apply inj_pair2 in H3.
    subst.
    exists ta. exists k2. split; auto.
  Qed.

  Lemma interp_prop_tau_inv :
    forall E F (h_spec : E ~> PropT F) R RR 
      (s : itree E R)
      (t : itree F R)
      (H : interp_prop h_spec R RR (Tau s) t), 
      interp_prop h_spec R RR s t.
  Proof using.
    intros.
    punfold H.
    red in H. inversion H; subst.
    pclearbot.
    apply HS.
  Qed.

  Lemma Returns_ret_inv_ : forall {E} A (a b : A) (t : itree E A), t ≈ (Ret b) -> Returns a t -> a = b.
  Proof using.
    intros E A a b t eq H. 
    revert b eq.
    induction H; intros; subst.
    - rewrite H in eq. apply Eq.eqit_Ret in eq. auto.
    - eapply IHReturns. rewrite tau_eutt in H. rewrite <- H. assumption.
    - rewrite H in eq. symmetry in eq. apply eutt_inv_ret_vis in eq. inv eq.
  Qed.

  Lemma Returns_ret_inv :  forall {E} A (a b : A), Returns a ((ret b) : itree E A) -> a = b.
  Proof using.
    intros.
    eapply Returns_ret_inv_. reflexivity. cbn in H. apply H.
  Qed.
  
(*  
  
  (* SAZ: Not clear that this one is provable : *)
  Lemma interp_prop_bind_inv_l :
    forall E F (h_spec : E ~> PropT F) R RR (HR: Reflexive RR) (HT : Transitive RR) S
      (HP : forall T, Proper (eq ==> Eq1_PropT T) (h_spec T))
      (m : itree E S)
      (k : S -> itree E R)
      (t : itree F R)
      (H : interp_prop h_spec R RR (bind m k) t),
       exists  (mf : itree F S) (kf : S -> itree F R) SS,
         eutt RR t (bind mf kf) /\ Proper (SS ==> eutt RR) kf /\
         (interp_prop h_spec S SS m mf) /\ (forall s, SS s s -> interp_prop h_spec R RR (k s) (kf s)).
  Proof using.
    intros.
    unfold bind, Monad_itree in *. rewrite (itree_eta m) in H. setoid_rewrite (itree_eta m).

    genobs m obsm.
    destruct obsm.
    - rewrite Eq.bind_ret_l in H.
      exists (ret r). exists (fun _ => t). exists (fun r1 r2 => r1 = r /\ r2 = r).
      split; [| split; [|split]].
      + cbn. rewrite Eq.bind_ret_l. reflexivity.
      + do 2 red. intros; subst. reflexivity.
      + repeat red. pstep. red. econstructor. split; reflexivity. reflexivity.
      + intros. destruct H0. subst. assumption.
    - rewrite Eq.bind_tau in H.
      punfold H. red in H. inv H; subst.
      pclearbot.
      assert (inhabited S \/ ~ inhabited S).
      { admit. (* TODO: classical logic *) }
      destruct H.
      * inv H. exists (ret X). (exists (fun _ => t)). exists (fun r1 r2 => True).
        split; [| split; [|split]].
      + cbn. rewrite Eq.bind_ret_l. reflexivity.
      + do 2 red. intros; subst. reflexivity.
  Abort.
*)  
    
  
  Lemma case_prop_handler_correct:
    forall {E1 E2 F}
      (h1_spec: E1 ~> PropT F)
      (h2_spec: E2 ~> PropT F)
      (h1: E1 ~> itree F)
      (h2: E2 ~> itree F)
      (C1: handler_correct h1_spec h1)
      (C2: handler_correct h2_spec h2),
      handler_correct (case_ h1_spec h2_spec) (case_ h1 h2).
  Proof using.
    intros E1 E2 F h1_spec h2_spec h1 h2 C1 C2.
    unfold handler_correct in *.
    intros T e.
    destruct e. apply C1. apply C2.
  Qed.


  Definition prop_compose :=
    fun {F G : Type -> Type } {T : Type} (TT : relation T)
      (g_spec : F ~> PropT G) (PF: PropT F T) (g:itree G T) =>
      exists f : itree F T, PF f /\ (interp_prop g_spec) T TT f g.


  Definition handler_correct_prop
             {E F G}
             (h_spec: E ~> PropT F) (h: E ~> itree F)
             (g_spec: F ~> PropT G) (g: F ~> itree G)
    :=
      (forall T TT e,
          (prop_compose TT g_spec (h_spec T e))
            (interp g (h T e))).

  
  Definition singletonT {E}: itree E ~> PropT E :=
    fun R t t' => t' ≈ t.

  Definition iter_cont {I E R} (step' : I -> itree E (I + R)) :
    I + R -> itree E R :=
    fun lr => ITree.on_left lr l (Tau (ITree.iter step' l)).

  Global Polymorphic Instance MonadIter_Prop {E} : MonadIter (PropT E) :=
    fun R I (step : I -> PropT E (I + R)) i =>
      fun (r : itree E R) =>
        (exists (step' : I -> (itree E (I + R)%type)),
                ITree.bind (step' i) (@iter_cont I E R step') ≈ r /\
                (forall j, step j (step' j))).

  Lemma eqit_bind_Returns_inv {E} {R S T} (RS : R -> S -> Prop) 
        (t : itree E T)  (k1: T -> itree E R) (k2 : T -> itree E S) :
    (eutt RS  (ITree.bind t k1) (ITree.bind t k2)) ->
    (forall r, Returns r t -> eutt RS (k1 r) (k2 r)).
  Proof using.
    intros EQIT r HRET.
    revert R S RS k1 k2 EQIT.
    induction HRET; intros.
    - rewrite H in EQIT.
      do 2 rewrite Eq.bind_ret_l in EQIT.
      assumption.
    - rewrite tau_eutt in H. rewrite H in EQIT.
      eapply IHHRET; eauto.
    - rewrite H in EQIT.
      do 2 rewrite Eq.bind_vis in EQIT.
      repeat red in EQIT. punfold EQIT.
      inversion EQIT.
      apply inj_pair2 in H2.
      apply inj_pair2 in H3.
      apply inj_pair2 in H4.
      apply inj_pair2 in H5.
      subst.
      eapply IHHRET.
      specialize (REL x).
      red in REL.
      pclearbot.
      apply REL.
  Qed.

  Section ReturnsBind.

    Context {E : Type -> Type} {R S : Type}. 

    Import ITreeNotations.
    Local Open Scope itree.

    Inductive eqit_Returns_bind_clo b1 b2 (r : itree E R -> itree E S -> Prop) :
      itree E R -> itree E S -> Prop :=
    | pbc_intro_h U (t1 t2: itree E U) (k1 : U -> itree E R) (k2 : U -> itree E S)
                  (EQV: eqit eq b1 b2 t1 t2)
                  (REL: forall u, Returns u t1 -> r (k1 u) (k2 u))
      : eqit_Returns_bind_clo b1 b2 r (ITree.bind t1 k1) (ITree.bind t2 k2)
    .
    Hint Constructors eqit_Returns_bind_clo: core.

    Lemma eqit_Returns_clo_bind  (RS : R -> S -> Prop) b1 b2 vclo
          (MON: monotone2 vclo)
          (CMP: compose (eqitC RS b1 b2) vclo <3= compose vclo (eqitC RS b1 b2))
          (ID: id <3= vclo):
      eqit_Returns_bind_clo b1 b2 <3= gupaco2 (eqit_ RS b1 b2 vclo) (eqitC RS b1 b2).
    Proof using.
      gcofix CIH. intros. destruct PR.
      guclo eqit_clo_trans.
      econstructor; auto_ctrans_eq; try (rewrite (itree_eta (x <- _;; _ x)), unfold_bind; reflexivity).
      punfold EQV. unfold_eqit.
      genobs t1 ot1.
      genobs t2 ot2.
      hinduction EQV before CIH; intros; pclearbot.
      - guclo eqit_clo_trans.
        econstructor; auto_ctrans_eq; try (rewrite <- !itree_eta; reflexivity).
        gbase; cbn.
        apply REL0.
        rewrite itree_eta, <- Heqot1; constructor; reflexivity.
      - gstep. econstructor.
        gbase.
        apply CIH.
        constructor; auto.
        intros u HR.
        apply REL0.
        rewrite itree_eta,  <- Heqot1.  econstructor 2. reflexivity. assumption.
      - gstep. econstructor.
        intros; apply ID; unfold id.
        gbase.
        apply CIH.
        constructor; auto.
        intros ? HR; apply REL0.
        rewrite itree_eta, <- Heqot1.
        econstructor 3; eauto; reflexivity.
      - destruct b1; try discriminate.
        guclo eqit_clo_trans.
        econstructor.
        3:{ eapply IHEQV; eauto.
            intros ? HR; apply REL.
            rewrite itree_eta, <- Heqot1; econstructor 2. reflexivity. eauto.
        }
        3,4:auto_ctrans_eq.
        2: reflexivity.
        eapply eqit_tauL. rewrite unfold_bind, <-itree_eta. reflexivity.
      - destruct b2; try discriminate.
        guclo eqit_clo_trans.
        econstructor; auto_ctrans_eq; cycle -1; eauto; try reflexivity.
        eapply eqit_tauL. rewrite unfold_bind, <-itree_eta. reflexivity.
    Qed.

  End ReturnsBind.

    Lemma eqit_Returns_bind' {E} {R} {T} b1 b2
          (t1 t2: itree E T) (k1 k2: T -> itree E R) :
      eqit eq b1 b2 t1 t2 ->
      (forall r, Returns r t1 -> eqit eq b1 b2 (k1 r) (k2 r)) ->
      @eqit E _ _ eq b1 b2 (ITree.bind t1 k1) (ITree.bind t2 k2).
    Proof using.
      intros. ginit. guclo (@eqit_Returns_clo_bind E R R eq). unfold eqit in *.
      econstructor; eauto with paco.
    Qed.

    Lemma eqit_Returns_bind'' {E} {R S} {T} (RS : R -> S -> Prop) b1 b2
          (t1 t2: itree E T) (k1: T -> itree E R) (k2 : T -> itree E S) :
      eqit eq b1 b2 t1 t2 ->
      (forall r, Returns r t1 -> eqit RS b1 b2 (k1 r) (k2 r)) ->
      @eqit E _ _ RS b1 b2 (ITree.bind t1 k1) (ITree.bind t2 k2).
    Proof using.
      intros. ginit. guclo (@eqit_Returns_clo_bind E R S RS). unfold eqit in *.
      econstructor; eauto with paco.
    Qed.


  Lemma eutt_ret_vis_abs: forall {X Y E} (x: X) (e: E Y) k, Ret x ≈ Vis e k -> False.
  Proof using.
    intros.
    punfold H; inv H.
  Qed.

  Lemma Returns_Ret_ : forall E A (a x : A) (t:itree E A), t ≈ Ret x -> Returns a t -> x = a.
  Proof using.
    intros E A a x t eq H. 
    induction H.
    - rewrite eq in H. eapply eutt_inv_ret. apply H.
     - rewrite tau_eutt in H. rewrite <- H in IHReturns. apply IHReturns. assumption.
    - rewrite eq in H. apply eqit_inv_ret_vis in H. contradiction.
  Qed.

  Lemma Returns_Ret :  forall E A (a x : A), Returns a ((Ret x) : itree E A) -> x = a.
  Proof using.
    intros.  eapply Returns_Ret_. 2: eassumption. reflexivity.
  Qed.

  Lemma Returns_bind : forall E A B a b (ma : itree E A) (k : A -> itree E B)
    (HM: Returns a ma)
    (HK: Returns b (k a)),
      Returns b (bind ma k).
  Proof using.
    intros.
    revert B b k HK.
    induction HM; intros.
    - rewrite H. cbn. rewrite Eq.bind_ret_l. assumption.
    - rewrite H. cbn. rewrite Eq.bind_tau. rewrite tau_eutt. apply IHHM. assumption.
    - rewrite H. cbn. rewrite Eq.bind_vis. econstructor 3. reflexivity. apply IHHM. assumption.
  Qed.
  
  Lemma Returns_bind_inversion_ : forall {E A B} (u : itree E B) (t : itree E A) (k : A -> itree E B) b,
      Returns b u ->
      u ≈ (bind t k) ->
      exists a, Returns a t /\ Returns b (k a).
  Proof using.
    intros E A B u t k b HR eq. 
    revert A t k eq.
    induction HR; intros.
    - rewrite eq in H.
      apply eutt_inv_bind_ret in H.
      destruct H as (a & HEQ & HK).
      exists a. split. rewrite HEQ. constructor. reflexivity. rewrite HK. constructor. reflexivity.
    - rewrite tau_eutt in H.
      eapply IHHR. rewrite <- H. assumption.
    - rewrite eq in H; clear eq.
      apply eutt_inv_bind_vis in H.
      destruct H as [(kx & HV & eq2) | (a & HRA & KA)].
      + setoid_rewrite HV.
        specialize (eq2 x).
        setoid_rewrite <- eq2 in IHHR.
        specialize (IHHR _ (kx x) k0).
        assert (ITree.bind (kx x) k0 ≈ bind (kx x) k0) by reflexivity.
        apply IHHR in H.
        destruct H as (a & HRet & HK).
        exists a. split.  econstructor 3. reflexivity. apply HRet. assumption.
      + exists a. split.
        rewrite HRA. constructor 1. reflexivity.
        specialize (IHHR _ (ret x) k).
        assert (k x ≈ bind (ret x) k).
        { rewrite bind_ret_l. reflexivity. }
        apply IHHR  in H. rewrite KA.
        destruct H as (x' & _ & HX).
        econstructor 3. reflexivity.  apply HX.
  Qed.

  Lemma Returns_bind_inversion : forall {E A B} (t : itree E A) (k : A -> itree E B) b,
      Returns b (bind t k) ->
      exists a, Returns a t /\ Returns b (k a).
  Proof using.
    intros.
    eapply Returns_bind_inversion_. apply H. reflexivity.
  Qed.

  Lemma Returns_vis_inversion_ : forall {E A B} (u : itree E B) (e : E A) (k : A -> itree E B) b,
      Returns b u ->
      u ≈ (Vis e k) ->
      exists a, Returns b (k a).
  Proof using.
    intros E A B u e k b HR eq. 
    revert A e k eq.
    induction HR; intros.
    - rewrite H in eq.
      apply eutt_inv_ret_vis in eq. inversion eq.
    - rewrite tau_eutt in H.
      eapply IHHR. rewrite <- H. apply eq.
    - rewrite eq in H; clear eq.
      punfold H.
      repeat red in H.
      simpl in H.
      inversion H. subst.
      apply inj_pair2 in H2.
      apply inj_pair2 in H3.
      apply inj_pair2 in H6.
      apply inj_pair2 in H5.
      subst.
      assert (Vis e k0 ≈ Vis e k).
      red. red. pfold. red. apply H.
      apply eqit_inv_vis in H0.
      destruct H0 as (_ & HX).
      exists x. specialize (HX x).
      rewrite HX. assumption.
  Qed.

  Lemma Returns_vis_inversion : forall {E A B} (e : E A) (k : A -> itree E B) b,
      Returns b (Vis e k) ->
      exists a, Returns b (k a).
  Proof using.
    intros.
    eapply Returns_vis_inversion_. apply H. reflexivity.
  Qed.

  (*
  Lemma interp_prop_bind_clo :
    forall E F (h_spec : E ~> PropT F) A B
      (HP : forall T, Proper (eq ==> Eq1_PropT T) (h_spec T))
      (t1 : itree E A) (t2 : itree F A)
      (k1 : A -> itree E B) (k2 : A -> itree F B)
      (HT : interp_prop h_spec A eq t1 t2)
      (HK :  forall (a : A), Returns a t2 -> interp_prop h_spec B eq (k1 a) (k2 a)),
      interp_prop h_spec B eq (ITree.bind t1 k1) (ITree.bind t2 k2).
  Proof using.
  Admitted.

  
  Lemma interp_prop_bind :
    forall E F (h_spec : E ~> PropT F) R S
      (HP : forall T, Proper (eq ==> Eq1_PropT T) (h_spec T))
      (m : itree E S)
      (k : S -> itree E R)
    , Eq1_PropT _ (interp_prop h_spec R eq (bind m k)) (bind (interp_prop h_spec S eq m) (fun x => interp_prop h_spec R eq (k x))).
  Proof using.
    intros.
    split; [|split].
    - intros; split; intro HQ.
      + (* SAZ: Thiis direction is the impossible one *)
        rewrite H in HQ. clear H.
        setoid_rewrite (itree_eta m) in HQ.
        repeat red.
        setoid_rewrite (itree_eta m).

        destruct (observe m).
        * setoid_rewrite Eq.bind_ret_l in HQ.
          exists (ret r). exists (fun _ => y).
          split; [| split].
          -- repeat red. pstep. red. econstructor. reflexivity. reflexivity.
          -- unfold bind, Monad_itree. cbn. rewrite Eq.bind_ret_l. reflexivity.
          -- intros. apply Returns_ret_inv in H. subst. assumption.
        * setoid_rewrite Eq.bind_tau in HQ. setoid_rewrite tau_eutt in HQ.
          setoid_rewrite tau_eutt.
          punfold HQ. red in HQ.
          admit.
        * setoid_rewrite Eq.bind_vis in HQ.
          apply interp_prop_vis_inv in HQ.
          destruct HQ as (ms & ks & HX & eq2).
          admit.
      + rewrite H. clear H.
        repeat red in HQ.
        setoid_rewrite (itree_eta m). setoid_rewrite (itree_eta m) in HQ.
        destruct (observe m).
        * destruct HQ as (ta & k0 & HI & eq2 & KK).
          pinversion HI; subst.
          rewrite eq0 in eq2. unfold bind, Monad_itree in *. rewrite Eq.bind_ret_l.
          rewrite Eq.bind_ret_l in eq2. rewrite eq2. eapply KK. rewrite eq0. econstructor. reflexivity.
        * destruct HQ as (ta & k0 & HI & eq2 & KK).
          pinversion HI; subst.
          unfold bind, Monad_itree in *.
          rewrite Eq.bind_tau. rewrite tau_eutt. rewrite eq2.
          eapply interp_prop_bind_clo. assumption.
          apply HS. apply KK.
        * destruct HQ as (ta & k1 & HI & eq2 & KK).
          pinversion HI; subst; clear HI.
          apply inj_pair2 in H1. apply inj_pair2 in H2.
          subst.
          unfold bind, Monad_itree in *.

          rewrite eq0 in eq2. rewrite Eq.bind_bind in eq2. rewrite eq2.
          rewrite Eq.bind_vis. pstep. red. econstructor.
          apply HTA. unfold bind, Monad_itree.
          red. unfold Eq1_ITree. reflexivity.
          intros.
          left. (* todo : interp_prop_bind_clo *)
          eapply interp_prop_bind_clo.
          assumption.
          specialize (HK a H). pclearbot. apply HK.
          intros. apply KK. rewrite eq0. 
          eapply Returns_bind; eauto.
  Admitted.          
*)
  
  

  Definition divergent {E A} (ta : itree E A) := (forall k , ta ≈ bind ta k).

  Lemma Returns_divergent {E A}:
    (forall (ta : itree E A), not (exists a, Returns a ta) -> divergent ta).
  Proof using.
    intros. red. intros. red in H.
    unfold bind, Monad_itree.
    generalize dependent ta. pcofix CIH. cbn. pstep. unfold eqit_.
    intros. remember (observe ta). destruct i.
    - destruct H0. assert (ta ≈ Ret r0). rewrite Heqi.
      rewrite <- itree_eta. reflexivity. exists r0. constructor. auto.
    - intros. rewrite unfold_bind_. cbn. rewrite <- Heqi. cbn.
      constructor. right. apply CIH. intros. destruct H. destruct H0.
      assert (ta ≈ Tau t). rewrite Heqi. rewrite <- itree_eta; reflexivity.
      eapply ReturnsTau in H; eauto.
    - rewrite unfold_bind_. cbn. rewrite <- Heqi. cbn. constructor. intros.
      unfold id. right. apply CIH. intros. destruct H. destruct H0.
      assert (ta ≈ Vis e k0). rewrite Heqi. rewrite <- itree_eta; reflexivity.
      eapply ReturnsVis in H; eauto.
  Qed.

  Definition divergent_cont {E A B} (ta : itree E A) :=
    (forall (k1 : A -> itree E B) (k2 : A -> itree E B) , bind ta k1 ≈ bind ta k2).

  (*
  Lemma Returns_divergent_cont {E A B}:
    (forall (ta : itree E A), not (exists a, Returns a ta) -> @divergent_cont _ A B ta).
  Proof using.
  Admitted.
   *)
(*
  Global Instance IterUnfold_PropT {E} : IterUnfold (Kleisli (PropT E)) sum.
  Proof using.
    intros A B f. split; [ intros x y EQ | ]; split.
    - intros H. repeat red in H. repeat red.
      destruct H as (step & H).
      exists (step a). exists (iter_cont step).
      destruct H as (BIND & PRED). split. auto.
      split. rewrite <- EQ.
      rewrite BIND. reflexivity.
      intros. repeat red.
      destruct a0.
      + cbn. repeat red. unfold iter_cont.
        setoid_rewrite tau_eutt at 2.
        exists step.
        setoid_rewrite unfold_iter. split; auto. reflexivity.
      + cbn. reflexivity.
    - intros H. repeat red in H. repeat red.
      destruct H as (FIRST & CONT & PRED_FIRST & EQ_Y & PRED).
      unfold iter_cont.
      setoid_rewrite EQ. clear EQ x.
      assert ((exists a, Returns a FIRST) \/ ~ (exists a, Returns a FIRST)).
      apply classic.
      destruct H.
      + destruct H.
        specialize (PRED _ H).
        setoid_rewrite EQ_Y. clear EQ_Y.
        cbn. setoid_rewrite bind_Returns_l. 2 : exact H.
        repeat red in PRED. destruct x.
        * repeat red in PRED.
          destruct PRED as (step & H_BIND & H_PRED).
          unfold iter_cont in H_BIND.
          setoid_rewrite <- H_BIND.
          (* We want an unfolded version of step. *)
          eexists ?[step]. split; auto. admit.
        * cbn in PRED. setoid_rewrite PRED. admit.
      + apply (Returns_divergent_cont (B := B)) in H. red in H.
        cbn in H. setoid_rewrite EQ_Y. cbn. setoid_rewrite <- H.
        (* It doesn't make sense in terms of unfolding a loop body, that
           the first part must return a value...
         *)
        exists (fun x => FIRST). split; auto. admit.
    - repeat intro. repeat red. intuition.
      repeat red in H0.
      repeat red. setoid_rewrite <- H. auto.
      repeat red in H0.
      repeat red. setoid_rewrite H. auto.
    - repeat intro. repeat red. intuition.
      repeat red in H0.
      repeat red. setoid_rewrite <- H. auto.
      repeat red in H0.
      repeat red. setoid_rewrite H. auto.
  Admitted.
*)
  (* SAZ: maybe define directly by coinduction  *)
  (* Global Polymorphic Instance MonadIter_Prop {E} : MonadIter (PropT E) := *)
  (*   fun R I (step : I -> PropT E (I + R)) i => *)
  (*     fun (r : itree E R) => *)
  (*       (exists step' : I * nat -> (itree E (I + R)%type), *)
  (*           (forall (j : I) (n : nat), *)
  (*              (* a, *) *)
  (*               (* Returns a (step' (j, n)) -> *) *)
  (*                 step j (step' (j, n))) /\ *)
  (*           (let body := *)
  (*             fun '(x, k) => *)
  (*               bind (step' (x, k)) *)
  (*                 (fun ir : I + R => *)
  (*                   match ir with *)
  (*                   | inl i0 => ret (inl (i0, S k)) *)
  (*                   | inr r0 => ret (inr r0) *)
  (*                   end) in *)

  (*            CategoryOps.iter body (i, 0)) ≈ r). *)

End PropMonad.


Section IterLaws.

  Ltac simpl_iter :=
      unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree.

  Definition g {a b : Type} {E} (x0 : a * nat -> itree E (a + b)) (a1 : a)
    := (fun '(x, k) =>
            bind (x0 (x, k))
                (fun ir : a + b =>
                    match ir with
                    | inl i0 => ret (inl (i0, k))
                    | inr r0 => ret (inr r0)
                    end)).

  Definition f {a b : Type} {E} : a * nat  -> itree E (a * nat + b) :=
    fun '(x, k) => ret (inl ((x, S k))).

  Lemma iter_succ_dinatural:
    forall {a b : Type} {E} (x0 : a * nat -> itree E (a + b)) (a1 : a),
      iter (C := Kleisli (itree E)) (bif := sum)
           (f >>> case_ (g x0 a1) inr_)
       ⩯
       f >>> case_ (iter (C := Kleisli (itree E)) (bif := sum) ((g x0 a1) >>> (case_ f inr_))) (id_ _).
  Proof using.
    intros. rewrite iter_dinatural. reflexivity.
  Qed.

  Lemma iter_eq_start_index:
    forall (a b : Type) (E : Type -> Type) (x0 : a * nat -> itree E (a + b)) (a1 : a),
      iter (C := Kleisli (itree E)) (bif := sum)
        (fun '(x, k) =>
            bind (x0 (x, S k))
                (fun ir : a + b =>
                    match ir with
                    | inl i0 => ret (inl (i0, S k))
                    | inr r0 => ret (inr r0)
                    end)) (a1, 0)
        ≈ iter (C := Kleisli (itree E)) (bif := sum)
        (fun '(x', k) =>
            bind (x0 (x', k))
                (fun ir : a + b =>
                    match ir with
                    | inl i0 => ret (inl (i0, S k))
                    | inr r0 => ret (inr r0)
                    end)) (a1, 1).
  Proof using.
    intros a b m x0 a1.
    pose proof (iter_succ_dinatural x0 a1) as H0.
    specialize (H0 (a1, 0)).
    unfold f at 1, g at 1 in H0.
    unfold cat at 1, Cat_Kleisli at 1 in H0.
    match goal with
    | H : ?body1 ≈ _ |- ?body2 ≈ _ => remember body1 as s1;
                                                 remember body2 as s2
    end.
    assert (s1 ≈ s2). {
      subst.
      match goal with
      | |- iter ?body1 _ ≈ iter ?body2 _ => remember body1 as k1;
                                            remember body2 as k2
      end.
      assert (iter k1 ⩯ iter k2). {
        eapply iterative_proper_iter.
        subst. do 3 red. intros.
        destruct a0; rewrite bind_ret_l; cbn.
        reflexivity.
      }
      do 3 red in H.
      apply H.
    }
    rewrite <- H. subst. clear H. rewrite H0.
    unfold f, g.
    unfold cat, Cat_Kleisli. rewrite bind_ret_l.
    cbn.
    match goal with
    | |- iter ?body1 _ ≈ iter ?body2 _ => remember body1 as i1; remember body2 as i2
     end.
    assert (iter i1 ⩯ iter i2). {
      eapply iterative_proper_iter.
      subst.
      do 3 red. intros.
      destruct a0. rewrite Eq.bind_bind.
      eapply eutt_clo_bind. reflexivity.
      intros. rewrite H. destruct u2;
      rewrite Eq.bind_ret_l; cbn; reflexivity.
    }
    do 3 red in H.
    apply H.
  Qed.

  (* If needed back, should rephrase the _iter continuation *)
  (* Lemma simplify_bind_match {E A B}: *)
  (*   forall x BODY, *)
  (*    ITree.bind *)
  (*      match x with *)
  (*      | inl i0 => Ret (inl (i0, 1)) *)
  (*      | inr r0 => Ret (inr r0) *)
  (*      end *)
  (*      (ITree._iter (fun t : itree E B => Tau t) *)
  (*         (ITree.iter *)
  (*            (fun '(x, k) => *)
  (*             ITree.bind (BODY (x, k)) *)
  (*               (fun ir : A + B => *)
  (*                match ir with *)
  (*                | inl i0 => Ret (inl (i0, S k)) *)
  (*                | inr r0 => Ret (inr r0) *)
  (*                end)))) *)
  (*     ≈ *)
  (*     match x with *)
  (*     | inl l => *)
  (*         (ITree.iter *)
  (*             (fun '(x0, k) => *)
  (*             ITree.bind (BODY (x0, k)) *)
  (*               (fun ir : A + B => *)
  (*                 match ir with *)
  (*                 | inl i0 => Ret (inl (i0, S k)) *)
  (*                 | inr r0 => Ret (inr r0) *)
  (*                 end))) (l, 1) *)
  (*     | inr r => Ret r end. *)
  (* Proof using. *)
  (*   intros. destruct x. rewrite Eq.bind_ret_l. cbn. rewrite tau_eutt. *)
  (*   reflexivity. rewrite Eq.bind_ret_l. reflexivity. *)
  (* Qed. *)

  (*
  Global Instance IterUnfold_PropT {E} : IterUnfold (Kleisli (PropT E)) sum.
    intros A B Pstep a.
    repeat red. split; [ intros x y EQ | ]; split.
  - (* Show that there is some looping itree body that Pstep can unfold into. *)
    intros LOOP. repeat red. repeat red in LOOP.
    setoid_rewrite <- EQ. clear EQ y.
    destruct LOOP as (BODY & PROP & RESULT).
    exists (BODY (a, 0)).
    exists (fun x : A + B =>
         match x with
         | inl l =>
              (ITree.iter
                  (fun '(x0, k) =>
                  ITree.bind (BODY (x0, k))
                    (fun ir : A + B =>
                      match ir with
                      | inl i0 => Ret (inl (i0, S k))
                      | inr r0 => Ret (inr r0)
                      end))) (l, 1)
         | inr r => Ret r end).
    split. auto. split.
    + (* Proposition holds over first part of computation. *)
      rewrite <- RESULT. simpl_iter.
      rewrite unfold_iter. cbn. rewrite Eq.bind_bind.
      eapply eutt_clo_bind. reflexivity.
      intros. rewrite <- H. destruct u1. rewrite Eq.bind_ret_l.
      cbn. rewrite tau_eutt. reflexivity.
      rewrite Eq.bind_ret_l. cbn. reflexivity.
    + (* There is some continuation that satisfies the computation. *)
      intros ab RET. repeat red.
      destruct ab eqn: H_ab.
      * (* Keep loopin' *)
        cbn. repeat red.
        exists (fun x : A * nat => BODY (fst x, S( snd x ))). split; auto.
        simpl_iter. cbn.
        (* rewrite Eq.bind_ret_l. cbn. rewrite tau_eutt. *)
        pose proof iter_eq_start_index.
        unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree in H.
        specialize (H _ _ _ BODY). apply H.
      * cbn. reflexivity.
  - (* An unfolded PropT implies a folded loop. *)
    (*      cat Pstep (case_ (iter Pstep) (id_ B)) a y -> iter Pstep a x      *)
    cbn. unfold bind_PropT.

    intros UNFOLD. repeat red. setoid_rewrite EQ. clear EQ x.
    destruct UNFOLD as (FIRST & CONTINUATION & FIRST_PROP & BIND_EQ &
                        CONT_PROP).
    (* Perhaps Returns should be a coinductive proposition?  =>
       Tried short experiment above, was not working out cleanly..
       Not convinced that a coinductive definition will give us more expressive
       power. We seem to be missing some other kind of information.
     *)

    simpl_iter. setoid_rewrite unfold_iter.
    setoid_rewrite BIND_EQ.
    eexists ?[step'].
    assert ((?step' (a, 0)) ≈ FIRST) as H. admit.
    split.
    (* IDEA? : Don't hold propositions holding over all index j, but
       up to a finite unfolding of the step' body. *)
    + intros.
      admit.
    + cbn. rewrite Eq.bind_bind.
      setoid_rewrite simplify_bind_match.
      eapply eutt_clo_bind. rewrite H. reflexivity.
      repeat intro. clear H0.
      destruct u1.
      * rewrite unfold_iter.
        rewrite Eq.bind_bind.
        destruct (observe FIRST) eqn: OBSERVE_STEP; cbn.
        -- admit.
        -- admit.
        -- admit.
      * exfalso. (* Should never be reached.... *) admit.
   (* + eapply eutt_clo_bind. reflexivity. intros. rewrite H. *)
   (*    clear H u1. destruct u2. *)
   (*    * rewrite Eq.bind_ret_l. cbn. rewrite tau_eutt. *)
   (*      rewrite unfold_iter. cbn. rewrite Eq.bind_bind. *)

    (* If we unfold a loop, the idea should be that the unfolded part is going
     * to ... terminate, right? It isn't necessarily a return, though. *)
    (* assert (FIRST_SHOULD_RETURN: exists a : A + B, Returns a FIRST). admit. *)
    (* destruct FIRST_SHOULD_RETURN as (AB & RETURN_FIRST). *)
    (* specialize (CONT_PROP _ RETURN_FIRST). *)

    (* I think that what we need to do, actually, is to encode "Returns" in
       the iter instance. This is because the definition of "iter" needs to
       coincide with how "bind" is defined for PropT.

       Let's think about how to define an "iterative PropT", by example.

     *)

    (* ... For this direction, it seems necessary to index the loop body, since
     the unfolded iter case is strictly more expressive than the folded body.

     Another idea suggestion, from Yannick: try expressing with (option itree),
     intuitively this makes a lot of sense since the empty predicate cannot
     be expressed by an itree, and there might be indices in the loop body
     that map to the empty predicate.
     *)
  - repeat intro. repeat red.
    simpl_iter. unfold MonadIter_Prop. setoid_rewrite H.
    auto.
  - repeat intro. repeat red.
    unfold cat, Cat_Kleisli. cbn. unfold bind_PropT.
    intuition.
    setoid_rewrite <- H. auto.
    setoid_rewrite H. auto.
  Admitted.


  Global Instance IterDinatural_PropT {E} : IterDinatural (Kleisli (PropT E)) sum.
  intros A B C f g.
  split; [intros x y EQ | ]; split.
  - intros H. repeat red. repeat red in H. setoid_rewrite <- EQ. clear EQ y.
    destruct H as (STEP & FST & CONT).
    repeat red in FST.
    specialize (FST a 0).
    edestruct FST as (ta & k & H_fa & H_step & H_cont). clear FST.
    exists ta.
    unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree in CONT.
    rewrite unfold_iter in CONT. cbn in CONT.
    rewrite Eq.bind_bind in CONT.
    (* exists (fun bc => ITree.bind *)
    (*             (match r with *)
    (*                inl *)
    (*             ) *)
    (*   ) *)
    (* bind t *)
    (* exists *)
    admit.
  - admit.
  - repeat red. intros. intuition.
    repeat red. setoid_rewrite <- H. auto.
    repeat red. setoid_rewrite H. auto.
  - repeat red. intros. intuition.
    repeat red. setoid_rewrite <- H. auto.
    repeat red. setoid_rewrite H. auto.
  Admitted.

  Global Instance IterCodiagonal_PropT {E} :  IterCodiagonal (Kleisli (PropT E)) sum.
  Admitted.
*)

End IterLaws.  


Section MonadLaws.



  Definition Eq1_PropT' {E} : Eq1 (PropT E) :=
    fun a PA PA' =>
      (forall x, (PA x -> exists y, x ≈ y /\ PA' y)) /\
      (forall y, (PA' y -> exists x, x ≈ y /\ PA x)) /\
      eutt_closed PA /\ eutt_closed PA'.

  Lemma Eq1_PropT'_Eq1_PropT : forall E a PA PA', @Eq1_PropT E a PA PA' -> Eq1_PropT' a PA PA'.
  Proof using.
    intros.
    red.
    red in H.
    destruct H as (HXY & EPA & EPA').
    split.
    intros.
    exists x. split; [reflexivity|]. specialize (HXY x x).  apply HXY. reflexivity. assumption.
    split; try tauto.
    intros. 
    exists y. split; [reflexivity|]. specialize (HXY y y).  apply HXY. reflexivity. assumption.
 Qed.

  
  (* Figure 8: ret_bind law for PropT  - first law *)
  Lemma ret_bind: forall {E} (a b : Type) (f : a -> PropT E b) (x : a),
      eutt_closed (f x) ->
      eq1 (bind (ret x) f) (f x).
  Proof using.
    intros.
    split; [| split].
    - intros t t' eq; split; intros eqtt'.
      * cbn in *.
        repeat red in eqtt'.
        destruct eqtt' as (ta & k & EQ1 & EQ2 & KA).
      + unfold bind, Monad_itree in EQ2. rewrite EQ1, Eq.bind_ret_l, eq in EQ2.
        eapply H; [apply EQ2 | apply KA].
        constructor 1; eauto.
     * cbn.
       exists (Ret x), (fun _ => t); split; [reflexivity|]; split.
        + unfold bind, Monad_itree. rewrite Eq.bind_ret_l; reflexivity.
        + intros.
          apply Returns_Ret in H0. subst. red in H. rewrite eq.
          assumption.

    - intros t t' EQ; cbn; split; intros HX.
      * destruct HX as (ta & k & EQ1 & EQ2 & KA).
        exists (Ret x), (fun _ => t); split; [reflexivity |]; split.
        --  unfold bind, Monad_itree. rewrite Eq.bind_ret_l. symmetry. assumption.
        -- 
          intros ? RET; inv RET.
          2: { rewrite tau_eutt in H0. rewrite <- H0 in H1. apply Returns_Ret in H1. subst.
               red in H. rewrite EQ2. rewrite EQ1.
               unfold bind, Monad_itree.
               rewrite Eq.bind_ret_l. apply KA. rewrite EQ1. constructor. reflexivity. }
          2: exfalso; eapply eutt_ret_vis_abs; eauto.
          apply eqit_inv_ret in H0; subst.
          eapply H. rewrite EQ1 in EQ2.
          unfold bind, Monad_itree in EQ2.
             rewrite Eq.bind_ret_l in EQ2. apply EQ2.
             apply KA; rewrite EQ1; constructor; reflexivity.

      * destruct HX as (ta & k & EQ1 & EQ2 & KA).
        exists (Ret x), (fun _ => t); split; [reflexivity |]; split.
        --  unfold bind, Monad_itree. rewrite Eq.bind_ret_l. reflexivity.
        -- 
          intros ? RET; inv RET.
          2: { rewrite tau_eutt in H0. rewrite <- H0 in H1. apply Returns_Ret in H1. subst.
               red in H. rewrite EQ. rewrite EQ2. rewrite EQ1.
               unfold bind, Monad_itree.
               rewrite Eq.bind_ret_l. apply KA; rewrite EQ1; constructor 1; reflexivity. 
          }
          2: exfalso; eapply eutt_ret_vis_abs; eauto.
          
          apply eqit_inv_ret in H0; subst.
          red in H.
          rewrite EQ, EQ2, EQ1.
          unfold bind, Monad_itree.
          rewrite Eq.bind_ret_l.
          apply KA; rewrite EQ1; constructor; reflexivity.
    - assumption.
  Qed.
  


   Global Instance bind_PropT_Proper {E} {A B} :
     Proper (eq1 ==> (eq ==> eq1) ==> eutt eq ==> iff) (@bind_PropT E A B).
   Proof using.
     repeat red; intros PA1 PA2 EQP K1 K2 EQK t1 t2 EQt; split; intros H.
     - destruct H as (ta & k & HA & eq & HK).
       red.
       exists ta, k. split.
       + destruct EQP. apply (H ta ta). reflexivity. assumption.
       + split. rewrite <- EQt. assumption. intros.
         repeat red in EQK.  specialize (EQK a a eq_refl). destruct EQK.
         rewrite <- H0. apply HK. assumption. reflexivity.
    -  destruct H as (ta & k & HA & eq & HK).
       red.
       exists ta, k. split.
       + destruct EQP. apply (H ta ta). reflexivity. assumption.
       + split. rewrite EQt. assumption. intros.
         repeat red in EQK.  specialize (EQK a a eq_refl). destruct EQK.
         rewrite H0. apply HK. assumption. reflexivity.
   Qed.

   Global Instance bind_Propt_Proper2 {E} {A B} (PA : PropT E A) (K : A -> PropT E B) :
     Proper (eutt eq ==> flip impl) (bind PA K).
   Proof using.
     repeat red.
     intros.
     repeat red in H0.
     destruct H0 as (ta & k & HA & eq & HK).
     exists ta, k. split; auto. split. rewrite H; auto. assumption.
   Qed.

   
  Definition agrees_itree {E} {A} (ta1 : itree E A) (ta2 : itree E (A -> Prop)) :=
    eutt (fun a p => p a) ta1 ta2.
  
  Definition bind_stronger {E} := 
    fun A B (PA: PropT E A) (K: A -> PropT E B) (tb: itree E B) =>
      exists (ta: itree E A),  PA ta /\
                          (exists (k: A -> itree E B),
                               (agrees_itree (fmap k ta) (fmap K ta)
                               /\ tb ≈ bind ta k)).


  
  Lemma agree_itree_Returns : forall E A B (ta : itree E A) (K : A -> PropT E B) (k : A -> itree E B),
      (forall a, Returns a ta -> K a (k a)) <-> (agrees_itree (fmap k ta) (fmap K ta)).
  Proof using.
    intros.
    split; intros.
    - cbn. red.
      unfold ITree.map.
      eapply eqit_Returns_bind''.
      + reflexivity.
      + intros. apply eqit_Ret. apply H. assumption.
    - revert B K k H.
      induction H0.
      + intros. cbn in H0. unfold agrees_itree in H0.
        unfold ITree.map in H0.
        rewrite H in H0.
        do 2 rewrite Eq.bind_ret_l in H0.
        apply Eq.eqit_Ret in H0. assumption.
      + intros.
        rewrite tau_eutt in H.
        unfold agrees_itree in H1.
        setoid_rewrite H in H1.
        eapply IHReturns. unfold agrees_itree.
        apply H1.
      + intros.
        apply IHReturns; clear IHReturns.
        unfold agrees_itree in *.
        setoid_rewrite H in H1.
        cbn in *. unfold ITree.map in *.
        repeat red in H1.
        punfold H1.
        inversion H1. cbn in *.
        subst.
        apply inj_pair2 in H4.
        apply inj_pair2 in H5.
        apply inj_pair2 in H6.
        apply inj_pair2 in H7.
        subst.
        
        
        apply eqit_Returns_bind''.
        * reflexivity.
        * intros. subst.
          apply Eq.eqit_Ret.
          specialize (REL x).
          red in REL. 
          pclearbot.
          apply eqit_bind_Returns_inv  with (r0:=r) in REL; auto.
          apply eqit_Ret in REL.
          assumption.
  Qed.
          
  
  Lemma distinguish_bind {E} {A B}
        (a : A)
        (ma : itree E A)
        (k1 k2 : A -> itree E B)
        (HRET : Returns a ma)
        (NEQ: ~((k1 a) ≈ (k2 a))) : 
    not ((ITree.bind ma k1) ≈ (ITree.bind ma k2)).
  Proof using.
    intro HI.
    apply NEQ. clear NEQ.
    revert k1 k2 HI.
    induction HRET; intros.
    - rewrite H in HI. cbn in HI. rewrite Eq.bind_ret_l in HI. rewrite Eq.bind_ret_l in HI.
      assumption.
    - apply IHHRET. unfold bind, Monad_itree in HI.
      rewrite H in HI.
      do 2 rewrite Eq.bind_tau in HI.
      do 2 rewrite tau_eutt in HI. apply HI.
    - apply IHHRET. rewrite H in HI.
      do 2 rewrite bind_vis in HI.
      apply eqit_inv_vis in HI.
      destruct HI as (_ & HI).
      apply HI.
  Qed.
  

  Lemma not_Returns {E} {A B} : inhabited B ->
    forall (ta: itree E A), (exists tb, forall (k : A -> itree E B), tb ≈ bind ta k) -> forall (a:A), ~ Returns a ta.
  Proof using.
    intros IB ta HX a HRet; inversion IB; clear IB.
    revert HX.
    induction HRet; intros (tb & HK).
    - setoid_rewrite H in HK.
      unfold bind, Monad_itree in HK.
      setoid_rewrite Eq.bind_ret_l in HK.
      pose (HK (fun _ => ret X)) as t2. cbn in t2.
      pose (HK (fun _ => ITree.spin)) as t3. cbn in t3.
      assert (Ret X ≈ (ITree.spin : itree E B)).
      rewrite <- t2. rewrite <- t3. reflexivity. apply eutt_Ret_spin_abs in H0. 
      auto.
    - apply IHHRet.
      exists tb. intros. 
      specialize (HK k).
      rewrite HK. unfold bind, Monad_itree.
      rewrite H. 
      rewrite bind_tau. apply tau_eutt.
    - setoid_rewrite H in HK; clear H t.
      pose (HK (fun _ => ret X)) as t2. cbn in t2.
      pose (HK (fun _ => ITree.spin)) as t3. cbn in t3.
      assert (ITree.bind (Vis e k) (fun _ : A => Ret X) ≈ ITree.bind (Vis e k) (fun _ : A => ITree.spin)).
      rewrite <- t2. rewrite <- t3.
      reflexivity.
      rewrite bind_vis in H. rewrite bind_vis in H.
      apply eqit_inv_vis in H.
      destruct H as (_ & H).
      specialize (H x).
      revert H.
      change (~((ITree.bind (k x) ( fun _ : A => Ret X)) ≈ ITree.bind (k x) (fun _ : A => ITree.spin))).
      eapply distinguish_bind. apply HRet.
      intro H. apply eutt_Ret_spin_abs in H. auto.
  Qed.      

  (* Figure 8: bind_ret - second monad law for PropT *)  
  Lemma bind_ret: forall {E} (A : Type) (PA : PropT E A),
      eutt_closed PA ->
      eq1 (bind PA (fun x => ret x)) PA.
  Proof using.
    intros.
    split; [| split].
    + intros t t' eq; split; intros eqtt'.
      * cbn in *.
        destruct eqtt' as (ta & k & HPA & EQ & HRET).
        eapply H; [symmetry; eauto | clear eq t'].
        eapply H; [eauto | clear EQ t].
        eapply H; eauto.
        rewrite <- (bind_ret_r _ ta) at 2.
        apply eqit_Returns_bind'; [reflexivity |].
          intros.
          rewrite (HRET r); auto.
          reflexivity.
          
      * cbn.
        exists t', (fun x => Ret x); split; [auto|]; split.
        unfold bind, Monad_itree. rewrite Eq.bind_ret_r; auto.
        intros; reflexivity.
        
    + intros x y EQ; split; intros eqtt'. 
      * cbn in *.
        destruct eqtt' as (ta & k & HPA & EQ' & HRET).
        exists ta, k; split; [auto|]; split; auto.
        rewrite <- EQ; auto.

      * cbn in *.
        destruct eqtt' as (ta & k & HPA & EQ' & HRET).
        exists ta, k; split; [auto|]; split; auto.
        rewrite EQ; auto.
    + auto.
  Qed.

  Definition EQ_REL {E A} (ta : itree E A) : A -> A -> Prop :=
    fun a b => a = b /\ Returns a ta.

  Lemma Symmteric_EQ_REL {E A} (ta : itree E A) : Symmetric (EQ_REL ta).
  Proof using.
    repeat red.
    intros a b (EQ & H).
    split.
    - symmetry. assumption.
    - subst; auto.
  Qed.

  Lemma Transitive_EQ_REL {E A} (ta : itree E A) : Transitive (EQ_REL ta).
  Proof using.
    repeat red.
    intros a b c (EQ1 & H1) (EQ2 & H2).
    split.
    - rewrite EQ1. assumption.
    - assumption.
  Qed.

  Instance EQ_REL_Proper {E A} : Proper (eutt eq ==> eq ==> eq ==> iff) (@EQ_REL E A).
  Proof using.
    repeat red.
    intros. subst.
    split; intros; unfold EQ_REL in *.
    - split. destruct H0. assumption. destruct H0.
      intros. rewrite <- H. assumption.
    - destruct H0.
      split. assumption.
      intros. rewrite H. assumption.
  Qed.
    
  Definition eq_relation {A} (R S : A -> A -> Prop) :=
    R <2= S /\ S <2= R.
  
  Instance eutt_EQ_REL_Proper {E} {A} :
    Proper (eq_relation ==> eutt eq ==> @eutt E A A eq ==> iff) (eutt).
  Proof using.
    repeat red.
    intros; split; intros.
    -  rewrite <- H0. rewrite <- H1.
       clear H0 H1.
       destruct H.
       eapply eqit_mon; eauto.
    - rewrite H0, H1.
      destruct H.
      eapply eqit_mon; eauto.
  Qed.
  
  Lemma eutt_EQ_REL_Reflexive_ {E} {A} (ta : itree E A) :
    forall R, (EQ_REL ta) <2= R ->
    eutt R ta ta.
  Proof using.
    revert ta.
    ginit. gcofix CIH. intros ta HEQ.
    gstep. red.
    genobs ta obs.
    destruct obs.
    - econstructor. apply HEQ. red. split; auto. rewrite itree_eta. rewrite <- Heqobs. constructor 1. reflexivity.
    - econstructor. gbase. apply CIH.
      setoid_rewrite itree_eta in HEQ.
      destruct (observe ta); inversion Heqobs. subst.
      assert (Tau t0 ≈ t0) by apply tau_eutt.
      setoid_rewrite H in HEQ. 
      auto.
    - econstructor.  intros. red. gbase. apply CIH.
      intros. apply HEQ.
      rewrite itree_eta. rewrite <- Heqobs.
      red in PR. destruct PR.
      red. split; auto.
      econstructor 3. reflexivity. apply H0.
  Qed.

  Lemma eutt_EQ_REL_Reflexive {E} {A} (ta : itree E A) : eutt (EQ_REL ta) ta ta.
  Proof using.
    apply eutt_EQ_REL_Reflexive_.
    auto.
  Qed.

  
  (* From Coq.Logic.ChoiceFacts *)
Definition GuardedFunctionalChoice_on {A B} :=
  forall P : A -> Prop, forall R : A -> B -> Prop,
    inhabited B ->
    (forall x : A, P x -> exists y : B, R x y) ->
    (exists f : A->B, forall x, P x -> R x (f x)).
Axiom guarded_choice : forall {A B}, @GuardedFunctionalChoice_on A B.


Definition RET_EQ {E} {A} (ta : itree E A) : A -> A -> Prop :=
  fun x y => Returns x ta /\ Returns y ta.


(*
Lemma commute {E} {A B} (ta : itree E A) 
forall x : A,
       Returns x ta ->
       exists k0 : B -> itree E C,
         KB x (kab x) /\ k x ≈ bind (kab x) k0 /\ (forall a : B, Returns a (kab x) -> KC a (k0 a))
         ->
         exists k0 : B -> itree E C,
forall x : A,
       Returns x ta ->
         KB x (kab x) /\ k x ≈ bind (kab x) k0 /\ (forall a : B, Returns a (kab x) -> KC a (k0 a))
*)

Section BIND_BIND_COUNTEREXAMPLE.

  Inductive ND : Type -> Type :=
  | Pick : ND bool.

  Definition PA : PropT ND bool := fun (ta : itree ND bool) => ta ≈ trigger Pick.

  Definition KB : bool -> PropT ND bool :=
    fun b => PA.

  Definition KC : bool -> PropT ND bool :=
    fun b => if b then (fun tc : itree ND bool => (tc ≈ ret true) \/ (tc ≈ ret false)) else (fun tc : itree ND bool => tc ≈ ITree.spin).

  Definition t : itree ND bool :=
    bind (trigger Pick) (fun (b:bool) => if b
                               then bind (trigger Pick) (fun (x:bool) => if x then ret true else ITree.spin)
                               else bind (trigger Pick) (fun (x:bool)  => if x then ret false else ITree.spin)).

  Lemma bind_right_assoc : bind PA (fun a => bind (KB a) KC) t.
  Proof using.
    repeat red.
    exists (trigger Pick).
    exists (fun (b:bool) => if b
             then (bind (trigger Pick) (fun (x:bool) => if x then ret true else ITree.spin))
             else (bind (trigger Pick) (fun (x:bool) => if x then ret false else ITree.spin))).            
    split; auto.
    red. reflexivity.
    split. reflexivity.
    intros. repeat red. exists (trigger Pick).
    exists (fun (x:bool) => if a
                 then (if x then ret true else ITree.spin)
                 else (if x then ret false else ITree.spin)).
    split.
    red. red.  reflexivity.
    split.
    destruct a.
    - reflexivity.
    - reflexivity.
    - intros.
      destruct a0.
      destruct a.
      red. left. reflexivity.
      red. right. reflexivity.
      destruct a.
      red. reflexivity. red.  reflexivity.
  Qed.

  Lemma not_bind_left_assoc : ~ (bind (bind PA KB) KC t).
  Proof using.
    intro H.
    repeat red in H.
    destruct H as (ta & k & HB & HEQ & HRET).
    destruct HB as (tb & kb & HX & HEQ' & HRET').
    red in HX.
    rewrite HX in *.
    setoid_rewrite HX in HRET'.
    clear tb HX.
    rewrite HEQ' in HEQ.
    unfold t in HEQ.
    unfold bind, Monad_itree in HEQ.
    rewrite Eq.bind_bind in HEQ.
    assert (forall r, Returns r (trigger Pick) -> eutt eq ((fun b : bool =>
           if b
           then ITree.bind (trigger Pick) (fun x : bool => if x then ret true else ITree.spin)
           else ITree.bind (trigger Pick) (fun x : bool => if x then ret false else ITree.spin)) r) ((fun r : bool => ITree.bind (kb r) k) r)).
    apply eqit_bind_Returns_inv. apply HEQ.
    assert (Returns true (trigger Pick)).
    { unfold trigger. econstructor 3. reflexivity. constructor 1. reflexivity. }
    assert (Returns false (trigger Pick)).
    { unfold trigger. econstructor 3. reflexivity. constructor 1. reflexivity. }
    assert (Returns true (trigger Pick)).
    { unfold trigger. econstructor 3. reflexivity. constructor 1. reflexivity. }
    assert (Returns false (trigger Pick)).
    { unfold trigger. econstructor 3. reflexivity. constructor 1. reflexivity. }
    apply H in H0.
    apply H in H1.
    apply HRET' in H2.
    apply HRET' in H3.
    red in H2. red in H3. red in H2. red in H3.
    rewrite H2 in H0.
    rewrite H3 in H1.
    rewrite <- H0 in H1.
    apply eqit_bind_Returns_inv with (r := true) in H1 .
    apply eqit_inv_ret in H1. inversion H1.
    { unfold trigger. econstructor 3. reflexivity. constructor 1. reflexivity. }
Qed.
    
Lemma bind_bind_counterexample: 
      (* eutt_closed PA -> *)
    exists t, bind PA (fun a => bind (KB a) KC) t /\ ~ (bind (bind PA KB) KC t).
Proof using.
  exists t.
  split.
  apply bind_right_assoc.
  apply not_bind_left_assoc.
Qed.  

End BIND_BIND_COUNTEREXAMPLE.


(* Figure 8: 3rd monad law, one direction bind associativity *)
Lemma bind_bind_Prop: forall {E}
                   (A B C : Type) (PA : PropT E A)
                   (KB : A -> PropT E B) (KC : B -> PropT E C)
                   (PQOK : eutt_closed PA)
                   (KBP : Proper (eq ==> eq1) KB)
                   (KCP : Proper (eq ==> eq1) KC)
                   (t : itree E C),
      (bind (bind PA KB) KC) t -> (bind PA (fun a => bind (KB a) KC)) t.
  Proof using.
    (* PA ~a> KB a ~b> KC b *)
    intros E A B C PA KB KC PQOK KBP KCP t eqtt'. 
        red in eqtt'.
        destruct eqtt' as (tb & kbc & (HBC & EQc & HRkbc)).
        destruct HBC as (ta & kab & HTA & EQb & HRkab).
        red. exists ta. exists (fun a => ITree.bind (kab a) kbc).
        split; [auto|]; split.
        * setoid_rewrite EQc; clear EQc.
          setoid_rewrite EQb. setoid_rewrite EQb in HRkbc; clear EQb tb.
          unfold bind, Monad_itree.
          rewrite Eq.bind_bind. reflexivity.
        * intros a HRet.
          exists (kab a), kbc.
          split; [auto|];split.
          -- reflexivity.
          -- intros b HRET. apply HRkbc. rewrite EQb. eapply Returns_bind; eauto.
  Qed.
  


End MonadLaws.
