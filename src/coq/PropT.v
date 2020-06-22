From Coq Require Import Ensembles Setoid Morphisms RelationClasses.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad
     Structures.MonadTrans
     Data.Monads.EitherMonad.

From ITree Require Import
     Basics.Basics
     Eq.Eq
     Eq.UpToTaus
     ITree
     Basics.Monad
     Core.ITreeMonad.

From Paco Require Import paco.

Section PropMonad.

  Definition PropT (E: Type -> Type) (X: Type): Type :=
    itree E X -> Prop.

  Global Instance Functor_Prop {E}
    : Functor (PropT E) :=
    {| fmap := fun A B f PA b => exists (a: itree E A), PA a /\ b = fmap f a |}.

  Inductive Returns {E} {A: Type} (a: A) : itree E A -> Prop :=
  | ReturnsRet: forall t, t ≈ Ret a -> Returns a t
  | ReturnsTau: forall t u, t ≈ Tau u -> Returns a u -> Returns a t
  | ReturnsVis: forall {X} (e: E X) (x: X) t k, t ≈ Vis e k -> Returns a (k x) -> Returns a t
  .
  Hint Constructors Returns: core.

  Definition bind_PropT {E} :=
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
    
  Global Instance Monad_Prop {E} : Monad (PropT E) :=
    {|
      ret := fun _ x y => y ≈ ret x
      ; bind := bind_PropT'
    |}.

  
  (*
  Inductive iter_Prop {R I : Type} (step : I -> I + R -> Prop) (i : I) (r : R)
    : Prop :=
  | iter_done
    : step i (inr r) -> iter_Prop step i r
  | iter_step i'
    : step i (inl i') ->
      iter_Prop step i' r ->
      iter_Prop step i r
  .
  Polymorphic Instance MonadIter_Prop : MonadIter Ensembles.Ensemble := @iter_Prop.
  *)

  (* SAZ: maybe define directly by coinduction  *)
  Global Polymorphic Instance MonadIter_Prop {E} : MonadIter (PropT E) :=
    fun R I (step : I -> PropT E (I + R)) i (r : itree E R)  =>
      exists (step': I -> itree E (I + R)%type),
        (forall j, step j (step' j)) /\ CategoryOps.iter step' i ≈ r.
  
  Definition interp_prop {E F} (h : E ~> PropT F) :
    itree E ~> PropT F := interp h.

  Definition singletonT {E}: itree E ~> PropT E :=
    fun R t t' => t' ≈ t.

End PropMonad.


Section MonadLaws.

  Global Instance Returns_eutt {E A} a: Proper (eutt eq ==> iff) (@Returns E A a).
  Proof.
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

  Definition eutt_closed {E X} (P: itree E X -> Prop): Prop :=
    Proper (eutt eq ==> iff) P.

  Global Polymorphic Instance EqM_PropT {E} : EqM (PropT E) :=
    fun a PA PA' =>
      (forall x y, x ≈ y -> (PA x <-> PA' y)) /\
      eutt_closed PA /\ eutt_closed PA'.

  Lemma eutt_ret_vis_abs: forall {X Y E} (x: X) (e: E Y) k, Ret x ≈ Vis e k -> False.
  Proof.
    intros.
    punfold H; inv H.
  Qed.

  Lemma Returns_Ret_ : forall E A (a x : A) (t:itree E A), t ≈ Ret x -> Returns a t -> x = a.
  Proof.
    intros E A a x t eq H. 
    induction H.
    - rewrite eq in H. eapply eutt_inv_ret. apply H.
     - rewrite tau_eutt in H. rewrite <- H in IHReturns. apply IHReturns. assumption.
    - rewrite eq in H. apply eqit_inv_ret_vis in H. contradiction.
  Qed.

  Lemma Returns_Ret :  forall E A (a x : A), Returns a ((Ret x) : itree E A) -> x = a.
  Proof.
    intros.  eapply Returns_Ret_. 2: eassumption. reflexivity.
  Qed.
    
  Lemma ret_bind: forall {E} (a b : Type) (f : a -> PropT E b) (x : a),
      eutt_closed (f x) ->
      eqm (bind (ret x) f) (f x).
  Proof.
    intros.
    split; [| split].
    - intros t t' eq; split; intros eqtt'.
      * cbn in *.
        repeat red in eqtt'.
        destruct eqtt' as (ta & EQ1 & [(k & KA & EQ2) | HX]).
        + unfold bind, Monad_itree in EQ2. rewrite EQ1, Eq.bind_ret_l, eq in EQ2.
          eapply H; [apply EQ2 | apply KA].
          constructor 1; eauto.
        + specialize (HX (fun a => t')).
          cbn in HX. destruct HX. apply H0.
     * cbn.
       exists (Ret x). split; [reflexivity|].
       left. exists (fun _ => t); split.
        + intros.
          apply Returns_Ret in H0. subst. red in H. rewrite eq. assumption.
        + unfold bind, Monad_itree. rewrite Eq.bind_ret_l; reflexivity.
          

    - intros t t' EQ; cbn; split; intros HX.
      * destruct HX as  (ta & EQ1 & [(k & KA & EQ2) | HX]).
        + exists (Ret x); split; [reflexivity |].
          left. exists (fun _ => t).
          split.
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
          apply KA. rewrite EQ1. constructor. reflexivity.
          unfold bind, Monad_itree.
          rewrite Eq.bind_ret_l. rewrite EQ. reflexivity.
          
        + exists (Ret x); split; [reflexivity|].
          right. intros. specialize (HX k). destruct HX. split;[ tauto | ].
          rewrite EQ1 in H1. rewrite <- EQ. assumption.
          
      * destruct HX as  (ta & EQ1 & [(k & KA & EQ2) | HX]).
        + exists (Ret x); split; [reflexivity |].
          left. exists (fun _ => t).
          split.
          intros ? RET; inv RET.
          2: { rewrite tau_eutt in H0. rewrite <- H0 in H1. apply Returns_Ret in H1. subst.
               red in H. rewrite EQ. rewrite EQ2. rewrite EQ1. 
               unfold bind, Monad_itree.
               rewrite Eq.bind_ret_l. apply KA. rewrite EQ1. constructor. reflexivity. }
          2: exfalso; eapply eutt_ret_vis_abs; eauto.
          apply eqit_inv_ret in H0; subst.
          eapply H. rewrite EQ1 in EQ2.
          unfold bind, Monad_itree in EQ2.
          rewrite Eq.bind_ret_l in EQ2. rewrite EQ. apply EQ2.
          apply KA. rewrite EQ1. constructor. reflexivity.
          unfold bind, Monad_itree.
          rewrite Eq.bind_ret_l. rewrite EQ. reflexivity.
          
        + exists (Ret x); split; [reflexivity|].
          right. intros. specialize (HX k). destruct HX. split;[ tauto | ].
          rewrite EQ1 in H1. rewrite EQ. assumption.
    - assumption.
  Qed.

  Section ReturnsBind.

    Context {E : Type -> Type} {R : Type}. 

    Import ITreeNotations.
    Local Open Scope itree.

    Inductive eqit_Returns_bind_clo b1 b2 (r : itree E R -> itree E R -> Prop) :
      itree E R -> itree E R -> Prop :=
    | pbc_intro_h U (t1 t2: itree E U) (k1 k2: U -> itree E R)
                  (EQV: eqit eq b1 b2 t1 t2)
                  (REL: forall u, Returns u t1 -> r (k1 u) (k2 u))
      : eqit_Returns_bind_clo b1 b2 r (ITree.bind t1 k1) (ITree.bind t2 k2)
    .
    Hint Constructors eqit_Returns_bind_clo: core.

    Lemma eqit_Returns_clo_bind b1 b2 vclo
          (MON: monotone2 vclo)
          (CMP: compose (eqitC eq b1 b2) vclo <3= compose vclo (eqitC eq b1 b2))
          (ID: id <3= vclo):
      eqit_Returns_bind_clo b1 b2 <3= gupaco2 (eqit_ eq b1 b2 vclo) (eqitC eq b1 b2).
    Proof.
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

    Lemma eqit_Returns_bind' {S} b1 b2
          (t1 t2: itree E S) (k1 k2: S -> itree E R) :
      eqit eq b1 b2 t1 t2 ->
      (forall r, Returns r t1 -> eqit eq b1 b2 (k1 r) (k2 r)) ->
      @eqit E _ _ eq b1 b2 (ITree.bind t1 k1) (ITree.bind t2 k2).
    Proof.
      intros. ginit. guclo eqit_Returns_clo_bind. unfold eqit in *.
      econstructor; eauto with paco.
    Qed.

  End ReturnsBind.

  Lemma distinguish_bind {E} {A B}
        (a : A)
        (ma : itree E A)
        (k1 k2 : A -> itree E B)
        (HRET : Returns a ma)
        (NEQ: ~((k1 a) ≈ (k2 a))) : 
    not ((ITree.bind ma k1) ≈ (ITree.bind ma k2)).
  Proof.
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
  Proof.
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

  
  Lemma bind_ret: forall {E} (A : Type) (PA : PropT E A),
      eutt_closed PA ->
      eqm (bind PA (fun x => ret x)) PA.
  Proof.
    intros.
    split; [| split].
    + intros t t' eq; split; intros eqtt'.
      * cbn in *.
        destruct eqtt' as  (ta & HPA & [(k & HRET & EQ) | HX]).
        - eapply H; [symmetry; eauto | clear eq t'].
          eapply H; [eauto | clear EQ t].
          eapply H; eauto.
          rewrite <- (bind_ret_r _ ta) at 2.
          apply eqit_Returns_bind'; [reflexivity |].
          intros.
          rewrite (HRET r); auto.
          reflexivity.
        - specialize (HX (fun x => Ret x)). destruct HX as (_ & HX).
          unfold bind, Monad_itree in HX. rewrite Eq.bind_ret_r in HX.
          red in H.
          rewrite <- eq. rewrite HX. assumption.
          
      * cbn.
        exists t'. split; [auto|].
        left. exists (fun x => Ret x); split.  
        intros ? ?; reflexivity.
        unfold bind, Monad_itree. rewrite Eq.bind_ret_r; auto.
        
    + intros x y EQ; split; intros eqtt'. 
      * cbn in *.
        destruct eqtt' as  (ta & HPA & [(k & HRET & EQ') | HX]).        
        - exists ta.  split; [auto|].
          left.
          exists k; split. auto. rewrite <- EQ; auto.
        - exists ta.  split; [auto|].
          right. intros. specialize (HX k). destruct HX.
          split; auto. rewrite <- EQ. assumption.
     * cbn in *.
        destruct eqtt' as  (ta & HPA & [(k & HRET & EQ') | HX]).        
        - exists ta.  split; [auto|].
          left.
          exists k; split. auto. rewrite EQ; auto.
        - exists ta.  split; [auto|].
          right. intros. specialize (HX k). destruct HX.
          split; auto. rewrite EQ. assumption.

    + auto.
  Qed.

  Lemma Returns_bind: forall {E A B} (t: itree E A) (k: A -> itree E B) a b,
      Returns a t ->
      Returns b (k a) ->
      Returns b (bind t k).
  Proof.
    intros E A B t k a b HRA HRB; induction HRA.
    - cbn; rewrite H, Eq.bind_ret_l; auto.
    - cbn in *. rewrite H. rewrite (eqit_tauL true u u); [| reflexivity]; auto. 
    - cbn in *; rewrite H, bind_vis.
      eapply (ReturnsVis b e); [reflexivity | cbn; eauto].
  Qed.

  Lemma Returns_bind_inversion : forall {E A B} (t : itree E A) (k : A -> itree E B) b,
      Returns b (bind t k) ->
      exists a, Returns a t.
  Proof.
    intros E A B t k b H.
    remember (bind t k) as t2.
    induction H; intros.
    - rewrite Heqt2 in H.
      apply eutt_inv_bind_ret in H.
      destruct H as (a & HEQ & HK).
      exists a. rewrite HEQ. constructor. reflexivity.
    - subst.
      (* SAZ: TODO - pick up here *)
  Admitted.
      

  
  (* From Coq.Logic.ChoiceFacts *)
Definition GuardedFunctionalChoice_on {A B} :=
  forall P : A -> Prop, forall R : A -> B -> Prop,
    inhabited B ->
    (forall x : A, P x -> exists y : B, R x y) ->
    (exists f : A->B, forall x, P x -> R x (f x)).
Axiom guarded_choice : forall {A B}, @GuardedFunctionalChoice_on A B.
  
  Lemma bind_bind: forall {E} (A B C : Type) (PA : PropT E A) (KB : A -> PropT E B) (KC : B -> PropT E C),
      (* eutt_closed PA -> *)
      eqm (bind (bind PA KB) KC) (bind PA (fun b => bind (KB b) KC)).
  Proof.
    (* PA ~a> KB a ~b> KC b *)
    intros.
    split; [| split].
    + intros t t' eq; split; intros eqtt'.
      * cbn in *.
        red in eqtt'.
        destruct eqtt' as (tb & HBC & [(kbc & KBC & EQc) | HX]).
        -  destruct HBC as (ta & HTA & [(kab & KAB & EQb) | HY]).
           -- rewrite eq in EQc; clear eq t.
              exists ta. split; [auto|].
              left.
              exists (fun b => ITree.bind (kab b) kbc).              
              setoid_rewrite EQc; clear EQc.
              setoid_rewrite EQb. setoid_rewrite EQb in KBC; clear EQb tb.
              (* ta ~a> kab a *)
              (* (ta; kab) ~b> kbc b *)
              split.
              ++ intros a HRet.
                 exists (kab a). split.
                 ** apply KAB; auto.
                 ** left.
                    exists kbc. split.
                    intros a' HRET'. apply KBC. apply Returns_bind with a; auto.
                    reflexivity.
              ++ unfold bind, Monad_itree.
                 rewrite Eq.bind_bind. reflexivity.
           -- (* ta diverges *)
             rewrite eq in EQc; clear eq t.
             red.
             exists ta. split; [auto|].
              right.
              setoid_rewrite EQc; clear EQc.
              intros. split.
             ++ intros a. red.
                exists (bind ta (fun _ => ITree.spin)).
                split.
                2 : { left. exists kbc. split. intros.
                      assert (~Returns a0 (bind ta (fun _ : A => ITree.spin))).
                      eapply not_Returns.
                      admit.
                (* CONTINUE HERE: USE not_returns? *)
                exists tb.
                admit.
                admit.
                admit. }
                admit.
             ++ admit.
        - admit.
      * cbn in *.
  (* ta: itree E A  (part 1)
           kac: A -> itree E C (part 2 3)
   *)
        (* ta ~a> exists tb, kbc ... *)
  (* Here we _cannot_ conclude: we would need to provide as continuation
           the function that given a "a" destruct HRet and returns the bind of ta with
           prefix returned by the destruct.
   *)
  Abort.

  (* Instance EqM_PropT {E} : EqM (PropT E) := *)
  (*   fun a PA PA' => *)
  (*     (forall x y, x ≈ y -> (PA x <-> PA' y)) /\ *)
  (*     eutt_closed PA /\ eutt_closed PA'. *)

  Lemma bind_bind: forall {E} (A B C : Type) (PA : PropT E A) (KB : A -> PropT E B) (KC : B -> PropT E C),
      (* eutt_closed PA -> *)
      forall x y, x ≈ y -> bind (bind PA KB) KC x -> bind PA (fun b => bind (KB b) KC) y.
  Proof.
      (*
    SAZ: This version depends on the old definition of bind.
   *)
  Admitted.
  (*
    (* PA ~a> KB a ~b> KC b *)
    intros.
    cbn in *.
    destruct H0 as (tb & kbc & (ta & kab & HPA & EQb & HRETA) & EQc & HRETB).
    rewrite H in EQc; clear H x.
    setoid_rewrite EQc; clear EQc.
    setoid_rewrite EQb. setoid_rewrite EQb in HRETB; clear EQb tb.
    (* ta ~a> kab a *)
    (* (ta; kab) ~b> kbc b *)
    exists ta.
    exists (fun b => ITree.bind (kab b) kbc).
    split; [| split]; auto.
    rewrite Eq.bind_bind; reflexivity.
    intros a HRet.
    (* ta ~a>, hence kab a *)
    exists (kab a), kbc.
    split; [| split]; auto.
    reflexivity.
    intros; apply HRETB.
    apply Returns_bind with a; auto.
  Qed.
*)

End MonadLaws.

From ITree Require Import
     Basics.Category
     CategoryKleisli
     CategoryKleisliFacts
     KTree
     KTreeFacts.


Section IterLaws.

  Global Instance IterUnfold_PropT {E} : IterUnfold (Kleisli (PropT E)) sum.
  intros A B Pstep a.

  repeat red. split.
  - intros t1 t2 EQ.
    split.
    + intros (step & H & EQ2).
      cbn.
      admit.
(* SAZ OLD 
      exists (step a). exists (fun ab : A + B => match ab with
                                    | inl a => Tau (ITree.iter step a)
                                    | inr b => Ret b
                                    end).
      split; [|split].
      * apply H.
      * rewrite <- EQ2 in EQ.
        rewrite unfold_iter_ktree in EQ.
        rewrite <- EQ. reflexivity.
      * intros a0 H0.
        destruct a0. cbn.
        exists step. split. assumption. apply Eq.eqit_tauR. reflexivity.
        cbn. reflexivity.
*)
    + intros H. admit.
(* SAZ OLD       
      cbn in H.
      destruct H as (ta & k & HP & EQ2 & HK).
      unfold iter, Iter_Kleisli, Basics.iter, MonadIter_Prop.
      exists (fun a => ITree.bind (ITree.bind ta k) (fun b => ret (inr b))).
      split.
      intros. specialize (HK (inl j)).
      cbn in HK.
      
      (iter step') a = (cat step' (case_ (iter step') (id_ b))) a
      
      
      
      specialize (Hbody (inl a)).
      cbn in Hbody.
      (* SAZ: need to decide about Returns (inl a) ta vs. not (Returns (inl a) ta) *)      
      assert ((Returns (inl a) ta) \/ ~(Returns (inl a) ta)) as CLASSICAL.
      { admit. (* TODO: Classical logic *) }
      destruct CLASSICAL as [HRet | HNoRet].
      apply Hbody in HRet.
      destruct HRet as (step' & Hfj & HI).
      exists step'. split. assumption.
 *)
      
  - split.
    + split; intros.
      destruct H0 as (step & Hstep & EQ).
      exists step. split; auto. rewrite EQ. assumption.
      destruct H0 as (step & Hstep & EQ).
      exists step. split; auto. rewrite EQ. symmetry. assumption.
    + cbn. admit.
        (* old destruct H1 as (ta & k & HF & EQ & HR).
      *
        exists ta. exists k. split; auto. split. rewrite <- EQ. symmetry. assumption.
        assumption.
      * destruct H1 as (ta & k & HF & EQ & HR).
        exists ta. exists k. split; auto. split. rewrite <- EQ. assumption.
        assumption. *)
  Admitted.

  Global Instance IterNatural_PropT {E} : IterNatural (Kleisli (PropT E)) sum.
  intros A B C f g a.
  cbn.
  split.
  - intros t1 t2 EQ.
    split.
  Admitted.
(*  
    + intros (tb & k & H & EQ2 & Hk).
      repeat red in H. destruct H as (step & Hstep & EQ3).
      repeat red. exists (fun a => bind (step a) (fun ab : A + B => match ab with
                                                         | inl a => Ret (inl a)
                                                         | inr b => fmap inr (k b)
                                                         end)).
      split.
      * intros. cbn. exists (step j).
        exists ((fun ab : A + B => match ab with
                                          | inl a0 => Ret (inl a0)
                                          | inr b => ITree.map inr (k b)
                                          end)).
        split. apply Hstep.
        split.  reflexivity.
        intros. destruct a0. cbn. exists (Ret (a0)). exists (fun a => ret (inl a)).
        split. reflexivity.
        split. rewrite Eq.bind_ret_l. reflexivity.
        intros. reflexivity.
        cbn. exists (k b).  exists (fun (c:C) => Ret (inr c)).
        split. apply Hk. rewrite <- EQ3.  (* SAZ: !?!? *) admit.
        split. unfold ITree.map. reflexivity.
        intros. reflexivity.
        
      * cbn.
        rewrite <- EQ. rewrite EQ2.
        (* SAZ: eventually need to use: iter_natural. *)
        unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree. rewrite unfold_iter.
  Admitted.
  *)            
      
  Global Instance IterDinatural_PropT {E} : IterDinatural (Kleisli (PropT E)) sum.
  Admitted.

  Global Instance IterCodiagonal_PropT {E} :  IterCodiagonal (Kleisli (PropT E)) sum.
  Admitted.

End IterLaws.  


