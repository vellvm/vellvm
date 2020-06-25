From Coq Require Import Ensembles Setoid Morphisms RelationClasses Logic.Classical_Prop.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad
     Structures.MonadTrans
     Data.Monads.EitherMonad.

From ITree Require Import
     Basics.Basics
     ITreeDefinition
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

  Definition subtree {E} {A B} (ta : itree E A) (tb : itree E B) := exists (k : A -> itree E B), tb ≈ bind ta k.

  Definition bind_PropT {E} :=
    fun A B (PA: PropT E A) (K: A -> PropT E B) (tb: itree E B) =>
      exists (ta: itree E A) (k: A -> itree E B),
        PA ta /\
        tb ≈ bind ta k /\
        (forall a, Returns a ta -> K a (k a)).

  Definition bind_PropT_stronger {E} :=
    fun A B (PA: PropT E A) (K: A -> PropT E B) (tb: itree E B) =>
      exists (tak : (itree E A * (A -> itree E B))),
        PA (fst tak) /\
        tb ≈ bind (fst tak) (snd tak) /\
        (forall a, Returns a (fst tak) -> K a ((snd tak) a)).

  (* BOGUS "CAST" to test hypotheses in bind_bind *)
  Lemma bind_PropT_bind_PropT_stronger {E}:
    forall A B PA K (tb : itree E B), bind_PropT A B PA K tb <-> bind_PropT_stronger A B PA K tb.
  Proof.
  Admitted.

  
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
  Proof.
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

  Inductive iter_Prop {R I : Type} (step : I -> I + R -> Prop) (i : I) (r : R)
    : Prop :=
  | iter_done'
    : step i (inr r) -> iter_Prop step i r
  | iter_step' i'
    : step i (inl i') ->
      iter_Prop step i' r ->
      iter_Prop step i r
  .

  (* Definition _iter {E : Type -> Type} {R I : Type} *)
  (*           (tau : _) *)
  (*           (iter_ : I -> itree E R) *)
  (*           (step_i : I + R) : itree E R := *)
  (*   match step_i with *)
  (*   | inl i => tau (iter_ i) *)
  (*   | inr r => Ret r *)
  (*   end. *)

  (* Definition iter {E : Type -> Type} {R I: Type} *)
  (*           (step : I -> itree E (I + R)) : I -> itree E R := *)
  (*   cofix iter_ i := bind (step i) (_iter (fun t => Tau t) iter_). *)

  Definition _iter {E : Type -> Type} {R I : Type}
             (iter_ : I -> PropT E R)
             (step_i : I + R) (r : itree E R) : Prop :=
    match step_i with
    | inl i => iter_ i r
    | inr x => True
    end.

  (* Definition iter {E : Type -> Type} {R I : Type} *)
  (*            (step : I -> PropT E (I + R)) : I -> PropT E R := *)
  (*   cofix iter_ i := bind (step i) (_iter iter_). *)


  (* CoInductive iter_PropT {E} {R I : Type} *)
  (*           (step : I -> PropT E (I + R)) (i : I) (r : itree E R) : Prop := *)
  (* | iter_done : forall (step' : I -> itree E (I + R)), *)
  (*               (step i) (step' i) -> *)
  (*               iter_PropT step i r. *)

  (* SAZ: maybe define directly by coinduction  *)
  Global Polymorphic Instance MonadIter_Prop {E} : MonadIter (PropT E) :=
    fun R I (step : I -> PropT E (I + R)) i =>
      fun (r : itree E R) =>
        (exists step' : I -> itree E (I + R)%type,
            (* How do we state that something is out of bounds? *)
            (forall j, step j (step' j)) /\
            CategoryOps.iter step' i ≈ r).

  Definition interp_prop {E F} (h : E ~> PropT F) :
    itree E ~> PropT F := interp h.

  Definition singletonT {E}: itree E ~> PropT E :=
    fun R t t' => t' ≈ t.

End PropMonad.


From ITree Require Import
     Basics.Category
     CategoryKleisli
     CategoryKleisliFacts
     KTree
     KTreeFacts.

Section IterLaws.

  Definition divergent {E A} (ta : itree E A) := (forall k , ta ≈ bind ta k).

  Lemma Returns_divergent {E A}:
    (forall (ta : itree E A), not (exists a, Returns a ta) -> divergent ta).
  Proof.
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


  Lemma Returns_divergent' {E A B}:
    (forall (ta : itree E A) (tb : itree E B),
        not (exists a, Returns a ta) -> not (exists b, Returns b tb) ->
        forall (k : A -> itree E B), tb ≈ bind ta k).
  Proof.
    intros. red. intros. red in H.
    unfold bind, Monad_itree.
    generalize dependent ta. pcofix CIH. cbn. pstep. unfold eqit_.
    intros. remember (observe ta). destruct i.
    - destruct H0. assert (ta ≈ Ret r0). rewrite Heqi.
      rewrite <- itree_eta. reflexivity.
  Admitted.

  Definition eutt_closed {E X} (P: itree E X -> Prop): Prop :=
    Proper (eutt eq ==> iff) P.

  Global Polymorphic Instance EqM_PropT {E} : EqM (PropT E) :=
    fun a PA PA' =>
      (forall x y, x ≈ y -> (PA x <-> PA' y)) /\
      eutt_closed PA /\ eutt_closed PA'.

  Ltac simpl_iter :=
      unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree.

  Import MonadNotation.
  Local Open Scope monad_scope.

  Global Instance IterUnfold_PropT {E} : IterUnfold (Kleisli (PropT E)) sum.
    intros A B Pstep a.
    repeat red. split; [ intros x y EQ | ]; split.
  - (* Show that there is some looping itree body that Pstep can unfold into. *)
    intros LOOP. repeat red. repeat red in LOOP.
    destruct LOOP as (BODY & PROP & RESULT).
    exists (BODY a).
    exists (fun ab : A + B => match ab with
        | inl a => Tau (ITree.iter BODY a)
        | inr b => Ret b
                      end). cbn.
    split. auto. split.
    + (* Proposition holds over first part of computation. *)
      rewrite <- EQ, <- RESULT. simpl_iter.
      rewrite unfold_iter. reflexivity.
    + (* There is some continuation that satisfies the computation. *)
      intros ab RET. repeat red.
      destruct ab eqn: H_ab.
      * (* Keep loopin' *)
        cbn. repeat red.
        exists BODY. split; auto.
        simpl_iter; rewrite unfold_iter. rewrite tau_eutt.
        reflexivity.
      * cbn. reflexivity.
  - (* An unfolded PropT implies a folded loop. *)
    (*      cat Pstep (case_ (iter Pstep) (id_ B)) a y -> iter Pstep a x      *)
    cbn. unfold bind_PropT.

    intros UNFOLD. repeat red. setoid_rewrite EQ. clear EQ x.
    destruct UNFOLD as (FIRST & CONTINUATION & FIRST_PROP & BIND_EQ &
                        CONT_PROP).
    (* Perhaps Returns should be a coinductive proposition? *)

    simpl_iter. setoid_rewrite unfold_iter.


    From Coq Require Import Classes.EquivDec.
    assert (EqDec A eq). admit.

    (* If we unfold a loop, the idea should be that the unfolded part is going
     * to ... terminate, right? It isn't necessarily a return, though. *)
    assert (FIRST_SHOULD_RETURN: exists a : A + B, Returns a FIRST). admit.
    destruct FIRST_SHOULD_RETURN as (AB & RETURN_FIRST).
    specialize (CONT_PROP _ RETURN_FIRST).

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
    admit.
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
  Admitted.

  Global Instance IterCodiagonal_PropT {E} :  IterCodiagonal (Kleisli (PropT E)) sum.
  Admitted.


End IterLaws.  


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


  Definition EqM_PropT' {E} : EqM (PropT E) :=
    fun a PA PA' =>
      (forall x, (PA x -> exists y, x ≈ y /\ PA' y)) /\
      (forall y, (PA' y -> exists x, x ≈ y /\ PA x)) /\
      eutt_closed PA /\ eutt_closed PA'.

  Lemma EqM_PropT'_Eqm_PropT : forall E a PA PA', @EqM_PropT E a PA PA' -> EqM_PropT' a PA PA'.
  Proof.
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

  End ReturnsBind.

    Lemma eqit_Returns_bind' {E} {R} {T} b1 b2
          (t1 t2: itree E T) (k1 k2: T -> itree E R) :
      eqit eq b1 b2 t1 t2 ->
      (forall r, Returns r t1 -> eqit eq b1 b2 (k1 r) (k2 r)) ->
      @eqit E _ _ eq b1 b2 (ITree.bind t1 k1) (ITree.bind t2 k2).
    Proof.
      intros. ginit. guclo (@eqit_Returns_clo_bind E R R eq). unfold eqit in *.
      econstructor; eauto with paco.
    Qed.

    Lemma eqit_Returns_bind'' {E} {R S} {T} (RS : R -> S -> Prop) b1 b2
          (t1 t2: itree E T) (k1: T -> itree E R) (k2 : T -> itree E S) :
      eqit eq b1 b2 t1 t2 ->
      (forall r, Returns r t1 -> eqit RS b1 b2 (k1 r) (k2 r)) ->
      @eqit E _ _ RS b1 b2 (ITree.bind t1 k1) (ITree.bind t2 k2).
    Proof.
      intros. ginit. guclo (@eqit_Returns_clo_bind E R S RS). unfold eqit in *.
      econstructor; eauto with paco.
    Qed.

    Lemma eqit_bind_Returns_inv {E} {R S T} (RS : R -> S -> Prop) 
          (t : itree E T)  (k1: T -> itree E R) (k2 : T -> itree E S) :
      (eutt RS  (ITree.bind t k1) (ITree.bind t k2)) ->
      (forall r, Returns r t -> eutt RS (k1 r) (k2 r)).
    Proof.
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

   Global Instance bind_PropT_Proper {E} {A B} :
     Proper (eqm ==> (eq ==> eqm) ==> eutt eq ==> iff) (@bind_PropT E A B).
   Proof.
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
   Proof.
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
  Proof.
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

  Lemma Returns_bind_inversion_ : forall {E A B} (u : itree E B) (t : itree E A) (k : A -> itree E B) b,
      Returns b u ->
      u ≈ (bind t k) ->
      exists a, Returns a t /\ Returns b (k a).
  Proof.
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

  Lemma Returns_bind_inversion : forall {E A B} (u : itree E B) (t : itree E A) (k : A -> itree E B) b,
      Returns b (bind t k) ->
      exists a, Returns a t /\ Returns b (k a).
  Proof.
    intros.
    eapply Returns_bind_inversion_. apply H. reflexivity.
  Qed.

  Lemma Returns_vis_inversion_ : forall {E A B} (u : itree E B) (e : E A) (k : A -> itree E B) b,
      Returns b u ->
      u ≈ (Vis e k) ->
      exists a, Returns b (k a).
  Proof.
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
  Proof.
    intros.
    eapply Returns_vis_inversion_. apply H. reflexivity.
  Qed.
  

  Definition EQ_REL {E A} (ta : itree E A) : A -> A -> Prop :=
    fun a b => a = b /\ Returns a ta.

  Lemma Symmteric_EQ_REL {E A} (ta : itree E A) : Symmetric (EQ_REL ta).
  Proof.
    repeat red.
    intros a b (EQ & H).
    split.
    - symmetry. assumption.
    - subst; auto.
  Qed.

  Lemma Transitive_EQ_REL {E A} (ta : itree E A) : Transitive (EQ_REL ta).
  Proof.
    repeat red.
    intros a b c (EQ1 & H1) (EQ2 & H2).
    split.
    - rewrite EQ1. assumption.
    - assumption.
  Qed.

  Instance EQ_REL_Proper {E A} : Proper (eutt eq ==> eq ==> eq ==> iff) (@EQ_REL E A).
  Proof.
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
  Proof.
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
  Proof.
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
  Proof.
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

(*
Definition RET_EQ {E} {A} a (ta : itree E A) : A -> A -> Prop :=
  fun x y => Returns a ta -> (Returns x ta <-> Returns y ta).

Instance Reflexive_RET_EQ {E} {A} a (ta : itree E A) : Reflexive (RET_EQ a ta).
Proof.
  repeat red.
  intros.
  split; auto. 
Qed.
*)


Lemma bind_bind: forall {E}
                   (A B C : Type) (PA : PropT E A)
                   (KB : A -> PropT E B) (KC : B -> PropT E C)
                   (PQOK : eutt_closed PA)
                   (KBP : Proper (eq ==> eqm) KB)
                   (KCP : Proper (eq ==> eqm) KC),
      eqm (bind (bind PA KB) KC) (bind PA (fun b => bind (KB b) KC)).
  Proof.
    (* PA ~a> KB a ~b> KC b *)
    intros.
    split; [| split].
    - intros t t' eq; split; intros eqtt'.
      + cbn in *.
        red in eqtt'.
        destruct eqtt' as (tb & kbc & (HBC & EQc & HRkbc)).
        destruct HBC as (ta & kab & HTA & EQb & HRkab).
        rewrite eq in EQc; clear eq t.
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
      + cbn in *.
        red in eqtt'.
        destruct eqtt' as (ta & k & (HTA & EQc & HRET)).

        unfold bind_PropT in HRET.
        apply guarded_choice in HRET.
        destruct HRET as (kab & HF).
        red.

        exists (bind ta kab).
        
        apply guarded_choice in HF.
        destruct HF as (kabc & HKabc).
        
        setoid_rewrite bind_bind.        

        assert (forall a1 a2 b, (kabc a1 b) ≈ (kabc a2 b)) as PARAMETRIC.
        { admit. (* TODO - is this justifiable? *) }

        assert ((exists a, Returns a ta) \/ ~ exists a, Returns a ta) as DEC.
        { admit. (* TODO - classical logic *) }
        destruct DEC as [(a & HRET) | N].

        * exists (fun b => kabc a b).
          split; [|split].
          -- red.
             exists ta. exists kab.
             split; auto. split; [reflexivity|].
             intros a0 HRET0. specialize (HKabc a0 HRET0). tauto.
          -- rewrite eq, EQc.
             eapply eutt_clo_bind with (UU:= EQ_REL ta).
             ** apply eutt_EQ_REL_Reflexive.
             ** intros.
                red in H.
                destruct H as (eq2 & HR).
                subst.

                specialize (HKabc u2 HR).
                destruct HKabc as (HK & EQ2 & RET).
                rewrite EQ2.
                clear eq.
                apply eutt_clo_bind with (UU:=eq).
                reflexivity.
                intros. subst.
                apply PARAMETRIC.
          -- intros.
             eapply Returns_bind_inversion_ in H.
             2: reflexivity.
             destruct H as (a1 & H1 & HX).
             
             specialize (HKabc a1 H1).
             destruct HKabc as (HK & EQ2 & RET).

             apply RET in HX.
             do 2 red in KCP.
             specialize (KCP a0 a0 eq_refl).
             destruct KCP as (HKCP & EC & _).
             specialize (HKCP (kabc a1 a0) (kabc a a0)).
             apply HKCP. apply PARAMETRIC. assumption.

        * exists (fun b => ITree.spin).
          split; [|split].
          -- red.
             exists ta. exists kab.
             split; auto. split; [reflexivity|].
             intros. specialize (HKabc a H). tauto.
          -- rewrite eq, EQc. clear t eq EQc.
             eapply eqit_Returns_bind'.
             ** reflexivity.
             ** intros. subst.
                assert (exists a, Returns a ta).
                { exists r. assumption. }
                contradiction.
          -- intros. apply Returns_bind_inversion in H.
             destruct H as (x & HRx & _).
             assert (exists a, Returns a ta).
             { exists x; auto. }
             contradiction.
             exact (ITree.spin).
        * constructor. exact (fun _ => ITree.spin).
        * constructor. exact (ITree.spin).
    - split; intros. 
      rewrite <- H. assumption.
      rewrite H. assumption.
    - split; intros.
      rewrite <- H. assumption.
      rewrite H. assumption.
Admitted.


  (* ta: itree E A  (part 1)
           kac: A -> itree E C (part 2 3)
   *)
        (* ta ~a> exists tb, kbc ... *)
  (* Here we _cannot_ conclude: we would need to provide as continuation
           the function that given a "a" destruct HRet and returns the bind of ta with
           prefix returned by the destruct.
   *)


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
