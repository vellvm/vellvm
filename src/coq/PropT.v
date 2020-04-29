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
  | ReturnsTau: forall t, Returns a t -> Returns a (Tau t)
  | ReturnsVis: forall {X} (e: E X) (x: X) t k, t ≈ Vis e k -> Returns a (k x) -> Returns a t
  .
  Hint Constructors Returns: core.

  Global Instance Monad_Prop {E} : Monad (PropT E) :=
    {|
      ret := fun _ x y => y ≈ ret x
      ; bind := fun A B (PA: PropT E A) (K: A -> PropT E B) (tb: itree E B) =>
                  exists (ta: itree E A) (k: A -> itree E B),
                    PA ta /\
                    tb ≈ bind ta k /\
                    (forall a, Returns a ta -> K a (k a))
    |}.

  Global Polymorphic Instance MonadIter_Prop {E} : MonadIter (PropT E) :=
    fun R I step i r =>
      exists (step': I -> itree E (I + R)%type),
        (forall j, step j (step' j)) /\ CategoryOps.iter step' i = r.

  Definition interp_prop {E F} (h : E ~> PropT F) :
    itree E ~> PropT F := interp h.

  Definition singletonT {E}: itree E ~> PropT E :=
    fun R t t' => t' ≈ t.

End PropMonad.

Section MonadLaws.

  Instance Returns_eutt {E A} a: Proper (eutt eq ==> iff) (@Returns E A a).
  Proof.
    repeat intro; split; intros HRet.
    - revert y H. induction HRet; intros.
      constructor; rewrite <- H, H0; reflexivity.
      apply IHHRet, eqit_inv_tauL; auto.
      econstructor 3; [rewrite <- H0, H; reflexivity | apply IHHRet; reflexivity].
    - revert x H; induction HRet; intros ? EQ.
      constructor; rewrite EQ; eauto.
      apply IHHRet, eqit_inv_tauR; auto.
      econstructor 3; [rewrite EQ, H; reflexivity | apply IHHRet; reflexivity].
  Qed.

  Definition eutt_closed {E X} (P: itree E X -> Prop): Prop :=
    Proper (eutt eq ==> iff) P.

  Instance EqM_PropT {E} : EqM (PropT E) :=
    fun a PA PA' =>
      (forall x y, x ≈ y -> (PA x <-> PA' y)) /\
      eutt_closed PA /\ eutt_closed PA'.

  Lemma eutt_ret_vis_abs: forall {X Y E} (x: X) (e: E Y) k, Ret x ≈ Vis e k -> False.
  Proof.
    intros.
    punfold H; inv H.
  Qed.

  Lemma ret_bind: forall {E} (a b : Type) (f : a -> PropT E b) (x : a),
      eutt_closed (f x) ->
      eqm (bind (ret x) f) (f x).
  Proof.
    intros.
    split; [| split].
    + intros t t' eq; split; intros eqtt'.
      * cbn in *.
        destruct eqtt' as (ta & k &  EQ1 & EQ2 & KA).
        rewrite EQ1, Eq.bind_ret_l, eq in EQ2.
        eapply H; [apply EQ2 | apply KA].
        constructor 1; eauto.
      * cbn.
        exists (Ret x), (fun _ => t); split; [reflexivity | split].
        rewrite Eq.bind_ret_l; reflexivity.
        intros.
        inv H0.
        { apply eqit_inv_ret in H1; subst.
          eapply H; eauto.
        }
        {
          exfalso; eapply eutt_ret_vis_abs; eauto. }
    + intros t t' EQ; cbn; split; intros (? & ? & ? & ? & ?).
      * exists (Ret x), (fun _ => t'); split; [reflexivity | split; [rewrite Eq.bind_ret_l; reflexivity |]].
        intros ? RET; inv RET.
        2: exfalso; eapply eutt_ret_vis_abs; eauto.
        apply eqit_inv_ret in H3; subst.
        eapply H, H2.
        2:rewrite H0; constructor; reflexivity.
        rewrite H0, Eq.bind_ret_l in H1; rewrite <- EQ, H1; reflexivity.
      * exists (Ret x), (fun _ => t); split; [reflexivity | split; [rewrite Eq.bind_ret_l; reflexivity |]].
        intros ? RET; inv RET.
        2: exfalso; eapply eutt_ret_vis_abs; eauto.
        apply eqit_inv_ret in H3; subst.
        eapply H, H2.
        2:rewrite H0; constructor; reflexivity.
        rewrite H0, Eq.bind_ret_l in H1; rewrite EQ, H1; reflexivity.
    + assumption.
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
        rewrite itree_eta, <- Heqot1; constructor 2; auto.
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
            rewrite itree_eta, <- Heqot1; constructor 2; eauto.
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
        exists t', (fun x => Ret x); split; [auto | split; [rewrite Eq.bind_ret_r; auto |]].
        intros ? ?; reflexivity.
    + intros x y EQ; split; intros (ta & k & HPA & EQ' & HRET).
      * cbn in *.
        exists ta, k; split; [| split]; auto.
        rewrite <- EQ; auto.
      * cbn in *.
        exists ta, k; split; [| split]; auto.
        cbn; rewrite EQ; auto.
    + auto.
  Qed.

  Lemma Returns_bind: forall {E A B} (t: itree E A) (k: A -> itree E B) a b,
      Returns a t ->
      Returns b (k a) ->
      Returns b (bind t k).
  Proof.
    intros E A B t k a b HRA HRB; induction HRA.
    - cbn; rewrite H, Eq.bind_ret_l; auto.
    - cbn in *. rewrite (eqit_tauL true t t); [| reflexivity]; auto. 
    - cbn in *; rewrite H, bind_vis.
      eapply (ReturnsVis b e); [reflexivity | cbn; eauto].
  Qed.

  Lemma bind_bind: forall {E} (A B C : Type) (PA : PropT E A) (KB : A -> PropT E B) (KC : B -> PropT E C),
      (* eutt_closed PA -> *)
      eqm (bind (bind PA KB) KC) (bind PA (fun b => bind (KB b) KC)).
  Proof.
    (* PA ~a> KB a ~b> KC b *)
    intros.
    split; [| split].
    + intros t t' eq; split; intros eqtt'.
      * cbn in *.
        destruct eqtt' as (tb & kbc & (ta & kab & HPA & EQb & HRETA) & EQc & HRETB).
        rewrite eq in EQc; clear eq t.
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
      * cbn in *.
        destruct eqtt' as (ta & kac & HPA & EQa & HRet).
        rewrite <- eq in EQa; clear eq t'.
        setoid_rewrite EQa; clear EQa t.
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

End MonadLaws.

