Require Import Paco.paco.
From ITree Require Import
     ITree
     Eq.Eq.
Set Implicit Arguments.
Set Strict Implicit.

(* TODO: replace the too restrictive version from itree *)
Lemma eutt_eq_bind : forall E R1 R2 RR U (t: itree E U) (k1: U -> itree E R1) (k2: U -> itree E R2),
    (forall u, eutt RR (k1 u) (k2 u)) -> eutt RR (ITree.bind t k1) (ITree.bind t k2).
Proof.
  intros.
  apply eutt_clo_bind with (UU := Logic.eq); [reflexivity |].
  intros ? ? ->; apply H.
Qed.

Lemma eutt_Ret :
  forall E (R1 R2 : Type) (RR : R1 -> R2 -> Prop) r1 r2, RR r1 r2 <-> eutt (E := E) RR (Ret r1) (Ret r2).
Proof.
  intros; apply eqit_Ret.
Qed.

Definition equiv_rel {A B : Type} (R S: A -> B -> Prop): Prop :=
  forall a b, R a b <-> S a b.
Infix "⇔" :=  equiv_rel (at level 85, right associativity).

Definition equiv_pred {A : Type} (R S: A -> Prop): Prop :=
  forall a, R a <-> S a.

Lemma fold_eqitF:
  forall {E R1 R2} (RR: R1 -> R2 -> Prop) b1 b2 (t1 : itree E R1) (t2 : itree E R2) ot1 ot2,
    eqitF RR b1 b2 id (upaco2 (eqit_ RR b1 b2 id) bot2) ot1 ot2 ->
    ot1 = observe t1 ->
    ot2 = observe t2 ->
    eqit RR b1 b2 t1 t2.
Proof.
  intros * eq -> ->; pfold; auto.
Qed.

Lemma eutt_conj {E} {R S} {RS RS'} :
  forall (t : itree E R) (s : itree E S),
    eutt RS  t s ->
    eutt RS' t s ->
    eutt (RS /2\ RS') t s. 
Proof.
  repeat red.
  einit.
  ecofix CIH; intros * EQ EQ'.
  rewrite itree_eta, (itree_eta s).
  punfold EQ; punfold EQ'; red in EQ; red in EQ'.
  genobs t ot; genobs s os.
  hinduction EQ before CIH0; subst; intros; pclearbot; simpl.

  - estep; split; auto.
    inv EQ'; auto.
  - estep; ebase; right; eapply CIH; eauto.
    rewrite <- tau_eutt.
    rewrite <- (tau_eutt m2); auto.
  - estep; ebase; intros ?; right; eapply CIH0; eauto.
    eapply eqit_Vis; eauto.
  - eapply fold_eqitF in EQ'; eauto.
    assert (t ≈ Tau t1) by (rewrite itree_eta, <- Heqot; reflexivity).
    rewrite H in EQ'.
    apply eqit_inv_tauL in EQ'.
    subst; specialize (IHEQ _ _ eq_refl eq_refl).
    punfold EQ'; red in EQ'.
    specialize (IHEQ EQ').
    rewrite eqit_tauL; [|reflexivity].
    rewrite (itree_eta t1).
    eapply IHEQ. 
  - subst; cbn.
    rewrite tau_euttge.
    rewrite (itree_eta t2); eapply IHEQ; eauto.
    eapply fold_eqitF in EQ'; eauto.
    assert (s ≈ Tau t2).
    rewrite (itree_eta s), <- Heqos; reflexivity.
    rewrite tau_eutt in H.
    assert (eutt RS' t t2).
    rewrite <- H; auto.
    punfold H0.
Qed.

Lemma eutt_disj_l {E} {R S} {RS RS'} :
  forall (t : itree E R) (s : itree E S),
    eutt RS t s ->
    eutt (RS \2/ RS') t s. 
Proof.
  intros.
  eapply eqit_mon with (RR := RS); eauto.
Qed.

Lemma eutt_disj_r {E} {R S} {RS RS'} :
  forall (t : itree E R) (s : itree E S),
    eutt RS' t s ->
    eutt (RS \2/ RS') t s. 
Proof.
  intros.
  eapply eqit_mon with (RR := RS'); eauto.
Qed.

Lemma eutt_equiv {E} {R S} {RS RS'} :
  forall (t : itree E R) (s : itree E S),
    (RS ⇔ RS') ->
    eutt RS t s <-> eutt RS' t s. 
Proof.
  intros * EQ; split; intros EUTT; eapply eqit_mon; try apply EUTT; eauto.
  all:apply EQ.
Qed.

(** * has_post  *)

Definition has_post {E X} (t : itree E X) (Q : X -> Prop) : Prop :=
  eutt (fun 'x _ => Q x) t t.

(* Note: the following definition is equivalent. To figure out what's more convenient to work with *)
Definition has_post_strong {E X} (t : itree E X) (Q : X -> Prop) : Prop :=
  eutt (fun 'x y => x = y /\ Q x) t t.

Lemma has_post_post_strong : forall {E X} (t : itree E X) Q,
    has_post t Q <-> has_post_strong t Q.
Proof.
  intros; split; intros HP.
  - apply eutt_conj; [reflexivity | auto].
  - eapply eqit_mon; eauto.
    intros * H; apply H.
Qed.

From Coq Require Import Morphisms.
Lemma has_post_equiv {E X} (t : itree E X) : Proper (equiv_pred ==> iff) (has_post t).
Proof.
  repeat red; intros * EQ *; split; intros HP; eapply eutt_equiv; eauto.
  all:split; apply EQ.
Qed.

Notation "t ⤳ Q" := (has_post t Q) (at level 50).

Lemma has_post_conj : forall {E X} (t : itree E X) P Q,
    t ⤳ P ->
    t ⤳ Q ->
    t ⤳ (P /1\ Q).
Proof.
  intros * HP HQ.
  pose proof eutt_conj HP HQ.
  auto.
Qed.     

Lemma has_post_disj_l : forall {E X} (t : itree E X) P Q,
    t ⤳ P ->
    t ⤳ (P \1/ Q).
Proof.
  intros * HP.
  epose proof eutt_disj_l HP as H.
  apply H.
Qed.     

Lemma has_post_disj_r : forall {E X} (t : itree E X) P Q,
    t ⤳ Q ->
    t ⤳ (P \1/ Q).
Proof.
  intros * HQ.
  epose proof eutt_disj_r HQ as H.
  apply H.
Qed.     

Lemma eutt_post_bind : forall E R1 R2 RR U Q (t: itree E U) (k1: U -> itree E R1) (k2: U -> itree E R2),
    t ⤳ Q ->
    (forall u, Q u -> eutt RR (k1 u) (k2 u)) -> eutt RR (ITree.bind t k1) (ITree.bind t k2).
Proof.
  intros * POST ?.
  apply eutt_clo_bind with (UU := fun x y => x = y /\ Q x); [apply has_post_post_strong; exact POST |].
  intros ? ? [-> ?]; auto.
Qed.

Lemma has_post_bind : forall {E X Y} (t : itree E X) (k : X -> itree E Y) Q,
    (forall x, k x ⤳ Q) ->
    ITree.bind t k ⤳ Q.
Proof.
  intros * POST.
  apply eutt_eq_bind; intros ?; apply POST.
Qed.

Lemma has_post_bind_strong : forall {E X Y} (t : itree E X) (k : X -> itree E Y) S Q,
    t ⤳ S ->
    (forall x, S x -> k x ⤳ Q) ->
    ITree.bind t k ⤳ Q.
Proof.
  intros * POST1 POST2.
  eapply eutt_post_bind; eauto.
Qed.

Lemma eutt_post_bind_gen :
  forall E R1 R2 RR S1 S2 SS Q1 Q2
    (t1 : itree E S1) (k1: S1 -> itree E R1) (t2 : itree E S2) (k2 : S2 -> itree E R2),
    t1 ⤳ Q1 ->
    t2 ⤳ Q2 ->
    eutt SS t1 t2 ->
    (forall u1 u2, SS u1 u2 -> Q1 u1 -> Q2 u2 -> eutt RR (k1 u1) (k2 u2)) ->
    eutt RR (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros * POST1 POST2 EQ KEQ.
  apply eutt_clo_bind with (UU := fun x y => SS x y /\ Q1 x /\ Q2 y).
  2: intros ? ? (? & ? & ?); apply KEQ; auto.
  clear KEQ.
  apply has_post_post_strong in POST1.
  apply has_post_post_strong in POST2.
  pose proof eqit_trans _ _ _ _ _ _ _ POST1 EQ as EQ1.
  pose proof eqit_trans _ _ _ _ _ _ _ EQ1 POST2 as EQ2.
  clear -EQ2.
  eapply eutt_equiv; eauto.
  split.
  - intros (? & ? & ?); do 2 econstructor; eauto. 
  - intros ?. inv H. inv REL1.
    destruct REL2 as [-> ?], REL0 as [<- ?]; eauto.
Qed.

(* TODO : develop the effect of handlers on this, in particular when interpreting into a state monad *)



