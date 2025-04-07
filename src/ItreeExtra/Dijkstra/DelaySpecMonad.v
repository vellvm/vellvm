From Coq Require Import
     Morphisms.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     ITree
     ITreeFacts
     Props.Infinite.

From ITree.Extra Require Import
     Dijkstra.DijkstraMonad
     Dijkstra.PureITreeBasics
     Dijkstra.IterRel.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.

#[local] Open Scope monad_scope.

Set Implicit Arguments.

(** Contains the DelaySpec monad, the specification monad for partial computations with no uninterpretted effects. Also contains an effect observation from the Delay monad into  the DelaySpec monad along with a proof that it is a monad morphism. Also contains a loop invariant principle for iter over Delay*)

Ltac clear_ret_eutt_spin :=
  match goal with | H : ret ?a ≈ ITree.spin  |- _ => simpl in H; exfalso; eapply not_ret_eutt_spin; eauto
             | H : Ret ?a ≈ ITree.spin  |- _ => exfalso; eapply not_ret_eutt_spin; eauto
             | H : ITree.spin ≈ ret ?a  |- _ => exfalso; symmetry in H; eapply not_ret_eutt_spin; eauto
             | H : any_infinite (ret _ ) |- _ => pinversion H
  end.

Ltac invert_evidence :=
  intros; repeat match goal with
                 | H : _ /\ _ |- _ => destruct H
                 | H : _ \/ _ |- _ => destruct H
                 | H : exists a : ?A, _ |- _ => destruct H as [?a ?H]
                 | x : ?A + ?B |- _ => destruct x as [?a | ?b]
                 | H : upaco1 _ _ _ |- _ => pclearbot
                 end.

Ltac invert_ret := simpl in *; match goal with | H : Ret ?a ≈ Ret ?b |- _ =>
                                                 apply eutt_inv_Ret in H; try discriminate; try (injection H as H);
                                                 subst end.


Ltac basic_solve := invert_evidence; try clear_ret_eutt_spin; try invert_ret.

Ltac dest_dep f a := destruct (f a) as [?fa ?Hfa] eqn : ?Heq; simpl in *.

Declare Scope delayspec_scope.
Delimit Scope delayspec_scope with delayspec.

#[local] Open Scope delayspec_scope.

Notation "a ∈ b" := (proj1_sig (A := _ -> Prop) b a) (at level 70) : delayspec_scope.
Notation "a ∋ b" := (proj1_sig (A := _ -> Prop) a b) (at level 70, only parsing) : delayspec_scope.

Definition Delay (A : Type) := itree void1 A.

#[global] Instance EqMDelay : Eq1 Delay := @ITreeMonad.Eq1_ITree void1.
#[global] Instance MonadDelay : Monad Delay := @Monad_itree void1.
#[global] Instance MonadIterDelay : MonadIter Delay := fun R I f a => ITree.iter f a.

Definition DelaySpecInput (A : Type) : Type := {p : Delay A -> Prop | resp_eutt p}.

Definition DelayIn {A : Type} (t : Delay A) (p : DelaySpecInput A) : Prop := proj1_sig p t.

Definition DelaySpec (A : Type) : Type :=
  { w : DelaySpecInput A -> Prop
  | forall (p p' : DelaySpecInput A), (forall t, t ∈ p -> t ∈ p') -> w p -> w p'}.

#[program] Definition ret_del (A : Type) (a : A) : DelaySpec A := fun p => p (Ret a).

#[program] Definition _bind_del (A B : Type) (w : DelaySpec A) (f : A -> DelaySpec B)
  : DelaySpecInput B -> Prop :=
  fun p => w ∋ (fun t => (exists a, Ret a ≈ t /\ p ∈ f a) \/ (any_infinite t /\ p ITree.spin)).
Next Obligation.
  intros t1 t2 Heutt. split; intros; basic_solve.
  - left. exists a. split; auto. rewrite H. auto.
  - right. rewrite <- Heutt. auto.
  - left. exists a. rewrite Heutt. auto.
  - right. rewrite Heutt. auto.
Qed.

#[program] Definition bind_del (A B : Type) (w : DelaySpec A) (f : A -> DelaySpec B) : DelaySpec B :=
  _bind_del w f.
Next Obligation.
  red. red in H0. destruct w as [w Hw]. simpl in *. eapply Hw; try apply H0.
  simpl. intros. basic_solve.
  - left. exists a. split; auto. dest_dep f a. eapply Hfa; eauto.
  - right. split; auto.
Qed.

#[global] Instance DelaySpecEq : Eq1 DelaySpec :=
  fun _ w1 w2 => forall p, p ∈ w1 <-> p ∈ w2.

#[global] Instance DelaySpecEqEquiv {A : Type} : Equivalence (A := DelaySpec A) eq1.
Proof.
  constructor; repeat intro; try tauto.
  - repeat red in H. specialize (H p). tauto.
  - repeat red in H, H0. specialize (H p). specialize (H0 p). tauto.
Qed.

#[global] Instance DelaySpecMonad : Monad DelaySpec :=
  {
    ret := ret_del;
    bind := bind_del
  }.

#[program, global]
Instance DelaySpecMonadLaws : MonadLawsE DelaySpec.
Next Obligation.
  repeat red. cbn. split; intros; basic_solve; auto.
  - pinversion H.
  - left. exists x. split; auto; reflexivity.
Qed.
Next Obligation.
  rename x into w.
  repeat red. cbn. split; intros.
  - red in H. simpl in H. destruct w as [w Hw]. simpl in *. eapply Hw; try apply H.
    intros. simpl in *. destruct p as [p Hp]. simpl in *. basic_solve.
    + eapply Hp; eauto. symmetry. auto.
    + apply div_spin_eutt in H0. eapply Hp; eauto.
  - red. destruct w as [w Hw]. simpl in *. eapply Hw; try apply H. intros.
    destruct p as [p Hp]. simpl in *.
    destruct (eutt_reta_or_div t); basic_solve.
    + left. exists a. split; auto. eapply Hp; eauto.
    + right. split; auto. eapply Hp; try apply H0. symmetry. apply div_spin_eutt. auto.
Qed.
Next Obligation.
  rename x into w.
  repeat red. cbn. split; intros.
  - red. red in H. destruct w as [w Hw]. simpl in *. destruct p as [p Hp]. simpl in *.
    eapply Hw; try apply H. intros. simpl in *. clear H. basic_solve.
    + left. exists a. auto.
    + right. auto.
  - red. red in H. destruct w as [w Hw]. simpl in *. destruct p as [p Hp]. simpl in *.
    eapply Hw; try apply H. simpl in *. intros. basic_solve.
    + left. exists a. auto.
    + right. split; auto. right. split; try auto using spin_infinite.
Qed.
Next Obligation.
  intros w1 w2 Hw k1 k2 Hk. unfold pointwise_relation in Hk.
  repeat red. unfold bind_del, _bind_del; split; intros; destruct w1 as [w1 Hw1];
                destruct w2 as [w2 Hw2]; do 2 red in Hw;
                  simpl in *.
  - rewrite <- Hw. eapply Hw1; try apply H; simpl in *. intros.
    destruct H0 as [ [a [Ht Ha] ] | [Hdiv Hspin] ]; auto.
    left. exists a. split; auto.
    specialize (Hk a). destruct (k1 a) as [k1a Hk1a];
                         destruct (k2 a) as [k2a Hk2a];
                         do 2 red in Hk; simpl in *.
    apply Hk. auto.
  - rewrite Hw. eapply Hw2; try apply H; simpl in *. intros.
    destruct H0 as [ [a [Ht Ha] ] | [Hdiv Hspin] ]; auto.
    left. exists a. split; auto.
    specialize (Hk a). destruct (k1 a) as [k1a Hk1a];
                         destruct (k2 a) as [k2a Hk2a];
                         do 2 red in Hk; simpl in *.
    apply Hk. auto.
Qed.

#[global] Instance DelaySpecOrderM : OrderM DelaySpec :=
  fun _ w1 w2 => forall p, p ∈ w2 -> p ∈ w1.

#[global] Instance DelaySpecOrder : OrderedMonad DelaySpec.
Proof.
  constructor.
  - intros. repeat red. intros. destruct w. auto.
  - intros. destruct w1. destruct w2. destruct w3. intro. simpl in *.
    specialize (H p2). specialize (H0 p2). simpl in *. intros. auto.
  - red. intros. repeat red. cbn. destruct w1 as [w1 Hw1]. destruct w2 as [w2 Hw2].
    intros. simpl in *. apply H. simpl in *. eapply Hw2; try apply H1. simpl in *. intros.
    basic_solve.
    + left. exists a. split; auto. apply H0. auto.
    + right. auto.
Qed.

#[program] Definition obs_del (A : Type) (t : Delay A) : DelaySpec A := fun p => t ∈ p.

#[global] Instance DelaySpecObs : EffectObs Delay DelaySpec := obs_del.

#[global] Instance DelaySpecMonadMorph : MonadMorphism Delay DelaySpec DelaySpecObs.
Proof.
  constructor.
  - repeat red. cbn. tauto.
  - repeat red. cbn. split; intros; basic_solve.
    + destruct (eutt_reta_or_div m); basic_solve.
      * left. exists a. split; auto. destruct p as [p Hp]. simpl in *. eapply Hp; try apply H.
        rewrite <- H0. setoid_rewrite bind_ret_l. reflexivity.
      * right. split; auto. apply div_spin_eutt in H0. destruct p as [p Hp]. eapply Hp; try apply H.
        rewrite H0. apply spin_bind.
    + destruct p as [p Hp]. simpl in *. eapply Hp; try apply H0. rewrite <- H. setoid_rewrite bind_ret_l. reflexivity.
    + apply div_spin_eutt in H. destruct p as [p Hp]. simpl in *. eapply Hp; try apply H0. rewrite H.
      symmetry. apply spin_bind.
Qed.

Definition iter_arrow_rel {A B : Type} (g : A -> Delay (A + B) ) (a1 a2 : A) : Prop :=
  g a1 ≈ ret (inl a2).

Notation "x =[ g ]=> y" := (iter_arrow_rel g x y) (at level 70) : delayspec_scope.

Lemma iter_inl_spin : forall (A B : Type) (g : A -> Delay (A + B) ) (a : A),
    not_wf_from (iter_arrow_rel g) a -> ITree.iter g a ≈ ITree.spin.
Proof.
  intros A B g. einit. ecofix CIH. intros. pinversion H0; try apply not_wf_F_mono'.
  setoid_rewrite unfold_iter_ktree. unfold iter_arrow_rel in Hrel. apply eutt_ret_euttge in Hrel.
  rewrite Hrel. rewrite bind_ret_l. rewrite unfold_spin. etau.
Qed.

(*eventually might want more general reasoning principle, like weaken the second precondition to only apply
  to a' reachable from a under g*)
Lemma iter_wf_converge : forall (A B : Type) (g : A -> Delay (A + B) ) (a : A),
    wf_from (iter_arrow_rel g) a ->
    (forall a, exists (ab : A + B), g a ≈ Ret ab) ->
    exists b : B, ITree.iter g a ≈ Ret b.
Proof.
  intros A B g a Hwf Hconv.
  induction Hwf.
  - specialize (Hconv a). destruct Hconv as [ [a' | b] Hret ].
    + exfalso. apply (H a'). auto.
    + exists b. rewrite unfold_iter. rewrite Hret. rewrite bind_ret_l.
      reflexivity.
  - specialize (Hconv a). destruct Hconv as [ [a' | b] Hret ].
    + apply H0 in Hret as Hret'. destruct Hret' as [b Hret']. exists b.
      rewrite unfold_iter. rewrite Hret. rewrite bind_ret_l. rewrite tau_eutt. auto.
    + exists b. rewrite unfold_iter. rewrite Hret. rewrite bind_ret_l.
      reflexivity.
Qed.


Definition loop_invar_imp {A B : Type} (q : Delay (A + B) -> Prop) (p : Delay B -> Prop) :Prop :=
  forall t, q (t >>= fun b => ret (inr b) ) -> p t.

Definition iter_lift {A B : Type} (g : A -> Delay (A + B)) : (A + B) -> Delay (A + B) :=
  fun x => match x with
             | inl a => g a
             | inr b => ret (inr b) end.

Notation "q -+> p" := (loop_invar_imp q p) (at level 80) : delayspec_scope.

Lemma loop_invar : forall (A B : Type) (g : A -> Delay (A + B) ) (a : A)
                          (p : Delay B -> Prop) (Hp : resp_eutt p)
                          (q : Delay (A + B) -> Prop) (Hq : resp_eutt q),
    (q -+> p) -> (q (g a)) ->
    (forall t, q t -> q (bind t (iter_lift g))) ->
    (p \1/ any_infinite) (ITree.iter g a).
Proof.
  intros. unfold loop_invar_imp in *.
  set (iter_arrow_rel g) as rg.
  destruct (classic_wf rg a).
  - left. induction H2.
    + unfold rg, iter_arrow_rel in H2. destruct (eutt_reta_or_div (g a)); basic_solve.
      * symmetry in H3. apply H2 in H3. contradiction.
      * apply H. cbn. eapply Hq; try apply H0.
        setoid_rewrite unfold_iter_ktree. rewrite <- H3.
        repeat setoid_rewrite bind_ret_l. reflexivity.
      * apply div_spin_eutt in H3. apply H. cbn.
        eapply Hq; try apply H0. rewrite H3.
        setoid_rewrite unfold_iter. rewrite H3.
        symmetry. setoid_rewrite <- spin_bind. apply spin_bind.
    + unfold rg in *.
      destruct (eutt_reta_or_div (g a)); basic_solve.
      * cbn in H4. rewrite unfold_iter, <- H4, bind_ret_l, tau_eutt.
        apply H3.
        -- red. symmetry; assumption.
        -- unfold iter_lift in H1. specialize (H1 (g a) H0).
           eapply Hq; try apply H1. cbn. rewrite <- H4. setoid_rewrite bind_ret_l.
           reflexivity.
      * cbn in H4. rewrite unfold_iter, <- H4, bind_ret_l.
        apply H. cbn. rewrite bind_ret_l. eapply Hq; eauto.
      * apply div_spin_eutt in H4. apply H. cbn.
        eapply Hq; try apply H0. rewrite H4.
        setoid_rewrite unfold_iter. rewrite H4. repeat setoid_rewrite <- spin_bind.
        reflexivity.
  - apply iter_inl_spin in H2. right. rewrite H2. apply spin_infinite.
Qed.
