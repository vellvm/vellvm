From Coq Require Import
     Morphisms.

From ExtLib Require Import
     Structures.Monad.

From Paco Require Import paco.

From ITree Require Import
     ITree
     ITreeFacts
     Props.Infinite.

From ITree.Extra Require Import
     Dijkstra.DijkstraMonad
     Dijkstra.PureITreeBasics
     Dijkstra.IterRel
     Dijkstra.DelaySpecMonad.

Import Monads.
Import MonadNotation.

#[local] Open Scope monad_scope.
#[local] Open Scope dijkstra_scope.
#[local] Open Scope delayspec_scope.

Section StateSpecT.
  Context (S : Type).
  Context (W : Type -> Type).
  Context {MonadW : Monad W}.
  Context {OrderW : OrderM W}.
  Context {OrderedMonadW : OrderedMonad W}.
  Context {EqW : Eq1 W}.
  Context {EquivRel : forall A, Equivalence (eq1 (A := A)) }.
  Context {MonadLawsW : MonadLawsE W}.

  Definition StateSpecT (A : Type) := stateT S W A.

  #[global] Instance StateSpecTOrder : OrderM StateSpecT :=
    fun A (w1 w2 : stateT S W A) => forall (s : S), w1 s <≈ w2 s.

  #[global] Instance StateSpecTOrderedLaws : OrderedMonad StateSpecT.
  Proof.
    destruct OrderedMonadW.
    constructor.
    - repeat intro.  auto.
    - repeat intro. eapply trans; eauto.
    - intros A B w1 w2 f1 f2 Hlw Hlf. unfold StateSpecT in *.
      repeat red.
      intros. apply monot; auto. intros. destruct a as [s' a]. simpl.
      repeat red in Hlf. apply Hlf.
  Qed.

  #[global] Instance StateSpecTEq : Eq1 StateSpecT :=
    fun _ w1 w2 => forall s, (w1 s ≈ w2 s)%monad.

  #[global] Instance StateSpecTMonadLaws : MonadLawsE StateSpecT.
  Proof.
    destruct MonadLawsW.
    constructor.
    - intros A B f a. intro. repeat red.
      cbn.
      rewrite bind_ret_l. simpl. reflexivity.
    - intros A w. intro. cbn.
      etransitivity; [ | apply bind_ret_r ].
      eapply Proper_bind; [ reflexivity | ].
      intros []; reflexivity.
    - intros A B C w f g. intro. cbn. rewrite bind_bind. reflexivity.
    - intros A B w1 w2 Hw k1 k2 Hk.
      cbn. do 2 red. intros. do 2 red in Hw. rewrite Hw. do 3 red in Hk.
      setoid_rewrite Hk. reflexivity.
  Qed.

  Section Observation.
    Context (M : Type -> Type).
    Context {MonadM : Monad M}.
    Context {EffectObsMW : EffectObs M W}.
    Context {MonadMorphismMW : MonadMorphism M W EffectObsMW}.

    #[global] Instance EffectObsStateT : EffectObs (stateT S M) (stateT S W) := fun _ m s => obs _ (m s).

    #[global] Instance MonadMorphimStateT : MonadMorphism (stateT S M) (stateT S W) EffectObsStateT.
    Proof.
      destruct MonadMorphismMW.
      constructor.
      - intros. repeat red. intros. specialize (ret_pres (S * A)%type (s,a) ).
        cbn. rewrite <- ret_pres. reflexivity.
      - intros. repeat red. intros. cbn. specialize (bind_pres (S * A)%type (S * B)%type ).
        unfold obs, EffectObsStateT.
        rewrite bind_pres. reflexivity.
    Qed.

  End Observation.

  (*Can I encode a pre post thing, state spec enriches the precondition and
     specializes post condition*)

  (*maybe I need a computational monad M with a monad iter structure,
    I think the taus only showed up because I was using hte monad iter structure
    of strong bisimulation not weak,
    also note that this loop invar stuff, while relevant to D monads, is not
    itself of D monads
   *)

End StateSpecT.

Section LoopInvarSpecific.
  Context (S : Type).

  Definition StateSpec (A : Type) := StateSpecT S DelaySpec A.

  Definition State (A : Type) := stateT S Delay A.

  Instance StateIter : MonadIter State := MonadIter_stateT0.

  Definition reassoc {A B : Type} (t : Delay (S * (A + B) ) ) : Delay ((S * A) + (S * B)  ) :=
    t >>= (fun '(s,ab) =>
             match ab with
             | inl a => ret (inl (s , a))
             | inr b => ret (inr (s , b))
             end
).

  Definition iso_arrow {A B : Type} (f : A -> State B) (g : (S * A) -> Delay (S * B) ) :=
    forall (a : A) (s : S), f a s ≈ g (s,a).

  Definition decurry_flip {A B C : Type} (f : A -> B -> C) : B * A -> C :=
    fun '(b,a) => f a b.

  (*this is just decurry*)
  Definition iso_destatify_arrow {A B : Type} (f : A -> State (A + B) ) : (S * A) -> Delay ((S * A) + (S * B)) :=
    fun '(s,a) => reassoc (f a s).

  (*should be able to use original*)
  Lemma loop_invar_state: forall (A B : Type) (g : A -> State (A + B)) (a : A) (s : S)
               (p : Delay ( S * B) -> Prop) (q : Delay ((S * A) + (S * B))  -> Prop  )
               (Hp : resp_eutt p) (Hq : resp_eutt q) ,
        (q (reassoc (g a s) )) ->
        (q -+> p) -> (forall t, q t -> q (t >>= (iter_lift ( iso_destatify_arrow g)  ))) ->
         (p \1/ any_infinite) (MonadIter_stateT0 _ _ g a s) .
  Proof.
    intros.
    set (iso_destatify_arrow g) as g'.
    enough ((p \1/ any_infinite) (ITree.iter g' (s,a) )).
    - assert (ITree.iter g' (s,a) ≈ iter g a s).
      + unfold g', iso_destatify_arrow.
        unfold iter, Iter_Kleisli, Basics.iter, MonadIterDelay, StateIter,
        MonadIter_stateT0, reassoc. unfold Basics.iter.
        unfold MonadIterDelay. eapply eutt_iter. intro.
        destruct a0 as [a' s']. simpl.
        eapply eutt_clo_bind; try reflexivity. intros.
        subst. destruct u2. simpl. destruct s1; reflexivity.
      + assert (Hpdiv : resp_eutt (p \1/ any_infinite)).
        { intros t1 t2 Heutt. split; intros; basic_solve.
          - left. eapply Hp; eauto. symmetry. auto.
          - right. rewrite <- Heutt. auto.
          - left. eapply Hp; eauto.
          - right. rewrite Heutt. auto.
         }
        eapply Hpdiv; try apply H2. symmetry. auto.
     - eapply loop_invar; eauto.
  Qed.

  Definition state_iter_arrow_rel {A B S : Type} (g : A -> stateT S Delay (A + B) ) '(s0,a0) '(s1,a1) :=
    g a0 s0 ≈ Ret (s1, inl a1).

  Lemma iter_inl_spin_state : forall (A B S : Type) (g : A -> stateT S Delay (A + B) ) (a : A) (s : S),
      not_wf_from (state_iter_arrow_rel g ) (s,a) -> MonadIter_stateT0 _ _  g a s ≈ ITree.spin.
  Proof.
    intros. unfold MonadIter_stateT0.
    apply iter_inl_spin. (*seems to require some coinduciton*)
    generalize dependent a. generalize dependent s.
    pcofix CIH. intros. pinversion H0; try apply not_wf_F_mono'. pfold.
    apply not_wf with (a' := a'); eauto.
    - red in Hrel. destruct a' as [s' a']. simpl. red. simpl. rewrite Hrel.
      rewrite bind_ret_l. simpl. reflexivity.
    - right. destruct a'. eauto.
  Qed.

  Lemma iter_wf_converge_state : forall (A B S : Type)  (g : A -> stateT S Delay (A + B) ) (a : A) (s : S),
      (forall a s, exists ab, g a s ≈ Ret ab) ->
      wf_from (state_iter_arrow_rel g) (s,a) ->
      exists (p : S * B), MonadIter_stateT0 _ _ g a s ≈ Ret p.
  Proof.
    intros. unfold MonadIter_stateT0, Basics.iter, MonadIterDelay.
    apply iter_wf_converge.
    - eapply wf_from_sub_rel; try apply H0.
      repeat intro. unfold iter_arrow_rel in *. unfold state_iter_arrow_rel.
      clear H0 a s.
      destruct x as [s a]. simpl in *. destruct y as [s' a'].
      destruct (eutt_reta_or_div (g a s)); basic_solve.
      + rewrite <- H0. rewrite <- H0 in H1. simpl in H1. rewrite bind_ret_l in H1.
        simpl in *. destruct a0. simpl in *. destruct s1; basic_solve.
        reflexivity.
      + apply div_spin_eutt in H0. rewrite H0 in H1. rewrite <- spin_bind in H1.
        symmetry in H1. exfalso. eapply not_ret_eutt_spin; eauto.
   - clear H0 a s. intros [s a]. specialize (H a s). basic_solve.
     destruct ab as [s' [a' | b] ].
     + exists (inl (s',a') ). simpl. rewrite H. rewrite bind_ret_l. simpl.
       reflexivity.
     + exists (inr (s',b)). simpl. rewrite H. rewrite bind_ret_l. simpl.
       reflexivity.
  Qed.

End LoopInvarSpecific.
