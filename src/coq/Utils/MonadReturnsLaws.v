From Coq Require Import
     Morphisms.

From ITree Require Import
     Basics.Monad.

From ExtLib Require Import
     Structures.Monads.

From Vellvm.Utils Require Import MonadExcLaws PropT.

Local Open Scope monad_scope.

Set Primitive Projections.

Section Laws.

  Context (M : Type -> Type).
  Context {Monad : Monad M}.
  Context {Eq1 : @Eq1 M}.

  Class MonadReturns :=
    { MReturns : forall {A} (x : A) (ma : M A), Prop;

      MReturns_bind : forall {A B} (a : A) (b : B) (ma : M A) (k : A -> M B),
          MReturns a ma -> MReturns b (k a) -> MReturns b (bind ma k);

      MReturns_bind_inv : forall {A B} (ma : M A) (k : A -> M B) (b : B),
          MReturns b (bind ma k) -> exists a : A , MReturns a ma /\ MReturns b (k a);

      MReturns_ret : forall {A} (a : A) (ma : M A),
        eq1 ma (ret a) -> MReturns a ma;

      MReturns_ret_inv : forall {A} (x y : A),
          MReturns x (ret y) -> x = y;

      MReturns_Proper :> forall {A} (a : A),
          Proper (eq1 ==> iff) (MReturns a)
    }.

End Laws.

Arguments MReturns {M _ _ _ _}.
Arguments MReturns_bind {M _ _ _ _}.
Arguments MReturns_bind_inv {M _ _ _ _}.
Arguments MReturns_ret {M _ _ _ _}.
Arguments MReturns_ret_inv {M _ _ _ _}.

Section EitherT.
  Import EitherMonad.

  Context {E : Type}.
  Context {M : Type -> Type}.
  Context {HM : Monad M}.
  Context {EQM : @Eq1 M}.
  Context {EQV : @Eq1Equivalence M HM EQM}.
  Context {MRET : @MonadReturns M HM EQM}.
          

  Definition EitherTReturns {A} (a : A) (ma : eitherT E M A) : Prop
    := MReturns (inr a) (unEitherT ma).

  Lemma EitherTReturns_bind :
    forall {A B} (a : A) (b : B) (ma : eitherT E M A) (k : A -> eitherT E M B),
      EitherTReturns a ma -> EitherTReturns b (k a) -> EitherTReturns b (bind ma k).
  Proof.
    intros * Ha Hb.
    eapply MReturns_bind; eauto.
  Qed.

  Lemma EitherTReturns_bind_inv :
    forall {A B} (ma : eitherT E M A) (k : A -> eitherT E M B) (b : B),
      EitherTReturns b (bind ma k) -> exists a : A , EitherTReturns a ma /\ EitherTReturns b (k a).
  Proof.
    intros * Hb.
    unfold EitherTReturns in *.
    eapply MReturns_bind_inv in Hb as (ea & Ha & Hb).
    destruct ea; eauto.

    apply MReturns_ret_inv in Hb.
    inversion Hb.
  Qed.

  Lemma EitherTReturns_ret :
    forall {A} (a : A) (ma : eitherT E M A),
      eq1 ma (ret a) -> EitherTReturns a ma.
  Proof.
    intros * Hma.
    eapply MReturns_ret; eauto.
  Qed.

  Lemma EitherTReturns_ret_inv :
    forall {A} (x y : A),
      EitherTReturns x (ret y) -> x = y.
  Proof.
    intros * H.
    unfold EitherTReturns in H.
    eapply MReturns_ret_inv; eauto.
    eapply MReturns_ret_inv in H.
    inversion H.
    apply MReturns_ret.
    reflexivity.
  Qed.

  #[global] Instance EitherTReturns_Proper : forall {A} (a : A),
      Proper (eq1 ==> iff) (EitherTReturns a).
  Proof.
    intros A a.
    unfold Proper, respectful.
    intros x y H.
    split; intros Hret; unfold EitherTReturns in *.
    - eapply MReturns_Proper; eauto.
      symmetry.
      auto.
    - eapply MReturns_Proper; eauto.
  Qed.
  
  Instance MonadReturns_EitherT : MonadReturns (eitherT E M)
    := { MReturns := fun A => EitherTReturns;
         MReturns_bind := fun A B => EitherTReturns_bind;
         MReturns_bind_inv := fun A B => EitherTReturns_bind_inv;
         MReturns_ret := fun A => EitherTReturns_ret;
         MReturns_ret_inv := fun A => EitherTReturns_ret_inv
       }.

End EitherT.

Section StateT.
  From ITree Require Import
       ITree
       Basics.Basics
       Events.StateFacts
       Events.State.

  Import Monads.

  From Vellvm Require Import Utils.StateMonads.

  Context {S : Type}.
  Context {M : Type -> Type}.
  Context {HM : Monad M}.
  Context {EQM : @Eq1 M}.
  Context {EQV : @Eq1Equivalence M HM EQM}.
  Context {MRET : @MonadReturns M HM EQM}.
          

  Definition StateTReturns {A} (a : A) (ma : stateT S M A) : Prop
    := forall s, exists s', MReturns (a, s') (runStateT ma s).

  Lemma StateTReturns_bind :
    forall {A B} (a : A) (b : B) (ma : stateT S M A) (k : A -> stateT S M B),
      StateTReturns a ma -> StateTReturns b (k a) -> StateTReturns b (bind ma k).
  Proof.
    intros * Ha Hb.
    unfold StateTReturns in *.

    intros s.
    specialize (Ha s) as (sa & Ha).
    specialize (Hb sa) as (sb & Hb).

    exists sb.

    unfold runStateT in *.

    apply MReturns_bind_inv in Ha as (a' & Ha' & Ha).
    destruct a'.
    apply MReturns_ret_inv in Ha.
    inversion Ha; subst.

    apply MReturns_bind_inv in Hb as (b' & Hb' & Hb).
    destruct b'.
    apply MReturns_ret_inv in Hb.
    inversion Hb; subst.

    eapply MReturns_bind.
    cbn.
    eapply MReturns_bind; cbn; eauto.

    cbn.

    apply MReturns_ret.
    reflexivity.
  Qed.

  Lemma StateTReturns_bind_inv :
    forall {A B} (ma : stateT S M A) (k : A -> stateT S M B) (b : B),
      StateTReturns b (bind ma k) -> exists a : A , StateTReturns a ma /\ StateTReturns b (k a).
  Proof.
    intros * Hb.
    unfold StateTReturns in *.

    (* Somehow I need to pull out an `S` state value in order to get
       `a`, which is the result from `ma` that gets passed to `k`. 

       I don't think I can do this. Suppose `S` is `void`... May not
       be able to get a state value at all because the type is
       uninhabited, and then `a` would come out of thin air...
     *)
    eexists.
    split.
    - intros s.
      specialize (Hb s) as (sb & Hb).
      unfold runStateT in *.
      eapply MReturns_bind_inv in Hb as ((sb' & b') & Ha & Hb).
      eapply MReturns_bind_inv in Ha as ((sa' & a') & Ha' & Hb').
      exists sa'.
      eapply MReturns_bind; eauto.
      cbn in *.
      apply MReturns_ret.
      reflexivity.




    destruct ea; eauto.

    apply MReturns_ret_inv in Hb.
    inversion Hb.
  Qed.

  Lemma StateTReturns_ret :
    forall {A} (a : A) (ma : stateT S M A),
      eq1 ma (ret a) -> StateTReturns a ma.
  Proof.
    intros * Hma.
    eapply MReturns_ret; eauto.
  Qed.

  Lemma StateTReturns_ret_inv :
    forall {A} (x y : A),
      StateTReturns x (ret y) -> x = y.
  Proof.
    intros * H.
    unfold StateTReturns in H.
    eapply MReturns_ret_inv; eauto.
    eapply MReturns_ret_inv in H.
    inversion H.
    apply MReturns_ret.
    reflexivity.
  Qed.

  Instance MonadReturns_StateT : MonadReturns (stateT S M)
    := { MReturns := fun A => StateTReturns;
         MReturns_bind := fun A B => StateTReturns_bind;
         MReturns_bind_inv := fun A B => StateTReturns_bind_inv;
         MReturns_ret := fun A => StateTReturns_ret;
         MReturns_ret_inv := fun A => StateTReturns_ret_inv
       }.

End StateT.

From ITree Require Import
     ITree
     Basics.Basics
     Events.Exception
     Eq.Eq
     Events.StateFacts
     Events.State.

Instance ITree_MonadReturns {E} : MonadReturns (itree E)
  := { MReturns := fun A => Returns;
       MReturns_bind := Returns_bind E;
       MReturns_bind_inv := fun A B => Returns_bind_inversion;
       MReturns_ret := fun A => ReturnsRet;
       MReturns_ret_inv := Returns_ret_inv
     }.
