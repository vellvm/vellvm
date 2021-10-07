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

      MFails : forall {A} (ma : M A), Prop;

      MFails_MReturns : forall {A} (ma : M A),
          MFails ma -> forall a, ~ MReturns a ma;

      MReturns_MFails : forall {A} (ma : M A) (a : A),
          MReturns a ma -> ~ MFails ma;

      MFails_ret : forall {A} (a : A),
          ~ MFails (ret a);

      MReturns_bind : forall {A B} (a : A) (b : B) (ma : M A) (k : A -> M B),
          MReturns a ma -> MReturns b (k a) -> MReturns b (bind ma k);

      MReturns_bind_inv : forall {A B} (ma : M A) (k : A -> M B) (b : B),
          MReturns b (bind ma k) -> exists a : A , MReturns a ma /\ MReturns b (k a);

      MReturns_ret : forall {A} (a : A) (ma : M A),
          ~MFails ma -> eq1 ma (ret a) -> MReturns a ma;

      MReturns_ret_inv : forall {A} (x y : A),
          MReturns x (ret y) -> x = y;

      MReturns_Proper :> forall {A} (a : A),
          Proper (eq1 ==> Basics.impl) (MReturns a)
   }.
End Laws.

Set Printing Implicit.
Unset Printing Notations.

Section MReturns_ProperFlip.
  Context (M : Type -> Type).
  Context {Monad : Monad M}.
  Context {Eq1 : @Eq1 M}.
  Context {MRET : @MonadReturns M Monad Eq1}.

  Class MonadReturns_ProperFlip :=
    { MReturns_ProperFlip :> forall {A} (a : A),
        Proper (eq1 ==> fun A B => Basics.impl B A) (MReturns _ a)
    }.
End MReturns_ProperFlip.

Section MonadReturnsInv.
  Context (M : Type -> Type).
  Context {Monad : Monad M}.
  Context {Eq1 : @Eq1 M}.
  Context {MRET : @MonadReturns M Monad Eq1}.
  Class MonadReturns_Proper_inv :=
    { MReturns_Proper_inv :> forall {A} (a: A),
        Proper ((fun (x y : M A) => MReturns M a x <-> MReturns M a y) ==> Monad.eq1) (fun x => x) }.
End MonadReturnsInv.

Arguments MReturns {M _ _ _ _}.
Arguments MFails {M _ _ _ _}.
Arguments MReturns_bind {M _ _ _ _}.
Arguments MReturns_bind_inv {M _ _ _ _}.
Arguments MReturns_ret {M _ _ _ _}.
Arguments MReturns_ret_inv {M _ _ _ _}.

Section Sum.
  Context {E : Type}.

  Definition SumReturns {A} (a : A) (ma : sum E A) : Prop
    := ma = inr a.

  Definition SumFails {A} (ma : sum E A) : Prop
    := exists e, ma = inl e.

  Lemma SumFails_SumReturns :
    forall {A} (ma : sum E A),
      SumFails ma -> forall a, ~ SumReturns a ma.
  Proof.
    intros A ma H a.
    destruct H as (e & FAILS).
    subst.
    intros CONTRA; inversion CONTRA.
  Qed.

  Lemma SumReturns_SumFails :
    forall {A} (ma : sum E A) (a : A),
      SumReturns a ma -> ~ SumFails ma.
  Proof.
    intros A ma a H.
    inversion H; subst.
    intros CONTRA; inversion CONTRA.
    inversion H0.
  Qed.

  Lemma SumFails_ret :
    forall {A} (a : A),
      ~SumFails (ret a).
  Proof.
    intros A a.
    intros FAILS.
    inversion FAILS.
    inversion H.
  Qed.

  Lemma SumReturns_bind :
    forall {A B} (a : A) (b : B) (ma : sum E A) (k : A -> sum E B),
      SumReturns a ma -> SumReturns b (k a) -> SumReturns b (bind ma k).
  Proof.
    intros * Ha Hb.
    unfold SumReturns in *.
    subst.
    auto.
  Qed.

  Lemma SumReturns_bind_inv :
    forall {A B} (ma : sum E A) (k : A -> sum E B) (b : B),
      SumReturns b (bind ma k) -> exists a : A , SumReturns a ma /\ SumReturns b (k a).
  Proof.
    intros * Hb.
    unfold SumReturns in *.
    destruct ma; inversion Hb.
    - exists a.
      auto.
  Qed.

  Lemma SumReturns_ret :
    forall {A} (a : A) (ma : sum E A),
      ~SumFails ma -> eq1 ma (ret a) -> SumReturns a ma.
  Proof.
    intros * Hma.
    auto.
  Qed.

  Lemma SumReturns_ret_inv :
    forall {A} (x y : A),
      SumReturns x (ret y) -> x = y.
  Proof.
    intros * H.
    unfold SumReturns in H.
    inversion H; auto.
  Qed.

  #[global] Instance SumReturns_ProperIff : forall {A} (a : A),
      Proper (eq1 ==> iff) (SumReturns a).
  Proof.
    intros A a.
    unfold Proper, respectful.
    intros x y H.
    split; intros Hret; unfold SumReturns in *; subst; auto.
  Qed.

  #[global] Instance SumReturns_Proper : forall {A} (a : A),
      Proper (eq1 ==> Basics.impl) (SumReturns a).
  Proof.
    intros A a.
    unfold Proper, respectful.
    intros x y H.
    intros Hret; unfold SumReturns in *; subst; auto.
  Qed.

  #[global] Instance SumReturns_ProperFlip : forall {A} (a : A),
      Proper (eq1 ==> fun A B => Basics.impl B A) (SumReturns a).
  Proof.
    intros A a.
    unfold Proper, respectful.
    intros x y H.
    intros Hret; unfold SumReturns in *; subst; auto.
  Qed.

  Instance MonadReturns_Sum : MonadReturns (sum E )
    := { MReturns := fun A => SumReturns;
         MFails := fun A => SumFails;
         MReturns_MFails := fun A => SumReturns_SumFails;
         MFails_MReturns := fun A => SumFails_SumReturns;
         MFails_ret := fun A => SumFails_ret;
         MReturns_bind := fun A B => SumReturns_bind;
         MReturns_bind_inv := fun A B => SumReturns_bind_inv;
         MReturns_ret := fun A => SumReturns_ret;
         MReturns_ret_inv := fun A => SumReturns_ret_inv
       }.

End Sum.


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

  Definition EitherTFails {A} (ma : eitherT E M A) : Prop
    := MFails (unEitherT ma).

  Lemma EitherTFails_EitherTReturns :
    forall {A} (ma : eitherT E M A),
      EitherTFails ma -> forall a, ~ EitherTReturns a ma.
  Proof.
    intros A ma FAILS a.
    unfold EitherTFails in FAILS.
    intros CONTRA.
    unfold EitherTReturns in CONTRA.
    eapply (MFails_MReturns M _ _ (inr a)); eauto.
    Unshelve.
    eauto.
  Qed.

  Lemma EitherTReturns_EitherTFails :
    forall {A} (ma : eitherT E M A) (a : A),
      EitherTReturns a ma -> ~ EitherTFails ma.
  Proof.
    intros A ma a RETS.
    unfold EitherTReturns, EitherTFails in *.
    eapply MReturns_MFails; eauto.
  Qed.

  Lemma EitherTFails_ret :
    forall {A} (a : A),
      ~ EitherTFails (ret a).
  Proof.
    intros A a.
    unfold EitherTFails.
    apply MFails_ret.
  Qed.

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
      ~EitherTFails ma -> eq1 ma (ret a) -> EitherTReturns a ma.
  Proof.
    intros * NFAILS Hma.
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
    apply MFails_ret.
    reflexivity.
  Qed.

  #[global] Instance EitherTReturns_Proper : forall {A} (a : A),
      Proper (eq1 ==> Basics.impl) (EitherTReturns a).
  Proof.
    intros A a.
    unfold Proper, respectful.
    intros x y H.
    intros Hret; unfold EitherTReturns in *.
    eapply MReturns_Proper; eauto.
  Qed.

  #[global] Instance EitherTReturns_ProperFlip : forall {A} (a : A),
      Proper (eq1 ==> fun A B => Basics.impl B A) (EitherTReturns a).
  Proof.
    intros A a.
    unfold Proper, respectful.
    intros x y H.
    intros Hret; unfold EitherTReturns in *.
    eapply MReturns_Proper; eauto.
    symmetry.
    auto.
  Qed.

  Instance MonadReturns_EitherT : MonadReturns (eitherT E M)
    := { MReturns := fun A => EitherTReturns;
         MFails := fun A => EitherTFails;
         MReturns_MFails := fun A => EitherTReturns_EitherTFails;
         MFails_MReturns := fun A => EitherTFails_EitherTReturns;
         MFails_ret := fun A => EitherTFails_ret;
         MReturns_bind := fun A B => EitherTReturns_bind;
         MReturns_bind_inv := fun A B => EitherTReturns_bind_inv;
         MReturns_ret := fun A => EitherTReturns_ret;
         MReturns_ret_inv := fun A => EitherTReturns_ret_inv
       }.

End EitherT.

(* TODO: Move this *)
Section Inhabited.
  Variable A: Type.
  Class Inhabited :=
    { has_value : A }.
End Inhabited.

(* TODO: Move this *)
Require Import ZArith.
Instance Inhabited_N : Inhabited N
  := { has_value := 0%N }.

Section StateT.
  From ITree Require Import
       ITree
       Basics.Basics
       Events.StateFacts
       Events.State.

  Import Monads.

  From Vellvm Require Import Utils.StateMonads.

  Context {S : Type}.
  Context {SINHAB : Inhabited S}.
  Context {M : Type -> Type}.
  Context {HM : Monad M}.
  Context {EQM : @Eq1 M}.
  Context {EQV : @Eq1Equivalence M HM EQM}.
  Context {MRET : @MonadReturns M HM EQM}.


  Definition StateTReturns {A} (a : A) (ma : stateT S M A) : Prop
    := forall s, exists s', MReturns (a, s') (runStateT ma s).

  (* Lemma StateTReturns_bind : *)
  (*   forall {A B} (s sa sb : S) (a : A) (b : B) (ma : stateT S M A) (k : A -> stateT S M B), *)
  (*     @StateTReturns A s sa a ma -> @StateTReturns B sa sb b (k a) -> @StateTReturns B s sb b (bind ma k). *)
  (* Proof. *)
  (*   intros * Ha Hb. *)
  (*   unfold StateTReturns in *. *)
  (*   cbn in *. *)
  (*   unfold runStateT in *. *)

  (*   apply MReturns_bind_inv in Ha as (a' & Ha' & Ha). *)
  (*   apply MReturns_bind_inv in Hb as (b' & Hb' & Hb). *)
  (*   destruct a' as (sa' & a'). *)
  (*   destruct b' as (sb' & b'). *)
  (*   apply MReturns_ret_inv in Ha. *)
  (*   apply MReturns_ret_inv in Hb. *)
  (*   inv Ha. *)
  (*   inv Hb. *)

  (*   repeat eapply MReturns_bind; eauto. *)
  (*   cbn. *)

  (*   apply MReturns_ret. *)
  (*   reflexivity. *)
  (* Qed. *)

  Lemma StateTReturns_bind_inv :
    forall {A B} (ma : stateT S M A) (k : A -> stateT S M B) (b : B),
      (forall s, exists sb, MReturns (b, sb) (runStateT (bind ma k) s)) -> forall s, exists (sa : S) (sb : S) (a : A), MReturns (a, sa) (runStateT ma s) /\ MReturns (b, sb) (runStateT (k a) sa).
  Proof.
    intros A B ma k b H s.

    specialize (H s) as (sb & RET).
    cbn in RET.
    apply MReturns_bind_inv in RET as ((s' & b') & Hbind & Hb).
    apply MReturns_bind_inv in Hbind as ((sa & a) & Hbind & Hb').

    exists sa. exists sb. exists a.
    split.
    - unfold runStateT.
      eapply MReturns_bind; eauto.
      cbn.
      apply MReturns_ret; [apply MFails_ret|reflexivity].
    - unfold runStateT.
      eapply MReturns_bind; eauto.
  Qed.

  (* Lemma StateTReturns_ret : *)
  (*   forall {A} (a : A) (ma : stateT S M A), *)
  (*     eq1 ma (ret a) -> StateTReturns a ma. *)
  (* Proof. *)
  (*   intros * Hma. *)
  (*   eapply MReturns_ret; eauto. *)
  (* Qed. *)

  (* Lemma StateTReturns_ret_inv : *)
  (*   forall {A} (x y : A), *)
  (*     StateTReturns x (ret y) -> x = y. *)
  (* Proof. *)
  (*   intros * H. *)
  (*   unfold StateTReturns in H. *)
  (*   eapply MReturns_ret_inv; eauto. *)
  (*   eapply MReturns_ret_inv in H. *)
  (*   inversion H. *)
  (*   apply MReturns_ret. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Instance MonadReturns_StateT : MonadReturns (stateT S M) *)
  (*   := { MReturns := fun A => StateTReturns; *)
  (*        MReturns_bind := fun A B => StateTReturns_bind; *)
  (*        MReturns_bind_inv := fun A B => StateTReturns_bind_inv; *)
  (*        MReturns_ret := fun A => StateTReturns_ret; *)
  (*        MReturns_ret_inv := fun A => StateTReturns_ret_inv *)
  (*      }. *)

End StateT.


Section ITree.
  From ITree Require Import
       ITree
       Basics.Basics
       Events.Exception
       Eq.Eq
       Events.StateFacts
       Events.State.

  (* Definition ITreeFails := fun {E A} (ma : itree E A) => False. *)

  (* Lemma ITreeReturns_ret : *)
    

  (* Instance ITree_MonadReturns {E} : MonadReturns (itree E) *)
  (*   := { MReturns := fun A => Returns; *)
  (*        MFails := fun A => ITreeFails; *)
  (*        MReturns_bind := Returns_bind E; *)
  (*        MReturns_bind_inv := fun A B => Returns_bind_inversion; *)
  (*        MReturns_ret := fun A => ReturnsRet; *)
  (*        MReturns_ret_inv := Returns_ret_inv *)
  (*      }. *)

End ITree.
