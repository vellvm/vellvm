From Coq Require Import
     List
     Morphisms.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.EitherMonad
     Data.Monads.IdentityMonad.

From ITree Require Import
     Basics.Monad Basics.MonadState.

From Vellvm Require Import
     Utils.Util.

Import Monads.

Import MonadNotation.
Import ListNotations.

Open Scope monad.

Fixpoint foldM {a b} {M} `{Monad M} (f : b -> a -> M b ) (acc : b) (l : list a) : M b
  := match l with
     | [] => ret acc
     | (x :: xs) =>
       b <- f acc x;;
       foldM f b xs
     end.

Lemma map_monad_unfold :
  forall {A B : Type} {M : Type -> Type} {H : Monad M} (x : A) (xs : list A)
    (f : A -> M B),
    map_monad f (x :: xs) =
    b <- f x;;
    bs <- map_monad (fun (x0 : A) => f x0) xs;;
    ret (b :: bs).
Proof.
  intros A B M H x xs f.
  induction xs; cbn; auto.
Qed.

Lemma map_monad_In {m : Type -> Type} {H : Monad m} {A B} (l : list A) (f: forall (x : A), In x l -> m B) : m (list B).
Proof.
  induction l.
  - exact (ret []).
  - refine (b <- f a _;; bs <- IHl _;; ret (b::bs)).
    + cbn; auto.
    + intros x Hin.
      apply (f x).
      cbn; auto.
Defined.

Lemma map_monad_In_unfold :
  forall {A B M} `{Monad M} (x : A) (xs : list A) (f : forall (elt:A), In elt (x::xs) -> M B),
    map_monad_In (x::xs) f = b <- f x (or_introl eq_refl);;
                            bs <- map_monad_In xs (fun x HIn => f x (or_intror HIn));;
                            ret (b :: bs).
Proof.
  intros A B M H x xs f.
  induction xs; cbn; auto.
Qed.


Instance EqM_sum {E} : Monad.Eq1 (sum E) :=
  fun (a : Type) (x y : sum E a) => x = y.

Instance EqMProps_sum {E} : Monad.Eq1Equivalence (sum E).
constructor; intuition.
repeat intro. etransitivity; eauto.
Defined.

Instance MonadLaws_sum {T} : Monad.MonadLawsE (sum T).
  constructor.
  - intros. repeat red. cbn. auto.
  - intros. repeat red. cbn. destruct x eqn: Hx; auto.
  - intros. repeat red. cbn.
    destruct x; auto.
  - repeat intro. repeat red. cbn. repeat red in H. rewrite H.
    repeat red in H0. destruct y; auto.
Qed.

Instance EqM_eitherT {E} {M} `{Monad.Eq1 M} : Monad.Eq1 (eitherT E M)
  := fun (a : Type) x y => Monad.eq1 (unEitherT x) (unEitherT y).
Global Instance Eq1Equivalence_eitherT :
  forall {M : Type -> Type} {H : Monad M} {H0 : Monad.Eq1 M} E,
    Monad.Eq1Equivalence M -> Monad.Eq1Equivalence (eitherT E M).
Proof.
  constructor; intuition;
  repeat intro.
  - unfold Monad.eq1, EqM_eitherT.
    reflexivity.
  - unfold Monad.eq1, EqM_eitherT.
    symmetry.
    auto.
  - unfold Monad.eq1, EqM_eitherT.
    etransitivity; eauto.
Qed.

(* TODO: move this *)
Global Instance Eq1_ident : Monad.Eq1 IdentityMonad.ident
  := {eq1 := fun A => Logic.eq}.

Global Instance Eq1Equivalence_ident : Monad.Eq1Equivalence IdentityMonad.ident.
Proof.
  split; red.
  - intros x.
    reflexivity.
  - intros x y H.
    rewrite H.
    reflexivity.
  - intros x y z H H0.
    rewrite H. rewrite H0.
    reflexivity.
Defined.

Global Instance MonadLawsE_ident : Monad.MonadLawsE IdentityMonad.ident.
Proof.
  split; intros *.
  - reflexivity.
  - destruct x; reflexivity.
  - cbn. reflexivity.
  - unfold Proper, respectful.
    intros x y H x0 y0 H0.
    cbn.
    rewrite H.
    rewrite H0.
    reflexivity.
Defined.

Lemma match_ret_sum :
  forall {X Y M} `{HM: Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM} (ma : (X + Y)%type),
    match ma with
    | inl a => ret (inl a)
    | inr a => ret (inr a)
    end ≈ @ret M _ _ ma.
Proof.
  intros X Y M HM EQM EQV ma.
  destruct ma; reflexivity.
Qed.

Global Instance MonadLaws_eitherT {E} {M} `{HM : Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM} `{@Monad.MonadLawsE M EQM _} : Monad.MonadLawsE (eitherT E M).
Proof.
  split; intros *.
  - cbn.
    destruct H.
    do 2 red.
    cbn. intros.

    rewrite bind_ret_l.
    reflexivity.
  - cbn.
    do 2 red.
    cbn.
    destruct x as [x].
    cbn.

    setoid_rewrite match_ret_sum.
    rewrite bind_ret_r.
    reflexivity.
  - cbn.
    do 2 red.
    destruct x as [x].
    cbn.

    rewrite bind_bind.
    
    assert (forall v : (E + A)%type,
              xM <- match v with
                   | inl x0 => ret (inl x0)
                   | inr x0 => unEitherT (f x0)
                   end;;
              match xM with
              | inl x0 => ret (inl x0)
              | inr x0 => unEitherT (g x0)
              end ≈
                  match v with
                  | inl x0 => ret (inl x0)
                  | inr x0 =>
                    xM0 <- unEitherT (f x0);;
                    match xM0 with
                    | inl x1 => ret (inl x1)
                    | inr x1 => unEitherT (g x1)
                    end
                  end).
    { intros [e | a].
      rewrite bind_ret_l; reflexivity.
      reflexivity.
    }

    setoid_rewrite H0.
    reflexivity.
  - unfold Proper, respectful.
    intros x y H0 x0 y0 H1.
    cbn.
    do 2 red.
    cbn.

    do 2 red in H0.
    destruct H.

    do 3 red in H1.
    
    unfold Proper, respectful in Proper_bind.
    apply Proper_bind; eauto.
    intros a.
    destruct a; eauto.
    reflexivity.
Defined.

Existing Instance MonadState.MonadLawsE_stateTM.
