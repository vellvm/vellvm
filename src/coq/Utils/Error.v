(* begin hide *)
From Coq Require Import String.
Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.EitherMonad.

From ITree Require Import
     ITree
     Events.Exception.
(* end hide *)

(** * Error and exception monads 
  The arithmetic performed by vir programs being essentially pure, we have chosen
  not to wrap it in the [itree] monad. It gets instead injected into it when 
  representing syntactic constructs relying on it.

  It is however not completely pure: it is partial, and may raise undefined behavior.
  We hence use a nested "double" error monad for this purpose.
*)

Notation err := (sum string).

#[global] Instance Monad_err : Monad err := Monad_either string.
#[global] Instance Exception_err : MonadExc string err := Exception_either string.

#[global] Instance EqM_err: Monad.Eq1 err := fun a x y => @eq (err a) x y.

#[global] Instance EqMProps_err: Monad.Eq1Equivalence err.
  constructor.
  - repeat intro. repeat red. destruct x; reflexivity.
  - repeat intro. repeat red. repeat red in H.
    destruct x; destruct y; try auto; try contradiction.
  - repeat intro. repeat red in H, H0. repeat red.
    destruct x, y, z; auto; try contradiction; try etransitivity; eauto.
Qed.

#[global] Instance MonadLaws_err: Monad.MonadLawsE err.
  constructor.
  - intros. repeat red. cbn. auto.
  - intros. repeat red. cbn. destruct x eqn: Hx; auto.
  - intros. repeat red. cbn.
    destruct x; auto.
  - repeat intro. repeat red. cbn. repeat red in H. rewrite H.
    repeat red in H0. destruct y; auto.
Qed.

Definition trywith {E A:Type} {F} `{Monad F} `{MonadExc E F} (e:E) (o:option A) : F A :=
    match o with
    | Some x => ret x
    | None => raise e
    end.
#[export] Hint Unfold trywith: core.
Arguments trywith _ _ _ _ _: simpl nomatch.

Definition failwith {A:Type} {F} `{Monad F} `{MonadExc string F} (s:string) : F A := raise s.
#[export] Hint Unfold failwith: core.
Arguments failwith _ _ _ _: simpl nomatch.

Definition undef := err.
Definition undef_or_err := eitherT string err.

#[global] Instance Monad_undef_or_err : Monad undef_or_err.
unfold undef_or_err. typeclasses eauto.
Defined.

#[global] Instance EqM_undef_or_err : Monad.Eq1 undef_or_err :=
  fun (a : Type) (x y : undef_or_err a) => x = y.

#[global] Instance EqMProps_undef_or_err : Monad.Eq1Equivalence undef_or_err.
constructor; intuition.
repeat intro. etransitivity; eauto.
Defined.

#[global] Instance MonadLaws_undef_or_err: Monad.MonadLawsE undef_or_err.
constructor.
- repeat intro. cbn. destruct (f x). cbn. reflexivity.
- repeat intro. cbn. destruct x. cbn. destruct unEitherT; try reflexivity.
  destruct s; reflexivity.
- repeat intro. cbn. destruct x. destruct unEitherT; destruct s; reflexivity.
- repeat intro. destruct x, y. rewrite H. destruct unEitherT, unEitherT0; cbn; try reflexivity.
  destruct s0; [reflexivity | rewrite H0; reflexivity].
  destruct s0; [reflexivity | rewrite H0; reflexivity].
Qed.
