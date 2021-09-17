(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

(* begin hide *)
From Coq Require Import String.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Structures.MonadExc
     Data.Monads.EitherMonad.

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

Instance Monad_err : Monad err := Monad_either string.
Instance Exception_err : MonadExc string err := Exception_either string.

Instance EqM_err: Monad.Eq1 err := fun a x y => @eq (err a) x y.

Instance EqMProps_err: Monad.Eq1Equivalence err.
  constructor.
  - repeat intro. repeat red. destruct x; reflexivity.
  - repeat intro. repeat red. repeat red in H.
    destruct x; destruct y; try auto; try contradiction.
  - repeat intro. repeat red in H, H0. repeat red.
    destruct x, y, z; auto; try contradiction; try etransitivity; eauto.
Qed.

Instance MonadLaws_err: Monad.MonadLawsE err.
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

Inductive UB_MESSAGE :=
| UB_message : string -> UB_MESSAGE
.

Inductive ERR_MESSAGE :=
| ERR_message : string -> ERR_MESSAGE
.

Notation UB := (sum UB_MESSAGE).
Notation ERR := (sum ERR_MESSAGE).

Instance Exception_UB : MonadExc UB_MESSAGE UB := Exception_either UB_MESSAGE.
Instance Exception_ERR : MonadExc ERR_MESSAGE ERR := Exception_either ERR_MESSAGE.

Class VErrorM (M : Type -> Type) : Type :=
  { raise_error : forall {A}, string -> M A }.

Class UBM (M : Type -> Type) : Type :=
  { raise_ub : forall {A}, string -> M A }.

#[global] Instance VErrorM_E_MT {M : Type -> Type} {MT : (Type -> Type) -> Type -> Type} `{MonadT (MT M) M} `{VErrorM M} : VErrorM (MT M) :=
  { raise_error := fun A e => lift (raise_error e);
  }.

#[global] Instance UBM_E_MT {M : Type -> Type} {MT : (Type -> Type) -> Type -> Type} `{MonadT (MT M) M} `{UBM M} : UBM (MT M) :=
  { raise_ub := fun A e => lift (raise_ub e);
  }.

#[global] Instance VErrorM_MonadExc {M} `{MonadExc ERR_MESSAGE M} : VErrorM M
  := { raise_error := fun _ msg => MonadExc.raise (ERR_message msg) }.

#[global] Instance UBM_MonadExc {M} `{MonadExc UB_MESSAGE M} : UBM M
  := { raise_ub := fun _ msg => MonadExc.raise (UB_message msg) }.

Instance Exception_UB_string : MonadExc string UB :=
  {| MonadExc.raise := fun _ msg => inl (UB_message msg);
     catch := fun T c h =>
                match c with
                | inl (UB_message msg) => h msg
                | inr _ => c
                end
  |}.

Instance Exception_ERR_string : MonadExc string ERR :=
  {| MonadExc.raise := fun _ msg => inl (ERR_message msg);
     catch := fun T c h =>
                match c with
                | inl (ERR_message msg) => h msg
                | inr _ => c
                end
  |}.

Definition err_to_ERR {A} (e : err A) : ERR A
  := match e with
     | inl e => inl (ERR_message e)
     | inr x => inr x
     end.

Definition lift_err {M A} `{MonadExc string M} `{Monad M} (e : err A) : (M A)
  := match e with
     | inl e => MonadExc.raise e
     | inr x => ret x
     end.

Definition lift_ERR {M A} `{MonadExc ERR_MESSAGE M} `{Monad M} (e : ERR A) : (M A)
  := match e with
     | inl e => MonadExc.raise e
     | inr x => ret x
     end.

Definition err_or_ub := eitherT ERR_MESSAGE UB.

Instance Monad_err_or_ub : Monad err_or_ub.
unfold err_or_ub. typeclasses eauto.
Defined.

Instance EqM_err_or_ub : Monad.Eq1 err_or_ub :=
  fun (a : Type) (x y : err_or_ub a) => x = y.

Instance EqMProps_err_or_ub : Monad.Eq1Equivalence err_or_ub.
constructor; intuition.
repeat intro. etransitivity; eauto.
Defined.

Instance MonadLaws_err_or_ub: Monad.MonadLawsE err_or_ub.
constructor.
- repeat intro. cbn. destruct (f x). cbn. reflexivity.
- repeat intro. cbn. destruct x. cbn. destruct unEitherT; try reflexivity.
  destruct s; reflexivity.
- repeat intro. cbn. destruct x. destruct unEitherT.
  destruct u; destruct s; reflexivity.
  destruct s; reflexivity.
- repeat intro. destruct x, y. rewrite H. destruct unEitherT, unEitherT0; cbn; try reflexivity.
  destruct s; [reflexivity | rewrite H0; reflexivity].
  destruct s0; [reflexivity | rewrite H0; reflexivity].
Qed.
