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
Require Import FunctionalExtensionality.

From Coq Require Import String.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Structures.MonadExc
     Data.Monads.EitherMonad.

From ITree Require Import
     ITree
     Events.Exception.

From Vellvm.Utils Require Import MonadReturnsLaws.

(* end hide *)

(** * Error and exception monads 
  The arithmetic performed by vir programs being essentially pure, we have chosen
  not to wrap it in the [itree] monad. It gets instead injected into it when 
  representing syntactic constructs relying on it.

  It is however not completely pure: it is partial, and may raise undefined behavior.
  We hence use a nested "double" error monad for this purpose.
*)

Notation err := (sum string).

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

Instance EqM_eitherT {E} {M} `{Monad.Eq1 M} : Monad.Eq1 (eitherT E M)
  := fun (a : Type) x y => Monad.eq1 (unEitherT x) (unEitherT y).

Instance EqMProps_eitherT {E} {M} `{Monad.Eq1Equivalence M} : Monad.Eq1Equivalence (eitherT E M).
constructor; intuition;
repeat intro.
- unfold Monad.eq1, EqM_eitherT.
  reflexivity.
- unfold Monad.eq1, EqM_eitherT.
  symmetry.
  auto.
- unfold Monad.eq1, EqM_eitherT.
  etransitivity; eauto.
Defined.

(* Instance MonadLaws_eitherT {E} {M} `{HM: Monad M} `{MEQ1 : Monad.Eq1 M} `{MEQ1V : @Monad.Eq1Equivalence M HM MEQ1} `{LAWS: @Monad.MonadLawsE M MEQ1 HM} `{MRETS : @MonadReturns M HM MEQ1} `{MRETSINV : @MonadReturns_Proper_inv M HM MEQ1 MRETS} : Monad.MonadLawsE (eitherT E M). *)
(* destruct LAWS. *)

(* constructor. *)
(* - repeat intro. cbn. destruct (f x) as [fx] eqn:Hfx. cbn. unfold Monad.eq1, EqM_eitherT. *)
(*   cbn. *)
(*   etransitivity; eauto. *)
(*   rewrite Hfx. *)
(*   cbn. *)
(*   reflexivity. *)
(* - repeat intro. cbn. destruct x as [x'] eqn:Hx. subst. cbn. unfold Monad.eq1, EqM_eitherT. *)
(*   cbn. *)
(*   replace (fun xM : E + A => *)
(*         match xM with *)
(*         | inl x => ret (inl x) *)
(*         | inr x => ret (inr x) *)
(*         end) with (fun xM : E + A => ret xM). *)
(*   etransitivity; eauto. *)
(*   reflexivity. *)

(*   apply functional_extensionality. *)
(*   intros x. *)
(*   destruct x; auto. *)
(* - repeat intro. cbn. destruct x as [x'] eqn:Hx. *)
(*   unfold Monad.eq1, EqM_eitherT. cbn. *)
(*   rewrite bind_bind. *)

(*   destruct MRETS. *)
(*   destruct MRETSINV. *)

(*   eapply MReturns_Proper_inv. *)
(*   split. *)
(*   + intros H. *)
(*     eapply MReturns_bind_inv in H as (xv & Hxv & RET). *)
(*     eapply MReturns_bind; eauto. *)
(*     destruct xv; eauto. *)
(*     rewrite bind_ret_l in RET; eauto. *)
(*   + intros H. *)
(*     eapply MReturns_bind_inv in H as (xv & Hxv & RET). *)
(*     eapply MReturns_bind; eauto. *)
(*     destruct xv; eauto. *)
(*     rewrite bind_ret_l; eauto. *)

(* - repeat intro. *)
(*   destruct x as [x'] eqn:Hx. *)
(*   destruct y as [y'] eqn:Hy. *)
(*   unfold Monad.eq1, EqM_eitherT. *)
(*   cbn in *. *)

(*   destruct MRETS. *)
(*   destruct MRETSINV. *)

(*   subst. *)
(*   unfold Monad.eq1, EqM_eitherT in H. *)
(*   cbn in H. *)
(*   rewrite <- H. *)

(*   eapply MReturns_Proper_inv. *)
(*   split. *)
(*   + intros RETS. *)
(*     eapply MReturns_bind_inv in RETS as (xv & Hxv & RETS). *)

(*     destruct xv; eauto. *)
(*     cbn in *. *)
(*     eapply MReturns_bind; eauto. *)
(*     eapply MReturns_bind; eauto. *)
(*     cbn. *)

(*     unfold Morphisms.pointwise_relation in H0. *)
(*     specialize (H0 a). *)

(*     unfold Monad.eq1, EqM_eitherT in H0. *)
(*     rewrite H0 in RETS; eauto. *)
(*   + intros RETS. *)
(*     eapply MReturns_bind_inv in RETS as (xv & Hxv & RETS). *)

(*     destruct xv; eauto. *)
(*     cbn in *. *)
(*     eapply MReturns_bind; eauto. *)
(*     eapply MReturns_bind; eauto. *)
(*     cbn. *)

(*     unfold Morphisms.pointwise_relation in H0. *)
(*     specialize (H0 a). *)

(*     unfold Monad.eq1, EqM_eitherT in H0. *)
(*     rewrite H0; eauto. *)
(* Defined. *)

Definition err_to_err_or_ub {A} (e : err A) : err_or_ub A
  := match e with
     | inr a => ret a
     | inl e => raise_error e
     end.
