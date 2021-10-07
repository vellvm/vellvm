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

From Coq Require Import
     String
     Classes.Morphisms.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Structures.MonadExc
     Data.Monads.EitherMonad.

From ITree Require Import
     ITree
     Events.Exception.

From Vellvm.Utils Require Import MonadReturnsLaws.

Import Monad.

(* end hide *)

(** * Error and exception monads 
  The arithmetic performed by vir programs being essentially pure, we have chosen
  not to wrap it in the [itree] monad. It gets instead injected into it when 
  representing syntactic constructs relying on it.

  It is however not completely pure: it is partial, and may raise undefined behavior.
  We hence use a nested "double" error monad for this purpose.
*)

Notation err := (sum string).

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

Inductive err_or_ub A :=
  ERR_OR_UB { unERR_OR_UB : eitherT ERR_MESSAGE UB A }.
Arguments ERR_OR_UB {_} _.
Arguments unERR_OR_UB {_} _.

Instance EqM_err_or_ub : Monad.Eq1 err_or_ub.
Proof.
  (* refine (fun T mt1 mt2 => _). *)
  (* destruct mt1, mt2. *)
  (* apply (Monad.eq1 unERR_OR_UB0 unERR_OR_UB1). *)
  
  refine (fun T mt1 mt2 => _).
  destruct mt1 as [[[ub_mt1 | [err_mt1 | t1]]]].
  - (* UB *)
    exact True.
  - (* Error *)
    exact True.
  - (* Success *)
    destruct mt2 as [[[ub_mt2 | [err_mt2 | t2]]]].
    + exact False.
    + exact False.
    + exact (t1 = t2).
Defined.

Import MonadNotation.
Import Utils.Monads.

#[global] Instance Monad_err_or_ub : Monad err_or_ub.
Proof.
  split.
  - exact (fun T t => ERR_OR_UB (ret t)).
  - exact (fun A B ema k =>
             match ema with
             | ERR_OR_UB ma =>
               ERR_OR_UB (bind ma (fun a => unERR_OR_UB (k a)))
             end).
Defined.

#[global] Instance Functor_err_or_ub : Functor err_or_ub.
Proof.
  split.
  - exact (fun A B f ema =>
             ERR_OR_UB (fmap f (unERR_OR_UB ema))).
Defined.

#[global] Instance MonadLawsE_err_or_ub : MonadLawsE err_or_ub.
Proof.
  split.
  - intros A B f x.
    cbn.
    destruct (f x) as [[[[ub_msg] | [[err_msg] | fx]]]]; cbn; auto.
  - intros A x.
    destruct x as [[[[ub_msg] | [[err_msg] | x]]]]; cbn; auto.
  - intros A B C x f g.
    cbn.
    destruct x as [[[[ub_msg] | [[err_msg] | x]]]]; cbn; auto.
    destruct (f x) as [[[[ub_msg] | [[err_msg] | fx]]]]; cbn; auto.
    destruct (g fx) as [[[[ub_msg] | [[err_msg] | gfx]]]]; cbn; auto.
  - intros A B.
    unfold Proper, respectful.
    intros x y H x0 y0 H0.
    destruct x as [[[[ub_msg] | [[err_msg] | x]]]]; cbn; auto.
    destruct y as [[[[ub_msg] | [[err_msg] | y]]]]; cbn; auto; inversion H.
    subst.

    destruct (x0 y) as [[[[ub_msg] | [[err_msg] | x0y]]]] eqn:Hx0y; cbn; auto.
    unfold pointwise_relation in H0.
    specialize (H0 y).

    unfold EqM_err_or_ub in *.
    cbn in *.

    unfold eq1 in H0.
    rewrite Hx0y in H0.
    destruct (y0 y) as [[[[ub_msg] | [[err_msg] | y0y]]]]; cbn; auto.
Defined.


#[global] Instance VErrorM_err_or_ub : VErrorM err_or_ub
  := { raise_error := fun _ msg => ERR_OR_UB (raise_error msg) }.

#[global] Instance UBM_err_or_ub : UBM err_or_ub
  := { raise_ub := fun _ msg => ERR_OR_UB (raise_ub msg) }.

Lemma unERR_OR_UB_bind :
  forall {A B} (ma : err_or_ub A) (k : A -> err_or_ub B),
    Monad.eq1 (unERR_OR_UB (x <- ma;; k x)) (x <- unERR_OR_UB ma;; (unERR_OR_UB (k x))).
Proof.
  intros A B ma k.
  cbn.
  destruct ma as [[[ub_a | [err_a | a]]]]; cbn; reflexivity.
Qed.

Section MonadReturns.
  Definition ErrOrUBReturns {A} (a : A) (ma : err_or_ub A) : Prop
    := match ma with
       | ERR_OR_UB ea =>
         match unEitherT ea with
         | inl (UB_message msg) => False
         | inr (inl (ERR_message msg)) => False
         | inr (inr a') => a' = a
         end
       end.

  Definition ErrOrUBFails {A} (ma : err_or_ub A) : Prop
    := match ma with
       | ERR_OR_UB ea =>
         match unEitherT ea with
         | inl (UB_message msg) => True
         | inr (inl (ERR_message msg)) => True
         | inr (inr a') => False
         end
       end.

  Lemma ErrOrUBFails_ErrOrUBReturns : forall {A} (ma : err_or_ub A),
      ErrOrUBFails ma -> forall a, ~ ErrOrUBReturns a ma.
  Proof.
    intros A ma FAILS a.
    destruct ma as [[[[ub_msg] | [[err_msg] | a']]]]; cbn in FAILS; auto.
  Qed.

  Lemma ErrOrUBReturns_ErrOrUBFails : forall {A} (ma : err_or_ub A) (a : A),
      ErrOrUBReturns a ma -> ~ ErrOrUBFails ma.
  Proof.
    intros A ma a RETS.
    destruct ma as [[[[ub_msg] | [[err_msg] | a']]]]; cbn in RETS; auto.
  Qed.

  Lemma ErrOrUBFails_ret : forall {A} (a : A),
      ~ ErrOrUBFails (ret a).
  Proof.
    intros A a CONTRA.
    inversion CONTRA.
  Qed.

  Lemma ErrOrUBReturns_bind :
    forall {A B} (a : A) (b : B) (ma : err_or_ub A) (k : A -> err_or_ub B),
      ErrOrUBReturns a ma -> ErrOrUBReturns b (k a) -> ErrOrUBReturns b (bind ma k).
  Proof.
    intros * Ha Hb.
    unfold ErrOrUBReturns in *.
    destruct ma as [[[[ub_msg] | [[err_msg] | a']]]]; cbn in *; try solve [inversion Ha].
    subst.
    destruct (k a); auto.
  Qed.

  Lemma ErrOrUBReturns_bind_inv :
    forall {A B} (ma : err_or_ub A) (k : A -> err_or_ub B) (b : B),
      ErrOrUBReturns b (bind ma k) -> exists a : A , ErrOrUBReturns a ma /\ ErrOrUBReturns b (k a).
  Proof.
    intros * Hb.
    unfold ErrOrUBReturns in *.
    destruct ma as [[[[ub_msg] | [[err_msg] | a']]]]; cbn in *; try solve [inversion Hb].
    destruct (k a') as [[[[ub_msg] | [[err_msg] | a'']]]] eqn:Hk'; cbn in *; try solve [inversion Hb].
    subst.
    exists a'.
    split; auto.
    rewrite Hk'.
    cbn; auto.
  Qed.

  Lemma ErrOrUBReturns_ret :
    forall {A} (a : A) (ma : err_or_ub A),
      ~ErrOrUBFails ma -> Monad.eq1 ma (ret a) -> ErrOrUBReturns a ma.
  Proof.
    intros * FAILS Hma.    
    destruct ma as [[[[ub_msg] | [[err_msg] | a']]]]; cbn in FAILS; auto; try contradiction.
  Qed.

  Lemma ErrOrUBReturns_ret_inv :
    forall {A} (x y : A),
      ErrOrUBReturns x (ret y) -> x = y.
  Proof.
    intros * H.
    unfold ErrOrUBReturns in H.
    inversion H; auto.
  Qed.

  #[global] Instance ErrOrUBReturns_Proper : forall {A} (a : A),
      Proper (eq1 ==> Basics.impl) (ErrOrUBReturns a).
  Proof.
    intros A a.
    unfold Proper, respectful.
    intros x y H.
    unfold ErrOrUBReturns in *.
    
    destruct x as [[[[ub_x] | [[err_x] | x]]]];
      destruct y as [[[[ub_y] | [[err_y] | y]]]]; inversion H; subst; cbn; auto; try (intros CONTRA; contradiction).

    intros YA; auto.
  Qed.

  Instance MonadReturns_ErrOrUB : MonadReturns err_or_ub
    := { MReturns := fun A => ErrOrUBReturns;
         MFails := fun A => ErrOrUBFails;
         MReturns_MFails := fun A => ErrOrUBReturns_ErrOrUBFails;
         MFails_MReturns := fun A => ErrOrUBFails_ErrOrUBReturns;
         MFails_ret := fun A => ErrOrUBFails_ret;
         MReturns_bind := fun A B => ErrOrUBReturns_bind;
         MReturns_bind_inv := fun A B => ErrOrUBReturns_bind_inv;
         MReturns_ret := fun A => ErrOrUBReturns_ret;
         MReturns_ret_inv := fun A => ErrOrUBReturns_ret_inv
       }.

End MonadReturns.

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

Definition UB_to_err_or_ub {A} (ub : UB A) : err_or_ub A
  := ERR_OR_UB (lift ub).

Ltac inv_err_or_ub :=
  match goal with
  | h: {| unERR_OR_UB := {| unEitherT := inl _ |} |} =
       {| unERR_OR_UB := {| unEitherT := inl _ |} |} |- _ => inv h
  | h: {| unERR_OR_UB := {| unEitherT := inr _ |} |} =
       {| unERR_OR_UB := {| unEitherT := inr _ |} |} |- _ => inv h
  | h: {| unERR_OR_UB := {| unEitherT := inr _ |} |} =
       {| unERR_OR_UB := {| unEitherT := inl _ |} |} |- _ => inv h
  | h: {| unERR_OR_UB := {| unEitherT := inl _ |} |} =
       {| unERR_OR_UB := {| unEitherT := inr _ |} |} |- _ => inv h
  end.
