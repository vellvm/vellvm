From Stdlib Require Import String.

From Vellvm Require Import
     Utils.Util
     Utils.Error
     Utils.Tactics
     Utils.MonadReturnsLaws.

From ITree Require Import Basics.Monad.

Import MonadNotation.
Open Scope monad_scope.

Definition RefineProp (X : Type) : Type := err_ub_oom X -> Prop.

Definition bind_RefineProp {A B : Type} (pa : RefineProp A) (k : A -> RefineProp B) : RefineProp B
  := (fun mb => exists (ma : err_ub_oom A) (k' : A -> err_ub_oom B),
          pa ma /\
            Monad.eq1 (Monad.bind ma k') mb /\
            (MFails ma \/ forall a, MReturns a ma -> k a (k' a))).

#[global] Instance Monad_RefineProp : Monad RefineProp :=
  {|
    ret := fun _ x y => Monad.eq1 (ret x) y;
    bind := @bind_RefineProp
  |}.

Import IdentityMonad.
#[global] Instance EQM_RefineProp : Eq1 RefineProp.
Proof.
  unfold Eq1.
  intros A X Y.
  refine (forall ma, Y ma -> X ma).
Defined.

Lemma RefineProp_bind_ret_l :
  forall (A B : Type) (f : A -> RefineProp B) (x : A),
    x <- ret x;; f x ≈ f x.
Proof.
  intros A B f x.
  unfold eq1, EQM_RefineProp; cbn.
  intros ma H.
  unfold bind_RefineProp.

  exists (ret x). (* (mkEitherT (mkEitherT (mkEitherT (mkIdent (inr (inr (inr x))))))). *)
  exists (fun _ => ma).
  split; cbn; auto. reflexivity.
  cbn.
  split.
  + destruct ma as [[[[[[[oom_ma] | [[ub_ma] | [[err_ma] | a]]]]]]]] eqn:Hma; 
    subst; cbn; reflexivity. 
  + right; intros a XA; subst; auto.
Qed.

Lemma RefineProp_bind_ret_r :
  forall (A : Type) (x : RefineProp A), y <- x;; ret y ≈ x.
Proof.
  intros A x.
  unfold eq1, EQM_RefineProp; cbn.
  intros ma H.
  unfold bind_RefineProp.

  exists ma.
  exists ret.

  split; eauto.
  split.
  + apply bind_ret_r.
  + right; reflexivity.
Qed.

Lemma RefineProp_bind_bind :
  forall (A B C : Type) (ma : RefineProp A) (fab : A -> RefineProp B) (fbc : B -> RefineProp C),
    b <- (a <- ma;; fab a);; fbc b ≈ a <- ma;; b <- fab a;; fbc b.
Proof.
  intros A B C ma fab fbc.

  unfold RefineProp in *.
  unfold eq1, EQM_RefineProp; cbn.
  unfold bind_RefineProp.

  intros ec H.
  destruct H as (ea & k' & paea & ea_eq_ec & REST).

  destruct_err_ub_oom ea; subst.

  { (* oom *)
    exists (raise_oom oom_msg).
    exists (fun b => ec).
    split.

    { eexists.
      exists (fun a => raise_oom oom_msg).
      split.
      apply paea.
      split; eauto.
      reflexivity.
      right. intros. inversion H.
    }

    split; intros; eauto; try contradiction.
    right; intros. inversion H.
  }

  { (* The 'a' action raises ub *)
    exists (raise_ub err_msg).
    exists (fun b => ec).
    split.

    { eexists.
      exists (fun a => raise_ub err_msg).

      split.
      apply paea.
      split; auto.
      reflexivity.
      left; reflexivity.
    }

    split; auto. left; reflexivity.
  }

  { (* The 'a' action raises a failure *)
    exists (raise_error err_msg).
    exists (fun b => ec).
    split.

    { eexists.
      exists (fun a => raise_error err_msg).

      split.
      apply paea.
      split; auto. reflexivity. left. reflexivity.
    }

    split; auto. left; reflexivity.
  }

  {
    rewrite bind_ret_l in ea_eq_ec.
    (* The 'a' action actually returns a value *)
    destruct REST as [CONTRA | REST]; [contradiction|].
    specialize (REST a).
    forward REST; [reflexivity|].
    destruct REST as (mb & kb & fmb & eqkb & RETS).

    exists mb.
    exists kb.

    split.
    { exists (ret a).
      exists (fun _ => mb).

      split; subst; auto.
      split.
      rewrite bind_ret_l. reflexivity.

      right.
      intros a' RETSa.
      cbn in RETSa; subst; auto.
    }

    destruct_err_ub_oom mb; subst.
    - split. rewrite <- ea_eq_ec. rewrite <- eqkb. reflexivity.
      right. intros. inversion H.
    - split. rewrite <- ea_eq_ec. rewrite <- eqkb. reflexivity.
      left. reflexivity.
    - split. rewrite <- ea_eq_ec. rewrite <- eqkb. reflexivity.
      left. reflexivity.
    - split. rewrite <- ea_eq_ec. rewrite <- eqkb. reflexivity.
      right. intros.  inversion H. subst. destruct RETS. inversion H0. eapply H0. reflexivity.
  }
Qed.

Require Import Morphisms.
#[global] Instance RefineProp_Proper_bind {A B : Type} :
  @Proper (RefineProp A -> (A -> RefineProp B) -> RefineProp B)
          (@eq1 RefineProp EQM_RefineProp A ==>
                @pointwise_relation A (RefineProp B) (@eq1 RefineProp EQM_RefineProp B) ==>
                @eq1 RefineProp EQM_RefineProp B)
          (@bind RefineProp Monad_RefineProp A B).
Proof.
  unfold Proper, respectful.
  intros A1 A2 H pa1 pa2 pw EB.

  unfold RefineProp in *.
  unfold eq1, EQM_RefineProp; cbn.
  unfold bind_RefineProp.

  intros Bind2.

  destruct Bind2 as (ma & k' & pa1ma & meq & REST).

  exists ma.
  exists k'.
  split; auto.
  split; auto.

  destruct REST as [FAILS|REST]; auto.

  right.
  intros a Rets.
  specialize (REST a Rets).

  unfold pointwise_relation in pw.
  specialize (pw a).

  unfold eq1, EQM_RefineProp in pw.
  auto.
Qed.

#[global] Instance MonadLawsE_RefineProp : MonadLawsE RefineProp.
Proof.
  split.
  - apply RefineProp_bind_ret_l.
  - apply RefineProp_bind_ret_r.
  - apply RefineProp_bind_bind.
  - apply @RefineProp_Proper_bind.
Defined.

