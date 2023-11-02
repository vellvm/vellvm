From Coq Require Import String.

From Vellvm Require Import
     Utils.Util
     Utils.Error
     Utils.Tactics
     Utils.MonadReturnsLaws.

From ITree Require Import Basics.Monad.

Import MonadNotation.
Open Scope monad_scope.

Definition ErrUbOomProp (X : Type) : Type := err_ub_oom X -> Prop.

Definition bind_ErrUbOomProp {A B : Type} (pa : ErrUbOomProp A) (k : A -> ErrUbOomProp B) : ErrUbOomProp B
  := (fun mb => exists (ma : err_ub_oom A) (k' : A -> err_ub_oom B),
          pa ma /\
            (Monad.bind ma k') = mb /\
            (MFails ma \/ forall a, MReturns a ma -> k a (k' a))).

#[global] Instance Monad_ErrUbOomProp : Monad ErrUbOomProp :=
  {|
    ret := fun _ x y => (ret x) = y;
    bind := @bind_ErrUbOomProp
  |}.

Import IdentityMonad.
#[global] Instance EQM_ErrUbOomProp : Eq1 ErrUbOomProp.
Proof.
  unfold Eq1.
  intros A X Y.
  refine (forall ma, Y ma <-> X ma).
Defined.

Ltac destruct_err_ub_oom x :=
  destruct x as [[[[[[[?oom_x] | [[?ub_x] | [[?err_x] | ?x]]]]]]]] eqn:?Hx.

Lemma ErrUbOomProp_bind_ret_l :
  forall (A B : Type) (f : A -> ErrUbOomProp B) (x : A),
    x <- ret x;; f x ≈ f x.
Proof.
  intros A B f x.
  unfold eq1, EQM_ErrUbOomProp; cbn.
  intros ma.
  split.
  - intros H.
    unfold bind_ErrUbOomProp.
    exists (ret x).
    exists (fun _ => ma).
    split; cbn; eauto.
    cbn.
    split.
    + destruct ma as [[[[[[[oom_ma] | [[ub_ma] | [[err_ma] | a]]]]]]]] eqn:Hma;
        cbn; intuition; inversion H0; subst; auto.
    + right; intros a XA; subst; auto.
  - intros H.
    unfold bind_ErrUbOomProp in H.
    destruct H as (?&?&?&?&?).
    subst.
    destruct H1 as [[] | H1].

    specialize (H1 x).
    forward H1; cbn; auto.

    remember (x1 x) as x1x.
    destruct_err_ub_oom x1x; subst; cbn in *; auto.
Qed.

Lemma ErrUbOomProp_bind_ret_r :
  forall (A : Type) (x : ErrUbOomProp A), y <- x;; ret y ≈ x.
Proof.
  intros A x ma.
  unfold eq1, EQM_ErrUbOomProp; cbn.
  split; intros H.
  - unfold bind_ErrUbOomProp.
    exists ma.
    exists ret.
    split; eauto.
    split.
    + cbn.
      destruct_err_ub_oom ma; subst; cbn; auto.
    + right.
      intros a H0.
      reflexivity.
  - unfold bind_ErrUbOomProp in H.
    destruct H as (?&?&?&?&?).
    subst.

    destruct_err_ub_oom x0; subst; cbn in *; auto.
    destruct H1 as [[] | H1].

    specialize (H1 x2 eq_refl).
    rewrite <- H1.
    cbn.
    auto.
Qed.

Lemma ErrUbOomProp_bind_bind :
  forall (A B C : Type) (ma : ErrUbOomProp A) (fab : A -> ErrUbOomProp B) (fbc : B -> ErrUbOomProp C),
    b <- (a <- ma;; fab a);; fbc b ≈ a <- ma;; b <- fab a;; fbc b.
Proof.
  intros A B C ma fab fbc.

  unfold ErrUbOomProp in *.
  unfold eq1, EQM_ErrUbOomProp; cbn.
  unfold bind_ErrUbOomProp.

  intros ec.
  split; intros H.
  { destruct H as (ea & k' & paea & ea_eq_ec & REST).
    destruct_err_ub_oom ea; subst.
    { (* oom *)
      clear REST.
      exists (raise_oom oom_x).
      exists (fun b => raise_oom oom_x).
      split.

      { eexists.
        exists (fun a => raise_oom oom_x).

        split.
        apply paea.
        cbn.
        split; eauto.
      }

      cbn.
      split; intros; eauto; try contradiction.
    }

    { (* The 'a' action raises ub *)
      exists (raise_ub ub_x).
      exists (fun b => raise_ub ub_x).
      split.

      { eexists.
        exists (fun a => raise_ub ub_x).

        split.
        apply paea.
        cbn.
        split; auto.
      }

      split; auto.
      left; cbn; auto.
    }

    { (* The 'a' action raises a failure *)
      exists (raise_error err_x).
      exists (fun b => raise_error err_x).
      split.

      { eexists.
        exists (fun a => raise_error err_x).

        split.
        apply paea.
        cbn.
        split; auto.
      }

      split; auto.
      left; cbn; auto.
    }

    { (* The 'a' action actually returns a value *)
      destruct REST as [CONTRA | REST]; [contradiction|].
      specialize (REST ea0).
      forward REST; [reflexivity|].
      destruct REST as (mb & kb & fmb & eqkb & RETS).

      exists mb.
      exists kb.

      split.
      { exists (ret ea0).
        exists (fun _ => mb).

        split; subst; auto.
        split.
        destruct mb as [[[[[[[oom_mb] | [[ub_mb] | [[err_mb] | b]]]]]]]] eqn:Hmb; cbn; split; auto.

        right.
        intros a' RETSa.
        cbn in RETSa; subst; auto.
      }

      cbn in eqkb.

      split.
      { destruct mb as [[[[[[[oom_mb] | [[ub_mb] | [[err_mb] | b]]]]]]]] eqn:Hmb; cbn in *; subst; rewrite <- eqkb; cbn; auto.
      }

      auto.
    }
  }

  { destruct H as (?&?&?&?&?).
    destruct H as (?&?&?&?&?).
    destruct_err_ub_oom x1; subst.

    { (* oom *)
      clear H1 H3.
      exists (raise_oom oom_x).
      exists (fun a => b <- x2 a;; x0 b).
      split; eauto.
      split; eauto.
      left; cbn; auto.
    }

    { (* The 'a' action raises ub *)
      exists (raise_ub ub_x).
      exists (fun b => raise_ub ub_x).
      split; eauto.
      split; eauto.
      left; cbn; eauto.
    }

    { (* The 'a' action raises a failure *)
      exists (raise_error err_x).
      exists (fun b => raise_error err_x).
      split; eauto.
      split; eauto.
      left; cbn; eauto.
    }

    { (* The 'a' action actually returns a value *)
      destruct H3 as [[] | REST].
      specialize (REST x3).
      forward REST; [reflexivity|].

      exists (ret x3).
      exists (fun a => b <- x2 a;; x0 b).
      split; eauto.
      split.
      { cbn.
        remember (x2 x3) as x2x3.
        destruct_err_ub_oom x2x3; subst; cbn; auto.
      }

      right.
      intros a H0.
      cbn in H0; subst.
      exists (x2 a).
      exists x0.
      split; eauto.
      split; eauto.

      cbn in *.
      remember (x2 a) as x2a.
      destruct_err_ub_oom x2a; cbn in *; subst; auto.
    }
  }
Qed.

Require Import Morphisms.
#[global] Instance ErrUbOomProp_Proper_bind {A B : Type} :
  @Proper (ErrUbOomProp A -> (A -> ErrUbOomProp B) -> ErrUbOomProp B)
          (@eq1 ErrUbOomProp EQM_ErrUbOomProp A ==>
                @pointwise_relation A (ErrUbOomProp B) (@eq1 ErrUbOomProp EQM_ErrUbOomProp B) ==>
                @eq1 ErrUbOomProp EQM_ErrUbOomProp B)
          (@bind ErrUbOomProp Monad_ErrUbOomProp A B).
Proof.
  unfold Proper, respectful.
  intros A1 A2 H pa1 pa2 pw EB.

  unfold ErrUbOomProp in *.
  unfold eq1, EQM_ErrUbOomProp; cbn.
  unfold bind_ErrUbOomProp.

  split; intros Bind2.
  - destruct Bind2 as (ma & k' & pa1ma & meq & REST).

    exists ma.
    exists k'.
    split; [apply H; auto|].
    split; auto.

    destruct REST as [FAILS|REST]; auto.

    right.
    intros a Rets.
    specialize (REST a Rets).

    unfold pointwise_relation in pw.
    specialize (pw a).

    unfold eq1, EQM_ErrUbOomProp in pw.
    apply pw. auto.
  - destruct Bind2 as (ma & k' & pa1ma & meq & REST).

    exists ma.
    exists k'.
    split; [apply H; auto|].
    split; auto.

    destruct REST as [FAILS|REST]; auto.

    right.
    intros a Rets.
    specialize (REST a Rets).

    unfold pointwise_relation in pw.
    specialize (pw a).

    unfold eq1, EQM_ErrUbOomProp in pw.
    apply pw. auto.
Qed.

#[global] Instance MonadLawsE_ErrUbOomProp : MonadLawsE ErrUbOomProp.
Proof.
  split.
  - apply ErrUbOomProp_bind_ret_l.
  - apply ErrUbOomProp_bind_ret_r.
  - apply ErrUbOomProp_bind_bind.
  - apply @ErrUbOomProp_Proper_bind.
Defined.
