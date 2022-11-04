From ExtLib Require Import
     Structures.Monads.

From ITree Require Import
     ITree
     Eq.Eq.

From Vellvm Require Import
     Utils.Error
     Utils.Raise
     Utils.MonadReturnsLaws
     Utils.MonadEq1Laws
     Utils.MonadExcLaws
     Utils.PropT
     Semantics.LLVMEvents.

Require Import Paco.paco.
Require Import String.

Import Basics.Basics.Monads.
Import MonadNotation.
Open Scope monad_scope.

Section ITreeRaiseError.
  Context {E : Type -> Type}.
  Context `{FAILE: FailureE -< E}.

  Definition ITreeReturns {A} (x : A) (ma : itree E A) := ma ≈ ret x.
  Definition ITreeErrorMFails {A} (t : itree E A) := exists x, t ≈ raise_error x.

  #[global] Instance ITreeErrorMonadReturns : MonadReturns (itree E).
  Proof.
    split with
      (MReturns := @ITreeReturns)
      (MFails := @ITreeErrorMFails).
    - (* MFails_ret *)
      intros A a [x CONTRA].
      pinversion CONTRA.
    - (* MFails_bind_ma *)
      intros A B ma k [x FAIL].
      exists x.
      rewrite FAIL.
      apply (@rbm_raise_bind (itree E) _ _ string (fun T => raise) (@RaiseBindM_Fail E FAILE)).
    - (* MFails_bind_ma *)
      intros A B ma a k RET [x FAIL].
      exists x.
      cbn in *.
      unfold ITreeReturns in *.
      rewrite RET.
      cbn.
      rewrite bind_ret_l.
      auto.
    - (* MFails_bind_k *)
      intros A B ma k [x FAIL].
      unfold ITreeErrorMFails in *.
      unfold ITreeReturns in *.
      (* ma could loop forever.

         ma could raise another event...

         Though this can't be true because FAIL is eutt
         raise_error. Something must fail.
       *)

      (* Need to do induction... *)
      Ltac clean_existT :=
        repeat match goal with
               | H: existT _ _ _ = existT _ _ _ |- _ =>
                   apply inj_pair2 in H
               end.

      (* I know that (x <- ma;; k x ≈ raise_error x).

         This is a itree that is known to terminate with an error.

         This means that either ma ≈ raise_error, as any vis event
         raised by ma must correspond to the error... Or `ma ≈ ret a`
         for some `a`. Tau nodes can be ignored...

         eutt
       *)

      cbn in FAIL.
      unfold raise in FAIL.
      rewrite bind_trigger in FAIL.
      apply eutt_inv_bind_vis in FAIL as [RAISEMA | RETMA].
      + destruct RAISEMA as [k' [MA EUTT]].
        left.
        exists x.
        rewrite MA.
        cbn.
        unfold raise.
        rewrite bind_trigger.
        pstep; red.
        constructor; intros [].
      + destruct RETMA as [r [MA EUTT]].
        right.
        exists r. split; auto.
        exists x.
        rewrite EUTT.
        cbn.
        unfold raise.
        rewrite bind_trigger.
        reflexivity.
    - (* MReturns_bind *)
      intros A B a b ma k RET1 RET2.
      unfold ITreeReturns in *.
      rewrite RET1.
      cbn.
      rewrite bind_ret_l.
      auto.
    - (* MReturns_bind_inv *)
      intros A B t k b EQ.
      unfold ITreeReturns in *.
      right.
      apply eutt_inv_bind_ret in EQ.
      auto.
    - (* MReturns_ret *)
      intros A a ma RET.
      unfold ITreeReturns.
      rewrite RET.
      reflexivity.
    - (* MReturns_ret_inv *)
      intros A x y RET.
      unfold ITreeReturns in *.
      eapply (@eq1_ret_ret _ _ _ (Eq1_ret_inv_itree _)).
      rewrite RET.
      reflexivity.
  Defined.
End ITreeRaiseError.

Section ITreeRaiseOOM.
  Context {E : Type -> Type}.
  Context `{OOM_EVENT: OOME -< E}.

  Definition ITreeOomMFails {A} (t : itree E A) := exists x, t ≈ raise_oom x.

  #[global] Instance ITreeOomMonadReturns : MonadReturns (itree E).
  Proof.
    split with
      (MReturns := @ITreeReturns E)
      (MFails := @ITreeOomMFails).
    - (* MFails_ret *)
      intros A a [x CONTRA].
      pinversion CONTRA.
    - (* MFails_bind_ma *)
      intros A B ma k [x FAIL].
      exists x.
      rewrite FAIL.
      apply (@rbm_raise_bind (itree E) _ _ string (fun T => raiseOOM) (@RaiseBindM_OOM E _)).
    - (* MFails_bind_ma *)
      intros A B ma a k RET [x FAIL].
      exists x.
      cbn in *.
      unfold ITreeReturns in *.
      rewrite RET.
      cbn.
      rewrite bind_ret_l.
      auto.
    - (* MFails_bind_k *)
      intros A B ma k [x FAIL].
      unfold ITreeErrorMFails in *.
      unfold ITreeReturns in *.
      (* ma could loop forever.

         ma could raise another event...

         Though this can't be true because FAIL is eutt
         raise_error. Something must fail.
       *)

      (* Need to do induction... *)
      Ltac clean_existT :=
        repeat match goal with
               | H: existT _ _ _ = existT _ _ _ |- _ =>
                   apply inj_pair2 in H
               end.

      (* I know that (x <- ma;; k x ≈ raise_error x).

         This is a itree that is known to terminate with an error.

         This means that either ma ≈ raise_error, as any vis event
         raised by ma must correspond to the error... Or `ma ≈ ret a`
         for some `a`. Tau nodes can be ignored...

         eutt
       *)

      cbn in FAIL.
      unfold raiseOOM in FAIL.
      rewrite bind_trigger in FAIL.
      apply eutt_inv_bind_vis in FAIL as [RAISEMA | RETMA].
      + destruct RAISEMA as [k' [MA EUTT]].
        left.
        exists x.
        rewrite MA.
        cbn.
        unfold raise_oom, raiseOOM.
        rewrite bind_trigger.
        pstep; red.
        constructor; intros [].
      + destruct RETMA as [r [MA EUTT]].
        right.
        exists r. split; auto.
        exists x.
        rewrite EUTT.
        cbn.
        unfold raise_oom, raiseOOM.
        rewrite bind_trigger.
        reflexivity.
    - (* MReturns_bind *)
      intros A B a b ma k RET1 RET2.
      unfold ITreeReturns in *.
      rewrite RET1.
      cbn.
      rewrite bind_ret_l.
      auto.
    - (* MReturns_bind_inv *)
      intros A B t k b EQ.
      unfold ITreeReturns in *.
      right.
      apply eutt_inv_bind_ret in EQ.
      auto.
    - (* MReturns_ret *)
      intros A a ma RET.
      unfold ITreeReturns.
      rewrite RET.
      reflexivity.
    - (* MReturns_ret_inv *)
      intros A x y RET.
      unfold ITreeReturns in *.
      eapply (@eq1_ret_ret _ _ _ (Eq1_ret_inv_itree _)).
      rewrite RET.
      reflexivity.
  Defined.
End ITreeRaiseOOM.

Section ITreeRaiseUB.
  Context {E : Type -> Type}.
  Context `{UB_EVENT: UBE -< E}.

  Definition ITreeUBMFails {A} (t : itree E A) := exists x, t ≈ raise_ub x.

  #[global] Instance ITreeUBMonadReturns : MonadReturns (itree E).
  Proof.
    split with
      (MReturns := @ITreeReturns E)
      (MFails := @ITreeUBMFails).
    - (* MFails_ret *)
      intros A a [x CONTRA].
      pinversion CONTRA.
    - (* MFails_bind_ma *)
      intros A B ma k [x FAIL].
      exists x.
      rewrite FAIL.
      apply (@rbm_raise_bind (itree E) _ _ string (fun T => raiseUB) (@RaiseBindM_UB E _)).
    - (* MFails_bind_ma *)
      intros A B ma a k RET [x FAIL].
      exists x.
      cbn in *.
      unfold ITreeReturns in *.
      rewrite RET.
      cbn.
      rewrite bind_ret_l.
      auto.
    - (* MFails_bind_k *)
      intros A B ma k [x FAIL].
      unfold ITreeErrorMFails in *.
      unfold ITreeReturns in *.
      (* ma could loop forever.

         ma could raise another event...

         Though this can't be true because FAIL is eutt
         raise_error. Something must fail.
       *)

      (* Need to do induction... *)
      Ltac clean_existT :=
        repeat match goal with
               | H: existT _ _ _ = existT _ _ _ |- _ =>
                   apply inj_pair2 in H
               end.

      (* I know that (x <- ma;; k x ≈ raise_error x).

         This is a itree that is known to terminate with an error.

         This means that either ma ≈ raise_error, as any vis event
         raised by ma must correspond to the error... Or `ma ≈ ret a`
         for some `a`. Tau nodes can be ignored...

         eutt
       *)

      cbn in FAIL.
      unfold raiseUB in FAIL.
      rewrite bind_trigger in FAIL.
      apply eutt_inv_bind_vis in FAIL as [RAISEMA | RETMA].
      + destruct RAISEMA as [k' [MA EUTT]].
        left.
        exists x.
        rewrite MA.
        cbn.
        unfold raise_oom, raiseUB.
        rewrite bind_trigger.
        pstep; red.
        constructor; intros [].
      + destruct RETMA as [r [MA EUTT]].
        right.
        exists r. split; auto.
        exists x.
        rewrite EUTT.
        cbn.
        unfold raise_oom, raiseUB.
        rewrite bind_trigger.
        reflexivity.
    - (* MReturns_bind *)
      intros A B a b ma k RET1 RET2.
      unfold ITreeReturns in *.
      rewrite RET1.
      cbn.
      rewrite bind_ret_l.
      auto.
    - (* MReturns_bind_inv *)
      intros A B t k b EQ.
      unfold ITreeReturns in *.
      right.
      apply eutt_inv_bind_ret in EQ.
      auto.
    - (* MReturns_ret *)
      intros A a ma RET.
      unfold ITreeReturns.
      rewrite RET.
      reflexivity.
    - (* MReturns_ret_inv *)
      intros A x y RET.
      unfold ITreeReturns in *.
      eapply (@eq1_ret_ret _ _ _ (Eq1_ret_inv_itree _)).
      rewrite RET.
      reflexivity.
  Defined.
End ITreeRaiseUB.
