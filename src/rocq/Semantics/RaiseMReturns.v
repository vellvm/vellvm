From ExtLib Require Import
     Structures.Monads.

     Unset Universe Checking.
From Vellvm Require Import
     Utils.Error
     Utils.Raise
     Utils.MonadReturnsLaws
     Utils.MonadEq1Laws
     Utils.MonadExcLaws
     Utils.PropT
     Semantics.LLVMEvents.

From CTree Require Import
    CTree
    CTreeDefinitions
    Eq

    .
Require Import Paco.paco.
From Stdlib Require Import String.

Import Basics.Basics.Monads.
Import MonadNotation.
Open Scope monad_scope.

Section CTreeRaiseError.
  Context {E : Type -> Type}.
  Context {BR : Type -> Type}.
  Context `{FAILE: FailureE -< E}.

  Definition CTreeReturns {A} (x : A) (ma : ctree E BR A) := ma ~ (ret x: ctree E BR A).
  Definition CTreeErrorMFails {A} (t : ctree E BR A) := exists x, t ~ (raise_error x: ctree E BR A).

  #[global] Instance CTreeErrorMonadReturns : MonadReturns (ctree E BR).
  Proof using E FAILE.
    split with
      (MReturns := @CTreeReturns)
      (MFails := @CTreeErrorMFails).
    - (* MFails_ret *)
      intros A a [x CONTRA].
      symmetry in CONTRA.
      apply raise_ret_inv_ctree in CONTRA.
      auto.
    - (* MFails_bind_ma *)
      intros A B ma k [x FAIL].
      exists x.
      rewrite FAIL.
      apply (@rbm_raise_bind (ctree E BR) _ _ string (fun T => raise) (@RaiseBindM_Fail E _ FAILE)).
    - (* MFails_bind_ma *)
      intros A B ma a k RET [x FAIL].
      exists x.
      cbn in *.
      unfold CTreeReturns in *.
      rewrite RET.
      cbn.
      rewrite bind_ret_l.
      auto.
    - (* MFails_bind_k *)
      intros A B ma k [x FAIL].
      unfold CTreeErrorMFails in *.
      unfold CTreeReturns in *.
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
      admit.
      (* apply sbisim_inv_bind_vis in FAIL as [RAISEMA | RETMA].
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
      unfold CTreeReturns in *.
      rewrite RET1.
      cbn.
      rewrite bind_ret_l.
      auto.
    - (* MReturns_bind_inv *)
      intros A B t k b EQ.
      unfold CTreeReturns in *.
      right.
      apply eutt_inv_bind_ret in EQ.
      auto.
    - (* MReturns_ret *)
      intros A a ma RET.
      unfold CTreeReturns.
      rewrite RET.
      reflexivity.
    - (* MReturns_ret_inv *)
      intros A x y RET.
      unfold CTreeReturns in *.
      eapply (@eq1_ret_ret _ _ _ (Eq1_ret_inv_itree _)).
      rewrite RET.
      reflexivity. *)
Admitted.
End CTreeRaiseError.
