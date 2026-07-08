(* begin hide *)
From Stdlib Require Import
  Morphisms
  String.

From ExtLib Require Import
  Structures.Monads
  EitherMonad.

From ITree Require Import
  ITree
  Eq.Eqit
  InterpFacts.

From Vellvm Require Import
  Utils
  LLVMEvents.

Import ITree.Basics.Basics.Monads.
(* end hide *)


(** * LLVMExcE handler
  Interpretation of the [LLVMExcE] events into the either monad.
*)

Section Exceptions.
  Context {Pa : Param}.

  Definition handle_LLVMExcE {E} : LLVMExcE ~> eitherT exc (itree E) :=
    fun X e =>  
      match e with
      | LLVMExc x => mkEitherT (ret (inl x))
      end.

  Section LLVMExcHandler.
    Variable (E F G : Type -> Type).
    Context `{FAIL: FailureE -< G}.
    Notation Effin := (E +' F +' LLVMExcE EXC +' G).
    Notation Effout := (E +' F +' LLVMExcE EXC +' G).

    Definition E_trigger : forall R, E R -> eitherT EXC (itree Effout) R :=
      fun R e => mkEitherT (r <- trigger e ;; ret (inr r)).

    Definition F_trigger : forall R, F R -> eitherT EXC (itree Effout) R :=
      fun R e => mkEitherT (r <- trigger e ;; ret (inr r)).

    Definition G_trigger : forall R, G R -> eitherT EXC (itree Effout) R :=
      fun R e => mkEitherT (r <- trigger e ;; ret (inr r)).

    Definition catch_llvm_exc_h : IFun Effin (fun R : Type => eitherT EXC (itree Effout) R)
      := (case_ E_trigger (case_ F_trigger (case_ (@handle_LLVMExcE (itree Effout) _) G_trigger))).

    Definition catch_llvm_exc : itree Effin ~> eitherT EXC (itree Effout)
      := interp_either catch_llvm_exc_h.

    Section Structural_Lemmas.
      Lemma catch_llvm_exc_bind :
        forall (R S : Type) (t : itree Effin R) (k : R -> itree Effin S),
          Monad.eq1 (catch_llvm_exc (ITree.bind t k))
            (r <- catch_llvm_exc t;; catch_llvm_exc (k r)).
      Proof using E EXC F G FAIL.
        intros.
        unfold catch_llvm_exc.
        setoid_rewrite interp_either_bind.
        reflexivity.
      Qed.

      Lemma catch_llvm_exc_ret :
        forall (R : Type) (x: R),
          Monad.eq1 (catch_llvm_exc (Ret x: itree Effin R)) (ret x).
      Proof using.
        intros.
        unfold catch_llvm_exc.
        apply interp_either_ret.
      Qed.

      Lemma catch_llvm_exc_Tau :
        forall {R} (t: itree Effin R),
          Monad.eq1 (catch_llvm_exc (Tau t)) (catch_llvm_exc t).
      Proof using.
        intros.
        unfold catch_llvm_exc.
        apply interp_either_tau.
      Qed.

      Lemma catch_llvm_exc_vis:
        forall S X (kk : X -> itree Effout S) (e : Effin X),
          @Monad.eq1 (eitherT EXC (itree Effout)) _ _ (@catch_llvm_exc S (Vis e kk)) (@bind (eitherT EXC (itree Effout)) _ _ _ (@catch_llvm_exc_h X e) (fun sx => @catch_llvm_exc S (kk sx))).
      Proof using.
        intros.
        unfold catch_llvm_exc.
        setoid_rewrite interp_either_vis.
        reflexivity.
      Qed.

      Lemma catch_llvm_exc_trigger:
        forall X (e : Effin X),
          Monad.eq1 (catch_llvm_exc (ITree.trigger e)) (catch_llvm_exc_h e).
      Proof using.
        intros.
        unfold catch_llvm_exc.
        rewrite interp_either_trigger.
        reflexivity.
      Qed.

      Lemma catch_llvm_exc_bind_trigger_eqit:
        forall X R
          (kk : X -> itree Effin R)
          (e : Effin X),
          eq_either_itree (catch_llvm_exc (ITree.bind (trigger e) kk)) (@bind (eitherT EXC (itree Effout)) _ _ _ (catch_llvm_exc_h e) (fun x => catch_llvm_exc (Tau (kk x)))).
      Proof using.
        intros.
        unfold catch_llvm_exc.
        rewrite bind_trigger.
        setoid_rewrite interp_either_vis'.
        reflexivity.
      Qed.

      Lemma catch_llvm_exc_bind_trigger:
        forall X R
          (kk : X -> itree Effin R)
          (e : Effin X),
          Monad.eq1 (catch_llvm_exc (ITree.bind (trigger e) kk)) (@bind (eitherT EXC (itree Effout)) _ _ _ (catch_llvm_exc_h e) (fun x => catch_llvm_exc (kk x))).
      Proof using.
        intros.
        rewrite catch_llvm_exc_bind_trigger_eqit.
        setoid_rewrite catch_llvm_exc_Tau.
        reflexivity.
      Qed.

      #[global] Instance eutt_catch_llvm_exc {R} :
        Proper (eutt eq ==> Monad.eq1) (@catch_llvm_exc R).
      Proof using.
        repeat intro.
        unfold catch_llvm_exc.
        apply eq1_interp_either.
        apply H.
      Qed.

    End Structural_Lemmas.

  End LLVMExcHandler.

End Exceptions.
