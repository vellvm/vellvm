Unset Universe Checking.
(* begin hide *)
From Stdlib Require Import
     Morphisms
     String.

From ExtLib Require Import
  Structures.Monads
  EitherMonad.

From Vellvm Require Import
     Utils.Util
     Utils.Error
     Utils.Tactics
     Utils.InterpEither
     Utils.CTreeUtils
     Utils.Monads
     Semantics.LLVMEvents
     Semantics.Memory.Sizeof.

From CTree Require Import
  CTree
  Fold
  FoldCTree
  FoldStateT
  Eq
  SBisim.

Require Import Ceres.Ceres.

Set Implicit Arguments.
Set Contextual Implicit.

Import MonadNotation.
Import ITree.Basics.Basics.Monads.
Open Scope string_scope.
Open Scope monad.

Import CategoryOps.
(* end hide *)


(** * LLVMExcE handler
  Interpretation of the [LLVMExcE] events into the either monad.
*)

Section Exceptions.
  Context {EXC : Type}.

  Definition handle_LLVMExcE {m} `{HM: Monad m} : LLVMExcE EXC ~> eitherT EXC m :=
    fun X e =>  
      match e with
      | LLVMExc x => mkEitherT (ret (inl x))
      end.

  Section LLVMExcHandler.
    Variable (E F G BR : Type -> Type).
    Context `{FAIL: FailureE -< G}.
    Notation Effin := (E +' F +' LLVMExcE EXC +' G).
    Notation Effout := (E +' F +' LLVMExcE EXC +' G).

    Definition E_trigger : forall R, E R -> eitherT EXC (ctree Effout BR) R :=
      fun R e => mkEitherT (r <- trigger e ;; ret (inr r)).

    Definition F_trigger : forall R, F R -> eitherT EXC (ctree Effout BR) R :=
      fun R e => mkEitherT (r <- trigger e ;; ret (inr r)).

    Definition G_trigger : forall R, G R -> eitherT EXC (ctree Effout BR) R :=
      fun R e => mkEitherT (r <- trigger e ;; ret (inr r)).

    Definition catch_llvm_exc_h : IFun Effin (fun R : Type => eitherT EXC (ctree Effout BR) R)
      := (case_ E_trigger (case_ F_trigger (case_ (@handle_LLVMExcE (ctree Effout BR) _) G_trigger))).

    Definition catch_llvm_exc : ctree Effin BR ~> eitherT EXC (ctree Effout BR)
      := interp_either catch_llvm_exc_h.

    Section Structural_Lemmas.
      Lemma catch_llvm_exc_bind :
        forall (R S : Type) (t : ctree Effin BR R) (k : R -> ctree Effin BR S),
          Monad.eq1 (catch_llvm_exc (CTree.bind t k))
            (r <- catch_llvm_exc t;; catch_llvm_exc (k r)).
      Proof using E EXC F G FAIL.
        intros.
        unfold catch_llvm_exc.
        setoid_rewrite interp_either_bind.
        reflexivity.
      Qed.

      Lemma catch_llvm_exc_ret :
        forall (R : Type) (x: R),
          Monad.eq1 (catch_llvm_exc (Ret x: ctree Effin BR R)) (ret x).
      Proof using.
        intros.
        unfold catch_llvm_exc.
        apply interp_either_ret.
      Qed.

      Lemma catch_llvm_exc_Guard :
        forall {R} (t: ctree Effin BR R),
          Monad.eq1 (catch_llvm_exc (Guard t)) (catch_llvm_exc t).
      Proof using.
        intros.
        unfold catch_llvm_exc.
        apply interp_either_guard.
      Qed.

      Lemma catch_llvm_exc_vis:
        forall S X (kk : X -> ctree Effout BR S) (e : Effin X),
          @Monad.eq1 (eitherT EXC (ctree Effout BR)) _ _ (@catch_llvm_exc S (Vis e kk)) (@bind (eitherT EXC (ctree Effout BR)) _ _ _ (@catch_llvm_exc_h X e) (fun sx => @catch_llvm_exc S (kk sx))).
      Proof using.
        intros.
        unfold catch_llvm_exc.
        setoid_rewrite interp_either_vis.
        reflexivity.
      Qed.

      Lemma catch_llvm_exc_trigger:
        forall X (e : Effin X),
          @Monad.eq1 _ EqM_eitherT _  (catch_llvm_exc (CTree.trigger e)) (catch_llvm_exc_h e).
      Proof using.
        intros.
        unfold catch_llvm_exc.
        rewrite interp_either_trigger.
        reflexivity.
      Qed.

      (* Lemma catch_llvm_exc_bind_trigger_eqit: *)
      (*   forall X R *)
      (*     (kk : X -> ctree Effin BR R) *)
      (*     (e : Effin X), *)
      (*     eq_either_itree (catch_llvm_exc (CTree.bind (trigger e) kk)) (@bind (eitherT EXC (ctree Effout BR)) _ _ _ (catch_llvm_exc_h e) (fun x => catch_llvm_exc (Guard (kk x)))). *)
      (* Proof using. *)
      (*   intros. *)
      (*   unfold catch_llvm_exc. *)
      (*   rewrite bind_trigger. *)
      (*   setoid_rewrite interp_either_vis'. *)
      (*   reflexivity. *)
      (* Qed. *)

      (* Lemma catch_llvm_exc_bind_trigger: *)
      (*   forall X R *)
      (*     (kk : X -> ctree Effin BR R) *)
      (*     (e : Effin X), *)
      (*     Monad.eq1 (catch_llvm_exc (CTree.bind (trigger e) kk)) (@bind (eitherT EXC (ctree Effout BR)) _ _ _ (catch_llvm_exc_h e) (fun x => catch_llvm_exc (kk x))). *)
      (* Proof using. *)
      (*   intros. *)
      (*   rewrite catch_llvm_exc_bind_trigger_eqit. *)
      (*   setoid_rewrite catch_llvm_exc_Guard. *)
      (*   reflexivity. *)
      (* Qed. *)

      #[global] Instance eutt_catch_llvm_exc {R} :
        Proper (sbisim eq  ==> Monad.eq1) (@catch_llvm_exc R).
      Proof using.
        repeat intro.
        unfold catch_llvm_exc.
        apply eq1_interp_either.
        apply H.
      Qed.

    End Structural_Lemmas.

  End LLVMExcHandler.

End Exceptions.
