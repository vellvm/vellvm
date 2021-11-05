From Coq Require Import ZArith String.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Structures.MonadExc
     Data.Monads.EitherMonad
     Data.Monads.StateMonad
     Data.Monads.IdentityMonad.

From Vellvm Require Import
     Utils.Error
     Utils.UBAndErrors
     Semantics.MemoryAddress
     Semantics.DynamicValues
     Semantics.LLVMEvents
     Semantics.Memory.FiniteProvenance
     Semantics.Memory.Sizeof
     Utils.StateMonads
     Utils.Monads
     Utils.MonadExcLaws.

From ITree Require Import
     ITree
     Basics.Basics
     Events.Exception
     Eq.Eq
     Events.StateFacts
     Events.State.

Import Morphisms.

Import Basics.Basics.Monads.

Import MonadNotation.

(* TODO: Provenance is an issue... *)
Module ERRSID (Addr:ADDRESS) (IP:INTPTR) (SIZEOF:Sizeof) (PROV:PROVENANCE(Addr)).
  Import PROV.

  (* Need failure, UB, state for store_ids, and state for provenances *)
  Definition ErrSID_T M := eitherT ERR_MESSAGE (eitherT UB_MESSAGE (eitherT OOM_MESSAGE (stateT store_id (stateT Provenance M)))).
  Definition ErrSID := ErrSID_T ident.

  (* I can make this work using ltac, but  for some reason I can't write the definition directly... *)
  #[global] Instance ErrSID_T_MT {M : Type -> Type} `{HM: Monad M} : MonadT (ErrSID_T M) M.
  Proof.
    constructor.
    refine (fun T mt => mkEitherT (mkEitherT (mkEitherT (fun sid prov => _)))).
    refine (fmap (fun v => (prov, (sid, inr (inr (inr v))))) mt : M (Provenance * (store_id * (OOM_MESSAGE + UB (ERR T))))%type).
  Defined.

  #[global] Instance RAISE_UB_ErrSID_T {M : Type -> Type} `{HM :  Monad M} : RAISE_UB (ErrSID_T M) :=
    { raise_ub := fun A e => lift (raise_ub e);
    }.

  #[global] Instance RAISE_ERROR_ErrSID_T {M : Type -> Type} `{HM :  Monad M} : RAISE_ERROR (ErrSID_T M) :=
    { raise_error := fun A e => raise_error e;
    }.

  #[global] Instance RAISE_OOM_ErrSID_T {M : Type -> Type} `{HM :  Monad M} : RAISE_OOM (ErrSID_T M) :=
    { raise_oom := fun A e => lift (lift (raise_oom e));
    }.

  Definition evalErrSID_T {A} {M} `{Monad M} (m : ErrSID_T M A) (sid : store_id) (prov : Provenance) : M (OOM_MESSAGE + UB (ERR A))%type
    := evalStateT (evalStateT (unEitherT (unEitherT (unEitherT m))) sid) prov.

  Definition evalErrSID {A} (m : ErrSID A) (sid : store_id) (prov : Provenance) : OOM_MESSAGE + UB (ERR A)
    := unIdent (evalErrSID_T m sid prov).

  Definition runErrSID_T {A} {M} `{Monad M} (m : ErrSID_T M A) (sid : store_id) (prov : Provenance) : M ((OOM_MESSAGE + UB (ERR A)) * store_id * Provenance)%type
    := runStateT (runStateT (unEitherT (unEitherT (unEitherT m))) sid) prov.

  Definition runErrSID {A} (m : ErrSID A) (sid : store_id) (prov : Provenance) : (OOM_MESSAGE + UB (ERR A)) * store_id * Provenance%type
    := unIdent (runErrSID_T m sid prov).

  Definition ErrSID_evals_to {A} (e : ErrSID A) sid pr (x : A) : Prop
    := evalErrSID e sid pr = inr (inr (inr x)).

  Definition ErrSID_runs_to {A} (e : ErrSID A) sid pr (x : A) sid' pr': Prop
    := runErrSID e sid pr = (inr (inr (inr x)), sid', pr').

  Definition fresh_sid : ErrSID store_id
    := lift (lift (modify N.succ)).

  Definition fresh_provenance : ErrSID Provenance
    := lift (lift (lift (lift (modify next_provenance)))).

  Definition fresh_allocation_id : ErrSID AllocationId
    := prov <- fresh_provenance;;
       ret (provenance_to_allocation_id prov).

  Definition err_to_ub {A} (e : err A) : ErrSID A
    := match e with
       | inl msg =>
           raise_ub msg
       | inr x => ret x
       end.

  Section Lemmas.
    Lemma ErrSID_evals_to_bind :
      forall {A X} sid prov (m : ErrSID X) k (res : A),
        ErrSID_evals_to (bind m k) sid prov res ->
        exists sid' prov' x,
          ErrSID_runs_to m sid prov x sid' prov' /\
            ErrSID_evals_to (k x) sid' prov' res.
    Proof.
      intros A X sid prov m k res EVAL.
      
      cbn in EVAL.
      inversion EVAL as [EVAL'].
      clear EVAL.
      rename EVAL' into EVAL.
      cbn in EVAL.

      unfold ErrSID_runs_to.
      unfold runErrSID.
      cbn.

      destruct (IdentityMonad.unIdent (unEitherT (unEitherT (unEitherT m)) sid prov)) as (p, p0) eqn:BLAH.
      destruct p0.
      cbn in *.

      destruct s0; cbn in *; inversion EVAL.
      destruct s0; cbn in *; inversion EVAL.
      destruct s0; cbn in *; inversion EVAL.

      do 3 eexists.
      split.
      { 
        reflexivity.
      }
      {
        unfold ErrSID_evals_to.
        cbn.
        auto.
      }
    Qed.

    Lemma ErrSID_runs_to_bind :
      forall {A X} sid prov (m : ErrSID X) k (res : A) sid_final prov_final,
        ErrSID_runs_to (bind m k) sid prov res sid_final prov_final ->
        exists sid' prov' x,
          ErrSID_runs_to m sid prov x sid' prov' /\
            ErrSID_runs_to (k x) sid' prov' res sid_final prov_final.
    Proof.
      intros A X sid prov m k res sid_final prov_final EVAL.
      
      cbn in EVAL.
      inversion EVAL as [EVAL'].
      clear EVAL.
      rename EVAL' into EVAL.
      cbn in EVAL.

      unfold ErrSID_runs_to.
      unfold runErrSID in *.
      cbn.

      destruct (IdentityMonad.unIdent (unEitherT (unEitherT (unEitherT m)) sid prov)) as (p, p0) eqn:BLAH.
      destruct p0.
      cbn in *.
      rewrite BLAH in EVAL.

      destruct s0; cbn in *; inversion EVAL.
      destruct s0; cbn in *; inversion EVAL.
      destruct s0; cbn in *; inversion EVAL.

      do 3 eexists.
      split.
      { 
        reflexivity.
      }
      {
        unfold ErrSID_evals_to.
        cbn.
        auto.
      }
    Qed.

    Lemma ErrSID_runs_to_ErrSID_evals_to :
      forall {X} sid prov sid' prov' (m : ErrSID X) (res : X),
        ErrSID_runs_to m sid prov res sid' prov' ->
        ErrSID_evals_to m sid prov res.
    Proof.
      intros X sid prov sid' prov' m res H.
      unfold ErrSID_runs_to in H.
      unfold ErrSID_evals_to.
      cbn.
      unfold runErrSID in H.
      cbn in H.
      match goal with
      |  H: _ |- fst (snd ?x) = _
         => destruct x
      end.
      cbn in H.
      inversion H.
      reflexivity.
    Qed.

    Global Instance proper_eq1_runs_to : forall {A}, Proper (@Monad.eq1 (eitherT ERR_MESSAGE (eitherT UB_MESSAGE _)) _ A ==> eq ==> eq ==> eq ==> eq  ==> eq ==> iff) (ErrSID_runs_to).
    Proof.
      repeat intro; subst. rename H into EQ.

      unfold Monad.eq1, Eq1_eitherT in EQ.
      split; intros RUNS.
      - unfold Monad.eq1 in EQ.
        unfold MonadState.Eq1_stateTM in EQ.
        unfold pointwise_relation in EQ.
        unfold Monad.eq1 in EQ.
        unfold Eq1_ident in EQ.

        cbn in EQ.
        unfold unEitherT in EQ.
        destruct x as [x].
        destruct y as [y].
        destruct x as [x].
        destruct y as [y].

        unfold ErrSID_runs_to, runErrSID, runErrSID_T in *.
        cbn in *.
        rewrite <- EQ.
        auto.
      - unfold Monad.eq1 in EQ.
        unfold MonadState.Eq1_stateTM in EQ.
        unfold pointwise_relation in EQ.
        unfold Monad.eq1 in EQ.
        unfold Eq1_ident in EQ.

        cbn in EQ.
        unfold unEitherT in EQ.
        destruct x as [x].
        destruct y as [y].
        destruct x as [x].
        destruct y as [y].

        unfold ErrSID_runs_to, runErrSID, runErrSID_T in *.
        cbn in *.
        rewrite EQ.
        auto.
    Qed.

  End Lemmas.

End ERRSID.
