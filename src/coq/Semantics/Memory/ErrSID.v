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
     Semantics.LLVMEvents
     Semantics.Memory.FiniteProvenance
     Semantics.Memory.Sizeof
     Utils.StateMonads
     Utils.Monads.

From ITree Require Import
     ITree
     Basics.Basics
     Events.Exception
     Eq.Eq
     Events.StateFacts
     Events.State.

Import Basics.Basics.Monads.

Import MonadNotation.

(* TODO: Provenance is an issue... *)
Module ERRSID (Addr:ADDRESS) (IP:INTPTR) (SIZEOF:Sizeof) (LLVMEvents:LLVM_INTERACTIONS(Addr)(IP)(SIZEOF)) (PROV:PROVENANCE(Addr)).
  Import LLVMEvents.
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

  Definition ErrSID_evals_to {A} (e : ErrSID A) (x : A) sid pr : Prop
    := evalErrSID e sid pr = inr (inr (inr x)).

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

End ERRSID.
