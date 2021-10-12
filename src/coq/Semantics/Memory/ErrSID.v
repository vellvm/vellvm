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
Module ERRSID (Addr:ADDRESS) (SIZEOF:Sizeof) (LLVMEvents:LLVM_INTERACTIONS(Addr)(SIZEOF)) (PROV:PROVENANCE(Addr)).
  Import LLVMEvents.
  Import PROV.

  (* Need failure, UB, state for store_ids, and state for provenances *)
  Definition ErrSID_T M := eitherT ERR_MESSAGE (eitherT UB_MESSAGE (stateT store_id (stateT Provenance M))).
  Definition ErrSID := ErrSID_T ident.

  (* I can make this work using ltac, but  for some reason I can't write the definition directly... *)
  #[global] Instance ErrSID_T_MT {M : Type -> Type} `{HM: Monad M} : MonadT (ErrSID_T M) M.
  Proof.
    constructor.
    refine (fun T mt => mkEitherT (mkEitherT (fun sid prov => _))).
    refine (fmap (fun v => (prov, (sid, inr (inr v)))) mt : M (Provenance * (store_id * UB (ERR T)))%type).
  Defined.

  #[global] Instance UBM_ErrSID_T {M : Type -> Type} `{HM :  Monad M} : UBM (ErrSID_T M) :=
    { raise_ub := fun A e => lift (raise_ub e);
    }.

  Definition evalErrSID_T {A} {M} `{Monad M} (m : ErrSID_T M A) (sid : store_id) (prov : Provenance) : M (UB (ERR A))
    := evalStateT (evalStateT (unEitherT (unEitherT m)) sid) prov.

  Definition evalErrSID {A} (m : ErrSID A) (sid : store_id) (prov : Provenance) : UB (ERR A)
    := unIdent (evalErrSID_T m sid prov).

  Definition runErrSID_T {A} {M} `{Monad M} (m : ErrSID_T M A) (sid : store_id) (prov : Provenance) : M (UB (ERR A) * store_id * Provenance)%type
    := runStateT (runStateT (unEitherT (unEitherT m)) sid) prov.

  Definition runErrSID {A} (m : ErrSID A) (sid : store_id) (prov : Provenance) : UB (ERR A) * store_id * Provenance%type
    := unIdent (runErrSID_T m sid prov).

  Definition ErrSID_evals_to {A} (e : ErrSID A) (x : A) sid pr : Prop
    := evalErrSID e sid pr = inr (inr x).

  Definition fresh_sid : ErrSID store_id
    := lift (lift (modify N.succ)).

  Definition fresh_provenance : ErrSID Provenance
    := lift (lift (lift (modify next_provenance))).

  Definition fresh_allocation_id : ErrSID AllocationId
    := prov <- fresh_provenance;;
       ret (provenance_to_allocation_id prov).

  Definition err_to_ub {A} (e : err A) : ErrSID A
    := match e with
       | inl msg =>
         (* TODO: can this be inferred...? *)
         @raise_ub ErrSID (@UBM_E_MT _ _ _ (@UBM_MonadExc (eitherT UB_MESSAGE (stateT store_id (stateT Provenance ident))) _)) _ msg
       | inr x => ret x
       end.

End ERRSID.
