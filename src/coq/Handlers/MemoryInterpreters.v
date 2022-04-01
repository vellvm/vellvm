From Coq Require Import
     Morphisms.

From Vellvm.Semantics Require Import
     MemoryParams
     Memory.ErrSID
     LLVMParams
     LLVMEvents.

From Vellvm.Handlers Require Import
     MemoryModel
     MemPropT.

From Vellvm.Utils Require Import
     StateMonads.

From ITree Require Import
     ITree
     Basics.Basics
     Eq.Eq
     Events.StateFacts
     Events.State.

From ExtLib Require Import
     Structures.Functor
     Structures.Monads.

(* Needs to be after ITree.Events.State *)
From Vellvm.Utils Require Import
     PropT.

Import Basics.Basics.Monads.
Import MonadNotation.

Set Implicit Arguments.
Set Contextual Implicit.

Module Type MemorySpecInterpreter (LP : LLVMParams) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) (MM : MemoryModelSpec LP MP MMSP).
  Import MM.
  Import MMSP.
  Import LP.Events.

  Section Interpreters.
    Variable (E F : Type -> Type).
    Context `{FailureE -< F} `{UBE -< F} `{OOME -< F}.
    Notation Effin := (E +' IntrinsicE +' MemoryE +' F).
    Notation Effout := (E +' F).

    Definition MemStateT M := stateT MemState M.

    Definition E_trigger : forall R, E R -> (MemStateT (PropT Effout) R) :=
      fun R e m => fun t => t ≈ r <- trigger e;; ret (m, r).

    Definition F_trigger : forall R, F R -> (MemStateT (PropT Effout) R) :=
      fun R e m => fun t => t ≈ r <- trigger e;; ret (m, r).

    (* TODO: get rid of this silly hack. *)
    Definition my_handle_memory_prop :
      forall T : Type, MemoryE T -> MemStateT (PropT Effout) T.
    Proof.
      intros T MemE.
      eapply MemPropT_lift_PropT.
      eapply handle_memory_prop; auto.
    Defined.

    Definition my_handle_intrinsic_prop :
      forall T : Type, IntrinsicE T -> MemStateT (PropT Effout) T.
    Proof.
      intros T IntE.
      eapply MemPropT_lift_PropT.
      eapply handle_intrinsic_prop; auto.
    Defined.

    Definition interp_memory_prop_h : forall T, Effin T -> MemStateT (PropT Effout) T
      := case_ E_trigger (case_ my_handle_intrinsic_prop (case_ my_handle_memory_prop F_trigger)).

    (* TODO: I find the lack of interp_prop here disturbing... *)
    Definition memory_k_spec
               {T R : Type}
               (e : Effin T)
               (ta : itree Effout T)
               (k1 : T -> itree Effin R)
               (k2 : T -> itree Effout R)
               (t2 : itree Effout R) : Prop
      := t2 ≈ (bind ta k2).

    Global Instance memory_k_spec_proper {T R : Type} {RR : R -> R -> Prop} {b a : bool} :
      Proper
        (eq ==>
            eq ==>
            (fun k1 k2 : T -> itree Effin R =>
               forall x : T, eqit RR b a (k1 x) (k2 x)) ==> eq ==> eq ==> iff)
        (memory_k_spec).
    Proof.
      unfold Proper, respectful.
      intros x y ? x0 y0 ? x1 y1 ? x2 y2 ? x3 y3 ?; subst.
      split; cbn; auto.
    Qed.

    Definition interp_memory_prop {R} (RR : R -> R -> Prop) :
      itree Effin R -> MemStateT (PropT Effout) R :=
      fun (t : itree Effin R) (ms : MemState) (t' : itree Effout (MemState * R)) =>
        interp_prop (fun T e t => exists ms', @interp_memory_prop_h T e ms (fmap (fun x => (ms', x)) t)) (@memory_k_spec) R RR t (fmap snd t').
  End Interpreters.
End MemorySpecInterpreter.

Module Type MemoryExecInterpreter (LP : LLVMParams) (MP : MemoryParams LP) (MMEP : MemoryModelExecPrimitives LP MP) (MM : MemoryModelExec LP MP MMEP) (SPEC_INTERP : MemorySpecInterpreter LP MP MMEP.MMSP MMEP.MemSpec).
  Import MM.
  Import MMEP.
  Import MMEP.MMSP.
  Import LP.
  Import LP.Events.
  Import LP.PROV.

  (** Specification of the memory model *)
  Import SPEC_INTERP.
  Import MMSP.
  Import MMSP.MemByte.

  Section Interpreters.
    Variable (E F : Type -> Type).
    Context `{FailureE -< F} `{UBE -< F} `{OOME -< F}.
    Notation Effin := (E +' IntrinsicE +' MemoryE +' F).
    Notation Effout := (E +' F).

    Definition E_trigger : E ~> MemStateT (itree Effout) :=
      fun R e m => r <- trigger e;; ret (m, r).

    Definition F_trigger : F ~> MemStateT (itree Effout) :=
      fun R e m => r <- trigger e;; ret (m, r).

    (* TODO: get rid of this silly hack. *)
    Definition my_handle_memory {MemM} `{MemMonad MemState AllocationId MemM} : MemoryE ~> MemStateT (itree Effout) :=
      fun T e ms => lift_err_ub_oom ret (MemMonad_run (handle_memory T e) ms).

    Definition my_handle_intrinsic {MemM} `{MemMonad MemState AllocationId MemM} : IntrinsicE ~> MemStateT (itree Effout) :=
      fun T e ms => lift_err_ub_oom ret (MemMonad_run (handle_intrinsic T e) ms).

    Definition interp_memory_h {MemM} `{MemMonad MemState AllocationId MemM} : Effin ~> MemStateT (itree Effout)
      := case_ E_trigger (case_ my_handle_intrinsic (case_ my_handle_memory F_trigger)).

    (* TODO: I find the lack of interp_prop here disturbing... *)
    Definition interp_memory {MemM} `{MemMonad MemState AllocationId MemM} :
      itree Effin ~> MemStateT (itree Effout) :=
      interp_state interp_memory_h.

    Lemma interp_memory_correct :
      forall {MemM} `{MM : MemMonad MemState AllocationId MemM} {T} t ms,
        interp_memory_prop eq t ms (@interp_memory MemM _ _ _ _ _ _ _ _ _ MM T t ms).
    Proof.
      intros MemM H2 H3 H4 H5 H6 H7 H8 H9 H10 MM T t ms.
      unfold interp_memory_prop.
      unfold interp_memory.
      unfold interp_state.
    Admitted.
  End Interpreters.
End MemoryExecInterpreter.


Module MakeMemorySpecInterpreter (LP : LLVMParams) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) (MS : MemoryModelSpec LP MP MMSP) <: MemorySpecInterpreter LP MP MMSP MS.
  Include MemorySpecInterpreter LP MP MMSP MS.
End MakeMemorySpecInterpreter.

Module MakeMemoryExecInterpreter (LP : LLVMParams) (MP : MemoryParams LP) (MMEP : MemoryModelExecPrimitives LP MP) (ME : MemoryModelExec LP MP MMEP) (SPEC_INTERP : MemorySpecInterpreter LP MP MMEP.MMSP MMEP.MemSpec) <: MemoryExecInterpreter LP MP MMEP ME SPEC_INTERP.
  Include MemoryExecInterpreter LP MP MMEP ME SPEC_INTERP.
End MakeMemoryExecInterpreter.
