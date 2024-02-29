(* begin hide *)
From Coq Require Import
     String Morphisms List.

From ITree Require Import
     ITree
     Basics.Monad
     Eq.Eqit
     TranslateFacts
     Events.State.

From TwoPhase Require Import
     Utilities
     Syntax
     Semantics
     Utils.NoFailure
     Utils.PostConditions
     Theory.StatePredicates
     Theory.InterpreterCFG
     Theory.ExpLemmas
     Theory.InstrLemmas
     Theory.InterpreterCFG
     Theory.SymbolicInterpreter.



Import ListNotations.
Import AlistNotations.
Import ITreeNotations.


Module LocalFrame (IS : InterpreterStack) (TOP : LLVMTopLevel IS).
  Module CFGT := CFGTheory IS TOP.

  Export CFGT.
  Export TOP.
  Export IS.
  Export IS.LLVM.
  Import IS.LLVM.MEM.
  Import MMEP.
  Import MMSP.

  Import SemNotations.
  (* end hide *)

  Definition local_has_changed (l1 : local_env) (defs: list raw_id) : local_env -> Prop :=
    fun l2 => forall x, ~ In x defs -> l1 @ x = l2 @ x.

  Definition lift_pred_L3 (T : Type) (P : local_env -> Prop) :
    (MemState * (local_env * (global_env * T))) -> Prop :=
    fun '(_,(l,_)) => P l.

End LocalFrame.

