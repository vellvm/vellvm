From ITree Require Import ITree.
From CTree Require Import CTree Eq Fold.
From Vellvm Require Import Utils.PropT Semantics.LLVMEvents Semantics.InterpretationStack Semantics.StoreId.
From Vellvm Require Import Utils.Error Handlers.MemoryModelImplementation.
​
Import Memory64BitIntptr.MMEP.MemSpec.
Import LLVMParams64BitIntptr.Events.
Import Memory64BitIntptr.MMEP.MMSP.
​
Import CTreeNotations.
​
(* see Handlers/MemoryModel.v *)
​
Variant MemC : Type -> Type :=
| memC {X} (e : MemoryE X) m : MemC ({res | handle_memory_prop _ e m res})
| intrinsicC {X} (e : IntrinsicE X) m : MemC ({res | handle_intrinsic_prop _ e m res}).
​
Definition err_ub_oom_ctree {E B X} `{OOME -< E} `{UBE -< E} `{FailureE -< E} : err_ub_oom X -> ctree E B X.
  intros. apply run_err_ub_oom in X0.
  destruct X0. apply (trigger (ThrowOOM tt);; Stuck).
  destruct s. apply (trigger (ThrowUB tt);; Stuck). (* FIXME UB *)
  destruct s. apply (trigger (Throw tt);; Stuck) (* FIXME special unary event? *).
  apply (Ret x).
Defined.
​
Unset Universe Checking.
​
Definition handle_memory_ctree {E B : Type -> Type} `{OOME -< E} `{UBE -< E} `{FailureE -< E} `{MemC -< B} : MemoryE ~> Monads.stateT MemState (ctree E B) :=
  fun T (m : MemoryE T) s =>
    r <- branch (memC m s);;
    err_ub_oom_ctree (proj1_sig r).
​
Definition handle_intrinsic_ctree {E B : Type -> Type} `{OOME -< E} `{UBE -< E} `{FailureE -< E} `{MemC -< B} : IntrinsicE ~> Monads.stateT MemState (ctree E B) :=
  fun T (m : IntrinsicE T) s =>
    r <- branch (intrinsicC m s);;
    err_ub_oom_ctree (proj1_sig r).
​
Section InterpMem.
​
#[local] Definition E_trigger {E F B} :
  E ~> Monads.stateT MemState (ctree (E +' F) B) := fun _ e s => x <- trigger e;; Ret (s, x).
​
#[local] Definition F_trigger {E F B} :
  F ~> Monads.stateT MemState (ctree (E +' F) B) := fun _ e s => x <- trigger e;; Ret (s, x).
​
Definition interp_memory_ctree {E R} :
  ITreeDefinition.itree (E +'
   IntrinsicE +'
   MemoryE +'
   PickUvalueE +'
   LLVMEvents.OOME +' LLVMEvents.UBE +' LLVMEvents.DebugE +' LLVMEvents.FailureE) R ->
  Monads.stateT MemState (ctree 
    (E +' PickUvalueE +'
      LLVMEvents.OOME +' LLVMEvents.UBE +' LLVMEvents.DebugE +' LLVMEvents.FailureE) MemC) R :=
  fun t => Interp.interp (M := Monads.stateT _ (ctree _ _)) (case_ E_trigger (case_ handle_intrinsic_ctree (case_ handle_memory_ctree F_trigger))) t.
​
End InterpMem.
​
Import Vellvm.Semantics.InterpretationStack.InterpreterStack64BitIntptr.LLVM.
Import Vellvm.Semantics.InterpretationStack.InterpreterStack64BitIntptr.LP.Events.
​
Variant PickC : Type -> Type :=
| pickC x : PickC {v | concretize_u x v}
(*| pickUniqueC x : PickC (option {v | unique_prop x /\ concretize_u x v})
| pickNonPoisonC x : PickC (option {v | non_poison_prop x /\ concretize_u x v})*)
| pickUniqueUBC x : PickC (unique_prop x -> False)
| pickNonPoisonUBC x : PickC (non_poison_prop x -> False)
.
​
(* TODO maybe concretize_uvalueM could work here? *)
Definition handle_pick {E B}
  `{FE:FailureE -< E} `{FO:UBE -< E} `{OO: OOME -< E}
  `{B2 -< B} `{PickC -< B} : PickUvalueE ~> ctree E B :=
  fun _ (e : PickE _) =>
  match e with
  | pick x =>
    res <- branch (pickC x);;
    v <- err_ub_oom_ctree (proj1_sig res);;
    Ret (exist _ v I)
  | pickUnique x => br2 (
      res <- branch (pickC x);;
      v <- err_ub_oom_ctree (proj1_sig res);;
      Ret (exist _ v I))
      (branch (pickUniqueUBC x);; trigger (ThrowUB tt);; Stuck)
  | pickNonPoison x => br2 (
      res <- branch (pickC x);;
      v <- err_ub_oom_ctree (proj1_sig res);;
      Ret (exist _ v I))
      (branch (pickNonPoisonUBC x);; trigger (ThrowUB tt);; Stuck)
  end.
​
Section InterpPick.
​
#[local] Definition E_trigger' {E F B} :
  E ~> ctree (E +' F) B := fun _ e => trigger e.
​
Definition F_trigger' {E F B} :
  F ~> ctree (E +' F) B := fun _ e => trigger e.
​
Program Definition interp_pick {E F B C X}
  `{FailureE -< E +' F} `{UBE -< E +' F} `{OOME -< F}
  `{B2 -< C} `{PickC -< C} `{B -< C}
  (t : ctree (E +' PickUvalueE +' F) B X) : ctree (E +' F) C X :=
  interp (M := ctree _ _) (case_ E_trigger' (case_ handle_pick F_trigger')) t.
​
End InterpPick.
​
(* (MemState * (store_id * (local_env * @stack local_env * (global_env * R)))) *)
​
Definition interp_mcfg3 {R} (t: itree L0 R) g l m : ctree L3 MemC _ :=
  let uvalue_trace   := interp_intrinsics t in
  let L1_trace       := interp_global uvalue_trace g in
  let L2_trace       := interp_local_stack L1_trace l in
  let L3_trace       := interp_memory_ctree L2_trace m in
  L3_trace.
​
Definition interp_mcfg4 {R} (t: itree L0 R) g l m : ctree L4 (B2 +' MemC +' PickC) (MemState * ((*store_id * *)(local_env * @stack local_env * (global_env * R)))) :=
  let uvalue_trace   := interp_intrinsics t in
  let L1_trace       := interp_global uvalue_trace g in
  let L2_trace       := interp_local_stack L1_trace l in
  let L3_trace       := interp_memory_ctree L2_trace m in
  let L4_trace       := interp_pick L3_trace in
  L4_trace.
