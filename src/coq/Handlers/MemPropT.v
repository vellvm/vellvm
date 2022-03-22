From Coq Require Import ZArith.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     ITree
     Basics.Basics
     Events.StateFacts
     Events.State.

From Vellvm Require Import Error.

From Vellvm.Semantics Require Import
     MemoryAddress
     LLVMEvents.

Import Basics.Basics.Monads.
Import MonadNotation.
Open Scope monad_scope.

(* Move this ? *)
Definition store_id := N.
Class MonadStoreID (M : Type -> Type) : Type :=
  { fresh_sid : M store_id;
  }.

Class MonadMemState (MemState : Type) (M : Type -> Type) : Type :=
  { get_mem_state : M MemState;
    put_mem_state : MemState -> M unit;
  }.

Definition modify_mem_state {M MemState} `{Monad M} `{MonadMemState MemState M} (f : MemState -> MemState) : M MemState :=
  ms <- get_mem_state;;
  put_mem_state (f ms);;
  ret ms.

(* TODO: Add RAISE_PICK or something... May need to be in a module *)
Class MemMonad (MemState : Type) (AllocationId : Type) (M : Type -> Type)
      `{Monad M}
      `{MonadAllocationId AllocationId M} `{MonadStoreID M} `{MonadMemState MemState M}
      `{RAISE_ERROR M} `{RAISE_UB M} `{RAISE_OOM M} : Type
  :=
  {
    MemMonad_runs_to {A} (ma : M A) (ms : MemState) : err_ub_oom (MemState * A);
    MemMonad_lift_stateT
      {E} `{FailureE -< E} `{UBE -< E} `{OOME -< E} {A}
      (ma : M A) : stateT MemState (itree E) A;
  }.


Definition MemPropT (MemState : Type) (X : Type) : Type
  := MemState -> err (OOM (MemState * X)%type) -> Prop.

(* Instance MemPropT_Monad : Monad MemPropT. *)
(* Proof. *)
(*   split. *)
(*   - (* ret *) *)
(*     intros T x. *)
(*     unfold MemPropT. *)
(*     intros ms [err_msg | [[ms' res] | oom_msg]]. *)
(*     + exact False. (* error is not a valid behavior here *) *)
(*     + exact (ms = ms' /\ x = res). *)
(*     + exact True. (* Allow OOM to refine anything *) *)
(*   - (* bind *) *)
(*     intros A B ma amb. *)
(*     unfold MemPropT in *. *)

(*     intros ms [err_msg | [[ms'' b] | oom_msg]]. *)
(*     + (* an error is valid when ma errors, or the continuation errors... *) *)
(*       refine *)
(*         ((exists err, ma ms (inl err)) \/ *)
(*          (exists ms' a, *)
(*              ma ms (inr (NoOom (ms', a))) -> *)
(*              (exists err, amb a ms' (inl err)))). *)
(*     + (* No errors, no OOM *) *)
(*       refine *)
(*         (exists ms' a k, *)
(*             ma ms (inr (NoOom (ms', a))) -> *)
(*             amb a ms' (inr (NoOom (ms'', k a)))). *)
(*     + (* OOM is always valid *) *)
(*       exact True. *)
(* Defined. *)

(* To triple check, but the following makes more sense to me *)
Instance MemPropT_Monad {MemState : Type} : Monad (MemPropT MemState).
Proof.
  split.
  - (* ret *)
    refine (fun _ v s r => match r with
                        | inl _ => False
                        | inr (NoOom (s',r')) => s' = s /\ r' = v
                        | inr (Oom _) => True
                        end).
  - (* bind *)
    refine (fun A B ma amb sa r =>
              match r with
              | inl err            =>
                  ma sa (inl err) \/
                    (exists sab a, ma sa (inr (NoOom (sab, a))) /\
                                (exists err, amb a sab (inl err)))
              | inr (NoOom (sb,r)) =>
                  exists sab a,
                  ma    sa  (inr (NoOom (sab, a))) /\
                    amb a sab (inr (NoOom (sb, r)))
              | inr (Oom _)         => True
              end
           ).
Defined.

Instance MemPropT_MonadMemState {MemState : Type} : MonadMemState MemState (MemPropT MemState).
Proof.
  split.
  - (* get_mem_state *)
    unfold MemPropT.
    intros ms [err_msg | [[ms' a] | oom_msg]].
    + exact True.
    + exact (ms = ms' /\ a = ms).
    + exact True.
  - (* put_mem_state *)
    unfold MemPropT.
    intros ms_to_put ms [err_msg | [[ms' t] | oom_msg]].
    + exact True.
    + exact (ms_to_put = ms').
    + exact True.
Defined.

Instance MemPropT_RAISE_OOM {MemState : Type} : RAISE_OOM (MemPropT MemState).
Proof.
  split.
  - intros A msg.
    unfold MemPropT.
    intros ms [err | [_ | oom]].
    + exact False. (* Must run out of memory, can't error *)
    + exact False. (* Must run out of memory *)
    + exact True. (* Don't care about message *)
Defined.

Instance MemPropT_RAISE_ERROR {MemState : Type} : RAISE_ERROR (MemPropT MemState).
Proof.
  split.
  - intros A msg.
    unfold MemPropT.
    intros ms [err | [_ | oom]].
    + exact True. (* Any error will do *)
    + exact False. (* Must error *)
    + exact False. (* Must error *)
Defined.

Definition MemPropT_assert {MemState X} (assertion : Prop) : MemPropT MemState X
  := fun ms ms'x =>
       match ms'x with
       | inl _ =>
           assertion
       | inr (NoOom (ms', x)) =>
           ms = ms' /\ assertion
       | inr (Oom s) =>
           assertion
       end.

Definition MemPropT_assert_post {MemState X} (Post : X -> Prop) : MemPropT MemState X
  := fun ms ms'x =>
       match ms'x with
       | inl _ =>
           True
       | inr (NoOom (ms', x)) =>
           ms = ms' /\ Post x
       | inr (Oom s) =>
           True
       end.
