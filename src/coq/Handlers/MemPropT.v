From Coq Require Import
     Strings.String
     ZArith.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     ITree
     Basics.Basics
     Eq.Eq
     Events.StateFacts
     Events.State.

From Vellvm Require Import Error.

From Vellvm.Utils Require Import
     PropT.

From Vellvm.Semantics Require Import
     MemoryAddress
     LLVMEvents.

Import Basics.Basics.Monads.
Import MonadNotation.
Open Scope monad_scope.

(* Move this ? *)
Definition store_id := N.

Class MonadStoreId (M : Type -> Type) : Type :=
  { fresh_sid : M store_id;
  }.

(* M could use MemState, sid, sid_set, etc... *)
Class StoreIdFreshness (S : Type) : Type :=
  { used_store_id : S -> store_id -> Prop;
    (* fresh_sid : M store_id; *)

    (* run_sid_freshness {A} : M A -> S -> (S * A); *)

    (* (* Doesn't match up with current usage... *)

    (*    E.g., when allocating or writing to memory we call fresh_sid, *)
    (*    then use that to create bytes, and then store those bytes in *)
    (*    memory. The problem is if `used_store_id` is in terms of *)
    (*    `MemState` the laws won't hold until the bytes are actually *)
    (*    stored in `MemState` after the write... *)
    (*  *) *)
    (* fresh_sid_now_used : *)
    (* forall s s' sid, *)
    (*   run_sid_freshness fresh_sid s = (s', sid) -> *)

    (*   (* Was not used *) *)
    (*   forall s'', run_sid_freshness (used_store_id sid) s = (s'', false) /\ *)

    (*   (* Freshly allocated one is now used *) *)
    (*   forall s'', run_sid_freshness (used_store_id sid) s' = (s'', true) /\ *)

    (*   (* Whether other sids are used is preserved *) *)
    (*   forall sid' s'' s''' usedp, *)
    (*     (sid' <> sid -> run_sid_freshness (used_store_id sid') s = (s'', usedp) -> run_sid_freshness (used_store_id sid') s' = (s''', usedp)); *)
  }.

Class AllocationIdFreshness (AllocationId : Type) (S : Type) : Type :=
  { used_allocation_id : S -> AllocationId -> Prop;
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
Import EitherMonad.
Import Monad.
Import Morphisms.
Class MemMonad (MemState : Type) (ExtraState : Type) (AllocationId : Type) (M : Type -> Type) (RunM : Type -> Type)
      `{Monad M} `{Monad RunM}
      `{MonadAllocationId AllocationId M} `{MonadStoreId M} `{MonadMemState MemState M}
      `{StoreIdFreshness MemState} `{AllocationIdFreshness AllocationId MemState}
      `{RAISE_ERROR M} `{RAISE_UB M} `{RAISE_OOM M}
      `{RAISE_ERROR RunM} `{RAISE_UB RunM} `{RAISE_OOM RunM}
  : Type
  :=
  { MemMonad_eq1_runm :> Eq1 RunM;
    MemMonad_runm_monadlaws :> MonadLawsE RunM;
    MemMonad_eq1_runm_equiv {A} :> Equivalence (@eq1 _ MemMonad_eq1_runm A);

    MemMonad_eq1_runm_proper :>
        (forall A, Proper ((@eq1 _ MemMonad_eq1_runm) A ==> (@eq1 _ MemMonad_eq1_runm) A ==> iff) ((@eq1 _ MemMonad_eq1_runm) A));

    MemMonad_run {A} (ma : M A) (ms : MemState) (st : ExtraState)
    : RunM (ExtraState * (MemState * A))%type;

    (** Whether a piece of extra state is valid for a given execution *)
    MemMonad_valid_state : MemState -> ExtraState -> Prop;

    (** Run bind / ret laws *)
    MemMonad_run_bind
      {A B} (ma : M A) (k : A -> M B) (ms : MemState) (st : ExtraState) (VALID : MemMonad_valid_state ms st):
    eq1 (MemMonad_run (x <- ma;; k x) ms st)
        ('(st', (ms', x)) <- MemMonad_run ma ms st;; MemMonad_run (k x) ms' st');

    MemMonad_run_ret
      {A} (x : A) (ms : MemState) st (VALID : MemMonad_valid_state ms st):
    eq1 (MemMonad_run (ret x) ms st) (ret (st, (ms, x)));

    (** MonadMemState properties *)
    MemMonad_get_mem_state
      (ms : MemState) st :
    eq1 (MemMonad_run (get_mem_state) ms st) (ret (st, (ms, ms)));

    MemMonad_put_mem_state
      (ms ms' : MemState) st :
    eq1 (MemMonad_run (put_mem_state ms') ms st) (ret (st, (ms', tt)));

    (** Fresh store id property *)
    MemMonad_run_fresh_sid
      (ms : MemState) st (VALID : MemMonad_valid_state ms st):
    exists st' sid',
      eq1 (MemMonad_run (fresh_sid) ms st) (ret (st', (ms, sid'))) /\ ~ used_store_id ms sid';

    (** Fresh allocation id property *)
    MemMonad_run_fresh_allocation_id
      (ms : MemState) st (VALID : MemMonad_valid_state ms st):
    exists st' aid',
      eq1 (MemMonad_run (fresh_allocation_id) ms st) (ret (st', (ms, aid'))) /\ ~ used_allocation_id ms aid';

    (** Exceptions *)
    MemMonad_run_raise_oom :
    forall {A} ms oom_msg st,
      eq1 (MemMonad_run (@raise_oom _ _ A oom_msg) ms st) (raise_oom oom_msg);

    MemMonad_run_raise_ub :
    forall {A} ms ub_msg st,
      eq1 (MemMonad_run (@raise_ub _ _ A ub_msg) ms st) (raise_ub ub_msg);

    MemMonad_run_raise_error :
    forall {A} ms error_msg st,
      eq1 (MemMonad_run (@raise_error _ _ A error_msg) ms st) (raise_error error_msg);
  }.

    (** StateT *)
    (* MemMonad_lift_stateT *)
    (*   {E} `{FailureE -< E} `{UBE -< E} `{OOME -< E} {A} *)
    (*   (ma : M A) : stateT MemState (itree E) A; *)

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
                        | inr (Oom _) => False
                        end).
  - (* bind *)
    refine (fun A B ma amb sa r =>
              match r with
              | inl err            =>
                  exists err,
                  (ma sa (inl err) \/
                     (exists sab a, ma sa (inr (NoOom (sab, a))) /\
                                 (amb a sab (inl err))))
              | inr (NoOom (sb,r)) =>
                  exists sab a,
                  ma sa (inr (NoOom (sab, a))) /\
                    amb a sab (inr (NoOom (sb, r)))
              | inr (Oom msg)         =>
                  exists msg',
                  (ma sa (inr (Oom msg')) \/
                     (exists sab a, ma sa (inr (NoOom (sab, a))) /\
                                 (amb a sab (inr (Oom msg')))))
                  
              end
           ).
Defined.

Instance MemPropT_MonadMemState {MemState : Type} : MonadMemState MemState (MemPropT MemState).
Proof.
  (* Operations must actually succeed *)
  split.
  - (* get_mem_state *)
    unfold MemPropT.
    intros ms [err_msg | [[ms' a] | oom_msg]].
    + exact False.
    + exact (ms = ms' /\ a = ms).
    + exact False.
  - (* put_mem_state *)
    unfold MemPropT.
    intros ms_to_put ms [err_msg | [[ms' t] | oom_msg]].
    + exact False.
    + exact (ms_to_put = ms').
    + exact False.
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

Instance MemPropT_RAISE_UB {MemState : Type} : RAISE_UB (MemPropT MemState).
Proof.
  split.
  intros A ub_msg.
  refine (fun ms res => False /\ ub_msg = ""%string).
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

Definition MemPropT_lift_PropT {MemState X} {E} `{UBE -< E} `{OOME -< E} `{FailureE -< E} (m : MemPropT MemState X) : 
  stateT MemState (PropT E) X.
Proof.
  unfold PropT, MemPropT, stateT in *.
  intros ms t.
  specialize (m ms).
  refine (((exists msg, t ≈ raise_ub msg) <-> (forall res, ~ m res)) /\
          ((exists msg, t ≈ raise_error msg) <-> (exists msg, m (inl msg))) /\
          ((exists msg, t ≈ raise_oom msg) <-> (exists msg, m (inr (Oom msg)))) /\
          (forall res, t ≈ ret res <-> m (inr (NoOom res)))).
Defined.

Definition MemPropT_lift_PropT_fresh {MemState Provenance X} {E} `{UBE -< E} `{OOME -< E} `{FailureE -< E} (m : MemPropT MemState X) : 
  stateT store_id (stateT Provenance (stateT MemState (PropT E))) X.
Proof.
  unfold PropT, MemPropT, stateT in *.
  intros sid pr ms t.
  specialize (m ms).
  refine (((exists msg, t ≈ raise_ub msg) <-> (forall res, ~ m res)) /\
          ((exists msg, t ≈ raise_error msg) <-> (exists msg, m (inl msg))) /\
          ((exists msg, t ≈ raise_oom msg) <-> (exists msg, m (inr (Oom msg)))) /\
          (forall sid pr ms x, t ≈ ret (ms, (pr, (sid, x))) <-> m (inr (NoOom (ms, x))))).
Defined.
