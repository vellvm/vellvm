From Coq Require Import
     Strings.String
     ZArith.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     ITree
     Basics.Basics
     Eq.Eqit
     Events.StateFacts
     Events.State.

From Vellvm Require Import Error.

From Vellvm.Utils Require Import
     MonadEq1Laws
     PropT
     Raise
     Tactics
     Inhabited.

From Mem Require Import
  MemoryModules.Within
  Semantics.Memory.StoreId.

Import Basics.Basics.Monads.
Import MonadNotation.
Open Scope monad_scope.

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

Class ProvenanceFreshness (Provenance : Type) (S : Type) : Type :=
  { used_provenance : S -> Provenance -> Prop;
  }.

Class MonadMemState (MemState : Type) (M : Type -> Type) : Type :=
  { get_mem_state : M MemState;
    put_mem_state : MemState -> M unit;
  }.

Class MemStateMem (MemState : Type) (memory : Type) : Type :=
  { ms_get_memory : MemState -> memory;
    ms_put_memory : memory -> MemState -> MemState;

    ms_get_put_memory : forall ms mem,
      ms_get_memory (ms_put_memory mem ms) = mem;
  }.

Definition modify_mem_state {M MemState} `{Monad M} `{MonadMemState MemState M} (f : MemState -> MemState) : M MemState :=
  ms <- get_mem_state;;
  put_mem_state (f ms);;
  ret ms.

(* TODO: Add RAISE_PICK or something... May need to be in a module *)
Import EitherMonad.
Import Monad.
Import Morphisms.

    (** StateT *)
    (* MemMonad_lift_stateT *)
    (*   {E} `{FailureE -< E} `{UBE -< E} `{OOME -< E} {A} *)
    (*   (ma : M A) : stateT MemState (itree E) A; *)

Definition MemPropT (MemState : Type) (X : Type) : Type
  := MemState -> err_ub_oom (MemState * X)%type -> Prop.

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
Import IdentityMonad.
Instance MemPropT_Monad {MemState : Type} : Monad (MemPropT MemState).
Proof.
  split.
  - (* ret *)
    refine (fun _ v s r =>
              match r with
              | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent r)))) =>
                  match r with
                  | inl (OOM_message x) => False
                  | inr (inl (UB_message x)) => False
                  | inr (inr (inl (ERR_message x))) => False
                  | inr (inr (inr (s',r'))) => s' = s /\ r' = v
                  end
              end).
  - (* bind *)
    refine (fun A B ma amb sa r =>
              match r with
              | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent r)))) =>
                  match r with
                  | inl (OOM_message msg') =>
                      (ma sa (raise_oom msg') \/
                         (exists sab a, ma sa (ret (sab, a)) /\
                                     (amb a sab (raise_oom msg'))))
                  | inr (inl (UB_message msg')) =>
                      (ma sa (raise_ub msg') \/
                         (exists sab a, ma sa (ret (sab, a)) /\
                                     (amb a sab (raise_ub msg'))))
                  | inr (inr (inl (ERR_message msg'))) =>
                      (ma sa (raise_error msg') \/
                         (exists sab a, ma sa (ret (sab, a)) /\
                                     (amb a sab (raise_error msg'))))
                  | inr (inr (inr (s',r'))) =>
                      exists sab a,
                      ma sa (ret (sab, a)) /\
                        amb a sab (ret (s', r'))
                  end
              end).
Defined.

#[global] Instance MemPropT_Eq1 {MemState} : Eq1 (MemPropT MemState).
Proof.
  unfold Eq1.
  intros A m1 m2.
  unfold MemPropT in *.
  exact (forall (ms : MemState) (x : err_ub_oom (MemState * A)),
            m1 ms x <-> m2 ms x).
Defined.

#[global] Instance MemPropT_Eq1Equivalance {MemState} : Eq1Equivalence (MemPropT MemState).
Proof.
  split.
  - firstorder.
  - firstorder.
  - unfold Transitive.
    intros x y z XY YZ.
    unfold eq1, MemPropT_Eq1 in *.
    intros ms x0.
    rewrite XY.
    auto.
Defined.

Ltac destruct_err_ub_oom x :=
  destruct x as [[[[[[[?oom_x] | [[?ub_x] | [[?err_x] | ?x]]]]]]]] eqn:?Hx.


#[global] Instance MemPropT_MonadLawsE {MemState} : MonadLawsE (MemPropT MemState).
Proof.
  split.
  - intros A B f x.
    cbn.
    unfold eq1, MemPropT_Eq1 in *.
    split;
      intros M.
    +
      (* TODO: Move to Error.v *)
      destruct_err_ub_oom x0; firstorder; subst; firstorder.
      repeat break_match_hyp.
      destruct M as (sab & a & (EQ1 & EQ2) & F); subst.
      auto.
    + destruct_err_ub_oom x0; firstorder.
      destruct x1. exists ms. exists x. firstorder.
  - intros A x.
    cbn.
    unfold eq1, MemPropT_Eq1 in *.
    split;
      intros M.
    + destruct_err_ub_oom x0; firstorder; subst; firstorder.
      repeat break_match_hyp.
      destruct M as (sab & a' & F & (EQ1 & EQ2)); subst.
      auto.
    + destruct_err_ub_oom x0; firstorder.
      destruct x1. exists m. exists a. firstorder.
  - intros A B C x f g.
    cbn.
    unfold eq1, MemPropT_Eq1 in *.
    split;
      intros M.
    + destruct_err_ub_oom x0; firstorder; subst; firstorder.
      * right. exists x3. exists x4. firstorder.
      * right. exists x3. exists x4. firstorder.
      * right. exists x3. exists x4. firstorder.
      * destruct x1.
        destruct M as (sab & b & ((sab' & a' & (x' & f')) & g')); subst.
        eexists. eexists. eauto.
    + destruct_err_ub_oom x0; firstorder; subst; firstorder.
      * right. eexists. eexists. eauto.
      * right. eexists. eexists. eauto.
      * right. eexists. eexists. eauto.
      * destruct x1.
        destruct M as (sab & a' & Hx & (sab' & b' & (f' & g'))); subst.
        eexists. eexists. eauto.
  - repeat red. intros.
    split; cbn; intros.
    + destruct_err_ub_oom x1; firstorder; subst; firstorder.
      * right. exists x2. exists x3. split. apply H. assumption. apply H0. assumption.
      * right. exists x2. exists x3. split. apply H. assumption. apply H0. assumption.
      * right. exists x2. exists x3. split. apply H. assumption. apply H0. assumption.
      * destruct x2.
        destruct H1 as (sab & a & (HX & HY)).
        exists sab. exists a. split. apply H. assumption. apply H0. assumption.
    + destruct_err_ub_oom x1; firstorder; subst; firstorder.
      * right. exists x2. exists x3. split. apply H. assumption. apply H0. assumption.
      * right. exists x2. exists x3. split. apply H. assumption. apply H0. assumption.
      * right. exists x2. exists x3. split. apply H. assumption. apply H0. assumption.
      * destruct x2.
        destruct H1 as (sab & a & (HX & HY)).
        exists sab. exists a. split. apply H. assumption. apply H0. assumption.
Qed.

#[global] Instance MemPropT_MonadMemState {MemState : Type} : MonadMemState MemState (MemPropT MemState).
Proof.
  (* Operations must actually succeed *)
  split.
  - (* get_mem_state *)
    unfold MemPropT.
    intros ms res.
    destruct res as [[[[[[[oom_res] | [[ub_res] | [[err_res] | [ms' a]]]]]]]]] eqn:Hres.
    + (* OOM *)
      exact False.
    + (* UB *)
      exact False.
    + (* Error *)
      exact False.
    + (* Success *)
      exact (ms = ms' /\ a = ms).
  - (* put_mem_state *)
    unfold MemPropT.
    intros ms_to_put ms res.
    destruct res as [[[[[[[oom_res] | [[ub_res] | [[err_res] | [ms' a]]]]]]]]] eqn:Hres.
    + (* OOM *)
      exact False.
    + (* UB *)
      exact False.
    + (* Error *)
      exact False.
    + exact (ms_to_put = ms').
Defined.

#[global] Instance MemPropT_RAISE_OOM {MemState : Type} : RAISE_OOM (MemPropT MemState).
Proof.
  split.
  - intros A msg.
    unfold MemPropT.
    intros ms res.
    destruct res as [[[[[[[oom_res] | [[ub_res] | [[err_res] | [ms' a]]]]]]]]] eqn:Hres.
    + (* OOM *)
      exact True. (* Don't care about particular error message, every OOM allowed. *)
    + (* UB *)
      exact False. (* Must run out of memory, can't UB *)
    + (* Error *)
      exact False. (* Must run out of memory, can't error *)
    + (* Success *)
      exact False. (* Must run out of memory *)
Defined.

#[global] Instance MemPropT_RAISE_ERROR {MemState : Type} : RAISE_ERROR (MemPropT MemState).
Proof.
  split.
  - intros A msg.
    unfold MemPropT.
    intros ms res.
    destruct res as [[[[[[[oom_res] | [[ub_res] | [[err_res] | [ms' a]]]]]]]]] eqn:Hres.
    + (* OOM *)
      exact False. (* Must error *)
    + (* UB *)
      exact False. (* Must error *)
    + (* Error *)
      exact True. (* Any error message is good *)
    + (* Success *)
      exact False. (* Must error. *)
Defined.

#[global] Instance MemPropT_RAISE_UB {MemState : Type} : RAISE_UB (MemPropT MemState).
Proof.
  split.
  intros A ub_msg.
    intros ms res.
    destruct res as [[[[[[[oom_res] | [[ub_res] | [[err_res] | [ms' a]]]]]]]]] eqn:Hres.
    + (* OOM *)
      exact False. (* Must UB *)
    + (* UB *)
      exact True. (* Any UB message is good *)
    + (* Error *)
      exact False. (* Must UB *)
    + (* Success *)
      exact False. (* Must UB *)
Defined.

Definition within_err_ub_oom_MemPropT {MemState} {A} (m : MemPropT MemState A) (pre : MemState) (e : err_ub_oom A) (post : MemState) : Prop :=
    m pre (a <- e;; ret (post, a)).

Lemma within_err_ub_oom_MemPropT_eq1Proper {MemState} {A} :
  Proper (eq1 ==> eq ==> eq ==> eq ==> iff) (@within_err_ub_oom_MemPropT MemState A).
Proof.
  unfold Proper, respectful.
  intros m1 m2 M x y X b1 b2 B z w Z.
  subst.

  unfold within_err_ub_oom_MemPropT.

  split; intros WITHIN;
    apply M in WITHIN; auto.
Qed.

#[global] Instance Within_err_ub_oom_MemPropT {MemState} : @Within (MemPropT MemState) _ err_ub_oom MemState MemState :=
  {
    within := @within_err_ub_oom_MemPropT MemState;
    within_eq1_Proper := @within_err_ub_oom_MemPropT_eq1Proper MemState;
  }.

#[global] Instance Within_ret_inv_MemPropT {MemState} {IMS : Inhabited MemState} :
  Within_ret_inv (MemPropT MemState) err_ub_oom MemState MemState.
Proof.
  split.
  - intros A x y H.
    cbn in *.
    firstorder.
  - intros A x.
    cbn.
    inv IMS.
    exists inhabitant. exists inhabitant.
    auto.
Defined.

#[global] Instance Within_ret_pre_post_inv_MemPropT {MemState} :
  Within_ret_pre_post_inv (MemPropT MemState) err_ub_oom MemState.
Proof.
  split.
  - intros A pre post x y H.
    cbn in *.
    firstorder.
  - intros A pre x.
    cbn.
    auto.
  - intros A pre1 post1 pre2 post2 x y z w H H0.
    cbn in *.
    tauto.
Defined.

#[global] Instance RaiseBindM_OOM_MemPropT {MemState} {IMS : Inhabited MemState} :
  RaiseBindM (MemPropT MemState) string (@raise_oom (MemPropT MemState) MemPropT_RAISE_OOM).
Proof.
  split.
  - intros A B f x.
    cbn.
    intros ms e.
    destruct e as [[[[[[[oom_e] | [[ub_e] | [[err_e] | [ms' b]]]]]]]]] eqn:He;
      firstorder.
  - intros A x y CONTRA.
    inv IMS.
    rename inhabitant into ms.
    specialize (CONTRA ms (raise_oom x)).
    cbn in *.
    tauto.
Defined.

#[global] Instance RaiseBindM_ERROR_MemPropT {MemState} {IMS : Inhabited MemState} :
  RaiseBindM (MemPropT MemState) string (@raise_error (MemPropT MemState) MemPropT_RAISE_ERROR).
Proof.
  split.
  - intros A B f x.
    cbn.
    intros ms e.
    destruct e as [[[[[[[oom_e] | [[ub_e] | [[err_e] | [ms' b]]]]]]]]] eqn:He;
      firstorder.
  - intros A x y CONTRA.
    inv IMS.
    rename inhabitant into ms.
    specialize (CONTRA ms (raise_error x)).
    cbn in *.
    tauto.
Defined.

#[global] Instance RaiseWithin_OOM_MemPropT {MemState} :
  RaiseWithin (MemPropT MemState) err_ub_oom MemState MemState string
    (@raise_oom (MemPropT MemState) MemPropT_RAISE_OOM).
Proof.
  split.
  intros X msg x.
  cbn.
  intros [ms [ms' CONTRA]].
  auto.
Defined.

#[global] Instance RaiseWithin_ERROR_MemPropT {MemState} :
  RaiseWithin (MemPropT MemState) err_ub_oom MemState MemState string
    (@raise_error (MemPropT MemState) MemPropT_RAISE_ERROR).
Proof.
  split.
  intros X msg x.
  cbn.
  intros [ms [ms' CONTRA]].
  auto.
Defined.

#[global] Instance RetWithin_UB_MemPropT {MemState} :
  RetWithin (MemPropT MemState) err_ub_oom MemState MemState string
    (@raise_ub err_ub_oom RAISE_UB_err_ub_oom_T).
Proof.
  split.
  intros X msg x.
  cbn.
  intros [ms [ms' CONTRA]].
  auto.
Defined.

#[global] Instance RetInvWithin_MemPropT {MemState} :
  RetInvWithin (MemPropT MemState) err_ub_oom MemState MemState.
Proof.
  split.
  intros X msg x.
  cbn.
  intros [ms [ms' CONTRA]].
  auto.
  break_match_hyp.
  break_match_hyp.
  break_match_hyp.
  break_match_hyp.
  break_match_hyp.
  break_match_hyp.
  break_match_hyp; inv CONTRA.
  break_match_hyp.
  break_match_hyp; inv CONTRA.
  break_match_hyp.
  break_match_hyp; inv CONTRA.
  destruct p.
  destruct CONTRA; subst.
  destruct_err_ub_oom msg; cbn in *; inv Heqe.
  auto.
Defined.

#[global] Instance DisjointRaiseWithin_UB_MemPropT {MemState} :
  DisjointRaiseWithin (MemPropT MemState) err_ub_oom MemState MemState string
    (@raise_ub err_ub_oom RAISE_UB_err_ub_oom_T) (@raise_oom (MemPropT MemState) MemPropT_RAISE_OOM).
Proof.
  split.
  intros X msg1 msg2.
  cbn.
  intros [ms [ms' CONTRA]].
  auto.
Defined.

#[global] Instance MemPropT_Eq1_ret_inv {MemState} `{IMS : Inhabited MemState} : Eq1_ret_inv (MemPropT MemState).
Proof.
  split.
  intros A x y EQ.
  cbn in EQ.
  red in EQ.
  red in EQ.
  inversion IMS.
  rename inhabitant into initial_memory_state.
  specialize (EQ initial_memory_state (ret (initial_memory_state, x))).
  cbn in *.
  tauto.
Defined.

Definition MemPropT_assert_pre {MemState} (assertion : Prop) : MemPropT MemState unit
  := fun ms ms'x =>
       match ms'x with
       | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent ms'x)))) =>
           match ms'x with
           | inl (OOM_message x) =>
               False
           | inr (inl (UB_message x)) =>
               ~ assertion
           | inr (inr (inl (ERR_message x))) =>
               False
           | inr (inr (inr (ms',x))) =>
               ms = ms' /\ assertion
           end
       end.
