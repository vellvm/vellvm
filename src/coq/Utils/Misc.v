From ITree Require Import
     ITree
     ITreeFacts
     Events.State
     Events.StateFacts
     InterpFacts
     Eq.Eq.

From Vellvm Require Import
     Utils.Tactics
     Utils.Util
     Syntax.LLVMAst
     Syntax.Traversal
     Syntax.AstLib
     Syntax.DynamicTypes
     Syntax.CFG
     Syntax.TypToDtyp
     Semantics.LLVMEvents
     Semantics.DynamicValues
     Semantics.TopLevel
     Semantics.InterpretationStack
     Handlers.Handlers
     Theory.Refinement
     Theory.DenotationTheory
     Theory.InterpreterCFG
     Theory.InterpreterMCFG.

From ExtLib Require Import
     Structures.Functor.

From Coq Require Import
     Strings.String
     Logic
     Morphisms
     Relations
     List
     Program
     ZArith.

Require Import Ceres.Ceres.
Import BinInt.
Import ListNotations.
Import ITree.Basics.Basics.Monads.

From Vellvm Require Import Util.
Require Import ITree.Events.State.

Require Import ITree.Eq.Eq.

From Vellvm Require Import Utils.AListFacts.

Import Traversal.

(* YZ: Should they be Opaque or simpl never? *)
Global Opaque denote_ocfg.
Global Opaque assoc.
Global Opaque denote_instr.
Global Opaque denote_terminator.
Global Opaque denote_phi.
Global Opaque denote_code.

Ltac typ_to_dtyp_simplify :=
  repeat
    (try rewrite typ_to_dtyp_I in *;
     try rewrite typ_to_dtyp_D in *;
     try rewrite typ_to_dtyp_D_array in *;
     try rewrite typ_to_dtyp_P in *).

From Paco Require Import paco.
Lemma eutt_mon {E R1 R2} (RR RR' : R1 -> R2 -> Prop)
      (LERR: RR <2= RR') :
  @eutt E R1 R2 RR <2= eutt RR'.
Proof.
  eapply eqit_mon; eauto.
Qed.

From Vellvm Require Import Syntax.Scope.

(* Enforcing these definitions to be unfolded systematically by [cbn] *)
Arguments endo /.
Arguments Endo_id /.
Arguments Endo_ident /.

Arguments find_block : simpl never.

From Vellvm Require Import Theory.SymbolicInterpreter.

Module eutt_Notations.
  Notation "t '======================' '======================' u '======================' '{' R '}'"
    := (eutt R t u)
         (only printing, at level 200,
          format "'//' '//' t '//' '======================' '======================' '//' u '//' '======================' '//' '{' R '}'"
         ).
End eutt_Notations.

Import D.
Module VIR_denotation_Notations.
  (* Notation "'ℐ' '(' t ')' g l m" := (interp_cfg_to_L3 _ t g l m) (only printing, at level 10). *)
  Notation "'global.' g 'local.' l 'memory.' m 'ℐ' t" :=
    (interp_cfg3 t g l m)
      (only printing, at level 10,
       format "'global.'  g '//' 'local.'  l '//' 'memory.'  m '//' 'ℐ'  t").

  Notation "⟦ c ⟧" := (denote_code c) (only printing, at level 10).
  Notation "⟦ i ⟧" := (denote_instr i) (only printing, at level 10).
  Notation "⟦ t ⟧" := (denote_terminator t) (only printing, at level 10).
  Notation "⟦ e ⟧" := (denote_exp None e) (only printing, at level 10).
  Notation "⟦ τ e ⟧" := (denote_exp (Some τ) e) (only printing, at level 10).
  Notation "x" := (translate exp_to_instr x) (only printing, at level 10).

  (* Should be part of the surface notations *)
  Notation "'call' x args" := ((IVoid _, INSTR_Call x args)) (at level 30, only printing).

  Notation "'λ' a b c d ',' k" := (fun '(a,(b,(c,d))) => k) (only printing, at level 0, format "'λ'  a  b  c  d ',' '[' '//' k ']'").

End VIR_denotation_Notations.

Import ITreeNotations.

From Vellvm Require Import InstrLemmas ExpLemmas.

Ltac vred_r :=
  let R := fresh
  in eutt_hide_rel_named R;
     let X := fresh
     in eutt_hide_left_named X; vred_C3;
        subst X; subst R.

Ltac vred_l :=
  let R := fresh
  in eutt_hide_rel_named R;
     let X := fresh
     in eutt_hide_right_named X; vred_C3;
        subst X; subst R.

Ltac vstep := vstep3.

Ltac tred := autorewrite with itree.

Arguments denote_exp : simpl never.
(* TODO: fmap (mk_block _ _ _ _ _) does not reduce, although we would like.
   However if I do the following to force the unfolding, then fmap always
   unfolds even in many other cases where we don't want it to do so.
   Solution?
 *)
(* Arguments fmap /. *)
(* Arguments Fmap_block /. *)
Arguments denote_phis : simpl never.
Arguments denote_code : simpl never.
Arguments denote_terminator : simpl never.
Arguments denote_block : simpl never.

From Vellvm Require Import
     Utils.TFor
     Utils.NoFailure
     Utils.PropT
.
Require Export ITree.Events.FailFacts.

From Vellvm Require Import Utils.PostConditions.

(** * Naming conventions for configurations and predicates over configurations *)

Notation memoryV := memory_stack.

(* Return state of a denoted and interpreted [cfg].
     Note the lack of local stack *)
Definition config_cfg
  := memoryV * (local_env * (global_env)).

(* Constructor to avoid having to worry about the nesting *)
Definition mk_config_cfg m l g: config_cfg := (m,(l,g)).

(* Return state of a denoted and interpreted [mcfg] *)
Definition config_mcfg
  := memoryV *
       (local_env * @Stack.stack (local_env) * (global_env)).

(* Return state and value of a denoted and interpreted (open) [cfg].
     Note the lack of local stack.
     Note that we may return a [block_id] alternatively to a [uvalue]
 *)
Definition config_cfg_T (T:Type): Type
  := memoryV * (local_env * (global_env * T)).
Definition config_res_cfg
  := config_cfg_T (block_id + uvalue).

(* Return state and value of a denoted and interpreted [mcfg]. *)
Definition config_mcfg_T (T:Type): Type
  := memoryV * (local_env * @Stack.stack (local_env) * (global_env * T)).
Definition config_res_mcfg :=
  config_mcfg_T uvalue.

(* -- Injections -- *)
(* The nested state transformers associate the products the other way,
     we therefore define injections of memory states and values into return
     types of computations.
 *)
Definition mk_config_cfg_T (T:Type) (v:T): config_cfg -> (config_cfg_T T)
  := fun '(m, (ρ, g)) => (m, (ρ, (g, v))).

Definition mk_config_mcfg_T (T:Type) (v:T): config_mcfg -> (config_mcfg_T T)
  := fun '(m, (ρ, g)) => (m, (ρ, (g, v))).


(* Facilities to refer to the type of relations used during the simulations
   of various pieces of denotions we manipulate.
   In particular, all relations we state assume success on the Helix side, and
   we will lift systematically these relations to the option type.
 *)

(** * Predicates  *)
(** Predicate on mcfg-level states *)
Definition Pred_mcfg: Type := config_mcfg -> Prop.
Definition Pred_mcfg_T (TV: Type): Type := config_mcfg_T TV -> Prop.
(** Predicate on cfg-level states *)
Definition Pred_cfg: Type := config_cfg -> Prop.
Definition Pred_cfg_T (TV: Type): Type := config_cfg_T TV -> Prop.

Require Import ExtLib.Data.Map.FMapAList.
Import SemNotations.

(** * Specifications for alloc *)

Lemma allocated_allocate_allocated (m1 m2 : memoryV) (d : dtyp) (a a' : Addr.addr) :
  allocated a m1 -> allocate m1 d = inr (m2, a') -> allocated a m2.
Proof.
  intros A AS.
  unfold allocate, allocated in *.
  destruct d; inv AS.
  all: repeat break_let; subst.
  all: unfold add_logical_block, add_logical_block_mem, add_to_frame in *.
  all: repeat break_match; inv Heqm1.
  all: apply member_add_ineq; [| assumption].
  all: unfold next_logical_key, next_logical_key_mem.
  all: simpl.
  all: intros C; rewrite C in A; contradict A.
  all: apply next_logical_key_fresh.
Qed.

Lemma allocate_allocated (m1 m2 : memoryV) (d : dtyp) (a : Addr.addr) :
  allocate m1 d = inr (m2, a) -> allocated a m2.
Proof.
  intros AS.
  unfold allocate, allocated in *.
  destruct d; inv AS.
  all: repeat break_let; subst.
  all: unfold add_logical_block, add_logical_block_mem, add_to_frame in *.
  all: repeat break_match; inv Heqm; inv Heqm0.
  all: apply member_add_eq.
Qed.

(** * MISC *)

Lemma eutt_trans : forall {E A} (R : A -> A -> Prop),
    Transitive R ->
    Transitive (eutt (E := E) R).
Proof.
  repeat intro.
  eapply eqit_trans in H1; [| apply H0].
  eapply eqit_mon with (RR := rcompose R R); eauto.
  intros.
  apply trans_rcompose; eauto.
Qed.

Lemma eutt_ret_inv_strong {E X Y} (R : X -> Y -> Prop) (x : X) (t : itree E Y) :
  eutt R (Ret x) t ->
  exists y, t ≈ Ret y /\ R x y.
Proof.
  intros EQ; punfold EQ.
  red in EQ.
  dependent induction EQ.
  - exists r2; split; auto.
    rewrite itree_eta, <-x; reflexivity.
  - edestruct IHEQ as (y & EQ1 & HR); auto.
    exists y; split; auto.
    now rewrite itree_eta, <- x, tau_eutt.
Qed.

Lemma eutt_ret_inv_strong' {E X Y} (R : X -> Y -> Prop) (t : itree E X) (y : Y) :
  eutt R t (Ret y) ->
  exists x, t ≈ Ret x /\ R x y.
Proof.
  intros EQ; punfold EQ.
  red in EQ.
  dependent induction EQ.
  - exists r1; split; auto.
    rewrite itree_eta, <-x; reflexivity.
  - edestruct IHEQ as (?x & EQ1 & HR); auto.
    exists x0; split; auto.
    now rewrite itree_eta, <- x, tau_eutt.
Qed.

Lemma typ_to_dtyp_void s : typ_to_dtyp s TYPE_Void = DTYPE_Void.
Proof.
  intros; rewrite typ_to_dtyp_equation; reflexivity.
Qed.

Lemma option_rel_trans : forall {A} (R : A -> A -> Prop),
    Transitive R ->
    Transitive (option_rel R).
Proof.
  repeat intro.
  cbv in *.
  repeat break_match; intuition.
  subst.
  eapply H; eauto.
Qed.

(* Vellvm invariant:
   a computation starting from a fresh frame:
   - always leads to memory where [free_frame] succeeds
   - the resulting memory still contains all initially allocated addresses
   - the [free_frame] operation itself only deallocates, it does not change
   the content of what remains.

   TODO: before proving, generalize over arbitrary trees rather than specifically
   denotations of ocfgs.
 *)
Lemma memory_scoping_cfg : forall ocfg b g ρ m,
    interp_cfg3 (⟦ ocfg ⟧bs b) g ρ (push_fresh_frame m)
      ⤳ (fun '(m',_) => exists m'',
             free_frame m' = inr m'' /\
               (forall a, allocated a m -> allocated a m'') /\
               (forall a τ v, read m'' a τ = inr v -> read m' a τ = inr v)).
Admitted.

#[local] Definition mcfg_ctx fundefs :
  forall T : Type,
    CallE T
    -> itree (CallE +' ExternalCallE +' IntrinsicE +' LLVMGEnvE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' PickE +' UBE +' DebugE +' FailureE) T :=

  (fun (T : Type) (call : CallE T) =>
    match call in (CallE T0) return (itree (CallE +' ExternalCallE +' IntrinsicE +' LLVMGEnvE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' PickE +' UBE +' DebugE +' FailureE) T0) with
    | LLVMEvents.Call dt0 fv args0 =>
        dfv <- concretize_or_pick fv True;;
        match lookup_defn dfv fundefs with
        | Some f_den => f_den args0
        | None =>
            dargs <- map_monad (fun uv : uvalue => pickUnique uv) args0;;
            Functor.fmap dvalue_to_uvalue (trigger (ExternalCall dt0 fv dargs))
        end
    end).

Lemma memory_scoping_mcfg : forall ocfg b g ρ m ctx,
    interp_mcfg3 (interp_mrec (mcfg_ctx ctx) (translate instr_to_L0' (⟦ ocfg ⟧bs b))) g ρ (push_fresh_frame m)
      ⤳ (fun '(m',(ρ',_)) =>
           exists (m'' : memory_stack),
             snd ρ' = snd ρ /\
               free_frame m' = inr m'' /\
               (forall a, allocated a m -> allocated a m'') /\
               (forall a τ v, read m'' a τ = inr v -> read m' a τ = inr v)).
Admitted.

Lemma has_post_enrich_eutt {E X Y RR Q1 Q2} :
  forall (t : itree E X) (u : itree E Y),
    eutt RR t u ->
    t ⤳ Q1 ->
    u ⤳ Q2 ->
    eutt (fun x y => RR x y /\ Q1 x /\ Q2 y) t u.
Proof.
  intros.
  rewrite <- bind_ret_r.
  pose proof bind_ret_r u as EQ; rewrite <- EQ; clear EQ.
  eapply eutt_post_bind_gen; eauto.
  intros.
  apply eutt_Ret; intuition.
Qed.

(* Auxilliary lemma to enrich an equation with an invariant over the right computation *)
Lemma has_post_enrich_eutt_r {E X Y RR Q} :
  forall (t : itree E X) (u : itree E Y),
    eutt RR t u ->
    u ⤳ Q ->
    eutt (fun x y => RR x y /\ Q y) t u.
Proof.
  intros.
  rewrite <- bind_ret_r.
  pose proof bind_ret_r u as EQ; rewrite <- EQ; clear EQ.
  eapply eutt_post_bind_gen; eauto.
  apply has_post_True.
  intros.
  apply eutt_Ret; intuition.
Qed.

(* Auxilliary lemma to enrich an equation with an invariant over the left computation *)
Lemma has_post_enrich_eutt_l {E X Y RR Q} :
  forall (t : itree E X) (u : itree E Y),
    eutt RR t u ->
    t ⤳ Q ->
    eutt (fun x y => RR x y /\ Q x) t u.
Proof.
  intros.
  rewrite <- bind_ret_r.
  pose proof bind_ret_r u as EQ; rewrite <- EQ; clear EQ.
  eapply eutt_post_bind_gen; eauto.
  apply has_post_True.
  intros.
  apply eutt_Ret; intuition.
Qed.


(** * [interp_local_stack] theory *)
Lemma interp_local_stack_tau:
  forall (k v map : Type) (M : Maps.Map k v map) (SK : CeresSerialize.Serialize k) (E F G : Type -> Type) (H : FailureE -< E +' F +' G) (R : Type) (l : map * stack) (t : itree (E +' F +' (LocalE k v +' StackE k v) +' G) R),
    interp_local_stack (Tau t) l ≅ Tau (interp_local_stack t l).
Proof.
  intros.
  unfold interp_local_stack at 1.
  rewrite interp_state_tau.
  reflexivity.
Qed.


(** * [interp_mcfg3] theory *)

Lemma interp3_ret : forall (R : Type) (g : global_env) (l : local_env * stack) (m : memoryV) (x : R), ℑs3 (Ret x) g l m ≅ Ret3 g l m x.
Proof.
  intros; unfold ℑs3.
  rewrite interp_intrinsics_ret, interp_global_ret, interp_local_stack_ret, interp_memory_ret.
  reflexivity.
Qed.

Lemma interp3_tau : forall R (t : itree L0 R) g l m,
    interp_mcfg3 (Tau t) g l m ≅ Tau (interp_mcfg3 t g l m).
Proof.
  intros; unfold ℑs3.
  rewrite interp_intrinsics_Tau, interp_global_Tau, interp_local_stack_tau, interp_memory_Tau.
  reflexivity.
Qed.

Lemma interp_cfg3_tau : forall R (t : itree _ R) g l m,
    interp_cfg3 (Tau t) g l m ≅ Tau (interp_cfg3 t g l m).
Proof.
  intros; unfold ℑ3.
  rewrite interp_intrinsics_Tau, interp_global_Tau, interp_local_Tau, interp_memory_Tau.
  reflexivity.
Qed.

Lemma interp3_map_monad {A B} g l m (xs : list A) (ts : A -> itree _ B) :
  ℑs3 (map_monad ts xs) g l m ≈
    map_monad (m := Monads.stateT _ (Monads.stateT _ (Monads.stateT _ (itree _))))
    (fun a => ℑs3 (ts a)) xs g l m.
Proof.
  intros; revert g l m; induction xs as [| a xs IH]; simpl; intros.
  - rewrite interp3_ret; reflexivity.
  - rewrite interp3_bind.
    apply eutt_eq_bind; intros (? & ? & ? & ?); cbn.
    rewrite interp3_bind, IH.
    apply eutt_eq_bind; intros (? & ? & ? & ?); cbn.
    rewrite interp3_ret; reflexivity.
Qed.

Instance eq_itree_interp3:
  forall T : Type, Proper (eq_itree eq ==> eq ==> eq ==> eq ==> eq_itree eq) (@interp_mcfg3 T).
Proof.
  repeat intro.
  unfold ℑs3.
  subst; rewrite H.
  reflexivity.
Qed.

Instance eq_itree_interp_cfg3:
  forall T : Type, Proper (eq_itree eq ==> eq ==> eq ==> eq ==> eq_itree eq) (@interp_cfg3 T).
Proof.
  repeat intro.
  unfold ℑ3.
  subst; rewrite H.
  reflexivity.
Qed.

Lemma interp3_MemPush: forall g l m,
    ℑs3 (trigger MemPush) g l m ≈ Ret3 g l (push_fresh_frame m) tt.
Proof.
  intros.
  unfold ℑs3.
  MCFGTactics.go.
  rewrite interp_memory_trigger.
  cbn.
  MCFGTactics.go.
  reflexivity.
Qed.

Lemma interp3_StackPush: forall g a sbot m s,
    ℑs3 (trigger (StackPush s)) g (a,sbot) m ≈
      Ret3 g (fold_right (fun '(x, dv) => alist_add x dv) [] s, a :: sbot) m tt.
Proof.
  intros.
  unfold ℑs3.
  MCFGTactics.go.
  reflexivity.
Qed.

Lemma interp3_GR : forall id g l m v,
  Maps.lookup id g = Some v ->
  interp_mcfg3 (trigger (GlobalRead id)) g l m ≈ Ret (m,(l,(g,v))).
Proof.
  intros * LU.
  unfold interp_mcfg3.
  rewrite interp_intrinsics_trigger.
  cbn.
  unfold Intrinsics.F_trigger.
  rewrite interp_global_trigger.
  cbn in *; rewrite LU.
  rewrite interp_local_stack_ret, interp_memory_ret.
  reflexivity.
Qed.

Lemma interp3_denote_exp_double : forall t g l m,
    interp_mcfg3
      (translate exp_to_L0
                 (denote_exp (Some (DTYPE_Double))
                             (EXP_Double t)))
      g l m
    ≈
    Ret (m, (l, (g, UVALUE_Double t))).
Proof.
  intros; unfold denote_exp; cbn.
  rewrite translate_ret, interp3_ret.
  reflexivity.
Qed.

Lemma interp3_denote_exp_i64 : forall t g l m,
    interp_mcfg3
      (translate exp_to_L0
                 (denote_exp (Some (DTYPE_I 64))
                             (EXP_Integer (unsigned t))))
       g l m
    ≈
    Ret (m, (l, (g, UVALUE_I64 (DynamicValues.Int64.repr (unsigned t))))).
Proof.
  intros; unfold denote_exp; cbn.
  rewrite translate_ret, interp3_ret.
  reflexivity.
Qed.

Lemma interp3_concretize_or_pick_concrete :
  forall (uv : uvalue) (dv : dvalue) P g ρ m,
    is_concrete uv ->
    uvalue_to_dvalue uv = inr dv ->
    interp_mcfg3 (concretize_or_pick uv P) g ρ m ≈ Ret (m, (ρ, (g, dv))).
Proof.
  intros uv dv P g ρ m CONC CONV.
  unfold concretize_or_pick.
  rewrite CONC.
  cbn.
  unfold lift_err.
  now rewrite CONV, interp3_ret.
Qed.

Lemma interp3_concretize_or_pick_concrete_exists :
  forall (uv : uvalue) P g ρ m,
    is_concrete uv ->
    exists dv, uvalue_to_dvalue uv = inr dv /\
          interp_mcfg3 (concretize_or_pick uv P) g ρ m ≈ Ret (m, (ρ, (g, dv))).
Proof.
  intros uv P g ρ m CONC.
  pose proof is_concrete_uvalue_to_dvalue uv CONC as (dv & CONV).
  exists dv.
  split; auto.
  now apply interp3_concretize_or_pick_concrete.
Qed.

Lemma interp3_store:
  forall (m m' : memoryV) (val : dvalue) (a : addr) g l,
    write m a val = inr m' ->
    interp_mcfg3 (trigger (Store (DVALUE_Addr a) val)) g l m ≈ Ret (m', (l, (g, ()))).
Proof.
  intros m m' val a g l WRITE.
  unfold interp_mcfg3.
  rewrite interp_intrinsics_trigger.
  cbn.
  unfold Intrinsics.F_trigger.
  rewrite interp_global_trigger.
  rewrite subevent_subevent.
  cbn.
  rewrite interp_local_stack_bind, interp_local_stack_trigger.
  cbn; rewrite subevent_subevent.
  rewrite Eq.bind_bind.
  rewrite interp_memory_bind, interp_memory_store; eauto.
  cbn; rewrite Eq.bind_ret_l.
  rewrite interp_memory_bind, interp_memory_ret, Eq.bind_ret_l.
  rewrite interp_local_stack_ret, interp_memory_ret.
  reflexivity.
Qed.

(** * [interp_mrec] theory *)

Lemma denote_mcfg_unfold_in : forall G τ addr args f,
    lookup_defn (DVALUE_Addr addr) G = Some f ->
    denote_mcfg G τ (UVALUE_Addr addr) args ≈
      interp_mrec (mcfg_ctx G) (f args).
Proof.
  intros * LU.
  unfold denote_mcfg at 1.
  rewrite RecursionFacts.mrec_as_interp.
  simpl bind. rewrite interp_bind.
  cbn.
  rewrite interp_ret, bind_ret_l.
  rewrite LU.
  rewrite <- RecursionFacts.interp_mrec_as_interp.
  reflexivity.
Qed.

Lemma interp_mrec_ret :
  forall (D E : Type -> Type) (ctx : forall T : Type, D T -> itree (D +' E) T) (U : Type) (u : U),
    interp_mrec ctx (Ret u) ≅ (Ret u).
Proof.
  intros.
  rewrite unfold_interp_mrec; reflexivity.
Qed.

Lemma interp_mrec_tau : forall D E (ctx : D ~> itree (D +' E)) R (t : itree _ R),
    interp_mrec ctx (Tau t) ≅ Tau (interp_mrec ctx t).
Proof.
  intros.
  now rewrite unfold_interp_mrec.
Qed.

#[global] Instance interp_mrec_eutt {D E}
  (ctx : D ~> itree (D +' E)) T :
  Proper (eutt eq ==> eutt eq) (interp_mrec ctx (T := T)).
Proof.
  repeat intro.
  eapply Proper_interp_mrec; auto.
  intros ??.
  reflexivity.
Qed.

Lemma interp3_call_void : forall G n τ f fdfn args g s m addr,
    prefix "llvm." f = false ->
    Maps.lookup (Name f) g = Some (DVALUE_Addr addr) ->
    lookup_defn (DVALUE_Addr addr) G = Some fdfn ->

    ℑs3 (interp_mrec (mcfg_ctx G)
           (Interp.translate instr_to_L0'
              ⟦(IVoid n, INSTR_Call (τ, EXP_Ident (ID_Global (Name f))) args) ⟧i)) g s m
      ≈
      '(m,(s,(g,vs))) <- ℑs3 (interp_mrec (mcfg_ctx G)
                               (Interp.translate instr_to_L0'
                                  (map_monad (fun '(t, op) => Interp.translate exp_to_instr ⟦ op at t ⟧e) args))) g s m
    ;;

    '(m,(s,(g,v))) <- ℑs3 (interp_mrec (mcfg_ctx G) (fdfn vs)) g s m;;
    Ret (m,(s,(g,tt))).
Proof.
  intros * PRE LU LUD.
  Transparent denote_instr.
  cbn.
  rewrite translate_bind, interp_mrec_bind, interp3_bind.
  (* Expressions are pure, lifted by induction over map_monad *)
  apply eutt_clo_bind with
    (UU := fun '(m1,(s1,(g1,v))) m2 =>
             (m1,(s1,(g1,v))) = m2 /\ m1 = m /\ s1 = s /\ g1 = g).
  admit.
  intros (m1,(s1,(g1,v1))) (m2,(s2,(g2,v2))) (EQ & -> & -> & ->).
  symmetry in EQ; inv EQ.
  rewrite PRE.
  (* repeat break_and. *)
  rewrite bind_bind.
  rewrite translate_bind, interp_mrec_bind, interp3_bind.
  Transparent denote_exp.
  unfold denote_exp.
  cbn.
  rewrite bind_trigger.
  rewrite translate_vis.
  rewrite translate_vis.
  rewrite translate_vis.
  cbn.
  rewrite <- bind_trigger.
  rewrite interp_mrec_bind.
  rewrite interp_mrec_trigger.
  cbn.
  rewrite interp3_bind.
  match goal with
    |- context[ℑs3 ?e] =>
      let eqn := fresh in
      assert (eqn:e = trigger (@GlobalRead raw_id dvalue (Name f))) by reflexivity;
      rewrite eqn; clear eqn
  end.
  rewrite interp3_GR; [| apply LU].
  rewrite bind_ret_l.
  rewrite 3translate_ret.
  rewrite interp_mrec_ret, interp3_ret, bind_ret_l.

  rewrite !translate_bind, interp_mrec_bind, interp3_bind.
  rewrite translate_trigger, interp_mrec_trigger.
  cbn.
  rewrite mrec_as_interp.
  cbn.
  rewrite bind_ret_l.
  rewrite LUD.
  cbn.
  rewrite <- RecursionFacts.interp_mrec_as_interp.

  apply eutt_eq_bind.
  intros (? & ? & ? & ?).
  rewrite translate_ret, interp_mrec_ret, interp3_ret.
  reflexivity.
  Opaque denote_instr.
  Opaque denote_exp.

Admitted.

(* Weirdly specific... Shouldn't we lift results that do not depend on [interp_mrec]? *)
Lemma denote_mcfg_ID_Global :
  forall ctx (g : global_env) s (m : memoryV) id (τ : dtyp) (ptr : Addr.addr),
    alist_find id g = Some (DVALUE_Addr ptr) ->

    ℑs3 (interp_mrec ctx
           (Interp.translate instr_to_L0'
              (Interp.translate exp_to_instr (denote_exp (Some τ) (EXP_Ident (ID_Global id)))))) g s m
      ≈
      Ret3 g s m (UVALUE_Addr ptr)
.
Proof.
  intros * LU.
  Transparent denote_exp.
  unfold denote_exp.
  cbn.
  rewrite 3translate_bind, interp_mrec_bind, interp3_bind.
  rewrite !translate_trigger.
  cbn.
  rewrite interp_mrec_trigger.
  cbn.

  match goal with
    |- context[ℑs3 ?e] =>
      let eqn := fresh in
      assert (eqn:e = trigger (@GlobalRead raw_id dvalue id)) by reflexivity;
      rewrite eqn; clear eqn
  end.

  rewrite interp3_GR; [| apply LU].
  rewrite bind_ret_l.
  rewrite !translate_ret,interp_mrec_ret,interp3_ret.
  reflexivity.
Qed.

(** * [allocate_globals] theory *)

Import AlistNotations.
Definition global_ptr_exists fnname : Pred_mcfg :=
  fun '(mem_llvm, (ρ,g)) => exists mf, g @ fnname = Some (DVALUE_Addr mf).

Definition global_ptr_existsT {T} fnname : Pred_mcfg_T T :=
  fun '(mem_llvm, (ρ,(g,_))) => exists mf, g @ fnname = Some (DVALUE_Addr mf).

Record gs_wf (gs : list (global dtyp)) : Prop :=
  {
    gs_wf_nodup  : NoDup (List.map g_ident gs);
    gs_wf_novoid : Forall (fun x => non_void (g_typ x)) gs
  }.

Definition global_is_init (g : global_env) (m : memoryV) (glob : global dtyp) : Prop :=
  exists mf, g @ (g_ident glob) = Some (DVALUE_Addr mf) /\ allocated mf m.

Definition globals_are_uniquely_init (g : global_env) (globs : list (global dtyp)) : Prop :=
  forall glob glob', In glob globs -> In glob' globs -> g_ident glob <> g_ident glob' ->
                g @ (g_ident glob) <> g @ (g_ident glob').

(* TODO
   [gs_init_fresh] should be replaced by a predicate specifying
   the current domain of [g], and take into account the declarations
   that have already be allocated
 *)
Record init_globals (globs : list (global dtyp)) (g : global_env) (m : memoryV) : Prop :=
  {
    gs_init          : Forall (global_is_init g m) globs;
    gs_init_distinct : globals_are_uniquely_init g globs;
    gs_init_fresh    : forall id, ~ In id (map g_ident globs) -> g @ id = None
  }
.

Definition init_globalsT {T} globs : Pred_mcfg_T T :=
  fun '(m, (_,(g,_))) => init_globals globs g m.

(*   In (dc_name d) (map dc_name IntrinsicsDefinitions.defined_intrinsics_decls) *)
(*   \/  *)
(* . *)

(* exists mf, g @ (g_ident glob) = Some (DVALUE_Addr mf) *)
(*         /\ allocated mf m. *)


(* Record init_decls (decls : list (declaration dtyp)) *)
(*   (g : global_env) (m : memoryV) : Prop := *)
(*   { *)
(*     gs_init_decls          : Forall (global_is_init g m) globs; *)
(*     gs_init_distinct_decls : globals_are_uniquely_init g globs; *)
(*     gs_init_fresh_decls    : forall id, ~ In id (map g_ident globs) -> g @ id = None *)
(*   } *)
(* . *)


(* Lemma allocate_declaration_spec : forall (d : declaration dtyp), *)
(*     allocate_declaration d ⤳  *)


(* One proper round of global initialization preserves the invariant *)
Lemma gs_init_extend :
  forall g m m' τ a (glob : global dtyp) globs v,
    ~ In (g_ident glob) (map g_ident globs) ->
    init_globals globs g m ->
    allocate m τ = inr (m', a) ->
    Forall (global_is_init (alist_add (g_ident glob) v g) m') globs.
Proof.
  intros * NIN [FA _ FR] AS.
  rewrite Forall_forall in FA.
  apply Forall_forall.
  intros * IN; apply FA in IN as (? & EQ & AL).
  eexists.
  split.
  - rewrite alist_find_neq.
    apply EQ.
    intros abs.
    apply FR in NIN.
    rewrite <- abs, EQ in NIN.
    inv NIN.
  - eapply allocated_allocate_allocated; eauto.
Qed.

Lemma allocate_global_spec : forall (glob : global dtyp) globs g s m,
    non_void (g_typ glob) ->
    ~ In (g_ident glob) (map g_ident globs) ->
    init_globals globs g m ->
    ℑs3 (allocate_global glob) g s m ⤳ init_globalsT (glob :: globs).
Proof.
  intros * NV FR INV; pose proof INV as [].
  unfold allocate_global.
  cbn.
  rewrite interp3_bind.
  edestruct interp3_alloca as (? & mf & ? & EQ); [eauto |].
  rewrite EQ; clear EQ.
  cbn; rewrite bind_ret_l.
  rewrite interp3_GW.
  apply eutt_Ret.
  cbn.
  split.
  - apply Forall_cons; auto.
    2: eapply gs_init_extend; eauto.
    eexists.
    split.
    rewrite alist_find_add_eq; reflexivity.
    eapply allocate_allocated; eauto.
  - intros ? ? IN IN' NEQ.
    destruct IN as [<- | IN].
    + rewrite alist_find_add_eq.
      destruct IN' as [<- | IN'].
      * now contradiction NEQ.
      * rewrite alist_find_neq; auto.
        eapply Forall_forall in gs_init0; [| apply IN'].
        destruct gs_init0 as (mf' & EQ & AL).
        unfold global_id in *; rewrite EQ.
        intros abs; inv abs.
        apply allocate_correct, was_fresh in H.
        intuition.
    + destruct IN' as [<- | IN'].
      * rewrite alist_find_neq; auto.
        rewrite alist_find_add_eq.
        eapply Forall_forall in gs_init0; [| apply IN].
        destruct gs_init0 as (mf' & EQ & AL).
        unfold global_id in *; rewrite EQ.
        intros abs; inv abs.
        apply allocate_correct, was_fresh in H.
        intuition.
      * rewrite 2 alist_find_neq; auto.
        all:intros abs; apply FR; rewrite <- abs; now apply in_map.
  - intros * NIN.
    destruct (raw_id_eq_dec id (g_ident glob)).
    + subst.
      exfalso; apply NIN; left; reflexivity.
    + rewrite alist_find_neq; auto.
      apply gs_init_fresh0.
      intros abs; apply NIN; right; auto.
Qed.


Lemma allocate_globals_cons :
  forall g gs,
    allocate_globals (g :: gs) ≈ allocate_global g;; allocate_globals gs.
Proof.
  intros; cbn.
  rewrite !bind_bind.
  apply eutt_eq_bind; intros ?.
  apply eutt_eq_bind; intros ?.
  rewrite !bind_bind.
  apply eutt_eq_bind; intros ?.
  rewrite bind_ret_l.
  reflexivity.
Qed.

Lemma init_globals_shuffle_snoc : forall glob globs g m,
      init_globals  (glob :: globs) g m ->
      init_globals (globs ++ [glob]) g m.
Proof.
  intros * [].
  constructor.
  - apply Forall_app; apply List.Forall_cons_iff in gs_init0 as [? ?].
    split; auto.
  - intros ? ? IN IN' NEQ.
    apply in_app_or in IN, IN'.
    apply gs_init_distinct0; auto.
    destruct IN as [IN | IN]; [right; auto| destruct IN as [<- |[]]; left; reflexivity].
    destruct IN' as [IN' | IN']; [right; auto| destruct IN' as [<- |[]]; left; reflexivity].
  - intros ? NIN.
    apply gs_init_fresh0; auto.
    intros abs; apply NIN; destruct abs as [<- | IN].
    rewrite map_app; apply in_or_app; right; left; reflexivity.
    rewrite map_app; apply in_or_app; now left.
Qed.

Lemma init_globalsT_shuffle_snoc : forall {T} glob globs cfn,
      init_globalsT (T := T) (glob :: globs) cfn ->
      init_globalsT (globs ++ [glob]) cfn.
Proof.
  intros ??? [m' [ρ' [g' ?]]]. apply init_globals_shuffle_snoc.
Qed.

Lemma init_globals_shuffle_snoc' : forall glob globs g m,
      init_globals (globs ++ [glob]) g m ->
      init_globals (glob :: globs) g m.
Proof.
  intros * [].
  constructor.
  - apply Forall_app in gs_init0 as [? ?]; apply List.Forall_cons_iff.
    inv H0; split; auto.
  - intros ? ? IN IN' NEQ.
    apply gs_init_distinct0; auto.
    apply in_or_app; destruct IN as [<- | IN]; auto; right; left; auto.
    apply in_or_app; destruct IN' as [<- | IN']; auto; right; left; auto.
  - intros ? NIN.
    apply gs_init_fresh0; auto.
    intros abs; apply NIN. rewrite map_app in abs.
    apply in_app_or in abs.
    cbn.
    destruct abs; auto.
    destruct H; auto.
    contradiction H.
Qed.

Lemma init_globalsT_shuffle_snoc' : forall {T} glob globs cfn,
      init_globalsT (globs ++ [glob]) cfn ->
      init_globalsT (T := T) (glob :: globs) cfn.
Proof.
  intros ??? [m' [ρ' [g' ?]]]. apply init_globals_shuffle_snoc'.
Qed.

Lemma allocate_globals_spec_gen :
  forall (globs_todo globs_done : list (global dtyp)) (g : global_env) s m,
    NoDup (List.map g_ident globs_todo) ->
    Forall (fun x => non_void (g_typ x)) globs_todo ->
    (forall glob, In glob globs_todo -> ~ In (g_ident glob) (map g_ident globs_done)) ->
    init_globals globs_done g m ->
    ℑs3 (allocate_globals globs_todo) g s m ⤳ init_globalsT (globs_todo ++ globs_done).
Proof.
  induction globs_todo as [| glob globs_todo IH]; intros * ND NV FRESH WF.
  - cbn.
    repeat rewrite ?interp3_bind, ?interp3_ret, ?bind_ret_l.
    now apply eutt_Ret.
  - rewrite allocate_globals_cons, interp3_bind.
    eapply has_post_bind_strong
      with (S := init_globalsT (glob :: globs_done)).
    + apply allocate_global_spec.
      * rewrite Forall_forall in NV; apply NV; left; reflexivity.
      * apply FRESH; left; reflexivity.
      * auto.
    + intros [m' [ρ' [g' []]]] HInit.
      apply has_post_weaken with (P := init_globalsT ((globs_todo ++ globs_done) ++ [glob])).
      2: intros; now cbn; apply init_globalsT_shuffle_snoc'.
      rewrite <- app_assoc.
      apply IH.
      * apply NoDup_cons_iff in ND; apply ND.
      * inv NV; auto.
      * intros ? IN abs.
        rewrite map_app in abs; apply in_app_or in abs as [abs | EQ].
        eapply FRESH; [right; eauto | auto].
        destruct EQ as [EQ | []].
        clear -ND EQ IN.
        cbn in ND.
        inv ND.
        apply H1; rewrite EQ.
        now apply in_map.
      * now apply init_globals_shuffle_snoc.
Qed.

Lemma allocate_globals_spec :
  forall (globs : list (global dtyp)) (g : global_env) (Ig : global_env -> Prop) s m,
    (forall g, Ig g -> init_globals [] g m) ->
    Ig g ->
    NoDup (List.map g_ident globs) ->
    Forall (fun x => non_void (g_typ x)) globs ->
    ℑs3 (allocate_globals globs) g s m ⤳ init_globalsT globs.
Proof.
  intros.
  pose proof app_nil_end globs as EQ.
  rewrite EQ at 2.
  apply allocate_globals_spec_gen; auto.
Qed.

Require Import LibHyps.LibHyps.

Ltac eqitree_of_eq h :=
  match type of h with
  | ?t = ?u =>
      let name := fresh in
      assert (name: t ≅ u) by (subst; reflexivity); clear h; rename name into h
  end.
Tactic Notation "eqi_of_eq" ident(h) := eqitree_of_eq h.

Ltac eqitree_of_oeq h :=
  match type of h with
  | ?t = ?u =>
      let name := fresh in
      assert (name: {| _observe := t |} ≅ {| _observe := u |}) by (rewrite h; reflexivity); clear h; rename name into h
  end.
Tactic Notation "eqi_of_oeq" ident(h) := eqitree_of_oeq h.

Lemma interp_trigger_eqit :
  forall {E F : Type -> Type} {R : Type} (f : forall T : Type, E T -> itree F T) (e : E R),
    interp f (ITree.trigger e) ≅ x <- f R e;; Tau (Ret x).
Proof.
  intros.
  unfold ITree.trigger. rewrite interp_vis.
  setoid_rewrite interp_ret.
  reflexivity.
Qed.

Section PARAMS.
  Variable (E F : Type -> Type).
  Context `{FailureE -< F}.
  Notation Eff := (E +' IntrinsicE +' F).

  Lemma interp_intrinsics_trigger_eqit:
    forall X (e : Eff X),
      interp_intrinsics (ITree.trigger e) ≅ x <- interp_intrinsics_h e;; Tau (Ret x).
  Proof.
    intros *.
    unfold interp_intrinsics.
    rewrite interp_trigger_eqit.
    reflexivity.
  Qed.

  #[global] Instance euttge_interp_intrinsics {R} :
    Proper (euttge Logic.eq ==> euttge Logic.eq)
      (@interp_intrinsics E F _ R).
  Proof.
    do 2 red; intros * EQ.
    unfold interp_intrinsics.
    rewrite EQ; reflexivity.
  Qed.

End PARAMS.

Lemma interp_cfg3_vis_eqit :
  forall T R (e : instr_E T) (k : T -> itree instr_E R) g l m,
    ℑ3 (Vis e k) g l m ≅ '(m, (l, (g, x))) <- ℑ3 (trigger e) g l m;; ℑ3 (k x) g l m.
Proof.
  intros.
  unfold ℑ3.
  rewrite interp_intrinsics_vis_eqit.
  rewrite interp_global_bind, interp_local_bind, interp_memory_bind.
  rewrite interp_intrinsics_trigger_eqit.
  rewrite interp_global_bind, interp_local_bind, interp_memory_bind.
  rewrite bind_bind.
  eapply eq_itree_clo_bind; [reflexivity |].
  intros x y <-; destruct x as [? [? [ ? ?]]].
  rewrite ?interp_global_Tau, ?interp_local_Tau, ?interp_memory_Tau.
  rewrite bind_tau, eqitree_Tau.
  rewrite interp_global_ret, interp_local_ret, interp_memory_ret, bind_ret_l.
  reflexivity.
Qed.

(* Lemma interp_intrinsics_ret_inv : *)
(*   forall {E F} `{FailureE -< F} [R] (t : itree (E +' _ +' F) R) (r : R), *)
(*     interp_intrinsics t ≅ Ret r -> t ≅ Ret r. *)
(* Proof. *)
(*   intros * EQ. *)
(*   unfold interp_intrinsics in EQ. *)
(*   rewrite unfold_interp in EQ. *)
(*   rewrite (itree_eta t). *)
(*   destruct (observe t) eqn:eqo; cbn in EQ; punfold EQ. *)
(*   red in EQ; cbn in EQ; inv EQ; inv CHECK. *)
(*   red in EQ; cbn in EQ; dependent destruction EQ. inv CHECK. *)


Notation E := (ExternalCallE +' PickE +' UBE +' DebugE +' FailureE).
Definition lenv := (local_env * @stack local_env).

Definition handle_all_intrinsics {E} `{FailureE -< E} :
  IntrinsicE ~> stateT memoryV (itree E) :=
  fun X '(Intrinsic _ fname args) m =>
    match assoc fname defs_assoc with
    | Some f => match f args with
               | inl msg => raise msg
               | inr result => Ret1 m result
               end
    | None =>
        if string_dec fname "llvm.memcpy.p0i8.p0i8.i32" then
          match handle_memcpy args (fst m) with
          | inl err => raise err
          | inr m' => Ret1 (m', snd m) DVALUE_None
          end
        else
          raise ("Unknown intrinsic: " ++ fname)
    end.
Arguments handle_all_intrinsics {_ _} [_].

Definition handler3 : L0 ~> stateT global_env (stateT lenv (stateT memoryV (itree E))) :=
  fun T e g l m =>
    match e with
    | inl1 e =>
        v <- trigger e;; Ret3 g l m v
    | inr1 (inl1 e) =>
        '(m,v) <- handle_all_intrinsics e m;; Ret3 g l m v
    | inr1 (inr1 (inl1 e)) =>
        '(g,v) <- handle_global e g;; Ret3 g l m v
    | inr1 (inr1 (inr1 (inl1 (inl1 e)))) =>
        '(l',v) <- handle_local e (fst l);; Ret3 g (l', snd l) m v
    | inr1 (inr1 (inr1 (inl1 (inr1 e)))) =>
        '(l,v) <- handle_stack e l;; Ret3 g l m v
    | inr1 (inr1 (inr1 (inr1 (inl1 e)))) =>
        '(m,v) <- handle_memory e m;; Ret3 g l m v
    | inr1 (inr1 (inr1 (inr1 (inr1 e)))) =>
        v <- trigger e;; Ret3 g l m v
    end.
Arguments handler3 [_].

Definition handler_cfg3 : instr_E ~> stateT global_env (stateT local_env (stateT memoryV (itree (CallE +' PickE +' UBE +' DebugE +' FailureE)))) :=
  fun T e g l m =>
    match e with
    | inl1 e =>
        v <- trigger e;; Ret3 g l m v
    | inr1 (inl1 e) =>
        '(m,v) <- handle_all_intrinsics e m;; Ret3 g l m v
    | inr1 (inr1 (inl1 e)) =>
        '(g,v) <- handle_global e g;; Ret3 g l m v
    | inr1 (inr1 (inr1 (inl1 e))) =>
        '(l,v) <- handle_local e l;; Ret3 g l m v
    | inr1 (inr1 (inr1 (inr1 (inl1 e)))) =>
        '(m,v) <- handle_memory e m;; Ret3 g l m v
    | inr1 (inr1 (inr1 (inr1 (inr1 e)))) =>
        v <- trigger e;; Ret3 g l m v
    end.
Arguments handler_cfg3 [_].

Fixpoint tick {E R} (n : nat) (t : itree E R) : itree E R :=
  match n with
  | O   => t
  | S n => Tau (tick n t)
  end.

Definition tickp {E R} (n : nat) (r : R) : itree E R :=
   tick n (Ret r).

Definition handler3_strong : L0 ~> stateT global_env (stateT lenv (stateT memoryV (itree E))) :=
  fun T e g l m =>
    match e with
    | inl1 e =>
        v <- trigger e;; tick 4 (Ret3 g l m v)
    | inr1 (inl1 (Intrinsic t f args as e)) =>
        match assoc f defs_assoc with
        | Some s => '(m,v) <- handle_all_intrinsics e m;; tick 1 (Ret3 g l m v)
        | None => '(m,v) <- handle_all_intrinsics e m;; tick 4 (Ret3 g l m v)
        end
    | inr1 (inr1 (inl1 e)) =>
        '(g,v) <- handle_global e g;; tick 2 (Ret3 g l m v)
    | inr1 (inr1 (inr1 (inl1 (inl1 e)))) =>
        '(l',v) <- handle_local e (fst l);; tick 3 (Ret3 g (l', snd l) m v)
    | inr1 (inr1 (inr1 (inl1 (inr1 e)))) =>
        '(l,v) <- handle_stack e l;; tick 3 (Ret3 g l m v)
    | inr1 (inr1 (inr1 (inr1 (inl1 e)))) =>
        '(m,v) <- handle_memory e m;; tick 4 (Ret3 g l m v)
    | inr1 (inr1 (inr1 (inr1 (inr1 e)))) =>
        v <- trigger e;; tick 4 (Ret3 g l m v)
    end.
Arguments handler3_strong [_].

Definition handler_cfg3_strong : instr_E ~> stateT global_env (stateT local_env (stateT memoryV (itree (CallE +' PickE +' UBE +' DebugE +' FailureE)))) :=
  fun T e g l m =>
    match e with
    | inl1 e =>
        v <- trigger e;; tick 4 (Ret3 g l m v)
    | inr1 (inl1 (Intrinsic t f args as e)) =>
        match assoc f defs_assoc with
        | Some s => '(m,v) <- handle_all_intrinsics e m;; tick 1 (Ret3 g l m v)
        | None => '(m,v) <- handle_all_intrinsics e m;; tick 4 (Ret3 g l m v)
        end
    | inr1 (inr1 (inl1 e)) =>
        '(g,v) <- handle_global e g;; tick 2 (Ret3 g l m v)
    | inr1 (inr1 (inr1 (inl1 e))) =>
        '(l,v) <- handle_local e l;; tick 3 (Ret3 g l m v)
    | inr1 (inr1 (inr1 (inr1 (inl1 e)))) =>
        '(m,v) <- handle_memory e m;; tick 4 (Ret3 g l m v)
    | inr1 (inr1 (inr1 (inr1 (inr1 e)))) =>
        v <- trigger e;; tick 4 (Ret3 g l m v)
    end.
Arguments handler_cfg3_strong [_].

From ExtLib Require Import
     Structures.Monads
     Structures.Maps.

Instance euttge_interp_state_eq {E F: Type -> Type} {S : Type}
         (h : E ~> Monads.stateT S (itree F)) R :
  Proper (euttge eq ==> eq ==> euttge eq) (@interp_state E (itree F) S _ _ _ h R).
Proof.
  repeat intro. subst. revert_until R.
  ginit. gcofix CIH. intros.

  rewrite !unfold_interp_state. punfold H0. red in H0.
  induction H0; intros; subst; simpl; pclearbot.
  - now gstep.
  - gstep; constructor; gbase; auto.
  - guclo eqit_clo_bind. econstructor; [reflexivity|].
    intros; subst.
    gstep; constructor. gbase; auto.
  - rewrite tau_euttge, unfold_interp_state; eauto.
  - inv CHECK.
Qed.

Section PARAMS.
  Variable (k v:Type).
  Context {map : Type}.
  Context {M: Map k v map}.
  Context {SK : Serialize k}.
  Variable (E F G H : Type -> Type).
  Context `{FailureE -< G}.
  Notation Effin := (E +' F +' (GlobalE k v) +' G).
  Notation Effout := (E +' F +' G).

  Lemma interp_global_trigger_eqit:
    forall (g : map) X (e : Effin X),
      interp_global (ITree.trigger e) g ≅ v <- interp_global_h e g;; Tau (Ret v).
  Proof.
    intros.
    unfold interp_global.
    rewrite interp_state_trigger_eqit.
    reflexivity.
  Qed.

  Lemma interp_global_raise :
    forall (g : map) T s,
    @interp_global k v map _ _ E F G _ T (LLVMEvents.raise s) g ≅ LLVMEvents.raise s.
  Proof.
    intros.
    unfold LLVMEvents.raise.
    rewrite interp_global_bind, interp_global_trigger_eqit, !bind_bind.
    cbn; rewrite ?bind_bind.
    eapply eq_itree_clo_bind.
    reflexivity.
    intros [].
  Qed.

  #[global] Instance euttge_interp_global {R} :
    Proper (euttge eq ==> eq ==> euttge eq) (@interp_global _ _ _ _ _ E F G _ R).
  Proof.
    repeat intro.
    unfold interp_global.
    subst; rewrite H1.
    reflexivity.
  Qed.

End PARAMS.

Section PARAMS.
  Variable (k v:Type).
  Context {map : Type}.
  Context {M: Map k v map}.
  Context {SK : Serialize k}.
  Variable (E F G H : Type -> Type).
  Context `{FailureE -< G}.
  Notation Effin := (E +' F +' (LocalE k v) +' G).
  Notation Effout := (E +' F +' G).

  Lemma interp_local_trigger_eqit:
    forall (l : map) X (e : Effin X),
      interp_local (ITree.trigger e) l ≅ v <- interp_local_h e l;; Tau (Ret v).
  Proof.
    intros.
    unfold interp_local.
    rewrite interp_state_trigger_eqit.
    reflexivity.
  Qed.

  Lemma interp_local_raise :
    forall (l : map) T s,
    @interp_local k v map _ _ E F G _ T (LLVMEvents.raise s) l ≅ LLVMEvents.raise s.
  Proof.
    intros.
    unfold LLVMEvents.raise.
    rewrite interp_local_bind, interp_local_trigger_eqit, !bind_bind.
    cbn; rewrite ?bind_bind.
    eapply eq_itree_clo_bind.
    reflexivity.
    intros [].
  Qed.

  #[global] Instance euttge_interp_local {R} :
    Proper (euttge eq ==> eq ==> euttge eq) (@interp_local _ _ _ _ _ E F G _ R).
  Proof.
    repeat intro.
    unfold interp_local.
    subst; rewrite H1.
    reflexivity.
  Qed.

End PARAMS.

Section PARAMS.
  Variable (k v:Type).
  Context {map : Type}.
  Context {M: Map k v map}.
  Context {SK : Serialize k}.
  Variable (E F G : Type -> Type).
  Context `{FailureE -< E +' F +' G}.
  Notation Effin := (E +' F +' (LocalE k v +' StackE k v) +' G).
  Notation Effout := (E +' F +' G).

  Lemma interp_local_stack_trigger_eqit:
    forall s X (e : Effin X),
      interp_local_stack (ITree.trigger e) s ≅
      v <- interp_local_stack_h (handle_local (v:=v)) e s;; Tau (Ret v).
  Proof.
    intros.
    unfold interp_local_stack.
    rewrite interp_state_trigger_eqit.
    reflexivity.
  Qed.

  #[global] Instance euttge_interp_local_stack {R} :
    Proper (euttge eq ==> eq ==> euttge eq) (@interp_local_stack _ _ _ _ _ E F G _ _ R).
  Proof.
    repeat intro.
    unfold interp_local_stack.
    subst; rewrite H0.
    reflexivity.
  Qed.

End PARAMS.

Section PARAMS.
  Variable (E F G : Type -> Type).
  Context `{FailureE -< F} `{UBE -< F} `{PickE -< F}.
  Notation Effin := (E +' IntrinsicE +' MemoryE +' F).
  Notation Effout := (E +' F).
  Notation interp_memory := (@interp_memory E F _ _ _).

  Lemma interp_memory_trigger_eqit:
    forall m X (e : Effin X),
      interp_memory (trigger e) m ≅
      v <- interp_memory_h e m;; Tau (Ret v).
  Proof.
    intros.
    unfold interp_memory.
    setoid_rewrite interp_state_trigger_eqit.
    reflexivity.
  Qed.

  Lemma interp_memory_raise :
    forall m T s,
    @interp_memory T (LLVMEvents.raise s) m ≅ LLVMEvents.raise s.
  Proof.
    intros.
    unfold LLVMEvents.raise.
    rewrite interp_memory_bind.
    match goal with
    |- ITree.bind (interp_memory (ITree.trigger ?e) _) _ ≅ _ =>
      rewrite (interp_memory_trigger_eqit _ _ e)
    end.
    cbn; rewrite ?bind_bind.
    eapply eq_itree_clo_bind.
    reflexivity.
    intros [].
  Qed.

  #[global] Instance euttge_interp_memory {R} :
    Proper (euttge eq ==> eq ==> euttge eq) (@interp_memory R).
  Proof.
    repeat intro.
    unfold interp_memory.
    subst; rewrite H2.
    reflexivity.
  Qed.

End PARAMS.

(* Lemma interp_global_trigger_eqit: *)
(*   forall X (e : Eff X), *)
(*     interp_intrinsics (ITree.trigger e) ≅ x <- interp_intrinsics_h e;; Tau (Ret x). *)
(* Proof. *)
(*   intros *. *)
(*   unfold interp_intrinsics. *)
(*   rewrite interp_trigger_eqit. *)
(*   reflexivity. *)
(* Qed. *)

Ltac go3 :=
  repeat match goal with
    | |- context [interp_intrinsics (ITree.bind _ _)] => rewrite interp_intrinsics_bind
    | |- context [interp_global (ITree.bind _ _)] => rewrite interp_global_bind
    | |- context [interp_local_stack (ITree.bind _ _)] => rewrite interp_local_stack_bind
    | |- context [interp_memory (ITree.bind _ _)] => rewrite interp_memory_bind
    | |- context [interp_intrinsics (ITree.trigger _)] => rewrite interp_intrinsics_trigger_eqit; cbn; rewrite ?subevent_subevent
    | |- context [interp_global (ITree.trigger _)] => rewrite interp_global_trigger_eqit; cbn; rewrite ?subevent_subevent
    | |- context [interp_local_stack (ITree.trigger _)] => rewrite interp_local_stack_trigger_eqit; cbn; rewrite ?subevent_subevent
    | |- context [interp_memory (ITree.trigger ?e)] =>
        rewrite (interp_memory_trigger_eqit _ _ _ _ e); cbn; rewrite ?subevent_subevent
    | |- context [ITree.bind (ITree.bind _ _) _] => rewrite bind_bind
    | |- context [interp_intrinsics (Ret _)] => rewrite interp_intrinsics_ret
    | |- context [interp_global (Ret _)] => rewrite interp_global_ret
    | |- context [interp_local_stack (Ret _)] => rewrite interp_local_stack_ret
    | |- context [interp_memory (Ret _)] => rewrite interp_memory_ret
    | |- context [ITree.bind (Ret _) _] => rewrite bind_ret_l
    | |- context [ITree.bind (Tau _) _] => rewrite bind_tau
    | |- Tau _ ≈ _ => rewrite tau_euttge
    | |- _ => rewrite ?interp_memory_Tau, ?interp_global_Tau, ?interp_local_stack_tau, ?interp_intrinsics_Tau
    end.

Lemma raise_eutt {E X Y Z} `{FailureE -< E} s (k : X -> itree _ Z) (g : Y -> itree _ Z):
  LLVMEvents.raise s >>= k ≈ LLVMEvents.raise s >>= g.
Proof.
  unfold LLVMEvents.raise; rewrite !bind_bind.
  apply eutt_eq_bind; intros [].
Qed.

Lemma equ_eq_bind : forall E R1 R2 RR U (t: itree E U) (k1: U -> itree E R1) (k2: U -> itree E R2),
    (forall u, eq_itree RR (k1 u) (k2 u)) -> eq_itree RR (ITree.bind t k1) (ITree.bind t k2).
Proof.
  intros.
  apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
  intros ? ? ->; apply H.
Qed.

Lemma raise_equ {E X Y Z} `{FailureE -< E} s (k : X -> itree _ Z) (g : Y -> itree _ Z):
  LLVMEvents.raise s >>= k ≅ LLVMEvents.raise s >>= g.
Proof.
  unfold LLVMEvents.raise; rewrite !bind_bind.
  apply equ_eq_bind; intros [].
Qed.

Lemma interp_local_stack_raise :
  forall l T s,
    @interp_local_stack raw_id uvalue _ _ _ ExternalCallE IntrinsicE (MemoryE +' PickE +' UBE +' DebugE +' FailureE) _ _ T (LLVMEvents.raise s) l ≅ LLVMEvents.raise s.
Proof.
  intros.
  unfold LLVMEvents.raise.
  rewrite interp_local_stack_bind, interp_local_stack_trigger_eqit, !bind_bind.
  cbn.
  go3.
  eapply eq_itree_clo_bind.
  reflexivity.
  intros [].
Qed.

Lemma string_dec_correct (s s' : string) :
  s <> s' -> exists pf, string_dec s s' = right pf.
Proof.
  intros.
  destruct string_dec.
  congruence.
  eauto.
Qed.

Lemma interp_mcfg3_trigger_is_handler3_strong : forall X (e : L0 X) g l m,
    interp_mcfg3 (trigger e) g l m ≅ handler3_strong e g l m.
Proof.
  intros.
  unfold ℑs3.
  rewrite interp_intrinsics_trigger_eqit; cbn.
  destruct e as [e | e]; cbn.
  - unfold Intrinsics.E_trigger; cbn.
    go3.
    apply equ_eq_bind.
    intros ?.
    go3.
    reflexivity.
  - destruct e as [e | [e | [e | [e | [e | [e | [e | e]]]]]]]; cbn.
    + destruct e; cbn.
      repeat break_match_goal; subst; cbn.
      * go3.
        rewrite interp_global_raise, interp_local_stack_raise, interp_memory_raise.
        apply raise_equ.
      * now go3.
      * go3.
        unfold handle_intrinsic; cbn.
        destruct m; cbn in *; rewrite Heqs; cbn.
        apply raise_equ.
      * go3.
        unfold handle_intrinsic; cbn.
        destruct m; cbn in *; rewrite Heqs; cbn.
        now go3.
      * go3.
        unfold handle_intrinsic; cbn.
        apply string_dec_correct in n as [? EQ].
        rewrite EQ.
        destruct m.
        apply raise_equ.
    + go3.
      destruct e; cbn; go3.
      reflexivity.
      break_match_goal.
      now go3.
      rewrite ?interp_global_raise, ?interp_local_stack_raise, ?interp_memory_raise.
      apply raise_equ.
    + destruct l; go3.
      destruct e as [e | e]; cbn; go3.
      * unfold ITree.map;
          destruct e; cbn; go3.
        reflexivity.
        break_match_goal; cbn; go3.
        reflexivity.
        rewrite ?interp_global_raise, ?interp_local_stack_raise, ?interp_memory_raise.
        apply raise_equ.
      * destruct e; cbn; go3.
        reflexivity.
        break_match_goal; cbn; go3.
        rewrite ?interp_global_raise, ?interp_local_stack_raise, ?interp_memory_raise.
        apply raise_equ.
        reflexivity.
    + cbn; go3.
      apply equ_eq_bind; intros [].
now go3.
    + cbn; go3.
      apply equ_eq_bind; intros ?.
      now go3.
    + cbn; go3.
      apply equ_eq_bind; intros ?.
      now go3.
    + cbn; go3.
      apply equ_eq_bind; intros ?.
      now go3.
    + cbn; go3.
      apply equ_eq_bind; intros ?.
      now go3.
Qed.

Lemma interp_mcfg3_trigger_is_handler3 : forall X (e : L0 X) g l m,
    interp_mcfg3 (trigger e) g l m ≈ handler3 e g l m.
Proof.
  intros.
  rewrite interp_mcfg3_trigger_is_handler3_strong.
  destruct e as [e | [e | [e | [e | [e | [e | [e | e]]]]]]]; cbn; repeat setoid_rewrite tau_eutt; try reflexivity.
  cbn; repeat break_match_goal; apply eutt_eq_bind; intros []; now rewrite ?tau_eutt.
  cbn; apply eutt_eq_bind; intros []; now rewrite ?tau_eutt.
  cbn; repeat break_match_goal; apply eutt_eq_bind; intros []; now rewrite ?tau_eutt.
  cbn; apply eutt_eq_bind; intros []; now rewrite ?tau_eutt.
Qed.

Ltac go_cfg3 :=
  repeat match goal with
    | |- context [interp_intrinsics (ITree.bind _ _)] => rewrite interp_intrinsics_bind
    | |- context [interp_global (ITree.bind _ _)] => rewrite interp_global_bind
    | |- context [interp_local (ITree.bind _ _)] => rewrite interp_local_bind
    | |- context [interp_memory (ITree.bind _ _)] => rewrite interp_memory_bind
    | |- context [interp_intrinsics (ITree.trigger _)] => rewrite interp_intrinsics_trigger_eqit; cbn; rewrite ?subevent_subevent
    | |- context [interp_global (ITree.trigger _)] => rewrite interp_global_trigger_eqit; cbn; rewrite ?subevent_subevent
    | |- context [interp_local (ITree.trigger _)] => rewrite interp_local_trigger_eqit; cbn; rewrite ?subevent_subevent
    | |- context [interp_memory (ITree.trigger ?e)] =>
        rewrite (interp_memory_trigger_eqit _ _ _ _ e); cbn; rewrite ?subevent_subevent
    | |- context [ITree.bind (ITree.bind _ _) _] => rewrite bind_bind
    | |- context [interp_intrinsics (Ret _)] => rewrite interp_intrinsics_ret
    | |- context [interp_global (Ret _)] => rewrite interp_global_ret
    | |- context [interp_local (Ret _)] => rewrite interp_local_ret
    | |- context [interp_memory (Ret _)] => rewrite interp_memory_ret
    | |- context [ITree.bind (Ret _) _] => rewrite bind_ret_l
    | |- context [ITree.bind (Tau _) _] => rewrite bind_tau
    | |- Tau _ ≈ _ => rewrite tau_euttge
    | |- _ => rewrite ?interp_memory_Tau, ?interp_global_Tau, ?interp_local_Tau, ?interp_intrinsics_Tau
    end.

Lemma interp_cfg3_trigger_is_handler_cfg3_strong : forall X (e : _ X) g l m,
    interp_cfg3 (trigger e) g l m ≅ handler_cfg3_strong e g l m.
Proof.
  intros.
  unfold ℑ3.
  rewrite interp_intrinsics_trigger_eqit; cbn.
  destruct e as [e | e]; cbn.
  - unfold Intrinsics.E_trigger; cbn.
    go_cfg3.
    apply equ_eq_bind.
    intros ?.
    go_cfg3.
    reflexivity.
  - destruct e as [e | [e | [e | [e | [e | [e | [e | e]]]]]]]; cbn.
    + destruct e; cbn.
      repeat break_match_goal; subst; cbn.
      * go_cfg3.
        rewrite interp_global_raise, interp_local_raise, interp_memory_raise.
        apply raise_equ.
      * now go_cfg3.
      * go_cfg3.
        unfold handle_intrinsic; cbn.
        destruct m; cbn in *; rewrite Heqs; cbn.
        apply raise_equ.
      * go_cfg3.
        unfold handle_intrinsic; cbn.
        destruct m; cbn in *; rewrite Heqs; cbn.
        now go_cfg3.
      * go_cfg3.
        unfold handle_intrinsic; cbn.
        apply string_dec_correct in n as [? EQ].
        rewrite EQ.
        destruct m.
        apply raise_equ.
    + go_cfg3.
      destruct e; cbn; go_cfg3.
      reflexivity.
      break_match_goal.
      now go_cfg3.
      rewrite ?interp_global_raise, ?interp_local_raise, ?interp_memory_raise.
      apply raise_equ.
    + go_cfg3.
      destruct e; cbn; go_cfg3.
      reflexivity.
      break_match_goal.
      now go_cfg3.
      rewrite ?interp_global_raise, ?interp_local_raise, ?interp_memory_raise.
      apply raise_equ.
    + cbn; go_cfg3.
      apply equ_eq_bind; intros [].
      now go_cfg3.
    + cbn; go_cfg3.
      apply equ_eq_bind; intros ?.
      now go_cfg3.
    + cbn; go_cfg3.
      apply equ_eq_bind; intros ?.
      now go_cfg3.
    + cbn; go_cfg3.
      apply equ_eq_bind; intros ?.
      now go_cfg3.
    + cbn; go_cfg3.
      apply equ_eq_bind; intros ?.
      now go_cfg3.
Qed.

Lemma interp_cfg3_trigger_is_handler_cfg3 : forall X (e : _ X) g l m,
    interp_cfg3 (trigger e) g l m ≈ handler_cfg3 e g l m.
Proof.
  intros; rewrite interp_cfg3_trigger_is_handler_cfg3_strong.
  destruct e as [e | [e | [e | [e | [e | [e | [e | e]]]]]]]; cbn; repeat setoid_rewrite tau_eutt; try reflexivity.
  cbn; repeat break_match_goal; apply eutt_eq_bind; intros []; now rewrite ?tau_eutt.
  cbn; apply eutt_eq_bind; intros []; now rewrite ?tau_eutt.
  cbn; repeat break_match_goal; apply eutt_eq_bind; intros []; now rewrite ?tau_eutt.
  cbn; apply eutt_eq_bind; intros []; now rewrite ?tau_eutt.
Qed.

Notation M := (itree _ _).

(* Lemma eutt_ret_eq_itree : *)
(*   forall E R (r: R) (t : itree E R), *)
(*     t ≈ Ret r -> *)
(*     exists n, t ≅ tickp n r. *)
(* Proof. *)
(*   intros * EQ; punfold EQ; red in EQ; cbn in EQ. *)
(*   dependent induction EQ. *)
(*   - exists O; rewrite itree_eta, <- x; reflexivity. *)
(*   - edestruct IHEQ; try reflexivity. *)
(*     exists (S x0); rewrite itree_eta, <-x, H. *)
(*     cbn. apply eqitree_Tau. *)
(*     reflexivity. *)
(* Qed. *)

Lemma interp3_vis_eq_itree:
  forall T R (e : L0 T) (k : T -> itree L0 R) g l m,
    ℑs3 (Vis e k) g l m ≅
            '(m, (l, (g, x))) <- ℑs3 (trigger e) g l m;; ℑs3 (k x) g l m.
Proof.
  intros.
  unfold ℑs3.
  rewrite interp_intrinsics_vis_eqit.
  rewrite interp_global_bind, interp_local_stack_bind, interp_memory_bind.
  rewrite interp_intrinsics_trigger_eqit.
  rewrite interp_global_bind, interp_local_stack_bind, interp_memory_bind.
  rewrite bind_bind.
  eapply eq_itree_clo_bind; [reflexivity |].
  intros x y <-; destruct x as [? [? [ ? ?]]].
  rewrite ?interp_global_Tau, ?interp_local_stack_tau, ?interp_memory_Tau.
  rewrite bind_tau, eqitree_Tau.
  rewrite interp_global_ret, interp_local_stack_ret, interp_memory_ret, bind_ret_l.
  reflexivity.
Qed.

Notation gequ r := (gpaco2 (eqit_ eq false false id) (eqitC eq false false) bot2 r).

Lemma interp_trigger_eq_itree {E F : Type -> Type} {R : Type}
      (f : E ~> (itree F))
      (e : E R) :
  interp f (ITree.trigger e) ≅ v <- f _ e;; Tau (Ret v).
Proof.
  unfold ITree.trigger. rewrite interp_vis.
  setoid_rewrite interp_ret; reflexivity.
Qed.

Lemma interp_intrinsics_trigger' {E F} `{FailureE -< F}:
  forall X (e : (E +' _ +' F) X),
    interp_intrinsics (ITree.trigger e) ≅ v <- interp_intrinsics_h e;; Tau (Ret v).
Proof.
  intros *.
  unfold interp_intrinsics.
  rewrite interp_trigger_eq_itree.
  reflexivity.
Qed.


Notation ρ := global_env.
Notation σ := local_env.
Notation μ := memoryV.

Transparent interp_cfg3.
Lemma interp_cfg3_ret : forall (R : Type) g l m (x : R), ℑ3 (Ret x) g l m ≅ Ret3 g l m x.
Proof.
  intros; unfold ℑ3.
  rewrite interp_intrinsics_ret, interp_global_ret, interp_local_ret, interp_memory_ret.
  reflexivity.
Qed.

Instance euttge_interp_cfg3:
  forall T : Type, Proper (euttge eq ==> eq ==> eq ==> eq ==> euttge eq) (@interp_cfg3 T).
Proof.
  repeat intro.
  unfold ℑ3.
  subst; rewrite H.
  reflexivity.
Qed.

Instance euttge_interp_mcfg3:
  forall T : Type, Proper (euttge eq ==> eq ==> eq ==> eq ==> euttge eq) (@interp_mcfg3 T).
Proof.
  repeat intro.
  unfold ℑs3.
  subst; rewrite H.
  reflexivity.
Qed.

Lemma interp3_bind_equ :
  forall {R S} (t: itree L0 R) (k: R -> itree L0 S) g l m,
    ℑs3 (t >>= k) g l m ≅ '(m',(l',(g',x))) <- ℑs3 t g l m;; ℑs3 (k x) g' l' m'.
Proof.
  intros.
  unfold ℑs3.
  go3.
  apply equ_eq_bind; intros (? & ? & ? & ?); reflexivity.
Qed.

Lemma interp_cfg3_bind_equ :
  forall {R S} (t: itree _ R) (k: R -> itree _ S) g l m,
    ℑ3 (t >>= k) g l m ≅ '(m',(l',(g',x))) <- ℑ3 t g l m;; ℑ3 (k x) g' l' m'.
Proof.
  intros.
  unfold ℑ3.
  go_cfg3.
  apply equ_eq_bind; intros (? & ? & ? & ?); reflexivity.
Qed.

Lemma ret_trigger_abs : forall {E : Type -> Type} (X Y : Type) (e : E X) (k : X -> itree E Y) (x : Y),
    Ret x ≅ trigger e >>= k -> False.
Proof.
  intros * abs; unfold trigger in abs; cbn in abs.
  punfold abs; inv abs.
Qed.

Lemma ret_tau_abs : forall {E : Type -> Type} (X : Type) (t : itree E X) (x : X),
    Ret x ≅ Tau t -> False.
Proof.
  intros * abs.
  punfold abs; inv abs; inv CHECK.
Qed.

Lemma ret_raise_abs {E A B} `{FailureE -< E} (s : string) (x : B) k :
  Ret x ≅ LLVMEvents.raise (A := A) s >>= k -> False.
Proof.
  unfold LLVMEvents.raise.
  rewrite bind_bind.
  apply ret_trigger_abs.
Qed.

Lemma ret_raiseUB {E A B} `{UBE -< E} (s : string) (x : B) k :
  Ret x ≅ raiseUB (X :=  A) s >>= k -> False.
Proof.
  unfold raiseUB.
  rewrite bind_bind.
  apply ret_trigger_abs.
Qed.

Lemma tau_trigger_abs : forall {E : Type -> Type} (X Y : Type) (e : E X) (k : X -> itree E Y) (t : itree E Y),
    Tau t ≅ trigger e >>= k -> False.
Proof.
  intros * abs; unfold trigger in abs; cbn in abs.
  now punfold abs; inv abs.
Qed.

Lemma tau_raise_abs {E A B} `{FailureE -< E} (s : string) (x : itree _ B) k :
  Tau x ≅ LLVMEvents.raise (A := A) s >>= k -> False.
Proof.
  unfold LLVMEvents.raise.
  rewrite bind_bind.
  apply tau_trigger_abs.
Qed.

Lemma tau_raiseUB {E A B} `{UBE -< E} (s : string) (x : itree _ B) k :
  Tau x ≅ raiseUB (X :=  A) s >>= k -> False.
Proof.
  unfold raiseUB.
  rewrite bind_bind.
  apply tau_trigger_abs.
Qed.

Lemma eqitree_inv_Tau :
  forall {E : Type -> Type} {R1 R2 : Type} {RR : R1 -> R2 -> Prop} (t1 t2 : itree E _),
    eq_itree RR (Tau t1) (Tau t2) -> eq_itree RR t1 t2.
Proof.
  intros; eapply eqit_inv_Tau; eauto.
Qed.

Lemma tick_eutt :
  forall {E : Type -> Type} {R : Type} n (t1 t2 : itree E R),
    t1 ≅ tick n t2 ->
    t1 ≈ t2.
Proof.
  intros *; revert t1.
  induction n as [| n IH]; cbn; intros * EQ.
  - now rewrite EQ.
  - rewrite EQ, tau_eutt.
    apply IH.
    reflexivity.
Qed.

Lemma tickp_tick :
  forall {E : Type -> Type} {R : Type} r n,
    tickp n r ≅ @tick E R n (Ret r).
Proof.
  induction n; [reflexivity |].
  cbn. apply eqit_Tau.
  reflexivity.
Qed.

Lemma tick_eutt' :
  forall {E : Type -> Type} {R : Type} (t : itree E R) r,
    t ≈ Ret r ->
    exists n, t ≅ tickp n r.
Proof.
  intros.
  punfold H; red in H; dependent induction H.
  - exists 0%nat; rewrite itree_eta, <-x; reflexivity.
  - specialize (IHeqitF t1 r eq_refl).
    destruct IHeqitF as [n EQ]; auto.
    exists (S n); rewrite itree_eta, <-x, EQ, tickp_tick.
    reflexivity.
Qed.

Lemma interp_cfg3_to_mcfg3_aux :
  forall R a b c d (ctx : _ ~> itree (_ +' L0)) (t : itree instr_E _) g l s m n,
    interp_cfg3  (R := R) t g l m ≅ tick n (Ret3 a b c d) ->
    interp_mcfg3 (R := R) (interp_mrec ctx (translate instr_to_L0' t)) g (l,s) m ≈ Ret3 a (b,s) c d .
Proof.
  intros *.
  revert g l m t.
  induction n using lt_wf_ind.
  destruct n as [| n].
  - intros * EQ.
    onAllHyps move_up_types.
    cbn in EQ.
    rewrite (itree_eta t) in EQ.
    rewrite (itree_eta t).
    (* We now have to painfully go through the process of deriving information over [t] from our equation *)
    destruct (observe t).
    + (* If [t] itself is pure, we can unify its value with the desired arguments and transport this information in the goal *)
      rewrite interp_cfg3_ret in EQ.
      apply eqitree_inv_Ret in EQ.
      inv EQ.
      rewrite translate_ret, interp_mrec_ret, interp3_ret.
      reflexivity.
    + (* If [t] starts with a Tau, we have a contradiction in our hypothesis *)
      rewrite interp_cfg3_tau in EQ; punfold EQ; inv EQ; inv CHECK.
    + (* If [t] starts with an effect, things get trickier: we need to go through each case *)
      rewrite interp_cfg3_vis_eqit in EQ.
      rewrite interp_cfg3_trigger_is_handler_cfg3_strong in EQ.
      rewrite translate_vis.
      rewrite <- bind_trigger.
      rewrite interp_mrec_bind,interp_mrec_trigger.
      rewrite interp3_bind_equ.
      (* Case analysis on whether the event is a function call or not *)
      destruct e as [e | e].
      * (* The call case is incompatible with our hypothesis *)
        cbn in *.
        rewrite bind_bind,bind_trigger in EQ.
        punfold EQ; inv EQ.
      * (* hence the event is spat out intact by [mrec] *)
        cbn.
        match goal with
          |- context[mrecursive _ _ ?x] =>
            set (f := x)
            (* replace f with (inr1 (inr1 e): (CallE +' ExternalCallE +' exp_E) X) *)
        end.
        destruct f eqn:EQ'; [subst f; repeat destruct e as [e | e]; inv EQ' |].
        cbn.
        rewrite (interp_mcfg3_trigger_is_handler3_strong _ s0).
        subst f.
        (* Ok, ready to go through each effect *)
        destruct e as [e |[e |[e |[e |e]]]]; inv EQ'.
        -- (* Intrinsics *)
          cbn in *.
          repeat (break_match_goal; cbn in *).
          all:rewrite ?bind_bind, ?bind_ret_l, ?bind_tau in EQ.
          all:symmetry in EQ.
          all: (now exfalso; eapply ret_raise_abs in EQ || now exfalso; eapply ret_tau_abs in EQ).
        -- (* genv *)
          destruct e; cbn in *.
          2:break_match_goal; cbn in *.
          all:rewrite ?bind_bind, ?bind_ret_l, ?bind_tau in EQ.
          all:symmetry in EQ.
          all: try (now exfalso; eapply ret_raise_abs in EQ || now exfalso; eapply ret_tau_abs in EQ).
        -- (* lenv *)
          destruct e; cbn in *.
          2:break_match_goal; cbn in *.
          all:rewrite ?bind_bind, ?bind_ret_l, ?bind_tau in EQ.
          all:symmetry in EQ.
          all: try (now exfalso; eapply ret_raise_abs in EQ || now exfalso; eapply ret_tau_abs in EQ).
        -- (* memory *)
          exfalso.
          rename EQ into h.
          destruct e; cbn in *.
          Ltac tmp' h :=
            repeat (
          cbn in h; rewrite ?bind_bind, ?bind_ret_l, ?bind_tau in h;
          try break_match_hyp;
          try (now exfalso; eapply ret_raise_abs in h ||
               now exfalso; eapply ret_tau_abs in h  ||
               now exfalso; eapply ret_raiseUB in h
            )).
          Ltac tmp h := unfold lift_undef_or_err,lift_pure_err, lift_err in h
          ; tmp' h.
          all: symmetry in h.
          all: tmp h.

        -- exfalso.
           cbn in *.
           rewrite ?bind_bind in EQ.
           punfold EQ; inv EQ.


  - cbn in *.
    intros * EQ.
    rewrite (itree_eta t) in EQ.
    rewrite (itree_eta t).
    (* We now have to painfully go through the process of deriving information over [t] from our equation *)
    destruct (observe t).
    + (* Being pure contradicts HeQT *)
      rewrite interp_cfg3_ret in EQ; punfold EQ; now inversion EQ.
    + (* If it starts with a Tau, we can conclude by induction *)
      rewrite interp_cfg3_tau in EQ.
      apply eqitree_inv_Tau in EQ.
      rewrite translate_tau, interp_mrec_tau, interp3_tau.
      rewrite tau_euttge.
      Import Psatz.
      apply (H n); [lia | auto].
    + (* Otherwise, it starts by interpreting an event *)
      rewrite interp_cfg3_vis_eqit in EQ.
      rewrite interp_cfg3_trigger_is_handler_cfg3_strong in EQ.
      rewrite translate_vis.
      rewrite <- bind_trigger.
      rewrite interp_mrec_bind,interp_mrec_trigger.
      rewrite interp3_bind_equ.
      (* Case analysis on whether the event is a function call or not *)
      destruct e as [e | e].
      * (* The call case is incompatible with our hypothesis *)
        exfalso.
        cbn in EQ.
        rewrite ?bind_bind in EQ.
        now punfold EQ; inv EQ.
      * (* hence the event is spat out intact by [mrec] *)
        cbn.
        match goal with
          |- context[mrecursive _ _ ?x] =>
            set (f := x)
            (* replace f with (inr1 (inr1 e): (CallE +' ExternalCallE +' exp_E) X) *)
        end.
        destruct f eqn:EQ'; [subst f; repeat destruct e as [e | e]; inv EQ' |].
        cbn.
        rewrite (interp_mcfg3_trigger_is_handler3_strong _ s0).
        subst f.
        (* Ok, ready to go through each effect *)
        destruct e as [e |[e |[e |[e |e]]]]; inv EQ'.
        -- (* Intrinsics *)
          cbn in *.
          repeat (break_match_goal; cbn in *).
          all:rewrite ?bind_bind, ?bind_ret_l, ?bind_tau in EQ.
          (* failure cases are ruled out *)
          all: try (now symmetry in EQ; exfalso; eapply tau_raise_abs in EQ).
          (* Successful cases progress by induction *)
          {
            apply eqitree_inv_Tau in EQ.
            rewrite bind_ret_l in EQ.
            rewrite ?bind_bind, ?bind_ret_l, ?bind_tau, tau_euttge, bind_ret_l.
            apply (H n); [lia | auto].
          }
          rewrite ?bind_bind, ?bind_ret_l, ?bind_tau, ?tau_euttge, bind_ret_l.
          apply eqitree_inv_Tau in EQ.
          do 3 (destruct n as [| n]; [ now apply eqit_inv in EQ | cbn in EQ; apply eqitree_inv_Tau in EQ]).
          rewrite bind_ret_l in EQ.
          apply H in EQ; [auto | lia].
        -- (* genv *)
          destruct e; cbn in *.
          2:break_match_goal; cbn in *.
          all:rewrite ?bind_bind, ?bind_ret_l, ?bind_tau in EQ.
          all:repeat rewrite ?bind_bind, ?bind_ret_l, ?bind_tau, ?tau_eutt.
          all: try (now symmetry in EQ; exfalso; eapply tau_raise_abs in EQ || now exfalso; eapply ret_tau_abs in EQ).
          all:apply eqitree_inv_Tau in EQ.
          all:destruct n as [| n]; [ now apply eqit_inv in EQ | cbn in EQ; apply eqitree_inv_Tau in EQ].
          all:rewrite bind_ret_l in EQ.
          all:eapply H; [| eassumption]; lia.
        -- (* lenv *)
          destruct e; cbn in *.
          2:break_match_goal; cbn in *.
          all:rewrite ?bind_bind, ?bind_ret_l, ?bind_tau in EQ.
          all:repeat rewrite ?bind_bind, ?bind_ret_l, ?bind_tau, ?tau_eutt.
          all: try (now symmetry in EQ; exfalso; eapply tau_raise_abs in EQ || now exfalso; eapply ret_tau_abs in EQ).
          all:apply eqitree_inv_Tau in EQ.
          all:do 2 (destruct n as [| n]; [ now apply eqit_inv in EQ | cbn in EQ; apply eqitree_inv_Tau in EQ]).
          all:rewrite bind_ret_l in EQ.
          all:eapply H; [| eassumption]; lia.
        -- (* memory *)
          destruct e; cbn in *.
          Ltac bk_prod := repeat match goal with
               | h: _ * _ |- _ => destruct h
               end.

          all:repeat (unfold lift_undef_or_err,lift_pure_err, lift_err in EQ;
            cbn in EQ; rewrite ?bind_bind, ?bind_ret_l, ?bind_tau in EQ;
            try break_match_hyp;
            try ((now symmetry in EQ; exfalso; eapply tau_raise_abs in EQ)
                 || (now symmetry in EQ; exfalso; eapply tau_raiseUB in EQ))).
          all:apply eqitree_inv_Tau in EQ.
          all: repeat (destruct n as [| n]; [ now apply eqit_inv in EQ | cbn in EQ; apply eqitree_inv_Tau in EQ]).
          all: apply H in EQ; [|lia].
          all: cbn; rewrite ?bind_bind, ?bind_ret_l, ?tau_eutt, ?bind_ret_l.
          all: auto.
        -- cbn in *.
           rewrite ?bind_bind in EQ; punfold EQ; now inv EQ.
Qed.

Lemma interp_cfg3_to_mcfg3 :
  forall R a b c d (ctx : _ ~> itree (_ +' L0)) (t : itree instr_E _) g l s m,
    interp_cfg3  (R := R) t g l m                                                ≈ Ret3 a b c d ->
    interp_mcfg3 (R := R) (interp_mrec ctx (translate instr_to_L0' t)) g (l,s) m ≈ Ret3 a (b,s) c d .
Proof.
  intros * EQ.
  apply tick_eutt' in EQ as [n EQ'].
  eapply interp_cfg3_to_mcfg3_aux.
  rewrite EQ', tickp_tick.
  reflexivity.
Qed.
