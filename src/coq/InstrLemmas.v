(** Lemmas pertaining to denote_instr *)
From Vellvm Require Import
     Util
     Error
     LLVMAst
     AstLib
     CFG
     DynamicTypes
     MemoryAddress
     LLVMEvents
     Handlers.Intrinsics
     Handlers.Handlers
     Denotation
     InterpreterCFG
     Refinement.


From ITree Require Import
     ITree
     Interp.Recursion
     Events.Exception
     Basics.Monad
     TranslateFacts
     Eq.Eq.

From Coq Require Import
     List.

Import ListNotations.

From ExtLib Require Import
     Core.RelDec
     Programming.Eqv
     Structures.Monads
     Data.Monads.EitherMonad
     Structures.Functor
     Data.Nat
     Data.List.



(* TODO: should this be functorized...?
   Currently interp_cfg_to_L3 is fixed to Handlers.LLVMEvents *)
Module D   := Denotation Memory.Addr LLVMEvents.
Module IS  := IntrinsicsDefinitions.Make Memory.Addr LLVMEvents.
Import D IS.

Lemma denote_instr_load :
  forall (i : raw_id) volatile τ τp ptr align defs g ρ ρ' m a uv,
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp (Some τp) ptr)) g ρ m ≈ Ret (m, (ρ', (g, UVALUE_Addr a))) ->
    read m a τ = inr uv ->
    interp_cfg_to_L3 defs (denote_instr (IId i, INSTR_Load volatile τ (τp, ptr) align)) g ρ m ≈ Ret (m, (Maps.add i uv ρ', (g, tt))).
Proof.
  intros i volatile τ τp ptr align defs g ρ ρ' m a uv EXP READ.
  cbn.
  rewrite interp_cfg_to_L3_bind.
  rewrite EXP.
  rewrite bind_ret_l.
  cbn.
  rewrite bind_ret_l.
  rewrite interp_cfg_to_L3_bind.
  rewrite interp_cfg_to_L3_Load; eauto.

  rewrite bind_ret_l.
  rewrite interp_cfg_to_L3_LW.
  cbn.
  reflexivity.
Qed.

(* TODO: Move this *)
Lemma interp_cfg_to_L3_concretize_or_pick_concrete :
  forall (uv : uvalue) (dv : dvalue) P defs g ρ m,
    is_concrete uv ->
    uvalue_to_dvalue uv = inr dv ->
    interp_cfg_to_L3 defs (concretize_or_pick uv P) g ρ m ≈ Ret (m, (ρ, (g, dv))).
Proof.
  intros uv dv P defs g ρ m CONC CONV.
  unfold concretize_or_pick.
  rewrite CONC.
  cbn.
  unfold lift_err.
  rewrite CONV.
  rewrite interp_cfg_to_L3_ret.
  reflexivity.
Qed.

(* TODO: Move this *)
Lemma uvalue_to_dvalue_list :
  forall fields,
    (forall u : uvalue,
        List.In u fields ->
        is_concrete u -> exists dv : dvalue, uvalue_to_dvalue u = inr dv) ->
    forallb is_concrete fields = true ->
    exists dfields, map_monad uvalue_to_dvalue fields = inr dfields.
Proof.
  induction fields; intros H ALL.
  - exists nil. reflexivity.
  - assert (List.In a (a :: fields)) as IN by intuition.

    change (a :: fields) with ([a] ++ fields) in ALL.
    rewrite forallb_app in ALL.
    apply andb_prop in ALL as (CONC_A & CONC_FIELDS).

    cbn in CONC_A.
    rewrite Bool.andb_true_r in CONC_A.
    pose proof (H a IN CONC_A) as (dv & CONV_A).

    assert (forall u : uvalue,
               List.In u fields -> is_concrete u -> exists dv : dvalue, uvalue_to_dvalue u = inr dv) as HCONV.
    { intros u INFS CONCU.
      apply H; intuition.
    }

    pose proof (IHfields HCONV CONC_FIELDS) as (dfields & CONV_DFIELDS).
    exists (dv :: dfields).

    change (a :: fields) with ([a] ++ fields).
    rewrite map_monad_app.
    cbn.
    rewrite CONV_A.
    rewrite CONV_DFIELDS.
    reflexivity.
Qed.

(* TODO: Move this *)
Lemma is_concrete_uvalue_to_dvalue :
  forall uv,
    is_concrete uv ->
    exists dv, uvalue_to_dvalue uv = inr dv.
Proof with reflexivity.
  intros uv CONC.
  induction uv using uvalue_ind';
    inversion CONC.
  - exists (DVALUE_Addr a)...
  - exists (DVALUE_I1 x)...
  - exists (DVALUE_I8 x)...
  - exists (DVALUE_I32 x)...
  - exists (DVALUE_I64 x)...
  - exists (DVALUE_Double x)...
  - exists (DVALUE_Float x)...
  - exists DVALUE_Poison...
  - exists DVALUE_None...
  (* Need to extract the fact that fields, etc, can all be concretized. *)
  - cbn.
    pose proof uvalue_to_dvalue_list _ H H1 as (dv & MAP).
    exists (DVALUE_Struct dv). rewrite MAP.
    reflexivity.
  - cbn.
    pose proof uvalue_to_dvalue_list _ H H1 as (dv & MAP).
    exists (DVALUE_Packed_struct dv). rewrite MAP.
    reflexivity.    
  - cbn.
    pose proof uvalue_to_dvalue_list _ H H1 as (dv & MAP).
    exists (DVALUE_Array dv). rewrite MAP.
    reflexivity.
  - cbn.
    pose proof uvalue_to_dvalue_list _ H H1 as (dv & MAP).
    exists (DVALUE_Vector dv). rewrite MAP.
    reflexivity.    
Qed.

Lemma interp_cfg_to_L3_concretize_or_pick_concrete_exists :
  forall (uv : uvalue) P defs g ρ m,
    is_concrete uv ->
    exists dv, uvalue_to_dvalue uv = inr dv /\ interp_cfg_to_L3 defs (concretize_or_pick uv P) g ρ m ≈ Ret (m, (ρ, (g, dv))).
Proof.
  intros uv P defs g ρ m CONC.
  pose proof is_concrete_uvalue_to_dvalue uv CONC as (dv & CONV).
  exists dv.
  split; auto.
  apply interp_cfg_to_L3_concretize_or_pick_concrete; auto.
Qed.

(* TODO: Move this *)
Lemma interp_cfg_to_L3_pick :
  forall uv P defs g ρ m,
    interp_cfg_to_L3 defs (trigger (pick uv P)) g ρ m ≈ ITree.bind (trigger (pick uv P)) (fun dv => Ret (m, (ρ, (g, dv)))).
Proof.
  intros uv P defs g ρ m.
  unfold interp_cfg_to_L3.

  rewrite interp_intrinsics_trigger.
  cbn.
  unfold Intrinsics.F_trigger.

  rewrite interp_global_trigger.
  rewrite subevent_subevent.
  cbn.

  rewrite bind_trigger.
  rewrite interp_local_vis.
  rewrite subevent_subevent.
  cbn.

  rewrite bind_trigger.
  rewrite bind_vis.

  rewrite interp_memory_vis.
  cbn.

  rewrite bind_trigger.
  rewrite bind_vis.

  repeat setoid_rewrite bind_ret_l.
  setoid_rewrite interp_local_ret.
  setoid_rewrite interp_memory_ret.
  cbn.

  rewrite bind_trigger.
  reflexivity.
Qed.

(* TODO; Move this *)
Lemma interp_cfg_to_L3_concretize_or_pick_not_concrete :
  forall (uv : uvalue) (dv : dvalue) P defs g ρ m,
    is_concrete uv = false ->
    interp_cfg_to_L3 defs (concretize_or_pick uv P) g ρ m ≈ ITree.bind (trigger (pick uv P)) (fun dv => Ret (m, (ρ, (g, dv)))).
Proof.
  intros uv dv P defs g ρ m NCONC.
  unfold concretize_or_pick.
  rewrite NCONC.
  rewrite interp_cfg_to_L3_pick.
  reflexivity.
Qed.

(* Lemma denote_instr_store : *)
(*   forall (i : int) volatile τv val τp ptr align defs uv dv g ρ ρ' m, *)
(*     interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp (Some τv) val)) g ρ m ≈ Ret (m, (ρ', (g, uv))) -> *)
(*     concretize_or_pick uv True ≈ Ret dv -> *)
(*     interp_cfg_to_L3 defs (denote_instr (IVoid i, INSTR_Store volatile (τv, val) (τp, ptr) align)) g ρ m ≈ Ret (m, (ρ', (g, tt))). *)
(* Proof. *)
(*   intros i volatile τv val τp ptr align defs uv dv g ρ ρ' m EXP CONEXP. *)
(*   cbn. *)
(*   rewrite interp_cfg_to_L3_bind. *)
(*   rewrite EXP. *)
(*   rewrite bind_ret_l. *)
(*   rewrite interp_cfg_to_L3_bind. *)
(*   rewrite CONEXP. *)
(*   cbn. *)
(*   rewrite bind_ret_l. *)
(*   rewrite interp_cfg_to_L3_bind. *)
(*   rewrite interp_cfg_to_L3_Load; eauto. *)

(*   rewrite bind_ret_l. *)
(*   rewrite interp_cfg_to_L3_LW. *)
(*   cbn. *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma denote_instr_op : *)
(*   forall (i : raw_id) (op : exp dtyp) defs g ρ m t, *)
(*     interp_cfg_to_L3 defs (denote_instr (IId i, INSTR_Op op)) g ρ m ≈ t. *)
(* Proof. *)
(*   intros i op defs g ρ m t. *)
(*   cbn. *)
(*   unfold denote_op. *)
(*   unfold denote_exp. *)
(*   setoid_rewrite interp_cfg_to_L3_LW. *)
(*   rewrite interp_cfg_to_L3_translate. *)
(*   rewrite translate_bind. *)
(* Qed. *)
