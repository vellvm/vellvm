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
     Handlers.Memory
     Denotation
     InterpreterCFG
     Tactics
     Transformations.Traversal
     TypToDtyp
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

(** Helper lemmas that should probably be moved *)

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

Lemma uvalue_to_dvalue_list_concrete :
  forall fields dfields,
    (forall u : uvalue,
        List.In u fields ->
        (exists dv : dvalue, uvalue_to_dvalue u = inr dv) -> is_concrete u) ->
    map_monad uvalue_to_dvalue fields = inr dfields ->
    forallb is_concrete fields = true.
Proof.
  induction fields; intros dfields H MAP; auto.

  cbn. apply andb_true_intro.
  split.
  - apply H.
    + apply in_eq.
    + inversion MAP.
      destruct (uvalue_to_dvalue a) eqn:Hdv; inversion H1.
      exists d. reflexivity.
  - inversion MAP.
    destruct (uvalue_to_dvalue a) eqn:Hdv; inversion H1.
    destruct (map_monad uvalue_to_dvalue fields) eqn:Hmap; inversion H2.

    assert (forall u : uvalue,
               In u fields -> (exists dv : dvalue, uvalue_to_dvalue u = inr dv) -> is_concrete u) as BLAH.
    { intros u IN (dv & CONV).
      apply H.
      - cbn. auto.
      - exists dv. auto.
    }

    apply (IHfields l BLAH eq_refl).
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

(* TODO: Move this *)
Lemma uvalue_to_dvalue_is_concrete :
  forall uv dv,
    uvalue_to_dvalue uv = inr dv ->
    is_concrete uv.
Proof.
  induction uv using uvalue_ind';
    intros dv CONV; cbn; inversion CONV; auto.
  - break_match; inversion H1.
    eapply uvalue_to_dvalue_list_concrete; eauto.
    intros u IN (dv' & CONV').
    eapply H; eauto.
  - break_match; inversion H1.
    eapply uvalue_to_dvalue_list_concrete; eauto.
    intros u IN (dv' & CONV').
    eapply H; eauto.
  - break_match; inversion H1.
    eapply uvalue_to_dvalue_list_concrete; eauto.
    intros u IN (dv' & CONV').
    eapply H; eauto.
  - break_match; inversion H1.
    eapply uvalue_to_dvalue_list_concrete; eauto.
    intros u IN (dv' & CONV').
    eapply H; eauto.
Qed.

(* TODO: Move this *)
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

(** Lemmas about denote_instr *)

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

Lemma denote_instr_store :
  forall (i : int) volatile τv val τp ptr align defs uv dv a g ρ ρ' ρ'' m m',
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp (Some τv) val)) g ρ m ≈ Ret (m, (ρ', (g, uv))) ->
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp (Some τp) ptr)) g ρ' m ≈ Ret (m, (ρ'', (g, UVALUE_Addr a))) ->
    uvalue_to_dvalue uv = inr dv ->
    write m a dv = inr m' ->
    interp_cfg_to_L3 defs (denote_instr (IVoid i, INSTR_Store volatile (τv, val) (τp, ptr) align)) g ρ m ≈ Ret (m', (ρ'', (g, tt))).
Proof.
  intros i volatile τv val τp ptr align defs uv dv a g ρ ρ' ρ'' m m' EXP PTR CONV_UV WRITE.
  cbn.
  rewrite interp_cfg_to_L3_bind.
  rewrite EXP.
  rewrite bind_ret_l.
  rewrite interp_cfg_to_L3_bind.

  pose proof (uvalue_to_dvalue_is_concrete _ _ CONV_UV) as CONC_UV.
  eapply interp_cfg_to_L3_concretize_or_pick_concrete_exists in CONC_UV as (dv' & CONV_UV' & CONC_UV).
  rewrite CONV_UV' in CONV_UV.
  injection CONV_UV; intros; subst.
  rewrite CONC_UV.

  rewrite bind_ret_l.
  rewrite interp_cfg_to_L3_bind.
  rewrite PTR.
  rewrite bind_ret_l.

  rewrite interp_cfg_to_L3_bind.
  cbn.
  rewrite interp_cfg_to_L3_ret.
  rewrite bind_ret_l.

  rewrite interp_cfg_to_L3_store; cbn; eauto.
  reflexivity.
Qed.

Lemma denote_instr_store_exists :
  forall (i : int) volatile τv val τp ptr align defs uv dv a g ρ ρ' ρ'' m,
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp (Some τv) val)) g ρ m ≈ Ret (m, (ρ', (g, uv))) ->
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp (Some τp) ptr)) g ρ' m ≈ Ret (m, (ρ'', (g, UVALUE_Addr a))) ->
    uvalue_to_dvalue uv = inr dv ->
    dvalue_has_dtyp dv τv ->
    dtyp_fits m a τv ->
    exists m',
      write m a dv = inr m' /\ interp_cfg_to_L3 defs (denote_instr (IVoid i, INSTR_Store volatile (τv, val) (τp, ptr) align)) g ρ m ≈ Ret (m', (ρ'', (g, tt))).
Proof.
  intros i volatile τv val τp ptr align defs uv dv a g ρ ρ' ρ'' m EXP PTR CONV_UV TYP FITS.
  apply write_succeeds with (v:=dv) in FITS as [m2 WRITE]; auto.
  exists m2. split; auto.
  eapply denote_instr_store; eauto.
Qed.

Lemma denote_instr_alloca_exists :
  forall (m : memory_stack) (τ : dtyp) g ρ i align nb defs,
    non_void τ ->
    exists m' a,
      allocate m τ = inr (m', a) /\
      interp_cfg_to_L3 defs (denote_instr (IId i, INSTR_Alloca τ nb align)) g ρ m ≈ Ret (m', (Maps.add i (UVALUE_Addr a) ρ, (g, tt))).
Proof.
  intros m τ g ρ i align nb defs NV.

  pose proof interp_cfg_to_L3_alloca defs m τ g ρ NV as (m' & a & ALLOC & TRIGGER).
  exists m'. exists a. split; auto.

  cbn. rewrite interp_cfg_to_L3_bind.
  rewrite TRIGGER; cbn.
  rewrite bind_ret_l.
  rewrite interp_cfg_to_L3_LW. cbn.
  reflexivity.
Qed.

Lemma denote_instr_comment :
  forall i str g ρ m defs,
    interp_cfg_to_L3 defs (denote_instr (i, INSTR_Comment str)) g ρ m ≈ Ret (m, (ρ, (g, tt))).
Proof.
  intros i str g ρ m defs.
  destruct i; cbn; rewrite interp_cfg_to_L3_ret; reflexivity.
Qed.


Lemma denote_instr_op :
  forall (i : raw_id) (op : exp dtyp) defs uv g ρ ρ' m,
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp None op)) g ρ m ≈ Ret (m, (ρ', (g, uv))) ->
    interp_cfg_to_L3 defs (denote_instr (IId i, INSTR_Op op)) g ρ m ≈ Ret (m, (Maps.add i uv ρ', (g, tt))).
Proof.
  intros i op defs uv g ρ ρ' m OP.
  cbn.
  unfold denote_op.
  rewrite interp_cfg_to_L3_bind.

  rewrite OP. rewrite bind_ret_l.
  rewrite interp_cfg_to_L3_LW.
  reflexivity.
Qed.

(* TODO: Move to place where expression lemmas belong? *)
Lemma denote_ibinop_concrete :
  forall (op : ibinop) τ e0 e1 g ρ m x a av b bv defs,
    uvalue_to_dvalue a = inr av ->
    uvalue_to_dvalue b = inr bv ->
    eval_iop op av bv  = ret x ->
    Ret (m, (ρ, (g, a)))
        ≈ interp_cfg_to_L3 defs
        (translate exp_E_to_instr_E (denote_exp (Some τ) (convert_typ [ ] e0))) g ρ
        m ->
    Ret (m, (ρ, (g, b)))
        ≈ interp_cfg_to_L3 defs
        (translate exp_E_to_instr_E (denote_exp (Some τ) (convert_typ [ ] e1))) g ρ
        m ->
   interp_cfg_to_L3 defs
   (translate exp_E_to_instr_E
      (D.denote_exp None
         (OP_IBinop op τ (Traversal.fmap (typ_to_dtyp [ ]) e0)
            (Traversal.fmap (typ_to_dtyp [ ]) e1)))) g ρ m ≈ Ret (m, (ρ, (g, (dvalue_to_uvalue x)))).
Proof.
  intros op τ e0 e1 g ρ m x a av b bv defs AV BV EVAL A B.

  (* First subexpression *)
  cbn.
  rewrite translate_bind.
  rewrite interp_cfg_to_L3_bind.
  rewrite <- A.
  rewrite bind_ret_l.

  (* Second subexpression *)
  rewrite translate_bind.
  rewrite interp_cfg_to_L3_bind.
  rewrite <- B.
  rewrite bind_ret_l.

  pose proof (uvalue_to_dvalue_is_concrete _ _ BV) as CONC.
  rewrite CONC.
  cbn. rewrite Bool.andb_false_r.

  unfold uvalue_to_dvalue_binop.
  rewrite AV, BV.
  cbn.

  rewrite EVAL.
  cbn.

  repeat rewrite translate_ret.
  rewrite interp_cfg_to_L3_ret.
  reflexivity.
Qed.

(* Lemma denote_instr_call : *)
(*   forall defs i τf f args uf uvs g ρ ρ' m t, *)
(*     map_monad (fun '(t, op) => translate exp_E_to_instr_E (denote_exp (Some t) op)) args ≈ Ret uvs -> *)
(*     interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp None f)) g ρ m ≈ Ret (m, (ρ', (g, uf))) -> *)
(*     intrinsic_exp f = None -> *)
(*     interp_cfg_to_L3 defs (denote_instr (IId i, INSTR_Call (τf, f) args)) g ρ m ≈ t. (* interp_cfg_to_L3 defs (ITree.bind (trigger (LLVMEvents.Call τf uf uvs)) (fun x => trigger (LocalWrite i x)) g ρ' m). *) *)
(* Proof. *)
(*   intros defs i τf f args uf uvs g ρ ρ' m t MAP FEXP INT. *)
(*   cbn. *)
(*   rewrite MAP. rewrite bind_ret_l. *)
(*   rewrite INT. rewrite bind_bind. *)

(*   rewrite interp_cfg_to_L3_bind. *)
(*   rewrite FEXP. rewrite bind_ret_l. *)

(*   rewrite interp_cfg_to_L3_bind. *)
(*   rewrite interp_cfg_to_L3_LW. *)
(*   rewrite <- bind_trigger. *)

(*   interp_cfg_to_L3 defs *)
(*     (ITree.bind (trigger (LLVMEvents.Call τf uf uvs)) *)
(*        (fun returned_value : uvalue => trigger (LocalWrite i returned_value))) g ρ' m ≈ t *)

(*   rewrite bind_trigger *)

(* Qed. *)
