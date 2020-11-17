From Coq Require Import
     Morphisms.

Require Import List.
Import ListNotations.
Require Import ZArith.

From ITree Require Import
     ITree
     Basics.Monad
     Eq.Eq
     TranslateFacts.

From Vellvm Require Import
     LLVMEvents
     LLVMAst
     Util
     DynamicTypes
     DynamicValues
     Handlers.Handlers
     Refinement
     TopLevel
     InterpreterCFG
     Tactics
     TypToDtyp
     AstLib
     ExpLemmas
.

Import D.
Open Scope itree_scope.

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

(* TODO: Move this *)
Lemma is_concrete_uvalue_to_dvalue :
  forall uv,
    is_concrete uv ->
    exists dv, uvalue_to_dvalue uv = inr dv.
Proof with reflexivity.
  intros uv CONC.
  induction uv;
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

(* TODO: something like this exists in tmp_aux_vellvm.v in Helix. Move these. *)
Lemma exp_E_to_instr_E_subevent : forall {E} {X} `{E -< exp_E} (e : E X),
    exp_E_to_instr_E (subevent X e) = subevent X e.
Proof.
  reflexivity.
Qed.


Lemma denote_instr_gep_array :
  forall i size τ defs e_ix ix ptr a val g ρ m,
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp (Some DTYPE_Pointer) ptr)) g ρ m
    ≈
    Ret (m, (ρ, (g, UVALUE_Addr a)))
    ->
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp (Some (DTYPE_I 64)) e_ix)) g ρ m
    ≈
    Ret (m, (ρ, (g, UVALUE_I64 (repr (Z.of_nat ix)))))
    ->
    get_array_cell m a ix τ = inr val
    ->
    exists ptr_res,
      read m ptr_res τ = inr val /\
      interp_cfg_to_L3 defs (denote_instr (IId i, INSTR_Op (OP_GetElementPtr (DTYPE_Array size τ) (DTYPE_Pointer, ptr) [(DTYPE_I 64, EXP_Integer 0%Z); (DTYPE_I 64, e_ix)]))) g ρ m
      ≈
      Ret (m, (Maps.add i (UVALUE_Addr ptr_res) ρ, (g, tt))).
Proof.
  intros i size τ defs e_ix ix ptr a val g ρ m PTR IX GET.

  pose proof interp_cfg_to_L3_GEP_array defs τ a size g ρ m val ix GET as (ptr_res & EQ & READ).
  exists ptr_res. split; auto.

  cbn.
  rewrite translate_bind.
  rewrite bind_bind.
  rewrite interp_cfg_to_L3_bind.

  rewrite PTR.
  rewrite bind_ret_l.

  (* Could probably automate some of this fiddliness *)
  repeat rewrite translate_bind.
  repeat rewrite bind_bind.
  rewrite translate_ret.
  rewrite bind_ret_l.
  repeat rewrite translate_bind.
  repeat rewrite bind_bind.

  rewrite interp_cfg_to_L3_bind.
  rewrite IX.
  rewrite bind_ret_l.

  rewrite interp_cfg_to_L3_bind.
  rewrite bind_ret_l.
  rewrite translate_ret.
  rewrite interp_cfg_to_L3_ret.
  rewrite bind_ret_l.
  rewrite translate_ret.
  rewrite bind_ret_l.
  cbn.
  unfold ITree.map.
  rewrite translate_bind.
  rewrite bind_bind.

  rewrite translate_trigger.
  rewrite interp_cfg_to_L3_bind_trigger.
  rewrite exp_E_to_instr_E_subevent.

  rewrite EQ.

  rewrite bind_ret_l.
  rewrite interp_cfg_to_L3_bind.
  cbn.
  rewrite translate_ret.
  rewrite interp_cfg_to_L3_ret.
  rewrite bind_ret_l.
  rewrite interp_cfg_to_L3_LW.
  reflexivity.
Qed.

Lemma denote_instr_gep_array' :
  forall i size τ defs e_ix ix ptr a val g ρ m,
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp (Some DTYPE_Pointer) ptr)) g ρ m
    ≈
    Ret (m, (ρ, (g, UVALUE_Addr a)))
    ->
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp (Some (DTYPE_I 64)) e_ix)) g ρ m
    ≈
    Ret (m, (ρ, (g, UVALUE_I64 (repr (Z.of_nat ix)))))
    ->
    get_array_cell m a ix τ = inr val
    ->
    exists ptr_res,
      read m ptr_res τ = inr val /\
      handle_gep_addr (DTYPE_Array size τ) a [DVALUE_I64 (repr 0); DVALUE_I64 (repr (Z.of_nat ix))] = inr ptr_res /\
      interp_cfg_to_L3 defs (denote_instr (IId i, INSTR_Op (OP_GetElementPtr (DTYPE_Array size τ) (DTYPE_Pointer, ptr) [(DTYPE_I 64, EXP_Integer 0%Z); (DTYPE_I 64, e_ix)]))) g ρ m
      ≈
      Ret (m, (Maps.add i (UVALUE_Addr ptr_res) ρ, (g, tt))).
Proof.
  intros i size τ defs e_ix ix ptr a val g ρ m PTR IX GET.

  pose proof interp_cfg_to_L3_GEP_array' defs τ a size g ρ m val ix GET as (ptr_res & EQ & GEP & READ).
  exists ptr_res.
  split; auto.
  split; auto.

  cbn.
  rewrite translate_bind.
  rewrite bind_bind.
  rewrite interp_cfg_to_L3_bind.

  rewrite PTR.
  rewrite bind_ret_l.

  (* Could probably automate some of this fiddliness *)
  repeat rewrite translate_bind.
  repeat rewrite bind_bind.
  rewrite translate_ret.
  rewrite bind_ret_l.
  repeat rewrite translate_bind.
  repeat rewrite bind_bind.

  rewrite interp_cfg_to_L3_bind.
  rewrite IX.
  rewrite bind_ret_l.

  rewrite interp_cfg_to_L3_bind.
  rewrite bind_ret_l.
  rewrite translate_ret.
  rewrite interp_cfg_to_L3_ret.
  rewrite bind_ret_l.
  rewrite translate_ret.
  rewrite bind_ret_l.
  cbn.
  unfold ITree.map.
  rewrite translate_bind.
  rewrite bind_bind.

  rewrite translate_trigger.
  rewrite interp_cfg_to_L3_bind_trigger.
  rewrite exp_E_to_instr_E_subevent.

  rewrite EQ.

  rewrite bind_ret_l.
  rewrite interp_cfg_to_L3_bind.
  cbn.
  rewrite translate_ret.
  rewrite interp_cfg_to_L3_ret.
  rewrite bind_ret_l.
  rewrite interp_cfg_to_L3_LW.
  reflexivity.
Qed.

Lemma denote_instr_gep_array_no_read :
  forall i size τ defs e_ix ix ptr a g ρ m,
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp (Some DTYPE_Pointer) ptr)) g ρ m
    ≈
    Ret (m, (ρ, (g, UVALUE_Addr a)))
    ->
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp (Some (DTYPE_I 64)) e_ix)) g ρ m
    ≈
    Ret (m, (ρ, (g, UVALUE_I64 (repr (Z.of_nat ix)))))
    ->
    dtyp_fits m a (DTYPE_Array size τ) ->
    exists ptr_res,
      handle_gep_addr (DTYPE_Array size τ) a [DVALUE_I64 (repr 0); DVALUE_I64 (repr (Z.of_nat ix))] = inr ptr_res /\
      interp_cfg_to_L3 defs (denote_instr (IId i, INSTR_Op (OP_GetElementPtr (DTYPE_Array size τ) (DTYPE_Pointer, ptr) [(DTYPE_I 64, EXP_Integer 0%Z); (DTYPE_I 64, e_ix)]))) g ρ m
      ≈
      Ret (m, (Maps.add i (UVALUE_Addr ptr_res) ρ, (g, tt))).
Proof.
  intros i size τ defs e_ix ix ptr a g ρ m PTR IX FITS.

  pose proof interp_cfg_to_L3_GEP_array_no_read defs τ a size g ρ m ix FITS as (ptr_res & EQ & GEP).
  exists ptr_res.
  split; auto.

  cbn.
  rewrite translate_bind.
  rewrite bind_bind.
  rewrite interp_cfg_to_L3_bind.

  rewrite PTR.
  rewrite bind_ret_l.

  (* Could probably automate some of this fiddliness *)
  repeat rewrite translate_bind.
  repeat rewrite bind_bind.
  rewrite translate_ret.
  rewrite bind_ret_l.
  repeat rewrite translate_bind.
  repeat rewrite bind_bind.

  rewrite interp_cfg_to_L3_bind.
  rewrite IX.
  rewrite bind_ret_l.

  rewrite interp_cfg_to_L3_bind.
  rewrite bind_ret_l.
  rewrite translate_ret.
  rewrite interp_cfg_to_L3_ret.
  rewrite bind_ret_l.
  rewrite translate_ret.
  rewrite bind_ret_l.
  cbn.
  unfold ITree.map.
  rewrite translate_bind.
  rewrite bind_bind.

  rewrite translate_trigger.
  rewrite interp_cfg_to_L3_bind_trigger.
  rewrite exp_E_to_instr_E_subevent.

  rewrite EQ.

  rewrite bind_ret_l.
  rewrite interp_cfg_to_L3_bind.
  cbn.
  rewrite translate_ret.
  rewrite interp_cfg_to_L3_ret.
  rewrite bind_ret_l.
  rewrite interp_cfg_to_L3_LW.
  reflexivity.
Qed.

Lemma denote_instr_intrinsic :
  forall i τ defs fn in_n sem_f args arg_vs conc_args res g ρ m,
    @intrinsic_exp dtyp (EXP_Ident (ID_Global (Name fn))) = Some in_n
    ->
    assoc in_n (defs_assoc defs) = Some sem_f
    ->
    interp_cfg_to_L3 defs (map_monad (fun '(t, op) => translate exp_E_to_instr_E (denote_exp (Some t) op)) args) g ρ m
    ≈
    Ret (m, (ρ, (g, arg_vs))) 
    ->
    interp_cfg_to_L3 defs (map_monad (fun uv : uvalue => pickUnique uv) arg_vs) g ρ m
    ≈
    Ret (m, (ρ, (g, conc_args)))
    ->
    sem_f conc_args = inr res
    ->
    (interp_cfg_to_L3 defs
       (denote_instr
          (IId i,
           INSTR_Call (τ, EXP_Ident (ID_Global (Name fn))) args)) g ρ m)
    ≈
    Ret (m, (FMapAList.alist_add eq_dec_raw_id i (dvalue_to_uvalue res) ρ, (g, tt))).
Proof.
  intros * INTRINSIC ASSOC  MAP CONCARGS RES.

  unfold denote_instr.
  setoid_rewrite interp_cfg_to_L3_bind.
  rewrite MAP.
  setoid_rewrite bind_ret_l.
  rewrite INTRINSIC.
  setoid_rewrite bind_bind.
  rewrite interp_cfg_to_L3_bind.
  rewrite CONCARGS.
  rewrite bind_ret_l.

  cbn; unfold ITree.map.
  rewrite bind_bind.
  rewrite interp_cfg_to_L3_bind.
  rewrite interp_cfg_to_L3_intrinsic; eauto.

  repeat (cbn; rewrite bind_ret_l).
  rewrite interp_cfg_to_L3_LW.
  cbn.
  reflexivity.
Qed.

Lemma denote_term_br_l :
  forall (e : exp dtyp) defs b1 b2 g ρ ρ' m,
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp (Some (DTYPE_I 1)) e)) g ρ m
    ≈
    Ret (m, (ρ', (g, UVALUE_I1 one)))
    ->
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_terminator (TERM_Br (DTYPE_I 1%Z, e) b1 b2))) g ρ m
    ≈
    Ret (m, (ρ', (g, inl b1))).
Proof.
  intros * EXP.
  simpl.
  rewrite translate_bind, interp_cfg_to_L3_bind.
  rewrite EXP, bind_ret_l.
  cbn.
  rewrite bind_ret_l.
  cbn.
  rewrite translate_ret,interp_cfg_to_L3_ret.
  reflexivity.
Qed.

Lemma denote_term_br_r :
  forall (e : exp dtyp) defs b1 b2 g ρ ρ' m,
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp (Some (DTYPE_I 1)) e)) g ρ m
    ≈
    Ret (m, (ρ', (g, UVALUE_I1 zero)))
    ->
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_terminator (TERM_Br (DTYPE_I 1%Z, e) b1 b2))) g ρ m
    ≈
    Ret (m, (ρ', (g, inl b2))).
Proof.
  intros * EXP.
  simpl.
  rewrite translate_bind, interp_cfg_to_L3_bind.
  rewrite EXP, bind_ret_l.
  cbn.
  rewrite bind_ret_l.
  cbn.
  rewrite translate_ret,interp_cfg_to_L3_ret.
  reflexivity.
Qed.

Lemma denote_term_br_1 :
  forall defs b g ρ m,
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_terminator (TERM_Br_1 b))) g ρ m
    ≈
    Ret (m, (ρ, (g, inl b))).
Proof.
  intros defs b g ρ m.
  cbn.
  rewrite translate_ret,interp_cfg_to_L3_ret.
  reflexivity.
Qed.


(* Lemma wah : *)
(*   forall m ptr τ val, *)
(*     read m ptr τ = inr val -> *)
(*     dtyp_fits m ptr τ. *)
(* Proof. *)
(*   intros m [ptr_blk ptr_idx] τ val READ. *)
(*   unfold read in READ; cbn in READ. *)
(*   destruct (get_logical_block m ptr_blk) eqn:GETBLOCK; inversion READ. *)
(*   destruct l. *)

(*   unfold dtyp_fits. *)
(*   exists size. exists bytes. exists concrete_id. *)
(*   cbn. *)
(*   split; auto. *)

(*   unfold get_logical_block in GETBLOCK. *)
(*   unfold get_logical_block_mem in GETBLOCK. *)

(*   destruct m. destruct m. cbn in *. *)

(*   unfold read_in_mem_block in READ. *)
(* Qed. *)

(*

interp_cfg_to_L3_intrinsic:
  forall (defs : Intrinsics.intrinsic_definitions) (m : memory_stack) (τ : dtyp)
    (g : global_env) (l : local_env) (fn : String.string) (args : list dvalue)
    (df : Intrinsics.semantic_function) (res : dvalue),
  assoc Strings.String.string_dec fn (defs_assoc defs) = Some df ->
  df args = inr res ->
  Monad.eqm (interp_cfg_to_L3 defs (trigger (Intrinsic τ fn args)) g l m) (ret (m, (l, (g, res))))

*)

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
