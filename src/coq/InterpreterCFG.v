From Coq Require Import
     Morphisms.

Require Import List.
Import ListNotations.
Require Import ZArith.

From ITree Require Import
     ITree
     Basics.Monad
     Eq.Eq.

From Vellvm Require Import
     LLVMEvents
     Util
     DynamicTypes
     DynamicValues
     Handlers.Handlers
     Refinement.

Section InterpreterCFG.

  (**
   Partial interpretations of the trees produced by the
   denotation of cfg. They differ from the ones of Vellvm programs by
   their event signature, as well as by the lack of a stack of local event.
   The intent is to allow us to only interpret as many layers as needed
   to perform the required semantic reasoning, and lift for free the
   equivalence down the pipe.
   This gives us a _vertical_ notion of compositionality.
   *)

  (**
   NOTE: Can we avoid this duplication w.r.t. [interp_to_Li]?
   *)

  Definition interp_cfg_to_L1 {R} user_intrinsics (t: itree instr_E R) (g: global_env) :=
    let L0_trace       := interp_intrinsics user_intrinsics t in
    let L1_trace       := interp_global L0_trace g in
    L1_trace.

  Definition interp_cfg_to_L2 {R} user_intrinsics (t: itree instr_E R) (g: global_env) (l: local_env) :=
    let L0_trace       := interp_intrinsics user_intrinsics t in
    let L1_trace       := interp_global L0_trace g in
    let L2_trace       := interp_local L1_trace l in
    L2_trace.

  Definition interp_cfg_to_L3 {R} user_intrinsics (t: itree instr_E R) (g: global_env) (l: local_env) (m: memory_stack) :=
    let L0_trace       := interp_intrinsics user_intrinsics t in
    let L1_trace       := interp_global L0_trace g in
    let L2_trace       := interp_local L1_trace l in
    let L3_trace       := interp_memory L2_trace m in
    L3_trace.

  Definition interp_cfg_to_L4 {R} RR user_intrinsics (t: itree instr_E R) (g: global_env) (l: local_env) (m: memory_stack) :=
    let L0_trace       := interp_intrinsics user_intrinsics t in
    let L1_trace       := interp_global L0_trace g in
    let L2_trace       := interp_local L1_trace l in
    let L3_trace       := interp_memory L2_trace m in
    let L4_trace       := model_undef RR L3_trace in
    L4_trace.

  Definition interp_cfg_to_L5 {R} RR user_intrinsics (t: itree instr_E R) (g: global_env) (l: local_env) (m: memory_stack) :=
    let L0_trace       := interp_intrinsics user_intrinsics t in
    let L1_trace       := interp_global L0_trace g in
    let L2_trace       := interp_local L1_trace l in
    let L3_trace       := interp_memory L2_trace m in
    let L4_trace       := model_undef RR L3_trace in
    model_UB RR L4_trace.

  Lemma interp_cfg_to_L1_bind :
    forall ui {R S} (t: itree instr_E R) (k: R -> itree instr_E S) g, 
      interp_cfg_to_L1 ui (ITree.bind t k) g ≈
                       (ITree.bind (interp_cfg_to_L1 ui t g) (fun '(g',x) => interp_cfg_to_L1 ui (k x) g')).
  Proof.
    intros.
    unfold interp_cfg_to_L1.
    rewrite interp_intrinsics_bind, interp_global_bind.
    apply eutt_eq_bind; intros (? & ?); reflexivity.
  Qed.

  Lemma interp_cfg_to_L1_ret : forall ui (R : Type) g (x : R), interp_cfg_to_L1 ui (Ret x) g ≈ Ret (g,x).
  Proof.
    intros; unfold interp_cfg_to_L1.
    rewrite interp_intrinsics_ret, interp_global_ret; reflexivity.
  Qed.

  Lemma interp_cfg_to_L2_bind :
    forall ui {R S} (t: itree instr_E R) (k: R -> itree instr_E S) g l,
      interp_cfg_to_L2 ui (ITree.bind t k) g l ≈
                       (ITree.bind (interp_cfg_to_L2 ui t g l) (fun '(g',(l',x)) => interp_cfg_to_L2 ui (k x) l' g')).
  Proof.
    intros.
    unfold interp_cfg_to_L2.
    rewrite interp_intrinsics_bind, interp_global_bind, interp_local_bind.
    apply eutt_eq_bind; intros (? & ? & ?); reflexivity.
  Qed.

  Lemma interp_cfg_to_L2_ret : forall ui (R : Type) g l (x : R), interp_cfg_to_L2 ui (Ret x) g l ≈ Ret (l, (g, x)).
  Proof.
    intros; unfold interp_cfg_to_L2.
    rewrite interp_intrinsics_ret, interp_global_ret, interp_local_ret; reflexivity.
  Qed.

  Lemma interp_cfg_to_L3_bind :
    forall ui {R S} (t: itree instr_E R) (k: R -> itree instr_E S) g l m,
      interp_cfg_to_L3 ui (ITree.bind t k) g l m ≈
                       (ITree.bind (interp_cfg_to_L3 ui t g l m) (fun '(m',(l',(g',x))) => interp_cfg_to_L3 ui (k x) g' l' m')).
  Proof.
    intros.
    unfold interp_cfg_to_L3.
    rewrite interp_intrinsics_bind, interp_global_bind, interp_local_bind, interp_memory_bind.
    apply eutt_eq_bind; intros (? & ? & ? & ?); reflexivity.
  Qed.

  Lemma interp_cfg_to_L3_ret : forall ui (R : Type) g l m (x : R), interp_cfg_to_L3 ui (Ret x) g l m ≈ Ret (m, (l, (g,x))).
  Proof.
    intros; unfold interp_cfg_to_L3.
    rewrite interp_intrinsics_ret, interp_global_ret, interp_local_ret, interp_memory_ret; reflexivity.
  Qed.

  Global Instance eutt_interp_cfg_to_L1 (defs: intrinsic_definitions) {T}:
    Proper (eutt Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp_cfg_to_L1 T defs).
  Proof.
    repeat intro.
    unfold interp_cfg_to_L1.
    subst; rewrite H.
    reflexivity.
  Qed.

  Global Instance eutt_interp_cfg_to_L2 (defs: intrinsic_definitions) {T}:
    Proper (eutt Logic.eq ==> Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp_cfg_to_L2 T defs).
  Proof.
    repeat intro.
    unfold interp_cfg_to_L2.
    subst; rewrite H.
    reflexivity.
  Qed.

  Global Instance eutt_interp_cfg_to_L3 (defs: intrinsic_definitions) {T}:
    Proper (eutt Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp_cfg_to_L3 T defs).
  Proof.
    repeat intro.
    unfold interp_cfg_to_L3.
    subst; rewrite H.
    reflexivity.
  Qed.

  (* NOTEYZ: This can probably be refined to [eqit eq] instead of [eutt eq], but I don't think it matters to us *)
  Lemma interp_cfg_to_L3_vis (defs: IS.intrinsic_definitions):
    forall T R (e : instr_E T) (k : T -> itree instr_E R) g l m,
      interp_cfg_to_L3 defs (Vis e k) g l m ≈ 
                       ITree.bind (interp_cfg_to_L3 defs (trigger e) g l m)
                       (fun '(m, (l, (g, x)))=> interp_cfg_to_L3 defs (k x) g l m).
  Proof.
    intros.
    unfold interp_cfg_to_L3.
    rewrite interp_intrinsics_vis.
    rewrite interp_global_bind, interp_local_bind, interp_memory_bind.
    unfold trigger; rewrite interp_intrinsics_vis.
    rewrite interp_global_bind, interp_local_bind, interp_memory_bind.
    rewrite Eq.bind_bind.
    apply eutt_eq_bind.
    intros (? & ? & ? & ?).
    do 2 match goal with
      |- context[interp ?x ?t] => replace (interp x t) with (interp_intrinsics defs t) by reflexivity
    end. 
    rewrite interp_intrinsics_ret, interp_global_ret, interp_local_ret, interp_memory_ret, bind_ret_l.
    reflexivity.
  Qed.

  Lemma interp_cfg_to_L3_bind_trigger (defs: IS.intrinsic_definitions):
    forall T R (e : instr_E T) (k : T -> itree instr_E R) g l m,
      interp_cfg_to_L3 defs (ITree.bind (trigger e) k) g l m ≈ 
                       ITree.bind (interp_cfg_to_L3 defs (trigger e) g l m)
                       (fun '(m, (l, (g, x)))=> interp_cfg_to_L3 defs (k x) g l m).
  Proof.
    intros.
    rewrite bind_trigger.
    rewrite interp_cfg_to_L3_vis at 1.
    reflexivity.
  Qed.

  Lemma interp_cfg_to_L3_GR : forall defs id g l m v,
      Maps.lookup id g = Some v ->
      interp_cfg_to_L3 defs (trigger (GlobalRead id)) g l m ≈ ret (m,(l,(g,v))).
  Proof.
    intros * LU.
    unfold interp_cfg_to_L3.
    rewrite interp_intrinsics_trigger.
    cbn.
    unfold Intrinsics.F_trigger.
    rewrite interp_global_trigger.
    cbn in *; rewrite LU.
    rewrite interp_local_ret, interp_memory_ret.
    reflexivity.
  Qed.

  Lemma interp_cfg_to_L3_LR : forall defs id g l m v,
      Maps.lookup id l = Some v ->
      interp_cfg_to_L3 defs (trigger (LocalRead id)) g l m ≈ ret (m,(l,(g,v))).
  Proof.
    intros * LU.
    unfold interp_cfg_to_L3.
    rewrite interp_intrinsics_trigger.
    cbn.
    unfold Intrinsics.F_trigger.
    rewrite interp_global_trigger.
    cbn.
    rewrite interp_local_bind, interp_local_trigger.
    cbn in *; rewrite LU.
    rewrite bind_ret_l, interp_local_ret, interp_memory_ret.
    reflexivity.
  Qed.

  Lemma interp_cfg_to_L3_LW : forall defs id g l m v,
      interp_cfg_to_L3 defs (trigger (LocalWrite id v)) g l m ≈ ret (m,(Maps.add id v l, (g,tt))).
  Proof.
    intros.
    unfold interp_cfg_to_L3.
    rewrite interp_intrinsics_trigger; cbn. 
    unfold Intrinsics.F_trigger.
    rewrite interp_global_trigger; cbn.
    rewrite interp_local_bind, interp_local_trigger; cbn.
    rewrite bind_ret_l, interp_local_ret, interp_memory_ret.
    reflexivity.
  Qed.

  Lemma interp_cfg_to_L3_GW : forall defs id g l m v,
      interp_cfg_to_L3 defs (trigger (GlobalWrite id v)) g l m ≈ ret (m,(l,(Maps.add id v g,tt))).
  Proof.
    intros.
    unfold interp_cfg_to_L3.
    rewrite interp_intrinsics_trigger; cbn. 
    unfold Intrinsics.F_trigger.
    rewrite interp_global_trigger; cbn.
    rewrite interp_local_ret, interp_memory_ret.
    reflexivity.
  Qed.

  Lemma interp_cfg_to_L3_Load : forall defs t a g l m val,
      read m a t = inr val ->
      interp_cfg_to_L3 defs (trigger (Load t (DVALUE_Addr a))) g l m ≈ Ret (m,(l,(g,val))).
  Proof.
    intros * READ.
    unfold interp_cfg_to_L3.
    rewrite interp_intrinsics_trigger.
    cbn.
    unfold Intrinsics.F_trigger.
    rewrite interp_global_trigger.
    cbn.
    rewrite interp_local_bind, interp_local_trigger.
    cbn; rewrite bind_bind.
    rewrite interp_memory_bind, subevent_subevent.
    rewrite interp_memory_load; eauto.
    cbn.
    rewrite 2 bind_ret_l, interp_local_ret, interp_memory_ret.
    reflexivity.
  Qed.

  Lemma interp_cfg_to_L3_store :
    forall (m m' : memory_stack) (t : dtyp) (val : dvalue) (a : addr) g l defs,
      write m a val = inr m' ->
      interp_cfg_to_L3 defs (trigger (Store (DVALUE_Addr a) val)) g l m ≈ ret (m',(l,(g,tt))).
  Proof.
    intros m m' t val a g l defs WRITE.
    unfold interp_cfg_to_L3.
    rewrite interp_intrinsics_trigger.
    cbn.
    unfold Intrinsics.F_trigger.
    rewrite interp_global_trigger.
    rewrite subevent_subevent.
    cbn.
    rewrite interp_local_bind, interp_local_trigger.
    cbn; rewrite bind_bind.
    rewrite interp_memory_bind, subevent_subevent.
    rewrite interp_memory_store; eauto.
    cbn.
    rewrite 2 bind_ret_l, interp_local_ret, interp_memory_ret.
    reflexivity.
  Qed.

  Arguments allocate : simpl never.
  Lemma interp_cfg_to_L3_alloca :
    forall (defs : intrinsic_definitions) (m : memory_stack) (t : dtyp) (g : global_env) l,
      non_void t ->
      exists m' a',
        allocate m t = inr (m', a') /\
        interp_cfg_to_L3 defs (trigger (Alloca t)) g l m ≈ ret (m', (l, (g, DVALUE_Addr a'))).
  Proof.
    intros * NV.
    unfold interp_cfg_to_L3.
    eapply interp_memory_alloca_exists in NV as [m' [a' [ALLOC INTERP]]].
    exists m'. exists a'.

    rewrite interp_intrinsics_trigger.
    cbn.
    unfold Intrinsics.F_trigger.
    rewrite interp_global_trigger.
    cbn.
    rewrite interp_local_bind, interp_local_trigger.
    cbn.
    rewrite bind_bind.
    rewrite interp_memory_bind.
    rewrite subevent_subevent, interp_memory_alloca; eauto.
    cbn.
    repeat rewrite bind_ret_l.
    cbn.
    rewrite interp_local_ret.
    rewrite interp_memory_ret.
    split; eauto.
    reflexivity.
    Unshelve.
    auto.
  Qed.

  Lemma interp_cfg_to_L3_intrinsic :
    forall (defs : intrinsic_definitions) (m : memory_stack) (τ : dtyp) (g : global_env) l fn args df res,
      assoc Strings.String.string_dec fn (defs_assoc defs) = Some df ->
      df args = inr res ->
      interp_cfg_to_L3 defs (trigger (Intrinsic τ fn args)) g l m ≈ ret (m, (l, (g, res))).
  Proof.
    intros defs m τ g l fn args df res LUP RES.
    unfold interp_cfg_to_L3.

    rewrite interp_intrinsics_trigger; cbn.
    rewrite LUP; cbn.
    rewrite RES.

    rewrite interp_global_ret.
    rewrite interp_local_ret.
    rewrite interp_memory_ret.

    reflexivity.
  Qed.

  Lemma interp_cfg_to_L3_GEP_array : forall defs t a size g l m val i,
      get_array_cell m a i t = inr val ->
      exists ptr,
        interp_cfg_to_L3 defs (trigger (GEP
                                  (DTYPE_Array size t)
                                  (DVALUE_Addr a)
                                  [DVALUE_I64 (Integers.Int64.repr 0); DVALUE_I64 (Integers.Int64.repr (Z.of_nat i))])) g l m
                      ≈ Ret (m, (l, (g, DVALUE_Addr ptr))) /\
        read m ptr t = inr val.
  Proof.
    intros defs t a size g l m val i GET.
    epose proof @interp_memory_GEP_array _ (PickE +' UBE +' DebugE +' FailureE) _ _ _ t _ size _ _ _ GET as [ptr [INTERP READ]].
    exists ptr.
    split; auto.

    unfold interp_cfg_to_L3.
    rewrite interp_intrinsics_trigger; cbn.
    unfold Intrinsics.F_trigger.
    rewrite subevent_subevent.
    rewrite interp_global_trigger; cbn.
    rewrite subevent_subevent.
    rewrite interp_local_bind, interp_local_trigger.
    cbn.
    rewrite subevent_subevent.
    repeat rewrite interp_memory_bind.
    rewrite INTERP.
    rewrite bind_bind.
    rewrite bind_ret_l.
    rewrite interp_memory_ret.
    rewrite bind_ret_l.
    rewrite interp_local_ret.
    rewrite interp_memory_ret.
    reflexivity.
  Qed.

  (**
     YZ : Should be obsolete. Keeping it around for a bit
   *)
  (*
  Lemma interp_cfg_to_L3_LM : forall defs t a size offset g l m v bytes concrete_id,
      get_logical_block m a = Some (LBlock size bytes concrete_id) ->
      deserialize_sbytes (lookup_all_index offset (sizeof_dtyp t) bytes SUndef) t = v ->
      interp_cfg_to_L3 defs (trigger (Load t (DVALUE_Addr (a, offset)))) g l m ≈ Ret (m,(l,(g,v))).
  Proof.
    intros * LUL EQ.
    unfold interp_cfg_to_L3.
    rewrite interp_intrinsics_trigger.
    cbn.
    unfold Intrinsics.F_trigger.
    rewrite interp_global_trigger.
    cbn.
    rewrite interp_local_bind, interp_local_trigger.
    cbn; rewrite bind_bind.
    rewrite interp_memory_bind, interp_memory_trigger.
    cbn.
    destruct m as [mem memstack]. cbn.
    cbn in LUL. unfold read.
    cbn; rewrite LUL.
    rewrite 2 bind_ret_l, interp_local_ret, interp_memory_ret.
    unfold read_in_mem_block.
    rewrite EQ.
    reflexivity.
  Qed.
   *)

End InterpreterCFG.
