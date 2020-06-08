From Coq Require Import
     Morphisms ZArith.

From ITree Require Import
     ITree
     Basics.Monad
     Events.StateFacts
     Eq.Eq.

From Vellvm Require Import
     Util
     Tactics
     LLVMEvents
     DynamicTypes
     Handlers.Handlers.

Section InterpreterMCFG.

  (**
   Partial interpretations of the trees produced by the denotation of _VIR_ programs.
   The intent is to allow us to only interpret as many layers as needed
   to perform the required semantic reasoning, and lift for free the
   equivalence down the pipe.
   This gives us a _vertical_ notion of compositionality.
   *)

  Definition interp_to_L1 {R} user_intrinsics (t: itree L0 R) g :=
    let uvalue_trace       := interp_intrinsics user_intrinsics t in
    let L1_trace           := interp_global uvalue_trace g in
    L1_trace.

  Definition interp_to_L2 {R} user_intrinsics (t: itree L0 R) g l :=
    let uvalue_trace   := interp_intrinsics user_intrinsics t in
    let L1_trace       := interp_global uvalue_trace g in
    let L2_trace       := interp_local_stack (handle_local (v:=uvalue)) L1_trace l in
    L2_trace.

  Definition interp_to_L3 {R} user_intrinsics (t: itree L0 R) g l m :=
    let uvalue_trace   := interp_intrinsics user_intrinsics t in
    let L1_trace       := interp_global uvalue_trace g in
    let L2_trace       := interp_local_stack (handle_local (v:=uvalue)) L1_trace l in
    let L3_trace       := interp_memory L2_trace m in
    L3_trace.

  Definition interp_to_L4 {R} user_intrinsics (t: itree L0 R) g l m :=
    let uvalue_trace   := interp_intrinsics user_intrinsics t in
    let L1_trace       := interp_global uvalue_trace g in
    let L2_trace       := interp_local_stack (handle_local (v:=uvalue)) L1_trace l in
    let L3_trace       := interp_memory L2_trace m in
    let L4_trace       := model_undef L3_trace in
    L4_trace.

  Definition interp_to_L5 {R} user_intrinsics (t: itree L0 R) g l m :=
    let uvalue_trace   := interp_intrinsics user_intrinsics t in
    let L1_trace       := interp_global uvalue_trace g in
    let L2_trace       := interp_local_stack (handle_local (v:=uvalue)) L1_trace l in
    let L3_trace       := interp_memory L2_trace m in
    let L4_trace       := model_undef L3_trace in
    model_UB L4_trace.

  (* The interpreter stray away from the model starting from the fourth layer: we pick an arbitrary valid path of execution *)
  Definition interp_to_L4_exec {R} user_intrinsics (t: itree L0 R) g l m :=
    let uvalue_trace   := interp_intrinsics user_intrinsics t in
    let L1_trace       := interp_global uvalue_trace g in
    let L2_trace       := interp_local_stack (handle_local (v:=uvalue)) L1_trace l in
    let L3_trace       := interp_memory L2_trace m in
    let L4_trace       := exec_undef L3_trace in
    L4_trace.

  Definition interp_to_L5_exec {R} user_intrinsics (t: itree L0 R) g l m :=
    let uvalue_trace   := interp_intrinsics user_intrinsics t in
    let L1_trace       := interp_global uvalue_trace g in
    let L2_trace       := interp_local_stack (handle_local (v:=uvalue)) L1_trace l in
    let L3_trace       := interp_memory L2_trace m in
    let L4_trace       := exec_undef L3_trace in
    exec_UB L4_trace.

  Section Structural_Lemmas.

    Lemma interp_to_L1_bind :
      forall ui {R S} (t: itree L0 R) (k: R -> itree L0 S) g, 
        interp_to_L1 ui (ITree.bind t k) g ≈
                     (ITree.bind (interp_to_L1 ui t g) (fun '(g',x) => interp_to_L1 ui (k x) g')).
    Proof.
      intros.
      unfold interp_to_L1.
      rewrite interp_intrinsics_bind, interp_global_bind.
      apply eutt_eq_bind; intros (? & ?); reflexivity.
    Qed.

    Lemma interp_to_L1_ret : forall ui (R : Type) g (x : R), interp_to_L1 ui (Ret x) g ≈ Ret (g,x).
    Proof.
      intros; unfold interp_to_L1.
      rewrite interp_intrinsics_ret, interp_global_ret; reflexivity.
    Qed.

    Lemma interp_to_L2_bind :
      forall ui {R S} (t: itree L0 R) (k: R -> itree L0 S) g l,
        interp_to_L2 ui (ITree.bind t k) g l ≈
                     (ITree.bind (interp_to_L2 ui t g l) (fun '(g',(l',x)) => interp_to_L2 ui (k x) l' g')).
    Proof.
      intros.
      unfold interp_to_L2.
      rewrite interp_intrinsics_bind, interp_global_bind, interp_local_stack_bind.
      apply eutt_eq_bind; intros (? & ? & ?); reflexivity.
    Qed.

    Lemma interp_to_L2_ret : forall ui (R : Type) g l (x : R), interp_to_L2 ui (Ret x) g l ≈ Ret (l, (g, x)).
    Proof.
      intros; unfold interp_to_L2.
      rewrite interp_intrinsics_ret, interp_global_ret, interp_local_stack_ret; reflexivity.
    Qed.

    Lemma interp_to_L3_bind :
      forall ui {R S} (t: itree L0 R) (k: R -> itree L0 S) g l m,
        interp_to_L3 ui (ITree.bind t k) g l m ≈
                     (ITree.bind (interp_to_L3 ui t g l m) (fun '(m',(l',(g',x))) => interp_to_L3 ui (k x) g' l' m')).
    Proof.
      intros.
      unfold interp_to_L3.
      rewrite interp_intrinsics_bind, interp_global_bind, interp_local_stack_bind, interp_memory_bind.
      apply eutt_eq_bind; intros (? & ? & ? & ?); reflexivity.
    Qed.

    Lemma interp_to_L3_ret : forall ui (R : Type) g l m (x : R), interp_to_L3 ui (Ret x) g l m ≈ Ret (m, (l, (g,x))).
    Proof.
      intros; unfold interp_to_L3.
      rewrite interp_intrinsics_ret, interp_global_ret, interp_local_stack_ret, interp_memory_ret; reflexivity.
    Qed.

    Global Instance eutt_interp_to_L1 (defs: intrinsic_definitions) {T}:
      Proper (eutt Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp_to_L1 T defs).
    Proof.
      repeat intro.
      unfold interp_to_L1.
      subst; rewrite H.
      reflexivity.
    Qed.

    Global Instance eutt_interp_to_L2 (defs: intrinsic_definitions) {T}:
      Proper (eutt Logic.eq ==> Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp_to_L2 T defs).
    Proof.
      repeat intro.
      unfold interp_to_L2.
      subst; rewrite H.
      reflexivity.
    Qed.

    Global Instance eutt_interp_to_L3 (defs: intrinsic_definitions) {T}:
      Proper (eutt Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp_to_L3 T defs).
    Proof.
      repeat intro.
      unfold interp_to_L3.
      subst; rewrite H.
      reflexivity.
    Qed.

    (* NOTEYZ: This can probably be refined to [eqit eq] instead of [eutt eq], but I don't think it matters to us *)
    Lemma interp_to_L3_vis (defs: IS.intrinsic_definitions):
      forall T R (e : L0 T) (k : T -> itree L0 R) g l m,
        interp_to_L3 defs (Vis e k) g l m ≈ 
                     ITree.bind (interp_to_L3 defs (trigger e) g l m)
                     (fun '(m, (l, (g, x)))=> interp_to_L3 defs (k x) g l m).
    Proof.
      intros.
      unfold interp_to_L3.
      rewrite interp_intrinsics_vis.
      rewrite interp_global_bind, interp_local_stack_bind, interp_memory_bind.
      unfold trigger; rewrite interp_intrinsics_vis.
      rewrite interp_global_bind, interp_local_stack_bind, interp_memory_bind.
      rewrite Eq.bind_bind.
      apply eutt_eq_bind.
      intros (? & ? & ? & ?).
      do 2 match goal with
             |- context[interp ?x ?t] => replace (interp x t) with (interp_intrinsics defs t) by reflexivity
           end. 
      rewrite interp_intrinsics_ret, interp_global_ret, interp_local_stack_ret, interp_memory_ret, bind_ret_l.
      reflexivity.
    Qed.

    Lemma interp_to_L3_bind_trigger (defs: IS.intrinsic_definitions):
      forall T R (e : L0 T) (k : T -> itree L0 R) g l m,
        interp_to_L3 defs (ITree.bind (trigger e) k) g l m ≈ 
                     ITree.bind (interp_to_L3 defs (trigger e) g l m)
                     (fun '(m, (l, (g, x)))=> interp_to_L3 defs (k x) g l m).
    Proof.
      intros.
      rewrite bind_trigger.
      rewrite interp_to_L3_vis at 1.
      reflexivity.
    Qed.

    Lemma interp_to_L3_GW : forall defs id g l m v,
        interp_to_L3 defs (trigger (GlobalWrite id v)) g l m ≈ ret (m,(l,(Maps.add id v g,tt))).
    Proof.
      intros.
      unfold interp_to_L3.
      rewrite interp_intrinsics_trigger; cbn. 
      unfold Intrinsics.F_trigger.
      rewrite interp_global_trigger; cbn.
      unfold interp_local_stack.
      rewrite interp_state_ret, interp_memory_ret.
      reflexivity.
    Qed.

    Lemma interp_cfg_to_L3_LM : forall defs t a size offset g l m v bytes concrete_id,
        get_logical_block m a = Some (LBlock size bytes concrete_id) ->
        deserialize_sbytes (lookup_all_index offset (sizeof_dtyp t) bytes SUndef) t = v ->
        interp_to_L3 defs (trigger (Load t (DVALUE_Addr (a, offset)))) g l m ≈ Ret (m,(l,(g,v))).
    Proof.
      intros * LUL EQ.
      unfold interp_to_L3.
      rewrite interp_intrinsics_trigger.
      cbn.
      unfold Intrinsics.F_trigger.
      rewrite interp_global_trigger.
      cbn.
      unfold interp_local_stack.
      rewrite interp_state_bind.
      rewrite interp_state_trigger.
      cbn. rewrite bind_bind.
      rewrite bind_trigger.
      rewrite interp_memory_vis.
      cbn.
      destruct m as [mem memstack]. cbn.
      cbn in LUL. unfold read.
      cbn; rewrite LUL.
      cbn; rewrite 2 bind_ret_l.
      rewrite interp_state_ret.
      rewrite interp_memory_ret.
      cbn in *.
      unfold read_in_mem_block. rewrite EQ.
      reflexivity.
    Qed.

    Lemma interp_to_L3_alloca :
      forall (defs : intrinsic_definitions) (m : memory_stack) (t : dtyp) (g : global_env) l,
        non_void t ->
        exists m' a',
          allocate m t = inr (m', a') /\
          interp_to_L3 defs (trigger (Alloca t)) g l m ≈ ret (m', (l, (g, DVALUE_Addr a'))).
    Proof.
      intros * NV.
      unfold interp_to_L3.
      eapply interp_memory_alloca_exists in NV as [m' [a' [ALLOC INTERP]]].
      exists m'. exists a'.

      rewrite interp_intrinsics_trigger.
      cbn.
      unfold Intrinsics.F_trigger.
      rewrite interp_global_trigger.
      cbn.
      unfold interp_local_stack.
      rewrite interp_state_bind.
      rewrite interp_state_trigger.
      cbn.
      rewrite bind_bind.
      rewrite interp_memory_bind.
      rewrite subevent_subevent, interp_memory_alloca; eauto.
      cbn.
      repeat rewrite bind_ret_l.
      cbn.
      rewrite interp_state_ret.
      rewrite interp_memory_ret.
      split; eauto.
      reflexivity.
      Unshelve.
      auto.
    Qed.

  End Structural_Lemmas.

End InterpreterMCFG.

Ltac fold_L1 :=
  match goal with
    |- context[interp_global (interp_intrinsics ?ui ?p) ?g] =>
    replace (interp_global (interp_intrinsics ui p) g) with
    (interp_to_L1 ui p g) by reflexivity
  end.

Ltac fold_L2 :=
  match goal with
    |- context[interp_local_stack ?h
                                 (interp_global (interp_intrinsics ?ui ?p) ?g) ?l] =>
    replace (interp_local_stack h (interp_global (interp_intrinsics ui p) g) l) with
    (interp_to_L2 ui p g l) by reflexivity
  end.

Ltac fold_L3 :=
  match goal with
    |- context[
          interp_memory
            (interp_local_stack ?h
                                (interp_global (interp_intrinsics ?ui ?p) ?g) ?l) ?m] =>
    replace (interp_memory (interp_local_stack h (interp_global (interp_intrinsics ui p) g) l) m) with
    (interp_to_L3 ui p g l m) by reflexivity
  end.

Ltac fold_L4 :=
  match goal with
    |- context[
          model_undef
            (interp_memory
               (interp_local_stack ?h
                                   (interp_global (interp_intrinsics ?ui ?p) ?g) ?l) ?m)] =>
    replace (model_undef (interp_memory (interp_local_stack h (interp_global (interp_intrinsics ui p) g) l) m)) with
    (interp_to_L4 ui p g l m) by reflexivity
  end.

Ltac fold_L5 :=
  match goal with
    |- context[model_UB (model_undef (interp_memory (interp_local_stack ?h (interp_global (interp_intrinsics ?ui ?p) ?g) ?l) ?m))] =>
    replace (model_UB (model_undef (interp_memory (interp_local_stack h (interp_global (interp_intrinsics ui p) g) l) m))) with
    (interp_to_L5 ui p g l m) by reflexivity
  end.
