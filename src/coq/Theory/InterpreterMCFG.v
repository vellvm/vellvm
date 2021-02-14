From Coq Require Import
     Morphisms ZArith.

From ITree Require Import
     ITree
     Basics.Monad
     Events.StateFacts
     Eq.Eq.

From Vellvm Require Import
     Utils.Tactics
     Utils.Util
     Syntax.DynamicTypes
     Semantics.LLVMEvents
     Handlers.Handlers.


Section InterpreterMCFG.

  (**
   Partial interpretations of the trees produced by the denotation of _VIR_ programs.
   The intent is to allow us to only interpret as many layers as needed
   to perform the required semantic reasoning, and lift for free the
   equivalence down the pipe.
   This gives us a _vertical_ notion of compositionality.
   *)

  Definition interp1 {R} (t: itree L0 R) g :=
    let uvalue_trace       := interp_intrinsics t in
    let L1_trace           := interp_global uvalue_trace g in
    L1_trace.

  Definition interp2 {R} (t: itree L0 R) g l :=
    let uvalue_trace   := interp_intrinsics t in
    let L1_trace       := interp_global uvalue_trace g in
    let L2_trace       := interp_local_stack (handle_local (v:=uvalue)) L1_trace l in
    L2_trace.

  Definition interp3 {R} (t: itree L0 R) g l m :=
    let uvalue_trace   := interp_intrinsics t in
    let L1_trace       := interp_global uvalue_trace g in
    let L2_trace       := interp_local_stack (handle_local (v:=uvalue)) L1_trace l in
    let L3_trace       := interp_memory L2_trace m in
    L3_trace.

  Definition interp4 {R} RR (t: itree L0 R) g l m :=
    let uvalue_trace   := interp_intrinsics t in
    let L1_trace       := interp_global uvalue_trace g in
    let L2_trace       := interp_local_stack (handle_local (v:=uvalue)) L1_trace l in
    let L3_trace       := interp_memory L2_trace m in
    let L4_trace       := model_undef RR L3_trace in
    L4_trace.

  Definition interp5 {R} RR (t: itree L0 R) g l m :=
    let uvalue_trace   := interp_intrinsics t in
    let L1_trace       := interp_global uvalue_trace g in
    let L2_trace       := interp_local_stack (handle_local (v:=uvalue)) L1_trace l in
    let L3_trace       := interp_memory L2_trace m in
    let L4_trace       := model_undef RR L3_trace in
    model_UB RR L4_trace.

  (* The interpreter stray away from the model starting from the fourth layer: we pick an arbitrary valid path of execution *)
  Definition interp4_exec {R} (t: itree L0 R) g l m :=
    let uvalue_trace   := interp_intrinsics t in
    let L1_trace       := interp_global uvalue_trace g in
    let L2_trace       := interp_local_stack (handle_local (v:=uvalue)) L1_trace l in
    let L3_trace       := interp_memory L2_trace m in
    let L4_trace       := exec_undef L3_trace in
    L4_trace.

  Definition interp5_exec {R} (t: itree L0 R) g l m :=
    let uvalue_trace   := interp_intrinsics t in
    let L1_trace       := interp_global uvalue_trace g in
    let L2_trace       := interp_local_stack (handle_local (v:=uvalue)) L1_trace l in
    let L3_trace       := interp_memory L2_trace m in
    let L4_trace       := exec_undef L3_trace in
    exec_UB L4_trace.

  Section Structural_Lemmas.

    Lemma interp1_bind :
      forall {R S} (t: itree L0 R) (k: R -> itree L0 S) g, 
        interp1 (ITree.bind t k) g ≈
                     (ITree.bind (interp1 t g) (fun '(g',x) => interp1 (k x) g')).
    Proof.
      intros.
      unfold interp1.
      rewrite interp_intrinsics_bind, interp_global_bind.
      apply eutt_eq_bind; intros (? & ?); reflexivity.
    Qed.

    Lemma interp1_ret : forall (R : Type) g (x : R), interp1 (Ret x) g ≈ Ret (g,x).
    Proof.
      intros; unfold interp1.
      rewrite interp_intrinsics_ret, interp_global_ret; reflexivity.
    Qed.

    Lemma interp2_bind :
      forall {R S} (t: itree L0 R) (k: R -> itree L0 S) g l,
        interp2 (ITree.bind t k) g l ≈
                     (ITree.bind (interp2 t g l) (fun '(g',(l',x)) => interp2 (k x) l' g')).
    Proof.
      intros.
      unfold interp2.
      rewrite interp_intrinsics_bind, interp_global_bind, interp_local_stack_bind.
      apply eutt_eq_bind; intros (? & ? & ?); reflexivity.
    Qed.

    Lemma interp2_ret : forall (R : Type) g l (x : R), interp2 (Ret x) g l ≈ Ret (l, (g, x)).
    Proof.
      intros; unfold interp2.
      rewrite interp_intrinsics_ret, interp_global_ret, interp_local_stack_ret; reflexivity.
    Qed.

    Lemma interp3_bind :
      forall {R S} (t: itree L0 R) (k: R -> itree L0 S) g l m,
        interp3 (ITree.bind t k) g l m ≈
                     (ITree.bind (interp3 t g l m) (fun '(m',(l',(g',x))) => interp3 (k x) g' l' m')).
    Proof.
      intros.
      unfold interp3.
      rewrite interp_intrinsics_bind, interp_global_bind, interp_local_stack_bind, interp_memory_bind.
      apply eutt_eq_bind; intros (? & ? & ? & ?); reflexivity.
    Qed.

    Lemma interp3_ret : forall (R : Type) g l m (x : R), interp3 (Ret x) g l m ≈ Ret (m, (l, (g,x))).
    Proof.
      intros; unfold interp3.
      rewrite interp_intrinsics_ret, interp_global_ret, interp_local_stack_ret, interp_memory_ret; reflexivity.
    Qed.

    Global Instance eutt_interp1 {T}:
      Proper (eutt Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp1 T).
    Proof.
      repeat intro.
      unfold interp1.
      subst; rewrite H.
      reflexivity.
    Qed.

    Global Instance eutt_interp2 {T}:
      Proper (eutt Logic.eq ==> Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp2 T).
    Proof.
      repeat intro.
      unfold interp2.
      subst; rewrite H.
      reflexivity.
    Qed.

    Global Instance eutt_interp3 {T}:
      Proper (eutt Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp3 T).
    Proof.
      repeat intro.
      unfold interp3.
      subst; rewrite H.
      reflexivity.
    Qed.

    (* NOTEYZ: This can probably be refined to [eqit eq] instead of [eutt eq], but I don't think it matters to us *)
    Lemma interp3_vis: 
      forall T R (e : L0 T) (k : T -> itree L0 R) g l m,
        interp3 (Vis e k) g l m ≈ 
                     ITree.bind (interp3 (trigger e) g l m)
                     (fun '(m, (l, (g, x)))=> interp3 (k x) g l m).
    Proof.
      intros.
      unfold interp3.
      rewrite interp_intrinsics_vis.
      rewrite interp_global_bind, interp_local_stack_bind, interp_memory_bind.
      unfold trigger; rewrite interp_intrinsics_vis.
      rewrite interp_global_bind, interp_local_stack_bind, interp_memory_bind.
      rewrite Eq.bind_bind.
      apply eutt_eq_bind.
      intros (? & ? & ? & ?).
      rewrite interp_intrinsics_ret, interp_global_ret, interp_local_stack_ret, interp_memory_ret, bind_ret_l.
      reflexivity.
    Qed.

    Lemma interp3_bind_trigger :
      forall T R (e : L0 T) (k : T -> itree L0 R) g l m,
        interp3 (ITree.bind (trigger e) k) g l m ≈ 
                     ITree.bind (interp3 (trigger e) g l m)
                     (fun '(m, (l, (g, x)))=> interp3 (k x) g l m).
    Proof.
      intros.
      rewrite bind_trigger.
      rewrite interp3_vis at 1.
      reflexivity.
    Qed.

    Lemma interp3_GW : forall id g l m v,
        interp3 (trigger (GlobalWrite id v)) g l m ≈ ret (m,(l,(Maps.add id v g,tt))).
    Proof.
      intros.
      unfold interp3.
      rewrite interp_intrinsics_trigger; cbn. 
      unfold Intrinsics.F_trigger.
      rewrite interp_global_trigger; cbn.
      unfold interp_local_stack.
      rewrite interp_state_ret, interp_memory_ret.
      reflexivity.
    Qed.

    Lemma interp_cfg3_LM : forall t a size offset g l m v bytes concrete_id,
        get_logical_block m a = Some (LBlock size bytes concrete_id) ->
        deserialize_sbytes (lookup_all_index offset (sizeof_dtyp t) bytes SUndef) t = v ->
        interp3 (trigger (Load t (DVALUE_Addr (a, offset)))) g l m ≈ Ret (m,(l,(g,v))).
    Proof.
      intros * LUL EQ.
      unfold interp3.
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

    Lemma interp3_alloca :
      forall (m : memory_stack) (t : dtyp) (g : global_env) l,
        non_void t ->
        exists m' a',
          allocate m t = inr (m', a') /\
          interp3 (trigger (Alloca t)) g l m ≈ ret (m', (l, (g, DVALUE_Addr a'))).
    Proof.
      intros * NV.
      unfold interp3.
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
    |- context[interp_global (interp_intrinsics ?p) ?g] =>
    replace (interp_global (interp_intrinsics p) g) with
    (interp1 p g) by reflexivity
  end.

Ltac fold_L2 :=
  match goal with
    |- context[interp_local_stack ?h
                                 (interp_global (interp_intrinsics ?p) ?g) ?l] =>
    replace (interp_local_stack h (interp_global (interp_intrinsics p) g) l) with
    (interp2 p g l) by reflexivity
  end.

Ltac fold_L3 :=
  match goal with
    |- context[
          interp_memory
            (interp_local_stack ?h
                                (interp_global (interp_intrinsics ?p) ?g) ?l) ?m] =>
    replace (interp_memory (interp_local_stack h (interp_global (interp_intrinsics p) g) l) m) with
    (interp3 p g l m) by reflexivity
  end.

Ltac fold_L4 :=
  match goal with
    |- context[
          model_undef ?RR
            (interp_memory
               (interp_local_stack ?h
                                   (interp_global (interp_intrinsics ?p) ?g) ?l) ?m)] =>
    replace (model_undef ?RR (interp_memory (interp_local_stack h (interp_global (interp_intrinsics p) g) l) m)) with
    (interp4 RR p g l m) by reflexivity
  end.

Ltac fold_L5 :=
  match goal with
    |- context[model_UB ?RR (model_undef (Logic.eq) (interp_memory (interp_local_stack ?h (interp_global (interp_intrinsics ?p) ?g) ?l) ?m))] =>
    replace (model_UB ?RR (model_undef (Logic.eq) (interp_memory (interp_local_stack h (interp_global (interp_intrinsics p) g) l) m))) with
    (interp5 RR p g l m) by reflexivity
  end.
