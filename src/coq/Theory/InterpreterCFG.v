(* begin hide *)
From Coq Require Import
     Morphisms String.

Require Import List.
Import ListNotations.
Require Import ZArith.

From ITree Require Import
     ITree
     Basics.Monad
     Eq.Eqit.

From Vellvm Require Import
     Utilities
     Syntax
     Semantics
     Theory.Refinement.

Import ITreeNotations.
Import SemNotations.
(* end hide *)

(** * General facts on the CFG-level interpretation
  A collection of elementary facts about the interpretation when considering an intra-function piece of syntax 
*)

(* TO MOVE *)
Arguments Intrinsics.F_trigger/.
Arguments String.append : simpl never.
Arguments allocate : simpl never.
Arguments defs_assoc: simpl never.

Module CFGTactics.

  (* Note: does not commute triggers for memory since those are more involved, we rely on specific lemmas *)
  Ltac go :=
    repeat match goal with
           | |- context [interp_intrinsics (ITree.bind _ _)] => rewrite interp_intrinsics_bind
           | |- context [interp_global (ITree.bind _ _)] => rewrite interp_global_bind
           | |- context [interp_local (ITree.bind _ _)] => rewrite interp_local_bind
           | |- context [interp_memory (ITree.bind _ _)] => rewrite interp_memory_bind
           | |- context [interp_intrinsics (trigger _)] => rewrite interp_intrinsics_trigger; cbn; rewrite ?subevent_subevent
           | |- context [interp_global (trigger _)] => rewrite interp_global_trigger; cbn; rewrite ?subevent_subevent
           | |- context [interp_local (trigger _)] => rewrite interp_local_trigger; cbn; rewrite ?subevent_subevent
           | |- context [ITree.bind (ITree.bind _ _) _] => rewrite bind_bind
           | |- context [interp_intrinsics (Ret _)] => rewrite interp_intrinsics_ret
           | |- context [interp_global (Ret _)] => rewrite interp_global_ret
           | |- context [interp_local (Ret _)] => rewrite interp_local_ret
           | |- context [interp_memory (Ret _)] => rewrite interp_memory_ret
           | |- context [ITree.bind (Ret _) _] => rewrite bind_ret_l
           end.

End CFGTactics.

Import CFGTactics.

Lemma interp_cfg1_bind :
  forall {R S} (t: itree instr_E R) (k: R -> itree instr_E S) g, 
    ℑ1 (t >>= k) g ≈ '(g',x) <- ℑ1 t g ;; ℑ1 (k x) g'.
Proof.
  intros.
  unfold ℑ1.
  go.
  apply eutt_eq_bind; intros (? & ?); reflexivity.
Qed.

Lemma interp_cfg1_ret : forall (R : Type) g (x : R), ℑ1 (Ret x) g ≈ Ret (g,x).
Proof.
  intros; unfold ℑ1.
  go.
  reflexivity.
Qed.

Lemma interp_cfg2_bind :
  forall {R S} (t: itree instr_E R) (k: R -> itree instr_E S) g l,
    ℑ2 (t >>= k) g l ≈ '(g',(l',x)) <- ℑ2 t g l ;; ℑ2 (k x) l' g'.
Proof.
  intros.
  unfold ℑ2.
  go.
  apply eutt_eq_bind; intros (? & ? & ?); reflexivity.
Qed.

Lemma interp_cfg2_ret : forall (R : Type) g l (x : R), ℑ2 (Ret x) g l ≈ Ret (l, (g, x)).
Proof.
  intros; unfold ℑ2.
  go.
  reflexivity.
Qed.

Lemma interp_cfg3_bind :
  forall {R S} (t: itree instr_E R) (k: R -> itree instr_E S) g l m,
    ℑ3 (t >>= k) g l m ≈
       '(m',(l',(g',x))) <- ℑ3 t g l m ;; ℑ3 (k x) g' l' m'.
Proof.
  intros.
  unfold ℑ3.
  go.
  apply eutt_eq_bind; intros3; reflexivity.
Qed.

Lemma interp_cfg3_ret : forall (R : Type) g l m (x : R), ℑ3 (Ret x) g l m ≈ Ret3 g l m x.
Proof.
  intros; unfold ℑ3.
  go.
  reflexivity.
Qed.

#[global] Instance eutt_interp_cfg1 {T}:
  Proper (eutt eq ==> eq ==> eutt eq) (@ℑ1 T).
Proof.
  repeat intro.
  unfold ℑ1.
  subst; rewrite H.
  reflexivity.
Qed.

#[global] Instance eutt_interp_cfg2 {T}:
  Proper (eutt eq ==> eq ==> eq ==> eutt eq) (@ℑ2 T).
Proof.
  repeat intro.
  unfold ℑ2.
  subst; rewrite H.
  reflexivity.
Qed.

#[global] Instance eutt_interp_cfg3 {T}:
  Proper (eutt eq ==> eq ==> eq ==> eq ==> eutt eq) (@ℑ3 T).
Proof.
  repeat intro.
  unfold ℑ3.
  subst; rewrite H.
  reflexivity.
Qed.

Lemma interp_cfg3_vis :
  forall T R (e : instr_E T) (k : T -> itree instr_E R) g l m,
    ℑ3 (Vis e k) g l m ≈ '(m, (l, (g, x))) <- ℑ3 (trigger e) g l m;; ℑ3 (k x) g l m.
Proof.
  intros.
  unfold ℑ3.
  rewrite interp_intrinsics_vis.
  go.
  apply eutt_eq_bind.
  intros3; go.
  reflexivity.
Qed.

Lemma interp_cfg3_bind_trigger :
  forall T R (e : instr_E T) (k : T -> itree instr_E R) g l m,
    ℑ3 (trigger e >>= k) g l m ≈ 
       '(m, (l, (g, x))) <- ℑ3 (trigger e) g l m ;; ℑ3 (k x) g l m.
Proof.
  intros.
  unfold ℑ3.
  go.
  apply eutt_eq_bind.
  intros3.
  reflexivity.
Qed.

Lemma interp_cfg3_GR : forall id g l m v,
    Maps.lookup id g = Some v ->
    ℑ3 (trigger (GlobalRead id)) g l m ≈ Ret3 g l m v.
Proof.
  intros * LU.
  unfold ℑ3.
  go. 
  cbn in *; rewrite LU.
  go.
  reflexivity.
Qed.

Lemma interp_cfg3_LR : forall id g l m v,
    Maps.lookup id l = Some v ->
    ℑ3 (trigger (LocalRead id)) g l m ≈ Ret3 g l m v.
Proof.
  intros * LU.
  unfold ℑ3.
  go.
  cbn in *; rewrite LU.
  go.
  reflexivity.
Qed.

Lemma interp_cfg3_LW : forall id g l m v,
    ℑ3 (trigger (LocalWrite id v)) g l m ≈ Ret3 g (Maps.add id v l) m tt.
Proof.
  intros.
  unfold ℑ3.
  go.
  reflexivity.
Qed.

Lemma interp_cfg3_GW : forall id g l m v,
    ℑ3 (trigger (GlobalWrite id v)) g l m ≈ Ret3 (Maps.add id v g) l m tt.
Proof.
  intros.
  unfold ℑ3.
  go; reflexivity.
Qed.

Lemma interp_cfg3_GR_fail : forall id g l m,
    Maps.lookup id g = None ->
    ℑ3 (trigger (GlobalRead id)) g l m ≈ raise ("Could not look up global id " ++ CeresSerialize.to_string id).
Proof.
  intros * LU.
  unfold interp_cfg3.
  go.
  cbn in *; rewrite LU.
  unfold raise; cbn.
  go.
  rewrite interp_memory_trigger; cbn; rewrite subevent_subevent, bind_bind.
  apply eutt_eq_bind; intros [].
Qed.

Lemma interp_cfg3_LR_fail : forall id g l m,
    Maps.lookup id l = None ->
    ℑ3 (trigger (LocalRead id)) g l m ≈ raise ("Could not look up id " ++ CeresSerialize.to_string id).
Proof.
  intros * LU.
  unfold interp_cfg3.
  go.
  cbn in *; rewrite LU.
  unfold raise; cbn.
  go.
  rewrite interp_memory_trigger; cbn; rewrite subevent_subevent, bind_bind.
  apply eutt_eq_bind; intros [].
Qed.

Lemma interp_cfg3_pick : forall u P m l g,
    ℑ3 (trigger (pick u P)) g l m ≈ v <- trigger (pick u P);; Ret3 g l m v.
Proof.
  intros.
  unfold interp_cfg3.
  go.
  rewrite interp_memory_trigger; cbn.
  rewrite subevent_subevent, bind_bind.
  apply eutt_eq_bind; intros.
  go.
  reflexivity.
Qed.

Lemma interp_cfg3_UB : forall s m l g,
    ℑ3 (trigger (ThrowUB s)) g l m ≈ v <- trigger (ThrowUB s);; Ret3 g l m v.
Proof.
  intros.
  unfold interp_cfg3.
  go.
  rewrite interp_memory_trigger; cbn.
  rewrite subevent_subevent, bind_bind.
  apply eutt_eq_bind; intros.
  go.
  reflexivity.
Qed.

Lemma interp_cfg3_Load : forall t a g l m val,
    read m a t = inr val ->
    ℑ3 (trigger (Load t (DVALUE_Addr a))) g l m ≈ Ret3 g l m val. 
Proof.
  intros * READ.
  unfold ℑ3.
  go.
  rewrite interp_memory_load; eauto.
  go.
  reflexivity.
Qed.

Lemma interp_cfg3_store :
  forall (m m' : memory_stack) (val : dvalue) (a : addr) g l,
    write m a val = inr m' ->
    ℑ3 (trigger (Store (DVALUE_Addr a) val)) g l m ≈ Ret3 g l m' tt.
Proof.
  intros * WRITE.
  unfold ℑ3.
  go.
  rewrite interp_memory_store; eauto.
  go.
  reflexivity.
Qed.

Lemma interp_cfg3_alloca :
  forall (m : memory_stack) (t : dtyp) (g : global_env) l,
    non_void t ->
    exists m' a',
      allocate m t = inr (m', a') /\
      ℑ3 (trigger (Alloca t)) g l m ≈ Ret3 g l m' (DVALUE_Addr a').
Proof.
  intros * NV.
  unfold ℑ3.
  eapply (@interp_memory_alloca_exists _ L3)in NV as (m' & a' & ALLOC & INTERP).
  exists m', a'. 
  split; eauto.
  go.
  rewrite interp_memory_alloca; eauto.
  go. reflexivity.
  Unshelve.
  auto.
Qed.

Lemma interp_cfg3_intrinsic :
  forall (m : memory_stack) (τ : dtyp) (g : global_env) l fn args df res,
    assoc fn defs_assoc = Some df ->
    df args = inr res ->
    ℑ3 (trigger (Intrinsic τ fn args)) g l m ≈ Ret3 g l m res.
Proof.
  intros m τ g l fn args df res LUP RES.
  unfold ℑ3.
  go.
  rewrite LUP; cbn.
  rewrite RES.
  go.
  reflexivity.
Qed.

Lemma interp_cfg3_GEP_array' : forall t a size g l m val i,
    get_array_cell m a i t = inr val ->
    exists ptr,
      ℑ3 (trigger (GEP
                     (DTYPE_Array size t)
                     (DVALUE_Addr a)
                     [DVALUE_I64 (Integers.Int64.repr 0); DVALUE_I64 (Integers.Int64.repr (Z.of_nat i))])) g l m
         ≈ Ret3 g l m (DVALUE_Addr ptr) /\
      handle_gep_addr (DTYPE_Array size t) a [DVALUE_I64 (repr 0); DVALUE_I64 (repr (Z.of_nat i))] = inr ptr /\
      read m ptr t = inr val.
Proof.
  intros * GET.
  epose proof @interp_memory_GEP_array' _ (PickE +' UBE +' DebugE +' FailureE) _ _ _ t _ size _ _ _ GET as [ptr [INTERP READ]].
  exists ptr.
  split; auto.

  unfold ℑ3.
  go.
  rewrite INTERP.
  go.
  reflexivity.
Qed.

Lemma interp_cfg3_GEP_array_no_read_addr : forall t a size g l m i ptr,
    dtyp_fits m a (DTYPE_Array size t) ->
    handle_gep_addr (DTYPE_Array size t) a [DVALUE_I64 (repr 0); DVALUE_I64 (repr (Z.of_nat i))] = inr ptr ->
    ℑ3 (trigger (GEP
                   (DTYPE_Array size t)
                   (DVALUE_Addr a)
                   [DVALUE_I64 (Integers.Int64.repr 0); DVALUE_I64 (Integers.Int64.repr (Z.of_nat i))])) g l m
       ≈ Ret3 g l m (DVALUE_Addr ptr).
Proof.
  intros * FITS GEP.
  epose proof @interp_memory_GEP_array_no_read_addr _ (PickE +' UBE +' DebugE +' FailureE) _ _ _ t _ size _ _ ptr FITS as EQ.
  unfold ℑ3.
  go.
  rewrite EQ; eauto.
  go.
  reflexivity.
Qed.

Lemma interp_cfg3_GEP_array_no_read : forall t a size g l m i,
    dtyp_fits m a (DTYPE_Array size t) ->
    exists ptr,
      ℑ3 (trigger (GEP
                     (DTYPE_Array size t)
                     (DVALUE_Addr a)
                     [DVALUE_I64 (Integers.Int64.repr 0); DVALUE_I64 (Integers.Int64.repr (Z.of_nat i))])) g l m
         ≈ Ret3 g l m (DVALUE_Addr ptr) /\
      handle_gep_addr (DTYPE_Array size t) a [DVALUE_I64 (repr 0); DVALUE_I64 (repr (Z.of_nat i))] = inr ptr.
Proof.
  intros * FITS.
  epose proof @interp_memory_GEP_array_no_read _ (PickE +' UBE +' DebugE +' FailureE) _ _ _ t _ size _ _ FITS as [ptr [INTERP GEP]]. 
  exists ptr.
  split; auto.

  unfold ℑ3.
  go.
  rewrite INTERP.
  go.
  reflexivity.
  auto.
Qed.

Lemma interp_cfg3_GEP_array : forall t a size g l m val i,
    get_array_cell m a i t = inr val ->
    exists ptr,
      ℑ3 (trigger (GEP
                     (DTYPE_Array size t)
                     (DVALUE_Addr a)
                     [DVALUE_I64 (Integers.Int64.repr 0); DVALUE_I64 (Integers.Int64.repr (Z.of_nat i))])) g l m
         ≈ Ret3 g l m (DVALUE_Addr ptr) /\
      read m ptr t = inr val.
Proof.
  intros * GET.
  epose proof @interp_memory_GEP_array _ (PickE +' UBE +' DebugE +' FailureE) _ _ _ t _ size _ _ _ GET as [ptr [INTERP READ]].
  exists ptr.
  split; auto.

  unfold ℑ3.
  go.
  rewrite INTERP.
  go.
  reflexivity.
Qed.

