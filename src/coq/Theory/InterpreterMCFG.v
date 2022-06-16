(* begin hide *)
From Coq Require Import
     Morphisms ZArith String.

From ITree Require Import
     ITree
     Basics.Monad
     Events.StateFacts
     Eq.Eqit.

From Vellvm Require Import
     Utilities
     Syntax
     Semantics.

Import ITreeNotations.
Import SemNotations.
(* end hide *)

(** * General facts on the MCFG-level interpretation
  A collection of elementary facts about the interpretation when considering mcfgs
*)

(* TO MOVE *)
(* COMMON WITH CFG *)
Arguments Intrinsics.F_trigger/.
Arguments String.append : simpl never.
Arguments allocate : simpl never.
Arguments defs_assoc: simpl never.

Module MCFGTactics.
  (* Note: does not commute triggers for memory since those are more involved, we rely on specific lemmas *)
  Ltac go :=
    repeat match goal with
           | |- context [interp_intrinsics (ITree.bind _ _)] => rewrite interp_intrinsics_bind
           | |- context [interp_global (ITree.bind _ _)] => rewrite interp_global_bind
           | |- context [interp_local_stack (ITree.bind _ _)] => rewrite interp_local_stack_bind
           | |- context [interp_memory (ITree.bind _ _)] => rewrite interp_memory_bind
           | |- context [interp_intrinsics (trigger _)] => rewrite interp_intrinsics_trigger; cbn; rewrite ?subevent_subevent
           | |- context [interp_global (trigger _)] => rewrite interp_global_trigger; cbn; rewrite ?subevent_subevent
           | |- context [interp_local_stack (trigger _)] => rewrite interp_local_stack_trigger; cbn; rewrite ?subevent_subevent
           | |- context [ITree.bind (ITree.bind _ _) _] => rewrite bind_bind
           | |- context [interp_intrinsics (Ret _)] => rewrite interp_intrinsics_ret
           | |- context [interp_global (Ret _)] => rewrite interp_global_ret
           | |- context [interp_local_stack (Ret _)] => rewrite interp_local_stack_ret
           | |- context [interp_memory (Ret _)] => rewrite interp_memory_ret
           | |- context [ITree.bind (Ret _) _] => rewrite bind_ret_l
           end.

End MCFGTactics.

Import MCFGTactics.

Lemma interp1_bind :
  forall {R S} (t: itree L0 R) (k: R -> itree L0 S) g, 
    ℑs1 (t >>= k) g ≈ '(g',x) <- ℑs1 t g ;; ℑs1 (k x) g'.
Proof.
  intros; unfold ℑs1.
  go.
  apply eutt_eq_bind; intros (? & ?); reflexivity.
Qed.

Lemma interp1_ret : forall (R : Type) g (x : R), ℑs1 (Ret x) g ≈ Ret1 g x.
Proof.
  intros; unfold ℑs1.
  go; reflexivity.
Qed.

Lemma interp2_bind :
  forall {R S} (t: itree L0 R) (k: R -> itree L0 S) g l,
    ℑs2 (t >>= k) g l ≈ '(g',(l',x)) <- ℑs2 t g l;; ℑs2 (k x) l' g'.
Proof.
  intros; unfold ℑs2.
  go.
  apply eutt_eq_bind; intros (? & ? & ?); reflexivity.
Qed.

Lemma interp2_ret : forall (R : Type) g l (x : R), ℑs2 (Ret x) g l ≈ Ret2 g l x.
Proof.
  intros; unfold ℑs2.
  go; reflexivity.
Qed.

Lemma interp3_bind :
  forall {R S} (t: itree L0 R) (k: R -> itree L0 S) g l m,
    ℑs3 (t >>= k) g l m ≈ '(m',(l',(g',x))) <- ℑs3 t g l m;; ℑs3 (k x) g' l' m'.
Proof.
  intros.
  unfold ℑs3.
  go.
  apply eutt_eq_bind; intros (? & ? & ? & ?); reflexivity.
Qed.

Lemma interp3_ret : forall (R : Type) g l m (x : R), ℑs3 (Ret x) g l m ≈ Ret3 g l m x.
Proof.
  intros; unfold ℑs3.
  go; reflexivity.
Qed.

#[global] Instance eutt_interp1 {T}:
  Proper (eutt eq ==> eq ==> eutt eq) (@ℑs1 T).
Proof.
  repeat intro.
  unfold ℑs1.
  subst; rewrite H.
  reflexivity.
Qed.

#[global] Instance eutt_interp2 {T}:
  Proper (eutt eq ==> eq ==> eq ==> eutt eq) (@ℑs2 T).
Proof.
  repeat intro.
  unfold ℑs2.
  subst; rewrite H.
  reflexivity.
Qed.

#[global] Instance eutt_interp3 {T}:
  Proper (eutt eq ==> eq ==> eq ==> eq ==> eutt eq) (@ℑs3 T).
Proof.
  repeat intro.
  unfold ℑs3.
  subst; rewrite H.
  reflexivity.
Qed.

Lemma interp3_vis: 
  forall T R (e : L0 T) (k : T -> itree L0 R) g l m,
    ℑs3 (Vis e k) g l m ≈ 
            '(m, (l, (g, x))) <- ℑs3 (trigger e) g l m;; ℑs3 (k x) g l m.
Proof.
  intros.
  unfold ℑs3.
  rewrite interp_intrinsics_vis.
  go.
  apply eutt_eq_bind.
  intros (? & ? & ? & ?).
  go.
  reflexivity.
Qed.

Lemma interp3_bind_trigger :
  forall T R (e : L0 T) (k : T -> itree L0 R) g l m,
    ℑs3 (trigger e >>= k) g l m ≈ 
            '(m, (l, (g, x))) <- ℑs3 (trigger e) g l m;; ℑs3 (k x) g l m.
Proof.
  intros.
  rewrite bind_trigger.
  rewrite interp3_vis at 1.
  reflexivity.
Qed.

Lemma interp3_GW : forall id g l m v,
    ℑs3 (trigger (GlobalWrite id v)) g l m ≈ Ret3 (Maps.add id v g) l m tt.
Proof.
  intros.
  unfold ℑs3.
  go.
  reflexivity.
Qed.

Lemma interp_cfg3_LM : forall t a size offset g l m v bytes concrete_id,
    get_logical_block m a = Some (LBlock size bytes concrete_id) ->
    deserialize_sbytes (lookup_all_index offset (sizeof_dtyp t) bytes SUndef) t = v ->
    ℑs3 (trigger (Load t (DVALUE_Addr (a, offset)))) g l m ≈ Ret3 g l m v.
Proof.
  intros * LUL EQ.
  unfold ℑs3.
  go.
  rewrite interp_memory_load; cycle -1.
  unfold read.
  cbn in *; rewrite LUL; reflexivity.
  go.
  unfold read_in_mem_block; rewrite EQ.
  reflexivity.
Qed.

Lemma interp3_alloca :
  forall (m : memory_stack) (t : dtyp) (g : global_env) l,
    non_void t ->
    exists m' a',
      allocate m t = inr (m', a') /\
      ℑs3 (trigger (Alloca t)) g l m ≈ ret (m', (l, (g, DVALUE_Addr a'))).
Proof.
  intros * NV.
  unfold ℑs3.
  eapply (@interp_memory_alloca_exists _ L3) in NV as [m' [a' [ALLOC INTERP]]].
  exists m', a'.
  split; eauto.
  go.
  rewrite interp_memory_alloca; eauto.
  go; reflexivity.
  Unshelve.
  auto.
Qed.
