(* begin hide *)
Require Import String.

From ITree Require Import
  ITree
  Basics
  Basics.HeterogeneousRelations
  Eq.Eqit.

From Vellvm Require Import
  Utilities
  Utils.VellvmRelations
  Syntax
  Semantics
  Semantics.MemoryAddress
  Semantics.GepM
  Semantics.Memory.Sizeof
  Semantics.Memory.MemBytes
  Semantics.LLVMParams
  Semantics.Lang
  Semantics.StoreId
  Theory.ContainsUB
  Handlers.OOM.

From ExtLib Require Import
  Structures.Monads
  Data.Monads.EitherMonad
  Structures.Functor.

From Coq Require Import Relations RelationClasses.
(* end hide *)

Module Make (LP : LLVMParams) (LLVM : Lang LP).
  Import LP.
  Import LLVM.
  Import LLVM.MEM.
  Import MEM.MEM_MODEL.
  Import MEM.MMEP.MMSP.
  Import MEM.MEM_EXEC_INTERP.
  Import MEM.MEM_SPEC_INTERP.

  Import DV.
  Import LLVM.MEM.CP.CONC.
  Import PROV.

  (* Refinement relation for uvalues *)
  Variant refine_uvalue: uvalue -> uvalue -> Prop :=
    | UndefPoison: forall dt uv uv1, concretize uv1 (DVALUE_Poison dt) -> uvalue_has_dtyp uv dt -> refine_uvalue uv1 uv
    | RefineConcrete: forall uv1 uv2, (forall (dv:dvalue), concretize uv2 dv -> concretize uv1 dv) -> refine_uvalue uv1 uv2
  .
  #[export] Hint Constructors refine_uvalue : core.

  Definition uvalue_eq (uv1 uv2 : uvalue) : Prop
    := refine_uvalue uv1 uv2 /\ refine_uvalue uv2 uv1.

  #[global] Instance refine_uvalue_Reflexive : Reflexive refine_uvalue.
  Proof.
    repeat intro.
    destruct x; (apply RefineConcrete; solve [auto]).
  Qed.

  #[global] Instance uvalue_eq_Reflexive : Reflexive uvalue_eq.
  Proof.
    repeat intro.
    split; reflexivity.
  Qed.

  #[global] Instance uvalue_eq_Symmetric : Symmetric uvalue_eq.
  Proof.
    intros x y [Rxy Ryx].
    split; auto.
  Qed.

  (* TODO: move this? *)
  Ltac red_concretize :=
    unfold concretize, concretize_u; rewrite concretize_uvalueM_equation.
  Ltac red_concretize_in H :=
    unfold concretize, concretize_u in H; rewrite concretize_uvalueM_equation in H.

  Ltac normalize_array_vector_dtyp :=
    match goal with
    | H : _ |- dvalue_has_dtyp _ (DTYPE_Array (BinNat.N.of_nat) _) =>
        idtac
    | H : _ |- dvalue_has_dtyp _ (DTYPE_Array ?sz _) =>
        rewrite <- (Nnat.N2Nat.id sz)
    | H : _ |- dvalue_has_dtyp _ (DTYPE_Vector (BinNat.N.of_nat) _) =>
        idtac
    | H : _ |- dvalue_has_dtyp _ (DTYPE_Vector ?sz _) =>
        rewrite <- (Nnat.N2Nat.id sz)
    end.

  Hint Resolve forall_repeat_true : DVALUE_HAS_DTYP.
  Hint Constructors dvalue_has_dtyp : DVALUE_HAS_DTYP.
  Hint Rewrite Nnat.Nat2N.id : DVALUE_HAS_DTYP.
  Hint Resolve List.repeat_length : DVALUE_HAS_DTYP.

  Ltac solve_dvalue_has_dtyp :=
    try normalize_array_vector_dtyp;
    solve [autorewrite with DVALUE_HAS_DTYP; auto with DVALUE_HAS_DTYP].

  Ltac solve_concretize :=
    red_concretize; cbn; subst; solve_dvalue_has_dtyp.

  Ltac invert_concretize H :=
    red_concretize_in H; cbn in H; subst; inversion H; subst; auto.

  (* Theorem 4.1 - uses this definition of refinement *)
  (* Refinement of uninterpreted mcfg *)
  Definition refine_L0: relation (itree L0 dvalue) := eutt eq.

  (* Refinement of mcfg after globals *)
  Definition refine_res1 : relation (global_env * dvalue)
    := TT × eq.

  Definition refine_L1 : relation (itree L1 (global_env * dvalue))
    := eutt refine_res1.

  (* Refinement of mcfg after locals *)
  Definition refine_res2 : relation (local_env * lstack * (global_env * dvalue))
    := TT × refine_res1.

  Definition refine_L2 : relation (itree L2 (local_env * stack * (global_env * dvalue)))
    := eutt refine_res2.

  (* For multiple CFG, after interpreting [LocalE] and [MemoryE] and [IntrinsicE] that are memory intrinsics *)
  Definition refine_res3 : relation (MemState * (store_id * (local_env * stack * (global_env * dvalue))))
    := TT × (TT × refine_res2).

  Definition refine_L3 : relation (itree L3 (MemState * (store_id * (local_env * stack * (global_env * dvalue)))) -> Prop)
    := fun ts ts' => forall t', ts' t' -> exists t, ts t /\ eutt refine_res3 t t'.

  (* Refinement for after interpreting pick. *)
  Definition refine_L4 : relation ((itree L4 (MemState * (store_id * (local_env * stack * (global_env * dvalue))))) -> Prop)
    := fun ts ts' => forall t', ts' t' -> exists t, ts t /\ eutt refine_res3 t t'.

  Definition refine_L5 : relation ((itree L4 (MemState * (store_id * (local_env * stack * (global_env * dvalue))))) -> Prop)
    := fun ts ts' =>
         (* For any tree in the target set *)
         forall t', ts' t' ->
               (* There is a tree in the source set that is eutt our target tree *)
               exists t, ts t /\ eutt refine_res3 t t'.

  Definition refine_L6 : relation ((itree L4 (MemState * (store_id * (local_env * stack * (global_env * dvalue))))) -> Prop)
    := fun ts ts' =>
         forall t', ts' t' ->
               exists t, ts t /\ refine_OOM_h refine_res3 t t'.

  Instance Transitive_refine_L5 : Transitive refine_L5.
  Proof.
    unfold Transitive.
    intros tx ty tz XY YZ.

    intros rz TZ.
    specialize (YZ rz TZ).
    destruct YZ as (ry & TY & YZ).
    specialize (XY ry TY).
    destruct XY as (rx & TX & XY).

    exists rx; split; auto.
    rewrite XY. eauto.
  Qed.

  (* Theorem 4.2 *)
  Instance Transitive_refine_L6 : Transitive refine_L6.
  Proof.
    unfold Transitive.
    intros tx ty tz XY YZ.

    intros rz TZ.
    specialize (YZ rz TZ).
    destruct YZ as (ry & TY & YZ).
    specialize (XY ry TY).
    destruct XY as (rx & TX & XY).

    exists rx; split; auto.
    rewrite XY. eauto.
  Qed.

End Make.
