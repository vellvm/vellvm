From Coq Require Import
     ZArith Ascii Strings.String Setoid Morphisms List.

From ExtLib Require Import
     Programming.Eqv
     Structures.Monads.

From ITree Require Import
     ITree
     Eq.Eq
     Interp.Interp
     Interp.InterpFacts
     Interp.TranslateFacts
     Events.StateKleisli
     Events.StateFacts.

From Vellvm Require Import
     PropT
     Error
     Util
     LLVMAst
     AstLib
     CFG
     TransformTypes
     DynamicTypes
     DynamicValues
     Denotation
     Handlers.Global
     Handlers.Local
     Handlers.Stack
     Handlers.Memory
     Handlers.UndefinedBehaviour
     LLVMEvents
     Transformations.Transformation
     Traversal
     TopLevelRefinements.

Import ListNotations.
Import TopLevel.
Import TopLevelEnv.
Import R.
Import EqvNotation.

(* WIP, broken, not compiled by the makefile **)

(* -------------------------------------------------- *)
(* CFG substitution into MCFG.                       *)
(* -------------------------------------------------- *)

Section Substitute_cfg.

  Context {T : Set}.
  Variable fid: function_id.
  Variable new_f : cfg T.

  (* This assumes the new function shares the exact same prototype. *)
  Instance subst_cfg_endo_cfg: endo (definition T (cfg T)) :=
    fun f => if (dc_name (df_prototype f)) ~=? fid
          then {| df_prototype := df_prototype f; df_args := df_args f ; df_instrs := new_f |}
          else f.

  Definition subst_cfg: endo (mcfg T) := f_endo.

End Substitute_cfg.

Definition interpret_model (t: itree IO.L0 res_L0): PropT (itree IO.L5) res_L3 :=
  let L0_trace        := INT.interpret_intrinsics [] t in
  let L1_trace        := run_state (interp_global L0_trace) [] in
  let L2_trace        := run_state (interp_local_stack (@handle_local _ _ _ _ _ _ _) L1_trace) ([],[]) in
  let L3_trace        := run_state (M.interp_memory L2_trace) (M.empty, [[]]) in
  let L4_trace        := model_L4 L3_trace in
  let L5_trace        := model_L5 L4_trace in
  L5_trace.


Definition model_mcfg_user' (user_intrinsics: IS.intrinsic_definitions) (prog: CFG.mcfg dtyp) : PropT (itree IO.L5) res_L3 :=
  let L0_trace        := denote_vellvm prog in
  let L0_trace'       := INT.interpret_intrinsics user_intrinsics L0_trace in
  let L1_trace        := run_state (interp_global L0_trace') [] in
  let L2_trace        := run_state (interp_local_stack (@handle_local _ _ _ _ _ _ _) L1_trace) ([],[]) in
  let L3_trace        := run_state (M.interp_memory L2_trace) (M.empty, [[]]) in
  let L4_trace        := model_L4 L3_trace in
  let L5_trace        := model_L5 L4_trace in
  L5_trace.

Definition transformation_correct (T: endo (mcfg dtyp)) p: Prop :=
  refine_L5 (model_mcfg_user' [] p) (model_mcfg_user' [] (T p)).

(* Definition model_to_L5 {R E} (t: itree IO.L0 R) g l m := *)
(*   let L0_trace       := INT.interpret_intrinsics [] t in *)
(*   let L1_trace       := run_state (interp_global L0_trace) g in *)
(*   let L2_trace       := run_state (interp_local_stack (handle_local (v:=res_L0)) L1_trace) l in *)
(*   let L3_trace       := run_state (M.interp_memory L2_trace) m in *)
(*   let L4_trace       := P.model_undef L3_trace in *)
(*   let L5_trace       := model_UB L4_trace *)
(*   in L5_trace. *)


Section Substitute_cfg_correct.

  Lemma subst_cfg_correct:
    forall (p: mcfg dtyp) id f d,
      In d (m_definitions p) ->
      dc_name (df_prototype d) = id ->
      model_cfg (D.denote_cfg (df_instrs d)) (D.denote_cfg f) ->
      transformation_correct (subst_cfg id f) p.
  Proof.
    intros.
    remember (D.denote_cfg f).

    intros p.
    unfold refine_mcfg_L2.
    unfold build_to_L2.

    (* Proof obligation number 1: commutation with normalize_types. *)
    rewrite normalize_types_swap.
    pattern (normalize_types p); generalize (normalize_types p); clear p; intros p.

    unfold denote_vellvm.
    simpl; rewrite 2 interp_to_L2_bind.
    split_bind.

    {
      (* Reasoning about initialization *)
      admit.
    }

    rewrite 2 interp_to_L2_bind.
    apply eutt_clo_bind with foo_rel.

    {
      (* Denotation of each cfg *)
      apply interp_to_L2_map_monad.
      admit.
    }

    intros (? & ? & ?) (? & ? & ?) EQ.
    inv EQ; repeat match goal with | h: prod_rel _ _ _ _ |- _ => inv h end.
    rewrite 2 interp_to_L2_bind.
    split_bind.

    { (* Getting the address of "main" *)
      admit.
    }

    (* Tying the recursive knot *)

    admit.
  (*   rewrite 2 interp_to_L2_bind. *)




(* -------------------------------------------------- *)
(* Block substitution into CFG.                       *)
(* -------------------------------------------------- *)

Section Substitute_block.

  Variable T : Set.
  Variable b : block T.



Fixpoint replace_pred {A} (p : A -> bool) (a : A) (xs : list A) : list A :=
  match xs with
  | nil => nil
  | (x::xs') =>
    if p x
    then a :: xs'
    else x :: replace_pred p a xs'
  end.

From ExtLib Require Import
     Core.RelDec
     Programming.Eqv.


(* Replace a block with a given block r if the ids match *)
Definition replace_block {T} (r : block T) (b : block T) : block T :=
  if blk_id b ~=? blk_id r then r else b.

Section block_replace.
  Variable T : Set.
  Variable b : block T.

  Definition blah := b.

  Instance block_replace_endo : endo (block T)
    := replace_block b.

  Definition cfg_replace_block : endo (cfg T)
    := f_endo.
End block_replace.


