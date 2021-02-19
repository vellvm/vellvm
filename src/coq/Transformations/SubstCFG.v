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
     DynamicTypes
     DynamicValues
     Denotation
     Handlers.Handlers
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

Definition transformation_correct (T: endo (mcfg dtyp)) p: Prop :=
  refine_mcfg [] p (T p).

Lemma interp3_bind:
  forall ui {R S} (t: itree IO.L0 R) (k: R -> itree IO.L0 S) s1 s2 m,
    interp3 ui (ITree.bind t k) s1 s2 m ≈
                 (ITree.bind (interp3 ui t s1 s2 m) (fun '(m',(s2',(s1',x))) => interp3 ui (k x) s1' s2' m')).
Proof.
  intros.
  unfold interp3.
  fold_L2; rewrite interp2_bind, M.interp_memory_bind.
  apply eutt_clo_bind with (UU := Logic.eq); [reflexivity | intros ? (? & ? & ? & ?) ->; reflexivity].
Qed.

Lemma interp3_ret: forall ui (R : Type) s1 s2 m (x : R), interp3 ui (Ret x) s1 s2 m ≈ Ret (m, (s2, (s1, x))).
Proof.
  intros; unfold interp3; fold_L2.
  rewrite interp2_ret, M.interp_memory_ret; reflexivity.
Qed.

Lemma interp4_bind: forall {R S} g l m (t: itree _ R) (k: R -> itree _ S) t',
    interp4 [] (bind t k) g l m t' ->
    bind (interp4 [] t g l m) (fun '(m,(l,(g,x))) => interp4 [] (k x) g l m) t'.
Proof.
  intros.
  cbn in *.
  unfold interp4 in H.
    match type of H with
       context[
            runState (M.interp_memory
            (runState
              (interp_local_stack ?h
                (runState (interp_global (INT.interpret_intrinsics ?ui ?p)) ?g)) ?l)) ?m] =>
      replace (runState (M.interp_memory (runState (interp_local_stack h (runState (interp_global (INT.interpret_intrinsics ui p)) g)) l)) m) with
        (interp3 ui p g l m) in H by reflexivity
    end.
    destruct H as [t1 [H1 H2]].
    rewrite interp3_bind in H2.

Lemma interp_vellvm_model_user_bind: forall {R S} g l m (t: itree _ R) (k: R -> itree _ S) t',
    interp_vellvm_model_user [] (bind t k) g l m t' ->
    bind (interp_vellvm_model_user [] t g l m) (fun '(m,(l,(g,x))) => interp_vellvm_model_user [] (k x) g l m) t'.
Proof.
  intros.
  cbn in *.
  destruct H as [t1 [MODEL1 H]].

    match type of MODEL1 with
      context[
            P.model_undef (runState (M.interp_memory
            (runState
              (interp_local_stack ?h
                (runState (interp_global (INT.interpret_intrinsics ?ui ?p)) ?g)) ?l)) ?m)] =>
      replace (P.model_undef (runState (M.interp_memory (runState (interp_local_stack h (runState (interp_global (INT.interpret_intrinsics ui p)) g)) l)) m)) with
        (interp4 ui p g l m) in MODEL1 by reflexivity
    end.


    match type of MODEL1 with
      context[
            P.model_undef (runState (M.interp_memory
            (runState
              (interp_local_stack ?h
                (runState (interp_global (INT.interpret_intrinsics ?ui ?p)) ?g)) ?l)) ?m)] =>
      replace (P.model_undef (runState (M.interp_memory (runState (interp_local_stack h (runState (interp_global (INT.interpret_intrinsics ui p)) g)) l)) m)) with
        (interp4 ui p g l m) in MODEL1 by reflexivity
    end.


  fold_L4.
  Global Instance Monad_Prop {M} {MM : Monad M}
    : Monad (PropT M).
  split.
  2:{
    intros A B PA KAB b.
    refine (exists (a: M A), PA a /\ KAB _ b).
    {|
      ret := fun _ x y =>  y = ret x
      ; bind := fun A B PA K b => exists (a: A), PA (ret a) /\ K a b
    |}.



Section Substitute_cfg_correct.

  Lemma subst_cfg_correct:
    forall (p: mcfg dtyp) id f d,
      In d (m_definitions p) ->
      dc_name (df_prototype d) = id ->
      refine_cfg (df_instrs d) f ->
      transformation_correct (subst_cfg id f) p.
  Proof.
    intros p id f d IN LU REFINE t tIN.
    unfold model_to_L5 in tIN.
    unfold denote_vellvm in tIN.
    simpl in tIN.

    destruct tIN as (t' & (t'' & t''IN & HUndef) & HUB).
    simpl in *.

    repeat red in REFINE.

    repeat red in INMODEL.

    intros p.
    unfold refine_mcfg_L2.
    unfold build_to_L2.

    (* Proof obligation number 1: commutation with normalize_types. *)
    rewrite normalize_types_swap.
    pattern (normalize_types p); generalize (normalize_types p); clear p; intros p.

    unfold denote_vellvm.
    simpl; rewrite 2 interp2_bind.
    split_bind.

    {
      (* Reasoning about initialization *)
      admit.
    }

    rewrite 2 interp2_bind.
    apply eutt_clo_bind with foo_rel.

    {
      (* Denotation of each cfg *)
      apply interp2_map_monad.
      admit.
    }

    intros (? & ? & ?) (? & ? & ?) EQ.
    inv EQ; repeat match goal with | h: prod_rel _ _ _ _ |- _ => inv h end.
    rewrite 2 interp2_bind.
    split_bind.

    { (* Getting the address of "main" *)
      admit.
    }

    (* Tying the recursive knot *)

    admit.
  (*   rewrite 2 interp2_bind. *)




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
