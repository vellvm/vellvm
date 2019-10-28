From Coq Require Import List String Ascii ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

From Vellvm Require Import
     LLVMAst
     LLVMEvents
     UndefTests
     TopLevel
     Refinement
     TopLevelRefinements
     CFG
     DynamicTypes
     PropT.

From Vellvm.Handlers Require Import
     Stack
     Local
     Global.

From ITree Require Import
     ITree
     Basics
     Eq.Eq
     Events.State.

From ExtLib Require Import
     Structures.Monads
     Structures.Maps.

Import ITree.Basics.Basics.Monads.

Import MonadNotation.
Import ListNotations.
Import Monads.

Require Import Morphisms.
Require Import Relations.

Import R.
Import TopLevelEnv.
Import IO.
Import D.

(* -------------------------------------------------- *)
(* Interpretation / refinement of blocks.             *)
(* -------------------------------------------------- *)
Definition block_interp_L0 (b: block dtyp) := denote_block b.
Definition block_interp_L1 (b : block dtyp) := interp_global (block_interp_L0 b) [].
Definition block_interp_L2 (b : block dtyp) := interp_local (block_interp_L1 b) [].
Definition block_interp_L3 (b : block dtyp) := M.interp_memory (block_interp_L2 b) (M.empty, [[]]).

Definition _failure_UB_to_block_L4 : (FailureE +' UBE) ~> (CallE +' UBE +' FailureE) :=
  fun T e =>
    match e with
    | inl1 x => inr1 (inr1 x)
    | inr1 x => inr1 (inl1 x)
    end.

Definition concretize_block_uv (res : (block_id + res_L0)) : itree (FailureE +' UBE) (block_id + dvalue)
  := match res with
     | inl bid => ret (inl bid)
     | inr uv => ITree.map inr (P.concretize_uvalue uv)
     end.

Definition block_interp_L4 (b : block dtyp) : itree (CallE +' UBE +' DebugE +' FailureE) (M.memory_stack * (list (raw_id * res_L0) * (list (raw_id * dvalue) * (block_id + dvalue)))) :=
  '(m, (env, (genv, buv))) <- P.interp_undef (block_interp_L3 b);;
   bdv <- translate _failure_UB_to_L4 (concretize_block_uv buv);;
   ret (m, (env, (genv, bdv))).


Definition refine_block_L2 b1 b2 := eutt (TT × (TT × (sum_rel Logic.eq refine_uvalue))) (block_interp_L2 b1) (block_interp_L2 b2).

(* -------------------------------------------------------- *)
(* Refinement of undef * undef to undef in uvalues / blocks *)
(* -------------------------------------------------------- *)
Theorem undef_refines_mul_undef_undef:
  refine_uvalue (UVALUE_Undef (DTYPE_I 64)) (UVALUE_IBinop (Mul false false) (UVALUE_Undef (DTYPE_I 64)) (UVALUE_Undef (DTYPE_I 64))).
Proof.
  constructor.
  intros dv H.
  Print dvalue.
  apply Concretize_IBinop with (dv1:=DVALUE_I64 one) (dv2:=dv).
  - apply Concretize_Undef. constructor.
  - auto.
  - simpl. inversion H; subst.
    + inversion H0.
    + inversion H1; subst; auto.
      unfold DynamicValues.Int64.mul. unfold DynamicValues.Int64.one.
      replace (DynamicValues.Int64.unsigned (DynamicValues.Int64.repr 1) *
               DynamicValues.Int64.unsigned x) with (DynamicValues.Int64.unsigned x).
      * destruct (Eqv.eqv_dec_p 64%nat 1%nat); rewrite DynamicValues.Int64.repr_unsigned; reflexivity.
      * rewrite Integers.Int64.unsigned_repr; try omega; cbn; try omega.
Qed.

Theorem undef_test0 :
 refine_block_L2 undef_test0_block_refine undef_test0_block.
Proof.
  unfold refine_block_L2.
  unfold block_interp_L2. unfold block_interp_L1.
  tau_steps.

  apply eqit_Ret.

  repeat (apply prod_morphism; firstorder).
  apply inr_morphism; apply undef_refines_mul_undef_undef.
Qed.

(* -------------------------------------------------- *)
(* CFG interpretation / refinement                    *)
(* -------------------------------------------------- *)
Definition cfg_interp_L0 (c : cfg dtyp) := denote_cfg c.
Definition cfg_interp_L1 (c : cfg dtyp) := interp_global (cfg_interp_L0 c) [].
Definition cfg_interp_L2 (c : cfg dtyp) := interp_local (cfg_interp_L1 c) [].
Definition cfg_interp_L3 (c : cfg dtyp) := M.interp_memory (cfg_interp_L2 c) (M.empty, [[]]).

Definition refine_cfg_L2 c1 c2 := eutt (TT × (TT × refine_uvalue)) (cfg_interp_L2 c1) (cfg_interp_L2 c2).


(* -------------------------------------------------- *)
(* Block substitution into CFG.                       *)
(* -------------------------------------------------- *)
Theorem bl2_subst_cfgl2 :
  forall (b1 b2 : block dtyp) (bls brs : list (block dtyp)) (bid : block_id) args,
    refine_block_L2 b1 b2 ->
    refine_cfg_L2 (mkCFG dtyp bid (bls ++ [b1] ++ brs) args)
                  (mkCFG dtyp bid (bls ++ [b2] ++ brs) args).
Proof.
  intros b1 b2 bls brs bid args H.
  unfold refine_cfg_L2, refine_block_L2 in *.
  unfold cfg_interp_L2, cfg_interp_L1, block_interp_L2, block_interp_L1 in *.
  tau_steps.
Qed.


(* SCRAPYARD. Will probably need some of these things, but not sure about all of them. *)

(*
Instance interp_local_Proper
         {E F G : Type -> Type} `{FailureE -< E +' F +' G}
         k v map `{Map k v map} `{Serialize.Serialize k} (st : map)
         R (RR : relation R)
         (f : itree (E +' F +' LocalE k v +' G) R -> itree (E +' F +' LocalE k v +' G) R) :
  Proper ((fun t1 t2 => @eutt (E +' F +' G) _ _ (TT × RR) (interp_local t1 st) (interp_local t2 st)) ==> (fun t1 t2 => @eutt (E +' F +' G) _ _ (TT × RR) (interp_local t1 st) (interp_local t2 st))) f.
intros t1 t2 ?.
Admitted.
*)

(*
Instance interp_global_Proper
         {E F G : Type -> Type} `{FailureE -< E +' F +' G}
         k v map `{Map k v map} `{Serialize.Serialize k} (st : map)
         R (RR : relation R)
         (f : itree (E +' F +' GlobalE k v +' G) R -> itree (E +' F +' GlobalE k v +' G) R) :
  Proper ((fun t1 t2 => @eutt (E +' F +' G) _ _ (TT × RR) (interp_global t1 st) (interp_global t2 st)) ==> (fun t1 t2 => @eutt (E +' F +' G) _ _ (TT × RR) (interp_global t1 st) (interp_global t2 st))) f.
intros t1 t2 ?.
Admitted.
*)

(*
Theorem interp_bind_st
  : forall (E F : Type -> Type) (R S : Type) (ST : Type) (st : ST)
      (f : forall T : Type, E T -> stateT ST (itree F) T) (t : itree E R) (k : R -> itree E S),
    interp f (ITree.bind t k) st ≅ ITree.bind (interp f t st) (fun '(s, r) => interp f (k r) s).
Proof.
Admitted.

Theorem interp_translate_st
     : forall (E F G : Type -> Type) (ST : Type) (st : ST) (f : forall T : Type, E T -> F T)
         (h : forall T : Type, F T -> stateT ST (itree G) T) (R : Type) 
         (t : itree E R),
       interp h (translate f t) st
       ≅ interp (fun (T : Type) (e : E T) => h T (f T e)) t st.
Proof.
Admitted.

Theorem interp_ret_st :
  forall (E F : Type -> Type) (R : Type) (ST : Type) (st : ST) (f : forall T : Type, E T -> stateT ST (itree F) T) (x : R),
    interp f (Ret x) st ≅ ITree.map (fun x => (st, x)) (Ret x).
Proof.
Admitted.

Theorem interp_trigger_st :
  forall (E F : Type -> Type) (R : Type) (ST : Type) (st : ST) (f : forall T : Type, E T -> stateT ST (itree F) T)
    (e : E R), interp f (ITree.trigger e) st ≳ f R e st.
Proof.
Admitted.
 *)
