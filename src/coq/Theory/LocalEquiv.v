(* begin hide *)
From Coq Require Import
     String Morphisms List.

From ITree Require Import
     ITree
     Basics.Monad
     Eq.Eq
     TranslateFacts
     Events.State.

From Vellvm Require Import
     Utilities
     Syntax
     Semantics
     Utils.NoFailure
     Utils.PostConditions
     Theory.InterpreterCFG
     Theory.ExpLemmas
     Theory.InstrLemmas
     Theory.InterpreterCFG
     Theory.SymbolicInterpreter.

From ExtLib Require Import
     Core.RelDec
     Data.Map.FMapAList
     Structures.Maps.

Import ListNotations.
Import AlistNotations.
Import ITreeNotations.
Import SemNotations.
(* end hide *)

(** * Live-equivalence
    Optimizations do not preserve functional equivalence of local environment in general.
 *)

From Coq Require Import ListSet.
Import SetNotations.
Import AlistNotations.

Definition local_agrees (l1 l2 : local_env) (scope : set raw_id) : Prop :=
  forall id, In id scope -> l1 @ id = l2 @ id.

Section UpwardExposed.

  (** * Upward exposed
        A use site is said to be upward exposed if its def site is not in the
        same block, i.e. if the live range of the used variable escapes the block
        of the use site.
   *)
  (* Note: this definition is quite naive, it doesn't consider the relative position
       within the block of the def and use sites considered.
       I believe that it's correct in SSA form, but should be triple checked.
   *)

  Definition upward_exposed {T} (bk : block T) : set raw_id :=
    use_sites bk ∖ def_sites bk.

End UpwardExposed.

Section Block_Substitution.

  (* This definition expresses the local proof obligation
     required to justify the substitution of a block [b1]
     by another block [b2] in a context.
     Contrary to the case of equivalent expressions, the
     context will be constrained as well.
     We state that if:
     - the upward exposed local variables are the same set
     [scope] in both blocks.
     - the initial local states extensionally agree on [scope]
     then:
     - the blocks are bisimilar
     - they return local states that extensionally agree on
   *)

  Definition local_post : 

  Definition block_equivalence :
    forall (b1 b2 : block dtyp) scope_in scope_out,
      upward_exposed b1 = scope_in -> (* To replace with bijection *)
      upward_exposed b2 = scope_out -> (* To replace with bijection *)
      forall g l1 l2 m bin,
        local_agrees l1 l2 scope_in ->
        eutt (fun '(m1,(l,(g,v)))
             (⟦ b1 ⟧b3 bin g l1 m)
             (⟦ b2 ⟧b3 bin g l2 m).




(* Definition lift_localR (R : local_env -> local_env -> Prop) : *)

End Block_Substitution.


(*
If pre = post = RS

relS := S -> S -> Prop

Any monad that is worth its name should come with an instance of eqmR.
S -> M (S * _)
EQMRBUILDER : relS -> relS -> eqmR_sig

Definition equiv (X Y S : Type) (pre post : S -> S -> Prop) (R : X -> Y -> Prop)
  : StateT S (itree E) X -> StateT S (itree E) Y -> Prop :=
  fun c1 c2 =>
    forall s1 s2,
      pre s1 s2 -> eutt (post * R) (c1 s1) (c2 s2).


(* forall R' *)
eqmr R' c1 c2
forall v1 v2, R' v v' -> eqmr R (k1 v1) (k2 v2)
==============================
eqmr R (bind c1 k1) (bind c2 k2)

hoaremR ~> (S -> S -> Prop) -> (S -> S -> Prop) -> eqmR_sig



(* forall R' (inter : S -> S -> Prop) *)
equiv pre inter R' c1 c2
forall v1 v2, R' v1 v2 -> equiv inter post R (k1 v1) (k2 v2)
==============================
equiv pre post R (bind c1 k1) (bind c2 k2)

 *)





Section Liveness.

  (** * Liveness
      Data-flow approach, we compute for each block the [LiveIn] set of live variables when entering the block,
      and [LiveOut] set of live variables when entering a successor of the block.
      These sets can be characterized by the following set of recursive equations:
      LiveIn bk  ≡ defs bk.(blk_phis) +++ upward_exposed bk +++ (LiveOut bk ∖ defs bk)
      LiveOut bk ≡ (set_flat_map (fun bk' => LiveIn bk' ∖ defs bk'.(blk_phis)) (bk_outputs bk)) +++ uses bk.(blk_phis)
      In SSA form, the fixpoint can be directly computed in two passses over the CFG.
   *)



End Liveness.
