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

(** * Live-equivalence
    Optimizations do not preserve functional equivalence of local environment in general.
 *)

From Coq Require Import ListSet.
Import SetNotations.
Import AlistNotations.

Definition local_agrees (l1 l2 : local_env) (scope : set raw_id) : Prop :=
  forall id, In id scope -> l1 @ id = l2 @ id.

Section Liveness.

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

  (** * Liveness
      Data-flow approach, we compute for each block the [LiveIn] set of live variables when entering the block,
      and [LiveOut] set of live variables when entering a successor of the block.
      These sets can be characterized by the following set of recursive equations:
      LiveIn bk  ≡ defs bk.(blk_phis) +++ upward_exposed bk +++ (LiveOut bk ∖ defs bk)
      LiveOut bk ≡ (set_flat_map (fun bk' => LiveIn bk' ∖ defs bk'.(blk_phis)) (bk_outputs bk)) +++ uses bk.(blk_phis)
      In SSA form, the fixpoint can be directly computed in two passses over the CFG.
   *)



End Liveness.
