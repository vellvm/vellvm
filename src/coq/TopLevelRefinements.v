From ITree Require Import
     ITree
     ITreeFacts
     Events.StateFacts
     Eq.Eq.

From Vellvm Require Import
     Memory
     Refinement
     Environment
     TopLevel
     LLVMAst
     Handlers.Stack.

Module R := Refinement.Make(Memory.A)(IO)(TopLevelEnv).
Import R.
Import TopLevelEnv.

(* Do I want to restrict this? *)
Lemma refine_01: forall t1 t2,
    refine_L0 t1 t2 -> refine_L1 (build_L1 t1) (build_L1 t2).
Abort.
