From Vellvm Require Import
     CFG
     LLVMAst
     TopLevel
     TopLevelRefinements.

From ITree Require Import
     ITree.

From Coq Require Export
     Relations.

Import R.
Import TopLevelEnv.

Definition transformation := mcfg typ -> mcfg typ.

Definition transformation_correct (T: transformation): Prop :=
  forall p, refine_L5 (model_mcfg p) (model_mcfg (T p)).

