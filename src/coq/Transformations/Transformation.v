From Vellvm Require Import
     CFG
     LLVMAst
     TopLevel
     TopLevelRefinements
     DynamicTypes.

From ITree Require Import
     ITree.

From Coq Require Export
     Relations.

Import R.
Import TopLevelEnv.

Definition transformation := mcfg dtyp -> mcfg dtyp.

Definition transformation_correct (T: transformation): Prop :=
  forall p, refine_mcfg nil p (T p).


