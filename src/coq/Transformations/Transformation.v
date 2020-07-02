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

Definition transformation := mcfg dtyp -> mcfg dtyp.
About refine_mcfg.
Definition transformation_correct (T: transformation): Prop :=
  forall m, refine_mcfg m (T m).


