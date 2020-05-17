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

Definition transformation_correct (T: transformation): Prop :=
  forall ret_typ entry args p, refine_mcfg ret_typ entry args nil p (T p).


