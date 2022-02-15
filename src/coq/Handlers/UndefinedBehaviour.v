(* begin hide *)
From ITree Require Import
     ITree.

From Vellvm Require Import
     Utils.PropT
     Semantics.LLVMEvents
     Theory.ContainsUB.

Set Implicit Arguments.
Set Contextual Implicit.
(* end hide *)

Section UBPropositional.
  Variable (E F G : Type -> Type).
  #[local] Notation Eff := (E +' F +' UBE +' G).


  Definition model_UB {T} (ts : PropT Eff T) : PropT Eff T:=
    fun t =>
      ts t \/ (exists ub, ts ub /\ contains_UB ub).
End UBPropositional.
