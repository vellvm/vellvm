(* begin hide *)
From ITree Require Import
     ITree.

From TwoPhase Require Import
     Utils.PropT
     Semantics.LLVMEvents
     Theory.ContainsUB.

Require Import Morphisms Program.Basics.

Set Implicit Arguments.
Set Contextual Implicit.
(* end hide *)

Section UBPropositional.
  Variable (E F G : Type -> Type).
  #[local] Notation Eff := (E +' F +' UBE +' G).

  Definition model_UB {T} (ts : PropT Eff T) : PropT Eff T:=
    fun t =>
      ts t \/ (exists ub, ts ub /\ contains_UB ub).

  #[global] Instance Proper_model_UB :
    forall T,
      Proper ((eq ==> iff) ==> eq ==> flip impl) (@model_UB T).
  Proof using.
    intros T.
    unfold Proper, respectful, flip, impl.
    intros x y IFF x0 y0 EQ UB.
    unfold model_UB in *.
    destruct UB as [Y | [uby [Y UBY]]].
    - left. eapply IFF; eauto.
    - right.
      exists uby.
      split; eauto.
      eapply IFF; eauto.
  Qed.

End UBPropositional.
