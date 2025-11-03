Unset Universe Checking.

From CTree Require Import
  CTree CTreeDefinitions Eq Fold FoldStateT.

From ExtLib Require Import
  Structures.Functor
  Structures.Monads.

From Vellvm.Utils Require Import
  MonadEq1Laws.

Import Monad.

#[global] Instance ctree_monad {E B} : Monad (ctree E B).
split.
- intros.
  apply ret; apply X.
- intros t u X X0.
  eapply bind.
  apply X.
  apply X0.
Defined.

#[global] Instance ctree_eq1 {Eff B} : Monad.Eq1 (ctree Eff B).
intros A.
apply sbisim.
apply eq.
Defined.

#[global] Instance ctree_Eq1_ret_inv {Eff B} : Eq1_ret_inv (ctree Eff B).
split.
intros A x y H.
eapply sbisim_ret_inv; eauto.
apply H.
Defined.

#[global] Instance ctree_monad_eq1_equiv {Eff B} : Monad.Eq1Equivalence (ctree Eff B).
red.
typeclasses eauto.
Defined.

#[global] Instance ctree_monad_laws {E B} : MonadLawsE (ctree E B).
split.
- (* bind_ret_l *)
  intros A B0 f x.
  setoid_rewrite Equ.bind_ret_l.
  reflexivity.
- (* bind_ret_r *)
  intros A x.
  setoid_rewrite Equ.bind_ret_r.
  reflexivity.
- (* bind_bind *)
  intros A B0 C x f g.
  setoid_rewrite Equ.bind_bind.
  reflexivity.  
- typeclasses eauto.
Defined.

#[global] Instance MonadStepState {S M} `{HM : Monad M} `{MS : MonadStep M} : MonadStep (Monads.stateT S M).
red.
intros s.
eapply bind.
apply mstep.
intros _.
apply (ret (s, tt)).
Defined.

#[global] Instance MonadStuckState {S M} `{HM : Monad M} `{MS : MonadStuck M} : MonadStuck (Monads.stateT S M).
red.
intros X.
red.
intros s.
apply mstuck.
Defined.

#[global] Instance MonadBrState {B S M} `{HM : Monad M} `{MB : MonadBr B M} : MonadBr B (Monads.stateT S M).
red.
intros X b s.
apply mbr in b.
eapply fmap; cycle 1; eauto.
Defined.
