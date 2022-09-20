From ITree Require Import
     Basics.Basics
     Basics.Monad
     Eq
     ITree.

Require Import Paco.paco.
Require Import Coq.Program.Equality.

Lemma itree_map_ret_inv :
  forall Eff A B (f : A -> B) (t : itree Eff A) b,
    ITree.map f t ≈ ret b ->
    exists a, t ≈ ret a /\ f a = b.
Proof.
  intros * HM.
  punfold HM.
  cbn in *.
  red in HM.
  dependent induction HM.
  - setoid_rewrite (itree_eta t).
    unfold ITree.map,observe in x; cbn in x.
    destruct (observe t) eqn:EQ'; try now inversion x.
    cbn in *; exists r; inversion x; split; reflexivity.
  - unfold ITree.map,observe in x; cbn in x.
    setoid_rewrite (itree_eta t).
    destruct (observe t) eqn:EQ'; try now inversion x.
    cbn in x.
    inversion x.
    subst.
    edestruct IHHM as (? & ? & ?).
    all: try reflexivity.
    exists x0; split; auto.
    rewrite H, tau_eutt; reflexivity.
Qed.
