From Stdlib Require Import
     Program
     Setoid
     Morphisms
     Relations.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.Utils
     Basics.HeterogeneousRelations
     Basics.Monad
     Basics.HeterogeneousRelations
     Core.ITreeDefinition
     Eq.Eqit
     Eq.Paco2.

From ITreeSpec Require Import
     ITreeSpecDefinition
     ITreeSpecFacts.

Local Open Scope itree_scope.



Inductive isConcreteF {E R} (F : itree_spec E R -> Prop) :
  itree_spec' E R -> Prop :=
  | isConcrete_Ret (r : R) : isConcreteF F (RetF r)
  | isConcrete_Tau (phi : itree_spec E R) :
      F phi -> isConcreteF F (TauF phi)
  | isConcrete_Vis {X} (e : E X) kphi :
      (forall a, F (kphi a)) -> isConcreteF F (VisF (Spec_vis e) kphi).

Hint Constructors isConcreteF.
Definition isConcrete_ {E R} F (t: itree_spec E R) : Prop :=
  isConcreteF F (observe t).

Lemma monotone_isConcreteF {E R} (ot : itree_spec' E R) sim sim'
  (LE : sim <1= sim')
  (IN : isConcreteF sim ot) :
  isConcreteF sim' ot.
Proof.
  induction IN; eauto.
Qed.

Lemma monotone_isConcrete_ {E R} : monotone1 (@isConcrete_ E R).
Proof. red. intros. eapply monotone_isConcreteF; eauto. Qed.

Hint Resolve monotone_isConcrete_ : paco.

Definition isConcrete {E R} : itree_spec E R -> Prop := paco1 isConcrete_ bot1.

Lemma isConcreteVisInv {E R X} (e : E X) (k : _ -> itree_spec E R) a :
  isConcrete (Vis (Spec_vis e) k) -> isConcrete (k a).
Proof.
  intro isc; punfold isc. inversion isc.
  assert (kphi0 = k); [ inj_existT; assumption | ].
  subst. pclearbot.
  apply H0.
Qed.


Variant voidE : Type -> Type := .

Section non_padded_completeness_counter.
  Definition top1 : itree_spec voidE unit :=
    ITree.bind (assume_spec False) (fun _ => Ret tt).

  Lemma top1_top : forall (t : itree_spec voidE unit) RPre RPost RR,
      refines RPre RPost RR t top1.
  Proof.
    intros. pstep. red. cbn. constructor. cbn. intros [].
  Qed.


  Definition top2 : itree_spec voidE unit :=
    ITree.bind (exists_spec bool) (fun b => if b then Ret tt else ITree.spin).
  Context (Hdec : forall (t : itree_spec voidE unit), isConcrete t -> eutt eq t (Ret tt) \/ eutt eq t ITree.spin).


  Lemma top2_top : forall (t : itree_spec voidE unit) RPre RPost,
      isConcrete t ->
      refines RPre RPost eq t top2.
  Proof.
    intros. specialize (Hdec t H). destruct Hdec; clear H Hdec; rename H0 into Ht.
    - punfold Ht. red in Ht. cbn in Ht. pstep. red.
      remember (RetF tt) as x.
      hinduction Ht before t; intros; inv Heqx; eauto.
      + unfold top2.
        cbn.
        apply refinesF_existsR with (a:=true).
        cbn.
        constructor; auto.
      + constructor. auto.
    - pstep. red. cbn.
      apply refinesF_existsR with (a:=false).
      cbn.
      constructor. pstep_reverse.
      generalize dependent t. pcofix CIH. intros t Ht.
      pstep. red. punfold Ht. red in Ht. remember (observe ITree.spin) as x.
      hinduction Ht before r; intros; inv Heqx; pclearbot; eauto.
      + constructor. eauto.
      + cbn. constructor. left. pstep. red. eapply IHHt; eauto.
  Qed.


  Lemma not_refines_top1_top2 RPre RPost RR : ~ refines RPre RPost RR top1 top2.
    Proof.
      intro Hcontra. punfold Hcontra. red in Hcontra.
      inversion Hcontra.
      - cbn in *. destruct a; cbn in *.
        + inj_existT. subst.
          cbn in *.
          inv H1.
          contradiction.
        + inj_existT. subst. cbn in *. clear Hcontra.
          remember (TauF ITree.spin) as y.
          remember (VisF (Spec_forall False)
                      (fun x : False =>
                         ITree.subst (fun _ : () => Ret ()) (ITree.subst (fun _ : False => Ret ()) (Ret x)))) as x.
          hinduction H1 before RR; intros; inv Heqx; try inv Heqy; eauto.
      - destruct a.
    Qed.
End non_padded_completeness_counter.
