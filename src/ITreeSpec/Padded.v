From Stdlib Require Import
  Program
  Setoid
  Morphisms
  Relations.

From ITree Require Import
  Basics.Basics
  Basics.Utils
  Basics.HeterogeneousRelations.

From ITree Require Import
  Basics.HeterogeneousRelations
  Core.ITreeDefinition
  Eq.Eqit
  Eq.EqAxiom.

From Paco Require Import paco.

Local Open Scope itree_scope.

Section padded.
Context {E : Type -> Type} {R : Type}.

Variant paddedF (F : itree E R -> Prop) : itree' E R -> Prop :=
  | paddedF_Ret r : paddedF F (RetF r)
  | paddedF_Tau t : F t -> paddedF F (TauF t)
  | paddedF_Vis {X} e (k : X -> itree E R) :
    (forall a, F (k a)) -> paddedF F (VisF e (fun a => (Tau (k a))))
.
Hint Constructors paddedF : itree_spec.

Definition padded_ sim := fun t => paddedF sim (observe t).

Lemma padded_monotone_ : monotone1 padded_.
Proof with eauto with itree_spec. 
  red. unfold padded_. intros. 
  induction IN...
Qed.

Hint Resolve padded_monotone_ : itree_spec.

Definition padded := paco1 padded_ bot1.

Lemma padded_VisF_inv {X} (e : E X) k F :
  paddedF F (VisF e k) ->
  exists k', forall a, k a ≅ Tau (k' a).
Proof with eauto with itree_spec.
  intros. dependent destruction H... eexists. reflexivity.
Qed.


CoFixpoint pad' (ot : itree' E R) : itree E R :=
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (pad' (observe t))
  | VisF e k => Vis e (fun x => Tau (pad' (observe (k x)))) 
  end.

Definition pad t := pad' (observe t).

Lemma pad_ret r : pad (Ret r) ≅ Ret r.
Proof.
  pstep.
  red. simpl.
  constructor. auto.
Qed.

Lemma pad_tau t : pad (Tau t) ≅ Tau (pad t).
Proof.
  pstep. red. cbn. constructor. left. enough (pad t ≅ pad t). auto.
  reflexivity.
Qed.

Lemma pad_vis {X} (e : E X) k : pad (Vis e k) ≅ Vis e (fun x => Tau (pad (k x))).
Proof.
  pstep. red. cbn. constructor. left.  pstep. constructor.
  left. enough (pad (k v) ≅ pad (k v)). auto. reflexivity.
Qed.

End padded.

#[global] Hint Constructors paddedF : itree_spec.

Theorem pad_is_padded {E : Type -> Type} {R : Type} : forall t : itree E R, padded (pad t).
Proof with eauto with itree_spec.
  pcofix CIH. intros. pstep. unfold pad.
  destruct (observe t); red; simpl; eauto with itree_spec.
Qed.
#[global] Hint Resolve padded_monotone_ : paco.
#[global] Hint Resolve padded_monotone_ : itree_spec.
#[global] Hint Resolve pad_is_padded : itree_spec.
#[global] Hint Resolve pad_is_padded : solve_padded.

Theorem pad_eutt {E : Type -> Type} {R : Type} : forall t : itree E R, t ≈ pad t.
Proof with eauto with itree_spec.
  ginit. gcofix CIH. intros.
  unfold pad.
  destruct (observe t) eqn : Ht; symmetry in Ht; apply simpobs in Ht.
  - rewrite Ht.
    gstep. red; simpl. constructor; auto.
  - rewrite Ht.
    gstep. red; simpl.
    constructor.
    gfinal. eauto.
  - rewrite Ht. gstep. red. cbn.
    constructor. intros. red.
    rewrite tau_euttge.
    gfinal. eauto.
Qed.

Theorem pad_eq_itree {E : Type -> Type} {R : Type} : forall t1 t2 : itree E R, t1 ≅ t2 -> pad t1 ≅ pad t2.
Proof with eauto with itree_spec.
  intros t1 t2 H.
  apply bisimulation_is_eq in H.
  subst.
  reflexivity.
Qed.

Global Instance pad_Proper {b1 b2 : bool} {E : Type -> Type} {R : Type} : Proper (eqit eq b1 b2 ==> eqit eq b1 b2) (@pad E R).
Proof.
  pcofix CIH.
  intros t1 t2 Ht12. pstep. red. unfold pad.
  punfold Ht12. red in Ht12. hinduction Ht12 before r;
    intros; cbn; eauto.
  - constructor. auto.
  - constructor. pclearbot. right. eapply CIH; eauto.
  - constructor. left. pstep. constructor. pclearbot. right.
    eapply CIH; eauto. apply REL.
  - constructor; auto.
  - constructor; auto.
Qed.

Theorem pad_bind {E : Type -> Type} {R S: Type} : forall (t : itree E R) (k : R -> itree E S),
    pad (ITree.bind t k) ≅ ITree.bind (pad t) (fun x => pad (k x)).
Proof.
  ginit. gcofix CIH. intros t k.
  destruct (observe t) eqn : Heq; symmetry in Heq; apply simpobs in Heq.
  - rewrite Heq. rewrite pad_ret. repeat rewrite bind_ret_l.
    apply Reflexive_eqit_gen. auto.
  - repeat rewrite Heq. rewrite pad_tau. repeat rewrite bind_tau. gstep.
    red; cbn.
    constructor.
    gfinal. eauto.
  - repeat rewrite Heq. rewrite pad_vis. repeat rewrite bind_vis. rewrite pad_vis.
    gstep. constructor. intros. unfold id. gstep. red; cbn. constructor. gfinal. left. eapply CIH.
Qed.

Theorem pad_iter E R S (body : R -> itree E (R + S)):
  forall r, pad (ITree.iter body r) ≅ ITree.iter (fun r => pad (body r)) r.
Proof.
  ginit. gcofix CIH.
  intros. setoid_rewrite unfold_iter. rewrite pad_bind.
  guclo eqit_clo_bind. econstructor.
  reflexivity. intros. subst. destruct u2.
  - rewrite pad_tau. gstep. constructor. gfinal. left. eauto.
  - rewrite pad_ret. gstep. constructor. auto.
Qed.
