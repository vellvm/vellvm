From Stdlib Require Export
  Datatypes
  Arith.PeanoNat
  Arith.Peano_dec
  Arith.Compare
  Wf_nat
  Morphisms
  Setoid
  Program.Equality
  Lists.List
  Logic.Eqdep_dec
  Logic.EqdepFacts
  Eqdep EqdepFacts
  Logic.ProofIrrelevance.

From ITree Require Import
  Basics.HeterogeneousRelations
  Eq.Eqit.

From ITreeSpec Require Import
  ITreeSpecDefinition
  ITreeSpecFacts
  ITreeSpecCombinatorFacts
  RecSpecFix
  SpecM
  MRecSpec.

From Paco Require Import paco.

Export SigTNotations.
Import SpecMNotations.
Local Open Scope entree_scope.


(*** Pre- and Post-condition relations for SpecM ***)

Definition SpecPreRel (E1 E2 : EvType) stk1 stk2 :=
  Rel (FunStackE E1 stk1) (FunStackE E2 stk2).
Definition SpecPostRel (E1 E2 : EvType) stk1 stk2 :=
  PostRel (FunStackE E1 stk1) (FunStackE E2 stk2).

(* The precondition requiring events on both sides to be equal *)
Definition eqPreRel {E stk} : SpecPreRel E E stk stk := eq.

(* The postcondition requiring return values on both sides to be equal *)
Definition eqPostRel {E stk} : SpecPostRel E E stk stk :=
  fun e1 e2 a1 a2 => eq_dep1 _ _ e1 a1 e2 a2.



(*** The definition of letrec refinement ***)
Section lr_refines.

Context {E1 E2 : EvType} {stk1 stk2 : FunStack} {R1 R2 : Type}.
Context (funs1 : StackTuple E1 stk1 stk1) (funs2 : StackTuple E2 stk2 stk2).

Context (RPre : SpecPreRel E1 E2 stk1 stk2)
  (RPost : SpecPostRel E1 E2 stk1 stk2) (RR : R1 -> R2 -> Prop).

Inductive lr_refinesF (sim : SpecM E1 stk1 R1 -> SpecM E2 stk2 R2 -> Prop) : SpecM' E1 stk1 R1 -> SpecM' E2 stk2 R2 -> Prop :=

(* Ret |= Ret *)
| lr_refinesF_Ret r1 r2 : RR r1 r2 -> lr_refinesF sim (RetF r1) (RetF r2)

(* t1 |= t2 => Tau t1 |= Tau t2 *)
| lr_refinesF_Tau t1 t2 : sim t1 t2 -> lr_refinesF sim (TauF t1) (TauF t2)

(* RPre e1 e2 -> (forall a b, RPost e1 e2 a b -> k1 a |= k2 b) ->
   Vis e1 k1 |= Vis e2 k2 *)
| lr_refinesF_Vis e1 e2 k1 k2 :
  RPre e1 e2 -> (forall a b, RPost e1 e2 a b -> sim (k1 a) (k2 b)) ->
  lr_refinesF sim (VisF (Spec_vis e1) k1) (VisF (Spec_vis e2) k2)

(* t1 |= t2 => Tau t1 |= t2 *)
| lr_refinesF_TauL t1 ot2 : lr_refinesF sim (observe t1) ot2 ->
                            lr_refinesF sim (TauF t1) ot2

(* t1 |= t2 => t1 |= Tau t2 *)
| lr_refinesF_TauR ot1 t2 : lr_refinesF sim ot1 (observe t2) ->
                            lr_refinesF sim ot1 (TauF t2)

(* (forall a, t1 |= k a) => t1 |= Forall k *)
| lr_refinesF_forallR A ot1 k : (forall a, lr_refinesF sim ot1 (TauF (k a))) ->
                                lr_refinesF sim ot1 (VisF (Spec_forall A) k)

(* (exists a, t1 |= k a) => t1 |= Exists k *)
| lr_refinesF_existsR A ot1 k a : lr_refinesF sim ot1 (TauF (k a)) ->
                                  lr_refinesF sim ot1 (VisF (Spec_exists A) k)

(* (exists a, k a |= t2) => Forall k |= t2 *)
| lr_refinesF_forallL A ot2 k a : lr_refinesF sim (TauF (k a)) ot2 ->
                                  lr_refinesF sim (VisF (Spec_forall A) k) ot2

(* (forall a, k a |= t2) => Exists k |= t2 *)
| lr_refinesF_existsL A ot2 k : (forall a, lr_refinesF sim (TauF (k a)) ot2) ->
                                lr_refinesF sim (VisF (Spec_exists A) k) ot2

(* apply funs1 call1 >>= k1 |= t2 => CallS call1 >>= k1 |= t2 *)
| lr_refinesF_unfoldL call1 k1 ot2 :
    lr_refinesF sim (TauF (applyStackTuple E1 stk1 funs1 call1 >>= k1)) ot2 ->
    lr_refinesF sim (VisF (Spec_vis (inl call1)) k1) ot2

(* t1 |= apply funs2 call2 >>= k2 => t1 |= CallS call2 >>= k2 *)
| lr_refinesF_unfoldR ot1 call2 k2 :
    lr_refinesF sim ot1 (TauF (applyStackTuple E2 stk2 funs2 call2 >>= k2)) ->
    lr_refinesF sim ot1 (VisF (Spec_vis (inl call2)) k2)
.


(** The standard Paco nonsense **)

Hint Constructors lr_refinesF : entree_spec.

Definition lr_refines_ sim : SpecM E1 stk1 R1 -> SpecM E2 stk2 R2 -> Prop :=
  fun t1 t2 => lr_refinesF sim (observe t1) (observe t2).

Lemma monotone_lr_refinesF ot1 ot2 sim sim' (LE : sim <2= sim')
      (IN : lr_refinesF sim ot1 ot2) : lr_refinesF sim' ot1 ot2.
Proof with eauto with entree_spec.
  induction IN...
Qed.

Lemma monotone_lr_refines_: monotone2 lr_refines_.
Proof. red. intros. eapply monotone_lr_refinesF; eauto. Qed.

(* lr_refines is the coinductive closure of lr_refinesF *)
Definition lr_refines := paco2 lr_refines_ bot2.

(* The unfolding of lr_refines to an lr_refinesF *)
Definition lr_refinesF_u := lr_refinesF (upaco2 lr_refines_ bot2).

End lr_refines.

Global Hint Resolve monotone_lr_refines_ : paco.



(*** Pre/post conditions on SpecM events ***)

(* Lift a relation on FunStackE events from the nil stack to arbitrary ones *)
Definition liftNilRel {E1 E2 stk1 stk2}
  (R : Rel (FunStackE E1 pnil) (FunStackE E2 pnil)) :
  Rel (FunStackE E1 stk1) (FunStackE E2 stk2) :=
  fun e1 e2 => match e1,e2 with
               | inr e1', inr e2' => R (inr e1') (inr e2')
               | _,_ => False
               end.

(* Lift a postcondition on FunStackE events from the nil stack to arbitrary ones *)
Definition liftNilPostRel {E1 E2 stk1 stk2}
  (R : PostRel (FunStackE E1 pnil) (FunStackE E2 pnil)) :
  PostRel (FunStackE E1 stk1) (FunStackE E2 stk2) :=
  fun e1 e2 => match e1,e2 with
               | inr e1', inr e2' => R (inr e1') (inr e2')
               | _,_ => fun _ _ => False
               end.

(* Compose two liftNilRel proofs *)
Lemma liftNilRel_compose {E1 E2 E3 stk1 stk2 stk3} R12 R23 x y z :
  @liftNilRel E1 E2 stk1 stk2 R12 x y ->
  @liftNilRel E2 E3 stk2 stk3 R23 y z ->
  liftNilRel (rcompose R12 R23) x z.
Proof.
  intros. destruct x; destruct y; destruct z; cbn in *; try contradiction.
  eexists; split; eassumption.
Qed.

Lemma elim_RComposePostRel {E1 E2 E3} `{EncodingType E1} `{EncodingType E2}
  `{EncodingType E3} {R1 : Rel E1 E2} {R2 : Rel E2 E3}
  {RPost1 RPost2 a b c x z} :
  R1 a b -> R2 b c ->
  RComposePostRel R1 R2 RPost1 RPost2 a c x z ->
  exists y, RPost1 a b x y /\ RPost2 b c y z.
Proof.
  intros. destruct H4. apply H4; assumption.
Qed.

(* Destruct the composition of two liftNilPostRel proofs *)
Lemma liftNilPostRel_compose_elim {E1 E2 E3 stk1 stk2 stk3 R12 R23 RPost12 RPost23}
  {e1 : FunStackE E1 stk1} {e2 : FunStackE E2 stk2} {e3 : FunStackE E3 stk3} {x z} :
  liftNilRel R12 e1 e2 -> liftNilRel R23 e2 e3 ->
  liftNilPostRel (RComposePostRel R12 R23 RPost12 RPost23) e1 e3 x z ->
  exists y:encodes e2,
    liftNilPostRel RPost12 e1 e2 x y /\ liftNilPostRel RPost23 e2 e3 y z.
Proof.
  intros. destruct e1; destruct e2; destruct e3; cbn in *; try contradiction.
  destruct (elim_RComposePostRel H H0 H1). destruct H2.
  eexists; split; eassumption.
Qed.

(* Add a precondition for recursive calls *)
Definition addCallPreRel {E1 E2 : EvType} {stk1 stk2}
           (precond : Rel (StackCall stk1) (StackCall stk2))
           (RPre : Rel (FunStackE E1 pnil) (FunStackE E2 pnil)) :
  Rel (FunStackE E1 stk1) (FunStackE E2 stk2) :=
  fun a1 a2 => match a1,a2 with
               | inl args1, inl args2 => precond args1 args2
               | inr ev1, inr ev2 => RPre (inr ev1) (inr ev2)
               | _, _ => False
               end.

(* Add a postcondition for recursive calls *)
Definition addCallPostRel {E1 E2 : EvType} {stk1 stk2}
           (postcond : PostRel (StackCall stk1) (StackCall stk2))
           (RPost : PostRel (FunStackE E1 pnil) (FunStackE E2 pnil)) :
  PostRel (FunStackE E1 stk1) (FunStackE E2 stk2) :=
  fun a1 a2 => match a1,a2 with
               | inl args1, inl args2 => postcond args1 args2
               | inr ev1, inr ev2 => RPost (inr ev1) (inr ev2)
               | _, _ => fun _ _ => False
               end.


(*** Inversion lemmas about refinement ***)
Section lr_refines_inv.
Context {E1 E2 : EvType} {stk1 stk2 : FunStack} {R1 R2 : Type}.
Context (funs1 : StackTuple E1 stk1 stk1) (funs2 : StackTuple E2 stk2 stk2).

Context (RPre : Rel (FunStackE E1 stk1) (FunStackE E2 stk2))
  (RPost : PostRel (FunStackE E1 stk1) (FunStackE E2 stk2))
  (RR : R1 -> R2 -> Prop).

(* Invert a Tau on the left of a refinement *)
Lemma lr_refines_TauL_inv t1 t2 :
  lr_refines funs1 funs2 RPre RPost RR (Tau t1) t2 ->
  lr_refines funs1 funs2 RPre RPost RR t1 t2.
Proof.
  remember (TauF t1) as x.
  intro. punfold H. red in H. simpl in H. pfold. red.
  remember (observe t2) as ot2.
  clear t2 Heqot2.
  induction H; inversion Heqx.
  - pclearbot. constructor. pstep_reverse. rewrite <- H1.
    eapply paco2_mon; [ eassumption | ]. intros x0 x1 b; destruct b.
  - rewrite <- H1. eapply monotone_lr_refinesF; [ | eassumption ].
    intros. pclearbot. left. eapply paco2_mon; [ eassumption | ].
    intros. contradiction.
  - constructor. apply IHlr_refinesF. assumption.
  - constructor. intros. apply H0. assumption.
  - econstructor. apply IHlr_refinesF. assumption.
  - constructor. apply IHlr_refinesF. assumption.
Qed.

(* Invert a Tau on the left of an unfolded lr_refinesF refinement *)
Lemma lr_refinesF_TauL_inv t1 t2 :
  lr_refinesF_u funs1 funs2 RPre RPost RR (TauF t1) (observe t2) ->
  lr_refinesF_u funs1 funs2 RPre RPost RR (observe t1) (observe t2).
Proof.
  unfold lr_refinesF_u.
  intros. pstep_reverse. apply lr_refines_TauL_inv. pstep. assumption.
Qed.

(* Invert a Tau on the right of a refinement *)
Lemma lr_refines_TauR_inv t1 t2 :
  lr_refines funs1 funs2 RPre RPost RR t1 (Tau t2) ->
  lr_refines funs1 funs2 RPre RPost RR t1 t2.
Proof.
  remember (TauF t2) as x.
  intro. punfold H. red in H. simpl in H. pfold. red.
  remember (observe t1) as ot1. clear t1 Heqot1.
  induction H; inversion Heqx.
  - pclearbot. constructor. pstep_reverse. rewrite <- H1.
    eapply paco2_mon; [ eassumption | ]. intros x0 x1 b; destruct b.
  - constructor. apply IHlr_refinesF. assumption.
  - rewrite <- H1. eapply monotone_lr_refinesF; [ | eassumption ].
    intros. pclearbot. left. eapply paco2_mon; [ eassumption | ].
    intros. contradiction.
  - econstructor. apply IHlr_refinesF. assumption.
  - constructor. intros. apply H0. assumption.
  - constructor. apply IHlr_refinesF. assumption.
Qed.

(* Invert a Tau on the right of an unfolded lr_refinesF refinement *)
Lemma lr_refinesF_TauR_inv t1 t2 :
  lr_refinesF_u funs1 funs2 RPre RPost RR (observe t1) (TauF t2) ->
  lr_refinesF_u funs1 funs2 RPre RPost RR (observe t1) (observe t2).
Proof.
  unfold lr_refinesF_u.
  intros. pstep_reverse. apply lr_refines_TauR_inv. pstep. apply H.
Qed.

(* Invert a refinement with a forall on the right to a unviversal *)
Lemma lr_refines_forallR_inv A t1 k2 :
  lr_refines funs1 funs2 RPre RPost RR
    t1 (Vis (@Spec_forall (FunStackE E2 stk2) A) k2) ->
  forall a, lr_refines funs1 funs2 RPre RPost RR t1 (Tau (k2 a)).
Proof.
  intros ref12 a. punfold ref12. red in ref12. cbn in ref12. pstep. red.
  remember (observe t1) as ot1; clear t1 Heqot1.
  remember (VisF (Spec_forall A) k2) as ot2.
  induction ref12; try discriminate.
  - apply lr_refinesF_TauL. apply IHref12. assumption.
  - inversion Heqot2. revert k Heqot2 H H0 H3; rewrite H2; intros.
    inj_existT. rewrite H3 in H. apply H.
  - eapply lr_refinesF_forallL. apply IHref12. assumption.
  - apply lr_refinesF_existsL. intros. apply H0. assumption.
  - apply lr_refinesF_unfoldL. apply IHref12. assumption.
Qed.


(* Invert a refinement with an exists on the left to a unviversal *)
Lemma lr_refines_existsL_inv A k1 t2 :
  lr_refines funs1 funs2 RPre RPost RR
    (Vis (@Spec_exists (FunStackE E1 stk1) A) k1) t2 ->
  forall a, lr_refines funs1 funs2 RPre RPost RR (Tau (k1 a)) t2.
Proof.
  intros ref12 a. punfold ref12. red in ref12. cbn in ref12. pstep. red.
  remember (observe t2) as ot2; clear t2 Heqot2.
  remember (VisF (Spec_exists A) k1) as ot1.
  induction ref12; try discriminate.
  - apply lr_refinesF_TauR. apply IHref12. assumption.
  - apply lr_refinesF_forallR. intros. apply H0. assumption.
  - eapply lr_refinesF_existsR. apply IHref12. assumption.
  - inversion Heqot1. revert k Heqot1 ot2 H a H0 H3; rewrite H2; intros.
    inj_existT. rewrite H3 in H. apply H.
  - apply lr_refinesF_unfoldR. apply IHref12. assumption.
Qed.


(* The result of inverting a refinement with a forall on the left, which could
take 0 or more right-hand side steps before the forallL rule. Note that the Taus
in the quantifier rules are removed in this definition, because this is needed
in the transitivity proof. *)
Inductive forallL_LRRefinesF {A : QuantEnc} (k1 : encodes A -> SpecM E1 stk1 R1)
  : SpecM' E2 stk2 R2 -> Prop :=
  | forallL_LRRefinesF_forallL t (a : encodes A) :
    lr_refinesF_u funs1 funs2 RPre RPost RR (TauF (k1 a)) t ->
    forallL_LRRefinesF k1 t
  | forallL_LRRefinesF_forallR (B : QuantEnc) k2 :
    (forall b, forallL_LRRefinesF k1 (observe (k2 b))) ->
    forallL_LRRefinesF k1 (VisF (Spec_forall B) k2)
  | forallL_LRRefinesF_existsR B k2 (b : encodes B) :
    forallL_LRRefinesF k1 (observe (k2 b)) ->
    forallL_LRRefinesF k1 (VisF (Spec_exists B : SpecEvent (FunStackE _ _)) k2)
  | forallL_LRRefinesF_TauR t2 :
    forallL_LRRefinesF k1 (observe t2) ->
    forallL_LRRefinesF k1 (TauF t2)
  | forallL_LRRefinesF_unfoldR call2 k2 :
    forallL_LRRefinesF k1 (observe (applyStackTuple E2 stk2 funs2 call2 >>= k2)) ->
    forallL_LRRefinesF k1 (VisF (Spec_vis (inl call2)) k2)
.

(* Helper lemma to invert a Tau in a forallL_LRRefinesF *)
Lemma forallL_LRRefinesF_TauL_inv A k1 t2 :
  @forallL_LRRefinesF A k1 (TauF t2) ->
  @forallL_LRRefinesF A k1 (observe t2).
Proof.
  intro H. remember (TauF t2) as tau_t2.
  revert t2 Heqtau_t2; induction H; intros; try discriminate.
  - subst t. eapply forallL_LRRefinesF_forallL. red. observe_tau. pstep_reverse.
    apply lr_refines_TauR_inv. pstep. apply H.
  - inversion Heqtau_t2. subst t0. assumption.
Qed.

(* Invert a refinement of a forall on the left to a forallL_LRRefinesF *)
Lemma lr_refinesF_forallL_inv A k1 t2 :
  lr_refinesF_u funs1 funs2 RPre RPost RR
    (VisF (@Spec_forall (FunStackE E1 stk1) A) k1) t2 ->
  forallL_LRRefinesF k1 t2.
Proof.
  intros. remember (VisF (Spec_forall A) k1) as ot1.
  induction H; try discriminate.
  - apply forallL_LRRefinesF_TauR; apply IHlr_refinesF; assumption.
  - apply forallL_LRRefinesF_forallR; intros.
    apply forallL_LRRefinesF_TauL_inv. apply H0. assumption.
  - eapply forallL_LRRefinesF_existsR.
    apply forallL_LRRefinesF_TauL_inv.
    apply IHlr_refinesF. assumption.
  - inversion Heqot1. subst A0. inj_existT. subst k.
    eapply forallL_LRRefinesF_forallL. apply H.
  - apply forallL_LRRefinesF_unfoldR. apply forallL_LRRefinesF_TauL_inv.
    apply IHlr_refinesF. assumption.
Qed.


(* The result of inverting a refinement with an exists on the right, which could
take 0 or more left-hand side steps before the existsR rule. Note that the Taus
in the quantifier rules are removed in this definition, because this is needed
in the transitivity proof. *)
Inductive existsR_LRRefinesF {A : QuantEnc} (k2 : encodes A -> SpecM E2 stk2 R2)
  : SpecM' E1 stk1 R1 -> Prop :=
  | existsR_LRRefinesF_existsR t (a : encodes A) :
    lr_refinesF_u funs1 funs2 RPre RPost RR t (TauF (k2 a)) ->
    existsR_LRRefinesF k2 t
  | existsR_LRRefinesF_forallL B k1 (b : encodes B) :
    existsR_LRRefinesF k2 (observe (k1 b)) ->
    existsR_LRRefinesF k2 (VisF (Spec_forall B : SpecEvent (FunStackE _ _)) k1)
  | existsR_LRRefinesF_existsL (B : QuantEnc) k1 :
    (forall b, existsR_LRRefinesF k2 (observe (k1 b))) ->
    existsR_LRRefinesF k2 (VisF (Spec_exists B) k1)
  | existsR_LRRefinesF_TauL t1 :
    existsR_LRRefinesF k2 (observe t1) ->
    existsR_LRRefinesF k2 (TauF t1)
  | existsR_LRRefinesF_unfoldL call1 k1 :
    existsR_LRRefinesF k2 (observe (applyStackTuple E1 stk1 funs1 call1 >>= k1)) ->
    existsR_LRRefinesF k2 (VisF (Spec_vis (inl call1)) k1)
.

(* Helper lemma to invert a Tau in an existsR_LRRefinesF *)
Lemma existsR_LRRefinesF_TauL_inv A k2 t1 :
  @existsR_LRRefinesF A k2 (TauF t1) ->
  @existsR_LRRefinesF A k2 (observe t1).
Proof.
  intro H. remember (TauF t1) as tau_t1.
  revert t1 Heqtau_t1; induction H; intros; try discriminate.
  - subst t. eapply existsR_LRRefinesF_existsR. red. observe_tau. pstep_reverse.
    apply lr_refines_TauL_inv. pstep. apply H.
  - inversion Heqtau_t1. rewrite <- H1. assumption.
Qed.

(* Invert a refinement of an exists on the right to an existsR_LRRefinesF *)
Lemma lr_refinesF_existsR_inv A t1 k2 :
  lr_refinesF_u funs1 funs2 RPre RPost RR
    t1 (VisF (@Spec_exists (FunStackE E2 stk2) A) k2) ->
  existsR_LRRefinesF k2 t1.
Proof.
  intros. remember (VisF (Spec_exists A) k2) as ot2.
  induction H; try discriminate.
  - apply existsR_LRRefinesF_TauL; apply IHlr_refinesF; assumption.
  - inversion Heqot2. revert k Heqot2 a H IHlr_refinesF H2; rewrite H1; intros.
    inj_existT. rewrite H2 in H. eapply existsR_LRRefinesF_existsR. apply H.
  - eapply existsR_LRRefinesF_forallL. apply existsR_LRRefinesF_TauL_inv.
    apply IHlr_refinesF. assumption.
  - apply existsR_LRRefinesF_existsL. intros. apply existsR_LRRefinesF_TauL_inv.
    apply H0. assumption.
  - apply existsR_LRRefinesF_unfoldL. apply existsR_LRRefinesF_TauL_inv.
    apply IHlr_refinesF. assumption.
Qed.

(* Invert a refinement with a corecursive call on the left *)
Lemma lr_refines_callL_inv pre post call1 k1 t2 :
  lr_refines funs1 funs2 (liftNilRel pre) (liftNilPostRel post) RR
    (Vis (Spec_vis (inl call1)) k1) t2 ->
  lr_refines funs1 funs2 (liftNilRel pre) (liftNilPostRel post) RR
    (Tau (applyStackTuple E1 stk1 funs1 call1 >>= k1)) t2.
Proof.
  intros ref12. punfold ref12. red in ref12. cbn in ref12. pstep. red.
  remember (observe t2) as ot2; clear t2 Heqot2.
  remember (VisF (Spec_vis (inl call1)) k1) as ot1.
  induction ref12; try discriminate.
  - inversion Heqot1. rewrite H2 in H. destruct e2; destruct H.
  - apply lr_refinesF_TauR. apply IHref12. assumption.
  - apply lr_refinesF_forallR; intros. apply H0. assumption.
  - eapply lr_refinesF_existsR. apply IHref12. assumption.
  - inversion Heqot1. revert k0 Heqot1 ref12 IHref12. rewrite H0. intros.
    remember (injection_VisF_eq Heqot1) as e. clear Heqe. inj_existT.
    rewrite <- e. apply ref12.
  - apply lr_refinesF_unfoldR. apply IHref12. assumption.
Qed.

(* Invert a refinement with a corecursive call on the right *)
Lemma lr_refines_callR_inv pre post t1 call2 k2 :
  lr_refines funs1 funs2 (liftNilRel pre) (liftNilPostRel post) RR
    t1 (Vis (Spec_vis (inl call2)) k2) ->
  lr_refines funs1 funs2 (liftNilRel pre) (liftNilPostRel post) RR
    t1 (Tau (applyStackTuple E2 stk2 funs2 call2 >>= k2)).
Proof.
  intros ref12. punfold ref12. red in ref12. cbn in ref12. pstep. red.
  remember (observe t1) as ot1; clear t1 Heqot1.
  remember (VisF (Spec_vis (inl call2)) k2) as ot2.
  induction ref12; try discriminate.
  - inversion Heqot2. rewrite H2 in H. destruct e1; destruct H.
  - apply lr_refinesF_TauL. apply IHref12. assumption.
  - eapply lr_refinesF_forallL. apply IHref12. assumption.
  - apply lr_refinesF_existsL; intros. apply H0. assumption.
  - apply lr_refinesF_unfoldL. apply IHref12. assumption.
  - inversion Heqot2. revert k0 Heqot2 ref12 IHref12. rewrite H0. intros.
    remember (injection_VisF_eq Heqot2) as e. clear Heqe. inj_existT.
    rewrite <- e. apply ref12.
Qed.

(* The result of inverting a refinement with a Vis on the right, which could
take 0 or more left-hand side steps before either the Vis rule or the unfoldR
rule *)
Inductive visR_LRRefinesF :
  SpecM' E1 stk1 R1 ->
  forall (e2: FunStackE E2 stk2), (encodes e2 -> SpecM E2 stk2 R2) -> Prop :=
  | visR_LRRefinesF_Vis e1 k1 e2 k2 :
    RPre e1 e2 ->
    (forall x y, RPost e1 e2 x y ->
                 lr_refinesF_u funs1 funs2 RPre RPost RR
                   (observe (k1 x)) (observe (k2 y))) ->
    visR_LRRefinesF (VisF (Spec_vis e1) k1) e2 k2
  | visR_LRRefinesF_unfoldR ot1 call2 k2 :
    lr_refinesF_u funs1 funs2 RPre RPost RR
      ot1 (observe (applyStackTuple E2 stk2 funs2 call2 >>= k2)) ->
    visR_LRRefinesF ot1 (inl call2) k2
  | visR_LRRefinesF_forallL B k1 (b : encodes B) e2 k2 :
    visR_LRRefinesF (observe (k1 b)) e2 k2 ->
    visR_LRRefinesF (VisF (Spec_forall B : SpecEvent (FunStackE _ _)) k1) e2 k2
  | visR_LRRefinesF_existsL (B : QuantEnc) k1 e2 k2 :
    (forall b, visR_LRRefinesF (observe (k1 b)) e2 k2) ->
    visR_LRRefinesF (VisF (Spec_exists B) k1) e2 k2
  | visR_LRRefinesF_TauL t1 e2 k2 :
    visR_LRRefinesF (observe t1) e2 k2 ->
    visR_LRRefinesF (TauF t1) e2 k2
  | visR_LRRefinesF_unfoldL call1 k1 e2 k2 :
    visR_LRRefinesF (observe (applyStackTuple E1 stk1 funs1 call1 >>= k1)) e2 k2 ->
    visR_LRRefinesF (VisF (Spec_vis (inl call1)) k1) e2 k2
.

(* Helper lemma to invert a Tau in a visR_LRRefinesF *)
Lemma visR_LRRefinesF_TauL_inv t1 e2 k2 :
  visR_LRRefinesF (TauF t1) e2 k2 ->
  visR_LRRefinesF (observe t1) e2 k2.
Proof.
  intro H. remember (TauF t1) as tau_t1.
  revert t1 Heqtau_t1; induction H; intros; try discriminate.
  - subst ot1. apply visR_LRRefinesF_unfoldR.
    apply lr_refinesF_TauL_inv. assumption.
  - inversion Heqtau_t1. subst t0. assumption.
Qed.

(* Invert a refinement of an event on the right to an visR_LRRefinesF *)
Lemma lr_refinesF_VisR_inv t1 e2 k2 :
  lr_refinesF_u funs1 funs2 RPre RPost RR t1 (VisF (Spec_vis e2) k2) ->
  visR_LRRefinesF t1 e2 k2.
Proof.
  intros. remember (VisF (Spec_vis e2) k2) as ot2.
  induction H; try discriminate.
  - inversion Heqot2. subst e0.
    set (e := injection_VisF_eq Heqot2); inversion e. inj_existT. subst k0.
    apply visR_LRRefinesF_Vis; [ assumption | ]. intros.
    destruct (H0 x y H2) as [ ref | []]. red.
    pstep_reverse.
  - apply visR_LRRefinesF_TauL; apply IHlr_refinesF; assumption.
  - eapply visR_LRRefinesF_forallL. apply visR_LRRefinesF_TauL_inv.
    apply IHlr_refinesF. assumption.
  - apply visR_LRRefinesF_existsL. intros. apply visR_LRRefinesF_TauL_inv.
    apply H0. assumption.
  - apply visR_LRRefinesF_unfoldL. apply visR_LRRefinesF_TauL_inv.
    apply IHlr_refinesF. assumption.
  - inversion Heqot2. subst e2.
    set (e := injection_VisF_eq Heqot2); inversion e. inj_existT. subst k0.
    apply visR_LRRefinesF_unfoldR. rewrite (entree_beta ot1).
    apply lr_refinesF_TauR_inv. apply H.
Qed.

(* The result of inverting a refinement with a Vis on the left, which could take
0 or more right-hand side steps before either the Vis rule or the unfoldL rule
*)
Inductive visL_LRRefinesF :
  forall (e1: FunStackE E1 stk1), (encodes e1 -> SpecM E1 stk1 R1) ->
  SpecM' E2 stk2 R2 -> Prop :=
  | visL_LRRefinesF_Vis e1 k1 e2 k2 :
    RPre e1 e2 ->
    (forall x y, RPost e1 e2 x y ->
                 lr_refinesF_u funs1 funs2 RPre RPost RR
                   (observe (k1 x)) (observe (k2 y))) ->
    visL_LRRefinesF e1 k1 (VisF (Spec_vis e2) k2)
  | visL_LRRefinesF_unfoldL call1 k1 ot2 :
    lr_refinesF_u funs1 funs2 RPre RPost RR
      (observe (applyStackTuple E1 stk1 funs1 call1 >>= k1)) ot2 ->
    visL_LRRefinesF (inl call1) k1 ot2
  | visL_LRRefinesF_forallR e1 k1 (B : QuantEnc) k2 :
    (forall b, visL_LRRefinesF e1 k1 (observe (k2 b))) ->
    visL_LRRefinesF e1 k1 (VisF (Spec_forall B) k2)
  | visL_LRRefinesF_existsR e1 k1 B (b : encodes B) k2 :
    visL_LRRefinesF e1 k1 (observe (k2 b)) ->
    visL_LRRefinesF e1 k1 (VisF (Spec_exists B : SpecEvent (FunStackE _ _)) k2)
  | visL_LRRefinesF_TauR e1 k1 t2 :
    visL_LRRefinesF e1 k1 (observe t2) ->
    visL_LRRefinesF e1 k1 (TauF t2)
  | visL_LRRefinesF_unfoldR e1 k1 call2 k2 :
    visL_LRRefinesF e1 k1 (observe (applyStackTuple E2 stk2 funs2 call2 >>= k2)) ->
    visL_LRRefinesF e1 k1 (VisF (Spec_vis (inl call2)) k2)
.

(* Helper lemma to invert a Tau in a visL_LRRefinesF *)
Lemma visL_LRRefinesF_TauR_inv e1 k1 t2 :
  visL_LRRefinesF e1 k1 (TauF t2) ->
  visL_LRRefinesF e1 k1 (observe t2).
Proof.
  intro H. remember (TauF t2) as tau_t2.
  revert t2 Heqtau_t2; induction H; intros; try discriminate.
  - subst ot2. apply visL_LRRefinesF_unfoldL.
    apply lr_refinesF_TauR_inv. assumption.
  - inversion Heqtau_t2. subst t0. assumption.
Qed.

(* Invert a refinement of an event on the right to an visL_LRRefinesF *)
Lemma lr_refinesF_VisL_inv e1 k1 t2 :
  lr_refinesF_u funs1 funs2 RPre RPost RR (VisF (Spec_vis e1) k1) t2 ->
  visL_LRRefinesF e1 k1 t2.
Proof.
  intros. remember (VisF (Spec_vis e1) k1) as ot1.
  induction H; try discriminate.
  - inversion Heqot1. subst e0.
    set (e := injection_VisF_eq Heqot1); inversion e. inj_existT. subst k0.
    apply visL_LRRefinesF_Vis; [ assumption | ]. intros.
    destruct (H0 x y H2) as [ ref | []].
    red. pstep_reverse.
  - apply visL_LRRefinesF_TauR; apply IHlr_refinesF; assumption.
  - apply visL_LRRefinesF_forallR. intros. apply visL_LRRefinesF_TauR_inv.
    apply H0. assumption.
  - eapply visL_LRRefinesF_existsR. apply visL_LRRefinesF_TauR_inv.
    apply IHlr_refinesF. assumption.
  - inversion Heqot1. subst e1.
    set (e := injection_VisF_eq Heqot1); inversion e. inj_existT. subst k0.
    apply visL_LRRefinesF_unfoldL. rewrite (entree_beta ot2).
    apply lr_refinesF_TauL_inv. apply H.
  - apply visL_LRRefinesF_unfoldR. apply visL_LRRefinesF_TauR_inv.
    apply IHlr_refinesF. assumption.
Qed.


End lr_refines_inv.


(*** Refinement respects entree equivalence ***)
Section lr_refines_proper.

Context {E1 E2 : EvType} {stk1 stk2 : FunStack} {R1 R2 : Type}.
Context (funs1 : StackTuple E1 stk1 stk1) (funs2 : StackTuple E2 stk2 stk2).

Context (RPre : Rel (FunStackE E1 stk1) (FunStackE E2 stk2))
  (RPost : PostRel (FunStackE E1 stk1) (FunStackE E2 stk2))
  (RR : Rel R1 R2).


(* lr_refines is Proper wrt eutt on the right *)
Lemma lr_refines_euttR t1 t2 t2' :
  lr_refines funs1 funs2 RPre RPost RR t1 t2 -> eutt eq t2 t2' ->
  lr_refines funs1 funs2 RPre RPost RR t1 t2'.
Proof.
  revert t1 t2 t2'; pcofix CIH; intros t1 t2 t2' ref12 e.
  destruct t1 as [ ot1 ]. destruct t2 as [ ot2 ].
  punfold ref12. red in ref12. simpl in ref12.
  revert t2' e; induction ref12; intros.
  - destruct t2' as [ ot2' ]; punfold e; red in e. simpl in e.
    remember (RetF r2) as ret_r2. induction e; inversion Heqret_r2.
    + rewrite <- REL; rewrite H1. pstep. apply lr_refinesF_Ret; assumption.
    + pstep. apply lr_refinesF_TauR. pstep_reverse. rewrite <- entree_eta in IHe.
      apply IHe. assumption.
  - pclearbot.
    assert (eutt eq t2 t2'); [ apply eqit_inv_Tau_l; assumption | ]. clear e.
    punfold H0. red in H0. punfold H. red in H.
    destruct t2 as [ ot2 ]. destruct t2' as [ ot2' ].
    simpl in H. simpl in H0. pstep. red. simpl. revert t1 H; induction H0; intros.
    + apply lr_refinesF_TauL. simpl.
      remember (observe t1) as ot1; clear t1 Heqot1.
      remember (RetF r1) as ret_r1.
      induction H; inversion Heqret_r1.
      * apply lr_refinesF_Ret. rewrite <- REL. rewrite <- H1. assumption.
      * apply lr_refinesF_TauL. apply IHlr_refinesF. assumption.
      * eapply lr_refinesF_forallL. apply IHlr_refinesF. assumption.
      * apply lr_refinesF_existsL; intros. apply H0. assumption.
      * apply lr_refinesF_unfoldL. apply IHlr_refinesF. assumption.
    + apply lr_refinesF_Tau. right. pclearbot. eapply CIH; [ | eassumption ].
      apply lr_refines_TauR_inv. pstep. assumption.
    + destruct e.
      * remember (lr_refinesF_VisR_inv _ _ _ _ _ _ _ _ H) as visRef.
        clear H HeqvisRef.
        destruct t1 as [ ot1 ]; simpl in visRef.
        induction visRef.
        -- apply lr_refinesF_TauL.
           apply lr_refinesF_Vis; [ assumption | ]. intros.
           right. pclearbot. eapply CIH; [ | apply REL ].
           pstep; apply H0; assumption.
        -- apply lr_refinesF_unfoldR. apply lr_refinesF_Tau. right.
           pclearbot. eapply CIH; [ pstep; apply H | ].
           eapply (eqit_bind _ (UU:=eq));
             [ | intros u1 u2 eq_u; rewrite eq_u; apply REL ].
           reflexivity.
        -- apply lr_refinesF_TauL.
           eapply (lr_refinesF_forallL _ _ _ _ _ _ _ _ _ b).
           rewrite (entree_eta (k1 b)). apply IHvisRef. intros. apply REL.
        -- apply lr_refinesF_TauL. apply lr_refinesF_existsL; intros.
           rewrite (entree_eta (k1 a)). apply H0. intros. apply REL.
        -- apply lr_refinesF_TauL. rewrite (entree_eta t1).
           apply IHvisRef. intros; apply REL.
        -- apply lr_refinesF_TauL. rewrite <- entree_eta in IHvisRef.
           apply lr_refinesF_unfoldL. apply IHvisRef. intros; apply REL.
      * apply lr_refinesF_forallR. intros. apply lr_refinesF_Tau.
        right. eapply CIH.
        -- apply lr_refines_forallR_inv. pstep. apply H.
        -- pstep. apply EqTauL; [ reflexivity | ].
           destruct (REL a) as [ e | []]. pstep_reverse.
      * assert (existsR_LRRefinesF funs1 funs2 RPre RPost RR k1 (observe t1))
        as ref_exR;
        [ apply lr_refinesF_existsR_inv; apply H | ]. clear H.
        destruct t1 as [ ot1 ]. simpl in ref_exR. induction ref_exR.
        -- eapply lr_refinesF_existsR. apply lr_refinesF_Tau. right.
           pclearbot. eapply CIH; [ | apply REL ].
           apply lr_refines_TauR_inv. pstep. apply H.
        -- apply lr_refinesF_TauL. eapply lr_refinesF_forallL.
           rewrite <- entree_eta in IHref_exR. apply IHref_exR.
        -- apply lr_refinesF_TauL. apply lr_refinesF_existsL. intros.
           rewrite (entree_eta (k0 a)). apply H0.
        -- apply lr_refinesF_TauL. rewrite <- entree_eta in IHref_exR.
           apply IHref_exR.
        -- apply lr_refinesF_TauL. apply lr_refinesF_unfoldL.
           rewrite <- entree_eta in IHref_exR. apply IHref_exR.
    + apply IHeqitF. apply lr_refinesF_TauR_inv. assumption.
    + apply lr_refinesF_Tau. right. rewrite (entree_beta ot1) in H.
      eapply CIH; pstep; [ eassumption | apply H0 ].
  - punfold e; red in e. pstep; red.
    remember (observe t2') as ot2'; clear t2' Heqot2'.
    remember (observe (Vis (Spec_vis e2) k2)) as ot1.
    induction e; inversion Heqot1.
    + subst e. inj_existT. subst k0. apply lr_refinesF_Vis; [ assumption | ].
      intros. destruct (H0 a b H1); [ | destruct H2 ].
      destruct (REL b); [ | destruct H3 ].
      right. eapply CIH; eassumption.
    + apply lr_refinesF_TauR. apply IHe. assumption.
  - pstep. apply lr_refinesF_TauL. pstep_reverse.
    rewrite <- entree_eta in IHref12. apply IHref12. assumption.
  - apply IHref12. apply eqit_inv_Tau_l. rewrite <- entree_eta. assumption.
  - punfold e; red in e. pstep; red. simpl.
    remember (observe t2') as ot2'; clear t2' Heqot2'.
    remember (observe (Vis (Spec_forall A) k)) as ot2.
    induction e; inversion Heqot2.
    + subst e. inj_existT. subst k1. apply lr_refinesF_forallR. intros.
      observe_tau. rewrite (entree_beta ot1). pstep_reverse. eapply H0.
      pstep. constructor. left. destruct (REL a); [ eassumption | destruct H1 ].
    + apply lr_refinesF_TauR. apply IHe. assumption.
  - punfold e; red in e. pstep; red. simpl.
    remember (observe t2') as ot2'; clear t2' Heqot2'.
    remember (observe (Vis (Spec_exists A) k)) as ot2.
    induction e; inversion Heqot2.
    + subst e. inj_existT. subst k1. eapply lr_refinesF_existsR.
      observe_tau. rewrite (entree_beta ot1). pstep_reverse. apply IHref12.
      pstep. constructor. left. destruct (REL a); [ eassumption | destruct H ].
    + apply lr_refinesF_TauR. apply IHe. assumption.
  - pstep. eapply lr_refinesF_forallL. observe_tau. pstep_reverse.
  - pstep. apply lr_refinesF_existsL; intros. observe_tau. pstep_reverse.
  - pstep. apply lr_refinesF_unfoldL. observe_tau. pstep_reverse.
  - punfold e; red in e. pstep; red. simpl.
    remember (observe t2') as ot2'; clear t2' Heqot2'. simpl in e.
    remember (VisF (Spec_vis (inl call2)) k2) as ot2.
    induction e; inversion Heqot2.
    + subst e. inj_existT. subst k1. apply lr_refinesF_unfoldR.
      observe_tau. rewrite (entree_beta ot1). pstep_reverse. apply IHref12.
      pstep. constructor. left. eapply eqit_bind; [ reflexivity | ]. intros.
      rewrite H. destruct (REL u2); [ | destruct H0 ]. assumption.
    + apply lr_refinesF_TauR. apply IHe. assumption.
Qed.


(* lr_refines is Proper wrt eutt on the left *)
Lemma lr_refines_euttL t1 t1' t2 :
  eutt eq t1' t1 -> lr_refines funs1 funs2 RPre RPost RR t1 t2 ->
  lr_refines funs1 funs2 RPre RPost RR t1' t2.
Proof.
  revert t1 t1' t2; pcofix CIH; intros t1 t1' t2 e ref12.
  destruct t1 as [ ot1 ]. destruct t2 as [ ot2 ].
  punfold ref12. red in ref12. simpl in ref12.
  revert t1' e; induction ref12; intros.
  - destruct t1' as [ ot1' ]; punfold e; red in e. simpl in e.
    remember (RetF r1) as ret_r1. induction e; inversion Heqret_r1.
    + subst r3; subst r0. pstep. apply lr_refinesF_Ret; assumption.
    + pstep. apply lr_refinesF_TauL. pstep_reverse. rewrite <- entree_eta in IHe.
      apply IHe. assumption.
  - pclearbot.
    assert (eutt eq t1' t1); [ apply eqit_inv_Tau_r; assumption | ]. clear e.
    punfold H0. red in H0. punfold H. red in H.
    destruct t1 as [ ot1 ]. destruct t1' as [ ot1' ].
    simpl in H. simpl in H0. pstep. red. simpl. revert t2 H; induction H0; intros.
    + apply lr_refinesF_TauR. simpl.
      remember (observe t2) as ot2; clear t2 Heqot2.
      remember (RetF r2) as ret_r2.
      induction H; inversion Heqret_r2.
      * apply lr_refinesF_Ret. rewrite REL. rewrite <- H1. assumption.
      * apply lr_refinesF_TauR. apply IHlr_refinesF. assumption.
      * apply lr_refinesF_forallR; intros. apply H0. assumption.
      * eapply lr_refinesF_existsR. apply IHlr_refinesF. assumption.
      * apply lr_refinesF_unfoldR. apply IHlr_refinesF. assumption.
    + apply lr_refinesF_Tau. right. pclearbot. eapply CIH; [ eassumption | ].
      apply lr_refines_TauL_inv. pstep. assumption.
    + destruct e.
      * remember (lr_refinesF_VisL_inv _ _ _ _ _ _ _ _ H) as visRef.
        clear H HeqvisRef.
        destruct t2 as [ ot2 ]; simpl in visRef.
        induction visRef.
        -- apply lr_refinesF_TauR.
           apply lr_refinesF_Vis; [ assumption | ]. intros.
           right. pclearbot. eapply CIH; [ apply REL | ].
           pstep; apply H0; assumption.
        -- apply lr_refinesF_unfoldL. apply lr_refinesF_Tau. right.
           pclearbot. eapply CIH; [ | pstep; apply H ].
           eapply (eqit_bind _ (UU:=eq));
             [ | intros u1 u2 eq_u; rewrite eq_u; apply REL ].
           reflexivity.
        -- apply lr_refinesF_TauR. apply lr_refinesF_forallR; intros.
           rewrite (entree_eta (k2 a)). apply H0. intros. apply REL.
        -- apply lr_refinesF_TauR.
           apply (lr_refinesF_existsR _ _ _ _ _ _ _ _ _ b).
           rewrite (entree_eta (k2 b)). apply IHvisRef. intros. apply REL.
        -- apply lr_refinesF_TauR. rewrite (entree_eta t2).
           apply IHvisRef. intros; apply REL.
        -- apply lr_refinesF_TauR. rewrite <- entree_eta in IHvisRef.
           apply lr_refinesF_unfoldR. apply IHvisRef. intros; apply REL.
      * assert (forallL_LRRefinesF funs1 funs2 RPre RPost RR k2 (observe t2))
          as ref_allL;
          [ apply lr_refinesF_forallL_inv; apply H | ]. clear H.
        destruct t2 as [ ot2 ]. simpl in ref_allL. induction ref_allL.
        -- eapply lr_refinesF_forallL. apply lr_refinesF_Tau. right.
           pclearbot. eapply CIH; [ apply REL | ].
           apply lr_refines_TauL_inv. pstep. apply H.
        -- apply lr_refinesF_TauR. apply lr_refinesF_forallR. intros.
           rewrite (entree_eta (k0 a)). apply H0.
        -- apply lr_refinesF_TauR. eapply lr_refinesF_existsR.
           rewrite <- entree_eta in IHref_allL. apply IHref_allL.
        -- apply lr_refinesF_TauR. rewrite <- entree_eta in IHref_allL.
           apply IHref_allL.
        -- apply lr_refinesF_TauR. apply lr_refinesF_unfoldR.
           rewrite <- entree_eta in IHref_allL. apply IHref_allL.
      * apply lr_refinesF_existsL. intros. apply lr_refinesF_Tau.
        right. eapply CIH; [ | apply lr_refines_existsL_inv; pstep; apply H ].
        destruct (REL a) as [ e | []]. pstep. apply EqTauR; [ reflexivity | ].
        pstep_reverse.
    + apply lr_refinesF_Tau. right. rewrite (entree_beta ot2) in H0.
      eapply CIH; pstep; [ apply H0 | eassumption ].
    + apply IHeqitF. apply lr_refinesF_TauL_inv. assumption.
  - punfold e; red in e. pstep; red.
    remember (observe t1') as ot1'; clear t1' Heqot1'.
    remember (observe (Vis (Spec_vis e1) k1)) as ot1.
    induction e; inversion Heqot1.
    + subst e. inj_existT. subst k3. apply lr_refinesF_Vis; [ assumption | ].
      intros. destruct (H0 a b H1); [ | destruct H2 ].
      destruct (REL a); [ | destruct H3 ].
      right. eapply CIH; eassumption.
    + apply lr_refinesF_TauL. apply IHe. assumption.
  - apply IHref12. apply eqit_inv_Tau_r. rewrite <- entree_eta. assumption.
  - pstep. apply lr_refinesF_TauR. pstep_reverse.
    rewrite <- entree_eta in IHref12. apply IHref12. assumption.
  - pstep. apply lr_refinesF_forallR; intros. observe_tau. pstep_reverse.
  - pstep. eapply lr_refinesF_existsR. observe_tau. pstep_reverse.
  - punfold e; red in e. pstep; red. simpl.
    remember (observe t1') as ot1'; clear t1' Heqot1'.
    remember (observe (Vis (Spec_forall A) k)) as ot1.
    induction e; inversion Heqot1.
    + subst e. inj_existT. subst k2. eapply lr_refinesF_forallL.
      observe_tau. rewrite (entree_beta ot2). pstep_reverse. apply IHref12.
      pstep. constructor. left. destruct (REL a); [ eassumption | destruct H ].
    + apply lr_refinesF_TauL. apply IHe. assumption.
  - punfold e; red in e. pstep; red. simpl.
    remember (observe t1') as ot1'; clear t1' Heqot1'.
    remember (observe (Vis (Spec_exists A) k)) as ot1.
    induction e; inversion Heqot1.
    + subst e. inj_existT. subst k2. apply lr_refinesF_existsL. intros.
      observe_tau. rewrite (entree_beta ot2). pstep_reverse. eapply H0.
      pstep. constructor. left. destruct (REL a); [ eassumption | destruct H1 ].
    + apply lr_refinesF_TauL. apply IHe. assumption.
  - punfold e; red in e. pstep; red. simpl.
    remember (observe t1') as ot1'; clear t1' Heqot1'. simpl in e.
    remember (VisF (Spec_vis (inl call1)) k1) as ot1.
    induction e; inversion Heqot1.
    + subst e. inj_existT. subst k2. apply lr_refinesF_unfoldL.
      observe_tau. rewrite (entree_beta ot2). pstep_reverse. apply IHref12.
      pstep. constructor. left. eapply eqit_bind; [ reflexivity | ]. intros.
      rewrite H. destruct (REL u2); [ | destruct H0 ]. assumption.
    + apply lr_refinesF_TauL. apply IHe. assumption.
  - pstep. apply lr_refinesF_unfoldR. observe_tau. pstep_reverse.
Qed.

End lr_refines_proper.


(* Refinement is proper wrt eutt *)
Global Instance Proper_eutt_lr_refines {E1 E2 : EvType} {stk1 stk2} {R1 R2}
  funs1 funs2 RPre RPost RR :
  Proper (eutt eq ==> eutt eq ==> flip impl)
    (@lr_refines E1 E2 stk1 stk2 R1 R2 funs1 funs2 RPre RPost RR).
Proof.
  repeat intro. eapply lr_refines_euttL; [ eassumption | ].
  eapply lr_refines_euttR; [ | symmetry ]; eassumption.
Qed.


(*** Reflexivity and Transitivity of refinemenet ***)

(* Reflexivity *)
Lemma lr_refines_refl {E stk R funs1 funs2}
  (RPre : Rel (FunStackE E stk) (FunStackE E stk))
  (RPost : PostRel (FunStackE E stk) (FunStackE E stk))
  (RR : Rel R R) :
  Reflexive RPre -> ReflexivePostRel RPost -> Reflexive RR ->
  forall t, lr_refines funs1 funs2 RPre RPost RR t t.
Proof.
  intros HRPre HRPost HRR. pcofix CIH. intros t. pstep. red.
  destruct t as [ ot ]. destruct ot.
  - apply lr_refinesF_Ret. auto.
  - apply lr_refinesF_Tau. right. pclearbot. eauto.
  - destruct e.
    + apply lr_refinesF_Vis; [ eauto | ]. intros.
      rewrite (HRPost e a b); [ | assumption ]. right. apply CIH.
    + apply lr_refinesF_forallR. intros. eapply lr_refinesF_forallL.
      apply lr_refinesF_Tau. right. apply CIH.
    + apply lr_refinesF_existsL. intros. eapply lr_refinesF_existsR.
      apply lr_refinesF_Tau. right. apply CIH.
Qed.

(* Transitivity *)
Lemma lr_refines_trans {E1 E2 E3} {stk1 stk2 stk3} {R1 R2 R3}
  RPre1 RPre2 RPost1 RPost2
  (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
  (funs1 : StackTuple E1 stk1 stk1) (funs2 : StackTuple E2 stk2 stk2)
  (funs3 : StackTuple E3 stk3 stk3)
  (t1 : SpecM E1 stk1 R1) (t2 : SpecM E2 stk2 R2) (t3 : SpecM E3 stk3 R3) :
  lr_refines funs1 funs2 (liftNilRel RPre1) (liftNilPostRel RPost1) RR1 t1 t2 ->
  lr_refines funs2 funs3 (liftNilRel RPre2) (liftNilPostRel RPost2) RR2 t2 t3 ->
  lr_refines funs1 funs3 (liftNilRel (rcompose RPre1 RPre2))
    (liftNilPostRel (RComposePostRel RPre1 RPre2 RPost1 RPost2))
    (rcompose RR1 RR2) t1 t3.
Proof.
  revert t1 t2 t3; pcofix CIH; intros t1 t2 t3 ref12 ref23.
  pfold. red. punfold ref12. red in ref12. punfold ref23. red in ref23.
  remember (observe t1) as ot1. clear t1 Heqot1.
  remember (observe t2) as ot2. clear t2 Heqot2.
  revert t3 ref23; induction ref12; intros.
  - remember (RetF r2) as x. induction ref23; inversion Heqx.
    + constructor. exists r2; split; [ assumption | ].
      rewrite <- H2. assumption.
    + constructor. apply IHref23. assumption.
    + constructor. intros. apply H1. assumption.
    + econstructor. apply IHref23. assumption.
    + constructor. apply IHref23. assumption.
  - pclearbot.
    assert (lr_refines funs2 funs3 (liftNilRel RPre2) (liftNilPostRel RPost2) RR2 t2 t3) as ref23'.
    { apply lr_refines_TauL_inv. pstep. assumption. }
    clear ref23. punfold ref23'. red in ref23'.
    remember (observe t3) as ot3; clear t3 Heqot3.
    punfold H. red in H.
    remember (observe t2) as ot2. clear t2 Heqot2.
    revert t1 H. induction ref23'; intros.
    + apply lr_refinesF_TauL.
      (* Proof that  t1 |= Ret r1 |= Ret r2  implies Tau t1 |= Ret r2 *)
      remember (observe t1) as ot1; clear t1 Heqot1.
      remember (RetF r1) as ot0. induction H0; try discriminate Heqot0.
      * inversion Heqot0. apply lr_refinesF_Ret. rewrite H2 in H0.
        eexists; split; eassumption.
      * apply lr_refinesF_TauL. apply IHlr_refinesF. assumption.
      * eapply lr_refinesF_forallL. apply IHlr_refinesF. assumption.
      * apply lr_refinesF_existsL. intros. apply H1. assumption.
      * apply lr_refinesF_unfoldL. apply IHlr_refinesF. assumption.
    + apply lr_refinesF_Tau. right. pclearbot. eapply CIH; [ | eassumption ].
      apply lr_refines_TauR_inv. pstep. apply H0.
    + apply lr_refinesF_TauL.
      (* Proof that  t1 |= Vis e2 k2 |= Vis e3 k3  implies t1 |= Vis e3 k3 *)
      remember (observe t1) as ot1; clear t1 Heqot1.
      remember (VisF (Spec_vis e1) k1) as ot0.
      induction H1; try discriminate Heqot0.
      * set (e := injection_VisF_eq Heqot0). inversion e.
        revert k3 Heqot0 H1 H2 e; rewrite H4; intros. clear e3 H4. inj_existT.
        apply lr_refinesF_Vis; [ eapply liftNilRel_compose; eassumption | ].
        intros.
        destruct (liftNilPostRel_compose_elim H1 H H3)
          as [ c [ PR_ac PR_cb ]].
        remember (H2 a c PR_ac) as ref_k0_k3. clear Heqref_k0_k3.
        rewrite <- e in H0.
        remember (H0 c b PR_cb) as ref_k3_k2. clear Heqref_k3_k2.
        pclearbot.
        right. eapply CIH; eassumption.
      * apply lr_refinesF_TauL. apply IHlr_refinesF. assumption.
      * eapply lr_refinesF_forallL. apply IHlr_refinesF. assumption.
      * eapply lr_refinesF_existsL. intros. apply H2. assumption.
      * apply lr_refinesF_unfoldL. apply IHlr_refinesF. assumption.
      * inversion Heqot0. rewrite <- H3 in H. destruct e2; simpl in H; contradiction.
    + apply IHref23'. pstep_reverse. apply lr_refines_TauR_inv.
      pstep. apply H.
    + apply lr_refinesF_Tau. right.
      apply (CIH _ (go _ _ ot1)); pstep; assumption.
    + apply lr_refinesF_forallR. intros. apply H0. assumption.
    + eapply lr_refinesF_existsR. apply IHref23'. assumption.
    + apply IHref23'. observe_tau. pstep_reverse.
      apply lr_refines_forallR_inv. pstep. apply H.
    + assert (existsR_LRRefinesF funs1 funs2
                (liftNilRel RPre1) (liftNilPostRel RPost1) RR1
                k (observe t1))
        as ref_exR;
        [ apply lr_refinesF_existsR_inv; assumption | ].
      clear H1.
      destruct t1 as [ ot1 ]. simpl in ref_exR.
      induction ref_exR.
      * apply (H0 a). assumption.
      * apply lr_refinesF_TauL. eapply lr_refinesF_forallL.
        rewrite <- (entree_eta (k1 b)) in IHref_exR. apply IHref_exR.
      * apply lr_refinesF_TauL. eapply lr_refinesF_existsL. intros.
        rewrite (entree_eta (k1 a)). apply H2.
      * apply lr_refinesF_TauL. simpl. rewrite (entree_eta t1).
        apply IHref_exR.
      * apply lr_refinesF_TauL. apply lr_refinesF_unfoldL.
        rewrite <- entree_eta in IHref_exR. apply IHref_exR.
    + apply IHref23'. observe_tau. pstep_reverse.
      apply lr_refines_callR_inv. pstep. assumption.
    + apply lr_refinesF_unfoldR. apply IHref23'. assumption.
  - (* Vis e1 k1 |= Vis e2 k2 |= t3  implies Vis e1 k1 |= t3 *)
    remember (observe t3) as ot3; clear t3 Heqot3.
    remember (VisF (Spec_vis e2) k2) as ot2.
    induction ref23; try discriminate Heqot2.
    + inversion Heqot2. revert k0 Heqot2 H1 H2; rewrite H4; intros.
      remember (injection_VisF_eq Heqot2) as e. clear Heqe. inj_existT.
      subst k0. apply lr_refinesF_Vis.
      * eapply liftNilRel_compose; eassumption.
      * intros. destruct (liftNilPostRel_compose_elim H H1 H3) as [ c [ Rac Rcb ] ].
        remember (H0 a c Rac) as ref_k1_k2; clear Heqref_k1_k2.
        remember (H2 c b Rcb) as ref_k2_k3; clear Heqref_k2_k3.
        pclearbot.
        right. eapply CIH; eassumption.
    + apply lr_refinesF_TauR. apply IHref23. assumption.
    + apply lr_refinesF_forallR; intros. apply H2. assumption.
    + eapply lr_refinesF_existsR. apply IHref23. assumption.
    + inversion Heqot2. rewrite <- H2 in H.
      destruct e1; destruct H.
    + apply lr_refinesF_unfoldR. apply IHref23. assumption.
  - apply lr_refinesF_TauL. apply IHref12. assumption.
  - apply IHref12. pstep_reverse. apply lr_refines_TauL_inv. pstep. assumption.
  - assert (forallL_LRRefinesF funs2 funs3
              (liftNilRel RPre2) (liftNilPostRel RPost2) RR2 k (observe t3))
      as ref_allL;
      [ apply lr_refinesF_forallL_inv; assumption | ].
    clear ref23. remember (observe t3) as ot3; clear t3 Heqot3.
    induction ref_allL.
    + apply (H0 a (go _ _ t)). apply H1.
    + apply lr_refinesF_forallR; intros. apply lr_refinesF_TauR. apply H2.
    + eapply lr_refinesF_existsR. apply lr_refinesF_TauR. apply IHref_allL.
    + apply lr_refinesF_TauR. apply IHref_allL.
    + apply lr_refinesF_unfoldR. apply lr_refinesF_TauR. apply IHref_allL.
  - apply IHref12. observe_tau.
    pstep_reverse. apply lr_refines_existsL_inv. pstep. apply ref23.
  - eapply lr_refinesF_forallL. apply IHref12. assumption.
  - apply lr_refinesF_existsL. intros. apply H0. assumption.
  - apply lr_refinesF_unfoldL. apply IHref12. assumption.
  - apply IHref12. observe_tau. pstep_reverse.
    apply lr_refines_callL_inv. pstep. assumption.
Qed.


(*** Laws about refinement of bind ***)
Section lr_refines_bind.
Context {E1 E2 : EvType} {stk1 stk2 : FunStack} {R1 R2 : Type} {RR : Rel R1 R2}.
Context {funs1 : StackTuple E1 stk1 stk1} {funs2 : StackTuple E2 stk2 stk2}.

(* Helper lemma to apply entree_beta to the lhs of a bind *)
Lemma observing_BindS E stk A B m (k : A -> SpecM E stk B) :
  BindS m k = BindS (go _ _ (observe m)) k.
Proof.
  reflexivity.
Qed.

Lemma BindS_Ret_l_eq {E stk R S} (r : R) (k : R -> SpecM E stk S) :
  Ret r >>= k = k r.
Proof.
  rewrite (entree_eta (Ret r >>= k)). rewrite (entree_eta (k r)).
  reflexivity.
Qed.

Lemma BindS_Tau_eq {E stk R S} (m : SpecM E stk R) (k : R -> SpecM E stk S) :
  Tau m >>= k = Tau (m >>= k).
Proof.
  rewrite (entree_eta (Tau m >>= k)). rewrite (entree_eta (Tau (m >>= k))).
  reflexivity.
Qed.


Lemma eq_itree_TauR_inv {E stk R} (t1 t2 : SpecM E stk R) :
  eq_itree eq t1 (Tau t2) ->
  exists t1', t1 = Tau t1' /\ eq_itree eq t1' t2.
Proof.
  intro e. punfold e. inversion e; try discriminate.
  exists m1. rewrite (entree_eta t1). rewrite <- H0. pclearbot.
  split; [ reflexivity | assumption ].
Qed.

Lemma BindS_Vis_eq {E:EvType} {stk R S} (e : SpecEvent (FunStackE E stk))
  (k1 : encodes e -> SpecM E stk R) (k2 : R -> SpecM E stk S) :
  Vis e k1 >>= k2 = Vis e (fun x => k1 x >>= k2).
Proof.
  rewrite (entree_eta (Vis e k1 >>= k2)).
  rewrite (entree_eta (Vis e (fun x => k1 x >>= k2))).
  reflexivity.
Qed.

Lemma eq_itree_VisR_inv {E stk R} (t : SpecM E stk R) e k :
  eq_itree eq t (Vis e k) ->
  exists k', t = Vis e k' /\ (forall x, eq_itree eq (k' x) (k x)).
Proof.
  intro H. punfold H.
  destruct t as [ ot ]; destruct ot;
    [ inversion H | inversion H; discriminate | ].
  assert (e0 = e); [ inversion H; reflexivity | ]. subst e0.
  exists k0; split; [ reflexivity | ].
  apply eqit_Vis_inv. pstep. assumption.
Qed.


(* Refinement commutes with bind *)
Lemma lr_refines_bind {RPre RPost S1 S2} {RS : Rel S1 S2} m1 m2 k1 k2 :
  lr_refines funs1 funs2 RPre RPost RS m1 m2 ->
  (forall x1 x2, RS x1 x2 ->
                 lr_refines funs1 funs2 RPre RPost RR (k1 x1) (k2 x2)) ->
  lr_refines funs1 funs2 RPre RPost RR (m1 >>= k1) (m2 >>= k2).
Proof.
  intros mref kref; revert m1 m2 mref.
  assert (forall t1 t2 m1 m2,
             eq_itree eq t1 (m1 >>= k1) -> eq_itree eq t2 (m2 >>= k2) ->
             lr_refines funs1 funs2 RPre RPost RS m1 m2 ->
             lr_refines funs1 funs2 RPre RPost RR t1 t2) as H;
    [ | intros; apply (H (m1 >>= k1) (m2 >>= k2) m1 m2);
        try reflexivity; assumption ].
  pcofix CIH; intros t1 t2 m1 m2 e1 e2 mref.
  punfold mref; red in mref.
  rewrite observing_BindS in e1. rewrite observing_BindS in e2.
  remember (observe m1) as om1. remember (observe m2) as om2.
  clear m1 m2 Heqom1 Heqom2.
  revert t1 t2 e1 e2; induction mref; intros; pclearbot.
  - rewrite BindS_Ret_l_eq in e1. rewrite BindS_Ret_l_eq in e2.
    eapply paco2_mon.
    + eapply lr_refines_euttL; [ apply eq_sub_eutt; apply e1 | ].
      eapply lr_refines_euttR; [ | apply eq_sub_eutt; symmetry; apply e2 ].
      apply kref; assumption.
    + intros. destruct PR.
  - pstep. rewrite BindS_Tau_eq in e1. rewrite BindS_Tau_eq in e2.
    destruct (eq_itree_TauR_inv _ _ e1) as [ t0' [ e_t0 e_t0' ]]; subst t0.
    destruct (eq_itree_TauR_inv _ _ e2) as [ t3' [ e_t3 e_t3' ]]; subst t3.
    apply lr_refinesF_Tau. right. eapply CIH; eassumption.
  - pstep. rewrite BindS_Vis_eq in e0. rewrite BindS_Vis_eq in e3.
    destruct (eq_itree_VisR_inv _ _ _ e0) as [ k1' [ e_k1 e_k1' ]]; subst t1.
    destruct (eq_itree_VisR_inv _ _ _ e3) as [ k2' [ e_k2 e_k2' ]]; subst t2.
    apply lr_refinesF_Vis; [ assumption | ].
    intros. right. eapply CIH; [ apply e_k1' | apply e_k2' | ].
    destruct (H0 a b H1) as [ H2 | []]. assumption.
  - cbn in e1; rewrite bind_Tau_eq in e1.
    destruct (eq_itree_TauR_inv _ _ e1) as [ t0' [ e_t0 e_t0' ]]; subst t0.
    pstep. apply lr_refinesF_TauL. pstep_reverse.
  - cbn in e2; rewrite bind_Tau_eq in e2.
    destruct (eq_itree_TauR_inv _ _ e2) as [ t0' [ e_t0 e_t0' ]]; subst t0.
    pstep. apply lr_refinesF_TauR. pstep_reverse.
  - cbn in e2; rewrite bind_Vis_eq in e2.
    destruct (eq_itree_VisR_inv _ _ _ e2) as [ k2' [ e_k2 e_k2' ]]; subst t2.
    pstep. apply lr_refinesF_forallR. intros.
    observe_tau. pstep_reverse.
    eapply H0; [ eassumption | ].
    transitivity (Tau (BindS (k a) k2));
      [ | rewrite <- BindS_Tau_eq; reflexivity ].
    apply eqit_Tau. apply e_k2'.
  - cbn in e2; rewrite bind_Vis_eq in e2.
    destruct (eq_itree_VisR_inv _ _ _ e2) as [ k2' [ e_k2 e_k2' ]]; subst t2.
    pstep. apply (lr_refinesF_existsR _ _ _ _ _ _ _ _ _ a).
    observe_tau. pstep_reverse. apply IHmref; [ assumption | ].
    transitivity (Tau (BindS (k a) k2));
      [ | rewrite <- BindS_Tau_eq; reflexivity ].
    apply eqit_Tau. apply e_k2'.
  - cbn in e1; rewrite bind_Vis_eq in e1.
    destruct (eq_itree_VisR_inv _ _ _ e1) as [ k1' [ e_k1 e_k1' ]]; subst t1.
    pstep. apply (lr_refinesF_forallL _ _ _ _ _ _ _ _ _ a).
    observe_tau. pstep_reverse. apply IHmref; [ | assumption ].
    transitivity (Tau (BindS (k a) k1));
      [ | rewrite <- BindS_Tau_eq; reflexivity ].
    apply eqit_Tau. apply e_k1'.
  - cbn in e1; rewrite bind_Vis_eq in e1.
    destruct (eq_itree_VisR_inv _ _ _ e1) as [ k1' [ e_k1 e_k1' ]]; subst t1.
    pstep. apply lr_refinesF_existsL. intros.
    observe_tau. pstep_reverse. apply (H0 a); [ | assumption ].
    transitivity (Tau (BindS (k a) k1));
      [ | rewrite <- BindS_Tau_eq; reflexivity ].
    apply eqit_Tau. apply e_k1'.
  - cbn in e1. unfold SpecM, entree_spec in e1. rewrite bind_Vis_eq in e1.
    destruct (eq_itree_VisR_inv _ _ _ e1) as [ k1' [ e_k1 e_k1' ]]; subst t1.
    pstep. apply lr_refinesF_unfoldL. observe_tau. pstep_reverse.
    apply IHmref; [ | assumption ].
    rewrite BindS_Tau_eq. apply eqit_Tau. cbn. rewrite bind_bind.
    eapply eqit_bind; [ reflexivity | ]. intros. subst u2. apply e_k1'.
  - cbn in e2. unfold SpecM, entree_spec in e2. rewrite bind_Vis_eq in e2.
    destruct (eq_itree_VisR_inv _ _ _ e2) as [ k2' [ e_k2 e_k2' ]]; subst t2.
    pstep. apply lr_refinesF_unfoldR. observe_tau. pstep_reverse.
    apply IHmref; [ assumption | ].
    rewrite BindS_Tau_eq. apply eqit_Tau. cbn. rewrite bind_bind.
    eapply eqit_bind; [ reflexivity | ]. intros. subst u2. apply e_k2'.
Qed.


End lr_refines_bind.


(*** LetRec Lemma ***)
Section lr_refines_letrec.
Context {E1 E2 : EvType} {stk1 stk2 : FunStack} {R1 R2 : Type}.
Context (funs1 : StackTuple E1 stk1 stk1) (funs2 : StackTuple E2 stk2 stk2).
Context (RPre : Rel (FunStackE E1 pnil) (FunStackE E2 pnil))
  (RPost : PostRel (FunStackE E1 pnil) (FunStackE E2 pnil))
  (RR : Rel R1 R2).

Lemma lr_refines_letrec t1 t2 :
  lr_refines funs1 funs2 (liftNilRel RPre) (liftNilPostRel RPost) RR t1 t2 ->
  lr_refines (emptyStackTuple E1 _) (emptyStackTuple E2 _) RPre RPost RR
    (LetRecS _ R1 _ funs1 t1) (LetRecS _ R2 _ funs2 t2).
Proof.
  revert t1 t2; pcofix CIH; intros t1 t2 ref12.
  punfold ref12; red in ref12. destruct t1 as [ ot1 ]. destruct t2 as [ ot2 ].
  pstep. red.
  simpl in ref12. induction ref12.
  - apply lr_refinesF_Ret. assumption.
  - apply lr_refinesF_Tau. right. apply CIH. pclearbot. assumption.
  - destruct e1; destruct e2; try destruct H.
    apply lr_refinesF_Vis; [ apply H | ]. right.
    apply CIH. destruct (H0 _ _ H1); [ | destruct H2 ]. apply H2.
  - apply lr_refinesF_TauL. assumption.
  - apply lr_refinesF_TauR. assumption.
  - apply lr_refinesF_forallR; intros; apply H0.
  - eapply lr_refinesF_existsR; apply IHref12.
  - eapply lr_refinesF_forallL; apply IHref12.
  - apply lr_refinesF_existsL; intros; apply H0.
  - apply IHref12.
  - apply IHref12.
Qed.

End lr_refines_letrec.


(*** Discharge and Push lemmas ***)
Section lr_refines_discharge_push.
Context {E1 E2 : EvType} {stk1 stk2 : FunStack} {R1 R2 : Type} {RR : Rel R1 R2}.
Context (funs1 : StackTuple E1 stk1 stk1) (funs2 : StackTuple E2 stk2 stk2).

(* Discharge a local pre/postcondition about calls *)
Lemma lr_refines_discharge RPre RPost precond postcond t1 t2 :
  (forall call1 call2,
      (precond call1 call2 : Prop) ->
      lr_refines funs1 funs2 (addCallPreRel precond RPre)
        (addCallPostRel postcond RPost) (postcond call1 call2)
        (applyStackTuple _ _ funs1 call1)
        (applyStackTuple _ _ funs2 call2)) ->
  lr_refines funs1 funs2 (addCallPreRel precond RPre)
    (addCallPostRel postcond RPost) RR t1 t2 ->
  lr_refines funs1 funs2 (liftNilRel RPre) (liftNilPostRel RPost) RR t1 t2.
Proof.
  intro funsRef. revert t1 t2; pcofix CIH; intros.
  punfold H0. red in H0. pstep. red.
  remember (observe t1) as ot1.
  remember (observe t2) as ot2.
  clear t1 Heqot1 t2 Heqot2.
  hinduction H0 before ot1; intros; pclearbot.
  - apply lr_refinesF_Ret. assumption.
  - apply lr_refinesF_Tau. right. apply CIH. apply H.
  - destruct e1; destruct e2.
    + apply lr_refinesF_unfoldL. apply lr_refinesF_unfoldR.
      apply lr_refinesF_Tau. right. apply CIH.
      apply (lr_refines_bind (RS:=postcond s s0)).
      -- apply funsRef. assumption.
      -- intros. destruct (H0 x1 x2 H1) as [ H3 | [] ].
         assumption.
    + destruct H.
    + destruct H.
    + apply lr_refinesF_Vis; [ apply H | ]. intros.
      right. apply CIH. destruct (H0 a b H1) as [ H2 | [] ].
      assumption.
  - apply lr_refinesF_TauL. assumption.
  - apply lr_refinesF_TauR. assumption.
  - apply lr_refinesF_forallR. intros. apply H0.
  - eapply lr_refinesF_existsR. apply IHlr_refinesF.
  - eapply lr_refinesF_forallL. apply IHlr_refinesF.
  - apply lr_refinesF_existsL. intros. apply H0.
  - apply lr_refinesF_unfoldL. apply IHlr_refinesF.
  - apply lr_refinesF_unfoldR. apply IHlr_refinesF.
Qed.

(* Push a pre/postcondition onto those of a refinement *)
Lemma lr_refines_push_prepost RPre RPost precond postcond t1 t2 :
  lr_refines funs1 funs2 (liftNilRel RPre) (liftNilPostRel RPost) RR t1 t2 ->
  lr_refines funs1 funs2 (addCallPreRel precond RPre)
    (addCallPostRel postcond RPost) RR t1 t2.
Proof.
  revert t1 t2; pcofix CIH; intros.
  punfold H0. red in H0. pstep. red.
  remember (observe t1) as ot1.
  remember (observe t2) as ot2.
  clear t1 Heqot1 t2 Heqot2.
  hinduction H0 before ot1; intros; pclearbot.
  - apply lr_refinesF_Ret. assumption.
  - apply lr_refinesF_Tau. right. apply CIH. assumption.
  - destruct e1 as [ call1 | ]; destruct e2 as [ call2 | ];
      [ destruct H | destruct H | destruct H | ].
    apply lr_refinesF_Vis; [ assumption | ]. intros.
    right. apply CIH. destruct (H0 a b H1) as [ H2 | [] ]. assumption.
  - apply lr_refinesF_TauL. apply IHlr_refinesF.
  - apply lr_refinesF_TauR. apply IHlr_refinesF.
  - apply lr_refinesF_forallR. intros. apply (H0 a).
  - eapply lr_refinesF_existsR. apply IHlr_refinesF.
  - eapply lr_refinesF_forallL. apply IHlr_refinesF.
  - apply lr_refinesF_existsL. intros. apply (H0 a).
  - apply lr_refinesF_unfoldL. apply IHlr_refinesF.
  - apply lr_refinesF_unfoldR. apply IHlr_refinesF.
Qed.

End lr_refines_discharge_push.
