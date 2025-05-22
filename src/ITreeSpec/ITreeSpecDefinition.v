From Stdlib Require Import
  Program
  Setoid
  Morphisms
  Relations.

From Paco Require Import paco.

From ITree Require Import
  ITreeMonad
  Basics.Basics
  Basics.Utils
  Basics.HeterogeneousRelations
  Basics.Monad
  Eq
  Eq.Paco2
  Eqit.

From ITree Require Import
  Basics
  ITree
  CategoryOps
  Basics.HeterogeneousRelations.

From ExtLib Require Import
  Structures.Monad
  Structures.Functor.

Polymorphic Variant SpecEvent (E : Type -> Type) : Type -> Type :=
| Spec_vis {X} (e : E X) : SpecEvent E X
| Spec_forall (A : Type) : SpecEvent E A
| Spec_exists (A : Type) : SpecEvent E A.

Arguments Spec_vis {_} {_} _.
Arguments Spec_forall {_} _.
Arguments Spec_exists {_} _.

#[global] Instance SpecEventReSum {E} : (ReSum IFun E (SpecEvent E)).
repeat red.
intros T X.
apply Spec_vis; auto.
Defined.

#[global] Instance SpecEventReSum_trans {E F} (EF : ReSum IFun E F) : (ReSum IFun E (SpecEvent F)).
repeat red.
repeat red in EF.
intros T X.
apply Spec_vis; auto.
Defined.

Definition itree_spec (E : Type -> Type) (R : Type) :=
  itree (SpecEvent E) R.

Import EitherMonad.

Universes u v w.

Definition my_handle_memory_prop' {E : Type@{u} -> Type@{v}} :
  forall T : Type@{w}, itree_spec E T.
Proof using.
  intros T.
  (*
Error:
In environment
E : Type@{u} -> Type@{v}
T : Type@{w}
The term "eitherT T (fun X : Type@{except.u1} => X) T" has type "Type@{except.u2}"
while it is expected to have type "Type@{SpecEvent.u3}" (universe inconsistency: Cannot enforce
except.u2 <= SpecEvent.u3 because SpecEvent.u3 < Functor_itree.u1 <= ITree.map.u2
<= ITreeMonad.Eq1_ITree.u0 <= MonadPlus.MonadPlus.u0 <= except.u2).

   *)
  refine (Vis (@Spec_forall E (eitherT T (fun X => X) T)) (fun (x : (eitherT T (fun X => X) T)) => _)).
Abort.

Notation itree_spec' E R := (itree' (SpecEvent E) R).

  Inductive contains_quantifiers {F R} : itree_spec F R -> Prop :=
  | contains_quant_CrawlTau  : forall t1 t2, t2 ≅ Tau t1 -> contains_quantifiers t1 -> contains_quantifiers t2
  | contains_quant_CrawVis : forall Y (e : F Y) x k t2, t2 ≅ (vis (Spec_vis e) k) ->  contains_quantifiers (k x) -> contains_quantifiers t2
  | contains_quant_Forall : forall A k t2, t2 ≅ (vis (Spec_forall A) k) -> contains_quantifiers t2
  | contains_quant_Exists : forall A k t2, t2 ≅ (vis (Spec_forall A) k) -> contains_quantifiers t2.

  Definition spec_event_to_event_err {F R} (e : SpecEvent F R) : option (F R) :=
    match e with
    | Spec_vis e => Some e
    | Spec_forall A => None
    | Spec_exists A => None
    end.

  Definition spec_event_to_event {F R} (e : SpecEvent F R) (VIS: {e' | e = @Spec_vis F R e'}) : F R.    
    destruct VIS.
    apply x.
  Defined.

  Definition is_spec_vis {F R} (e : SpecEvent F R) : bool :=
    match e with
    | Spec_vis  e => true
    | Spec_forall A => false
    | Spec_exists A => false
    end.

  Variant VisOnlyE F T :=
    | is_vis : {e | @is_spec_vis F T e = true} -> VisOnlyE F T.

  Definition to_SpecEvent {F : Type -> Type} {T : Type} (e : F T) : SpecEvent F T
    := @Spec_vis F T e.

  Definition to_VisOnlyE {F : Type -> Type} {T : Type} (e : F T) : VisOnlyE F T.
    constructor.
    exists (to_SpecEvent e).
    cbn; auto.
  Defined.

  Definition to_itree_spec {F : Type -> Type} {T : Type} (t : itree F T) : itree_spec F T
    := translate (@to_SpecEvent F) t.

  Definition to_itree_VisOnlyE {F : Type -> Type} {T : Type} (t : itree F T) : itree (VisOnlyE F) T
    := translate (@to_VisOnlyE F) t.

#[global] Instance Monad_itree_spec {E} : Monad (itree_spec E).
unfold itree_spec.
constructor.
- intros t X.
  apply (ret X).
- intros t u X X0.
  eapply bind.
  apply X.
  apply X0.
Defined.

#[global] Instance Functor_itree_spec {E} : Functor (itree_spec E).
unfold itree_spec.
constructor.
- intros A B X X0.
  eapply fmap.
  apply X.
  apply X0.
Defined.

#[global] Instance MonadIter_itree_spec {E} : MonadIter (itree_spec E).
unfold itree_spec.
repeat red.
intros R I X X0.
eapply Basics.iter.
apply X.
apply X0.
Defined.

Create HintDb itree_spec.

Section refines.

  Context {E1 E2 : Type -> Type} {R1 R2 : Type}.

  Context (RPre : prerel E1 E2) (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop).

  Inductive refinesF vclo (sim : itree_spec E1 R1 -> itree_spec E2 R2 -> Prop) : itree_spec' E1 R1 -> itree_spec' E2 R2 -> Prop := 
  | refinesF_Ret r1 r2 : RR r1 r2 -> refinesF vclo sim (RetF r1) (RetF r2)
  | refinesF_Tau t1 t2 : sim t1 t2 -> refinesF vclo sim (TauF t1) (TauF t2)

  | refinesF_Vis {X Y} (e1 : E1 X) (e2 : E2 Y) k1 k2 :
    RPre X Y e1 e2 ->
    (forall a b, RPost X Y e1 a e2 b -> vclo sim (k1 a) (k2 b)) ->
    refinesF vclo sim (VisF (Spec_vis e1) k1) (VisF (Spec_vis e2) k2)

  | refinesF_TauL t1 ot2 : refinesF vclo sim (observe t1) ot2 -> refinesF vclo sim (TauF t1) ot2
  | refinesF_TauR ot1 t2 : refinesF vclo sim ot1 (observe t2) -> refinesF vclo sim ot1 (TauF t2)

  | refinesF_forallR A ot1 k : (forall a, refinesF vclo sim ot1 (observe (k a)) ) -> refinesF vclo sim ot1 (VisF (Spec_forall A) k)
  | refinesF_existsR A ot1 k a : refinesF vclo sim ot1 (observe (k a)) -> refinesF vclo sim ot1 (VisF (Spec_exists A) k)
  | refinesF_forallL A ot2 k a : refinesF vclo sim (observe (k a)) ot2 -> refinesF vclo sim (VisF (Spec_forall A) k ) ot2
  | refinesF_existsL A ot2 k : (forall a, refinesF vclo sim (observe (k a)) ot2) -> refinesF vclo sim (VisF (Spec_exists A) k) ot2
  .

  Hint Constructors refinesF : itree_spec.

  Definition refines_ vclo sim : itree_spec E1 R1 -> itree_spec E2 R2 -> Prop :=
    fun t1 t2 => refinesF vclo sim (observe t1) (observe t2).

  Lemma monotone_refinesF ot1 ot2 vclo vclo' sim sim'
    (MON: monotone2 vclo)
    (LEc: vclo <3= vclo')
    (LE : sim <2= sim')
    (IN : refinesF vclo sim ot1 ot2) : refinesF vclo' sim' ot1 ot2.
  Proof with eauto with itree_spec.
    induction IN...
  Qed.

  Lemma monotone_refines_ vclo (MON: monotone2 vclo) : monotone2 (refines_ vclo).
  Proof. red. intros. eapply monotone_refinesF; eauto. Qed.

  Hint Resolve monotone_refines_ : paco.

  Lemma refines_idclo_mono : monotone2 (@id (itree_spec E1 R1 -> itree_spec E2 R2 -> Prop)).
  Proof. unfold id. eauto. Qed.

  Hint Resolve refines_idclo_mono : paco.

  Definition refines := paco2 (refines_ id) bot2.

End refines.

Hint Resolve monotone_refines_ : paco.
Hint Resolve refines_idclo_mono : paco.

Definition forall_spec {E} (A : Type) : itree_spec E A :=
  Vis (Spec_forall A) (fun a => Ret a).
Definition exists_spec {E} (A : Type) : itree_spec E A :=
  Vis (Spec_exists A) (fun a => Ret a).

Definition assume_spec {E} (P : Prop) : itree_spec E unit :=
  ITree.bind (forall_spec P) (fun _ => Ret tt).

Definition assert_spec {E} (P : Prop) : itree_spec E unit :=
  ITree.bind (exists_spec P) (fun _ => Ret tt).

Lemma forall_spec_correctr {E1 E2}
  (A : Type) R1 R2  RPre RPost RR
  (k : A -> itree_spec E2 R1) (t : itree_spec E1 R2) :
  (forall a : A, refines RPre RPost RR t (k a)) ->
  refines RPre RPost RR t (ITree.bind (forall_spec A) k).
Proof.
  intros. pstep. red. cbn. constructor. cbn. intros. simpl.
  pstep_reverse. auto with itree_spec.
  apply H.
Qed.

Lemma forall_spec_correctl {E1 E2}
  (A : Type) R1 R2  RPre RPost RR
  (k : A -> itree_spec E2 R1) (t : itree_spec E1 R2) :
  (exists a : A, refines RPre RPost RR (k a) t) ->
  refines RPre RPost RR (ITree.bind (forall_spec A) k) t.
Proof.
  intros. destruct H as [a Ha]. pstep. red.
  cbn.
  apply refinesF_forallL with (a:=a).
  unfold observe. cbn.
  pstep_reverse.
Qed.

Lemma exists_spec_correctr {E1 E2}
  (A : Type) R1 R2  RPre RPost RR
  (k : A -> itree_spec E2 R1) (t : itree_spec E1 R2) :
  (exists a : A, refines RPre RPost RR t (k a)) ->
  refines RPre RPost RR t (ITree.bind (exists_spec A) k).
Proof.
  intros. destruct H as [a Ha]. pstep. red.
  cbn.
  apply refinesF_existsR with (a:=a).
  simpl.
  pstep_reverse.
Qed.

Lemma exists_spec_correctl {E1 E2}
  (A : Type) R1 R2  RPre RPost RR
  (k : A -> itree_spec E2 R1) (t : itree_spec E1 R2) :
  (forall a : A, refines RPre RPost RR t (k a)) ->
  refines RPre RPost RR t (ITree.bind (forall_spec A) k).
Proof.
  intros. pstep. red. cbn. constructor. cbn. intros. simpl.
  pstep_reverse. auto with itree_spec.
  apply H.
Qed.
