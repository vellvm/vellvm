Set Implicit Arguments.
Set Contextual Implicit.
Global Generalizable All Variables.
Global Set Automatic Coercions Import.
From Coq Require Export Morphisms RelationClasses List Bool Utf8 Setoid.
Export ListNotations.
From Coq.Program Require Export Basics Syntax.


Notation "t $ r" := (t r)
  (at level 65, right associativity, only parsing).
Notation "($)" := (λ f x, f x) (only parsing).
Notation "($ x )" := (λ f, f x) (only parsing).

Infix "∘" := compose.
Notation "(∘)" := compose (only parsing).
Notation "( f ∘)" := (compose f) (only parsing).
Notation "(∘ f )" := (λ g, compose g f) (only parsing).

(** Ensure that [simpl] unfolds [id], [compose], and [flip] when fully
applied. *)
Arguments id _ _ /.
Arguments compose _ _ _ _ _ _ /.
Arguments flip _ _ _ _ _ _ /.
Arguments const _ _ _ _ /.
Typeclasses Transparent id compose flip const.


(* Setoid Equivalence ------------------------------------------------------- *)

Class Equiv A := equiv: relation A.
Infix "≡" := equiv (at level 70, no associativity).
Notation "(≡)" := equiv (only parsing).
Notation "( X ≡)" := (equiv X) (only parsing).
Notation "(≡ X )" := (λ Y, Y ≡ X) (only parsing). 
Notation "(≢)" := (λ X Y, ¬X ≡ Y) (only parsing). 
Notation "X ≢ Y":= (¬X ≡ Y) (at level 70, no associativity).
Notation "( X ≢)" := (λ Y, X ≢ Y) (only parsing).
Notation "(≢ X )" := (λ Y, Y ≢ X) (only parsing).


Class EquivProps A := {
   EquivPropsEquiv :> Equiv A ;
   EquivPropsEquivalence :> Equivalence (EquivPropsEquiv) ;
}.


(** The type class [LeibnizEquiv] collects setoid equalities that coincide
with Leibniz equality. We provide the tactic [fold_leibniz] to transform such
setoid equalities into Leibniz equalities, and [unfold_leibniz] for the
reverse. *)
Class LeibnizEquiv A `{Equiv A} := leibniz_equiv x y : x ≡ y → x = y.
Lemma leibniz_equiv_iff `{LeibnizEquiv A, !Reflexive (@equiv A _)} (x y : A) :
  x ≡ y ↔ x = y.
Proof. split. apply leibniz_equiv. intros ->; reflexivity. Qed.
 
Ltac fold_leibniz := repeat
  match goal with
  | H : context [ @equiv ?A _ _ _ ] |- _ =>
    setoid_rewrite (leibniz_equiv_iff (A:=A)) in H
  | |- context [ @equiv ?A _ _ _ ] =>
    setoid_rewrite (leibniz_equiv_iff (A:=A))
  end.
Ltac unfold_leibniz := repeat
  match goal with
  | H : context [ @eq ?A _ _ ] |- _ =>
    setoid_rewrite <-(leibniz_equiv_iff (A:=A)) in H
  | |- context [ @eq ?A _ _ ] =>
    setoid_rewrite <-(leibniz_equiv_iff (A:=A))
  end.

(** Equality ------------------------------------------------------------- *)
(** Introduce some Haskell style like notations. *)
Notation "(=)" := eq (only parsing).
Notation "( x =)" := (eq x) (only parsing).
Notation "(= x )" := (λ y, eq y x) (only parsing).
Notation "(≠)" := (λ x y, x ≠ y) (only parsing).
Notation "( x ≠)" := (λ y, x ≠ y) (only parsing).
Notation "(≠ x )" := (λ y, y ≠ x) (only parsing).

Hint Extern 0 (_ = _) => reflexivity.
Hint Extern 100 (_ ≠ _) => discriminate.

Instance: @PreOrder A (=).
Proof. split; repeat intro; congruence. Qed.

Instance equivL {A} : Equiv A := (=).

(** A [Params f n] instance forces the setoid rewriting mechanism not to
rewrite in the first [n] arguments of the function [f]. We will declare such
instances for all operational type classes in this development. *)
Instance: Params (@equiv) 2.

(** The following instance forces [setoid_replace] to use setoid equality
(for types that have an [Equiv] instance) rather than the standard Leibniz
equality. *)
Instance equiv_default_relation `{Equiv A} : DefaultRelation (≡) | 3.
Hint Extern 0 (_ ≡ _) => reflexivity.
Hint Extern 0 (_ ≡ _) => symmetry; assumption.

(** * Type classes *)

(** ** Decidable propositions ---------------------------------------------- *)
(** This type class by (Spitters/van der Weegen, 2011) collects decidable
propositions. For example to declare a parameter expressing decidable equality
on a type [A] we write [`{∀ x y : A, Decidable (x = y)}] and use it by writing
[decide (x = y)]. *)

Class Decidable (P : Prop) := decide : {P} + {¬P}.
Arguments decide _ {_}.
Notation eq_dec A := (∀ x y : A, Decidable (x = y)).
Notation "x == y" := (decide (x = y)) (at level 70, no associativity).

Ltac decide_eq_dec :=
  match goal with
  | [ |- eq_dec ?T ] => intros x y; unfold Decidable; decide equality; decide_eq_dec
  | [ H: eq_dec ?T |- {?X = ?Y} + {?X <> ?Y} ] => apply H
  end.

Instance eq_dec_bool : eq_dec bool.
Proof.
  decide_eq_dec.
Defined.

Instance eq_dec_nat : eq_dec nat.
Proof.
  decide_eq_dec.
Defined.

Instance eq_dec_pair {A B} `(EA:eq_dec A) `(EB:eq_dec B) : eq_dec (A * B)%type.
Proof.
  decide_eq_dec.
Defined.

Instance eq_dec_option {A} `(EA:eq_dec A) : eq_dec (option A).
Proof.
  decide_eq_dec.
Defined.  

Instance eq_dec_list {A} `(EA:eq_dec A) : eq_dec (list A).
Proof.
  decide_eq_dec.
Defined.

(** ** Functors ----------------------------------------------------------------- *)

Class Functor (F:Type -> Type) := fmap : forall {A B}, (A -> B) -> F A -> F B.
Infix "<$>" := fmap (at level 60, right associativity).

Class FunctorLaws (F:Type -> Type) `{Functor F} `{eqiv:forall A, Equiv A}    :=
{
  fmap_id : forall A (a : F A),
    (id <$> a) ≡ a;

  fmap_comp : forall A B C (f:A -> B) (g:B -> C) (a:F A),
      g <$> (f <$> a) ≡ (g ∘ f) <$> a;
}.

Instance option_functor : @Functor option := option_map.
Instance option_functor_eq_laws : (@FunctorLaws option) option_functor  (@eq).
Proof.
  intros. split.
  intros. unfold fmap. unfold option_functor. unfold option_map. destruct a.
  reflexivity. reflexivity.
  intros. unfold fmap. unfold option_functor. destruct a. simpl. reflexivity.
  simpl. reflexivity.
Qed.

Instance list_functor: @Functor list := List.map.
Instance list_functor_eq_laws : (@FunctorLaws list) list_functor (@eq).
Proof.
  split.
  - apply List.map_id.
  - apply List.map_map.
Qed.    

(** ** Monads ------------------------------------------------------------------- *)
Class Monad F `{Functor F} :=
{
  mret : forall {A}, A -> F A ;
  mbind : forall {A B}, F A -> (A -> F B) -> F B ;
}.

Notation "m ≫= f"  := (mbind m f) (at level 60, right associativity).
Notation "( m ≫=)" := (mbind m) (only parsing).
Notation "(≫= f )" := (fun m => mbind m f) (only parsing).
Notation "(≫=)"    := (λ m f, mbind m f) (only parsing).
Notation "x ← y ; z" := (y ≫= (λ x : _, z))
  (at level 65, only parsing, right associativity).
Notation "' ( x1 , x2 ) ← y ; z" :=
  (y ≫= (λ x : _, let ' (x1, x2) := x in z))
  (at level 65, only parsing, right associativity).
Notation "' ( x1 , x2 , x3 ) ← y ; z" :=
  (y ≫= (λ x : _, let ' (x1,x2,x3) := x in z))
  (at level 65, only parsing, right associativity).
Notation "' ( x1 , x2 , x3  , x4 ) ← y ; z" :=
  (y ≫= (λ x : _, let ' (x1,x2,x3,x4) := x in z))
  (at level 65, only parsing, right associativity).
Notation "' ( x1 , x2 , x3  , x4 , x5 ) ← y ; z" :=
  (y ≫= (λ x : _, let ' (x1,x2,x3,x4,x5) := x in z))
  (at level 65, only parsing, right associativity).
Notation "' ( x1 , x2 , x3  , x4 , x5 , x6 ) ← y ; z" :=
  (y ≫= (λ x : _, let ' (x1,x2,x3,x4,x5,x6) := x in z))
  (at level 65, only parsing, right associativity).

Class MonadLaws F `{Monad F} `{FunctorLaws F} :=
{
  mbind_mret  : forall {A} (a: F A), (a ≫= mret) ≡ a;
  mret_mbind  : forall {A B:Type} a (f:A -> F B), (mret a) ≫= f ≡ (f a);
  mbind_assoc : forall {A B C} (a : F A) (f : A -> F B) (g : B -> F C),
      (a ≫= f) ≫= g ≡ a ≫= (fun x => f x ≫= g);
}.

Program Instance option_monad : (@Monad option) option_functor := _.
Next Obligation.
  split.
  - intros A X. exact (Some X).
  - intros A B X X0.  destruct X. apply X0. exact a. exact None.
Defined.    

Program Instance option_monad_eq_laws : (@MonadLaws option) _ _ _ _ _.
Next Obligation.
  destruct a. reflexivity. reflexivity.
Defined.
Next Obligation.
  destruct a; try reflexivity.
Defined.  

Program Instance list_monad : (@Monad list) list_functor := _.
Next Obligation.
  split.
  - intros A X. exact ([X]).
  - intros A B. exact (fun l f => flat_map f l).
Defined.    

Program Instance list_monad_eq_laws : (@MonadLaws list) _ _ _ _ _.
Next Obligation.
  induction a.
  - reflexivity.
  - simpl. rewrite IHa. reflexivity.
Defined.
Next Obligation.
  apply app_nil_r.
Defined.
Next Obligation.
  induction a.
  -  reflexivity.
  -  simpl.
     repeat (rewrite flat_map_concat_map).
     rewrite map_app.
     rewrite concat_app.
     repeat (rewrite <- flat_map_concat_map).
     rewrite IHa. reflexivity.
Defined.

(* Continuations ------------------------------------------------------------ *)

Definition cont (A:Type) := (A -> False) -> False.

Program Instance cont_functor : (@Functor cont).
Next Obligation.
  unfold cont in *. intros.
  apply H. intros. apply X in X0. apply H0. apply X0.
Defined.

Instance cont_functor_laws_eq : (@FunctorLaws cont) cont_functor (@eq).
Proof.
  split.
  - reflexivity.
  - reflexivity.
Defined.

Program Instance cont_monad : (@Monad cont) cont_functor := _.
Next Obligation.
  split.
  - intros. unfold cont. exact (fun (k : A -> False) => k X).
  - intros A B f g.
    unfold cont in *. intros k.
    apply f. intros a. apply g. exact a. exact k.
Defined.

Program Instance cont_monad_eq_laws : (@MonadLaws cont) _ _ _ _ _.


(* Needs functional extensionality to prove the laws ------------------------ *)
Require Import FunctionalExtensionality.
Definition ST (M:Type) (A:Type) := M -> (M * A).
Definition st_map {M A B} (f : A -> B) (s : ST M A) : ST M B :=
  fun (m:M) =>
    let (m', x) := s m in (m', f x).
Definition st_ret {M A} : A -> ST M A := fun (x:A) => fun (m: M) => (m, x).
Definition st_bind {M A B} : (ST M A) -> (A -> ST M B) -> ST M B :=
  fun s => fun f => fun m => let (m', x) := s m in f x m'.            

Instance st_functor {M} : (@Functor (ST M)) := (@st_map M).
Instance st_functor_eq_laws {M} `{Equiv M} : (@FunctorLaws (ST M)) st_functor (@eq).
Proof.
  split.
  - intros A a. unfold fmap. unfold st_functor. unfold st_map.
    unfold ST in a.
    apply functional_extensionality.
    intros.
    destruct (a x). reflexivity.
  - intros A B C f g a.
    unfold fmap. unfold st_functor. unfold st_map.
    apply functional_extensionality.
    intros.
    destruct (a x). reflexivity.
Defined.

Program Instance st_monad : forall A, (@Monad (ST A)) st_functor := _.
Next Obligation.
  split.
  - intros A0 X. unfold ST. auto.
  - intros A0 B X X0. unfold ST in *.
    intros. apply X in X1. destruct X1 as [a b]. apply X0; auto.
Defined.

Program Instance st_monad_eq_laws : forall A, (@MonadLaws (ST A)) st_functor _ _ _ _.
Next Obligation.
  apply functional_extensionality.
  intros x.  destruct (a x). reflexivity.
Defined.
Next Obligation.
  apply functional_extensionality.
  intros x.
  destruct (a x).
  destruct (f a1 a0).
  reflexivity.
Defined.











