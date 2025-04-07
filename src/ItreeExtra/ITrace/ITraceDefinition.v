From ITree Require Import
     ITree
     ITreeFacts
     Eq.Rutt
     Props.Infinite
.


From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Variant EvAns (E : Type -> Type) : Type -> Type :=
  | evans : forall {A : Type} (ev : E A) (ans : A), EvAns E unit
  (*if you can prove there is no answers, don't need to proved one*)
  | evempty : forall {A : Type} (Hempty : A -> void) (ev : E A), EvAns E void
.

Arguments evans {E}.
Arguments evempty {E}.

Definition itrace (E : Type -> Type) (R : Type) := itree (EvAns E) R.

Definition itrace' (E : Type -> Type) (R : Type) := itree' (EvAns E) R.

Definition ev_stream (E : Type -> Type) := itrace E unit.

Definition Nil {E : Type -> Type} : ev_stream E := Ret tt.

Definition ev_list (E : Type -> Type) := list (EvAns E unit).

Fixpoint ev_list_to_stream {E : Type -> Type} (l : ev_list E) : ev_stream E :=
  match l with
  | nil => Ret tt
  | cons e t => Vis e (fun _ => ev_list_to_stream t) end.

(*one append for traces and streams, get associativity for free from bind_bind*)
Definition append {E R} (s : itrace E unit) (b : itrace E R) :=
  ITree.bind s (fun _ => b).

Notation "s ++ b" := (append s b).

Variant REvRef (E : Type -> Type) : forall (A B : Type), EvAns E A -> E B -> Prop :=
  | rer {A : Type} (e : E A) (a : A) : REvRef E unit A (evans A e a) e
  | ree {A : Type} (e : E A) (Hempty : A -> void) : REvRef E void A (evempty A Hempty e) e
.
#[global] Hint Constructors REvRef : itree.

(*shouldn't need an empty case*)
Variant RAnsRef (E : Type -> Type) : forall (A B : Type), EvAns E A -> A -> E B -> B -> Prop :=
  | rar {A : Type} (e : E A) (a : A) : RAnsRef E unit A (evans A e a) tt e a.
#[global] Hint Constructors RAnsRef : itree.

Definition trace_refine {E R}  (t : itree E R) (b : itrace E R)  :=
   rutt (REvRef E) (RAnsRef E) eq b t.


Notation "b ⊑ t" := (trace_refine t b) (at level 70).

Definition finite {E : Type -> Type} (s : ev_stream E) : Prop := may_converge tt s.

#[global] Instance itrace_eq {E} : Eq1 (itrace E) := ITreeMonad.Eq1_ITree.
