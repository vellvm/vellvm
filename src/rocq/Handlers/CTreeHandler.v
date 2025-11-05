(** * Event handlers *)

(** Events types [E, F : Type -> Type] and itree [E ~> itree F]
    form a category. *)

(* begin hide *)
From Coq Require Import
     Morphisms.

From CTree Require Import
    CTree
    Fold
    Eq
    WBisim.

Import Relation.
Import CategoryOps.
(* end hide *)

(** ** Handler combinators *)

Module Handler.
(** These are defined primarily for documentation. Except for [htrigger],
    it is recommended to use the [CategoryOps] classes instead
    (with the same function names). *)

(** Lift an _event morphism_ into an _event handler_. *)
Definition htrigger {A B} {BR} (m : A ~> B) : A ~> ctree B BR :=
  fun _ e => CTree.trigger (m _ e).

(** Trivial handler, triggering any event it's given, so
    the resulting interpretation is the identity function:
    [interp (id_ E) _ t ≈ t]. *)
Definition id_ (E : Type -> Type) {BR} : E ~> ctree E BR := CTree.trigger.

(** Chain handlers: [g] handles the events produced by [f]. *)
Definition cat {E F G : Type -> Type} {BR}
           (f : E ~> ctree F BR) (g : F ~> ctree G BR)
  : E ~> ctree G BR
  := fun R e => interp g (f R e).

(** Wrap events to the left of a sum. *)
Definition inl_ {E F : Type -> Type} {BR} : E ~> ctree (E +' F) BR
  := htrigger inl1.

(** Wrap events to the right of a sum. *)
Definition inr_ {E F : Type -> Type} {BR}: F ~> ctree (E +' F) BR
  := htrigger inr1.

(** Case analysis on sums of events. *)
Definition case_ {E F G : Type -> Type} {BR}
           (f : E ~> ctree G BR) (g : F ~> ctree G BR)
  : E +' F ~> ctree G BR
  := fun _ ab => match ab with
                 | inl1 a => f _ a
                 | inr1 b => g _ b
                 end.

(* Definition case_' {E F G : Type -> Type}
           (f : E ~> ctree G) (g : F ~> ctree G)
  : E +' F ~> ctree G
  := @case_sum1 E F (ctree G) f g.
(* TODO: why is there a universe inconsistency if this is before [inl_] and [inr_]? *)
 *)

(** Handle events independently, with disjoint sets of output events. *)
Definition bimap {E F G H : Type -> Type} {BR}
           (f : E ~> ctree G BR) (g : F ~> ctree H BR)
  : E +' F ~> ctree (G +' H) BR
  := case_ (Handler.cat f inl_) (Handler.cat g inr_).

(** Handle [void1] events (of which there are none). *)
Definition empty {E : Type -> Type} {BR}
  : void1 ~> ctree E BR
  := fun _ e => match e : void1 _ with end.

End Handler.

(** ** Category instances *)
Definition Handler (E F : Type -> Type) BR := E ~> ctree F BR.

(** Conversion functions between [Handler] and [_ ~> ctree _].
    Although they are the identity function, they guide type inference
    and type class search. *)
Definition handle {E F} {BR} (f : Handler E F BR) : E ~> ctree F BR := f.
Definition handling {E F} {BR} (f : E ~> ctree F BR) : Handler E F BR := f.

Definition eq_Handler {E F : Type -> Type} {BR}
  : Handler E F BR -> Handler E F BR -> Prop
  := i_pointwise (fun R => sbisim eq).

Definition eutt_Handler {E F : Type -> Type} {BR}
  : Handler E F BR -> Handler E F BR -> Prop
  := i_pointwise (fun R => wbisim ).
(** The default handler equivalence is [eutt]. *)
#[global]
Instance Eq2_Handler BR: Eq2 (fun a b => (Handler a b BR))
  := (fun e f => (@eutt_Handler e f BR)).

#[global]
Instance Id_Handler BR: Id_ (fun a b => (Handler a b BR))
  := (fun e => (@Handler.id_ e BR)).

#[global]
Instance Cat_Handler BR: Cat (fun a b => (Handler a b BR))
  := (fun e f g => (@Handler.cat e f g BR)).

#[global]
Instance Case_sum1_Handler BR: Case (fun a b => (Handler a b BR)) sum1
  := (fun e f g => (@Handler.case_ e f g BR)).

#[global]
Instance Inl_sum1_Handler BR: Inl (fun a b => (Handler a b BR)) sum1
  := (fun e f => @Handler.inl_ e f BR).

#[global]
Instance Inr_sum1_Handler BR: Inr (fun a b => (Handler a b BR)) sum1
  := (fun e f => @Handler.inr_ e f BR).

#[global]
Instance Initial_void1_Handler BR: Initial (fun a b => (Handler a b BR)) void1
  := (fun e => @Handler.empty e BR).

(* #[global]
Instance Iter_Handler BR: Iter (fun a b => (Handler a b BR)) sum1
  := @mrec. *)
