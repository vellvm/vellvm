(* begin hide *)
From Paco Require Import paco.
From ITree Require Import
     ITree
     Eq.Eq.
Set Implicit Arguments.
Set Strict Implicit.
(* end hide *)

(** * NoEvent
    We develop in this file a tiny theory to reason about absence of a given event signature
    in a tree, and how to use this absence to safely eliminate this signature from the tree.
 *)

(** * Signature vacuousness
  A simple way to assert the absence of a signature is based on the shape of the signature.
  We define straightforward non-recursive functors and take the cofixed points.
 *)

(* Note : Need to state/prove the monotony of the functors to reason about their paco *)

(* The left part of the signature is absent *)
Variant no_event_lF {E F X} (R: itree (E +' F) X -> Prop): itree (E +' F) X -> Prop :=
| no_event_l_ret: forall (x: X), no_event_lF R (Ret x)
| no_event_l_tau: forall t, R t -> no_event_lF R (Tau t)
| no_event_l_vis: forall {Y} (e: F Y) k, (forall x, R (k x)) -> no_event_lF R (Vis (inr1 e) k).
Definition no_event_l {E F X} := paco1 (@no_event_lF E F X) bot1. 

(* The right part of the signature is absent *)
Variant no_event_rF {E F X} (R: itree (E +' F) X -> Prop): itree (E +' F) X -> Prop :=
| no_event_r_ret: forall (x: X), no_event_rF R (Ret x)
| no_event_r_tau: forall t, R t -> no_event_rF R (Tau t)
| no_event_r_vis: forall {Y} (e: E Y) k, (forall x, R (k x)) -> no_event_rF R (Vis (inl1 e) k).
Definition no_event_r {E F X} := paco1 (@no_event_rF E F X) bot1. 

(* The tree contains no event *)
Variant no_eventF {E X} (R: itree E X -> Prop): itree E X -> Prop :=
| no_event_ret: forall (x: X), no_eventF R (Ret x)
| no_event_tau: forall t, R t -> no_eventF R (Tau t).
Definition no_event {E X} := paco1 (@no_eventF E X) bot1. 

(* Sanity check, trees with empty signature should have no event *)
Lemma no_event_empty {X} : forall (t: itree void1 X), no_event t.
Admitted.

(** * Signature elimination
  In order to eliminate a signature from the type,
  we need to handle it into an itree over the remaining signature.
  Since the intent is to run these handlers over trees that do not
  contain such events, how we handle them should not matter, but
  the obvious solution is to interpret them into [spin]
 *)

Definition helim_l {E F}: E +' F ~> itree F :=
  fun _ e => match e with
          | inl1 _ => ITree.spin
          | inr1 e => trigger e
          end.

Definition helim_r {E F}: E +' F ~> itree E :=
  fun _ e => match e with
          | inr1 _ => ITree.spin
          | inl1 e => trigger e
          end.

Definition helim {E}: E ~> itree void1 :=
  fun _ _ => ITree.spin.

Definition elim_l {E F}: itree (E +' F) ~> itree F     := interp helim_l. 
Definition elim_r {E F}: itree (E +' F) ~> itree E     := interp helim_r. 
Definition elim   {E}  : itree E        ~> itree void1 := interp helim.

(** * Soundness
    The tricky part is now to figure out how to express the correctness of
    the elimination of vacuous signatures.
 *)

(** By asserting that handlers can't be distinguished: *)

Lemma no_event_elim_l :
  forall {E F X} (t : itree (E +' F) X),
    no_event_l t ->
    forall h, elim_l t ≈ interp h t.
Admitted.

Lemma no_event_elim_r :
  forall {E F X} (t : itree (E +' F) X),
    no_event_r t ->
    forall h, elim_r t ≈ interp h t.
Admitted.

Lemma no_event_elim :
  forall {E X} (t : itree E X),
    no_event t ->
    forall h, elim t ≈ interp h t.
Admitted.

(** By expressing that [elim] is an inverse to the signature injection: *)

(* Injection to the left *)
Definition inject_l {E F}: itree F ~> itree (E +' F) :=
  translate inr_.

(* [elim_l] is _always_ a left inverse to [inject_l] *)
Lemma elim_inject_l :
  forall {E F X} (t : itree F X),
    elim_l (@inject_l E F _ t) ≈ t.
Admitted.

(* [inject_l] is a left inverse to [elim_l] when considering trees with [no_event_l] *)
Lemma inject_elim_l :
  forall {E F X} (t : itree (E +' F) X),
    no_event_l t -> 
    inject_l (elim_l t) ≈ t.
Admitted.

(* Injection to the left *)
Definition inject_r {E F}: itree E ~> itree (E +' F) :=
  translate inl_.

(* [elim_r] is _always_ a left inverse to [inject_r] *)
Lemma elim_inject_r :
  forall {E F X} (t : itree E X),
    elim_r (@inject_r E F _ t) ≈ t.
Admitted.

(* [inject_r] is a left inverse to [elim_r] when considering trees with [no_event_r] *)
Lemma inject_elim_r :
  forall {E F X} (t : itree (E +' F) X),
    no_event_r t -> 
    inject_r (elim_r t) ≈ t.
Admitted.

(* Injection *)
Definition inject {E}: itree void1 ~> itree E :=
  translate (fun _ (e : void1 _) => match e with end).

(* [elim] is _always_ a left inverse to [inject] *)
Lemma elim_inject :
  forall {E X} (t : itree void1 X),
    elim (@inject E _ t) ≈ t.
Admitted.

(* [inject] is a left inverse to [elim] when considering trees with [no_event] *)
Lemma inject_elim :
  forall {E X} (t : itree E X),
    no_event t -> 
    inject (elim t) ≈ t.
Admitted.

(** * Establishing [no_event]
    If two tree are similar after non-trivial injections, they have no events.
    The following probably needs to be refined.
 *)

Lemma eutt_disjoint_no_event :
  forall {E F X Y} (R : X -> Y -> Prop) (t : itree E X) (s : itree F Y),
    eutt R (inject_r t) (@inject_l E F _ s) ->
    no_event t /\ no_event s.
Admitted.

(* And while we're at it, injection should not compromise [no_event] *)
Lemma no_event_inject_l :
  forall {E F X} (t : itree F X),
    no_event t ->
    no_event (@inject_l E F _ t).
Admitted.

Lemma no_event_inject_r :
  forall {E F X} (t : itree E X),
    no_event t ->
    no_event (@inject_r E F _ t).
Admitted.


(** * Other discussions  *)

(* We want to express that a tree contains no [pickE] events,
   and that if so that entails that the interpretation by the pick handlers
   leads to the singleton predicate containing the elimination of the pick event.
   Something like:
   no_pick t ->
   forall t', model_pick t t' -> t' ≈ elim_pick t
 *)
