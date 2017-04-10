(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Dmitri Garbuzov <dmitri@sease.upenn.edu>            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)
Require Import Basics.
Require Import List.
Require Import Vellvm.Util.

Definition opt_compose {A B C} (g:B -> C) (f:A -> option B) : A -> option C :=
  fun a => option_map g (f a).

Fixpoint option_iter {A} (f:A -> option A) (a:A) (n:nat) : option A :=
  match n with
  | 0 => Some a
  | S n' => match f a with
            | Some a' => option_iter f a' n'
            | None => None
            end
  end.

Arguments option_map {_ _} _ _.

Lemma option_map_id : forall A (a : option A), option_map id a = a.
Proof.
  unfold option_map; destruct a; auto.
Qed.

Lemma option_map_ext : forall A B (f g:A->B),
  (forall a, f a = g a) ->
  forall oa, option_map f oa = option_map g oa.
Proof.
  intros. destruct oa. simpl. rewrite H; auto. auto.
Qed.

Lemma option_map_some_inv {A B} : forall (o:option A) (f : A -> B) (b:B),
  option_map f o = Some b ->
  exists a, o = Some a /\ f a = b.
Proof.
  destruct o; simpl; intros; inversion H; eauto.
Qed.

Definition option_prop {A} (P: A -> Prop) (a:option A) :=
  match a with
    | None => True
    | Some a' => P a'
  end.

Definition option_bind {A B} (m:option A) (f:A -> option B) : option B :=
  match m with
  | Some a => f a
  | None => None
  end.

Definition option_bind2 {A B C} (m: option (A * B)) (f: A -> B -> option C) : option C :=
  match m with
  | Some (a, b) => f a b
  | None => None
  end.

Module OptionNotations.

  Notation "'do' x <- m ; f" := (option_bind m (fun x => f)) 
    (at level 200, x ident, m at level 100, f at level 200).

  Notation "'do' x , y <- m ; f" := (option_bind2 m (fun x y => f))
    (at level 200, x ident, y ident, m at level 100, f at level 200).

End OptionNotations.

Tactic Notation "not_var" constr(t) :=
  try (is_var t; fail 1 "not_var").

Create HintDb inversions.
Tactic Notation "iauto" := auto 10 with inversions.
Tactic Notation "ieauto" := eauto 10 with inversions.

Definition map_prod {A B C D} (p:A * B) (f:A -> C) (g:B -> D) : (C * D) :=
  (f (fst p), g (snd p)).

Definition flip := @Basics.flip.
Definition comp := @Basics.compose.

Notation "g `o` f" := (Basics.compose g f) 
  (at level 40, left associativity).

Lemma map_prod_distr_comp : forall A B C D E F
  (p:A * B) (f1:A -> C) (f2:B -> D) (g1:C -> E) (g2:D -> F),
  map_prod (map_prod p f1 f2) g1 g2 =
  map_prod p (g1 `o` f1) (g2 `o` f2).
Proof.
  unfold map_prod, Basics.compose. auto.
Qed.

Definition map_snd {A B C} (f:B -> C) : list (A * B) -> list (A * C) :=
  map (fun ab : A * B => let (a, b) := ab in (a, f b)).

Import OptionNotations.

Lemma option_bind_assoc {A B C} : forall (o:option A) (p:A -> option B) (q:B -> option C),
   (do y <- (do x <- o; p x); q y) = (do x <- o; do y <- p x; q y).
Proof.
  intros. destruct o; auto.
Qed.

Lemma option_bind_some_inv {A B} : forall (o:option A) (p:A -> option B) (b:B),
  (do x <- o; p x) = Some b ->
  exists a, o = Some a /\ p a = Some b.
Proof.
  intros. destruct o. eexists. eauto. inversion H.
Qed.

Lemma option_bind_None : forall A B (m : option A),
  (do x <- m; (None(A := B))) = None.
Proof.
  destruct m; auto.
Qed.

Lemma option_bind_some : forall A (m : option A),
  (do x <- m; Some x) = m.
Proof.
  destruct m; auto.
Qed.

Tactic Notation "inv_bind" hyp(H) :=
  repeat rewrite option_bind_assoc in H;
    match type of H with
    | option_bind ?o ?p = Some ?b => 
      let hy := fresh H in
      destruct o eqn:hy; [|discriminate]; simpl in H
    end.

Theorem map_option_map :
  forall A B C (f : B -> option C) (g : A -> B) (l : list A),
    map_option f (map g l) = map_option (fun x => f (g x)) l.
Proof.
  intros. induction l; eauto.
  simpl. rewrite IHl; eauto.
Qed.

