(* begin hide *)
From Coq Require Import
     List.
Import ListNotations.

From stdpp Require Import base gmap fin_maps fin_map_dom ssreflect.
From Vellvm Require Import
     Numeric.Coqlib
     Utilities
     Syntax.

Set Implicit Arguments.
Set Strict Implicit.
(* end hide *)

(** * Working with stdpp, useful tactics:
    - solve_proper
    - solve_map_disjoint
    - set_solver
    - simplify_map_eq
 *)

(* TODO: the lib lemma is weirdly specialized, todo ask/PR stdpp *)
Lemma map_fold_comm_acc
  {K : Type} {M : Type → Type} `{FMap M, ∀ A : Type, Lookup K A (M A), ∀ A : Type, Empty (M A), ∀ A : Type, PartialAlter K A (M A),  OMap M, Merge M, ∀ A : Type, MapFold K A (M A), EqDecision K,
                                   FinMap K M}
  {A B} (f : K → A → B → B) (g : B → B) (x : B) (m : M A) :
  (∀ j1 j2 z1 z2 y, f j1 z1 (f j2 z2 y) = f j2 z2 (f j1 z1 y)) →
  (∀ j z y, f j z (g y) = g (f j z y)) →
  map_fold f (g x) m = g (map_fold f x m).
Proof.
  intros. apply (map_fold_comm_acc_strong _); [solve_proper|solve_proper|done..].
Qed.

(** * Scope theory: relating elementary graph constructions to scope collections *)
Section SCOPE_THEORY.

  Context {T : Set}.

(* Preliminaries: [gset_bk_acc/map_fold_bk_acc] *)

  Lemma fold_bk_acc_empty (f : block_id -> block T -> _):
    fold_bk_acc f ∅ = ∅.
  Proof.
    set_solver.
  Qed.

  Lemma gset_bk_acc_comm : forall f,
    ∀ (i j : block_id) (bk1 bk2 : block T) (ids : gset block_id),
      i ≠ j →
      gset_bk_acc f i bk1 (gset_bk_acc f j bk2 ids) =
      gset_bk_acc f j bk2 (gset_bk_acc f i bk1 ids).
  Proof.
    set_solver.
  Qed.

  Lemma gset_bk_acc_union_acc : forall f (g g' : ocfg T),
      g ##ₘ g' ->
      map_fold (gset_bk_acc f) ∅ (g ∪ g') =
      map_fold (gset_bk_acc f) (map_fold (gset_bk_acc f) ∅ g) g'.
  Proof.
    induction g as [|i bk g ? IH] using (map_ind (M := gmap block_id)).
    - intros * _.
      by rewrite left_id.
    - intros ? DISJ.
      rewrite <- insert_union_l.
      do 2 (rewrite map_fold_insert_L;
            [| intros ; eapply gset_bk_acc_comm; eauto |
              (auto || apply lookup_union_None; by simplify_map_eq)]).
      rewrite IH.
      2: eapply map_disjoint_insert_l; eauto.
      symmetry; apply map_fold_comm_acc.
      intros; set_solver.
      intros; set_solver.
  Qed.

  Lemma fold_bk_acc_union: forall f (g g' : ocfg T),
      g ##ₘ g' ->
      fold_bk_acc f (g ∪ g') =
        fold_bk_acc f g ∪ fold_bk_acc f g'.
  Proof.
    induction g as [|i bk g ? IH] using (map_ind (M := gmap block_id)).
    - intros * _.
      rewrite fold_bk_acc_empty map_empty_union.
      set_solver.
    - intros ? DISJ.
      rewrite <- insert_union_l.
      do 2 (rewrite map_fold_insert_L;
            [| intros; eapply gset_bk_acc_comm; eauto |
              (auto || apply lookup_union_None; by simplify_map_eq)]).
      rewrite IH.
      2: solve_map_disjoint.
      unfold gset_bk_acc; set_solver.
  Qed.

  Lemma fold_bk_acc_singleton : forall f i (bk : block T),
      fold_bk_acc f {[ i := bk]} = f i bk.
  Proof.
    intros.
    rewrite map_fold_singleton.
    set_solver.
  Qed.

  Lemma fold_bk_acc_insert: forall f i bk (g : ocfg T),
      g !! i = None ->
      fold_bk_acc f (<[ i := bk]> g) = f i bk ∪ fold_bk_acc f g.
  Proof.
    intros.
    rewrite insert_union_singleton_l.
    rewrite fold_bk_acc_union.
    by rewrite fold_bk_acc_singleton.
    solve_map_disjoint.
  Qed.

  Lemma elem_of_fold_bk_acc :
    forall f (g : ocfg T) (i : block_id),
      i ∈ fold_bk_acc f g ->
      exists j bk, g !! j = Some bk /\ i ∈ f j bk.
  Proof.
    induction g as [|i bk g ? IH] using (map_ind (M := gmap block_id)).
    - intros * IN; rewrite fold_bk_acc_empty in IN; set_solver.
    - intros j IN.
      rewrite fold_bk_acc_insert in IN; auto.
      apply elem_of_union in IN as [IN | IN].
      + exists i, bk; split; auto.
        by simplify_map_eq.
      + apply IH in IN as (k & bkk & LU & IN).
        do 2 eexists; split; eauto.
        by simplify_map_eq.
  Qed.

(* [inputs] *)
  Lemma inputs_empty :
    @inputs T ∅ = ∅.
  Proof.
    set_solver.
  Qed.

  Lemma inputs_union: forall (l l' : ocfg T),
      @inputs T (l ∪ l') = inputs l ∪ inputs l'.
  Proof.
    set_solver.
  Qed.

  Lemma inputs_singleton: forall i (bk : block T),
      inputs {[ i := bk]} = {[i]}.
  Proof.
    intros.
    unfold inputs.
    set_solver.
  Qed.

  Lemma inputs_insert: forall i bk (g : ocfg T),
      inputs (<[ i := bk]> g) = {[i]} ∪ inputs g.
  Proof.
    set_solver.
  Qed.

  Lemma disjoint_inputs_l (g1 g2 : ocfg T) :
    g1 ##ₘ g2 ->
    forall x, x ∈ inputs g2 ->
         x ∉ inputs g1.
  Proof.
    intros * DISJ x; apply map_disjoint_dom in DISJ.
    set_solver.
  Qed.

  Lemma disjoint_inputs_r (g1 g2 : ocfg T) :
    g1 ##ₘ g2 ->
    forall x, x ∈ inputs g1 ->
         x ∉ inputs g2.
  Proof.
    intros * DISJ x; apply map_disjoint_dom in DISJ.
    set_solver.
  Qed.

  Lemma find_block_in_inputs :
    forall i (g : ocfg T),
      i ∈ inputs g ->
      is_Some (g !! i).
  Proof.
    intros; by apply elem_of_dom.
  Qed.

  Lemma free_out_of_inputs :
    forall i (g : ocfg T),
      i free in g ->
      g !! i = None.
  Proof.
    intros; by apply not_elem_of_dom.
  Qed.

  Lemma free_in_cfg_union:
    forall (g g' : ocfg T) i,
      i free in (g ∪ g') <->
      i free in g /\ i free in g'.
  Proof.
    set_solver.
  Qed.

(* [outputs] *)
  Lemma outputs_empty : outputs (T := T) ∅ = ∅.
  Proof.
    set_solver.
  Qed.

  Lemma outputs_union: forall (g g' : ocfg T),
      g ##ₘ g' ->
      outputs (g ∪ g') = outputs g ∪ outputs g'.
  Proof.
    apply fold_bk_acc_union.
  Qed.

  Lemma outputs_singleton: forall i (bk : block T),
      outputs {[ i := bk]} = successors bk.
  Proof.
    apply fold_bk_acc_singleton.
  Qed.

  Lemma outputs_insert: forall i bk (g : ocfg T),
      g !! i = None ->
      outputs (<[ i := bk]> g) = successors bk ∪ outputs g.
  Proof.
    apply fold_bk_acc_insert.
  Qed.

  Lemma outputs_elem_of' : forall i b (g : ocfg T),
      g !! i = Some b ->
      successors b ⊆ outputs g.
  Proof.
    intros * Lu.
    rewrite <- (insert_delete _ _ _ Lu).
    rewrite outputs_insert.
    2: by simplify_map_eq.
    set_solver.
  Qed.

  Lemma outputs_elem_of : forall i j (b: block T) (g : ocfg T),
      g !! i = Some b ->
      j ∈ successors b ->
      j ∈ outputs g.
  Proof.
    intros * Lu In.
    pose proof outputs_elem_of' _ _ Lu.
    set_solver.
  Qed.

  (* predecessors *)
  Lemma predecessors_empty :
    forall i,
      predecessors (T := T) i ∅ = ∅.
  Proof.
    unfold predecessors; set_solver.
  Qed.

 Lemma predecessors_union :
    forall i (g g' : ocfg T),
      g ##ₘ g' ->
      predecessors i (g ∪ g') = predecessors i g ∪ predecessors i g'.
  Proof.
    intros i; apply fold_bk_acc_union.
  Qed.

  Lemma predecessors_singleton : forall i j (bk : block T),
      predecessors j {[ i := bk]} = predecessors_acc j i bk.
  Proof.
    intros.
    unfold predecessors.
    rewrite map_fold_singleton.
    set_solver.
  Qed.

  Lemma predecessors_insert: forall i j bk (g : ocfg T),
      g !! i = None ->
      predecessors j (<[ i := bk]> g) = predecessors_acc j i bk ∪ predecessors j g.
  Proof.
    intros.
    rewrite insert_union_singleton_l.
    rewrite predecessors_union.
    by rewrite predecessors_singleton.
    solve_map_disjoint.
  Qed.

  Lemma predecessors_elem_of :
    forall (g : ocfg T) (src tgt : block_id) (bk : block T),
      g !! src = Some bk ->
      tgt ∈ successors bk ->
      src ∈ predecessors tgt g.
  Proof.
    intros * Lu In.
    rewrite <- (insert_delete _ _ _ Lu).
    rewrite predecessors_insert.
    2: by simplify_map_eq.
    apply elem_of_union_l.
    unfold predecessors_acc, is_predecessor.
    rewrite decide_True; auto.
    set_solver.
  Qed.

  Lemma elem_of_predecessors :
    forall (g : ocfg T) (src tgt : block_id),
      src ∈ predecessors tgt g ->
      exists bk, g !! src = Some bk /\ is_predecessor tgt bk = true.
  Proof.
    intros * IN.
    apply elem_of_fold_bk_acc in IN as (j & bk & LU & IN).
    unfold predecessors_acc in IN.
    exists bk.
    destruct (is_predecessor tgt bk); [| set_solver].
    apply elem_of_singleton in IN; subst; auto.
  Qed.

  Lemma successor_elem_of :
    forall (G : ocfg T) (src tgt : block_id) (bk : block T),
      src ∈ predecessors tgt G ->
      G !! src = Some bk ->
      tgt ∈ successors bk.
  Proof.
    intros * IN FIND.
    apply elem_of_predecessors in IN as (bk' & LU & ?).
    simplify_map_eq.
    unfold is_predecessor in *.
    case_match; easy.
  Qed.

(* [no_reentrance] *)
  Lemma no_reentrance_not_in (g1 g2 : ocfg T) :
    no_reentrance g1 g2 ->
    forall i, i ∈ outputs g2 ->
         i ∉ inputs g1.
  Proof.
    set_solver.
  Qed.

  Lemma no_reentrance_union_l :
    forall (g1 g1' g2 : ocfg T),
      no_reentrance (g1 ∪ g1') g2 <->
      no_reentrance g1 g2 /\ no_reentrance g1' g2.
  Proof.
    set_solver.
  Qed.

  Lemma no_reentrance_union_r :
    forall (g1 g2 g2' : ocfg T),
      g2 ##ₘ g2' ->
      no_reentrance g1 (g2 ∪ g2') <->
      no_reentrance g1 g2 /\ no_reentrance g1 g2'.
  Proof.
    intros * DISJ; unfold no_reentrance; split; [intros H | intros [H1 H2]].
    - rewrite outputs_union in H; set_solver.
    - rewrite outputs_union; set_solver.
  Qed.

  Lemma independent_flows_no_reentrance_l (g1 g2 : ocfg T):
    independent_flows g1 g2 ->
    no_reentrance g1 g2.
  Proof.
    intros INDEP; apply INDEP; auto.
  Qed.

  Lemma independent_flows_no_reentrance_r (g1 g2 : ocfg T):
    independent_flows g1 g2 ->
    no_reentrance g2 g1.
  Proof.
    intros INDEP; apply INDEP; auto.
  Qed.

  Lemma independent_flows_disjoint (g1 g2 : ocfg T):
    independent_flows g1 g2 ->
    g1 ##ₘ g2.
  Proof.
    intros INDEP; apply INDEP; auto.
  Qed.

End SCOPE_THEORY.

