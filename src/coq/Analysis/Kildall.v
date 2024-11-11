(** * Kildall: Forward Dataflow Analysis *)

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** * Acknowledgements *)
(**
  This file is heavily based on:

      - lib/Lattice.v

      - backend/Kildall.v

  from the CompCert development,  modified to remove dependencies and
  optimizations.

*)

From Coq Require Import List Equalities Orders Classes.RelationClasses Program.Equality.

From Vellvm.Analysis Require Import
     Iteration
     Lattice.

From MathClasses Require interfaces.orders interfaces.abstract_algebra orders.lattices.
Import (hints) interfaces.canonical_names interfaces.orders interfaces.abstract_algebra orders.lattices.
(* Print Instances abstract_algebra *)

Module Framework.
  From MathClasses Require Import canonical_names.

  Class Framework `{Ae: Equiv A} (Ale: Le A) `{Meet A} `{Join A} :=
    make   {
        (* The lattice L. *)
        lattice:: orders.LatticeOrder Ale;
        top: A;

        (* A set of transfer functions, indexed by I.  *)
        I: Type;
        fs: I -> A -> A;
        fs_proper:: Proper ((@eq I) ==> canonical_names.equiv ==> canonical_names.equiv) fs;
      }.
End Framework.
Export Framework(Framework).
Export (hints) Framework.

Module Instance.
  From MathClasses Require Import canonical_names.
  Import Framework.

  Class Instance `{Ae: Equiv A} `{Ale: Le A} `{Meet A} `{Join A} (framework: Framework Ale) :=
    make {
        Node: Type;
        root: Node;
        (* Could by any foldable. *)
        successors: Node -> list Node;
        label: Node -> framework.(I);
      }.

  Definition transfer `{instance: Instance} (n: Node): A -> A := Framework.fs (label n).

  Add Parametric Morphism `{instance: Instance} (n: Node): (transfer n)
      with signature canonical_names.equiv ==> canonical_names.equiv as transfer_morphism.
  Proof.
    intros x y x_Eqv_y. (* unfold transfer. rewrite -> x_Eqv_y. *)
    apply framework.(fs_proper).
    - reflexivity.
    - assumption.
  Qed.

End Instance.
Export Instance(Instance).
Export (hints) Instance.
Print Instances Proper.

Module Solver.
  Section Global.
    From stdpp Require base decidable countable gmap.
    Import (notations) base. Import base(dom).

    (* For now, let's assume N (the set of graph nodes) countable.
         We only actually need that the set of reachable Ns is countable.
         A is the analysis domain, aka the framework's lattice.
     *)
    (* BUG: Why is A explicit? Why do we have to resort to this weird named parameter thing?
         https://github.com/coq/coq/issues/10272
     *)
    Context {A: Type} `{instance: (Instance A (framework := framework))} `{Countable_N: countable.Countable Instance.Node}.
    Notation N := (Instance.Node).
    Notation Map := (gmap.gmap N A).

    Notation "x '?!' y" := (match x !! y with | None => ⊤ | Some v => v end)
                             (at level 1).

    Instance top_le: base.Top A := Framework.top (A := A).
    Instance sqsubseteq_le: base.SqSubsetEq A := canonical_names.le (A := A).
    Instance meet_meet: base.Meet A := canonical_names.meet (A := A).

    Class Analysis :=
      make {
          fixpoint: Map -> option Map;
          fixpoint_solution: forall (init result: Map) (n s: N),
            fixpoint init = Some result -> n ∈ dom(init) -> s ∈ (Instance.successors n) -> (result ?! s) ⊑ Instance.transfer n (result ?! n);
          fixpoint_invariant: forall (P: N -> A -> Prop) (init result: Map),
            fixpoint init = Some result ->
            (forall n, P n (init ?! n)) ->
            (forall (p n: N) (pApprox nApprox: A), P p pApprox -> P n nApprox ->
                                              n ∈ (Instance.successors p) ->
                                              P n (nApprox ⊓ (Instance.transfer p pApprox))) ->
            forall (n: N), P n (result ?! n);
        }.

    Section Lemmas.
      Context `{analysis: Analysis} (init result: Map) (Def_result: fixpoint init = Some result).

      Lemma fixpoint_entry: forall (n: N), (result ?! n) ⊑ (init ?! n).
      Proof.
        intros n.
        apply fixpoint_invariant with (init := init); [assumption| |]; clear n.
        - intros n; generalize (init ?! n); clear n. intros l.
          reflexivity.
        - intros p n pApprox nApprox IH_p IH_n Successor_n.
          (* For some reason, apply doesn't work...  *)
          unfold "⊓" in *.
          apply (lattices.meet_le_compat_r _ _ _ IH_n).
      Qed.

    End Lemmas.
  End Global.
End Solver.

Module Kildall.
  From stdpp Require base option countable fin_maps gmap.
  Import (notations, hints) base. Import base(dom).

  Section Global.
    Context {A: Type} `{instance: (Instance A (Ae := Ae) (framework := framework))} `{Countable_N: countable.Countable Instance.Node} `{base.RelDecision _ _ (@canonical_names.equiv A Ae)}.
    Notation N := (Instance.Node).
    Notation Map := (gmap.gmap N A).

    Record State := mkst { in_flow_map: Map; work: list N }.

    (* Instance top_le: base.Top A := Framework.top (A := A). *)
    (* Instance default_A: base.Inhabited A := base.populate (Framework.top (A := A)). *)
    Instance sqsubseteq_le `{canonical_names.Le T}: base.SqSubsetEq T := canonical_names.le (A := T).
    Instance meet_meet `{canonical_names.Meet T}: base.Meet T := canonical_names.meet (A := T).
    Instance equiv `{canonical_names.Equiv T}: base.Equiv T := canonical_names.equiv (A := T).

    Definition lookup (m: Map) (n: N) := option.from_option id Framework.top (m !! n).
    Infix "?!" := lookup (at level 20).
    Notation "'(' x '?!)'" := (fun (y: N) => (x: Map) ?! y) (at level 0).

    Definition andsb (P Q: Prop) `{base.Decision P} `{base.Decision Q}: {P /\ Q} + {~P \/ ~Q}.
      destruct (base.decide P).
      - destruct (base.decide Q).
        + left; split; assumption.
        + right. right. assumption.
      - right. left. assumption.
    Qed.

    Definition orsb (P Q: Prop) `{base.Decision P} `{base.Decision Q}: {P \/ Q} + {~P /\ ~Q}.
      destruct (base.decide P).
      - left. left. assumption.
      - destruct (base.decide Q).
        + left. right. assumption.
        + right. split; assumption.
    Qed.

    Definition negsb (P: Prop) `{base.Decision P}: {~P} + {P}.
      destruct (base.decide P).
      - right. assumption.
      - left. assumption.
    Qed.

    Instance and_dec `{base.Decision P} `{base.Decision Q}: base.Decision (P /\ Q).
    Proof.
      unfold base.Decision.
      destruct (base.decide P).
      - destruct (base.decide Q).
        + left. split; assumption.
        + right. rewrite -> decidable.not_and_l. right. assumption.
      - right. rewrite -> decidable.not_and_l. left. assumption.
    Qed.

    (* Instance or_dec `{base.Decision P} `{base.Decision Q}: base.Decision (P \/ Q). *)
    (* Proof. *)
    (*   unfold base.Decision. *)
    (*   destruct (base.decide P). *)
    (*   - left. left. assumption. *)
    (*   - destruct (base.decide Q). *)
    (*     + left. right. assumption. *)
    (*     + right. rewrite -> decidable.not_and_l.  *)
    (* Qed. *)


    Lemma insert_lookup: forall (m: Map) n v, (<[ n := v ]> m) ?! n = v.
    Proof. intros. unfold lookup,base.insert,fin_maps.map_insert. rewrite -> fin_maps.lookup_partial_alter. reflexivity. Qed.

    Lemma insert_lookup_ne: forall (m: Map) n n' v, n' <> n -> (<[ n' := v ]> m) ?! n = m ?! n.
    Proof. intros. unfold lookup,base.insert,fin_maps.map_insert. rewrite -> fin_maps.lookup_partial_alter_ne by assumption. reflexivity. Qed.

    Definition in_flow (state: State) (n: N): A := state.(in_flow_map) ?! n.
    Definition out_flow (state: State) (n: N): A := Instance.transfer n (in_flow state n).

    Arguments in_flow !state /.
    Arguments out_flow !state /.

    (* Allows using the pointwise lattice on map lookup.
       This means that one can write
            (m ?!) ⊑ (n ?!)
       as a shothand for
            forall x, (m ?! x) ⊑ (n ?! x)
     *)
    Import (hints) Lattices.Pointwise.
    Instance state_lattice: Lattices.Pointwise.Pointwise N A := {}.

    (* Setoid are really useful (who knew?); let's expose their instances. *)
    Local Instance setoid `{orders.PartialOrder T}: abstract_algebra.Setoid T.
    Proof. apply orders.po_setoid. Qed.

    Local Instance meetsemilattice `{orders.MeetSemiLatticeOrder T}: abstract_algebra.MeetSemiLattice T := orders.lattices.meet_sl_order_meet_sl.

    Instance state_equiv: canonical_names.Equiv State := fun s0 s1 => (in_flow s0 ≡ in_flow s1) /\ s0.(work) = s1.(work).

    Instance state_equiv_equiv: Equivalence (@canonical_names.equiv _ state_equiv).
    Proof.
      constructor.
      - intros []. split; reflexivity.
      - intros [] []. split; symmetry; firstorder.
      - intros [] [] [] [] []. split; etransitivity; eassumption.
    Qed.

    Add Morphism in_flow
        with signature (≡) ==> (=) ==> (≡) as in_flow_morph.
    Proof. intros [x ?] [y ?] [x_Equiv_y ?]. apply x_Equiv_y. Qed.

    Add Morphism out_flow
        with signature (≡) ==> (=) ==> (≡) as out_flow_morph.
    Proof.
      intros x y x_Equiv_y n. unfold out_flow.
      apply Instance.transfer_morphism.
      apply in_flow_morph.
      - assumption.
      - reflexivity.
    Qed.

    Section Implementation.
      (* Propagate the output of an update to the node n. *)
      Definition propagate_to (out: A) (s: State) (n: N) : State :=
        let oldl := in_flow s n in
        let newl := oldl ⊓ out in
        if base.decide (oldl ≡ newl /\ n ∈ dom(s.(in_flow_map)))
        then s else mkst (<[ n := newl  ]>s.(in_flow_map)) (n :: s.(work)).

      Definition step (state: State): Map + State :=
        match state.(work) with
        | nil => inl state.(in_flow_map)
        | n :: rem =>
            inr (fold_left (propagate_to (out_flow state n))
                   (Instance.successors n) (mkst state.(in_flow_map) rem))
        end.

      Definition make_init_state (inits: Map): State :=
        mkst inits (base.elements (dom(inits))).

      Definition fixpoint (inits: Map): option Map := Iter.iterate step (make_init_state inits).
    End Implementation.

    Notation "x '~>' y" := (y ∈ (Instance.successors x)) (at level 70, no associativity).
    Notation "x '~/>' y" := (y ∉ (Instance.successors x)) (at level 70, no associativity).

    Instance decide_succ: base.RelDecision (fun x y => x ~> y).
    Proof. intros x y. apply (@list.elem_of_list_dec N _ y (Instance.successors x)). Qed.

    Section Invariants.

      Local Definition InitCondition (init: Map) (state: State): Prop :=
        in_flow state ⊑ (init ?!).

      Local Definition undefined (state: State) (n: N): Prop :=
        n ∈ state.(work) \/ n ∉ dom(state.(in_flow_map)).

      Local Definition SuccCondition (n: N) (state: State): Prop :=
        forall p, p ~> n -> (undefined state p \/ in_flow state n ⊑ out_flow state p).
      Local Tactic Notation "in_work" := left; left.
      Local Tactic Notation "ignored" := left; right.
      Local Tactic Notation "satisfies_equation" := right.

      Local Definition Conditions (init: Map) (state: State): Prop :=
        InitCondition init state /\ forall n, SuccCondition n state.

      Lemma SuccCond_non_pred_weakening: forall n map work w,
          SuccCondition n (mkst map (w :: work)) ->
          w ~/> n ->
          SuccCondition n (mkst map work).
      Proof.
        intros n map work w SuccCond w_NotPred_n.
        intros p p_Pred_n. specialize (SuccCond _ p_Pred_n) as [[Work_p|Ignored_p]|FlowEq_n_w].
        - cbn in Work_p. rewrite -> list.elem_of_cons in Work_p.
          destruct Work_p as [?|?].
          + subst. contradiction.
          + in_work. assumption.
        - ignored. assumption.
        - right.
          unfold out_flow,in_flow in *. cbn in *.
          assumption.
      Qed.

      Lemma SuccCond_strengthening: forall map work w,
          (forall n, SuccCondition n (mkst map (w :: work))) ->
          (forall s, w ~> s -> map ?! s ⊑ Instance.transfer w (map ?! w)) ->
          (forall n, SuccCondition n (mkst map work)).
      Proof.
        intros map work w SuccCond Flow_w.
        intros n. specialize (SuccCond n).
        destruct (base.decide (w ~> n)) as [w_Pred_n | w_NotPred_n].
        - intros p p_Pred_n.
          specialize (SuccCond _ p_Pred_n) as [[Work_p|Ignored_p]|Flow_n_p].
          + cbn in Work_p. rewrite -> list.elem_of_cons in Work_p.
            destruct Work_p as [?|?].
            * subst. satisfies_equation. apply Flow_w. assumption.
            * in_work. assumption.
          + ignored. assumption.
          + satisfies_equation. apply Flow_n_p.
        - apply SuccCond_non_pred_weakening with (1 := SuccCond) (2 := w_NotPred_n).
      Qed.

      Local Ltac destruct_propagation_impl H1 H2 H3 :=
        (lazymatch goal with
         | [|- context[ propagate_to ?out ?state ?w  ] ] =>
             unfold propagate_to;
             destruct (base.decide (in_flow state w ≡ in_flow state w ⊓ out /\ w ∈ dom(in_flow_map state)))
                      as [[H1 H2] | H3%decidable.not_and_l]
         end).
      Tactic Notation "destruct_propagation" :=
        (let H1 := fresh in let H2 := fresh in let H3 := fresh in
          destruct_propagation_impl H1 H2 H3).
      Tactic Notation "destruct_propagation" "as" simple_intropattern(H1) simple_intropattern(H2) simple_intropattern(H3) := (destruct_propagation_impl H1 H2 H3).

      Lemma propagation_smaller: forall out state w,
          (in_flow (propagate_to out state w)) ⊑ (in_flow state).
      Proof.
        intros out state w n.
        destruct_propagation.
        - reflexivity.
        - unfold in_flow, "⊓". cbn.
          destruct (base.decide (w = n)) as [?|?]; subst.
          + rewrite -> insert_lookup.
            apply orders.meet_lb_l.
          + rewrite -> insert_lookup_ne by assumption.
            reflexivity.
      Qed.

      Lemma propagation_equ: forall out state w,
          w ∈ (propagate_to out state w).(work) \/
            in_flow (propagate_to out state w) w ≡ in_flow state w.
      Proof.
        intros out state w.
        destruct_propagation.
        - right. reflexivity.
        - left. apply base.elem_of_list_here.
      Qed.

      Lemma propagation_lookup_eq: forall out state w,
          in_flow (propagate_to out state w) w ≡ in_flow state w ⊓ out.
      Proof.
        intros out state w.
        destruct_propagation.
        - assumption.
        - unfold in_flow. cbn. rewrite -> insert_lookup. reflexivity.
      Qed.

      Lemma propagation_lookup_ne: forall out state w n,
          w <> n -> in_flow (propagate_to out state w) n ≡ in_flow state n.
      Proof.
        intros.
        destruct_propagation.
        - reflexivity.
        - unfold in_flow; cbn. rewrite -> insert_lookup_ne by assumption. reflexivity.
      Qed.

      (* Lemma propagation_ignored: forall out state w, *)
      (*     w ∉ dom(state.(in_flow_map)) -> w ∈ (propagate_to out state w).(work). *)
      (* Proof. *)
      (*   intros. destruct_propagation. - contradiction. - apply base.elem_of_list_here. *)
      (* Qed. *)

      Lemma propagation_work_update: forall out state w,
          state.(work) ⊆ (propagate_to out state w).(work).
      Proof.
        intros out state w n In_state_work.
        destruct_propagation.
        - assumption. - apply base.elem_of_list_further. assumption.
      Qed.

      Lemma propagation_preserves_undefined: forall out state w n,
          undefined state n -> undefined (propagate_to out state w) n.
      Proof.
        intros out state w n [? | ?].
        - left. apply propagation_work_update. assumption.
        - destruct_propagation as ? ? G.
          + right. assumption.
          + destruct (base.decide (n = w)).
            * subst. left. apply base.elem_of_list_here.
            * right. intros Falsum. cbn in Falsum.
              apply fin_map_dom.dom_insert in Falsum.
              rewrite -> base.elem_of_union in Falsum.
              destruct Falsum as [ ?%sets.elem_of_singleton_1 | ? ]; contradiction.
      Qed.

      Lemma propagation_preserves_succ: forall out state w n,
          SuccCondition n state -> SuccCondition n (propagate_to out state w).
      Proof.
        intros out state w n SuccCond p p_Pred_n.
        specialize (SuccCond _ p_Pred_n) as [Undefined_p|Flow_n_w].
        - left. apply (propagation_preserves_undefined _ _ _ _ Undefined_p).
        - unfold out_flow in *.
          destruct (base.decide (w = p)); subst.
          + destruct (propagation_equ out state p) as [? | ->].
            * in_work. assumption.
            * satisfies_equation. rewrite -> (propagation_smaller _ _ _ n). apply Flow_n_w.
          + satisfies_equation.
            rewrite -> (propagation_smaller _ _ _ n).
            rewrite -> (propagation_lookup_ne _ _ w p) by assumption.
            apply Flow_n_w.
      Qed.

      (* Lemma fold_invariant {T U: Type}: forall (f: T -> U -> T) (P: T -> Prop), *)
      (*     (forall a b, P a -> P (f a b)) -> *)
      (*     forall ls a, *)
      (*       P a -> *)
      (*       P (fold_left f ls a). *)
      (* Proof. *)
      (*   intros f P Inv. induction ls as [|h t]. *)
      (*   - intros. assumption. *)
      (*   - intros a P_a. *)
      (*     specialize Inv with (b := h) (1 := P_a). *)
      (*     cbn. revert Inv. generalize (f a h). *)
      (*     apply IHt. *)
      (* Qed. *)

      (* Lemma fold_strenghtening {T U: Type} `{base.EqDecision T}: forall (f: U -> T -> U) (Q: T -> U -> Prop) (P: T -> U -> Prop), *)
      (*     (forall t u, P t u -> Q t u) -> *)
      (*     (forall t u, Q t u -> P t (f u t)) -> *)
      (*     (forall t t' u, t <> t' -> Q t u -> Q t (f u t')) -> *)
      (*     (forall t t' u, P t u -> P t (f u t')) -> *)
      (*     forall (ls: list T) (u: U), *)
      (*       (forall t, t ∈ ls -> Q t u) -> *)
      (*       forall (t: T), t ∈ ls -> P t (fold_left f ls u). *)
      (* Proof. *)
      (*   intros f Q P Strenghtening Intro StepPre StepPost. *)
      (*   induction ls as [| h ls IH]; intros u Base t t_In_ls. *)
      (*   - rewrite -> list.elem_of_nil in t_In_ls. contradiction. *)
      (*   - apply list.elem_of_cons in t_In_ls as [<- | t_In_ls]. *)
      (*     + cbn. *)
      (*       apply fold_invariant. *)
      (*       * intros. apply StepPost. assumption. *)
      (*       * apply Intro. apply Base. apply base.elem_of_list_here. *)
      (*     + cbn. apply IH. *)
      (*       * clear t t_In_ls. *)
      (*         intros t t_In_ls. *)
      (*         destruct (base.decide (t = h)); subst. *)
      (*         -- apply Strenghtening. apply Intro. apply Base. apply base.elem_of_list_here. *)
      (*         -- apply StepPre. *)
      (*            ++ assumption. *)
      (*            ++ apply Base. apply base.elem_of_list_further. assumption. *)
      (*       * assumption. *)
      (* Qed. *)

      Lemma fold_propagation_smaller: forall ls state out,
          (in_flow (fold_left (propagate_to out) ls state)) ⊑ (in_flow state).
      Proof.
        assert (forall ls state state' out,
                   in_flow state' ⊑ in_flow state ->
                   (in_flow (fold_left (propagate_to out) ls state')) ⊑ (in_flow state)) as Ind. {

          induction ls; intros state state' out Smaller.
          - exact Smaller.
          - cbn. apply IHls. rewrite -> propagation_smaller. assumption.
        }
        intros. apply Ind. reflexivity.
      Qed.

      Add Parametric Morphism
        (S T: Type) `{base.Equiv S} `{base.Equiv T} (f: S -> T -> S) `{Proper_f: Proper _  ((≡) ==> (≡) ==> (≡))%signature f}:
        (@fold_left S T f) with signature (≡) ==> (≡) ==> (≡) as list_equiv_morphis.
      Proof.
        intros xs ys xs_Equiv_ys.
        induction xs_Equiv_ys as [| x y xs ys ? ? IH].
        - intros x y x_Equiv_y. cbn. assumption.
        - intros hl hr hl_Equiv_hr.
          cbn. apply IH.
          apply Proper_f; assumption.
      Qed.

      Lemma fold_propagation_lookup_nin: forall ls state out n,
          n ∉ ls -> in_flow (fold_left (propagate_to out) ls state) n ≡ in_flow state n.
      Proof.
        induction ls; intros state out n n_NotIn_ls.
        - reflexivity.
        - rewrite -> list.not_elem_of_cons in n_NotIn_ls. destruct n_NotIn_ls as [n_NotEq_a n_NotIn_ls].
          cbn. rewrite -> IHls by assumption.
          apply propagation_lookup_ne.
          symmetry. assumption.
      Qed.

      Lemma fold_propagation_lookup_in: forall ls state out n,
          n ∈ ls -> in_flow (fold_left (propagate_to out) ls state) n ≡ in_flow state n ⊓ out.
      Proof.
        induction ls; intros state out n n_In_ls.
        - apply list.elem_of_nil in n_In_ls. contradiction.
        - cbn.
          destruct (base.decide (n ∈ ls)).
          + rewrite -> IHls by assumption.
            destruct (base.decide (a = n)); subst.
            * rewrite -> propagation_lookup_eq.
              rewrite <- (canonical_names.associativity).
              rewrite -> (canonical_names.idempotency _ _).
              reflexivity.
            * rewrite -> propagation_lookup_ne by assumption. reflexivity.
          + assert (n = a) as <-. {
              apply list.elem_of_cons in n_In_ls as [? | ?].
              - assumption. - contradiction.
            }
            rewrite -> fold_propagation_lookup_nin by assumption.
            rewrite ->  propagation_lookup_eq.
            reflexivity.
      Qed.


      Lemma fold_propagation_lookup_lower: forall ls state out n,
          in_flow state n ⊓ out ⊑ in_flow (fold_left (propagate_to out) ls state) n.
      Proof.
        intros. destruct (base.decide (n ∈ ls)).
        - rewrite -> fold_propagation_lookup_in by assumption. reflexivity.
        - rewrite -> fold_propagation_lookup_nin by assumption. unfold "⊓". apply orders.meet_lb_l.
      Qed.

      Lemma fold_propagation_lookup_upper: forall ls state out n,
          in_flow (fold_left (propagate_to out) ls state) n ⊑ in_flow state n.
      Proof.
        intros. destruct (base.decide (n ∈ ls)).
        - rewrite -> fold_propagation_lookup_in by assumption. unfold "⊓". apply orders.meet_lb_l.
        - rewrite -> fold_propagation_lookup_nin by assumption. reflexivity.
      Qed.

      Lemma fold_propagation: forall ls out state,
            Forall (fun n => in_flow (fold_left (propagate_to out) ls state) n ⊑ out) ls.
      Proof.
        induction ls as [| h t IH]; intros out state; cbn.
        - constructor.
        - specialize (IH out (propagate_to out state h)).
          constructor; [|apply IH].
          rewrite -> (fold_propagation_smaller _ _ _ h). rewrite -> propagation_lookup_eq. unfold "⊓". apply orders.meet_lb_r.
      Qed.

      Lemma fold_propagation': forall ls out state n,
          n ∈ ls -> in_flow (fold_left (propagate_to out) ls state) n ⊑ out.
      Proof.
        intros ls out state n n_In_ls.
        pose proof (fold_propagation ls out state) as G.
        rewrite -> Forall_forall in G. apply G.
        rewrite <- base.elem_of_list_In. apply n_In_ls.
      Qed.

      Lemma fold_propagation_work_lower: forall ls out state,
          state.(work) ⊆ (fold_left (propagate_to out) ls state).(work).
      Proof.
        induction ls; intros.
        - reflexivity.
        - cbn. rewrite <- IHls. apply propagation_work_update.
      Qed.

      Lemma fold_propagation_equ: forall ls out state n,
          let result := fold_left (propagate_to out) ls state in
          n ∈ result.(work) \/ in_flow state n ≡ in_flow result n.
      Proof.
        induction ls as [| h t IH]; intros out state n result.
        - right. reflexivity.
        - cbn in result; subst result.
          specialize IH with (out := out) (state := (propagate_to out state h)) (n := n) as [? | <-].
          + left. assumption.
          + destruct (base.decide (h = n)).
            * subst.
              pose proof (propagation_equ out state n) as [? | <-].
              -- subst. left. apply fold_propagation_work_lower. assumption.
              -- right. reflexivity.
            * right. symmetry. apply propagation_lookup_ne. assumption.
      Qed.

      Lemma fold_propagation_equ': forall ls out state n,
          let result := fold_left (propagate_to out) ls state in
          in_flow state n ≢ in_flow result n -> n ∈ result.(work).
      Proof. intros. destruct (fold_propagation_equ ls out state n). - assumption. - contradiction. Qed.

      Lemma fold_propagation_preserves_undefined: forall ls out state n,
          undefined state n -> undefined (fold_left (propagate_to out) ls state) n.
      Proof.
        induction ls as [| h t IH]; intros out state n Undef_n.
        - assumption.
        - cbn. apply IH. apply propagation_preserves_undefined. assumption.
      Qed.

      Lemma undefined_strenghtening: forall flow w work n,
          n <> w -> undefined (mkst flow (w :: work)) n -> undefined (mkst flow work) n.
      Proof.
        intros flow w work n n_NotEq_w [Work_n | Ignored_n].
        - apply list.elem_of_cons in Work_n as [? | ?]; [contradiction|]. left. assumption.
        - right. assumption.
      Qed.

      Lemma step_loop_preserves_succ: forall  state result,
          step state = inr result ->
          (forall n, SuccCondition n state) ->
          forall n, SuccCondition n result.
      Proof.
        intros [flow work] result Def_result SuccCond n p p_Pred_n.
        specialize (SuccCond _ _ p_Pred_n).
        unfold step in Def_result.
        destruct work as [?|w work];  [discriminate|injection Def_result as Def_result].
        destruct (base.decide (p = w)) as [? | p_NEq_w]. {
          subst.
          rewrite -> (fold_propagation_lookup_in) by assumption.
          unfold out_flow.
          destruct (fold_propagation_equ (Instance.successors w) (Instance.transfer w (flow ?! w)) (mkst flow work) w).
          - in_work. assumption.
          - satisfies_equation. rewrite <- H2. unfold "⊓". apply orders.meet_lb_r.
        }
        destruct (base.decide (in_flow (mkst flow work) p ≡ in_flow result p)) as [Unchg_p | ?]; subst.
        - destruct SuccCond as [? | ?].
          + left.
            apply fold_propagation_preserves_undefined.
            apply undefined_strenghtening with (1 := p_NEq_w).
            assumption.
          + satisfies_equation.
            unfold out_flow. rewrite <- Unchg_p.
            rewrite -> (fold_propagation_lookup_upper).
            assumption.
        - in_work. apply fold_propagation_equ'. assumption.
      Qed.

      Lemma step_loop_smaller: forall state result,
          step state = inr result ->
          in_flow result ⊑ in_flow state.
      Proof.
        intros [flow work] result Def_result.
        unfold step in Def_result.
        destruct work; cbn in Def_result.
        - discriminate.
        - injection Def_result as <-.
          cbn.
          apply fold_propagation_smaller.
      Qed.

      Lemma init_invariants: forall init,
          Conditions init (make_init_state init).
      Proof.
        unfold Conditions, InitCondition, SuccCondition.
        split.
        - reflexivity.
        - intros n p p_Pred_n.
          left; unfold undefined; cbn.
          destruct (base.decide (p ∈ dom(init))).
          + left. rewrite -> base.elem_of_elements. assumption.
          + right. assumption.
      Qed.

      Lemma fixpoint_invariants: forall init result,
          fixpoint init = Some result ->
          Conditions init (mkst result []).
      Proof.
        intros.
        apply Iter.iter_prop with (P := (fun s => InitCondition init s /\ forall n, SuccCondition n s)) (3 := H2).
        - intros s Conditions_s.
          destruct (step s) eqn:Eq.
          + destruct s as [flow work].
            unfold step in Eq. destruct work; [|discriminate].
            injection Eq as <-.
            apply Conditions_s.
          + split.
            * unfold InitCondition. rewrite ->  step_loop_smaller with (1 := Eq). apply Conditions_s.
            * apply step_loop_preserves_succ with (1 := Eq). destruct Conditions_s as [_ ?]. assumption.
        - apply init_invariants.
      Qed.

      Lemma fixpoint_solution: forall (init result: Map) (p s: N),
          fixpoint init = Some result ->
          p ∈ dom(init) ->
          s ∈ (Instance.successors p) ->
          (result ?! s) ⊑ Instance.transfer p (result ?! p).
      Proof.
        intros init result p s Def_result p_In_init p_Pred_s.
        pose proof (fixpoint_invariants init result Def_result) as [InitCond SuccCond].
        specialize (SuccCond _ _ p_Pred_s) as [[Work_p | Ignored_p] | Equ_p_s].
        - rewrite -> list.elem_of_nil in Work_p. contradiction.
        - admit.
        - apply Equ_p_s.
      Qed.

        (*

          fixpoint_solution: forall (init result: Map) (n s: N),
            fixpoint init = Some result -> n ∈ dom(init) -> s ∈ (Instance.successors n) -> (result ?! s) ⊑ Instance.transfer n (result ?! n);
          fixpoint_invariant: forall (P: N -> A -> Prop) (init result: Map),
            fixpoint init = Some result ->
            (forall n, P n (init ?! n)) ->
            (forall (p n: N) (pApprox nApprox: A), P p pApprox -> P n nApprox ->
                                              n ∈ (Instance.successors p) ->
                                              P n (nApprox ⊓ (Instance.transfer p pApprox))) ->
            forall (n: N), P n (result ?! n);
         *)

    End Invariants.

  Definition n_invar (s:state) (n:N.t) : Prop :=
    In n s.(wlist) \/ forall m, In m (succs n) ->
      s.(lmap)!!m <= trans n s.(lmap)!!n.

  Definition state_invar (s:state) : Prop :=
    forall n, NM.In n inits -> n_invar s n.

  Lemma prop_n_invar_pres : forall o s n n',
    n_invar s n -> n_invar (prop_succ o s n') n.
  Proof.
    unfold n_invar. intros.
    set (s' := prop_succ o s n'); unfold prop_succ in s'.
    destruct (L.eq_dec _ _); [solve [apply H]|].
    destruct H; [solve [simpl; intuition]|].
    destruct (N.eq_dec n n'); [solve [simpl; intuition]|].
    right. intros.
    destruct (N.eq_dec n' m); subst s'; simpl.
    - subst.
      rewrite
        -> (find_default_eq _ _ m),
        -> (find_default_neq _ _ m n) by auto.
      transitivity (lmap s)!!m.
      + apply LFacts.le_meet_l.
      + apply H. assumption.
    - rewrite find_default_neq, find_default_neq; auto.
  Qed.

  (* TO MOVE *)
  Lemma fold_left_1 : forall {A B: Type} (P:A -> Prop) (f:A -> B -> A) (bs : list B)
                         (Hpres : forall a b, In b bs -> P a -> P (f a b)),
      forall a a',
        a' = fold_left f bs a -> P a -> P a'.
  Proof.
    intros. subst a'. generalize dependent a.
    induction bs; simpl; intros. assumption.
    apply IHbs. intros. apply Hpres. right; auto. assumption.
    apply Hpres. left; auto. assumption.
  Qed.

  (* TO MOVE *)
  Lemma fold_left_2 : forall {A B: Type} (P:A -> B -> Prop)
                        (f:A -> B -> A)
                        (Hpres : forall a b b', P a b -> P (f a b') b)
                        (Hintr : forall a b, P (f a b) b),
      forall a a' bs b,
        a' = fold_left f bs a ->
        In b bs -> P a' b.
  Proof.
    intros. subst a'. generalize dependent a.
    induction bs as [|b']. contradiction.
    simpl; intros. destruct H0. subst b'.
    set (a' := fold_left _ _ _). pattern a'.
    eapply fold_left_1; eauto.
    subst; reflexivity.
    apply IHbs; assumption.
  Qed.

  Lemma prop_n_out : forall o ns s s' n,
    s' = fold_left (prop_succ o) ns s ->
    ~ In n (wlist s') ->
    trans n (lmap s')!!n == trans n (lmap s)!!n.
  Proof.
    intros o ns s s' n Heqs'. pattern s'.
    eapply fold_left_1; eauto.
    intros. set (r := prop_succ o a b) in *.
    unfold prop_succ in r. destruct (L.eq_dec _ _). apply H0; auto.
    destruct (N.eq_dec b n). contradict H1; simpl; auto.
      subst r. simpl in *. rewrite find_default_neq; auto.
   intro. reflexivity.
  Qed.

  Lemma step_state_invar : forall s s',
    state_invar s -> inr s' = step s -> state_invar s'.
  Proof.
    unfold step, state_invar; intros s s' Hinv Hstep.
    destruct (wlist s) eqn:Hwls. discriminate Hstep.
    injection Hstep; clear Hstep. intros Heqs' n.

    destruct (N.eq_dec t n).

    (* n_invar is restablished for n *)
    - subst t. unfold n_invar.
      destruct(in_dec N.eq_dec n (wlist s')) as [|Hwl]; [auto | right].
      intros m Hin. rewrite prop_n_out; eauto; simpl.
      generalize Hwl; clear Hwl. pattern s', m.

      eapply fold_left_2; eauto.
      + intros a b b'.
        set (r := prop_succ _ a b').
        intros. unfold prop_succ in r. destruct (L.eq_dec _ _). apply H0; auto.
        unfold r. simpl. destruct (N.eq_dec b' b).
        * rewrite find_default_eq; auto. apply LFacts.le_meet_r.
        * rewrite find_default_neq; auto. apply H0. contradict Hwl; simpl; auto.

      + intros a b.
        set (r := prop_succ _ a b).
        intros. unfold prop_succ in r. destruct (L.eq_dec _ _) as [Heq|].
        * subst r. rewrite Heq. apply LFacts.le_meet_r.
        * simpl. rewrite find_default_eq; auto. apply LFacts.le_meet_r.
    - (* n_invar is preserved for all successors ~= n *)
      intros Hin. pattern s'. eapply fold_left_1; eauto.
      intros. apply prop_n_invar_pres. assumption.
      unfold state_invar, n_invar in Hinv |- *.
      simpl. specialize (Hinv n). rewrite Hwls in Hinv. destruct Hinv.
      assumption. left. destruct H; intuition. right. apply H.
  Qed.

  Lemma fixpoint_solution: forall res n s,
    fixpoint = Some res ->
    NM.In n inits ->
    In s (succs n) ->
    res!!s <= trans n res!!n.
  Proof.
    unfold fixpoint; intros. pattern res.
    eapply Iter.iter_prop with
      (step:=step) (P:=state_invar) (a:=make_init_state); eauto.
    - intros a Ha.
    unfold step. destruct (wlist a) eqn:Heql.
      + specialize (Ha n). destruct Ha.
        * auto.
        * rewrite Heql in *. contradiction.
        * auto.
      + eapply step_state_invar. apply Ha.
        unfold step. rewrite Heql. auto.
    - left. simpl. apply in_map_iff.
      pose proof (NMFacts.elements_in_iff inits n0) as [He _].
      specialize (He H2). destruct He as [e Hine].
      apply InA_alt in Hine as [y [Heq Hk]].
      inversion Heq; eauto.
  Qed.

  (* monotonicity *)

  Definition le_nlmap (nl1 nl2: nlmap) : Prop :=
    forall n, nl1!!n <= nl2!!n.

  Lemma le_nlmap_refl : forall nl, le_nlmap nl nl.
  Proof.
    unfold le_nlmap. reflexivity.
  Qed.

  Instance le_nlmap_trans : Transitive le_nlmap.
    unfold Transitive, le_nlmap; intros. transitivity y !! n; auto.
  Qed.

  Hint Resolve LFacts.le_meet_l LFacts.le_meet_r : core .
    (* L.eq_equiv L.le_preorder L.le_poset L.eq_le_reflexive. *)
    (* Saw this in Relation_Definitions but it doesn't appear to work? *)

  Lemma prop_succ_le_nlmap: forall st out n,
    le_nlmap (prop_succ out st n).(lmap) st.(lmap).
  Proof.
    unfold le_nlmap, prop_succ; intros.
    destruct (L.eq_dec _ _). reflexivity.
    simpl. destruct (N.eq_dec n n0).
      subst. rewrite find_default_eq; auto.
      rewrite find_default_neq; auto. reflexivity.
  Qed.

  Lemma step_le_nlmap: forall st st',
    inr st' = step st ->
    le_nlmap st'.(lmap) st.(lmap).
  Proof.
    unfold step; intros. destruct (wlist st).
    discriminate. injection H. intro Heqs.
    pattern st'. eapply fold_left_1.
    intros. transitivity (lmap a).
       apply prop_succ_le_nlmap. assumption.
    apply Heqs. apply le_nlmap_refl.
  Qed.

  Lemma fixpoint_entry : forall res n,
    fixpoint = Some res -> res!!n <= inits!!n.
  Proof.
    unfold fixpoint. intros. pattern res.
    eapply Iter.iter_prop with (step:=step).
    - intros.
      destruct (step a) eqn:Hstep.
      + unfold step in Hstep. destruct (wlist a); try discriminate.
        injection Hstep. intro; subst t. apply H0.
      + simpl in *. transitivity (lmap a)!!n; [|assumption].
        apply step_le_nlmap. auto.
    - change inits with (lmap make_init_state).
      cbv beta. reflexivity.
    - apply H.
  Qed.

  Lemma fixpoint_invariant : forall
    (P: N.t -> L.t -> Prop)
    (Pinits: forall n, P n inits!!n)
    (Ptrans: forall n ln s ls,
      In s (succs n) ->
      P n ln -> P s ls -> P s (L.meet ls (trans n ln))),
    forall res n, fixpoint = Some res -> P n res!!n.
  Proof.
    intros until 2.
    unfold fixpoint. intros. pattern res.
    eapply Iter.iter_prop with (step:=step); eauto.

    intro. destruct (step a) eqn:Hstep.

    (* last step  Q implies P *)
    unfold step in Hstep. destruct (wlist a); try discriminate.
    instantiate (1:=fun s => forall n, P n s.(lmap)!!n).
    injection Hstep. intro; subst t. intros; auto.

    (* P preserved across step *)
    simpl. intros. unfold step in Hstep.
    destruct (wlist a); try discriminate.
    injection Hstep; clear Hstep; intro Heqs.

    pattern s. eapply fold_left_1 with (f:=prop_succ _); eauto.
    intros. unfold prop_succ.
    destruct (L.eq_dec _ _); simpl; auto.
    destruct (N.eq_dec b n0).
    rewrite find_default_eq; auto.
      subst b. apply Ptrans; auto.
    rewrite find_default_neq; auto.
    auto.
  Qed.


    #[refine]
    Instance solver : Solver.Analysis := {

      }.



  End Global.
End Kildall.

Module ForwardSolver (PC:UsualDecidableType) (LAT: Lattice.SemiLattice) <:
                     FORWARD_SOLVER with Module L := LAT
                                    with Module N := PC.

  Module L := LAT.
  Module N := PC.
  Module LFacts := Lattice.SemiLatticeFacts L.
  Import (notations) L.


  (* TODO: can define a total order for PCs to use more efficient sets/maps *)
  Module NM := FMapWeakList.Make N.
  Module Import FMP := FMapProps N NM.
  Module NMFacts := FMapFacts.WFacts NM.

  Import (notations) L.
  Notation "a !! b" := (find_default _ a b L.top) (at level 1, format "a !! b").
  Notation nlmap := (NM.t L.t).

  Record state := mkst { lmap: NM.t L.t; wlist: list N.t }.

  Section KILDALL.

  Variable succs : N.t -> list N.t.
  Variable trans : N.t -> L.t -> L.t.
  Variable inits : nlmap.

  Definition prop_succ (out:L.t) (s:state) (n:N.t) : state :=
    let oldl := s.(lmap)!!n in
    let newl := L.meet oldl out in
    if L.eq_dec oldl newl
    then s else mkst (NM.add n newl s.(lmap)) (n::s.(wlist)).

  Definition step (s:state) : NM.t L.t + state :=
    match s.(wlist) with
      | nil => inl s.(lmap)
      | n::rem =>
        inr (fold_left (prop_succ (trans n s.(lmap)!!n))
                       (succs n) (mkst s.(lmap) rem))
    end.

  Definition make_init_state : state :=
    mkst inits (map (@fst _ _) (NM.elements inits)).

  Definition fixpoint := Iter.iterate step make_init_state.


  (* correctness *)

  Definition n_invar (s:state) (n:N.t) : Prop :=
    In n s.(wlist) \/ forall m, In m (succs n) ->
      s.(lmap)!!m <= trans n s.(lmap)!!n.

  Definition state_invar (s:state) : Prop :=
    forall n, NM.In n inits -> n_invar s n.

  Lemma prop_n_invar_pres : forall o s n n',
    n_invar s n -> n_invar (prop_succ o s n') n.
  Proof.
    unfold n_invar. intros.
    set (s' := prop_succ o s n'); unfold prop_succ in s'.
    destruct (L.eq_dec _ _); [solve [apply H]|].
    destruct H; [solve [simpl; intuition]|].
    destruct (N.eq_dec n n'); [solve [simpl; intuition]|].
    right. intros.
    destruct (N.eq_dec n' m); subst s'; simpl.
    - subst.
      rewrite
        -> (find_default_eq _ _ m),
        -> (find_default_neq _ _ m n) by auto.
      transitivity (lmap s)!!m.
      + apply LFacts.le_meet_l.
      + apply H. assumption.
    - rewrite find_default_neq, find_default_neq; auto.
  Qed.

  (* TO MOVE *)
  Lemma fold_left_1 : forall {A B: Type} (P:A -> Prop) (f:A -> B -> A) (bs : list B)
                         (Hpres : forall a b, In b bs -> P a -> P (f a b)),
      forall a a',
        a' = fold_left f bs a -> P a -> P a'.
  Proof.
    intros. subst a'. generalize dependent a.
    induction bs; simpl; intros. assumption.
    apply IHbs. intros. apply Hpres. right; auto. assumption.
    apply Hpres. left; auto. assumption.
  Qed.

  (* TO MOVE *)
  Lemma fold_left_2 : forall {A B: Type} (P:A -> B -> Prop)
                        (f:A -> B -> A)
                        (Hpres : forall a b b', P a b -> P (f a b') b)
                        (Hintr : forall a b, P (f a b) b),
      forall a a' bs b,
        a' = fold_left f bs a ->
        In b bs -> P a' b.
  Proof.
    intros. subst a'. generalize dependent a.
    induction bs as [|b']. contradiction.
    simpl; intros. destruct H0. subst b'.
    set (a' := fold_left _ _ _). pattern a'.
    eapply fold_left_1; eauto.
    subst; reflexivity.
    apply IHbs; assumption.
  Qed.

  Lemma prop_n_out : forall o ns s s' n,
    s' = fold_left (prop_succ o) ns s ->
    ~ In n (wlist s') ->
    trans n (lmap s')!!n == trans n (lmap s)!!n.
  Proof.
    intros o ns s s' n Heqs'. pattern s'.
    eapply fold_left_1; eauto.
    intros. set (r := prop_succ o a b) in *.
    unfold prop_succ in r. destruct (L.eq_dec _ _). apply H0; auto.
    destruct (N.eq_dec b n). contradict H1; simpl; auto.
      subst r. simpl in *. rewrite find_default_neq; auto.
   intro. reflexivity.
  Qed.

  Lemma step_state_invar : forall s s',
    state_invar s -> inr s' = step s -> state_invar s'.
  Proof.
    unfold step, state_invar; intros s s' Hinv Hstep.
    destruct (wlist s) eqn:Hwls. discriminate Hstep.
    injection Hstep; clear Hstep. intros Heqs' n.

    destruct (N.eq_dec t n).

    (* n_invar is restablished for n *)
    - subst t. unfold n_invar.
      destruct(in_dec N.eq_dec n (wlist s')) as [|Hwl]; [auto | right].
      intros m Hin. rewrite prop_n_out; eauto; simpl.
      generalize Hwl; clear Hwl. pattern s', m.

      eapply fold_left_2; eauto.
      + intros a b b'.
        set (r := prop_succ _ a b').
        intros. unfold prop_succ in r. destruct (L.eq_dec _ _). apply H0; auto.
        unfold r. simpl. destruct (N.eq_dec b' b).
        * rewrite find_default_eq; auto. apply LFacts.le_meet_r.
        * rewrite find_default_neq; auto. apply H0. contradict Hwl; simpl; auto.

      + intros a b.
        set (r := prop_succ _ a b).
        intros. unfold prop_succ in r. destruct (L.eq_dec _ _) as [Heq|].
        * subst r. rewrite Heq. apply LFacts.le_meet_r.
        * simpl. rewrite find_default_eq; auto. apply LFacts.le_meet_r.
    - (* n_invar is preserved for all successors ~= n *)
      intros Hin. pattern s'. eapply fold_left_1; eauto.
      intros. apply prop_n_invar_pres. assumption.
      unfold state_invar, n_invar in Hinv |- *.
      simpl. specialize (Hinv n). rewrite Hwls in Hinv. destruct Hinv.
      assumption. left. destruct H; intuition. right. apply H.
  Qed.

  Lemma fixpoint_solution: forall res n s,
    fixpoint = Some res ->
    NM.In n inits ->
    In s (succs n) ->
    res!!s <= trans n res!!n.
  Proof.
    unfold fixpoint; intros. pattern res.
    eapply Iter.iter_prop with
      (step:=step) (P:=state_invar) (a:=make_init_state); eauto.
    - intros a Ha.
    unfold step. destruct (wlist a) eqn:Heql.
      + specialize (Ha n). destruct Ha.
        * auto.
        * rewrite Heql in *. contradiction.
        * auto.
      + eapply step_state_invar. apply Ha.
        unfold step. rewrite Heql. auto.
    - left. simpl. apply in_map_iff.
      pose proof (NMFacts.elements_in_iff inits n0) as [He _].
      specialize (He H2). destruct He as [e Hine].
      apply InA_alt in Hine as [y [Heq Hk]].
      inversion Heq; eauto.
  Qed.

  (* monotonicity *)

  Definition le_nlmap (nl1 nl2: nlmap) : Prop :=
    forall n, nl1!!n <= nl2!!n.

  Lemma le_nlmap_refl : forall nl, le_nlmap nl nl.
  Proof.
    unfold le_nlmap. reflexivity.
  Qed.

  Instance le_nlmap_trans : Transitive le_nlmap.
    unfold Transitive, le_nlmap; intros. transitivity y !! n; auto.
  Qed.

  Hint Resolve LFacts.le_meet_l LFacts.le_meet_r : core .
    (* L.eq_equiv L.le_preorder L.le_poset L.eq_le_reflexive. *)
    (* Saw this in Relation_Definitions but it doesn't appear to work? *)

  Lemma prop_succ_le_nlmap: forall st out n,
    le_nlmap (prop_succ out st n).(lmap) st.(lmap).
  Proof.
    unfold le_nlmap, prop_succ; intros.
    destruct (L.eq_dec _ _). reflexivity.
    simpl. destruct (N.eq_dec n n0).
      subst. rewrite find_default_eq; auto.
      rewrite find_default_neq; auto. reflexivity.
  Qed.

  Lemma step_le_nlmap: forall st st',
    inr st' = step st ->
    le_nlmap st'.(lmap) st.(lmap).
  Proof.
    unfold step; intros. destruct (wlist st).
    discriminate. injection H. intro Heqs.
    pattern st'. eapply fold_left_1.
    intros. transitivity (lmap a).
       apply prop_succ_le_nlmap. assumption.
    apply Heqs. apply le_nlmap_refl.
  Qed.

  Lemma fixpoint_entry : forall res n,
    fixpoint = Some res -> res!!n <= inits!!n.
  Proof.
    unfold fixpoint. intros. pattern res.
    eapply Iter.iter_prop with (step:=step).
    - intros.
      destruct (step a) eqn:Hstep.
      + unfold step in Hstep. destruct (wlist a); try discriminate.
        injection Hstep. intro; subst t. apply H0.
      + simpl in *. transitivity (lmap a)!!n; [|assumption].
        apply step_le_nlmap. auto.
    - change inits with (lmap make_init_state).
      cbv beta. reflexivity.
    - apply H.
  Qed.

  Lemma fixpoint_invariant : forall
    (P: N.t -> L.t -> Prop)
    (Pinits: forall n, P n inits!!n)
    (Ptrans: forall n ln s ls,
      In s (succs n) ->
      P n ln -> P s ls -> P s (L.meet ls (trans n ln))),
    forall res n, fixpoint = Some res -> P n res!!n.
  Proof.
    intros until 2.
    unfold fixpoint. intros. pattern res.
    eapply Iter.iter_prop with (step:=step); eauto.

    intro. destruct (step a) eqn:Hstep.

    (* last step  Q implies P *)
    unfold step in Hstep. destruct (wlist a); try discriminate.
    instantiate (1:=fun s => forall n, P n s.(lmap)!!n).
    injection Hstep. intro; subst t. intros; auto.

    (* P preserved across step *)
    simpl. intros. unfold step in Hstep.
    destruct (wlist a); try discriminate.
    injection Hstep; clear Hstep; intro Heqs.

    pattern s. eapply fold_left_1 with (f:=prop_succ _); eauto.
    intros. unfold prop_succ.
    destruct (L.eq_dec _ _); simpl; auto.
    destruct (N.eq_dec b n0).
    rewrite find_default_eq; auto.
      subst b. apply Ptrans; auto.
    rewrite find_default_neq; auto.
    auto.
  Qed.

  End KILDALL.

End ForwardSolver.
