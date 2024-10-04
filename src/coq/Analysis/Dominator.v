(** Reasoning about dominators in a graph. *)

From Coq Require Import List Equalities Orders RelationClasses Lia.
From Coq Require Import FSets.
From Coq Require Import Classes.RelationClasses Program.Equality.

Import ListNotations.

From Vellvm.Analysis Require Lattice Graph Kildall.

(** ** Specification of Dominators *)

Module Spec (Import G: Graph.PGraph).
  Module Path := Graph.PGraphPaths G.
  Import Path(Path,Reachable).

  (** *** Definition of domination *)
  Definition Dominates (g: G.t) (d v: V): Prop :=
    forall p, Path g (entry g) v p -> In d p.

  (* Non-reflexive domination.  *)
  Definition StrictlyDominates (g: G.t) (d v: V): Prop :=
    d <> v /\ Dominates g d v.

  Definition ImmediatelyDominates (g: G.t) (d v: V): Prop :=
    StrictlyDominates g d v /\ forall d', StrictlyDominates g d' v -> Dominates g d' d.

  Lemma Dominates_reflexive : forall (g: G.t) (v: V),
      Dominates g v v.
  Proof.
    (* By definition of dominator; v is always the last vertex in the path. *)
    intros g v p. apply Path.end_in_path.
  Qed.

  Lemma Dominates_antisymmetric : forall (g: G.t) (v1 v2: V),
      Path.Reachable g v1 ->
      Dominates g v1 v2 -> Dominates g v2 v1 -> v1 = v2.
  Proof.
    (* Unpack assumptions *)
    intros g v1 v2 [p Path_p] Dom_v1_v2 Dom_v2_v1.

    (* Replace the path witnessing v1's reachability by a simple one. *)
    apply Path.simple_path_exists in Path_p; clear p; destruct Path_p as (p & Path_p & NoDup_p).

    (* Since v2 domiantes v1, it must be on that simple path. *)
    (* The path can hence be segmented into p = entry -p0-> ? -> v2 -> ? -p1-> v1.  *)
    specialize (Dom_v2_v1 _ Path_p) as v2_in_p.
    apply List.in_split in v2_in_p as (p1 & p0 & ->).
    apply Path.path_excise in Path_p as [Path_p1 Path_p0].

    (* Since p was simple, p0 is simple and v1 cannot appear on p0. *)
    rewrite ListUtil.appcons_to_appapp in NoDup_p.
    apply Path.path_uncons in Path_p1 as [p1_ Tmp]; rewrite -> Tmp in *; clear Tmp p1; rename p1_ into p1.
    cbn in NoDup_p. rewrite -> NoDup_cons_iff in NoDup_p. destruct NoDup_p as [v1_NotIn_p NoDup_p].
    apply ListUtil.not_in_app in v1_NotIn_p as [_ v1_NotIn_p0]. apply NoDup_app_remove_l in NoDup_p.

    (* However, since v1 domintaes v2, it must appear on v2::p0.  *)
    specialize (Dom_v1_v2 _ Path_p0) as v1_In_p0.
    destruct v1_In_p0.
    - (* Hence v1 = v2  *)
      symmetry. assumption.
    - (* Or a contradiction was reached. *)
      contradiction.
  Qed.

  Lemma Dominates_transitive : forall (g: G.t) (v1 v2 v3 : V),
      Dominates g v1 v2 -> Dominates g v2 v3 -> Dominates g v1 v3.
  Proof.
    intros g v1 v2 v3 Dom_v1_v2 Dom_v2_v3.

    intros p Path_p.
    (* Since v2 dominates v3, it must be on the path, hence the path can be partitioned. *)
    specialize (Dom_v2_v3 _ Path_p) as In_v2.
    apply List.in_split in In_v2 as (p1 & p2 & ->).
    apply Path.path_excise in Path_p as [_ Path_p2].

    (* Since v1 dominates v2, it must be on the prefix of the partition.  *)
    specialize (Dom_v1_v2 _ Path_p2) as In_v1.
    (* Which allows to conclude.  *)
    apply List.in_or_app. right. assumption.
  Qed.

  Add Parametric Relation (g: G.t):  V (Dominates g)
      reflexivity proved by (Dominates_reflexive g)
      transitivity proved by (Dominates_transitive g)
      as Dominates_refl_trans.


  (* Lemma ImmediatelyDominates_alt: *)
  (*   forall g v1 v2, ImmediatelyDominates g v1 v2 <-> *)
  (*                (StrictlyDominates g v1 v2 /\ forall v', StrictlyDominates g v' v2 -> ~StrictlyDominates g v1 v'). *)
  (* Proof. *)
  (*   unfold ImmediatelyDominates, StrictlyDominates. *)
  (*   intros g v1 v2; split. *)
  (*   - intros ((Dif_v1_v2 & Dom_v1_v2) & H). *)
  (*     split; [split; assumption|]. *)
  (*     intros v' Dif_v'_v2 [Falsum_1 Falsum_2]. *)
  (*     specialize H with (1 := Dif_v'_v2). *)
  (*     assert (Reachable g v') by admit. *)
  (*     pose proof (Dominates_antisymmetric _ _ _ ltac:(eassumption) H Falsum_2); subst. *)
  (*     contradiction. *)
  (*   - intros ((Dif_v1_v2 & Dom_v1_v2) & H). *)
  (*     split; [split; assumption|]. *)
  (*     intros v' SDom_v'_v2. specialize H with (1 := SDom_v'_v2). *)
  (*     Search (~(_ /\ _)). Print Decidable.decidable. *)
  (*     exfalso. apply H. *)
  (*     split; [admit|]. *)

  Lemma not_StrictlyDominates_entry: forall (g: G.t) (v: V),
      ~StrictlyDominates g v (G.entry g).
  Proof.
    (* Strict domination cannot hold by reflexivity, so any path to the entry must contain v.  *)
    intros g v [Ineq Dom_v_entry].

    (* Consider the singleton path from the entry to itself. *)
    assert (Path g (entry g) (entry g) [entry g]) as Path_sing by constructor.
    (* It must contain the dominator v. *)
    specialize (Dom_v_entry _ Path_sing).
    (* But since the path is a singleton, u is the entry, which contradicts the definition of strict dominator.  *)
    destruct Dom_v_entry as [<- | ?]; contradiction.
  Qed.

  Lemma ImmediatelyDominates_unique : forall (g: G.t) (v1 v2 v : V),
      Reachable g v1 ->
      ImmediatelyDominates g v1 v -> ImmediatelyDominates g v2 v -> v1 = v2.
  Proof.
    intros g v1 v2 v Reachable_v1 IDom_v1_v IDom_v2_v.
    (* By definition of immediate domination, the two dominators must dominate each other.  *)
    destruct IDom_v1_v as [SDom_v1_v IDom_cond_v1].
    destruct IDom_v2_v as [SDom_v2_v IDom_cond_v2].
    specialize IDom_cond_v1 with (1 := SDom_v2_v).
    specialize IDom_cond_v2 with (1 := SDom_v1_v).
    (* By antisymmetry, these must hence be equal.  *)
    apply (Dominates_antisymmetric g); assumption.
  Qed.

  (* Note that the assumption that v0 *Strictly* dominates v2 is necessary,
     as otherwise the theorem would imply that the existence of an edge
     would imply domination (by letting v0 = v2 and using Dominates' reflexivity).
   *)
  Lemma Dominates_reachable_edge : forall g v1 v2,
      G.Edge g v1 v2 ->
      forall v0, StrictlyDominates g v0 v2 -> Dominates g v0 v1.
  Proof.
    intros g v1 v2 Edge_v1_v2 v0 [Ineq Dom_v0_v2].
    (* Let v0 -p-> v2  *)
    intros p Path_p.
    (* Then p can be extended to reach v2 using the hypothesized edge. *)
    apply Path.path_cons with (2 := Edge_v1_v2) in Path_p.
    (* Then v0 must be on that path, since it dominates v1. *)
    specialize (Dom_v0_v2 _ Path_p) as [->|?]; [contradiction|].
    assumption.
  Qed.

End Spec.

(** *** Relate an algorithm to the specification *)
Module Type Algdom (G: Graph.Graph).
  Module Spec := Spec G.

  Declare Module DecidableV : UsualDecidableType with Definition t := G.V.
  Declare Module NodeSet: FSetInterface.WS with Module E := DecidableV.
  Module NodeBoundedSet := Lattice.BoundedSet NodeSet.

  Import (notations) NodeBoundedSet.
  Import NodeBoundedSet(union,singleton,empty,In,universe).

  Parameter calc_sdom : G.t -> option (G.V -> NodeBoundedSet.t).

  Axiom entry_sound : forall g sdom,
      calc_sdom g = Some sdom ->
      sdom (G.entry g) == empty.

  Axiom successors_sound : forall g sdom n1 n2,
      calc_sdom g = Some sdom ->
      G.Edge g n1 n2 ->
      sdom n2 <= union (singleton n1) (sdom n1).

  Axiom complete : forall g sdom n1 n2,
      calc_sdom g = Some sdom ->
      Spec.StrictlyDominates g n1 n2 -> In n1 (sdom n2).

End Algdom.

Module AlgdomProperties (G: Graph.Graph) (Import A : Algdom G).
  (* nnModule Path := A.Spec.Path. *)
  (* Import Path(Path,Reachable). *)

  Import (hints) NodeSet NodeBoundedSet.
  Import (notations) NodeBoundedSet.

  (* Import (notations,hints) A.NodeSet. *)
  (* Import A.NodeSet(union,singleton,In). *)
  Module NodeSetFacts := FSetFacts.WFacts_fun A.DecidableV A.NodeSet.

  (* Lemma path_sound: forall g sdom d v p, *)
  (*     A.calc_sdom g = Some sdom -> *)
  (*     (* Path g (G.entry g) v p -> *) *)
  (*     Path g d v p -> *)
  (*     (* List.In d p -> *) *)
  (*     sdom v [<=] union (singleton d) (sdom d). *)
  (* Proof. *)
  (*   intros g sdom d v p Def_sdom Path_p. *)
  (*   (* apply List.in_split in In_d_p as (s & p'& ->). *) *)
  (*   (* apply Path.path_excise in Path_p as (Path_s & Path_p').  *) *)
  (*   dependent induction Path_p. *)
  (*   - intros u. apply A.NodeSet.union_3.  *)
  (*   - transitivity (A.NodeSet.union (A.NodeSet.singleton v2) (sdom v2)). *)
  (*     + apply A.successors_sound with (g := g); assumption. *)
  (*     + apply IHPath_p. *)

  (*     assert (sdom v1 [<=] A.NodeSet.union (A.NodeSet.singleton v1) (sdom v1) ). { *)
  (*       admit. *)
  (*     } *)
  (*     rewrite H0. *)
  (*     apply successors_sound. *)

  (* Note that the algorithm is slightly underspecified: the current implementation
     actually ensures that d *strictly* dominates v. We might want to add an antisymmetry
     axiom (~In v (sdom v)).
   *)
  Lemma sound : forall g sdom d v,
    calc_sdom g = Some sdom ->
    NodeBoundedSet.In d (sdom v) -> Spec.Dominates g d v.
  Proof.
    intros g sdom d v Def_sdom Dom_d_v.
    (* Let's proceed by induction on entry -p-> v  *)
    intros p Path_p; dependent induction Path_p.
    + (* p = [v] = [entry] (since the path is a singleton),
           which entails that sdom v = empty (by assumption since v = entry),
           which in turns yield a contradiction (that d is in it).
       *)
      rewrite -> A.entry_sound in Dom_d_v by assumption.
      rewrite -> NodeBoundedSet.empty_iff in Dom_d_v. contradiction.
    + rename v3 into v, v2 into v', H into Edge_v'_v, vs into p'.
      (* p = entry -p'-> v' -> v; edge soudness can be used to distinguish two cases: *)
      pose proof (A.successors_sound _ _ _ _ Def_sdom Edge_v'_v) as Dom_d_v'.
      rewrite -> Dom_d_v' in Dom_d_v.
      apply NodeBoundedSet.In_union in Dom_d_v as [Eq | ?].
      * (* * d = v2, since v2 is the endpoint of vs, is on the path p.  *)
        rewrite -> NodeBoundedSet.singleton_iff in Eq; subst.
        right. apply Spec.Path.end_in_path with (1 := Path_p).
      * (* * {d} <= sdom v2, hence d is on the subpath vs by IH. *)
        right. apply IHPath_p; [assumption|assumption|reflexivity].
  Qed.

End AlgdomProperties.

Module AlgdomKildall (Graph: Graph.FiniteGraph)
       <: Algdom Graph.

  Module MiniDecidableV <: MiniDecidableType with Definition t := Graph.V.
    Definition t: Type := Graph.V.
    Definition eq_dec: forall (l r: t), {l = r} + {l <> r} := Graph.veq.
  End MiniDecidableV.
  Module DecidableV := Make_UDT MiniDecidableV.

  Module Spec := Spec Graph.
  Module NodeSet := FSetWeakList.Make DecidableV.
  Module NodeBoundedSet := Lattice.BoundedSet NodeSet.
  Module Solver  := Kildall.ForwardSolver DecidableV NodeBoundedSet.

  Module SolverResFacts := FMapFacts.WFacts_fun DecidableV Solver.NM.
  Module NodeSetFacts := FSetFacts.WFacts_fun DecidableV NodeSet.

  Import NodeBoundedSet(union, singleton).
  Notation NodeBoundedSet := NodeBoundedSet.t.
  Notation Graph := Graph.t.
  Notation Vertex := Graph.V.
  Import (notations) NodeBoundedSet Solver.

  Definition trans (n: Vertex) (l: NodeBoundedSet) : NodeBoundedSet :=
    union (singleton n) l.

  Definition inits (g: Graph) : Solver.NM.t NodeBoundedSet :=
    Solver.NM.add (Graph.entry g) NodeBoundedSet.empty
    (fold_right (fun n g => Solver.NM.add n NodeBoundedSet.universe g) (Solver.NM.empty NodeBoundedSet) (Graph.vertices g) ).

  Definition calc_sdom (g: Graph) : option (Graph.V -> NodeBoundedSet) :=
    let nmo := Solver.fixpoint (Graph.successors g) trans (inits g) in
    match nmo with
      | None => None
      | Some nm => Some (fun n => nm!!n)
    end.

  Lemma entry_sound : forall g sdom,
    calc_sdom g = Some sdom ->
    sdom (Graph.entry g) == NodeBoundedSet.empty.
  Proof.
    (* Unpack assumptions. *)
    unfold calc_sdom. intros g sdom Def_sdom.
    destruct (Solver.fixpoint _ _ _) eqn:Heqk; [|discriminate Def_sdom].
    injection Def_sdom as <-.

    (* Let r be the result of the analysis for the entry node. *)
    set (r := t!!(Graph.entry g)).

    (* Let's first show that r <= ∅. *)
    assert (NodeBoundedSet.le r NodeBoundedSet.empty). {
      (* By definition, the initial value of the root is the empty set. *)
      assert (NodeBoundedSet.empty == (inits g)!!(Graph.entry g)) as ->. {
        unfold inits. rewrite -> Solver.FMP.find_default_eq; reflexivity.
      }
      (* Conclude using the fact that the result is always smaller than the initial value. *)
      apply Solver.fixpoint_entry with (1 := Heqk).
    }
    (* By definition, the empty set is the bottom of the lattice, and hence is smaller than r. *)
    pose proof (NodeBoundedSet.ord_bot r).
    (* Conclude by antisymmety that r is the ∅.  *)
    apply antisymmetry; assumption.
  Qed.

  Lemma successors_sound : forall g sdom n1 n2,
    calc_sdom g = Some sdom ->
    Graph.Edge g n1 n2 ->
    sdom n2 <= union (singleton n1) (sdom n1).
  Proof.
    unfold calc_sdom. intros.
    destruct (Solver.fixpoint _ _ _) eqn:Heqk; try discriminate H.
    injection H. intro. clear H. subst sdom.

    set (trans n o := union (singleton n) o).
    change (union (singleton n1) t!!n1)
           with (trans n1 t!!n1).
    eapply Solver.fixpoint_solution.
    - eauto.
    - unfold inits. destruct (DecidableV.eq_dec n1 (Graph.entry g)).
      1: solve [apply SolverResFacts.add_in_iff; auto].
      apply SolverResFacts.add_neq_in_iff; auto.
      (* separate lemma? *)
      pose proof (Graph.contains_edge_endpoints _ _ _ H0) as [Vertex_n1%Graph.vertices_spec _].

      assert (In n1 (Graph.vertices g) \/ Solver.NM.In n1 (Solver.NM.empty NodeBoundedSet))
        as Hin by solve [left; assumption].
      generalize (Graph.vertices g) (Solver.NM.empty NodeBoundedSet) Hin.
      induction l; simpl.
      + intuition auto with *.
      + intros to Hin'. destruct Hin' as [[? | ?] | ?]; subst; auto.
        * apply SolverResFacts.add_in_iff; auto.
        * destruct (DecidableV.eq_dec a n1).
          ++ subst.
             apply SolverResFacts.add_in_iff; auto.
          ++ apply SolverResFacts.add_neq_in_iff; auto.
        * lapply (IHl to). intros.
          apply SolverResFacts.add_in_iff; auto.
          right; auto.
    - apply Graph.successors_spec ; auto.
  Qed.

  Lemma complete : forall g sdom n1 n2,
      calc_sdom g = Some sdom ->
      Spec.StrictlyDominates g n1 n2 -> NodeBoundedSet.In n1 (sdom n2).
  Proof.
    intros. pose proof entry_sound _ _ H as Hentry.
    unfold calc_sdom in *.
    destruct (Solver.fixpoint _ _ _) as [res|] eqn:heqk; try discriminate H.
    injection H. intro. clear H. subst sdom.

    generalize H0. clear H0. pattern n2, res!!n2.
    eapply Solver.fixpoint_invariant; eauto.
    - intros. destruct (DecidableV.eq_dec (Graph.entry g) n).
      + subst n. contradict H0.
        apply Spec.not_StrictlyDominates_entry.
      + unfold inits.
        rewrite Solver.FMP.find_default_neq; auto. unfold Solver.FMP.find_default.
        destruct (Solver.NM.find _ _) as [l'|] eqn:Heq; simpl; auto.

        induction (Graph.vertices g); simpl in *.
        * rewrite SolverResFacts.empty_o in Heq. inversion Heq.
        * rewrite <- SolverResFacts.find_mapsto_iff in Heq.
          rewrite SolverResFacts.add_mapsto_iff in Heq.
          destruct Heq as [[eq1 eq2] | [neq1 hyp]]; subst; simpl in *; auto.
          apply IHl. rewrite SolverResFacts.find_mapsto_iff in hyp.
          apply hyp.

    (* step preserves completeness *)
    - intros. unfold trans.
      rewrite -> Graph.successors_spec in H.
      pose proof (Graph.contains_edge_endpoints _ _ _ H) as [??].

      destruct ls eqn:Heqls, ln eqn:Heqln; simpl; auto.
      + apply NodeSetFacts.inter_iff. split. apply H1; auto.
        apply NodeSetFacts.union_iff.
        destruct (DecidableV.eq_dec n1 n).
        * left. apply NodeSetFacts.singleton_iff; auto.
        * right. apply H0. red; split; auto.
          eapply Spec.Dominates_reachable_edge with (v2 := s); auto.
      + apply H1; auto.
      + apply NodeSetFacts.union_iff.
        destruct (DecidableV.eq_dec n1 n).
        * left. apply NodeSetFacts.singleton_iff; auto.
        * right. apply H0. red; split; auto.
          eapply Spec.Dominates_reachable_edge with (v2:=s); auto.
  Qed.

End AlgdomKildall.
