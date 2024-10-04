(** Reasoning about dominators in a graph. *)

From Coq Require Import List Equalities Orders RelationClasses Lia.
From Coq Require Import FSets.
From Coq Require Import Classes.RelationClasses Program.Equality.

Import ListNotations.

From Vellvm.Analysis Require Lattice Graph Kildall.

(** ** Specification of Dominators *)

Module Spec (Import G: Graph.PGraph).
  Module Path := Graph.PGraphPaths G.
  Import Path(Path).

  (** *** Definition of domination *)
  Definition Dominates (g: G.t) (v1 v2: V) : Prop :=
    forall vs, Path g (entry g) v2 vs -> In v1 vs.

  (* Non-reflexive domantion.  *)
  Definition StrictlyDominates (g: G.t) (v1 v2: V) : Prop :=
    v1 <> v2 /\ Dominates g v1 v2.

  Definition ImmediatelyDominates (g:G.t) (v1 v2 : V) : Prop :=
    StrictlyDominates g v1 v2 /\ forall v3, StrictlyDominates g v3 v2 -> Dominates g v3 v1.

  Lemma Dominates_reflexive : forall (g:G.t) (v : V),
      Dominates g v v.
  Proof.
    intros g v.
    unfold Dominates.
    intros vs Hp.
    apply Path.end_in_path with (1 := Hp).
  Qed.

  Lemma Dominates_antisymmetric : forall (g:G.t) (v1 v2 : V),
      Path.Reachable g v1 ->
      Dominates g v1 v2 -> Dominates g v2 v1 -> v1 = v2.
  Proof.
    intros g v1 v2 H1 D1 D2.
    unfold Dominates in *.
    destruct H1 as [p Hp].
    assert (In v1 p). eapply Path.end_in_path. apply Hp.
    destruct (Path.acyclic_path_exists g (entry g) v1 v1 p Hp H) as [p' [Hp' Hin]].
    assert (In v2 (v1 :: p')) as Hin'. eapply D2. apply Hp'.
    destruct (Path.path_splits g (entry g) v1 v2 (v1::p') Hp' Hin') as [q1 [q2 [HQ1 [HQ2 Heq]]]].
    inversion Heq. subst. clear Heq.
    eapply D1 in HQ1.
    destruct (in_inv HQ1). auto.
    contradiction Hin. eapply in_or_app. right. apply H0.
  Qed.

  Lemma Dominates_transitive : forall (g:G.t) (v1 v2 v3 : V),
      Dominates g v1 v2 -> Dominates g v2 v3 -> Dominates g v1 v3.
  Proof.
    intros g v1 v2 v3 D1 D2.
    unfold Dominates in *.
    intros vs Hp.
    destruct (Path.path_splits g (entry g) v3 v2 vs) as [q1 [q2 [HQ1 [HQ2 Heq]]]]; auto.
    apply D1 in HQ1.
    inversion HQ1.
    - subst. rewrite app_comm_cons.
      apply in_or_app. left. eapply Path.start_in_path. apply HQ2.
    - subst. simpl. right. apply in_or_app. right. exact H.
  Qed.

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
    intros g v [Falsum_1 Falsum_2].
    (* TODO: use fast forward instead *)
    unfold Dominates in *.
    assert (Path g (entry g) (entry g) [entry g]) as Path_entry. {
      constructor. apply G.contains_entry.
    }
    specialize Falsum_2 with (vs := [entry g]) (1 := Path_entry).
    apply in_inv in Falsum_2 as [|]; [congruence|].
    apply in_nil with (a := v). assumption.
  Qed.

  Lemma ImmediatelyDominates_unique : forall (g:G.t) (v1 v2 v : V),
      Path.Reachable g v1 ->
      ImmediatelyDominates g v1 v -> ImmediatelyDominates g v2 v -> v1 = v2.
  Proof.
    intros g v1 v2 v H H1 H2.
    destruct H1 as [S1 H1].
    destruct H2 as [S2 H2].
    apply H1 in S2.
    apply H2 in S1.
    eapply Dominates_antisymmetric; eauto.
  Qed.


  Lemma dom_step : forall g v1 v2,
    G.Contains g v2 -> G.Edge g v1 v2 -> forall v', StrictlyDominates g v' v2 -> Dominates g v' v1.
  Proof.
    unfold StrictlyDominates, Dominates. intros g v1 v2 Hmem Hsucc v' [Hneq Hdom] p Hp.
    assert (In v' (v2::p)) as H. { apply Hdom. eapply Path.path_cons; eauto. }
    inversion H; subst; intuition auto with *.
  Qed.

End Spec.

(** *** Relate an algorithm to the specification *)
Module Type Algdom (G: Graph.Graph).
  Module Spec := Spec G.

  Declare Module DecidableV : UsualDecidableType with Definition t := G.V.
  Declare Module NodeSet: FSetInterface.WS with Module E := DecidableV.
  Module NodeBoundedSet := Lattice.BoundedSet NodeSet.

  Import (notations) NodeBoundedSet.

  Parameter calc_sdom : G.t -> option (G.V -> NodeBoundedSet.t).

  Axiom entry_sound : forall g sdom,
    calc_sdom g = Some sdom ->
    sdom (G.entry g) == NodeBoundedSet.empty.

  Axiom successors_sound : forall g sdom n1 n2,
    calc_sdom g = Some sdom ->
    G.Edge g n1 n2 ->
    sdom n2 <= NodeBoundedSet.union (NodeBoundedSet.singleton n1) (sdom n1).

  Axiom complete : forall g sdom n1 n2,
    calc_sdom g = Some sdom ->
    Spec.StrictlyDominates g n1 n2 -> NodeBoundedSet.In n1 (sdom n2).
End Algdom.

Module AlgdomProperties (G: Graph.Graph) (A : Algdom G).
  Import (notations) A.NodeBoundedSet.

  Lemma sound : forall g sdom n1 n2,
    A.calc_sdom g = Some sdom ->
    A.NodeBoundedSet.In n1 (sdom n2) -> A.Spec.Dominates g n1 n2.
  Proof.
    red; intros. remember (G.entry g) as entry. dependent induction H1.
    - assert (sdom v == A.NodeBoundedSet.empty). { subst. apply A.entry_sound. assumption. }
      destruct (sdom v) eqn:Eq_sdom; [cbn in *; subst; left | contradiction].
      rewrite -> H2 in H0. rewrite -> A.NodeBoundedSet.SFacts.empty_iff in H0. contradiction.
    - right.
      destruct (A.DecidableV.eq_dec v2 n1); subst.
      + inversion H1; intuition auto with *.
      + destruct (sdom v2) eqn:Heqv2; simpl in *; auto.
        assert (A.NodeSet.In n1 (A.NodeSet.union (A.NodeSet.singleton v2) t)) as Hin. {
          pose proof A.successors_sound g sdom v2 v3 as Hss.
          specialize (Hss ltac:(assumption) ltac:(assumption)).
          rewrite -> Heqv2 in Hss. (* Why on earth are you unfolding?  *)
          destruct (sdom v3); cbn in Hss.
          * rewrite <- Hss. apply H0.
          * contradiction.
        }
        apply A.NodeSet.union_1 in Hin as [Hin | Hin]; [|auto].
        contradict n. apply A.NodeSet.singleton_1. assumption.
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
    unfold calc_sdom. intros.
    destruct (Solver.fixpoint _ _ _) eqn:Heqk; try discriminate H.
    injection H. intro. clear H. subst sdom.
    set (r := t!!(Graph.entry g)). cut (NodeBoundedSet.le r NodeBoundedSet.empty).
    destruct r; try inversion 1. simpl.
    intro Hsub. red. intro a. split;
    intro; exfalso; eapply NodeSetFacts.empty_iff; eauto.

    replace NodeBoundedSet.empty with ((inits g)!!(Graph.entry g)).
    eapply Solver.fixpoint_entry. apply Heqk.
    unfold inits. rewrite Solver.FMP.find_default_eq; auto.
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
    eauto.

    unfold inits. destruct (DecidableV.eq_dec n1 (Graph.entry g)).
    apply SolverResFacts.add_in_iff; auto. apply SolverResFacts.add_neq_in_iff; auto.

    (* separate lemma? *)
    pose proof (Graph.contains_edge_endpoints _ _ _ H0) as [Vertex_n1%Graph.vertices_spec _].

    (* set (f g n := NM.add n L.bot g). *)
    assert (In n1 (Graph.vertices g) \/ Solver.NM.In n1 (Solver.NM.empty NodeBoundedSet))
           as Hin by solve [left; assumption].
    generalize (Graph.vertices g) (Solver.NM.empty NodeBoundedSet) Hin.
    induction l; simpl. intuition auto with *.
    intros to Hin'. destruct Hin' as [[? | ?] | ?]; subst; auto.
    apply SolverResFacts.add_in_iff; auto.
    destruct (DecidableV.eq_dec a n1).
      subst.
      apply SolverResFacts.add_in_iff; auto. apply SolverResFacts.add_neq_in_iff; auto.
      lapply (IHl to). intros.
      apply SolverResFacts.add_in_iff; auto.
      right; auto.
    apply Graph.successors_spec ; auto.
  Qed.

  (* Include AlgdomProperties G. *)

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

    intros. destruct (DecidableV.eq_dec (Graph.entry g) n).
    subst n. contradict H0.
    apply Spec.not_StrictlyDominates_entry. unfold inits.
    rewrite Solver.FMP.find_default_neq; auto. unfold Solver.FMP.find_default.
    destruct (Solver.NM.find _ _) as [l'|] eqn:Heq; simpl; auto.

    induction (Graph.vertices g); simpl in *.
    rewrite SolverResFacts.empty_o in Heq. inversion Heq.
    rewrite <- SolverResFacts.find_mapsto_iff in Heq.
    rewrite SolverResFacts.add_mapsto_iff in Heq.
    destruct Heq as [[eq1 eq2] | [neq1 hyp]]; subst; simpl in *; auto.
    apply IHl. rewrite SolverResFacts.find_mapsto_iff in hyp.
    apply hyp.

    (* step preserves completeness *)
    intros. unfold trans.
    rewrite -> Graph.successors_spec in H.
    pose proof (Graph.contains_edge_endpoints _ _ _ H) as [??].

    destruct ls eqn:Heqls, ln eqn:Heqln; simpl; auto.
    apply NodeSetFacts.inter_iff. split. apply H1; auto.
    apply NodeSetFacts.union_iff.
    destruct (DecidableV.eq_dec n1 n). left. apply NodeSetFacts.singleton_iff; auto.
    right. apply H0. red; split; auto.
    eapply Spec.dom_step with (v2:=s); auto.


    apply H1; auto.

    apply NodeSetFacts.union_iff.
    destruct (DecidableV.eq_dec n1 n). left. apply NodeSetFacts.singleton_iff; auto.
    right. apply H0. red; split; auto.
    eapply Spec.dom_step with (v2:=s); auto.
  Qed.

End AlgdomKildall.
