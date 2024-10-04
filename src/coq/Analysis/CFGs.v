From Vellvm Require
  Syntax.CFG
  Syntax.DynamicTypes
  Syntax.LLVMAst
  Syntax.Scope.
From Vellvm.Analysis Require Graph.

Module Block <: Graph.FiniteGraph.
  Definition t: Type := CFG.cfg DynamicTypes.dtyp.
  Definition V: Type := LLVMAst.block_id.
  Definition entry (g: t): V := CFG.init g.

  Definition Edge (g: t) (u v: V): Prop :=
    match CFG.find_block (CFG.blks g) u with
    | None => False
    | Some i => List.In v (Scope.successors i)
    end.

  Definition Contains (g: t) (u: V): Prop :=
    match CFG.find_block (CFG.blks g) u with
    | None => False
    | Some _ => True
    end.

  Definition veq: forall (v1 v2: V), {v1 = v2} + {v1 <> v2} := Scope.raw_id_eq_dec.

  Lemma contains_entry: forall t, Contains t (entry t).
  Proof. admit. Admitted.
  Lemma contains_edge_endpoints: forall t v1 v2, Edge t v1 v2 -> Contains t v1 /\ Contains t v2.
  Proof. admit. Admitted.

  Definition successors (g: t) (v: V): list V :=
    match CFG.find_block (CFG.blks g) v with
    | None => nil
    | Some i => Scope.successors i
    end.

  Definition edge_predicate (v: V) := fun v' => if veq v v' then true else false.
  Definition edge (g: t) (u v: V): bool :=
    match List.find (edge_predicate v) (successors g u) with
    | None => false
    | Some _ => true
    end.
    
  Definition contains (g: t) (v: V): bool :=
    match CFG.find_block (CFG.blks g) v with
    | None => false
    | Some _ => true
    end.


  Lemma edge_spec: forall g v1 v2, Bool.reflect (Edge g v1 v2) (edge g v1 v2).
  Proof.
    intros g v1 v2.
    unfold edge,successors,Edge in *.
    destruct (CFG.find_block (CFG.blks g) v1) as [b|]; cbn.
    - destruct (List.find (edge_predicate v2) (Scope.successors b)) eqn:Eq_find.
      + apply List.find_some in Eq_find as [In Eq_v].
        unfold edge_predicate in Eq_v. destruct (veq v2 v); [subst|discriminate].
        constructor. assumption.
      + constructor; intros Falsum.
        apply List.find_none with (2 := Falsum) in Eq_find.
        unfold edge_predicate in Eq_find. destruct (veq v2 v2); [discriminate|contradiction].
    - constructor. intros [].
  Qed.

  Lemma successors_spec: forall g v1 v2, List.In v2 (successors g v1) <-> Edge g v1 v2.
  Proof.
    intros g v1 v2.
    unfold successors,Edge.
    destruct (CFG.find_block (CFG.blks g) v1).
    - reflexivity.
    - split; [|intros []]. intros []%List.in_nil.
  Qed.

  Lemma contains_spec: forall g v, Bool.reflect (Contains g v) (contains g v).
  Proof.
    intros g v. unfold Contains,contains.
    destruct (CFG.find_block (CFG.blks g) v); constructor.
    - constructor. - intros [].
  Qed.

  Definition vertices (g: t): list V :=
    Scope.inputs (CFG.blks g).

  Lemma vertices_spec: forall g v, List.In v (vertices g) <-> Contains g v.
  Proof. Admitted.

End Block.

(* Module Instructions. *)
(* TODO: Implement instruction CFG *)
(* End Instructions. *)
