Require Import Coq.Program.Equality.
Require Import Equalities.
Require Import FSets.

(* Set Mangle Names. *)

Module Type PGraph.
  Parameter Inline t V : Type.
  Parameter Inline entry : t -> V.
  Parameter Inline Edge : t -> V -> V -> Prop.
  Parameter Inline Contains : t -> V -> Prop.

  Parameter Inline veq: forall (v1 v2: V), {v1 = v2} + {v1 <> v2}.

  Axiom Inline contains_entry: forall t, Contains t (entry t).
  Axiom Inline contains_edge_endpoints: forall t v1 v2, Edge t v1 v2 -> Contains t v1 /\ Contains t v2.
End PGraph.

Module PGraphFacts (Import Graph: PGraph).
  Lemma contains_edge_source: forall t v1 v2, Edge t v1 v2 -> Contains t v1.
  Proof. intros ??? [H _]%contains_edge_endpoints. exact H. Qed.
  Lemma contains_edge_target: forall t v1 v2, Edge t v1 v2 -> Contains t v2.
  Proof. intros ??? [_ H]%contains_edge_endpoints. exact H. Qed.
End PGraphFacts.

Module PGraphPaths (Import G: PGraph).
  Import List.ListNotations.

  (** Defines a path in the graph. *)

  Inductive Path (g: t) : V -> V -> list V -> Prop :=
  | path_nil : forall v,
      G.Contains g v -> Path g v v [v]
  | path_cons : forall v1 v2 v3 vs,
      Path g v1 v2 vs -> G.Edge g v2 v3
      -> Path g v1 v3 (v3::vs).

  #[export] Hint Constructors Path : core.


  Definition Reachable (g: t) (v: V) : Prop :=
    exists p, Path g (entry g) v p.


  Lemma start_in_path: forall (g: t) (v1 v2: V) p,
      Path g v1 v2 p -> In v1 p.
  Proof.
    intros g v1 v2 p H.
    induction H.
    - simpl. left. reflexivity.
    - simpl. right. assumption.
  Qed.


  Lemma end_in_path: forall (g: t) (v1 v2 : V) p,
      Path g v1 v2 p -> In v2 p.
  Proof.
    intros g v1 v2 p H.
    destruct H; left; reflexivity.
  Qed.


  Lemma acyclic_path_exists: forall (g:G.t) (v1 v2 v3 : V) p,
      Path g v1 v2 p -> In v3 p -> exists q, Path g v1 v3 (v3::q) /\ ~ In v3 q.
  Proof.
    intros g v1 v2 v3 p Hp Hin.
    generalize dependent v3.
    induction Hp; simpl; intros u Hin.
    - destruct Hin. subst. exists []. split.
      * apply path_nil. exact H.
      * simpl. auto.
      * inversion H0.
    - destruct Hin as [H_eq | H_in]. subst.
      + destruct (in_dec G.veq u vs).
        * apply IHHp. apply i.
        * exists vs. split. eapply path_cons; eauto. auto.
      + apply IHHp. apply H_in.
  Qed.

  Lemma path_splits: forall (g:G.t) (v1 v2 v3 : V) p,
      Path g v1 v2 p -> In v3 p ->
      exists p1, exists p2, Path g v1 v3 (v3::p1)
                  /\ Path g v3 v2 (v2::p2)
                  /\ p = (v2::p2 ++ p1).
  Proof.
    intros g v1 v2 v3 p Hp Hin.
    generalize dependent v3.
    induction Hp; simpl; intros u Hin.
    - destruct Hin. subst.
      * exists []. exists []. repeat split;auto.
      * destruct H0.
    - destruct Hin as [?|H_in]. subst.
      + exists vs. exists []. split.
        eapply path_cons; eauto.
        split.
        * apply path_nil. apply G.contains_edge_endpoints in H as [_?]. assumption.
        * reflexivity.
      + eapply IHHp in H_in.
        destruct H_in as [p1 [p2 [Hp1 [Hp2 Heq]]]].
        exists p1. exists (v2::p2). split; auto. split.
        * eapply path_cons; eauto.
        * subst. reflexivity.
  Qed.

  Lemma path_start_is_contained: forall p g v1 v2, Path g v1 v2 p -> G.Contains g v1.
  Proof.
    induction p; intros g v1 v2 Path_v1_v2; dependent destruction Path_v1_v2.
    - assumption.
    - apply IHp with (1 := Path_v1_v2).
  Qed.

  Lemma path_end_is_contained: forall p g v1 v2, Path g v1 v2 p -> G.Contains g v2.
  Proof.
    induction p; intros g v1 v2 Path_v1_v2; dependent destruction Path_v1_v2.
    - assumption.
    - apply G.contains_edge_endpoints in H as [_?]. assumption.
  Qed.

End PGraphPaths.

Module Type Graph.
  Include PGraph.
  Parameter Inline edge: t -> V -> V -> bool.
  Parameter Inline contains: t -> V -> bool.
  
  Parameter Inline successors: t -> V -> list V.
    
  Axiom Inline edge_spec: forall t v1 v2, reflect (Edge t v1 v2) (edge t v1 v2).
  Axiom Inline successors_spec: forall t v1 v2, List.In v2 (successors t v1) <-> Edge t v1 v2.
  Axiom Inline contains_spec: forall t v, reflect (Contains t v) (contains t v).
End Graph.

Module Type IsFiniteGraph (Import G: Graph).
  Parameter Inline vertices: t -> list V.
  Axiom Inline vertices_spec: forall t v, List.In v (vertices t) <-> Contains t v.
End IsFiniteGraph.

Module Type FiniteGraph := Graph <+ IsFiniteGraph.
