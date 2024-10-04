From Coq Require List.
From Coq Require Import Lia Program.Equality.
Import (notations) List List.ListNotations.

From Vellvm Require ListUtil.
From Vellvm Require Import Tactics.

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
      Path g v v [v]
  | path_cons : forall v1 v2 v3 vs,
      Path g v1 v2 vs -> G.Edge g v2 v3
      -> Path g v1 v3 (v3::vs).

  #[export] Hint Constructors Path : core.

  Definition path_snoc (g: t) (v1 v2 v3: V) (p: list V) (E: Edge g v1 v2) (Path_p: Path g v2 v3 p): Path g v1 v3 (p ++ [v1]).
    induction Path_p as [| v2 v3 v4 p' Path_p' rec].
    - cbn. apply path_cons with (v2 := v1). + constructor. + assumption.
    - cbn. apply path_cons with (v2 := v3).
      + apply rec. assumption.
      + assumption.
  Defined.


  Definition Reachable (g: t) (v: V) : Prop :=
    exists p, Path g (entry g) v p.

  Definition SimplePath (g: t) (v1 v2: V) (p: list V): Prop :=
    Path g v1 v2 p /\ List.NoDup p.

  Lemma start_in_path: forall (g: t) (v1 v2: V) p,
      Path g v1 v2 p -> List.In v1 p.
  Proof.
    intros g v1 v2 p H.
    induction H.
    - simpl. left. reflexivity.
    - simpl. right. assumption.
  Qed.


  Lemma end_in_path: forall (g: t) (v1 v2 : V) p,
      Path g v1 v2 p -> List.In v2 p.
  Proof.
    intros g v1 v2 p H.
    destruct H; left; reflexivity.
  Qed.

  Lemma path_uncons: forall (g: t) (v1 v2: V) p,
      Path g v1 v2 p -> exists p', p = v2 :: p'.
  Proof.
    intros g v1 v2 p Path_p. dependent destruction Path_p.
    - exists nil. reflexivity.
    - exists vs. reflexivity.
  Qed.

  Lemma path_unsnoc: forall (g: t) (v1 v2: V) p,
      Path g v1 v2 p -> exists p', p = p' ++ [v1].
  Proof.
    intros g v1 v2 p. revert v1 v2.
    induction p as [| h t IH]; intros v1 v2 Path_p; dependent destruction Path_p.
    - exists nil. reflexivity.
    - specialize (IH _ _ Path_p) as (p'&->).
      exists (h :: p'). reflexivity.
  Qed.


  Lemma path_excise: forall g v1 v2 l1 a l2, Path g v1 v2 (l1 ++ (a :: l2)) ->
                               Path g a v2 (l1 ++ [a]) /\ Path g v1 a (a :: l2).
  Proof.
    intros g v1 v2 l1 a l2 P; dependent induction P; rename x into Eq.
    - pose proof Eq as Eq'.
      destruct l1; destruct l2;
        apply f_equal with (f := @List.length _) in Eq';
        rewrite -> List.app_length in Eq';
        cbn in *; try lia; clear Eq'.
      injection Eq as <-.
      split; constructor.
    - assert ((exists l1', l1 = v3 :: l1') \/ (l1 = nil /\ v3 = a)) as Cases. {
        clear -Eq.
        destruct l1 as [| h l1' ]; cbn in Eq.
        * injection Eq as -> ->.
          right. split; reflexivity.
        * injection Eq as -> ->.
          left. exists l1'. f_equal.
      }
      destruct Cases as [[l1' ->] | (-> & ->) ].
      + cbn in Eq. injection Eq as Eq. specialize IHP with (1 := Eq) as [Path_l Path_r].
        split; [|assumption].
        apply path_cons with (v2 := v2); assumption.
      + cbn in Eq |- *; injection Eq as ->.
        split; [constructor|].
        apply path_cons with (v2 := v2); assumption.
  Qed.

  Lemma simple_singleton: forall g v, SimplePath g v v [v].
  Proof.
    intros g v.
    split. - constructor. - constructor; [easy|constructor].
  Qed.

  Lemma simple_cons: forall g v1 v2 v3 p, SimplePath g v1 v2 p -> ~List.In v3 p -> Edge g v2 v3  -> SimplePath g v1 v3 (v3 :: p).
  Proof.
    intros g v1 v2 v3 p [Path_p Simple_p] Edge_v2_v3 NIn_v3_p.
    split.
    - apply path_cons with (v2 := v2); assumption.
    - apply List.NoDup_cons; assumption.
  Qed.

  Lemma simple_excise: forall g v1 v2 l1 a l2,
      SimplePath g v1 v2 (l1 ++ (a :: l2)) ->
      SimplePath g a v2 (l1 ++ [a]) /\ SimplePath g v1 a (a :: l2).
  Proof.
    intros g v1 v2 l1 a l2 [Path_p NoDup_p].
    apply path_excise in Path_p as [Path_l1 Path_l2].
    pose proof (List.NoDup_remove_2 _ _ _ NoDup_p) as NotIn_a.
    split.
    - split; [assumption|].
      apply Util.not_in_app_l in NotIn_a.
      pose proof (List.Add_app a l1 []) as Add_a.
      rewrite -> (List.NoDup_Add Add_a).
      rewrite -> List.app_nil_r. split; [|assumption].
      apply List.NoDup_app_remove_r with (1 := NoDup_p).
    - split; [assumption|].
      apply List.NoDup_app_remove_l with (1 := NoDup_p).
  Qed.

  Lemma simple_path_exists:
    forall (g: G.t) (v1 v2: V) (p: list V),
      Path g v1 v2 p ->
      exists s,
        (* (forall u, List.In u p <-> List.In u s) /\ *)
        SimplePath g v1 v2 s.
  Proof.
    intros g v1 v2 p Path_p.
    dependent induction Path_p.
    - exists [v]. apply simple_singleton.
    - destruct IHPath_p as (s & Path_s).  (* Path_s & Simple_s*)
      pose proof (List.in_dec veq v3 s) as [In_a_s | NotIn_a_s].
      + apply List.in_split in In_a_s as (l1 & l2 & ->).
        apply simple_excise in Path_s as [_ ?].
        exists (v3 :: l2). assumption.
      + exists (v3 :: s). apply simple_cons with (v2 := v2); assumption.
  Qed.


End PGraphPaths.

Module Type Graph.
  Include PGraph.
  Parameter Inline edge: t -> V -> V -> bool.
  Parameter Inline contains: t -> V -> bool.
  
  Parameter Inline successors: t -> V -> list V.
    
  Axiom Inline edge_spec: forall t v1 v2, Bool.reflect (Edge t v1 v2) (edge t v1 v2).
  Axiom Inline successors_spec: forall t v1 v2, List.In v2 (successors t v1) <-> Edge t v1 v2.
  Axiom Inline contains_spec: forall t v, Bool.reflect (Contains t v) (contains t v).
End Graph.

Module Type IsFiniteGraph (Import G: Graph).
  Parameter Inline vertices: t -> list V.
  Axiom Inline vertices_spec: forall t v, List.In v (vertices t) <-> Contains t v.
End IsFiniteGraph.

Module Type FiniteGraph := Graph <+ IsFiniteGraph.
