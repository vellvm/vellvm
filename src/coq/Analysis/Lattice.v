Require Import List Equalities Orders RelationClasses Lia.
Require Import FSets.

From MathClasses Require interfaces.abstract_algebra interfaces.orders orders.lattices.
Import (hints) interfaces.abstract_algebra interfaces.orders.
From MathClasses Require Import  interfaces.canonical_names.
Local Open Scope mc_scope.

Module Lattices.

  Module Pointwise.
    (* Marker class enabling the pointwise lattice. *)
    Class Pointwise (T L: Type) `{Lattice_L: @orders.LatticeOrder L Equiv_L Le_L Meet_L Join_L} := {}.

    (* We want these instances to depent artifially on Pointwise T L, so Context cannot be used. *)
    Instance meet `{Pointwise T L}: Meet (T -> L) := fun l r => (fun x => l x ⊓ r x).
    Instance join `{Pointwise T L}: Join (T -> L) := fun l r => (fun x => l x ⊔ r x).
    Instance equiv `{Pointwise T L}: Equiv (T -> L) := fun l r => ∀ x, l x = r x.
    Instance le `{Pointwise T L}: Le (T -> L) := fun l r => forall x, l x ≤ r x.

    Section Lattice.
       Context `{@Pointwise T L Equiv_L Le_L Meet_L Join_L Lattice_L}.

       (* Some notations for the underlying lattice. *)
       Infix "=ₗ" := (Equiv_L) (at level 70).
       Infix "≤ₗ" := (Le_L) (at level 70).
       Infix "⊓ₗ" := (Meet_L) (at level 50).
       Infix "⊔ₗ" := (Join_L) (at level 50).

       (* A's setoid instance is not registered as a subclass. *)
       Local Instance setoid_L: abstract_algebra.Setoid L.
       Proof. apply orders.po_setoid. Qed.

       (* Most of the following proofs will follow from the same mechanical steps:
       - Unfold the definitions down to the lattice operations on L;
       - Specialize all assumptions (e.g. f ≤ g) on the specific input under consideration (f x ≤ g x).
        *)

       Ltac simplifier :=
         repeat (
             intros ?
             || constructor
             || (unfold "=", "≤", "⊓", "⊔", meet, join in * )
             || (lazymatch goal with
                | [H: equiv _ _, x: T |- _] => specialize (H x)
                | [H: le _ _, x: T |- _] => specialize (H x)
                | [|- _ <-> _] => split
                end)).

       (* By no means complete. *)
       Ltac solver := try solve [
                          repeat (
                              lazymatch goal with
                              | [|- ?x =ₗ ?x] => reflexivity
                              | [|- ?x ≤ₗ ?x] => reflexivity
                              | [H: ?T |- ?T] => exact H
                              | [H: _ =ₗ  _ |- _] => (rewrite -> H + rewrite <- H); clear H
                              | [H:  _ ≤ₗ _ |- _] => (rewrite -> H + rewrite <- H); clear H
                              end)].

       Lemma po: orders.PartialOrder le.
       Proof.
         simplifier; solver.
         - (* Only antisymmetry is left. *)
           apply antisymmetry with (R := Le_L).
           + eauto with typeclass_instances.
           + assumption.
           + assumption.
       Qed.

       #[export]
       Instance mapped_lattice: orders.LatticeOrder le.
       Proof.
         constructor; constructor; try exact po.
         - simplifier. apply orders.meet_lb_l.
         - simplifier. apply orders.meet_lb_r.
         - simplifier. apply orders.meet_glb; assumption.
         - simplifier. apply orders.join_ub_l.
         - simplifier. apply orders.join_ub_r.
         - simplifier. apply orders.join_lub; assumption.
       Qed.

    End Lattice.
  End Pointwise.
  Export Pointwise(Pointwise).

  (* BoundedSets: sets with a special value representing the entire universe.
   - Bot: The empty set;
   - Top: The universal set;
   - Meet: Set intersection;
   - Join: Set union;
   - Preorder: Set inclusion (i.e. subset).

   Note that the "bounded" in the name refers to the fact that the lattice is bounded,
   not to a bound on the size of the sets (they can be arbitratily large).
   *)
  Module BoundedSet (Import S: FSetInterface.WS).
    Module Import SFacts := FSetFacts.WFacts S.

    (* Set signature. *)
    Definition t: Type := option S.t.
    Definition empty: t := Some S.empty.
    Definition universe: t := None.

    Definition intersection (t1 t2: t): t :=
      match t1, t2 with
      | Some s1, Some s2 => Some (S.inter s1 s2)
      | None, Some s | Some s, None => Some s
      | None, None => None
      end.

    Definition union (t1 t2: t) : t :=
      match t1, t2 with
      | Some s1, Some s2 => Some (S.union s1 s2)
      | None, _ | _, None => None
      end.

    Definition singleton (e:S.elt) : t := Some (S.singleton e).

    Definition Equal (t1 t2: t) : Prop :=
      match t1, t2 with
      | Some s1, Some s2 => s1 [=] s2
      | None, None => True
      | _, _ => False
      end.

    Definition Subset (t1 t2: t) : Prop :=
      match t1, t2 with
      | Some s1, Some s2 => s1 [<=] s2
      | _, None => True
      | _, _ => False
      end.

    Definition In (e:S.elt) (t:t) : Prop :=
      match t with
      | Some s => S.In e s
      | None => True
      end.

    Definition eq_dec : forall (x y: t), {Equal x y} + {~Equal x y}.
      refine (fun t1 t2 => match t1, t2 with
                        | Some s1, Some s2 => _
                        | None, None => left _
                        | _, _ => right _
                        end).
      - apply S.eq_dec.
      - intros [].
      - intros [].
      - constructor.
    Defined.

    (* Some props *)
    (* Lemma empty_iff: forall v, In v empty <-> False. *)
    (* Proof. intros v. cbn. apply SFacts.empty_iff. Qed. *)

    (* Lemma singleton_iff: forall v v', In v (singleton v') <-> S.E.eq v' v. *)
    (* Proof. cbn. intros. apply SFacts.singleton_iff. Qed. *)

    (* Lemma Equal_refl: forall t, Equal t t. *)
    (* Proof. intros []; cbn. - reflexivity. - constructor. Qed. *)

    (* Lemma Equal_symm: forall t t', Equal t t' -> Equal t' t. *)
    (* Proof. intros [] []; cbn; firstorder. Qed. *)

    (* Lemma Equal_trans: forall t0 t1 t2, Equal t0 t1 -> Equal t1 t2 -> Equal t0 t2. *)
    (* Proof. intros [] [] []; firstorder. Qed. *)

    (* Lemma Subset_spec: forall a s s', In a s -> Subset s s' -> In a s'. *)
    (* Proof. intros a s s' H H'. destruct s, s'; [|trivial|contradiction|trivial]. apply H'. apply H. Qed. *)

    (* Lemma Subset_refl: forall s, Subset s s. *)
    (* Proof. intros []; cbn; firstorder. Qed. *)

    (* Lemma Subset_trans: forall s0 s1 s2, Subset s0 s1 -> Subset s1 s2 -> Subset s0 s2. *)
    (* Proof. intros [] [] []; firstorder. Qed. *)

    (* Lemma In_union: forall s t0 t1, In s (union t0 t1) -> In s t0 \/ In s t1. *)
    (* Proof. intros s [] [] In; firstorder. cbn in *. apply S.union_1. assumption. Qed. *)

    (* Add Relation t Equal *)
    (*     reflexivity proved by Equal_refl *)
    (*     symmetry proved by Equal_symm *)
    (*     transitivity proved by Equal_trans *)
    (*     as Equal_equiv. *)

    (* Add Relation t Subset *)
    (*   reflexivity proved by Subset_refl *)
    (*   transitivity proved by Subset_trans *)
    (*     as Subset_order. *)

    (* Add Morphism In *)
    (*     with signature (S.E.eq) ==> (Equal) ==> iff as In_eq_mor. *)
    (* Proof. *)
    (*   intros e e' Eq_e_e' t t' Eq_t_t'. *)
    (*   destruct t, t'; cbn in *; firstorder. *)
    (*   - rewrite <- Eq_t_t', <- Eq_e_e'. assumption. *)
    (*   - rewrite -> Eq_t_t', -> Eq_e_e'. assumption. *)
    (* Qed. *)

    (* Add Morphism Subset *)
    (*     with signature Equal ==> Equal ==> iff as Subset_eq_mor. *)
    (* Proof. intros [] [] Eq0 [] [] Eq1; firstorder. Qed. *)

    (* Add Morphism In *)
    (*     with signature S.E.eq ==> Subset ==> impl as In_Subset_mor. *)
    (* Proof. *)
    (*   intros e e' Eq_e_e' t t' Sub_t_t'. *)
    (*   destruct t, t'; cbn in *; firstorder. *)
    (*   intros ?. apply Sub_t_t'. rewrite <- Eq_e_e'. assumption. *)
    (* Qed. *)

    (* Tactic to solve core lattice equations, e.g. x ⊓ y ≤ x  *)
    Local Ltac core_ineq_solver :=
      intros;
      (* Analyse whether the set is universal or regular. *)
      (repeat lazymatch goal with
         | [ s: t |- _ ] => destruct s as [s|]
         end);
      (* Discharge to firstorder if possible universal (typically when one set is universal); reduce o/w. *)
      (try firstorder); cbn;
      (* Split depending on goal.  *)
      lazymatch goal with
      | [|- _ [<=] _] => intros ? ?
      | [|- _ [=] _] => split; intros ? ?
      end;
      (* Get rid of intersection&union.  *)
      (repeat rewrite -> ?SFacts.inter_iff, -> ?SFacts.union_iff in * );
      (* Hope for the best. *)
      firstorder.

    Local Lemma subset_po: @orders.PartialOrder _ Equal Subset.
    Proof.
      constructor.
      * (* (t, Equal) is a setoid. *)
        constructor.
      + (* Equal is reflexive. *)
        intros []; firstorder.
      + (* Equal is symmetric. *)
        intros [] []; firstorder.
      + (* Equal is transitive. *)
        intros [] [] []; firstorder.
        * (* Subset respects Equal  *)
          intros [] [] Eq0 [] [] Eq1; firstorder.
        * (* (t, Subset) form a pre order. *)
          constructor.
      + (* Subset is reflexive. *)
        intros []; firstorder.
      + (* Subset is transitive *)
        intros [] [] []; firstorder.
        * (* Subset is antisymmetric (w.r.t. Equal). *)
          intros [] []; firstorder.
    Qed.

    Instance lattice_order: @orders.LatticeOrder _ Equal Subset intersection union.
    constructor.
    - (* It is an (ordered) meet semi-lattice... *)
      constructor.
      + exact subset_po.
      + core_ineq_solver.
      + core_ineq_solver.
      + core_ineq_solver.
    - (* ... and an (ordered) join semi-lattice. *)
      constructor.
      + exact subset_po.
      + core_ineq_solver.
      + core_ineq_solver.
      + core_ineq_solver.
    Qed.

    Instance bot: Bottom t := empty.
    Instance top: Top t := universe.
  End BoundedSet.
End Lattices.
