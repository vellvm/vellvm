Require Import List Equalities Orders RelationClasses Lia.
Require Import FSets.

(* (Bounded) (join) semi-lattice *)

Definition is_glb {T: Type} (le: T -> T -> Prop) (glb x y: T) :=
  le glb x /\ le glb y /\
    forall z, le z x -> le z y -> le z glb.

Module Type EqType.
  Parameter t: Type.
  Parameter eq: t -> t -> Prop.
  #[global] Declare Instance eq_equiv : Equivalence eq.
End EqType.

(* Module Type order_SemiLattice (Import Eq: EqType). *)
(*   (* Signature *) *)
(*   (* Parameter t: Type. *) *)
(*   Parameter Inline bot : t. *)

(*   (* Parameter eq: t -> t -> Prop. *) *)
(*   Parameter le: t -> t -> Prop. *)
  
(*   (* (Local) notations *) *)
(*   Infix "==" := eq (at level 70, no associativity). *)
(*   Infix "<=" := le (at level 70, no associativity). *)
(*   Notation "⊥" := bot (at level 0). *)
  
(*   (* Characterisation *) *)
(*   (* #[global] Declare Instance eq_equiv : Equivalence eq. *) *)
(*   #[global] Declare Instance le_preorder : PreOrder le. *)
(*   #[global] Declare Instance le_poset : PartialOrder eq le. *)

(*   Axiom ord_bot: forall x, ⊥ <= x. *)
(*   Axiom ord_glbExists: forall x y, exists glb, is_glb le glb x y. *)
(* End order_SemiLattice. *)

(* Module Type algebraic_SemiLattice (Import Eq: EqType). *)
(*   (* Signature *) *)
(*   (* Parameter t: Type. *) *)
(*   Parameter Inline bot : t. *)
(*   Parameter join : t -> t -> t. *)

(*   (* Parameter eq: t -> t -> Prop. *) *)
  
(*   (* (Local) notations *) *)
(*   Infix "==" := eq (at level 70, no associativity). *)
(*   Infix "∧" := join (at level 50, left associativity). *)
(*   Notation "⊥" := bot (at level 0). *)
  
(*   (* Characterisation *) *)
(*   (* #[global] Declare Instance eq_equiv : Equivalence eq. *) *)
  
(*   Axiom alg_botRight : forall x, x ∧ ⊥ == x. *)
(*   Axiom alg_assoc: forall x y z, (x ∧ y) ∧ z == x ∧ (y ∧ z). *)
(*   Axiom alg_comm: forall x y, x ∧ y == y ∧ x. *)
(*   Axiom alg_idem: forall x, x ∧ x == x. *)
(* End algebraic_SemiLattice. *)

Module Type SemiLattice.
  (* Signature *)
  Parameter t: Type.
  Parameter top : t.
  Parameter meet : t -> t -> t.

  Parameter eq: t -> t -> Prop.
  Parameter le: t -> t -> Prop.

  Parameter eq_dec: forall (l r: t), {eq l r} + {~eq l r}.
  
  (* Notations *)
  Infix "==" := eq (at level 70, no associativity).
  Infix "<=" := le (at level 70, no associativity).
  Infix "∧" := meet (at level 50, left associativity).
  Notation "⊤" := top (at level 0).

  (* Algebraic characterisation *)
  Axiom alg_eqCompatLeft: forall x x' y, x == x' -> x ∧ y == x' ∧ y.
  Axiom alg_eqCompatRight: forall x y y', y == y' -> x ∧ y == x ∧ y'.
  
  Axiom alg_topRight : forall x, x ∧ ⊤ == x.
  Axiom alg_assoc: forall x y z, (x ∧ y) ∧ z == x ∧ (y ∧ z).
  Axiom alg_comm: forall x y, x ∧ y == y ∧ x.
  Axiom alg_idem: forall x, x ∧ x == x.

  (* Order-theoretic characterisation *)
  #[global] Declare Instance eq_equiv : Equivalence eq.
  #[global] Declare Instance le_preorder : PreOrder le.
  #[global] Declare Instance le_poset : PartialOrder eq le.

  Axiom ord_top: forall x, x <= ⊤.
  Axiom ord_glbExists: forall x y, exists glb, is_glb le glb x y.

  (* Compatibility of characterisations *)
  Axiom characterisations_compat: forall x y, x <= y <-> x == x ∧ y.
End SemiLattice.

Module SemiLatticeFacts (Import SL: SemiLattice).

  (* Relations & morphisms *)
  (* Add Relation t eq *)
  (*     reflexivity proved by Equivalence_Reflexive *)
  (*     symmetry proved by Equivalence_Symmetric *)
  (*     transitivity proved by Equivalence_Transitive *)
  (*     as sl_eq_rel. *)
  (* Add Relation t le *)
  (*     reflexivity proved by PreOrder_Reflexive *)
  (*     transitivity proved by PreOrder_Transitive *)
  (*     as sl_le_rel. *)

  Add Morphism meet with signature @eq ==> @eq ==> @eq as meet_morphism.
  Proof.
    intros x x' Eq_x_x' y y' Eq_y_y'.
    apply alg_eqCompatLeft with (y := y) in Eq_x_x' as ->.
    apply alg_eqCompatRight with (x := x') in Eq_y_y' as <-.
    reflexivity.
  Qed.

  (* Add Morphism le with signature @eq ==> @eq ==> iff as le_morphism. *)
  (* Proof. *)
  (*   intros x x' Eq_x_x' y y' Eq_y_y'. *)
  (*   rewrite -> Eq_x_x', -> Eq_y_y'.  *)
  (*   split; intros; assumption. *)
  (* Qed. *)
  
  Lemma meet_le: forall x x' y y', x <= x' -> y <= y' -> x ∧ y <= x' ∧ y'.
  Proof.
    intros x x' y y' Le_x_x' Le_y_y'.
    rewrite -> characterisations_compat in *.
    rewrite -> (alg_assoc x y _), <- (alg_assoc y x' y') , -> (alg_comm y x'), -> (alg_assoc x' y y'), <- (alg_assoc x x' _).
    rewrite <- Le_x_x', <- Le_y_y'.
    reflexivity.
  Qed.

  Lemma glb_uniqueness: forall x y glb glb', is_glb le glb x y -> is_glb le glb' x y -> glb == glb'.
  Proof.
    unfold is_glb. intros x y glb glb' (Le_glb_x & Le_glb_y & is_glb_glb) (Le_glb'_x & Le_glb'_y & is_glb_glb').
    specialize (is_glb_glb glb' ltac:(assumption) ltac:(assumption)).
    specialize (is_glb_glb' glb ltac:(assumption) ltac:(assumption)).
    apply antisymmetry; assumption.
  Qed.
  
  Lemma meet_is_glb: forall x y, is_glb le (x ∧ y) x y.
  Proof.
    intros x y. unfold is_glb.
    split; [| split].
    - rewrite -> characterisations_compat. rewrite -> (alg_comm x y). rewrite -> alg_assoc. rewrite -> alg_idem. reflexivity.
    - rewrite -> characterisations_compat. rewrite -> alg_assoc. rewrite -> alg_idem. reflexivity.
    - intros z Le_z_x Le_z_y. rewrite <- (alg_idem z). apply meet_le; assumption.
  Qed.
  
  Lemma le_meet_l : forall x y, x ∧ y <= x.
  Proof. intros. rewrite -> characterisations_compat. rewrite (alg_comm x y). rewrite -> (alg_assoc). rewrite -> (alg_idem). reflexivity. Qed.
  
  Lemma le_meet_r : forall x y, x ∧ y <= y.
  Proof. intros. rewrite -> (alg_comm). apply le_meet_l. Qed.

End SemiLatticeFacts.
(* TODO: split into alg_SL and order_SL *)
(* TODO: define lattice + injections (2) into semi lattices *)

(* BoundedSets: sets with a special value representing the entire universe.
   - Bot: The empty set;
   - Top: The universal set;
   - Meet: Set intersection;
   - Join: Set union;
   - Preorder: Set inclusion (i.e. subset).

   Note that the "bounded" in the name refers to the fact that the lattice is bounded,
   not to a bound on the size of the sets (they can be arbitratily large).
 *)
Module BoundedSet (Import S: FSetInterface.WS) <: SemiLattice.
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

  (* Some props *)
  Lemma empty_iff: forall v, In v empty <-> False.
  Proof. intros v. cbn. apply SFacts.empty_iff. Qed.

  Lemma singleton_iff: forall v v', In v (singleton v') <-> S.E.eq v' v.
  Proof. cbn. intros. apply SFacts.singleton_iff. Qed.

  Lemma Equal_refl: forall t, Equal t t.
  Proof. intros []; cbn. - reflexivity. - constructor. Qed.

  Lemma Equal_symm: forall t t', Equal t t' -> Equal t' t.
  Proof. intros [] []; cbn; firstorder. Qed.

  Lemma Equal_trans: forall t0 t1 t2, Equal t0 t1 -> Equal t1 t2 -> Equal t0 t2.
  Proof. intros [] [] []; firstorder. Qed.

  Lemma Subset_spec: forall a s s', In a s -> Subset s s' -> In a s'.
  Proof. intros a s s' H H'. destruct s, s'; [|trivial|contradiction|trivial]. apply H'. apply H. Qed.

  Lemma Subset_refl: forall s, Subset s s.
  Proof. intros []; cbn; firstorder. Qed.

  Lemma Subset_trans: forall s0 s1 s2, Subset s0 s1 -> Subset s1 s2 -> Subset s0 s2.
  Proof. intros [] [] []; firstorder. Qed.

  Lemma In_union: forall s t0 t1, In s (union t0 t1) -> In s t0 \/ In s t1.
  Proof. intros s [] [] In; firstorder. cbn in *. apply S.union_1. assumption. Qed.

  Add Relation t Equal
      reflexivity proved by Equal_refl
      symmetry proved by Equal_symm
      transitivity proved by Equal_trans
      as Equal_equiv.

  Add Relation t Subset
    reflexivity proved by Subset_refl
    transitivity proved by Subset_trans
      as Subset_order.

  Add Morphism In
      with signature (S.E.eq) ==> (Equal) ==> iff as In_eq_mor.
  Proof.
    intros e e' Eq_e_e' t t' Eq_t_t'.
    destruct t, t'; cbn in *; firstorder.
    - rewrite <- Eq_t_t', <- Eq_e_e'. assumption.
    - rewrite -> Eq_t_t', -> Eq_e_e'. assumption.
  Qed.

  Add Morphism Subset
      with signature Equal ==> Equal ==> iff as Subset_eq_mor.
  Proof. intros [] [] Eq0 [] [] Eq1; firstorder. Qed.

  Add Morphism In
      with signature S.E.eq ==> Subset ==> impl as In_Subset_mor.
  Proof.
    intros e e' Eq_e_e' t t' Sub_t_t'.
    destruct t, t'; cbn in *; firstorder.
    intros ?. apply Sub_t_t'. rewrite <- Eq_e_e'. assumption.
  Qed.

  (* Lattice signature.*)
  Definition bot: t := empty.
  Definition top: t := universe.

  Definition meet: t -> t -> t := intersection. 

  Definition eq := Equal.
  Definition le := Subset.

  Definition eq_dec : forall x y, {eq x y} + {~eq x y}.
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


  (* Notations *)
  Infix "==" := eq (at level 70, no associativity).
  Infix "<=" := le (at level 70, no associativity).
  Infix "∧" := meet (at level 50, left associativity).
  Notation "⊥" := bot (at level 0).
  Notation "⊤" := top (at level 0).

  (* Algebraic characterisation *)
  Lemma alg_eqCompatLeft: forall x x' y, x == x' -> x ∧ y == x' ∧ y.
  Proof. intros [x|] [x'|] [y|] Eq_x_x'; try easy. cbn in *. rewrite -> Eq_x_x'. reflexivity. Qed.
    
  Lemma alg_eqCompatRight: forall x y y', y == y' -> x ∧ y == x ∧ y'.
  Proof. intros [x|] [y|] [y'|] Eq_y_y'; try easy. cbn in *. rewrite -> Eq_y_y'. reflexivity. Qed.
  
  Lemma alg_topRight: forall x, x ∧ ⊤ == x.
  Proof. intros []; easy. Qed.

  Lemma alg_botRight: forall x, x ∧ ⊥ == ⊥.
  Proof.
    intros []; try easy. cbn. unfold bot, empty. f_equal.
    intros x; rewrite -> inter_iff.
    rewrite -> SFacts.empty_iff. easy.
  Qed.
  
  Lemma alg_assoc: forall x y z, (x ∧ y) ∧ z == x ∧ (y ∧ z).
  Proof. intros [] [] []; try easy. cbn. intros x. repeat rewrite -> inter_iff. easy. Qed.
  
  Lemma alg_comm: forall x y, x ∧ y == y ∧ x.
  Proof. intros [] []; try easy. cbn. intros x. repeat rewrite -> inter_iff. easy. Qed.
  
  Lemma alg_idem: forall x, x ∧ x == x.
  Proof. intros []; try easy. cbn. intros x. rewrite -> inter_iff. easy. Qed.

  (* Order-theoretic characterisation *)
  #[global] Instance eq_equiv : Equivalence eq.
  Proof.
    constructor.
    -  intros []; cbn. + reflexivity. + constructor.
    - intros [] []; cbn; intros; easy.
    - intros [] [] []; cbn; intros; try easy. etransitivity; eassumption.
  Qed.

  #[global] Instance le_preorder : PreOrder le.
  Proof.
    constructor.
    - intros []; cbn. + reflexivity. + constructor.
    - intros [] [] []; cbn; intros; try easy. etransitivity; eassumption.
  Qed.

  #[global] Instance le_poset : PartialOrder eq le.
  Proof.
    intros x y. constructor.
    - destruct x, y; intros H; cbn in *; try easy.
      rewrite -> H.
      split; reflexivity.
    - destruct x, y; intros [Le_x_y Le_y_x]; cbn in *; try easy.
      intros x; split. + apply Le_x_y. + apply Le_y_x.
  Qed.

  (* Compatibility of characterisations *)
  Lemma characterisations_compat: forall x y, x <= y <-> x == x ∧ y.
  Proof.
    intros x y; split; destruct x, y; try easy; cbn.
    - intros H x. rewrite -> inter_iff.
      split; [| intros [? _]; assumption].
      intros In_x. split; [assumption|].
      rewrite -> H in In_x. assumption.
    - intros -> x. rewrite -> inter_iff.
      intros [_ ?]. assumption.
  Qed.

  (* Order-theoretic characterisation (cont'd) *)
  Lemma ord_bot: forall x, ⊥ <= x.
  Proof. intros x. rewrite -> characterisations_compat. rewrite -> alg_comm. symmetry. apply alg_botRight. Qed.

  Lemma ord_top: forall x, x <= ⊤.
  Proof. intros x. rewrite -> characterisations_compat. symmetry. apply alg_topRight. Qed.
  
  Lemma ord_glbExists: forall x y, exists glb, is_glb le glb x y.
  Proof.
    intros x y; exists (x ∧ y).
    (* The missing parts are actual lemmas in SemiLatticeFacts *)
    unfold is_glb. split; [|split].
    - admit.
    - admit.
    - intros z Le_z_x Le_z_y.
      rewrite <- (alg_idem z).
      admit.
  Admitted.
End BoundedSet.
