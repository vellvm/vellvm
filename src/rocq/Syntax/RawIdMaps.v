(* begin hide *)
From Stdlib Require Import
  FSets.FMapAVL
  FMapFacts.

From ExtLib Require Import
  Structures.Maps.

From Vellvm Require Import
  Syntax.LLVMAst
  Syntax.AstLib
  Numeric.Rocqlib.
(* end hide *)

(** * Efficient maps keyed by [raw_id]
    AVL maps over [raw_id], used for the local and global environments
    ([Handlers.Local.local_env], [Handlers.Global.global_env]) in place of
    association lists, whose linear lookups made environment accesses a
    quadratic cost center (see [perf/README.md], [perf/locals-chain.ll]).

    The handlers access their environment exclusively through ExtLib's
    [Map] typeclass, so we expose the AVL map as a [Map] instance and the
    swap is transparent to them. [IntMaps] plays the same role for
    [Z]-keyed maps in the memory model.
 *)

Module RM := FMapAVL.Make(RawIDOrd).
Module RMF := FMapFacts.WProperties_fun(RawIDOrd)(RM).

(* Polymorphic type of maps indexed by [raw_id] *)
Definition rmap := RM.t.

#[global] Instance Map_rmap {V} : Map raw_id V (rmap V) :=
  { empty := @RM.empty V
  ; add := @RM.add V
  ; remove := @RM.remove V
  ; lookup := @RM.find V
  (* eta-expanded so the extracted record is a syntactic value: a partial
     application here trips OCaml's value restriction and weakens the type *)
  ; union := fun m1 m2 =>
               RM.map2 (fun mx my => match mx with Some x => Some x | None => my end) m1 m2
  }.

(* Sorted list of the bindings, for consumers that need to enumerate the
   environment (e.g. the OCaml debugger's locals/globals printing). *)
Definition rmap_to_list {V} (m : rmap V) : list (raw_id * V) := RM.elements m.

#[local] Coercion is_true : bool >-> Sortclass.

Definition rid_member {V} k (m : rmap V) := RM.mem k m.
Definition rid_lookup {V} k (m : rmap V) := RM.find k m.

(** Bridges [rid_lookup] with ExtLib's generic [Maps.lookup] (the spelling
    that appears in [handle_global]/[handle_local]'s own definitions,
    [Handlers/Global.v]/[Handlers/Local.v]) — the two are convertible
    ([Maps.lookup]'s [Map_rmap] instance projects to exactly [RM.find]) but
    not syntactically identical, so callers that need to relate a goal
    built from [Maps.lookup] to a fact established via [rid_lookup] should
    [rewrite] with this lemma rather than re-elaborate the equality inline
    (a fresh [replace ... by reflexivity] can leave the [Map] instance
    unresolved depending on the surrounding proof state). *)
Lemma Maps_lookup_rid_lookup {V} k (m : rmap V) : Maps.lookup k m = rid_lookup k m.
Proof. reflexivity. Qed.

(** Heterogeneous relation on [rmap]s lifting a relation on values: same key
    set, and related values at every shared key. Mirrors [IM_Refine]
    ([Utils/IntMaps.v]) for the [Z]-keyed memory maps — same shape, [raw_id]
    keys instead of [Z], no [remove]/[next_key] corollaries since
    [LocalE]/[GlobalE] ([LLVMEvents.v:59-68]) only ever [Write]/[Read]. *)
Definition RM_Refine {a b} (R : a -> b -> Prop) : rmap a -> rmap b -> Prop :=
  fun m m' =>
    (forall k, rid_member k m <-> rid_member k m') /\
      (forall k e e', rid_lookup k m = Some e -> rid_lookup k m' = Some e' -> R e e').

Lemma RM_Refine_empty :
  forall {R1 R2} (R1R2 : R1 -> R2 -> Prop),
    RM_Refine R1R2 (RM.empty R1) (RM.empty R2).
Proof.
  intros R1 R2 R1R2.
  split.
  - intros k; unfold rid_member.
    split; intro H; apply RMF.F.mem_in_iff in H; apply RMF.F.empty_in_iff in H; contradiction.
  - intros k e e' L1 L2; unfold rid_lookup in L1.
    rewrite RMF.F.empty_o in L1; discriminate.
Qed.

Lemma RM_Refine_add :
  forall {R1 R2} (R1R2 : R1 -> R2 -> Prop) m1 m2 k x y
    (REF : RM_Refine R1R2 m1 m2)
    (RXY : R1R2 x y),
    RM_Refine R1R2 (RM.add k x m1) (RM.add k y m2).
Proof.
  intros R1 R2 R1R2 m1 m2 k x y [DOM VAL] RXY.
  assert (DOM' : forall k0, RM.In k0 m1 <-> RM.In k0 m2).
  { intros k0; unfold rid_member in DOM.
    split; intro H.
    - apply RMF.F.mem_in_iff, DOM, RMF.F.mem_in_iff; exact H.
    - apply RMF.F.mem_in_iff, DOM, RMF.F.mem_in_iff; exact H. }
  split.
  - intros k0; unfold rid_member.
    split; intro H;
      apply RMF.F.mem_in_iff, RMF.F.add_in_iff;
      apply RMF.F.mem_in_iff, RMF.F.add_in_iff in H;
      destruct H as [->|H]; auto;
      right; apply DOM'; exact H.
  - intros k0 e e' L L'; unfold rid_lookup in L, L'.
    destruct (RawIDOrd.eq_dec k k0) as [Heq|Hneq].
    + subst k0. rewrite RMF.F.add_eq_o in L, L' by reflexivity.
      injection L as <-; injection L' as <-; auto.
    + rewrite RMF.F.add_neq_o in L, L' by auto.
      eapply VAL; eauto.
Qed.

Lemma RM_Refine_lookup :
  forall {R1 R2} (R1R2 : R1 -> R2 -> Prop) m1 m2
    (REF : RM_Refine R1R2 m1 m2) k,
    option_rel R1R2 (rid_lookup k m1) (rid_lookup k m2).
Proof.
  intros R1 R2 R1R2 m1 m2 [DOM VAL] k.
  destruct (rid_lookup k m1) as [e|] eqn:E1; destruct (rid_lookup k m2) as [e'|] eqn:E2.
  - constructor; eapply VAL; eauto.
  - exfalso.
    assert (IN1 : RM.In k m1) by (apply RMF.F.in_find_iff; unfold rid_lookup in E1; congruence).
    assert (MEM1 : rid_member k m1) by (apply RMF.F.mem_in_iff; auto).
    apply DOM in MEM1.
    assert (IN2 : RM.In k m2) by (apply RMF.F.mem_in_iff; auto).
    apply RMF.F.in_find_iff in IN2; unfold rid_lookup in E2; congruence.
  - exfalso.
    assert (IN2 : RM.In k m2) by (apply RMF.F.in_find_iff; unfold rid_lookup in E2; congruence).
    assert (MEM2 : rid_member k m2) by (apply RMF.F.mem_in_iff; auto).
    apply DOM in MEM2.
    assert (IN1 : RM.In k m1) by (apply RMF.F.mem_in_iff; auto).
    apply RMF.F.in_find_iff in IN1; unfold rid_lookup in E1; congruence.
  - constructor.
Qed.

#[global] Instance MapOk_rmap {V} : MapOk (@eq raw_id) (@Map_rmap V).
Proof.
  refine {| mapsto := fun k v (m : rmap V) => RM.MapsTo k v m |}; cbn.
  - intros k v IN.
    apply RMF.F.empty_mapsto_iff in IN; exact IN.
  - intros k v m.
    symmetry; apply RMF.F.find_mapsto_iff.
  - intros m k v.
    apply RM.add_1; reflexivity.
  - intros m k v k' NEQ v'.
    symmetry; apply RMF.F.add_neq_mapsto_iff; auto.
  - intros m k v IN.
    apply RMF.F.remove_mapsto_iff in IN.
    destruct IN as [NEQ _]; apply NEQ; reflexivity.
  - intros m k k' NEQ v'.
    symmetry; apply RMF.F.remove_neq_mapsto_iff; auto.
Defined.
