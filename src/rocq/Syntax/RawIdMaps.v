(* begin hide *)
From Stdlib Require Import
  FSets.FMapAVL
  FMapFacts.

From ExtLib Require Import
  Structures.Maps.

From Vellvm Require Import
  Syntax.LLVMAst
  Syntax.AstLib.
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
