(* begin hide *)
From Stdlib Require Import OrderedType OrderedTypeEx.

From Vellvm Require Import
  Utils
  DynamicTypes
  EOU
  Interfaces.Provenance
  Interfaces.Sizeof.

(* end hide *)

(** * Signature for addresses
    The semantics is functorized by the notion of pointers manipulated by the
    memory model. This allows us to easily plug different memory models.
    This module is concretely implemented currently in [Handlers/Memory.v].
 *)
Class Pointer {P : Provenance} :=
  {
    ptr  : Set;
    null : ptr;

    (* Rocq's logical equality on the pointer data type *)
    eq_dec_ptr : forall (a b : ptr), {a = b} + {a <> b};
    (* different_ptrs : forall (a : ptr), exists (b : ptr), a <> b; *)

    (* Access the provenance for an address *)
    ptr_provenance : ptr -> prov;

    (* Debug *)
    show_ptr : ptr -> string;
  }.

(* We pull this into a separate class to allow for a generic
   implementation parametirized by any Pointer supporting PI.
   Could be merged into Pointer if we don't care about that.
 *)
Class Overlaps {P : Provenance} {A : @Pointer P} :=
  {
      (** Do two memory regions overlap each other?
        - *a1* and *a2* are addresses to the start of each region.
        - *sz1* and *sz2* are the sizes of the two regions. *)
    overlaps : ptr -> N -> ptr -> N -> bool ;
}.

(* TODO: Merge in the Pointer class, or keep it separate? *)
(* TODO: Is it not over-engineering to allow margin for [ptr_to_int]
   to be anything but the one from iptr?
 *)
Class PI {P : Provenance} {A : @Pointer P} :=
  {
    ptr_to_int : ptr -> Z;

    int_to_ptr : Z -> prov -> EOU ptr;
  }.

Class PITheory {P : Provenance} {A : @Pointer P} {P2I : @PI P A} :=
  {
    int_to_ptr_provenance :
    forall (x : Z) (p : prov) (a : ptr),
      int_to_ptr x p = ret a ->
      ptr_provenance a = p;

    int_to_ptr_ptr_to_int :
    forall (a : ptr) (p : prov),
      ptr_provenance a = p ->
      int_to_ptr (ptr_to_int a) p = ret a;

    int_to_ptr_ptr_to_int_exists :
    forall (a : ptr) (p : prov),
    exists a',
      int_to_ptr (ptr_to_int a) p = ret a' /\
        ptr_to_int a' = ptr_to_int a /\
        ptr_provenance a' = p;

    ptr_to_int_int_to_ptr :
    forall (x : Z) (p : prov) (a : ptr),
      int_to_ptr x p = ret a ->
      ptr_to_int a = x;
  }.

Open Scope Z.

Instance overlaps_ptoi {P : Provenance} {A : @Pointer P} {PI : @PI P A} :
  @Overlaps P A :=
  {|
    overlaps (a1 : ptr) (sz1 : N) (a2 : ptr) (sz2 : N) :=
      let a1_start := ptr_to_int a1 in
      let a1_end   := ptr_to_int a1 + (Z.of_N sz1) in
      let a2_start := ptr_to_int a2 in
      let a2_end   := ptr_to_int a2 + (Z.of_N sz2) in
      (a1_start <=? (a2_end - 1)) && (a2_start <=? (a1_end - 1))
  |}.     

(* TODO: Where should this kind of theory live?
   It is awkward: it is generic to some extent, but depends on [dtyp].
   Move simply on the Vellvm implementation side?
   Move in the Params file?
 *)
Section Overlap.
  Context {P : Provenance} {A : @Pointer P} {Si : Sizeof} {O : @Overlaps P A}.

  (** Checks if two regions of memory overlap each other. The types
   *τ1* and *τ2* are used to determine the size of the two memory
        regions.
   *)
  Definition overlaps_dtyp (a1 : ptr) (τ1 : dtyp) (a2 : ptr) (τ2 : dtyp)
    : bool :=
    overlaps a1 (sizeof_dtyp τ1) a2 (sizeof_dtyp τ2).

  (** Make sure that two regions of memory do not overlap *)
  Definition no_overlap (a1 : ptr) (sz1 : N) (a2 : ptr) (sz2 : N) : bool
    := negb (overlaps a1 sz1 a2 sz2).

  (** Same as *no_overlap*, but using *dtyp*s *τ1* and *τ2* to
        determine the size of the regions. *)
  Definition no_overlap_dtyp (a1 : ptr) (τ1 : dtyp) (a2 : ptr) (τ2 : dtyp)
    : bool := negb (overlaps_dtyp a1 τ1 a2 τ2).

End Overlap.

