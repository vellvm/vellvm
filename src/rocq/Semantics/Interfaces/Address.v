(* begin hide *)
From Stdlib Require Import OrderedType OrderedTypeEx.

From Vellvm Require Import
  Utilities
  DynamicTypes
  EOU
  Interfaces.Provenance
  Interfaces.Sizeof.

(* end hide *)

(** * Signature for addresses
    The semantics is functorized by the notion of addresses manipulated by the
    memory model. This allows us to easily plug different memory models.
    This module is concretely implemented currently in [Handlers/Memory.v].
 *)
Class Address {P : Provenance} :=
  {
    addr : Set;
    null : addr;

    (* Coq's logical equality on the pointer data type *)
    eq_dec_addr : forall (a b : addr), {a = b} + {a <> b};
    (* different_addrs : forall (a : addr), exists (b : addr), a <> b; *)

    (* Access the provenance for an address *)
    address_provenance : addr -> prov;

    (* Debug *)
    show_addr : addr -> string;
  }.

(* We pull this into a separate class to allow for a generic
   implementation parametirized by any Address supporting PI.
   Could be merged into Address if we don't care about that.
 *)
Class Overlaps {P : Provenance} {A : @Address P} :=
  {
      (** Do two memory regions overlap each other?
        - *a1* and *a2* are addresses to the start of each region.
        - *sz1* and *sz2* are the sizes of the two regions. *)
    overlaps : addr -> N -> addr -> N -> bool ;
}.

(* TODO: Merge in the Address class, or keep it separate? *)
(* TODO: Is it not over-engineering to allow margin for [ptr_to_int]
   to be anything but the one from iptr?
 *)
Class PI {P : Provenance} {A : @Address P} :=
  {
    ptr_to_int : addr -> Z;

    int_to_ptr : Z -> prov -> EOU addr;
  }.

Class PITheory {P : Provenance} {A : @Address P} {P2I : @PI P A} :=
  {
    int_to_ptr_provenance :
    forall (x : Z) (p : prov) (a : addr),
      int_to_ptr x p = ret a ->
      address_provenance a = p;

    int_to_ptr_ptr_to_int :
    forall (a : addr) (p : prov),
      address_provenance a = p ->
      int_to_ptr (ptr_to_int a) p = ret a;

    int_to_ptr_ptr_to_int_exists :
    forall (a : addr) (p : prov),
    exists a',
      int_to_ptr (ptr_to_int a) p = ret a' /\
        ptr_to_int a' = ptr_to_int a /\
        address_provenance a' = p;

    ptr_to_int_int_to_ptr :
    forall (x : Z) (p : prov) (a : addr),
      int_to_ptr x p = ret a ->
      ptr_to_int a = x;
  }.

Open Scope Z.

Instance overlaps_ptoi {P : Provenance} {Ad : @Address P} {PI : @PI P Ad} :
  @Overlaps P Ad :=
  {|
    overlaps (a1 : addr) (sz1 : N) (a2 : addr) (sz2 : N) :=
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
  Context {P : Provenance} {Ad : @Address P} {Si : Sizeof} {O : @Overlaps P Ad}.

  (** Checks if two regions of memory overlap each other. The types
   *τ1* and *τ2* are used to determine the size of the two memory
        regions.
   *)
  Definition overlaps_dtyp (a1 : addr) (τ1 : dtyp) (a2 : addr) (τ2 : dtyp)
    : bool :=
    overlaps a1 (sizeof_dtyp τ1) a2 (sizeof_dtyp τ2).

  (** Make sure that two regions of memory do not overlap *)
  Definition no_overlap (a1 : addr) (sz1 : N) (a2 : addr) (sz2 : N) : bool
    := negb (overlaps a1 sz1 a2 sz2).

  (** Same as *no_overlap*, but using *dtyp*s *τ1* and *τ2* to
        determine the size of the regions. *)
  Definition no_overlap_dtyp (a1 : addr) (τ1 : dtyp) (a2 : addr) (τ2 : dtyp)
    : bool := negb (overlaps_dtyp a1 τ1 a2 τ2).

End Overlap.

