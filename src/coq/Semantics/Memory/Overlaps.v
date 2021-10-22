Require Import ZArith.

Require Import Vellvm.Semantics.MemoryAddress.
Require Import Vellvm.Semantics.Memory.Sizeof.
From Vellvm Require Import DynamicTypes.

(* Define overlapping of memory addresses. *)
Module Overlaps(Addr:MemoryAddress.ADDRESS) (PTOI:PTOI(Addr)) (Size:Sizeof).
  Import Addr.
  Import PTOI.
  Import Size.

  Local Open Scope Z.

  (** Do two memory regions overlap each other?

        - *a1* and *a2* are addresses to the start of each region.
        - *sz1* and *sz2* are the sizes of the two regions.

        Proposition should hold whenever the two regions overlap each
        other. *)
  Definition overlaps (a1 : addr) (sz1 : Z) (a2 : addr) (sz2 : Z) : Prop :=
    let a1_start := ptr_to_int a1 in
    let a1_end   := ptr_to_int a1 + sz1 in
    let a2_start := ptr_to_int a2 in
    let a2_end   := ptr_to_int a2 + sz2 in
    a1_start <= (a2_end - 1) /\ a2_start <= (a1_end - 1).

  (** Checks if two regions of memory overlap each other. The types
   *τ1* and *τ2* are used to determine the size of the two memory
        regions.
   *)
  Definition overlaps_dtyp (a1 : addr) (τ1 : dtyp) (a2 : addr) (τ2 : dtyp)
    : Prop :=
    overlaps a1 (Z.of_N (sizeof_dtyp τ1)) a2 (Z.of_N (sizeof_dtyp τ2)).

  (** Make sure that two regions of memory do not overlap *)
  Definition no_overlap (a1 : addr) (sz1 : Z) (a2 : addr) (sz2 : Z) : Prop :=
    let a1_start := ptr_to_int a1 in
    let a1_end   := ptr_to_int a1 + sz1 in
    let a2_start := ptr_to_int a2 in
    let a2_end   := ptr_to_int a2 + sz2 in
    a1_start > (a2_end - 1) \/ a2_start > (a1_end - 1).

  (** Same as *no_overlap*, but using *dtyp*s *τ1* and *τ2* to
        determine the size of the regions. *)
  Definition no_overlap_dtyp (a1 : addr) (τ1 : dtyp) (a2 : addr) (τ2 : dtyp)
    : Prop :=
    no_overlap a1 (Z.of_N (sizeof_dtyp τ1)) a2 (Z.of_N (sizeof_dtyp τ2)).

  (** Boolean version of *no_overlap* *)
  Definition no_overlap_b (a1 : addr) (sz1 : Z) (a2 : addr) (sz2 : Z) : bool :=
    let a1_start := ptr_to_int a1 in
    let a1_end   := ptr_to_int a1 + sz1 in
    let a2_start := ptr_to_int a2 in
    let a2_end   := ptr_to_int a2 + sz2 in
    (a1_start >? (a2_end - 1)) || (a2_start >? (a1_end - 1)).
End Overlaps.