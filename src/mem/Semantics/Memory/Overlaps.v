Require Import ZArith.

Require Import Mem.Addresses.MemoryAddress.

Module Type Overlaps (Addr:MemoryAddress.ADDRESS).
  Import Addr.

  (** Do two memory regions overlap each other?

        - *a1* and *a2* are addresses to the start of each region.
        - *sz1* and *sz2* are the sizes of the two regions.

        Proposition should hold whenever the two regions overlap each
        other. *)

  Parameter overlaps :
    forall (a1 : addr) (sz1 : Z) (a2 : addr) (sz2 : Z), bool.
End Overlaps.

(* Define overlapping of memory addresses when PTOI is defined. *)
Module PTOIOverlaps (Addr:MemoryAddress.ADDRESS) (PTOI:PTOI(Addr)).
  Import Addr.
  Import PTOI.

  Local Open Scope Z.

  Definition overlaps (a1 : addr) (sz1 : Z) (a2 : addr) (sz2 : Z) : bool :=
    let a1_start := ptr_to_int a1 in
    let a1_end   := ptr_to_int a1 + sz1 in
    let a2_start := ptr_to_int a2 in
    let a2_end   := ptr_to_int a2 + sz2 in
    (a1_start <=? (a2_end - 1)) && (a2_start <=? (a1_end - 1)).
End PTOIOverlaps.
