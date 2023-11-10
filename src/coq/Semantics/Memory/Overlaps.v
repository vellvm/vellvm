Require Import ZArith.

Require Import Vellvm.Semantics.MemoryAddress.
Require Import Vellvm.Semantics.Memory.Sizeof.
From Vellvm Require Import DynamicTypes.

Module Type _OVERLAPS (Import Addr:MemoryAddress.ADDRESS).
  (** Do two memory regions overlap each other?

        - *a1* and *a2* are addresses to the start of each region.
        - *sz1* and *sz2* are the sizes of the two regions.

        Proposition should hold whenever the two regions overlap each
        other. *)

  Parameter overlaps :
    forall (a1 : addr) (sz1 : Z) (a2 : addr) (sz2 : Z), bool.
End _OVERLAPS.

Module Type ADDRESS_OVERLAPS := ADDRESS_ITOP <+ _OVERLAPS.
Module Type ADDRESS_OVERLAPS_BIG := ADDRESS_ITOP_BIG <+ _OVERLAPS.

(* SAZ: MODULE CLEANUP TODO: rename this? *)
Module OverlapHelpers (Import Addr : ADDRESS_OVERLAPS) (Import Sizeof : SIZEOF).

  (** Checks if two regions of memory overlap each other. The types
   *τ1* and *τ2* are used to determine the size of the two memory
        regions.
   *)
  Definition overlaps_dtyp (a1 : addr) (τ1 : dtyp) (a2 : addr) (τ2 : dtyp)
    : bool :=
    overlaps a1 (Z.of_N (sizeof_dtyp τ1)) a2 (Z.of_N (sizeof_dtyp τ2)).

  (** Make sure that two regions of memory do not overlap *)
  Definition no_overlap (a1 : addr) (sz1 : Z) (a2 : addr) (sz2 : Z) : bool
    := negb (overlaps a1 sz1 a2 sz2).

  (** Same as *no_overlap*, but using *dtyp*s *τ1* and *τ2* to
        determine the size of the regions. *)
  Definition no_overlap_dtyp (a1 : addr) (τ1 : dtyp) (a2 : addr) (τ2 : dtyp)
    : bool := negb (overlaps_dtyp a1 τ1 a2 τ2).
End OverlapHelpers.

