(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

(* begin hide *)
Require Import String.
Require Import OrderedType OrderedTypeEx.
Require Import ZArith.
Require Import Vellvm.Utils.Error.
(* end hide *)

(** * Signature for addresses
    The semantics is functorized by the notion of addresses manipulated by the
    memory model. This allows us to easily plug different memory models.
    This module is concretely implemented currently in [Handlers/Memory.v].
 *)
Module Type ADDRESS.
  Parameter addr : Set.
  Parameter null : addr.
  Parameter eq_dec : forall (a b : addr), {a = b} + {a <> b}.

  (* Debug *)
  Parameter show_addr : addr -> string.
End ADDRESS.

Module Type INTPTR.
  Parameter intptr : Set.
  Parameter zero : intptr.

  Parameter eq_dec : forall (a b : intptr), {a = b} + {a <> b}.
  Parameter eqb : forall (a b : intptr), bool.

  Parameter to_Z : forall (a : intptr), Z.
  Parameter to_unsigned : forall (a : intptr), Z.
  Parameter from_Z : Z -> OOM intptr.
End INTPTR.

(* TODO: move this? *)
Module Type PTOI(Addr:MemoryAddress.ADDRESS).  
  Parameter ptr_to_int : Addr.addr -> Z.
End PTOI.

(* TODO: move this?
   TODO: Have I crammed too much into this?
 *)
Module Type PROVENANCE(Addr:MemoryAddress.ADDRESS).
  (* Types *)
  (* Morally:

     - Provenance is the base identifier for provenances.
     - AllocationId is the provenance associated with bytes /
       locations in memory
       + This could additionally allow for wildcard provenance for
         memory locations, for instance.
     - Prov is the provenance for a pointer.
       + May have wildcard provenance, or a set of provenances (e.g.,
         this pointer may be allowed to access several different blocks
         of memory, but not all).
  *)
  Parameter Provenance : Set.
  Parameter AllocationId : Set.
  Parameter Prov : Set.

  Parameter wildcard_prov : Prov.
  Parameter nil_prov : Prov.

  (* Access the provenance for an address *)
  Parameter address_provenance : Addr.addr -> Prov.

  (* Does the provenance set pr allow for access to aid? *)
  Parameter access_allowed : Prov -> AllocationId -> bool.

  (* Does the first AllocationId have access to the second? *)
  Parameter aid_access_allowed : AllocationId -> AllocationId -> bool.

  (* Conversions *)
  Parameter allocation_id_to_prov : AllocationId -> Prov.
  Parameter provenance_to_allocation_id : Provenance -> AllocationId.

  (* Provenance allocation *)
  Parameter initial_provenance : Provenance.
  Parameter next_provenance : Provenance -> Provenance.

  (* Debug *)
  Parameter show_prov : Prov -> string.
  Parameter show_provenance : Provenance -> string.
  Parameter show_allocation_id : AllocationId -> string.
End PROVENANCE.

(* Derived functions on provenances. *)
Module PROV_FUNCS(Addr:MemoryAddress.ADDRESS)(PROV:PROVENANCE(Addr)).
  Import PROV.

  Definition all_accesses_allowed (pr : Prov) (aids : list AllocationId) : bool
    := forallb (access_allowed pr) aids.

  Definition all_aid_accesses_allowed (pr : AllocationId) (aids : list AllocationId) : bool
    := forallb (aid_access_allowed pr) aids.
End PROV_FUNCS.

(* TODO: move this? *)
Module Type ITOP(Addr:MemoryAddress.ADDRESS)(PROV:PROVENANCE(Addr)).
  Parameter int_to_ptr : Z -> PROV.Prov -> Addr.addr.
End ITOP.
