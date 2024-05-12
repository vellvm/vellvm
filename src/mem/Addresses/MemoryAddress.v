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
Require Import Coqlib.

From Vellvm Require Import
  Utils.Error
  Utils.Monads.

From ExtLib Require Import
  Structures.Monads.

From Coq Require Import
  Structures.Equalities.

From Mem Require Import
  Addresses.Provenance.

Import MonadNotation.
Open Scope monad_scope.
(* end hide *)

(*** Abstract address modules *)
Module ADDRESS_TYPE_NOTATION (Import T:Typ).
  Notation addr := t.
End ADDRESS_TYPE_NOTATION.

(** The core abstract address type, which essentially just has
    decidable equality.
 *)
Module Type CORE_ADDRESS := DecidableType <+ ADDRESS_TYPE_NOTATION.

(*** Address functors *)

(** Addresses which have null pointers *)
Module Type HAS_NULL (Import Addr:CORE_ADDRESS).
  Parameter null : addr.
End HAS_NULL.

(** Address types which can be converted to integers *)
Module Type HAS_PTOI (Import Addr:CORE_ADDRESS).
  Parameter ptr_to_int : addr -> Z.
End HAS_PTOI.

Module Type HAS_POINTER_ARITHMETIC_CORE (Import Addr:CORE_ADDRESS).
  (** Pointer addition. May error if the result cannot be represented
      as a pointer, e.g., if it would be out of bounds.
   *)
  Parameter ptr_add : addr -> Z -> err addr.
  Parameter ptr_add_0 :
    forall ptr,
      ptr_add ptr 0 = inr ptr.
End HAS_POINTER_ARITHMETIC_CORE.

Module Type HAS_POINTER_ARITHMETIC_HELPERS
  (Import Addr:CORE_ADDRESS)
  (Import ARITH:HAS_POINTER_ARITHMETIC_CORE Addr).

  Definition get_consecutive_ptrs (ptr : addr) (len : nat) : err (list addr) :=
    let ixs := seq 0 len in
    map_monad
      (fun ix => ptr_add ptr (Z.of_nat ix))
      ixs (m:=err).

  Fixpoint consecutive_ptrs_h (start : addr) (ptrs : list addr) : bool :=
    match ptrs with
    | nil => true
    | cons ptr ptrs =>
        match (ptr_add ptr 1) with
        | inl _ => false
        | inr ptr' =>
            proj_sumbool (eq_dec ptr ptr') &&
              consecutive_ptrs_h ptr ptrs
        end
    end.

  Definition consecutive_ptrs (ptrs : list addr) : bool :=
    match ptrs with
    | nil => true
    | cons ptr ptrs => consecutive_ptrs_h ptr ptrs
    end.
    
End HAS_POINTER_ARITHMETIC_HELPERS.

Module Type HAS_POINTER_ARITHMETIC (ADDR : CORE_ADDRESS)
  := HAS_POINTER_ARITHMETIC_CORE ADDR <+ HAS_POINTER_ARITHMETIC_HELPERS ADDR.

Module Type PTOI_ARITH_EXTRAS (Import Addr:CORE_ADDRESS) (Import PTOI : HAS_PTOI Addr) (Import HPA : HAS_POINTER_ARITHMETIC Addr).
  Parameter ptr_to_int_ptr_add :
    forall (ptr ptr' : addr) (x : Z),
      ptr_add ptr x = inr ptr' ->
      ptr_to_int ptr' = ptr_to_int ptr + x.
End PTOI_ARITH_EXTRAS.

(* TODO: Should this be moved to a utility file? *)
(** Types with additional metadata associated with them *)
Module Type HAS_METADATA (METADATA : Typ) (Import T:Typ).
  Parameter extract_metadata : t -> METADATA.t.
End HAS_METADATA.

(** Address types which support casts from integers

    METADATA is a type representing any extra metadata that might be
    needed when constructing a pointer from an integer type. Usually
    this metadata is something like a provenance.
 *)
Module Type HAS_ITOP (METADATA : Typ) (Import Addr:CORE_ADDRESS) (Import HMD : HAS_METADATA METADATA Addr).
  (** Convert an integer to a pointer.

      Parameters:
      - The integer to convert to a pointer value.
      - Metadata associated with the pointer (often this is a provenance).

      Return value:
      The resulting address. May OOM if the integer value doesn't fit
      in the address space.
   *)
  Parameter int_to_ptr : Z -> METADATA.t -> OOM addr.
  Parameter int_to_ptr_metadata :
    forall (x : Z) (p : METADATA.t) (a : addr),
      int_to_ptr x p = ret a ->
      extract_metadata a = p.
End HAS_ITOP.

(** Addresses that integers can safely be converted to (infinite
    address space)
 *)
Module Type ITOP_BIG (METADATA : Typ) (Import Addr:CORE_ADDRESS) (Import HMD : HAS_METADATA METADATA Addr) (Import ITOP : HAS_ITOP METADATA Addr HMD).
  Parameter int_to_ptr_safe :
    forall z pr,
      match int_to_ptr z pr with
      | NoOom _ => True
      | Oom _ => False
      end.
End ITOP_BIG.

(** Extra properties for addresses that support both ptoi and itop casts *)
Module Type PTOI_ITOP_EXTRA (METADATA : Typ) (Import Addr:CORE_ADDRESS) (Import HMD : HAS_METADATA METADATA Addr) (Import ITOP : HAS_ITOP METADATA Addr HMD) (Import PTOI : HAS_PTOI Addr).
  Parameter int_to_ptr_ptr_to_int :
    forall (a : addr) (p : METADATA.t),
      extract_metadata a = p ->
      int_to_ptr (ptr_to_int a) p = ret a.

  Parameter int_to_ptr_ptr_to_int_exists :
    forall (a : addr) (p : METADATA.t),
    exists a',
      int_to_ptr (ptr_to_int a) p = ret a' /\
        ptr_to_int a' = ptr_to_int a /\
        extract_metadata a' = p.

  Parameter ptr_to_int_int_to_ptr :
    forall (x : Z) (p : METADATA.t) (a : addr),
      int_to_ptr x p = ret a ->
      ptr_to_int a = x.
End PTOI_ITOP_EXTRA.

(** Address types with an associated provenance *)
Module Type HAS_PROVENANCE (Import PS : PROV_SET) (Import Addr:CORE_ADDRESS).
  (** Access the provenance for an address *)
  Parameter address_provenance : addr -> ProvSet.
End HAS_PROVENANCE.

Module HAS_PROVENANCE_TO_HAS_METADATA (Import PS : PROV_SET) (Import Addr:CORE_ADDRESS) (Import HP : HAS_PROVENANCE PS Addr) <: HAS_METADATA PS Addr.
  Definition extract_metadata := address_provenance.
End HAS_PROVENANCE_TO_HAS_METADATA.

(*** Address module types *)
(** Addresses that can be null *)
Module Type NULLABLE_ADDRESSES := CORE_ADDRESS <+ HAS_NULL.

(** Addresses with the batteries included *)
Module Type ADDRESS :=
  CORE_ADDRESS <+ HAS_NULL <+ HAS_POINTER_ARITHMETIC <+
    HAS_PROVENANCE <+ HAS_PROVENANCE_TO_HAS_METADATA <+
    HAS_PTOI <+ HAS_ITOP <+ PTOI_ITOP_EXTRA <+ PTOI_ARITH_EXTRAS.

(** Infinite addresses with the batteries included *)
Module Type INFINITE_ADDRESS :=
  ADDRESS <+ ITOP_BIG.

(* TODO: Move this to a show utility file? *)
Module Type SHOWABLE (Import T:Typ).
  Parameter show_t : t -> string.
End SHOWABLE.
