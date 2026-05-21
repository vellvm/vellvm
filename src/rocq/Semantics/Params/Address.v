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
From Stdlib Require Import OrderedType OrderedTypeEx.

From Vellvm Require Import
  Utilities
  Params.Provenance.
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

(* TODO: Merge in the Address class, or keep it separate? *)
(* TODO: Is it not over-engineering to allow margin for [ptr_to_int]
   to be anything but the one from iptr?
 *)
Class PI {P : Provenance} {A : @Address P} :=
  {
    ptr_to_int : addr -> Z;

    int_to_ptr : Z -> prov -> EOB addr;
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

