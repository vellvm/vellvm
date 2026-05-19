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
Module Type ADDRESS (P : PROVENANCE).
  Parameter addr : Set.
  Parameter null : addr.

  (* Coq's logical equality on the pointer data type *)
  Parameter eq_dec : forall (a b : addr), {a = b} + {a <> b}.
  (* Parameter different_addrs : forall (a : addr), exists (b : addr), a <> b. *)

  (* Access the provenance for an address *)
  Parameter address_provenance : addr -> P.Prov.

  (* Debug *)
  Parameter show_addr : addr -> string.
End ADDRESS.

