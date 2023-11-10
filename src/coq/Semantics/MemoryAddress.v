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
     Syntax.DynamicTypes
     Semantics.VellvmIntegers
     Utils.Error.

From ExtLib Require Import
     Structures.Monads.

Import MonadNotation.
Open Scope monad_scope.
(* end hide *)

(** * Signature for addresses
    The semantics is functorized by the notion of addresses manipulated by the
    memory model. This allows us to easily plug different memory models.
    This module is concretely implemented currently in [Handlers/Memory.v].
 *)
Module Type ADDRESS.
  Parameter addr : Set.
  Parameter null : addr.

  (* Coq's logical equality on the pointer data type *)
  Parameter eq_dec : forall (a b : addr), {a = b} + {a <> b}.

  (* SAZ: MODULE CLEANUP - this can't possibly be very useful: delete? *)
  Parameter different_addrs : forall (a : addr), exists (b : addr), a <> b.

  (* Debug *)
  Parameter show_addr : addr -> string.
End ADDRESS.


(* SAZ: Design note? I'm experimenting with naming functors / sig_funs with "underscore" [_] names
   to indicate that they're intended to "extend" existing signatures / modules.

   For example: [_PTOI] adds the [ptr_to_int] function to an [ADDRESS] module.
*)
(* SAZ: CLEANUP - rename PTOI to ATOI and [ptr_to_int] to [addr_to_int] *)
Module Type _PTOI (Import Addr:ADDRESS).
  Parameter ptr_to_int : addr -> Z.
End _PTOI.

(* SAZ: We define the combined signature like so: *)
Module Type ADDRESS_PTOI := ADDRESS <+ _PTOI.

(* TODO: Should provenance just be a typeclass? *)
(* Monad class *)
Class MonadProvenance (Provenance : Type) (M : Type -> Type) : Type :=
  { fresh_provenance : M Provenance;
  }.

(* TODO: move this?
   TODO: Have I crammed too much into this?
 *)
Module Type _PROVENANCE (Import Addr:ADDRESS).
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
  Parameter provenance_to_prov : Provenance -> Prov.

  (* Provenance allocation *)
  Parameter initial_provenance : Provenance.
  Parameter next_provenance : Provenance -> Provenance.

  (* Way easier to keep track of provenances in use if they're ordered... *)
  Parameter provenance_lt : Provenance -> Provenance -> Prop.

  (* Lemmas *)
  Parameter aid_access_allowed_refl :
    forall aid, aid_access_allowed aid aid = true.

  Parameter access_allowed_refl :
    forall aid,
      access_allowed (allocation_id_to_prov aid) aid = true.

  Parameter allocation_id_to_prov_inv:
    forall aid aid',
      allocation_id_to_prov aid = allocation_id_to_prov aid' ->
      aid = aid'.

  Parameter provenance_to_allocation_id_inv :
    forall pr pr',
      provenance_to_allocation_id pr = provenance_to_allocation_id pr' ->
      pr = pr'.

  Parameter allocation_id_to_prov_provenance_to_allocation_id :
    forall pr,
      allocation_id_to_prov (provenance_to_allocation_id pr) = provenance_to_prov pr.

  Parameter provenance_eq_dec :
    forall (pr pr' : Provenance),
      {pr = pr'} + {pr <> pr'}.

  Parameter provenance_eq_dec_refl :
    forall (pr : Provenance),
      true = (provenance_eq_dec pr pr).

  Parameter aid_eq_dec :
    forall (aid aid' : AllocationId),
      {aid = aid'} + {aid <> aid'}.

  Parameter aid_eq_dec_refl :
    forall (aid : AllocationId),
      true = (aid_eq_dec aid aid).

  Parameter access_allowed_Proper :
    Proper (eq ==> (fun aid aid' => true = (aid_eq_dec aid aid')) ==> eq) access_allowed.

  Parameter provenance_lt_trans : Transitive provenance_lt.

  Parameter provenance_lt_next_provenance :
    forall pr,
      provenance_lt pr (next_provenance pr).

  Parameter provenance_lt_nrefl :
    forall pr,
      ~ provenance_lt pr pr.

  Parameter provenance_lt_antisym : Antisymmetric Provenance eq provenance_lt.

  Parameter next_provenance_neq :
    forall pr,
      pr <> next_provenance pr.

  (* Debug *)
  Parameter show_prov : Prov -> string.
  Parameter show_provenance : Provenance -> string.
  Parameter show_allocation_id : AllocationId -> string.

  (* Hints *)
  Hint Resolve
       provenance_lt_trans
       provenance_lt_next_provenance
       provenance_lt_nrefl : PROVENANCE_LT.
End _PROVENANCE.

Module Type ADDRESS_PROVENANCE := ADDRESS_PTOI <+ _PROVENANCE.

(*
(* Derived functions on provenances. *)
Module PROV_FUNCS(Addr:MemoryAddress.ADDRESS)(PROV:PROVENANCE(Addr)).
  Import PROV.

  Definition all_accesses_allowed (pr : Prov) (aids : list AllocationId) : bool
    := forallb (access_allowed pr) aids.

  Definition all_aid_accesses_allowed (pr : AllocationId) (aids : list AllocationId) : bool
    := forallb (aid_access_allowed pr) aids.

  Lemma allocation_id_to_prov_provenance_to_allocation_id_inv :
    forall pr pr',
      allocation_id_to_prov (provenance_to_allocation_id pr) = allocation_id_to_prov (provenance_to_allocation_id pr') ->
      pr = pr'.
  Proof.
    intros pr pr' H.
    apply provenance_to_allocation_id_inv.
    apply allocation_id_to_prov_inv.
    auto.
  Qed.
End PROV_FUNCS.
*)

(* TODO: move this? *)
Module Type _ITOP (Import Addr:ADDRESS_PROVENANCE).

  Parameter int_to_ptr : Z -> Prov -> OOM addr.
  Parameter int_to_ptr_provenance :
    forall (x : Z) (p : Prov) (a : addr),
      int_to_ptr x p = ret a ->
      address_provenance a = p.

  Parameter int_to_ptr_ptr_to_int :
    forall (a : addr) (p : Prov),
      address_provenance a = p ->
      int_to_ptr (ptr_to_int a) p = ret a.

  Parameter int_to_ptr_ptr_to_int_exists :
    forall (a : addr) (p : Prov),
    exists a',
      int_to_ptr (ptr_to_int a) p = ret a' /\
        ptr_to_int a' = ptr_to_int a /\
        address_provenance a' = p.

  Parameter ptr_to_int_int_to_ptr :
    forall (x : Z) (p : Prov) (a : addr),
      int_to_ptr x p = ret a ->
      ptr_to_int a = x.
End _ITOP.

Module Type ADDRESS_ITOP := ADDRESS_PROVENANCE <+ _ITOP.

Module Type _ITOP_BIG (Import Addr:ADDRESS_ITOP).
  Parameter int_to_ptr_safe :
    forall z pr,
      match int_to_ptr z pr with
      | NoOom _ => True
      | Oom _ => False
      end.
End _ITOP_BIG.

Module Type ADDRESS_ITOP_BIG := ADDRESS_ITOP <+ _ITOP_BIG.


