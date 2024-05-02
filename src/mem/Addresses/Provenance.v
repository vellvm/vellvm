From Coq Require Import
  Structures.Equalities
  Structures.Orders.

(* TODO: Should provenance just be a typeclass? *)
(* Monad class *)
Class MonadProvenance (Provenance : Type) (M : Type -> Type) : Type :=
  { fresh_provenance : M Provenance;
  }.

Module Type CORE_PROVENANCE_TYPE (Import OT:OrderedType).
  Notation Provenance := t.
  (* Provenance allocation *)
  Parameter initial_provenance : Provenance.
  Parameter next_provenance : Provenance -> Provenance.

  Parameter provenance_lt_next_provenance :
    forall pr,
      lt pr (next_provenance pr).
End CORE_PROVENANCE_TYPE.

(** The basic type for provenances.

    This essentially just sets up an ordering and an initial
    provenance value to allow us to allocate fresh ones.
 *)

Module Type PROVENANCE_TYPE := OrderedType <+ CORE_PROVENANCE_TYPE.

(** Allocation ids are the provenances associated with bytes in
    memory. In many cases this will essentially be the same as
    Provenance, but could differ.
 *)
Module Type CORE_ALLOCATION_ID (Import T:DecidableType).
  Notation AllocationId := t.
End CORE_ALLOCATION_ID.

Module Type ALLOCATION_ID := DecidableType <+ CORE_ALLOCATION_ID.


(** A ProvSet is the provenance associated with a pointer.

    This is distinct from a Provenance above as pointers in some
    memory modules may have multiple provenances associated with them,
    wildcard provenances, nil provenances, or more complex permission
    models --- ProvSet is intended to allow for these complexities.
 *)
Module Type CORE_PROV_SET (Import T : Typ).
  Notation ProvSet:=t.
End CORE_PROV_SET.

Module Type PROV_SET <: Typ := Typ <+ CORE_PROV_SET.

Module Type HAS_WILD_PROV (Import PS : PROV_SET).
  Parameter wildcard_prov : ProvSet.
End HAS_WILD_PROV.

Module Type HAS_NIL_PROV (Import PS : PROV_SET).
  Parameter nil_prov : ProvSet.
End HAS_NIL_PROV.

(** Access controls to memory based on pointer provenance and the
    AllocationId of the byte being accessed in memory.
 *)
Module Type ACCESS (Import PS : PROV_SET) (Import AID : ALLOCATION_ID).
  (** Does the provenance set pr allow for access to aid? *)
  Parameter access_allowed : ProvSet -> AllocationId -> bool.
End ACCESS.

(* Module Type PROVENANCE (Addr:ADDRESS_BASE). *)
(*   (* Types *) *)
(*   (* Morally: *)

(*      - Provenance is the base identifier for provenances. *)
(*      - AllocationId is the provenance associated with bytes / *)
(*        locations in memory *)
(*        + This could additionally allow for wildcard provenance for *)
(*          memory locations, for instance. *)
(*      - Prov is the provenance for a pointer. *)
(*        + May have wildcard provenance, or a set of provenances (e.g., *)
(*          this pointer may be allowed to access several different blocks *)
(*          of memory, but not all). *)
(*   *) *)
(*   Parameter Provenance : Set. *)
(*   Parameter AllocationId : Set. *)
(*   Parameter Prov : Set. *)

(*   (* Conversions *) *)
(*   Parameter allocation_id_to_prov : AllocationId -> Prov. *)
(*   Parameter provenance_to_allocation_id : Provenance -> AllocationId. *)
(*   Parameter provenance_to_prov : Provenance -> Prov. *)

(*   (* Lemmas *) *)

(*   Parameter access_allowed_refl : *)
(*     forall aid, *)
(*       access_allowed (allocation_id_to_prov aid) aid = true. *)

(*   Parameter allocation_id_to_prov_inv: *)
(*     forall aid aid', *)
(*       allocation_id_to_prov aid = allocation_id_to_prov aid' -> *)
(*       aid = aid'. *)

(*   Parameter provenance_to_allocation_id_inv : *)
(*     forall pr pr', *)
(*       provenance_to_allocation_id pr = provenance_to_allocation_id pr' -> *)
(*       pr = pr'. *)

(*   Parameter allocation_id_to_prov_provenance_to_allocation_id : *)
(*     forall pr, *)
(*       allocation_id_to_prov (provenance_to_allocation_id pr) = provenance_to_prov pr. *)

(*   Parameter access_allowed_Proper : *)
(*     Proper (eq ==> (fun aid aid' => true = (aid_eq_dec aid aid')) ==> eq) access_allowed. *)

(*   Parameter provenance_lt_trans : Transitive provenance_lt. *)

(*   Parameter provenance_lt_next_provenance : *)
(*     forall pr, *)
(*       provenance_lt pr (next_provenance pr). *)

(*   Parameter provenance_lt_nrefl : *)
(*     forall pr, *)
(*       ~ provenance_lt pr pr. *)

(*   Parameter provenance_lt_antisym : Antisymmetric Provenance eq provenance_lt. *)

(*   Parameter next_provenance_neq : *)
(*     forall pr, *)
(*       pr <> next_provenance pr. *)

(*   (* Debug *) *)
(*   Parameter show_prov : Prov -> string. *)
(*   Parameter show_provenance : Provenance -> string. *)
(*   Parameter show_allocation_id : AllocationId -> string. *)

(*   (* Hints *) *)
(*   Hint Resolve *)
(*        provenance_lt_trans *)
(*        provenance_lt_next_provenance *)
(*        provenance_lt_nrefl : PROVENANCE_LT. *)
(* End PROVENANCE. *)

(* (* Derived functions on provenances. *) *)
(* Module PROV_FUNCS (Addr:ADDRESS). *)
(*   Import Addr. *)

(*   Definition all_accesses_allowed (pr : Prov) (aids : list AllocationId) : bool *)
(*     := forallb (access_allowed pr) aids. *)

(*   Definition all_aid_accesses_allowed (pr : AllocationId) (aids : list AllocationId) : bool *)
(*     := forallb (aid_access_allowed pr) aids. *)

(*   Lemma allocation_id_to_prov_provenance_to_allocation_id_inv : *)
(*     forall pr pr', *)
(*       allocation_id_to_prov (provenance_to_allocation_id pr) = allocation_id_to_prov (provenance_to_allocation_id pr') -> *)
(*       pr = pr'. *)
(*   Proof. *)
(*     intros pr pr' H. *)
(*     apply provenance_to_allocation_id_inv. *)
(*     apply allocation_id_to_prov_inv. *)
(*     auto. *)
(*   Qed. *)
(* End PROV_FUNCS. *)
