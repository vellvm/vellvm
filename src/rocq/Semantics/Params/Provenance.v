(* begin hide *)
From Stdlib Require Import OrderedType OrderedTypeEx.

From Vellvm Require Import
  Utilities
  Syntax.
(* end hide *)

(* TODO: Should provenance just be a typeclass? *)
(* Monad class *)
Class MonadProvenance (Provenance : Type) (M : Type -> Type) : Type :=
  { fresh_provenance : M Provenance;
  }.

(* TODO: move this?
   TODO: Have I crammed too much into this?
 *)
Module Type PROVENANCE.
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

  Parameter eq_dec :
    forall (pr pr' : Provenance),
      {pr = pr'} + {pr <> pr'}.


  (* (* Way easier to keep track of provenances in use if they're ordered... *) *)
  (* Parameter provenance_lt : Provenance -> Provenance -> Prop. *)

  (* (* Lemmas *) *)
  (* Parameter aid_access_allowed_refl : *)
  (*   forall aid, aid_access_allowed aid aid = true. *)

  (* Parameter access_allowed_refl : *)
  (*   forall aid, *)
  (*     access_allowed (allocation_id_to_prov aid) aid = true. *)

  (* Parameter allocation_id_to_prov_inv: *)
  (*   forall aid aid', *)
  (*     allocation_id_to_prov aid = allocation_id_to_prov aid' -> *)
  (*     aid = aid'. *)

  (* Parameter provenance_to_allocation_id_inv : *)
  (*   forall pr pr', *)
  (*     provenance_to_allocation_id pr = provenance_to_allocation_id pr' -> *)
  (*     pr = pr'. *)

  (* Parameter allocation_id_to_prov_provenance_to_allocation_id : *)
  (*   forall pr, *)
  (*     allocation_id_to_prov (provenance_to_allocation_id pr) = provenance_to_prov pr. *)

  (* Parameter provenance_eq_dec_refl : *)
  (*   forall (pr : Provenance), *)
  (*     true = (provenance_eq_dec pr pr). *)

  (* Parameter aid_eq_dec : *)
  (*   forall (aid aid' : AllocationId), *)
  (*     {aid = aid'} + {aid <> aid'}. *)

  (* Parameter aid_eq_dec_refl : *)
  (*   forall (aid : AllocationId), *)
  (*     true = (aid_eq_dec aid aid). *)

  (* Parameter access_allowed_Proper : *)
  (*   Proper (eq ==> (fun aid aid' => true = (aid_eq_dec aid aid')) ==> eq) access_allowed. *)

  (* Parameter provenance_lt_trans : Transitive provenance_lt. *)

  (* Parameter provenance_lt_next_provenance : *)
  (*   forall pr, *)
  (*     provenance_lt pr (next_provenance pr). *)

  (* Parameter provenance_lt_nrefl : *)
  (*   forall pr, *)
  (*     ~ provenance_lt pr pr. *)

  (* Parameter provenance_lt_antisym : Antisymmetric Provenance eq provenance_lt. *)

  (* Parameter next_provenance_neq : *)
  (*   forall pr, *)
  (*     pr <> next_provenance pr. *)

  (* Debug *)
  Parameter show_prov : Prov -> string.
  Parameter show_provenance : Provenance -> string.
  Parameter show_allocation_id : AllocationId -> string.

  (* (* Hints *) *)
  (* Hint Resolve *)
  (*      provenance_lt_trans *)
  (*      provenance_lt_next_provenance *)
  (*      provenance_lt_nrefl : PROVENANCE_LT. *)
  
End PROVENANCE.


(* (* Derived functions on provenances. *) *)
(* Module PROV_FUNCS(Addr : ADDRESS) (PROV : PROVENANCE(Addr)). *)
(*   Import PROV. *)

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

