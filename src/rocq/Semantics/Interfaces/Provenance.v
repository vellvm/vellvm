(* begin hide *)
From Stdlib Require Import OrderedType OrderedTypeEx.

From Vellvm Require Import
  Utils
  Syntax.
(* end hide *)

Class Provenance :=
  {
    (* Types *)
    (* Morally:

     - Provenance is the base identifier for provenances;
     - AllocationId is the provenance associated with bytes /
       locations in memory
       + This could additionally allow for wildcard provenance for
         memory locations, for instance;
     - Prov is the provenance for a pointer;
       + May have wildcard provenance, or a set of provenances (e;g;,
         this pointer may be allowed to access several different blocks
         of memory, but not all);
     *)
    provenance : Set;
    allocationId : Set;
    prov : Set;

    wildcard_prov : prov;
    nil_prov : prov;

    (* Does the provenance set pr allow for access to aid? *)
    access_allowed : prov -> allocationId -> bool;

    (* Does the first AllocationId have access to the second? *)
    aid_access_allowed : allocationId -> allocationId -> bool;

    (* Conversions *)
    allocation_id_to_prov : allocationId -> prov;
    provenance_to_allocation_id : provenance -> allocationId;
    provenance_to_prov : provenance -> prov;

    (* provenance allocation *)
    initial_provenance : provenance;
    (* TODO: this field contains already in itself the deterministic instance, which is weird *)
    next_provenance : provenance -> provenance;

    eq_dec_provenance :
    forall (pr pr' : provenance),
      {pr = pr'} + {pr <> pr'};

    eq_dec_aid :
    forall (aid aid' : allocationId),
      {aid = aid'} + {aid <> aid'};

    (* Way easier to keep track of provenances in use if they're ordered;;; *)
    provenance_lt : provenance -> provenance -> Prop;
    
    show_prov : prov -> string;
    show_provenance : provenance -> string;
    show_allocation_id : allocationId -> string;
  }.

Class ProvenanceTheory {P : Provenance} : Prop :=
  {
   
    (* Lemmas *)
    aid_access_allowed_refl :
      forall aid, aid_access_allowed aid aid = true;

    access_allowed_refl :
      forall aid,
        access_allowed (allocation_id_to_prov aid) aid = true;

    allocation_id_to_prov_inv:
      forall aid aid',
        allocation_id_to_prov aid = allocation_id_to_prov aid' ->
        aid = aid';

    provenance_to_allocation_id_inv :
      forall pr pr',
        provenance_to_allocation_id pr = provenance_to_allocation_id pr' ->
        pr = pr';

    allocation_id_to_prov_provenance_to_allocation_id :
      forall pr,
        allocation_id_to_prov (provenance_to_allocation_id pr) = provenance_to_prov pr;

    provenance_eq_dec_refl :
      forall (pr : provenance),
        true = (eq_dec_provenance pr pr);

    aid_eq_dec_refl :
      forall (aid : allocationId),
        true = (eq_dec_aid aid aid);

    access_allowed_Proper :
      Proper (eq ==> (fun aid aid' => true = (eq_dec_aid aid aid')) ==> eq) access_allowed;

    provenance_lt_trans : Transitive provenance_lt;

    provenance_lt_next_provenance :
      forall pr,
        provenance_lt pr (next_provenance pr);

    provenance_lt_nrefl :
      forall pr,
        ~ provenance_lt pr pr;

    provenance_lt_antisym : Antisymmetric provenance eq provenance_lt;

    next_provenance_neq :
      forall pr,
        pr <> next_provenance pr;
  }.


