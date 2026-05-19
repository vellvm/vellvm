From Vellvm Require Import
  Utilities
  Syntax.

From Vellvm Require Import
  Params.IPtr
  Params.Provenance
  Integers
  VellvmIntegers.

From QuickChick Require Import Show.

Module Provenance <: PROVENANCE.

  Definition Provenance := N.
  Definition AllocationId := option Provenance. (* None is wildcard *)
  (* TODO: Should probably make this an NSet, but it gives universe inconsistency with Module addr *)
  Definition Prov := option (list Provenance). (* Provenance *)

  Definition wildcard_prov : Prov := None.
  Definition nil_prov : Prov := Some [].

  (* Does the provenance set pr allow for access to aid? *)
  Definition access_allowed (pr : Prov) (aid : AllocationId) : bool
    := match pr with
       | None => true (* Wildcard can access anything. *)
       | Some prset =>
         match aid with
         | None => true (* Wildcard, can be accessed by anything. *)
         | Some aid =>
           existsb (N.eqb aid) prset
         end
       end.

  Definition aid_access_allowed (pr : AllocationId) (aid : AllocationId) : bool
    := match pr with
       | None => true
       | Some pr =>
         match aid with
         | None => true
         | Some aid =>
           N.eqb pr aid
         end
       end.

  Definition allocation_id_to_prov (aid : AllocationId) : Prov
    := fmap (fun x => [x]) aid.

  Definition provenance_to_allocation_id (pr : Provenance) : AllocationId
    := Some pr.

  Definition provenance_to_prov (pr : Provenance) : Prov
    := Some [pr].

  Definition next_provenance (pr : Provenance) : Provenance
    := N.succ pr.

  Definition initial_provenance : Provenance
    := 0%N.

  Lemma eq_dec :
    forall (pr pr' : Provenance),
      {pr = pr'} + {pr <> pr'}.
  Proof.
    exact N.eq_dec.
  Defined.

    (* Debug *)
  Definition show_prov (pr : Prov) := Show.show pr.
  Definition show_provenance (pr : Provenance) := Show.show pr.
  Definition show_allocation_id (aid : AllocationId) := Show.show aid.

End Provenance.

