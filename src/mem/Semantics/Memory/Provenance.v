From Coq Require Import NArith.

Definition Provenance := N.
Definition AllocationId := option Provenance. (* None is wildcard *)

(*
I have...

- Prov
- Provenance
- AllocationId

Definition Prov := option (list Provenance). (* Provenance *)

Provenance is the base of all of this, it's just a single id...

AllocationId is an option Provenance, where None is a wildcard
provenance allowing accesses from any pointer... Not sure why we have
this, but it could be useful..

Prov is the provenances that a pointer can have. This can be a
wildcard provenance (None here), or it can be a set of provenances.
*)
