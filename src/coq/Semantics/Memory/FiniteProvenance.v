From Coq Require Import NArith.

Definition Provenance := N.
Definition AllocationId := option Provenance. (* None is wildcard *)
