(** * Vellvm parameter bundle
    [Params] aggregates the parametric components shared across the
    semantics (intptr representation, provenance, sizeof, address, and
    their theories). Most semantics-side definitions take a
    [Context {Pa : Params}]; on extraction, Section closure lifts this to
    a [coq_Params] function argument on each definition that mentions it.
*)

From Vellvm Require Export
  Params.IPtr
  Params.Provenance
  Params.Address
  Params.Sizeof.

Class Params := {
    IPTR :: IPtr;
    PROV :: Provenance;
    SIZE :: Sizeof;
    ADDR :: @Address PROV;
    P2I  :: @PI PROV ADDR;

    IPTRT :: @IPtrTheory IPTR;
    PROVT :: @ProvenanceTheory PROV;
    SIZET :: @SizeofTheory SIZE;
    P2IT  :: @PITheory PROV ADDR P2I;
  }.

