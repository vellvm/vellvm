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

