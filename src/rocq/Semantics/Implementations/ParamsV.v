From Vellvm Require Import
  Params
  Implementations.Provenance
  Implementations.Address
  Implementations.Sizeof.

Instance ParamsV {IP : IPtr} {IPT : @IPtrTheory IP}: Params.
econstructor; try typeclasses eauto.
exact PITheoryV.
Defined.
