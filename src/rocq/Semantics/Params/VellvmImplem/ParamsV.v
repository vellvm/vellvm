From Vellvm Require Import
  Params
  Params.VellvmImplem.Provenance
  Params.VellvmImplem.Address
  Params.VellvmImplem.Sizeof.

Instance ParamsV {IP : IPtr} {IPT : @IPtrTheory IP}: Params.
econstructor; try typeclasses eauto.
exact PITheoryV.
Defined.
