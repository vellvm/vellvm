From Vellvm.Semantics Require Import
  InterpretationStack
  Memory.Sizeof.

Module Type Sizeof_Refine (SZ_INF : SIZEOF) (SZ_FIN : SIZEOF).
  Parameter bit_sizeof_dtyp_fin_inf :
    forall t,
      SZ_INF.bit_sizeof_dtyp t = SZ_FIN.bit_sizeof_dtyp t.

  Parameter sizeof_dtyp_fin_inf :
    forall t,
      SZ_INF.sizeof_dtyp t = SZ_FIN.sizeof_dtyp t.

  Parameter dtyp_alignment_fin_inf :
    forall t,
      SZ_INF.dtyp_alignment t = SZ_FIN.dtyp_alignment t.

  Parameter max_preferred_dtyp_alignment_fin_inf :
    forall dts,
      SZ_INF.max_preferred_dtyp_alignment dts = SZ_FIN.max_preferred_dtyp_alignment dts.
End Sizeof_Refine.

Module Sizeof_Refine_InfFin : Sizeof_Refine InterpreterStackBigIntptr.LP.SZ InterpreterStack64BitIntptr.LP.SZ.
  Lemma bit_sizeof_dtyp_fin_inf :
    forall t,
      InterpreterStackBigIntptr.LP.SZ.bit_sizeof_dtyp t = InterpreterStack64BitIntptr.LP.SZ.bit_sizeof_dtyp t.
  Proof.
    intros t.
    unfold InterpreterStackBigIntptr.LP.SZ.bit_sizeof_dtyp.
    reflexivity.
  Qed.

  Lemma sizeof_dtyp_fin_inf :
    forall t,
      InterpreterStackBigIntptr.LP.SZ.sizeof_dtyp t = InterpreterStack64BitIntptr.LP.SZ.sizeof_dtyp t.
  Proof.
    reflexivity.
  Qed.

  Lemma dtyp_alignment_fin_inf :
    forall t,
      InterpreterStackBigIntptr.LP.SZ.dtyp_alignment t = InterpreterStack64BitIntptr.LP.SZ.dtyp_alignment t.
  Proof.
    reflexivity.
  Qed.

  Lemma max_preferred_dtyp_alignment_fin_inf :
    forall dts,
      InterpreterStackBigIntptr.LP.SZ.max_preferred_dtyp_alignment dts = InterpreterStack64BitIntptr.LP.SZ.max_preferred_dtyp_alignment dts.
  Proof.
    reflexivity.
  Qed.

End Sizeof_Refine_InfFin.
