From Coq Require Import
  Structures.Equalities.

Module UNIT_TYP <: DecidableType.
  Definition t := unit.
  Definition eq : unit -> unit -> Prop := Logic.eq.

  Lemma eq_dec : forall (a b : unit), {a = b} + {a <> b}.
  Proof.
    intros [] []; auto.
  Qed.

  #[global] Instance eq_equiv : Equivalence eq.
  typeclasses eauto.
  Defined.
End UNIT_TYP.

Module Type HasDefault (Import T : Typ).
  Parameter default : t.
End HasDefault.

Module UNIT_HAS_DEFAULT <: HasDefault UNIT_TYP.
  Definition default := tt.
End UNIT_HAS_DEFAULT.
