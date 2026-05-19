From Vellvm Require Import
  Utilities
  Syntax.

From Vellvm Require Import
  Rocqlib
  Params.IPtr
  Params.Address
  VellvmImplem.Provenance
  VellvmIntegers.

From QuickChick Require Import Show.

Module Address (IP : IPTR) <: ADDRESS Provenance.

  Module P := Provenance.
  Import IP P.

  Definition addr := (intptr * Prov) % type.
  Definition null : addr := (zero, nil_prov)%Z.

  (* TODO: is this what we should be using for equality on pointers? Probably *NOT* because of provenance. *)
  Lemma eq_dec : forall (a b : addr), {a = b} + {a <> b}.
  Proof.
    intros [a1 a2] [b1 b2].
    destruct (IP.eq_dec a1 b1); destruct (option_eq (list_eq_dec P.eq_dec) a2 b2); subst.
    - left; reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
  Qed.

  Definition show_addr (a : addr) :=
    match a with
    | (i, p) => show (show_intptr i, show_prov p)
    end.
  
End Address.
