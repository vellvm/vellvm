From Vellvm Require Import
  Utils
  Syntax.

From Vellvm Require Import
  Rocqlib
  EOU
  Interfaces.IPtr
  Interfaces.Address
  Interfaces.Provenance
  Implementations.Provenance
  VellvmIntegers.


Section withIPtr.
  Context {IP : IPtr}.
  Context {IPT : @IPtrTheory IP}.
  
  (* TODO: move this *)
  Instance showIptr {IP : IPtr} : Show iptr := {| show := show_iptr |}.

  #[refine] Instance AddressV {IP : IPtr} : @Address ProvenanceV :=
    {|
      addr := (iptr * prov);
      null := (zero_iptr, nil_prov)%Z;
      address_provenance := snd;
      show_addr a := show a;
    |}.
  Proof.
    intros [a1 a2] [b1 b2].
    destruct (eq_dec_iptr a1 b1); destruct (option_eq (list_eq_dec N.eq_dec) a2 b2); subst.
    - left; reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
  Defined.

  Instance PIV : @PI ProvenanceV AddressV :=
    {|
      ptr_to_int p := to_Z (fst p);
      int_to_ptr i pr := a <- from_Z i ;; ret (a, pr) 
    |}
  .

  Instance PITheoryV : @PITheory ProvenanceV AddressV PIV.
  Proof.
    constructor.
    - cbn; intros * EQ.
      repeat break_match; abs_eq.
      destruct a; abs_eq.
      now inv EQ.
    - intros [a p'] * <-; cbn.
      now rewrite to_Z_from_Z.
    - intros [i p'] p; exists (i,p).
      cbn; now rewrite to_Z_from_Z.
    - intros ?? [i p'].
      cbn.
      intros ?; break_match; abs_eq.
      inv H.
      now apply from_Z_to_Z.
  Qed.
  
  Existing Instance overlaps_ptoi.

End withIPtr.
