From Stdlib Require Import
  Lia
  Basics
  Morphisms.

From Vellvm Require Import
  Numeric.Rocqlib
  Utils.Error
  Utils.Tactics.

From Mem Require Import
  Addresses.MemoryAddress
  Addresses.Provenance
  Tactics.

From Vellvm.Semantics Require Import
  VellvmIntegers.

From QuickChick Require Import Show.

From ExtLib Require Import
  Structures.Functor
  Structures.Monads.

From Stdlib Require Import
  Structures.Equalities
  Structures.Orders.

Import ListNotations.
Import MonadNotation.
Open Scope monad.

(** ** Type of pointers
    Implementation of the notion of pointer used: an address and an offset.
 *)
Definition Iptr := int64. (* Integer pointer type (physical addresses) *)

(* TODO: Should probably make this an NSet, but it gives universe inconsistency with Module addr *)
Definition Prov := N_ProvSet.t.

Definition wildcard_prov : Prov := None.
Definition nil_prov : Prov := Some [].

Module FinAddrType <: CORE_ADDRESS.
  Definition t := (Iptr * Prov) % type.
  Definition eq := @Logic.eq t.

  (* TODO: is this what we should be using for equality on pointers? Probably *NOT* because of provenance. *)
  Lemma eq_dec : forall (a b : t), {a = b} + {a <> b}.
  Proof.
    intros [a1 a2] [b1 b2].

    destruct (Integers.eq_dec a1 b1);
      destruct (option_eq (fun x y => list_eq_dec N.eq_dec x y) a2 b2); subst.
    - left; reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
  Qed.

  #[global] Instance eq_equiv : Equivalence eq.
  typeclasses eauto.
  Defined.
End FinAddrType.

Module FinNull <: HAS_NULL FinAddrType.
  Definition null := (@Integers.repr 64%positive 0, nil_prov).

  Definition is_null (a : FinAddrType.t) : bool :=
    Integers.eq (fst null) (fst a).

  Lemma null_is_null :
    is_null null = true.
  Proof.
    reflexivity.
  Qed.

End FinNull.

Module FinPTOI <: HAS_PTOI FinAddrType.
  Definition ptr_to_int := fun (ptr : FinAddrType.t) => @Integers.unsigned 64 (fst ptr).
End FinPTOI.

Module Fin_HAS_NULL_PTOI <: HAS_NULL_PTOI FinAddrType FinNull FinPTOI.
  Import FinAddrType FinNull FinPTOI.

  Lemma is_null_is_zero :
    forall ptr,
      is_null ptr = true <-> ptr_to_int ptr = 0.
  Proof.
    intros ptr.
    destruct ptr; unfold is_null, ptr_to_int; cbn.
    pose proof (Integers.eq_spec (Integers.repr 0) i) as EQ.
    split; intros H.
    - rewrite H in EQ; auto.
      subst.
      auto.
    - break_match_hyp; auto.
      exfalso.
      apply EQ.
      epose proof Integers.repr_unsigned i.
      rewrite H in H0; auto.
  Qed.

  #[global] Hint Resolve is_null_is_zero : MEM.
End Fin_HAS_NULL_PTOI.

Module Type Fin_HAS_POINTER_ARITHMETIC_CORE <: HAS_POINTER_ARITHMETIC_CORE FinAddrType.
  (** Pointer addition. May error if the result cannot be represented
      as a pointer, e.g., if it would be out of bounds.
   *)
  Definition ptr_add (a : FinAddrType.t) (i : Z) : err FinAddrType.t
    := match a with
       | (ptr, pr) =>
           let res := @Integers.unsigned 64 ptr + i in
           if (res <? 0)%Z || (res >=? @Integers.modulus 64)%Z
           then inl ("ptr_add: out of range.")%string
           else ret (@Integers.repr 64 res, pr)
       end.

  Lemma ptr_add_0 :
    forall ptr,
      ptr_add ptr 0 = inr ptr.
  Proof.
    intros ptr.
    unfold ptr_add.
    destruct ptr.
    rewrite Z.add_0_r in *.
    pose proof Integers.unsigned_range i.
    break_match; try lia.
    rewrite Integers.repr_unsigned.
    reflexivity.
  Qed.

  Lemma ptr_add_hom :
    forall ptr x y,
      x >= 0 ->
      y >= 0 ->
      p <- ptr_add ptr x;;
      ptr_add p y = ptr_add ptr (x + y).
  Proof.
    intros ptr x y X Y.
    cbn.
    destruct ptr; cbn; auto.
    pose proof Integers.unsigned_range i.
    repeat break_match;
      try inv Heqs; auto; try lia.
    - cbn.
      break_match; auto.
      apply orb_false_iff in Heqb1, Heqb0;
        apply orb_true_iff in Heqb.
      destruct Heqb0.
      destruct Heqb; try lia.
      destruct Heqb1; try lia.
      rewrite Integers.Z_mod_modulus_eq in H3, H4.
      pose proof Z.mod_small (Integers.unsigned i + x) (@Integers.modulus 64) as MOD.
      lia.
    - cbn.
      rewrite Integers.Z_mod_modulus_eq.
      pose proof Z.mod_small (Integers.unsigned i + x) (@Integers.modulus 64) as MOD.
      break_match; auto; try lia.
      apply orb_false_iff in Heqb, Heqb0, Heqb1.
      destruct Heqb0; try lia;
      destruct Heqb; try lia;
        destruct Heqb1; try lia.
      replace ((Integers.unsigned i + x) mod Integers.modulus + y) with (Integers.unsigned i + (x + y)) by lia.
      reflexivity.
  Qed.
End Fin_HAS_POINTER_ARITHMETIC_CORE.

Module Fin_PTOI_HAS_POINTER_ARITHMETIC <: HAS_POINTER_ARITHMETIC FinAddrType := Fin_HAS_POINTER_ARITHMETIC_CORE  <+ HAS_POINTER_ARITHMETIC_HELPERS FinAddrType.

Module Fin_PTOI_ARITH_EXTRAS <: PTOI_ARITH_EXTRAS FinAddrType FinPTOI Fin_PTOI_HAS_POINTER_ARITHMETIC.
  Import FinPTOI.
  Import Fin_PTOI_HAS_POINTER_ARITHMETIC.
  Lemma ptr_to_int_ptr_add :
    forall (ptr ptr' : FinAddrType.t) (x : Z),
      ptr_add ptr x = inr ptr' ->
      ptr_to_int ptr' = ptr_to_int ptr + x.
  Proof.
    intros ptr ptr' x H.
    unfold ptr_to_int.
    unfold ptr_add in *.
    cbn in *.
    destruct ptr, ptr'; cbn in *.
    break_match_hyp_inv.
    rewrite (Integers.unsigned_repr (@Integers.unsigned 64 i + x)); unfold Integers.max_unsigned;
      lia.
  Qed.

  Include (PTOI_ARITH_EXTRAS_HELPERS FinAddrType FinPTOI Fin_PTOI_HAS_POINTER_ARITHMETIC).
End Fin_PTOI_ARITH_EXTRAS.

Module Fin_HAS_METADATA <: HAS_METADATA N_ProvSet FinAddrType.
  Definition extract_metadata (addr : FinAddrType.t) : N_ProvSet.t :=
    snd addr.

  Definition default_metadata := N_ProvSet.wildcard_prov.
End Fin_HAS_METADATA.

(* TODO: Move to utility *)
Module METADATA_PROVENANCE_ID (MD : Typ) <: METADATA_PROVENANCE MD MD.
  (** Modify the provenance in the metadata, returning the new provenance and metadata values *)
  Definition metadata_modify_provenance (md : MD.t) (f : MD.t -> MD.t) : (MD.t * MD.t) :=
    let md' := f md in
    (md', md').

  (** Access the provenance for an address *)
  Definition metadata_provenance (md : MD.t) : MD.t
    := fst (metadata_modify_provenance md id).

  Definition metadata_set_provenance (md : MD.t) (p : MD.t) : MD.t
    := snd (metadata_modify_provenance md (const p)).

  Lemma metadata_modify_provenance_spec :
    forall md f,
    exists md', metadata_modify_provenance md f = (f (metadata_provenance md), md') /\
             metadata_provenance md' = f (metadata_provenance md).
  Proof.
    intros md f.
    cbn in *.
    exists (f md).
    eexists; cbn; split; eauto.
  Qed.

  Lemma metadata_get_set_provenance :
    forall md p,
      metadata_provenance (metadata_set_provenance md p) = p.
  Proof.
    intros md p.
    unfold metadata_provenance.
    unfold metadata_set_provenance.
    pose proof (metadata_modify_provenance_spec md (const p)) as (?&?&?).
    rewrite H.
    cbn.
    pose proof (metadata_modify_provenance_spec x id) as (?&?&?).
    cbn in *.
    unfold id, const in *; subst; auto.
  Qed.

  #[global] Hint Resolve
    metadata_get_set_provenance
    metadata_set_provenance : MEM.

End METADATA_PROVENANCE_ID.

Module Fin_HAS_ITOP <: HAS_ITOP N_ProvSet FinAddrType Fin_HAS_METADATA.
  Definition int_to_ptr :=
    fun (i : Z) (pr : Prov) =>
      if (i <? 0)%Z || (i >=? @Integers.modulus 64)%Z
      then Oom ("FinITOP.int_to_ptr: out of range (" ++ show i ++ ").")
      else NoOom (@Integers.repr 64 i, pr).

  Lemma int_to_ptr_metadata :
    forall (x : Z) (p : N_ProvSet.t) (a : FinAddrType.t),
      int_to_ptr x p = ret a ->
      Fin_HAS_METADATA.extract_metadata a = p.
  Proof.
    intros x p a H.
    destruct a; cbn in *.
    unfold int_to_ptr in *.
    break_match_hyp_inv; auto.
  Qed.
End Fin_HAS_ITOP.

Module Fin_PTOI_ITOP_EXTRA <: PTOI_ITOP_EXTRA N_ProvSet FinAddrType Fin_PTOI_HAS_POINTER_ARITHMETIC Fin_HAS_METADATA Fin_HAS_ITOP FinPTOI.
  Import FinPTOI Fin_HAS_METADATA Fin_HAS_ITOP Fin_PTOI_HAS_POINTER_ARITHMETIC.
  Lemma int_to_ptr_ptr_to_int :
    forall (a : FinAddrType.t) (p : N_ProvSet.t),
      extract_metadata a = p ->
      int_to_ptr (ptr_to_int a) p = ret a.
  Proof.
    intros a p H.
    cbn in *.
    unfold int_to_ptr, ptr_to_int, extract_metadata in *.
    pose proof (Integers.unsigned_range (fst a)).
    break_match; try lia.
    rewrite Integers.repr_unsigned.
    destruct a; cbn in *; subst; auto.
  Qed.

  Lemma int_to_ptr_ptr_to_int_exists :
    forall (a : FinAddrType.t) (p : N_ProvSet.t),
    exists a',
      int_to_ptr (ptr_to_int a) p = ret a' /\
        ptr_to_int a' = ptr_to_int a /\
        extract_metadata a' = p.
  Proof.
    intros a p.
    destruct a.
    exists (i, p).
    unfold int_to_ptr, ptr_to_int, extract_metadata in *.
    pose proof (Integers.unsigned_range i); cbn in *.
    break_match; try lia.
    rewrite Integers.repr_unsigned.
    cbn; auto.
  Qed.

  Lemma ptr_to_int_int_to_ptr :
    forall (x : Z) (p : N_ProvSet.t) (a : FinAddrType.t),
      int_to_ptr x p = ret a ->
      ptr_to_int a = x.
  Proof.
    intros x p a H.
    unfold int_to_ptr, ptr_to_int, extract_metadata in *.
    break_match_hyp_inv.
    cbn.
    apply (@Integers.unsigned_repr 64 x); auto.
    unfold Integers.max_unsigned; lia.
  Qed.

  Lemma ptr_add_metadata :
    forall a x p,
      ptr_add a x = inr p ->
      extract_metadata p = extract_metadata a.
  Proof.
    intros a x p ADD.
    destruct a; cbn in *.
    break_match_hyp_inv; cbn; auto.
  Qed.
End Fin_PTOI_ITOP_EXTRA.

Module FinAddr <: ADDRESS N_ProvSet N_ProvSet := FinAddrType <+ FinNull <+ FinPTOI <+ Fin_HAS_NULL_PTOI <+ Fin_PTOI_HAS_POINTER_ARITHMETIC <+ Fin_PTOI_ARITH_EXTRAS <+ METADATA_PROVENANCE_ID N_ProvSet <+ Fin_HAS_METADATA <+ HAS_PROVENANCE N_ProvSet N_ProvSet <+ Fin_HAS_ITOP <+ Fin_PTOI_ITOP_EXTRA <+ PTOI_ITOP_ARITH_EXTRA N_ProvSet.
