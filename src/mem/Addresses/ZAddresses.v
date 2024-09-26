From Coq Require Import
  Lia
  Morphisms.

From Vellvm Require Import
  Numeric.Coqlib
  Utils.Error.

From Mem Require Import
  Addresses.MemoryAddress
  Addresses.TypeModules
  Memory.Provenance
  Addresses.Provenance.

From QuickChick Require Import Show.

From ExtLib Require Import
  Structures.Functor
  Structures.Monads.

From Coq Require Import
  Structures.Equalities.

Import ListNotations.

Module ZAddrType <: CORE_ADDRESS.
  Definition t := Z.
  Definition eq := @Logic.eq t.

  (* TODO: is this what we should be using for equality on pointers? Probably *NOT* because of provenance. *)
  Lemma eq_dec : forall (a b : t), {a = b} + {a <> b}.
  Proof.
    intros a b.
    destruct (Z.eq_dec a b); subst; auto.
  Qed.

  #[global] Instance eq_equiv : Equivalence eq.
  typeclasses eauto.
  Defined.
End ZAddrType.

Module ZNull <: HAS_NULL ZAddrType.
  Definition null := 0%Z.

  Definition is_null (a : ZAddrType.t) : bool := Z.eqb null a.

  Lemma null_is_null :
    is_null null = true.
  Proof.
    reflexivity.
  Qed.
End ZNull.

Module Z_PTOI <: HAS_PTOI ZAddrType.
  Definition ptr_to_int := fun (ptr : ZAddrType.t) => ptr.
End Z_PTOI.

Module Type Z_HAS_POINTER_ARITHMETIC_CORE <: HAS_POINTER_ARITHMETIC_CORE ZAddrType.
  (** Pointer addition. May error if the result cannot be represented
      as a pointer, e.g., if it would be out of bounds.
   *)
  Definition ptr_add (a : ZAddrType.t) (i : Z) : err ZAddrType.t
    := ret (a + i).

  Lemma ptr_add_0 :
    forall ptr,
      ptr_add ptr 0 = inr ptr.
  Proof.
    intros ptr.
    unfold ptr_add.
    rewrite Z.add_0_r in *.
    reflexivity.
  Qed.
End Z_HAS_POINTER_ARITHMETIC_CORE.

Module Z_PTOI_HAS_POINTER_ARITHMETIC <: HAS_POINTER_ARITHMETIC ZAddrType := Z_HAS_POINTER_ARITHMETIC_CORE  <+ HAS_POINTER_ARITHMETIC_HELPERS ZAddrType.

Module Z_PTOI_ARITH_EXTRAS <: PTOI_ARITH_EXTRAS ZAddrType Z_PTOI Z_PTOI_HAS_POINTER_ARITHMETIC.
  Import Z_PTOI.
  Import Z_PTOI_HAS_POINTER_ARITHMETIC.
  Lemma ptr_to_int_ptr_add :
    forall (ptr ptr' : ZAddrType.t) (x : Z),
      ptr_add ptr x = inr ptr' ->
      ptr_to_int ptr' = ptr_to_int ptr + x.
  Proof.
    intros ptr ptr' x H.
    unfold ptr_to_int.
    unfold ptr_add in *.
    cbn in *.
    inv H.
    reflexivity.
  Qed.
End Z_PTOI_ARITH_EXTRAS.

Module Z_HAS_METADATA <: HAS_METADATA UNIT_TYP ZAddrType.
  Definition extract_metadata (addr : ZAddrType.t) : unit := tt.
End Z_HAS_METADATA.

Module Z_HAS_ITOP <: HAS_ITOP UNIT_TYP ZAddrType Z_HAS_METADATA.
  Definition int_to_ptr (x : Z) (pr : unit) : OOM ZAddrType.t
    := ret x.

  Lemma int_to_ptr_metadata :
    forall (x : Z) (p : unit) (a : ZAddrType.t),
      int_to_ptr x p = ret a ->
      Z_HAS_METADATA.extract_metadata a = p.
  Proof.
    intros x p a H.
    unfold Z_HAS_METADATA.extract_metadata.
    destruct p; auto.
  Qed.
End Z_HAS_ITOP.

Module Z_ITOP_BIG <: ITOP_BIG UNIT_TYP ZAddrType Z_HAS_METADATA Z_HAS_ITOP.
  Import Z_HAS_ITOP.
  Lemma int_to_ptr_safe :
    forall z pr,
      match int_to_ptr z pr with
      | NoOom _ => True
      | Oom _ => False
      end.
  Proof.
    intros z pr.
    cbn; auto.
  Qed.
End Z_ITOP_BIG.

Module Z_PTOI_ITOP_EXTRA <: PTOI_ITOP_EXTRA UNIT_TYP ZAddrType Z_HAS_METADATA Z_HAS_ITOP Z_PTOI.
  Import Z_PTOI Z_HAS_METADATA Z_HAS_ITOP.
  Lemma int_to_ptr_ptr_to_int :
    forall (a : ZAddrType.t) (p : unit),
      extract_metadata a = p ->
      int_to_ptr (ptr_to_int a) p = ret a.
  Proof.
    intros a p H.
    cbn in *.
    unfold int_to_ptr, ptr_to_int, extract_metadata in *.
    destruct a; cbn in *; subst; auto.
  Qed.

  Lemma int_to_ptr_ptr_to_int_exists :
    forall (a : ZAddrType.t) (p : unit),
    exists a',
      int_to_ptr (ptr_to_int a) p = ret a' /\
        ptr_to_int a' = ptr_to_int a /\
        extract_metadata a' = p.
  Proof.
    intros a [].
    exists a.
    unfold int_to_ptr, ptr_to_int, extract_metadata in *.
    cbn; auto.
  Qed.

  Lemma ptr_to_int_int_to_ptr :
    forall (x : Z) (p : unit) (a : ZAddrType.t),
      int_to_ptr x p = ret a ->
      ptr_to_int a = x.
  Proof.
    intros x p a H.
    unfold int_to_ptr, ptr_to_int, extract_metadata in *.
    inv H; cbn; auto.
  Qed.
End Z_PTOI_ITOP_EXTRA.

Module ZAddr := ZAddrType <+ ZNull <+ Z_PTOI <+ Z_PTOI_HAS_POINTER_ARITHMETIC <+ Z_PTOI_ARITH_EXTRAS <+ Z_HAS_METADATA <+ Z_HAS_ITOP <+ Z_ITOP_BIG <+ Z_PTOI_ITOP_EXTRA.
