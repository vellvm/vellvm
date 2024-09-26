From Coq Require Import
  Lia
  Morphisms.

From Vellvm Require Import
  Numeric.Coqlib
  Utils.Error.

From Mem Require Import
  Addresses.MemoryAddress
  Memory.Provenance
  Addresses.Provenance.

From QuickChick Require Import Show.

From ExtLib Require Import
  Structures.Functor
  Structures.Monads.

From Coq Require Import
  Structures.Equalities.

Import ListNotations.

(** ** Type of pointers
    Implementation of the notion of pointer used: an address and an offset.
 *)
Definition Iptr := Z. (* Integer pointer type (physical addresses) *)

(* TODO: Should probably make this an NSet, but it gives universe inconsistency with Module addr *)
Definition Prov := option (list Provenance). (* Provenance *)

Definition wildcard_prov : Prov := None.
Definition nil_prov : Prov := Some [].

(* TODO: If Prov is an NSet, I get a universe inconsistency here... *)
Module InfAddrType <: CORE_ADDRESS.
  Definition t := (Iptr * Prov) % type.
  Definition eq := @Logic.eq t.

  (* TODO: is this what we should be using for equality on pointers? Probably *NOT* because of provenance. *)
  Lemma eq_dec : forall (a b : t), {a = b} + {a <> b}.
  Proof.
    intros [a1 a2] [b1 b2].

    destruct (Z.eq_dec a1 b1);
      destruct (option_eq (fun x y => list_eq_dec N.eq_dec x y) a2 b2); subst.
    - left; reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
  Qed.

  #[global] Instance eq_equiv : Equivalence eq.
  typeclasses eauto.
  Defined.
End InfAddrType.

Module InfNull <: HAS_NULL InfAddrType.
  Definition null := (0, nil_prov)%Z.

  Definition is_null (a : InfAddrType.t) : bool :=
    Z.eqb (fst null) (fst a).

  Lemma null_is_null :
    is_null null = true.
  Proof.
    reflexivity.
  Qed.
End InfNull.

Module InfPTOI <: HAS_PTOI InfAddrType.
  Definition ptr_to_int := fun (ptr : InfAddrType.t) => fst ptr.
End InfPTOI.

Module Type Inf_HAS_POINTER_ARITHMETIC_CORE <: HAS_POINTER_ARITHMETIC_CORE InfAddrType.
  (** Pointer addition. May error if the result cannot be represented
      as a pointer, e.g., if it would be out of bounds.
   *)
  Definition ptr_add (a : InfAddrType.t) (i : Z) : err InfAddrType.t
    := match a with
       | (ptr, pr) =>
           let res := ptr + i in
           ret (res, pr)
       end.

  Lemma ptr_add_0 :
    forall ptr,
      ptr_add ptr 0 = inr ptr.
  Proof.
    intros ptr.
    unfold ptr_add.
    destruct ptr.
    rewrite Z.add_0_r in *.
    reflexivity.
  Qed.
End Inf_HAS_POINTER_ARITHMETIC_CORE.

Module Inf_PTOI_HAS_POINTER_ARITHMETIC <: HAS_POINTER_ARITHMETIC InfAddrType := Inf_HAS_POINTER_ARITHMETIC_CORE  <+ HAS_POINTER_ARITHMETIC_HELPERS InfAddrType.

Module Inf_PTOI_ARITH_EXTRAS <: PTOI_ARITH_EXTRAS InfAddrType InfPTOI Inf_PTOI_HAS_POINTER_ARITHMETIC.
  Import InfPTOI.
  Import Inf_PTOI_HAS_POINTER_ARITHMETIC.
  Lemma ptr_to_int_ptr_add :
    forall (ptr ptr' : InfAddrType.t) (x : Z),
      ptr_add ptr x = inr ptr' ->
      ptr_to_int ptr' = ptr_to_int ptr + x.
  Proof.
    intros ptr ptr' x H.
    unfold ptr_to_int.
    unfold ptr_add in *.
    cbn in *.
    destruct ptr, ptr'; cbn in *.
    inv H.
    reflexivity.
  Qed.
End Inf_PTOI_ARITH_EXTRAS.

Module Inf_HAS_METADATA <: HAS_METADATA N_ProvSet InfAddrType.
  Definition extract_metadata (addr : InfAddrType.t) : N_ProvSet.t :=
    snd addr.
End Inf_HAS_METADATA.

(* TODO: Move to utility *)
Module METADATA_PROVENANCE_ID (MD : Typ) <: METADATA_PROVENANCE MD MD.
  Definition metadata_provenance (md : MD.t) := md.
End METADATA_PROVENANCE_ID.

Module Inf_HAS_ITOP <: HAS_ITOP N_ProvSet InfAddrType Inf_HAS_METADATA.
  Definition int_to_ptr (x : Z) (pr : N_ProvSet.t) : OOM InfAddrType.t
    := NoOom (x, pr).

  Lemma int_to_ptr_metadata :
    forall (x : Z) (p : N_ProvSet.t) (a : InfAddrType.t),
      int_to_ptr x p = ret a ->
      Inf_HAS_METADATA.extract_metadata a = p.
  Proof.
    intros x p a H.
    destruct a; cbn in *.
    unfold int_to_ptr in *.
    inv H; auto.
  Qed.
End Inf_HAS_ITOP.

Module Inf_ITOP_BIG <: ITOP_BIG N_ProvSet InfAddrType Inf_HAS_METADATA Inf_HAS_ITOP.
  Import Inf_HAS_ITOP.
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
End Inf_ITOP_BIG.

Module Inf_PTOI_ITOP_EXTRA <: PTOI_ITOP_EXTRA N_ProvSet InfAddrType Inf_HAS_METADATA Inf_HAS_ITOP InfPTOI.
  Import InfPTOI Inf_HAS_METADATA Inf_HAS_ITOP.
  Lemma int_to_ptr_ptr_to_int :
    forall (a : InfAddrType.t) (p : N_ProvSet.t),
      extract_metadata a = p ->
      int_to_ptr (ptr_to_int a) p = ret a.
  Proof.
    intros a p H.
    cbn in *.
    unfold int_to_ptr, ptr_to_int, extract_metadata in *.
    destruct a; cbn in *; subst; auto.
  Qed.

  Lemma int_to_ptr_ptr_to_int_exists :
    forall (a : InfAddrType.t) (p : N_ProvSet.t),
    exists a',
      int_to_ptr (ptr_to_int a) p = ret a' /\
        ptr_to_int a' = ptr_to_int a /\
        extract_metadata a' = p.
  Proof.
    intros a p.
    destruct a.
    exists (i, p).
    unfold int_to_ptr, ptr_to_int, extract_metadata in *.
    cbn; auto.
  Qed.

  Lemma ptr_to_int_int_to_ptr :
    forall (x : Z) (p : N_ProvSet.t) (a : InfAddrType.t),
      int_to_ptr x p = ret a ->
      ptr_to_int a = x.
  Proof.
    intros x p a H.
    unfold int_to_ptr, ptr_to_int, extract_metadata in *.
    inv H; cbn; auto.
  Qed.
End Inf_PTOI_ITOP_EXTRA.

Module InfAddr <: INFINITE_ADDRESS N_ProvSet N_ProvSet := InfAddrType <+ InfNull <+ InfPTOI <+ Inf_PTOI_HAS_POINTER_ARITHMETIC <+ Inf_PTOI_ARITH_EXTRAS <+ METADATA_PROVENANCE_ID N_ProvSet <+ Inf_HAS_METADATA <+ HAS_PROVENANCE N_ProvSet N_ProvSet <+ Inf_HAS_ITOP <+ Inf_ITOP_BIG <+ Inf_PTOI_ITOP_EXTRA.
