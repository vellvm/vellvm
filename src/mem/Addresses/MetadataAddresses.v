From Coq Require Import
  Lia
  Morphisms.

From Vellvm Require Import
  Numeric.Coqlib
  Utils.Error
  Utils.Tactics.

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
Import MonadNotation.
Import HeterogeneousRelations.

Module Type MetadataAddrType (METADATA : DecidableType) (ADDR : CORE_ADDRESS) <: CORE_ADDRESS.
  Definition t := (ADDR.t * METADATA.t)%type.
  Definition eq := prod_rel ADDR.eq METADATA.eq.

  (* TODO: is this what we should be using for equality on pointers? Probably *NOT* because of provenance. *)
  Lemma eq_dec : forall (a b : t), {eq a b} + {not (eq a b)}.
  Proof.
    intros [a1 a2] [b1 b2].

    destruct (ADDR.eq_dec a1 b1);
      destruct (METADATA.eq_dec a2 b2); subst; unfold eq; cbn in *.
    - left.
      constructor; cbn; auto.
    - right. intros H. inversion H; subst. cbn in *; apply n; auto.
    - right. intros H. inversion H; subst. cbn in *; apply n; auto.
    - right. intros H. inversion H; subst. cbn in *; apply n; auto.
  Qed.

  #[global] Instance eq_equiv : Equivalence eq.
  typeclasses eauto.
  Defined.
End MetadataAddrType.

Module MetadataNull (METADATA : DecidableType) (Import DEF : HasDefault METADATA) (ADDR : CORE_ADDRESS) (NULL : HAS_NULL ADDR) (META_ADDR : MetadataAddrType METADATA ADDR) <: HAS_NULL META_ADDR.
  Definition null := (NULL.null, default).

  Definition is_null (a : META_ADDR.t) : bool :=
    NULL.is_null (fst a).

  Lemma null_is_null :
    is_null null = true.
  Proof.
    unfold is_null.
    cbn.
    apply NULL.null_is_null.
  Qed.
End MetadataNull.

Module Type METADATA_PTOI (METADATA : DecidableType) (ADDR : CORE_ADDRESS) (PTOI : HAS_PTOI ADDR) (META_ADDR : MetadataAddrType METADATA ADDR) <: HAS_PTOI META_ADDR.
  Definition ptr_to_int := fun (ptr : META_ADDR.t) => PTOI.ptr_to_int (fst ptr).
End METADATA_PTOI.

Module Type METADATA_ADDR_HAS_POINTER_ARITHMETIC_CORE (METADATA : DecidableType) (ADDR : CORE_ADDRESS) (ARITH : HAS_POINTER_ARITHMETIC_CORE ADDR) (META_ADDR : MetadataAddrType METADATA ADDR) <: HAS_POINTER_ARITHMETIC_CORE META_ADDR.
  (** Pointer addition. May error if the result cannot be represented
      as a pointer, e.g., if it would be out of bounds.
   *)
  Definition ptr_add (a : META_ADDR.t) (i : Z) : err META_ADDR.t
    := p <- ARITH.ptr_add (fst a) i;;
       ret (p, snd a).

  Lemma ptr_add_0 :
    forall ptr,
      ptr_add ptr 0 = inr ptr.
  Proof.
    intros ptr.
    unfold ptr_add.
    cbn.
    rewrite ARITH.ptr_add_0.
    destruct ptr; reflexivity.
  Qed.
End METADATA_ADDR_HAS_POINTER_ARITHMETIC_CORE.

Module Type METADATA_PTOI_HAS_POINTER_ARITHMETIC
  (METADATA : DecidableType) (ADDR : CORE_ADDRESS) (ARITH : HAS_POINTER_ARITHMETIC_CORE ADDR) (META_ADDR : MetadataAddrType METADATA ADDR)
  := METADATA_ADDR_HAS_POINTER_ARITHMETIC_CORE METADATA ADDR ARITH META_ADDR <+ HAS_POINTER_ARITHMETIC_HELPERS META_ADDR.

Module Type METADATA_PTOI_ARITH_EXTRAS
  (METADATA : DecidableType) (ADDR : CORE_ADDRESS) (PTOI : HAS_PTOI ADDR) (ARITH : HAS_POINTER_ARITHMETIC ADDR) (ARITH_EXTRAS : PTOI_ARITH_EXTRAS ADDR PTOI ARITH) (META_ADDR : MetadataAddrType METADATA ADDR) (META_PTOI : METADATA_PTOI METADATA ADDR PTOI META_ADDR) (META_ARITH : METADATA_PTOI_HAS_POINTER_ARITHMETIC METADATA ADDR ARITH META_ADDR)
<: PTOI_ARITH_EXTRAS META_ADDR META_PTOI META_ARITH.
  Import META_PTOI.
  Import META_ARITH.
  Lemma ptr_to_int_ptr_add :
    forall (ptr ptr' : META_ADDR.t) (x : Z),
      ptr_add ptr x = inr ptr' ->
      ptr_to_int ptr' = ptr_to_int ptr + x.
  Proof.
    intros ptr ptr' x H.
    unfold ptr_to_int.
    unfold ptr_add in *.
    cbn in *.
    destruct ptr, ptr'; cbn in *.
    destruct (ARITH.ptr_add t x) eqn:H'; inv H.
    apply ARITH_EXTRAS.ptr_to_int_ptr_add in H';
      auto.
  Qed.
End METADATA_PTOI_ARITH_EXTRAS.

Module Type METADATA_ADDR_HAS_METADATA
  (METADATA : DecidableType) (ADDR : CORE_ADDRESS) (META_ADDR : MetadataAddrType METADATA ADDR) <: HAS_METADATA METADATA META_ADDR.
  Definition extract_metadata (addr : META_ADDR.t) : METADATA.t := snd addr.
End METADATA_ADDR_HAS_METADATA.

Module Type METADATA_HAS_ITOP
  (METADATA : DecidableType) (METADATA_ORIG : DecidableType) (Import DEF : HasDefault METADATA_ORIG) (ADDR : CORE_ADDRESS) (HMD_ORIG : HAS_METADATA METADATA_ORIG ADDR)  (ITOP : HAS_ITOP METADATA_ORIG ADDR HMD_ORIG) (META_ADDR : MetadataAddrType METADATA ADDR) (HMD : METADATA_ADDR_HAS_METADATA METADATA ADDR META_ADDR) <: HAS_ITOP METADATA META_ADDR HMD.
  Definition int_to_ptr (x : Z) (md : METADATA.t) : OOM META_ADDR.t
    := p <- ITOP.int_to_ptr x default;;
       ret (p, md).

  Lemma int_to_ptr_metadata :
    forall (x : Z) (md : METADATA.t) (a : META_ADDR.t),
      int_to_ptr x md = ret a ->
      HMD.extract_metadata a = md.
  Proof.
    intros x p a H.
    unfold HMD.extract_metadata.
    destruct a; unfold int_to_ptr in *.
    cbn in *.
    destruct (ITOP.int_to_ptr x default); inv H; auto.
  Qed.
End METADATA_HAS_ITOP.

Module METADATA_ITOP_BIG
  (MD : DecidableType) (MD_ORIG : DecidableType) (Import DEF : HasDefault MD_ORIG) (ADDR : CORE_ADDRESS) (HMD_ORIG : HAS_METADATA MD_ORIG ADDR)  (ITOP : HAS_ITOP MD_ORIG ADDR HMD_ORIG) (META_ADDR : MetadataAddrType MD ADDR) (HMD : METADATA_ADDR_HAS_METADATA MD ADDR META_ADDR)
  (MD_HAS_ITOP : METADATA_HAS_ITOP MD MD_ORIG DEF ADDR HMD_ORIG ITOP META_ADDR HMD)
  (ITOP_BIG_ORIG : ITOP_BIG MD_ORIG ADDR HMD_ORIG ITOP) <: ITOP_BIG MD META_ADDR HMD MD_HAS_ITOP.
  Import MD_HAS_ITOP.
  Lemma int_to_ptr_safe :
    forall z pr,
      match int_to_ptr z pr with
      | NoOom _ => True
      | Oom _ => False
      end.
  Proof.
    intros z pr.
    cbn; auto.
    pose proof ITOP_BIG_ORIG.int_to_ptr_safe z default.
    break_match_hyp; auto.
  Qed.
End METADATA_ITOP_BIG.

Module METADATA_PTOI_ITOP_EXTRA
  (MD : DecidableType) (ADDR : CORE_ADDRESS) (PTOI_ORIG : HAS_PTOI ADDR) (HMD_ORIG : HAS_METADATA UNIT_TYP ADDR)  (ITOP : HAS_ITOP UNIT_TYP ADDR HMD_ORIG) (META_ADDR : MetadataAddrType MD ADDR) (HMD : METADATA_ADDR_HAS_METADATA MD ADDR META_ADDR)
  (MD_HAS_ITOP : METADATA_HAS_ITOP MD UNIT_TYP UNIT_HAS_DEFAULT ADDR HMD_ORIG ITOP META_ADDR HMD)
  (PTOI : METADATA_PTOI MD ADDR PTOI_ORIG META_ADDR)
  (PTOI_EXTRA : PTOI_ITOP_EXTRA UNIT_TYP ADDR HMD_ORIG ITOP PTOI_ORIG)
<: PTOI_ITOP_EXTRA MD META_ADDR HMD MD_HAS_ITOP PTOI.
  Import PTOI HMD MD_HAS_ITOP.
  Lemma int_to_ptr_ptr_to_int :
    forall (a : META_ADDR.t) (md : MD.t),
      extract_metadata a = md ->
      int_to_ptr (ptr_to_int a) md = ret a.
  Proof.
    intros a md H.
    cbn in *.
    unfold int_to_ptr, ptr_to_int, extract_metadata in *.
    destruct a; cbn in *; subst; auto.
    rewrite PTOI_EXTRA.int_to_ptr_ptr_to_int; cbn; auto.
    unfold UNIT_HAS_DEFAULT.default.
    destruct HMD_ORIG.extract_metadata; auto.
  Qed.

  Lemma int_to_ptr_ptr_to_int_exists :
    forall (a : META_ADDR.t) (md : MD.t),
    exists a',
      int_to_ptr (ptr_to_int a) md = ret a' /\
        ptr_to_int a' = ptr_to_int a /\
        extract_metadata a' = md.
  Proof.
    intros [a md'] md.
    exists (a, md).
    unfold int_to_ptr, ptr_to_int, extract_metadata in *.
    cbn; split; auto.
    unfold UNIT_HAS_DEFAULT.default.
    pose proof PTOI_EXTRA.int_to_ptr_ptr_to_int_exists a tt as (?&?&?&?).
    rewrite H; cbn.
    rewrite PTOI_EXTRA.int_to_ptr_ptr_to_int in H; inv H; auto.
    destruct (HMD_ORIG.extract_metadata a); auto.
  Qed.

  Lemma ptr_to_int_int_to_ptr :
    forall (x : Z) (md : MD.t) (a : META_ADDR.t),
      int_to_ptr x md = ret a ->
      ptr_to_int a = x.
  Proof.
    intros x md a H.
    unfold int_to_ptr, ptr_to_int, extract_metadata in *.
    cbn in *.
    unfold UNIT_HAS_DEFAULT.default in *.
    break_match_hyp_inv.
    apply PTOI_EXTRA.ptr_to_int_int_to_ptr in Heqo.
    cbn; auto.
  Qed.
End METADATA_PTOI_ITOP_EXTRA.
