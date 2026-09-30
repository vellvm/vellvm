From Vellvm Require Import
  Utils
  Syntax.

Definition pad_amount (alignment : N) (offset : N) :=
  ((alignment - (offset mod alignment)) mod alignment)%N.

Definition pad_to (alignment : N) (sz : N) :=
  (sz + pad_amount alignment sz)%N.

Record alignment :=
  { abi_alignment : N  (** Required alignment in bytes *)
  ; preferred_alignment : N  (** Preferred alignment in bytes *)
  }.

(* SAZ/TODO: LLVM lays values out using the *ABI* alignment
   ([getABITypeAlign]); [preferred_alignment] is only an upper bound it may
   use for allocations it controls.  Vellvm currently uses the preferred
   alignment at every layout site, which is what these two helpers encode.
   Switching to [abi_alignment] is a separate (behaviour-changing) decision;
   keeping it in one place here makes it a one-line change when we make it. *)
Definition pad_to_align (align : alignment) (sz : N) :=
  pad_to (preferred_alignment align) sz.

Definition pad_to_align_bitwise (align : alignment) (sz : N) :=
  pad_to ((preferred_alignment align) * 8) sz.

Section PadLemmas.
  Local Open Scope N_scope.

Lemma pad_to_0 : forall (x:N), pad_to 0 x = x.
Proof. intros [|x]; reflexivity. Qed.

Lemma pad_to_mod : forall (a x : N), a <> 0%N -> ((pad_to a x) mod a = 0)%N.
Proof.
  intros a x Ha; unfold pad_to, pad_amount.
  pose proof (N.mod_upper_bound x a Ha) as U.
  rewrite N.Div0.add_mod, N.Div0.mod_mod.
  destruct (x mod a) as [|q] eqn:E.
  - rewrite N.sub_0_r, N.Div0.mod_same, N.add_0_l; apply N.Div0.mod_0_l.
  - assert (Hs : (a - N.pos q) mod a = a - N.pos q) by (apply N.mod_small; lia).
    rewrite Hs.
    replace (N.pos q + (a - N.pos q))%N with a by lia.
    apply N.Div0.mod_same.
Qed.

Lemma pad_amount_aligned : forall (a y : N), (y mod a = 0)%N -> pad_amount a y = 0%N.
Proof.
  intros a y H; unfold pad_amount; rewrite H, N.sub_0_r.
  destruct (N.eq_dec a 0) as [->|Ha]; [reflexivity | apply N.Div0.mod_same].
Qed.

Lemma pad_to_idem : forall (a x : N), pad_to a (pad_to a x) = pad_to a x.
Proof.
  intros a x; destruct (N.eq_dec a 0) as [->|Ha].
  - now rewrite !pad_to_0.
  - assert (H0 : pad_amount a (pad_to a x) = 0)
      by (apply pad_amount_aligned, pad_to_mod; auto).
    unfold pad_to at 1; rewrite H0; apply N.add_0_r.
Qed.

End PadLemmas.

(** * Sizes of dynamic types

    Following LLVM, a [dtyp] has two distinct byte sizes:

    - its **store size**, the number of bytes a value of that type actually
      occupies when written to memory ([getTypeStoreSize]); and

    - its **alloc size**, the store size rounded up to the type's alignment
      ([getTypeAllocSize] = [alignTo (getTypeStoreSize t) (align t)]).  This
      is the distance from one element of the type to the next when they are
      laid out consecutively.

    The two differ exactly when the store size is not already a multiple of
    the alignment -- [i24] (3 bytes, 4-byte aligned), [x86_fp80] (10 bytes,
    16-byte aligned), and similar.  Getting them confused is easy and
    invisible on well-behaved types like [i32]/[i64], where they coincide.

    Which one to use where:
    - what a [store]/[load] of type [t] transfers: store size;
    - the stride between array elements, and the advance from one struct
      field to the next: alloc size;
    - a non-packed struct's own size already includes its tail padding, so
      for structs store size = alloc size ([store_size_dtyp_Struct_alloc]).
*)
Class Sizeof : Type :=
  {
    (** ** Size of a dynamic type in bits *)
    bit_sizeof_dtyp : dtyp -> N;

    (** ** Store size of a dynamic type
      The number of bytes a value of this type occupies in memory. *)
    store_size_dtyp : dtyp -> N;

    (** Alignment of a dtyp *)
    dtyp_alignment : dtyp -> alignment;
  }.

(** ** Alloc size: the store size rounded up to the type's alignment.
    This is the element-to-element stride. *)
Definition alloc_size_dtyp `{Sizeof} (t : dtyp) : N :=
  pad_to_align (dtyp_alignment t) (store_size_dtyp t).

(* The alignment of a non-packed struct: the maximum over its fields,
   defaulting to 1.  Written as the same [fold_left] shape that
   [Dtyp_alignment] uses for structs, so that the two agree on the nose
   (see [preferred_Dtyp_alignment_Struct]). *)
Definition max_preferred_dtyp_alignment {S : Sizeof} (dts : list dtyp) : N :=
  List.fold_left (fun acc dt => N.max acc (preferred_alignment (dtyp_alignment dt))) dts 1%N.

Definition ptr_size `{Sizeof} : N := store_size_dtyp (DTYPE_Base DTYPE_Pointer).

(** The running offset after laying out the fields of a struct: each field is
    placed at its alignment (unless the struct is packed) and then advances the
    offset by its *alloc* size.  Mirrors LLVM's [StructLayout]. *)
Definition struct_fields_extent `{Sizeof} (packed : bool) (dts : list dtyp) : N :=
  List.fold_left
    (fun acc dt =>
       N.add (if packed then acc else pad_to_align (dtyp_alignment dt) acc)
             (alloc_size_dtyp dt))
    dts 0%N.

Class SizeofTheory {S : Sizeof} : Prop :=
  {
    store_size_dtyp_void : store_size_dtyp (DTYPE_Base DTYPE_Void) = 0%N;
    store_size_dtyp_pos :
    forall dt, (0 <= store_size_dtyp dt)%N;

    (** A non-packed struct places each field at its alignment, advances by the
        field's alloc size, and pads its own tail to the struct's alignment. *)
    store_size_dtyp_Struct :
    forall dts,
      store_size_dtyp (DTYPE_Struct false dts) =
        pad_to (max_preferred_dtyp_alignment dts) (struct_fields_extent false dts);

    (** A packed struct places fields back to back with no offset alignment and
        no tail padding -- but still advances by each field's alloc size, as
        LLVM's [StructLayout] does. *)
    store_size_dtyp_Packed_struct :
    forall dts,
      store_size_dtyp (DTYPE_Struct true dts) = struct_fields_extent true dts;

    (** Array elements are laid out at their alloc size. *)
    store_size_dtyp_array :
    forall sz t,
      store_size_dtyp (DTYPE_Array false sz t) = (sz * alloc_size_dtyp t)%N;

    (** Vectors are bit-packed: elements are contiguous, with no per-element
        padding.  (The vector's own alloc size may still exceed this.) *)
    store_size_dtyp_vector :
    forall sz t,
      store_size_dtyp (DTYPE_Array true sz t) = (sz * store_size_dtyp t)%N;

    store_size_dtyp_i8 :
    store_size_dtyp (DTYPE_Base (DTYPE_I 8)) = 1%N;

    (** A base type occupies whole bytes, as many as its bit width needs.

        Nothing above ties a base type's store size to its width, but the
        deserializer's bit arithmetic is keyed to exactly that: [DTYPE_I sz]
        splits on [sz mod 8] to decide whether the last byte is mixed, and
        [memory_byte_of_dvalue_bv] pads it accordingly.  Without these laws
        the writer and reader cannot be shown to invert each other
        ([read_base_block] in MemoryBytes.v). *)
    store_size_dtyp_int :
    forall sz, store_size_dtyp (DTYPE_Base (DTYPE_I sz)) = ((Npos sz + 7) / 8)%N;

    store_size_dtyp_bytes :
    forall sz, store_size_dtyp (DTYPE_Base (DTYPE_B sz)) = ((Npos sz + 7) / 8)%N;

    store_size_dtyp_float :
    store_size_dtyp (DTYPE_Base (DTYPE_FP FP_float)) = 4%N;

    store_size_dtyp_double :
    store_size_dtyp (DTYPE_Base (DTYPE_FP FP_double)) = 8%N;

    (** Pointers occupy at least one byte.  Needed so that a poison pointer
        serializes to a non-empty run: an empty byte list would read back as
        a concrete zero rather than poison. *)
    store_size_dtyp_ptr_pos :
    (0 < store_size_dtyp (DTYPE_Base DTYPE_Pointer))%N;

    store_size_dtyp_iptr_pos :
    (0 < store_size_dtyp (DTYPE_Base DTYPE_Iptr))%N;

    (** A non-packed struct is self-aligned: its store size already includes
        the tail padding, so it coincides with its alloc size.  This is what
        makes laying out consecutive structs by store size correct, and what
        keeps [store_size_dtyp]'s struct case from needing [alloc_size_dtyp]
        at its own type. *)
    store_size_dtyp_Struct_alloc :
    forall dts,
      alloc_size_dtyp (DTYPE_Struct false dts) = store_size_dtyp (DTYPE_Struct false dts);
  }.
