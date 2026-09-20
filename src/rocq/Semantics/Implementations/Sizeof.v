From Vellvm Require Import
  Utils
  Syntax.

From Vellvm.Semantics Require Import
  DynamicValues
  Interfaces.Sizeof.

(* TODO: make parameter? *)
Definition ptr_size : nat := 8.

Definition Dtyp_base_alignment (dt : dtyp_base) : alignment :=
  match dt with  
    | DTYPE_I sz =>
        if Pos.leb sz 8
        then Build_alignment 1 1
        else if Pos.leb sz 16
             then Build_alignment 2 2
             else if Pos.leb sz 32
                  then Build_alignment 4 4
                  else Build_alignment 4 8
    | DTYPE_Iptr => Build_alignment 8 8
    | DTYPE_Pointer => Build_alignment 8 8
    | DTYPE_Void => Build_alignment 1 1
    | DTYPE_FP FP_half => Build_alignment 2 2
    | DTYPE_FP FP_bfloat => Build_alignment 2 2  (* same as for half? *)
    | DTYPE_FP FP_float => Build_alignment 4 4
    | DTYPE_FP FP_double => Build_alignment 8 8
    | DTYPE_FP FP_x86_fp80 => Build_alignment 16 16  (* Not sure if this is right *)
    | DTYPE_FP FP_fp128 => Build_alignment 16 16
    | DTYPE_FP FP_ppc_fp128 => Build_alignment 16 16
    | DTYPE_Label => Build_alignment 8 8 (* treat labels as pointers? *)
    | DTYPE_Token => Build_alignment 8 8 (* not sure what alignment for token values *)
    | DTYPE_Metadata => Build_alignment 1 1
    | DTYPE_X86_mmx => Build_alignment 8 8 (* I assume these are 64-bit, but I'm not sure *)
    | DTYPE_Opaque => Build_alignment 1 1
    | DTYPE_B sz =>
        if Pos.leb sz 8
        then Build_alignment 1 1
        else if Pos.leb sz 16
             then Build_alignment 2 2
             else if Pos.leb sz 32
                  then Build_alignment 4 4
                  else Build_alignment 4 8
  end.  

(* Default alignment matching LLVMs defaults *)
Definition max_alignment (a b : alignment) : alignment :=
  Build_alignment
    (N.max (abi_alignment a) (abi_alignment b))
    (N.max (preferred_alignment a) (preferred_alignment b)).

Fixpoint Dtyp_alignment (dt : dtyp) : alignment :=
  (* TODO: 64-bit+ vectors should be 128-bit aligned *)
  match dt with
  | DTYPE_Base t => Dtyp_base_alignment t
  (* "Structures may optionally be “packed” structures, which indicate that the alignment of the
     struct is one byte, and that there is no padding between the elements." *)
  | DTYPE_Struct true fields => Build_alignment 1 1
  (* "Structures and unions assume the alignment of their most strictly aligned component." *)
  | DTYPE_Struct false fields =>
      fold_left (fun acc f => max_alignment acc (Dtyp_alignment f)) fields
        (Build_alignment 1 1)
  (* "An array uses the same alignment as its elements, except that a local or global array variable
     of length at least 16 bytes or a C99 variable-length array variable always has alignment of at
     least 16 bytes."
     Exception not implemented. *)
  | DTYPE_Array v sz t => Dtyp_alignment t
  end.

(* Same shape as [Dtyp_alignment]'s struct fold, and as the [Sizeof]-generic
   [Interfaces.Sizeof.max_preferred_dtyp_alignment]; the three then agree
   definitionally at [SizeofV]. *)
Definition max_preferred_dtyp_alignment (dts : list dtyp) : N :=
  fold_left (fun acc dt => N.max acc (preferred_alignment (Dtyp_alignment dt))) dts 1%N.

Definition round_up_to_eight (n : N) : N :=
  if N.eqb 0 n
  then 0
  else (((n - 1) / 8) + 1) * 8.


Definition byte_sizeof_floating_point_variant (fp : floating_point_variant) : N :=
  match fp with
  | FP_half => 2
  | FP_bfloat => 2
  | FP_float => 4
  | FP_double => 8
  | FP_x86_fp80 => 10
  | FP_fp128 => 16
  | FP_ppc_fp128 => 16
  end.

Definition bit_sizeof_floating_point_variant (fp : floating_point_variant) : N :=
  8 * (byte_sizeof_floating_point_variant fp).

Definition Bit_sizeof_dtyp_base (ty : dtyp_base) : N :=
  match ty with
  | DTYPE_I sz => Npos sz
  | DTYPE_Iptr => 64 (* TODO: probably kind of a lie... *)
  | DTYPE_Pointer => 64
  | DTYPE_Void => 0
  | DTYPE_FP fp => bit_sizeof_floating_point_variant fp
  | DTYPE_Label => 64
  | DTYPE_Token => 64 (* ??? *)
  | DTYPE_Metadata => 0
  | DTYPE_X86_mmx => 64
  | DTYPE_Opaque => 0
  | DTYPE_B sz => Npos sz
  end.

Fixpoint Bit_sizeof_dtyp (ty : dtyp) : N :=
  match ty with
  | DTYPE_Base t => Bit_sizeof_dtyp_base t
  | DTYPE_Struct false fields =>
      let sz := fold_left (fun acc x => pad_to_align_bitwise (Dtyp_alignment x) acc + (Bit_sizeof_dtyp x)%N) fields 0%N in
      let max_align := 8 * (max_preferred_dtyp_alignment fields) in
      pad_to max_align sz
  | DTYPE_Struct true fields =>
      fold_left (fun acc x => (acc + round_up_to_eight (Bit_sizeof_dtyp x))%N) fields 0%N
  | DTYPE_Array false sz t => sz * (round_up_to_eight (Bit_sizeof_dtyp t))
  | DTYPE_Array true sz t => sz * Bit_sizeof_dtyp t
  end.

Definition Sizeof_dtyp_base (ty:dtyp_base) : N :=
  match ty with
  | DTYPE_Void         => 0
  | DTYPE_I sz         => N.div (round_up_to_eight (Npos sz)) 8
  | DTYPE_Iptr         => N.of_nat ptr_size
  | DTYPE_Pointer      => N.of_nat ptr_size
  | DTYPE_FP fp        => byte_sizeof_floating_point_variant fp
  | DTYPE_Label        => 8
  | DTYPE_Token        => 8
  | DTYPE_Metadata     => 0
  | DTYPE_X86_mmx      => 8 (* TODO: Unsupported *)
  | DTYPE_Opaque       => 0 (* TODO: Unsupported *)
  | DTYPE_B sz         => N.div (round_up_to_eight (Npos sz)) 8
  end.

                           
(* The store size.  At each recursive position the *alloc* size is what a
   layout advances by, so [pad_to_align (Dtyp_alignment t) (Store_size_dtyp t)]
   is inlined here -- that is exactly [alloc_size_dtyp t] once [SizeofV] is in
   scope, which [Store_size_alloc_size] below records. *)
Fixpoint Store_size_dtyp (ty:dtyp) : N :=
  let Alloc_size_dtyp t := pad_to_align (Dtyp_alignment t) (Store_size_dtyp t) in
  match ty with
  | DTYPE_Base t => Sizeof_dtyp_base t
  | DTYPE_Struct true l =>
      (* packed: no offset alignment and no tail padding, but fields still
         advance by their alloc size (cf. LLVM's StructLayout) *)
      fold_left (fun acc x => (acc + Alloc_size_dtyp x)%N) l 0%N
  | DTYPE_Struct false l =>
      let sz := fold_left (fun acc x => pad_to_align (Dtyp_alignment x) acc + (Alloc_size_dtyp x)%N) l 0%N in
      let max_align := max_preferred_dtyp_alignment l in
      pad_to max_align sz
  | DTYPE_Array false sz ty' =>
      sz * (Alloc_size_dtyp ty')
  | DTYPE_Array true sz ty' =>
      (* vectors are bit-packed: elements are contiguous *)
      sz * (Store_size_dtyp ty')
  end.

Instance SizeofV : Sizeof :=
  {|
    bit_sizeof_dtyp := Bit_sizeof_dtyp ;
    store_size_dtyp := Store_size_dtyp ;
    dtyp_alignment := Dtyp_alignment
  |}.

(* [alloc_size_dtyp] at [SizeofV] is the [Alloc_size_dtyp] inlined above. *)
Lemma Store_size_alloc_size : forall t,
    @alloc_size_dtyp SizeofV t = pad_to_align (Dtyp_alignment t) (Store_size_dtyp t).
Proof. reflexivity. Qed.

Lemma struct_fields_extent_V : forall packed l,
    @struct_fields_extent SizeofV packed l =
      fold_left (fun acc x =>
                   N.add (if packed then acc else pad_to_align (Dtyp_alignment x) acc)
                         (pad_to_align (Dtyp_alignment x) (Store_size_dtyp x))) l 0%N.
Proof. reflexivity. Qed.

(* The preferred alignment of a non-packed struct is the running max over its
   fields -- which is exactly how [max_preferred_dtyp_alignment] is defined.
   Both sides are a [fold_left]; only the accumulator type differs, so the
   induction just has to commute [preferred_alignment] with the fold. *)
Lemma preferred_Dtyp_alignment_Struct : forall dts,
    preferred_alignment (Dtyp_alignment (DTYPE_Struct false dts))
    = max_preferred_dtyp_alignment dts.
Proof.
  intros dts; cbn [Dtyp_alignment]; unfold max_preferred_dtyp_alignment.
  assert (H : forall ds acc n, preferred_alignment acc = n ->
             preferred_alignment
               (fold_left (fun a f => max_alignment a (Dtyp_alignment f)) ds acc)
             = fold_left (fun a dt => N.max a (preferred_alignment (Dtyp_alignment dt))) ds n).
  { intros ds; induction ds as [| d ds' IH]; intros acc n Heq; cbn; auto.
    apply IH; cbn; now rewrite Heq. }
  now apply H.
Qed.

Instance SizeofTheoryV : @SizeofTheory SizeofV.
Proof.
  (* the size laws hold by computation: [struct_fields_extent] and
     [alloc_size_dtyp] at [SizeofV] are exactly the forms inlined in
     [Store_size_dtyp] *)
  constructor; try reflexivity.
  - lia.
  - (* a non-packed struct is self-aligned: its store size already ends in
       [pad_to (max_preferred_dtyp_alignment dts) _] *)
    intros dts.
    unfold alloc_size_dtyp, pad_to_align; cbn [dtyp_alignment SizeofV].
    rewrite preferred_Dtyp_alignment_Struct.
    cbn [store_size_dtyp SizeofV Store_size_dtyp]; apply pad_to_idem.
Qed.
