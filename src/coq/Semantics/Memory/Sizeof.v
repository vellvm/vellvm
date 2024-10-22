From Coq Require Import
         ZArith
         List.

From Vellvm Require Import
  DynamicTypes
  Utils.ListUtil.

Definition pad_amount (alignment : N) (offset : N) :=
  ((alignment - (offset mod alignment)) mod alignment)%N.

Definition pad_to (alignment : N) (sz : N) :=
  (sz + pad_amount alignment sz)%N.

Record alignment :=
  { abi_alignment : N  (** Required alignment in bytes *)
  ; preferred_alignment : N  (** Preferred alignment in bytes *)
  }.

Definition pad_to_align (align : alignment) (sz : N) :=
  pad_to (preferred_alignment align) sz.

Definition pad_to_align_bitwise (align : alignment) (sz : N) :=
  pad_to ((preferred_alignment align) * 8) sz.

Module Type Sizeof.
  (** ** Size of a dynamic type in bits *)
  Parameter bit_sizeof_dtyp : dtyp -> N.

  (** ** Size of a dynamic type
      Computes the byte size of a [dtyp]. *)
  Parameter sizeof_dtyp : dtyp -> N.

  Parameter sizeof_dtyp_void : sizeof_dtyp DTYPE_Void = 0%N.
  Parameter sizeof_dtyp_pos :
    forall dt,
      (0 <= sizeof_dtyp dt)%N.

  (** Alignment of a dtyp *)
  Parameter dtyp_alignment : dtyp -> alignment.

  Definition max_preferred_dtyp_alignment (dts : list dtyp) : N :=
    match maximumByOpt (fun dt1 dt2 => preferred_alignment (dtyp_alignment dt1) <? preferred_alignment (dtyp_alignment dt1))%N dts with
    | Some dt =>
        preferred_alignment (dtyp_alignment dt)
    | None => 1
    end.

  Parameter sizeof_dtyp_Struct :
    forall dts,
      sizeof_dtyp (DTYPE_Struct dts) = pad_to (max_preferred_dtyp_alignment dts) (List.fold_left (fun acc dt => N.add (pad_to_align (dtyp_alignment dt) acc) (sizeof_dtyp dt)) dts 0%N).
    
  Parameter sizeof_dtyp_Packed_struct :
    forall dts,
      sizeof_dtyp (DTYPE_Packed_struct dts) = List.fold_left (fun acc dt => N.add acc (sizeof_dtyp dt)) dts 0%N.

  Parameter sizeof_dtyp_array :
    forall sz t,
      sizeof_dtyp (DTYPE_Array sz t) = (sz * sizeof_dtyp t)%N.

  Parameter sizeof_dtyp_vector :
    forall sz t,
      sizeof_dtyp (DTYPE_Vector sz t) = (sz * sizeof_dtyp t)%N.

  Parameter sizeof_dtyp_i8 :
    sizeof_dtyp (DTYPE_I 8) = 1%N.
End Sizeof.

(* Derived functions / constants on Sizeof. *)
Module Sizeof_helpers(SIZEOF:Sizeof).
  Import SIZEOF.

  Definition ptr_size : N := sizeof_dtyp DTYPE_Pointer.
End Sizeof_helpers.
