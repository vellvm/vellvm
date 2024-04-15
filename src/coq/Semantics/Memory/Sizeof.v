From Coq Require Import
         ZArith
         List.

From Vellvm Require Import
     DynamicTypes.


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

  (* Should take padding into account *)
  Parameter sizeof_dtyp_Struct :
    forall dts,
      sizeof_dtyp (DTYPE_Struct dts) = List.fold_left (fun acc dt => N.add acc (sizeof_dtyp dt)) dts 0%N.

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
