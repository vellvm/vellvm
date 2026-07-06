From Vellvm Require Import
  Utilities
  Syntax.

From Vellvm.Semantics Require Import
  DynamicValues
  Interfaces.Sizeof.

(* TODO: make parameter? *)
Definition ptr_size : nat := 8.

(* Default alignment matching LLVMs defaults *)
Definition Dtyp_alignment (dt : dtyp) : alignment
  := match dt with
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
     | DTYPE_Array sz t => Build_alignment 8 8
     | DTYPE_Struct fields => Build_alignment 8 8
     | DTYPE_Packed_struct fields => Build_alignment 8 8
     | DTYPE_Opaque => Build_alignment 1 1
     | DTYPE_Vector sz t =>
         (* Alignment depends on the size of the vector types *)
         (* TODO: 64-bit+ vectors should be 128-bit aligned *)
         Build_alignment 8 8
     end.

Definition max_preferred_dtyp_alignment (dts : list dtyp) : N :=
  match maximumByOpt (fun dt1 dt2 => preferred_alignment (Dtyp_alignment dt1) <? preferred_alignment (Dtyp_alignment dt1))%N dts with
  | Some dt =>
      preferred_alignment (Dtyp_alignment dt)
  | None => 1
  end.

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

Fixpoint Bit_sizeof_dtyp (ty : dtyp) : N :=
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
  | DTYPE_Array sz t => sz * (round_up_to_eight (Bit_sizeof_dtyp t))
  | DTYPE_Struct fields =>
      let sz := fold_left (fun acc x => pad_to_align_bitwise (Dtyp_alignment x) acc + (Bit_sizeof_dtyp x)%N) fields 0%N in
      let max_align := 8 * (max_preferred_dtyp_alignment fields) in
      pad_to max_align sz
  | DTYPE_Packed_struct fields =>
      fold_left (fun acc x => (acc + round_up_to_eight (Bit_sizeof_dtyp x))%N) fields 0%N
  | DTYPE_Opaque => 0
  | DTYPE_Vector sz t => sz * Bit_sizeof_dtyp t
  end.

Fixpoint Sizeof_dtyp (ty:dtyp) : N :=
  match ty with
  | DTYPE_Void         => 0
  | DTYPE_I sz         => N.max 1 (N.div (Npos sz) 8)
  | DTYPE_Iptr         => N.of_nat ptr_size
  | DTYPE_Pointer      => N.of_nat ptr_size
  | DTYPE_Packed_struct l =>
      fold_left (fun acc x => (acc + Sizeof_dtyp x)%N) l 0%N
  | DTYPE_Struct l =>
      let sz := fold_left (fun acc x => pad_to_align (Dtyp_alignment x) acc + (Sizeof_dtyp x)%N) l 0%N in
      let max_align := max_preferred_dtyp_alignment l in
      pad_to max_align sz
  | DTYPE_Vector sz ty'  (* TODO: Vector sizeof currently invalid for sub-bytesize / non-byte aligned elements. Changing this involves changing serialization. *)
  | DTYPE_Array sz ty' =>
      sz * (Sizeof_dtyp ty')
  | DTYPE_FP fp        => byte_sizeof_floating_point_variant fp
  | DTYPE_Label        => 8
  | DTYPE_Token        => 8
  | DTYPE_Metadata     => 0
  | DTYPE_X86_mmx      => 8 (* TODO: Unsupported *)
  | DTYPE_Opaque       => 0 (* TODO: Unsupported *)
  end.


Instance SizeofV : Sizeof :=
  {|
    bit_sizeof_dtyp := Bit_sizeof_dtyp ;
    sizeof_dtyp := Sizeof_dtyp ;
    dtyp_alignment := Dtyp_alignment
  |}.

Instance SizeofTheoryV : @SizeofTheory SizeofV.
Proof.
  constructor; eauto.
  lia.
Qed.

