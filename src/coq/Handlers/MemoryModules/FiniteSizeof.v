From Coq Require Import
     List
     Lia
     ZArith.

From Vellvm.Utils Require Import
     ListUtil.

From Vellvm.Syntax Require Import
     DynamicTypes.

From Vellvm.Semantics Require Import
     DynamicValues
     LLVMEvents
     Memory.MemBytes
     Memory.Sizeof
     StoreId.

Module FinSizeof : Sizeof.
  (* TODO: make parameter? *)
  Definition ptr_size : nat := 8.

  (* Default alignment matching LLVMs defaults *)
  Definition dtyp_alignment (dt : dtyp) : alignment
    := match dt with
       | DTYPE_I sz =>
           if Pos.leb sz 8
           then Build_alignment 1 1
           else if Pos.leb sz 16
                then Build_alignment 2 2
                else if Pos.leb sz 32
                     then Build_alignment 4 4
                     else Build_alignment 4 8
       | DTYPE_IPTR => Build_alignment 8 8
       | DTYPE_Pointer => Build_alignment 8 8
       | DTYPE_Void => Build_alignment 1 1
       | DTYPE_Half => Build_alignment 2 2
       | DTYPE_Float => Build_alignment 4 4
       | DTYPE_Double => Build_alignment 8 8
       | DTYPE_X86_fp80 => Build_alignment 16 16  (* Not sure if this is right *)
       | DTYPE_Fp128 => Build_alignment 16 16
       | DTYPE_Ppc_fp128 => Build_alignment 16 16
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
    match maximumByOpt (fun dt1 dt2 => preferred_alignment (dtyp_alignment dt1) <? preferred_alignment (dtyp_alignment dt1))%N dts with
    | Some dt =>
        preferred_alignment (dtyp_alignment dt)
    | None => 1
    end.

  Definition round_up_to_eight (n : N) : N :=
    if N.eqb 0 n
    then 0
    else (((n - 1) / 8) + 1) * 8.

  Fixpoint bit_sizeof_dtyp (ty : dtyp) : N :=
    match ty with
    | DTYPE_I sz => Npos sz
    | DTYPE_IPTR => 64 (* TODO: probably kind of a lie... *)
    | DTYPE_Pointer => 64
    | DTYPE_Void => 0
    | DTYPE_Half => 16
    | DTYPE_Float => 32
    | DTYPE_Double => 64
    | DTYPE_X86_fp80 => 80
    | DTYPE_Fp128 => 128
    | DTYPE_Ppc_fp128 => 128
    | DTYPE_Metadata => 0
    | DTYPE_X86_mmx => 64
    | DTYPE_Array sz t => pad_to_align_bitwise (dtyp_alignment ty) (sz * (round_up_to_eight (bit_sizeof_dtyp t)))
    | DTYPE_Struct fields =>
        let sz := fold_left (fun acc x => pad_to_align_bitwise (dtyp_alignment x) acc + round_up_to_eight (bit_sizeof_dtyp x)%N) fields 0%N in
        (* Add padding to the end of a struct if necessary *)
        pad_to_align_bitwise (dtyp_alignment ty) sz
    | DTYPE_Packed_struct fields =>
        pad_to_align_bitwise (dtyp_alignment ty) (fold_left (fun acc x => (acc + round_up_to_eight (bit_sizeof_dtyp x))%N) fields 0%N)
    | DTYPE_Opaque => 0
    | DTYPE_Vector sz t => pad_to_align_bitwise (dtyp_alignment ty) (sz * bit_sizeof_dtyp t)
    end.

  Fixpoint sizeof_dtyp (ty:dtyp) : N :=
    match ty with
    | DTYPE_I sz         => N.max 1 (N.div (Npos sz) 8)
    | DTYPE_IPTR         => N.of_nat ptr_size
    | DTYPE_Pointer      => N.of_nat ptr_size
    | DTYPE_Packed_struct l =>
        fold_left (fun acc x => (acc + sizeof_dtyp x)%N) l 0%N
    | DTYPE_Struct l =>
        let sz := fold_left (fun acc x => pad_to_align (dtyp_alignment x) acc + (sizeof_dtyp x)%N) l 0%N in
        let max_align := max_preferred_dtyp_alignment l in
        pad_to max_align sz
    | DTYPE_Vector sz ty'  (* TODO: Vector sizeof currently invalid for sub-bytesize / non-byte aligned elements. Changing this involves changing serialization. *)
    | DTYPE_Array sz ty' =>
        sz * (sizeof_dtyp ty')
    | DTYPE_Float        => 4
    | DTYPE_Double       => 8
    | DTYPE_Half         => 4
    | DTYPE_X86_fp80     => 10 (* TODO: Unsupported, currently modeled by Float32 *)
    | DTYPE_Fp128        => 16 (* TODO: Unsupported, currently modeled by Float32 *)
    | DTYPE_Ppc_fp128    => 16 (* TODO: Unsupported, currently modeled by Float32 *)
    | DTYPE_Metadata     => 0
    | DTYPE_X86_mmx      => 8 (* TODO: Unsupported *)
    | DTYPE_Opaque       => 0 (* TODO: Unsupported *)
    | _                  => 0 (* TODO: add support for more types as necessary *)
    end.

  Lemma sizeof_dtyp_void :
    sizeof_dtyp DTYPE_Void = 0%N.
  Proof. reflexivity. Qed.

  Lemma sizeof_dtyp_pos :
    forall dt,
      (0 <= sizeof_dtyp dt)%N.
  Proof.
    intros dt.
    lia.
  Qed.

  Lemma sizeof_dtyp_Struct :
    forall dts,
      sizeof_dtyp (DTYPE_Struct dts) = pad_to (max_preferred_dtyp_alignment dts) (List.fold_left (fun acc dt => N.add (pad_to_align (dtyp_alignment dt) acc) (sizeof_dtyp dt)) dts 0%N).
  Proof.
    reflexivity.
  Qed.
    
  Lemma sizeof_dtyp_Packed_struct :
    forall dts,
      sizeof_dtyp (DTYPE_Packed_struct dts) = List.fold_left (fun acc dt => N.add acc (sizeof_dtyp dt)) dts 0%N.
  Proof.
    reflexivity.
  Qed.

  Lemma sizeof_dtyp_array :
    forall sz t,
      sizeof_dtyp (DTYPE_Array sz t) = (sz * sizeof_dtyp t)%N.
  Proof.
    reflexivity.
  Qed.

  Lemma sizeof_dtyp_vector :
    forall sz t,
      sizeof_dtyp (DTYPE_Vector sz t) = (sz * sizeof_dtyp t)%N.
  Proof.
    reflexivity.
  Qed.

  Lemma sizeof_dtyp_i8 :
    sizeof_dtyp (DTYPE_I 8) = 1%N.
  Proof.
    reflexivity.
  Qed.
End FinSizeof.

Inductive UByte (uvalue : Type) :=
| mkUByte (uv : uvalue) (dt : dtyp) (idx : N) (sid : store_id) : UByte uvalue.

Module FinByte (ADDR : MemoryAddress.ADDRESS) (IP : MemoryAddress.INTPTR) (SIZEOF : Sizeof) (LLVMEvents:LLVM_INTERACTIONS(ADDR)(IP)(SIZEOF)) : ByteImpl(ADDR)(IP)(SIZEOF)(LLVMEvents)
with  Definition SByte := UByte LLVMEvents.DV.uvalue
with  Definition uvalue_sbyte := mkUByte LLVMEvents.DV.uvalue.
  Import LLVMEvents.
  Import DV.

  Definition SByte := UByte uvalue.

  Definition uvalue_sbyte := mkUByte uvalue.

  Definition sbyte_to_extractbyte (byte : SByte) : uvalue
    := match byte with
       | mkUByte uv dt idx sid => UVALUE_ExtractByte uv dt idx sid
       end.

  Lemma sbyte_to_extractbyte_inv :
    forall (b : SByte),
      {uv & {dt & {idx & {sid & sbyte_to_extractbyte b = UVALUE_ExtractByte uv dt idx sid}}}}.
  Proof.
    intros b. destruct b.
    cbn; eauto.
  Qed.

  Lemma sbyte_to_extractbyte_of_uvalue_sbyte :
    forall uv dt idx sid,
      sbyte_to_extractbyte (uvalue_sbyte uv dt idx sid) =  UVALUE_ExtractByte uv dt idx sid.
  Proof.
    auto.
  Qed.

End FinByte.
