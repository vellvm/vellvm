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
     Memory.Sizeof.

Module FinSizeof : Sizeof.
  (* TODO: make parameter? *)
  Definition ptr_size : nat := 8.

  Definition round_up_to_eight (n : N) : N :=
    if N.eqb 0 n
    then 0
    else (((n - 1) / 8) + 1) * 8.

  Fixpoint bit_sizeof_dtyp (t : dtyp) : N :=
    match t with
    | DTYPE_I sz => N.max 1 sz
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
    | DTYPE_Array sz t => sz * (round_up_to_eight (bit_sizeof_dtyp t))
    | DTYPE_Struct fields
    | DTYPE_Packed_struct fields =>
        fold_right (fun x acc => (round_up_to_eight (bit_sizeof_dtyp x) + acc)%N) 0%N fields
    | DTYPE_Opaque => 0
    | DTYPE_Vector sz t => sz * bit_sizeof_dtyp t
    end.

  Fixpoint sizeof_dtyp (ty:dtyp) : N :=
    match ty with
    | DTYPE_I 1          => 1 (* TODO: i1 sizes... *)
    | DTYPE_I 8          => 1
    | DTYPE_I 32         => 4
    | DTYPE_I 64         => 8
    | DTYPE_I _          => 0 (* Unsupported integers *)
    | DTYPE_IPTR         => N.of_nat ptr_size
    | DTYPE_Pointer      => N.of_nat ptr_size
    | DTYPE_Packed_struct l
    | DTYPE_Struct l     => fold_left (fun acc x => (acc + sizeof_dtyp x)%N) l 0%N
    | DTYPE_Vector sz ty'
    | DTYPE_Array sz ty' => sz * sizeof_dtyp ty'
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

  Lemma sizeof_dtyp_packed_struct_0 :
    sizeof_dtyp (DTYPE_Packed_struct nil) = 0%N.
  Proof.
    reflexivity.
  Qed.

  Lemma sizeof_dtyp_packed_struct_cons :
    forall dt dts,
      sizeof_dtyp (DTYPE_Packed_struct (dt :: dts)) = (sizeof_dtyp dt + sizeof_dtyp (DTYPE_Packed_struct dts))%N.
  Proof.
    intros dt dts.
    cbn.
    rewrite fold_sum_acc.
    reflexivity.
  Qed.

  Lemma sizeof_dtyp_struct_0 :
    sizeof_dtyp (DTYPE_Struct nil) = 0%N.
  Proof.
    reflexivity.
  Qed.

  (* TODO: this should take padding into account *)
  Lemma sizeof_dtyp_struct_cons :
    forall dt dts,
      sizeof_dtyp (DTYPE_Struct (dt :: dts)) = (sizeof_dtyp dt + sizeof_dtyp (DTYPE_Struct dts))%N.
  Proof.
    intros dt dts.
    cbn.
    rewrite fold_sum_acc.
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
| mkUByte (uv : uvalue) (dt : dtyp) (idx : uvalue) (sid : store_id) : UByte uvalue.

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
    exists uv dt idx sid,
      sbyte_to_extractbyte b = UVALUE_ExtractByte uv dt idx sid.
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
