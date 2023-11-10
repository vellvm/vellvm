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

Module FinSizeof <: SIZEOF.
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

  (* Should take padding into account *)
  Lemma sizeof_dtyp_Struct :
    forall dts,
      sizeof_dtyp (DTYPE_Struct dts) = List.fold_left (fun acc dt => N.add acc (sizeof_dtyp dt)) dts 0%N.
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
