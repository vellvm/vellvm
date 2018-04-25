(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import ZArith List String Omega.
Require Import compcert.lib.Integers compcert.lib.Floats.
Require Import Vellvm.MemoryAddress.

Set Implicit Arguments.
Set Contextual Implicit.

Open Scope Z_scope.

(* Set up representations for for i1, i32, and i64 *) 
Module Wordsize1.
  Definition wordsize := 1%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize1.

Module Int1 := Make(Wordsize1).
Module Int32 := Integers.Int.
Module Int64 := Integers.Int64.

Definition int1 := Int1.int.
Definition int32 := Int32.int.
Definition int64 := Int64.int.

Definition inttyp (x:Z) : Type :=
  match x with
  | 1 => int1
  | 32 => int32
  | 64 => int64
  | _ => False
  end.

Definition ll_float  := Floats.float32.
Definition ll_double := Floats.float.

Module DVALUE(A:Vellvm.MemoryAddress.ADDRESS).
       
(* The set of dynamic values manipulated by an LLVM program. *)
Inductive dvalue : Set :=
| DVALUE_Addr (a:A.addr)
| DVALUE_I1 (x:int1)
| DVALUE_I32 (x:int32)
| DVALUE_I64 (x:int64)
| DVALUE_Double (x:ll_double)
| DVALUE_Float (x:ll_float)
| DVALUE_Undef     (* TODO: include type information? Ideally, also include some kind of constraint: (p:dvalue -> bool) *)
| DVALUE_Poison
| DVALUE_None
| DVALUE_Struct        (fields: list dvalue)
| DVALUE_Packed_struct (fields: list dvalue)
| DVALUE_Array         (elts: list dvalue)
| DVALUE_Vector        (elts: list dvalue)
.

(* TODO: include Undefined values in this way? i.e. Undef is really a predicate on values 
   Note: this isn't correct because it won't allow for undef fields of a struct or elts of an array
Inductive dvalue' : Set :=
| DVALUE_Undef (p:dvalue -> bool) (* TODO: used to include type information. is it necessary? (t:dtyp)  *)
| DVALUE_Val (d:dvalue).
*)

Definition is_DVALUE_I1 (d:dvalue) : bool :=
  match d with
  | DVALUE_I1 _ => true
  | _ => false
  end.

Definition is_DVALUE_I32 (d:dvalue) : bool :=
  match d with
  | DVALUE_I32 _ => true
  | _ => false
  end.

Definition is_DVALUE_I64 (d:dvalue) : bool :=
  match d with
  | DVALUE_I64 _ => true
  | _ => false
  end.


Definition undef_i1  := DVALUE_Undef.
Definition undef_i32 := DVALUE_Undef.
Definition undef_i64 := DVALUE_Undef.

End DVALUE.
