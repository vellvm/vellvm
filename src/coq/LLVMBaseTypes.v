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

Set Implicit Arguments.
Set Contextual Implicit.

Open Scope Z_scope.

(* Set up for i1, i32, and i64 *) 
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
