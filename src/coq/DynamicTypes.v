(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

From Coq Require Import
     ZArith
     List
     String
     Setoid
     Morphisms
     Omega
     Classes.RelationClasses.

From ExtLib Require Import
     Core.RelDec
     Programming.Eqv.

From Vellvm Require Import
     Util
     LLVMAst
     Error.

Require Import Ceres.Ceres.

Set Implicit Arguments.
Set Contextual Implicit.

Inductive dtyp : Set :=
| DTYPE_I (sz:Z)
| DTYPE_Pointer
| DTYPE_Void
| DTYPE_Half
| DTYPE_Float
| DTYPE_Double
| DTYPE_X86_fp80
| DTYPE_Fp128
| DTYPE_Ppc_fp128
| DTYPE_Metadata
| DTYPE_X86_mmx
| DTYPE_Array (sz:Z) (t:dtyp)
| DTYPE_Struct (fields:list dtyp)
| DTYPE_Packed_struct (fields:list dtyp)
| DTYPE_Opaque
| DTYPE_Vector (sz:Z) (t:dtyp)     (* t must be integer, floating point, or pointer type *)
.

Section hiding_notation.
  Local Open Scope sexp_scope.

  Fixpoint serialize_dtyp' (dt:dtyp): sexp atom :=
    match dt with
    | DTYPE_I sz     => Raw ("i" ++ to_string sz)
    | DTYPE_Pointer  => Raw "ptr"
    | DTYPE_Void     => Raw "dvoid"
    | DTYPE_Half     => Raw "half"
    | DTYPE_Float    => Raw "float"
    | DTYPE_Double   => Raw "double"
    | DTYPE_X86_fp80 => Raw "x86_fp80"
    | DTYPE_Fp128    => Raw "fp128"
    | DTYPE_Ppc_fp128 => Raw "ppc_fp128"
    | DTYPE_Metadata  => Raw "metadata"
    | DTYPE_X86_mmx   => Raw "x86_mmx"
    | DTYPE_Array sz t
      => [Raw ("[" ++ to_string sz) ; Raw "x" ; serialize_dtyp' t ; Raw "]"]
    | DTYPE_Struct fields
      => [Raw "{" ; to_sexp (List.map (fun x => [serialize_dtyp' x ; Raw ","]) fields) ; Raw "}"]
    | DTYPE_Packed_struct fields
      => [Raw "packed{" ; to_sexp (List.map (fun x => [serialize_dtyp' x ; Raw ","]) fields) ; Raw "}"]
    | DTYPE_Opaque => Raw "opaque"
    | DTYPE_Vector sz t
      => [Raw ("<" ++ to_string sz) ; Raw "x" ; serialize_dtyp' t ; Raw ">"]  (* TODO: right notation? *)
    end.

  Global Instance serialize_dtyp : Serialize dtyp := serialize_dtyp'.
End hiding_notation.

