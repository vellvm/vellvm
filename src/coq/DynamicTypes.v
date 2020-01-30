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

  Fixpoint serialize_dtyp' (dt:dtyp): sexp :=
    match dt with
    | DTYPE_I sz     => Atom ("i" ++ to_string sz)%string
    | DTYPE_Pointer  => Atom "ptr"
    | DTYPE_Void     => Atom "dvoid"
    | DTYPE_Half     => Atom "half"
    | DTYPE_Float    => Atom "float"
    | DTYPE_Double   => Atom "double"
    | DTYPE_X86_fp80 => Atom "x86_fp80"
    | DTYPE_Fp128    => Atom "fp128"
    | DTYPE_Ppc_fp128 => Atom "ppc_fp128"
    | DTYPE_Metadata  => Atom "metadata"
    | DTYPE_X86_mmx   => Atom "x86_mmx"
    | DTYPE_Array sz t
      => [Atom ("[" ++ to_string sz) ; Atom "x" ; serialize_dtyp' t ; Atom "]"]%string
    | DTYPE_Struct fields
      => [Atom "{" ; to_sexp (List.map (fun x => [serialize_dtyp' x ; Atom ","]) fields) ; Atom "}"]
    | DTYPE_Packed_struct fields
      => [Atom "packed{" ; to_sexp (List.map (fun x => [serialize_dtyp' x ; Atom ","]) fields) ; Atom "}"]
    | DTYPE_Opaque => Atom "opaque"
    | DTYPE_Vector sz t
      => [Atom ("<" ++ to_string sz) ; Atom "x" ; serialize_dtyp' t ; Atom ">"]%string  (* TODO: right notation? *)
    end.

  Global Instance serialize_dtyp : Serialize dtyp := serialize_dtyp'.
End hiding_notation.

