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
     Programming.Eqv
     Programming.Show.

From Vellvm Require Import
     Util
     LLVMAst
     Error.

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
  Import ShowNotation.
  Local Open Scope show_scope.

  Fixpoint show_dtyp' (dt:dtyp) :=
    match dt with
    | DTYPE_I sz     => ("i" << show sz)
    | DTYPE_Pointer  => "ptr"
    | DTYPE_Void     => "dvoid"
    | DTYPE_Half     => "half"
    | DTYPE_Float    => "float"
    | DTYPE_Double   => "double"
    | DTYPE_X86_fp80 => "x86_fp80"
    | DTYPE_Fp128    => "fp128"
    | DTYPE_Ppc_fp128 => "ppc_fp128"
    | DTYPE_Metadata  => "metadata"
    | DTYPE_X86_mmx   => "x86_mmx"
    | DTYPE_Array sz t
      => ("[" << show sz << " x " << (show_dtyp' t) << "]")
    | DTYPE_Struct fields
      => ("{" << iter_show (List.map (fun x => (show_dtyp' x) << ",") fields) << "}")
    | DTYPE_Packed_struct fields
      => ("packed{" << iter_show (List.map (fun x => (show_dtyp' x) << ",") fields) << "}")
    | DTYPE_Opaque => "opaque"
    | DTYPE_Vector sz t
      => ("<" << show sz << " x " << (show_dtyp' t) << ">")  (* TODO: right notation? *)
    end%string.

  Global Instance show_dtyp : Show dtyp := show_dtyp'.
End hiding_notation.

