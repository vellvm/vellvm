(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

;; open TopLevel
;; open Datatypes

open AilTypes
open Core_ctype
open LLVMIO
open Nat_big_num
open Concrete

let rec dtyp_to_ctype (dt : dtyp) : ctype0 =
  (match dt with
   | LLVMIO.DTYPE_I sz -> Basic0 (Integer (Signed (IntN_t (Camlcoq.Z.to_int sz))))
   | LLVMIO.DTYPE_Pointer -> Pointer0 ({ const = false; restrict = false; volatile = false }, Void0)
   | LLVMIO.DTYPE_Void -> Void0
   | LLVMIO.DTYPE_Half -> Basic0 (Floating (RealFloating Float))
   | LLVMIO.DTYPE_Float -> Basic0 (Floating (RealFloating Float))
   | LLVMIO.DTYPE_Double -> Basic0 (Floating (RealFloating Double))
   | LLVMIO.DTYPE_X86_fp80 -> Basic0 (Floating (RealFloating Double))
   | LLVMIO.DTYPE_Fp128 -> Basic0 (Floating (RealFloating LongDouble))
   | LLVMIO.DTYPE_Ppc_fp128 -> Basic0 (Floating (RealFloating LongDouble))
   | LLVMIO.DTYPE_Metadata -> Void0
   | LLVMIO.DTYPE_X86_mmx -> Void0
   | LLVMIO.DTYPE_Array (sz, t) -> Array0 (dtyp_to_ctype t, Some (Nat_big_num.of_int (Camlcoq.Z.to_int sz)))
   | LLVMIO.DTYPE_Struct ts -> Void0
   | LLVMIO.DTYPE_Packed_struct ts -> Void0
   | LLVMIO.DTYPE_Opaque -> Void0
   | LLVMIO.DTYPE_Vector (sz, t) -> Array0 (dtyp_to_ctype t, Some (Nat_big_num.of_int (Camlcoq.Z.to_int sz))))

module DV = TopLevel.IO.DV

let print_int_dvalue dv : unit =
  match dv with
  | DV.DVALUE_I1 (x) -> Printf.printf "Program terminated with: DVALUE_I1(%d)\n" (Camlcoq.Z.to_int (DynamicValues.Int1.unsigned x))
  | DV.DVALUE_I8 (x) -> Printf.printf "Program terminated with: DVALUE_I8(%d)\n" (Camlcoq.Z.to_int (DynamicValues.Int8.unsigned x))
  | DV.DVALUE_I32 (x) -> Printf.printf "Program terminated with: DVALUE_I32(%d)\n" (Camlcoq.Z.to_int (DynamicValues.Int32.unsigned x))
  | DV.DVALUE_I64 (x) -> Printf.printf "Program terminated with: DVALUE_I64(%d) [possible precision loss: converted to OCaml int]\n"
                       (Camlcoq.Z.to_int (DynamicValues.Int64.unsigned x))
  | _ -> Printf.printf "Program terminated with non-Integer value.\n"

let rec step m =
  match Lazy.force m with
  | ITree.Tau x -> step x
  | ITree.Ret (Coq_inr v) -> v
  | ITree.Ret (Coq_inl s) -> failwith (Printf.sprintf "ERROR: %s" (Camlcoq.camlstring_of_coqstring s))
  | ITree.Vis (IO.Call(t, f, args), k) ->
    (Printf.printf "UNINTERPRETED EXTERNAL CALL: %s - returning 0l to the caller\n" (Camlcoq.camlstring_of_coqstring f));
    step (k (Obj.magic (DV.DVALUE_I64 DynamicValues.Int64.zero)))
    
  | ITree.Vis (IO.GEP(_, _, _), _) -> failwith "GEP failed"
  | ITree.Vis _ -> failwith "should have been handled by the memory model"  
      

let interpret (prog:(LLVMAst.block list) LLVMAst.toplevel_entity list) = 
  match TopLevel.run_with_memory prog with
  | None -> failwith "bad module"
  | Some t -> step t
  
