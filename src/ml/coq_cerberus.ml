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
