open AilTypes
open Core_ctype
open LLVMAddr
open LLVMIO

open Nat_big_num
open Concrete

module IO = LLVMIO.Make(A)

(* TODO structures, opaque, metadata, mmx, etc *)
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


let rec pointer_value_to_dvalue (pv : pointer_value) : IO.DV.dvalue =
  (match pv with
   | PV (prov, PVnull t) -> IO.DV.DVALUE_Addr A.null
   | PV (prov, PVconcrete n) -> IO.DV.DVALUE_Addr (Camlcoq.Z.of_sint 0, Camlcoq.Z.of_sint (Nat_big_num.to_int n))
   | PV (prov, PVfunction s) -> failwith "Function pointers not implemented.")


(* TODO, use block? *)
let dvalue_to_pointer_value (dv : IO.DV.dvalue) : pointer_value =
  (match dv with
   | IO.DV.DVALUE_Addr a ->
      (match a with | (b, o) -> if Camlcoq.Z.to_int b == 0 && Camlcoq.Z.to_int o == 0
                                then PV (Prov_none, PVnull Void0)
                                else PV (Prov_none, PVconcrete (Nat_big_num.of_int (Camlcoq.Z.to_int o))))
   | _ -> failwith "Undefined conversion from dvalue to pointer value.")

let integer_value_to_dvalue (iv : integer_value) : IO.DV.dvalue =
  (match iv with | IV (_, n) -> DVALUE_I64 (DynamicValues.Int64.repr (Camlcoq.Z.of_sint (Nat_big_num.to_int n))))


let dvalue_to_integer_value (dv : IO.DV.dvalue) : integer_value =
  (match dv with
   | IO.DV.DVALUE_I1 i -> IV (Prov_none, Nat_big_num.of_int (Camlcoq.Z.to_int (DynamicValues.Int1.signed i)))
   | IO.DV.DVALUE_I8 i -> IV (Prov_none, Nat_big_num.of_int (Camlcoq.Z.to_int (DynamicValues.Int8.signed i)))
   | IO.DV.DVALUE_I32 i -> IV (Prov_none, Nat_big_num.of_int (Camlcoq.Z.to_int (DynamicValues.Int32.signed i)))
   | IO.DV.DVALUE_I64 i -> IV (Prov_none, Nat_big_num.of_int (Camlcoq.Z.to_int (DynamicValues.Int64.signed i)))
   | _ -> failwith "Cannot convert non-integer dvalue to cerberus integer value.")

let floating_value_to_dvalue (fv : floating_value) : IO.DV.dvalue =
  IO.DV.DVALUE_Double (Camlcoq.coqfloat_of_camlfloat fv)

let dvalue_to_floating_value (dv : IO.DV.dvalue) : floating_value =
  (match dv with
   | IO.DV.DVALUE_Double d -> Camlcoq.camlfloat_of_coqfloat d
   | IO.DV.DVALUE_Float f -> Camlcoq.camlfloat_of_coqfloat32 f)


(*
  type mem_value =
    | MVunspecified of Core_ctype.ctype0
    | MVinteger of AilTypes.integerType * integer_value
    | MVfloating of AilTypes.floatingType * floating_value
    | MVpointer of Core_ctype.ctype0 * pointer_value
    | MVarray of mem_value list
    | MVstruct of Symbol.sym (*struct/union tag*) * (Cabs.cabs_identifier (*member*) * Core_ctype.ctype0 * mem_value) list
    | MVunion of Symbol.sym (*struct/union tag*) * Cabs.cabs_identifier (*member*) * mem_value
 *)

let rec mem_value_to_dvalue (mv : mem_value) : IO.DV.dvalue =
  (match mv with
   | MVunspecified ct -> DVALUE_Undef
   | MVinteger (at, iv) -> integer_value_to_dvalue iv
   | MVfloating (at, fv) -> floating_value_to_dvalue fv
   | MVpointer (ct, pv) -> pointer_value_to_dvalue pv
   | MVarray ml -> failwith "Arrays unimplemented." (* (List.map mem_value_to_dvalue ml) *)
   | MVstruct (_, _) -> failwith "Structs unimplemented."
   | MVunion (_, _, _) -> failwith "Unions unimplemented.")

let dvalue_to_mem_value (dv : IO.DV.dvalue) : mem_value =
  (match dv with
   | IO.DV.DVALUE_Addr _ -> MVpointer (Void0, dvalue_to_pointer_value dv)
   | IO.DV.DVALUE_I1 _ -> MVinteger (Signed (IntN_t 1), dvalue_to_integer_value dv)
   | IO.DV.DVALUE_I8 _ -> MVinteger (Signed (IntN_t 8), dvalue_to_integer_value dv)
   | IO.DV.DVALUE_I32 _ -> MVinteger (Signed (IntN_t 32), dvalue_to_integer_value dv)
   | IO.DV.DVALUE_I64 _ -> MVinteger (Signed (IntN_t 64), dvalue_to_integer_value dv)
   | _ -> failwith "dvalue_to_mem_value unimplemented")

let z_to_iv z : integer_value = IV (Prov_none, Nat_big_num.of_int (Camlcoq.Z.to_int z))

let dtyp_to_ail_integer_type (dt : dtyp) : AilTypes.integerType =
  (match dt with
   | LLVMIO.DTYPE_I sz -> Signed (IntN_t (Camlcoq.Z.to_int sz))
   | _ -> failwith "Invalid conversion from dtyp to integer type.")
