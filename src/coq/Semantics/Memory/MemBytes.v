From Coq Require Import List ZArith.

From ExtLib Require Import Structures.Monads.

From Vellvm Require Import
     Syntax.DynamicTypes
     Semantics.DynamicValues
     Semantics.MemoryAddress
     Semantics.LLVMEvents
     Utils.Monads
     Utils.NMaps
     Utils.OptionUtil.

Import Basics.Basics.Monads.

Import ListNotations.
Import MonadNotation.

Module Type ByteImpl(Addr:ADDRESS)(LLVMEvents: LLVM_INTERACTIONS(Addr)).
  Import LLVMEvents.
  Import DV.

  Parameter SByte : Set.

  (* Get a specific byte of a uvalue of a given type.

     Arguments are:

     - The uvalue to get the byte of.
     - The type of the uvalue that we are getting the byte of.
     - The index of the byte (as a uvalue).
     - The store id for the byte we are creating.
   *)
  Parameter uvalue_sbyte : uvalue -> dtyp -> uvalue -> store_id -> SByte.

  (* Turn an SByte into a UVALUE_ExtractByte value *)
  Parameter sbyte_to_extractbyte : SByte -> uvalue.

  Parameter sbyte_to_extractbyte_inv  :
    forall (b : SByte),
    exists uv dt idx sid,
      sbyte_to_extractbyte b = UVALUE_ExtractByte uv dt idx sid.

  Parameter sbyte_to_extractbyte_of_uvalue_sbyte :
    forall uv dt idx sid,
      sbyte_to_extractbyte (uvalue_sbyte uv dt idx sid) =  UVALUE_ExtractByte uv dt idx sid.
End ByteImpl.

Module Byte(Addr:ADDRESS)(LLVMEvents:LLVM_INTERACTIONS(Addr))(Byte:ByteImpl(Addr)(LLVMEvents)).
  Export Byte.
  Import LLVMEvents.
  Import DV.

  Fixpoint all_bytes_from_uvalue_helper (idx' : Z) (sid' : store_id) (parent : uvalue) (bytes : list SByte) : option uvalue
    := match bytes with
       | [] => Some parent
       | sbyte::bytes =>
         match sbyte_to_extractbyte sbyte with
         | UVALUE_ExtractByte uv dt idx sid =>
           guard_opt (uvalue_int_eq_Z idx idx');;
           guard_opt (RelDec.rel_dec uv parent);;
           guard_opt (N.eqb sid sid');;
           all_bytes_from_uvalue_helper (Z.succ idx') sid' parent bytes
         | _ => None
         end
       end.

  Definition all_bytes_from_uvalue (bytes : list SByte) : option uvalue
    := match bytes with
       | nil => None
       | cons sbyte xs =>
         match sbyte_to_extractbyte sbyte with
         | UVALUE_ExtractByte uv dt idx sid =>
           all_bytes_from_uvalue_helper 0 sid uv bytes
         | _ => None
         end
       end.
End Byte.
