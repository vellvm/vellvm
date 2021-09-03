Require Import ZArith String.

From ExtLib Require Import
     Structures.Functor.

From Vellvm Require Import
     DynamicTypes
     LLVMEvents
     Semantics.Memory.Sizeof
     Utils.Error.

Module Type GEPM(Addr:MemoryAddress.ADDRESS)(SIZEOF:Sizeof)(LLVMEvents:LLVM_INTERACTIONS(Addr)(SIZEOF)).
  Import LLVMEvents.
  Import DV.

  (* TODO: should this be here? *)
  Parameter handle_gep_h : dtyp -> Z -> list dvalue -> err Z.

  Parameter handle_gep_addr : dtyp -> Addr.addr -> list dvalue -> err Addr.addr.

  Definition handle_gep (t:dtyp) (dv:dvalue) (vs:list dvalue) : err dvalue :=
    match dv with
    | DVALUE_Addr a => fmap DVALUE_Addr (handle_gep_addr t a vs)
    | _ => failwith "non-address"
    end.
End GEPM.
