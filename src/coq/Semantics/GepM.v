Require Import ZArith String List.

From ExtLib Require Import
     Structures.Monad
     Structures.Functor.

From Vellvm Require Import
     DynamicTypes
     LLVMEvents
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof
     Utils.Error
     Utils.Monads.

Import ListNotations.
Import MonadNotation.

Module Type GEPM(Addr:ADDRESS)(IP:INTPTR)(SIZEOF:Sizeof)(LLVMEvents:LLVM_INTERACTIONS(Addr)(IP)(SIZEOF)).
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

Module Make (ADDR : ADDRESS) (IP : INTPTR) (SIZE : Sizeof) (Events : LLVM_INTERACTIONS(ADDR)(IP)(SIZE)) (PTOI : PTOI ADDR) (PROV : PROVENANCE ADDR) (ITOP : ITOP ADDR PROV) <: GEPM(ADDR)(IP)(SIZE)(Events).
  Import ADDR.
  Import Events.
  Import DV.
  Import SIZE.
  Import PTOI.
  Import ITOP.
  Import PROV.

  (** ** Get Element Pointer
      Retrieve the address of a subelement of an indexable (i.e. aggregate) [dtyp] [t] (i.e. vector, array, struct, packed struct).
      The [off]set parameter contains the current entry address of the aggregate structure being analyzed, while the list
      of [dvalue] [vs] describes the indexes of interest used to access the subelement.
      The interpretation of these values slightly depends on the type considered.
      But essentially, for instance in a vector or an array, the head value should be an [i32] describing the index of interest.
      The offset is therefore incremented by this index times the size of the type of elements stored. Finally, a recursive call
      at this new offset allows for deeper unbundling of a nested structure.
   *)
  Fixpoint handle_gep_h (t:dtyp) (off:Z) (vs:list dvalue): err Z :=
    match vs with
    | v :: vs' =>
      match v with
      | DVALUE_I32 i =>
        let k := unsigned i in
        let n := BinIntDef.Z.to_nat k in
        match t with
        | DTYPE_Vector _ ta
        | DTYPE_Array _ ta =>
          handle_gep_h ta (off + k * (Z.of_N (sizeof_dtyp ta))) vs'
        | DTYPE_Struct ts
        | DTYPE_Packed_struct ts => (* Handle these differently in future *)
          let offset := fold_left (fun acc t => (acc + (Z.of_N (sizeof_dtyp t))))%Z
                                  (firstn n ts) 0%Z in
          match nth_error ts n with
          | None => failwith "overflow"
          | Some t' =>
            handle_gep_h t' (off + offset) vs'
          end
        | _ => failwith ("non-i32-indexable type")
        end
      | DVALUE_I8 i =>
        let k := unsigned i in
        let n := BinIntDef.Z.to_nat k in
        match t with
        | DTYPE_Vector _ ta
        | DTYPE_Array _ ta =>
          handle_gep_h ta (off + k * (Z.of_N (sizeof_dtyp ta))) vs'
        | _ => failwith ("non-i8-indexable type")
        end
      | DVALUE_I64 i =>
        let k := unsigned i in
        let n := BinIntDef.Z.to_nat k in
        match t with
        | DTYPE_Vector _ ta
        | DTYPE_Array _ ta =>
          handle_gep_h ta (off + k * (Z.of_N (sizeof_dtyp ta))) vs'
        | _ => failwith ("non-i64-indexable type")
        end
      | _ => failwith "non-I32 index"
      end
    | [] => ret off
    end.

  (* At the toplevel, GEP takes a [dvalue] as an argument that must contain a pointer, but no other pointer can be recursively followed.
     The pointer set the block into which we look, and the initial offset. The first index value add to the initial offset passed to [handle_gep_h] for the actual access to structured data.
   *)
  Definition handle_gep_addr (t:dtyp) (a:addr) (vs:list dvalue) : err addr :=
    let ptr := ptr_to_int a in
    let prov := address_provenance a in
    match vs with
    | DVALUE_I32 i :: vs' => (* TODO: Handle non i32 / i64 indices *)
      ptr' <- handle_gep_h t (ptr + Z.of_N (sizeof_dtyp t) * (unsigned i)) vs' ;;
      ret (int_to_ptr ptr' prov)
    | DVALUE_I64 i :: vs' =>
      ptr' <- handle_gep_h t (ptr + Z.of_N (sizeof_dtyp t) * (unsigned i)) vs' ;;
      ret (int_to_ptr ptr' prov)
    | _ => failwith "non-I32 index"
    end.

  Definition handle_gep (t:dtyp) (dv:dvalue) (vs:list dvalue) : err dvalue :=
    match dv with
    | DVALUE_Addr a => fmap DVALUE_Addr (handle_gep_addr t a vs)
    | _ => failwith "non-address"
    end.
End Make.
