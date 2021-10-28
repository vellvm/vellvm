(** * Handlers for VIR's events *)

(**
   Reexport the handlers implementing the effects of the VIR's events for:
   * manipulating the global environment;
   * manipulating the local environment;
   * manipulating a stack of local environment;
   * manipulating the memory;
   * calling intrinsics;
   * collecting the set semantics of symbolic expressions denoting [uvalue]s;
   * interpreting undefined behaviors according to the "anything can happen"
   (without time traveling) policy.

   In the case of the non-deterministic handlers (for [pickE] and [UBE]), two
   handlers are provided: a propositional model, and an executable interpreter.

   For each handler, up-to-tau equations are provided to commute them with [Ret],
   [bind], [vis] and [trigger], as well as the proof that they respect [eutt].
 *)

From Vellvm.Handlers Require Export
     Global
     Local
     Stack
     Intrinsics
     FiniteMemory
     FiniteMemoryTheory
     Pick
     UndefinedBehaviour
     OOM
     Serialization.

From Vellvm.Semantics Require Import Memory.Sizeof Memory.MemBytes GepM.

(* Handlers get instantiated over the domain of addresses provided by the memory model *)
Module LLVMEvents := LLVMEvents.Make(FiniteMemory.Addr)(FiniteMemory.BigIP)(FiniteMemory.FinSizeof).
Module Global := Global.Make FiniteMemory.Addr FiniteMemory.BigIP FiniteMemory.FinSizeof LLVMEvents.
Module Local  := Local.Make  FiniteMemory.Addr FiniteMemory.BigIP FiniteMemory.FinSizeof LLVMEvents.
Module Stack  := Stack.Make  FiniteMemory.Addr FiniteMemory.BigIP FiniteMemory.FinSizeof LLVMEvents.

Module LLVMEvents64 := LLVMEvents.Make(FiniteMemory.Addr)(FiniteMemory.IP64Bit)(FiniteMemory.FinSizeof).
Module Global64 := Global.Make FiniteMemory.Addr FiniteMemory.IP64Bit FiniteMemory.FinSizeof LLVMEvents64.
Module Local64  := Local.Make  FiniteMemory.Addr FiniteMemory.IP64Bit FiniteMemory.FinSizeof LLVMEvents64.
Module Stack64  := Stack.Make  FiniteMemory.Addr FiniteMemory.IP64Bit FiniteMemory.FinSizeof LLVMEvents64.

Require Import List ZArith String.
Import ListNotations.

From Vellvm Require Import
     Utils.Error
     Semantics.MemoryAddress
     Semantics.LLVMEvents
     DynamicTypes.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

Import MonadNotation.

Module GEP_Make (IP:MemoryAddress.INTPTR) (LLVMEvents : LLVM_INTERACTIONS(FiniteMemory.Addr)(IP)(FiniteMemory.FinSizeof)) <: GEPM(FiniteMemory.Addr)(IP)(FiniteMemory.FinSizeof)(LLVMEvents).
  Import Addr.
  Import LLVMEvents.
  Import DV.
  Import FiniteMemory.FinSizeof.

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
    let '(ptr, prov) := a in
    match vs with
    | DVALUE_I32 i :: vs' => (* TODO: Handle non i32 / i64 indices *)
      ptr' <- handle_gep_h t (ptr + Z.of_N (sizeof_dtyp t) * (unsigned i)) vs' ;;
      ret (ptr', prov)
    | DVALUE_I64 i :: vs' =>
      ptr' <- handle_gep_h t (ptr + Z.of_N (sizeof_dtyp t) * (unsigned i)) vs' ;;
      ret (ptr', prov)
    | _ => failwith "non-I32 index"
    end.

  Definition handle_gep (t:dtyp) (dv:dvalue) (vs:list dvalue) : err dvalue :=
    match dv with
    | DVALUE_Addr a => fmap DVALUE_Addr (handle_gep_addr t a vs)
    | _ => failwith "non-address"
    end.
End GEP_Make.

Module GEP := GEP_Make FiniteMemory.BigIP LLVMEvents.
Module GEP64 := GEP_Make FiniteMemory.IP64Bit LLVMEvents64.

Module Intrinsics := Intrinsics.Make FiniteMemory.Addr FiniteMemory.BigIP FiniteMemory.FinSizeof LLVMEvents.
Module Intrinsics64 := Intrinsics.Make FiniteMemory.Addr FiniteMemory.IP64Bit FiniteMemory.FinSizeof LLVMEvents64.

Module Byte := FinByte FiniteMemory.BigIP LLVMEvents.
Module Byte64 := FinByte FiniteMemory.IP64Bit LLVMEvents64.

Module SER := Serialization.Make(FiniteMemory.Addr)(FiniteMemory.BigIP)(FiniteMemory.FinSizeof)(LLVMEvents)(FiniteMemory.FinPTOI)(FiniteMemory.FinPROV)(FiniteMemory.FinITOP)(GEP)(Byte).
Module SER64 := Serialization.Make(FiniteMemory.Addr)(FiniteMemory.IP64Bit)(FiniteMemory.FinSizeof)(LLVMEvents64)(FiniteMemory.FinPTOI)(FiniteMemory.FinPROV)(FiniteMemory.FinITOP)(GEP64)(Byte64).

Module MEM := FiniteMemory.Make(FiniteMemory.Addr)(FiniteMemory.BigIP)(FiniteMemory.FinSizeof)(LLVMEvents)(FiniteMemory.FinPTOI)(FiniteMemory.FinPROV)(FiniteMemory.FinITOP)(GEP)(Byte).
Module MEM64 := FiniteMemory.Make(FiniteMemory.Addr)(FiniteMemory.IP64Bit)(FiniteMemory.FinSizeof)(LLVMEvents64)(FiniteMemory.FinPTOI)(FiniteMemory.FinPROV)(FiniteMemory.FinITOP)(GEP64)(Byte64).

Module MEMORY_THEORY := FiniteMemoryTheory.Make(FiniteMemory.Addr)(FiniteMemory.BigIP)(FiniteMemory.FinSizeof)(LLVMEvents)(FiniteMemory.FinPTOI)(FiniteMemory.FinPROV)(FiniteMemory.FinITOP)(GEP)(Byte).
Module MEMORY_THEORY64 := FiniteMemoryTheory.Make(FiniteMemory.Addr)(FiniteMemory.IP64Bit)(FiniteMemory.FinSizeof)(LLVMEvents64)(FiniteMemory.FinPTOI)(FiniteMemory.FinPROV)(FiniteMemory.FinITOP)(GEP64)(Byte64).

Module Pick := Pick.Make FiniteMemory.Addr FiniteMemory.BigIP FinSizeof LLVMEvents FinPTOI FinPROV FinITOP GEP Byte.
Module Pick64 := Pick.Make FiniteMemory.Addr FiniteMemory.IP64Bit FinSizeof LLVMEvents64 FinPTOI FinPROV FinITOP GEP64 Byte64.

Export LLVMEvents LLVMEvents.DV Global Local Stack Pick Intrinsics
       MEM MEMORY_THEORY UndefinedBehaviour.
