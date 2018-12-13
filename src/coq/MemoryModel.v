(*
  Memory model that matches the ml interface...
 *)
Require Import Coq.Strings.String.
Require Import LLVMIO.
Require Import ZArith List String Omega.
Require Import Vellvm.LLVMAst Vellvm.Classes Vellvm.Util.
Require Import Vellvm.StepSemantics Vellvm.LLVMIO.
Require Import Vellvm.MemoryAddress.
Require Import Vellvm.LLVMIO.
Require Import ITree.
Require Import FSets.FMapAVL.
Require Import compcert.lib.Integers compcert.lib.Coqlib.
Require Coq.Structures.OrderedTypeEx.
Require Import ZMicromega.
Import ListNotations.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Structures.Monad.
Require Import DynamicValues.
Require Import LLVMAddr.


Definition ocaml_string : Type := unit.
Extract Constant ocaml_string => "string".

Module Type Memory.
  Parameter memM : Type -> Type.
  Parameter ret : forall a, a -> memM a.
  Parameter bind : forall a b, memM a -> (a -> memM b) -> memM b.

  Parameter name : string.

  Parameter pointer_value : Type.
  Parameter integer_value : Type.
  Parameter floating_value : Type.

  Parameter mem_value : Type.

  (* Definition mem_iv_constraint = Mem_Common.mem_constraint integer_value.*)

  Parameter footprint : Type.

  Parameter mem_state : Type.
  Parameter initial_mem_state : mem_state.

  (* TODO Original just uses Cthread.thread_id, not sure what we would use. *)
  Parameter thread_id : Type.

  (* TODO Original used Core_ctype.ctype0... Not sure what this is, though. *)
  Parameter ctype0 : Type.

  (* TODO Symbol.prefix *)
  Parameter symbol_prefix : Type.

  (* TODO Symbol.sym? *)
  Parameter symbol_sym : Type.
  
  (* Pointer value constructors *)
  Parameter null_ptrval : ctype0 -> pointer_value.
  Parameter fun_ptrval: symbol_sym -> pointer_value.

  (* TODO Location_ocaml.t, not sure what this is... *)
  Parameter loc_ocaml_t : Type.

  (* TODO AilTypes.integerType ? *)
  Parameter AilIntegerType : Type.

  (* TODO Nat_big_num.num ? *)
  Parameter big_num : Type.

  (* TODO AilTypes.floatingType *)
  Parameter AilFloatingType : Type.

  (* TODO float *)
  (* Parameter float : Type. *)

  (* TODO Cabs.cabs_identifier ? *)
  Parameter cabs_identifier : Type.

  (* TODO Mem_common.integer_operator *)
  Parameter Mem_common_integer_operator : Type.

  (* TODO Mem_common.floating_operator *)
  Parameter Mem_common_floating_operator : Type.

  Parameter do_overlap : footprint -> footprint -> bool.

  (* Memory actions *)
  Parameter allocate_static :
      thread_id  (* the allocating thread *)
      -> symbol_prefix      (* symbols coming from the Core/C program, for debugging purpose *)
      -> integer_value      (* alignment constraint *)
      -> ctype0  (* type of the allocation *)
      -> option mem_value   (* optional initialisation value (if provided the allocation is made read-only) *)
      -> memM pointer_value.

  Parameter allocate_dynamic :
    thread_id (* the allocating thread *)
    -> symbol_prefix     (* symbols coming from the Core/C program, for debugging purpose *)
    -> integer_value     (* alignment constraint *)
    -> integer_value     (* size *)
    -> memM pointer_value.

  Parameter kill : loc_ocaml_t -> bool -> pointer_value -> memM unit.
  
  Parameter load : loc_ocaml_t -> ctype0 -> pointer_value -> memM (footprint * mem_value).
  Parameter store : loc_ocaml_t -> ctype0 -> bool -> pointer_value -> mem_value -> memM footprint.
  
  (* Operations on pointer values *)
  Parameter eq_ptrval: pointer_value -> pointer_value -> memM bool.
  Parameter ne_ptrval: pointer_value -> pointer_value -> memM bool.
  Parameter lt_ptrval: pointer_value -> pointer_value -> memM bool.
  Parameter gt_ptrval: pointer_value -> pointer_value -> memM bool.
  Parameter le_ptrval: pointer_value -> pointer_value -> memM bool.
  Parameter ge_ptrval: pointer_value -> pointer_value -> memM bool.
  Parameter diff_ptrval: ctype0 -> pointer_value -> pointer_value -> memM integer_value.
  
  Parameter validForDeref_ptrval : ctype0 -> pointer_value -> memM bool.
  Parameter isWellAligned_ptrval: ctype0 -> pointer_value -> memM bool.
  
  (* Casting operations *)
  (* the first ctype is the original integer type, the second is the target referenced type *)
  Parameter ptrcast_ival: ctype0 -> ctype0 -> integer_value -> memM pointer_value.
  (* the first ctype is the original referenced type, the integerType is the target integer type *)
  Parameter intcast_ptrval: ctype0 -> AilIntegerType -> pointer_value -> memM integer_value.
  
  (* Pointer shifting constructors *)
  Parameter array_shift_ptrval:  pointer_value -> ctype0 -> integer_value -> pointer_value.
  Parameter member_shift_ptrval: pointer_value -> symbol_sym -> cabs_identifier -> pointer_value.
  
  Parameter memcmp: pointer_value -> pointer_value -> integer_value -> memM integer_value.
  
  (* Integer value constructors *)
  Parameter concurRead_ival: AilIntegerType -> symbol_sym -> integer_value.
  Parameter integer_ival: big_num -> integer_value.
  Parameter max_ival: AilIntegerType -> integer_value.
  Parameter min_ival: AilIntegerType -> integer_value.
  Parameter op_ival: Mem_common_integer_operator -> integer_value -> integer_value -> integer_value.
  Parameter offsetof_ival: symbol_sym -> cabs_identifier -> integer_value.
  
  Parameter sizeof_ival: ctype0 -> integer_value.
  Parameter alignof_ival: ctype0 -> integer_value.
  
  Parameter bitwise_complement_ival: AilIntegerType -> integer_value -> integer_value.
  Parameter bitwise_and_ival: AilIntegerType -> integer_value -> integer_value -> integer_value.
  Parameter bitwise_or_ival: AilIntegerType -> integer_value -> integer_value -> integer_value.
  Parameter bitwise_xor_ival: AilIntegerType -> integer_value -> integer_value -> integer_value.
  
  Parameter case_integer_value: (* TODO: expose more ctors *)
    forall a,
    integer_value ->
    (big_num -> a) ->
    (unit -> a) ->
    a.
  
  Parameter is_specified_ival: integer_value -> bool.
  
  (* Predicats on integer values *)
  Parameter eq_ival: option mem_state -> integer_value -> integer_value -> option bool.
  Parameter lt_ival: option mem_state -> integer_value -> integer_value -> option bool.
  Parameter le_ival: option mem_state -> integer_value -> integer_value -> option bool.
  
  Parameter eval_integer_value: integer_value -> option big_num.
  
  (* Floating value constructors *)
  Parameter zero_fval: floating_value.
  Parameter str_fval: ocaml_string -> floating_value.
  
  (* Floating value destructors *)
  (* Parameter case_fval: forall a, floating_value -> (unit -> a) -> (float -> a) -> a. *)
  
  (* Predicates on floating values *)
  Parameter op_fval: Mem_common_floating_operator -> floating_value -> floating_value -> floating_value.
  Parameter eq_fval: floating_value -> floating_value -> bool.
  Parameter lt_fval: floating_value -> floating_value -> bool.
  Parameter le_fval: floating_value -> floating_value -> bool.
  
  (* Integer <-> Floating casting constructors *)
  Parameter fvfromint: integer_value -> floating_value.
  Parameter ivfromfloat: AilIntegerType -> floating_value -> integer_value.

  (* Memory value constructors *)
  (*symbolic_mval: Symbolic.symbolic mem_value pointer_value -> mem_value *)
  Parameter unspecified_mval: ctype0 -> mem_value.
  Parameter integer_value_mval: AilIntegerType -> integer_value -> mem_value.
  Parameter floating_value_mval: AilFloatingType -> floating_value -> mem_value.
  Parameter pointer_mval: ctype0 -> pointer_value -> mem_value.
  Parameter array_mval: list mem_value -> mem_value.
  (* Parameter struct_mval: symbol_sym -> list (cabs_identifier * ctype0 * mem_value) -> mem_value. *)
  Parameter union_mval: symbol_sym -> cabs_identifier -> mem_value -> mem_value.
  
  (* Memory value destructor *)
  (*
  Parameter case_mem_value:
    forall a,
      mem_value ->
      (ctype0 -> a) -> (* unspecified case *)
      (AilIntegerType -> symbol_sym -> a) -> (* concurrency read case *)
      (AilIntegerType -> integer_value -> a) ->
      (AilFloatingType -> floating_value -> a) ->
      (ctype0 -> pointer_value -> a) ->
      (list mem_value -> a) ->
      (symbol_sym -> list (cabs_identifier * mem_value) -> a) ->
      (symbol_sym -> cabs_identifier -> mem_value -> a) ->
      a.
  *)
  
  (* For race detection *)
  Parameter sequencePoint: memM unit.

  (* TODO, not sure if any of this is important *)

  (*
  (* pretty printing *)
  Parameter pp_pointer_value: pointer_value -> PPrint.document
  Parameter pp_integer_value: integer_value -> PPrint.document
  Parameter pp_integer_value_for_core: integer_value -> PPrint.document
  Parameter pp_mem_value: mem_value -> PPrint.document
  Parameter pp_pretty_pointer_value: pointer_value -> PPrint.document
  Parameter pp_pretty_integer_value: Boot_printf.formatting -> integer_value -> PPrint.document
  Parameter pp_pretty_mem_value: Boot_printf.formatting -> mem_value -> PPrint.document
  
(*
  Parameter string_of_pointer_value: pointer_value -> string
  Parameter string_of_integer_value: integer_value -> string
  Parameter string_of_mem_value: mem_value -> string
*)

  (* JSON serialisation *)
  Parameter serialise_mem_state: mem_state -> Json.json
  
  
  
  
  
(*  
  Parameter runND:
    Driver.driver_result Driver.driverM ->
    Driver.driver_state ->
    ( (Driver.driver_result, Driver.driver_error) Nondeterminism.nd_status
    * string list
    * Driver.driver_state ) list
*)
*)
End Memory.

(*
Module Type MemoryTypeConversion (Import LLVMIO: LLVMInters) (Import M: Memory).
  Parameter pointer_value_to_dvalue : pointer_value -> dvalue.
  Parameter dvalue_to_pointer_value : dvalue -> pointer_value.  (* Type checking to catch incompatible dvalues? *)

  Parameter integer_value_to_dvalue : integer_value -> dvalue.
  Parameter dvalue_to_integer_value : dvalue -> integer_value.

  Parameter floating_value_to_dvalue : floating_value -> dvalue.
  Parameter dvalue_to_floating_value : dvalue -> floating_value.

  Parameter mem_value_to_dvalue : mem_value -> dvalue.
  Parameter dvalue_to_mem_value : dvalue -> mem_value.

  Parameter dtyp_to_ctype : dtyp -> ctype0.
  Parameter ctype_to_dtyp : ctype0 -> dtyp.
End MemoryTypeConversion.
*)