(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import Vellvm.Classes.
Require Import Vellvm.LLVMIO.
Require Import Vellvm.StepSemantics.
Require Import Vellvm.MemoryCerberus.
Require Import LLVMAddr.


Module Memory := MemoryCerberus.
Module IO := LLVMIO.Make(LLVMAddr.A).
Module M := Memory.Make(IO).
Module SS := StepSemantics(LLVMAddr.A)(IO).

Import IO.
Export IO.DV.

Module CMM <: M.MemoryInst.
   Include M.CerberusTypes.
   Include M.CerberusMonad.
   Axiom do_overlap : footprint -> footprint -> bool.
   Axiom allocate_static :
     thread_id -> symbol_prefix -> integer_value -> ctype0 -> option mem_value -> memM pointer_value.
   Axiom allocate_dynamic : thread_id -> symbol_prefix -> integer_value -> integer_value -> memM pointer_value.
   Axiom kill : pointer_value -> memM ().
   Axiom load : loc_ocaml_t -> ctype0 -> pointer_value -> memM (footprint * mem_value).
   Axiom store : loc_ocaml_t -> ctype0 -> pointer_value -> mem_value -> memM footprint.
   Axiom eq_ptrval : pointer_value -> pointer_value -> memM bool.
   Axiom ne_ptrval : pointer_value -> pointer_value -> memM bool.
   Axiom lt_ptrval : pointer_value -> pointer_value -> memM bool.
   Axiom gt_ptrval : pointer_value -> pointer_value -> memM bool.
   Axiom le_ptrval : pointer_value -> pointer_value -> memM bool.
   Axiom ge_ptrval : pointer_value -> pointer_value -> memM bool.
   Axiom diff_ptrval : ctype0 -> pointer_value -> pointer_value -> memM integer_value.
   Axiom validForDeref_ptrval : pointer_value -> bool.
   Axiom isWellAligned_ptrval : ctype0 -> pointer_value -> memM bool.
   Axiom ptrcast_ival : ctype0 -> ctype0 -> integer_value -> memM pointer_value.
   Axiom intcast_ptrval : ctype0 -> AilIntegerType -> pointer_value -> memM integer_value.
   Axiom array_shift_ptrval : pointer_value -> ctype0 -> integer_value -> pointer_value.
   Axiom member_shift_ptrval : pointer_value -> symbol_sym -> cabs_identifier -> pointer_value.
   Axiom memcmp : pointer_value -> pointer_value -> integer_value -> memM integer_value.
   Axiom concurRead_ival : AilIntegerType -> symbol_sym -> integer_value.
   Axiom integer_ival : big_num -> integer_value.
   Axiom max_ival : AilIntegerType -> integer_value.
   Axiom min_ival : AilIntegerType -> integer_value.
   Axiom op_ival : Mem_common_integer_operator -> integer_value -> integer_value -> integer_value.
   Axiom offsetof_ival : symbol_sym -> cabs_identifier -> integer_value.
   Axiom sizeof_ival : ctype0 -> integer_value.
   Axiom alignof_ival : ctype0 -> integer_value.
   Axiom bitwise_complement_ival : AilIntegerType -> integer_value -> integer_value.
   Axiom bitwise_and_ival : AilIntegerType -> integer_value -> integer_value -> integer_value.
   Axiom bitwise_or_ival : AilIntegerType -> integer_value -> integer_value -> integer_value.
   Axiom bitwise_xor_ival : AilIntegerType -> integer_value -> integer_value -> integer_value.
   Axiom case_integer_value : forall a : Type, integer_value -> (big_num -> a) -> (() -> a) -> a.
   Axiom is_specified_ival : integer_value -> bool.
   Axiom eq_ival : option mem_state -> integer_value -> integer_value -> option bool.
   Axiom lt_ival : option mem_state -> integer_value -> integer_value -> option bool.
   Axiom le_ival : option mem_state -> integer_value -> integer_value -> option bool.
   Axiom eval_integer_value : integer_value -> option big_num.
   Axiom zero_fval : floating_value.
   Axiom str_fval : String.string -> floating_value.
   Axiom case_fval : forall a : Type, floating_value -> (() -> a) -> (float -> a) -> a.
   Axiom op_fval : Mem_common_floating_operator -> floating_value -> floating_value -> floating_value.
   Axiom eq_fval : floating_value -> floating_value -> bool.
   Axiom lt_fval : floating_value -> floating_value -> bool.
   Axiom le_fval : floating_value -> floating_value -> bool.
   Axiom fvfromint : integer_value -> floating_value.
   Axiom ivfromfloat : AilIntegerType -> floating_value -> integer_value.
   Axiom unspecified_mval : ctype0 -> mem_value.
   Axiom integer_value_mval : AilIntegerType -> integer_value -> mem_value.
   Axiom floating_value_mval : AilFloatingType -> floating_value -> mem_value.
   Axiom pointer_mval : ctype0 -> pointer_value -> mem_value.
   Axiom array_mval : list mem_value -> mem_value.
   Axiom struct_mval : symbol_sym -> list (cabs_identifier * mem_value) -> mem_value.
   Axiom union_mval : symbol_sym -> cabs_identifier -> mem_value -> mem_value.
   Axiom case_mem_value :
     forall a : Type,
     mem_value ->
     (ctype0 -> a) ->
     (AilIntegerType -> symbol_sym -> a) ->
     (AilIntegerType -> integer_value -> a) ->
     (AilFloatingType -> floating_value -> a) ->
     (ctype0 -> pointer_value -> a) ->
     (list mem_value -> a) ->
     (symbol_sym -> list (cabs_identifier * mem_value) -> a) ->
     (symbol_sym -> cabs_identifier -> mem_value -> a) -> a.
   Axiom sequencePoint : memM ().
End CMM.

Module MemLLVM := M.MemoryLLVM(CMM).

(* TODO: Probably relies on runND in smt2.ml *)
Axiom runMemM : forall a, CMM.memM a -> a.

Definition run_with_memory prog : option (Trace DV.dvalue) :=
  let scfg := Vellvm.AstLib.modul_of_toplevel_entities prog in
  match CFG.mcfg_of_modul scfg with
  | None => None
  | Some mcfg =>
    mret (runMemM _
            (MemLLVM.memD MemLLVM.empty
                          ('s <- SS.init_state mcfg "main";
                           SS.step_sem mcfg (SS.Step s))))
  end.
