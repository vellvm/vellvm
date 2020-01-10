(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2018 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

From Coq Require Import
     ZArith List String.

From ExtLib Require Import
     Structures.Monads
     Programming.Eqv
     Data.String.

From Vellvm Require Import
     LLVMEvents
     LLVMAst
     Error
     Coqlib
     Numeric.Integers
     Numeric.Floats.

From ITree Require Import
     ITree.

Import MonadNotation.
Import EqvNotation.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

Definition fabs_32_decl: declaration typ :=
  {|
    dc_name        := Name "llvm.fabs.f32";
    dc_type        := TYPE_Function TYPE_Float [TYPE_Float] ;
    dc_param_attrs := ([], [[]]);
    dc_linkage     := None ;
    dc_visibility  := None ;
    dc_dll_storage := None ;
    dc_cconv       := None ;
    dc_attrs       := [] ;
    dc_section     := None ;
    dc_align       := None ;
    dc_gc          := None
  |}.


Definition fabs_64_decl: declaration typ :=
  {|
    dc_name        := Name "llvm.fabs.f64";
    dc_type        := TYPE_Function TYPE_Double [TYPE_Double] ;
    dc_param_attrs := ([], [[]]);
    dc_linkage     := None ;
    dc_visibility  := None ;
    dc_dll_storage := None ;
    dc_cconv       := None ;
    dc_attrs       := [] ;
    dc_section     := None ;
    dc_align       := None ;
    dc_gc          := None
  |}.

Definition memcpy_8_decl: declaration typ :=
  let pt := TYPE_Pointer (TYPE_I 8%Z) in
  let i32 := TYPE_I 32%Z in
  let i1 := TYPE_I 1%Z in
  {|
    dc_name        := Name "llvm.memcpy.p0i8.p0i8.i32";
    dc_type        := TYPE_Function TYPE_Void [pt; pt; i32; i32; i1] ;
    dc_param_attrs := ([], [[];[];[];[];[]]);
    dc_linkage     := None ;
    dc_visibility  := None ;
    dc_dll_storage := None ;
    dc_cconv       := None ;
    dc_attrs       := [] ;
    dc_section     := None ;
    dc_align       := None ;
    dc_gc          := None
  |}.


(* This may seem to overlap with `defined_intrinsics`, but there are few differences:
   1. This one is defined outside of the module and could be used at the LLVM AST generation stage without yet specifying memory model.
   2. It includes declarations for built-in memory-dependent intrinisics such as `memcpy`.
 *)
Definition defined_intrinsics_decls :=
  [ fabs_32_decl; fabs_64_decl; memcpy_8_decl ].

(* This functor module provides a way to (extensibly) add the semantic behavior
   for intrinsics defined outside of the core Vellvm operational semantics.

   Internally, invocation of an intrinsic looks no different than that of an
   external function call, so each LLVM intrinsic instruction should produce
   a Call effect.

   Each intrinsic is identified by its name (a string) and its denotation is
   given by a function from a list of dynamic values to a dynamic value (or
   possibly an error).

   NOTE: The intrinsics that can be defined at this layer of the semantics
   cannot affect the core interpreter state or the memory model.  This layer is
   useful for implementing "pure value" intrinsics like floating point
   operations, etc.  Also note that such intrinsics cannot themselves generate
   any other effects.

*)
Module Make(A:MemoryAddress.ADDRESS)(LLVMIO: LLVM_INTERACTIONS(A)).
  Open Scope string_scope.

  Import LLVMIO.
  Import DV.

  (* Each (pure) intrinsic is defined by a function of the following type.

   - each intrinsic should "morally" be a total function: assuming the LLVM program
     is well formed, the intrisnic should always produce an LLVM value (which itself
     might be poison or undef)

   - error should be returned only in the case that the LLVM program is ill-formed
     (e.g. if the wrong number and/or type of arguments is given to the intrinsic)

   *)
  (* SAZ: TODO - unify this with the Denotational notion of semantic function?
  *)
  Definition semantic_function := (list dvalue) -> err dvalue.

  (* An association list mapping intrinsic names to their semantic definitions *)
  Definition intrinsic_definitions := list (declaration typ * semantic_function).


  (* Intrinsics semantic functions -------------------------------------------- *)

  (* Abosulute value for Float. *)
  Definition llvm_fabs_f32 : semantic_function :=
    fun args =>
      match args with
      | [DVALUE_Float d] => ret (DVALUE_Float (Float32.abs d))
      | _ => failwith "llvm_fabs_f64 got incorrect / ill-typed intputs"
      end.

  (* Abosulute value for Doubles. *)
  Definition llvm_fabs_f64 : semantic_function :=
    fun args =>
      match args with
      | [DVALUE_Double d] => ret (DVALUE_Double (Float.abs d))
      | _ => failwith "llvm_fabs_f64 got incorrect / ill-typed intputs"
      end.

  (* Clients of Vellvm can register the names of their own intrinsics
     definitions here. *)
  Definition defined_intrinsics : intrinsic_definitions :=
    [ (fabs_32_decl, llvm_fabs_f32) ;
      (fabs_64_decl, llvm_fabs_f64) ].

  (* SAZ: TODO: it could be nice to provide a more general/modular way to "lift"
     primitive functions into intrinsics. *)


End Make.
