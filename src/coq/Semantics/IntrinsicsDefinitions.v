(* begin hide *)
From Coq Require Import
     ZArith List String.

From ExtLib Require Import
     Structures.Monads
     Programming.Eqv
     Data.String.

From Vellvm Require Import
     Utilities
     Syntax
     Semantics.LLVMEvents
     Numeric.Coqlib
     Numeric.Integers
     Numeric.Floats.

From ITree Require Import
     ITree.

From Flocq.IEEE754 Require Import
     BinarySingleNaN
     Binary
     Bits.

Import MonadNotation.
Import EqvNotation.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.
(* end hide *)

(** * Intrinsics
    VIR provides an easily extensible support for instrinsics.
    In this file are defined the intrinsics suuported by VIR.
    Each intrinsic must be:
    - registered by providing a [declaration typ] and added to [defined_intrinsics_decls]
    - _if_ the intrinsics is a pure computation, it must be implemented as a pure Gallina
      function of type [semantic_function] and added to [defined_intrinsics]
    - _if_ it is impure, i.e. depends on the memory, as is the case for [memcpy], its
    implementation must be provided in [src/coq/Handlers/Memory.v] and an equality test on its
    name added to [handle_intrinsic].
*)

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
  let pt := TYPE_Pointer (TYPE_I 8%N) in
  let i32 := TYPE_I 32%N in
  let i1 := TYPE_I 1%N in
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


Definition maxnum_64_decl: declaration typ :=
  {|
    dc_name        := Name "llvm.maxnum.f64";
    dc_type        := TYPE_Function TYPE_Double [TYPE_Double;TYPE_Double] ;
    dc_param_attrs := ([], [[];[]]);
    dc_linkage     := None ;
    dc_visibility  := None ;
    dc_dll_storage := None ;
    dc_cconv       := None ;
    dc_attrs       := [] ;
    dc_section     := None ;
    dc_align       := None ;
    dc_gc          := None
  |}.

Definition minimum_64_decl: declaration typ :=
  {|
    dc_name        := Name "llvm.minimum.f64";
    dc_type        := TYPE_Function TYPE_Double [TYPE_Double;TYPE_Double] ;
    dc_param_attrs := ([], [[];[]]);
    dc_linkage     := None ;
    dc_visibility  := None ;
    dc_dll_storage := None ;
    dc_cconv       := None ;
    dc_attrs       := [] ;
    dc_section     := None ;
    dc_align       := None ;
    dc_gc          := None
  |}.

Definition maxnum_32_decl: declaration typ :=
  {|
    dc_name        := Name "llvm.maxnum.f32";
    dc_type        := TYPE_Function TYPE_Float [TYPE_Float;TYPE_Float] ;
    dc_param_attrs := ([], [[];[]]);
    dc_linkage     := None ;
    dc_visibility  := None ;
    dc_dll_storage := None ;
    dc_cconv       := None ;
    dc_attrs       := [] ;
    dc_section     := None ;
    dc_align       := None ;
    dc_gc          := None
  |}.

Definition minimum_32_decl: declaration typ :=
  {|
    dc_name        := Name "minimum.f32";
    dc_type        := TYPE_Function TYPE_Float [TYPE_Float;TYPE_Float] ;
    dc_param_attrs := ([], [[];[]]);
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
  [ fabs_32_decl; fabs_64_decl; maxnum_32_decl ; maxnum_64_decl; minimum_32_decl; minimum_64_decl; memcpy_8_decl ].

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
  Definition semantic_function := (list dvalue) -> err dvalue.

  (* An association list mapping intrinsic names to their semantic definitions *)
  Definition intrinsic_definitions := list (declaration typ * semantic_function).


  (* Intrinsics semantic functions -------------------------------------------- *)

  (* Abosulute value for Float. *)
  Definition llvm_fabs_f32 : semantic_function :=
    fun args =>
      match args with
      | [DVALUE_Float d] => ret (DVALUE_Float (b32_abs d))
      | _ => failwith "llvm_fabs_f64 got incorrect / ill-typed intputs"
      end.

  (* Abosulute value for Doubles. *)
  Definition llvm_fabs_f64 : semantic_function :=
    fun args =>
      match args with
      | [DVALUE_Double d] => ret (DVALUE_Double (b64_abs d))
      | _ => failwith "llvm_fabs_f64 got incorrect / ill-typed intputs"
      end.

  Definition Float_maxnum (a b: float): float :=
    match a, b with
    | B754_nan _ _ _ _ _, _ | _, B754_nan _ _ _ _ _ => build_nan _ _ (binop_nan_pl64 a b)
    | _, _ =>
      if Float.cmp Clt a b then b else a
    end.

  Definition Float32_maxnum (a b: float32): float32 :=
    match a, b with
    | B754_nan _ _ _ _ _, _ | _, B754_nan _ _ _ _ _ => build_nan _ _ (binop_nan_pl32 a b)
    | _, _ =>
      if Float32.cmp Clt a b then b else a
    end.

  Definition llvm_maxnum_f64 : semantic_function :=
    fun args =>
      match args with
      | [DVALUE_Double a; DVALUE_Double b] => ret (DVALUE_Double (Float_maxnum a b))
      | _ => failwith "llvm_maxnum_f64 got incorrect / ill-typed intputs"
      end.

  Definition llvm_maxnum_f32 : semantic_function :=
    fun args =>
      match args with
      | [DVALUE_Float a; DVALUE_Float b] => ret (DVALUE_Float (Float32_maxnum a b))
      | _ => failwith "llvm_maxnum_f32 got incorrect / ill-typed intputs"
      end.

  Definition Float_minimum (a b: float): float :=
    match a, b with
    | B754_nan _ _ _ _ _, _ | _, B754_nan _ _ _ _ _ => build_nan _ _ (binop_nan_pl64 a b)
    | _, _ =>
      if Float.cmp Clt a b then a else b
    end.

  Definition Float32_minimum (a b: float32): float32 :=
    match a, b with
    | B754_nan _ _ _ _ _, _ | _, B754_nan _ _ _ _ _ => build_nan _ _ (binop_nan_pl32 a b)
    | _, _ =>
      if Float32.cmp Clt a b then a else b
    end.

  Definition llvm_minimum_f64 : semantic_function :=
    fun args =>
      match args with
      | [DVALUE_Double a; DVALUE_Double b] => ret (DVALUE_Double (Float_minimum a b))
      | _ => failwith "llvm_minimum_f64 got incorrect / ill-typed intputs"
      end.

  Definition llvm_minimum_f32 : semantic_function :=
    fun args =>
      match args with
      | [DVALUE_Float a; DVALUE_Float b] => ret (DVALUE_Float (Float32_minimum a b))
      | _ => failwith "llvm_minimum_f32 got incorrect / ill-typed intputs"
      end.

  (* Clients of Vellvm can register the names of their own intrinsics
     definitions here. *)
  Definition defined_intrinsics : intrinsic_definitions :=
    [ (fabs_32_decl, llvm_fabs_f32) ;
    (fabs_64_decl, llvm_fabs_f64) ;
    (maxnum_32_decl , llvm_maxnum_f32) ;
    (maxnum_64_decl , llvm_maxnum_f64);
    (minimum_32_decl, llvm_minimum_f32);
    (minimum_64_decl, llvm_minimum_f64)
    ].


End Make.
