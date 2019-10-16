From Coq Require Import
     ZArith List String.

From ExtLib Require Import
     Structures.Monads
     Programming.Eqv
     Data.String.

From Vellvm Require Import
     Error
     LLVMEvents
     LLVMAst
     Numeric.Integers
     Numeric.Floats
     IntrinsicsDefinitions
     TopLevel.

Import MonadNotation.
Import ListNotations.

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

  Definition Float_maxnum (a b: float): float :=
    if Float.cmp Clt a b then b else a.

  Definition Float32_maxnum (a b: float32): float32 :=
    if Float32.cmp Clt a b then b else a.

  Definition llvm_maxnum_f64 : IS.semantic_function :=
    fun args =>
      match args with
      | [DVALUE_Double a; DVALUE_Double b] => ret (DVALUE_Double (Float_maxnum a b))
      | _ => failwith "llvm_maxnum_f64 got incorrect / ill-typed intputs"
      end.

  Definition llvm_maxnum_f32 : IS.semantic_function :=
    fun args =>
      match args with
      | [DVALUE_Float a; DVALUE_Float b] => ret (DVALUE_Float (Float32_maxnum a b))
      | _ => failwith "llvm_maxnum_f32 got incorrect / ill-typed intputs"
      end.


  (* Clients of Vellvm can register the names of their own intrinsics
     definitions here. *)
  Definition user_intrinsics : IS.intrinsic_definitions :=
    [(maxnum_64_decl, llvm_maxnum_f64);
       (maxnum_32_decl, llvm_maxnum_f32)
    ].

  Definition user_interpreter := interpreter_user user_intrinsics.
