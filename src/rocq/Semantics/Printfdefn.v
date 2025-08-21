Require Import Floats.
From Stdlib Require Import
     List
     String
     ZArith.
From Vellvm Require Import
  Utilities
  Utils.IntMaps
  Syntax
  Syntax.LLVMAst
  Syntax.AstLib
  Semantics.LLVMEvents
  Semantics.Denotation
  Semantics.IntrinsicsDefinitions
  Semantics.InterpretationStack
  Semantics.VellvmIntegers
  Semantics.StoreId.

Import ListNotations.

  Definition ll_toplevel_entities := toplevel_entities typ 
                                       (block typ * list (block typ)).

  Local Notation t_ptr t := (TYPE_Pointer (Some t)).

  (* METADATA TODO: regenerate this definition *)
  Definition printf_definition : ll_toplevel_entities := [].
