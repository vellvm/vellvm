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

  (* NOTE:
     Regenerating the printf_definition is necessary when the LLVMAst representation changes.

     To create this definition:
     1. run `./vellvm -print-ast ../utilities/vaargs/printf-src/printf.ll` from the `src` directory
        this will generate the file src/output/printf.v.ast 
     2. copy the list appearing after "Internal Coq representation of the ast:" to 
        be the definition of `printf_definition` (below).
     3. add a `.` to the end of the list
     4. replace all occurrences of slash double-quote (OCaml quoted quotes) double-quote double-quote
        (Rocq quoted quotes)

     TODOS
        - cleanup the `-print-ast` flag
        - fix pretty-printing of quoted strings in `ReprAst`
        - add a make target to auto-generate this file.
   *)

  Definition printf_definition : ll_toplevel_entities := [].
  
