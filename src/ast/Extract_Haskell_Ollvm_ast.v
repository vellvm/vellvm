Require Import Ascii String.
Extraction Language Haskell.

Require Import Vellvm.Ollvm_ast.

Extract Inductive string => "Prelude.String" [ "[]" "(:)" ].
Extract Inlined Constant int => "Prelude.Int".
Extract Inlined Constant float => "Prelude.Float".

Extraction Library Datatypes.
Extraction Library Ollvm_ast.
