Require Import Ascii String.
Extraction Language Haskell.

Require Import Vellvm.Ollvm_ast.

Extract Inductive option => "Prelude.Maybe" [ "Nothing" "Just" ].
Extract Inductive list => "[]" [ "[]" "(:)" ].
Extract Inductive prod => "(,)" [ "(,)" ].
Extract Inductive string => "Prelude.String" [ "[]" "(:)" ].
Extract Inductive bool => "Prelude.Bool" [ "False" "True" ].
Extract Inlined Constant int => "Prelude.Int".
Extract Inlined Constant float => "Prelude.Float".

Extraction Library Datatypes.
Extraction Library Ollvm_ast.
