
Require Import Vellvm.Maps Vellvm.Imp Vellvm.CompilerProp.
Require Import Vellvm.ImpQuickChick.

Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Require Import List ZArith.
Import ListNotations.
Require Import String.





(* Example program that fails imp_compiler_correct here:
Eample prog1 := X ::= APlus (AId W) (AId W).
*)

QuickChick (forAll arbitrary
                   imp_compiler_correct_aux).


Definition result1 := imp_compiler_correct_aux prog1.
(* Recursive Extraction result1.  *)
(* Eval vm_compute in (imp_compiler_correct_aux prog1). *)