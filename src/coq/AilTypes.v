(** Types *************************************************************************************** *)
Require Import ZArith.
Require Import String.

Definition symbol_sym := string.
Definition identifier := symbol_sym.

Inductive (* name = "^\\(\\|\\([a-z A-Z]+_\\)\\)ibty[0-9]*'?$"*) integerBaseType :=
 | Ichar
 | Short
 | Int_
 | Long
 | LongLong
   (* Things defined in the standard libraries *)
 | IntN_t : Z -> integerBaseType
 | Int_leastN_t :  Z -> integerBaseType
 | Int_fastN_t :  Z -> integerBaseType
 | Intmax_t
 | Intptr_t
.
(* | IBBuiltin of string *)


(* STD Â§6.2.5#17, sentence 1 *)
Inductive integerType (* [name = "^\\(\\|\\([a-z A-Z]+_\\)\\)ity[0-9]*'?$"] *) :=
 | Char
 | Bool
 | Signed : integerBaseType -> integerType
 | Unsigned : integerBaseType -> integerType
 | IBuiltin : string -> integerType
 | Enum : identifier -> integerType
 | Size_t
 | Ptrdiff_t
(*
 | Wchar_t (* TODO: merge into a IBuiltin variant ? *)
 | Char16_t (* TODO: merge into a IBuiltin variant ? *)
 | Char32_t (* TODO: merge into a IBuiltin variant ? *)
*)
 (* | StdInt of string (\* integer types defined in stdint.h (Â§7.20) *\)  *)
.

(* STD Â§6.2.5#10, sentence 1 *)
Inductive realFloatingType :=
  | Float
  | Double
  | LongDouble
.

(* STD Â§6.2.5#11, sentence 2 *)
Inductive floatingType :=
| RealFloating : realFloatingType -> floatingType
.
(*  | Complex of floatingType (* STD Â§6.2.5#11, sentence 1 *) *)

(* STD Â§6.2.5#14, sentence 1 *)
Inductive (* name = "^\\(\\|\\([a-z A-Z]+_\\)\\)bty[0-9]*'?$"*) basicType :=
 | Integer : integerType -> basicType
 | Floating : floatingType -> basicType
.

Inductive qualifiers (*[name = "^\\(\\|\\([a-z A-Z]+_\\)\\)qs[0-9]*'?$"]*) :=
| const    : bool -> qualifiers
| restrict : bool -> qualifiers
| volatile : bool -> qualifiers
.