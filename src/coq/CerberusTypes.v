Require Import AilTypes.
Require Import ZArith String.

Definition struct_tag := symbol_sym.
Definition union_tag := symbol_sym.
Definition member_tag := symbol_sym.

Inductive ctype0 :=
| Void0
| Basic0 : basicType -> ctype0
| Array0 : ctype0 * option Z -> ctype0
| Function0 : (qualifiers * ctype0) * list (qualifiers * ctype0) * bool -> ctype0 (*isVariadic*)
| Pointer0 : qualifiers * ctype0 -> ctype0
| Atomic0 : ctype0 -> ctype0
(*
TODO: it should be like that
 | Struct of struct_tag * list (member_id * modifiable * ctype)
 | Union  of union_tag * list (member_id * modifiable * ctype)
*)
| Struct0 : struct_tag -> ctype0
| Union0 : union_tag -> ctype0
| Builtin0 : string -> ctype0
.


    Definition pointer_value := A.addr.
    Definition integer_value := Z.
    Definition floating_value := unit.

    Definition mem_value := dvalue.

    Definition footprint := unit.

    Definition mem_state := unit.
    Definition initial_mem_state := tt.

    (* TODO Original just uses Cthread.thread_id, not sure what we would use. *)
    Definition thread_id := nat.

    (* TODO Original used Core_ctype.ctype0... Not sure what this is, though. *)
    Definition ctype0 := dtyp.

    (* TODO Symbol.prefix *)
    Definition symbol_prefix := string.

    Definition symbol_sym := string.
    Definition null_ptrval := fun (_ : ctype0) => A.null.
    Definition fun_ptrval := fun (_ : symbol_sym) => A.null.
