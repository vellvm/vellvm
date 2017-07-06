Require Import String.
Open Scope string_scope.

(* print list of args to the *trace* buffer in proof general *)
Tactic Notation "ltrace" constr_list(cl) := idtac "<ltrace>" cl "</ltrace>".


