Require Import Ascii Strings.String.
Require Import Vellvm.Ollvm_ast.
Open Scope string_scope.


Parameter str_cat : string -> string -> string.
Parameter str_nil : string.
Parameter str_cons : (ascii * string) -> string.

Definition mangle_ident (id:ident) : ident :=
  match id with
  | ID_Global s => ID_Global (str_cat s "_vellvm")
  | ID_Local s => ID_Local (str_cat s "_vellvm")
  end.

Definition mangle_declaration (d:declaration) : declaration :=
  mk_declaration
    (mangle_ident (dc_name d))
    (dc_type d)
    (dc_param_attrs d)
.

Definition mangle_instr (i:instr) : instr :=
  match i with
  | INSTR_Assign s j => INSTR_Assign (mangle_ident s) i
  | _ => i
  end.

Definition mangle_block (blk:block) : block :=
  let (name, instrs) := blk in
  (name, List.map mangle_instr instrs).

Definition mangle_blocks (blks:list block) : list block :=
  List.map mangle_block blks.

Definition mangle_definition (d:definition) : definition :=
  mk_definition
  (df_prototype d)
  (df_args d)
  (mangle_blocks (df_instrs d))
  (df_linkage d)
  (df_visibility d)
  (df_dll_storage d)
  (df_cconv d)
  (df_attrs d)
  (df_section d)
  (df_align d)
  (df_gc d)
.


Definition mangle_toplevelentry (tle : toplevelentry) : toplevelentry :=
  match tle with
  | TLE_Definition d => TLE_Definition (mangle_definition d)
  | _ => tle
  end.

Definition transform (prog: list toplevelentry) : list toplevelentry :=
  List.map mangle_toplevelentry prog.