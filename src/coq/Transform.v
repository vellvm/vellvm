Require Import Ascii Strings.String.
Require Import Vellvm.Ollvm_ast.
Open Scope string_scope.


Parameter str_cat : string -> string -> string.
Parameter str_nil : string.
Parameter str_cons : (ascii * string) -> string.

Definition mangle_raw_id (id:raw_id) : raw_id :=
  match id with
  | Anon n => id
  | Name s => Name (str_cat "_vellvm" s)
  end.

Definition mangle_ident (id:ident) : ident :=
  match id with
  | ID_Global i => ID_Global (mangle_raw_id i)
  | ID_Local i => ID_Local (mangle_raw_id i)
  end.

Definition mangle_declaration (d:declaration) : declaration :=
  mk_declaration
    (mangle_ident (dc_name d))
    (dc_type d)
    (dc_param_attrs d)
.

Definition mangle_instr (i:instr_id * instr) : (instr_id * instr) :=
  match i with
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


Definition mangle_toplevel_entity (tle : toplevel_entity) : toplevel_entity :=
  match tle with
  | TLE_Definition d => TLE_Definition (mangle_definition d)
  | _ => tle
  end.

Definition transform (prog: list toplevel_entity) : list toplevel_entity :=
  List.map mangle_toplevel_entity prog.