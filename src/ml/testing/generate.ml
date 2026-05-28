(* Stub: the previous QuickChick/Alive2-driven generator depended on the
   InfAddr/BigIP/FinSizeof memory-model modules that are no longer extracted
   on this branch. Until the random testing layer is rebuilt, only the type
   signatures consumed by [Assertion] remain. *)

module GA = struct
  type runnable_blocks =
    LLVMAst.typ LLVMAst.block * LLVMAst.typ LLVMAst.block list
end

let unavailable name = failwith (name ^ ": srctgt random testing is disabled on this branch")

let generate_n_args (_ : int)
    (_ : LLVMAst.typ list)
  : (LLVMAst.typ * DynamicValues.dvalue) list list =
  unavailable "Generate.generate_n_args"

let generate_n_runner (_ : int)
    (_ : LLVMAst.typ list) (_ : LLVMAst.typ)
    (_ : char list) (_ : char list)
  : ((LLVMAst.typ, GA.runnable_blocks) LLVMAst.toplevel_entity
     * (LLVMAst.typ, GA.runnable_blocks) LLVMAst.toplevel_entity) list =
  unavailable "Generate.generate_n_runner"

let explode_str s = List.init (String.length s) (String.get s)
