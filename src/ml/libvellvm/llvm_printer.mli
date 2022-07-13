open InterpretationStack.InterpreterStackBigIntptr.LP.Events

val toplevel_entities :
  Format.formatter -> (LLVMAst.typ , (LLVMAst.typ LLVMAst.block) * ((LLVMAst.typ LLVMAst.block) list)) LLVMAst.toplevel_entities -> unit
val string_of_typ : LLVMAst.typ -> string
val string_of_exp : LLVMAst.typ LLVMAst.exp -> string  
val string_of_dvalue : DV.dvalue -> string
