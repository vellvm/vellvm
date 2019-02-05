;; open TopLevel.IO

val pp_addr : Format.formatter -> Memory.A.addr -> unit

val pp_dvalue : Format.formatter -> DV.dvalue -> unit

val interpret: ((LLVMAst.block list) LLVMAst.toplevel_entity list) -> (DV.dvalue, string) result

val step: (DV.dvalue coq_Trace) -> (DV.dvalue, string) result

val debug_flag: bool ref
