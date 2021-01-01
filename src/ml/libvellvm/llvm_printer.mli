val pp_sep : string -> Format.formatter -> unit -> unit
val pp_space : Format.formatter -> unit -> unit
val pp_comma_space : Format.formatter -> unit -> unit
val linkage : Format.formatter -> LLVMAst.linkage -> unit
val dll_storage : Format.formatter -> LLVMAst.dll_storage -> unit
val visibility : Format.formatter -> LLVMAst.visibility -> unit
val cconv : Format.formatter -> LLVMAst.cconv -> unit
val param_attr : Format.formatter -> LLVMAst.param_attr -> unit
val fn_attr : Format.formatter -> LLVMAst.fn_attr -> unit
val ident : Format.formatter -> LLVMAst.ident -> unit
val typ : Format.formatter -> LLVMAst.typ -> unit
val icmp : Format.formatter -> LLVMAst.icmp -> unit
val fcmp : Format.formatter -> LLVMAst.fcmp -> unit
val ibinop : Format.formatter -> LLVMAst.ibinop -> unit
val fbinop : Format.formatter -> LLVMAst.fbinop -> unit
val fast_math : Format.formatter -> LLVMAst.fast_math -> unit
val conversion_type : Format.formatter -> LLVMAst.conversion_type -> unit
val instr : Format.formatter -> LLVMAst.typ LLVMAst.instr -> unit
val exp : Format.formatter -> LLVMAst.typ LLVMAst.exp -> unit
val texp : Format.formatter -> LLVMAst.typ LLVMAst.texp -> unit
val tident : Format.formatter -> LLVMAst.typ LLVMAst.tident -> unit
val toplevel_entities :
  Format.formatter -> (LLVMAst.typ , (LLVMAst.typ LLVMAst.block) * ((LLVMAst.typ LLVMAst.block) list)) LLVMAst.toplevel_entities -> unit
val toplevel_entity : Format.formatter -> (LLVMAst.typ, (LLVMAst.typ LLVMAst.block) * ((LLVMAst.typ LLVMAst.block) list)) LLVMAst.toplevel_entity -> unit
val metadata : Format.formatter -> LLVMAst.typ LLVMAst.metadata -> unit
val global : Format.formatter -> LLVMAst.typ LLVMAst.global -> unit
val declaration : Format.formatter -> LLVMAst.typ LLVMAst.declaration -> unit
val definition : Format.formatter -> (LLVMAst.typ, (LLVMAst.typ LLVMAst.block) * ((LLVMAst.typ LLVMAst.block) list)) LLVMAst.definition -> unit
val block : Format.formatter -> (LLVMAst.typ LLVMAst.block) -> unit
val modul : Format.formatter -> (LLVMAst.typ, (LLVMAst.typ LLVMAst.block) * ((LLVMAst.typ LLVMAst.block) list)) CFG.modul -> unit
