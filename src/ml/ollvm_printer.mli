val pp_sep : string -> Format.formatter -> unit -> unit
val pp_space : Format.formatter -> unit -> unit
val pp_comma_space : Format.formatter -> unit -> unit
val linkage : Format.formatter -> Ollvm_ast.linkage -> unit
val dll_storage : Format.formatter -> Ollvm_ast.dll_storage -> unit
val visibility : Format.formatter -> Ollvm_ast.visibility -> unit
val cconv : Format.formatter -> Ollvm_ast.cconv -> unit
val param_attr : Format.formatter -> Ollvm_ast.param_attr -> unit
val fn_attr : Format.formatter -> Ollvm_ast.fn_attr -> unit
val ident : Format.formatter -> Ollvm_ast.ident -> unit
val typ : Format.formatter -> Ollvm_ast.typ -> unit
val icmp : Format.formatter -> Ollvm_ast.icmp -> unit
val fcmp : Format.formatter -> Ollvm_ast.fcmp -> unit
val ibinop : Format.formatter -> Ollvm_ast.ibinop -> unit
val fbinop : Format.formatter -> Ollvm_ast.fbinop -> unit
val fast_math : Format.formatter -> Ollvm_ast.fast_math -> unit
val conversion_type : Format.formatter -> Ollvm_ast.conversion_type -> unit
val instr : Format.formatter -> Ollvm_ast.instr -> unit
val value : Format.formatter -> Ollvm_ast.value -> unit
val tvalue : Format.formatter -> Ollvm_ast.tvalue -> unit
val tident : Format.formatter -> Ollvm_ast.tident -> unit
val toplevel_entities :
  Format.formatter -> (Ollvm_ast.block list) Ollvm_ast.toplevel_entities -> unit
val toplevel_entity : Format.formatter -> (Ollvm_ast.block list) Ollvm_ast.toplevel_entity -> unit
val metadata : Format.formatter -> Ollvm_ast.metadata -> unit
val global : Format.formatter -> Ollvm_ast.global -> unit
val declaration : Format.formatter -> Ollvm_ast.declaration -> unit
val definition : Format.formatter -> (Ollvm_ast.block list) Ollvm_ast.definition -> unit
val block : Format.formatter -> Ollvm_ast.block -> unit
val modul : Format.formatter -> (Ollvm_ast.block list) Ollvm_ast.modul -> unit
