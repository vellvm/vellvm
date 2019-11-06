;; open TopLevel.IO
open ITreeDefinition

val pp_addr : Format.formatter -> Memory.A.addr -> unit

val pp_uvalue : Format.formatter -> DV.uvalue -> unit

val interpret: ((LLVMAst.typ, (LLVMAst.typ LLVMAst.block) list) LLVMAst.toplevel_entity) list -> (DV.uvalue, string) result

(* SAZ: do we need to expose the step function in this way?  Its type is very complicated *)
(* val step : ((Obj.t Std.failureE, Obj.t debugE, 'b) Sum.sum1, DV.dvalue) coq_LLVM -> (TopLevel.IO.DV.dvalue, string) result *)
val step : ('a TopLevel.IO.coq_L5, TopLevel.TopLevelEnv.memory * ((TopLevel.TopLevelEnv.local_env * TopLevel.TopLevelEnv.stack) * (TopLevel.TopLevelEnv.global_env * TopLevel.IO.DV.uvalue))) itree -> (TopLevel.IO.DV.uvalue, string) result

val debug_flag: bool ref
