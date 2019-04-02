;; open TopLevel.IO

val pp_addr : Format.formatter -> Memory.A.addr -> unit

val pp_dvalue : Format.formatter -> DV.dvalue -> unit

val interpret: ((LLVMAst.block list) LLVMAst.toplevel_entity list) -> (DV.dvalue, string) result

(* SAZ: do we need to expose the step function in this way?  Its type is very complicated *)
(* val step : ((Obj.t Std.failureE, Obj.t debugE, 'b) Sum.sum1, DV.dvalue) coq_LLVM -> (TopLevel.IO.DV.dvalue, string) result *)
val step : ((Obj.t failureE, Obj.t debugE, 'b) Sum.sum1, 'a * DV.dvalue) coq_LLVM -> (TopLevel.IO.DV.dvalue, string) result

val debug_flag: bool ref
