(*  ------------------------------------------------------------------------- *)
(* Adapted for use in Vellvm by Steve Zdancewic (c) 2017                      *)
(*  ------------------------------------------------------------------------- *)

open Format
open LLVMAst


let toplevel_entities (fmt : Format.formatter) (tles: (LLVMAst.typ , (LLVMAst.typ LLVMAst.block) * ((LLVMAst.typ LLVMAst.block) list)) LLVMAst.toplevel_entities) : unit =
  Format.pp_print_string fmt (Camlcoq.camlstring_of_coqstring (ShowAST.showProg tles))


let string_of_typ (t:LLVMAst.typ) = Camlcoq.camlstring_of_coqstring (ShowAST.show_typ t)
let string_of_exp (e:LLVMAst.typ LLVMAst.exp) = Camlcoq.camlstring_of_coqstring (ShowAST.show_exp ShowAST.show_typ e)

