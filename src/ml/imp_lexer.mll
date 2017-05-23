(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

{
  open Imp_parser
  let str = Camlcoq.coqstring_of_camlstring
  let of_str = Camlcoq.camlstring_of_coqstring
  let coq_of_int = Camlcoq.Nat.of_int

  let kw = function
  | "IFB"     -> IFB
  | "THEN"    -> THEN
  | "FI"      -> FI
  | "ELSE"    -> ELSE
  | "WHILE"   -> WHILE
  | "DO"      -> DO
  | "END"     -> END
  | "SKIP"    -> SKIP
  
  (*constants*)
  | "TRUE"  -> TRUE
  | "FALSE" -> FALSE

  (* catch_all *)
  | s -> failwith ("Unknown or unsupported keyword: " ^ s)

  type ident_type = Named | NamedString | Unnamed

}

let ws = [' ' '\t']
let eol = ('\n' | '\r' | "\r\n" | "\n\r")
let digit = ['0'-'9']
let upletter = ['A'-'Z']
let lowletter = ['a'-'z']
let letter = upletter | lowletter

rule token = parse
  (* seps and stuff *)
  | ws+     { token lexbuf }
  | eol     { Lexing.new_line lexbuf; token lexbuf }
  | eof     { EOF }
  | ";;"    { SEMISEMI }
  | '+'     { PLUS }
  | '-'     { DASH }
  | '*'     { STAR }
  | '='     { EQ }
  | "<="    { LTEQ }
  | '('     { LPAREN }
  | ')'     { RPAREN }
  | '!'     { BANG }
  | '&'     { AMPER }
  | "::="   { COLONCOLONEQ }

  (* constants *)
  | digit+ as d          { INT (int_of_string d) }

  (* keywords *)
  | upletter+ as a { kw a }
  | lowletter+ as a { IDENT a }

{

  let parse lexbuf =
    let parsing_err lexbuf =
      let pos = Lexing.lexeme_start_p lexbuf in
      let msg =
        Printf.sprintf "Parsing error: line %d, column %d, token '%s'"
                       pos.Lexing.pos_lnum
                       (pos.Lexing.pos_cnum - pos.Lexing.pos_bol)
                       (Lexing.lexeme lexbuf)
      in failwith msg
    in
    try Imp_parser.com_top token lexbuf
    with Imp_parser.Error -> parsing_err lexbuf

}
