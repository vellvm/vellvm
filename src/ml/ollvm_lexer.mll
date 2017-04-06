 (* {{{ LICENSE                                                              *
  * vi: set fdm=marker fdl=0:                                                *
  *                                                                          *
  * Copyright (c) 2012 Raphaël Proust <raphlalou@gmail.com>                  *
  * Copyright (c) 2012 INRIA - Raphaël Proust <raphlalou@gmail.com>          *
  * Copyright (c) 2012 ENS - Raphaël Proust <raphlalou@gmail.com>            *
  *                                                                          *
  * Permission to use, copy, modify, and distribute this software for any    *
  * purpose with or without fee is hereby granted, provided that the above   *
  * copyright notice and this permission notice appear in all copies.        *
  *                                                                          *
  * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES *
  * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF         *
  * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR  *
  * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES   *
  * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN    *
  * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF  *
  * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.           *
  * }}}                                                                      *)

(*  ------------------------------------------------------------------------- *)
(* Adapted for use in Vellvm by Steve Zdancewic (c) 2017                      *)
(*  ------------------------------------------------------------------------- *)

{
  open Ollvm_parser
  let str = Camlcoq.coqstring_of_camlstring
  let of_str = Camlcoq.camlstring_of_coqstring
  let coq_of_int = Camlcoq.Z.of_sint

  exception Lex_error_unterminated_string of Lexing.position

  let kw = function
  | "target"                       -> KW_TARGET
  | "datalayout"                   -> KW_DATALAYOUT
  | "source_filename"              -> KW_SOURCE_FILENAME
  | "triple"                       -> KW_TRIPLE
  | "define"                       -> KW_DEFINE
  | "declare"                      -> KW_DECLARE
  | "private"                      -> KW_PRIVATE
  | "internal"                     -> KW_INTERNAL
  | "available_externally"         -> KW_AVAILABLE_EXTERNALLY
  | "linkonce"                     -> KW_LINKONCE
  | "weak"                         -> KW_WEAK
  | "common"                       -> KW_COMMON
  | "appending"                    -> KW_APPENDING
  | "extern_weak"                  -> KW_EXTERN_WEAK
  | "linkonce_odr"                 -> KW_LINKONCE_ODR
  | "weak_odr"                     -> KW_WEAK_ODR
  | "external"                     -> KW_EXTERNAL
  | "dllimport"                    -> KW_DLLIMPORT
  | "dllexport"                    -> KW_DLLEXPORT
  | "default"                      -> KW_DEFAULT
  | "hidden"                       -> KW_HIDDEN
  | "protected"                    -> KW_PROTECTED
  | "ccc"                          -> KW_CCC
  | "fastcc"                       -> KW_FASTCC
  | "coldcc"                       -> KW_COLDCC
  | "cc"                           -> KW_CC
  | "unnamed_addr"                 -> KW_UNNAMED_ADDR
  | "type"                         -> KW_TYPE
  | "opaque"                       -> KW_OPAQUE
  | "global"                       -> KW_GLOBAL
  | "addrspace"                    -> KW_ADDRSPACE
  | "externally_initialized"       -> KW_EXTERNALLY_INITIALIZED
  | "constant"                     -> KW_CONSTANT
  | "section"                      -> KW_SECTION
  | "thread_local"                 -> KW_THREAD_LOCAL
  | "localdynamic"                 -> KW_LOCALDYNAMIC
  | "initialexec"                  -> KW_INITIALEXEC
  | "localexec"                    -> KW_LOCALEXEC
  | "zeroext"                      -> KW_ZEROEXT
  | "signext"                      -> KW_SIGNEXT
  | "inreg"                        -> KW_INREG
  | "byval"                        -> KW_BYVAL
  | "sret"                         -> KW_SRET
  | "noalias"                      -> KW_NOALIAS
  | "nocapture"                    -> KW_NOCAPTURE
  | "nest"                         -> KW_NEST
  | "dereferenceable"              -> KW_DEREFERENCEABLE
  | "inalloca"                     -> KW_INALLOCA
  | "returned"                     -> KW_RETURNED
  | "nonnull"                      -> KW_NONNULL
  | "alignstack"                   -> KW_ALIGNSTACK
  | "alwaysinline"                 -> KW_ALWAYSINLINE
  | "builtin"                      -> KW_BUILTIN
  | "cold"                         -> KW_COLD
  | "inlinehint"                   -> KW_INLINEHINT
  | "jumptable"                    -> KW_JUMPTABLE
  | "minsize"                      -> KW_MINSIZE
  | "naked"                        -> KW_NAKED
  | "nobuiltin"                    -> KW_NOBUILTIN
  | "noduplicate"                  -> KW_NODUPLICATE
  | "noimplicitfloat"              -> KW_NOIMPLICITFLOAT
  | "noinline"                     -> KW_NOINLINE
  | "nonlazybind"                  -> KW_NONLAZYBIND
  | "noredzone"                    -> KW_NOREDZONE
  | "noreturn"                     -> KW_NORETURN
  | "nounwind"                     -> KW_NOUNWIND
  | "optnone"                      -> KW_OPTNONE
  | "optsize"                      -> KW_OPTSIZE
  | "readnone"                     -> KW_READNONE
  | "readonly"                     -> KW_READONLY
  | "returns_twice"                -> KW_RETURNS_TWICE
  | "sanitize_address"             -> KW_SANITIZE_ADDRESS
  | "sanitize_memory"              -> KW_SANITIZE_MEMORY
  | "sanitize_thread"              -> KW_SANITIZE_THREAD
  | "ssp"                          -> KW_SSP
  | "sspreq"                       -> KW_SSPREQ
  | "sspstrong"                    -> KW_SSPSTRONG
  | "uwtable"                      -> KW_UWTABLE
  | "align"                        -> KW_ALIGN
  | "gc"                           -> KW_GC
  | "to"                           -> KW_TO
  | "unwind"                       -> KW_UNWIND
  | "tail"                         -> KW_TAIL
  | "volatile"                     -> KW_VOLATILE

  (* instrs *)
  | "add"            -> KW_ADD
  | "fadd"           -> KW_FADD
  | "sub"            -> KW_SUB
  | "fsub"           -> KW_FSUB
  | "mul"            -> KW_MUL
  | "fmul"           -> KW_FMUL
  | "udiv"           -> KW_UDIV
  | "sdiv"           -> KW_SDIV
  | "fdiv"           -> KW_FDIV
  | "urem"           -> KW_UREM
  | "srem"           -> KW_SREM
  | "frem"           -> KW_FREM
  | "shl"            -> KW_SHL
  | "lshr"           -> KW_LSHR
  | "ashr"           -> KW_ASHR
  | "and"            -> KW_AND
  | "or"             -> KW_OR
  | "xor"            -> KW_XOR
  | "icmp"           -> KW_ICMP
  | "fcmp"           -> KW_FCMP
  | "phi"            -> KW_PHI
  | "call"           -> KW_CALL
  | "trunc"          -> KW_TRUNC
  | "zext"           -> KW_ZEXT
  | "sext"           -> KW_SEXT
  | "fptrunc"        -> KW_FPTRUNC
  | "fpext"          -> KW_FPEXT
  | "uitofp"         -> KW_UITOFP
  | "sitofp"         -> KW_SITOFP
  | "fptoui"         -> KW_FPTOUI
  | "fptosi"         -> KW_FPTOSI
  | "inttoptr"       -> KW_INTTOPTR
  | "ptrtoint"       -> KW_PTRTOINT
  | "bitcast"        -> KW_BITCAST
  | "select"         -> KW_SELECT
  | "va_arg"         -> KW_VAARG
  | "ret"            -> KW_RET
  | "br"             -> KW_BR
  | "switch"         -> KW_SWITCH
  | "indirectbr"     -> KW_INDIRECTBR
  | "invoke"         -> KW_INVOKE
  | "resume"         -> KW_RESUME
  | "unreachable"    -> KW_UNREACHABLE
  | "alloca"         -> KW_ALLOCA
  | "load"           -> KW_LOAD
  | "store"          -> KW_STORE
  | "cmpxchg"        -> KW_ATOMICCMPXCHG
  | "atomicrmw"      -> KW_ATOMICRMW
  | "fence"          -> KW_FENCE
  | "getelementptr"  -> KW_GETELEMENTPTR
  | "inbounds"       -> KW_INBOUNDS
  | "extractelement" -> KW_EXTRACTELEMENT
  | "insertelement"  -> KW_INSERTELEMENT
  | "shufflevector"  -> KW_SHUFFLEVECTOR
  | "extractvalue"   -> KW_EXTRACTVALUE
  | "insertvalue"    -> KW_INSERTVALUE
  | "landingpad"     -> KW_LANDINGPAD

  (* icmp *)
  | "nuw"            -> KW_NUW
  | "nsw"            -> KW_NSW
  | "exact"          -> KW_EXACT
  | "eq"             -> KW_EQ
  | "ne"             -> KW_NE
  | "ugt"            -> KW_UGT
  | "uge"            -> KW_UGE
  | "ult"            -> KW_ULT
  | "ule"            -> KW_ULE
  | "sgt"            -> KW_SGT
  | "sge"            -> KW_SGE
  | "slt"            -> KW_SLT
  | "sle"            -> KW_SLE

  (* fcmp. true and false are already handled later.
   * some are already handled in icmp *)
  | "oeq"            -> KW_OEQ
  | "ogt"            -> KW_OGT
  | "oge"            -> KW_OGE
  | "olt"            -> KW_OLT
  | "ole"            -> KW_OLE
  | "one"            -> KW_ONE
  | "ord"            -> KW_ORD
  | "uno"            -> KW_UNO
  | "ueq"            -> KW_UEQ
  | "une"            -> KW_UNE

  (* fast math flags *)
  | "nnan"           -> KW_NNAN
  | "ninf"           -> KW_NINF
  | "nsz"            -> KW_NSZ
  | "arcp"           -> KW_ARCP
  | "fast"           -> KW_FAST

  (*types*)
  | "void"      -> KW_VOID
  | "half"      -> KW_HALF
  | "float"     -> KW_FLOAT
  | "double"    -> KW_DOUBLE
  | "x86_fp80"  -> KW_X86_FP80
  | "fp128"     -> KW_FP128
  | "ppc_fp128" -> KW_PPC_FP128
  | "label"     -> KW_LABEL
  | "metadata"  -> KW_METADATA
  | "x86_mmx"   -> KW_X86_MMX

  | "attributes" -> KW_ATTRIBUTES

  (*constants*)
  | "true"  -> KW_TRUE
  | "false" -> KW_FALSE
  | "null"  -> KW_NULL
  | "undef" -> KW_UNDEF
  | "zeroinitializer" -> KW_ZEROINITIALIZER
  | "c" -> KW_C
  
  (* misc *)
  | "x" -> KW_X

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
let alphanum = digit | letter
let ident_fst  = letter   | ['-' '$' '.' '_']
let ident_nxt  = alphanum | ['-' '$' '.' '_']
let label_char = alphanum | ['-' '$' '.' '_']
let kwletter   = alphanum | ['_']

rule token = parse
  (* seps and stuff *)
  | ws+ { token lexbuf }
  | eol { Lexing.new_line lexbuf; EOL }
  | eof { EOF }
  | ';' { comment lexbuf }
  | '=' { EQ }
  | ',' { COMMA }
  | '('  { LPAREN }
  | ')'  { RPAREN }
  | '{'  { LCURLY }
  | '}'  { RCURLY }
  | "<{" { LTLCURLY }
  | "}>" { RCURLYGT }
  | '['  { LSQUARE }
  | ']'  { RSQUARE }
  | '<'  { LT }
  | '>'  { GT }

  (* labels *)
  | ((label_char)+) as l ':' { LABEL l }

  (* identifier *)
  | '@' { GLOBAL (raw_id lexbuf) }
  | '%' { LOCAL (raw_id lexbuf) }

  (* FIXME: support metadata strings and struct. Parsed as identifier here. *)
  | "!{" { BANGLCURLY }
  | '!'  { let rid = raw_id lexbuf in
           begin match rid with 
           | Ollvm_ast.Name id ->
	   let id = of_str id in
	   (if id.[0] = '"' && id.[String.length id - 1] = '"'
               then METADATA_STRING id
               else METADATA_ID rid)
	   | Ollvm_ast.Anon _ -> METADATA_ID rid
	   end
         }

  | '#' (digit+ as i) { ATTR_GRP_ID (coq_of_int (int_of_string i)) }

  (* constants *)
  | '-'? digit+ as d            { INTEGER (coq_of_int (int_of_string d)) }
  | '-'? digit* '.' digit+ as d { FLOAT (float_of_string d) }
  | '-'? digit ('.' digit+)? 'e' ('+'|'-') digit+ as d
                                { FLOAT (float_of_string d) }
  | '"'                         { STRING (string (Buffer.create 10) lexbuf) }

  (* types *)
  | 'i' (digit+ as i) { I (coq_of_int (int_of_string i)) }
  | '*' { STAR }

  (* keywords *)
  | kwletter+ as a { kw a }

and comment = parse
  | eol { Lexing.new_line lexbuf; EOL }
  | eof { EOF }
  | _ { comment lexbuf }

and string buf = parse
  | '"'    { Buffer.contents buf }
  | _ as c { Buffer.add_char buf c; string buf lexbuf }

and raw_id = parse
  | ident_fst ident_nxt* as i { Ollvm_ast.Name (str i) }
  | digit+ as i               { Ollvm_ast.Anon (coq_of_int (int_of_string i)) }
  | '"'                       { Ollvm_ast.Name (str ("\"" ^ string (Buffer.create 10) lexbuf ^ "\"")) }

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
    try Ollvm_parser.toplevel_entities token lexbuf
    with Ollvm_parser.Error -> parsing_err lexbuf

}
