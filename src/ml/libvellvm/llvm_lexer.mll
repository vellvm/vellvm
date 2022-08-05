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
  open Llvm_parser
  let str = Camlcoq.coqstring_of_camlstring
  let of_str = Camlcoq.camlstring_of_coqstring
  let coq_N_of_int = Camlcoq.N.of_int
  let coq_of_int = Camlcoq.Z.of_sint
  let coq_of_int64 = Camlcoq.Z.of_sint64
  let coqfloat_of_float f = Floats.Float.of_bits(Camlcoq.coqint_of_camlint64(Int64.bits_of_float f))

  exception Lex_error_unterminated_string of Lexing.position

  (* TODO: Replace this function with a hash table, which should be a lot more efficient. *)
  let kw = function
  | "target"                       -> KW_TARGET
  | "datalayout"                   -> KW_DATALAYOUT
  | "source_filename"              -> KW_SOURCE_FILENAME
  | "triple"                       -> KW_TRIPLE
  | "define"                       -> KW_DEFINE
  | "declare"                      -> KW_DECLARE

  (* Linkage *)
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

  (* DLL storage *)
  | "dllimport"                    -> KW_DLLIMPORT
  | "dllexport"                    -> KW_DLLEXPORT

  (* Visibility *)
  | "default"                      -> KW_DEFAULT
  | "hidden"                       -> KW_HIDDEN
  | "protected"                    -> KW_PROTECTED

  (* Calling Conventions cconv *)
  | "ccc"                          -> KW_CCC
  | "fastcc"                       -> KW_FASTCC
  | "coldcc"                       -> KW_COLDCC
  | "cc"                           -> KW_CC
  | "webkit_jscc"                  -> KW_WEBKIT_JSCC
  | "anyregcc"                     -> KW_ANYREGCC
  | "preserve_mostcc"              -> KW_PRESERVE_MOSTCC
  | "preserve_allcc"               -> KW_PRESERVE_ALLCC
  | "cxx_fast_tlscc"               -> KW_CXX_FAST_TLSCC
  | "tailcc"                       -> KW_TAILCC
  | "swiftcc"                      -> KW_SWIFTCC
  | "swifttailcc"                  -> KW_SWIFTTAILCC
  | "cfguard_checkcc"              -> KW_CFGUARD_CHECKCC


  | "unnamed_addr"                 -> KW_UNNAMED_ADDR
  | "local_unnamed_addr"           -> KW_LOCAL_UNNAMED_ADDR

  | "type"                         -> KW_TYPE
  | "opaque"                       -> KW_OPAQUE
  | "global"                       -> KW_GLOBAL
  | "addrspace"                    -> KW_ADDRSPACE
  | "externally_initialized"       -> KW_EXTERNALLY_INITIALIZED
  | "constant"                     -> KW_CONSTANT
  | "section"                      -> KW_SECTION
  | "comdat"                       -> KW_COMDAT
  | "partition"                    -> KW_PARTITION
  | "thread_local"                 -> KW_THREAD_LOCAL
  | "localdynamic"                 -> KW_LOCALDYNAMIC
  | "initialexec"                  -> KW_INITIALEXEC
  | "localexec"                    -> KW_LOCALEXEC

  (* Parameter Attributes param_attr *)
  | "zeroext"                      -> KW_ZEROEXT
  | "signext"                      -> KW_SIGNEXT
  | "inreg"                        -> KW_INREG
  | "byval"                        -> KW_BYVAL
  | "byref"                        -> KW_BYREF
  | "preallocated"                 -> KW_PREALLOCATED
  | "inalloca"                     -> KW_INALLOCA
  | "sret"                         -> KW_SRET
  | "elementtype"                  -> KW_ELEMENTTYPE
(* | "align"                        -> KW_ALIGN   (* align is used multiple ways *) *)
  | "noalias"                      -> KW_NOALIAS
  | "nocapture"                    -> KW_NOCAPTURE
  | "readonly"                     -> KW_READONLY
  | "nofree"                       -> KW_NOFREE
  | "nest"                         -> KW_NEST
  | "returned"                     -> KW_RETURNED
  | "nonnull"                      -> KW_NONNULL
  | "dereferenceable"              -> KW_DEREFERENCEABLE
  | "dereferenceable_or_null"      -> KW_DEREFERENCEABLE_OR_NULL
  | "swiftself"                    -> KW_SWIFTSELF
  | "swiftasync"                   -> KW_SWIFTASYNC
  | "swifterror"                   -> KW_SWIFTERROR
  | "immarg"                       -> KW_IMMARG
  | "noundef"                      -> KW_NOUNDEF
  | "alignstack"                   -> KW_ALIGNSTACK
  | "allocalign"                   -> KW_ALLOCALIGN
  | "allocptr"                     -> KW_ALLOCPTR

(* Function Attributes *)
  | "allockind"                    -> KW_ALLOCKIND
  | "allocsize"                    -> KW_ALLOCSIZE
  | "alwaysinline"                 -> KW_ALWAYSINLINE
  | "builtin"                      -> KW_BUILTIN
  | "cold"                         -> KW_COLD
  | "convergent"                   -> KW_CONVERGENT
  | "disable_sanitizer_instrumentation" -> KW_DISABLE_SANITIZER_INSTRUMENTATION
  | "fn_ret_thunk_extern"          -> KW_FN_RET_THUNK_EXTERN
  | "hot"                          -> KW_HOT
  | "inaccessiblememonly"          -> KW_INACCESSIBLEMEMONLY
  | "inaccessiblemem_or_argmemeonly" -> KW_INACCESSIBLEMEM_OR_ARGMEMONLY
  | "inlinehint"                   -> KW_INLINEHINT
  | "jumptable"                    -> KW_JUMPTABLE
  | "minsize"                      -> KW_MINSIZE
  | "naked"                        -> KW_NAKED
  | "no_jump_tables"               -> KW_NO_JUMP_TABLES
  | "nobuiltin"                    -> KW_NOBUILTIN
  | "noduplicate"                  -> KW_NODUPLICATE
  | "noimplicitfloat"              -> KW_NOIMPLICITFLOAT
  | "noinline"                     -> KW_NOINLINE
  | "nomerge"                      -> KW_NOMERGE
  | "nonlazybind"                  -> KW_NONLAZYBIND
  | "noredzone"                    -> KW_NOREDZONE
  | "indirect-tls-seg-refs"        -> KW_INDIRECT_TLS_SEG_REFS
  | "noreturn"                     -> KW_NORETURN
  | "norecurse"                    -> KW_NORECURSE
  | "willreturn"                   -> KW_WILLRETURN
  | "nosync"                       -> KW_NOSYNC
  | "nounwind"                     -> KW_NOUNWIND
  | "nosantitize_bounds"           -> KW_NOSANITIZE_BOUNDS
  | "nosantitize_coverage"         -> KW_NOSANITIZE_COVERAGE
  | "null_pointer_is_valid"        -> KW_NULL_POINTER_IS_VALID
  | "optforfuzzing"                -> KW_OPTFORFUZZING
  | "optnone"                      -> KW_OPTNONE
  | "optsize"                      -> KW_OPTSIZE
  | "readnone"                     -> KW_READNONE
  | "writeonly"                    -> KW_WRITEONLY
  | "argmemonly"                   -> KW_ARGMEMONLY
  | "returns_twice"                -> KW_RETURNS_TWICE
  | "safestack"                    -> KW_SAFESTACK
  | "sanitize_address"             -> KW_SANITIZE_ADDRESS
  | "no_sanitize"                  -> KW_NO_SANITIZE
  | "no_sanitize_address"          -> KW_NO_SANITIZE_ADDRESS
  | "no_sanitize_hwaddress"        -> KW_NO_SANITIZE_HWADDRESS
  | "sanitize_address_dyninit"     -> KW_SANITIZE_ADDRESS_DYNINIT
  | "sanitize_memory"              -> KW_SANITIZE_MEMORY
  | "sanitize_thread"              -> KW_SANITIZE_THREAD
  | "sanitize_hwaddress"           -> KW_SANITIZE_HWADDRESS
  | "sanitize_memtag"              -> KW_SANITIZE_MEMTAG
  | "speculative_load_hardening"   -> KW_SPECULATIVE_LOAD_HARDENING
  | "speculatable"                 -> KW_SPECULATABLE
  | "ssp"                          -> KW_SSP
  | "sspreq"                       -> KW_SSPREQ
  | "sspstrong"                    -> KW_SSPSTRONG
  | "strictfp"                     -> KW_STRICTFP
  | "uwtable"                      -> KW_UWTABLE
  | "sync"                         -> KW_SYNC
  | "async"                        -> KW_ASYNC
  | "nocf_check"                   -> KW_NOCF_CHECK
  | "shadowcallstack"              -> KW_SHADOWCALLSTACK
  | "mustprogress"                 -> KW_MUSTPROGRESS
  | "vscale_range"                 -> KW_VSCALE_RANGE

  | "align"                        -> KW_ALIGN

  | "prefix"                       -> KW_PREFIX
  | "prologue"                     -> KW_PROLOGUE
  | "personality"                  -> KW_PERSONALITY
  | "gc"                           -> KW_GC
  | "to"                           -> KW_TO
  | "unwind"                       -> KW_UNWIND
  | "tail"                         -> KW_TAIL
  | "musttail"                     -> KW_MUSTTAIL
  | "notail"                       -> KW_NOTAIL
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
  | "freeze"         -> KW_FREEZE
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

  | "dso_preemptable" -> KW_DSO_PREEMPTABLE
  | "dso_local"       -> KW_DSO_LOCAL

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
  | "contract"       -> KW_CONTRACT
  | "afn"            -> KW_AFN
  | "reassoc"        -> KW_REASSOC
  | "fast"           -> KW_FAST

  (* synchronization *)
  | "syncscope"      -> KW_SYNCSCOPE
  | "unordered"      -> KW_UNORDERED
  | "monotonic"      -> KW_MONOTONIC
  | "acquire"        -> KW_ACQUIRE
  | "release"        -> KW_RELEASE
  | "acq_rel"        -> KW_ACQ_REL
  | "seq_cst"        -> KW_SEQ_CST

  (*types*)
  | "iptr"      -> KW_IPTR
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


  let metadata = function
  | "nontemporal"             -> META_NONTEMPORAL
  | "invariant.load"          -> META_INVARIANT_LOAD
  | "invariant.group"         -> META_INVARIANT_GROUP
  | "nonnull"                 -> META_NONNULL
  | "dereferenceable"         -> META_DEREFERENCEABLE
  | "dereferenceable_or_null" -> META_DEREFERENCEABLE_OR_NULL
  | "align"                   -> META_ALIGN
  | "noundef"                 -> META_NOUNDEF
  | s                         -> METADATA_ID (Name (str s))
}

let ws = [' ' '\t']
let eol = ('\n' | '\r' | "\r\n" | "\n\r")
let digit = ['0'-'9']
let hexletter = ['A'-'F']|['a'-'f']
let hexdigit = digit | hexletter
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
  | "..." { DOTDOTDOT }

  (* labels *)
  | ((label_char)+) as l ':' { LABEL l }

  (* identifier *)
  | '@' { GLOBAL (lexed_id lexbuf) }
  | '%' { LOCAL  (lexed_id lexbuf) }

  (* FIXME: support metadata strings and struct. Parsed as identifier here. *)
  | "!{" { BANGLCURLY }
  | '!'  { let rid = lexed_id lexbuf in
           begin match rid with
           | ParseUtil.Named id ->
	   (if id.[0] = '"' && id.[String.length id - 1] = '"'
               then METADATA_STRING (String.sub id 1 (String.length id - 2))
               else metadata id)

	   | ParseUtil.Anonymous n -> METADATA_ID (Anon (coq_of_int n))
	   end
         }

  | '#' (digit+ as i) { ATTR_GRP_ID (coq_of_int (int_of_string i)) }

  (* constants *)
  | ('-'? digit+) as d            { INTEGER (coq_of_int64 (Int64.of_string d)) }
  | ('-'? digit* '.' digit+) as d { FLOAT d }
  | ('-'? digit ('.' digit+)? 'e' ('+'|'-') digit+) as d { FLOAT d }
  | ('0''x' hexdigit+) as d     { HEXCONSTANT (coqfloat_of_float (Int64.float_of_bits (Int64.of_string d))) }
  | '"'                         { STRING (string (Buffer.create 10) lexbuf) }

  (* types *)
  | 'i' (digit+ as i) { I (coq_N_of_int (int_of_string i)) }
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

and lexed_id = parse
  | ident_fst ident_nxt* as i { ParseUtil.Named i }
  | digit+ as i               { ParseUtil.Anonymous (int_of_string i) }
  | '"'                       { ParseUtil.Named ("\"" ^ string (Buffer.create 10) lexbuf ^ "\"") }

{

  let parsing_err lexbuf msg =
    let pos = Lexing.lexeme_start_p lexbuf in
    let msg =
        Printf.sprintf "Parsing error: line %d, column %d, token '%s': %s\n%s"
                       pos.Lexing.pos_lnum
                       (pos.Lexing.pos_cnum - pos.Lexing.pos_bol)
                       (Lexing.lexeme lexbuf)
		       msg
		       (Printexc.get_backtrace ())
      in failwith msg

  let parse lexbuf =
    try Llvm_parser.toplevel_entities token lexbuf
    with
    | Llvm_parser.Error -> parsing_err lexbuf "Error token encountered"
    | Failure s ->
      begin
        parsing_err lexbuf s
      end

  let parse_test_call lexbuf =
    try Llvm_parser.test_call token lexbuf
    with Llvm_parser.Error -> parsing_err lexbuf "Error token encountered"

  let parse_texp lexbuf =
    try Llvm_parser.texp token lexbuf
    with Llvm_parser.Error -> parsing_err lexbuf "Error token encountered"

}
