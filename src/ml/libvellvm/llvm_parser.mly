%{ (* {{{ LICENSE                                                              *
  * vi: set fdm=marker fdl=0:                                                *
  *                                                                          *
  * Copyright (c) 2012 Raphaël Proust <raphlalou@gmail.com>                  *
  * Copyright (c) 2012 INRIA - Raphaël Proust <raphlalou@gmail.com>          *
  * Copyright (c) 2012 ENS - Raphaël Proust <raphlalou@gmail.com>            *
  * Copyright (c) 2014 OCamlPro - Julien Sagot <ju.sagot@gmail.com>          *
  * Copyright (c) 2026 U. Penn. Steve Zdancewic <stevez@cis.upenn.edu>       *
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


open Lexing
open LLVMAst
open ParserHelper
open Parse_util

(* Compute a METADATA_File_info value from the current parser state. *)
let pos_of_lexpos (p : position) =
  (p.pos_lnum,  (p.pos_cnum - p.pos_bol))

let metadata_file_info (startpos:Lexing.position) (endpos:Lexing.position) =
  let filename = str startpos.pos_fname in
  let start_line = coq_of_int startpos.pos_lnum in
  let start_col = coq_of_int (startpos.pos_cnum - startpos.pos_bol) in
  let end_line = coq_of_int endpos.pos_lnum in
  let end_col = coq_of_int (endpos.pos_cnum - endpos.pos_bol) in
  METADATA_File_info {
      filename ;
      start_line ;
      start_col ;
      end_line ;
      end_col ;
      }
      

(* normalize_float_size :
   - LLVM floating point literals need different interpretations depending
     on their types.

   - This function converts a string into either a
     EXP_Double 64-bit literal, or
     EXP_Float 32-bit literal depending on the type annotation t
 *)
(*
SAZ: This should no longer be necessary, since it is handled in Rocq now.
TODO: Delete
let normalize_float_literal (t:typ) (d:string) =
  match t with
  | TYPE_Double -> EXP_Double (coqfloat_of_string d)
  | TYPE_Float  ->
       let v = coqfloat_of_string d in
         if can_convert_float_to_float32 v
           then EXP_Float (coqfloat32_of_string d)
         else
           let dbg = (match v with
                   | B754_finite (_, m, e) -> Printf.sprintf "\"%s\" [m=%s, e=%s]" d (string_of_positive m) (string_of_Z e)
                   | _ -> Printf.sprintf "\"%s\"" d)
           in
           failwith ("Illegal 32-bit floating point literal: " ^ dbg)
  | _ -> failwith "normalize_float_literal called with non-float type"
*)

let opt_list (m:'a option) : 'a list =
  match m with
  | None -> []
  | Some x -> [x]

let list_opt (m : 'a list) : 'a option =
  match m with
  | [] -> None
  | [x] -> Some x
  | _ -> failwith "Should Not Happen: too many list elements"

let opt_bool (m:'a option) : bool =
  match m with
  | None -> false
  | Some _ -> true

let ann_opt (m:'a option) (a:typ annotation) : typ annotation list =
  match m with
  | None -> []
  | Some _ -> [a]

let ann_linkage_opt (m : linkage option) : (typ annotation) option =
  match m with
  | None -> None
  | Some l -> Some (ANN_linkage l)

let mk_metadata (m : ('a metadata list option)) : 'a metadata list =
  match m with
  | None -> []
  | Some ms -> ms

%}

%token<Parse_util.lexed_id> GLOBAL LOCAL
%token LPAREN RPAREN LCURLY RCURLY LTLCURLY RCURLYGT LSQUARE RSQUARE LT GT EQ COMMA EOF STAR COLON DOTDOTDOT

%token<string> COMMENT
%token<string> COMMENT_EOF (* Special case of comment that ends in eof and not a line break. *)
%token<string> STRING
%token<LLVMAst.int_syntax> INTEGER
%token<LLVMAst.float_syntax> FLOAT
%token KW_NULL
%token KW_UNDEF
%token KW_POISON
%token KW_TRUE
%token KW_FALSE
%token KW_ZEROINITIALIZER
%token KW_C

%token<string> LABEL

%token KW_DEFINE
%token KW_DECLARE
%token KW_TARGET
%token KW_DATALAYOUT
%token KW_TRIPLE
%token KW_SOURCE_FILENAME
%token KW_ALIAS

(* Linkage *)
%token KW_PRIVATE
%token KW_INTERNAL
%token KW_AVAILABLE_EXTERNALLY
%token KW_LINKONCE
%token KW_WEAK
%token KW_COMMON
%token KW_APPENDING
%token KW_EXTERN_WEAK
%token KW_LINKONCE_ODR
%token KW_WEAK_ODR
%token KW_EXTERNAL

(* Visibility *)
%token KW_DEFAULT
%token KW_HIDDEN
%token KW_PROTECTED
(* dll storage *)
%token KW_DLLIMPORT
%token KW_DLLEXPORT

(* Calling Conventions: cconv *)
%token KW_CCC
%token KW_FASTCC
%token KW_COLDCC
%token KW_CC
%token KW_WEBKIT_JSCC
%token KW_ANYREGCC
%token KW_PRESERVE_MOSTCC
%token KW_PRESERVE_ALLCC
%token KW_CXX_FAST_TLSCC
%token KW_TAILCC
%token KW_SWIFTCC
%token KW_SWIFTTAILCC
%token KW_CFGUARD_CHECKCC

%token KW_UNNAMED_ADDR
%token KW_LOCAL_UNNAMED_ADDR

%token KW_TYPE
%token KW_X
%token KW_OPAQUE
%token KW_GLOBAL
%token KW_ADDRSPACE
%token KW_CONSTANT
%token KW_SECTION
%token KW_COMDAT
%token KW_PARTITION
%token KW_THREAD_LOCAL
%token KW_LOCALDYNAMIC
%token KW_INITIALEXEC
%token KW_LOCALEXEC
%token KW_EXTERNALLY_INITIALIZED

(* Parameter Attributes param_attr *)
%token KW_ZEROEXT
%token KW_SIGNEXT
%token KW_INREG
%token KW_BYVAL
%token KW_BYREF
%token KW_PREALLOCATED
%token KW_INALLOCA
%token KW_SRET
%token KW_ELEMENTTYPE
%token KW_ALIGN
%token KW_NOALIAS
%token KW_NOCAPTURE
%token KW_READONLY
%token KW_NOFREE
%token KW_NEST
%token KW_RETURNED
%token KW_NONNULL
%token KW_DEREFERENCEABLE
%token KW_DEREFERENCEABLE_OR_NULL
%token KW_SWIFTSELF
%token KW_SWIFTASYNC
%token KW_SWIFTERROR
%token KW_IMMARG
%token KW_NOUNDEF
%token KW_ALIGNSTACK
%token KW_ALLOCALIGN
%token KW_ALLOCPTR

(* Function Attributes *)
(* %token KW_ALIGNSTACK *)
(* %token KW_ALLOC_FAMILY  (* quoted "alloc-family" *) *)
%token KW_ALLOCKIND
%token KW_ALLOCSIZE
%token KW_ALWAYSINLINE
%token KW_BUILTIN
%token KW_COLD
%token KW_CONVERGENT
%token KW_DISABLE_SANITIZER_INSTRUMENTATION
(* %token KW_DONTCALL_ERROR *)
(* %token KW_DONTCALL_WARN *)
%token KW_FN_RET_THUNK_EXTERN
%token KW_HOT
%token KW_INACCESSIBLEMEMONLY
%token KW_INACCESSIBLEMEM_OR_ARGMEMONLY
%token KW_INLINEHINT
%token KW_JUMPTABLE
%token KW_MINSIZE
%token KW_NAKED
(* %token KW_NO_INLINE_LINE_TABLES  (* quoted "no-inline-line-tables" *) *)
%token KW_NO_JUMP_TABLES
%token KW_NOBUILTIN
%token KW_NODUPLICATE
(* KW_NOFREE - used in multiple ways *)
%token KW_NOIMPLICITFLOAT
%token KW_NOINLINE
%token KW_NOMERGE
%token KW_NONLAZYBIND
%token KW_NOREDZONE
%token KW_INDIRECT_TLS_SEG_REFS
%token KW_NORETURN
%token KW_NORECURSE
%token KW_WILLRETURN
%token KW_NOSYNC
%token KW_NOUNWIND
%token KW_NOSANITIZE_BOUNDS
%token KW_NOSANITIZE_COVERAGE
%token KW_NULL_POINTER_IS_VALID
%token KW_OPTFORFUZZING
%token KW_OPTNONE
%token KW_OPTSIZE
(* %token KW_PATCHABLE_FUNCTION quoted "patchable-function" *)
(* %token KW_PROBE_STACK quoted "probe-stack"  *)
%token KW_READNONE
(* %token KW_READONLY *)
(* %token KW_STACK_PROBE_SIZE (* quoted "stack-probe-size" *) *)
(* %token KW_NO_STACK_ARG_PROBE (* quoted "no-stack-arg-probe " *) *)
%token KW_WRITEONLY
%token KW_WRITABLE
%token KW_DEADONUNWIND
%token KW_ARGMEMONLY
%token KW_RETURNS_TWICE
%token KW_SAFESTACK
%token KW_NO_SANITIZE
%token KW_SANITIZE_ADDRESS
%token KW_SANITIZE_ADDRESS_DYNINIT
%token KW_NO_SANITIZE_ADDRESS
%token KW_NO_SANITIZE_HWADDRESS
%token KW_SANITIZE_MEMORY
%token KW_SANITIZE_THREAD
%token KW_SANITIZE_HWADDRESS
%token KW_SANITIZE_MEMTAG
%token KW_SPECULATIVE_LOAD_HARDENING
%token KW_SPECULATABLE
%token KW_SSP
%token KW_SSPSTRONG
%token KW_SSPREQ
%token KW_STRICTFP
(* %token KW_DENORMAL_FP_MATH (* quoted "denormal-fp-math" *) *)
(* %token KW_DENORMAL_FP_MATH_F32 (* quoted "denormal-fp-math-f32" *) *)
(* %token KW_THUNK (* quoted "thunk" *) *)
(* %token KW_TLS_LOAD_HOIST (* quoted "tls-load-hoist" *) *)
%token KW_UWTABLE
%token KW_SYNC  (* goes with uwtable *)
%token KW_ASYNC (* goes with uwtable *)
%token KW_NOCF_CHECK
%token KW_SHADOWCALLSTACK
%token KW_MUSTPROGRESS
(* %token KW_WARN_STACK_SIZE (* quoted "warn-stack-size" *) *)
%token KW_VSCALE_RANGE
(* %token KW_MIN_LEGAL_VECTOR_WIDTH (* quoted "min-legal-vector-width" *) *)
%token KW_MEMORY
%token KW_READ
%token KW_WRITE
%token KW_NONE
%token KW_READWRITE
%token KW_ARGMEM
%token KW_INACCESSIBLEMEM
%token KW_ERRNOMEM
(* keywords that can be followed by `:` with no space:
   memory(default: foo)
   memory(default : foo)
   memory(default :foo)
*)
%token KW_DEFAULT_COLON
%token KW_ARGMEM_COLON
%token KW_INACCESSIBLEMEM_COLON
%token KW_ERRNOMEM_COLON

%token KW_DSO_PREEMPTABLE
%token KW_DSO_LOCAL

%token KW_GC

%token KW_PREFIX
%token KW_PROLOGUE
%token KW_PERSONALITY

%token KW_ADD
%token KW_FADD
%token KW_SUB
%token KW_FSUB
%token KW_MUL
%token KW_FMUL
%token KW_UDIV
%token KW_SDIV
%token KW_FDIV
%token KW_FNEG
%token KW_UREM
%token KW_SREM
%token KW_FREM
%token KW_SHL
%token KW_LSHR
%token KW_ASHR
%token KW_AND
%token KW_OR
%token KW_DISJOINT
%token KW_XOR
%token KW_ICMP
%token KW_FCMP
%token KW_PHI
%token KW_CALL
%token KW_TRUNC
%token KW_ZEXT
%token KW_SEXT
%token KW_FPTRUNC
%token KW_FPEXT
%token KW_UITOFP
%token KW_SITOFP
%token KW_FPTOUI
%token KW_FPTOSI
%token KW_INTTOPTR
%token KW_PTRTOINT
%token KW_PTRTOADDR
%token KW_ADDRSPACECAST
%token KW_BITCAST
%token KW_SELECT
%token KW_FREEZE
%token KW_VAARG
%token KW_RET
%token KW_BR
%token KW_SWITCH
%token KW_INDIRECTBR
%token KW_INVOKE
%token KW_RESUME
%token KW_UNREACHABLE
%token KW_ALLOCA
%token KW_LOAD
%token KW_STORE
%token KW_ATOMICCMPXCHG
%token KW_ATOMICRMW
%token KW_FENCE
%token KW_GETELEMENTPTR
%token KW_INBOUNDS
%token KW_EXTRACTELEMENT
%token KW_INSERTELEMENT
%token KW_SHUFFLEVECTOR
%token KW_EXTRACTVALUE
%token KW_INSERTVALUE
%token KW_LANDINGPAD
%token KW_CATCH
%token KW_FILTER
%token KW_CLEANUP

%token KW_NNAN
%token KW_NINF
%token KW_NSZ
%token KW_ARCP
%token KW_CONTRACT
%token KW_AFN
%token KW_REASSOC
%token KW_FAST
%token<Camlcoq.P.t> I
%token KW_IPTR
%token KW_PTR
%token KW_VOID
%token KW_HALF
%token KW_FLOAT
%token KW_DOUBLE
%token KW_X86_FP80
%token KW_FP128
%token KW_PPC_FP128
%token KW_LABEL
%token KW_METADATA
%token KW_DISTINCT
%token KW_X86_MMX

%token KW_UNWIND
%token KW_TO
%token KW_NUW
%token KW_NUSW
%token KW_NSW
%token KW_EXACT
%token KW_NNEG
%token KW_EQ
%token KW_NE
%token KW_SGT
%token KW_SGE
%token KW_SLT
%token KW_SLE
%token KW_UGT
%token KW_UGE
%token KW_ULT
%token KW_ULE
%token KW_OEQ
%token KW_OGT
%token KW_OGE
%token KW_OLT
%token KW_OLE
%token KW_ONE
%token KW_ORD
%token KW_UNO
%token KW_UEQ
%token KW_UNE
%token KW_TAIL
%token KW_MUSTTAIL
%token KW_NOTAIL
%token KW_VOLATILE

%token KW_MAX
%token KW_MIN
%token KW_XCHG
%token KW_FMAX
%token KW_FMIN
%token KW_UMIN
%token KW_UMAX
%token KW_NAND
%token KW_FMAXIMUM 
%token KW_FMINIMUM 
%token KW_UINC_WRAP 
%token KW_UDEC_WRAP 
%token KW_USUB_COND 
%token KW_USUB_SAT  

%token KW_ATOMIC
%token KW_SYNCSCOPE
%token KW_UNORDERED
%token KW_MONOTONIC
%token KW_ACQUIRE
%token KW_RELEASE
%token KW_ACQ_REL
%token KW_SEQ_CST

%token KW_RANGE
%token KW_INITIALIZES
%token KW_SPLAT
%token KW_SAMESIGN

%token<string> KW_UNKNOWN

(* METADATA constants *)

(* for load instructions *)

%token<(string * string)> METADATA_DEBUG

%token BANG

(* ASM *)
%token KW_ASM
%token KW_SIDEEFFECT
%token KW_INTELDIALECT

%token KW_ATTRIBUTES
%token<Camlcoq.Z.t> ATTR_GRP_ID

%start<(LLVMAst.typ, (LLVMAst.typ LLVMAst.block) * ((LLVMAst.typ LLVMAst.block) list)) LLVMAst.toplevel_entities> toplevel_entities
%start<LLVMAst.typ LLVMAst.instr> test_call
%start<(LLVMAst.typ * LLVMAst.typ LLVMAst.exp)> texp
%start<LLVMAst.typ LLVMAst.metadata> metadata_id

%%

toplevel_entities:
  | m=toplevel_entity* EOF { m }
  | m=toplevel_entity* c = COMMENT_EOF { m @ [TLE_Comment (str c) ] }

toplevel_entity:
  | d=definition                        { TLE_Definition d               }
  | d=declaration                       { TLE_Declaration d              }
  | KW_TARGET KW_DATALAYOUT EQ s=STRING { TLE_Datalayout (str s)         }
  | KW_TARGET KW_TRIPLE EQ s=STRING     { TLE_Target (str s)             }
  | KW_SOURCE_FILENAME EQ s=STRING      { TLE_Source_filename (str s)    }

  (* SAZ: It's not clear what the rules for named identifiers are.  It
     seems that they don't follow the "anonymous" rules of sequentiality
     and they also seem to live in another name space.
   *)
  | i=lident EQ KW_TYPE t=typ           { TLE_Type_decl (ID_Local i, t)  }
  | g=global_decl                       { TLE_Global g                   }
  | BANG i=metadata_id EQ d=KW_DISTINCT? m=tle_metadata
                                        { TLE_Metadata (i, opt_bool d, m)}
  | KW_ATTRIBUTES i=ATTR_GRP_ID EQ LCURLY a=fn_attr* RCURLY
    { TLE_Attribute_group (i, a)     }
  | c=COMMENT { TLE_Comment (str c) }

(* metadata are not implemented yet, but are at least (partially) parsed *)
tle_metadata:
  | BANG LCURLY m=separated_list(csep, tconst_or_metadata_value) RCURLY
    { METADATA_Node m }
  | md=METADATA_DEBUG { METADATA_Debug(str (fst md), str (snd md)) }
  | KW_METADATA m=metadata_node
    { m }


(* integer literal syntax *)


metadata_id:
  | KW_NOALIAS                   { METADATA_Id (Name (str "noalias")) }
  | KW_NONNULL                   { METADATA_Id (Name (str "nonnull")) }
  | KW_NOUNDEF                   { METADATA_Id (Name (str "noundef")) }
  | KW_ALIGN                     { METADATA_Id (Name (str "align")) }
  | KW_RANGE                     { METADATA_Id (Name (str "range")) }
  | s=STRING                     { METADATA_Id (Name (str ("\"" ^ s ^ "\""))) } (* preserve quotes *)
  | mid=INTEGER                  { METADATA_Id (Anon (BinIntDef.Z.of_num_int mid)) }
  | mid=KW_UNKNOWN               { METADATA_Id (Name (str mid)) }


metadata_node:
  | LCURLY m=separated_list(csep, tconst_or_metadata_value) RCURLY
    { METADATA_Node m }

tconst_or_metadata_value:
  | KW_NULL                     { METADATA_Null }
  | tconst                      { METADATA_Const $1  } 
  | m=metadata_value            { m } 

metadata_value:
  | BANG mid=metadata_id        { mid }
  | BANG mn=metadata_node       { mn  }
  | db=METADATA_DEBUG           { METADATA_Debug(str (fst db), str (snd db)) }

(* For externally defined global variables *)
%inline
external_linkage:
  | KW_EXTERN_WEAK                  { LINKAGE_Extern_weak                  }
  | KW_EXTERNAL                     { LINKAGE_External                     }

(* For internally defined global variabls *)
%inline
nonexternal_linkage:
  | KW_PRIVATE                      { LINKAGE_Private                      }
  | KW_INTERNAL                     { LINKAGE_Internal                     }
  | KW_AVAILABLE_EXTERNALLY         { LINKAGE_Available_externally         }
  | KW_LINKONCE                     { LINKAGE_Linkonce                     }
  | KW_WEAK                         { LINKAGE_Weak                         }
  | KW_COMMON                       { LINKAGE_Common                       }
  | KW_APPENDING                    { LINKAGE_Appending                    }
  | KW_LINKONCE_ODR                 { LINKAGE_Linkonce_odr                 }
  | KW_WEAK_ODR                     { LINKAGE_Weak_odr                     }

(* For function declarations and definitions *)
%inline
linkage:
  | KW_PRIVATE                      { LINKAGE_Private                      }
  | KW_INTERNAL                     { LINKAGE_Internal                     }
  | KW_AVAILABLE_EXTERNALLY         { LINKAGE_Available_externally         }
  | KW_LINKONCE                     { LINKAGE_Linkonce                     }
  | KW_WEAK                         { LINKAGE_Weak                         }
  | KW_COMMON                       { LINKAGE_Common                       }
  | KW_APPENDING                    { LINKAGE_Appending                    }
  | KW_EXTERN_WEAK                  { LINKAGE_Extern_weak                  }
  | KW_LINKONCE_ODR                 { LINKAGE_Linkonce_odr                 }
  | KW_WEAK_ODR                     { LINKAGE_Weak_odr                     }
  | KW_EXTERNAL                     { LINKAGE_External                     }

%inline
preemption_specifier:
  | KW_DSO_PREEMPTABLE { ANN_preemption_specifier PREEMPTION_Dso_preemptable }
  | KW_DSO_LOCAL { ANN_preemption_specifier PREEMPTION_Dso_local }


%inline
visibility:
  | KW_DEFAULT   { ANN_visibility VISIBILITY_Default   }
  | KW_HIDDEN    { ANN_visibility VISIBILITY_Hidden    }
  | KW_PROTECTED { ANN_visibility VISIBILITY_Protected }

%inline
dll_storage_class:
  | KW_DLLIMPORT { ANN_dll_storage DLLSTORAGE_Dllimport }
  | KW_DLLEXPORT { ANN_dll_storage DLLSTORAGE_Dllexport }

%inline
thread_local_storage:
  | KW_THREAD_LOCAL { ANN_thread_local_storage TLS_NONE }
  | KW_THREAD_LOCAL LPAREN t=tls RPAREN  { ANN_thread_local_storage t }

%inline
tls:
  | KW_LOCALDYNAMIC { TLS_Localdynamic }
  | KW_INITIALEXEC  { TLS_Initialexec  }
  | KW_LOCALEXEC    { TLS_Localexec    }

%inline
unnamed_addr:
  | KW_UNNAMED_ADDR       { ANN_unnamed_addr Unnamed_addr }
  | KW_LOCAL_UNNAMED_ADDR { ANN_unnamed_addr Local_Unnamed_addr }

%inline
addrspace:
  | KW_ADDRSPACE LPAREN n=INTEGER RPAREN { ANN_addrspace n }

global_pre_annotations:
|   p=preemption_specifier?
    v=visibility?
    d=dll_storage_class?
    t=thread_local_storage?
    u=unnamed_addr?
    a=addrspace?
    { (opt_list p)
      @ (opt_list v)
      @ (opt_list d)
      @ (opt_list t)
      @ (opt_list u)
      @ (opt_list a) }

(* For some reason, LLVM IR expects there to be a COMMA before the
   annotations for global expressions, but _not_ for declarations or
   definitions.
*)

c_section:
  | csep KW_SECTION s=STRING l=c_partition { (ANN_section (str s)) :: l }
  |  l=c_partition { l }

c_partition:
  | csep KW_PARTITION s=STRING l=c_comdat { (ANN_partition (str s)) :: l }
  | l=c_comdat { l }

c_comdat:
  | csep KW_COMDAT LPAREN lid=lident RPAREN l=c_align { (ANN_comdat lid) :: l }
  | l=c_align { l }

c_align:
  | csep KW_ALIGN n=INTEGER l=c_no_sanitize { (ANN_align n) :: l }
  | l=c_no_sanitize { l }

c_no_sanitize:
  | csep KW_NO_SANITIZE l=c_no_sanitize_address { ANN_no_sanitize :: l }
  | l=c_no_sanitize_address { l }

c_no_sanitize_address:
  | csep KW_NO_SANITIZE_ADDRESS l=c_no_sanitize_hwaddress { ANN_no_sanitize_address :: l }
  | l=c_no_sanitize_hwaddress { l }

c_no_sanitize_hwaddress:
  | csep KW_NO_SANITIZE_HWADDRESS l=c_sanitize_address_dyninit { ANN_no_sanitize_hwaddress :: l }
  | l=c_sanitize_address_dyninit { l }

c_sanitize_address_dyninit:
  | csep KW_SANITIZE_ADDRESS_DYNINIT l=c_global_metadata { ANN_sanitize_address_dyninit :: l }
  | l=c_global_metadata { l }

c_global_metadata:
 |  csep BANG m1=metadata_id m2=metadata_value l=c_global_metadata { (ANN_metadata [m1; m2]) :: l }
 | (* empty *) { [] }

global_post_annotations:
    | l=c_section { l }

%inline
externally_initialized:
  | KW_EXTERNALLY_INITIALIZED { true }
  | (* empty *) { false }

%inline
global_is_constant:
  | KW_GLOBAL { false }
  | KW_CONSTANT { true }


global_decl:
(* Internal declarations - may have initializers *)
  |  g_ident = gident EQ
     l = nonexternal_linkage?
     g_pre = global_pre_annotations
     g_externally_initialized = externally_initialized
     g_constant = global_is_constant
     g_typ=typ
     gv = exp
     g_post = global_post_annotations
    { { g_ident ;
        g_typ ;
        g_constant ;
        g_exp = Some (gv g_typ) ;
        g_externally_initialized ;
	g_alias = false; 
        g_annotations = ((opt_list (ann_linkage_opt l)) @ g_pre @ g_post)
      }
    }

(* External declarations - cannot have initializers *)
  |  g_ident = gident EQ
     l = external_linkage
     g_pre = global_pre_annotations
     g_externally_initialized = externally_initialized
     g_constant = global_is_constant
     g_typ=typ
     g_post = global_post_annotations
    { { g_ident ;
	g_typ ;
	g_constant ;
	g_exp = None ; (* No initializer *)
	g_externally_initialized ;
	g_alias = false;
	g_annotations = ([ANN_linkage l] @ g_pre @ g_post)
      }
    }

(* Aliases - resolve to an existing global.*)
  |  g_ident = gident EQ
     l = nonexternal_linkage?
     g_pre = global_pre_annotations
     KW_ALIAS
     g_typ=typ
     COMMA
     typ
     gv = gident
     g_post = global_post_annotations
    { { g_ident ;
	g_typ ;
	g_constant = false ;
	g_exp = Some (EXP_Ident (ID_Global gv)) ; (* Initializer _is_ the aliased global value *)
	g_externally_initialized = false;
	g_alias = true;
	g_annotations = ((opt_list (ann_linkage_opt l)) @ g_pre @ g_post)
      }
    }


%inline
section:
  | KW_SECTION s=STRING { ANN_section (str s) }

%inline
partition:
  | KW_PARTITION s=STRING { ANN_partition (str s) }

%inline
comdat:
  | KW_COMDAT LPAREN l=lident RPAREN { ANN_comdat l }

%inline
align_ann:
  | KW_ALIGN n=INTEGER { ANN_align n }


global_metadata:
 |  BANG m1=metadata_id m2=metadata_value l=c_global_metadata { (ANN_metadata [m1; m2]) :: l }
 | (* empty *) { [] }

%inline
cconv:
  | KW_CCC                {ANN_cconv CC_Ccc}
  | KW_FASTCC             {ANN_cconv CC_Fastcc}
  | KW_COLDCC             {ANN_cconv CC_Coldcc}
  | KW_WEBKIT_JSCC        {ANN_cconv CC_Webkit_jscc}
  | KW_ANYREGCC		  {ANN_cconv CC_Anyregcc}
  | KW_PRESERVE_MOSTCC	  {ANN_cconv CC_Preserve_mostcc}
  | KW_PRESERVE_ALLCC	  {ANN_cconv CC_Preserve_allcc}
  | KW_CXX_FAST_TLSCC	  {ANN_cconv CC_Cxx_fast_tlscc}
  | KW_TAILCC		  {ANN_cconv CC_Tailcc}
  | KW_SWIFTCC		  {ANN_cconv CC_Swiftcc}
  | KW_SWIFTTAILCC	  {ANN_cconv CC_Swifttailcc}
  | KW_CFGUARD_CHECKCC	  {ANN_cconv CC_cfguard_checkcc}
  | KW_CC n=INTEGER       {ANN_cconv (CC_Cc n)}

%inline
prefix:
  | KW_PREFIX t = texp { ANN_prefix t }

%inline
prologue:
  | KW_PROLOGUE t = texp { ANN_prologue t }

%inline
personality:
  | KW_PERSONALITY t = texp { ANN_personality t }

%inline
gc:
  | KW_GC s = STRING { ANN_gc (str s) }


dc_arg:
  | t=typ p=param_attr*         { (t, p) }
  | t=typ p=param_attr* lident  { (t, p) }  (* Throw away declaration names? *)

dc_args:
  | (* empty *)  { ([], false) }
  | DOTDOTDOT    { ([], true) }
  | arg=dc_arg   { ([arg], false) }
  | arg=dc_arg csep r=dc_args  { (arg::(fst r), snd r) }

%inline
declaration:
  | KW_DECLARE
    l = linkage?
    p = preemption_specifier?
    v = visibility?
    d = dll_storage_class?
    c = cconv?
    df_ret_attrs=param_attr*
    df_ret_typ=ret_typ
    name=GLOBAL

    midrule( { void_ctr.reset () } )   (* reset the void counter to 0 *)

    LPAREN args = dc_args RPAREN 

    u = unnamed_addr?
    dc_attrs = fn_attr*
    a = align_ann?
    g = gc?
    pre = prefix?
    pro = prologue?

    { let (dc_args, vararg) = args in
      {
	 dc_name        = lexed_id_to_raw_id name ;
	 dc_type        = TYPE_Function(df_ret_typ, List.map fst dc_args, vararg);
         dc_param_attrs = (df_ret_attrs, List.map snd dc_args);
	 dc_attrs;
	 dc_annotations =
	   ( (opt_list (ann_linkage_opt l))
	     @ (opt_list p)
	     @ (opt_list v)
	     @ (opt_list d)
	     @ (opt_list c)
	     @ (opt_list u)
	     @ (opt_list a)
	     @ (opt_list g)
	     @ (opt_list pre)
	     @ (opt_list pro)
	   )
      }
    }

df_args:
  | (* empty *)  { ([], false) }
  | DOTDOTDOT    { ([], true) }
  | arg=df_arg   { ([arg], false) }
  | arg=df_arg csep r=df_args  { (arg::(fst r), snd r) }


df_arg:
 | t=typ p=param_attr*                { ((t, p), None)   }  (* Later generate anonymous label *)
 | t=typ p=param_attr* l=bound_lident { ((t, p), Some l) }  (* Later validate anonymous or use name *)

%inline
definition:
  | KW_DEFINE
    (* begin LLParser::parseFunctionHeader from https://github.com/llvm/llvm-project/blob/main/llvm/lib/AsmParser/LLParser.cpp *)
    l = linkage?
    p = preemption_specifier?
    v = visibility?
    d = dll_storage_class?
    c = cconv?
    df_ret_attrs  = param_attr*
    df_ret_typ    = ret_typ
    name          = GLOBAL

    midrule( { void_ctr.reset () } )   (* reset the void counter to 0 *)

    LPAREN df_args = df_args RPAREN

    u = unnamed_addr?
    ad = addrspace?
    dc_attrs = fn_attr*

    sec = section?
    part = partition?
    com = comdat?
    al = align_ann?
    g = gc?
    pre = prefix?
    pro = prologue?
    per = personality?
    (* end LLParser::parseFunctionHeader *)

    (* begin LLParser::parseOptionalFunctionMetadata *)
    meta = global_metadata
    (* end LLParser::parseOptionalFunctionMetadata *)

    (* begin LLParser::parseFunctionBody *)
    LCURLY 
    blks=df_blocks
    RCURLY
    { let (args, vararg) = df_args in
      (* prepare to validate / generate the sequential identifiers *)
      let _ = anon_ctr.reset ()
      in

      (* process the arg identifiers *)
      let df_args =
	List.map (fun (_, aopt) -> check_or_generate_id aopt) args
      in

      let process_lhs_phi ((lopt, x), md) = ((check_or_generate_id lopt, x), md)
      in

      let process_lhs_instr ((lopt, i), md) =
	if AstLib.is_void_instr i then
	  match lopt with
	  | None   -> ((generate_void_instr_id (), i), md)
	  | Some _ -> failwith "void function has defined left-hand-side"
	else
	  ((IId (check_or_generate_id lopt), i), md)
      in

      let process_lhs_term ((lopt, t), md) =
	match lopt with
	| None -> ((generate_void_instr_id (), t), md)
	| Some r -> ((IId (validate_bound_lexed_id r), t), md)
      in
      
      let process_block (lopt, (phis, instrs, term)) =
	  let blk_id   = check_or_generate_label lopt in
	  let blk_phis = List.map process_lhs_phi phis in
	  let blk_code = List.map process_lhs_instr instrs in
	  let blk_term = process_lhs_term term in
	  { blk_id; blk_phis; blk_code; blk_term; blk_comments = None }
      in

      let blocks = List.map process_block blks
      in
      let df_instrs =
	match blocks with
	| [] -> failwith "illegal LLVM function definition: must have non-empty entry block"
	| entry::body -> (entry, body)
      in
      { df_prototype = {
	  dc_name        = lexed_id_to_raw_id name;
          dc_type = TYPE_Function (df_ret_typ,
                                   List.map (fun x -> fst (fst x)) args, vararg) ;
          dc_param_attrs = (df_ret_attrs,
                            List.map (fun x -> snd (fst x)) args) ;
	  dc_attrs;
	  dc_annotations =
	    ( (opt_list (ann_linkage_opt l))
	      @ (opt_list p)
	      @ (opt_list v)
	      @ (opt_list d)
	      @ (opt_list c)
	      @ (opt_list u)
	      @ (opt_list ad)
	      @ (opt_list sec)
	      @ (opt_list part)
	      @ (opt_list com)
	      @ (opt_list al)
	      @ (opt_list g)
	      @ (opt_list pre)
	      @ (opt_list pro)
	      @ (opt_list per)
	      @ meta
	    )
	} ;
        df_args;
        df_instrs;
      }
    }


(* Dealing with anonymous identifiers

   Each function definition in LLVM IR can have so-called "anonymous" local identifiers
   some of which can be omitted from the concrete syntax of the program.

   These identifiers are either
       - temporaries (a.k.a. registers) of the name %NNN, found as function arguments or
         on the left-hand-sides of instruction definitions, or
       - block labels (without the '%') that are numbered

   All "anonymous" identifiers, whether omitted or not, must be bound consecutively (in
   program order).  This means that a parser for an LLVM IR function
   Block labels, function arguments, and local temporaries all share the same counter.

   So-called "void" instructions, that _don't_ have a binding occurrence (i.e. to the left of an =)
   but we still generate a unique identifier for them for use in the semantics.
*)

(* Correctly parsing a CFG definition while generating / checking anonymous
   instruction identifiers is annoying because what to do for a `call`
   instruction depends on the type of the call.  If the function's return type
   is "void" then no identifier is bound (and it is a syntax error to try to
   bind an identifier).  If the function's return-type is non-void, then
   an anonymous identifier might need to be generated / checked.

   Also, since some anonymous identifiers can be omitted, we have to process
   the whole function body and then post-process to either check of generate
   the appropriate anonymous ids.
*)


(* An instruction lhs might have a declared identifier, which can be either
"anonymous" (i.e. of the form %N where N is a number is sequence order or %x,
where x is a string.  At this stage, an omitted lhs is parsed as None.  We
post-process such omitted lhs later to generate the sequence number.  An
"anonymous" (a.k.a.  sequential, possibly implicit identifier) might not be
omitted, in which case we have to check that it is indeed the correct number.
The post-processing takes place after the whole cfg has been parsed as part of
the declatation parser production.

SAZ: I would prefer the terminology "sequential, possibly implicit identifiers"
to "anonymous".
*)

%inline
instr_lhs:
  | /* empty */
    { None   }

  | l=bound_lident EQ
    { Some l }

(* A block label behaves like the lhs of an instruction (except, strangely, it
  isn't written with a leading % except when used as a label value in a
  terminator).  Block labels can be omitted, just like a lhs, and they are
  post-processed in the same pass since they use the same sequence counter.
*)
%inline
block_label:
  | /* empty */
    { None }

  | lbl=LABEL 
    { Some lbl }

  | KW_DEFAULT_COLON
    { Some "default" }

  | KW_ARGMEM_COLON
    { Some "argmem" }

  | KW_INACCESSIBLEMEM_COLON
    { Some "inaccessiblemem" }

  | KW_ERRNOMEM_COLON
    { Some "errnomem" }

  | str=STRING COLON
    { Some ("\"" ^ str ^ "\"")}

block_phis_and_instrs_and_term:
  | id=bound_lident EQ pm=phi
    bl=block_phis_and_instrs_and_term
    {
      let (p, md) = pm in 
      let (phis, instrs, t) = bl in
      (((Some id, p), md)::phis, instrs, t) }

  | id_opt=instr_lhs im=instr 
    ins=block_instrs_and_term
    { let (inst, md) = im in 
      let (instrs, t) = ins in 
      ([], ((id_opt, inst), md)::instrs, t) }

  | id_opt=instr_lhs tm=terminator
    { let (t,md) = tm in 
      ([], [], ((id_opt, t), md)) }
      
block_instrs_and_term:
  | id_opt=instr_lhs tm=terminator
    { let (t,md) = tm in
      ([], ((id_opt, t), md)) }

  | id_opt=instr_lhs im=instr
    ins=block_instrs_and_term
    { let (inst, md) = im in
      let (instrs, t) = ins in
      (((id_opt, inst), md)::instrs, t) }


phi:
  | KW_PHI t=typ ps=phi_suffix
    { let (table, md) = ps in
      let f_info = metadata_file_info $startpos $endpos in
      (Phi (t, List.map (fun (l,v) -> (l, v t)) table), f_info::md) }

phi_suffix:
  | te=phi_table_entry COMMA ps=phi_suffix
    { let (tes, md) = ps in
      (te::tes, md) }
  | te=phi_table_entry md=instr_metadata
    { ([te], md) }

%inline
phi_table_entry:
  | LSQUARE v=exp COMMA l=lident RSQUARE { (l, v) }

block:
  blk_id   = block_label
  body     = block_phis_and_instrs_and_term
    {
	(blk_id, body)
    }

metadata_pair:
  m1=metadata_value m2=metadata_value
    { METADATA_Pair(m1, m2) }

instr_metadata:
  | COMMA mp=metadata_pair md=instr_metadata
    { mp::md }
  | 
    { [] }

df_blocks:
  | blks=block+
    { blks }

typ_args:
  | (* empty *)  { ([], false) }
  | DOTDOTDOT    { ([], true) }
  | arg=typ   { ([arg], false) }
  | arg=typ csep r=typ_args  { (arg::(fst r), snd r) }

ret_typ:
  | KW_VOID {TYPE_Void}
  | t = non_function_type { t }

typ:
  | t=non_function_type { t }
  | t=non_function_type LPAREN args=typ_args RPAREN   { let (ts,v) = args in TYPE_Function (t, ts, v) }
  | KW_VOID LPAREN args=typ_args RPAREN               { let (ts,v) = args in TYPE_Function (TYPE_Void, ts, v) }
  | KW_METADATA                                       { TYPE_Metadata         }

non_metadata_type:
  | t=non_function_type { t }
  | t=non_function_type LPAREN args=typ_args RPAREN   { let (ts,v) = args in TYPE_Function (t, ts, v) }
  | KW_VOID LPAREN args=typ_args RPAREN               { let (ts,v) = args in TYPE_Function (TYPE_Void, ts, v) }

non_function_type:
  | n=I                                               { TYPE_I n              }
  | KW_IPTR                                           { TYPE_Iptr             }
  | KW_PTR                                            { TYPE_Pointer (None)   }
  | KW_HALF                                           { TYPE_FP FP_half       }
  | KW_FLOAT                                          { TYPE_FP FP_float      }
  | KW_DOUBLE                                         { TYPE_FP FP_double     }
  | KW_X86_FP80                                       { TYPE_FP FP_x86_fp80   }
  | KW_FP128                                          { TYPE_FP FP_fp128      }
  | KW_PPC_FP128                                      { TYPE_FP FP_ppc_fp128  }
  | KW_X86_MMX                                        { TYPE_X86_mmx          }
  | t=typ STAR                                        { TYPE_Pointer (Some t) }
  | LSQUARE n=INTEGER KW_X t=typ RSQUARE              { TYPE_Array (n_of_int_syntax n, t)  }
  | LCURLY ts=separated_list(csep, typ) RCURLY        { TYPE_Struct ts        }
  | LTLCURLY ts=separated_list(csep, typ) RCURLYGT    { TYPE_Packed_struct ts }
  | KW_OPAQUE                                         { TYPE_Opaque           }
  | LT n=INTEGER KW_X t=typ GT                        { TYPE_Vector (n_of_int_syntax n, t) }
  | l=lident                                          { TYPE_Identified (ID_Local l)  }

param_attr:
  | KW_ZEROEXT                           { PARAMATTR_Zeroext                   }
  | KW_SIGNEXT                           { PARAMATTR_Signext                   }
  | KW_INREG                             { PARAMATTR_Inreg                     }
  | KW_BYVAL LPAREN t=typ RPAREN         { PARAMATTR_Byval t                   }
  | KW_BYREF LPAREN t=typ RPAREN         { PARAMATTR_Byref t                   }
  | KW_PREALLOCATED LPAREN t=typ RPAREN  { PARAMATTR_Preallocated t            }
  | KW_INALLOCA LPAREN t=typ RPAREN      { PARAMATTR_Inalloca t                }
  | KW_SRET LPAREN t=typ RPAREN          { PARAMATTR_Sret t                    }
  | KW_ELEMENTTYPE LPAREN t=typ RPAREN   { PARAMATTR_Elementtype t             }
  | KW_ALIGN n=INTEGER                   { PARAMATTR_Align n                   }
  | KW_ALIGN LPAREN n=INTEGER RPAREN     { PARAMATTR_Align n                   }
  | KW_NOALIAS                           { PARAMATTR_Noalias                   }
  | KW_NOCAPTURE                         { PARAMATTR_Nocapture                 }
  | KW_NOFREE                            { PARAMATTR_Nofree                    }
  | KW_NEST                              { PARAMATTR_Nest                      }
  | KW_RETURNED                          { PARAMATTR_Returned                  }
  | KW_NONNULL                           { PARAMATTR_Nonnull                   }
  | KW_DEREFERENCEABLE LPAREN n=INTEGER RPAREN
                                         { PARAMATTR_Dereferenceable n         }
  | KW_DEREFERENCEABLE_OR_NULL LPAREN n=INTEGER RPAREN
                                         { PARAMATTR_Dereferenceable_or_null n }
  | KW_SWIFTSELF                         { PARAMATTR_Swiftself                 }
  | KW_SWIFTASYNC                        { PARAMATTR_Swiftasync                }
  | KW_SWIFTERROR                        { PARAMATTR_Swifterror                }
  | KW_IMMARG                            { PARAMATTR_Immarg                    }
  | KW_NOUNDEF                           { PARAMATTR_Noundef                   }
  | KW_ALIGNSTACK LPAREN n=INTEGER RPAREN
                                         { PARAMATTR_Alignstack n              }
  | KW_ALLOCALIGN                        { PARAMATTR_Allocalign                }
  | KW_ALLOCPTR                          { PARAMATTR_Allocptr                  }
  | KW_READNONE                          { PARAMATTR_Readnone                  }
  | KW_READONLY                          { PARAMATTR_Readonly                  }
  | KW_WRITEONLY                         { PARAMATTR_Writeonly                 }
  | KW_WRITABLE                          { PARAMATTR_Writable                  }
  | KW_DEADONUNWIND                      { PARAMATTR_Dead_on_unwind            }
  | KW_RANGE LPAREN t=typ a=INTEGER COMMA b=INTEGER RPAREN { PARAMATTR_Range(t, a, b) }
  | KW_INITIALIZES LPAREN l=separated_list(csep, int_pair) RPAREN { PARAMATTR_Initializes(l) }

int_pair:
  | LPAREN i1=INTEGER COMMA i2=INTEGER RPAREN { (i1, i2) }

 (* TODO: This loses information when metadata is used as an argument *)
call_arg:
  | t=non_metadata_type ra=list(param_attr) i=exp { ((t, i t), ra) }
  | KW_METADATA mv=metadata_value                 { ((TYPE_Metadata, EXP_Metadata mv), []) } 
  | KW_METADATA t=non_metadata_type ra=list(param_attr) i=exp 
      { ((TYPE_Metadata, EXP_Metadata(METADATA_Const(t, i t))), ra) }

fn_attr:
  | KW_ALIGNSTACK LPAREN p=INTEGER RPAREN { FNATTR_Alignstack p     }
  (*  KW_ALLOC_FAMILY - quoted KeyValue *)
  | KW_ALLOCKIND LPAREN s=STRING RPAREN   { FNATTR_Allockind (str s) }
  | KW_ALLOCSIZE LPAREN l=separated_nonempty_list(csep, INTEGER) RPAREN
                                          { match l with
					    | [] -> failwith "impossible"
					    | x :: [] -> FNATTR_Allocsize (x, None)
					    | x :: y :: [] -> FNATTR_Allocsize (x, Some y)
					    | _ -> failwith "allocsize illegal - too long"

                                          }
  | KW_ALWAYSINLINE                       { FNATTR_Alwaysinline     }
  | KW_BUILTIN                            { FNATTR_Nobuiltin        }
  | KW_COLD                               { FNATTR_Cold             }
  | KW_CONVERGENT                         { FNATTR_Convergent       }
  | KW_DISABLE_SANITIZER_INSTRUMENTATION  { FNATTR_Disable_sanitizer_instrumentation }
(* KW_DONTCALL_ERROR - quoted *)
(* KW_DONTCALL_WARN - quoted *)
  | KW_FN_RET_THUNK_EXTERN                { FNATTR_Fn_ret_thunk_extern }
(* KW_FRAME_POINTER - quoted KeyValue *)
  | KW_HOT                                { FNATTR_Hot              }
  | KW_INACCESSIBLEMEMONLY                { FNATTR_Inaccessiblememonly }
  | KW_INACCESSIBLEMEM_OR_ARGMEMONLY      { FNATTR_Inaccessiblemem_or_argmemonly }
  | KW_INLINEHINT                         { FNATTR_Inlinehint       }
  | KW_JUMPTABLE                          { FNATTR_Jumptable        }
  | KW_MINSIZE                            { FNATTR_Minsize          }
  | KW_NAKED                              { FNATTR_Naked            }
(* KW_NO_INLINE_LINE_TABLES - quoted *)
  | KW_NO_JUMP_TABLES                     { FNATTR_No_jump_tables   }
  | KW_NOBUILTIN                          { FNATTR_Nobuiltin        }
  | KW_NODUPLICATE                        { FNATTR_Noduplicate      }
  | KW_NOFREE                             { FNATTR_Nofree           }
  | KW_NOIMPLICITFLOAT                    { FNATTR_Noimplicitfloat  }
  | KW_NOINLINE                           { FNATTR_Noinline         }
  | KW_NOMERGE                            { FNATTR_Nomerge          }
  | KW_NONLAZYBIND                        { FNATTR_Nonlazybind      }
  | KW_NOREDZONE                          { FNATTR_Noredzone        }
  | KW_INDIRECT_TLS_SEG_REFS              { FNATTR_Indirect_tls_seg_refs }
  | KW_NORETURN                           { FNATTR_Noreturn         }
  | KW_NORECURSE                          { FNATTR_Norecurse        }
  | KW_WILLRETURN                         { FNATTR_Willreturn       }
  | KW_NOSYNC                             { FNATTR_Nosync           }
  | KW_NOUNWIND                           { FNATTR_Nounwind         }
  | KW_NOSANITIZE_BOUNDS                  { FNATTR_Nosanitize_bounds }
  | KW_NOSANITIZE_COVERAGE                { FNATTR_Nosanitize_coverage }
  | KW_NULL_POINTER_IS_VALID              { FNATTR_Null_pointer_is_valid }
  | KW_OPTFORFUZZING                      { FNATTR_Optforfuzzing    }
  | KW_OPTNONE                            { FNATTR_Optnone          }
  | KW_OPTSIZE                            { FNATTR_Optsize          }
(* KW_PATCHABLE_FUNCTION - quoted KeyValue *)
(* KW_PROBE_STACK - quoted *)
  | KW_READNONE                           { FNATTR_Readnone         }
  | KW_READONLY                           { FNATTR_Readonly         }
(* KW_STACK_PROBE_SIZE - quoted KeyValue *)
(* KW_NO_STACK_ARG_PROBE - quoted *)
  | KW_WRITEONLY                          { FNATTR_Writeonly        }
  | KW_ARGMEMONLY                         { FNATTR_Argmemonly       }
  | KW_RETURNS_TWICE                      { FNATTR_Returns_twice    }
  | KW_SAFESTACK                          { FNATTR_Safestack        }
  | KW_SANITIZE_ADDRESS                   { FNATTR_Sanitize_address }
  | KW_SANITIZE_MEMORY                    { FNATTR_Sanitize_memory  }
  | KW_SANITIZE_THREAD                    { FNATTR_Sanitize_thread  }
  | KW_SANITIZE_HWADDRESS                 { FNATTR_Sanitize_hwaddress }
  | KW_SANITIZE_MEMTAG                    { FNATTR_Sanitize_memtag  }
  | KW_SPECULATIVE_LOAD_HARDENING         { FNATTR_Speculative_load_hardening }
  | KW_SPECULATABLE                       { FNATTR_Speculatable     }
  | KW_SSP                                { FNATTR_Ssp              }
  | KW_SSPSTRONG                          { FNATTR_Sspstrong        }
  | KW_SSPREQ                             { FNATTR_Sspreq           }
  | KW_STRICTFP                           { FNATTR_Strictfp         }
(* KW_DENORMAL_FP_MATH - quoted KeyValue *)
(* KW_DENORMAL_FP_MATH_F32 - quoted KeyValue *)
(* KW_THUNK - quoted *)
  | KW_UWTABLE                            { FNATTR_Uwtable None     }
  | KW_UWTABLE LPAREN KW_SYNC RPAREN      { FNATTR_Uwtable (Some true) }
  | KW_UWTABLE LPAREN KW_ASYNC RPAREN     { FNATTR_Uwtable (Some false) }
  | KW_NOCF_CHECK                         { FNATTR_Nocf_check       }
  | KW_SHADOWCALLSTACK                    { FNATTR_Shadowcallstack  }
  | KW_MUSTPROGRESS                       { FNATTR_Mustprogress     }
  | KW_VSCALE_RANGE LPAREN l=separated_nonempty_list(csep, INTEGER) RPAREN
                                          { match l with
					    | [] -> failwith "impossible"
					    | x :: [] -> FNATTR_Vscale_range (x, None)
					    | x :: y :: [] -> FNATTR_Vscale_range (x, Some y)
					    | _ -> failwith "allocsize illegal - too long"
					  }
  | s=STRING                              { FNATTR_String (str s)   }
  | k=STRING EQ v=STRING                  { FNATTR_Key_value (str k, str v) }
  | i=ATTR_GRP_ID                         { FNATTR_Attr_grp i       }
  | s=KW_UNKNOWN                          { FNATTR_UNKNOWN (str s)  }
  | KW_MEMORY LPAREN l=separated_nonempty_list (csep, mem_attr) RPAREN   { FNATTR_Memory l }

mem_attr:
  | k=mem_access_kind { (LOC_Default, k) }
  | l=mem_loc COLON k=mem_access_kind { (l, k) }
  | l=mem_loc_colon k=mem_access_kind { (l, k) }

mem_access_kind:
  | KW_NONE  { ACC_None }
  | KW_READ  { ACC_Read }
  | KW_WRITE { ACC_Write }
  | KW_READWRITE { ACC_Readwrite }

mem_loc:
  | KW_DEFAULT         { LOC_Default }
  | KW_ARGMEM          { LOC_Argmem }
  | KW_INACCESSIBLEMEM { LOC_Inaccessiblemem }
  | KW_ERRNOMEM        { LOC_Errnomem }

mem_loc_colon:
  | KW_DEFAULT_COLON   { LOC_Default }
  | KW_ARGMEM_COLON    { LOC_Argmem }
  | KW_INACCESSIBLEMEM_COLON { LOC_Inaccessiblemem }
  | KW_ERRNOMEM_COLON  { LOC_Errnomem }


%inline
ibinop_nuw_nsw_opt: (* may appear with `nuw`/`nsw` keywords *)
  | KW_ADD { fun nuw nsw -> Add (nuw, nsw) }
  | KW_SUB { fun nuw nsw -> Sub (nuw, nsw) }
  | KW_MUL { fun nuw nsw -> Mul (nuw, nsw) }
  | KW_SHL { fun nuw nsw -> Shl (nuw, nsw) }


ibinop_exact_opt: (* may appear with `exact` keyword *)
  | KW_UDIV { fun exact -> UDiv exact }
  | KW_SDIV { fun exact -> SDiv exact }
  | KW_LSHR { fun exact -> LShr exact }
  | KW_ASHR { fun exact -> AShr exact }

ibinop_no_opt: (* can not appear with any keyword *)
  | KW_UREM { URem }
  | KW_SREM { SRem }
  | KW_AND  { And  }
  | KW_OR dj=KW_DISJOINT?  { Or (opt_bool dj)  }
  | KW_XOR  { Xor  }

icmp:
  | KW_EQ  { Eq  }
  | KW_NE  { Ne  }
  | KW_UGT { Ugt }
  | KW_UGE { Uge }
  | KW_ULT { Ult }
  | KW_ULE { Ule }
  | KW_SGT { Sgt }
  | KW_SGE { Sge }
  | KW_SLT { Slt }
  | KW_SLE { Sle }


fcmp:
  | KW_FALSE { FFalse }
  | KW_OEQ   { FOeq   }
  | KW_OGT   { FOgt   }
  | KW_OGE   { FOge   }
  | KW_OLT   { FOlt   }
  | KW_OLE   { FOle   }
  | KW_ONE   { FOne   }
  | KW_ORD   { FOrd   }
  | KW_UNO   { FUno   }
  | KW_UEQ   { FUeq   }
  | KW_UGT   { FUgt   }
  | KW_UGE   { FUge   }
  | KW_ULT   { FUlt   }
  | KW_ULE   { FUle   }
  | KW_UNE   { FUne   }
  | KW_TRUE  { FTrue  }


conversion_pure:
  | KW_TRUNC                 { Trunc(false, false)  }
  | KW_TRUNC KW_NSW          { Trunc(false, true)   }
  | KW_TRUNC KW_NUW          { Trunc(true, false)   }
  | KW_TRUNC KW_NUW KW_NSW   { Trunc(true, true)    }
  | KW_ZEXT n=KW_NNEG?       { Zext(match n with None -> false | Some _ -> true) }
  | KW_SEXT                  { Sext     }
  | KW_FPTRUNC f=fast_math*  { Fptrunc f }
  | KW_FPEXT f=fast_math*    { Fpext f }
  | KW_UITOFP n=KW_NNEG?     { Uitofp(match n with None -> false | Some _ -> true)   }
  | KW_SITOFP                { Sitofp   }
  | KW_FPTOUI                { Fptoui   }
  | KW_FPTOSI                { Fptosi   }

conversion_impure:
  | KW_INTTOPTR              { Inttoptr      }
  | KW_PTRTOINT              { Ptrtoint      }
  | KW_PTRTOADDR             { Ptrtoaddr     }
  | KW_ADDRSPACECAST         { Addrspacecast }

conversion:
  | KW_BITCAST               { CONV_Bitcast  }
  | c=conversion_pure        { CONV_Pure c   }
  | c=conversion_impure      { CONV_Impure c } 

ibinop:
  | op=ibinop_nuw_nsw_opt   { op false false }
  | op=ibinop_nuw_nsw_opt KW_NSW { op false true }
  | op=ibinop_nuw_nsw_opt KW_NUW { op true false }
  | op=ibinop_nuw_nsw_opt KW_NUW KW_NSW { op true true }
  | op=ibinop_nuw_nsw_opt KW_NSW KW_NUW { op true true }
  | op=ibinop_exact_opt exact=KW_EXACT? { op (exact <> None) }
  | op=ibinop_no_opt { op }

fbinop:
  | KW_FADD { FAdd }
  | KW_FSUB { FSub }
  | KW_FMUL { FMul }
  | KW_FDIV { FDiv }
  | KW_FREM { FRem }

fast_math:
  | KW_NNAN { Nnan }
  | KW_NINF { Ninf }
  | KW_NSZ  { Nsz  }
  | KW_ARCP { Arcp }
  | KW_CONTRACT { Contract }
  | KW_AFN  { Afn }
  | KW_REASSOC { Reassoc }
  | KW_FAST { Fast }

comma_path_with_instr_metadata(X):
  | COMMA x=X lm=comma_path_with_instr_metadata(X)
    { let (l,md) = lm in
      (x::l, md) }
  | md=instr_metadata { ([], md) }

%inline
instr_op:
  | op=ibinop t=typ o1=exp COMMA o2=exp
    { OP_IBinop (op, t, o1 t, o2 t) }

  | KW_ICMP s=KW_SAMESIGN? op=icmp t=typ o1=exp COMMA o2=exp
    { OP_ICmp (opt_bool s, op, t, o1 t, o2 t) }

  | op=fbinop f=fast_math* t=typ o1=exp COMMA o2=exp
    { OP_FBinop (op, f, t, o1 t, o2 t) }

    // special case, coerced to fsub
  | KW_FNEG f=fast_math* t=typ o=exp 
     { OP_Fneg(f, (t,o t)) }

  | KW_FCMP op=fcmp t=typ o1=exp COMMA o2=exp 
    { OP_FCmp (op, t, o1 t, o2 t) }

  | c=conversion t1=typ v=exp KW_TO t2=typ
    { OP_Conversion (c, t1, v t1, t2) }

  | KW_SELECT if_=texp COMMA then_=texp COMMA else_= texp
    { OP_Select (if_, then_, else_) }

  | KW_FREEZE v=texp
    { OP_Freeze v }

  | KW_EXTRACTELEMENT vec=texp COMMA idx=texp 
    { OP_ExtractElement (vec, idx) }

  | KW_INSERTELEMENT vec=texp 
    COMMA new_el=texp COMMA idx=texp 
    { OP_InsertElement (vec, new_el, idx)  }

  | KW_SHUFFLEVECTOR v1=texp COMMA v2=texp COMMA mask=texp
    { OP_ShuffleVector (v1, v2, mask)  }

expr_op:
  | op=ibinop LPAREN t=typ o1=exp COMMA typ o2=exp RPAREN
    { OP_IBinop (op, t, o1 t, o2 t) }

  | KW_ICMP s=KW_SAMESIGN? op=icmp LPAREN t=typ o1=exp COMMA typ o2=exp RPAREN
    { OP_ICmp (opt_bool s, op, t, o1 t, o2 t) }

  | op=fbinop f=fast_math* LPAREN t=typ o1=exp COMMA typ o2=exp RPAREN
    { OP_FBinop (op, f, t, o1 t, o2 t) }

  // special case, coerced to fsub
  | KW_FNEG f=fast_math* t=typ o=exp
     { OP_Fneg(f, (t, o t)) }

  | KW_FCMP op=fcmp LPAREN t=typ o1=exp COMMA typ o2=exp RPAREN
    { OP_FCmp (op, t, o1 t, o2 t) }

  | c=conversion LPAREN t1=typ v=exp KW_TO t2=typ RPAREN
    { OP_Conversion (c, t1, v t1, t2) }

    (* SAZ: TODO - record the inbounds, nuw, nusw flags, also allow inrange(S,E) *) 
  | KW_GETELEMENTPTR KW_INBOUNDS? KW_NUSW? KW_NUW? LPAREN t=typ COMMA ptr=texp idx=preceded(COMMA, texp)* RPAREN
    { OP_GetElementPtr (t, ptr, idx) }

  | KW_SELECT LPAREN if_=texp COMMA then_=texp COMMA else_= texp RPAREN
    { OP_Select (if_, then_, else_) }

  | KW_FREEZE LPAREN v=texp RPAREN
    { OP_Freeze v }

  | KW_EXTRACTELEMENT LPAREN vec=texp COMMA idx=texp RPAREN
    { OP_ExtractElement (vec, idx) }

  | KW_INSERTELEMENT LPAREN vec=texp COMMA new_el=texp COMMA idx=texp RPAREN
    { OP_InsertElement (vec, new_el, idx)  }

  | KW_EXTRACTVALUE LPAREN tv=texp COMMA idx=separated_nonempty_list (csep, INTEGER) RPAREN
    { OP_ExtractValue (tv, idx) }

  | KW_INSERTVALUE LPAREN agg=texp COMMA new_val=texp COMMA idx=separated_nonempty_list (csep, INTEGER) RPAREN
    { OP_InsertValue (agg, new_val, idx) }

  | KW_SHUFFLEVECTOR LPAREN v1=texp COMMA v2=texp COMMA mask=texp RPAREN
    { OP_ShuffleVector (v1, v2, mask)  }

instr_path:
  | KW_EXTRACTVALUE tv=texp im=comma_path_with_instr_metadata(INTEGER)
    { let f_info = metadata_file_info $startpos $endpos in
      let (idx, md) = im in 
      (INSTR_Op (OP_ExtractValue (tv, idx)), f_info::md) }

  | KW_INSERTVALUE agg=texp COMMA new_val=texp im=comma_path_with_instr_metadata(INTEGER)
    { let f_info = metadata_file_info $startpos $endpos in
      let (idx, md) = im in
      (INSTR_Op (OP_InsertValue (agg, new_val, idx)), f_info::md) }

    (* SAZ: TODO - record the inbounds, nuw, nusw flags, also allow inrange(S,E) *) 
  | KW_GETELEMENTPTR KW_INBOUNDS? KW_NUSW? KW_NUW? t=typ COMMA ptr=texp im=comma_path_with_instr_metadata(texp)
    { let f_info = metadata_file_info $startpos $endpos in
      let (idx, md) = im in
      (INSTR_Op(OP_GetElementPtr (t, ptr, idx)), f_info::md) }


expr_val:
  | i=INTEGER                                         { fun _ -> EXP_Integer i        }
  | f=FLOAT                                           { fun _ -> EXP_Float f          }
  | KW_TRUE                                           { fun _ -> EXP_Bool true        }
  | KW_FALSE                                          { fun _ -> EXP_Bool false       }
  | KW_NULL                                           { fun _ -> EXP_Null             } 
  (* We still accept `undef`, but the minimal semantics has no dedicated
     undef value: it is parsed into [EXP_Undef] and denotes as [poison]
     (see [denote_exp] in src/rocq/Semantics/Denotation.v). *)
  | KW_UNDEF                                          { fun _ -> EXP_Undef            }
  | KW_POISON                                         { fun _ -> EXP_Poison           }
  | KW_ZEROINITIALIZER                                { fun _ -> EXP_Zero_initializer }
  | LCURLY l=separated_list(csep, tconst) RCURLY      { fun _ -> EXP_Struct l         }
  | LTLCURLY l=separated_list(csep, tconst) RCURLYGT  { fun _ -> EXP_Packed_struct l  }
  | LSQUARE l=separated_list(csep, tconst) RSQUARE    { fun t -> EXP_Array (t, l)     }
  | LT l=separated_list(csep, tconst) GT              { fun t -> EXP_Vector (t, l)    }
  | i=ident                                           { fun _ -> EXP_Ident i          }
  | KW_C cstr=STRING                                  { fun _ -> EXP_Cstring (
								     cstring_bytes_to_LLVM_i8_array
								     (unescape (str cstr))) }
  | KW_ASM se=KW_SIDEEFFECT? al=KW_ALIGNSTACK? id=KW_INTELDIALECT? uw=KW_UNWIND? s1=STRING COMMA s2=STRING
      { fun _ -> EXP_Asm (
		     (opt_bool se),
		     (opt_bool al),
		     (opt_bool id),
		     (opt_bool uw),
		     str s1,
		     str s2)
		   }
  | m=metadata_value { fun _ -> EXP_Metadata m }

  (* Note: we could pull the same trick as for parsing vectors to annotate splat with the
     full vector type rather than just the (local) element type.  That might mean that
     Denotation becomes simpler?
  *)
  | KW_SPLAT LPAREN elt=texp RPAREN                   { fun _ -> EXP_Splat(elt) }

a_num_elts:
  | csep t=texp lm=a_align
    { let (l,md) = lm in
      ((ANN_num_elements t)::l, md) }
  | l=a_align { l }

a_align:
  | csep KW_ALIGN n=INTEGER lm=a_addrspace
    { let (l,md) = lm in
      ((ANN_align n) :: l, md) }
  | l=a_addrspace { l }

a_addrspace:
  | csep a=addrspace md=instr_metadata { ([a], md) }
  | md=instr_metadata { ([], md) }

alloca_anns:
  anns=a_num_elts { anns }

ls_anns:
  | csep a=align md=instr_metadata
    { ([a], md) }
  | md=instr_metadata { ([], md) }

ax_anns:
  | a=comma_align md=instr_metadata
    { (Some a, md) }
  | md=instr_metadata { (None, md) }



tailcall:
  | KW_TAIL { ANN_tail Tail }
  | KW_MUSTTAIL { ANN_tail Musttail }
  | KW_NOTAIL { ANN_tail Notail }

exp:
  | eo=expr_op { fun _ -> eo }
  | ev=expr_val { ev }

operand:
  | t=texp    { SSA_value t }
  | s=STRING  { Metadata_string (METADATA_Id (LLVMAst.Name (str s))) }

operand_bundle:
  tag=STRING LPAREN ops=separated_list(csep, operand) RPAREN
    { {ob_tag = str tag; ob_ops = ops } }

operand_bundles:
  LSQUARE ops=separated_list(csep, operand_bundle) RSQUARE { ops }

instr:
  | eo=instr_op md=instr_metadata
    { 
      let f_info = metadata_file_info $startpos $endpos in
      (INSTR_Op eo, f_info::md)  }

  | ep=instr_path
     { ep }

  | t=tailcall? KW_CALL fm=list(fast_math) cc=cconv? ra=list(param_attr) addr=addrspace?
    f=call_exp  a=delimited(LPAREN, separated_list(csep, call_arg), RPAREN)
    fa=list(fn_attr) ops=operand_bundles? md=instr_metadata
    {
      let f_info = metadata_file_info $startpos $endpos in
      let atts =
	(opt_list t)
	@ (List.map (fun f -> ANN_fast_math_flag f) fm)
	@ (opt_list cc)
        @ (List.map (fun r -> ANN_ret_attribute r) ra)
        @ (opt_list addr)
        @ (List.map (fun f -> ANN_fun_attribute f) fa)
      in
      let ops = begin match ops with
		| None -> []
		| Some ops -> ops
		end
      in
      (INSTR_Call (f, a, atts, ops), f_info::md) }

  | KW_ALLOCA ia=KW_INALLOCA? t=typ am=alloca_anns
    {
      let f_info = metadata_file_info $startpos $endpos in     
      let a = ann_opt ia ANN_inalloca in
      let (anns, md) = am in
      (INSTR_Alloca (t, a@anns), f_info::md) }

  | KW_LOAD at=KW_ATOMIC? vol=KW_VOLATILE? t=typ COMMA tv=texp ss=syncscope? o=ordering? am=ls_anns
    { let f_info = metadata_file_info $startpos $endpos in     
      let at_ann = ann_opt at ANN_atomic in
      let v = ann_opt vol ANN_volatile in
      let (a, md) = am in
      let (ss_ann : typ annotation list) = opt_list ss in
      let ord_ann = List.map (fun x -> ANN_ordering x) (opt_list o) in
      (INSTR_Load (t, tv, at_ann@v@ss_ann@ord_ann@a), f_info::md) } 


  | KW_VAARG tv=texp COMMA t=typ md=instr_metadata
    { let f_info = metadata_file_info $startpos $endpos in     
      (INSTR_VAArg (tv, t), f_info::md)
    }

  | KW_STORE at=KW_ATOMIC? vol=KW_VOLATILE? all=texp COMMA ptr=texp ss=syncscope? o=ordering? am=ls_anns
    { let f_info = metadata_file_info $startpos $endpos in     
      let at_ann = ann_opt at ANN_atomic in
      let v = ann_opt vol ANN_volatile in
      let (a, md) = am in
      let (ss_ann : typ annotation list) = opt_list ss in
      let ord_ann = List.map (fun x -> ANN_ordering x) (opt_list o) in
      (INSTR_Store (all, ptr, at_ann@v@ss_ann@ord_ann@a), f_info::md) }

  | KW_ATOMICCMPXCHG c_weak=KW_WEAK? c_volatile=KW_VOLATILE?
    c_ptr=texp COMMA c_cmp=texp COMMA c_new=texp ss=syncscope?
    c_success_ordering=ordering c_failure_ordering=ordering am=ax_anns
    { let f_info = metadata_file_info $startpos $endpos in
      let (c_align, md) = am in
      let c_syncscope =
	       begin match ss with
               | Some (ANN_syncscope s) -> Some s
	       | Some _ -> failwith "impossible: syncscope not found"
	       | _ -> None
	       end
      in
      (INSTR_AtomicCmpXchg
	 {
	   c_weak;
	   c_volatile;
	   c_ptr;
	   c_cmp;
	   c_new;
	   c_syncscope;
	   c_success_ordering;
	   c_failure_ordering;	   
	   c_align;
	 }
      , f_info::md)
    }
      
  | KW_ATOMICRMW a_volatile=KW_VOLATILE? a_operation=atomicrmw_op
    a_ptr=texp COMMA a_val=texp ss=syncscope? a_ordering=ordering am=ax_anns;
    { let f_info = metadata_file_info $startpos $endpos in
      let (a_align, md) = am in      
      let a_syncscope = begin match ss with
               | Some (ANN_syncscope s) -> Some s
	       | Some _ -> failwith "impossible: syncscope not found"
	       | _ -> None
	       end
      in
      (INSTR_AtomicRMW
	{ a_volatile;
          a_operation;
	  a_ptr;
	  a_val;
	  a_syncscope;
	  a_ordering;
	  a_align;
	}
      , f_info::md)
    }

  | KW_FENCE ss=syncscope? a_ordering=ordering md=instr_metadata
    { let f_info = metadata_file_info $startpos $endpos in     
      let a_syncscope = begin match ss with
               | Some (ANN_syncscope s) -> Some s
	       | Some _ -> failwith "impossible: syncscope not found"
	       | _ -> None
	       end
      in
      (INSTR_Fence(a_syncscope, a_ordering), f_info::md)
    }
  | KW_LANDINGPAD t=typ KW_CLEANUP cs=clause* md=instr_metadata
    { let f_info = metadata_file_info $startpos $endpos in     
      (INSTR_LandingPad (t, true, cs), f_info::md) }

  | KW_LANDINGPAD t=typ cs=clause+ md=instr_metadata
    { let f_info = metadata_file_info $startpos $endpos in     
      (INSTR_LandingPad (t, false, cs), f_info::md) }

syncscope:
  KW_SYNCSCOPE LPAREN s=STRING RPAREN
    { ANN_syncscope (str s) }

ordering:
 | KW_UNORDERED  { Unordered }
 | KW_MONOTONIC  { Monotonic }
 | KW_ACQUIRE    { Acquire }
 | KW_RELEASE    { Release }
 | KW_ACQ_REL    { Acq_rel }
 | KW_SEQ_CST    { Seq_cst }

atomicrmw_op:
 | KW_XCHG  { Axchg }
 | KW_ADD   { Aadd }
 | KW_SUB   { Asub }
 | KW_AND   { Aand }
 | KW_NAND  { Anand }
 | KW_OR    { Aor }
 | KW_XOR   { Axor }
 | KW_MAX   { Amax }
 | KW_MIN   { Amin }
 | KW_UMAX  { Aumax }
 | KW_UMIN  { Aumin }
 | KW_FADD  { Afadd }
 | KW_FSUB  { Afsub }
 | KW_FMAX  { Afmax }
 | KW_FMIN  { Afmin }
 | KW_FMAXIMUM { Afmaximum }
 | KW_FMINIMUM { Afminimum }
 | KW_UINC_WRAP { Auinc_wrap }
 | KW_UDEC_WRAP { Audec_wrap }
 | KW_USUB_COND { Ausub_cond }
 | KW_USUB_SAT  { Ausub_sat }




%inline
clause:
  | KW_CATCH t=typ v=expr_val { CATCH (t, v t) }
  | KW_FILTER t=typ v=expr_val{ FILTER (t, v t) }

branch_label:
  KW_LABEL o=LOCAL  { lexed_id_to_raw_id o }

%inline
terminator:
  | KW_RET tv=texp md=instr_metadata
    { let f_info = metadata_file_info $startpos $endpos in     
      ((TERM_Ret tv), f_info::md) }

  | KW_RET KW_VOID md=instr_metadata
    { let f_info = metadata_file_info $startpos $endpos in     
      (TERM_Ret_void, f_info::md) }

  | KW_BR c=texp COMMA o1=branch_label COMMA o2=branch_label md=instr_metadata
    { let f_info = metadata_file_info $startpos $endpos in     
      (TERM_Br (c, o1, o2), f_info::md) }

  | KW_BR b=branch_label md=instr_metadata
    { let f_info = metadata_file_info $startpos $endpos in     
      (TERM_Br_1 b, f_info::md) }

  | KW_SWITCH c=texp COMMA
    def=branch_label LSQUARE table=list(switch_table_entry) RSQUARE md=instr_metadata
    { let f_info = metadata_file_info $startpos $endpos in     
      (TERM_Switch (c, def, table), f_info::md) }

  | KW_INDIRECTBR tv=texp
    COMMA LSQUARE til=separated_list(csep, branch_label)  RSQUARE md=instr_metadata
    { let f_info = metadata_file_info $startpos $endpos in     
      (TERM_IndirectBr (tv, til), f_info::md) }

  | KW_RESUME tv=texp md=instr_metadata
    { let f_info = metadata_file_info $startpos $endpos in
      (TERM_Resume tv, f_info::md) }

  | KW_INVOKE fm=list(fast_math) cc=cconv? ra=list(param_attr) addr=addrspace?
    f=call_exp  a=delimited(LPAREN, separated_list(csep, call_arg), RPAREN)
    fa=list(fn_attr)
    ops=operand_bundles?
    KW_TO l1=branch_label 
    KW_UNWIND l2=branch_label
    md=instr_metadata

    { let f_info = metadata_file_info $startpos $endpos in
      let atts =
	  (List.map (fun f -> ANN_fast_math_flag f) fm)
	@ (opt_list cc)
        @ (List.map (fun r -> ANN_ret_attribute r) ra)
        @ (opt_list addr)
        @ (List.map (fun f -> ANN_fun_attribute f) fa)
      in
      let ops = begin match ops with
		| None -> []
		| Some ops -> ops
		end
      in
      (TERM_Invoke(f, a, l1, l2, atts, ops), f_info::md)  }

  | KW_UNREACHABLE md=instr_metadata
    { let f_info = metadata_file_info $startpos $endpos in
      (TERM_Unreachable, f_info::md) }

comma_align:
  | COMMA KW_ALIGN n=INTEGER { n }

align:
  | KW_ALIGN n=INTEGER { ANN_align n }

switch_table_entry:
  | sz=I x=INTEGER COMMA i=branch_label { (TInt_Literal(sz, x), i) }

%inline csep:
  COMMA { }


lident:
  | l=LOCAL  { (lexed_id_to_raw_id l) }

bound_lident:
  | l=LOCAL  { l }

gident:
  | g=GLOBAL  { (lexed_id_to_raw_id g) }

ident:
  | g=gident  { ID_Global g }
  | l=lident  { ID_Local  l }

call_exp:
  | t=typ v=exp { (t, v t) }
  | KW_VOID v=exp { (TYPE_Void, v TYPE_Void) }

texp:   t=typ v=exp { (t, v t) }
tconst: t=typ c=exp { (t, c t) }

(* SAZ: Copying this here is a bit unfortunate but works for now.
   It might be better to experiment with eliminating the "inline" keyword
   for the instr nonterminal and then add a new nonterminal like this:
test_instr:
   instr EOF { ... }
*)

test_call:
  | t=tailcall? KW_CALL fm=list(fast_math) cc=cconv? ra=list(param_attr) addr=addrspace?
    f=texp  a=delimited(LPAREN, separated_list(csep, call_arg), RPAREN)
    fa=list(fn_attr) EOF (* TODO: operand bundles? *)
    { let atts =
	(opt_list t)
	@ (List.map (fun f -> ANN_fast_math_flag f) fm)
	@ (opt_list cc)
        @ (List.map (fun r -> ANN_ret_attribute r) ra)
        @ (opt_list addr)
        @ (List.map (fun f -> ANN_fun_attribute f) fa)
      in
      INSTR_Call (f, a, atts, []) }
