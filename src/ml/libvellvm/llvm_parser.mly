%{ (* {{{ LICENSE                                                              *
  * vi: set fdm=marker fdl=0:                                                *
  *                                                                          *
  * Copyright (c) 2012 Raphaël Proust <raphlalou@gmail.com>                  *
  * Copyright (c) 2012 INRIA - Raphaël Proust <raphlalou@gmail.com>          *
  * Copyright (c) 2012 ENS - Raphaël Proust <raphlalou@gmail.com>            *
  * Copyright (c) 2014 OCamlPro - Julien Sagot <ju.sagot@gmail.com>          *
  * Copyright (c) 2017 U. Penn. Steve Zdancewic <stevez@cis.upenn.edu>       *
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



open LLVMAst
open ParserHelper
open ParseUtil

(* normalize_float_size : 
   - LLVM floating point literals need different interpretations depending
     on their types.

   - This function converts a string into either a 
     EXP_Double 64-bit literal, or
     EXP_Float 32-bit literal depending on the type annotation t
 *)
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

(* att type is a workaround to simplify parsing of optionnal keywords in
 * global / function declaration / definition.
 * It is far from what would be ideal since it will allow to parse silly
 * LLVM IR (keywords at the bad place, or function attributes in global
 * variable declaration, ...).
 * It will work as expected with valid LLVM IR. *)

type att =
  | OPT_fn_attr of fn_attr list
  | OPT_align of Camlcoq.Z.t
  | OPT_section of string
  | OPT_linkage of linkage
  | OPT_visibility of visibility
  | OPT_thread_local of thread_local_storage
  | OPT_addrspace of Camlcoq.Z.t
  | OPT_unnamed_addr
  | OPT_cconv of cconv
  | OPT_dll_storage of dll_storage
  | OPT_externally_initialized
  | OPT_gc of string

let rec get_opt f  = function
  | []       -> None
  | hd :: tl -> match f hd with None -> get_opt f tl | x -> x

let get_fn_attrs l =
  match get_opt (function OPT_fn_attr a -> Some a | _ -> None) l with
  | None  -> []
  | Some l -> l

let get_section =
  get_opt (function OPT_section s -> Some (str s) | _ -> None)

let get_align =
  get_opt (function OPT_align a -> Some a | _ -> None)

let get_linkage =
  get_opt (function OPT_linkage l -> Some l | _ -> None)

let get_visibility =
  get_opt (function OPT_visibility v -> Some v | _ -> None)

let get_addrspace =
  get_opt (function OPT_addrspace i -> Some i | _ -> None)

let get_dll_storage =
  get_opt (function OPT_dll_storage i -> Some i | _ -> None)

let get_cconv =
  get_opt (function OPT_cconv i -> Some i | _ -> None)

let get_thread_local =
  get_opt (function OPT_thread_local x -> Some x | _ -> None)

let get_gc =
  get_opt (function OPT_gc x -> Some (str x) | _ -> None)

let is_unnamed_addr l =
  None <> get_opt (function OPT_unnamed_addr -> Some () | _ -> None) l

let is_externally_initialized l =
  None <> get_opt (function OPT_externally_initialized -> Some () | _ -> None) l

%}

%token<ParseUtil.lexed_id> GLOBAL LOCAL
%token LPAREN RPAREN LCURLY RCURLY LTLCURLY RCURLYGT LSQUARE RSQUARE LT GT EQ COMMA EOF EOL STAR DOTDOTDOT

%token<string> STRING
%token<Camlcoq.Z.t> INTEGER
%token<string> FLOAT
%token<Floats.float> HEXCONSTANT
%token KW_NULL 
%token KW_UNDEF 
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
%token KW_DLLIMPORT 
%token KW_DLLEXPORT
%token KW_DEFAULT 
%token KW_HIDDEN 
%token KW_PROTECTED

%token KW_CCC 
%token KW_FASTCC 
%token KW_COLDCC 
%token KW_CC
%token KW_UNNAMED_ADDR
%token KW_TYPE 
%token KW_X 
%token KW_OPAQUE
%token KW_GLOBAL 
%token KW_ADDRSPACE 
%token KW_CONSTANT 
%token KW_SECTION 
%token KW_THREAD_LOCAL 
%token KW_LOCALDYNAMIC 
%token KW_INITIALEXEC 
%token KW_LOCALEXEC 
%token KW_EXTERNALLY_INITIALIZED
%token KW_ZEROEXT 
%token KW_SIGNEXT 
%token KW_INREG 
%token KW_BYVAL 
%token KW_SRET 
%token KW_NOALIAS 
%token KW_NOCAPTURE 
%token KW_NEST

%token KW_ALIGNSTACK
%token KW_ALLOCSIZE 
%token KW_ALWAYSINLINE 
%token KW_BUILTIN 
%token KW_COLD
%token KW_CONVERGENT
%token KW_HOT
%token KW_INACCESSIBLEMEMONLY
%token KW_INACCESSIBLEMEM_OR_ARGMEMONLY
%token KW_INLINEHINT 
%token KW_JUMPTABLE 
%token KW_MINSIZE 
%token KW_NAKED 
%token KW_NO_JUMP_TABLES
%token KW_NOBUILTIN 
%token KW_NODUPLICATE
%token KW_NOFREE
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
%token KW_NULL_POINTER_IS_VALID
%token KW_OPTFORFUZZING
%token KW_OPTNONE 
%token KW_OPTSIZE 
%token KW_READNONE 
%token KW_READONLY 
%token KW_WRITEONLY
%token KW_ARGMEMONLY
%token KW_RETURNS_TWICE
%token KW_SAFESTACK
%token KW_SANITIZE_ADDRESS 
%token KW_SANITIZE_MEMORY 
%token KW_SANITIZE_THREAD 
%token KW_SANITIZE_HWADDRESS
%token KW_SANITIZE_MEMTAG
%token KW_SPECULATIVE_LOAD_HARDENING
%token KW_SPECULATABLE
%token KW_SSP 
%token KW_SSPREQ 
%token KW_SSPSTRONG
%token KW_STRICTFP
%token KW_UWTABLE
%token KW_NOCF_CHECK
%token KW_SHADOWCALLSTACK
%token KW_MUSTPROGRESS

%token KW_DEREFERENCEABLE 
%token KW_INALLOCA
%token KW_RETURNED 
%token KW_NONNULL


%token KW_ALIGN
%token KW_GC

%token KW_ADD 
%token KW_FADD 
%token KW_SUB 
%token KW_FSUB 
%token KW_MUL 
%token KW_FMUL 
%token KW_UDIV 
%token KW_SDIV 
%token KW_FDIV 
%token KW_UREM 
%token KW_SREM 
%token KW_FREM 
%token KW_SHL 
%token KW_LSHR 
%token KW_ASHR 
%token KW_AND 
%token KW_OR 
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

%token KW_NNAN 
%token KW_NINF 
%token KW_NSZ 
%token KW_ARCP 
%token KW_FAST
%token<Camlcoq.N.t> I
%token KW_VOID 
%token KW_HALF 
%token KW_FLOAT 
%token KW_DOUBLE 
%token KW_X86_FP80 
%token KW_FP128 
%token KW_PPC_FP128 
%token KW_LABEL 
%token KW_METADATA 
%token KW_X86_MMX

%token KW_UNWIND 
%token KW_TO
%token KW_NUW 
%token KW_NSW
%token KW_EXACT
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
%token KW_VOLATILE
%token KW_NOUNDEF 
%token KW_IMMARG 


%token<LLVMAst.raw_id> METADATA_ID
%token<string> METADATA_STRING
%token BANGLCURLY
%token KW_ATTRIBUTES
%token<Camlcoq.Z.t> ATTR_GRP_ID

%start<(LLVMAst.typ, (LLVMAst.typ LLVMAst.block) * ((LLVMAst.typ LLVMAst.block) list)) LLVMAst.toplevel_entities> toplevel_entities
%start<LLVMAst.typ LLVMAst.instr> test_call
%start<(LLVMAst.typ * LLVMAst.typ LLVMAst.exp)> texp

%%

toplevel_entities:
  | EOL* m=terminated(toplevel_entity, EOL*)* EOF { m }

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
  | i=METADATA_ID EQ m=tle_metadata     { TLE_Metadata (i, m)            }
  | KW_ATTRIBUTES i=ATTR_GRP_ID EQ LCURLY a=fn_attr* RCURLY
                                        { TLE_Attribute_group (i, a)     }

(* metadata are not implemented yet, but are at least (partially) parsed *)
tle_metadata:
  | BANGLCURLY m=separated_list(csep, metadata_value) RCURLY
   { METADATA_Node m }
  | KW_METADATA m=metadata_node
    { m }

metadata_node:
  | BANGLCURLY m=separated_list(csep, metadata_value) RCURLY
    { METADATA_Node m }

metadata_value:
  | tconst                      { METADATA_Const $1  }
  | KW_NULL                     { METADATA_Null      } (* null with no type *)
  | ms=METADATA_STRING          { METADATA_String (str ms) }
  | mid=METADATA_ID             { METADATA_Id mid     }
  | mn=metadata_node            { mn                  }


global_decl:
  | g_ident=gident EQ
    el=external_linkage
    attrs=global_attr*
    g_constant=global_is_constant
    g_typ=typ
    opt=preceded(COMMA, separated_list(csep, global_attr))?
      { let opt = match opt with Some o -> o | None -> [] in
        { g_ident;
          g_typ;
          g_constant;

	  g_exp = None;
          g_linkage = Some el;
          g_visibility = get_visibility attrs;
          g_dll_storage = get_dll_storage attrs;
          g_thread_local = get_thread_local attrs;
          g_unnamed_addr = is_unnamed_addr attrs;
          g_addrspace = get_addrspace attrs;
          g_externally_initialized = is_externally_initialized attrs;
          g_section = get_section opt;
          g_align = get_align opt; } }
  
  | g_ident=gident EQ
    g_linkage=nonexternal_linkage?
    attrs=global_attr*
    g_constant=global_is_constant
    g_typ=typ
    gv=exp
    opt=preceded(COMMA, separated_list(csep, global_attr))?
      { let opt = match opt with Some o -> o | None -> [] in
        { g_ident;
          g_typ;
          g_constant;
          g_exp = Some (gv g_typ);

          g_linkage;
          g_visibility = get_visibility attrs;
          g_dll_storage = get_dll_storage attrs;
          g_thread_local = get_thread_local attrs;
          g_unnamed_addr = is_unnamed_addr attrs;
          g_addrspace = get_addrspace attrs;
          g_externally_initialized = is_externally_initialized attrs;
          g_section = get_section opt;
          g_align = get_align opt; } }

global_is_constant:
  | KW_GLOBAL { false }
  | KW_CONSTANT { true }

global_attr:
  | a=visibility                         { OPT_visibility a           }
  | a=dll_storage                        { OPT_dll_storage a          }
  | KW_THREAD_LOCAL LPAREN t=tls RPAREN  { OPT_thread_local t         }
  | KW_UNNAMED_ADDR                      { OPT_unnamed_addr           }
  | KW_EXTERNALLY_INITIALIZED            { OPT_externally_initialized }
  | KW_ALIGN n=INTEGER           	 { OPT_align n                }
  | KW_ADDRSPACE LPAREN n=INTEGER RPAREN { OPT_addrspace n            }

dll_storage:
  | KW_DLLIMPORT { DLLSTORAGE_Dllimport }
  | KW_DLLEXPORT { DLLSTORAGE_Dllexport }

tls:
  | KW_LOCALDYNAMIC { TLS_Localdynamic }
  | KW_INITIALEXEC  { TLS_Initialexec  }
  | KW_LOCALEXEC    { TLS_Localexec    }

declaration:
  | KW_DECLARE
    pre_attrs=df_pre_attr*
    df_ret_attrs=param_attr*
    df_ret_typ=typ
    name=GLOBAL

    midrule( { void_ctr.reset () } )   (* reset the void counter to 0 *)

    LPAREN dc_args=separated_list(csep, dc_arg) RPAREN
    post_attrs=df_post_attr*

    { 
      {
	 dc_type        = TYPE_Function(df_ret_typ, List.map fst dc_args);
         dc_param_attrs = (df_ret_attrs, List.map snd dc_args);
         dc_name        = lexed_id_to_raw_id name ;
         dc_linkage     = get_linkage pre_attrs;
         dc_visibility  = get_visibility pre_attrs;
         dc_dll_storage = get_dll_storage pre_attrs;
         dc_cconv       = get_cconv pre_attrs;
         dc_attrs       = get_fn_attrs post_attrs;
         dc_section     = get_section post_attrs;
         dc_align       = get_align post_attrs;
         dc_gc          = get_gc post_attrs;
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

definition:
  | KW_DEFINE
    pre_attrs     = df_pre_attr*
    df_ret_attrs  = param_attr*
    df_ret_typ    = typ
    name          = GLOBAL

    midrule( { void_ctr.reset () } )   (* reset the void counter to 0 *)

    LPAREN args=separated_list(csep, df_arg) RPAREN

    post_attrs   = df_post_attr* EOL*
    LCURLY EOL*
    blks=df_blocks
    RCURLY
    {
      (* prepare to validate / generate the sequential identifiers *)
      let _ = anon_ctr.reset ()
      in

      (* process the arg identifiers *)
      let df_args =
	List.map (fun (_, aopt) -> check_or_generate_id aopt) args
      in

      let process_lhs_phi (lopt, x) = (check_or_generate_id lopt, x)
      in

      let process_lhs_instr (lopt, i) =
	if AstLib.is_void_instr i then
	  match lopt with
	  | None   -> (generate_void_instr_id (), i)
	  | Some _ -> failwith "void function has defined left-hand-side"
	else
	  (IId (check_or_generate_id lopt), i)
      in	
	
      let process_block (lopt, (phis, instrs), blk_term) =
	  let blk_id   = check_or_generate_label lopt in
	  let blk_phis = List.map process_lhs_phi phis in
	  let blk_code = List.map process_lhs_instr instrs in
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
          dc_type = TYPE_Function (df_ret_typ, 
                                   List.map (fun x -> fst (fst x)) args) ;
          dc_param_attrs = (df_ret_attrs,
                           List.map (fun x -> snd (fst x)) args) ;
          dc_name        = lexed_id_to_raw_id name;
	  dc_linkage     = get_linkage pre_attrs;
          dc_visibility  = get_visibility pre_attrs;
          dc_dll_storage = get_dll_storage pre_attrs;
          dc_cconv       = get_cconv pre_attrs;
          dc_attrs       = get_fn_attrs post_attrs;
          dc_section     = get_section post_attrs;
          dc_align       = get_align post_attrs;
          dc_gc          = get_gc post_attrs;
	  } ;
        df_args;
        df_instrs;
      }
    }

(*
      begin match blks with
      | [] -> failwith "illegal LLVM function definition: must have non-empty entry block"
      | entry::rest -> (entry, rest)
      end
    }
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

  | lbl=LABEL EOL*
    { Some lbl }


block_phis_and_instrs:
  | /* empty */   { ([], []) }

  | id_opt=instr_lhs p=phi EOL+ bl=block_phis_and_instrs
    { let (phis, instrs) = bl in ((id_opt, p)::phis, instrs) }

  | id_opt=instr_lhs inst=instr EOL+ ins=block_instrs
    { ([], (id_opt, inst)::ins) }

block_instrs:
  | /* empty */  { [] }

  | id_opt=instr_lhs inst=instr EOL+ ins=block_instrs
    {  (id_opt, inst)::ins }

%inline phi:
  | KW_PHI t=typ table=separated_nonempty_list(csep, phi_table_entry)
    { Phi (t, List.map (fun (l,v) -> (l, v t)) table)}

phi_table_entry:
  | LSQUARE v=exp COMMA l=lident RSQUARE { (l, v) }

block:
  blk_id   = block_label 
  body     = block_phis_and_instrs
  blk_term = terminated(terminator, EOL+)
    {
	(blk_id, body, blk_term)
    }


df_blocks: 
  | blks=block+
    { blks }

df_pre_attr:
  | a=linkage                            { OPT_linkage a     }
  | a=visibility                         { OPT_visibility a  }
  | a=dll_storage                        { OPT_dll_storage a }
  | a=cconv                              { OPT_cconv a       }

df_post_attr:
  | KW_ADDRSPACE LPAREN n=INTEGER RPAREN { OPT_addrspace n   }
  | KW_UNNAMED_ADDR                      { OPT_unnamed_addr  }
  | a=fn_attr+                           { OPT_fn_attr a     }
  (* parser conflict with fn_attr+ looking for a df_post_attr list,
   * because if function attribute a2 follows function attribute a1,
   * it can be seen as [...;[a1];[a2];...] or [...;[a1;a2];...].
   * Shifting to [a1;a2] is the good solution and it is how menhir
   * will handle this conflict. *)
  | s=section                            { OPT_section s     }
                                         (* TODO: comdat *)
  | a=align                              { OPT_align a       }
  | KW_GC a=STRING                       { OPT_gc a          }
                                         (* TODO: prefix *)
external_linkage:
  | KW_EXTERN_WEAK                  { LINKAGE_Extern_weak                  }
  | KW_EXTERNAL                     { LINKAGE_External                     }

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

visibility:
  | KW_DEFAULT   { VISIBILITY_Default   }
  | KW_HIDDEN    { VISIBILITY_Hidden    }
  | KW_PROTECTED { VISIBILITY_Protected }

cconv:
  |KW_CCC{CC_Ccc}|KW_FASTCC{CC_Fastcc}|KW_COLDCC{CC_Coldcc}
  |KW_CC n=INTEGER{CC_Cc n}

typ:
  | n=I                                               { TYPE_I n              }
  | KW_VOID                                           { TYPE_Void             }
  | KW_HALF                                           { TYPE_Half             }
  | KW_FLOAT                                          { TYPE_Float            }
  | KW_DOUBLE                                         { TYPE_Double           }
  | KW_X86_FP80                                       { TYPE_X86_fp80         }
  | KW_FP128                                          { TYPE_Fp128            }
  | KW_PPC_FP128                                      { TYPE_Ppc_fp128        }
  | KW_METADATA                                       { TYPE_Metadata         }
  | KW_X86_MMX                                        { TYPE_X86_mmx          }
  | t=typ STAR                                        { TYPE_Pointer t        }
  | LSQUARE n=INTEGER KW_X t=typ RSQUARE              { TYPE_Array (n_of_z n, t)  }
  | t=typ LPAREN ts=separated_list(csep, typ) RPAREN  { TYPE_Function (t, ts) }
  | LCURLY ts=separated_list(csep, typ) RCURLY        { TYPE_Struct ts        }
  | LTLCURLY ts=separated_list(csep, typ) RCURLYGT    { TYPE_Packed_struct ts }
  | KW_OPAQUE                                         { TYPE_Opaque           }
  | LT n=INTEGER KW_X t=typ GT                        { TYPE_Vector (n_of_z n, t) }
  | l=lident                                          { TYPE_Identified (ID_Local l)  }

param_attr:
  | KW_ZEROEXT                   { PARAMATTR_Zeroext           }
  | KW_SIGNEXT                   { PARAMATTR_Signext           }
  | KW_INREG                     { PARAMATTR_Inreg             }
  | KW_BYVAL                     { PARAMATTR_Byval             }
  | KW_INALLOCA                  { PARAMATTR_Inalloca          }
  | KW_SRET                      { PARAMATTR_Sret              }
  | KW_ALIGN n=INTEGER           { PARAMATTR_Align n           }
  | KW_NOALIAS                   { PARAMATTR_Noalias           }
  | KW_NOCAPTURE                 { PARAMATTR_Nocapture         }
  | KW_READONLY                  { PARAMATTR_Readonly          }
  | KW_NEST                      { PARAMATTR_Nest              }
  | KW_RETURNED                  { PARAMATTR_Returned          }
  | KW_NONNULL                   { PARAMATTR_Nonnull           }
  | KW_DEREFERENCEABLE LPAREN n=INTEGER RPAREN
                                 { PARAMATTR_Dereferenceable n }
  | KW_IMMARG                    { PARAMATTR_Immarg            }
  | KW_NOUNDEF                   { PARAMATTR_Noundef           }
  | KW_NOFREE                    { PARAMATTR_Nofree            }

dc_arg:
  | t=typ p=param_attr*         { (t, p) }
  | t=typ p=param_attr* lident  { (t, p) }  (* Throw away declaration names? *)

df_arg:
 | t=typ p=param_attr*                { ((t, p), None)   }  (* Later generate anonymous label *)
 | t=typ p=param_attr* l=bound_lident { ((t, p), Some l) }  (* Later validate anonymous or use name *)

call_arg: t=typ i=exp             { (t, i t)      }

fn_attr:
  | KW_ALIGNSTACK LPAREN p=INTEGER RPAREN { FNATTR_Alignstack p     }
  | KW_ALLOCSIZE LPAREN l=separated_nonempty_list(csep, INTEGER) RPAREN
                                          { FNATTR_Allocsize l      }
  | KW_ALWAYSINLINE                       { FNATTR_Alwaysinline     }
  | KW_BUILTIN                            { FNATTR_Nobuiltin        }
  | KW_COLD                               { FNATTR_Cold             }
  | KW_CONVERGENT                         { FNATTR_Convergent       }
  | KW_HOT                                { FNATTR_Hot              }
  | KW_INACCESSIBLEMEMONLY                { FNATTR_Inaccessiblememonly }
  | KW_INACCESSIBLEMEM_OR_ARGMEMONLY      { FNATTR_Inaccessiblemem_or_argmemonly }
  | KW_INLINEHINT                         { FNATTR_Inlinehint       }
  | KW_JUMPTABLE                          { FNATTR_Jumptable        }
  | KW_MINSIZE                            { FNATTR_Minsize          }
  | KW_NAKED                              { FNATTR_Naked            }
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
  | KW_NULL_POINTER_IS_VALID              { FNATTR_Null_pointer_is_valid }
  | KW_OPTFORFUZZING                      { FNATTR_Optforfuzzing    }
  | KW_OPTNONE                            { FNATTR_Optnone          }
  | KW_OPTSIZE                            { FNATTR_Optsize          }
  | KW_READNONE                           { FNATTR_Readnone         }
  | KW_READONLY                           { FNATTR_Readonly         }
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
  | KW_SSPREQ                             { FNATTR_Sspreq           }
  | KW_SSPSTRONG                          { FNATTR_Sspstrong        }
  | KW_STRICTFP                           { FNATTR_Strictfp         }
  | KW_UWTABLE                            { FNATTR_Uwtable          }
  | KW_NOCF_CHECK                         { FNATTR_Nocf_check       }
  | KW_SHADOWCALLSTACK                    { FNATTR_Shadowcallstack  }
  | KW_MUSTPROGRESS                       { FNATTR_Mustprogress     }
  | s=STRING                              { FNATTR_String (str s)   }
  | k=STRING EQ v=STRING                  { FNATTR_Key_value (str k, str v) }
  | i=ATTR_GRP_ID                         { FNATTR_Attr_grp i       }

align: KW_ALIGN p=INTEGER { p }

section: KW_SECTION s=STRING { s }

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
  | KW_OR   { Or   }
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

conversion:
  | KW_TRUNC    { Trunc    }
  | KW_ZEXT     { Zext     }
  | KW_SEXT     { Sext     }
  | KW_FPTRUNC  { Fptrunc  }
  | KW_FPEXT    { Fpext    }
  | KW_UITOFP   { Uitofp   }
  | KW_SITOFP   { Sitofp   }
  | KW_FPTOUI   { Fptoui   }
  | KW_FPTOSI   { Fptosi   }
  | KW_INTTOPTR { Inttoptr }
  | KW_PTRTOINT { Ptrtoint }
  | KW_BITCAST  { Bitcast  }

ibinop:
  | op=ibinop_nuw_nsw_opt nuw=KW_NUW? nsw=KW_NSW?
    { op (nuw <> None) (nsw <> None) }
  (* allow `nsw` to be first *)
  | op=ibinop_nuw_nsw_opt KW_NSW nuw=KW_NUW?
    { op (nuw <> None) true }
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
  | KW_FAST { Fast }

instr_op:
  | op=ibinop t=typ o1=exp COMMA o2=exp
    { OP_IBinop (op, t, o1 t, o2 t) }

  | KW_ICMP op=icmp t=typ o1=exp COMMA o2=exp
    { OP_ICmp (op, t, o1 t, o2 t) }

  | op=fbinop f=fast_math* t=typ o1=exp COMMA o2=exp
    { OP_FBinop (op, f, t, o1 t, o2 t) }

  | KW_FCMP op=fcmp t=typ o1=exp COMMA o2=exp
    { OP_FCmp (op, t, o1 t, o2 t) }

  | c=conversion t1=typ v=exp KW_TO t2=typ
    { OP_Conversion (c, t1, v t1, t2) }

  | KW_GETELEMENTPTR KW_INBOUNDS? t=typ COMMA ptr=texp idx=preceded(COMMA, texp)*
    { OP_GetElementPtr (t, ptr, idx) }

  | KW_SELECT if_=texp COMMA then_=texp COMMA else_= texp
    { OP_Select (if_, then_, else_) }

  | KW_FREEZE v=texp
    { OP_Freeze v }

  | KW_EXTRACTELEMENT vec=texp COMMA idx=texp
    { OP_ExtractElement (vec, idx) }

  | KW_INSERTELEMENT vec=texp
    COMMA new_el=texp COMMA idx=texp
    { OP_InsertElement (vec, new_el, idx)  }

  | KW_EXTRACTVALUE tv=texp COMMA
    idx=separated_nonempty_list (csep, INTEGER)
    { OP_ExtractValue (tv, idx) }

  | KW_INSERTVALUE agg=texp COMMA new_val=texp COMMA
    idx=separated_nonempty_list (csep, INTEGER)
    { OP_InsertValue (agg, new_val, idx) }

  | KW_SHUFFLEVECTOR v1=texp COMMA v2=texp COMMA mask=texp
    { OP_ShuffleVector (v1, v2, mask)  }

expr_op:
  | op=ibinop LPAREN t=typ o1=exp COMMA typ o2=exp RPAREN
    { OP_IBinop (op, t, o1 t, o2 t) }

  | KW_ICMP op=icmp LPAREN t=typ o1=exp COMMA typ o2=exp RPAREN
    { OP_ICmp (op, t, o1 t, o2 t) }

  | op=fbinop f=fast_math* LPAREN t=typ o1=exp COMMA typ o2=exp RPAREN
    { OP_FBinop (op, f, t, o1 t, o2 t) }

  | KW_FCMP op=fcmp LPAREN t=typ o1=exp COMMA typ o2=exp RPAREN
    { OP_FCmp (op, t, o1 t, o2 t) }

  | c=conversion LPAREN t1=typ v=exp KW_TO t2=typ RPAREN
    { OP_Conversion (c, t1, v t1, t2) }

  | KW_GETELEMENTPTR KW_INBOUNDS? LPAREN t=typ COMMA ptr=texp idx=preceded(COMMA, texp)* RPAREN
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


expr_val:
  | i=INTEGER                                         { fun _ -> EXP_Integer i        }
  | f=FLOAT                                           { fun t -> normalize_float_literal t f }
  | f=HEXCONSTANT                                     { fun _ -> EXP_Hex f            }
  | KW_TRUE                                           { fun _ -> EXP_Bool true        }
  | KW_FALSE                                          { fun _ -> EXP_Bool false       }
  | KW_NULL                                           { fun _ -> EXP_Null             }
  | KW_UNDEF                                          { fun _ -> EXP_Undef            }
  | KW_ZEROINITIALIZER                                { fun _ -> EXP_Zero_initializer }
  | LCURLY l=separated_list(csep, tconst) RCURLY      { fun _ -> EXP_Struct l         }
  | LTLCURLY l=separated_list(csep, tconst) RCURLYGT  { fun _ -> EXP_Packed_struct l  }
  | LSQUARE l=separated_list(csep, tconst) RSQUARE    { fun _ -> EXP_Array l          }
  | LT l=separated_list(csep, tconst) GT              { fun _ -> EXP_Vector l         }
  | i=ident                                           { fun _ -> EXP_Ident i          }
  | KW_C cstr=STRING                                  { fun _ -> EXP_Cstring (
								     cstring_bytes_to_LLVM_i8_array
								     (unescape (str cstr))) }

exp:
  | eo=expr_op { fun _ -> eo }
  | ev=expr_val { ev }
  
%inline instr:
  | eo=instr_op { INSTR_Op eo }

  | KW_TAIL? KW_CALL cconv? list(param_attr) f=texp
    a=delimited(LPAREN, separated_list(csep, call_arg), RPAREN)
    list(fn_attr)
    { INSTR_Call (f, a) }

  | KW_ALLOCA t=typ opt=preceded(COMMA, alloca_opt)?
    { let (n, a) = match opt with Some x -> x | None -> (None, None) in
      INSTR_Alloca (t, n, a) }

  | KW_LOAD vol=KW_VOLATILE? t=typ COMMA tv=texp a=preceded(COMMA, align)?
    { INSTR_Load (vol<>None, t, tv, a) }


  | KW_VAARG  { failwith"INSTR_VAArg"  }
  | KW_LANDINGPAD    { failwith"INSTR_LandingPad"    }

  | KW_STORE vol=KW_VOLATILE? all=texp COMMA ptr=texp a=preceded(COMMA, align)?
    { INSTR_Store (vol<>None, all, ptr, a) }

  | KW_ATOMICCMPXCHG { failwith"INSTR_AtomicCmpXchg" }
  | KW_ATOMICRMW     { failwith"INSTR_AtomicRMW"     }
  | KW_FENCE         { failwith"INSTR_Fence"         }


branch_label:
  KW_LABEL o=LOCAL  { lexed_id_to_raw_id o }
  
terminator:  
  | KW_RET tv=texp
    { TERM_Ret tv }

  | KW_RET KW_VOID
    { TERM_Ret_void }

  | KW_BR c=texp COMMA o1=branch_label COMMA o2=branch_label
    { TERM_Br (c, o1, o2) }

  | KW_BR b=branch_label
    { TERM_Br_1 b }

  | KW_SWITCH c=texp COMMA
    def=branch_label LSQUARE EOL? table=list(switch_table_entry) RSQUARE
    { TERM_Switch (c, def, table) }

  | KW_INDIRECTBR tv=texp
    COMMA LSQUARE til=separated_list(csep, branch_label)  RSQUARE
    { TERM_IndirectBr (tv, til) }

  | KW_RESUME tv=texp
    { TERM_Resume tv }

  | KW_INVOKE cconv? ret=tident
    LPAREN a=separated_list(csep, call_arg) RPAREN
    list(fn_attr) KW_TO l1=branch_label KW_UNWIND l2=branch_label
    { TERM_Invoke (ret, a, l1, l2)  }

  | KW_UNREACHABLE
    { TERM_Unreachable }


alloca_opt:
  | a=align                           { (None, Some a) }
  | nb=texp a=preceded(COMMA, align)? { (Some nb, a) }


switch_table_entry:
  | sz=I x=INTEGER COMMA i=branch_label EOL? { (TInt_Literal(sz, x), i) }

csep:
  COMMA EOL* { () }


lident:
  | l=LOCAL  { (lexed_id_to_raw_id l) }

bound_lident:
  | l=LOCAL  { l }

gident:
  | g=GLOBAL  { (lexed_id_to_raw_id g) }

ident:
  | g=gident  { ID_Global g }
  | l=lident  { ID_Local  l }

texp:   t=typ v=exp { (t, v t) }
tconst: t=typ c=exp { (t, c t) }
tident: t=typ i=ident { (t, i) }

(* SAZ: Copying this here is a bit unfortunate but works for now.
   It might be better to experiment with eliminating the "inline" keyword
   for the instr nonterminal and then add a new nonterminal like this:
test_instr:
   instr EOF { ... }
*)
test_call:
  | KW_TAIL? KW_CALL cconv? list(param_attr) f=texp
    a=delimited(LPAREN, separated_list(csep, call_arg), RPAREN)
    list(fn_attr) EOF
    { INSTR_Call (f, a) }
