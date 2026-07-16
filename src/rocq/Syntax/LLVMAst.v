(* begin hide *)
From Stdlib Require Import
     Number Decimal Hexadecimal.
From Vellvm Require Import
     Utils.

Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
(* end hide *)


(** * VIR front AST

    Definition of the internal AST used to represent VIR programs. More
    specifically, this file contains the first representation produced by the
    (unverified) OCaml parser of surface IR syntax. In particular, this
    file defines the structure that a front end for a higher level language
    should target: [@toplevel_entities typ (block typ * list (block typ))]

    All changes to this file must naturally be mirrored in:
    - the parser:
       "/src/ml/libvellvm/llvm_parser.mly"
    - the Rocq Representation
       "/src/rocq/Syntax/ReprAST.v"
    - the prettyprinter
       "/src/rocq/Syntax/ShowAST.v"

 *)

(* [int_ast] - type used for internal numeric values. *)
Definition int_ast := Z.

(* Representation for parsed integer literals:
    - IntDecimal (Pos d)    for 1234
    - IntDecimal (Neg d)    for -1234
    - IntHexadecimal (Pos h) for u0x8000  is 32768
    - IntHexadecimal (Neg h) for s0x8000  is -32768
    NB: LLVM IR uses `u` and `s` to stand for "signed" and "unsigned" but maybe they
    mean "positive" and "negative"?  e.g. according to LangRef:

      "Note that hexadecimal integers are sign extended from the number of active
       bits, i.e., the bit width minus the number of leading zeros. So
       ‘s0x0001’ of type ‘i16’ will be -1, not 1."

   In many places we use
        [BinIntDef.Z.of_num_int x]
   to recover a [Z] from parsed syntax.
 *)
Definition int_syntax := Number.signed_int.


(* File Information - this is used by the Vellvm-only 
   METADATA_File_info "virtual" metadata value to record source information.
   Every phi, instr, and terminator is annotated with a file_info value provided
   by the parser.
   - These are never pretty printed via "show"
   - They *are* reflected via "repr"
   - They can be used to generate error messages: see examples in Denotation.v
   - See AstLib for some utility functions (especially [location_error_string])
 *)
Record file_info : Set :=
  mk_file_info {
      filename : string ;
      start_line : int_ast ;
      start_col  : int_ast ;
      end_line   : int_ast ;
      end_col    : int_ast ;
    }.


(* SAZ: NB - the [int_ast] of [Anon] could be [int_syntax], but that is annoying to work out. *)
Variant raw_id : Set :=
| Name (s:string)        (* Named identifiers are strings: %argc, %val, %x, @foo, @bar etc. *)
| Anon (n:int_ast)       (* Anonymous identifiers must be sequentially numbered %0, %1, %2, etc. *)
| Raw  (n:int_ast)       (* Used for code generation -- serializes as %_RAW_0 %_RAW_1 etc. *)
.

Variant ident : Set :=
| ID_Global (id:raw_id)   (* @id *)
| ID_Local  (id:raw_id)   (* %id *)
.


(* Floating point variants *)
Variant floating_point_variant : Set :=
| FP_half       (* 16-bit IEEE 754 binary 16 *)
| FP_bfloat     (* 16-bit with 7-bit significand *)
| FP_float      (* 32-bit IEEE 754 binary 32 *)
| FP_double     (* 64-bit IEEE 754 binary 64 *)
| FP_fp128      (* 128-bit IEEE 754 binary 128 *)
| FP_x86_fp80   (* 80-bit x87 floating-point-value *)
| FP_ppc_fp128  (* 128-bit floating-point value (two 64-bits) ? *)
.  

Scheme Equality for floating_point_variant.

Unset Elimination Schemes.
Inductive typ : Set :=
| TYPE_I (sz:positive)
| TYPE_Iptr
| TYPE_Pointer (t: option typ)
| TYPE_Void
| TYPE_FP (fp:floating_point_variant)
| TYPE_Label  (* type of block labels *)
| TYPE_Token  (* used with exceptions *)
| TYPE_Metadata
| TYPE_X86_mmx
| TYPE_Array (sz:N) (t:typ)
| TYPE_Function (ret:typ) (args:list typ) (vararg:bool)
                (* Langref doesn't specify that "..." appears only at the end of the arguments,
                   but I believe it is implied *)
| TYPE_Struct (fields:list typ)
| TYPE_Packed_struct (fields:list typ)
| TYPE_Opaque
| TYPE_Vector (sz:N) (t:typ)     (* t must be integer, floating point, or pointer type *)
| TYPE_Identified (id:ident)     
.

Variant linkage : Set :=
| LINKAGE_Private
| LINKAGE_Internal
| LINKAGE_Available_externally
| LINKAGE_Linkonce
| LINKAGE_Weak
| LINKAGE_Common
| LINKAGE_Appending
| LINKAGE_Extern_weak
| LINKAGE_Linkonce_odr
| LINKAGE_Weak_odr
| LINKAGE_External
.

Variant preemption_specifier : Set :=
  | PREEMPTION_Dso_preemptable
  | PREEMPTION_Dso_local
.


Variant dll_storage : Set :=
| DLLSTORAGE_Dllimport
| DLLSTORAGE_Dllexport
.

Variant visibility : Set :=
| VISIBILITY_Default
| VISIBILITY_Hidden
| VISIBILITY_Protected
.

Variant cconv : Set :=
| CC_Ccc
| CC_Fastcc
| CC_Coldcc
| CC_Cc (cc:int_syntax)
| CC_Webkit_jscc
| CC_Anyregcc
| CC_Preserve_mostcc
| CC_Preserve_allcc
| CC_Cxx_fast_tlscc
| CC_Tailcc
| CC_Swiftcc
| CC_Swifttailcc
| CC_cfguard_checkcc
.

Variant param_attr : Set :=
| PARAMATTR_Zeroext
| PARAMATTR_Signext
| PARAMATTR_Inreg
| PARAMATTR_Byval (t : typ)
| PARAMATTR_Byref (t : typ)
| PARAMATTR_Preallocated (t : typ)
| PARAMATTR_Inalloca (t : typ)
| PARAMATTR_Sret (t : typ)
| PARAMATTR_Elementtype (t : typ)
| PARAMATTR_Align (a:int_syntax)
| PARAMATTR_Noalias
| PARAMATTR_Nocapture
| PARAMATTR_Nofree
| PARAMATTR_Nest
| PARAMATTR_Returned
| PARAMATTR_Nonnull
| PARAMATTR_Dereferenceable (a:int_syntax)
| PARAMATTR_Dereferenceable_or_null (a : int_syntax)
| PARAMATTR_Swiftself
| PARAMATTR_Swiftasync
| PARAMATTR_Swifterror
| PARAMATTR_Immarg
| PARAMATTR_Noundef
(* | PARAMATTR_Nofpclass (* MISSING: floating point class *) *) 
| PARAMATTR_Alignstack (a : int_syntax)
| PARAMATTR_Allocalign
| PARAMATTR_Allocptr
| PARAMATTR_Readnone      
| PARAMATTR_Readonly  
| PARAMATTR_Writeonly
| PARAMATTR_Writable
| PARAMATTR_Dead_on_unwind      
| PARAMATTR_Range (t : typ) (a b : int_syntax)
| PARAMATTR_Initializes (l : list (int_syntax * int_syntax))
.

Variant frame_pointer_val : Set :=
| FRAMEPTR_None
| FRAMEPTR_Non_leaf
| FRAMEPTR_All
.

Variant mem_loc : Set :=
| LOC_Default
| LOC_Argmem
| LOC_Inaccessiblemem
| LOC_Errnomem
.

Variant mem_access_kind : Set :=
| ACC_None
| ACC_Read      
| ACC_Write
| ACC_Readwrite
.
    
Variant fn_attr : Set :=
| FNATTR_Alignstack (a:int_syntax)
(* | FNATTR_Alloc_family (fam : string) - FNATTR_KeyValue *)
| FNATTR_Allockind (kind : string)
| FNATTR_Allocsize (a1 : int_syntax) (a2 : option int_syntax)
| FNATTR_Alwaysinline
| FNATTR_Builtin
| FNATTR_Cold
| FNATTR_Convergent
| FNATTR_Disable_sanitizer_instrumentation
(* | FNATTR_Dontcall_error - FNATTR_String *)
(* | FNATTR_Dontcall_warn - FNATTR_String *)
| FNATTR_Fn_ret_thunk_extern
(* | FNATTR_Frame_pointer - FNATTR_KeyValue *)
| FNATTR_Hot
| FNATTR_Inaccessiblememonly
| FNATTR_Inaccessiblemem_or_argmemonly
| FNATTR_Inlinehint
| FNATTR_Jumptable
| FNATTR_Minsize
| FNATTR_Naked
(* | FNATTR_No_inline_line_tables - FNATTR_String *)
| FNATTR_No_jump_tables
| FNATTR_Nobuiltin
| FNATTR_Noduplicate
| FNATTR_Nofree
| FNATTR_Noimplicitfloat
| FNATTR_Noinline
| FNATTR_Nomerge
| FNATTR_Nonlazybind
| FNATTR_Noprofile
| FNATTR_Noredzone
| FNATTR_Indirect_tls_seg_refs
| FNATTR_Noreturn
| FNATTR_Norecurse
| FNATTR_Willreturn
| FNATTR_Nosync
| FNATTR_Nounwind
| FNATTR_Nosanitize_bounds
| FNATTR_Nosanitize_coverage
| FNATTR_Null_pointer_is_valid
| FNATTR_Optforfuzzing
| FNATTR_Optnone
| FNATTR_Optsize
(* | FNATTR_Patchable_function - FNATTR_KeyValue *)
(* | FNATTR_Probe_stack - FNATTR_String *)
| FNATTR_Readnone
| FNATTR_Readonly
(* | FNATTR_Stack_probe_size - FNATTR_KeyValue *)
(* | FNATTR_No_stack_arg_probe  - FNATTR_String *)
| FNATTR_Writeonly
| FNATTR_Argmemonly
| FNATTR_Returns_twice
| FNATTR_Safestack
| FNATTR_Sanitize_address
| FNATTR_Sanitize_memory
| FNATTR_Sanitize_thread
| FNATTR_Sanitize_hwaddress
| FNATTR_Sanitize_memtag
| FNATTR_Speculative_load_hardening
| FNATTR_Speculatable
| FNATTR_Ssp
| FNATTR_Sspstrong
| FNATTR_Sspreq
| FNATTR_Strictfp
(* | FNATTR_Denormal_fp_math (s1 : string) (s2 : option string)  - FNATTR_KeyValue *)
(* | FNATTR_Denormal_fp_math_f32 (s1 : string) (s2 : option string) - FNATTR_KeyValue *)
(* | FNATTR_Thunk - FNATTR_String *)
| FNATTR_Tls_load_hoist
| FNATTR_Uwtable (sync : option bool)   (* None ~ Some False ~ async, Some true = sync *)
| FNATTR_Nocf_check
| FNATTR_Shadowcallstack
| FNATTR_Mustprogress
(* | FNATTR_Warn_stack_size (th : int) - FNATTR_KeyValue *)
| FNATTR_Vscale_range (min : int_syntax) (max : option int_syntax)
(* | FNATTR_Min_legal_vector_width  (size : int_syntax) - FNATTR_KeyValue *)
| FNATTR_String (s:string)   (* See the comments above for cases covered by FNATTR_String *)
| FNATTR_Key_value (kv : string * string) (* See the comments above for cases covered by FNATTR_KeyValue *)
| FNATTR_Attr_grp (g:int_ast)
(* This memory attribute is just a syntactic representation of the constraints. *)                    
| FNATTR_Memory (effs: list (mem_loc * mem_access_kind))
| FNATTR_UNKNOWN (s:string)
.

Variant thread_local_storage : Set :=
| TLS_NONE (* tls is optional *)  
| TLS_Localdynamic
| TLS_Initialexec
| TLS_Localexec
.

(* auxiliary definitions for when we know which case we're in already *)
Definition local_id  := raw_id.
Definition global_id := raw_id.
Definition block_id := raw_id.
Definition function_id := global_id.


(* NOTE:
   We could separate return types from types, but that needs mutually recursive types.
   This would entail a lot of down-stream changes to the semantics, but might simplify or
   eliminate some corner cases.

   ```
    Inductive type : Set :=
      ...
    with
    rtyp : Set :=
    | RTYPE_Void
    | RTYPE_Typ (t:typ)
   ```
*)

Set Elimination Schemes.

Variant icmp : Set := Eq|Ne|Ugt|Uge|Ult|Ule|Sgt|Sge|Slt|Sle.
Variant fcmp : Set := FFalse|FOeq|FOgt|FOge|FOlt|FOle|FOne|FOrd|FUno|FUeq|FUgt|FUge|FUlt|FUle|FUne|FTrue.

Variant ibinop : Set :=
| Add (nuw:bool) (nsw:bool)
| Sub (nuw:bool) (nsw:bool)
| Mul (nuw:bool) (nsw:bool)
| Shl (nuw:bool) (nsw:bool)
| UDiv (exact:bool)
| SDiv (exact:bool)
| LShr (exact:bool)
| AShr (exact:bool)
| URem | SRem | And | Or (disjoint:bool) | Xor
.

Variant fbinop : Set :=
  FAdd | FSub | FMul | FDiv | FRem.

Variant fast_math : Set :=
  Nnan | Ninf | Nsz | Arcp | Contract | Afn | Reassoc | Fast.

(* Pure conversions - cannot interact with the memory model. *)
Variant pure_conversion : Set :=
| Trunc (nuw:bool) (nsw:bool)
| Zext (nneg:bool)
| Sext
| Fptrunc (flags:list fast_math)
| Fpext (flags:list fast_math)
| Uitofp (nneg:bool)
| Sitofp | Fptoui | Fptosi 
.

(* Impure conversions - might interact with the memory model.
   NB: Addrspacecast might be "pure" but I included it here
   since it *might* interact with the memory model.
 *)
Variant impure_conversion : Set :=
  | Inttoptr | Ptrtoint | Ptrtoaddr | Addrspacecast.

Variant conversion_type : Set :=
  | CONV_Bitcast    (* kept separate because it does not work on vectors *)
  | CONV_Pure (c : pure_conversion)
  | CONV_Impure (c : impure_conversion)
.
                
Section TypedSyntax.

  Context {T:Set}.

  Definition tident : Set := (T * ident)%type.


(* NOTES:
  This datatype is more permissive than legal in LLVM:
     - it allows identifiers to appear nested inside of "constant expressions"
       that is OK as long as we validate the syntax as "well-formed" before
       trying to give it semantics

  NOTES:
   - Integer expressions: llc parses large integer exps and converts them to some
     internal form (based on integer size?)

   - Float constants: these are always parsed as 64-bit representable floats
     using ocamls float_of_string function. The parser converts float literals
     to 32-bit values using the type information available in the syntax.

     -- TODO: 128-bit, 16-bit, other float formats?

   - Hex constants: these are always parsed as 0x<16-digit> 64-bit exps and
     bit-converted to ocaml's 64-bit float representation.  If they are
     evaluated at 32-bit float types, they are converted during evaluation.

   - EXP_ prefix denotes syntax that LLVM calls a "value"
   - OP_  prefix denotes syntax that requires further evaluation
 *)

Unset Elimination Schemes.



(* Representation for parse float literals *)
Variant float_hex_type :=
  | FH_X (* 0xABCD0000ABCD0000 Should be 16 digits, but is also used for bfloat, half, float and double? *)
  | FH_K (* 0xKABCD0000ABCD0000ABCD Should be 20 digits. used for x86 *)
  | FH_L (* 0xL...  Should be 32 digits. used for f128 *)
  | FH_M (* 0xMABCD0000ABCD0000ABCD0000ABCD0000 Should be 32 digits. used for power pc *)
  | FH_H (* 0xHABCD Should be 4 digits. used for half  *)
  | FH_R (* 0xRABCD should be 4 digits. used for bfloat "brain float" *)
  .

Variant float_syntax :=
  | FS_decimal (d:Decimal.decimal)  (* 123.45    -23.45e-17 etc.  *)
  | FS_hex (t:float_hex_type) (u:Hexadecimal.uint).

Inductive exp : Set :=
| EXP_Ident   (id:ident)
| EXP_Integer (x:int_syntax)
| EXP_Float   (f:float_syntax)  
| EXP_Bool    (b:bool)
| EXP_Null
| EXP_Zero_initializer
    (* change type of Cstring to string *)
| EXP_Cstring         (elts: list (T * exp))
                      (* parsing guarantees that the elts of a Cstring will be of the form
                         ((TYPE_I 8), Exp_Integer (IntDecimal (Pos <byte>)))
                      *)

(* [undef] is still accepted by the parser, but the minimal semantics has no
   dedicated undef value: [EXP_Undef] is denoted semantically as [poison]
   (see [denote_exp] in Semantics/Denotation.v). *)
| EXP_Undef
| EXP_Poison
| EXP_Struct          (fields: list (T * exp))
| EXP_Packed_struct   (fields: list (T * exp))
| EXP_Array           (t:T) (elts: list (T * exp))
| EXP_Vector          (t:T) (elts: list (T * exp))
| OP_IBinop           (iop:ibinop) (t:T) (v1:exp) (v2:exp)
| OP_ICmp             (samesign:bool) (cmp:icmp)   (t:T) (v1:exp) (v2:exp)
| OP_FBinop           (fop:fbinop) (fm:list fast_math) (t:T) (v1:exp) (v2:exp)
| OP_Fneg             (flags:list fast_math) (v:(T * exp))
| OP_FCmp             (cmp:fcmp)   (t:T) (v1:exp) (v2:exp)
| OP_Conversion       (conv:conversion_type) (t_from:T) (v:exp) (t_to:T)
| OP_GetElementPtr    (t:T) (ptrval:(T * exp)) (idxs:list (T * exp))
| OP_ExtractElement   (vec:(T * exp)) (idx:(T * exp))
| OP_InsertElement    (vec:(T * exp)) (elt:(T * exp)) (idx:(T * exp))
| OP_ShuffleVector    (vec1:(T * exp)) (vec2:(T * exp)) (idxmask:(T * exp))
| OP_ExtractValue     (vec:(T * exp)) (idxs:list int_syntax)
| OP_InsertValue      (vec:(T * exp)) (elt:(T * exp)) (idxs:list int_syntax)
| OP_Select           (cnd:(T * exp)) (v1:(T * exp)) (v2:(T * exp)) (* if * then * else *)
| OP_Freeze           (v:(T * exp))
| EXP_Asm             (sideffect:bool) (alignstack:bool) (inteldialect:bool) (unwind:bool) (template:string) (operand_constraints:string)
| EXP_Metadata        (m:metadata)
| EXP_Splat           (elt:(T * exp))
                      
with metadata : Set :=
(* METADATA_Id covers all metadata values of the form:
    !id (without quotes), including, !invariant.load  !nontemporal, etc.
    !"llvm.loop.unroll", (with quotes)
    !0, !1, !2
   Following the same conventions as for other identifiers
    - Anon is for numbers
    - Name is for others, but the string includes quotes  
*)
| METADATA_Null   (* Annoying edge case -- no ! needed *)
| METADATA_Id     (id:raw_id)  
| METADATA_Const  (tv:T * exp)
| METADATA_Node   (mds:list metadata)
| METADATA_Pair   (md1 md2:metadata)  (* adjacent elements in instruction metadata *)
                  
(* DI Metadata introduced completely new lexical conventions for "structured" debug
   metadata.  Vellvm doesn't do anything interesting with this metadata (yet),
   so we simply parse it in a way that preserves the information.

   METADATA_Debug represents a !DI<str>(<contents>) metadata node tag
   and its contents represented as a string.
   For example
      !DIExpression(DW_OP_deref, DW_OP_constu, 3, DW_OP_plus, DW_OP_LLVM_fragment, 3, 7)

   would be represented as:
      METADATA_Debug ("Expression", "DW_OP_deref, DW_OP_constu, 3, DW_OP_plus, DW_OP_LLVM_fragment, 3, 7")

   Note that there is no parsing of the inner contents (but balanced parens are enforced), so
      !DIExpression(2, 3, !DIExpression(1, !DIExpression()))

   would be represented as:
      METADATA_Debug ("Expression", "2, 3, !DIExpression(1, !DIExpression())")
 *)
| METADATA_Debug (DIstr:string) (contents:string)

(* SAZ: hijack the metadata to add Vellvm line numbers - this will be added by the parser but
   elided in the prettyprinter.
   We can use this to improve the error messages by providing more context.
 *)
| METADATA_File_info (finfo:file_info)
.
Set Elimination Schemes.

Definition texp : Set := T * exp.

(* Used in switch branches which insist on integer literals *)
Variant tint_literal : Set :=
  | TInt_Literal (sz:positive) (x:int_syntax).

Variant instr_id : Set :=
  | IId   (id:raw_id)    (* "Anonymous" or explicitly named instructions *)
  | IVoid (n:int_ast)    (* "Void" return type, for "store",  "void call", and terminators.
                            Each with unique number (NOTE: these are distinct from Anon raw_id) *)
.

Variant phi : Set :=
  | Phi  (t:T) (args:list (block_id * exp))
.

Variant ordering : Set :=
  | Unordered
  | Monotonic
  | Acquire
  | Release
  | Acq_rel
  | Seq_cst
.

Record cmpxchg : Set :=
  mk_cmpxchg {
      c_weak              : option unit;
      c_volatile          : option unit;
      c_ptr               : texp;
      c_cmp               : texp;
      c_new               : texp;
      c_syncscope            : option string;
      c_success_ordering     : ordering;
      c_failure_ordering     : ordering;
      c_align                : option int_syntax;
    }.

Variant atomic_rmw_operation : Set :=
  | Axchg
  | Aadd
  | Asub
  | Aand
  | Anand
  | Aor
  | Axor
  | Amax
  | Amin
  | Aumax
  | Aumin
  | Afadd
  | Afsub
  | Afmax
  | Afmin
  | Afmaximum
  | Afminimum
  | Auinc_wrap
  | Audec_wrap
  | Ausub_cond
  | Ausub_sat
.

Record atomicrmw : Set :=
  mk_atomicrmw {
      a_volatile             : option unit;
      a_operation            : atomic_rmw_operation;
      a_ptr                  : texp;
      a_val                  : texp;
      a_syncscope            : option string;
      a_ordering             : ordering;
      a_align                : option int_syntax;
    }.



Variant unnamed_addr : Set :=
  | Unnamed_addr
  | Local_Unnamed_addr
.

Variant tailcall : Set :=
  | Tail
  | Musttail
  | Notail
.

(* LLVM has many optional attributes and annotations for global values,
   declarations, and definitions.  This type collects together these options so
   that they can be represented as a single list of features.  We call these
   "annotations".  Some annotations (such as prefix) are applicable only to
   function declarations or definitions, but we collect them all here
   for a more uniform treatment.
*)
Variant annotation : Set :=
  | ANN_linkage (l:linkage)
  | ANN_preemption_specifier (p:preemption_specifier)
  | ANN_visibility (v:visibility)
  | ANN_dll_storage (d:dll_storage)
  | ANN_thread_local_storage (t:thread_local_storage)
  | ANN_unnamed_addr (u:unnamed_addr)
  | ANN_addrspace (n:int_syntax)
  | ANN_section (s:string)
  | ANN_partition (s:string)
  | ANN_comdat (l:local_id)
  | ANN_align (n:int_syntax)
  | ANN_no_sanitize
  | ANN_no_sanitize_address
  | ANN_no_sanitize_hwaddress
  | ANN_sanitize_address_dyninit
  | ANN_metadata (l: list metadata)  
  | ANN_cconv (c:cconv) (* declaration / definitions only *)
  | ANN_gc (s:string) (* declaration / definitions only *)
  | ANN_prefix (t:texp) (* declaration / definitions only *)
  | ANN_prologue (t:texp) (* declaration / definitions only *)
  | ANN_personality (t:texp) (* declaration / definitions only *)
  | ANN_inalloca  (* alloca instruction only *)
  | ANN_num_elements (t:texp) (* alloca instruction only *)
  | ANN_volatile (* load / store *)
  | ANN_tail (t:tailcall)
  | ANN_fast_math_flag (f:fast_math)
  | ANN_ret_attribute (p:param_attr)
  | ANN_fun_attribute (f:fn_attr)
  | ANN_atomic
  | ANN_syncscope (s:string)
  | ANN_ordering (o:ordering)                       
.

Definition ann_linkage (a:annotation) : option linkage :=
  match a with
  | ANN_linkage l => Some l
  | _ => None
  end.

Definition ann_preemption_specifier (a:annotation) : option preemption_specifier :=
  match a with
  | ANN_preemption_specifier p => Some p
  | _ => None
  end.

Definition ann_visibility (a:annotation) : option visibility :=
  match a with
  | ANN_visibility v => Some v
  | _ => None
  end.

Definition ann_dll_storage (a:annotation) : option dll_storage :=
  match a with
  | ANN_dll_storage d => Some d
  | _ => None
  end.

Definition ann_thread_local_storage (a:annotation) : option thread_local_storage :=
  match a with
  | ANN_thread_local_storage t => Some t
  | _ => None
  end.

Definition ann_unnamed_addr (a:annotation) : option unnamed_addr :=
  match a with
  | ANN_unnamed_addr a => Some a
  | _ => None
  end.

Definition ann_addrspace (a:annotation) : option int_syntax :=
  match a with
  | ANN_addrspace a => Some a
  | _ => None
  end.

Definition ann_section (a:annotation) : option string :=
  match a with
  | ANN_section s => Some s
  | _ => None
  end.

Definition ann_partition (a:annotation) : option string :=
  match a with
  | ANN_partition p => Some p
  | _ => None
  end.

Definition ann_comdat (a:annotation) : option local_id :=
  match a with
  | ANN_comdat s => Some s
  | _ => None
  end.

Definition ann_align (a:annotation) : option int_syntax :=
  match a with
  | ANN_align n => Some n
  | _ => None
  end.

Definition ann_no_sanitize (a:annotation) : option unit :=
  match a with
  | ANN_no_sanitize => Some tt
  | _ => None
  end.

Definition ann_no_sanitize_address (a:annotation) : option unit :=
  match a with
  | ANN_no_sanitize_address => Some tt
  | _ => None
  end.

Definition ann_no_sanitize_hwaddress (a:annotation) : option unit :=
  match a with
  | ANN_no_sanitize_hwaddress => Some tt
  | _ => None
  end.

Definition ann_sanitize_address_dynint (a:annotation) : option unit :=
  match a with
  | ANN_sanitize_address_dyninit => Some tt
  | _ => None
  end.

Definition ann_metadata (a:annotation) : option (list metadata) :=
  match a with
  | ANN_metadata l => Some l
  | _ => None
  end.

Definition ann_cconv (a:annotation) : option cconv :=
  match a with
  | ANN_cconv c => Some c
  | _ => None
  end.

Definition ann_gc (a:annotation) : option string :=
  match a with
  | ANN_gc s => Some s
  | _ => None
  end.

Definition ann_prefix (a:annotation) : option texp :=
  match a with
  | ANN_prefix t => Some t
  | _ => None
  end.

Definition ann_prologue (a:annotation) : option texp :=
  match a with
  | ANN_prologue t => Some t
  | _ => None
  end.

Definition ann_personality (a:annotation) : option texp :=
  match a with
  | ANN_personality t => Some t
  | _ => None
  end.

Definition ann_inalloca (a:annotation) : option unit :=
  match a with
  | ANN_inalloca => Some tt
  | _ => None
  end.

Definition ann_num_elements (a:annotation) : option texp :=
  match a with
  | ANN_num_elements t => Some t
  | _ => None
  end.

Definition ann_volatile (a:annotation) : option unit :=
  match a with
  | ANN_volatile => Some tt
  | _ => None
  end.

Definition ann_tail (a:annotation) : option tailcall :=
  match a with
  | ANN_tail t => Some t
  | _ => None
  end.

Definition ann_fast_math_flag (a:annotation) : option fast_math :=
  match a with
  | ANN_fast_math_flag f => Some f
  | _ => None
  end.

Definition ann_ret_attribute (a:annotation) : option param_attr :=
  match a with
  | ANN_ret_attribute p => Some p
  | _ => None
  end.

Definition ann_fun_attribute (a:annotation) : option fn_attr :=
  match a with
  | ANN_fun_attribute f => Some f
  | _ => None
  end.

Definition ann_atomic (a:annotation) : option unit :=
  match a with
  | ANN_atomic => Some tt
  | _ => None
  end.

Definition ann_syncscope (a:annotation) : option string :=
  match a with
  | ANN_syncscope s => Some s
  | _ => None
  end.

Definition ann_ordering (a:annotation) : option ordering :=
  match a with
  | ANN_ordering o => Some o
  | _ => None
  end.

(* Operand Bundles
   - Note: does not support `preallocated(%foo)` style bundles.
 *)

Variant operand :=
  | SSA_value (t:texp)
  | Metadata_string (m:metadata).

Record operand_bundle :=
  mk_operand_bundle {
      ob_tag : string ;
      ob_ops : list operand 
    }.

Variant landingpad_clause :=
  | CATCH (t : texp)
  | FILTER (t : texp).

Variant instr : Set :=
| INSTR_Comment (msg:string)
| INSTR_Op   (op:exp) (* INVARIANT: op must be of the form (OP_ ...) *)
| INSTR_Call (fn:texp) (args:list (texp * (list param_attr))) (anns:list annotation) (obs : list operand_bundle)   (* CORNER CASE: return type is void treated specially *)
| INSTR_Alloca (t:T) (anns: list annotation)
| INSTR_Load  (t:T) (ptr:texp) (anns: list annotation)
| INSTR_Store (val:texp) (ptr:texp) (anns: list annotation)
| INSTR_Fence (syncscope:option string) (o:ordering)
| INSTR_AtomicCmpXchg (c : cmpxchg)
| INSTR_AtomicRMW (a :atomicrmw )
| INSTR_VAArg (va_list_and_arg_list : texp) (t: T) (* arg_list isn't actually a list, this is just the name of the argument  *)
| INSTR_LandingPad (resultty:T) (cleanup:bool) (cs:list landingpad_clause)
.

Variant terminator : Set :=
(* Terminators *)
(* Types in branches are TYPE_Label constant *)
| TERM_Ret        (v:texp)
| TERM_Ret_void
| TERM_Br         (v:texp) (br1:block_id) (br2:block_id)
| TERM_Br_1       (br:block_id)
| TERM_Switch     (v:texp) (default_dest:block_id) (brs: list (tint_literal * block_id))
| TERM_IndirectBr (v:texp) (brs:list block_id) (* address * possible addresses (labels) *)
| TERM_Resume     (v:texp)

| TERM_Invoke  (fnptrval:texp) (args:list (texp * (list param_attr))) (to_label:block_id) (unwind_label:block_id) (anns:list annotation) (obs : list operand_bundle)
| TERM_Unreachable
.


Record global : Set :=
  mk_global {
      g_ident        : global_id;
      g_typ          : T;
      g_constant     : bool;              (* true = constant, false = global *)
      g_exp          : option exp;     (* InitializerConstant *)
      g_externally_initialized: bool;
      g_alias        : bool;              (* Is this an Alias? see: https://llvm.org/docs/LangRef.html#aliases *)
      g_annotations : list annotation  (* Invariant: the list of annotations is in the same order as is valid for the LLVM IR grammar *)
}.

Definition g_linkage (g:global) : option linkage :=
  find_option ann_linkage (g_annotations g).

Definition g_visibility (g:global) : option visibility :=
  find_option ann_visibility (g_annotations g).

Definition g_dll_storage (g:global) : option dll_storage :=
  find_option ann_dll_storage (g_annotations g).

Definition g_thread_local_storage (g:global) : option thread_local_storage :=
  find_option ann_thread_local_storage (g_annotations g).

Definition g_unnamed_addr (g:global) : option unnamed_addr :=
  find_option ann_unnamed_addr (g_annotations g).

Definition g_addrspace (g:global) : option int_syntax :=
  find_option ann_addrspace (g_annotations g).

Definition g_section (g:global) : option string :=
  find_option ann_section (g_annotations g).

Definition g_partition (g:global) : option string :=
  find_option ann_partition (g_annotations g).

Definition g_comdat (g:global) : option local_id :=
  find_option ann_comdat (g_annotations g).

Definition g_align (g:global) : option int_syntax :=
  find_option ann_align (g_annotations g).

Definition g_no_sanitize (g:global) : option unit :=
  find_option ann_no_sanitize (g_annotations g).

Definition g_no_sanitize_address (g:global) : option unit :=
  find_option ann_no_sanitize_address (g_annotations g).

Definition g_no_sanitize_hwaddress (g:global) : option unit :=
  find_option ann_no_sanitize_hwaddress (g_annotations g).

Definition g_sanitize_address_dyninit (g:global) : option unit :=
  find_option ann_sanitize_address_dynint (g_annotations g).

Definition g_metadata (g:global) : (list (list metadata)) :=
  filter_option ann_metadata (g_annotations g).

Record declaration : Set :=
  mk_declaration
  {
    dc_name         : function_id;
    dc_type         : T;    (* INVARIANT: should be TYPE_Function (ret_t * args_t * vararg) *)
    dc_param_attrs  : list param_attr * list (list param_attr); (* ret_attrs * args_attrs *)
    dc_attrs        : list fn_attr;
    dc_annotations  : list annotation
  }.

Definition dc_linkage (d:declaration) : option linkage :=
  find_option ann_linkage (dc_annotations d).

Definition dc_visibility (d:declaration) : option visibility :=
  find_option ann_visibility (dc_annotations d).

Definition dc_dll_storage (d:declaration) : option dll_storage :=
  find_option ann_dll_storage (dc_annotations d).

Definition dc_thread_local_storage (d:declaration) : option thread_local_storage :=
  find_option ann_thread_local_storage (dc_annotations d).

Definition dc_unnamed_addr (d:declaration) : option unnamed_addr :=
  find_option ann_unnamed_addr (dc_annotations d).

Definition dc_addrspace (d:declaration) : option int_syntax :=
  find_option ann_addrspace (dc_annotations d).

Definition dc_section (d:declaration) : option string :=
  find_option ann_section (dc_annotations d).

Definition dc_partition (d:declaration) : option string :=
  find_option ann_partition (dc_annotations d).

Definition dc_comdat (d:declaration) : option local_id :=
  find_option ann_comdat (dc_annotations d).

Definition dc_align (d:declaration) : option int_syntax :=
  find_option ann_align (dc_annotations d).

Definition dc_cconv (d:declaration) : option cconv :=
  find_option ann_cconv (dc_annotations d).

Definition dc_gc (d:declaration) : option string :=
  find_option ann_gc (dc_annotations d).

Definition dc_prefix (d:declaration) : option texp :=
  find_option ann_prefix (dc_annotations d).

Definition dc_prologue (d:declaration) : option texp :=
  find_option ann_prologue (dc_annotations d).

Definition dc_personality (d:declaration) : option texp :=
  find_option ann_personality (dc_annotations d).

Definition dc_metadata (d:declaration) : list (list metadata) :=
  filter_option ann_metadata (dc_annotations d).

Definition code := list (instr_id * instr * (list metadata)).

Record block : Set :=
  mk_block
    {
      blk_id    : block_id;
      blk_phis  : list (local_id * phi * (list metadata));
      blk_code  : code;
      blk_term  : instr_id * terminator * (list metadata);
      blk_comments : option (list string)
    }.

Record definition {FnBody:Set} :=
  mk_definition
  {
    df_prototype   : declaration;
    df_args        : list local_id;
    df_instrs      : FnBody;
  }.


Variant toplevel_entity {FnBody:Set} : Set :=
| TLE_Comment         (msg:string)
| TLE_Target          (tgt:string)
| TLE_Datalayout      (layout:string)
| TLE_Declaration     (decl:declaration)
| TLE_Definition      (defn:@definition FnBody)
| TLE_Type_decl       (id:ident) (t:T)
| TLE_Source_filename (s:string)
| TLE_Global          (g:global)
| TLE_Metadata        (id:metadata) (distinct:bool) (md:metadata)
| TLE_Attribute_group (i:int_ast) (attrs:list fn_attr)
.

Definition toplevel_entities (FnBody:Set) : Set := list (@toplevel_entity FnBody).

End TypedSyntax.

Arguments exp: clear implicits.
Arguments cmpxchg : clear implicits.
Arguments atomicrmw : clear implicits.
Arguments block: clear implicits.
Arguments texp: clear implicits.
Arguments phi: clear implicits.
Arguments instr: clear implicits.
Arguments terminator: clear implicits.
Arguments code: clear implicits.
Arguments annotation: clear implicits.
Arguments global: clear implicits.
Arguments declaration: clear implicits.
Arguments definition: clear implicits.
Arguments metadata: clear implicits.
Arguments toplevel_entity: clear implicits.
Arguments toplevel_entities: clear implicits.
