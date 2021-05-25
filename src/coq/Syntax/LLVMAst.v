(* begin hide *)
Require Import Floats.
From Coq Require Import List String Ascii ZArith.
From Vellvm Require Import
     Utilities.

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

    All changes to this file must naturally be mirrored in the parser.
    "/src/ml/libvellvm/llvm_parser.mly"

*)

Definition int := Z.
Definition float := Floats.float.  (* 64-bit floating point value *)
Definition float32 := Floats.float32.

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
| CC_Cc (cc:int)
.

Variant param_attr : Set :=
| PARAMATTR_Zeroext
| PARAMATTR_Signext
| PARAMATTR_Inreg
| PARAMATTR_Byval
| PARAMATTR_Inalloca
| PARAMATTR_Sret
| PARAMATTR_Align (a:int)
| PARAMATTR_Noalias
| PARAMATTR_Nocapture
| PARAMATTR_Readonly
| PARAMATTR_Nest
| PARAMATTR_Returned
| PARAMATTR_Nonnull
| PARAMATTR_Dereferenceable (a:int)
| PARAMATTR_Immarg
| PARAMATTR_Noundef
| PARAMATTR_Nofree
.

Variant fn_attr : Set :=
| FNATTR_Alignstack (a:int)
| FNATTR_Allocsize  (l:list int)                    
| FNATTR_Alwaysinline
| FNATTR_Builtin
| FNATTR_Cold
| FNATTR_Convergent
| FNATTR_Hot
| FNATTR_Inaccessiblememonly
| FNATTR_Inaccessiblemem_or_argmemonly
| FNATTR_Inlinehint
| FNATTR_Jumptable
| FNATTR_Minsize
| FNATTR_Naked
| FNATTR_No_jump_tables
| FNATTR_Nobuiltin
| FNATTR_Noduplicate
| FNATTR_Nofree    
| FNATTR_Noimplicitfloat
| FNATTR_Noinline
| FNATTR_Nomerge    
| FNATTR_Nonlazybind
| FNATTR_Noredzone
| FNATTR_Indirect_tls_seg_refs
| FNATTR_Noreturn
| FNATTR_Norecurse
| FNATTR_Willreturn
| FNATTR_Nosync    
| FNATTR_Nounwind
| FNATTR_Null_pointer_is_valid
| FNATTR_Optforfuzzing    
| FNATTR_Optnone
| FNATTR_Optsize
| FNATTR_Readnone
| FNATTR_Readonly
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
| FNATTR_Sspreq
| FNATTR_Sspstrong
| FNATTR_Strictfp    
| FNATTR_Uwtable
| FNATTR_Nocf_check
| FNATTR_Shadowcallstack
| FNATTR_Mustprogress    
| FNATTR_String (s:string) (* "no-see" *)
| FNATTR_Key_value (kv : string * string) (* "unsafe-fp-math"="false" *)
| FNATTR_Attr_grp (g:int)
.

Variant thread_local_storage : Set :=
| TLS_Localdynamic
| TLS_Initialexec
| TLS_Localexec
.

Variant raw_id : Set :=
| Name (s:string)     (* Named identifiers are strings: %argc, %val, %x, @foo, @bar etc. *)
| Anon (n:int)        (* Anonymous identifiers must be sequentially numbered %0, %1, %2, etc. *)
| Raw  (n:int)        (* Used for code generation -- serializes as %_RAW_0 %_RAW_1 etc. *)
.

Variant ident : Set :=
| ID_Global (id:raw_id)   (* @id *)
| ID_Local  (id:raw_id)   (* %id *)
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

Unset Elimination Schemes.
Inductive typ : Set :=
| TYPE_I (sz:N)
| TYPE_Pointer (t:typ)
| TYPE_Void
| TYPE_Half
| TYPE_Float
| TYPE_Double
| TYPE_X86_fp80
| TYPE_Fp128
| TYPE_Ppc_fp128
(* | TYPE_Label  label is not really a type *)
(* | TYPE_Token -- used with exceptions *)
| TYPE_Metadata
| TYPE_X86_mmx
| TYPE_Array (sz:N) (t:typ)
| TYPE_Function (ret:typ) (args:list typ)
| TYPE_Struct (fields:list typ)
| TYPE_Packed_struct (fields:list typ)
| TYPE_Opaque
| TYPE_Vector (sz:N) (t:typ)     (* t must be integer, floating point, or pointer type *)
| TYPE_Identified (id:ident)
.
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
| URem | SRem | And | Or | Xor
.

Variant fbinop : Set :=
  FAdd | FSub | FMul | FDiv | FRem.

Variant fast_math : Set :=
  Nnan | Ninf | Nsz | Arcp | Fast.

Variant conversion_type : Set :=
  Trunc | Zext | Sext | Fptrunc | Fpext | Uitofp | Sitofp | Fptoui |
  Fptosi | Inttoptr | Ptrtoint | Bitcast.

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

Inductive exp : Set :=
| EXP_Ident   (id:ident)
| EXP_Integer (x:int)
| EXP_Float   (f:float32)  (* 32-bit floating point values *)
| EXP_Double  (f:float)    (* 64-bit floating point values *)
| EXP_Hex     (f:float)    (* See LLVM documentation about hex float constants. *)
| EXP_Bool    (b:bool)
| EXP_Null
| EXP_Zero_initializer
| EXP_Cstring         (elts: list (T * exp))
                      (* parsing guarantees that the elts of a Cstring will be of the form
                         ((TYPE_I 8), Exp_Integer <byte>)
                      *)

| EXP_Undef
| EXP_Struct          (fields: list (T * exp))
| EXP_Packed_struct   (fields: list (T * exp))
| EXP_Array           (elts: list (T * exp))
| EXP_Vector          (elts: list (T * exp))
| OP_IBinop           (iop:ibinop) (t:T) (v1:exp) (v2:exp)
| OP_ICmp             (cmp:icmp)   (t:T) (v1:exp) (v2:exp)
| OP_FBinop           (fop:fbinop) (fm:list fast_math) (t:T) (v1:exp) (v2:exp)
| OP_FCmp             (cmp:fcmp)   (t:T) (v1:exp) (v2:exp)
| OP_Conversion       (conv:conversion_type) (t_from:T) (v:exp) (t_to:T)
| OP_GetElementPtr    (t:T) (ptrval:(T * exp)) (idxs:list (T * exp))
| OP_ExtractElement   (vec:(T * exp)) (idx:(T * exp))
| OP_InsertElement    (vec:(T * exp)) (elt:(T * exp)) (idx:(T * exp))
| OP_ShuffleVector    (vec1:(T * exp)) (vec2:(T * exp)) (idxmask:(T * exp))
| OP_ExtractValue     (vec:(T * exp)) (idxs:list int)
| OP_InsertValue      (vec:(T * exp)) (elt:(T * exp)) (idxs:list int)
| OP_Select           (cnd:(T * exp)) (v1:(T * exp)) (v2:(T * exp)) (* if * then * else *)
| OP_Freeze           (v:(T * exp))
.

Set Elimination Schemes.

Definition texp : Set := T * exp.

(* Used in switch branches which insist on integer literals
   
*)
Variant tint_literal : Set :=
  | TInt_Literal (sz:N) (x:int).

Variant instr_id : Set :=
| IId   (id:raw_id)    (* "Anonymous" or explicitly named instructions *)
| IVoid (n:int)        (* "Void" return type, for "store",  "void call", and terminators.
                           Each with unique number (NOTE: these are distinct from Anon raw_id) *)
.

Variant phi : Set :=
| Phi  (t:T) (args:list (block_id * exp))
.

Variant instr : Set :=
| INSTR_Comment (msg:string)
| INSTR_Op   (op:exp)                        (* INVARIANT: op must be of the form (OP_ ...) *)
| INSTR_Call (fn:texp) (args:list texp)      (* CORNER CASE: return type is void treated specially *)
| INSTR_Alloca (t:T) (nb: option texp) (align:option int)
| INSTR_Load  (volatile:bool) (t:T) (ptr:texp) (align:option int)
| INSTR_Store (volatile:bool) (val:texp) (ptr:texp) (align:option int)
| INSTR_Fence
| INSTR_AtomicCmpXchg
| INSTR_AtomicRMW
| INSTR_VAArg
| INSTR_LandingPad
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
| TERM_Invoke     (fnptrval:tident) (args:list texp) (to_label:block_id) (unwind_label:block_id)
| TERM_Unreachable
.


Record global : Set :=
  mk_global {
      g_ident        : global_id;
      g_typ          : T;
      g_constant     : bool;
      g_exp          : option exp;
      g_linkage      : option linkage;
      g_visibility   : option visibility;
      g_dll_storage  : option dll_storage;
      g_thread_local : option thread_local_storage;
      g_unnamed_addr : bool;
      g_addrspace    : option int;
      g_externally_initialized: bool;
      g_section      : option string;
      g_align        : option int;
}.

Record declaration : Set :=
  mk_declaration
  {
    dc_name        : function_id;
    dc_type        : T;    (* INVARIANT: should be TYPE_Function (ret_t * args_t) *)
    dc_param_attrs : list param_attr * list (list param_attr); (* ret_attrs * args_attrs *)
    dc_linkage     : option linkage;
    dc_visibility  : option visibility;
    dc_dll_storage : option dll_storage;
    dc_cconv       : option cconv;
    dc_attrs       : list fn_attr;
    dc_section     : option string;
    dc_align       : option int;
    dc_gc          : option string;
  }.


Definition code := list (instr_id * instr).

Record block : Set :=
  mk_block
    {
      blk_id    : block_id;
      blk_phis  : list (local_id * phi);
      blk_code  : code;
      blk_term  : terminator;
      blk_comments : option (list string)
    }.

Record definition {FnBody:Set} :=
  mk_definition
  {
    df_prototype   : declaration;
    df_args        : list local_id;
    df_instrs      : FnBody;
  }.

Inductive metadata : Set :=
  | METADATA_Const  (tv:texp)
  | METADATA_Null
  | METADATA_Id     (id:raw_id)  (* local or global? *)
  | METADATA_String (str:string)
  | METADATA_Named  (strs:list string)
  | METADATA_Node   (mds:list metadata)
.

Variant toplevel_entity {FnBody:Set} : Set :=
| TLE_Comment         (msg:string)
| TLE_Target          (tgt:string)
| TLE_Datalayout      (layout:string)
| TLE_Declaration     (decl:declaration)
| TLE_Definition      (defn:@definition FnBody)
| TLE_Type_decl       (id:ident) (t:T)
| TLE_Source_filename (s:string)
| TLE_Global          (g:global)
| TLE_Metadata        (id:raw_id) (md:metadata)
| TLE_Attribute_group (i:int) (attrs:list fn_attr)
.

Definition toplevel_entities (FnBody:Set) : Set := list (@toplevel_entity FnBody).

End TypedSyntax.

Arguments exp: clear implicits.
Arguments block: clear implicits.
Arguments texp: clear implicits.
Arguments phi: clear implicits.
Arguments instr: clear implicits.
Arguments terminator: clear implicits.
Arguments code: clear implicits.
Arguments global: clear implicits.
Arguments declaration: clear implicits.
Arguments definition: clear implicits.
Arguments metadata: clear implicits.
Arguments toplevel_entity: clear implicits.
Arguments toplevel_entities: clear implicits.

