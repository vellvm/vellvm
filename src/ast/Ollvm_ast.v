(* {{{ LICENSE                                                              *
  * vi: set fdm=marker fdl=0:                                                *
  *                                                                          *
  * Copyright (c) 2012 Raphaël Proust <raphlalou@gmail.com>                  *
  * Copyright (c) 2012 INRIA - Raphaël Proust <raphlalou@gmail.com>          *
  * Copyright (c) 2012 ENS - Raphaël Proust <raphlalou@gmail.com>            *
  * Copyright (c) 2014 OCamlPro - Julien Sagot <ju.sagot@gmail.com>          *
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
  * }}}                                                                      

  Ported from ollvm_ast.ml
  Copyright (c) 2016 Steve Zdancewic <stevez@cis.upenn.edu>
*)

Require Import List. 
Require Import String Ascii.
Open Scope string_scope.
Open Scope list_scope.

Parameter int : Set.
Parameter float : Set.

Inductive linkage : Set :=
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
      
Inductive dll_storage : Set :=
| DLLSTORAGE_Dllimport
| DLLSTORAGE_Dllexport
.      

Inductive visibility : Set :=
| VISIBILITY_Default
| VISIBILITY_Hidden
| VISIBILITY_Protected
.
    
Inductive cconv : Set :=
| CC_Ccc
| CC_Fastcc
| CC_Coldcc
| CC_Cc (cc:int)
.
        
Inductive param_attr : Set :=
| PARAMATTR_Zeroext
| PARAMATTR_Signext
| PARAMATTR_Inreg
| PARAMATTR_Byval
| PARAMATTR_Inalloca
| PARAMATTR_Sret
| PARAMATTR_Align (a:int)
| PARAMATTR_Noalias
| PARAMATTR_Nocapture
| PARAMATTR_Nest
| PARAMATTR_Returned
| PARAMATTR_Nonnull
| PARAMATTR_Dereferenceable (a:int)
.
                            
Inductive fn_attr : Set :=
| FNATTR_Alignstack (a:int)
| FNATTR_Alwaysinline
| FNATTR_Builtin
| FNATTR_Cold
| FNATTR_Inlinehint
| FNATTR_Jumptable
| FNATTR_Minsize
| FNATTR_Naked
| FNATTR_Nobuiltin
| FNATTR_Noduplicate
| FNATTR_Noimplicitfloat
| FNATTR_Noinline
| FNATTR_Nonlazybind
| FNATTR_Noredzone
| FNATTR_Noreturn
| FNATTR_Nounwind
| FNATTR_Optnone
| FNATTR_Optsize
| FNATTR_Readnone
| FNATTR_Readonly
| FNATTR_Returns_twice
| FNATTR_Sanitize_address
| FNATTR_Sanitize_memory
| FNATTR_Sanitize_thread
| FNATTR_Ssp
| FNATTR_Sspreq
| FNATTR_Sspstrong
| FNATTR_Uwtable
| FNATTR_String (s:string) (* "no-see" *)
| FNATTR_Key_value (kv : string * string) (* "unsafe-fp-math"="false" *)
| FNATTR_Attr_grp (g:int)
.


Inductive raw_id : Set :=
| Name (s:string)     (* Named identifiers are strings: %argc, %val, %x, etc. *)  
| Anon (n:int)        (* Anonymous identifiers must be sequentially numbered %0, %1, %2, etc. *)
.
       
Inductive ident : Set :=
| ID_Global (id:raw_id)   (* @id *)
| ID_Local  (id:raw_id)   (* %id *)
.
              
Inductive typ : Set :=
| TYPE_I (sz:int)
| TYPE_Pointer (t:typ)
| TYPE_Void
| TYPE_Half
| TYPE_Float
| TYPE_Double
| TYPE_X86_fp80
| TYPE_Fp128
| TYPE_Ppc_fp128
| TYPE_Label
| TYPE_Metadata
| TYPE_X86_mmx
| TYPE_Array (sz:int) (t:typ)
| TYPE_Function (ret:typ) (args:list typ)
| TYPE_Struct (fields:list typ)
| TYPE_Packed_struct (fields:list typ)
| TYPE_Opaque
| TYPE_Vector (sz:int) (t:typ)
| TYPE_Identified (id:ident)
.


Inductive icmp : Set := Eq|Ne|Ugt|Uge|Ult|Ule|Sgt|Sge|Slt|Sle.
Inductive fcmp : Set := FFalse|FOeq|FOgt|FOge|FOlt|FOle|FOne|FOrd|FUno|FUeq|FUgt|FUge|FUlt|FUle|FUne|FTrue.


Inductive ibinop : Set :=
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

Inductive fbinop : Set :=
  FAdd | FSub | FMul | FDiv | FRem.

Inductive fast_math : Set :=
  Nnan | Ninf | Nsz | Arcp | Fast.

Inductive conversion_type : Set :=
  Trunc | Zext | Sext | Fptrunc | Fpext | Uitofp | Sitofp | Fptoui |
  Fptosi | Inttoptr | Ptrtoint | Bitcast.

Definition tident : Set := (typ * ident)%type.


(* NOTES: 

  This is the "functorial" presentation of the syntax.  Note that the 'value' type 
  declared below actually creates the fixpoint.  Setting things up this way means 
  that we can re-use this functor for defining the dynamic values (over in
  StepSemantics.v) but we have to do some work to define appropriate induction
  principles (see AstInd.v).

  This datatype is more permissive than legal in LLVM:
     - it allows identifiers to appear nested inside of "constant expressions"

  TODO:
   Integer values should be OCaml int64 or some other machine-word compatible thing.
 *)
Inductive Expr (a:Set) : Set :=
| VALUE_Ident   (id:ident)  
| VALUE_Integer (x:int)
| VALUE_Float   (f:float)
| VALUE_Bool    (b:bool)
| VALUE_Null
| VALUE_Zero_initializer
| VALUE_Cstring (s:string)
| VALUE_None                                       (* "token" constant *)
| VALUE_Undef
| VALUE_Struct        (fields: list (typ * a))
| VALUE_Packed_struct (fields: list (typ * a))
| VALUE_Array         (elts: list (typ * a))
| VALUE_Vector        (elts: list (typ * a))
| OP_IBinop           (iop:ibinop) (t:typ) (v1:a) (v2:a)  
| OP_ICmp             (cmp:icmp)   (t:typ) (v1:a) (v2:a)
| OP_FBinop           (fop:fbinop) (fm:list fast_math) (t:typ) (v1:a) (v2:a)
| OP_FCmp             (cmp:fcmp)   (t:typ) (v1:a) (v2:a)
| OP_Conversion       (conv:conversion_type) (t_from:typ) (v:a) (t_to:typ)
| OP_GetElementPtr    (t:typ) (ptrval:(typ * a)) (idxs:list (typ * a))
| OP_ExtractElement   (vec:(typ * a)) (idx:(typ * a))
| OP_InsertElement    (vec:(typ * a)) (elt:(typ * a)) (idx:(typ * a))
| OP_ShuffleVector    (vec1:(typ * a)) (vec2:(typ * a)) (idxmask:(typ * a))
| OP_ExtractValue     (vec:(typ * a)) (idxs:list int)
| OP_InsertValue      (vec:(typ * a)) (elt:(typ * a)) (idxs:list int)
| OP_Select           (cnd:(typ * a)) (v1:(typ * a)) (v2:(typ * a)) (* if * then * else *)
.

(* static values *)
Inductive value : Set :=
| SV : Expr value -> value.
            
Definition tvalue : Set := typ * value.

Inductive instr_id : Set :=
| IId   (id:raw_id)    (* Anonymous or explicitly named instructions *)
| IVoid (n:int)        (* "Void" return type, each with unique number (NOTE: these are distinct from Anon raw_id)*)
.
        
Inductive instr : Set :=
| INSTR_Op   (op:value)                          (* INVARIANT: op must be of the form SV (OP_ ...) *)
| INSTR_Call (fn:tident) (args:list tvalue)      (* CORNER CASE: return type is void treated specially *)

| INSTR_Phi  (t:typ) (args:list (value * ident))

| INSTR_Alloca (t:typ) (nb: option tvalue) (align:option int) 
| INSTR_Load  (volatile:bool) (t:typ) (ptr:tvalue) (align:option int)       
| INSTR_Store (volatile:bool) (val:tvalue) (ptr:tvalue) (align:option int)
| INSTR_Fence
| INSTR_AtomicCmpXchg
| INSTR_AtomicRMW

(* Terminators *)
(* Types in branches are TYPE_Label constant *)
| INSTR_Invoke     (fnptrval:tident) (args:list tvalue) (to_label:tident) (unwind_label:tident)
| INSTR_Ret        (v:tvalue)
| INSTR_Ret_void
| INSTR_Br         (v:tvalue) (br1:tident) (br2:tident) 
| INSTR_Br_1       (br:tident)
| INSTR_Switch     (v:tvalue) (default_dest:tident) (brs: list (tvalue * tident))
| INSTR_IndirectBr (v:tvalue) (brs:list tident) (* address * possible addresses (labels) *)
| INSTR_Resume     (v:tvalue)

| INSTR_Unreachable

| INSTR_VAArg
| INSTR_LandingPad
.

Inductive thread_local_storage : Set :=
| TLS_Localdynamic
| TLS_Initialexec
| TLS_Localexec
.

Record global : Set :=
  mk_global {
      g_ident: ident;
      g_typ: typ;
      g_constant: bool;
      g_value: option value;

      g_linkage: option linkage;
      g_visibility: option visibility;
      g_dll_storage: option dll_storage;
      g_thread_local: option thread_local_storage;
      g_unnamed_addr: bool;
      g_addrspace: option int;
      g_externally_initialized: bool;
      g_section: option string;
      g_align: option int;
}.

Record declaration : Set :=
  mk_declaration
  {
    dc_name        : ident;  (* SAZ: could be raw_id since this should always be an ID_Global *)
    dc_type        : typ;    (* INVARIANT: should be TYPE_Function (ret_t * args_t) *)
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

Definition block_label : Set := raw_id.
        
Definition block : Set := block_label * list (instr_id * instr).

Record definition :=
  mk_definition
  {
    df_prototype   : declaration;
    df_args        : list ident;
    df_instrs      : list block;
  }.

Inductive metadata : Set :=
  | METADATA_Const  (tv:tvalue)
  | METADATA_Null
  | METADATA_Id     (id:raw_id)
  | METADATA_String (str:string)
  | METADATA_Named  (strs:list string)
  | METADATA_Node   (mds:list metadata)
.

Inductive toplevel_entity : Set :=
| TLE_Target          (tgt:string)
| TLE_Datalayout      (layout:string)
| TLE_Declaration     (decl:declaration)
| TLE_Definition      (defn:definition)
| TLE_Type_decl       (id:ident) (t:typ)
| TLE_Source_filename (s:string)
| TLE_Global          (g:global)
| TLE_Metadata        (id:raw_id) (md:metadata)
| TLE_Attribute_group (i:int) (attrs:list fn_attr)
.

Record modul : Set :=
  mk_modul
  {
    m_name: string;
    m_target: toplevel_entity;
    m_datalayout: toplevel_entity;
    m_globals: list (string * global);
    m_declarations: list (string * declaration);
    m_definitions: list (string * definition);
  }.


Definition toplevel_entities : Set := list toplevel_entity.
