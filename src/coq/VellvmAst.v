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
                  
Inductive ident : Set :=
| ID_Global (id:string)
| ID_Local  (id:string)
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

Inductive fbinop : Set := FAdd|FSub|FMul|FDiv|FRem.

Inductive fast_math : Set := Nnan | Ninf | Nsz | Arcp | Fast.

Inductive conversion_type : Set := Trunc|Zext|Sext|Fptrunc|Fpext|Uitofp|Sitofp|Fptoui
                       |Fptosi|Inttoptr|Ptrtoint|Bitcast.

Definition tident : Set := (typ * ident)%type.

(** FIXME: should be split into const/value? *)
Inductive value : Set :=
| VALUE_Ident (id:ident)
| VALUE_Integer (x:int)
| VALUE_Float (f:float)
| VALUE_Bool (b:bool)
| VALUE_Null
| VALUE_Undef
| VALUE_Struct (fields: list (typ * value))
| VALUE_Packed_struct (fields: list (typ * value))
| VALUE_Array (elts: list (typ * value))
| VALUE_Vector (elts: list (typ * value))
| VALUE_Zero_initializer
.

Definition tvalue := (typ * value)%type.

Inductive instr : Set :=
| INSTR_IBinop (iop:ibinop) (t:typ) (v1:value) (v2:value)
| INSTR_ICmp (cmp:icmp) (t:typ) (v1:value) (v2:value)
| INSTR_FBinop (fop:fbinop) (fm:list fast_math) (t:typ) (v1:value) (v2:value)
| INSTR_FCmp (cmp:fcmp) (t:typ) (v1:value) (v2:value)
| INSTR_Conversion (conv:conversion_type) (t_from:typ) (v:value) (t_to:typ)
| INSTR_GetElementPtr (ptrval:tvalue) (idxs:list tvalue)
| INSTR_ExtractElement (vec:tvalue) (idx:value)
| INSTR_InsertElement (vec:tvalue) (elt:tvalue) (idx:tvalue)
| INSTR_ShuffleVector (vec1:tvalue) (vec2:tvalue) (idxmask:tvalue)
| INSTR_ExtractValue (vec:tvalue) (idxs:list int)
| INSTR_InsertValue (vec:tvalue) (elt:tvalue) (idxs:list int)
| INSTR_Call (fn:tident) (args:list tvalue)
| INSTR_Alloca (t:typ) (nb: option tvalue) (align:option int) (* typ, nb el, align *)
| INSTR_Load (volatile:bool) (ptr:tvalue) (align:option int) (* FIXME: use tident instead of value *)
| INSTR_Phi (t:typ) (args:list (value * ident))
| INSTR_Select (cnd:tvalue) (v1:tvalue) (v2:tvalue) (* if * then * else *)
| INSTR_VAArg
| INSTR_LandingPad
| INSTR_Store (volatile:bool) (val:tvalue) (ptr:tident) (align:option int)
| INSTR_Fence
| INSTR_AtomicCmpXchg
| INSTR_AtomicRMW

(* Terminators *)
| INSTR_Invoke (fnptrval:tident) (args:list tvalue) (to_label:tident) (unwind_label:tident)
| INSTR_Ret (v:tvalue)
| INSTR_Ret_void
| INSTR_Br (v:tvalue) (br1:tident) (br2:tident) (* types are constant *)
| INSTR_Br_1 of tident
| INSTR_Switch of tvalue * tident * (tvalue * tident) list
| INSTR_IndirectBr of tvalue * tident list (* address
                                            * possible addresses (labels) *)
| INSTR_Resume of tvalue
| INSTR_Unreachable

(* Special `assign` instruction:
 * not a real LLVM instruction, allow to bind an identifier to an instruction *)
| INSTR_Assign of ident * instr

and toplevelentry =
  | TLE_Target of string
  | TLE_Datalayout of string
  | TLE_Declaration of declaration
  | TLE_Definition of definition
  | TLE_Type_decl of (ident * typ)
  | TLE_Global of global
  | TLE_Metadata of string * metadata
  | TLE_Attribute_group of int * fn_attr list

and toplevelentries = toplevelentry list

and global = {
  g_ident: ident;
  g_typ: typ;
  g_constant: bool;
  g_value: value option;

  g_linkage: linkage option;
  g_visibility: visibility option;
  g_dll_storage: dll_storage option;
  g_thread_local: thread_local_storage option;
  g_unnamed_addr: bool;
  g_addrspace: int option;
  g_externally_initialized: bool;
  g_section: string option;
  g_align: int option;
}

and thread_local_storage = TLS_Localdynamic
                         | TLS_Initialexec
                         | TLS_Localexec

and declaration = {
  dc_name: ident;
  dc_type: typ; (* TYPE_Function (ret_t * args_t) *)

  (* ret_attrs * args_attrs *)
  dc_param_attrs: param_attr list * param_attr list list;
}

and definition = {
  df_prototype: declaration;
  df_args: ident list;
  df_instrs: block list;

  df_linkage: linkage option;
  df_visibility: visibility option;
  df_dll_storage: dll_storage option;
  df_cconv: cconv option;
  df_attrs: fn_attr list;
  df_section: string option;
  df_align: int option;
  df_gc: string option;
}

and block = string * instr list

and modul = {
  m_name: string;
  m_target: toplevelentry;
  m_datalayout: toplevelentry;
  m_globals: (string * global) list;
  m_declarations: (string * declaration) list;
  m_definitions: (string * definition) list;
}

Inductive metadata : Set :=
  | METADATA_Const (tv:tvalue)
  | METADATA_Null
  | METADATA_Id (id:string)
  | METADATA_String (str:string)
  | METADATA_Named (strs:list string)
  | METADATA_Node (mds:list metadata)
.
              