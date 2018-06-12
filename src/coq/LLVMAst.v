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
   }}}                                                                       *)
(*  ------------------------------------------------------------------------- *)
(* Adapted for use in Vellvm by Steve Zdancewic (c) 2017                      *)
(*  ------------------------------------------------------------------------- *)

Require Import compcert.lib.Floats.
Require Import List String Ascii ZArith.
Require Import Vellvm.Util.

Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Definition int := Z.
Definition float := Floats.float.  (* 64-bit floating point value *)

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
| PARAMATTR_Readonly
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
| Name (s:string)     (* Named identifiers are strings: %argc, %val, %x, @foo, @bar etc. *)  
| Anon (n:int)        (* Anonymous identifiers must be sequentially numbered %0, %1, %2, etc. *)
| Raw  (n:int)        (* Used for code generation -- serializes as %_RAW_0 %_RAW_1 etc. *)
.


(** Use hints to resolve all decision procedures we require **)
Hint Resolve string_dec.
Hint Resolve Integers.Int.eq_dec.
Hint Resolve Z.eq_dec.

Lemma raw_id_eq_dec: forall (r1 r2: raw_id), {r1 = r2} + {r1 <> r2}.
Proof.
  decide equality; auto.
Qed.

Hint Resolve raw_id_eq_dec.

Inductive ident : Set :=
| ID_Global (id:raw_id)   (* @id *)
| ID_Local  (id:raw_id)   (* %id *)
.


Theorem ident_eq_dec: forall (a b: ident), {a = b } + {a <> b}.
Proof.
  intros.
  decide equality; auto.
Qed.

Hint Resolve ident_eq_dec.

(* auxilliary definitions for when we know which case we're in already *)
Definition local_id  := raw_id.
Definition global_id := raw_id.
Definition block_id := raw_id.
Definition function_id := global_id.


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
(* | TYPE_Label  label is not really a type *)
(* | TYPE_Token -- used with exceptions *)    
| TYPE_Metadata
| TYPE_X86_mmx
| TYPE_Array (sz:int) (t:typ)
| TYPE_Function (ret:typ) (args:list typ)
| TYPE_Struct (fields:list typ)
| TYPE_Packed_struct (fields:list typ)
| TYPE_Opaque
| TYPE_Vector (sz:int) (t:typ)     (* t must be integer, floating point, or pointer type *)
| TYPE_Identified (id:ident)
.
Section typ_nested_ind.
  Variable P: typ -> Type.
  Hypothesis I: forall sz: int, P (TYPE_I sz).
  Hypothesis POINTER: forall (t: typ), P t ->
                        P (TYPE_Pointer t).
  Hypothesis VOID: P (TYPE_Void).
  Hypothesis HALF: P (TYPE_Half).
  Hypothesis FLOAT: P (TYPE_Float).
  Hypothesis DOUBLE: P (TYPE_Double).
  Hypothesis X86_fp80: P (TYPE_X86_fp80).
  Hypothesis FP128: P TYPE_Fp128.
  Hypothesis PPC_FP128: P TYPE_Ppc_fp128.
  Hypothesis METADATA: P (TYPE_Metadata).
  Hypothesis X86_mmx: P (TYPE_X86_mmx).
  Hypothesis ARRAY: forall (sz: int) (t: typ),
      P t -> P (TYPE_Array sz t).
  Hypothesis  FUNCTION: forall (ret: typ) (ts: list typ),
      P ret -> ForallListT P ts -> P (TYPE_Function ret ts).
  Hypothesis STRUCT: forall (ts: list typ),
      ForallListT P ts -> P (TYPE_Struct ts).
  Hypothesis PACKED: forall (ts: list typ),
      ForallListT P ts -> P (TYPE_Packed_struct ts).
  Hypothesis OPAQUE: P (TYPE_Opaque).
  Hypothesis VECTOR: forall (sz: int) (t: typ),
      P t -> P (TYPE_Vector sz t).
  Hypothesis IDENTIFIED: forall (id: ident), P (TYPE_Identified id).

    Check (Forall_cons).
    Check (Forall).
    Fixpoint typ_nested_ind (t: typ) : P t :=
      match t with
      | TYPE_I sz => I sz
      | TYPE_Pointer p => POINTER p (typ_nested_ind p)
      | TYPE_Void => VOID
      | TYPE_Half => HALF
      | TYPE_Float => FLOAT
      | TYPE_Double => DOUBLE
      | TYPE_X86_fp80 => X86_fp80
      | TYPE_Fp128 => FP128
      | TYPE_Ppc_fp128 => PPC_FP128
      | TYPE_Metadata => METADATA
      | TYPE_X86_mmx => X86_mmx
      | TYPE_Array sz t => ARRAY sz t (typ_nested_ind t)
      | TYPE_Function ret args =>
        let H := (fix fold (xs: list typ) : ForallListT P xs :=
                    match xs with
                    | nil => ForallListT_nil _
                    | cons x xs' =>
                      ForallListT_cons _ (typ_nested_ind x) (fold xs')
                    end) args
        in FUNCTION ret args (typ_nested_ind ret) H
      | TYPE_Struct ts =>
        let H := (fix fold (xs: list typ) : ForallListT P xs :=
                    match xs with
                    | nil => ForallListT_nil _
                    | cons x xs' =>
                      ForallListT_cons _ (typ_nested_ind x) (fold xs')
                    end) ts
        in STRUCT ts H
        
      | TYPE_Packed_struct ts =>
        let H := (fix fold (xs: list typ) : ForallListT P xs :=
                    match xs with
                    | nil => ForallListT_nil _
                    | cons x xs' =>
                      ForallListT_cons _ (typ_nested_ind x) (fold xs')
                    end) ts
        in PACKED ts H
        
      | TYPE_Opaque => OPAQUE
      | TYPE_Vector sz t =>  VECTOR sz t (typ_nested_ind t)
      | TYPE_Identified id => IDENTIFIED id
          
      end.
End typ_nested_ind.

(* If we can decide equality "pointwise" for every list element, then
we can decide list equality *)
Lemma pointwise_decide_list_equality_to_list_equality:
  forall {A: Type}
    (l1 l2: list A)
    (FORALL_DECEQ: ForallListT
                     (fun t1 : A => forall t2 : A, {t1 = t2} + {t1 <> t2}) l1),
    {l1 = l2} + {l1 <> l2}.
Proof.
  intros.
  generalize dependent l2.
  induction l1.
  - destruct l2; auto.
  - intros.
    destruct l2; auto.

    assert (ADEC: {a = a0} + {a <> a0}).
    inversion FORALL_DECEQ; subst.
    apply X.

    assert (LDEC: {l1 = l2} + {l1 <> l2}).
    inversion FORALL_DECEQ; subst.
    apply IHl1.
    auto.

    destruct ADEC; destruct LDEC; subst; auto;
      try (right; intros CONTRA; inversion CONTRA; auto; fail).
Qed.

    
    

Lemma type_eq_dec: forall (t1 t2: typ), {t1 = t2} + {t1 <> t2}.
Proof.
  induction t1 using typ_nested_ind;
     auto; destruct t2; auto; try discriminate.
  - assert (SZ_CASES: {sz = sz0} + {sz <> sz0}); auto.
    destruct SZ_CASES; subst; auto;
      try (right; intros CONTRA; inversion CONTRA; auto; fail).
    
  - destruct (IHt1 t2); subst; auto;
      try (right; intros CONTRA; inversion CONTRA; auto; fail).

  - assert (SZ_CASES: {sz = sz0} + {sz <> sz0}); auto.
    destruct (IHt1 t2); destruct SZ_CASES; subst; auto;
      try (right; intros CONTRA; inversion CONTRA; auto; fail).

    
  - assert (T1_CASES: {t1 = t2} + {t1 <> t2}).
    apply IHt1; auto.
    
    assert (LIST_EQ_CASES: {ts = args} + {ts <> args}).
    apply pointwise_decide_list_equality_to_list_equality; auto.

    destruct T1_CASES; destruct LIST_EQ_CASES; subst; auto;
      try (right; intros CONTRA; inversion CONTRA; auto; fail).

  - assert (LIST_EQ_CASES: {ts = fields} + {ts <> fields}).
    apply pointwise_decide_list_equality_to_list_equality; auto.
    destruct LIST_EQ_CASES; subst; auto;
      try (right; intros CONTRA; inversion CONTRA; auto; fail).
     
  - assert (LIST_EQ_CASES: {ts = fields} + {ts <> fields}).
    apply pointwise_decide_list_equality_to_list_equality; auto.
    destruct LIST_EQ_CASES; subst; auto;
      try (right; intros CONTRA; inversion CONTRA; auto; fail).

  - assert (SZ_CASES: {sz = sz0} + {sz <> sz0}); auto.
    assert (T_CASES: {t1 = t2} + {t1 <> t2}).
    auto.

    
    destruct SZ_CASES; destruct T_CASES; subst; auto;
      try (right; intros CONTRA; inversion CONTRA; auto; fail).
    
  - assert (ID_EQ: {id = id0} + {id <> id0}); auto.

    
    destruct ID_EQ; subst; auto;
      try (right; intros CONTRA; inversion CONTRA; auto; fail).
Qed.

Hint Resolve type_eq_dec.
    

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
  This datatype is more permissive than legal in LLVM:
     - it allows identifiers to appear nested inside of "constant expressions"

  NOTES:
   - Integer expressions: llc parses large integer exps and converts them to some 
     internal form (based on integer size?)
   
   - Float constants: these are always parsed as 64-bit representable floats 
     using ocamls float_of_string function.  If they are used in LLVM as 32-bit 
     rather than 64-bit floats, they are converted when evaluated.

   - Hex constants: these are always parsed as 0x<16-digit> 64-bit exps and
     bit-converted to ocaml's 64-bit float representation.

   - EXP_ prefix denotes syntax that LLVM calls a "value"
   - OP_  prefix denotes syntax that requires further evaluation
 *)
Inductive exp : Set :=
| EXP_Ident   (id:ident)  
| EXP_Integer (x:int)
| EXP_Float   (f:float)
| EXP_Hex     (f:float)  (* See LLVM documentation about hex float constants. *)
| EXP_Bool    (b:bool)
| EXP_Null
| EXP_Zero_initializer
| EXP_Cstring         (s:string)
| EXP_Undef
| EXP_Struct          (fields: list (typ * exp))
| EXP_Packed_struct   (fields: list (typ * exp))
| EXP_Array           (elts: list (typ * exp))
| EXP_Vector          (elts: list (typ * exp))
| OP_IBinop           (iop:ibinop) (t:typ) (v1:exp) (v2:exp)  
| OP_ICmp             (cmp:icmp)   (t:typ) (v1:exp) (v2:exp)
| OP_FBinop           (fop:fbinop) (fm:list fast_math) (t:typ) (v1:exp) (v2:exp)
| OP_FCmp             (cmp:fcmp)   (t:typ) (v1:exp) (v2:exp)
| OP_Conversion       (conv:conversion_type) (t_from:typ) (v:exp) (t_to:typ)
| OP_GetElementPtr    (t:typ) (ptrval:(typ * exp)) (idxs:list (typ * exp))
| OP_ExtractElement   (vec:(typ * exp)) (idx:(typ * exp))
| OP_InsertElement    (vec:(typ * exp)) (elt:(typ * exp)) (idx:(typ * exp))
| OP_ShuffleVector    (vec1:(typ * exp)) (vec2:(typ * exp)) (idxmask:(typ * exp))
| OP_ExtractValue     (vec:(typ * exp)) (idxs:list int)
| OP_InsertValue      (vec:(typ * exp)) (elt:(typ * exp)) (idxs:list int)
| OP_Select           (cnd:(typ * exp)) (v1:(typ * exp)) (v2:(typ * exp)) (* if * then * else *)
.

Definition texp : Set := typ * exp.

Inductive instr_id : Set :=
| IId   (id:raw_id)    (* "Anonymous" or explicitly named instructions *)
| IVoid (n:int)        (* "Void" return type, for "store",  "void call", and terminators.
                           Each with unique number (NOTE: these are distinct from Anon raw_id) *)
.

Inductive phi : Set :=
| Phi  (t:typ) (args:list (block_id * exp))
.
       
Inductive instr : Set :=
| INSTR_Op   (op:exp)                        (* INVARIANT: op must be of the form SV (OP_ ...) *)
| INSTR_Call (fn:texp) (args:list texp)      (* CORNER CASE: return type is void treated specially *)
| INSTR_Alloca (t:typ) (nb: option texp) (align:option int) 
| INSTR_Load  (volatile:bool) (t:typ) (ptr:texp) (align:option int)       
| INSTR_Store (volatile:bool) (val:texp) (ptr:texp) (align:option int)
| INSTR_Fence
| INSTR_AtomicCmpXchg
| INSTR_AtomicRMW
| INSTR_Unreachable
| INSTR_VAArg
| INSTR_LandingPad
.

Inductive terminator : Set :=
(* Terminators *)
(* Types in branches are TYPE_Label constant *)
| TERM_Ret        (v:texp)
| TERM_Ret_void
| TERM_Br         (v:texp) (br1:block_id) (br2:block_id) 
| TERM_Br_1       (br:block_id)
| TERM_Switch     (v:texp) (default_dest:block_id) (brs: list (texp * block_id))
| TERM_IndirectBr (v:texp) (brs:list block_id) (* address * possible addresses (labels) *)
| TERM_Resume     (v:texp)
| TERM_Invoke     (fnptrval:tident) (args:list texp) (to_label:block_id) (unwind_label:block_id)
.

Inductive thread_local_storage : Set :=
| TLS_Localdynamic
| TLS_Initialexec
| TLS_Localexec
.

Record global : Set :=
  mk_global {
      g_ident        : global_id;
      g_typ          : typ;
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


Definition code := list (instr_id * instr).

Record block : Set :=
  mk_block
    {
      blk_id    : block_id;
      blk_phis  : list (local_id * phi);
      blk_code  : code;
      blk_term  : instr_id * terminator;
    }.

Record definition (FnBody:Set) :=
  mk_definition
  {
    df_prototype   : declaration;
    df_args        : list local_id;
    df_instrs      : FnBody;
  }.

Arguments df_prototype {_} _.
Arguments df_args {_} _.
Arguments df_instrs {_} _.

Inductive metadata : Set :=
  | METADATA_Const  (tv:texp)
  | METADATA_Null
  | METADATA_Id     (id:raw_id)  (* local or global? *)
  | METADATA_String (str:string)
  | METADATA_Named  (strs:list string)
  | METADATA_Node   (mds:list metadata)
.

Inductive toplevel_entity (FnBody:Set) : Set :=
| TLE_Target          (tgt:string)
| TLE_Datalayout      (layout:string)
| TLE_Declaration     (decl:declaration)
| TLE_Definition      (defn:definition FnBody)
| TLE_Type_decl       (id:ident) (t:typ)
| TLE_Source_filename (s:string)
| TLE_Global          (g:global)
| TLE_Metadata        (id:raw_id) (md:metadata)
| TLE_Attribute_group (i:int) (attrs:list fn_attr)
.
Arguments TLE_Target {_} _.
Arguments TLE_Datalayout {_} _.
Arguments TLE_Declaration {_} _.
Arguments TLE_Definition {_} _.
Arguments TLE_Type_decl {_} _.
Arguments TLE_Source_filename {_} _.
Arguments TLE_Global {_} _.
Arguments TLE_Metadata {_} _.
Arguments TLE_Attribute_group {_} _ _.

Definition toplevel_entities (FnBody:Set) : Set := list (toplevel_entity FnBody).

Record modul (FnBody:Set) : Set :=
  mk_modul
  {
    m_name: option string;
    m_target: option string;
    m_datalayout: option string;
    m_type_defs: list (ident * typ);
    m_globals: list global;
    m_declarations: list declaration;
    m_definitions: list (definition FnBody);
  }.

Arguments m_name {_} _.
Arguments m_target {_} _.
Arguments m_datalayout {_} _.
Arguments m_type_defs {_} _.
Arguments m_globals {_} _.
Arguments m_declarations {_} _.
Arguments m_definitions {_} _.


