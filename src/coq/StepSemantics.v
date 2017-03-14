Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.AstLib Vellvm.CFG.
Import ListNotations.
Open Scope positive_scope.

Set Implicit Arguments.
Set Contextual Implicit.

(* The set of dynamic values manipulated by an LLVM program. This datatype
   uses the "Expr" functor from the Ollvm_ast definition, injecting new base values.
   This allows the semantics to do 'symbolic' execution for things that we don't 
   have a way of interpreting concretely (e.g. undef).   
*)
Inductive dvalue : Set :=
| DV : Expr dvalue -> dvalue
| DVALUE_CodePointer (p : path)
| DVALUE_Addr (a:nat)
.  


Definition env  := list (local_id * dvalue).

Inductive frame : Set :=
| KRet      (e:env) (id:local_id) (q:path)
| KRet_void (e:env) (q:path)
.       
          
Definition stack := list frame.
Definition state := (path * env * stack)%type.


Definition init_state (CFG:cfg) : state := (init CFG, [], []).

Definition def_id_of_path (p:path) : option local_id :=
  match ins p with
  | IId id => Some id
  | _ => None
  end.

Definition local_id_of_ident (i:ident) : option local_id :=
  match i with
  | ID_Global _ => None
  | ID_Local i => Some i
  end.


Definition lookup_env (e:env) (id:local_id) : option dvalue :=
  assoc RawID.eq_dec id e.


(* Arithmetic Operations ---------------------------------------------------- *)
(* TODO: implement LLVM semantics *)


Definition eval_iop iop v1 v2 :=
  match v1, v2 with
  | DV (VALUE_Integer _ i1), DV (VALUE_Integer _ i2) =>
    Some (DV (VALUE_Integer _
    match iop with
    | Add _ _ => (i1 + i2)
    | Sub _ _ => (i1 - i2)
    | Mul _ _ => (i1 * i2)
    | _ => 1
    end))
  | _, _ => None
  end.


Definition eval_icmp icmp v1 v2 :=
  match v1, v2 with
  | DV (VALUE_Integer _ i1), DV (VALUE_Integer _ i2) =>
    Some (DV (VALUE_Bool _
    match icmp with
    | Eq => Pos.eqb i1 i2
    | Ule => Pos.leb i1 i2
    |  _ => false 
    end))
  | _, _ => None
  end.

(*
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
*)

Definition eval_expr {A:Set} (f:env -> A -> option dvalue) (e:env) (o:Expr A) : option dvalue :=
  match o with
  | VALUE_Ident _ id => 
    'i <- local_id_of_ident id;
      lookup_env e i
  | VALUE_Integer _ x => Some (DV (VALUE_Integer _ x))
  | VALUE_Float _ x   => Some (DV (VALUE_Float _ x))
  | VALUE_Bool _ b    => Some (DV (VALUE_Bool _ b)) 
  | VALUE_Null _      => Some (DV (VALUE_Null _))
  | VALUE_Zero_initializer _ => Some (DV (VALUE_Zero_initializer _))
  | VALUE_Cstring _ s => Some (DV (VALUE_Cstring _ s))
  | VALUE_None _      => Some (DV (VALUE_None _))
  | VALUE_Undef _     => Some (DV (VALUE_Undef _))
  | VALUE_Struct _ fs =>
    'vs <- map_option (map_option_snd (f e)) fs;
     Some (DV (VALUE_Struct _ vs))
  | VALUE_Packed_struct _ fs =>
    'vs <- map_option (map_option_snd (f e)) fs;
     Some (DV (VALUE_Packed_struct _ vs))
    
  | VALUE_Array _ es =>
    'vs <- map_option (map_option_snd (f e)) es;
     Some (DV (VALUE_Array _ vs))
    
  | VALUE_Vector _ es =>
    'vs <- map_option (map_option_snd (f e)) es;
     Some (DV (VALUE_Vector _ vs))

  | OP_IBinop _ iop t op1 op2 =>
    'v1 <- f e op1;
    'v2 <- f e op2;
    (eval_iop iop) v1 v2

  | OP_ICmp _ cmp t op1 op2 => 
    'v1 <- f e op1;
    'v2 <- f e op2;
    (eval_icmp cmp) v1 v2

  | _ => None
  end.

Fixpoint eval_op (e:env) (o:value) : option dvalue :=
  match o with
  | SV o' => eval_expr eval_op e o'
  end.

Fixpoint jump (CFG:cfg) (p:path) (e_init:env) (e:env) ps (q:path) (k:stack) : option state :=
  match ps with
  | [] => Some (q, e, k)
  | (id, (INSTR_Phi _ ls))::rest => 
    match assoc Ident.eq_dec (ID_Local (bn p)) ls with
    | Some op => match eval_op e_init op with
                | Some dv => jump CFG p e_init ((id,dv)::e) rest q k
                | None => None
                end
    | None => None
    end
  | _ => None
  end.
