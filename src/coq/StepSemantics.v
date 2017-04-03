Require Import ZArith List String Omega.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Vellvm.Ollvm_ast Vellvm.AstLib Vellvm.CFG.
Import ListNotations.
Open Scope positive_scope.

Set Implicit Arguments.
Set Contextual Implicit.

Require Import Vellvm.Effects.

Module Type ADDR.
  Parameter addr : Set.
End ADDR.  

Module StepSemantics(A:ADDR).
  Module ET : Vellvm.Effects.EffT with Definition addr := A.addr with Definition typ := Ollvm_ast.typ.
    Definition addr := A.addr.
    Definition typ := Ollvm_ast.typ.
  End ET.    
  Module E := Vellvm.Effects.Effects(ET).
  Export E.

(* The set of dynamic values manipulated by an LLVM program. This datatype
   uses the "Expr" functor from the Ollvm_ast definition, injecting new base values.
   This allows the semantics to do 'symbolic' execution for things that we don't 
   have a way of interpreting concretely (e.g. undef).   
 *)
Inductive dvalue : Set :=
| DV : Expr dvalue -> dvalue
| DVALUE_CodePointer (p : path)
| DVALUE_Addr (a:addr)
.  

(* TODO: add the global environment *)
Definition genv := list (global_id * dvalue).
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

Definition eval_fop (fop:fbinop) (v1:dvalue) (v2:dvalue) : option dvalue := None.

Definition eval_fcmp (fcmp:fcmp) (v1:dvalue) (v2:dvalue) : option dvalue := None.

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

  | VALUE_Struct _ es =>
    'vs <- map_option (map_option_snd (f e)) es;
     Some (DV (VALUE_Struct _ vs))

  | VALUE_Packed_struct _ es =>
    'vs <- map_option (map_option_snd (f e)) es;
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

  | OP_FBinop _ fop fm t op1 op2 =>
    'v1 <- f e op1;
    'v2 <- f e op2;
    (eval_fop fop) v1 v2

  | OP_FCmp _ fcmp t op1 op2 => 
    'v1 <- f e op1;
    'v2 <- f e op2;
    (eval_fcmp fcmp) v1 v2
              
  | OP_Conversion _ conv t1 op t2 =>
    f e op    (* TODO: is conversion a no-op semantically? *)
      
  | OP_GetElementPtr _ t ptrval idxs =>
    'vptr <- map_option_snd (f e) ptrval;
    'vs <- map_option (map_option_snd (f e)) idxs;
    None  (* TODO: Getelementptr *)  
    
  | OP_ExtractElement _ vecop idx =>
    'vec <- map_option_snd (f e) vecop;
    'vidx <- map_option_snd (f e) idx;
    None (* TODO: Extract Element *)
      
  | OP_InsertElement _ vecop eltop idx =>
    'vec <- map_option_snd (f e) vecop;
    'v <- map_option_snd (f e) eltop;
    'vidx <- map_option_snd (f e) idx;
    None (* TODO *)
    
  | OP_ShuffleVector _ vecop1 vecop2 idxmask =>
    'vec1 <- map_option_snd (f e) vecop1;
    'vec2 <- map_option_snd (f e) vecop2;      
    'vidx <- map_option_snd (f e) idxmask;
    None (* TODO *)

  | OP_ExtractValue _ vecop idxs =>
    'vec <- map_option_snd (f e) vecop;
      None
        
  | OP_InsertValue _ vecop eltop idxs =>
    'vec <- map_option_snd (f e) vecop;
    'v <- map_option_snd (f e) eltop;
    None
    
  | OP_Select _ cndop op1 op2 =>
    'cnd <- map_option_snd (f e) cndop;
    'v1 <- map_option_snd (f e) op1;
    'v2 <- map_option_snd (f e) op2;      
    None
  end.

Fixpoint eval_op (e:env) (o:value) : option dvalue :=
  match o with
  | SV o' => eval_expr eval_op e o'
  end.

(* Semantically, a jump at the LLVM IR level might not be "atomic" in the sense that
   Phi nodes may be lowered into a sequence of non-atomic operations on registers.  However,
   Phi's should never touch memory [is that true? can there be spills?], so modeling them
   as atomic should be OK. *)
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


Definition Obs := D dvalue.

Definition lift_option_d {A B} (m:option A) (f: A -> Obs B) : Obs B :=
  match m with
    | None => Err
    | Some b => f b
  end.

Notation "'do' x <- m ; f" := (lift_option_d m (fun x => f)) 
   (at level 200, x ident, m at level 100, f at level 200).

Fixpoint stepD (CFG:cfg) (s:state) : Obs state :=
  let '(p, e, k) := s in
  do cmd <- (code CFG) p;
    match cmd with
    | Step (INSTR_Op op) p' =>
      do id <- def_id_of_path p;
      do dv <- eval_op e op;
       Ret (p', (id, dv)::e, k)

    (* NOTE : this doesn't yet correctly handle external calls or function pointers *)
    | Step (INSTR_Call (ret_ty,ID_Global f) args) p' =>
      do id <- def_id_of_path p;
      do fn <- (funs CFG) f;
      let '(ids, blk, i) := fn in
      do ids' <- map_option local_id_of_ident ids;
      do dvs <-  map_option (eval_op e) (map snd args);
      match ret_ty with
      | TYPE_Void => Ret (mk_path f blk i, combine ids' dvs, (KRet_void e p')::k)
      | _ => Ret (mk_path f blk i, combine ids' dvs, (KRet e id p')::k)
      end

    | Step (INSTR_Call (_, ID_Local _) _) _ => Err
        
    | Step (INSTR_Unreachable) _ => Err
                                                       
    | Jump (TERM_Ret (t, op)) =>
      match k, eval_op e op with
      | [], Some dv => Fin
      | (KRet e' id p') :: k', Some dv => Ret (p', (id, dv)::e', k')
      | _, _ => Err
      end

    | Jump (TERM_Ret_void) =>
      match k with
      | [] => Fin
      | (KRet_void e' p')::k' => Ret (p', e', k')
      | _ => Err
      end
        
    | Jump (TERM_Br (_,op) (_, br1) (_, br2)) =>
      do br <-
      match eval_op e op  with
      | Some (DV (VALUE_Bool _ true))  => Some br1
      | Some (DV (VALUE_Bool _ false)) => Some br2
      | Some _ => None
      | None => None
      end;
      do lbl <- local_id_of_ident br;
        match (blks CFG) (bn p) lbl with
          | Some (Phis ps q) => 
            lift_option_d (jump CFG p e e ps q k) (@Ret _ state)
          | None => Err
        end
        
    | Jump (TERM_Br_1 (_, br)) =>
      do lbl <- local_id_of_ident br;
        match (blks CFG) (bn p) lbl with
          | Some (Phis ps q) => 
            lift_option_d (jump CFG p e e ps q k) (@Ret _ state)
          | None => Err
        end
      
    | Step (INSTR_Alloca t _ _) p' =>
      do id <- def_id_of_path p;
      Eff (Alloca t (fun (a:dvalue) => Ret (p', (id, a)::e, k)))
        
    | Step (INSTR_Load _ t (_,ptr) _) p' =>
      do id <- def_id_of_path p;
      do dv <- eval_op e ptr;
      match dv with
        | DVALUE_Addr a => Eff (Load a (fun dv => Ret (p', (id, dv)::e, k)))
        | _ => Err
      end
        
    | Step (INSTR_Store _ (_, val) (_, ptr) _) p' =>
      match eval_op e val, eval_op e ptr with
      | Some dv, Some (DVALUE_Addr a) => Eff (Store a dv (Ret (p', e, k)))
      | _, _ => Err
      end

    | Step (INSTR_Phi _ _) p' => Err
      (* We should never evaluate Phi nodes except in jump *)

    (* Currently unhandled LLVM instructions *)
    | Step INSTR_Fence p'
    | Step INSTR_AtomicCmpXchg p'
    | Step INSTR_AtomicRMW p'
    | Step INSTR_VAArg p'
    | Step INSTR_LandingPad p' => Err
 
    (* Currently unhandled LLVM terminators *)                                  
    | Jump (TERM_Switch _ _ _)
    | Jump (TERM_IndirectBr _ _)
    | Jump (TERM_Resume _)
    | Jump (TERM_Invoke _ _ _ _) => Err
    end.


(* Note: codomain is D'  *)
CoFixpoint sem (CFG:cfg) (s:state) : (Obs Empty) :=
  bind (stepD CFG s) (sem CFG).

End StepSemantics.