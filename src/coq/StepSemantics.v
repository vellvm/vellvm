(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import ZArith List String Omega.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Vellvm.Ollvm_ast Vellvm.AstLib Vellvm.CFG.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.

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


Definition err := sum string.
Definition failwith {A:Type} (s : string) : err A := inl s.
Definition trywith {A:Type} (s:string) (o:option A) : err A :=
  match o with
  | Some x => mret x
  | None => failwith s
  end.

Definition def_id_of_path (p:path) : err local_id :=
  match ins p with
  | IId id => mret id
  | _ => failwith ("def_id_of_path: " ++ (string_of_path p))
  end.

Definition local_id_of_ident (i:ident) : err local_id :=
  match i with
  | ID_Global _ => failwith ("local_id_of_ident: " ++ string_of_ident i)
  | ID_Local i => mret i
  end.

Fixpoint string_of_env (e:env) : string :=
  match e with
  | [] => ""
  | (lid, _)::rest => (string_of_raw_id lid) ++ " " ++ (string_of_env rest)
  end.

Definition lookup_env (e:env) (id:local_id) : err dvalue :=
  trywith ("lookup_env: id = " ++ (string_of_raw_id id) ++ " NOT IN env = " ++ (string_of_env e)) (assoc RawID.eq_dec id e).

(* Arithmetic Operations ---------------------------------------------------- *)
(* TODO: implement LLVM semantics *)


Definition eval_iop iop v1 v2 : err dvalue :=
  match v1, v2 with
  | DV (VALUE_Integer _ i1), DV (VALUE_Integer _ i2) =>
    mret (DV (VALUE_Integer _
    match iop with
    | Add _ _ => (i1 + i2)%Z
    | Sub _ _ => (i1 - i2)%Z
    | Mul _ _ => (i1 * i2)%Z
    | Shl _ _ 
    | UDiv _
    | SDiv _
    | LShr _
    | AShr _
    | URem | SRem | And | Or | Xor => 0%Z
    end))
  | _, _ => failwith "eval_iop"
  end.

(* TODO: replace Coq Z with appropriate i64, i32, i1 values *)
Definition eval_icmp icmp v1 v2 : err dvalue :=
  match v1, v2 with
  | DV (VALUE_Integer _ i1), DV (VALUE_Integer _ i2) =>
    mret (DV (VALUE_Bool _
    match icmp with
    | Eq => Z.eqb i1 i2
    | Ne => negb (Z.eqb i1 i2)
    | Ugt => Z.gtb i1 i2
    | Uge => Z.leb i2 i1
    | Ult => Z.gtb i2 i1
    | Ule => Z.leb i1 i2
    | Sgt => Z.gtb i1 i2
    | Sge => Z.leb i2 i1
    | Slt => Z.ltb i1 i2
    | Sle => Z.leb i1 i2
    end))
  | _, _ => failwith "eval_icmp"
  end.

Definition eval_fop (fop:fbinop) (v1:dvalue) (v2:dvalue) : err dvalue := failwith "eval_fop not implemented".

Definition eval_fcmp (fcmp:fcmp) (v1:dvalue) (v2:dvalue) : err dvalue := failwith "eval_fcmp not implemented".

Definition eval_expr {A:Set} (f:env -> A -> err dvalue) (e:env) (o:Expr A) : err dvalue :=
  match o with
  | VALUE_Ident _ id => 
    'i <- local_id_of_ident id;
      lookup_env e i
  | VALUE_Integer _ x => mret (DV (VALUE_Integer _ x))
  | VALUE_Float _ x   => mret (DV (VALUE_Float _ x))
  | VALUE_Bool _ b    => mret (DV (VALUE_Bool _ b)) 
  | VALUE_Null _      => mret (DV (VALUE_Null _))
  | VALUE_Zero_initializer _ => mret (DV (VALUE_Zero_initializer _))
  | VALUE_Cstring _ s => mret (DV (VALUE_Cstring _ s))
  | VALUE_None _      => mret (DV (VALUE_None _))
  | VALUE_Undef _     => mret (DV (VALUE_Undef _))

  | VALUE_Struct _ es =>
    'vs <- map_monad (monad_app_snd (f e)) es;
     mret (DV (VALUE_Struct _ vs))

  | VALUE_Packed_struct _ es =>
    'vs <- map_monad (monad_app_snd (f e)) es;
     mret (DV (VALUE_Packed_struct _ vs))
    
  | VALUE_Array _ es =>
    'vs <- map_monad (monad_app_snd (f e)) es;
     mret (DV (VALUE_Array _ vs))
    
  | VALUE_Vector _ es =>
    'vs <- map_monad (monad_app_snd (f e)) es;
     mret (DV (VALUE_Vector _ vs))

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
    'vptr <- monad_app_snd (f e) ptrval;
    'vs <- map_monad (monad_app_snd (f e)) idxs;
    failwith "getelementptr not implemented"  (* TODO: Getelementptr *)  
    
  | OP_ExtractElement _ vecop idx =>
    'vec <- monad_app_snd (f e) vecop;
    'vidx <- monad_app_snd (f e) idx;
    failwith "extractelement not implemented" (* TODO: Extract Element *)
      
  | OP_InsertElement _ vecop eltop idx =>
    'vec <- monad_app_snd (f e) vecop;
    'v <- monad_app_snd (f e) eltop;
    'vidx <- monad_app_snd (f e) idx;
    failwith "insertelement not implemented" (* TODO *)
    
  | OP_ShuffleVector _ vecop1 vecop2 idxmask =>
    'vec1 <- monad_app_snd (f e) vecop1;
    'vec2 <- monad_app_snd (f e) vecop2;      
    'vidx <- monad_app_snd (f e) idxmask;
    failwith "shufflevector not implemented" (* TODO *)

  | OP_ExtractValue _ vecop idxs =>
    'vec <- monad_app_snd (f e) vecop;
    failwith "extractvalue not implemented"
        
  | OP_InsertValue _ vecop eltop idxs =>
    'vec <- monad_app_snd (f e) vecop;
    'v <- monad_app_snd (f e) eltop;
    failwith "insertvalue not implemented"
    
  | OP_Select _ cndop op1 op2 =>
    'cnd <- monad_app_snd (f e) cndop;
    'v1 <- monad_app_snd (f e) op1;
    'v2 <- monad_app_snd (f e) op2;      
    failwith "select not implemented"
  end.

Fixpoint eval_op (e:env) (o:value) : err dvalue :=
  match o with
  | SV o' => eval_expr eval_op e o'
  end.

(* Semantically, a jump at the LLVM IR level might not be "atomic" in the sense that
   Phi nodes may be lowered into a sequence of non-atomic operations on registers.  However,
   Phi's should never touch memory [is that true? can there be spills?], so modeling them
   as atomic should be OK. *)
Fixpoint jump (CFG:cfg) (p:path) (e_init:env) (e:env) ps (q:path) (k:stack) : err state :=
  match ps with
  | [] => mret (q, e, k)
  | (id, (INSTR_Phi _ ls))::rest => 
    match assoc Ident.eq_dec (ID_Local (bn p)) ls with
    | Some op =>
      'dv <- eval_op e_init op;
      jump CFG p e_init ((id,dv)::e) rest q k
    | None => failwith ("jump: block name not found " ++ string_of_path p)
    end
  | _ => failwith "jump: got non-phi instruction"
  end.


Definition Obs := D dvalue.

Definition raise s p : (Obs state) :=
  Err (s ++ ": " ++ (string_of_path p)).

Definition lift_err_d {A B} (m:err A) (f: A -> Obs B) : Obs B :=
  match m with
    | inl s => Err s
    | inr b => f b
  end.

Notation "'do' x <- m ; f" := (lift_err_d m (fun x => f)) 
   (at level 200, x ident, m at level 100, f at level 200).

Fixpoint stepD (CFG:cfg) (s:state) : Obs state :=
  let '(p, e, k) := s in
  do cmd <- trywith ("stepD: no cmd at path " ++ (string_of_path p)) (code CFG p); 
    match cmd with
    | Step (INSTR_Op op) p' =>
      do id <- def_id_of_path p; 
      do dv <- eval_op e op;     
       Ret (p', (id, dv)::e, k)

    (* NOTE : this doesn't yet correctly handle external calls or function pointers *)
    | Step (INSTR_Call (ret_ty,ID_Global f) args) p' =>
      do id <- def_id_of_path p; 
      do fn <- trywith ("stepD: no function " ++ (string_of_raw_id f)) (funs CFG f);     
      let '(ids, blk, i) := fn in
      do ids' <- map_monad local_id_of_ident ids;  
      do dvs <-  map_monad (eval_op e) (map snd args); 
      match ret_ty with
      | TYPE_Void => Ret (mk_path f blk i, combine ids' dvs, (KRet_void e p')::k)
      | _ => Ret (mk_path f blk i, combine ids' dvs, (KRet e id p')::k)
      end

    | Step (INSTR_Call (_, ID_Local _) _) _ => raise "INSTR_Call to local" p
        
    | Step (INSTR_Unreachable) _ => raise "IMPOSSIBLE: unreachable" p
                                                       
    | Jump (TERM_Ret (t, op)) =>
      do dv <- eval_op e op;
      match k with
      | [] => Fin dv
      | (KRet e' id p') :: k' => Ret (p', (id, dv)::e', k')
      | _ => raise "IMPOSSIBLE: Ret op in non-return configuration" p
      end

    | Jump (TERM_Ret_void) =>
      match k with
      | [] => Fin (DV (VALUE_Bool _ true))
      | (KRet_void e' p')::k' => Ret (p', e', k')
      | _ => raise "IMPOSSIBLE: Ret void in non-return configuration" p
      end
        
    | Jump (TERM_Br (_,op) (_, br1) (_, br2)) =>
      do dv <- eval_op e op;
      do br <- match dv with 
      | DV (VALUE_Bool _ true) => mret br1
      | DV (VALUE_Bool _ false) => mret br2
      | _ => failwith "Br got non-bool value"
      end;
      do lbl <- local_id_of_ident br; 
        match (blks CFG) (fn p) lbl with
          | Some (Phis ps q) => 
            lift_err_d (jump CFG p e e ps q k) (@Ret _ state)
          | None => raise ("ERROR: Br lbl" ++ (AstLib.string_of_raw_id lbl) ++ " not found") p
        end
        
    | Jump (TERM_Br_1 (_, br)) =>
      do lbl <- local_id_of_ident br;  
        match (blks CFG) (fn p) lbl with
          | Some (Phis ps q) => 
            lift_err_d (jump CFG p e e ps q k) (@Ret _ state)
          | None => raise ("ERROR: Br1 lbl " ++ (AstLib.string_of_raw_id lbl) ++ " not found") p
        end
      
    | Step (INSTR_Alloca t _ _) p' =>
      do id <- def_id_of_path p;  
      Eff (Alloca t (fun (a:dvalue) => Ret (p', (id, a)::e, k)))
      
    | Step (INSTR_Load _ t (_,ptr) _) p' =>
      do id <- def_id_of_path p;  
      do dv <- eval_op e ptr;     
      match dv with
      | DVALUE_Addr a => Eff (Load a (fun dv => Ret (p', (id, dv)::e, k))) 
      | _ => raise "ERROR: Load got non-pointer value" p
      end

      
    | Step (INSTR_Store _ (_, val) (_, ptr) _) p' => 
      do dv <- eval_op e val;
      do v <- eval_op e ptr;
      match v with 
      | DVALUE_Addr a => Eff (Store a dv (Ret (p', e, k)))
      |  _ => raise "ERROR: Store got non-pointer value" p
      end

    | Step (INSTR_Phi _ _) p' => Err "IMPOSSIBLE: Phi encountered in step"
      (* We should never evaluate Phi nodes except in jump *)

    (* Currently unhandled LLVM instructions *)
    | Step INSTR_Fence p'
    | Step INSTR_AtomicCmpXchg p'
    | Step INSTR_AtomicRMW p'
    | Step INSTR_VAArg p'
    | Step INSTR_LandingPad p' => raise "Unsupported LLVM intsruction" p
 
    (* Currently unhandled LLVM terminators *)                                  
    | Jump (TERM_Switch _ _ _)
    | Jump (TERM_IndirectBr _ _)
    | Jump (TERM_Resume _)
    | Jump (TERM_Invoke _ _ _ _) => raise "Unsupport LLVM terminator" p
    end.


(* Note: codomain is D'  *)
CoFixpoint sem (CFG:cfg) (s:state) : (Obs Empty) :=
  bind (stepD CFG s) (sem CFG).

End StepSemantics.