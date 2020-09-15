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
Require Coq.FSets.FMapAVL.
Require Coq.FSets.FMapFacts.
Require Coq.Structures.OrderedTypeEx.

Require Import compcert.lib.Integers compcert.lib.Floats.

Require Import Vellvm.Classes Vellvm.Util.
Require Import Vellvm.Trace Vellvm.AstLib.
Require Import Oat.AST Oat.OATIO.
Import ListNotations.


Set Implicit Arguments.
Set Contextual Implicit.

Open Scope Z_scope.
Open Scope string_scope.


Module OStepSemantics(A:ADDR).
  Module DV := DVALUE(A).
  Import DV.

  

  (* Environments ------------------------------------------------------------- *)  
  Module ENV := FMapAVL.Make(AstLib.StringOrd).
  Module ENVFacts := FMapFacts.WFacts_fun(AstLib.StringOrd)(ENV).
  
  Definition env_of_assoc {A} (l:list (id * A)) : ENV.t A :=
    List.fold_left (fun e '(k,v) => ENV.add k v e) l (@ENV.empty A).
  
  Definition genv := ENV.t dvalue.
  Definition env  := ENV.t dvalue.
  Definition fenv := ENV.t (list stmt).
                           
  Definition pc := list stmt. (* Was this right? *)
  
  Inductive frame : Type :=
  | KRetExp (e:env) (p:pc)
  .       
  Definition stack := list frame.

  Definition state := (genv * pc * env * fenv * stack)%type.

  Definition empty_genv : genv := ENV.empty dvalue.
  Definition empty_env : env := ENV.empty dvalue.
  Definition empty_fenv : fenv := ENV.empty (list stmt).
  Definition empty_pc : pc := [].
  Definition empty_stack : stack := [].
  
  Definition empty_state : state := (empty_genv, empty_pc, empty_env, empty_fenv, empty_stack).

  Definition globs_of (s:state) :=
    let '(g, p, e, f, k) := s in g.

  Definition pc_of (s:state) :=
    let '(g, p, e, f, k) := s in p.

  Definition env_of (s:state) :=
    let '(g, p, e, f, k) := s in e.

  Definition fenv_of (s:state) :=
    let '(g, p, e, f, k) := s in f.
  
  Definition stack_of (s:state) :=
    let '(g, p, e, f, k) := s in k.
  
  Fixpoint string_of_env' (e:list (id * dvalue)) : string :=
    match e with
    | [] => ""
    | (lid, _)::rest => lid ++ " " ++ (string_of_env' rest)
    end.

  Instance string_of_env : StringOf env := fun env => string_of_env' (ENV.elements env).
  
  Definition lookup_env {X} (e:ENV.t X) (id:id) : Trace X :=
    match ENV.find id e with
    | Some v => mret v
    | None => failwith ("lookup_env: failed to find id = " ++ (string_of id))
    end.
  
  Definition add_env := ENV.add.

  Inductive result :=
| Done (v:dvalue)
| Step (s:state)
.       

Definition cont (s:state) : Trace result := mret (Step s).
Definition halt (v:dvalue) : Trace result := mret (Done v).

Definition jump (CFG:prog) (fid:id) (bid_src:id) (bid_tgt:id) (g:genv) (e_init:env) (k:stack) : Trace result :=
  raise "Unimplemented".



Definition eval_uop (u:unop) (v:dvalue) : Trace dvalue :=
  match u with
  | Neg =>
    match v with
    | DVALUE_I64 i => mret (DVALUE_I64 (Int64.neg i))
    | _ => raise "Non I64 passed to Neg uop"
    end
  | Lognot =>
    match v with
    | DVALUE_Bool b => mret (DVALUE_Bool (negb b))
    | _ => raise "Non bool passed to Lognot uop"
    end
  | Bitnot =>
    match v with
    | DVALUE_I64 i => mret (DVALUE_I64 (Int64.not i))
    | _ => raise "Non I64 passed to Bitnot uop"
    end 
  end.

  
Definition eval_int_op (b:binop) (v1 v2:int64) : Trace dvalue :=
  match b with
  | Add => mret (DVALUE_I64 (Int64.add v1 v2))
  | Sub => mret (DVALUE_I64 (Int64.sub v1 v2))
  | Mul => mret (DVALUE_I64 (Int64.mul v1 v2))
  | Shl => mret (DVALUE_I64 (Int64.shl v1 v2))
  | Shr => mret (DVALUE_I64 (Int64.shru v1 v2)) 
  | Sar => mret (DVALUE_I64 (Int64.shr v1 v2))
  | IAnd => mret (DVALUE_I64 (Int64.and v1 v2))
  | IOr => mret (DVALUE_I64 (Int64.or v1 v2))

  | Eq => mret (DVALUE_Bool (Int64.eq v1 v2))
  | Neq => mret (DVALUE_Bool (negb (Int64.eq v1 v2)))
  | Lt => mret (DVALUE_Bool (Int64.lt v1 v2))
  | Lte => mret (DVALUE_Bool (orb (Int64.lt v1 v2) (Int64.eq v1 v2)))
  | Gt => mret (DVALUE_Bool (negb (orb (Int64.lt v1 v2) (Int64.eq v1 v2))))
  | Gte => mret (DVALUE_Bool (negb (Int64.lt v1 v2)))
      
  | _ => raise "Boolean"
  end.

Definition eval_bool_op (b:binop) (v1 v2:bool) : Trace dvalue :=
  match b with
  | And => mret (DVALUE_Bool (andb v1 v2))
  | Or => mret (DVALUE_Bool (orb v1 v2))
  | _ => raise "Integer"
  end.


Definition eval_op (b:binop) (v1 v2:dvalue) : Trace dvalue :=
  match b with
  | And => raise ""
  | Or =>
    match v1 with
    | DVALUE_Bool b1 =>
      match v2 with
      | DVALUE_Bool b2 =>
        eval_bool_op b b1 b2
      | _ => raise "non bool given to bool op 2"
      end
    | _ => raise "non bool given to bool op 1"
    end
  | _ =>
    match v1 with
    | DVALUE_I64 i1 =>
      match v2 with
      | DVALUE_I64 i2 =>
        eval_int_op b i1 i2
      | _ => raise "non int given to int op 2"                      
      end
    | _ => raise "non int given to int op 1"
    end
  end.
        
Fixpoint find_function_entry (CFG:prog) (fid:id) : option fdecl :=
  match CFG with
  | [] => None
  | decl :: CFG' =>
    match decl with
    | Gfdecl {| elt := f; loc := _ |} =>
      match f with
      | {| frtyp := _; fname := name; args := _; body := _ |} =>
        if StringOrdFacts.eqb name fid then Some f else find_function_entry CFG' fid
      end
    | _ => find_function_entry CFG' fid
    end
  end.


Definition assert_pointer (p: dvalue) : Trace () :=
  match p with
  | DVALUE_Addr _ => mret ()
  | _ => raise "Not a pointer"
  end.

Definition get_index (i:dvalue) : Trace nat :=
  match i with
  | DVALUE_I64 i => mret (Z.abs_nat (Int64.unsigned i))
  | _ => raise "index is not i64"
  end.

Definition index_into_array (i:dvalue) (a:dvalue) : Trace dvalue := 
  match a with
  | DVALUE_Array dvs =>
    'i <- get_index i;
    match nth_error dvs i with
    | Some dv => mret dv
    | None => raise "Index Array out of bounds"
    end
  | _ => raise "Non array passed to index"
  end.

Definition length_of_array (a:dvalue) : Trace dvalue :=
  match a with
  | DVALUE_Array dvs =>
    mret (DVALUE_I64 (Int64.repr (Z.of_nat (List.length dvs))))
  | _ => raise "Length taken of non array value"
  end.

Fixpoint project_from_struct_h (dvs: list (id * dvalue)) (i:id) : Trace dvalue :=
  match dvs with
  | [] => raise "Id in project not in struct"
  | (eid, e) :: tl =>
    if StringOrdFacts.eqb eid i then mret e else project_from_struct_h tl i
  end.

Definition get_struct_values (str:dvalue) : Trace (list (id * dvalue)) :=
  match str with
  | DVALUE_Struct dvs =>
    mret dvs
  | _ => raise "Tried to project from non struct"
  end.

Definition project_from_struct (str:dvalue) (i:id) : Trace dvalue :=
  'dvs <- get_struct_values str;
  project_from_struct_h dvs i.    


Fixpoint eval_exp (CFG:prog) (s:state) (o:exp) : Trace dvalue :=
  let '(g, pc, e, f, k) := s in
  match o with
  | CNull t => mret (DVALUE_Addr A.null)
  | CBool b =>
    Trace.Vis (Alloca TBool)
              (fun dv => Trace.Vis (Store (DVALUE_Bool b) dv)
                                (fun dv' => mret dv))
  | CInt i =>
    Trace.Vis (Alloca TInt)
              (fun dv => Trace.Vis (Store (DVALUE_I64 (Int64.repr i)) dv)
                                (fun dv' => mret dv))
  | CStr s => raise "TODO: Implement strings"
  | CArr t es => 
    'dvs <- map_monad (fun x => eval_exp CFG s (elt_of x)) es;
    Trace.Vis (Alloca (TRef (RArray t)))
              (fun dv => Trace.Vis (Store (DVALUE_Array dvs) dv)
                                (fun dv' => mret dv))
                     
  | CStruct i es => 
    'dvs <- map_monad (fun x => eval_exp CFG s (elt_of (snd x))) es;
    let dvs' := List.map (fun '((id, _), dv) => (id, dv)) (List.combine es dvs) in
    Trace.Vis (Alloca (TRef (RStruct i)))
              (fun dv => Trace.Vis (Store (DVALUE_Struct dvs') dv)
                                (fun dv' => mret dv))
    

  | Proj en i =>
    'str <- eval_exp CFG s (elt_of en);
    '; assert_pointer str;
    Trace.Vis (Load str) (fun dv => project_from_struct dv i)
    
  | NewArr t en =>
    'v <- eval_exp CFG s (elt_of en);
    'i <- get_index v;
    Trace.Vis (Alloca t) (fun (a:dvalue) =>
                            Trace.Vis (Store (DVALUE_Array (replicate (DVALUE_Null t) i)) a)
                                      (fun _ => mret a))
                               
  | Id id =>  
    match (lookup_env (env_of s) id) with
    | Ret v => mret v
    | _ =>
      'v <- (lookup_env (globs_of s) id);
      mret v
    end

  | Index en1 en2 =>
    'a <- eval_exp CFG s (elt_of en1);
    'i <- eval_exp CFG s (elt_of en2);
    '_ <- assert_pointer a;
    '_ <- assert_pointer i;
    Trace.Vis (Load a) (fun dv => Trace.Vis (Load i) (fun i => index_into_array i dv))
      
  | AST.Call f args => raise "Function calls in expressions not supported"

  | Bop b e1 e2 =>                   
    'v1 <- eval_exp CFG s (elt _ e1);
    'v2 <- eval_exp CFG s (elt _ e2);
    '_ <- assert_pointer v1;
    '_ <- assert_pointer v2;
    Trace.Vis (Load v1) (fun dv1 => Trace.Vis (Load v2) (fun dv2 =>
                        'r <- eval_op b dv1 dv2; mret r))
           
  | Uop u e =>                       
    'v <- eval_exp CFG s (elt _ e);
    '_ <- assert_pointer v;
    Trace.Vis (Load v) (fun dv => 'r <- eval_uop u dv; mret r)
           
  | Length en =>
    'a <- eval_exp CFG s (elt _ en);
    '_ <- assert_pointer a;
    Trace.Vis (Load a) (fun dv => length_of_array dv)
  end.

Fixpoint project_into_struct_h (dvs: list (id * dvalue)) (i:id) (v:dvalue)
  : Trace (list (id * dvalue)) :=
  match dvs with
  | [] => raise "Id in assignment not in struct"
  | (eid, e) :: tl =>
    if StringOrdFacts.eqb eid i
    then mret ((eid, v) :: tl)
    else 'r <- project_into_struct_h tl i v;
         mret ((eid, e) :: r)
  end.

Definition project_into_struct (str:dvalue) (i:id) (v:dvalue) : Trace dvalue :=
  'dvs <- get_struct_values str;
  'r <- project_into_struct_h dvs i v;
  mret (DVALUE_Struct r).

Fixpoint insert_into_array_h (dvs: list dvalue) (i:nat) (v:dvalue) : Trace (list dvalue) :=
  match dvs with
  | [] => raise "Id in assignment not in struct"
  | e :: tl =>
    if beq_nat i 0 then mret (v :: tl)
    else 'r <- insert_into_array_h tl (i-1) v;
         mret (e :: r) 
  end.

Definition get_array_values (arr:dvalue) : Trace (list dvalue) :=
  match arr with
  | DVALUE_Array dvs =>
    mret dvs
  | _ => raise "Tried to index into non array"
  end.

Definition insert_into_array (arr:dvalue) (i:nat) (v:dvalue) : Trace dvalue :=
  'dvs <- get_array_values arr;
  'r <- insert_into_array_h dvs i v;
  mret (DVALUE_Array r).

Definition get_bool (v:dvalue) : Trace bool :=
  match v with
  | DVALUE_Bool b => mret b
  | _ => raise "guard is not a boolean"
  end. 

Print stmt.


Fixpoint step (CFG:prog) (s:state) : Trace result :=
  let '(g, pc, e, f, k) := s in
  match pc with
  | Assn en1 en2 :: tl =>
    'v2 <- eval_exp CFG s (elt_of en2);
    '_ <- assert_pointer v2;
    match elt_of en1 with
    | Id i =>
      mret (Step (g, pc, add_env i v2 e, f, k)) 
    | Proj en i =>
      'str <- eval_exp CFG s (elt_of en);
      '_ <- assert_pointer str;  
      Trace.Vis (Load str)
                (fun dv => 'd <- project_into_struct dv i v2;
                        Trace.Vis (Store d str)
                                  (fun dv' => mret (Step (g, tl, e, f, k))))
    | Index en1 en2 =>
      'a <- eval_exp CFG s (elt_of en1);
      'i <- eval_exp CFG s (elt_of en2);
      '_ <- assert_pointer a;
      '_ <- assert_pointer i;
      Trace.Vis (Load i)
                (fun j => 'i <- get_index j;
                       Trace.Vis (Load a)
                                 (fun arr => 'r <- insert_into_array arr i v2;
                                          Trace.Vis (Store r arr) (fun _ => mret (Step (g, tl, e, f, k)))))
      
    | _ => raise "Invalid LHS for assignment"
    end
    
  | Return (Some {| elt := e'; loc := _ |}) :: [] =>(*
    'dv <- eval_exp g None e';
      match k with
      | [] => halt dv       
      | (KRetExp e' p')::k => cont (g, p', 
      | _ => raise "IMPOSSIBLE: Ret op in non-return configuration" 
      end*)
    raise "Unimplemented"
        
  | Return None :: [] => (*
    match k with
    | [] => halt DVALUE_Null
    | (KRet_void e' p')::k => mret DVALUE_Null
    | _ => raise "IMPOSSIBLE: Ret void in non-return configuration"
    end*)
    raise "Unimplemented"
  | If en thens elses :: tl =>
    'bd <- eval_exp CFG s (elt_of en);
    'b <- get_bool bd;
    if b then mret (Step (g, app (map elt_of thens) tl, e, f, k))
    else mret (Step (g, app (map elt_of elses) tl, e, f, k))
  | While en thens :: tl =>
    'bd <- eval_exp CFG s (elt_of en);
    'b <- get_bool bd;
    if b then mret (Step (g, app (map elt_of thens) pc, e, f, k))
    else mret (Step (g, tl, e, f, k))
  | _ => raise "Unimplemented"     

  end.
Arguments eval_exp  _ _ _ : simpl nomatch.

Fixpoint register_globals (CFG:prog) : Trace genv :=
  match CFG with
  | [] => mret empty_genv
  | Gvdecl gn :: tl =>
    'genv <- register_globals tl;
    'r <- eval_exp CFG empty_state (elt_of (init (elt_of gn)));
    mret (ENV.add (name (elt_of gn)) r genv)
  | h :: tl => register_globals tl
  end.

Fixpoint register_functions (CFG:prog) : Trace fenv :=
  match CFG with
  | [] => mret empty_fenv
  | Gfdecl fn :: tl =>
    'fenv <- register_functions tl;
     mret (ENV.add (fname (elt_of fn)) (List.map elt_of (body (elt_of fn))) fenv)
  | h :: tl => register_functions tl
  end. 

Definition init_state (CFG:prog) : Trace state :=
  raise "Unimplemented".

CoFixpoint step_sem (CFG:prog) (r:result) : Trace dvalue :=
  match r with
  | Done v => mret v
  | Step s => 'x <- step CFG s ; step_sem CFG x
  end.


End OStepSemantics.