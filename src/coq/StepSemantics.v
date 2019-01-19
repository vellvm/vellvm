(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

From Coq Require Import
     ZArith List String Omega
     FSets.FMapAVL
     FSets.FMapFacts
     Structures.OrderedTypeEx.

Require Import Integers Floats.

From ExtLib Require Import
     Programming.Show
     Structures.Monads
     Eqv.

Require Import ITree.

From Vellvm Require Import 
     Util
     Error
     LLVMAst
     AstLib
     CFG
     MemoryAddress
     LLVMIO
     DynamicValues
     TypeUtil.

Import EqvNotation.
Import ListNotations.
Import MonadNotation.
Import ShowNotation.

Set Implicit Arguments.
Set Contextual Implicit.

Open Scope monad_scope.
Open Scope Z_scope.
Open Scope string_scope.

Module StepSemantics(A:MemoryAddress.ADDRESS)(LLVMIO:LLVM_INTERACTIONS(A)).
  
  Import LLVMIO.


  
  (* Environments ------------------------------------------------------------- *)
  Module ENV := FMapAVL.Make(AstLib.RawIDOrd).
  Module ENVFacts := FMapFacts.WFacts_fun(AstLib.RawIDOrd)(ENV).
  Module ENVProps := FMapFacts.WProperties_fun(AstLib.RawIDOrd)(ENV).
  
  Definition env_of_assoc {A} (l:list (raw_id * A)) : ENV.t A :=
    List.fold_left (fun e '(k,v) => ENV.add k v e) l (@ENV.empty A).
  
  Definition genv := ENV.t dvalue.
  Definition env  := ENV.t dvalue.

  Inductive frame : Type :=
  | KRet      (e:env) (id:local_id) (q:pc)
  | KRet_void (e:env) (p:pc)
  .       
  Definition stack := list frame.

  Definition state := (genv * pc * env * stack)%type.

  Definition pc_of (s:state) :=
    let '(g, p, e, k) := s in p.

  Definition env_of (s:state) :=
    let '(g, p, e, k) := s in e.

  Definition stack_of (s:state) :=
    let '(g, p, e, k) := s in k.
  
  Fixpoint string_of_env' (e:list (raw_id * dvalue)) :=
    match e with
    | [] => empty
    | (lid, _)::rest => ((to_string lid) << " " << (string_of_env' rest))%show
    end.

  Instance show_env : Show env := fun env => string_of_env' (ENV.elements env).
  
  Definition lookup_env {X} (e:ENV.t X) (id:raw_id) : err X :=
    match ENV.find id e with
    | Some v => ret v
    | None => failwith "lookup_env: failed to find id" (* can't include ids in the error ++ (string_of id) *)
    end.

  Definition lookup_id (g:genv) (e:env) (i:ident) : err dvalue :=
    match i with
    | ID_Global x => lookup_env g x
    | ID_Local x => lookup_env e x
    end.

  Definition reverse_lookup_function_id (g:genv) (a:A.addr) : err raw_id :=
    let f x :=
        match x with
        | (_, DVALUE_Addr b) => if a ~=? b then true else false
        | _ => false
        end
    in
    match List.find f (ENV.elements g) with
    | None => failwith "reverse_lookup_function_id failed"
    | Some (fid, _) => ret fid
    end.
  
  Definition add_env := ENV.add.

  
  Section CONVERSIONS.
  (* Conversions can't go into DynamicValues because Int2Ptr and Ptr2Int casts 
     generate memory effects. *) 
  Definition eval_conv_h conv t1 x t2 : Trace dvalue :=
    match conv with
    | Trunc =>
      match t1, x, t2 with
      | TYPE_I 8, DVALUE_I8 i1, TYPE_I 1 =>
        ret (DVALUE_I1 (repr (unsigned i1)))
      | TYPE_I 32, DVALUE_I32 i1, TYPE_I 1 =>
        ret (DVALUE_I1 (repr (unsigned i1)))
      | TYPE_I 32, DVALUE_I32 i1, TYPE_I 8 =>
        ret (DVALUE_I8 (repr (unsigned i1)))
      | TYPE_I 64, DVALUE_I64 i1, TYPE_I 1 =>
        ret (DVALUE_I1 (repr (unsigned i1)))
      | TYPE_I 64, DVALUE_I64 i1, TYPE_I 8 =>
        ret (DVALUE_I8 (repr (unsigned i1)))
      | TYPE_I 64, DVALUE_I64 i1, TYPE_I 32 =>
        ret (DVALUE_I32 (repr (unsigned i1)))
      | _, _, _ => raise "ill typed-conv"
      end
    | Zext =>
      match t1, x, t2 with
      | TYPE_I 1, DVALUE_I1 i1, TYPE_I 8 =>
        ret (DVALUE_I8 (repr (unsigned i1)))
      | TYPE_I 1, DVALUE_I1 i1, TYPE_I 32 =>
        ret (DVALUE_I32 (repr (unsigned i1)))
      | TYPE_I 1, DVALUE_I1 i1, TYPE_I 64 =>
        ret (DVALUE_I64 (repr (unsigned i1)))
      | TYPE_I 8, DVALUE_I8 i1, TYPE_I 32 =>
        ret (DVALUE_I32 (repr (unsigned i1)))
      | TYPE_I 8, DVALUE_I8 i1, TYPE_I 64 =>
        ret (DVALUE_I64 (repr (unsigned i1)))
      | TYPE_I 32, DVALUE_I32 i1, TYPE_I 64 =>
        ret (DVALUE_I64 (repr (unsigned i1)))
      | _, _, _ => raise "ill typed-conv"
      end
    | Sext =>
      match t1, x, t2 with
      | TYPE_I 1, DVALUE_I1 i1, TYPE_I 8 =>
        ret (DVALUE_I8 (repr (signed i1)))
      | TYPE_I 1, DVALUE_I1 i1, TYPE_I 32 =>
        ret (DVALUE_I32 (repr (signed i1)))
      | TYPE_I 1, DVALUE_I1 i1, TYPE_I 64 =>
        ret (DVALUE_I64 (repr (signed i1)))
      | TYPE_I 8, DVALUE_I8 i1, TYPE_I 32 =>
        ret (DVALUE_I32 (repr (signed i1)))
      | TYPE_I 8, DVALUE_I8 i1, TYPE_I 64 =>
        ret (DVALUE_I64 (repr (signed i1)))
      | TYPE_I 32, DVALUE_I32 i1, TYPE_I 64 =>
        ret (DVALUE_I64 (repr (signed i1)))
      | _, _, _ => raise "ill typed-conv"
      end
    | Bitcast =>
      match t1, x, t2 with
      | TYPE_I bits1, x, TYPE_I bits2 =>
        if bits1 =? bits2 then ret x else raise "unequal bitsize in cast"
      | TYPE_Pointer t1, DVALUE_Addr a, TYPE_Pointer t2 =>
        ret (DVALUE_Addr a) 
      | _, _, _ => raise "ill-typed_conv"
      end
    | Fptrunc
    | Fpext
    | Uitofp
    | Sitofp
    | Fptoui
    | Fptosi => raise "TODO: floating point conversion not yet implemented"
    | Inttoptr =>
      match t1, t2 with
      | TYPE_I 64, TYPE_Pointer t => vis (ItoP x) ret
      | _, _ => raise "ERROR: Inttoptr got illegal arguments"
      end 
    | Ptrtoint =>
      match t1, t2 with
      | TYPE_Pointer t, TYPE_I 64 => vis (PtoI x) ret
      | _, _ => raise "ERROR: Ptrtoint got illegal arguments"
      end
    end.
  Arguments eval_conv_h _ _ _ _ : simpl nomatch.

  
  Definition eval_conv conv t1 x t2 : Trace dvalue :=
    match t1, x with
    | TYPE_I bits, dv =>
        eval_conv_h conv t1 dv t2
    | TYPE_Vector s t, (DVALUE_Vector elts) =>
      (* In the future, implement bitcast and etc with vectors *)
      raise "vectors unimplemented"
    | _, _ => eval_conv_h conv t1 x t2
    end.
  Arguments eval_conv _ _ _ _ : simpl nomatch.

  End CONVERSIONS.

  Definition dv_zero_initializer (t:dtyp) : err dvalue :=
    failwith "dv_zero_initializer unimplemented".


Section IN_CFG_CONTEXT.
Variable CFG:mcfg.

Definition eval_typ (t:typ) : dtyp :=
  TypeUtil.normalize_type_dtyp (m_type_defs CFG) t.


Section IN_LOCAL_ENVIRONMENT.
Variable g : genv.
Variable e : env.

(*
  [eval_exp] is the main entry point for evaluating LLVM expressions.
  top : is the type at which the expression should be evaluated (if any)
  INVARIANT: 
    - top may be None only for 
        - EXP_Ident 
        - OP_* cases

    - top must be Some t for the remaining EXP_* cases
      Note that when top is Some t, the resulting dvalue can never be
      a function pointer for a well-typed LLVM program.
 *)


Fixpoint eval_exp (top:option dtyp) (o:exp) {struct o} : Trace dvalue :=
  let eval_texp '(t,ex) :=
             let dt := eval_typ t in
             v <- eval_exp (Some dt) ex ;;
             ret v
  in
  match o with
  | EXP_Ident i => lift_err ret (lookup_id g e i) 

  | EXP_Integer x =>
    match top with
    | None =>  raise "eval_exp given untyped EXP_Integer"
    | Some (DTYPE_I bits) => do w <- coerce_integer_to_int bits x ;; ret w
    | _ => raise "bad type for constant int"
    end

  | EXP_Float x   =>
    match top with
    | None => raise "eval_exp given untyped EXP_Float"
    | Some DTYPE_Float  =>  ret (DVALUE_Float (Float32.of_double x))
    | Some DTYPE_Double =>  ret (DVALUE_Double x)
    | _ => raise "bad type for constant float"
    end

  | EXP_Hex x     =>
    match top with
    | None => raise "eval_exp given untyped EXP_Hex"
    | Some DTYPE_Float  =>  ret (DVALUE_Float (Float32.of_double x))
    | Some DTYPE_Double =>  ret (DVALUE_Double x)
    | _ => raise "bad type for constant hex float"
    end

  | EXP_Bool b    =>
    match b with
    | true  => ret (DVALUE_I1 one)
    | false => ret (DVALUE_I1 zero)
    end

  | EXP_Null => ret (DVALUE_Addr A.null)

  | EXP_Zero_initializer =>
    match top with
    | None => raise "eval_exp given untyped EXP_Zero_initializer"
    | Some t => do w <- dv_zero_initializer t;; ret w
    end

  | EXP_Cstring s =>
    raise "EXP_Cstring not yet implemented"

  | EXP_Undef =>
    match top with
    | None => raise "eval_exp given untyped EXP_Undef"
    | Some t => ret DVALUE_Undef  (* TODO: use t for size? *)
    end

  (* Question: should we do any typechecking for aggregate types here? *)
  (* Option 1: do no typechecking: *)
  | EXP_Struct es =>
     vs <- map_monad eval_texp es ;;
     ret (DVALUE_Struct vs)

  (* Option 2: do a little bit of typechecking *)
  | EXP_Packed_struct es =>
    match top with
    | None => raise "eval_exp given untyped EXP_Struct"
    | Some (DTYPE_Packed_struct _) =>
       vs <- map_monad eval_texp es ;;
       ret (DVALUE_Packed_struct vs)
    | _ => raise "bad type for VALUE_Packed_struct"
    end

  | EXP_Array es =>
     vs <- map_monad eval_texp es ;;
     ret (DVALUE_Array vs)
    
  | EXP_Vector es =>
     vs <- map_monad eval_texp es ;;
     ret (DVALUE_Vector vs)

  | OP_IBinop iop t op1 op2 =>
    let dt := eval_typ t in
    v1 <- eval_exp (Some dt) op1 ;;
    v2 <- eval_exp (Some dt) op2 ;;
    do w <- eval_iop iop v1 v2 ;;
    ret w

  | OP_ICmp cmp t op1 op2 =>
    let dt := eval_typ t in
    v1 <- eval_exp (Some dt) op1 ;;
    v2 <- eval_exp (Some dt) op2 ;;
    do w <- (eval_icmp cmp) v1 v2 ;;
    ret w

  | OP_FBinop fop fm t op1 op2 =>
    let dt := eval_typ t in    
    v1 <- eval_exp (Some dt) op1 ;;
    v2 <- eval_exp (Some dt) op2 ;;
    do w <- eval_fop fop v1 v2 ;;
    ret w

  | OP_FCmp fcmp t op1 op2 =>
    let dt := eval_typ t in
    v1 <- eval_exp (Some dt) op1 ;;
    v2 <- eval_exp (Some dt) op2 ;;
    do w <- eval_fcmp fcmp v1 v2 ;;
    ret w
              
  | OP_Conversion conv t1 op t2 =>
    let dt1 := eval_typ t1 in
    v <- eval_exp (Some dt1) op ;;
    eval_conv conv t1 v t2
                       
  | OP_GetElementPtr _ (TYPE_Pointer t, ptrval) idxs =>
    let dt := eval_typ t in
    vptr <- eval_exp (Some DTYPE_Pointer) ptrval ;;
    vs <- map_monad (fun '(_, index) => eval_exp (Some (DTYPE_I 32)) index) idxs ;;
    vis (GEP dt vptr vs) ret

  | OP_GetElementPtr _ (_, _) _ =>
    raise "getelementptr has non-pointer type annotation"
    
  | OP_ExtractElement vecop idx =>
    (*    'vec <- monad_app_snd (eval_exp e) vecop;
    'vidx <- monad_app_snd (eval_exp e) idx;  *)
    raise "extractelement not implemented" (* TODO: Extract Element *) 
      
  | OP_InsertElement vecop eltop idx =>
(*    'vec <- monad_app_snd (eval_exp e) vecop;
    'v <- monad_app_snd (eval_exp e) eltop;
    'vidx <- monad_app_snd (eval_exp e) idx; *)
    raise "insertelement not implemented" (* TODO *)
    
  | OP_ShuffleVector vecop1 vecop2 idxmask =>
(*    'vec1 <- monad_app_snd (eval_exp e) vecop1;
    'vec2 <- monad_app_snd (eval_exp e) vecop2;      
    'vidx <- monad_app_snd (eval_exp e) idxmask; *)
    raise "shufflevector not implemented" (* TODO *)

  | OP_ExtractValue strop idxs =>
    let '(t, str) := strop in
    let dt := eval_typ t in
    str <- eval_exp (Some dt) str ;;
    let fix loop str idxs : err dvalue :=
        match idxs with
        | [] => ret str
        | i :: tl =>
          v <- index_into_str str i ;;
          loop v tl
        end in
    do w <- loop str idxs ;;
      ret w
        
  | OP_InsertValue strop eltop idxs =>
    (*
    '(t1, str) <- monad_app_snd (eval_exp e) strop;
    '(t2, v) <- monad_app_snd (eval_exp e) eltop;
    let fix loop str idxs : err dvalue :=
        match idxs with
        | [] => raise "invalid indices"
        | [i] =>
          insert_into_str str v i
        | i :: tl =>
          '(_, v) <- index_into_str str i;
          'v <- loop v tl;
          insert_into_str str v i
        end in
    loop str idxs*)
    raise "TODO"
    
  | OP_Select (t, cnd) (t1, op1) (t2, op2) =>
    let dt := eval_typ t in
    let dt1 := eval_typ t1 in
    let dt2 := eval_typ t2 in
    cndv <- eval_exp (Some dt) cnd ;;
    v1 <- eval_exp (Some dt1) op1 ;;
    v2 <- eval_exp (Some dt2) op2 ;;
    do w <- eval_select cndv v1 v2 ;;
    ret w
  end.
Arguments eval_exp _ _ : simpl nomatch.

Definition eval_op (o:exp) : Trace dvalue :=
  eval_exp None o.
Arguments eval_op _ : simpl nomatch.

End IN_LOCAL_ENVIRONMENT.


Inductive result :=
| Done (v:dvalue)
| Step (s:state)
.       

Definition raise_p {X} (p:pc) s : Trace X := raise (s ++ " in block: " ++ (to_string p)).
Definition cont (s:state)  : Trace result := ret (Step s).
Definition halt (v:dvalue) : Trace result := ret (Done v).

(* TODO: move elsewhere? *)
Fixpoint combine_lists_err {A B:Type} (l1:list A) (l2:list B) : err (list (A * B)) :=
  match l1, l2 with
  | [], [] => ret []
  | x::xs, y::ys =>
    l <- combine_lists_err xs ys ;;
    ret ((x,y)::l)
  | _, _ => failwith "combine_lists_err: different lenth lists"
  end.

Definition jump (fid:function_id) (bid_src:block_id) (bid_tgt:block_id) (g:genv) (e_init:env) (k:stack) : Trace result :=
  let eval_phi (e:env) '(iid, Phi t ls) :=
      match assoc RawIDOrd.eq_dec bid_src ls with
      | Some op =>
        let dt := eval_typ t in
        dv <- eval_exp g e_init (Some dt) op ;;
        ret (add_env iid dv e)
      | None => raise ("jump: phi node doesn't include block " ++ to_string bid_src )
      end
  in
  match find_block_entry CFG fid bid_tgt with
  | None => raise ("jump: target block " ++ to_string bid_tgt ++ " not found")
  | Some (BlockEntry phis pc_entry) =>
      e_out <- monad_fold_right eval_phi phis e_init ;;
      cont (g, pc_entry, e_out, k)
  end.

Definition step (s:state) : Trace result :=
  let '(g, pc, e, k) := s in
  let eval_exp top exp := eval_exp g e top exp in
  
  do cmd <- trywith ("CFG has no instruction at " (* ++ string_of pc *)) (fetch CFG pc) ;;
  match cmd with
  | Term (TERM_Ret (t, op)) =>
    dv <- eval_exp (Some (eval_typ t)) op ;;
      match k with
      | [] => halt dv       
      | (KRet e' id p') :: k' => cont (g, p', add_env id dv e', k')
      | _ => raise_p pc "IMPOSSIBLE: Ret op in non-return configuration" 
      end
        
  | Term TERM_Ret_void =>
    match k with
    | [] => halt DVALUE_None
    | (KRet_void e' p')::k' => cont (g, p', e', k')
    | _ => raise_p pc "IMPOSSIBLE: Ret void in non-return configuration"
    end
      
  | Term (TERM_Br (t,op) br1 br2) =>
    dv <- eval_exp (Some (eval_typ t)) op ;; 
    br <- match dv with 
            | DVALUE_I1 comparison_bit =>
              if eq comparison_bit one then
                ret br1
              else
                ret br2
            | _ => raise "Br got non-bool value"
            end ;;
    jump (fn pc) (bk pc) br g e k
             
  | Term (TERM_Br_1 br) =>
    jump (fn pc) (bk pc) br g e k

             
  (* Currently unhandled LLVM terminators *)                                  
  | Term (TERM_Switch _ _ _)
  | Term (TERM_IndirectBr _ _)
  | Term (TERM_Resume _)
  | Term (TERM_Invoke _ _ _ _) => raise_p pc "Unsupport LLVM terminator" 

  | Inst insn =>  (* instruction *)
    do pc_next <- trywith "no fallthrough instruction" (incr_pc CFG pc) ;;
    match (pt pc), insn  with

      | IId id, INSTR_Op op =>
         dv <- eval_op g e op ;;     
         cont (g, pc_next, add_env id dv e, k)
          
      | IId id, INSTR_Alloca t _ _ =>
        vis (Alloca (eval_typ t)) (fun (a:dvalue) =>  cont (g, pc_next, add_env id a e, k))
                
      | IId id, INSTR_Load _ t (u,ptr) _ =>
        dv <- eval_exp (Some (eval_typ u)) ptr ;;
        vis (Load (eval_typ t) dv) (fun dv => cont (g, pc_next, add_env id dv e, k))
            
      | IVoid _, INSTR_Store _ (t, val) (u, ptr) _ => 
        dv <- eval_exp (Some (eval_typ t)) val ;; 
        v <- eval_exp (Some (eval_typ u)) ptr ;;
        vis (Store v dv) (fun _ => cont (g, pc_next, e, k))

      | _, INSTR_Store _ _ _ _ => raise "ERROR: Store to non-void ID" 

      | pt, INSTR_Call (t, f) args =>
        debug ("call") ;;
        fv <- eval_exp None f ;;
        dvs <-  map_monad (fun '(t, op) => (eval_exp (Some (eval_typ t)) op)) args ;;
        match fv with
        | DVALUE_Addr addr =>
          (* TODO: lookup fid given addr from global environment *)
          do fid <- reverse_lookup_function_id g addr ;;
          debug ("  fid:" ++ to_string fid) ;;
          match (find_function_entry CFG fid) with
          | Some fnentry =>
            let 'FunctionEntry ids pc_f := fnentry in
            do bs <- combine_lists_err ids dvs ;;
              let env := env_of_assoc bs in
              match pt with
              | IVoid _ =>
                (debug "pushed void stack frame") ;;
                cont (g, pc_f, env, (KRet_void e pc_next::k))
              | IId id =>
                (debug "pushed non-void stack frame") ;;
                cont (g, pc_f, env, (KRet e id pc_next::k))          
              end
          | None => (* This must have been a registered external function *)
            match fid with
              (* TODO: make sure the external call's type is correct *)
            | Name s => vis (Call DTYPE_Void s dvs) (fun dv => cont (g, pc_next, e, k))
            | _ => raise ("step: no function " (* ++ (string_of fid) *))
            end
          end
        | _ => raise_p pc "call got non-function pointer"
        end

      | _, INSTR_Unreachable => raise_p pc "IMPOSSIBLE: unreachable in reachable position" 

        (* Currently unhandled LLVM instructions *)
      | _, INSTR_Fence 
      | _, INSTR_AtomicCmpXchg 
      | _, INSTR_AtomicRMW
      | _, INSTR_VAArg 
      | _, INSTR_LandingPad => raise_p pc "Unsupported LLVM instruction"

      (* Error states *)                                     
      | _, _ => raise_p pc "ID / Instr mismatch void/non-void"
      end
  end.

(* Defining the Global Environment ------------------------------------------------------- *)

Definition allocate_globals (gs:list global) : Trace genv :=
  monad_fold_right
    (fun (m:genv) (g:global) =>
       vis (Alloca (eval_typ (g_typ g))) (fun v => ret (ENV.add (g_ident g) v m))) gs (@ENV.empty _).


Definition register_declaration (g:genv) (d:declaration) : Trace genv :=
  (* TODO: map dc_name d to the returned address *)
    vis (Alloca DTYPE_Pointer) (fun v => ret (ENV.add (dc_name d) v g)).

Definition register_functions (g:genv) : Trace genv :=
  monad_fold_right register_declaration
                   ((m_declarations CFG) ++ (List.map df_prototype (m_definitions CFG)))
                   g.
  
Definition initialize_globals (gs:list global) (g:genv) : Trace unit :=
  monad_fold_right
    (fun (_:unit) (glb:global) =>
       let dt := eval_typ (g_typ glb) in
       do a <- lookup_env g (g_ident glb) ;;
       dv <-
           match (g_exp glb) with
           | None => ret DVALUE_Undef
           | Some e => eval_exp g (@ENV.empty _) (Some dt) e
           end ;;
       vis (Store a dv) ret)
    gs tt.
  
Definition build_global_environment : Trace genv :=
  g <- allocate_globals (m_globals CFG) ;;
  g2 <- register_functions g ;;
  _ <- initialize_globals (m_globals CFG) g2 ;;
  ret g2.

(* Assumes that the entry-point function is named "fname" and that it takes
   no parameters *)
Definition init_state (fname:string) : Trace state :=
  g <- build_global_environment ;;
  fentry <- trywith ("INIT: no function named " ++ fname) (find_function_entry CFG (Name fname)) ;;
  let 'FunctionEntry ids pc_f := fentry in
    ret (g, pc_f, (@ENV.empty dvalue), []).

CoFixpoint step_sem (r:result) : Trace dvalue :=
  match r with
  | Done v => ret v
  | Step s => x <- step s ;; Tau (step_sem x)
  end%itree.

End IN_CFG_CONTEXT.

End StepSemantics.
