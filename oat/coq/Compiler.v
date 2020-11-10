(** 
    Adapted from vzaliva github.com/vzaliva/helix/Compiler.v
*)
From Coq Require Import List String Init.Datatypes Program.Basics.
Local Open Scope string_scope.
Local Open Scope program_scope.
Local Open Scope list_scope.
From Vellvm Require Import LLVMAst Util.
Require Import AST. 
Import ListNotations.
Set Implicit Arguments.
Set Strict Implicit.
From Coq Require Import FSets.FMapList.
Require Import FunInd FMapInterface.
Require Import Integers.
Require Import Integers String ZArith.
Require Import Plumbing.
Module Int64 := Integers.Int64. 
Definition int64 := Int64.int. 


From ExtLib Require Import
     Structures.Monads
     Structures.Monad
     Structures.MonadExc
     Structures.MonadState
     Data.Monads.EitherMonad.
Import MonadNotation.
Open Scope monad_scope.


Require Import CompilerCtxt.

Definition eq_raw (i: raw_id) (r: raw_id) : bool :=
  match i, r with
  | Name s, Name r => String.eqb s r
  | Anon s, Anon r => Z.eqb s r
  | Raw s, Raw r => Z.eqb s r
  | _,_ => false
  end.

Definition eq_ident (i: ident) (r: ident) : bool :=
  match i, r with
  | ID_Global s, ID_Global r => eq_raw s r
  | ID_Local s, ID_Local r => eq_raw s r
  | _, _ => false
  end.

Fixpoint eq_typ (t1: LLVMAst.typ) (t2: LLVMAst.typ) : bool :=
  match (t1, t2) with
    | (TYPE_I s, TYPE_I r) => Z.eqb s r
    | (TYPE_Pointer s, TYPE_Pointer r) => eq_typ s r
    | (TYPE_Void, TYPE_Void) => true
    | (TYPE_Half, TYPE_Half) => true
    | (TYPE_Float, TYPE_Float) => true
    | (TYPE_Double, TYPE_Double) => true
    | (TYPE_X86_fp80, TYPE_X86_fp80) => true
    | (TYPE_Fp128, TYPE_Fp128) => true
    | (TYPE_Ppc_fp128, TYPE_Ppc_fp128) => true
    | (TYPE_Metadata, TYPE_Metadata) => true
    | (TYPE_Opaque, TYPE_Opaque) => true
    | (TYPE_Identified l, TYPE_Identified r) => eq_ident l r      
    | (TYPE_Vector szl tl, TYPE_Vector szr tr) =>
      Z.eqb szl szr && eq_typ tl tr
    | (TYPE_Array sl s, TYPE_Array sr r) =>
      Z.eqb sl sr && eq_typ s r
    | (TYPE_Function lrt largs, TYPE_Function rrt rargs) =>
      let eq_both := fix eq_tls l r : bool :=
                       match l, r with
                       | nil, nil => true
                       | l::t1, r :: t2 => eq_typ l r && eq_tls t1 t2
                       | _, _ => false
                       end in
      eq_typ lrt rrt && eq_both largs rargs 
    | (TYPE_Struct lf, TYPE_Struct rf) =>
      let eq_both := fix eq_tls l r : bool :=
                       match l, r with
                       | nil, nil => true
                       | l::t1, r :: t2 => eq_typ l r && eq_tls t1 t2
                       | _, _ => false
                       end in
      eq_both lf rf
    | (TYPE_Packed_struct lf, TYPE_Packed_struct rf) =>
      let eq_both := fix eq_tls l r : bool :=
                       match l, r with
                       | nil, nil => true
                       | l::t1, r :: t2 => eq_typ l r && eq_tls t1 t2
                       | _, _ => false
                       end in
      eq_both lf rf
    | _ => false
  end.
   


Definition int_ty (i : nat) : LLVMAst.typ := TYPE_I (Z_of_nat i).
(** Fill these in as part of the compiler *)
 Fixpoint cmp_ty (ty:  AST.ty) : LLVMAst.typ :=
  match ty with
  | TBool => int_ty 1 
  | TInt => int_ty 64 
  | TRef rt => TYPE_Pointer (cmp_rty rt)
  | TNotNullRef rt => TYPE_Pointer (cmp_rty rt)
  end with
cmp_rty (rt : rty) : LLVMAst.typ :=
  match rt with
  | RString => int_ty 8 
  | RArray t => TYPE_Struct [int_ty 64; TYPE_Array (Z_of_nat 0) (cmp_ty t)] 
  | RFun ts r =>
    let '(args, rett) := (List.map cmp_ty ts, cmp_retty r) in
    TYPE_Function rett args 
  | _ => int_ty 0
  end with
cmp_retty (ret_ty: ret_ty) : LLVMAst.typ :=
  match ret_ty with
  | RetVoid => TYPE_Void
  | RetVal v => cmp_ty v
  end.

Check AST.rty_ind.
 Fixpoint eq_ty (t1: AST.ty) (t2: AST.ty) : bool :=
  match (t1, t2) with
  | (TBool, TBool) => true
  | (TInt, TInt) => true
  | (TRef l, TRef r) => eq_rty l r
  | (TNotNullRef l, TNotNullRef r) => eq_rty l r
  | (_, _) => false
  end with
eq_rty (t1: AST.rty) (t2: AST.rty) : bool :=
  match (t1, t2) with
  | (RString, RString) => true
  | (RArray l, RArray r) => eq_ty l r
  | (RStruct l, RStruct r) => String.eqb l r
  | (RFun tls l, RFun trs r) =>
    let eq_ls := fix eq_tls l r : bool :=
                   match (l, r) with
                   | (nil, nil) => true
                   | (l::t1, r::t2) => eq_ty l r && eq_tls t1 t2
                   | (_, _) => false
                   end in
    eq_ls tls trs &&
    eq_retty l r
  | (_, _) => false
  end with
eq_retty (t1: AST.ret_ty) (t2: AST.ret_ty) : bool :=
  match (t1, t2) with
  | (RetVoid, RetVoid) => true
  | (RetVal l, RetVal r) => eq_ty l r
  | (_, _) => false
  end.

Notation "x =? y" := (eq_ty x y). 

 
Definition typ_of_binop (op : AST.binop) : (AST.ty * AST.ty * AST.ty) :=
  match op with
    | AST.Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr => (TInt, TInt, TInt)
    | Eq | Neq | Lt | Lte | Gt | Gte => (TInt, TInt, TBool) 
    | And | Or => (TBool, TBool, TBool)
  end.           
                    
Definition typ_of_unop (op: AST.unop) : (AST.ty * AST.ty) :=
  match op with
  | Neg | Bitnot => (TInt, TInt)
  | Lognot => (TBool, TBool)
  end.

(** Create a local const definition with value v and type t*)
Definition instr_const (v: Z) (t: LLVMAst.typ) : cerr (LLVMAst.typ * ident * code typ) :=     
  raw_id' <- inc_tmp ;;
  let bop_id := IId raw_id' in
  let loc_id := ID_Local raw_id' in
  let binop_flags := LLVMAst.Add false false in
  match t with
  | TYPE_I 1%Z =>
    let ll_val :=  EXP_Bool (if Z.eqb v (1%Z) then true else false ) in
    let ll_id := EXP_Bool false in
    let op_binop := OP_IBinop binop_flags t ll_val ll_id in
    ret (t, loc_id, [(bop_id, INSTR_Op op_binop)]) 
  | TYPE_I 64%Z =>
    let ll_val :=  EXP_Integer v in
    let ll_id := EXP_Integer (Z_of_nat 0) in
    let op_binop := OP_IBinop binop_flags t ll_val ll_id in
    ret (t, loc_id, [(bop_id, INSTR_Op op_binop)]) 
  | _ => raise "err"
  end.

Definition cmp_unop (op: AST.unop) (src: ident) (ty: LLVMAst.typ) : cerr (LLVMAst.typ * ident * code typ) :=
  inst_id <- inc_tmp ;;
  let unop_id := IId inst_id in
  let loc_id := ID_Local inst_id in
  match op with
  | AST.Neg =>
    (* numerical negation *) 
    let exp_op := OP_IBinop (LLVMAst.Mul false false) ty (EXP_Ident src) (EXP_Integer(-1)%Z) in
    ret (ty, loc_id, [(unop_id, INSTR_Op exp_op)])  
  | AST.Lognot =>
    (* Logical negation *)
    let exp_op := OP_IBinop (LLVMAst.Xor) ty (EXP_Ident src) (EXP_Integer(-1)%Z) in
    ret (int_ty 1, loc_id, [(unop_id, INSTR_Op exp_op)])  
  | AST.Bitnot =>
    (* Bitwsie negation *)
    let exp_op := OP_IBinop (LLVMAst.Xor) ty (EXP_Ident src) (EXP_Integer (1%Z)) in
    ret (ty, loc_id, [(unop_id, INSTR_Op exp_op)])  
  end.

Definition cmp_binop (op: AST.binop) (src_l : ident) (src_r: ident) (ty: LLVMAst.typ) : cerr (LLVMAst.typ * ident * code typ) :=
  raw_id' <- inc_tmp ;;
  let bop_id := IId raw_id' in
  let loc_id := ID_Local raw_id' in
  match op with
    (* Basic (signed) integer arithmetic *)
  | AST.Add =>  
    let exp_op := OP_IBinop (LLVMAst.Add false false) ty (EXP_Ident src_l) (EXP_Ident src_r) in
    ret (ty, loc_id, [(bop_id, INSTR_Op exp_op)])
  | AST.Sub =>  
    let exp_op := OP_IBinop (LLVMAst.Sub false false) ty (EXP_Ident src_l) (EXP_Ident src_r) in
    ret (ty, loc_id, [(bop_id, INSTR_Op exp_op)])
  | AST.Mul =>  
    let exp_op := OP_IBinop (LLVMAst.Mul false false) ty (EXP_Ident src_l) (EXP_Ident src_r) in
    ret (ty, loc_id, [(bop_id, INSTR_Op exp_op)])
  (* Basic (signed) comparison *)
  | AST.Eq =>
    let exp_op := OP_ICmp (LLVMAst.Eq) (int_ty 1) (EXP_Ident src_l) (EXP_Ident src_r) in
    ret (int_ty 1, loc_id, [(bop_id, INSTR_Op exp_op)])
  | AST.Neq =>
    let exp_op := OP_ICmp (LLVMAst.Ne) (int_ty 1) (EXP_Ident src_l) (EXP_Ident src_r) in
    ret (int_ty 1, loc_id, [(bop_id, INSTR_Op exp_op)])
  | AST.Lt =>
    let exp_op := OP_ICmp (LLVMAst.Slt) (int_ty 1) (EXP_Ident src_l) (EXP_Ident src_r) in
    ret (int_ty 1, loc_id, [(bop_id, INSTR_Op exp_op)])
  | AST.Lte =>
    let exp_op := OP_ICmp (LLVMAst.Sle) (int_ty 1) (EXP_Ident src_l) (EXP_Ident src_r) in
    ret (int_ty 1, loc_id, [(bop_id, INSTR_Op exp_op)])
  | AST.Gt =>
    let exp_op := OP_ICmp (LLVMAst.Sgt) (int_ty 1) (EXP_Ident src_l) (EXP_Ident src_r) in
    ret (int_ty 1, loc_id, [(bop_id, INSTR_Op exp_op)])
  | AST.Gte =>
    let exp_op := OP_ICmp (LLVMAst.Sge) (int_ty 1) (EXP_Ident src_l) (EXP_Ident src_r) in
    ret (int_ty 1, loc_id, [(bop_id, INSTR_Op exp_op)])
  (* Basic (logical) operations *)
  | AST.And =>
    let exp_op := OP_IBinop (LLVMAst.And) (int_ty 1) (EXP_Ident src_l) (EXP_Ident src_r) in
    ret (int_ty 1, loc_id, [(bop_id, INSTR_Op exp_op)])
  | AST.Or =>
    let exp_op := OP_IBinop (LLVMAst.Or) (int_ty 1) (EXP_Ident src_l) (EXP_Ident src_r) in
    ret (int_ty 1, loc_id, [(bop_id, INSTR_Op exp_op)])
  (* Basic bitwise logical operations *)
  | AST.IAnd =>
    let exp_op := OP_IBinop (LLVMAst.And) (int_ty 64) (EXP_Ident src_l) (EXP_Ident src_r) in
    ret (ty, loc_id, [(bop_id, INSTR_Op exp_op)])
  | AST.IOr =>
    let exp_op := OP_IBinop (LLVMAst.Or) (int_ty 64) (EXP_Ident src_l) (EXP_Ident src_r) in
    ret (ty, loc_id, [(bop_id, INSTR_Op exp_op)])
  (* Basic shifting operations *)
  | AST.Shl =>  
    let exp_op := OP_IBinop (LLVMAst.Shl false false) ty (EXP_Ident src_l) (EXP_Ident src_r) in
    ret (ty, loc_id, [(bop_id, INSTR_Op exp_op)])
  | AST.Shr =>  
    let exp_op := OP_IBinop (LLVMAst.LShr false)  ty (EXP_Ident src_l) (EXP_Ident src_r) in
    ret (ty, loc_id, [(bop_id, INSTR_Op exp_op)])
  | AST.Sar =>  
    let exp_op := OP_IBinop (LLVMAst.AShr false) ty (EXP_Ident src_l) (EXP_Ident src_r) in
    ret (ty, loc_id, [(bop_id, INSTR_Op exp_op)])
  end.
                   
(* Dereference a pointer *)
(*
  this should take an id with type ptr t,
  and return a local id dereferencing that
  e.g. 
  if it's id %i
  then we emit
  %(i+1) = Load t (ptr r) %i
*)
Definition deref (id: AST.id) : cerr ( LLVMAst.typ * ident * code typ ) :=
    '(op_id, op_ty) <- find_ident id;;
    match op_ty with
    | TYPE_Pointer t =>
      raw_id' <- inc_tmp ;;
      let '(ld_id, loc_id) := (IId raw_id', ID_Local raw_id') in
      let ld_instr := INSTR_Load false t (op_ty,  EXP_Ident op_id) None in
      ret (t, loc_id, [(ld_id, ld_instr)])
    | _ => raise "not a valid rhs - should be a pointer"
    end.

(** Compiling expressions is straightforward - we can just invoke
    the convenient definitions from earlier :) *)

Fixpoint foldl2_err {A B C : Type}
         (comb: A -> B -> C -> A)
         (base: A) (l1: list B) (l2: list C) : cerr A :=
  match (l1, l2) with
  | (nil, nil) => ret base
  | (_, nil) => raise "unequal length lists passed to foldlerr"
  | (nil, _) => raise "unequal length lists passed to foldlerr"
  | (l :: t1, r :: t2) => let merge := comb base l r in
                        foldl2_err comb merge t1 t2
  end.
About eq_ty.
Fixpoint cmp_exp (expr: AST.exp)
  : cerr (LLVMAst.typ * ident * code typ) :=
  match expr with
  | CBool b => instr_const (if b then 1%Z else 0%Z) (cmp_ty TBool)
  | CInt i => instr_const (Int64.signed i) (cmp_ty TInt)
  | Id i => deref i
  | Uop op nexp =>
    '(ty, id, stream) <-  cmp_exp (elt AST.exp nexp) ;;
    '(op_t, op_id, s_unop) <- cmp_unop op id ty ;;
    ret (op_t, op_id, stream ++ s_unop)
  | Bop op lexp rexp =>
    '(t_l, id_l, code_l) <- cmp_exp (elt AST.exp lexp) ;;
    '(t_r, id_r, code_r) <- cmp_exp (elt AST.exp rexp) ;;
    '(op_t, op_id, code_res) <- cmp_binop op id_l id_r t_l ;;
    ret (op_t, op_id, code_l ++ code_r ++ code_res)
  | Call id_e args_e =>
    raise "err"
  | _ => raise "unimplemented"
  end.

Print LLVMAst.block.
Fixpoint cmp_stmt
         (rt : LLVMAst.typ)
         (stmt: AST.stmt) : cerr ( code typ ) :=
  let loc_id := fun e => EXP_Ident (ID_Local e) in
  match stmt with
    | AST.Decl (i, e) => 
      '(ty, id, code) <- cmp_exp (elt AST.exp e) ;;
      let t_ptr_id := TYPE_Pointer ty in
      alloca_id <- inc_tmp ;;
      store_id <- inc_tmp ;;
      (* TODO - instr_alloca nb texp and load volatile? *)
      let stream := code ++ [
                           (IId alloca_id, INSTR_Alloca ty None None ) ;
                         (IId store_id, INSTR_Store false (ty, loc_id id) (t_ptr_id, loc_id alloca_id) None)
                         ] in 
      put_local i t_ptr_id alloca_id ;;
      ret stream
    | Assn lhs rhs =>
      '(dest_ty, dest_id, dest_code) <- cmp_exp (elt AST.exp lhs) ;;
      '(src_ty, src_id, src_code) <- cmp_exp (elt AST.exp rhs) ;;
      (* This should generate a store src_ty src_id src *)
      store_id <- inc_tmp ;;
      ret ( dest_code ++ src_code ++ [
                        (IId store_id, INSTR_Store false (src_ty, loc_id src_id) (dest_ty, loc_id dest_id) None)
          ]) 
    | If cond pos neg =>  
      '(cond_ty, cond_id, cond_code) <- 
      raise "unimp"
    | _ => raise "unimplemented"
  end.
  
(** 
with cmp_block (rt : LLVMAst.typ) (stmts: AST.block) : cerr (code typ)
(* TODO *). Admitted.
*)                                   

(** Initialize a function context, compiler the given prog
    and run the state ... - work out what the nicest 
*)

Definition Populate_function_ctxt (c: ctxt) (p: AST.prog) : ctxt 
(* TODO *). Admitted.

(* TODO - add this once globals are supported in OAT *)
Fixpoint Populate_global_ctxt (c: ctxt) (p: AST.prog) : ctxt
(* TODO *). Admitted.

Definition cfg : Set := LLVMAst.block typ * list (LLVMAst.block typ).

Definition cmp_fdecl (f: node AST.fdecl)
  : cerr ( toplevel_entity typ cfg)
(* TODO *). Admitted.

Definition cmp_prog (p: AST.prog) : cerr ( toplevel_entities typ cfg) 
(* TODO *). Admitted.



