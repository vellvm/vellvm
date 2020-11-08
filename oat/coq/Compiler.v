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

(** Definitions needed for generating id's *)
Definition instr_const (v: Z) (id : raw_id) (t: LLVMAst.typ) : cerr (instr_id * instr typ) :=     
  let binop_flags := LLVMAst.Add false false in
  match t with
  | TYPE_I 1%Z =>
    let ll_val :=  EXP_Bool (if Z.eqb v (1%Z) then true else false ) in
    let ll_id := EXP_Bool false in
    let op_binop := OP_IBinop binop_flags t ll_val ll_id in
    ret (IId id, INSTR_Op op_binop) 
  | TYPE_I 64%Z =>
    let ll_val :=  EXP_Integer v in
    let ll_id := EXP_Integer (Z_of_nat 0) in
    let op_binop := OP_IBinop binop_flags t ll_val ll_id in
    ret (IId id, INSTR_Op op_binop) 
  | _ => raise "err"
  end.

Definition cmp_unop (op: AST.unop) ( src: raw_id) (ty: LLVMAst.typ) : cerr (LLVMAst.typ * raw_id * code typ) :=
  raw_id' <- inc_tmp ;;
  match op with
  | AST.Neg =>
    (* numerical negation *) 
    let exp_op := OP_IBinop (LLVMAst.Mul false false) ty (EXP_Ident (ID_Local src)) (EXP_Integer(-1)%Z) in
    ret (ty, raw_id', [(IId raw_id', INSTR_Op exp_op)])  
  | AST.Lognot =>
    (* Logical negation *)
    let exp_op := OP_IBinop (LLVMAst.Xor) ty (EXP_Ident (ID_Local src)) (EXP_Integer(-1)%Z) in
    ret (int_ty 1, raw_id', [(IId raw_id', INSTR_Op exp_op)])  
  | AST.Bitnot =>
    (* Bitwsie negation *)
    let exp_op := OP_IBinop (LLVMAst.Xor) ty (EXP_Ident (ID_Local src)) (EXP_Integer (1%Z)) in
    ret (ty, raw_id', [(IId raw_id', INSTR_Op exp_op)])  
  end.

Definition cmp_binop (op: AST.binop) (src_l : raw_id) (src_r: raw_id) (ty: LLVMAst.typ) : cerr (LLVMAst.typ * raw_id * code typ) :=
  let idexp := fun i => EXP_Ident (ID_Local i) in
  raw_id' <- inc_tmp ;;
  match op with
    (* Basic (signed) integer arithmetic *)
  | AST.Add =>  
    let exp_op := OP_IBinop (LLVMAst.Add false false) ty (idexp src_l) (idexp src_r) in
    ret (ty, raw_id', [(IId raw_id', INSTR_Op exp_op)])
  | AST.Sub =>  
    let exp_op := OP_IBinop (LLVMAst.Sub false false) ty (idexp src_l) (idexp src_r) in
    ret (ty, raw_id', [(IId raw_id', INSTR_Op exp_op)])
  | AST.Mul =>  
    let exp_op := OP_IBinop (LLVMAst.Mul false false) ty (idexp src_l) (idexp src_r) in
    ret (ty, raw_id', [(IId raw_id', INSTR_Op exp_op)])
  (* Basic (signed) comparison *)
  | AST.Eq =>
    let exp_op := OP_ICmp (LLVMAst.Eq) (int_ty 1) (idexp src_l) (idexp src_r) in
    ret (int_ty 1, raw_id', [(IId raw_id', INSTR_Op exp_op)])
  | AST.Neq =>
    let exp_op := OP_ICmp (LLVMAst.Ne) (int_ty 1) (idexp src_l) (idexp src_r) in
    ret (int_ty 1, raw_id', [(IId raw_id', INSTR_Op exp_op)])
  | AST.Lt =>
    let exp_op := OP_ICmp (LLVMAst.Slt) (int_ty 1) (idexp src_l) (idexp src_r) in
    ret (int_ty 1, raw_id', [(IId raw_id', INSTR_Op exp_op)])
  | AST.Lte =>
    let exp_op := OP_ICmp (LLVMAst.Sle) (int_ty 1) (idexp src_l) (idexp src_r) in
    ret (int_ty 1, raw_id', [(IId raw_id', INSTR_Op exp_op)])
  | AST.Gt =>
    let exp_op := OP_ICmp (LLVMAst.Sgt) (int_ty 1) (idexp src_l) (idexp src_r) in
    ret (int_ty 1, raw_id', [(IId raw_id', INSTR_Op exp_op)])
  | AST.Gte =>
    let exp_op := OP_ICmp (LLVMAst.Sge) (int_ty 1) (idexp src_l) (idexp src_r) in
    ret (int_ty 1, raw_id', [(IId raw_id', INSTR_Op exp_op)])
  (* Basic (logical) operations *)
  | AST.And =>
    let exp_op := OP_IBinop (LLVMAst.And) (int_ty 1) (idexp src_l) (idexp src_r) in
    ret (int_ty 1, raw_id', [(IId raw_id', INSTR_Op exp_op)])
  | AST.Or =>
    let exp_op := OP_IBinop (LLVMAst.Or) (int_ty 1) (idexp src_l) (idexp src_r) in
    ret (int_ty 1, raw_id', [(IId raw_id', INSTR_Op exp_op)])
  (* Basic bitwise logical operations *)
  | AST.IAnd =>
    let exp_op := OP_IBinop (LLVMAst.And) (int_ty 64) (idexp src_l) (idexp src_r) in
    ret (ty, raw_id', [(IId raw_id', INSTR_Op exp_op)])
  | AST.IOr =>
    let exp_op := OP_IBinop (LLVMAst.Or) (int_ty 64) (idexp src_l) (idexp src_r) in
    ret (ty, raw_id', [(IId raw_id', INSTR_Op exp_op)])
  (* Basic shifting operations *)
  | AST.Shl =>  
    let exp_op := OP_IBinop (LLVMAst.Shl false false) ty (idexp src_l) (idexp src_r) in
    ret (ty, raw_id', [(IId raw_id', INSTR_Op exp_op)])
  | AST.Shr =>  
    let exp_op := OP_IBinop (LLVMAst.LShr false)  ty (idexp src_l) (idexp src_r) in
    ret (ty, raw_id', [(IId raw_id', INSTR_Op exp_op)])
  | AST.Sar =>  
    let exp_op := OP_IBinop (LLVMAst.AShr false) ty (idexp src_l) (idexp src_r) in
    ret (ty, raw_id', [(IId raw_id', INSTR_Op exp_op)])
  end.
                   

(* Handle function call *)
About List.fold_left.


(* Dereference a pointer *)
Definition deref (id: AST.id) : cerr ( LLVMAst.typ * raw_id * code typ ) :=
    st <- get ;;
    '(op_id, op_ty) <- find_local id st ;;
    match op_ty with
    | TYPE_Pointer t => ret (t, op_id, nil)
    | _ => raise "not a valid rhs - should be a pointer"
    end.

(* the exp is the operand *)
Fixpoint cmp_exp (expr: AST.exp)
  : cerr (LLVMAst.typ * raw_id * code typ) :=
  match expr with
  | CBool b =>
    let t := cmp_ty TBool in
    tmp_id <- inc_tmp ;;
    code <- instr_const (if b then 1%Z else 0%Z) (tmp_id) t ;;
    ret (t, tmp_id, [code])
  | CInt i =>
    let t := cmp_ty TInt in
    tmp_id <- inc_tmp ;;
    code <- instr_const (Int64.signed i) tmp_id t ;;
    ret (t, tmp_id, [code])
  | Uop op nexp =>
    '(ty, id, stream) <-  cmp_exp (elt AST.exp nexp) ;;
    '(op_t, op_id, s_unop) <- cmp_unop op id ty ;;
    ret (op_t, op_id, stream ++ s_unop)
  | Bop op lexp rexp =>
    '(t_l, id_l, code_l) <- cmp_exp (elt AST.exp lexp) ;;
    '(t_r, id_r, code_r) <- cmp_exp (elt AST.exp lexp) ;;
    '(op_t, op_id, code_res) <- cmp_binop op id_l id_r t_l ;;
    ret (op_t, op_id, code_l ++ code_r ++ code_res)
  | Id i =>
    deref i
  | Call id_e args_e =>
    '(f_ty, f_id, s) <- cmp_exp (elt AST.exp id_e) ;;
    '(args, streams) <- List.fold_left (fun acc e =>
                                          '(arglist, stream) <- acc ;;
                                          '(et, eid, es) <- cmp_exp (elt AST.exp e) ;;
                                          (* The following line is going to cause an issue in the future
                                             - suppose the expression id is global?  *)
                                          ret (arglist ++ [(et, EXP_Ident (ID_Local(eid)))], stream ++ es)
                                       ) args_e (ret (nil, nil)) ;;
    op_id <- inc_tmp ;;
    (* Calling a global - all functions are globally scoped *)
    let insn_call := INSTR_Call (f_ty, EXP_Ident (ID_Global f_id)) args in 
    ret (f_ty, op_id, s ++ streams ++ [(IId op_id, insn_call)])
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



