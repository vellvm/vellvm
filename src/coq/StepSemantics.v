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

Require Import compcert.lib.Integers.

Open Scope Z_scope.
Open Scope string_scope.

Set Implicit Arguments.
Set Contextual Implicit.

Require Import Vellvm.Effects.

Module Type ADDR.
  Parameter addr : Set.
End ADDR.  

(* Set up for i1, i32, and i64 *)
Module Wordsize1.
  Definition wordsize := 1%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize1.

Module Int64 := Integers.Int64.
Module Int32 := Integers.Int.
Module Int1 := Make(Wordsize1).

Definition int1 := Int1.int.
Definition int32 := Int32.int.
Definition int64 := Int64.int.

Definition inttyp (x:Z) : Type :=
  match x with
  | 1 => int1
  | 32 => int32
  | 64 => int64
  | _ => False
  end.

Module StepSemantics(A:ADDR).

  (* The set of dynamic values manipulated by an LLVM program. This
   datatype uses the "Expr" functor from the Ollvm_ast definition,
   injecting new base values.  This allows the semantics to do
   'symbolic' execution for things that we don't have a way of
   interpreting concretely (e.g. undef).  *)
    Inductive dvalue : Set :=
    | DV : Expr dvalue -> dvalue
    | DVALUE_CodePointer (p : pc)
    | DVALUE_Addr (a:A.addr)
    | DVALUE_I1 (x:int1)
    | DVALUE_I32 (x:int32)
    | DVALUE_I64 (x:int64)
  (*| DVALUE_Double (x:ll_double)
    | DVALUE_Float (x:ll_float)*)
    | DVALUE_Poison
    .
  
    Module ET : Vellvm.Effects.EffT
        with Definition addr := A.addr
        with Definition typ := Ollvm_ast.typ
        with Definition value := dvalue.

      Definition addr := A.addr.
      Definition typ := Ollvm_ast.typ.
      Definition value := dvalue.
      Definition inj_addr := DVALUE_Addr.
      Definition no_value := DV (VALUE_None).
    End ET.    
  Module E := Vellvm.Effects.Effects(ET).
  Export E.

  (* TODO: add the global environment *)
  Definition genv := list (global_id * value).
  Definition env  := list (local_id * value).

  Inductive frame : Set :=
  | KRet      (e:env) (id:local_id) (q:pc)
  | KRet_void (e:env) (q:pc)
  .       
  
  Definition stack := list frame.
  Definition state := (pc * env * stack)%type.

  Definition def_id_of_pc (p:pc) : err local_id :=
    match ins p with
    | IId id => mret id
    | _ => failwith ("def_id_of_pc: " ++ (string_of p))
    end.

  Definition local_id_of_ident (i:ident) : err local_id :=
    match i with
    | ID_Global _ => failwith ("local_id_of_ident: " ++ string_of i)
    | ID_Local i => mret i
    end.

  Fixpoint string_of_env' (e:env) : string :=
    match e with
    | [] => ""
    | (lid, _)::rest => (string_of_raw_id lid) ++ " " ++ (string_of_env' rest)
    end.

  Instance string_of_env : StringOf env := string_of_env'.
  
  Definition lookup_env (e:env) (id:local_id) : err value :=
    trywith ("lookup_env: id = " ++ (string_of id) ++ " NOT IN env = " ++ (string_of e)) (assoc RawID.eq_dec id e).

  Definition add_env id dv (e:env) := (id,dv)::e.
  
  (* Arithmetic Operations ---------------------------------------------------- *)
  (* TODO: implement LLVM semantics *)

  (* Since modules are not first class, this code duplication
     will probably have to do. *)
  Definition eval_i1_op (iop:ibinop) (x y:inttyp 1) : value:=
    (* See eval_i64_op for a few comments *)
    match iop with
    | Add nuw nsw =>
      if orb (andb nuw (Int1.eq (Int1.add_carry x y Int1.zero) Int1.one))
             (andb nsw (Int1.eq (Int1.add_overflow x y Int1.zero) Int1.one))
      then DVALUE_Poison else DVALUE_I1 (Int1.add x y)
    | Sub nuw nsw =>
      if orb (andb nuw (Int1.eq (Int1.sub_borrow x y Int1.zero) Int1.one))
             (andb nsw (Int1.eq (Int1.sub_overflow x y Int1.zero) Int1.one))
      then DVALUE_Poison else DVALUE_I1 (Int1.sub x y)
    | Mul nuw nsw =>
      (* I1 mul can't overflow, just based on the 4 possible multiplications. *)
      DVALUE_I1 (Int1.mul x y)
    | Shl nuw nsw =>
      if (Int1.unsigned y) >=? 1 then DV (VALUE_Undef) else DVALUE_I1 x
    | UDiv ex =>
      if andb ex (negb ((Int1.unsigned x) mod (Int1.unsigned y) =? 0))
      then DVALUE_Poison else DVALUE_I1 (Int1.divu x y)
    | SDiv ex =>
      (* What does signed i1 mean? *)
      if andb ex (negb (((Int1.signed x) mod (Int1.signed y)) =? 0))
      then DVALUE_Poison else DVALUE_I1 (Int1.divs x y)
    | LShr ex =>
      if (Int1.unsigned y) >=? 1 then DV (VALUE_Undef) else DVALUE_I1 x
    | AShr ex =>
      if (Int1.unsigned y) >=? 1 then DV (VALUE_Undef) else DVALUE_I1 x
    | URem =>
      DVALUE_I1 (Int1.modu x y)
    | SRem =>
      DVALUE_I1 (Int1.mods x y)
    | And =>
      DVALUE_I1 (Int1.and x y)
    | Or =>
      DVALUE_I1 (Int1.or x y)
    | Xor =>
      DVALUE_I1 (Int1.xor x y)
    end.

  Definition eval_i32_op (iop:ibinop) (x y:inttyp 32) : value:=
    match iop with
    | Add nuw nsw =>
      if orb (andb nuw (Int32.eq (Int32.add_carry x y Int32.zero) Int32.one))
             (andb nsw (Int32.eq (Int32.add_overflow x y Int32.zero) Int32.one))
      then DVALUE_Poison else DVALUE_I32 (Int32.add x y)
    | Sub nuw nsw =>
      if orb (andb nuw (Int32.eq (Int32.sub_borrow x y Int32.zero) Int32.one))
             (andb nsw (Int32.eq (Int32.sub_overflow x y Int32.zero) Int32.one))
      then DVALUE_Poison else DVALUE_I32 (Int32.sub x y)
    | Mul nuw nsw =>
      let res := Int32.mul x y in
      let res_s' := (Int32.signed x) * (Int32.signed y) in
      if orb (andb nuw ((Int32.unsigned x) * (Int32.unsigned y) >?
                      Int32.unsigned res))
             (andb nsw (orb (Int32.min_signed >? res_s')
                            (res_s' >? Int32.max_signed)))
      then DVALUE_Poison else DVALUE_I32 res
    | Shl nuw nsw =>
      let res := Int32.shl x y in
      let res_u := Int32.unsigned res in
      let res_u' := Z.shiftl (Int32.unsigned x) (Int32.unsigned y) in
      if (Int32.unsigned y) >=? 32 then DV (VALUE_Undef) 
      else if orb (andb nuw (res_u' >? res_u))
                  (andb nsw (negb (Z.shiftr (Int32.unsigned x)
                                            (32 - Int32.unsigned y)
                                   =? (Int32.unsigned (Int32.negative res))
                                      * (Z.pow 2 (Int32.unsigned y) - 1))))
      then DVALUE_Poison else DVALUE_I32 res
    | UDiv ex =>
      if andb ex (negb ((Int32.unsigned x) mod (Int32.unsigned y) =? 0))
      then DVALUE_Poison else DVALUE_I32 (Int32.divu x y)
    | SDiv ex =>
      if andb ex (negb (((Int32.signed x) mod (Int32.signed y)) =? 0))
      then DVALUE_Poison else DVALUE_I32 (Int32.divs x y)
    | LShr ex =>
      if (Int32.unsigned y) >=? 32 then DV (VALUE_Undef)
      else if andb ex (negb ((Int32.unsigned x)
                               mod (Z.pow 2 (Int32.unsigned y)) =? 0))
      then DVALUE_Poison else DVALUE_I32 (Int32.shru x y)
    | AShr ex =>
      if (Int32.unsigned y) >=? 32 then DV (VALUE_Undef)
      else if andb ex (negb ((Int32.unsigned x)
                               mod (Z.pow 2 (Int32.unsigned y)) =? 0))
      then DVALUE_Poison else DVALUE_I32 (Int32.shr x y)
    | URem =>
      DVALUE_I32 (Int32.modu x y)
    | SRem =>
      DVALUE_I32 (Int32.mods x y)
    | And =>
      DVALUE_I32 (Int32.and x y)
    | Or =>
      DVALUE_I32 (Int32.or x y)
    | Xor =>
      DVALUE_I32 (Int32.xor x y)
    end.

  Definition eval_i64_op (iop:ibinop) (x y:inttyp 64) : value:=
    (* This needs to be tested *)
    match iop with
    (* Following to cases are probably right since they use CompCert *)
    | Add nuw nsw =>
      if orb (andb nuw (Int64.eq (Int64.add_carry x y Int64.zero) Int64.one))
             (andb nsw (Int64.eq (Int64.add_overflow x y Int64.zero) Int64.one))
      then DVALUE_Poison else DVALUE_I64 (Int64.add x y)
    | Sub nuw nsw =>
      if orb (andb nuw (Int64.eq (Int64.sub_borrow x y Int64.zero) Int64.one))
             (andb nsw (Int64.eq (Int64.sub_overflow x y Int64.zero) Int64.one))
      then DVALUE_Poison else DVALUE_I64 (Int64.sub x y)
    | Mul nuw nsw =>
      let res := Int64.mul x y in
      let res_s' := (Int64.signed x) * (Int64.signed y) in
      if orb (andb nuw ((Int64.unsigned x) * (Int64.unsigned y) >?
                      Int64.unsigned res))
             (andb nsw (orb (Int64.min_signed >? res_s')
                            (res_s' >? Int64.max_signed)))
      then DVALUE_Poison else DVALUE_I64 res
    | Shl nuw nsw =>
      let res := Int64.shl x y in
      let res_u := Int64.unsigned res in
      let res_u' := Z.shiftl (Int64.unsigned x) (Int64.unsigned y) in
      (* Unsigned shift x right by 64 - y. If shifted x != sign bit * (2^y - 1),
         then there is overflow. *)
      if (Int64.unsigned y) >=? 64 then DV (VALUE_Undef) 
      else if orb (andb nuw (res_u' >? res_u))
                  (andb nsw (negb (Z.shiftr (Int64.unsigned x)
                                            (64 - Int64.unsigned y)
                                   =? (Int64.unsigned (Int64.negative res))
                                      * (Z.pow 2 (Int64.unsigned y) - 1))))
           then DVALUE_Poison else DVALUE_I64 res
    | UDiv ex =>
      if andb ex (negb ((Int64.unsigned x) mod (Int64.unsigned y) =? 0))
      then DVALUE_Poison else DVALUE_I64 (Int64.divu x y)
    | SDiv ex =>
      if andb ex (negb (((Int64.signed x) mod (Int64.signed y)) =? 0))
      then DVALUE_Poison else DVALUE_I64 (Int64.divs x y)
    | LShr ex =>
      if (Int64.unsigned y) >=? 64 then DV (VALUE_Undef)
      else if andb ex (negb ((Int64.unsigned x)
                               mod (Z.pow 2 (Int64.unsigned y)) =? 0))
      then DVALUE_Poison else DVALUE_I64 (Int64.shru x y)
    | AShr ex =>
      if (Int64.unsigned y) >=? 64 then DV (VALUE_Undef)
      else if andb ex (negb ((Int64.unsigned x)
                               mod (Z.pow 2 (Int64.unsigned y)) =? 0))
      then DVALUE_Poison else DVALUE_I64 (Int64.shr x y)
    | URem =>
      DVALUE_I64 (Int64.modu x y)
    | SRem =>
      DVALUE_I64 (Int64.mods x y)
    | And =>
      DVALUE_I64 (Int64.and x y)
    | Or =>
      DVALUE_I64 (Int64.or x y)
    | Xor =>
      DVALUE_I64 (Int64.xor x y)
    end.

  (* Evaluate the given iop on the given arguments according to the bitsize *)
  Definition integer_op (bits:Z) (iop:ibinop) (x y:inttyp bits) : err value:=
    match bits, x, y with
    | 1, x, y => mret (eval_i1_op iop x y)
    | 32, x, y => mret (eval_i32_op iop x y)
    | 64, x, y => mret (eval_i64_op iop x y)
    | _, _, _ => failwith "unsupported bitsize"
    end.

  (* Convert written integer constant to corresponding integer with bitsize bits.
     Takes the integer modulo 2^bits. *)
  Definition coerce_integer_to_int (bits:Z) (i:Z) : err dvalue :=
    match bits with
    | 1 => mret (DVALUE_I1 (Int1.repr i)) 
    | 32 => mret (DVALUE_I32 (Int32.repr i))
    | 64 => mret (DVALUE_I64 (Int64.repr i))
    | _ => failwith "unsupported integer size"
    end.
  
  (* Helper for looping 2 argument evaluation over vectors, producing a vector *)
  Fixpoint vec_loop (f:dvalue -> dvalue -> err dvalue)
           (elts:list ((typ * dvalue) * (typ * dvalue)))
    : err (list (typ * dvalue)) :=
    monad_fold_right (fun acc e =>
                       match e with
                       | pair (pair t e1) (pair _ e2) =>
                         'val <- f e1 e2;
                         mret (pair t val :: acc)
                       end) elts [].
    
  (* Integer iop evaluation, called from eval_iop. 
     Here the values must be integers. Helper defined
     in order to prevent eval_iop from being recursive. *)
  Definition eval_iop_integer_h t iop v1 v2 : err value :=
    match t, v1, v2 with
    | TYPE_I 1, DVALUE_I1 i1, DVALUE_I1 i2 => integer_op 1 iop i1 i2
    | TYPE_I 32, DVALUE_I32 i1, DVALUE_I32 i2 => integer_op 32 iop i1 i2
    | TYPE_I 64, DVALUE_I64 i1, DVALUE_I64 i2 => integer_op 64 iop i1 i2
    | _, _, _ => failwith "ill_typed-iop"
    end.

  (* Handles the written constant cases for ops *)
  Definition eval_bop_integer t op v1 v2 : err value :=
    match t, v1, v2 with
    | TYPE_I bits, DV (VALUE_Integer i1), DV (VALUE_Integer i2) =>
      'v1 <- coerce_integer_to_int bits i1;
      'v2 <- coerce_integer_to_int bits i2;
      op t v1 v2
    | TYPE_I bits, DV (VALUE_Integer i1),v2 =>
      'v1 <- coerce_integer_to_int bits i1;
      op t v1 v2
    | TYPE_I bits, v1, DV (VALUE_Integer i2) =>
      'v2 <- coerce_integer_to_int bits i2;
      op t v1 v2
    | _,  v1, v2 => op t v1 v2
    end.

  (* I split the definition between the vector and other evaluations because
     otherwise eval_iop should be recursive to allow for vector calculations, 
     but coq can't find a fixpoint. *)
  Definition eval_iop t iop v1 v2 : err value :=
    match t, v1, v2 with
    | TYPE_Vector s (TYPE_I 1), DV (VALUE_Vector elts1), DV (VALUE_Vector elts2)
    | TYPE_Vector s (TYPE_I 32), DV (VALUE_Vector elts1), DV (VALUE_Vector elts2)
    | TYPE_Vector s (TYPE_I 64), DV (VALUE_Vector elts1), DV (VALUE_Vector elts2) =>
      'val <- vec_loop (eval_bop_integer t (fun t => eval_iop_integer_h t iop))
           (List.combine elts1 elts2);
      mret (DV (VALUE_Vector val))
    | _, _, _ => (eval_bop_integer t (fun t => eval_iop_integer_h t iop)) v1 v2
    end.
  
  Definition eval_i1_icmp icmp x y : value :=
    if match icmp with
       | Eq => Int1.cmp Ceq x y
       | Ne => Int1.cmp Cne x y
       | Ugt => Int1.cmpu Cgt x y
       | Uge => Int1.cmpu Cge x y
       | Ult => Int1.cmpu Clt x y
       | Ule => Int1.cmpu Cle x y
       | Sgt => Int1.cmp Cgt x y
       | Sge => Int1.cmp Cge x y
       | Slt => Int1.cmp Clt x y
       | Sle => Int1.cmp Cle x y
       end
    then DVALUE_I1 Int1.one else DVALUE_I1 Int1.zero.

  Definition eval_i32_icmp icmp x y : value :=
    if match icmp with
       | Eq => Int32.cmp Ceq x y
       | Ne => Int32.cmp Cne x y
       | Ugt => Int32.cmpu Cgt x y
       | Uge => Int32.cmpu Cge x y
       | Ult => Int32.cmpu Clt x y
       | Ule => Int32.cmpu Cle x y
       | Sgt => Int32.cmp Cgt x y
       | Sge => Int32.cmp Cge x y
       | Slt => Int32.cmp Clt x y
       | Sle => Int32.cmp Cle x y
       end
    then DVALUE_I1 Int1.one else DVALUE_I1 Int1.zero.

  Definition eval_i64_icmp icmp x y : value :=
    if match icmp with
       | Eq => Int64.cmp Ceq x y
       | Ne => Int64.cmp Cne x y
       | Ugt => Int64.cmpu Cgt x y
       | Uge => Int64.cmpu Cge x y
       | Ult => Int64.cmpu Clt x y
       | Ule => Int64.cmpu Cle x y
       | Sgt => Int64.cmp Cgt x y
       | Sge => Int64.cmp Cge x y
       | Slt => Int64.cmp Clt x y
       | Sle => Int64.cmp Cle x y
       end
    then DVALUE_I1 Int1.one else DVALUE_I1 Int1.zero.
  
  Definition integer_cmp bits icmp (x y:inttyp bits) : err value :=
    match bits, x, y with
    | 1, x, y => mret (eval_i1_icmp icmp x y)
    | 32, x, y => mret (eval_i32_icmp icmp x y)
    | 64, x, y => mret (eval_i64_icmp icmp x y)
    | _, _, _ => failwith "unsupported bitsize"
    end.

  (*Helper defined in order to prevent 
    eval_icmp from being recursive. *)
  Definition eval_icmp_h t icmp v1 v2 : err value :=
    match t, v1, v2 with
    | TYPE_I 1, DVALUE_I1 i1, DVALUE_I1 i2 => integer_cmp 1 icmp i1 i2
    | TYPE_I 32, DVALUE_I32 i1, DVALUE_I32 i2 => integer_cmp 32 icmp i1 i2
    | TYPE_I 64, DVALUE_I64 i1, DVALUE_I64 i2 => integer_cmp 64 icmp i1 i2
    | _, _, _ => failwith "ill_typed-icmp"
    end.
  
  Definition eval_icmp t icmp v1 v2 : err value :=
    eval_bop_integer t (fun t => eval_icmp_h t icmp) v1 v2.
  (*
  Definition double_op (fop:fbinop) (v1:ll_double) (v2:ll_double) : err value :=
    match fop with
    | FAdd => mret (DVALUE_Double (Float.add v1 v2))
    | FSub => mret (DVALUE_Double (Float.sub v1 v2))
    | FMul => mret (DVALUE_Double (Float.mul v1 v2))
    | FDiv => mret (DVALUE_Double (Float.div v1 v2))
    | FRem => failwith "unimplemented"
    end.
  
  Definition float_op (fop:fbinop) (v1:ll_float) (v2:ll_float) : err value :=
    match fop with
    | FAdd => mret (DVALUE_Float (Float32.add v1 v2))
    | FSub => mret (DVALUE_Float (Float32.sub v1 v2))
    | FMul => mret (DVALUE_Float (Float32.mul v1 v2))
    | FDiv => mret (DVALUE_Float (Float32.div v1 v2))
    | FRem => failwith "unimplemented"
    end.*)
  
  Definition eval_fop (t:typ) (fop:fbinop) (v1:value) (v2:value) : err value :=
    (* This can be revisited. Ollvm_ast.v needs to be updated. 
    match t, v1, v2 with
    | TYPE_Float, DV (VALUE_Float f1), DV (VALUE_Float f2) =>
      
    | TYPE_Float, DVALUE_Float f1, DVALUE_Float f2 => float_op fop f1 f2
    | TYPE_Double, DV (VALUE_Float d1), DV (VALUE_Float d2) =>
      
    | TYPE_Double, DVALUE_Double d1, DVALUE_Double d2 => double_op fop d1 d2
    | _, _, _ => failwith "ill_typed-fop"
    end. *)
    failwith "unimplemented".

  Definition eval_fcmp (fcmp:fcmp) (v1:value) (v2:value) : err value := failwith "eval_fcmp not implemented".

  Definition eval_conv_h conv t1 x t2 : err value :=
    match conv with
    | Trunc =>
      match t1, x, t2 with
      | TYPE_I 32, DVALUE_I32 i1, TYPE_I 1 =>
        mret (DVALUE_I1 (Int1.repr (Int32.unsigned i1)))
      | TYPE_I 64, DVALUE_I64 i1, TYPE_I 1 =>
        mret (DVALUE_I1 (Int1.repr (Int64.unsigned i1)))
      | TYPE_I 64, DVALUE_I64 i1, TYPE_I 32 =>
        mret (DVALUE_I32 (Int32.repr (Int64.unsigned i1)))
      | _, _, _ => failwith "ill typed-conv"
      end
    | Zext =>
      match t1, x, t2 with
      | TYPE_I 1, DVALUE_I1 i1, TYPE_I 32 =>
        mret (DVALUE_I32 (Int32.repr (Int1.unsigned i1)))
      | TYPE_I 1, DVALUE_I1 i1, TYPE_I 64 =>
        mret (DVALUE_I64 (Int64.repr (Int1.unsigned i1)))
      | TYPE_I 32, DVALUE_I32 i1, TYPE_I 64 =>
        mret (DVALUE_I64 (Int64.repr (Int32.unsigned i1)))
      | _, _, _ => failwith "ill typed-conv"
      end
    | Sext =>
      match t1, x, t2 with
      | TYPE_I 1, DVALUE_I1 i1, TYPE_I 32 =>
        mret (DVALUE_I32 (Int32.repr (Int1.signed i1)))
      | TYPE_I 1, DVALUE_I1 i1, TYPE_I 64 =>
        mret (DVALUE_I64 (Int64.repr (Int1.signed i1)))
      | TYPE_I 32, DVALUE_I32 i1, TYPE_I 64 =>
        mret (DVALUE_I64 (Int64.repr (Int32.signed i1)))
      | _, _, _ => failwith "ill typed-conv"
      end
    | Bitcast =>
      match t1, x, t2 with
      | TYPE_I bits1, x, TYPE_I bits2 =>
        if bits1 =? bits2 then mret x else failwith "unequal bitsize in cast"
      | TYPE_Pointer t1, DVALUE_Addr a, TYPE_Pointer t2 =>
        mret (DVALUE_Addr a) 
      | _, _, _ => failwith "ill-typed_conv"
      end
    | Inttoptr
    | Ptrtoint
    | Fptrunc
    | Fpext
    | Uitofp
    | Sitofp
    | Fptoui
    | Fptosi => failwith "unimplemented conv"
    end.
  
  Definition eval_conv conv t1 x t2 : err value :=
    match t1, x with
    | TYPE_I bits, DV (VALUE_Integer x) =>
      'v <- coerce_integer_to_int bits x;
        eval_conv_h conv t1 v t2
    | TYPE_Vector s t, DV (VALUE_Vector elts) =>
      (* In the future, implement bitcast and etc with vectors *)
      failwith "vectors unimplemented"
    | _, _ => eval_conv_h conv t1 x t2
    end.

  (* Same deal as above with the helper *)
  Definition eval_select_h cnd v1 v2 : err value :=
    match cnd with
    | DVALUE_I1 i =>
      mret (if Int1.unsigned i =? 1 then v1 else v2)
    | _ => failwith "ill_typed-select"
    end.

  Definition eval_select t cnd t' v1 v2 : err value :=
    match t, t', cnd, v1, v2 with
    | TYPE_Vector _ t, TYPE_Vector _ t', DV (VALUE_Vector es),
      DV (VALUE_Vector es1), DV (VALUE_Vector es2) =>
      (* vec needs to loop over es, es1, and es2. Is there a way to
         generalize vec_loop to cover this? (make v1,v2 generic?) *)
      let fix loop elts := 
          match elts with
          | [] => mret []
          | e :: tl =>
            match e with
            | pair (pair _ cnd) (pair (pair t v1) (pair _ v2)) =>
              'val <- eval_select_h cnd v1 v2;
              'vec <- loop tl;
              mret (pair t val :: vec)
            end
          end in
      'val <- loop (List.combine es (List.combine es1 es2));
      mret (DV (VALUE_Vector val))
    | _, _, _, _, _ => eval_select_h cnd v1 v2
    end.

  (* Helper function for indexding into a structured datatype 
     for extractvalue and insertvalue *)
  Definition index_into_str (v:value) (idx:Ollvm_ast.int) : err (typ * value) :=
    let fix loop elts i :=
        match elts with
        | [] => failwith "index out of bounds"
        | h :: tl =>
          if idx =? 0 then mret h else loop tl (i-1)
        end in
    match v with
    | DV (VALUE_Struct f) => loop f idx
    | DV (VALUE_Array e) => loop e idx
    | _ => failwith "invalid aggregate data"
    end.

  (* Helper function for indexding into a structured datatype 
     for insertvalue *)
  Definition insert_into_str (str:value) (v:value) (idx:Ollvm_ast.int) : err value :=
    let fix loop (acc elts:list (typ * value)) (i:Ollvm_ast.int) :=
        match elts with
        | [] => failwith "index out of bounds"
        | (t, h) :: tl =>
          if idx =? 0 then mret (app (app acc [pair t v]) tl)
          else loop (app acc [pair t h]) tl (i-1)
        end in
    match str with
    | DV (VALUE_Struct f) =>
      'v <- (loop [] f idx);
      mret (DV (VALUE_Struct v))
    | DV (VALUE_Array e) =>
      'v <- (loop [] e idx);
      mret (DV (VALUE_Array v))
    | _ => failwith "invalid aggregate data"
    end.

Definition eval_expr {A:Set} (f:env -> A -> err value) (e:env) (o:Expr A) : err value :=
  match o with
  | VALUE_Ident id => 
    'i <- local_id_of_ident id;
      lookup_env e i
  | VALUE_Integer x => mret (DV (VALUE_Integer x))
  | VALUE_Float x   => mret (DV (VALUE_Float x))
  | VALUE_Bool b    => mret (DV (VALUE_Bool b)) 
  | VALUE_Null      => mret (DV (VALUE_Null))
  | VALUE_Zero_initializer => mret (DV (VALUE_Zero_initializer))
  | VALUE_Cstring s => mret (DV (VALUE_Cstring s))
  | VALUE_None      => mret (DV (VALUE_None))
  | VALUE_Undef     => mret (DV (VALUE_Undef))

  | VALUE_Struct es =>
    'vs <- map_monad (monad_app_snd (f e)) es;
     mret (DV (VALUE_Struct vs))

  | VALUE_Packed_struct es =>
    'vs <- map_monad (monad_app_snd (f e)) es;
     mret (DV (VALUE_Packed_struct vs))
    
  | VALUE_Array es =>
    'vs <- map_monad (monad_app_snd (f e)) es;
     mret (DV (VALUE_Array vs))
    
  | VALUE_Vector es =>
    'vs <- map_monad (monad_app_snd (f e)) es;
     mret (DV (VALUE_Vector vs))

  | OP_IBinop iop t op1 op2 =>
    'v1 <- f e op1;
    'v2 <- f e op2;
    (eval_iop t iop) v1 v2

  | OP_ICmp cmp t op1 op2 => 
    'v1 <- f e op1;                   
    'v2 <- f e op2;
    (eval_icmp t cmp) v1 v2

  | OP_FBinop fop fm t op1 op2 =>
    'v1 <- f e op1;
    'v2 <- f e op2;
    (eval_fop t fop) v1 v2

  | OP_FCmp fcmp t op1 op2 => 
    'v1 <- f e op1;
    'v2 <- f e op2;
    (eval_fcmp fcmp) v1 v2
              
  | OP_Conversion conv t1 op t2 =>
    'v <- f e op;
    (eval_conv conv) t1 v t2
                       
  | OP_GetElementPtr t ptrval idxs =>
    'vptr <- monad_app_snd (f e) ptrval;
    'vs <- map_monad (monad_app_snd (f e)) idxs;
    failwith "getelementptr not implemented"  (* TODO: Getelementptr *)  
    
  | OP_ExtractElement vecop idx =>
    'vec <- monad_app_snd (f e) vecop;
    'vidx <- monad_app_snd (f e) idx;
    failwith "extractelement not implemented" (* TODO: Extract Element *)
      
  | OP_InsertElement vecop eltop idx =>
    'vec <- monad_app_snd (f e) vecop;
    'v <- monad_app_snd (f e) eltop;
    'vidx <- monad_app_snd (f e) idx;
    failwith "insertelement not implemented" (* TODO *)
    
  | OP_ShuffleVector vecop1 vecop2 idxmask =>
    'vec1 <- monad_app_snd (f e) vecop1;
    'vec2 <- monad_app_snd (f e) vecop2;      
    'vidx <- monad_app_snd (f e) idxmask;
    failwith "shufflevector not implemented" (* TODO *)

  | OP_ExtractValue strop idxs =>
    '(_, str) <- monad_app_snd (f e) strop;
    let fix loop str idxs : err dvalue :=
        match idxs with
        | [] => mret str
        | i :: tl =>
          '(_, v) <- index_into_str str i;
          loop v tl
        end in
    loop str idxs
        
  | OP_InsertValue strop eltop idxs =>
    '(t1, str) <- monad_app_snd (f e) strop;
    '(t2, v) <- monad_app_snd (f e) eltop;
    let fix loop str idxs : err dvalue :=
        match idxs with
        | [] => failwith "invalid indices"
        | [i] =>
          insert_into_str str v i
        | i :: tl =>
          '(_, v) <- index_into_str str i;
          'v <- loop v tl;
          insert_into_str str v i
        end in
    loop str idxs
    
  | OP_Select cndop op1 op2 => (* Do this *)
    '(t, cnd) <- monad_app_snd (f e) cndop;
    '(t1, v1) <- monad_app_snd (f e) op1;
    '(t2, v2) <- monad_app_snd (f e) op2;
    eval_select t cnd t1 v1 v2
  end.

Fixpoint eval_op (e:env) (o:Ollvm_ast.value) : err value :=
  match o with
  | SV o' => eval_expr eval_op e o'
  end.

(* Semantically, a jump at the LLVM IR level might not be "atomic" in the sense that
   Phi nodes may be lowered into a sequence of non-atomic operations on registers.  However,
   Phi's should never touch memory [is that true? can there be spills?], so modeling them
   as atomic should be OK. *)
Fixpoint jump (CFG:cfg) (bn:block_id) (e_init:env) (e:env) ps (q:pc) (k:stack) : err state :=
  match ps with
  | [] => mret (q, e, k)
  | (id, (INSTR_Phi _ ls))::rest => 
    match assoc RawID.eq_dec bn ls with
    | Some op =>
      'dv <- eval_op e_init op;
      jump CFG bn e_init (add_env id dv e) rest q k
    | None => failwith ("jump: block name not found " ++ string_of_raw_id bn)
    end
  | _ => failwith "jump: got non-phi instruction"
  end.

Definition raise s p : state + (Event state) :=
  inr (Err (s ++ ": " ++ (string_of_pc p))).

Definition lift_err_d {A B} (m:err A) (f: A -> (state + Event B)) : (state + Event B) :=
  match m with
    | inl s => inr (Err s)
    | inr b => f b
  end.

Notation "'do' x <- m ; f" := (lift_err_d m (fun x => f)) 
   (at level 200, x ident, m at level 100, f at level 200).

Definition stepD (CFG:mcfg) (s:state) : state + (Event state) :=
  let '(p, e, k) := s in
  let pc_of_pt pt := mk_pc (fn p) pt in
  do cmd <- trywith ("stepD: no cmd at pc " ++ (string_of p)) (fetch CFG p);
    match cmd with
    | Step (INSTR_Op op) p' =>
      do id <- def_id_of_pc p; 
      do dv <- eval_op e op;     
       inl (pc_of_pt p', (id, dv)::e, k)

    (* NOTE : this doesn't yet correctly handle external calls or function pointers *)
    | Step (INSTR_Call (ret_ty,ID_Global f) args) p' =>
      do id <- def_id_of_pc p; 
      do fdef <- trywith ("stepD: no function " ++ (string_of f)) (find_function CFG f);
      let ids := (df_args fdef) in  
      let cfg := df_instrs fdef in
      do dvs <-  map_monad (eval_op e) (map snd args);
      inl (mk_pc f (init cfg), combine ids dvs, 
          match ret_ty with
          | TYPE_Void => (KRet_void e (pc_of_pt p'))::k
          | _ =>         (KRet e id (pc_of_pt p'))::k
          end)

    | Step (INSTR_Call (_, ID_Local _) _) _ => raise "INSTR_Call to local" p
        
    | Step (INSTR_Unreachable) _ => raise "IMPOSSIBLE: unreachable" p
                                                       
    | Jump _ (TERM_Ret (t, op)) =>
      do dv <- eval_op e op;
      match k with
      | [] => inr (Fin dv)
      | (KRet e' id p') :: k' => inl (p', add_env id dv e', k')
      | _ => raise "IMPOSSIBLE: Ret op in non-return configuration" p
      end

    | Jump _ (TERM_Ret_void) =>
      match k with
      | [] => inr (Fin (DV (VALUE_Bool true)))
      | (KRet_void e' p')::k' => inl (p', e', k')
      | _ => raise "IMPOSSIBLE: Ret void in non-return configuration" p
      end
        
    | Jump current_block (TERM_Br (_,op) br1 br2) =>
      do dv <- eval_op e op;
      do br <- match dv with 
               | DV (VALUE_Bool true) => mret br1
               | DV (VALUE_Bool false) => mret br2
               | _ => failwith "Br got non-bool value"
      end;
      do fdef <- trywith ("stepD: no function " ++ (string_of (fn p))) (find_function CFG (fn p));
      let cfg := (df_instrs fdef) in
      match (phis cfg br) with
      | Some (Phis _ ps q) => 
        lift_err_d (jump cfg current_block e e ps (pc_of_pt q) k) inl
      | None => raise ("ERROR: Br " ++ (string_of br) ++ " not found") p
      end
        
    | Jump current_block (TERM_Br_1 br) =>
      do fdef <- trywith ("stepD: no function " ++ (string_of (fn p))) (find_function CFG (fn p));
      let cfg := (df_instrs fdef) in
        match (phis cfg br) with
          | Some (Phis _ ps q) => 
            lift_err_d (jump cfg current_block e e ps (pc_of_pt q) k) inl
          | None => raise ("ERROR: Br1  " ++ (string_of br) ++ " not found") p
        end
      
    | Step (INSTR_Alloca t _ _) p' =>
      do id <- def_id_of_pc p;  
      inr (Eff (Alloca t (fun (a:value) =>  (pc_of_pt p', add_env id a e, k))))
      
    | Step (INSTR_Load _ t (_,ptr) _) p' =>
      do id <- def_id_of_pc p;  
      do dv <- eval_op e ptr;     
      match dv with
      | DVALUE_Addr a => inr (Eff (Load a (fun dv => (pc_of_pt p', add_env id dv e, k))))
      | _ => raise "ERROR: Load got non-pointer value" p
      end

      
    | Step (INSTR_Store _ (_, val) (_, ptr) _) p' => 
      do dv <- eval_op e val;
      do v <- eval_op e ptr;
      match v with 
      | DVALUE_Addr a => inr (Eff (Store a dv (fun _ => (pc_of_pt p', e, k))))
      |  _ => raise "ERROR: Store got non-pointer value" p
      end

    | Step (INSTR_Phi _ _) p' => inr (Err "IMPOSSIBLE: Phi encountered in step")
      (* We should never evaluate Phi nodes except in jump *)

    (* Currently unhandled LLVM instructions *)
    | Step INSTR_Fence p'
    | Step INSTR_AtomicCmpXchg p'
    | Step INSTR_AtomicRMW p'
    | Step INSTR_VAArg p'
    | Step INSTR_LandingPad p' => raise "Unsupported LLVM intsruction" p
 
    (* Currently unhandled LLVM terminators *)                                  
    | Jump _ (TERM_Switch _ _ _)
    | Jump _ (TERM_IndirectBr _ _)
    | Jump _ (TERM_Resume _)
    | Jump _ (TERM_Invoke _ _ _ _) => raise "Unsupport LLVM terminator" p
    end.

Inductive Empty := .

(* Assumes that the entry-point function is named "fn" and that it takes
   no parameters *)
Definition init_state (CFG:mcfg) (fn:string) : err state :=
  'fdef <- trywith ("stepD: no function named " ++ fn) (find_function CFG (Name fn));
    let cfg := df_instrs fdef in
    mret ((mk_pc (Name fn) (init cfg)), [], []).

(* Note: codomain is D'  *)
CoFixpoint sem (CFG:mcfg) (s:state) : Trace :=
  match (stepD CFG s) with
  | inl s => Tau (sem CFG s)
  | inr (Err s) => Vis (Err s)
  | inr (Fin s) => Vis (Fin s)
  | inr (Eff m) => Vis (Eff (effects_map (sem CFG) m))
  end.


End StepSemantics.