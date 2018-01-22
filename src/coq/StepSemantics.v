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

Require Import compcert.lib.Integers compcert.lib.Floats.

Open Scope Z_scope.
Open Scope string_scope.

Set Implicit Arguments.
Set Contextual Implicit.

Require Import Vellvm.Effects.

Module Type ADDR.
  Parameter addr : Set.
  Parameter null : addr.
End ADDR.  

(* Set up for i1, i32, and i64 *) 
Module Int64 := Integers.Int64.
Module Int32 := Integers.Int.
Module Int1 := Ollvm_ast.Int1.

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

Definition ll_float  := Floats.float32.
Definition ll_double := Floats.float.


Module StepSemantics(A:ADDR).
  
  (* The set of dynamic values manipulated by an LLVM program. *)
  Inductive dvalue : Set :=
  | DVALUE_CodePointer (p : instr_id)
  | DVALUE_Addr (a:A.addr)
  | DVALUE_I1 (x:int1)
  | DVALUE_I32 (x:int32)
  | DVALUE_I64 (x:int64)
  | DVALUE_Double (x:ll_double)
  | DVALUE_Float (x:ll_float)
  | DVALUE_Undef (t:typ) (v:option value)
  | DVALUE_Poison
  | DVALUE_None
  | DVALUE_Struct        (fields: list (typ * dvalue))
  | DVALUE_Packed_struct (fields: list (typ * dvalue))
  | DVALUE_Array         (elts: list (typ * dvalue))
  | DVALUE_Vector        (elts: list (typ * dvalue))
  .

  Definition undef_i1  := (DVALUE_Undef (TYPE_I 1) None).
  Definition undef_i32 := (DVALUE_Undef (TYPE_I 32) None).
  Definition undef_i64 := (DVALUE_Undef (TYPE_I 64) None).
    
    Module ET : Vellvm.Effects.EffT
        with Definition addr := A.addr
        with Definition typ := Ollvm_ast.typ
        with Definition value := dvalue.

      Definition addr := A.addr.
      Definition typ := Ollvm_ast.typ.
      Definition value := dvalue.
      Definition inj_addr := DVALUE_Addr.
      Definition no_value := DVALUE_None.
    End ET.    
  Module E := Vellvm.Effects.Effects(ET).
  Export E.

  (* TODO: add the global environment *)
  Definition genv := list (global_id * value).
  Definition env  := list (local_id * value).

  Inductive frame : Set :=
  | KRet      (e:env) (id:local_id) (q:pc)
  | KRet_void (e:env) (p:pc)
  .       
  
  Definition stack := list frame.
  Definition state := (pc * env * stack)%type.

  Definition pc_of (s:state) :=
    let '(p, e, k) := s in p.

  Definition env_of (s:state) :=
    let '(p, e, k) := s in e.

  Definition stack_of (s:state) :=
    let '(p, e, k) := s in k.
  
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
  
  Definition lookup_env (e:env) (id:raw_id) : option dvalue :=
    assoc RawID.eq_dec id e.

  Definition add_env id dv (e:env) := (id,dv)::e.
  
  (* Arithmetic Operations ---------------------------------------------------- *)

  (* Since modules are not first class, this code duplication
     will probably have to do. *)
  Definition eval_i1_op (iop:ibinop) (x y:inttyp 1) : dvalue:=
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
      if (Int1.unsigned y) >=? 1 then undef_i1 else DVALUE_I1 x
    | UDiv ex =>
      if andb ex (negb ((Int1.unsigned x) mod (Int1.unsigned y) =? 0))
      then DVALUE_Poison else DVALUE_I1 (Int1.divu x y)
    | SDiv ex =>
      (* What does signed i1 mean? *)
      if andb ex (negb (((Int1.signed x) mod (Int1.signed y)) =? 0))
      then DVALUE_Poison else DVALUE_I1 (Int1.divs x y)
    | LShr ex =>
      if (Int1.unsigned y) >=? 1 then undef_i1 else DVALUE_I1 x
    | AShr ex =>
      if (Int1.unsigned y) >=? 1 then undef_i1 else DVALUE_I1 x
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
  Arguments eval_i1_op _ _ _ : simpl nomatch.

  
  Definition eval_i32_op (iop:ibinop) (x y:inttyp 32) : dvalue:=
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
      if (Int32.unsigned y) >=? 32 then undef_i32
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
      if (Int32.unsigned y) >=? 32 then undef_i32
      else if andb ex (negb ((Int32.unsigned x)
                               mod (Z.pow 2 (Int32.unsigned y)) =? 0))
      then DVALUE_Poison else DVALUE_I32 (Int32.shru x y)
    | AShr ex =>
      if (Int32.unsigned y) >=? 32 then undef_i32
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
  Arguments eval_i32_op _ _ _ : simpl nomatch.
  
  Definition eval_i64_op (iop:ibinop) (x y:inttyp 64) : dvalue:=
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
      if (Int64.unsigned y) >=? 64 then undef_i64
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
      if (Int64.unsigned y) >=? 64 then undef_i64
      else if andb ex (negb ((Int64.unsigned x)
                               mod (Z.pow 2 (Int64.unsigned y)) =? 0))
      then DVALUE_Poison else DVALUE_I64 (Int64.shru x y)
    | AShr ex =>
      if (Int64.unsigned y) >=? 64 then undef_i64
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
  Arguments eval_i64_op _ _ _ : simpl nomatch.
  
  (* Evaluate the given iop on the given arguments according to the bitsize *)
  Definition integer_op (bits:Z) (iop:ibinop) (x y:inttyp bits) : err dvalue:=
    match bits, x, y with
    | 1, x, y => mret (eval_i1_op iop x y)
    | 32, x, y => mret (eval_i32_op iop x y)
    | 64, x, y => mret (eval_i64_op iop x y)
    | _, _, _ => failwith "unsupported bitsize"
    end.
  Arguments integer_op _ _ _ _ : simpl nomatch.
  
  (* Convert written integer constant to corresponding integer with bitsize bits.
     Takes the integer modulo 2^bits. *)
  Definition coerce_integer_to_int (bits:Z) (i:Z) : err dvalue :=
    match bits with
    | 1 => mret (DVALUE_I1 (Int1.repr i)) 
    | 32 => mret (DVALUE_I32 (Int32.repr i))
    | 64 => mret (DVALUE_I64 (Int64.repr i))
    | _ => failwith "unsupported integer size"
    end.
  Arguments coerce_integer_to_int _ _ : simpl nomatch.
  
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
  Arguments eval_iop_integer_h _ _ _ _ : simpl nomatch.

  (* I split the definition between the vector and other evaluations because
     otherwise eval_iop should be recursive to allow for vector calculations, 
     but coq can't find a fixpoint. *)
  Definition eval_iop t iop v1 v2 : err value :=
    match t, v1, v2 with
    | TYPE_Vector s (TYPE_I i), (DVALUE_Vector elts1), (DVALUE_Vector elts2) =>
      'val <- vec_loop (eval_iop_integer_h (TYPE_I i) iop) (List.combine elts1 elts2);
      mret (DVALUE_Vector val)
    | _, _, _ => eval_iop_integer_h t iop v1 v2
    end.
  Arguments eval_iop _ _ _ _ : simpl nomatch.


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
  Arguments eval_i1_icmp _ _ _ : simpl nomatch.
  
  Definition eval_i32_icmp icmp x y : dvalue :=
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
  Arguments eval_i32_icmp _ _ _ : simpl nomatch.
  
  Definition eval_i64_icmp icmp x y : dvalue :=
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
  Arguments eval_i64_icmp _ _ _ : simpl nomatch.
  
  Definition integer_cmp bits icmp (x y:inttyp bits) : err value :=
    match bits, x, y with
    | 1, x, y => mret (eval_i1_icmp icmp x y)
    | 32, x, y => mret (eval_i32_icmp icmp x y)
    | 64, x, y => mret (eval_i64_icmp icmp x y)
    | _, _, _ => failwith "unsupported bitsize"
    end.
  Arguments integer_cmp _ _ _ _ : simpl nomatch.
  
  Definition eval_icmp t icmp v1 v2 : err dvalue :=
    match t, v1, v2 with
    | TYPE_I 1, DVALUE_I1 i1, DVALUE_I1 i2 => integer_cmp 1 icmp i1 i2
    | TYPE_I 32, DVALUE_I32 i1, DVALUE_I32 i2 => integer_cmp 32 icmp i1 i2
    | TYPE_I 64, DVALUE_I64 i1, DVALUE_I64 i2 => integer_cmp 64 icmp i1 i2
    | _, _, _ => failwith "ill_typed-icmp"
    end.
  Arguments eval_icmp _ _ _ _ : simpl nomatch.


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
    end.
  
  Definition eval_fop (t:typ) (fop:fbinop) (v1:value) (v2:value) : err dvalue :=
    match t, v1, v2 with
    | TYPE_Float, DVALUE_Float f1, DVALUE_Float f2 => float_op fop f1 f2
    | TYPE_Double, DVALUE_Double d1, DVALUE_Double d2 => double_op fop d1 d2
    | _, _, _ => failwith "ill_typed-fop"
    end. 

  Definition eval_fcmp (fcmp:fcmp) (v1:value) (v2:value) : err value := failwith "eval_fcmp not implemented".

  Definition eval_conv_h conv t1 x t2 : err dvalue :=
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
  Arguments eval_conv_h _ _ _ _ : simpl nomatch.
  
  Definition eval_conv conv t1 x t2 : err dvalue :=
    match t1, x with
    | TYPE_I bits, dv =>
        eval_conv_h conv t1 dv t2
    | TYPE_Vector s t, (DVALUE_Vector elts) =>
      (* In the future, implement bitcast and etc with vectors *)
      failwith "vectors unimplemented"
    | _, _ => eval_conv_h conv t1 x t2
    end.
  Arguments eval_conv _ _ _ _ : simpl nomatch.

  
  (* Same deal as above with the helper *)
  Definition eval_select_h cnd v1 v2 : err dvalue :=
    match cnd with
    | DVALUE_I1 i =>
      mret (if Int1.unsigned i =? 1 then v1 else v2)
    | _ => failwith "ill_typed-select"
    end.
  Arguments eval_select_h _ _ _ : simpl nomatch.

  
  Definition eval_select t cnd t' v1 v2 : err dvalue :=
    match t, t', cnd, v1, v2 with
    | TYPE_Vector _ t, TYPE_Vector _ t', (DVALUE_Vector es),
      (DVALUE_Vector es1), (DVALUE_Vector es2) =>
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
      mret (DVALUE_Vector val)
    | _, _, _, _, _ => eval_select_h cnd v1 v2
    end.
  Arguments eval_select _ _ _ _ _ : simpl nomatch.
  
  (* Helper function for indexing into a structured datatype 
     for extractvalue and insertvalue *)
  Definition index_into_str (v:value) (idx:Ollvm_ast.int) : err (typ * dvalue) :=
    let fix loop elts i :=
        match elts with
        | [] => failwith "index out of bounds"
        | h :: tl =>
          if idx =? 0 then mret h else loop tl (i-1)
        end in
    match v with
    | DVALUE_Struct f => loop f idx
    | DVALUE_Array e => loop e idx
    | _ => failwith "invalid aggregate data"
    end.
  Arguments index_into_str _ _ : simpl nomatch.
  
  (* Helper function for inserting into a structured datatype for insertvalue *)
  Definition insert_into_str (str:value) (v:value) (idx:Ollvm_ast.int) : err dvalue :=
    let fix loop (acc elts:list (typ * value)) (i:Ollvm_ast.int) :=
        match elts with
        | [] => failwith "index out of bounds"
        | (t, h) :: tl =>
          if idx =? 0 then mret (app (app acc [pair t v]) tl)
          else loop (app acc [pair t h]) tl (i-1)
        end in
    match str with
    | DVALUE_Struct f =>
      'v <- (loop [] f idx);
      mret (DVALUE_Struct v)

    | DVALUE_Array e =>
      'v <- (loop [] e idx);
      mret (DVALUE_Array v)

    | _ => failwith "invalid aggregate data"
    end.
  Arguments insert_into_str _ _ _ : simpl nomatch.


  (* NOTE: See compcert.lib.Floats.Float32.from_parsed *)
  Definition dv_float_of_string (h:string) : err dvalue :=
    failwith "dv_float_of_string unimplemented".

  Definition dv_double_of_string (h:string) : err dvalue :=
    failwith "dv_double_of_string unimplemented".

    (* NOTE: See compcert.lib.Floats.Float32.of_bits *)
  Definition dv_float_of_hex_string (h:string) : err dvalue :=
    failwith "dv_float_of_hex_string unimplemented".

  Definition dv_double_of_hex_string (h:string) : err dvalue :=
    failwith "dv_double_of_hex_string unimplemented".

  Definition dv_zero_initializer (t:typ) : err dvalue :=
    failwith "dv_zero_initializer unimplemented".

  Fixpoint combine_lists_err {A B:Type} (l1:list A) (l2:list B) : err (list (A * B)) :=
    match l1, l2 with
    | [], [] => mret []
    | x::xs, y::ys =>
      'l <- combine_lists_err xs ys;
        mret ((x,y)::l)
    | _, _ => failwith "combine_lists_err: different lenth lists"
    end.
  
(*
  [eval_expr] is the main entry point for evaluating LLVM expressions.
  top : is the type at which the expression should be evaluated (if any)
  INVARIANT: 
    - top my be None only for Ollvm_ast.OP_* cases
    - top must be Some t for Ollvm_ast.VALUE_* cases
*)
Fixpoint eval_expr (e:env) (top:option typ) (o:Ollvm_ast.value) : err dvalue :=
  match o with
  | Ollvm_ast.VALUE_Ident id => 
    'i <- local_id_of_ident id;
      match lookup_env e i with
      | None => failwith ("lookup_env: id = " ++ (string_of i) ++ " NOT IN env = " ++ (string_of e))
      | Some v => mret v
      end

  | Ollvm_ast.VALUE_Integer x =>
    match top with
    | None =>  failwith "eval_expr given untyped VALUE_Integer"
    | Some (TYPE_I bits) => coerce_integer_to_int bits x
    | _ => failwith "bad type for constant int"
    end

  | Ollvm_ast.VALUE_Float x   =>
    match top with
    | None => failwith "eval_expr given untyped VALUE_Float"
    | Some TYPE_Float  =>  dv_float_of_string x 
    | Some TYPE_Double =>  dv_double_of_string x
    | _ => failwith "bad type for constant float"
    end

  | Ollvm_ast.VALUE_Hex h     =>
    match top with
    | None => failwith "eval_expr given untyped VALUE_Hex"
    | Some TYPE_Float => dv_float_of_hex_string h
    | Some TYPE_Double => dv_double_of_hex_string h
    | _ => failwith "bad type for constant hex float"
    end

  | Ollvm_ast.VALUE_Bool b    =>
    match b with
    | true => mret (DVALUE_I1 Int1.one)
    | false => mret (DVALUE_I1 Int1.zero)
    end

  | Ollvm_ast.VALUE_Null      => mret (DVALUE_Addr A.null)

  | Ollvm_ast.VALUE_Zero_initializer =>
    match top with
    | None => failwith "eval_expr given untyped VALUE_Zero_initializer"
    | Some t => dv_zero_initializer t
    end

  | Ollvm_ast.VALUE_Cstring s =>
    failwith "VALUE_Cstring not yet implemented"

  | Ollvm_ast.VALUE_Undef     =>
    match top with
    | None => failwith "eval_expr given untyped VALUE_Undef"
    | Some t => mret (DVALUE_Undef t None)
    end

  (* Question: should we do any typechecking for aggregate types here? *)
  (* Option 1: do no typechecking: *)
  | Ollvm_ast.VALUE_Struct es =>
      'vs <- map_monad (fun '(t,ex) => 'v <- eval_expr e (Some t) ex; mret (t, v)) es;
      mret (DVALUE_Struct vs)

  (* Option 2: do a little bit of typechecking *)
  | Ollvm_ast.VALUE_Packed_struct es =>
    match top with
    | None => failwith "eval_expr given untyped VALUE_Struct"
    | Some (TYPE_Packed_struct _) =>
      'vs <- map_monad (fun '(t,ex) => 'v <- eval_expr e (Some t) ex; mret (t, v)) es;
      mret (DVALUE_Packed_struct vs)
    | _ => failwith "bad type for VALUE_Packed_struct"
    end

  | Ollvm_ast.VALUE_Array es =>
    'vs <- map_monad (fun '(t,ex) => 'v <- eval_expr e (Some t) ex; mret (t, v)) es;    
     mret (DVALUE_Array vs)
    
  | Ollvm_ast.VALUE_Vector es =>
    'vs <- map_monad (fun '(t,ex) => 'v <- eval_expr e (Some t) ex; mret (t, v)) es;        
     mret (DVALUE_Vector vs)

  | Ollvm_ast.OP_IBinop iop t op1 op2 =>
    'v1 <- eval_expr e (Some t) op1;
    'v2 <- eval_expr e (Some t) op2;
    (eval_iop t iop) v1 v2

  | Ollvm_ast.OP_ICmp cmp t op1 op2 => 
    'v1 <- eval_expr e (Some t) op1;                   
    'v2 <- eval_expr e (Some t) op2;
    (eval_icmp t cmp) v1 v2

  | Ollvm_ast.OP_FBinop fop fm t op1 op2 =>
    'v1 <- eval_expr e (Some t) op1;
    'v2 <- eval_expr e (Some t) op2;
    (eval_fop t fop) v1 v2

  | Ollvm_ast.OP_FCmp fcmp t op1 op2 => 
    'v1 <- eval_expr e (Some t) op1;
    'v2 <- eval_expr e (Some t) op2;
    (eval_fcmp fcmp) v1 v2
              
  | Ollvm_ast.OP_Conversion conv t1 op t2 =>
    'v <- eval_expr e (Some t1) op;
    (eval_conv conv) t1 v t2
                       
  | Ollvm_ast.OP_GetElementPtr t (ptrtyp, ptrval) idxs =>
    'vptr <- eval_expr e (Some ptrtyp) ptrval;
      'vs <- map_monad (fun '(t,ex) => 'v <- eval_expr e (Some t) ex; mret (t, v)) idxs;              
      failwith "getelementptr not implemented"  (* TODO: Getelementptr *)  
    
  | Ollvm_ast.OP_ExtractElement vecop idx =>
    (*    'vec <- monad_app_snd (eval_expr e) vecop;
    'vidx <- monad_app_snd (eval_expr e) idx;  *)
    failwith "extractelement not implemented" (* TODO: Extract Element *) 
      
  | Ollvm_ast.OP_InsertElement vecop eltop idx =>
(*    'vec <- monad_app_snd (eval_expr e) vecop;
    'v <- monad_app_snd (eval_expr e) eltop;
    'vidx <- monad_app_snd (eval_expr e) idx; *)
    failwith "insertelement not implemented" (* TODO *)
    
  | Ollvm_ast.OP_ShuffleVector vecop1 vecop2 idxmask =>
(*    'vec1 <- monad_app_snd (eval_expr e) vecop1;
    'vec2 <- monad_app_snd (eval_expr e) vecop2;      
    'vidx <- monad_app_snd (eval_expr e) idxmask; *)
    failwith "shufflevector not implemented" (* TODO *)

  | Ollvm_ast.OP_ExtractValue strop idxs =>
    let '(t, str) := strop in
    'str <- eval_expr e (Some t) str;
    let fix loop str idxs : err dvalue :=
        match idxs with
        | [] => mret str
        | i :: tl =>
          '(_, v) <- index_into_str str i;
          loop v tl
        end in
    loop str idxs
        
  | Ollvm_ast.OP_InsertValue strop eltop idxs =>
    (*
    '(t1, str) <- monad_app_snd (eval_expr e) strop;
    '(t2, v) <- monad_app_snd (eval_expr e) eltop;
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
    loop str idxs*)
    failwith "TODO"
    
  | Ollvm_ast.OP_Select (t, cnd) (t1, op1) (t2, op2) => 
    'cndv <- eval_expr e (Some t) cnd;
    'v1 <- eval_expr e (Some t1) op1;
    'v2 <- eval_expr e (Some t2) op2;
    eval_select t cndv t1 v1 v2
  end.
Arguments eval_expr _ _ _ : simpl nomatch.

Fixpoint eval_op (e:env) (o:Ollvm_ast.value) : err dvalue :=
  eval_expr e None o.

Arguments eval_op _ _ : simpl nomatch.

(*
Definition eval_op_for_store (e:env) (t:typ) (o:Ollvm_ast.value)
  : err value :=
  match o with
  | SV o' => 
    match t, o' with 
    | TYPE_I 1, VALUE_Integer i => mret (DVALUE_I1 (Int1.repr i))
    | TYPE_I 32, VALUE_Integer i => mret (DVALUE_I32 (Int32.repr i))
    | TYPE_I 64, VALUE_Integer i => mret (DVALUE_I64 (Int64.repr i))

    | _, OP_IBinop _ _ _ _
    | _, OP_ICmp _ _ _ _
    | _, OP_FBinop _ _ _ _ _
    | _, OP_FCmp _ _ _ _
    | _, OP_Conversion _ _ _ _
    | _, OP_GetElementPtr _ _ _
    | _, OP_ExtractElement _ _
    | _, OP_InsertElement _ _ _
    | _, OP_ShuffleVector _ _ _
    | _, OP_ExtractValue _ _
    | _, OP_InsertValue _ _ _
    | _, OP_Select _ _ _ => failwith "invalid operand for store"
                                             
    | _, _ => eval_op e (Some t) o
    end
  end.

Definition eval_cond (e:env) (o:Ollvm_ast.value) : err value :=
  match o with
  | SV o' =>
    match o' with
    | VALUE_Bool true => mret (DVALUE_I1 (Int1.one))
    | VALUE_Bool false => mret (DVALUE_I1 (Int1.zero))

    | OP_IBinop _ _ _ _
    | OP_ICmp _ _ _ _
    | OP_FBinop _ _ _ _ _
    | OP_FCmp _ _ _ _
    | OP_Conversion _ _ _ _
    | OP_GetElementPtr _ _ _
    | OP_ExtractElement _ _
    | OP_InsertElement _ _ _
    | OP_ShuffleVector _ _ _
    | OP_ExtractValue _ _
    | OP_InsertValue _ _ _
    | OP_Select _ _ _ => failwith "invalid conditional"

    | _ => eval_op e None o
    end
  end.
*)

(*
(* Semantically, a jump at the LLVM IR level might not be "atomic" in the sense that
   Phi nodes may be lowered into a sequence of non-atomic operations on registers.  However,
   Phi's should never touch memory [is that true? can there be spills?], so modeling them
   as atomic should be OK. *)
Fixpoint jump (CFG:cfg) (from:block_id) (e_init:env) (e:env) (to:block) (k:stack) : err state :=
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
*)


Definition jump (CFG:mcfg) (fid:function_id) (bid_src:block_id) (bid_tgt:block_id) (e_init:env) (k:stack)  : err state :=
  let eval_phi (e:env) '(iid, Phi t ls) :=
      match assoc RawID.eq_dec bid_src ls with
      | Some op =>
        'dv <- eval_expr e_init (Some t) op;
          mret (add_env iid dv e)
      | None => failwith ("jump: block " ++ string_of bid_src ++ " not found in " ++ string_of iid)
      end
  in
  match find_block_entry CFG fid bid_tgt with
  | None => failwith ("jump: target block " ++ string_of bid_tgt ++ " not found")
  | Some (BlockEntry phis pc_entry) =>
    'e_out <- monad_fold_right eval_phi phis e_init;
      mret (pc_entry, e_out, k)
  end.


Inductive transition X :=
| Step (s:X)
| Jump (s:X)
| Obs  (m:Event X)
.

Definition lift_err_d {A} (m:err A) (f: A -> transition state) : transition state :=
  match m with
    | inl s => Obs (Err s)
    | inr b => f b
  end.

Notation "'do' x <- m ; f" := (lift_err_d m (fun x => f)) 
   (at level 200, x ident, m at level 100, f at level 200).

Definition t_raise s : transition state :=
  Obs (Err s). 

Definition t_raise_p (p:pc) s := t_raise (s ++ ": " ++ (string_of p)).

(* TODO:  clean up the pc abstraction: 
   - replace blk_term (bk pc) with an accessor like 'fetch'
*)


Definition stepD (CFG:mcfg) (s:state) : transition state :=
  let '(pc, e, k) := s in
  do cmd <- trywith ("CFG has no instruction at " ++ string_of pc) (fetch CFG pc);
  match cmd with
  | Term (TERM_Ret (t, op)) =>
    do dv <- eval_expr e (Some t) op;
      match k with
      | [] => Obs (Fin dv)
      | (KRet e' id p') :: k' => Jump (p', add_env id dv e', k')
      | _ => t_raise_p pc "IMPOSSIBLE: Ret op in non-return configuration" 
      end

  | Term TERM_Ret_void =>
    match k with
    | [] => Obs (Fin (DVALUE_None))
    | (KRet_void e' p')::k' => Jump (p', e', k')
    | _ => t_raise_p pc "IMPOSSIBLE: Ret void in non-return configuration"
    end
          
  | Term (TERM_Br (t,op) br1 br2) =>
    do dv <- eval_expr e (Some t) op; (* TO SEE *)
      do br <- match dv with 
              (* CHKoh: | DV (VALUE_Bool true) => mret br1
                 | DV (VALUE_Bool false) => mret br2 *)
              | DVALUE_I1 comparison_bit =>
                if Int1.eq comparison_bit Int1.one then
                  mret br1
                else
                  mret br2
              | _ => failwith "Br got non-bool value"
              end;
      do st <- jump CFG (fn pc) (bk pc) br e k;
      Jump st
             
                 
  | Term (TERM_Br_1 br) =>
    do st <- jump CFG (fn pc) (bk pc) br e k;
    Jump st
             
  (* Currently unhandled LLVM terminators *)                                  
  | Term (TERM_Switch _ _ _)
  | Term (TERM_IndirectBr _ _)
  | Term (TERM_Resume _)
  | Term (TERM_Invoke _ _ _ _) => t_raise "Unsupport LLVM terminator" 
  

  | CFG.Step insn =>  (* instruction *)
    do pc_next <- trywith "no fallthrough intsruction" (incr_pc CFG pc);
      match (pt pc), insn  with
      | IId id, INSTR_Op op =>
        do dv <- eval_op e op;     
          Step (pc_next, add_env id dv e, k)

      | IId id, INSTR_Alloca t _ _ =>
        Obs (Eff (Alloca t (fun (a:value) =>  (pc_next, add_env id a e, k))))
                
      | IId id, INSTR_Load _ t (u,ptr) _ =>
        do dv <- eval_expr e (Some u) ptr;     
          match dv with
          | DVALUE_Addr a => Obs (Eff (Load t a (fun dv => (pc_next, add_env id dv e, k))))
          | _ => t_raise "ERROR: Load got non-pointer value" 
          end
            
      | IVoid _, INSTR_Store _ (t, val) (u, ptr) _ => 
        do dv <- eval_expr e (Some t) val; (* TO SEE: Added new function *)
          (* CHKoh: do dv <- eval_op e val; *)
          do v <- eval_expr e (Some u) ptr;
          match v with 
          | DVALUE_Addr a => Obs (Eff (Store a dv (fun _ => (pc_next, e, k))))
          |  _ => t_raise "ERROR: Store got non-pointer value" 
          end

      | _, INSTR_Store _ _ _ _ => t_raise "ERROR: Store to non-void ID" 
            
      (* NOTE : this doesn't yet correctly handle external calls or function pointers *)
      | pt, INSTR_Call (ret_ty, ID_Global fid) args =>
        do fnentry <- trywith ("stepD: no function " ++ (string_of fid)) (find_function_entry CFG fid); 
        let 'FunctionEntry ids pc_f := fnentry in
        do dvs <-  map_monad (fun '(t, op) => (eval_expr e (Some t) op)) args;
          match pt, ret_ty with
              | IVoid _, TYPE_Void => Step (pc_f, combine ids dvs, (KRet_void e pc_next::k))
              | IId id, _ =>          Step (pc_f, combine ids dvs, (KRet e id pc_next::k))
              | _, _ => t_raise "Call mismatch void/non-void"
          end        
                
      | _, INSTR_Call (_, ID_Local _) _ => t_raise "INSTR_Call to local"

      | _, INSTR_Unreachable => t_raise "IMPOSSIBLE: unreachable" 

        (* Currently unhandled LLVM instructions *)
      | _, INSTR_Fence 
      | _, INSTR_AtomicCmpXchg 
      | _, INSTR_AtomicRMW
      | _, INSTR_VAArg 
      | _, INSTR_LandingPad => t_raise "Unsupported LLVM intsruction" 

      (* Error states *)                                     
      | _, _ => t_raise "ID / Instr mismatch void/non-void"
      end
  end.

    

(* Assumes that the entry-point function is named "fname" and that it takes
   no parameters *)
Definition init_state (CFG:mcfg) (fname:string) : err state :=
  'fentry <- trywith ("INIT: no function named " ++ fname) (find_function_entry CFG (Name fname));
  let 'FunctionEntry ids pc_f := fentry in
    mret (pc_f, [], []).

(* Note: codomain is D'  *)
CoFixpoint step_sem (CFG:mcfg) (s:state) : Trace state :=
  match (stepD CFG s) with
  | Step s' => Tau s (step_sem CFG s')
  | Jump s' => Tau s (step_sem CFG s')
  | Obs (Err s) => Vis (Err s)
  | Obs (Fin s) => Vis (Fin s)
  | Obs (Eff m) => Vis (Eff (effects_map (step_sem CFG) m))
  end.

Definition sem (CFG:mcfg) (s:state) : Trace () := hide_taus (step_sem CFG s).


Section Properties.
(* environment facts -------------------------------------------------------- *)
  Lemma lookup_env_hd : forall id dv e, lookup_env (add_env id dv e) id = Some dv.
  Proof.
    intros id dv e.  unfold lookup_env. 
    unfold add_env.
    rewrite Util.assoc_hd. reflexivity.
  Qed.  

  Lemma lookup_env_tl : forall id1 v1 e id2,
      id1 <> id2 -> lookup_env (add_env id1 v1 e) id2 = lookup_env e id2.
  Proof.
    unfold lookup_env.
    intros id1 v1 e id2 H.
    unfold add_env. 
    rewrite Util.assoc_tl; auto.
  Qed.  


  Lemma lookup_add_env_inv :
    forall id1 v e id2 u
      (Hl: lookup_env (add_env id1 v e) id2 = Some u),
      (id1 = id2 /\ v = u) \/ (lookup_env e id2 = Some u).
  Proof.
    intros id1 v e id2 u Hl.
    unfold add_env in Hl.
    unfold lookup_env in Hl.
    remember (Util.assoc RawID.eq_dec id2 ((id1, v)::e)) as res.
    destruct res; simpl in Hl; try solve [inversion Hl].
    symmetry in Heqres.
    apply Util.assoc_cons_inv in Heqres.
    destruct Heqres as [[H1 H2]|[H1 H2]]. subst; auto.
    (* destruct (@Util.assoc_cons_inv raw_id value id2 id1 v v0 e RawID.eq_dec)  *)
    inversion Hl. tauto. 
    right. inversion Hl. subst. unfold lookup_env. exact H2.
  Qed.

  Definition pc_satisfies (CFG:mcfg) (p:pc) (P:cmd -> Prop) : Prop :=
    forall cmd, fetch CFG p = Some cmd -> P cmd.


  (* Move to AstLib.v ? *)
  Definition is_Op (i:instr) : Prop :=
    match i with
    | INSTR_Op _ => True
    | _ => False
    end.

  Definition is_Eff (i:instr) : Prop :=
    match i with 
    | INSTR_Alloca t nb a => True
    | INSTR_Load v t p a => True
    | INSTR_Store v val p a => True
    | _ => False    (* TODO: Think about call *)
    end.
  
  Definition is_Call (i:instr) : Prop :=
    match i with
    | INSTR_Call _ _ => True
    | _ => False
    end.
  
  Definition pc_non_call (CFG:mcfg) (p:pc) : Prop :=
    pc_satisfies CFG p (fun c => exists i, not (is_Call i) /\ c = CFG.Step i).

  Ltac stepD_destruct :=
    repeat (match goal with
            | [ H : context[do _ <- trywith _ ?E; _] |- _ ] => destruct E; [simpl in H | solve [inversion H]]
            | [ H : context[do _ <- ?E; _] |- _ ] => destruct E; [solve [inversion H] | simpl in H]
            | [ H : context[match ?E with _ => _ end] |- _ ] => destruct E; try solve [inversion H]; simpl in H
            | [ H : Step (?p, _ , _) = Step (?q, _, _) |- Some ?p = Some ?q ] => inversion H; auto
            | [ H : ~ (is_Call (INSTR_Call _ _)) |- _ ] => simpl in H; contradiction
            end).

  (* Not true for Call *)
  Lemma stepD_pc_incr_inversion:
    forall CFG pc1 e1 k1 pc2 e2 k2
      (Hpc: pc_non_call CFG pc1)
      (Hstep: stepD CFG (pc1, e1, k1) = Step (pc2, e2, k2)),
      incr_pc CFG pc1 = Some pc2.
  Proof.
    intros CFG pc1 e1 k1 pc2 e2 k2 Hpc Hstep.
    simpl in Hstep.
    unfold pc_non_call in Hpc. unfold pc_satisfies in Hpc.
    destruct (fetch CFG pc1); try solve [inversion Hstep]; simpl in Hstep.
    specialize Hpc with (cmd0 := c). destruct Hpc as [i [Hi Hc]]; auto.
    subst.
    destruct (incr_pc CFG pc1); [simpl in Hstep | solve [inversion Hstep]].
    stepD_destruct.
  Qed.    

End Properties.

End StepSemantics.