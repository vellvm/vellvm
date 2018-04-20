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

Require Import Vellvm.Classes.
Require Import Vellvm.Util.
Require Import Vellvm.Trace.
Require Import Vellvm.LLVMAst.
Require Import Vellvm.AstLib.
Require Import Vellvm.CFG.
Require Import Vellvm.LLVMBaseTypes.
Require Import Vellvm.LLVMIO.
Require Import Vellvm.TypeUtil.
Import ListNotations.


Set Implicit Arguments.
Set Contextual Implicit.

Open Scope Z_scope.
Open Scope string_scope.

Module StepSemantics(A:ADDR).
  Module DV := DVALUE(A).
  Import DV.
  

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
  
  Fixpoint string_of_env' (e:list (raw_id * dvalue)) : string :=
    match e with
    | [] => ""
    | (lid, _)::rest => (string_of_raw_id lid) ++ " " ++ (string_of_env' rest)
    end.

  Instance string_of_env : StringOf env := fun env => string_of_env' (ENV.elements env).
  
  Definition lookup_env {X} (e:ENV.t X) (id:raw_id) : err X :=
    match ENV.find id e with
    | Some v => mret v
    | None => failwith ("lookup_env: failed to find id = " ++ (string_of id))
    end.

  Definition lookup_id (g:genv) (e:env) (i:ident) : err dvalue :=
    match i with
    | ID_Global x => lookup_env g x
    | ID_Local x => lookup_env e x
    end.
  
  Definition add_env := ENV.add.

  (* Arithmetic Operations ---------------------------------------------------- *)
  Section ARITHMETIC.

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
  Definition integer_op (bits:Z) (iop:ibinop) (x y:inttyp bits) : err dvalue :=
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
  Fixpoint vec_loop (f:dvalue -> dvalue -> err dvalue) (elts:list ((dtyp * dvalue) * (dtyp * dvalue)))
    : err (list (dtyp * dvalue)) :=
    monad_fold_right (fun acc e =>
                       match e with
                       | pair (pair t e1) (pair _ e2) =>
                         'val <- f e1 e2;
                         mret (pair t val :: acc)
                       end) elts [].
    
  (* Integer iop evaluation, called from eval_iop. 
     Here the values must be integers. Helper defined
     in order to prevent eval_iop from being recursive. *)
  Definition eval_iop_integer_h t iop v1 v2 : err dvalue :=
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
  Definition eval_iop t iop v1 v2 : err dvalue :=
    match t, v1, v2 with
    | TYPE_Vector s (TYPE_I i), (DVALUE_Vector elts1), (DVALUE_Vector elts2) =>
      'val <- vec_loop (eval_iop_integer_h (TYPE_I i) iop) (List.combine elts1 elts2);
      mret (DVALUE_Vector val)
    | _, _, _ => eval_iop_integer_h t iop v1 v2
    end.
  Arguments eval_iop _ _ _ _ : simpl nomatch.


  Definition eval_i1_icmp icmp x y : dvalue :=
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
  
  Definition integer_cmp bits icmp (x y:inttyp bits) : err dvalue :=
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


  Definition double_op (fop:fbinop) (v1:ll_double) (v2:ll_double) : err dvalue :=
    match fop with
    | FAdd => mret (DVALUE_Double (Float.add v1 v2))
    | FSub => mret (DVALUE_Double (Float.sub v1 v2))
    | FMul => mret (DVALUE_Double (Float.mul v1 v2))
    | FDiv => mret (DVALUE_Double (Float.div v1 v2))
    | FRem => failwith "unimplemented"
    end.
  
  Definition float_op (fop:fbinop) (v1:ll_float) (v2:ll_float) : err dvalue :=
    match fop with
    | FAdd => mret (DVALUE_Float (Float32.add v1 v2))
    | FSub => mret (DVALUE_Float (Float32.sub v1 v2))
    | FMul => mret (DVALUE_Float (Float32.mul v1 v2))
    | FDiv => mret (DVALUE_Float (Float32.div v1 v2))
    | FRem => failwith "unimplemented"
    end.
  
  Definition eval_fop (t:typ) (fop:fbinop) (v1:dvalue) (v2:dvalue) : err dvalue :=
    match t, v1, v2 with
    | TYPE_Float, DVALUE_Float f1, DVALUE_Float f2 => float_op fop f1 f2
    | TYPE_Double, DVALUE_Double d1, DVALUE_Double d2 => double_op fop d1 d2
    | _, _, _ => failwith "ill_typed-fop"
    end. 

  Definition not_nan32 (f:ll_float) : bool :=
    negb (compcert.flocq.Appli.Fappli_IEEE.is_nan _ _ f). 

  Definition ordered32 (f1 f2:ll_float) : bool :=
    andb (not_nan32 f1) (not_nan32 f2).

  Definition not_nan64 (f:ll_double) : bool :=
    negb (compcert.flocq.Appli.Fappli_IEEE.is_nan _ _ f). 

  Definition ordered64 (f1 f2:ll_double) : bool :=
    andb (not_nan64 f1) (not_nan64 f2).
  
  Definition float_cmp (fcmp:fcmp) (x:ll_float) (y:ll_float) : dvalue :=
    if match fcmp with
       | FFalse => false
       | FOeq => andb (ordered32 x y) (Float32.cmp Ceq x y)
       | FOgt => andb (ordered32 x y) (Float32.cmp Cgt x y)
       | FOge => andb (ordered32 x y) (Float32.cmp Cge x y)
       | FOlt => andb (ordered32 x y) (Float32.cmp Clt x y)
       | FOle => andb (ordered32 x y) (Float32.cmp Cle x y)
       | FOne => andb (ordered32 x y) (Float32.cmp Cne x y)
       | FOrd => ordered32 x y
       | FUno => negb (ordered32 x y)
       | FUeq => (Float32.cmp Ceq x y)
       | FUgt => (Float32.cmp Cgt x y)
       | FUge => (Float32.cmp Cge x y)
       | FUlt => (Float32.cmp Clt x y)
       | FUle => (Float32.cmp Cle x y)
       | FUne => (Float32.cmp Cne x y)
       | FTrue => true
       end
    then DVALUE_I1 Int1.one else DVALUE_I1 Int1.zero.
  Arguments float_cmp _ _ _ : simpl nomatch.

  Definition double_cmp (fcmp:fcmp) (x:ll_double) (y:ll_double) : dvalue :=
    if match fcmp with
       | FFalse => false
       | FOeq => andb (ordered64 x y) (Float.cmp Ceq x y)
       | FOgt => andb (ordered64 x y) (Float.cmp Cgt x y)
       | FOge => andb (ordered64 x y) (Float.cmp Cge x y)
       | FOlt => andb (ordered64 x y) (Float.cmp Clt x y)
       | FOle => andb (ordered64 x y) (Float.cmp Cle x y)
       | FOne => andb (ordered64 x y) (Float.cmp Cne x y)
       | FOrd => ordered64 x y
       | FUno => negb (ordered64 x y)
       | FUeq => (Float.cmp Ceq x y)
       | FUgt => (Float.cmp Cgt x y)
       | FUge => (Float.cmp Cge x y)
       | FUlt => (Float.cmp Clt x y)
       | FUle => (Float.cmp Cle x y)
       | FUne => (Float.cmp Cne x y)
       | FTrue => true
       end
    then DVALUE_I1 Int1.one else DVALUE_I1 Int1.zero.
    Arguments double_cmp _ _ _ : simpl nomatch.
  
  Definition eval_fcmp (fcmp:fcmp) (v1:dvalue) (v2:dvalue) : err dvalue :=
    match v1, v2 with
    | DVALUE_Float f1, DVALUE_Float f2 => mret (float_cmp fcmp f1 f2)
    | DVALUE_Double f1, DVALUE_Double f2 => mret (double_cmp fcmp f1 f2)
    | _, _ => failwith "ill_typed-fcmp"
    end.

  End ARITHMETIC.


  Section CONVERSIONS.

  Definition eval_conv_h conv t1 x t2 : Trace dvalue :=
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
    | Fptrunc
    | Fpext
    | Uitofp
    | Sitofp
    | Fptoui
    | Fptosi => failwith "TODO: floating point conversion not yet implemented"
    | Inttoptr =>
      match t1, t2 with
      | TYPE_I 64, TYPE_Pointer t => Trace.Vis (ItoP x) mret
      | _, _ => raise "ERROR: Inttoptr got illegal arguments"
      end 
    | Ptrtoint =>
      match t1, t2 with
      | TYPE_Pointer t, TYPE_I 64 => Trace.Vis (PtoI x) mret
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
      failwith "vectors unimplemented"
    | _, _ => eval_conv_h conv t1 x t2
    end.
  Arguments eval_conv _ _ _ _ : simpl nomatch.

  End CONVERSIONS.


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
  Definition index_into_str (v:dvalue) (idx:LLVMAst.int) : err (dtyp * dvalue) :=
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
  Definition insert_into_str (str:dvalue) (v:dvalue) (idx:LLVMAst.int) : err dvalue :=
    let fix loop (acc elts:list (dtyp * dvalue)) (i:LLVMAst.int) :=
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


  Definition dv_zero_initializer (t:dtyp) : err dvalue :=
    failwith "dv_zero_initializer unimplemented".


Section IN_CFG_CONTEXT.
Variable CFG:mcfg.

Definition eval_typ (t:typ) : dtyp :=
  TypeUtil.normalize_type (m_type_defs CFG) t.


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
             'v <- eval_exp (Some dt) ex; mret (dt, v)
  in
  match o with
  | EXP_Ident i => lift_err_d (lookup_id g e i) mret

  | EXP_Integer x =>
    match top with
    | None =>  failwith "eval_exp given untyped EXP_Integer"
    | Some (DTYPE_I bits) => do w <- coerce_integer_to_int bits x; mret w
    | _ => failwith "bad type for constant int"
    end

  | EXP_Float x   =>
    match top with
    | None => failwith "eval_exp given untyped EXP_Float"
    | Some DTYPE_Float  =>  mret (DVALUE_Float (Float32.of_double x))
    | Some DTYPE_Double =>  mret (DVALUE_Double x)
    | _ => failwith "bad type for constant float"
    end

  | EXP_Hex x     =>
    match top with
    | None => failwith "eval_exp given untyped EXP_Hex"
    | Some DTYPE_Float  =>  mret (DVALUE_Float (Float32.of_double x))
    | Some DTYPE_Double =>  mret (DVALUE_Double x)
    | _ => failwith "bad type for constant hex float"
    end

  | EXP_Bool b    =>
    match b with
    | true => mret (DVALUE_I1 Int1.one)
    | false => mret (DVALUE_I1 Int1.zero)
    end

  | EXP_Null      => mret (DVALUE_Addr A.null)

  | EXP_Zero_initializer =>
    match top with
    | None => failwith "eval_exp given untyped EXP_Zero_initializer"
    | Some t => do w <- dv_zero_initializer t; mret w
    end

  | EXP_Cstring s =>
    failwith "EXP_Cstring not yet implemented"

  | EXP_Undef     =>
    match top with
    | None => failwith "eval_exp given untyped EXP_Undef"
    | Some t => mret (DVALUE_Undef t)
    end

  (* Question: should we do any typechecking for aggregate types here? *)
  (* Option 1: do no typechecking: *)
  | EXP_Struct es =>
    'vs <- map_monad eval_texp es;
      mret (DVALUE_Struct vs)

  (* Option 2: do a little bit of typechecking *)
  | EXP_Packed_struct es =>
    match top with
    | None => failwith "eval_exp given untyped EXP_Struct"
    | Some (DTYPE_Packed_struct _) =>
      'vs <- map_monad eval_texp es;
        mret (DVALUE_Packed_struct vs)
    | _ => failwith "bad type for VALUE_Packed_struct"
    end

  | EXP_Array es =>
    'vs <- map_monad eval_texp es;
      mret (DVALUE_Array vs)
    
  | EXP_Vector es =>
    'vs <- map_monad eval_texp es;
      mret (DVALUE_Vector vs)

  | OP_IBinop iop t op1 op2 =>
    let dt := eval_typ t in
    'v1 <- eval_exp (Some dt) op1;
    'v2 <- eval_exp (Some dt) op2;
    do w <- (eval_iop t iop) v1 v2;
    mret w

  | OP_ICmp cmp t op1 op2 =>
    let dt := eval_typ t in
    'v1 <- eval_exp (Some dt) op1;                   
    'v2 <- eval_exp (Some dt) op2;
    do w <- (eval_icmp t cmp) v1 v2;
    mret w

  | OP_FBinop fop fm t op1 op2 =>
    let dt := eval_typ t in    
    'v1 <- eval_exp (Some dt) op1;
    'v2 <- eval_exp (Some dt) op2;
    do w <- (eval_fop t fop) v1 v2;
    mret w

  | OP_FCmp fcmp t op1 op2 =>
    let dt := eval_typ t in
    'v1 <- eval_exp (Some dt) op1;
    'v2 <- eval_exp (Some dt) op2;
    do w <- (eval_fcmp fcmp) v1 v2;
    mret w
              
  | OP_Conversion conv t1 op t2 =>
    let dt1 := eval_typ t1 in
    'v <- eval_exp (Some dt1) op;
    eval_conv conv t1 v t2

  | OP_GetElementPtr _ (TYPE_Pointer t, ptrval) idxs =>
    let dt := eval_typ t in
    'vptr <- eval_exp (Some DTYPE_Pointer) ptrval;
    'vs <- map_monad (fun '(_, index) => eval_exp (Some (DTYPE_I 32)) index) idxs;
    Trace.Vis (GEP dt vptr vs) mret

  | OP_GetElementPtr _ (_, _) _ =>
    failwith "getelementptr has non-pointer type annotation"
              
  | OP_ExtractElement vecop idx =>
    (*    'vec <- monad_app_snd (eval_exp e) vecop;
    'vidx <- monad_app_snd (eval_exp e) idx;  *)
    failwith "extractelement not implemented" (* TODO: Extract Element *) 
      
  | OP_InsertElement vecop eltop idx =>
(*    'vec <- monad_app_snd (eval_exp e) vecop;
    'v <- monad_app_snd (eval_exp e) eltop;
    'vidx <- monad_app_snd (eval_exp e) idx; *)
    failwith "insertelement not implemented" (* TODO *)
    
  | OP_ShuffleVector vecop1 vecop2 idxmask =>
(*    'vec1 <- monad_app_snd (eval_exp e) vecop1;
    'vec2 <- monad_app_snd (eval_exp e) vecop2;      
    'vidx <- monad_app_snd (eval_exp e) idxmask; *)
    failwith "shufflevector not implemented" (* TODO *)

  | OP_ExtractValue strop idxs =>
    let '(t, str) := strop in
    let dt := eval_typ t in
    'str <- eval_exp (Some dt) str;
    let fix loop str idxs : err dvalue :=
        match idxs with
        | [] => mret str
        | i :: tl =>
          '(_, v) <- index_into_str str i;
          loop v tl
        end in
    do w <- loop str idxs;
      mret w
        
  | OP_InsertValue strop eltop idxs =>
    (*
    '(t1, str) <- monad_app_snd (eval_exp e) strop;
    '(t2, v) <- monad_app_snd (eval_exp e) eltop;
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
    
  | OP_Select (t, cnd) (t1, op1) (t2, op2) =>
    let dt := eval_typ t in
    let dt1 := eval_typ t1 in
    let dt2 := eval_typ t2 in
    'cndv <- eval_exp (Some dt) cnd;
    'v1 <- eval_exp (Some dt1) op1;
    'v2 <- eval_exp (Some dt2) op2;
    do w <- eval_select t cndv t1 v1 v2;
    mret w
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

Definition raise_p {X} (p:pc) s : Trace X := raise (s ++ ": " ++ (string_of p)).
Definition cont (s:state) : Trace result := mret (Step s).
Definition halt (v:dvalue) : Trace result := mret (Done v).

  
Definition jump (fid:function_id) (bid_src:block_id) (bid_tgt:block_id) (g:genv) (e_init:env) (k:stack) : Trace result :=
  let eval_phi (e:env) '(iid, Phi t ls) :=
      match assoc RawIDOrd.eq_dec bid_src ls with
      | Some op =>
        let dt := eval_typ t in
        'dv <- eval_exp g e_init (Some dt) op;
          mret (add_env iid dv e)
      | None => failwith ("jump: block " ++ string_of bid_src ++ " not found in " ++ string_of iid)
      end
  in
  match find_block_entry CFG fid bid_tgt with
  | None => raise ("jump: target block " ++ string_of bid_tgt ++ " not found")
  | Some (BlockEntry phis pc_entry) =>
      'e_out <- monad_fold_right eval_phi phis e_init;
      cont (g, pc_entry, e_out, k)
  end.

Definition step (s:state) : Trace result :=
  let '(g, pc, e, k) := s in
  let eval_exp top exp := eval_exp g e top exp in
  
  do cmd <- trywith ("CFG has no instruction at " ++ string_of pc) (fetch CFG pc);
  match cmd with
  | Term (TERM_Ret (t, op)) =>
    'dv <- eval_exp (Some (eval_typ t)) op;
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
    'dv <- eval_exp (Some (eval_typ t)) op; 
    'br <- match dv with 
            | DVALUE_I1 comparison_bit =>
              if Int1.eq comparison_bit Int1.one then
                mret br1
              else
                mret br2
            | _ => failwith "Br got non-bool value"
            end;
    jump (fn pc) (bk pc) br g e k
             
  | Term (TERM_Br_1 br) =>
    jump (fn pc) (bk pc) br g e k

             
  (* Currently unhandled LLVM terminators *)                                  
  | Term (TERM_Switch _ _ _)
  | Term (TERM_IndirectBr _ _)
  | Term (TERM_Resume _)
  | Term (TERM_Invoke _ _ _ _) => raise_p pc "Unsupport LLVM terminator" 

  | Inst insn =>  (* instruction *)
    do pc_next <- trywith "no fallthrough intsruction" (incr_pc CFG pc);
    match (pt pc), insn  with

      | IId id, INSTR_Op op =>
         'dv <- eval_op g e op;     
          cont (g, pc_next, add_env id dv e, k)
          
      | IId id, INSTR_Alloca t _ _ =>
        Trace.Vis (Alloca (eval_typ t)) (fun (a:dvalue) =>  cont (g, pc_next, add_env id a e, k))
                
      | IId id, INSTR_Load _ t (u,ptr) _ =>
        'dv <- eval_exp (Some (eval_typ u)) ptr;
          Trace.Vis (Load (eval_typ t) dv) (fun dv => cont (g, pc_next, add_env id dv e, k))
            
      | IVoid _, INSTR_Store _ (t, val) (u, ptr) _ => 
        'dv <- eval_exp (Some (eval_typ t)) val; 
        'v <- eval_exp (Some (eval_typ u)) ptr;
          Trace.Vis (Store v dv) (fun _ => cont (g, pc_next, e, k))

      | _, INSTR_Store _ _ _ _ => raise "ERROR: Store to non-void ID" 

      | pt, INSTR_Call (t, f) args =>
        'fv <- eval_exp None f;
        'dvs <-  map_monad (fun '(t, op) => (eval_exp (Some (eval_typ t)) op)) args;
        match fv with
        | DVALUE_Addr addr =>
          (* TODO: lookup fid given addr from global environment *)
          let fid := Name "" in
          match (find_function_entry CFG fid) with
          | Some fnentry =>
            let 'FunctionEntry ids pc_f := fnentry in
            do bs <- combine_lists_err ids dvs;
              let env := env_of_assoc bs in
              match pt with
              | IVoid _ => cont (g, pc_f, env, (KRet_void e pc_next::k))
              | IId id =>  cont (g, pc_f, env, (KRet e id pc_next::k))          
              end
          | None => (* This must have been a registered external function *)
            match fid with
              (* TODO: make sure the external call's type is correct *)
            | Name s => Trace.Vis (Call DTYPE_Void s dvs) (fun dv => cont (g, pc_next, e, k))
            | _ => raise ("step: no function " ++ (string_of fid))
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
      | _, INSTR_LandingPad => raise_p pc "Unsupported LLVM intsruction" 

      (* Error states *)                                     
      | _, _ => raise_p pc "ID / Instr mismatch void/non-void"
      end
  end.

(* Defining the Global Environment ------------------------------------------------------- *)

Definition allocate_globals (gs:list global) : Trace genv :=
  monad_fold_right
    (fun (m:genv) (g:global) =>
       Trace.Vis (Alloca (eval_typ (g_typ g))) (fun v => mret (ENV.add (g_ident g) v m))) gs (@ENV.empty _).


Definition register_declaration (g:genv) (d:declaration) : Trace genv :=
    Trace.Vis (DeclareFun (dc_name d)) (fun v => mret (ENV.add (dc_name d) v g)).

Definition register_functions (g:genv) : Trace genv :=
  monad_fold_right register_declaration
                   ((m_declarations CFG) ++ (List.map df_prototype (m_definitions CFG)))
                   g.
  
Definition initialize_globals (gs:list global) (g:genv) : Trace unit :=
  monad_fold_right
    (fun (_:unit) (glb:global) =>
       let dt := eval_typ (g_typ glb) in
       do a <- lookup_env g (g_ident glb);
       'dv <-
           match (g_exp glb) with
           | None => mret (DVALUE_Undef dt)
           | Some e => eval_exp g (@ENV.empty _) (Some dt) e
           end;
       Trace.Vis (Store a dv) mret)
    gs tt.
  
Definition build_global_environment : Trace genv :=
  'g <- allocate_globals (m_globals CFG);
  'g2 <- register_functions g;
  '_ <- initialize_globals (m_globals CFG) g2;
  mret g2.

(* Assumes that the entry-point function is named "fname" and that it takes
   no parameters *)
Definition init_state (fname:string) : Trace state :=
  'g <- build_global_environment;
  'fentry <- trywith ("INIT: no function named " ++ fname) (find_function_entry CFG (Name fname));
  let 'FunctionEntry ids pc_f := fentry in
    mret (g, pc_f, (@ENV.empty dvalue), []).

CoFixpoint step_sem (r:result) : Trace dvalue :=
  match r with
  | Done v => mret v
  | Step s => 'x <- step s ; step_sem x
  end.

End IN_CFG_CONTEXT.

End StepSemantics.