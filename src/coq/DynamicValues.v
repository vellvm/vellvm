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
Require Import compcert.lib.Integers compcert.lib.Floats.
Require Import Vellvm.Classes.
Require Import Vellvm.LLVMAst.
Require Import Vellvm.MemoryAddress.

Set Implicit Arguments.
Set Contextual Implicit.

Open Scope Z_scope.

(* Set up representations for for i1, i32, and i64 *) 
Module Wordsize1.
  Definition wordsize := 1%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize1.

Module Int1 := Make(Wordsize1).
Module Int32 := Integers.Int.
Module Int64 := Integers.Int64.

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

Module DVALUE(A:Vellvm.MemoryAddress.ADDRESS).
       
(* The set of dynamic values manipulated by an LLVM program. *)
Inductive dvalue : Set :=
| DVALUE_Addr (a:A.addr)
| DVALUE_I1 (x:int1)
| DVALUE_I32 (x:int32)
| DVALUE_I64 (x:int64)
| DVALUE_Double (x:ll_double)
| DVALUE_Float (x:ll_float)
| DVALUE_Undef     (* TODO: include type information? Ideally, also include some kind of constraint: (p:dvalue -> bool) *)
| DVALUE_Poison
| DVALUE_None
| DVALUE_Struct        (fields: list dvalue)
| DVALUE_Packed_struct (fields: list dvalue)
| DVALUE_Array         (elts: list dvalue)
| DVALUE_Vector        (elts: list dvalue)
.

(* TODO: include Undefined values in this way? i.e. Undef is really a predicate on values 
   Note: this isn't correct because it won't allow for undef fields of a struct or elts of an array
Inductive dvalue' : Set :=
| DVALUE_Undef (p:dvalue -> bool) (* TODO: used to include type information. is it necessary? (t:dtyp)  *)
| DVALUE_Val (d:dvalue).
*)

Definition is_DVALUE_I1 (d:dvalue) : bool :=
  match d with
  | DVALUE_I1 _ => true
  | _ => false
  end.

Definition is_DVALUE_I32 (d:dvalue) : bool :=
  match d with
  | DVALUE_I32 _ => true
  | _ => false
  end.

Definition is_DVALUE_I64 (d:dvalue) : bool :=
  match d with
  | DVALUE_I64 _ => true
  | _ => false
  end.


Definition undef_i1  := DVALUE_Undef.
Definition undef_i32 := DVALUE_Undef.
Definition undef_i64 := DVALUE_Undef.

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
  Fixpoint vec_loop (f:dvalue -> dvalue -> err dvalue) (elts:list (dvalue * dvalue))
    : err (list dvalue) :=
    monad_fold_right (fun acc '(e1, e2) =>
                         'val <- f e1 e2;
                         mret (val :: acc)
                       ) elts [].
    
  (* Integer iop evaluation, called from eval_iop. 
     Here the values must be integers. Helper defined
     in order to prevent eval_iop from being recursive. *)
  Definition eval_iop_integer_h iop v1 v2 : err dvalue :=
    match v1, v2 with
    | DVALUE_I1 i1, DVALUE_I1 i2 => integer_op 1 iop i1 i2
    | DVALUE_I32 i1, DVALUE_I32 i2 => integer_op 32 iop i1 i2
    | DVALUE_I64 i1, DVALUE_I64 i2 => integer_op 64 iop i1 i2
    | _, _ => failwith "ill_typed-iop"
    end.
  Arguments eval_iop_integer_h _ _ _ : simpl nomatch.

  (* I split the definition between the vector and other evaluations because
     otherwise eval_iop should be recursive to allow for vector calculations, 
     but coq can't find a fixpoint. *)
  Definition eval_iop iop v1 v2 : err dvalue :=
    match v1, v2 with
    | (DVALUE_Vector elts1), (DVALUE_Vector elts2) =>
      'val <- vec_loop (eval_iop_integer_h iop) (List.combine elts1 elts2);
      mret (DVALUE_Vector val)
    | _, _ => eval_iop_integer_h iop v1 v2
    end.
  Arguments eval_iop _ _ _ : simpl nomatch.


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
  
  Definition eval_icmp icmp v1 v2 : err dvalue :=
    match v1, v2 with
    | DVALUE_I1 i1, DVALUE_I1 i2 => integer_cmp 1 icmp i1 i2
    | DVALUE_I32 i1, DVALUE_I32 i2 => integer_cmp 32 icmp i1 i2
    | DVALUE_I64 i1, DVALUE_I64 i2 => integer_cmp 64 icmp i1 i2
    | _, _ => failwith "ill_typed-icmp"
    end.
  Arguments eval_icmp _ _ _ : simpl nomatch.


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
  
  Definition eval_fop (fop:fbinop) (v1:dvalue) (v2:dvalue) : err dvalue :=
    match v1, v2 with
    | DVALUE_Float f1, DVALUE_Float f2 => float_op fop f1 f2
    | DVALUE_Double d1, DVALUE_Double d2 => double_op fop d1 d2
    | _, _ => failwith "ill_typed-fop"
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


  (* Same deal as above with the helper *)
  Definition eval_select_h cnd v1 v2 : err dvalue :=
    match cnd with
    | DVALUE_I1 i =>
      mret (if Int1.unsigned i =? 1 then v1 else v2)
    | _ => failwith "ill_typed-select"
    end.
  Arguments eval_select_h _ _ _ : simpl nomatch.

  
  Definition eval_select cnd v1 v2 : err dvalue :=
    match cnd, v1, v2 with
    | (DVALUE_Vector es), (DVALUE_Vector es1), (DVALUE_Vector es2) =>
      (* vec needs to loop over es, es1, and es2. Is there a way to
         generalize vec_loop to cover this? (make v1,v2 generic?) *)
      let fix loop elts := 
          match elts with
          | [] => mret []
          | (cnd,(v1,v2)) :: tl =>
              'val <- eval_select_h cnd v1 v2;
              'vec <- loop tl;
              mret (val :: vec)
          end in
      'val <- loop (List.combine es (List.combine es1 es2));
      mret (DVALUE_Vector val)
    | _, _, _ => eval_select_h cnd v1 v2
    end.
  Arguments eval_select _ _ _ : simpl nomatch.
  
  (* Helper function for indexing into a structured datatype 
     for extractvalue and insertvalue *)
  Definition index_into_str (v:dvalue) (idx:LLVMAst.int) : err dvalue :=
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
    let fix loop (acc elts:list dvalue) (i:LLVMAst.int) :=
        match elts with
        | [] => failwith "index out of bounds"
        | h :: tl =>
          if idx =? 0 then mret (acc ++ (v :: tl))
          else loop (acc ++ [h]) tl (i-1)
        end%list in
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

  
End DVALUE.
