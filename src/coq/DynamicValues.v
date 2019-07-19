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
     ZArith List String Omega.

From ExtLib Require Import 
     Core.RelDec
     Programming.Eqv
     Programming.Show
     Structures.Monads
     Data.Nat
     Data.List.

From Vellvm Require Import
     LLVMAst
     AstLib
     MemoryAddress
     Error
     Util
     DynamicTypes.

Require Import Integers Floats.

Import EqvNotation.
Import MonadNotation.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

Open Scope Z_scope.

Instance Eqv_nat : Eqv nat := (@eq nat).

(* Set up representations for for i1, i32, and i64 *)
Module Wordsize1.
  Definition wordsize := 1%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize1.

Module Wordsize8.
  Definition wordsize := 8%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize8.

Module Int1 := Make(Wordsize1).
Module Int8 := Make(Wordsize8).
Module Int32 := Integers.Int.
Module Int64 := Integers.Int64.

Definition int1 := Int1.int.
Definition int8 := Int8.int.
Definition int32 := Int32.int.
Definition int64 := Int64.int.

Definition inttyp (x:Z) : Type :=
  match x with
  | 1 => int1
  | 8 => int8
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
| DVALUE_I8 (x:int8)
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

Section hiding_notation.
  Import ShowNotation.
  Local Open Scope show_scope.

  Fixpoint show_dvalue' (dv:dvalue) : showM :=
    match dv with 
    | DVALUE_Addr a => "address" (* TODO: insist that memory models can print addresses? *)
    | DVALUE_I1 x => "dvalue(i1)"
    | DVALUE_I8 x => "dvalue(i8)"
    | DVALUE_I32 x => "dvalue(i32)"
    | DVALUE_I64 x => "dvalue(i64)"
    | DVALUE_Double x => "dvalue(double)"
    | DVALUE_Float x => "dvalue(float)"
    | DVALUE_Undef => "undef"   
    | DVALUE_Poison => "poison"
    | DVALUE_None => "none"
    | DVALUE_Struct fields
      => ("{" << iter_show (List.map (fun x => (show_dvalue' x) << ",") fields) << "}")
    | DVALUE_Packed_struct fields
      => ("packed{" << iter_show (List.map (fun x => (show_dvalue' x) << ",") fields) << "}")
    | DVALUE_Array elts
      => ("[" << iter_show (List.map (fun x => (show_dvalue' x) << ",") elts) << "]")
    | DVALUE_Vector elts
      => ("<" << iter_show (List.map (fun x => (show_dvalue' x) << ",") elts) << ">")                  
    end%string.
  
  Global Instance show_dvalue : Show dvalue := show_dvalue'.

End hiding_notation.

Ltac dec_dvalue :=
  match goal with
  | [ |- { ?X ?a = ?X ?b} + { ?X ?a <> ?X ?b} ] => idtac
  | [ |- { ?X ?a = ?Y ?b} + { ?X ?a <> ?Y ?b} ] => right; intros H; inversion H
  | [ |- { ?X = ?X } + { ?X <> ?X } ] => left; reflexivity
  | [ |- { ?X = ?Y } + { ?X <> ?Y } ] => right; intros H; inversion H
  end.
                                                               
Section DecidableEquality.

  Fixpoint dvalue_eqb (d1 d2:dvalue) : bool :=
    let lsteq := list_eqb (Build_RelDec eq dvalue_eqb) in
    match d1, d2 with
    | DVALUE_Addr a1, DVALUE_Addr a2 =>
      if A.eq_dec a1 a2 then true else false
    | DVALUE_I1 x1, DVALUE_I1 x2 =>
      if Int1.eq_dec x1 x2 then true else false 
    | DVALUE_I8 x1, DVALUE_I8 x2 =>
      if Int8.eq_dec x1 x2 then true else false 
    | DVALUE_I32 x1, DVALUE_I32 x2 =>
      if Int32.eq_dec x1 x2 then true else false 
    | DVALUE_I64 x1, DVALUE_I64 x2 =>
      if Int64.eq_dec x1 x2 then true else false 
    | DVALUE_Double x1, DVALUE_Double x2 =>
      if Float.eq_dec x1 x2 then true else false
    | DVALUE_Float x1, DVALUE_Float x2 =>
      if Float32.eq_dec x1 x2 then true else false
    | DVALUE_Undef, DVALUE_Undef => true
    | DVALUE_Poison, DVALUE_Poison => true
    | DVALUE_None, DVALUE_None => true
    | DVALUE_Struct f1, DVALUE_Struct f2 =>
      lsteq f1 f2
    | DVALUE_Packed_struct f1, DVALUE_Packed_struct f2 =>
      lsteq f1 f2
    | DVALUE_Array f1, DVALUE_Array f2 =>
      lsteq f1 f2
    | DVALUE_Vector f1, DVALUE_Vector f2 =>
      lsteq f1 f2
    | _, _ => false
    end.
  

  Lemma dvalue_eq_dec : forall (d1 d2:dvalue), {d1 = d2} + {d1 <> d2}.
    refine (fix f d1 d2 :=
    let lsteq_dec := list_eq_dec f in
    match d1, d2 with
    | DVALUE_Addr a1, DVALUE_Addr a2 => _
    | DVALUE_I1 x1, DVALUE_I1 x2 => _
    | DVALUE_I8 x1, DVALUE_I8 x2 => _
    | DVALUE_I32 x1, DVALUE_I32 x2 => _
    | DVALUE_I64 x1, DVALUE_I64 x2 => _
    | DVALUE_Double x1, DVALUE_Double x2 => _
    | DVALUE_Float x1, DVALUE_Float x2 => _
    | DVALUE_Undef, DVALUE_Undef => _
    | DVALUE_Poison, DVALUE_Poison => _
    | DVALUE_None, DVALUE_None => _
    | DVALUE_Struct f1, DVALUE_Struct f2 => _
    | DVALUE_Packed_struct f1, DVALUE_Packed_struct f2 => _
    | DVALUE_Array f1, DVALUE_Array f2 => _
    | DVALUE_Vector f1, DVALUE_Vector f2 => _
    | _, _ => _
    end);  ltac:(dec_dvalue).
    - destruct (A.eq_dec a1 a2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (Int1.eq_dec x1 x2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (Int8.eq_dec x1 x2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (Int32.eq_dec x1 x2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (Int64.eq_dec x1 x2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (Float.eq_dec x1 x2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (Float32.eq_dec x1 x2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (lsteq_dec f1 f2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (lsteq_dec f1 f2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (lsteq_dec f1 f2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (lsteq_dec f1 f2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
  Qed.
  
  Global Instance eq_dec_dvalue : RelDec (@eq dvalue) := RelDec_from_dec (@eq dvalue) (@dvalue_eq_dec).
  Global Instance eqv_dvalue : Eqv dvalue := (@eq dvalue).
  Hint Unfold eqv_dvalue.
End DecidableEquality.

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

Definition is_DVALUE_I8 (d:dvalue) : bool :=
  match d with
  | DVALUE_I8 _ => true
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
Definition undef_i8  := DVALUE_Undef.
Definition undef_i32 := DVALUE_Undef.
Definition undef_i64 := DVALUE_Undef.
Definition undef_int := DVALUE_Undef.


Class VInt I : Type :=
  {
    (* Comparisons *)
    eq : I -> I -> bool;
    cmp : comparison -> I -> I -> bool;
    cmpu : comparison -> I -> I -> bool;

    (* Constants *)
    bitwidth : nat;
    zero : I;
    one : I;

    (* Arithmetic *)
    add : I -> I -> I;
    add_carry : I -> I -> I -> I;
    add_overflow : I -> I -> I -> I;

    sub : I -> I -> I;
    sub_borrow : I -> I -> I -> I;
    sub_overflow : I -> I -> I -> I;

    mul : I -> I -> I;

    divu : I -> I -> I;
    divs : I -> I -> I;
    modu : I -> I -> I;
    mods : I -> I -> I;

    shl : I -> I -> I;
    shr : I -> I -> I;
    shru : I -> I -> I;

    negative : I -> I;

    (* Logic *)
    and : I -> I -> I;
    or : I -> I -> I;
    xor : I -> I -> I;

    (* Bounds *)
    min_signed : Z;
    max_signed : Z;

    (* Conversion *)
    to_dvalue : I -> dvalue;
    unsigned : I -> Z;
    signed : I -> Z;

    repr : Z -> I;
  }.


  Global Instance VInt1 : VInt Int1.int :=
  {
    (* Comparisons *)
    eq := Int1.eq;
    cmp := Int1.cmp;
    cmpu := Int1.cmpu;

    bitwidth := 1;

    (* Constants *)
    zero := Int1.zero;
    one := Int1.one;    

    (* Arithmetic *)
    add := Int1.add;
    add_carry := Int1.add_carry;
    add_overflow := Int1.add_overflow;

    sub := Int1.sub;
    sub_borrow := Int1.sub_borrow;
    sub_overflow := Int1.sub_overflow;

    mul := Int1.mul;

    divu := Int1.divu;
    divs := Int1.divs;
    modu := Int1.modu;
    mods := Int1.mods;

    shl := Int1.shl;
    shr := Int1.shr;
    shru := Int1.shru;

    negative := Int1.negative;

    (* Logic *)
    and := Int1.and;
    or := Int1.or;
    xor := Int1.xor;

    (* Bounds *)
    min_signed := Int1.min_signed;
    max_signed := Int1.max_signed;
    
    (* Conversion *)
    to_dvalue := DVALUE_I1;
    unsigned := Int1.unsigned;
    signed := Int1.signed;

    repr := Int1.repr;
  }.


  Global Instance VInt8 : VInt Int8.int :=
  {
    (* Comparisons *)
    eq := Int8.eq;
    cmp := Int8.cmp;
    cmpu := Int8.cmpu;

    bitwidth := 8;

    (* Constants *)
    zero := Int8.zero;
    one := Int8.one;    

    (* Arithmetic *)
    add := Int8.add;
    add_carry := Int8.add_carry;
    add_overflow := Int8.add_overflow;

    sub := Int8.sub;
    sub_borrow := Int8.sub_borrow;
    sub_overflow := Int8.sub_overflow;

    mul := Int8.mul;

    divu := Int8.divu;
    divs := Int8.divs;
    modu := Int8.modu;
    mods := Int8.mods;

    shl := Int8.shl;
    shr := Int8.shr;
    shru := Int8.shru;

    negative := Int8.negative;

    (* Logic *)
    and := Int8.and;
    or := Int8.or;
    xor := Int8.xor;

    (* Bounds *)
    min_signed := Int8.min_signed;
    max_signed := Int8.max_signed;
    
    (* Conversion *)
    to_dvalue := DVALUE_I8;
    unsigned := Int8.unsigned;
    signed := Int8.signed;

    repr := Int8.repr;
  }.


  Global Instance VInt32 : VInt Int32.int :=
  {
    (* Comparisons *)
    eq := Int32.eq;
    cmp := Int32.cmp;
    cmpu := Int32.cmpu;

    bitwidth := 32;

    (* Constants *)
    zero := Int32.zero;
    one := Int32.one;    

    (* Arithmetic *)
    add := Int32.add;
    add_carry := Int32.add_carry;
    add_overflow := Int32.add_overflow;

    sub := Int32.sub;
    sub_borrow := Int32.sub_borrow;
    sub_overflow := Int32.sub_overflow;

    mul := Int32.mul;

    divu := Int32.divu;
    divs := Int32.divs;
    modu := Int32.modu;
    mods := Int32.mods;

    shl := Int32.shl;
    shr := Int32.shr;
    shru := Int32.shru;

    negative := Int32.negative;

    (* Logic *)
    and := Int32.and;
    or := Int32.or;
    xor := Int32.xor;

    (* Bounds *)
    min_signed := Int32.min_signed;
    max_signed := Int32.max_signed;
    
    (* Conversion *)
    to_dvalue := DVALUE_I32;
    unsigned := Int32.unsigned;
    signed := Int32.signed;

    repr := Int32.repr;
  }.

  Global Instance VInt64 : VInt Int64.int :=
  {
    (* Comparisons *)
    eq := Int64.eq;
    cmp := Int64.cmp;
    cmpu := Int64.cmpu;

    bitwidth := 64;

    (* Constants *)
    zero := Int64.zero;
    one := Int64.one;

    (* Arithmetic *)
    add := Int64.add;
    add_carry := Int64.add_carry;
    add_overflow := Int64.add_overflow;

    sub := Int64.sub;
    sub_borrow := Int64.sub_borrow;
    sub_overflow := Int64.sub_overflow;

    mul := Int64.mul;

    divu := Int64.divu;
    divs := Int64.divs;
    modu := Int64.modu;
    mods := Int64.mods;

    shl := Int64.shl;
    shr := Int64.shr;
    shru := Int64.shru;

    negative := Int64.negative;

    (* Logic *)
    and := Int64.and;
    or := Int64.or;
    xor := Int64.xor;

    (* Bounds *)
    min_signed := Int64.min_signed;
    max_signed := Int64.max_signed;
    
    (* Conversion *)
    to_dvalue := DVALUE_I64;
    unsigned := Int64.unsigned;
    signed := Int64.signed;

    repr := Int64.repr;
  }.


  (* Arithmetic Operations ---------------------------------------------------- *)
  Section ARITHMETIC.


  (* Evaluate integer opererations to get a dvalue.

     These operations are between VInts, which are "vellvm"
     integers. This is a typeclass that wraps all of the integer
     operations that we use for integer types with different bitwidths.
   *)
  (* SAZ: This needs to move into: [itree (UndefinedBehaviorE +' UndefE) dvalue]  *)
  Definition eval_int_op {Int} `{VInt Int} (iop:ibinop) (x y: Int) : dvalue:=
    match iop with
    (* Following to cases are probably right since they use CompCert *)
    | Add nuw nsw =>
      if orb (andb nuw (eq (add_carry x y zero) one))
             (andb nsw (eq (add_overflow x y zero) one))
      then DVALUE_Poison else to_dvalue (add x y)
    | Sub nuw nsw =>
      if orb (andb nuw (eq (sub_borrow x y zero) one))
             (andb nsw (eq (sub_overflow x y zero) one))
      then DVALUE_Poison else to_dvalue (sub x y)

    | Mul nuw nsw =>
      (* I1 mul can't overflow, just based on the 4 possible multiplications. *)
      if (bitwidth ~=? 1)%nat then to_dvalue (mul x y)
      else 
        let res := mul x y in
        let res_s' := (signed x) * (signed y) in
        if orb (andb nuw ((unsigned x) * (unsigned y) >?
                      unsigned res))
             (andb nsw (orb (min_signed >? res_s')
                            (res_s' >? max_signed)))
      then DVALUE_Poison else to_dvalue res
  
    | Shl nuw nsw =>
      if (bitwidth ~=? 1)%nat
      then
        if (unsigned y) >=? 1 then undef_int else to_dvalue x
      else
        let bz := Z.of_nat bitwidth in
        let res := shl x y in
        let res_u := unsigned res in
        let res_u' := Z.shiftl (unsigned x) (unsigned y) in
        (* Unsigned shift x right by bitwidth - y. If shifted x != sign bit * (2^y - 1),
         then there is overflow. *)
        if (unsigned y) >=? bz then undef_int
        else if orb (andb nuw (res_u' >? res_u))
                    (andb nsw (negb (Z.shiftr (unsigned x)
                                              (bz - unsigned y)
                                     =? (unsigned (negative res))
                                        * (Z.pow 2 (unsigned y) - 1))))
             then DVALUE_Poison else to_dvalue res
    | UDiv ex =>
      if andb ex (negb ((unsigned x) mod (unsigned y) =? 0))
      then DVALUE_Poison else to_dvalue (divu x y)
    | SDiv ex =>
      (* What does signed i1 mean? *)
      if andb ex (negb (((signed x) mod (signed y)) =? 0))
      then DVALUE_Poison else to_dvalue (divs x y)
    | LShr ex =>
      if (bitwidth ~=? 1)%nat
      then
        if (unsigned y) >=? 1 then undef_int else to_dvalue x
      else
        let bz := Z.of_nat bitwidth in
        if (unsigned y) >=? bz then undef_int
        else if andb ex (negb ((unsigned x)
                                 mod (Z.pow 2 (unsigned y)) =? 0))
             then DVALUE_Poison else to_dvalue (shru x y)
    | AShr ex =>
      if (bitwidth ~=? 1)%nat
      then
        if (unsigned y) >=? 1 then undef_int else to_dvalue x
      else
        let bz := Z.of_nat bitwidth in
        if (unsigned y) >=? bz then undef_int
        else if andb ex (negb ((unsigned x)
                                 mod (Z.pow 2 (unsigned y)) =? 0))
             then DVALUE_Poison else to_dvalue (shr x y)

    | URem =>
      to_dvalue (modu x y)
    | SRem =>
      to_dvalue (mods x y)
    | And =>
      to_dvalue (and x y)
    | Or =>
      to_dvalue (or x y)
    | Xor =>
      to_dvalue (xor x y)
    end.
  Arguments eval_int_op _ _ _ : simpl nomatch.


  

  (* Evaluate the given iop on the given arguments according to the bitsize *)
  Definition integer_op (bits:Z) (iop:ibinop) (x y:inttyp bits) : err dvalue :=
    match bits, x, y with
    | 1, x, y => ret (eval_int_op iop x y)
    | 8, x, y => ret (eval_int_op iop x y)
    | 32, x, y => ret (eval_int_op iop x y)
    | 64, x, y => ret (eval_int_op iop x y)
    | _, _, _ => failwith "unsupported bitsize"
    end.
  Arguments integer_op _ _ _ _ : simpl nomatch.

  (* Convert written integer constant to corresponding integer with bitsize bits.
     Takes the integer modulo 2^bits. *)
  Definition coerce_integer_to_int (bits:Z) (i:Z) : err dvalue :=
    match bits with
    | 1 => ret (DVALUE_I1 (repr i))
    | 8 => ret (DVALUE_I8 (repr i))
    | 32 => ret (DVALUE_I32 (repr i))
    | 64 => ret (DVALUE_I64 (repr i))
    | _ => failwith "unsupported integer size"
    end.
  Arguments coerce_integer_to_int _ _ : simpl nomatch.

  (* Helper for looping 2 argument evaluation over vectors, producing a vector *)

  Fixpoint vec_loop (f:dvalue -> dvalue -> err dvalue) (elts:list (dvalue * dvalue)) : err (list dvalue) :=
    monad_fold_right (fun acc '(e1, e2) =>
                         val <- f e1 e2 ;;
                         ret (val :: acc)
                       ) elts [].


  (* Integer iop evaluation, called from eval_iop.
     Here the values must be integers. Helper defined
     in order to prevent eval_iop from being recursive. *)
  Definition eval_iop_integer_h iop v1 v2 : err dvalue :=
    match v1, v2 with
    | DVALUE_I1 i1, DVALUE_I1 i2 => ret (eval_int_op iop i1 i2)
    | DVALUE_I8 i1, DVALUE_I8 i2 => ret (eval_int_op iop i1 i2)
    | DVALUE_I32 i1, DVALUE_I32 i2 => ret (eval_int_op iop i1 i2)
    | DVALUE_I64 i1, DVALUE_I64 i2 => ret (eval_int_op iop i1 i2)
    | _, _ => failwith "ill_typed-iop"
    end.
  Arguments eval_iop_integer_h _ _ _ : simpl nomatch.

  (* I split the definition between the vector and other evaluations because
     otherwise eval_iop should be recursive to allow for vector calculations,
     but coq can't find a fixpoint. *)
  (* SAZ: Here is where we want to add the case distinction  for uvalues

       - this should check for "determined" uvalues and then use eval_iop_integer_h
         otherwise leave the op symbolic

       - this should use the inclusion of dvalue into uvalue in the case that
         eval_iop_integer_h is calle
 
   *)
  Definition eval_iop iop v1 v2 : err dvalue :=
    match v1, v2 with
    | (DVALUE_Vector elts1), (DVALUE_Vector elts2) =>
      val <- vec_loop (eval_iop_integer_h iop) (List.combine elts1 elts2) ;;
      ret (DVALUE_Vector val)
    | _, _ => eval_iop_integer_h iop v1 v2
    end.
  Arguments eval_iop _ _ _ : simpl nomatch.


  Definition eval_int_icmp {Int} `{VInt Int} icmp (x y : Int) : dvalue :=
    if match icmp with
       | Eq => cmp Ceq x y
       | Ne => cmp Cne x y
       | Ugt => cmpu Cgt x y
       | Uge => cmpu Cge x y
       | Ult => cmpu Clt x y
       | Ule => cmpu Cle x y
       | Sgt => cmp Cgt x y
       | Sge => cmp Cge x y
       | Slt => cmp Clt x y
       | Sle => cmp Cle x y
       end
    then DVALUE_I1 (Int1.one) else DVALUE_I1 (Int1.zero).
  Arguments eval_int_icmp _ _ _ : simpl nomatch.

  Definition eval_icmp icmp v1 v2 : err dvalue :=
    match v1, v2 with
    | DVALUE_I1 i1, DVALUE_I1 i2 => ret (eval_int_icmp icmp i1 i2)
    | DVALUE_I8 i1, DVALUE_I8 i2 => ret (eval_int_icmp icmp i1 i2)
    | DVALUE_I32 i1, DVALUE_I32 i2 => ret (eval_int_icmp icmp i1 i2)
    | DVALUE_I64 i1, DVALUE_I64 i2 => ret (eval_int_icmp icmp i1 i2)
    | _, _ => failwith "ill_typed-icmp"
    end.
  Arguments eval_icmp _ _ _ : simpl nomatch.


  Definition double_op (fop:fbinop) (v1:ll_double) (v2:ll_double) : err dvalue :=
    match fop with
    | FAdd => ret (DVALUE_Double (Float.add v1 v2))
    | FSub => ret (DVALUE_Double (Float.sub v1 v2))
    | FMul => ret (DVALUE_Double (Float.mul v1 v2))
    | FDiv => ret (DVALUE_Double (Float.div v1 v2))
    | FRem => failwith "unimplemented"
    end.

  Definition float_op (fop:fbinop) (v1:ll_float) (v2:ll_float) : err dvalue :=
    match fop with
    | FAdd => ret (DVALUE_Float (Float32.add v1 v2))
    | FSub => ret (DVALUE_Float (Float32.sub v1 v2))
    | FMul => ret (DVALUE_Float (Float32.mul v1 v2))
    | FDiv => ret (DVALUE_Float (Float32.div v1 v2))
    | FRem => failwith "unimplemented"
    end.

  Definition eval_fop (fop:fbinop) (v1:dvalue) (v2:dvalue) : err dvalue :=
    match v1, v2 with
    | DVALUE_Float f1, DVALUE_Float f2 => float_op fop f1 f2
    | DVALUE_Double d1, DVALUE_Double d2 => double_op fop d1 d2
    | _, _ => failwith ("ill_typed-fop: " ++ (to_string fop) ++ " " ++ (to_string v1) ++ " " ++ (to_string v2))
    end.

  Definition not_nan32 (f:ll_float) : bool :=
    negb (Flocq.IEEE754.Binary.is_nan _ _ f).

  Definition ordered32 (f1 f2:ll_float) : bool :=
    andb (not_nan32 f1) (not_nan32 f2).

  Definition not_nan64 (f:ll_double) : bool :=
    negb (Flocq.IEEE754.Binary.is_nan _ _ f).

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
    | DVALUE_Float f1, DVALUE_Float f2 => ret (float_cmp fcmp f1 f2)
    | DVALUE_Double f1, DVALUE_Double f2 => ret (double_cmp fcmp f1 f2)
    | _, _ => failwith "ill_typed-fcmp"
    end.

  End ARITHMETIC.


  (* Same deal as above with the helper *)
  Definition eval_select_h cnd v1 v2 : err dvalue :=
    match cnd with
    | DVALUE_I1 i =>
      ret (if Int1.unsigned i =? 1 then v1 else v2)
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
          | [] => ret []
          | (cnd,(v1,v2)) :: tl =>
              val <- eval_select_h cnd v1 v2 ;;
              vec <- loop tl ;;
              ret (val :: vec)
          end in
      val <- loop (List.combine es (List.combine es1 es2)) ;;
      ret (DVALUE_Vector val)
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
          if idx =? 0 then ret h else loop tl (i-1)
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
          if idx =? 0 then ret (acc ++ (v :: tl))
          else loop (acc ++ [h]) tl (i-1)
        end%list in
    match str with
    | DVALUE_Struct f =>
      v <- (loop [] f idx) ;;
      ret (DVALUE_Struct v)

    | DVALUE_Array e =>
      v <- (loop [] e idx) ;;
      ret (DVALUE_Array v)

    | _ => failwith "invalid aggregate data"
    end.
  Arguments insert_into_str _ _ _ : simpl nomatch.

(*  ------------------------------------------------------------------------- *)
  (** TODO: Add [uvalue] *)


(* The set of dynamic values manipulated by an LLVM program. *)
Inductive uvalue : Set :=
| UVALUE_Addr (a:A.addr)
| UVALUE_I1 (x:int1)
| UVALUE_I8 (x:int8)
| UVALUE_I32 (x:int32)
| UVALUE_I64 (x:int64)
| UVALUE_Double (x:ll_double)
| UVALUE_Float (x:ll_float)
| UVALUE_Undef (t:dtyp)
| UVALUE_Poison
| UVALUE_None
| UVALUE_Struct        (fields: list uvalue)
| UVALUE_Packed_struct (fields: list uvalue)
| UVALUE_Array         (elts: list uvalue)
| UVALUE_Vector        (elts: list uvalue)
| UVALUE_IBinop           (iop:ibinop) (v1:uvalue) (v2:uvalue)  
| UVALUE_ICmp             (cmp:icmp)   (v1:uvalue) (v2:uvalue)
| UVALUE_FBinop           (fop:fbinop) (fm:list fast_math) (v1:uvalue) (v2:uvalue)
| UVALUE_FCmp             (cmp:fcmp)   (v1:uvalue) (v2:uvalue)
| UVALUE_Conversion       (conv:conversion_type) (v:uvalue) (t_to:dtyp)
| UVALUE_GetElementPtr    (t:dtyp) (ptrval:uvalue) (idxs:list (uvalue))
| UVALUE_ExtractElement   (vec: uvalue) (idx: uvalue)
| UVALUE_InsertElement    (vec: uvalue) (elt:uvalue) (idx:uvalue)
| UVALUE_ShuffleVector    (vec1:uvalue) (vec2:uvalue) (idxmask:uvalue)
| UVALUE_ExtractValue     (vec:uvalue) (idxs:list int)
| UVALUE_InsertValue      (vec:uvalue) (elt:uvalue) (idxs:list int)
| UVALUE_Select           (cnd:uvalue) (v1:uvalue) (v2:uvalue) 
.


Variant UndefE : Type -> Type :=
| pick (u:uvalue) : UndefE dvalue.

(* TODO: define the inclusion dvalue -> uvalue 
     trivial inclusion
*)

(* TODO: define [is_defined : uvalue -> bool] 

    returns true iff the uvalue contains no occurrence of UVALUE_Undef.
*)

(* TODO: define [refines : uvalue -> dvalue -> Prop] which characterizes the nondeterminism of undef values *)

  
End DVALUE.
