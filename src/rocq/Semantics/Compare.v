From Vellvm Require Import
  Utilities
  Syntax
  Numeric.Rocqlib
  Numeric.Integers
  Numeric.Floats
  Semantics.DynamicValues
  Semantics.MemoryParams
  Semantics.LLVMParams.

Module COMPARE (LP : LLVMParams) (MP : MEMORY_PARAMS LP).
  Import MP.
  Import LP.
  Import SZ.
  Import DV.
  Import MBYTES.
  Import PTOI.
  
  Definition eval_icmp (samesign:bool) (icmp : icmp) (v1 v2 : dvalue) : EOB dvalue.
    refine
      (match v1, v2 with
       | @DVALUE_I sz1 i1, @DVALUE_I sz2 i2 =>
           _
       | DVALUE_IPTR i1, DVALUE_IPTR i2 => eval_int_icmp samesign icmp i1 i2
       | DVALUE_Poison t1, DVALUE_Poison t2 => ret (DVALUE_Poison t1)
       | DVALUE_Poison t, _ => if is_DVALUE_IX v2 then ret (DVALUE_Poison t) else raise_error "ill_typed-iop"
       | _, DVALUE_Poison t => if is_DVALUE_IX v1 then ret (DVALUE_Poison t) else raise_error "ill_typed-iop"
       | DVALUE_Addr a1, DVALUE_Addr a2 =>
           let i1 := ptr_to_int a1 in
           let i2 := ptr_to_int a2 in
           eval_int_icmp false icmp i1 i2
       | _, _ => raise_error ("ill_typed-icmp: " ++ show_dvalue v1 ++ ", " ++ show_dvalue v2)
       end).
    destruct (Pos.eq_dec sz1 sz2); subst.
    - exact (eval_int_icmp samesign icmp i1 i2).
    - exact (raise_error ("ill_typed-icmp: " ++ show_dvalue v1 ++ ", " ++ show_dvalue v2)).
  Defined.
  Arguments eval_icmp _ _ _ _ : simpl nomatch.

End COMPARE.
