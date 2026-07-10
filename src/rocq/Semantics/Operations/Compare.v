From Vellvm Require Import
  Utils
  Syntax
  EOU
  DynamicValues
  Params.

Section Compare.
  Context {Pa : Params}.

  Definition eval_icmp_base (samesign:bool) (icmp : icmp) (v1 v2 : dvalue_base) : EOU dvalue_base.
    refine
      (match v1, v2 with
       | DVALUE_I sz1 i1, DVALUE_I sz2 i2 =>
           _
       | DVALUE_Iptr i1, DVALUE_Iptr i2 => eval_int_icmp samesign icmp i1 i2
       | DVALUE_Poison t1, DVALUE_Poison t2 => ret (DVALUE_Poison t1)
       | DVALUE_Poison t, _ => if is_DVALUE_IX v2 then ret (DVALUE_Poison t) else raise_error "ill_typed-iop"
       | _, DVALUE_Poison t => if is_DVALUE_IX v1 then ret (DVALUE_Poison t) else raise_error "ill_typed-iop"
       | DVALUE_Pointer a1, DVALUE_Pointer a2 =>
           let i1 := ptr_to_int a1 in
           let i2 := ptr_to_int a2 in
           eval_int_icmp false icmp i1 i2
       | _, _ => raise_error ("eval_icmp_base: ill_typed-icmp: " ++ show v1 ++ ", " ++ show v2)
       end).
    destruct (Pos.eq_dec sz1 sz2); subst.
    - exact (eval_int_icmp samesign icmp i1 i2).
    - exact (raise_error ("eval_icmp_base: ill_typed-icmp: " ++ show v1 ++ ", " ++ show v2)).
  Defined.
  Arguments eval_icmp_base _ _ _ _ : simpl nomatch.

  Definition eval_icmp (samesign:bool) (icmp : icmp) (v1 v2 : dvalue) : EOU dvalue :=
    match v1, v2 with
    | (DVALUE_Vector t elts1), (DVALUE_Vector _ elts2) =>
        let n := N.length elts1 in
        let m := N.length elts2 in
        if (n =? m)%N  then 
          val <- vec_loop (eval_icmp_base samesign icmp) (List.combine elts1 elts2) ;;
          ret (DVALUE_Vector (DTYPE_Vector n (DTYPE_I 1)) val)
        else
          raise_ub "icmp of different-length vectors"
    | DVALUE_Base v1, DVALUE_Base v2 => DVALUE_Base <$> (eval_icmp_base samesign icmp v1 v2)
    | _, _ => raise_error "eval_icmp_base: ill-typed icmp"
    end.

  Arguments eval_icmp _ _ _ _ : simpl nomatch.
    
End Compare.
