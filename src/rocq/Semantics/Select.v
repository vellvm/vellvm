From Vellvm Require Import
  Utilities
  Syntax
  Params
  DynamicValues.

Section Select.
  Context {Pa : Params}.

  Definition eval_select
    (cnd : dvalue) (v1 v2 : dvalue) : EOB dvalue
    := match cnd with
       | DVALUE_Poison t =>
           (* TODO: Should be the type of the result of the select... *)
           ret (DVALUE_Poison t)
       | DVALUE_I 1 i =>
           if (@Integers.unsigned 1 i =? 1)%Z
           then ret v1
           else ret v2
       | DVALUE_Vector _ conds =>
           let fix loop conds xs ys : EOB (list dvalue) :=
             match conds, xs, ys with
             | [], [], [] => ret []
             | (c::conds), (x::xs), (y::ys) =>
                 selected <- match c with
                            | DVALUE_Poison t =>
                                (* TODO: Should be the type of the result of the select... *)
                                ret (DVALUE_Poison t)
                            | DVALUE_I 1 i =>
                                if (@Integers.unsigned 1 i =? 1)%Z
                                then ret x
                                else ret y
                            | _ => raise_error "eval_select: ill-typed select, condition in vector was not poison or i1."
                            end;;
                 rest <- loop conds xs ys;;
                 ret (selected :: rest)
             | _, _, _ => raise_error "eval_select: ill-typed vector select, length mismatch."
             end in
           match v1, v2 with
           | DVALUE_Poison t, _ =>
               (* TODO: Should we make sure t is a vector type...? *)
               ret (DVALUE_Poison t)
           | DVALUE_Vector _ _, DVALUE_Poison t =>
               (* TODO: Should we make sure t is a vector type...? *)
               ret (DVALUE_Poison t)
           | DVALUE_Vector t xs, DVALUE_Vector _ ys =>
               selected <- loop conds xs ys;;
               ret (DVALUE_Vector t selected)
           | _, _ => raise_error "eval_select: ill-typed vector select, non-vector arguments"
           end
       | _ => raise_error "eval_select: ill-typed select."
       end.

End Select.
