From Vellvm Require Import
  Utils
  Syntax
  EOU
  DynamicValues
  Params.

Section Select.
  Context {Pa : Params}.

  Definition eval_select_base (cnd : dvalue_base) (v1 v2 : dvalue_base) : EOU dvalue_base :=
    match cnd with
    | DVALUE_Poison (DTYPE_Base (DTYPE_I 1)) =>
        (* picks the "type" of v1 *)
        ret (DVALUE_Poison (dtyp_of_dvalue_base v1))
    | DVALUE_I 1 i =>
        if (@Integers.unsigned 1 i =? 1)%Z
        then ret v1
        else ret v2
    | _ => raise_error "eval_select_base: ill-typed select."
    end.
    
  Definition eval_select_base_dvalue (cnd : dvalue_base) (v1 v2 : dvalue) : EOU dvalue :=
    match cnd with
    | DVALUE_Poison (DTYPE_Base (DTYPE_I 1)) =>
        (* picks the "type" of v1 *)
        (fun x => DVALUE_Base (DVALUE_Poison x)) <$> (dtyp_of_dvalue v1)
    | DVALUE_I 1 i =>
        if (@Integers.unsigned 1 i =? 1)%Z
        then ret v1
        else ret v2
    | _ => raise_error "eval_select_base_dvalue: ill-typed select."
    end.



  Definition eval_select (cnd : dvalue) (v1 v2 : dvalue) : EOU dvalue :=
    match cnd with
    | DVALUE_Base cnd' => eval_select_base_dvalue cnd' v1 v2
    | DVALUE_Vector _ conds =>
        match v1, v2 with
        | DVALUE_Vector t elts1, DVALUE_Vector _ elts2 =>
            (DVALUE_Vector t) <$>
              (vec_loop (fun c => fun '(v1, v2) => eval_select_base c v1 v2)
                 (List.combine conds (List.combine elts1 elts2)))
        | DVALUE_Base (DVALUE_Poison (DTYPE_Vector sz t)), DVALUE_Vector _ ys =>
            (DVALUE_Vector (DTYPE_Vector sz t)) <$>
              (vec_loop (fun c => fun '(v1, v2) => eval_select_base c v1 v2)
                 (List.combine conds (List.combine (repeat (DVALUE_Poison (DTYPE_Base t)) (N.to_nat sz)) ys)))
        | DVALUE_Vector _ xs, DVALUE_Base (DVALUE_Poison (DTYPE_Vector sz t)) =>
            (DVALUE_Vector (DTYPE_Vector sz t)) <$>
              (vec_loop (fun c => fun '(v1, v2) => eval_select_base c v1 v2)
                 (List.combine conds (List.combine xs (repeat (DVALUE_Poison (DTYPE_Base t)) (N.to_nat sz)))))
        | DVALUE_Base (DVALUE_Poison (DTYPE_Vector sz t)), DVALUE_Base (DVALUE_Poison (DTYPE_Vector _ _)) =>
        (* TODO: could check the sizes to see if this is UB *)
            ret (DVALUE_Base (DVALUE_Poison (DTYPE_Vector sz t)))
        | _, _ => raise_error "eval_select: ill-typed vector select, non-vector arguments"
        end
    | _ => raise_error "eval_select: ill-typed select."
    end.

End Select.
