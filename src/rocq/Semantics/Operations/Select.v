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
    | DVALUE_Poison => ret DVALUE_Poison
    | DVALUE_I 1 i =>
        if (@Integers.unsigned 1 i =? 1)%Z
        then ret v1
        else ret v2
    | _ => raise_error "eval_select_base: ill-typed select."
    end.
    
  Definition eval_select_base_dvalue (cnd : dvalue_base) (v1 v2 : dvalue) : EOU dvalue :=
    match cnd with
    | DVALUE_Poison => ret (DVALUE_Base DVALUE_Poison)
    | DVALUE_I 1 i =>
        if (@Integers.unsigned 1 i =? 1)%Z
        then ret v1
        else ret v2
    | _ => raise_error "eval_select_base_dvalue: ill-typed select."
    end.



  Definition eval_select (cnd : dvalue) (v_t:dtyp) (v1 v2 : dvalue) : EOU dvalue :=
    match cnd with
    | DVALUE_Base cnd' => eval_select_base_dvalue cnd' v1 v2
    | DVALUE_Array true conds =>
        match v_t with
        | DTYPE_Array true sz t =>
            conds' <- map_monad dvalue_to_dvalue_base conds ;;
            match v1, v2 with
            | DVALUE_Array true elts1, DVALUE_Array true elts2 =>
                (DVALUE_Array true) <$>
                  (vec_loop (fun c => fun '(v1, v2) => eval_select_base_dvalue c v1 v2)
                     (List.combine conds' (List.combine elts1 elts2)))
            | DVALUE_Base DVALUE_Poison, DVALUE_Array true ys =>
                (DVALUE_Array true) <$>
                  (vec_loop (fun c => fun '(v1, v2) => eval_select_base_dvalue c v1 v2)
                     (List.combine conds' (List.combine (repeat (DVALUE_Base DVALUE_Poison) (N.to_nat sz)) ys)))
            | DVALUE_Array true xs, DVALUE_Base DVALUE_Poison =>
                (DVALUE_Array true) <$>
                  (vec_loop (fun c => fun '(v1, v2) => eval_select_base_dvalue c v1 v2)
                     (List.combine conds' (List.combine xs (repeat (DVALUE_Base DVALUE_Poison) (N.to_nat sz)))))
            | DVALUE_Base DVALUE_Poison, DVALUE_Base DVALUE_Poison =>
                ret (DVALUE_Base DVALUE_Poison)
            | _, _ => raise_error "eval_select: non-vector argument values"
            end
        | _ => raise_error "eval_select: ill-typed select."
        end
    | _ => raise_error "eval_select: ill-typed select."
    end.

End Select.
