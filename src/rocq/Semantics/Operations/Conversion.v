From Vellvm Require Import
     Numeric
     Utilities
     Syntax
     Params
     EOU
     DynamicValues
     MemoryBytes.

Section Convert.
  Context {Pa : Params}.
  
  (** ** Typed conversion
        Performs a dynamic conversion of a [dvalue] of type [t1] to one of type [t2].
        For instance, convert an integer over 8 bits to one over 1 bit by truncation.

        The conversion function is not pure, i.e. in particular cannot live in [DynamicValues.v]
        as would be natural, due to the [Int2Ptr] and [Ptr2Int] cases. At those types, the conversion
        needs to cast between integers and pointers, which depends on the memory model.
   *)
  Definition get_conv_case (conv : conversion_type) (t1:dtyp) (x:dvalue) (t2:dtyp) : conv_case :=
    match conv with
    | Trunc nuw nsb => (* TODO: handle the nuw and nsb flags *)
        match t1, x, t2 with
        | DTYPE_I sz_t, DVALUE_I sz_from i1, DTYPE_I sz_to =>
            if Pos.eqb sz_t sz_from && (sz_to <? sz_from)%positive
            then Conv_Pure (DVALUE_I sz_to (repr (unsigned i1)))
            else Conv_Illegal "i-to-i ill-typed Trunc"

        | DTYPE_I sz_t, DVALUE_Poison t, DTYPE_I sz_to =>
            Conv_Pure (DVALUE_Poison t)

        | _, _, _ => Conv_Illegal "ill-typed Trunc"
        end

    | Zext nneg => (* TODO: handle the nneg flag *)
        match t1, x, t2 with
        | DTYPE_I sz_t, DVALUE_I sz_from i1, DTYPE_I sz_to =>
            if Pos.eqb sz_t sz_from && (sz_from <? sz_to)%positive
            then Conv_Pure (DVALUE_I sz_to (repr (unsigned i1)))
            else Conv_Illegal "i-to-i ill-typed Zext"

        | DTYPE_I sz_t, DVALUE_Poison t, DTYPE_I sz_to =>
            Conv_Pure (DVALUE_Poison t)

        | _, _, _ => Conv_Illegal "ill-typed Zext"
        end

    | Sext =>
        match t1, x, t2 with
        | DTYPE_I sz_t, DVALUE_I sz_from i1, DTYPE_I sz_to =>
            if Pos.eqb sz_t sz_from && (sz_from <? sz_to)%positive
            then Conv_Pure (DVALUE_I sz_to (repr (signed i1)))
            else Conv_Illegal "i-to-i ill-typed Sext"

        | DTYPE_I sz_t, DVALUE_Poison t, DTYPE_I sz_to =>
            Conv_Pure (DVALUE_Poison t)

        | _, _, _ => Conv_Illegal "ill-typed Sext"
        end

    | Bitcast =>
        if dtyp_eqb t1 t2
        then Conv_Pure x
        else if bit_sizeof_dtyp t1 =? bit_sizeof_dtyp t2
             then
               let bytes := dvalue_to_memory_bytes x t1 in
               let dv_conv := memory_bytes_to_dvalue bytes t2 in
               match dv_conv with
               | raise_error err => Conv_Illegal ("Bitcast failure: " ++ err)
               | raise_oom oom => Conv_Oom ("Bitcast OOM: " ++ oom)
               | raise_ub ub => Conv_Illegal ("Bitcast UB " ++ ub)
               | raise_ret v => Conv_Pure v
               end
             else Conv_Illegal "unequal bitsize in cast"

    | Uitofp nneg => (* TODO: handle the nneg flag *)
        match t1, x, t2 with
        | DTYPE_I sz_t, DVALUE_I sz_from i1, DTYPE_FP FP_float =>
            if Pos.eqb sz_t sz_from
            then Conv_Pure (DVALUE_Float (Float32.of_intu (repr (unsigned i1))))
            else Conv_Illegal "i-to-float ill-typed Uitofp"

        | DTYPE_I sz_t, DVALUE_I sz_from i1, DTYPE_FP FP_double =>
            if Pos.eqb sz_t sz_from
            then Conv_Pure (DVALUE_Double (Float.of_longu (repr (unsigned i1))))
            else Conv_Illegal "i-to-double ill-typed Uitofp"

        | DTYPE_I sz_t, DVALUE_Poison t, DTYPE_FP _ =>
            Conv_Pure (DVALUE_Poison t)

        | _, _, _ => Conv_Illegal "ill-typed Uitofp"
        end

    | Sitofp =>
        match t1, x, t2 with
        | DTYPE_I sz_t, DVALUE_I sz_from i1, DTYPE_FP FP_float =>
            if Pos.eqb sz_t sz_from
            then Conv_Pure (DVALUE_Float (Float32.of_intu (repr (signed i1))))
            else Conv_Illegal "i-to-float ill-typed Sitofp"

        | DTYPE_I sz_t, DVALUE_I sz_from i1, DTYPE_FP FP_double =>
            if Pos.eqb sz_t sz_from
            then Conv_Pure (DVALUE_Double (Float.of_longu (repr (signed i1))))
            else Conv_Illegal "i-to-double ill-typed Sitofp"

        | DTYPE_I sz_t, DVALUE_Poison t, DTYPE_FP _ =>
            Conv_Pure (DVALUE_Poison t)

        | _, _, _ => Conv_Illegal "ill-typed Sitofp"
        end

    | Inttoptr =>
        match t1, t2 with
        | DTYPE_I _, DTYPE_Pointer => Conv_ItoP x
        | DTYPE_Iptr , DTYPE_Pointer => Conv_ItoP x
        | _, _ => Conv_Illegal "Inttoptr got illegal arguments"
        end
    | Ptrtoint =>
        match t1, t2 with
        | DTYPE_Pointer, DTYPE_I _ => Conv_PtoI x
        | DTYPE_Pointer, DTYPE_Iptr => Conv_PtoI x
        | _, _ => Conv_Illegal "Ptrtoint got illegal arguments"
        end

    | Fptoui
    | Fptosi
    | Fptrunc _
    | Fpext _
    | Addrspacecast
      => Conv_Illegal "TODO: unimplemented numeric conversion"
    end.
  
  Arguments get_conv_case _ _ _ _ : simpl nomatch.

  Definition convert (conv : conversion_type) (t_from : dtyp) (dv : dvalue) (t_to : dtyp) : EOU dvalue :=
    match get_conv_case conv t_from dv t_to with
    | Conv_PtoI x =>
        match x, t_to with
        | DVALUE_Addr addr, DTYPE_I sz => coerce_integer_to_int (Some sz) (ptr_to_int addr)
        | DVALUE_Addr addr, DTYPE_Iptr => coerce_integer_to_int None (ptr_to_int addr)
        | _, _ => raise_error "Invalid PTOI conversion"
        end
    | Conv_ItoP x =>
        DVALUE_Addr <$> int_to_ptr (dvalue_int_unsigned x) wildcard_prov
    | Conv_Pure x => ret x
    | Conv_Oom s => raise_oom s
    | Conv_Illegal s => raise_error s
    end.

End Convert.

