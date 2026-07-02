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

  (* Floating point extension *)
  (* SAZ: I'm not sure that this implementation does the right thing
     with respect to the rounding mode (maybe not a problem for extension)
     and NAN propagation.
   *)
  (* LANGREF: The ‘fpext’ instruction extends the value from a smaller
     floating-point type to a larger floating-point type. The fpext cannot be
     used to make a no-op cast because it always changes bits. Use bitcast to
     make a no-op cast for a floating-point cast.

     NaN values follow the usual NaN behaviors, except that _if_ a NaN payload
     is propagated from the input (“Quieting NaN propagation” or “Unchanged NaN
     propagation” cases), then it is copied to the high order bits of the
     resulting payload, and the remaining low order bits are zero.

   *)
  Program Definition float_to_double (f : ll_float) : ll_double :=
    Bconv _ _ _ _ eq_refl eq_refl (fun _ => default_nan_64) BinarySingleNaN.mode_NE f.
  
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
            Conv_Pure (DVALUE_Poison t2)

        | _, _, _ => Conv_Illegal "ill-typed Trunc"
        end

    | Zext nneg => (* TODO: handle the nneg flag *)
        match t1, x, t2 with
        | DTYPE_I sz_t, DVALUE_I sz_from i1, DTYPE_I sz_to =>
            if Pos.eqb sz_t sz_from && (sz_from <? sz_to)%positive
            then Conv_Pure (DVALUE_I sz_to (repr (unsigned i1)))
            else Conv_Illegal "i-to-i ill-typed Zext"

        | DTYPE_I sz_t, DVALUE_Poison t, DTYPE_I sz_to =>
            Conv_Pure (DVALUE_Poison t2)

        | _, _, _ => Conv_Illegal "ill-typed Zext"
        end

    | Sext =>
        match t1, x, t2 with
        | DTYPE_I sz_t, DVALUE_I sz_from i1, DTYPE_I sz_to =>
            if Pos.eqb sz_t sz_from && (sz_from <? sz_to)%positive
            then Conv_Pure (DVALUE_I sz_to (repr (signed i1)))
            else Conv_Illegal "i-to-i ill-typed Sext"

        | DTYPE_I sz_t, DVALUE_Poison t, DTYPE_I sz_to =>
            Conv_Pure (DVALUE_Poison t2)

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
            Conv_Pure (DVALUE_Poison t2)

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
            Conv_Pure (DVALUE_Poison t2)

        | _, _, _ => Conv_Illegal "ill-typed Sitofp"
        end

    | Inttoptr =>
        match t1, t2 with
        | DTYPE_I _, DTYPE_Pointer => Conv_ItoP x
        | DTYPE_IPTR , DTYPE_Pointer => Conv_ItoP x
        | _, _ => Conv_Illegal "Inttoptr got illegal arguments"
        end
    | Ptrtoint =>
        match t1, t2 with
        | DTYPE_Pointer, DTYPE_I _ => Conv_PtoI x
        | DTYPE_Pointer, DTYPE_IPTR => Conv_PtoI x
        | _, _ => Conv_Illegal "Ptrtoint got illegal arguments"
        end

    | Fptoui =>
        match t1, x, t2 with
          (* LANGREF: The ‘fptoui’ instruction converts its floating-point operand into
          the nearest (rounding towards zero) unsigned integer value. If the
          value cannot fit in ty2, the result is a poison value. *)
        | DTYPE_FP FP_float, DVALUE_Float f, DTYPE_I sz_t =>
            match ZofB_range _ _ f (0%Z) (@max_unsigned sz_t) with
            | None => Conv_Pure (DVALUE_Poison t2)
            | Some z => Conv_Pure (DVALUE_I sz_t (repr z))
            end
              
        | DTYPE_FP FP_double, DVALUE_Double f, DTYPE_I sz_t  =>
            match ZofB_range _ _ f (0%Z) (@max_unsigned sz_t) with
            | None => Conv_Pure (DVALUE_Poison t2)
            | Some z => Conv_Pure (DVALUE_I sz_t (repr z))
            end
              
        | DTYPE_FP _, DVALUE_Poison t, DTYPE_I _ =>
            Conv_Pure (DVALUE_Poison t2)

        | _, _, _ => Conv_Illegal "ill-typed Fptoui"
        end
        
    | Fptosi =>
        match t1, x, t2 with
          (* LANGREF: The ‘fptosi’ instruction converts its floating-point operand into
          the nearest (rounding towards zero) unsigned integer value. If the
          value cannot fit in ty2, the result is a poison value. *)
        | DTYPE_FP FP_float, DVALUE_Float f, DTYPE_I sz_t =>
            match ZofB_range _ _ f (@min_signed sz_t) (@max_signed sz_t) with
            | None => Conv_Pure (DVALUE_Poison t2)
            | Some z => Conv_Pure (DVALUE_I sz_t (repr z))
            end
              
        | DTYPE_FP FP_double, DVALUE_Double f, DTYPE_I sz_t  =>
            match ZofB_range _ _ f (@min_signed sz_t) (@max_signed sz_t) with
            | None => Conv_Pure (DVALUE_Poison t2)
            | Some z => Conv_Pure (DVALUE_I sz_t (repr z))
            end
              
        | DTYPE_FP _, DVALUE_Poison t, DTYPE_I _ =>
            Conv_Pure (DVALUE_Poison t2)

        | _, _, _ => Conv_Illegal "ill-typed Fptosi"
        end

    | Fpext _ =>
        (* NOTE: Does not support "fast-math" flags *)
        match t1, x, t2 with
        | DTYPE_FP FP_float, DVALUE_Float f, DTYPE_FP FP_double  =>
            Conv_Pure (DVALUE_Double (float_to_double f))
            
        | _, _, _ => Conv_Illegal "ill-typed Fpext"
        end

    | Fptrunc _

    | Addrspacecast
      => Conv_Illegal "TODO: unimplemented numeric conversion"
    end.
  
  Arguments get_conv_case _ _ _ _ : simpl nomatch.

  Definition convert_h (conv : conversion_type) (t_from : dtyp) (dv : dvalue) (t_to : dtyp) : EOU dvalue :=
    match get_conv_case conv t_from dv t_to with
    | Conv_PtoI x =>
        match x, t_to with
        | DVALUE_Addr addr, DTYPE_I sz => coerce_integer_to_int (Some sz) (ptr_to_int addr)
        | DVALUE_Addr addr, DTYPE_IPTR => coerce_integer_to_int None (ptr_to_int addr)
        | _, _ => raise_error "Invalid PTOI conversion"
        end
    | Conv_ItoP x =>
        DVALUE_Addr <$> int_to_ptr (dvalue_int_unsigned x) wildcard_prov
    | Conv_Pure x => ret x
    | Conv_Oom s => raise_oom s
    | Conv_Illegal s => raise_error s
    end.

  Definition get_vec_conversion_type (t_from t_to : dtyp) : option (dtyp * dtyp) :=
    match t_from, t_to with
    | DTYPE_Vector n t_from', DTYPE_Vector m t_to' =>
        if N.eqb n m then Some (t_from', t_to') else None
    | _, _ => None
    end.

  
  Definition convert (conv : conversion_type) (t_from : dtyp) (dv : dvalue) (t_to : dtyp) : EOU dvalue :=
    match dv with
    | (DVALUE_Vector t elts1) =>
        match get_vec_conversion_type t_from t_to with
        | Some (t_from', t_to') =>
            val <- map_monad (fun v => convert_h conv t_from' v t_to') elts1 ;;
            ret (DVALUE_Vector t_to' val)
        | None =>
            raise_error "vector conversion at incompatible types or vector lengths"
        end
    | _ => convert_h conv t_from dv t_to 
    end.

  
End Convert.

