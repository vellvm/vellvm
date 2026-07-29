From Vellvm Require Import
     Syntax
     Numeric
     Utils
     Params
     EOU
     DynamicValues
     MemoryBytes
     LLVMEvents.


Section Convert.
  Context {Pa : Params}.

  (** ** Typed conversion
        Performs a dynamic conversion of a [dvalue] of type [t1] to one of type [t2].
        For instance, convert an integer over 8 bits to one over 1 bit by truncation.

        The conversion function is not pure, i.e. in particular cannot live in [DynamicValues.v]
        as would be natural, due to the [Int2Ptr] and [Ptr2Int] cases. At those types, the conversion
        needs to cast between integers and pointers, which depends on the memory model.
   *)

  (* Section CONVERSIONS. *)
(*

    (* Note: Inferring the subevent instance takes a small but non-trivial amount of time,
       and has to be done here hundreds and hundreds of times due to the brutal pattern matching on
       several values. Factoring the inference upfront is therefore necessary.
     *)

    (* A trick avoiding proofs that involve thousands of cases: we split the conversion into
      the composition of a huge case analysis that builds a value of [conv_case], and a function
      with only four cases to actually build the tree.
     *)
    Variant conv_case : Set :=
    | Conv_Pure    (x : dvalue_base)
    | Conv_ItoP    (x : dvalue_base)
    | Conv_PtoI    (x : dvalue_base)
    | Conv_Oom     (s : string)
    | Conv_Illegal (s: string).
     
    Variant ptr_conv_cases : Set :=
    | PtrConv_ItoP
    | PtrConv_PtoI
    | PtrConv_Neither.

    Definition assert_conv_case_ptr conv (t1 : dtyp_base) (t2 : dtyp_base) : EOU unit
      := match conv with
         | Inttoptr =>
           match t1, t2 with
           | DTYPE_I 64, DTYPE_Pointer => ret tt
           | DTYPE_Iptr, DTYPE_Pointer => ret tt
           | _, _ => raise_error "bad"
           end
         | Ptrtoint =>
           match t1, t2 with
           | DTYPE_Pointer, DTYPE_I _ => ret tt
           | DTYPE_Pointer, DTYPE_Iptr => ret tt
           | _, _ => raise_error "bad"
           end
         | _ => raise_error "bad"
         end.

  End CONVERSIONS.
 *)
  
  (* Floating point extension *)
  (* LANGREF: The ‘fpext’ instruction extends the value from a smaller
     floating-point type to a larger floating-point type. The fpext cannot be
     used to make a no-op cast because it always changes bits. Use bitcast to
     make a no-op cast for a floating-point cast.

     NaN values follow the usual NaN behaviors, except that _if_ a NaN payload
     is propagated from the input (“Quieting NaN propagation” or “Unchanged NaN
     propagation” cases), then it is copied to the high order bits of the
     resulting payload, and the remaining low order bits are zero.

     [Float.of_single] is [Bconv] instantiated with [Float.of_single_nan],
     which implements exactly the rule above: [expand_nan_payload] shifts the
     source payload left by 29 bits, putting it in the high order bits of the
     result and zeroing the rest.  Rolling our own [conv_nan] here instead
     (which is what we used to do) flattens every NaN to the default one:
     legal, since the "Preferred NaN" case is always an option, but needlessly
     lossy and inconsistent with what the binops do.

     Note that [of_single_nan] consults [Archi.float_of_single_preserves_sNaN],
     which we set to [true]: a signaling NaN stays signaling across [fpext].
     That is the "Unchanged NaN propagation" case, and is legal.
   *)
  Definition float_to_double : ll_float -> ll_double := Float.of_single.

  (* Floating point truncation *)
  (* LANGREF: The ‘fptrunc’ instruction casts a value from a larger
     floating-point type to a smaller floating-point type.  This instruction is
     assumed to execute in the default floating-point environment.

     NaN values follow the usual NaN behaviors, except that if a NaN payload is
     propagated from the input (“Quieting NaN propagation” or “Unchanged NaN
     propagation” cases), then the low order bits of the NaN payload which
     cannot fit in the resulting type are discarded.

     [Float.to_single] is [Bconv] instantiated with [Float.to_single_nan],
     which implements exactly the rule above: [reduce_nan_payload] shifts the
     source payload right by 29 bits, discarding the low order bits that do not
     fit.  It quiets the payload *before* the shift, which is precisely what
     stops the shift from producing the all-zero payload the LangRef warns
     about (an all-zero payload with the quiet bit clear would denote an
     infinity, not a NaN).

     Caveat inherited from [float_to_double]: unlike extension, truncation
     genuinely rounds, and we do not model the non-default rounding modes.
     [mode_NE] is the default environment's round-to-nearest-ties-to-even.
   *)
  Definition double_to_float : ll_double -> ll_float := Float.to_single.

  (** ** Typed conversion
        Performs a dynamic conversion of a [dvalue] of type [t1] to one of type [t2].
        For instance, convert an integer over 8 bits to one over 1 bit by truncation.

        The conversion function is not pure, i.e. in particular cannot live in [DynamicValues.v]
        as would be natural, due to the [Int2Ptr] and [Ptr2Int] cases. At those types, the conversion
        needs to cast between integers and pointers, which depends on the memory model.
   *)
  Definition convert_pure_base (conv : pure_conversion) (t1:dtyp_base) (x:dvalue_base) (t2:dtyp_base) : EOU dvalue_base :=
    match conv with
    | Trunc nuw nsb => (* TODO: handle the nuw and nsb flags *)
        match t1, x, t2 with
        | DTYPE_I sz_t, DVALUE_I sz_from i1, DTYPE_I sz_to =>
            if Pos.eqb sz_t sz_from && (sz_to <? sz_from)%positive
            then ret (DVALUE_I sz_to (repr (unsigned i1)))
            else raise_error "i-to-i ill-typed Trunc"

        | DTYPE_I sz_t, DVALUE_Poison t, DTYPE_I sz_to =>
            ret (dvp t2)

        | _, _, _ => raise_error "ill-typed Trunc"
        end

    | Zext nneg => (* TODO: handle the nneg flag *)
        match t1, x, t2 with
        | DTYPE_I sz_t, DVALUE_I sz_from i1, DTYPE_I sz_to =>
            if Pos.eqb sz_t sz_from && (sz_from <? sz_to)%positive
            then ret (DVALUE_I sz_to (repr (unsigned i1)))
            else raise_error "i-to-i ill-typed Zext"

        | DTYPE_I sz_t, DVALUE_Poison t, DTYPE_I sz_to =>
            ret (dvp t2)

        | _, _, _ => raise_error "ill-typed Zext"
        end

    | Sext =>
        match t1, x, t2 with
        | DTYPE_I sz_t, DVALUE_I sz_from i1, DTYPE_I sz_to =>
            if Pos.eqb sz_t sz_from && (sz_from <? sz_to)%positive
            then ret (DVALUE_I sz_to (repr (signed i1)))
            else raise_error "i-to-i ill-typed Sext"

        | DTYPE_I sz_t, DVALUE_Poison t, DTYPE_I sz_to =>
            ret (dvp t2)

        | _, _, _ => raise_error "ill-typed Sext"
        end

    | Uitofp nneg => (* TODO: handle the nneg flag *)
        match t1, x, t2 with
        | DTYPE_I sz_t, DVALUE_I sz_from i1, DTYPE_FP FP_float =>
            if Pos.eqb sz_t sz_from
            then ret (DVALUE_Float (Float32.of_intu (repr (unsigned i1))))
            else raise_error "i-to-float ill-typed Uitofp"

        | DTYPE_I sz_t, DVALUE_I sz_from i1, DTYPE_FP FP_double =>
            if Pos.eqb sz_t sz_from
            then ret (DVALUE_Double (Float.of_longu (repr (unsigned i1))))
            else raise_error "i-to-double ill-typed Uitofp"

        | DTYPE_I sz_t, DVALUE_Poison t, DTYPE_FP _ =>
            ret (dvp t2)

        | _, _, _ => raise_error "ill-typed Uitofp"
        end

    | Sitofp =>
        match t1, x, t2 with
        | DTYPE_I sz_t, DVALUE_I sz_from i1, DTYPE_FP FP_float =>
            if Pos.eqb sz_t sz_from
            then ret (DVALUE_Float (Float32.of_int (repr (signed i1))))
            else raise_error "i-to-float ill-typed Sitofp"

        | DTYPE_I sz_t, DVALUE_I sz_from i1, DTYPE_FP FP_double =>
            if Pos.eqb sz_t sz_from
            then ret (DVALUE_Double (Float.of_long (repr (signed i1))))
            else raise_error "i-to-double ill-typed Sitofp"

        | DTYPE_I sz_t, DVALUE_Poison t, DTYPE_FP _ =>
            ret (dvp t2)

        | _, _, _ => raise_error "ill-typed Sitofp"
        end

    | Fptoui =>
        match t1, x, t2 with
          (* LANGREF: The ‘fptoui’ instruction converts its floating-point operand into
          the nearest (rounding towards zero) unsigned integer value. If the
          value cannot fit in ty2, the result is a poison value. *)
        | DTYPE_FP FP_float, DVALUE_Float f, DTYPE_I sz_t =>
            match ZofB_range _ _ f (0%Z) (@max_unsigned sz_t) with
            | None => ret (dvp t2)
            | Some z => ret (DVALUE_I sz_t (repr z))
            end
              
        | DTYPE_FP FP_double, DVALUE_Double f, DTYPE_I sz_t  =>
            match ZofB_range _ _ f (0%Z) (@max_unsigned sz_t) with
            | None => ret (dvp t2)
            | Some z => ret (DVALUE_I sz_t (repr z))
            end
              
        | DTYPE_FP _, DVALUE_Poison t, DTYPE_I _ =>
            ret (dvp t2)

        | _, _, _ => raise_error "ill-typed Fptoui"
        end
        
    | Fptosi =>
        match t1, x, t2 with
          (* LANGREF: The ‘fptosi’ instruction converts its floating-point operand into
          the nearest (rounding towards zero) unsigned integer value. If the
          value cannot fit in ty2, the result is a poison value. *)
        | DTYPE_FP FP_float, DVALUE_Float f, DTYPE_I sz_t =>
            match ZofB_range _ _ f (@min_signed sz_t) (@max_signed sz_t) with
            | None => ret (dvp t2)
            | Some z => ret (DVALUE_I sz_t (repr z))
            end
              
        | DTYPE_FP FP_double, DVALUE_Double f, DTYPE_I sz_t  =>
            match ZofB_range _ _ f (@min_signed sz_t) (@max_signed sz_t) with
            | None => ret (dvp t2)
            | Some z => ret (DVALUE_I sz_t (repr z))
            end
              
        | DTYPE_FP _, DVALUE_Poison t, DTYPE_I _ =>
            ret (dvp t2)

        | _, _, _ => raise_error "ill-typed Fptosi"
        end

    | Fpext _ =>
        (* NOTE: Does not support "fast-math" flags *)
        match t1, x, t2 with
        | DTYPE_FP FP_float, DVALUE_Float f, DTYPE_FP FP_double  =>
            ret (DVALUE_Double (float_to_double f))

        | DTYPE_FP FP_float, DVALUE_Poison t, DTYPE_FP FP_double =>
            ret (dvp t2)
           
        | _, _, _ => raise_error "ill-typed Fpext"
        end

    | Fptrunc _ =>
        (* NOTE: Does not support "fast-math" flags *)
        match t1, x, t2 with
        (* [double] and [float] are the only floating-point types carried by
           [dvalue_base], so double-to-float is the only narrowing there is.
           In particular the LangRef's second example, [fptrunc double 1.0E+300
           to half], is out of reach. *)
        | DTYPE_FP FP_double, DVALUE_Double f, DTYPE_FP FP_float =>
            ret (DVALUE_Float (double_to_float f))

        | DTYPE_FP FP_double, DVALUE_Poison t, DTYPE_FP FP_float =>
            ret (dvp t2)

        | _, _, _ => raise_error "ill-typed Fptrunc"
        end
    end.
  
  Arguments convert_pure_base _ _ _ _ : simpl nomatch.


  Definition get_base_conversion_type (t_from t_to : dtyp) : option (dtyp_base * dtyp_base) :=
    match t_from, t_to with
    | DTYPE_Base t_from', DTYPE_Base t_to' =>
        Some (t_from', t_to')
    | _, _ => None
    end.


  Definition get_vector_conversion_type (t_from t_to : dtyp) : option (dtyp_base * dtyp_base) :=
    match t_from, t_to with
    | DTYPE_Array true n (DTYPE_Base t_from'), DTYPE_Array true m (DTYPE_Base t_to') =>
        if N.eqb n m
        then Some (t_from', t_to')
        else None

    | _, _ => None
    end.

  
  Definition convert_pure (conv : pure_conversion) (t_from : dtyp) (dv : dvalue) (t_to : dtyp) : EOU dvalue :=
    match dv with
    | (DVALUE_Base dv) =>
        match get_base_conversion_type t_from t_to with
        | Some (t_from', t_to') =>
            DVALUE_Base <$> (convert_pure_base conv t_from' dv t_to')
        | None =>
            raise_error "convert_pure: type mismatch"
        end
          
    | (DVALUE_Array true (DTYPE_Array true sz t) elts1) =>
        match get_vector_conversion_type t_from t_to with
        | Some (t_from', t_to') =>
              elts1' <- map_monad dvalue_to_dvalue_base elts1 ;;
              val <- map_monad (fun v => convert_pure_base conv t_from' v t_to') elts1' ;;
              ret (DVALUE_Array true (DTYPE_Array true sz t_to') (List.map DVALUE_Base val))

        | None =>
            raise_error "convert_pure: type or vector size mismatch"
        end
    | _ => raise_error "convert_pure: invalid input dvalue"
    end.

  (* SAZ: TODO - clean up this logic? Is there a cleaner way, and do we really need
     the conversion cases stuff?
   *)
  Definition convert (ct : conversion_type) (t_from : dtyp) (dv : dvalue) (t_to : dtyp) : MCFGtop dvalue :=
    match ct with
    | CONV_Bitcast =>
        if dtyp_eqb t_from t_to
        then ret dv
        else if bit_sizeof_dtyp t_from =? bit_sizeof_dtyp t_to
             then
               let bytes := dvalue_to_memory_bytes dv t_from in
               EOU_to_itree (memory_bytes_to_dvalue bytes t_to)
             else raise "unequal bitsize in cast"
    | CONV_Pure ct =>
        EOU_to_itree (convert_pure ct t_from dv t_to)
    | CONV_Impure ct => conv ct t_from dv t_to
    end.

  
End Convert.

