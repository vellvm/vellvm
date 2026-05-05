From Vellvm Require Import
     Numeric.Rocqlib
     Numeric.Integers
     Numeric.Floats
     Utils.Tactics
     Utils.Util
     Utils.OptionUtil
     Utils.Error
     Utils.ListUtil
     Utils.NonEmpty
     Utils.NMaps
     Utils.Monads
     Utils.MonadReturnsLaws
     Utils.ErrUbOomProp
     Syntax.LLVMAst
     Syntax.DynamicTypes
     Syntax.DataLayout
     Semantics.VellvmIntegers
     Semantics.DynamicValues
     Semantics.MemoryAddress
     Semantics.GepM
     Semantics.Memory.Sizeof
     Semantics.MemoryParams
     Semantics.LLVMEvents
     Semantics.LLVMParams
     Handlers.MemoryModel
     QC.ShowAST.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.EitherMonad
     StateMonad.

From Stdlib Require Import Lia.

Import IdentityMonad.

Import ListNotations.
Import MonadNotation.

(* TODO: replace in the next iteration *)
Definition err_oom := eitherT string (@sum string).
Instance err_oom_error : RAISE_ERROR err_oom := {| raise_error _ s := raise s |}.
Instance err_oom_oom : RAISE_OOM err_oom := {| raise_oom _ s := lift (raise s) |}.

(* TODO: why can't this be inferred? *)
#[global] Instance Monad_StateT_err_ub_oom : Monad (stateT N (err_ub_oom_T ident)).
Proof.
  eapply Monad_stateT; typeclasses eauto.
Defined.

Module Type CONVERSIONS (LP : LLVMParams) (MP : MEMORY_PARAMS LP).
  Import MP.
  Import LP.
  Import PTOI.
  Import ITOP.
  Import PROV.
  Import GEP.
  Import SZ.
  Import DV.
  Import MP.MBYTES.
  Import IP.

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
        | DTYPE_I sz_t, @DVALUE_I sz_from i1, DTYPE_I sz_to =>
            if Pos.eqb sz_t sz_from && (sz_to <? sz_from)%positive
            then Conv_Pure (@DVALUE_I sz_to (repr (unsigned i1)))
            else Conv_Illegal "i-to-i ill-typed Trunc"

        | DTYPE_I sz_t, DVALUE_Poison t, DTYPE_I sz_to =>
            Conv_Pure (DVALUE_Poison t)

        | _, _, _ => Conv_Illegal "ill-typed Trunc"
        end

    | Zext nneg => (* TODO: handle the nneg flag *)
        match t1, x, t2 with
        | DTYPE_I sz_t, @DVALUE_I sz_from i1, DTYPE_I sz_to =>
            if Pos.eqb sz_t sz_from && (sz_from <? sz_to)%positive
            then Conv_Pure (@DVALUE_I sz_to (repr (unsigned i1)))
            else Conv_Illegal "i-to-i ill-typed Zext"

        | DTYPE_I sz_t, DVALUE_Poison t, DTYPE_I sz_to =>
            Conv_Pure (DVALUE_Poison t)

        | _, _, _ => Conv_Illegal "ill-typed Zext"
        end

    | Sext =>
        match t1, x, t2 with
        | DTYPE_I sz_t, @DVALUE_I sz_from i1, DTYPE_I sz_to =>
            if Pos.eqb sz_t sz_from && (sz_from <? sz_to)%positive
            then Conv_Pure (@DVALUE_I sz_to (repr (signed i1)))
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
               let dv_conv :=  (memory_bytes_to_dvalue (M := err_oom) bytes t2) in
               match unEitherT dv_conv with
               | inl err => Conv_Illegal ("Bitcast failure: " ++ err)
               | inr (inl oom) => Conv_Oom ("Bitcast OOM: " ++ oom)
               | inr (inr v) => Conv_Pure v
               end
             else Conv_Illegal "unequal bitsize in cast"

    | Uitofp nneg => (* TODO: handle the nneg flag *)
        match t1, x, t2 with
        | DTYPE_I sz_t, @DVALUE_I sz_from i1, DTYPE_FP FP_float =>
            if Pos.eqb sz_t sz_from
            then Conv_Pure (DVALUE_Float (Float32.of_intu (repr (unsigned i1))))
            else Conv_Illegal "i-to-float ill-typed Uitofp"

        | DTYPE_I sz_t, @DVALUE_I sz_from i1, DTYPE_FP FP_double =>
            if Pos.eqb sz_t sz_from
            then Conv_Pure (DVALUE_Double (Float.of_longu (repr (unsigned i1))))
            else Conv_Illegal "i-to-double ill-typed Uitofp"

        | DTYPE_I sz_t, DVALUE_Poison t, DTYPE_FP _ =>
            Conv_Pure (DVALUE_Poison t)

        | _, _, _ => Conv_Illegal "ill-typed Uitofp"
        end

    | Sitofp =>
        match t1, x, t2 with
        | DTYPE_I sz_t, @DVALUE_I sz_from i1, DTYPE_FP FP_float =>
            if Pos.eqb sz_t sz_from
            then Conv_Pure (DVALUE_Float (Float32.of_intu (repr (signed i1))))
            else Conv_Illegal "i-to-float ill-typed Sitofp"

        | DTYPE_I sz_t, @DVALUE_I sz_from i1, DTYPE_FP FP_double =>
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
        | DTYPE_IPTR , DTYPE_Pointer => Conv_ItoP x
        | _, _ => Conv_Illegal "Inttoptr got illegal arguments"
        end
    | Ptrtoint =>
        match t1, t2 with
        | DTYPE_Pointer, DTYPE_I _ => Conv_PtoI x
        | DTYPE_Pointer, DTYPE_IPTR => Conv_PtoI x
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

End CONVERSIONS.

