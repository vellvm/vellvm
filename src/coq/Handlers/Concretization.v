From Vellvm Require Import
     Numeric.Coqlib
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
     Semantics.DynamicValues
     Semantics.MemoryAddress
     Semantics.GepM
     Semantics.Memory.Sizeof
     Semantics.Memory.MemBytes
     Semantics.MemoryParams
     Semantics.LLVMEvents
     Semantics.LLVMParams
     Handlers.MemoryModel.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.EitherMonad
     StateMonad.

Require Import Lia.

Import IdentityMonad.

Import ListNotations.
Import MonadNotation.

(* TODO: Move this *)
#[global] Instance MonadStoreId_stateT {M} `{HM: Monad M} : MemPropT.MonadStoreId (stateT MemPropT.store_id M).
Proof.
  split.
  eapply (sid <- get;;
          put (sid + 1);;
          ret sid).

  Unshelve.
  (* TODO: why can't this be inferred? *)
  all: eapply Monad_stateT; eauto.
Defined.

(* TODO: why can't this be inferred? *)
#[global] Instance Monad_StateT_err_ub_oom : Monad (stateT N (err_ub_oom_T ident)).
Proof.
  eapply Monad_stateT; typeclasses eauto.
Defined.

Module Type ConcretizationBase (LP : LLVMParams) (MP : MemoryParams LP) (Byte : ByteModule LP.ADDR LP.IP LP.SIZEOF LP.Events MP.BYTE_IMPL).
  Import MP.
  Import LP.
  Import PTOI.
  Import ITOP.
  Import PROV.
  Import GEP.
  Import SIZEOF.
  Import Events.

  Module MemHelpers := MemoryHelpers LP MP Byte.
  Import MemHelpers.

  Definition eval_icmp {M} `{Monad M} `{RAISE_ERROR M} icmp v1 v2 : M dvalue :=
    match v1, v2 with
    | DVALUE_I1 i1, DVALUE_I1 i2
    | DVALUE_I8 i1, DVALUE_I8 i2
    | DVALUE_I32 i1, DVALUE_I32 i2
    | DVALUE_I64 i1, DVALUE_I64 i2
    | DVALUE_IPTR i1, DVALUE_IPTR i2 => ret (eval_int_icmp icmp i1 i2)
    | DVALUE_Poison t1, DVALUE_Poison t2 => ret (DVALUE_Poison t1)
    | DVALUE_Poison t, _ => if is_DVALUE_IX v2 then ret (DVALUE_Poison t) else raise_error "ill_typed-iop"
    | _, DVALUE_Poison t => if is_DVALUE_IX v1 then ret (DVALUE_Poison t) else raise_error "ill_typed-iop"
    | DVALUE_Addr a1, DVALUE_Addr a2 =>
        let i1 := ptr_to_int a1 in
        let i2 := ptr_to_int a2 in
        ret (eval_int_icmp icmp i1 i2)
    | _, _ => raise_error "ill_typed-icmp"
    end.
  Arguments eval_icmp _ _ _ : simpl nomatch.

  Section CONVERSIONS.

    (** ** Typed conversion
        Performs a dynamic conversion of a [dvalue] of type [t1] to one of type [t2].
        For instance, convert an integer over 8 bits to one over 1 bit by truncation.

        The conversion function is not pure, i.e. in particular cannot live in [DynamicValues.v]
        as would be natural, due to the [Int2Ptr] and [Ptr2Int] cases. At those types, the conversion
        needs to cast between integers and pointers, which depends on the memory model.
     *)

    Definition get_conv_case conv (t1:dtyp) (x:dvalue) (t2:dtyp) : conv_case :=
      match conv with
      | Trunc =>
        match t1, x, t2 with
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 1
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 1
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_I 1 =>
          Conv_Pure (DVALUE_I1 (repr (unsigned i1)))

        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 8
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_I 8 =>
          Conv_Pure (DVALUE_I8 (repr (unsigned i1)))

        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_I 32 =>
          Conv_Pure (DVALUE_I32 (repr (unsigned i1)))

        | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 1
        | DTYPE_I 32, DVALUE_Poison t, DTYPE_I 1
        | DTYPE_I 32, DVALUE_Poison t, DTYPE_I 8
        | DTYPE_I 64, DVALUE_Poison t, DTYPE_I 1
        | DTYPE_I 64, DVALUE_Poison t, DTYPE_I 8
        | DTYPE_I 64, DVALUE_Poison t, DTYPE_I 32 =>
          Conv_Pure (DVALUE_Poison t)

        | _, _, _ => Conv_Illegal "ill-typed conv"
        end

      | Zext =>
        match t1, x, t2 with
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 8 =>
          Conv_Pure (DVALUE_I8 (repr (unsigned i1)))

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 32
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 32 =>
          Conv_Pure (DVALUE_I32 (repr (unsigned i1)))

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 64
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 64
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 64 =>
          Conv_Pure (DVALUE_I64 (repr (unsigned i1)))

        | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 8
        | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 32
        | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 32
        | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 64
        | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 64
        | DTYPE_I 32, DVALUE_Poison t, DTYPE_I 64 =>
          Conv_Pure (DVALUE_Poison t)

        | _, _, _ => Conv_Illegal "ill-typed conv"
        end

      | Sext =>
        match t1, x, t2 with
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 8 =>
          Conv_Pure (DVALUE_I8 (repr (signed i1)))

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 32
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 32 =>
          Conv_Pure (DVALUE_I32 (repr (signed i1)))

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 64
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 64
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 64 =>
          Conv_Pure (DVALUE_I64 (repr (signed i1)))

        | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 8
        | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 32
        | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 32
        | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 64
        | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 64
        | DTYPE_I 32, DVALUE_Poison t, DTYPE_I 64 =>
          Conv_Pure (DVALUE_Poison t)

        | _, _, _ => Conv_Illegal "ill-typed conv"
        end

      | Bitcast =>
          if bit_sizeof_dtyp t1 =? bit_sizeof_dtyp t2
          then
            let bytes := evalStateT (serialize_sbytes (dvalue_to_uvalue x) t1) 0%N in
            match unIdent (unEitherT (unEitherT (unEitherT (unERR_UB_OOM bytes)))) with
            | inl (OOM_message oom) =>
                Conv_Illegal ("Bitcast OOM: " ++ oom)
            | inr (inl (UB_message ub)) =>
                Conv_Illegal ("Bitcast UB: " ++ ub)
            | inr (inr (inl (ERR_message err))) =>
                Conv_Illegal ("Bitcast Error: " ++ err)
            | inr (inr (inr bytes)) =>
                match deserialize_sbytes bytes t2 with
                | inl msg => Conv_Illegal ("Bitcast failed: " ++ msg)
                | inr uv =>
                    match uvalue_to_dvalue uv with
                    | inl msg => Conv_Illegal ("Bitcast failed to convert to dvalue: " ++ msg)
                    | inr dv => Conv_Pure dv
                    end
                end
            end
          else Conv_Illegal "unequal bitsize in cast"

      | Uitofp =>
        match t1, x, t2 with
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Float
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Float
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Float
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Float =>
          Conv_Pure (DVALUE_Float (Float32.of_intu (repr (unsigned i1))))

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Double
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Double
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Double
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Double =>
          Conv_Pure (DVALUE_Double (Float.of_longu (repr (unsigned i1))))

        | DTYPE_I 1, DVALUE_Poison t, DTYPE_Float
        | DTYPE_I 8, DVALUE_Poison t, DTYPE_Float
        | DTYPE_I 32, DVALUE_Poison t, DTYPE_Float
        | DTYPE_I 64, DVALUE_Poison t, DTYPE_Float
        | DTYPE_I 1, DVALUE_Poison t, DTYPE_Double
        | DTYPE_I 8, DVALUE_Poison t, DTYPE_Double
        | DTYPE_I 32, DVALUE_Poison t, DTYPE_Double
        | DTYPE_I 64, DVALUE_Poison t, DTYPE_Double =>
          Conv_Pure (DVALUE_Poison t)

        | _, _, _ => Conv_Illegal "ill-typed Uitofp"
        end

      | Sitofp =>
        match t1, x, t2 with
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Float
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Float
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Float
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Float =>
          Conv_Pure (DVALUE_Float (Float32.of_intu (repr (signed i1))))

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Double
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Double
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Double
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Double =>
          Conv_Pure (DVALUE_Double (Float.of_longu (repr (signed i1))))

        | DTYPE_I 1, DVALUE_Poison t, DTYPE_Float
        | DTYPE_I 8, DVALUE_Poison t, DTYPE_Float
        | DTYPE_I 32, DVALUE_Poison t, DTYPE_Float
        | DTYPE_I 64, DVALUE_Poison t, DTYPE_Float
        | DTYPE_I 1, DVALUE_Poison t, DTYPE_Double
        | DTYPE_I 8, DVALUE_Poison t, DTYPE_Double
        | DTYPE_I 32, DVALUE_Poison t, DTYPE_Double
        | DTYPE_I 64, DVALUE_Poison t, DTYPE_Double =>
          Conv_Pure (DVALUE_Poison t)

        | _, _, _ => Conv_Illegal "ill-typed Sitofp"
        end

      | Inttoptr =>
        match t1, t2 with
        | DTYPE_I _, DTYPE_Pointer => Conv_ItoP x
        | DTYPE_IPTR , DTYPE_Pointer => Conv_ItoP x
        | _, _ => Conv_Illegal "ERROR: Inttoptr got illegal arguments"
        end
      | Ptrtoint =>
        match t1, t2 with
        | DTYPE_Pointer, DTYPE_I _ => Conv_PtoI x
        | DTYPE_Pointer, DTYPE_IPTR => Conv_PtoI x
        | _, _ => Conv_Illegal "ERROR: Ptrtoint got illegal arguments"
        end

      | Fptoui
      | Fptosi
      | Fptrunc
      | Fpext
      | Addrspacecast
        => Conv_Illegal "TODO: unimplemented numeric conversion"
      end.
    Arguments get_conv_case _ _ _ _ : simpl nomatch.

  End CONVERSIONS.

  Parameter ptr_size : nat.
  Parameter endianess : Endianess.
  Parameter concretize_uvalueM :
    forall (M : Type -> Type) `{Monad M} (handler : dtyp -> M dvalue)
      (ERR_M : Type -> Type) `{Monad ERR_M} `{RAISE_ERROR ERR_M} `{RAISE_UB ERR_M} `{RAISE_OOM ERR_M},
      (forall A : Type, ERR_M A -> M A) -> uvalue -> M dvalue.
  Parameter extractbytes_to_dvalue :
    forall (M : Type -> Type) `{Monad M} (handler : dtyp -> M dvalue) (ERR_M : Type -> Type) `{Monad ERR_M} `{RAISE_ERROR ERR_M} `{RAISE_UB ERR_M} `{RAISE_OOM ERR_M},
      (forall A : Type, ERR_M A -> M A) -> list uvalue -> dtyp -> M dvalue.

  Parameter all_extract_bytes_from_uvalue : dtyp -> list uvalue -> option uvalue.

  Parameter eval_select :
    forall (M : Type -> Type) `{Monad M} (handler : dtyp -> M dvalue)
      (ERR_M : Type -> Type) `{Monad ERR_M} `{RAISE_ERROR ERR_M} `{RAISE_UB ERR_M} `{RAISE_OOM ERR_M}
      (lift_ue : forall A : Type, ERR_M A -> M A)
      (cnd : dvalue) (v1 v2 : uvalue), M dvalue.

  (* Equations *)
  Parameter concretize_uvalueM_equation :
    forall (M : Type -> Type) {HM : Monad M} (undef_handler : dtyp -> M dvalue)
      (ERR_M : Type -> Type) {HM_ERR : Monad ERR_M} {ERR : RAISE_ERROR ERR_M} {UB : RAISE_UB ERR_M}
      {OOM : RAISE_OOM ERR_M} (lift_ue : forall A : Type, ERR_M A -> M A) (u : uvalue),
      concretize_uvalueM M undef_handler ERR_M lift_ue u =
        match u with
        | UVALUE_Addr a => ret (DVALUE_Addr a)
        | UVALUE_I1 x => ret (DVALUE_I1 x)
        | UVALUE_I8 x => ret (DVALUE_I8 x)
        | UVALUE_I32 x => ret (DVALUE_I32 x)
        | UVALUE_I64 x => ret (DVALUE_I64 x)
        | UVALUE_IPTR x => ret (DVALUE_IPTR x)
        | UVALUE_Double x => ret (DVALUE_Double x)
        | UVALUE_Float x => ret (DVALUE_Float x)
        | UVALUE_Undef t => undef_handler t
        | UVALUE_Poison t => ret (DVALUE_Poison t)
        | UVALUE_Oom t => ret (DVALUE_Oom t)
        | UVALUE_None => ret DVALUE_None
        | UVALUE_Struct fields =>
            x <- map_monad (concretize_uvalueM M undef_handler ERR_M lift_ue) fields;; ret (DVALUE_Struct x)
        | UVALUE_Packed_struct fields =>
            x <- map_monad (concretize_uvalueM M undef_handler ERR_M lift_ue) fields;;
            ret (DVALUE_Packed_struct x)
        | UVALUE_Array elts =>
            x <- map_monad (concretize_uvalueM M undef_handler ERR_M lift_ue) elts;; ret (DVALUE_Array x)
        | UVALUE_Vector elts =>
            x <- map_monad (concretize_uvalueM M undef_handler ERR_M lift_ue) elts;; ret (DVALUE_Vector x)
        | UVALUE_IBinop iop v1 v2 =>
            dv1 <- concretize_uvalueM M undef_handler ERR_M lift_ue v1;;
            dv2 <- concretize_uvalueM M undef_handler ERR_M lift_ue v2;; lift_ue dvalue (eval_iop iop dv1 dv2)
        | UVALUE_ICmp cmp v1 v2 =>
            dv1 <- concretize_uvalueM M undef_handler ERR_M lift_ue v1;;
            dv2 <- concretize_uvalueM M undef_handler ERR_M lift_ue v2;; lift_ue dvalue (eval_icmp cmp dv1 dv2)
        | UVALUE_FBinop fop _ v1 v2 =>
            dv1 <- concretize_uvalueM M undef_handler ERR_M lift_ue v1;;
            dv2 <- concretize_uvalueM M undef_handler ERR_M lift_ue v2;; lift_ue dvalue (eval_fop fop dv1 dv2)
        | UVALUE_FCmp cmp v1 v2 =>
            dv1 <- concretize_uvalueM M undef_handler ERR_M lift_ue v1;;
            dv2 <- concretize_uvalueM M undef_handler ERR_M lift_ue v2;; lift_ue dvalue (eval_fcmp cmp dv1 dv2)
        | UVALUE_Conversion conv t_from v t_to =>
            dv <- concretize_uvalueM M undef_handler ERR_M lift_ue v;;
            match get_conv_case conv t_from dv t_to with
            | Conv_Pure x => ret x
            | Conv_ItoP x =>
                match int_to_ptr (dvalue_int_unsigned x) wildcard_prov with
                | NoOom a =>
                    ret (DVALUE_Addr a)
                | Oom msg =>
                    lift_ue dvalue (raise_oom ("concretize_uvalueM OOM in Conv_ItoP: " ++ msg))
                end
            | Conv_PtoI (DVALUE_Addr addr) =>
                match t_to with
                | DTYPE_I sz => lift_ue dvalue (coerce_integer_to_int (Some sz) (ptr_to_int addr))
                | DTYPE_IPTR => lift_ue dvalue (coerce_integer_to_int None (ptr_to_int addr))
                | _ => lift_ue dvalue (raise_error "Invalid PTOI conversion")
                end
            | Conv_Illegal s => lift_ue dvalue (raise_error s)
            | _ => lift_ue dvalue (raise_error "Invalid PTOI conversion")
            end
        | UVALUE_GetElementPtr t ua uvs =>
            da <- concretize_uvalueM M undef_handler ERR_M lift_ue ua;;
            dvs <- map_monad (concretize_uvalueM M undef_handler ERR_M lift_ue) uvs;;
            match handle_gep t da dvs with
            | inl err => lift_ue dvalue (raise_error err)
            | inr (Oom msg) => lift_ue dvalue (raise_oom ("concretize_uvalueM OOM in GetElementPtr: " ++ msg))
            | inr (NoOom dv) => ret dv
            end
        | UVALUE_ExtractValue t uv idxs =>
            str <- concretize_uvalueM M undef_handler ERR_M lift_ue uv;;
            (let
                fix loop (str0 : dvalue) (idxs0 : list int) {struct idxs0} : ERR_M dvalue :=
                match idxs0 with
                | [] => ret str0
                | i :: tl => v <- index_into_str_dv str0 i;; loop v tl
                end in
              lift_ue dvalue (loop str idxs))

        | UVALUE_Select cond v1 v2 =>
            dcond <- concretize_uvalueM M undef_handler ERR_M lift_ue cond;;
            eval_select M undef_handler ERR_M lift_ue dcond v1 v2
        | UVALUE_ExtractByte _ _ _ _ =>
            lift_ue dvalue (raise_error "Attempting to concretize UVALUE_ExtractByte, should not happen.")
        | UVALUE_ConcatBytes bytes dt =>
            if N.of_nat (Datatypes.length bytes) =? sizeof_dtyp dt
            then
              match all_extract_bytes_from_uvalue dt bytes with
              | Some uv => concretize_uvalueM M undef_handler ERR_M lift_ue uv
              | None => extractbytes_to_dvalue M undef_handler ERR_M lift_ue bytes dt
              end
            else extractbytes_to_dvalue M undef_handler ERR_M lift_ue bytes dt
        | UVALUE_InsertValue t uv elt idxs =>
            str <- concretize_uvalueM M undef_handler ERR_M lift_ue uv;;
            elt <- concretize_uvalueM M undef_handler ERR_M lift_ue elt;;
            let fix loop str idxs : ERR_M dvalue :=
              match idxs with
              | [] => raise_error "Index was not provided"
              | i :: nil =>
                  v <- insert_into_str str elt i;;
                  ret v
              | i :: tl =>
                  subfield <- index_into_str_dv str i;;
                  modified_subfield <- loop subfield tl;;
                  insert_into_str str modified_subfield i
              end in
            lift_ue dvalue (loop str idxs)
        | UVALUE_ExtractElement vec_typ vec idx =>
            dvec <- concretize_uvalueM M undef_handler ERR_M lift_ue vec;;
            didx <- concretize_uvalueM M undef_handler ERR_M lift_ue idx;;
            elt_typ <- match vec_typ with
                       | DTYPE_Vector _ t => ret t
                       | _ => lift_ue _ (raise_error "Invalid vector type for ExtractElement")
                       end;;
            lift_ue dvalue (index_into_vec_dv elt_typ dvec didx)
        | UVALUE_InsertElement vec_typ vec elt idx =>
            dvec <- concretize_uvalueM M undef_handler ERR_M lift_ue vec;;
            didx <- concretize_uvalueM M undef_handler ERR_M lift_ue idx;;
            delt <- concretize_uvalueM M undef_handler ERR_M lift_ue elt;;
            lift_ue dvalue (insert_into_vec_dv vec_typ dvec delt didx)
        | _ =>
            lift_ue dvalue
                    (raise_error
                       ("concretize_uvalueM: Attempting to convert a partially non-reduced uvalue to dvalue. Should not happen: " ++
                                                                                                                                  uvalue_constructor_string u))
        end.
End ConcretizationBase.

Module Type Concretization (LP : LLVMParams) (MP : MemoryParams LP) (Byte : ByteModule LP.ADDR LP.IP LP.SIZEOF LP.Events MP.BYTE_IMPL) (SER : ConcretizationBase LP MP Byte) <: ConcretizationBase LP MP Byte.
  Include SER.
  Import MP.
  Import LP.
  Import Events.

  Definition concretize_uvalue {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_UB M} `{RAISE_OOM M}
             (uv : uvalue) : M dvalue
    := concretize_uvalueM M (fun dt => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt)) M (fun _ x => x) uv.

  Definition concretize_u (uv : uvalue) : ErrUbOomProp dvalue.
    refine (concretize_uvalueM _ (fun dt => _) err_ub_oom (fun _ x => _) uv).

    (* Undef handler *)
    { unfold ErrUbOomProp.
      refine (fun edv => match unERR_UB_OOM edv with
                      | mkEitherT (mkEitherT (mkEitherT (mkIdent (inr (inr (inr dv)))))) =>
                          (* As long as the dvalue has the same type, it's a refinement *)
                          dvalue_has_dtyp dv dt
                      | _ => False
                      end).
    }

    (* lift_ue *)
    { unfold ErrUbOomProp.
      intros ue.
      exact (x=ue).
    }
  Defined.

  Definition concretize_u_succeeds (uv : uvalue) : ErrUbOomProp dvalue.
    refine (concretize_uvalueM _ (fun dt => _) err_ub_oom (fun _ x => _) uv).

    (* Undef handler *)
    { unfold ErrUbOomProp.
      refine (fun edv => match unERR_UB_OOM edv with
                      | mkEitherT (mkEitherT (mkEitherT (mkIdent (inr (inr (inr dv)))))) =>
                          (* As long as the dvalue has the same type, it's a refinement *)
                          dvalue_has_dtyp dv dt
                      | _ => False
                      end).
    }

    (* lift_ue *)
    { unfold ErrUbOomProp.
      intros ue.

      exact (~MFails x /\ ~MFails ue).
    }
  Defined.

  Definition concretize (uv: uvalue) (dv : dvalue) := concretize_u uv (ret dv).

  (* TODO: should the post condition be concretize uv dv ? *)
  Definition pick_uvalue (Pre : Prop) (uv : uvalue) : PickUvalueE {dv : dvalue | True}
    := pick Pre uv.

  (* Concretization encounters UB / Failure.

     Note, this does mean that `concretize_u uv (ret dv)` should hold
     for any `dv`. This just means that UB or Failure was encountered
     during concretization.
   *)
  Definition concretize_fails (uv : uvalue) : Prop
    := concretize_u uv (raise_ub "").

  (* Concretization succeeds without UB / Error *)
  Definition concretize_succeeds (uv : uvalue) : Prop
    := ~ concretize_fails uv.

  Lemma concretize_equation : forall (uv: uvalue) (dv : dvalue),
      concretize uv dv = concretize_u uv (ret dv).
  Proof.
    reflexivity.
  Qed.

  Lemma Concretize_Undef : forall dt dv,
      dvalue_has_dtyp dv dt ->
      concretize (UVALUE_Undef dt) dv.
  Proof.
    intros dt dv H.
    rewrite concretize_equation.
    unfold concretize_u.
    rewrite concretize_uvalueM_equation.
    cbn; auto.
  Qed.

  Lemma Concretize_IBinop : forall iop uv1 e1 uv2 e2,
      concretize_u uv1 e1 ->
      concretize_u uv2 e2 ->
      concretize_u (UVALUE_IBinop iop uv1 uv2)
                   (dv1 <- e1 ;;
                    dv2 <- e2 ;;
                    (eval_iop iop dv1 dv2)).
  Proof.
    intros iop uv1 e1 uv2 e2 C1 C2.
    unfold concretize_u in *.

    rewrite concretize_uvalueM_equation.
    red.

    unfold bind.
    cbn.
    unfold bind_ErrUbOomProp.

    eexists.
    exists (fun x => match unIdent (unEitherT (unEitherT (unEitherT (unERR_UB_OOM e2)))) with
             | inl (OOM_message oom) => raise_oom oom
             | inr (inl (UB_message ub)) => raise_ub ub
             | inr (inr (inl (ERR_message err))) => raise_error err
             | inr (inr (inr x0)) => eval_iop iop x x0
             end).
    split; eauto.
    split; eauto.

    { (* Monad.eq1 mb (x <- ma;; k' x) *)
      unfold bind.
      cbn.
      destruct e1 as [[[[[[[oom_e1] | [[ub_e1] | [[err_e1] | e1]]]]]]]]; cbn; try reflexivity.
      destruct e2 as [[[[[[[oom_e2] | [[ub_e2] | [[err_e2] | e2]]]]]]]]; cbn; try reflexivity.
    }

    right.
    intros dv1 Re1.

    eexists.
    exists (fun x0 => eval_iop iop dv1 x0).
    split; eauto.
    split.

    { (* Monad.eq1 mb (x <- ma;; k' x) *)
      unfold bind.
      cbn.
      destruct e2 as [[[[[[[oom_e2] | [[ub_e2] | [[err_e2] | e2]]]]]]]]; cbn; try reflexivity.

      unfold Monad.eq1.
      destruct (eval_iop iop dv1 e2) as [[[[[[[oom_eval_iopiopdv1e2] | [[ub_eval_iopiopdv1e2] | [[err_eval_iopiopdv1e2] | eval_iopiopdv1e2]]]]]]]]; reflexivity.
    }

    right.
    intros dv2 Re2.
    destruct (eval_iop iop dv1 dv2) as [[[[[[[oom_eval_iopiopdv1dv2] | [[ub_eval_iopiopdv1dv2] | [[err_eval_iopiopdv1dv2] | eval_iopiopdv1dv2]]]]]]]]; reflexivity.
  Qed.

End Concretization.

Module MakeBase (LP : LLVMParams) (MP : MemoryParams LP) (Byte : ByteModule LP.ADDR LP.IP LP.SIZEOF LP.Events MP.BYTE_IMPL) <: ConcretizationBase LP MP Byte.
  Import MP.
  Import LP.
  Import Events.
  Import SIZEOF.
  Import PTOI.
  Import PROV.
  Import ITOP.
  Import DV.
  Import GEP.
  Open Scope list.

  Export Byte.

  Module MemHelpers := MemoryHelpers LP MP Byte.
  Import MemHelpers.

  Definition eval_icmp {M} `{Monad M} `{RAISE_ERROR M} icmp v1 v2 : M dvalue :=
    match v1, v2 with
    | DVALUE_I1 i1, DVALUE_I1 i2
    | DVALUE_I8 i1, DVALUE_I8 i2
    | DVALUE_I32 i1, DVALUE_I32 i2
    | DVALUE_I64 i1, DVALUE_I64 i2
    | DVALUE_IPTR i1, DVALUE_IPTR i2 => ret (eval_int_icmp icmp i1 i2)
    | DVALUE_Poison t1, DVALUE_Poison t2 => ret (DVALUE_Poison t1)
    | DVALUE_Poison t, _ => if is_DVALUE_IX v2 then ret (DVALUE_Poison t) else raise_error "ill_typed-iop"
    | _, DVALUE_Poison t => if is_DVALUE_IX v1 then ret (DVALUE_Poison t) else raise_error "ill_typed-iop"
    | DVALUE_Addr a1, DVALUE_Addr a2 =>
        let i1 := ptr_to_int a1 in
        let i2 := ptr_to_int a2 in
        ret (eval_int_icmp icmp i1 i2)
    | _, _ => raise_error "ill_typed-icmp"
    end.
  Arguments eval_icmp _ _ _ : simpl nomatch.

  Section CONVERSIONS.

    (** ** Typed conversion
        Performs a dynamic conversion of a [dvalue] of type [t1] to one of type [t2].
        For instance, convert an integer over 8 bits to one over 1 bit by truncation.

        The conversion function is not pure, i.e. in particular cannot live in [DynamicValues.v]
        as would be natural, due to the [Int2Ptr] and [Ptr2Int] cases. At those types, the conversion
        needs to cast between integers and pointers, which depends on the memory model.
     *)

    (* Note: Inferring the subevent instance takes a small but non-trivial amount of time,
       and has to be done here hundreds and hundreds of times due to the brutal pattern matching on
       several values. Factoring the inference upfront is therefore necessary.
     *)

    (* A trick avoiding proofs that involve thousands of cases: we split the conversion into
      the composition of a huge case analysis that builds a value of [conv_case], and a function
      with only four cases to actually build the tree.
     *)

    Definition get_conv_case conv (t1:dtyp) (x:dvalue) (t2:dtyp) : conv_case :=
      match conv with
      | Trunc =>
        match t1, x, t2 with
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 1
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 1
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_I 1 =>
          Conv_Pure (DVALUE_I1 (repr (unsigned i1)))

        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 8
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_I 8 =>
          Conv_Pure (DVALUE_I8 (repr (unsigned i1)))

        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_I 32 =>
          Conv_Pure (DVALUE_I32 (repr (unsigned i1)))

        | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 1
        | DTYPE_I 32, DVALUE_Poison t, DTYPE_I 1
        | DTYPE_I 32, DVALUE_Poison t, DTYPE_I 8
        | DTYPE_I 64, DVALUE_Poison t, DTYPE_I 1
        | DTYPE_I 64, DVALUE_Poison t, DTYPE_I 8
        | DTYPE_I 64, DVALUE_Poison t, DTYPE_I 32 =>
          Conv_Pure (DVALUE_Poison t)

        | _, _, _ => Conv_Illegal "ill-typed conv"
        end

      | Zext =>
        match t1, x, t2 with
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 8 =>
          Conv_Pure (DVALUE_I8 (repr (unsigned i1)))

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 32
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 32 =>
          Conv_Pure (DVALUE_I32 (repr (unsigned i1)))

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 64
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 64
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 64 =>
          Conv_Pure (DVALUE_I64 (repr (unsigned i1)))

        | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 8
        | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 32
        | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 32
        | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 64
        | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 64
        | DTYPE_I 32, DVALUE_Poison t, DTYPE_I 64 =>
          Conv_Pure (DVALUE_Poison t)

        | _, _, _ => Conv_Illegal "ill-typed conv"
        end

      | Sext =>
        match t1, x, t2 with
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 8 =>
          Conv_Pure (DVALUE_I8 (repr (signed i1)))

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 32
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 32 =>
          Conv_Pure (DVALUE_I32 (repr (signed i1)))

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 64
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 64
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 64 =>
          Conv_Pure (DVALUE_I64 (repr (signed i1)))

        | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 8
        | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 32
        | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 32
        | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 64
        | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 64
        | DTYPE_I 32, DVALUE_Poison t, DTYPE_I 64 =>
          Conv_Pure (DVALUE_Poison t)

        | _, _, _ => Conv_Illegal "ill-typed conv"
        end

      | Bitcast =>
          if bit_sizeof_dtyp t1 =? bit_sizeof_dtyp t2
          then
            let bytes := evalStateT (serialize_sbytes (dvalue_to_uvalue x) t1) 0%N in
            match unIdent (unEitherT (unEitherT (unEitherT (unERR_UB_OOM bytes)))) with
            | inl (OOM_message oom) =>
                Conv_Illegal ("Bitcast OOM: " ++ oom)
            | inr (inl (UB_message ub)) =>
                Conv_Illegal ("Bitcast UB: " ++ ub)
            | inr (inr (inl (ERR_message err))) =>
                Conv_Illegal ("Bitcast Error: " ++ err)
            | inr (inr (inr bytes)) =>
                match deserialize_sbytes bytes t2 with
                | inl msg => Conv_Illegal ("Bitcast failed: " ++ msg)
                | inr uv =>
                    match uvalue_to_dvalue uv with
                    | inl msg => Conv_Illegal ("Bitcast failed to convert to dvalue: " ++ msg)
                    | inr dv => Conv_Pure dv
                    end
                end
            end
          else Conv_Illegal "unequal bitsize in cast"

      | Uitofp =>
        match t1, x, t2 with
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Float
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Float
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Float
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Float =>
          Conv_Pure (DVALUE_Float (Float32.of_intu (repr (unsigned i1))))

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Double
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Double
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Double
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Double =>
          Conv_Pure (DVALUE_Double (Float.of_longu (repr (unsigned i1))))

        | DTYPE_I 1, DVALUE_Poison t, DTYPE_Float
        | DTYPE_I 8, DVALUE_Poison t, DTYPE_Float
        | DTYPE_I 32, DVALUE_Poison t, DTYPE_Float
        | DTYPE_I 64, DVALUE_Poison t, DTYPE_Float
        | DTYPE_I 1, DVALUE_Poison t, DTYPE_Double
        | DTYPE_I 8, DVALUE_Poison t, DTYPE_Double
        | DTYPE_I 32, DVALUE_Poison t, DTYPE_Double
        | DTYPE_I 64, DVALUE_Poison t, DTYPE_Double =>
          Conv_Pure (DVALUE_Poison t)

        | _, _, _ => Conv_Illegal "ill-typed Uitofp"
        end

      | Sitofp =>
        match t1, x, t2 with
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Float
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Float
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Float
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Float =>
          Conv_Pure (DVALUE_Float (Float32.of_intu (repr (signed i1))))

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Double
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Double
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Double
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Double =>
          Conv_Pure (DVALUE_Double (Float.of_longu (repr (signed i1))))

        | DTYPE_I 1, DVALUE_Poison t, DTYPE_Float
        | DTYPE_I 8, DVALUE_Poison t, DTYPE_Float
        | DTYPE_I 32, DVALUE_Poison t, DTYPE_Float
        | DTYPE_I 64, DVALUE_Poison t, DTYPE_Float
        | DTYPE_I 1, DVALUE_Poison t, DTYPE_Double
        | DTYPE_I 8, DVALUE_Poison t, DTYPE_Double
        | DTYPE_I 32, DVALUE_Poison t, DTYPE_Double
        | DTYPE_I 64, DVALUE_Poison t, DTYPE_Double =>
          Conv_Pure (DVALUE_Poison t)

        | _, _, _ => Conv_Illegal "ill-typed Sitofp"
        end

      | Inttoptr =>
        match t1, t2 with
        | DTYPE_I _, DTYPE_Pointer => Conv_ItoP x
        | DTYPE_IPTR , DTYPE_Pointer => Conv_ItoP x
        | _, _ => Conv_Illegal "ERROR: Inttoptr got illegal arguments"
        end
      | Ptrtoint =>
        match t1, t2 with
        | DTYPE_Pointer, DTYPE_I _ => Conv_PtoI x
        | DTYPE_Pointer, DTYPE_IPTR => Conv_PtoI x
        | _, _ => Conv_Illegal "ERROR: Ptrtoint got illegal arguments"
        end

      | Fptoui
      | Fptosi
      | Fptrunc
      | Fpext
      | Addrspacecast
        => Conv_Illegal "TODO: unimplemented numeric conversion"
      end.
    Arguments get_conv_case _ _ _ _ : simpl nomatch.

  End CONVERSIONS.

  (* Variable ptr_size : nat. *)
  (* Variable datalayout : DataLayout. *)
  Definition ptr_size : nat := 8.

  Definition addr := ADDR.addr.

  Definition endianess : Endianess
    := ENDIAN_LITTLE.

  Fixpoint all_extract_bytes_from_uvalue_helper (idx' : Z) (sid' : store_id) (dt' : dtyp) (parent : uvalue) (bytes : list uvalue) : option uvalue
    := match bytes with
       | [] => Some parent
       | (UVALUE_ExtractByte uv dt idx sid)::bytes =>
           guard_opt (uvalue_int_eq_Z idx idx');;
           guard_opt (RelDec.rel_dec uv parent);;
           guard_opt (N.eqb sid sid');;
           guard_opt (dtyp_eqb dt dt');;
           all_extract_bytes_from_uvalue_helper (Z.succ idx') sid' dt' parent bytes
       | _ => None
       end.

  (* Check that store ids, uvalues, and types match up, as well as
       that the extract byte indices are in the right order *)
  Definition all_extract_bytes_from_uvalue (t : dtyp) (bytes : list uvalue) : option uvalue
    := match bytes with
       | nil => None
       | (UVALUE_ExtractByte uv dt idx sid)::xs =>
           guard_opt (dtyp_eqb t dt);;
           all_extract_bytes_from_uvalue_helper 0 sid dt uv bytes
       | _ => None
       end.

  (* Definition fp_alignment (bits : N) : option Alignment := *)
  (*   let fp_map := dl_floating_point_alignments datalayout *)
  (*   in NM.find bits fp_map. *)

  (* Definition int_alignment (bits : N) : option Alignment := *)
  (*   let int_map := dl_integer_alignments datalayout *)
  (*   in match NM.find bits int_map with *)
  (*      | Some align => Some align *)
  (*      | None => *)
  (*        let keys  := map fst (NM.elements int_map) in *)
  (*        let bits' := nextOrMaximumOpt N.leb bits keys  *)
  (*        in match bits' with *)
  (*           | Some bits => NM.find bits int_map *)
  (*           | None => None *)
  (*           end *)
  (*      end. *)

  (* TODO: Finish this function *)
  (* Fixpoint dtyp_alignment (dt : dtyp) : option Alignment := *)
  (*   match dt with *)
  (*   | DTYPE_I sz => *)
  (*     int_alignment sz *)
  (*   | DTYPE_IPTR => *)
  (*     (* TODO: should these have the same alignments as pointers? *) *)
  (*     int_alignment (N.of_nat ptr_size * 4)%N *)
  (*   | DTYPE_Pointer => *)
  (*     (* TODO: address spaces? *) *)
  (*     Some (ps_alignment (head (dl_pointer_alignments datalayout))) *)
  (*   | DTYPE_Void => *)
  (*     None *)
  (*   | DTYPE_Half => *)
  (*     fp_alignment 16 *)
  (*   | DTYPE_Float => *)
  (*     fp_alignment 32 *)
  (*   | DTYPE_Double => *)
  (*     fp_alignment 64 *)
  (*   | DTYPE_X86_fp80 => *)
  (*     fp_alignment 80 *)
  (*   | DTYPE_Fp128 => *)
  (*     fp_alignment 128 *)
  (*   | DTYPE_Ppc_fp128 => *)
  (*     fp_alignment 128 *)
  (*   | DTYPE_Metadata => *)
  (*     None *)
  (*   | DTYPE_X86_mmx => _ *)
  (*   | DTYPE_Array sz t => *)
  (*     dtyp_alignment t *)
  (*   | DTYPE_Struct fields => _ *)
  (*   | DTYPE_Packed_struct fields => _ *)
  (*   | DTYPE_Opaque => _ *)
  (*   | DTYPE_Vector sz t => _ *)
  (*   end. *)

  (* Assign fresh sids to ubytes while preserving entanglement *)

  (* TODO: address termination checker here *)
  Unset Guard Checking.
  Section Concretize.



    Variable endianess : Endianess.

    (* Convert a list of UVALUE_ExtractByte values into a dvalue of
         a given type.

         Assumes bytes are in little endian form...

         Note: I believe this function has to be endianess aware.

         This probably also needs to be mutually recursive with
         concretize_uvalue...

         Idea:

         For each byte in the list, find uvalues that are from the
         same store.

         - Can I have bytes that are from the same store, but
           different uvalues?  + Might not be possible, actually,
           because if I store a concatbytes I get the old sids...  +
           TODO: Getting the old sids might be a problem,
           though. Should be new, but entangled wherever they were
           entangled before. This needs to be changed in serialize...
           * I.e., If I load bytes from one store, and then store them
           beside them... It should have a different sid, allowing the
           bytes from that store to vary independently.  * ALSO bytes
           that are entangled should *stay* entangled.

         The above is largely an issue with serialize_sbytes...

         The idea here should be to take equal uvalues in our byte
         list with the same sid and concretize the uvalue exactly
         once.

         After all uvalues in our list are concretized we then need to
         convert the corresponding byte extractions into a single
         dvalue.

     *)

    (* TODO: probably move this *)
    (* TODO: Make these take endianess into account.

         Can probably use bitwidth from VInt to do big-endian...
     *)
    Definition extract_byte_vint {I} `{VInt I} (i : I) (idx : Z) : Z
      := unsigned (modu (shru i (repr (idx * 8))) (repr 256)).

    Fixpoint concat_bytes_vint {I} `{VInt I} (bytes : list I) : I
      := match bytes with
         | [] => repr 0
         | (byte::bytes) =>
             add byte (shl (concat_bytes_vint bytes) (repr 8))
         end.

    (* TODO: Endianess *)
    (* TODO: does this work correctly with negative x? *)
    Definition extract_byte_Z (x : Z) (idx : Z) : Z
      := (Z.shiftr x (idx * 8)) mod 256.

    (* TODO: Endianess *)
    Definition concat_bytes_Z_vint {I} `{VInt I} (bytes : list Z) : I
      := concat_bytes_vint (map repr bytes).

    (* TODO: Endianess *)
    Fixpoint concat_bytes_Z (bytes : list Z) : Z
      := match bytes with
         | [] => 0
         | (byte::bytes) =>
             byte + (Z.shiftl (concat_bytes_Z bytes) 8)
         end.

    (* TODO: Move this??? *)
    Inductive Poisonable (A : Type) : Type :=
    | Unpoisoned : A -> Poisonable A
    | Poison : forall (dt : dtyp), Poisonable A
    .

    Arguments Unpoisoned {A} a.
    Arguments Poison {A}.

    #[global] Instance MonadPoisonable : Monad Poisonable
      := { ret  := @Unpoisoned;
           bind := fun _ _ ma mab => match ma with
                                     | Poison dt => Poison dt
                                     | Unpoisoned v => mab v
                                     end
      }.

    Class RAISE_POISON (M : Type -> Type) :=
      { raise_poison : forall {A}, dtyp -> M A }.

    #[global] Instance RAISE_POISON_Poisonable : RAISE_POISON Poisonable :=
      { raise_poison := fun A dt => Poison dt }.

    #[global] Instance RAISE_POISON_E_MT {M : Type -> Type} {MT : (Type -> Type) -> Type -> Type} `{MonadT (MT M) M} `{RAISE_POISON M} : RAISE_POISON (MT M) :=
      { raise_poison := fun A dt => lift (raise_poison dt);
      }.

    (* TODO: Move this??? *)
    Inductive Oomable (A : Type) : Type :=
    | Unoomed : A -> Oomable A
    | Oomed : forall (dt : dtyp), Oomable A
    .

    Arguments Unoomed {A} a.
    Arguments Oomed {A}.

    #[global] Instance MonadOomable : Monad Oomable
      := { ret  := @Unoomed;
           bind := fun _ _ ma mab => match ma with
                                     | Oomed dt => Oomed dt
                                     | Unoomed v => mab v
                                     end
      }.

    Class RAISE_OOMABLE (M : Type -> Type) :=
      { raise_oomable : forall {A}, dtyp -> M A }.

    #[global] Instance RAISE_OOMABLE_Oomable : RAISE_OOMABLE Oomable :=
      { raise_oomable := fun A dt => Oomed dt }.

    #[global] Instance RAISE_OOMABLE_E_MT {M : Type -> Type} {MT : (Type -> Type) -> Type -> Type} `{MonadT (MT M) M} `{RAISE_OOMABLE M} : RAISE_OOMABLE (MT M) :=
      { raise_oomable := fun A dt => lift (raise_oomable dt);
      }.

    Inductive OomableT (m : Type -> Type) (A : Type) : Type :=
      mkOomableT
        { unMkOomableT : m (Oomable A)
        }.

    Arguments mkOomableT {m A}.
    Arguments unMkOomableT {m A}.

    #[global] Instance MonadT_OomableT (m : Type -> Type) `{Monad m} : MonadT (OomableT m) m :=
      { lift := fun T c => mkOomableT (liftM ret c) }.

    Definition lift_OOMABLE {M : Type -> Type} `{Monad M} `{RAISE_OOMABLE M} {A} (dt : dtyp) (ma : OOM A) : M A
      := match ma with
         | NoOom a => ret a
         | Oom s => raise_oomable dt
         end.

    #[global] Instance Monad_OomableT (m : Type -> Type) `{Monad m} : Monad (OomableT m) :=
      {
        ret := fun T x => mkOomableT (ret (Unoomed x));
        bind := fun A B ma mab =>
                  mkOomableT
                    (oom_a <- unMkOomableT ma;;
                     match oom_a with
                     | Oomed dt =>
                         ret (Oomed dt)
                     | Unoomed a =>
                         unMkOomableT (mab a)
                     end
                    )
      }.

    #[global] Instance RAISE_OOMABLE_OomableT m `{Monad m} : RAISE_OOMABLE (OomableT m) :=
      { raise_oomable := fun A dt => mkOomableT (ret (Oomed dt)) }.

    Definition ErrOOMPoison := eitherT ERR_MESSAGE (OomableT Poisonable).

    Definition ErrOOMPoison_handle_poison_and_oom_dv {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_OOM M} (ep : ErrOOMPoison dvalue) : M dvalue
      := match unMkOomableT (unEitherT ep) with
         | Unpoisoned edv =>
             match edv with
             (* TODO: Should we use lazy OOM, or should we raise OOM here? *)
             | Oomed dt => raise_oom "ErrOOMPoison_handle_poison_and_oom_dv: OOM."
             | Unoomed (inl (ERR_message msg)) => raise_error msg
             | Unoomed (inr val) => ret val
             end
         | Poison dt => ret (DVALUE_Poison dt)
         end.

    (* Walk through a list *)
    (* Returns field index + number of bytes remaining *)
    Fixpoint extract_field_byte_helper {M} `{Monad M} `{RAISE_ERROR M} (fields : list dtyp) (field_idx : N) (byte_idx : N) : M (dtyp * (N * N))%type
      := match fields with
         | [] =>
             raise_error "No fields left for byte-indexing..."
         | (x::xs) =>
             let sz := sizeof_dtyp x
             in if N.ltb byte_idx sz
                then ret (x, (field_idx, byte_idx))
                else extract_field_byte_helper xs (N.succ field_idx) (byte_idx - sz)
         end.

    Definition extract_field_byte {M} `{Monad M} `{RAISE_ERROR M} (fields : list dtyp) (byte_idx : N) : M (dtyp * (N * N))%type
      := extract_field_byte_helper fields 0 byte_idx.

    (* Need the type of the dvalue in order to know how big fields and array elements are.

         It's not possible to use the dvalue alone, as DVALUE_Poison's
         size depends on the type.
     *)
    Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia | solve_dvalue_measure].
    Program Fixpoint dvalue_extract_byte {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_POISON M} `{RAISE_OOMABLE M} (dv : dvalue) (dt : dtyp) (idx : Z) {measure (dvalue_measure dv)} : M Z
      := match dv with
         | DVALUE_I1 x
         | DVALUE_I8 x
         | DVALUE_I32 x
         | DVALUE_I64 x =>
             ret (extract_byte_vint x idx)
         | DVALUE_IPTR x =>
             ret (extract_byte_Z (IP.to_Z x) idx)
         | DVALUE_Addr addr =>
             (* Note: this throws away provenance *)
             ret (extract_byte_Z (ptr_to_int addr) idx)
         | DVALUE_Float f =>
             ret (extract_byte_Z (unsigned (Float32.to_bits f)) idx)
         | DVALUE_Double d =>
             ret (extract_byte_Z (unsigned (Float.to_bits d)) idx)
         | DVALUE_Poison dt => raise_poison dt
         | DVALUE_Oom dt => raise_oomable dt
         | DVALUE_None =>
             (* TODO: Not sure if this should be an error, poison, or what. *)
             raise_error "dvalue_extract_byte on DVALUE_None"

         (* TODO: Take padding into account. *)
         | DVALUE_Struct fields =>
             match dt with
             | DTYPE_Struct dts =>
                 (* Step to field which contains the byte we want *)
                 '(fdt, (field_idx, byte_idx)) <- extract_field_byte dts (Z.to_N idx);;
                 match List.nth_error fields (N.to_nat field_idx) with
                 | Some f =>
                     (* call dvalue_extract_byte recursively on the field *)
                     dvalue_extract_byte f fdt (Z.of_N byte_idx )
                 | None =>
                     raise_error "dvalue_extract_byte: more fields in DVALUE_Struct than in dtyp."
                 end
             | _ => raise_error "dvalue_extract_byte: type mismatch on DVALUE_Struct."
             end

         | DVALUE_Packed_struct fields =>
             match dt with
             | DTYPE_Packed_struct dts =>
                 (* Step to field which contains the byte we want *)
                 '(fdt, (field_idx, byte_idx)) <- extract_field_byte dts (Z.to_N idx);;
                 match List.nth_error fields (N.to_nat field_idx) with
                 | Some f =>
                     (* call dvalue_extract_byte recursively on the field *)
                     dvalue_extract_byte f fdt (Z.of_N byte_idx )
                 | None =>
                     raise_error "dvalue_extract_byte: more fields in DVALUE_Packed_struct than in dtyp."
                 end
             | _ => raise_error "dvalue_extract_byte: type mismatch on DVALUE_Packed_struct."
             end

         | DVALUE_Array elts =>
             match dt with
             | DTYPE_Array sz dt =>
                 let elmt_sz  := sizeof_dtyp dt in
                 let elmt_idx := N.div (Z.to_N idx) elmt_sz in
                 let byte_idx := (Z.to_N idx) mod elmt_sz in
                 match List.nth_error elts (N.to_nat elmt_idx) with
                 | Some elmt =>
                     (* call dvalue_extract_byte recursively on the field *)
                     dvalue_extract_byte elmt dt (Z.of_N byte_idx)
                 | None =>
                     raise_error "dvalue_extract_byte: more fields in dvalue than in dtyp."
                 end
             | _ =>
                 raise_error "dvalue_extract_byte: type mismatch on DVALUE_Array."
             end

         | DVALUE_Vector elts =>
             match dt with
             | DTYPE_Vector sz dt =>
                 let elmt_sz  := sizeof_dtyp dt in
                 let elmt_idx := N.div (Z.to_N idx) elmt_sz in
                 let byte_idx := (Z.to_N idx) mod elmt_sz in
                 match List.nth_error elts (N.to_nat elmt_idx) with
                 | Some elmt =>
                     (* call dvalue_extract_byte recursively on the field *)
                     dvalue_extract_byte elmt dt (Z.of_N byte_idx)
                 | None =>
                     raise_error "dvalue_extract_byte: more fields in dvalue than in dtyp."
                 end
             | _ =>
                 raise_error "dvalue_extract_byte: type mismatch on DVALUE_Vector."
             end
         end.

    (* Taking a byte out of a dvalue...

      Unlike UVALUE_ExtractByte, I don't think this needs an sid
      (store id). There should be no nondeterminism in this value. *)
    Inductive dvalue_byte : Type :=
    | DVALUE_ExtractByte (dv : dvalue) (dt : dtyp) (idx : N) : dvalue_byte
    .

    Definition dvalue_byte_value {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_POISON M} `{RAISE_OOMABLE M} (db : dvalue_byte) : M Z
      := match db with
         | DVALUE_ExtractByte dv dt idx =>
             dvalue_extract_byte dv dt (Z.of_N idx)
         end.

    Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia].
    Program Fixpoint dvalue_bytes_to_dvalue {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_POISON M} `{RAISE_OOMABLE M} (dbs : list dvalue_byte) (dt : dtyp) {measure (dtyp_measure dt)} : M dvalue
      := match dt with
         | DTYPE_I sz =>
             zs <- map_monad dvalue_byte_value dbs;;
             match sz with
             | 1 =>
                 ret (DVALUE_I1 (concat_bytes_Z_vint zs))
             | 8 =>
                 ret (DVALUE_I8 (concat_bytes_Z_vint zs))
             | 32 =>
                 ret (DVALUE_I32 (concat_bytes_Z_vint zs))
             | 64 =>
                 ret (DVALUE_I64 (concat_bytes_Z_vint zs))
             | _ => raise_error "Unsupported integer size."
             end
         | DTYPE_IPTR =>
             zs <- map_monad dvalue_byte_value dbs;;
             val <- lift_OOMABLE DTYPE_IPTR (IP.from_Z (concat_bytes_Z zs));;
             ret (DVALUE_IPTR val)
         | DTYPE_Pointer =>
             (* TODO: not sure if this should be wildcard provenance.
                TODO: not sure if this should truncate iptr value...
              *)
             (* TODO: not sure if this should be lazy OOM or not *)
             zs <- map_monad dvalue_byte_value dbs;;
             match int_to_ptr (concat_bytes_Z zs) wildcard_prov with
             | NoOom a => ret (DVALUE_Addr a)
             | Oom msg => raise_oomable DTYPE_Pointer
             end
         | DTYPE_Void =>
             raise_error "dvalue_bytes_to_dvalue on void type."
         | DTYPE_Half =>
             raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_Half."
         | DTYPE_Float =>
             zs <- map_monad dvalue_byte_value dbs;;
             ret (DVALUE_Float (Float32.of_bits (concat_bytes_Z_vint zs)))
         | DTYPE_Double =>
             zs <- map_monad dvalue_byte_value dbs;;
             ret (DVALUE_Double (Float.of_bits (concat_bytes_Z_vint zs)))
         | DTYPE_X86_fp80 =>
             raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_X86_fp80."
         | DTYPE_Fp128 =>
             raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_Fp128."
         | DTYPE_Ppc_fp128 =>
             raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_Ppc_fp128."
         | DTYPE_Metadata =>
             raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_Metadata."
         | DTYPE_X86_mmx =>
             raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_X86_mmx."
         | DTYPE_Array sz t =>
             let sz := sizeof_dtyp t in
             elt_bytes <- lift_err_RAISE_ERROR (split_every sz dbs);;
             elts <- map_monad (fun es => dvalue_bytes_to_dvalue es t) elt_bytes;;
             ret (DVALUE_Array elts)
         | DTYPE_Vector sz t =>
             let sz := sizeof_dtyp t in
             elt_bytes <- lift_err_RAISE_ERROR (split_every sz dbs);;
             elts <- map_monad (fun es => dvalue_bytes_to_dvalue es t) elt_bytes;;
             ret (DVALUE_Vector elts)
         | DTYPE_Struct fields =>
             match fields with
             | [] => ret (DVALUE_Struct []) (* TODO: Not 100% sure about this. *)
             | (dt::dts) =>
                 let sz := sizeof_dtyp dt in
                 let init_bytes := take sz dbs in
                 let rest_bytes := drop sz dbs in
                 f <- dvalue_bytes_to_dvalue init_bytes dt;;
                 rest <- dvalue_bytes_to_dvalue rest_bytes (DTYPE_Struct dts);;
                 match rest with
                 | DVALUE_Struct fs =>
                     ret (DVALUE_Struct (f::fs))
                 | _ =>
                     raise_error "dvalue_bytes_to_dvalue: DTYPE_Struct recursive call did not return a struct."
                 end
             end
         | DTYPE_Packed_struct fields =>
             match fields with
             | [] => ret (DVALUE_Packed_struct []) (* TODO: Not 100% sure about this. *)
             | (dt::dts) =>
                 let sz := sizeof_dtyp dt in
                 let init_bytes := take sz dbs in
                 let rest_bytes := drop sz dbs in
                 f <- dvalue_bytes_to_dvalue init_bytes dt;;
                 rest <- dvalue_bytes_to_dvalue rest_bytes (DTYPE_Struct dts);;
                 match rest with
                 | DVALUE_Packed_struct fs =>
                     ret (DVALUE_Packed_struct (f::fs))
                 | _ =>
                     raise_error "dvalue_bytes_to_dvalue: DTYPE_Packed_struct recursive call did not return a struct."
                 end
             end
         | DTYPE_Opaque =>
             raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_Opaque."
         end.
    Next Obligation.
      pose proof dtyp_measure_gt_0 dt.
      cbn.
      unfold list_sum.
      lia.
    Qed.
    Next Obligation.
      pose proof dtyp_measure_gt_0 dt.
      cbn.
      unfold list_sum.
      lia.
    Qed.

    Definition uvalue_sid_match (a b : uvalue) : bool
      :=
      match a, b with
      | UVALUE_ExtractByte uv dt idx sid, UVALUE_ExtractByte uv' dt' idx' sid' =>
          RelDec.rel_dec uv uv' && N.eqb sid sid'
      | _, _ => false
      end.

    Definition filter_uvalue_sid_matches (byte : uvalue) (uvs : list (N * uvalue)) : (list (N * uvalue) * list (N * uvalue))
      := filter_split (fun '(n, uv) => uvalue_sid_match byte uv) uvs.

    (* TODO: satisfy termination checker *)
    Section Concretize.
      Context (M : Type -> Type).
      Context {HM : Monad M}.
      Variable undef_handler : dtyp -> M dvalue.
      Context (ERR_M : Type -> Type). (* Monad encapsulating errors, ub, oom *)
      Context {HM_ERR : Monad ERR_M}.
      Context {ERR : RAISE_ERROR ERR_M}.
      Context {UB : RAISE_UB ERR_M}.
      Context {OOM : RAISE_OOM ERR_M}.
      Variable lift_ue : forall {A}, ERR_M A -> M A.

      (* TODO: satisfy the termination checker here. *)
      (* M will be err_or_ub / MPropT err_or_ub? *)
      (* Define a sum type f a, g b.... a + b. Mutual recursive
           function as one big function with sum type to select between
           which "function" is being called *)
      Fixpoint concretize_uvalueM (u : uvalue) {struct u} : M dvalue :=
        match u with
        | UVALUE_Addr a                          => ret (DVALUE_Addr a)
        | UVALUE_I1 x                            => ret (DVALUE_I1 x)
        | UVALUE_I8 x                            => ret (DVALUE_I8 x)
        | UVALUE_I32 x                           => ret (DVALUE_I32 x)
        | UVALUE_I64 x                           => ret (DVALUE_I64 x)
        | UVALUE_IPTR x                          => ret (DVALUE_IPTR x)
        | UVALUE_Double x                        => ret (DVALUE_Double x)
        | UVALUE_Float x                         => ret (DVALUE_Float x)
        | UVALUE_Undef t                         => undef_handler t
        | UVALUE_Poison t                        => ret (DVALUE_Poison t)
        | UVALUE_Oom t                           => ret (DVALUE_Oom t)
        | UVALUE_None                            => ret DVALUE_None
        | UVALUE_Struct fields                   => 'dfields <- map_monad concretize_uvalueM fields ;;
                                                    ret (DVALUE_Struct dfields)
        | UVALUE_Packed_struct fields            => 'dfields <- map_monad concretize_uvalueM fields ;;
                                                    ret (DVALUE_Packed_struct dfields)
        | UVALUE_Array elts                      => 'delts <- map_monad concretize_uvalueM elts ;;
                                                    ret (DVALUE_Array delts)
        | UVALUE_Vector elts                     => 'delts <- map_monad concretize_uvalueM elts ;;
                                                    ret (DVALUE_Vector delts)
        | UVALUE_IBinop iop v1 v2                => dv1 <- concretize_uvalueM v1 ;;
                                                    dv2 <- concretize_uvalueM v2 ;;
                                                    lift_ue (eval_iop iop dv1 dv2)
        | UVALUE_ICmp cmp v1 v2                  => dv1 <- concretize_uvalueM v1 ;;
                                                    dv2 <- concretize_uvalueM v2 ;;
                                                    lift_ue (eval_icmp cmp dv1 dv2)
        | UVALUE_FBinop fop fm v1 v2             => dv1 <- concretize_uvalueM v1 ;;
                                                    dv2 <- concretize_uvalueM v2 ;;
                                                    lift_ue (eval_fop fop dv1 dv2)
        | UVALUE_FCmp cmp v1 v2                  => dv1 <- concretize_uvalueM v1 ;;
                                                    dv2 <- concretize_uvalueM v2 ;;
                                                    lift_ue (eval_fcmp cmp dv1 dv2)

        | UVALUE_Conversion conv t_from v t_to    =>
            dv <- concretize_uvalueM v ;;
            match get_conv_case conv t_from dv t_to with
            | Conv_PtoI x =>
                match x, t_to with
                | DVALUE_Addr addr, DTYPE_I sz =>
                    lift_ue (coerce_integer_to_int (Some sz) (ptr_to_int addr))
                | DVALUE_Addr addr, DTYPE_IPTR =>
                    lift_ue (coerce_integer_to_int None (ptr_to_int addr))
                | _, _ =>
                    lift_ue (raise_error "Invalid PTOI conversion")
                end
            | Conv_ItoP x =>
                match int_to_ptr (dvalue_int_unsigned x) wildcard_prov with
                | NoOom a =>
                    ret (DVALUE_Addr a)
                | Oom msg =>
                    lift_ue (raise_oom ("concretize_uvalueM OOM in Conv_ItoP: " ++ msg))
                end
            | Conv_Pure x => ret x
            | Conv_Illegal s => lift_ue (raise_error s)
            end

        | UVALUE_GetElementPtr t ua uvs =>
            da <- concretize_uvalueM ua;;
            dvs <- map_monad concretize_uvalueM uvs;;
            match handle_gep t da dvs with
            | inl err => lift_ue (raise_error err)
            | inr (Oom msg) => lift_ue (raise_oom ("concretize_uvalueM OOM in GetElementPtr: " ++ msg))
            | inr (NoOom dv) => ret dv
            end
        | UVALUE_ExtractValue t uv idxs =>
            str <- concretize_uvalueM uv;;
            let fix loop str idxs : ERR_M dvalue :=
              match idxs with
              | [] => ret str
              | i :: tl =>
                  v <- index_into_str_dv str i ;;
                  loop v tl
              end in
            lift_ue (loop str idxs)

        | UVALUE_Select cond v1 v2 =>
            dcond <- concretize_uvalueM cond;;
            eval_select dcond v1 v2

        | UVALUE_ConcatBytes bytes dt =>
            match N.eqb (N.of_nat (length bytes)) (sizeof_dtyp dt), all_extract_bytes_from_uvalue dt bytes with
            | true, Some uv => concretize_uvalueM uv
            | _, _ => extractbytes_to_dvalue bytes dt
            end

        | UVALUE_ExtractByte byte dt idx sid =>
            (* TODO: maybe this is just an error? ExtractByte should be guarded by ConcatBytes? *)
            lift_ue (raise_error "Attempting to concretize UVALUE_ExtractByte, should not happen.")
        | UVALUE_InsertValue t uv elt idxs =>
            str <- concretize_uvalueM uv;;
            elt <- concretize_uvalueM elt;;
            let fix loop str idxs : ERR_M dvalue :=
              match idxs with
              | [] => raise_error "Index was not provided"
              | i :: nil =>
                  v <- insert_into_str str elt i;;
                  ret v
              | i :: tl =>
                      subfield <- index_into_str_dv str i;;
                      modified_subfield <- loop subfield tl;;
                      insert_into_str str modified_subfield i
              end in
            lift_ue (loop str idxs)
        | UVALUE_ExtractElement vec_typ vec idx =>
            dvec <- concretize_uvalueM vec;;
            didx <- concretize_uvalueM idx;;
            elt_typ <- match vec_typ with
                       | DTYPE_Vector _ t => ret t
                       | _ => lift_ue (raise_error "Invalid vector type for ExtractElement")
                       end;;
            lift_ue (index_into_vec_dv elt_typ dvec didx)
        | UVALUE_InsertElement vec_typ vec elt idx =>
            dvec <- concretize_uvalueM vec;;
            didx <- concretize_uvalueM idx;;
            delt <- concretize_uvalueM elt;;
            lift_ue (insert_into_vec_dv vec_typ dvec delt didx)
        | _ => lift_ue (raise_error ("concretize_uvalueM: Attempting to convert a partially non-reduced uvalue to dvalue. Should not happen: " ++ uvalue_constructor_string u))

        end

      with

      (* Take a UVALUE_ExtractByte, and replace the uvalue with a given dvalue...

         Note: this also concretizes the index.
       *)
      uvalue_byte_replace_with_dvalue_byte (uv : uvalue) (dv : dvalue) {struct uv} : M dvalue_byte
      := match uv with
         | UVALUE_ExtractByte uv dt idx sid =>
             cidx <- concretize_uvalueM idx;;
             ret (DVALUE_ExtractByte dv dt (Z.to_N (dvalue_int_unsigned cidx)))
         | _ => lift_ue (raise_error "uvalue_byte_replace_with_dvalue_byte called with non-UVALUE_ExtractByte value.")
         end

      with
      (* Concretize the uvalues in a list of UVALUE_ExtractBytes...

       *)
      (* Pick out uvalue bytes that are the same + have same sid

         Concretize these identical uvalues...
       *)

      concretize_uvalue_bytes_helper (uvs : list (N * uvalue)) (acc : NMap dvalue_byte) {struct uvs} : M (NMap dvalue_byte)
      := match uvs with
         | [] => ret acc
         | ((n, uv)::uvs) =>
             match uv with
             | UVALUE_ExtractByte byte_uv dt idx sid =>
                 let '(ins, outs) := filter_uvalue_sid_matches uv uvs in
                 (* Concretize first uvalue *)
                 dv <- concretize_uvalueM byte_uv;;
                 cidx <- concretize_uvalueM idx;;
                 let dv_byte := DVALUE_ExtractByte dv dt (Z.to_N (dvalue_int_unsigned cidx)) in
                 let acc := @NM.add _ n dv_byte acc in
                 (* Concretize entangled bytes *)
                 acc <- monad_fold_right (fun acc '(n, uv) =>
                                            dvb <- uvalue_byte_replace_with_dvalue_byte uv dv;;
                                            ret (@NM.add _ n dvb acc)) ins acc;;
                 (* Concretize the rest of the bytes *)
                 concretize_uvalue_bytes_helper outs acc
             | _ => lift_ue (raise_error "concretize_uvalue_bytes_helper: non-byte in uvs.")
             end
         end

      with
      concretize_uvalue_bytes (uvs : list uvalue) {struct uvs} : M (list dvalue_byte)
      :=
        let len := length uvs in
        byte_map <- concretize_uvalue_bytes_helper (zip (Nseq 0 len) uvs) (@NM.empty _);;
        match NM_find_many (Nseq 0 len) byte_map with
        | Some dvbs => ret dvbs
        | None => lift_ue (raise_error "concretize_uvalue_bytes: missing indices.")
        end

      with
      extractbytes_to_dvalue (uvs : list uvalue) (dt : dtyp) {struct uvs} : M dvalue
      := dvbs <- concretize_uvalue_bytes uvs;;
         lift_ue (ErrOOMPoison_handle_poison_and_oom_dv (dvalue_bytes_to_dvalue dvbs dt))

      with
      eval_select
      (cnd : dvalue) (v1 v2 : uvalue) {struct cnd} (* Lie for the termination checker *) : M dvalue
      := match cnd with
         | DVALUE_Poison t =>
             (* TODO: Should be the type of the result of the select... *)
             ret (DVALUE_Poison t)
         | DVALUE_I1 i =>
             if (Int1.unsigned i =? 1)%Z
             then concretize_uvalueM v1
             else concretize_uvalueM v2
         | DVALUE_Vector conds =>
             let fix loop conds xs ys : M (list dvalue) :=
               match conds, xs, ys with
               | [], [], [] => ret []
               | (c::conds), (x::xs), (y::ys) =>
                   selected <- match c with
                              | DVALUE_Poison t =>
                                  (* TODO: Should be the type of the result of the select... *)
                                  ret (DVALUE_Poison t)
                              | DVALUE_I1 i =>
                                  if (Int1.unsigned i =? 1)%Z
                                  then ret x
                                  else ret y
                              | _ =>
                                  lift_ue
                                    (raise_error "concretize_uvalueM: ill-typed select, condition in vector was not poison or i1.")
                              end;;
                   rest <- loop conds xs ys;;
                   ret (selected :: rest)
               | _, _, _ =>
                   lift_ue (raise_error "concretize_uvalueM: ill-typed vector select, length mismatch.")
               end in
             (* TODO: lazily concretize these vectors to avoid
                   evaluating elements that aren't chosen? *)
             dv1 <- concretize_uvalueM v1;;
             dv2 <- concretize_uvalueM v2;;
             match dv1, dv2 with
             | DVALUE_Poison t, _ =>
                 (* TODO: Should we make sure t is a vector type...? *)
                 ret (DVALUE_Poison t)
             | DVALUE_Vector _, DVALUE_Poison t =>
                 (* TODO: Should we make sure t is a vector type...? *)
                 ret (DVALUE_Poison t)
             | DVALUE_Vector xs, DVALUE_Vector ys =>
                 selected <- loop conds xs ys;;
                 ret (DVALUE_Vector selected)
             | _, _ =>
                 lift_ue (raise_error "concretize_uvalueM: ill-typed vector select, non-vector arguments")
             end
         | _ => lift_ue (raise_error "concretize_uvalueM: ill-typed select.")
         end.


      Lemma concretize_uvalueM_equation :
        forall u,
          concretize_uvalueM u =
            match u with
            | UVALUE_Addr a                          => ret (DVALUE_Addr a)
            | UVALUE_I1 x                            => ret (DVALUE_I1 x)
            | UVALUE_I8 x                            => ret (DVALUE_I8 x)
            | UVALUE_I32 x                           => ret (DVALUE_I32 x)
            | UVALUE_I64 x                           => ret (DVALUE_I64 x)
            | UVALUE_IPTR x                          => ret (DVALUE_IPTR x)
            | UVALUE_Double x                        => ret (DVALUE_Double x)
            | UVALUE_Float x                         => ret (DVALUE_Float x)
            | UVALUE_Undef t                         => undef_handler t
            | UVALUE_Poison t                        => ret (DVALUE_Poison t)
            | UVALUE_Oom t                           => ret (DVALUE_Oom t)
            | UVALUE_None                            => ret DVALUE_None
            | UVALUE_Struct fields                   => 'dfields <- map_monad concretize_uvalueM fields ;;
                                                        ret (DVALUE_Struct dfields)
            | UVALUE_Packed_struct fields            => 'dfields <- map_monad concretize_uvalueM fields ;;
                                                        ret (DVALUE_Packed_struct dfields)
            | UVALUE_Array elts                      => 'delts <- map_monad concretize_uvalueM elts ;;
                                                        ret (DVALUE_Array delts)
            | UVALUE_Vector elts                     => 'delts <- map_monad concretize_uvalueM elts ;;
                                                        ret (DVALUE_Vector delts)
            | UVALUE_IBinop iop v1 v2                => dv1 <- concretize_uvalueM v1 ;;
                                                        dv2 <- concretize_uvalueM v2 ;;
                                                        lift_ue (eval_iop iop dv1 dv2)
            | UVALUE_ICmp cmp v1 v2                  => dv1 <- concretize_uvalueM v1 ;;
                                                        dv2 <- concretize_uvalueM v2 ;;
                                                        lift_ue (eval_icmp cmp dv1 dv2)
            | UVALUE_FBinop fop fm v1 v2             => dv1 <- concretize_uvalueM v1 ;;
                                                        dv2 <- concretize_uvalueM v2 ;;
                                                        lift_ue (eval_fop fop dv1 dv2)
            | UVALUE_FCmp cmp v1 v2                  => dv1 <- concretize_uvalueM v1 ;;
                                                        dv2 <- concretize_uvalueM v2 ;;
                                                        lift_ue (eval_fcmp cmp dv1 dv2)

            | UVALUE_Conversion conv t_from v t_to    =>
                dv <- concretize_uvalueM v ;;
                match get_conv_case conv t_from dv t_to with
                | Conv_PtoI x =>
                    match x, t_to with
                    | DVALUE_Addr addr, DTYPE_I sz =>
                        lift_ue (coerce_integer_to_int (Some sz) (ptr_to_int addr))
                    | DVALUE_Addr addr, DTYPE_IPTR =>
                        lift_ue (coerce_integer_to_int None (ptr_to_int addr))
                    | _, _ =>
                        lift_ue (raise_error "Invalid PTOI conversion")
                    end
                | Conv_ItoP x =>
                    match int_to_ptr (dvalue_int_unsigned x) wildcard_prov with
                    | NoOom a =>
                        ret (DVALUE_Addr a)
                    | Oom msg =>
                        lift_ue (raise_oom ("concretize_uvalueM OOM in Conv_ItoP: " ++ msg))
                    end
                | Conv_Pure x => ret x
                | Conv_Illegal s => lift_ue (raise_error s)
                end

            | UVALUE_GetElementPtr t ua uvs =>
                da <- concretize_uvalueM ua;;
                dvs <- map_monad concretize_uvalueM uvs;;
                match handle_gep t da dvs with
                | inl err => lift_ue (raise_error err)
                | inr (Oom msg) => lift_ue (raise_oom ("concretize_uvalueM OOM in GetElementPtr: " ++ msg))
                | inr (NoOom dv) => ret dv
                end

            | UVALUE_ExtractValue t uv idxs =>
                str <- concretize_uvalueM uv;;
                let fix loop str idxs : ERR_M dvalue :=
                  match idxs with
                  | [] => ret str
                  | i :: tl =>
                      v <- index_into_str_dv str i ;;
                      loop v tl
                  end in
                lift_ue (loop str idxs)

            | UVALUE_Select cond v1 v2 =>
                dcond <- concretize_uvalueM cond;;
                eval_select dcond v1 v2

            | UVALUE_ConcatBytes bytes dt =>
                match N.eqb (N.of_nat (length bytes)) (sizeof_dtyp dt), all_extract_bytes_from_uvalue dt bytes with
                | true, Some uv => concretize_uvalueM uv
                | _, _ => extractbytes_to_dvalue bytes dt
                end

            | UVALUE_ExtractByte byte dt idx sid =>
                (* TODO: maybe this is just an error? ExtractByte should be guarded by ConcatBytes? *)
                lift_ue (raise_error "Attempting to concretize UVALUE_ExtractByte, should not happen.")
            | UVALUE_InsertValue t uv elt idxs =>
                str <- concretize_uvalueM uv;;
                elt <- concretize_uvalueM elt;;
                let fix loop str idxs : ERR_M dvalue :=
                  match idxs with
                  | [] => raise_error "Index was not provided"
                  | i :: nil =>
                      v <- insert_into_str str elt i;;
                      ret v
                  | i :: tl =>
                      subfield <- index_into_str_dv str i;;
                      modified_subfield <- loop subfield tl;;
                      insert_into_str str modified_subfield i
                  end in
                lift_ue (loop str idxs)
            | UVALUE_ExtractElement vec_typ vec idx =>
                dvec <- concretize_uvalueM vec;;
                didx <- concretize_uvalueM idx;;
                elt_typ <- match vec_typ with
                           | DTYPE_Vector _ t => ret t
                           | _ => lift_ue (raise_error "Invalid vector type for ExtractElement")
                           end;;
                lift_ue (index_into_vec_dv elt_typ dvec didx)
            | UVALUE_InsertElement vec_typ vec elt idx =>
                dvec <- concretize_uvalueM vec;;
                didx <- concretize_uvalueM idx;;
                delt <- concretize_uvalueM elt;;
                lift_ue (insert_into_vec_dv vec_typ dvec delt didx)
            | _ => lift_ue (raise_error ("concretize_uvalueM: Attempting to convert a partially non-reduced uvalue to dvalue. Should not happen: " ++ uvalue_constructor_string u))

            end.
      Proof.
        intros u.
        unfold concretize_uvalueM at 1.
        destruct u; try reflexivity.
      Qed.

    End Concretize.

    Arguments concretize_uvalueM {_ _}.

  End Concretize.

  Set Guard Checking.
End MakeBase.

Module Make (LP : LLVMParams) (MP : MemoryParams LP) (Byte : ByteModule LP.ADDR LP.IP LP.SIZEOF LP.Events MP.BYTE_IMPL) (SER : ConcretizationBase LP MP Byte) : Concretization LP MP Byte SER.
  Include Concretization LP MP Byte SER.
End Make.
