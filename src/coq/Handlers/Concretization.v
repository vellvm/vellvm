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
  Utils.Oomable
  Utils.Poisonable
  Utils.ErrOomPoison
  Syntax.LLVMAst
  Syntax.DynamicTypes
  Syntax.DataLayout
  Semantics.VellvmIntegers
  Semantics.DynamicValues
  Semantics.MemoryParams
  Semantics.LLVMEvents
  Semantics.LLVMParams.

From Mem Require Import
  Addresses.MemoryAddress
  Semantics.Memory.StoreId
  MemoryModel.

From LLVM_Memory Require Import
  Sizeof
  Intptr
  GepM
  MemBytes.

From ExtLib Require Import
  Structures.Monads
  Data.Monads.EitherMonad
  StateMonad.

Require Import Lia.

Import IdentityMonad.

Import ListNotations.
Import MonadNotation.

(* TODO: Move this *)
#[global] Instance MonadStoreId_stateT {M} `{HM: Monad M} : MemPropT.MonadStoreId (stateT store_id M).
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
  Import DVALUE_BYTES.

  Module MemHelpers := MemoryHelpers LP MP Byte.
  Import MemHelpers.

  Definition eval_icmp {M} `{Monad M} `{RAISE_ERROR M} icmp v1 v2 : M dvalue :=
    match v1, v2 with
    | DVALUE_I1 i1, DVALUE_I1 i2
    | DVALUE_I8 i1, DVALUE_I8 i2
    | DVALUE_I16 i1, DVALUE_I16 i2
    | DVALUE_I32 i1, DVALUE_I32 i2
    | DVALUE_I64 i1, DVALUE_I64 i2
    | DVALUE_IPTR i1, DVALUE_IPTR i2 => eval_int_icmp icmp i1 i2
    | DVALUE_Poison t1, DVALUE_Poison t2 => ret (DVALUE_Poison t1)
    | DVALUE_Poison t, _ => if is_DVALUE_IX v2 then ret (DVALUE_Poison t) else raise_error "ill_typed-iop"
    | _, DVALUE_Poison t => if is_DVALUE_IX v1 then ret (DVALUE_Poison t) else raise_error "ill_typed-iop"
    | DVALUE_Addr a1, DVALUE_Addr a2 =>
        let i1 := ptr_to_int a1 in
        let i2 := ptr_to_int a2 in
        eval_int_icmp icmp i1 i2
    | _, _ => raise_error ("ill_typed-icmp: " ++ show_dvalue v1 ++ ", " ++ show_dvalue v2)
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
          | DTYPE_I 16, DVALUE_I16 i1, DTYPE_I 1
          | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 1
          | DTYPE_I 64, DVALUE_I64 i1, DTYPE_I 1 =>
              Conv_Pure (DVALUE_I1 (repr (unsigned i1)))

          | DTYPE_I 16, DVALUE_I16 i1, DTYPE_I 8
          | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 8
          | DTYPE_I 64, DVALUE_I64 i1, DTYPE_I 8 =>
              Conv_Pure (DVALUE_I8 (repr (unsigned i1)))

          | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 16
          | DTYPE_I 64, DVALUE_I64 i1, DTYPE_I 16 =>
              Conv_Pure (DVALUE_I16 (repr (unsigned i1)))

          | DTYPE_I 64, DVALUE_I64 i1, DTYPE_I 32 =>
              Conv_Pure (DVALUE_I32 (repr (unsigned i1)))

          | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 1
          | DTYPE_I 16, DVALUE_Poison t, DTYPE_I 1
          | DTYPE_I 16, DVALUE_Poison t, DTYPE_I 8
          | DTYPE_I 32, DVALUE_Poison t, DTYPE_I 1
          | DTYPE_I 32, DVALUE_Poison t, DTYPE_I 8
          | DTYPE_I 32, DVALUE_Poison t, DTYPE_I 16
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

          | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 16
          | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 16 =>
              Conv_Pure (DVALUE_I16 (repr (unsigned i1)))

          | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 32
          | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 32
          | DTYPE_I 16, DVALUE_I16 i1, DTYPE_I 32 =>
              Conv_Pure (DVALUE_I32 (repr (unsigned i1)))

          | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 64
          | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 64
          | DTYPE_I 16, DVALUE_I16 i1, DTYPE_I 64
          | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 64 =>
              Conv_Pure (DVALUE_I64 (repr (unsigned i1)))

          | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 8
          | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 16
          | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 32
          | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 64
          | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 16
          | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 32
          | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 64
          | DTYPE_I 16, DVALUE_Poison t, DTYPE_I 32
          | DTYPE_I 16, DVALUE_Poison t, DTYPE_I 64
          | DTYPE_I 32, DVALUE_Poison t, DTYPE_I 64 =>
              Conv_Pure (DVALUE_Poison t)

          | _, _, _ => Conv_Illegal "ill-typed conv"
          end

      | Sext =>
          match t1, x, t2 with
          | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 8 =>
              Conv_Pure (DVALUE_I8 (repr (signed i1)))

          | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 16
          | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 16 =>
              Conv_Pure (DVALUE_I16 (repr (signed i1)))

          | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 32
          | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 32
          | DTYPE_I 16, DVALUE_I16 i1, DTYPE_I 32 =>
              Conv_Pure (DVALUE_I32 (repr (signed i1)))

          | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 64
          | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 64
          | DTYPE_I 16, DVALUE_I16 i1, DTYPE_I 64
          | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 64 =>
              Conv_Pure (DVALUE_I64 (repr (signed i1)))

          | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 8
          | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 16
          | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 32
          | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 64
          | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 16
          | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 32
          | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 64
          | DTYPE_I 16, DVALUE_Poison t, DTYPE_I 32
          | DTYPE_I 16, DVALUE_Poison t, DTYPE_I 64
          | DTYPE_I 32, DVALUE_Poison t, DTYPE_I 64 =>
              Conv_Pure (DVALUE_Poison t)

          | _, _, _ => Conv_Illegal "ill-typed conv"
          end

      | Bitcast =>
          if dtyp_eqb t1 t2
          then Conv_Pure x
          else if bit_sizeof_dtyp t1 =? bit_sizeof_dtyp t2
               then
                 let bytes := dvalue_to_dvalue_bytes x t1 in
                 let dv_conv := ErrOOMPoison_handle_poison_and_oom DVALUE_Poison (@dvalue_bytes_to_dvalue ErrOOMPoison _ _ _ _ bytes t2) in
                 match unIdent (unEitherT (unEitherT (unEitherT (unERR_UB_OOM dv_conv)))) with
                 | inl (OOM_message oom) =>
                     Conv_Oom ("Bitcast OOM: " ++ oom)
                 | inr (inl (UB_message ub)) =>
                     Conv_Illegal ("Bitcast UB: " ++ ub)
                 | inr (inr (inl (ERR_message err))) =>
                     Conv_Illegal ("Bitcast Error: " ++ err)
                 | inr (inr (inr dv)) =>
                     Conv_Pure dv
                 end
               else Conv_Illegal "unequal bitsize in cast"

      | Uitofp =>
          match t1, x, t2 with
          | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Float
          | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Float
          | DTYPE_I 16, DVALUE_I16 i1, DTYPE_Float
          | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Float
          | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Float =>
              Conv_Pure (DVALUE_Float (Float32.of_intu (repr (unsigned i1))))

          | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Double
          | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Double
          | DTYPE_I 16, DVALUE_I16 i1, DTYPE_Double
          | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Double
          | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Double =>
              Conv_Pure (DVALUE_Double (Float.of_longu (repr (unsigned i1))))

          | DTYPE_I 1, DVALUE_Poison t, DTYPE_Float
          | DTYPE_I 8, DVALUE_Poison t, DTYPE_Float
          | DTYPE_I 16, DVALUE_Poison t, DTYPE_Float
          | DTYPE_I 32, DVALUE_Poison t, DTYPE_Float
          | DTYPE_I 64, DVALUE_Poison t, DTYPE_Float
          | DTYPE_I 1, DVALUE_Poison t, DTYPE_Double
          | DTYPE_I 8, DVALUE_Poison t, DTYPE_Double
          | DTYPE_I 16, DVALUE_Poison t, DTYPE_Double
          | DTYPE_I 32, DVALUE_Poison t, DTYPE_Double
          | DTYPE_I 64, DVALUE_Poison t, DTYPE_Double =>
              Conv_Pure (DVALUE_Poison t)

          | _, _, _ => Conv_Illegal "ill-typed Uitofp"
          end

      | Sitofp =>
          match t1, x, t2 with
          | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Float
          | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Float
          | DTYPE_I 16, DVALUE_I16 i1, DTYPE_Float
          | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Float
          | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Float =>
              Conv_Pure (DVALUE_Float (Float32.of_intu (repr (signed i1))))

          | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Double
          | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Double
          | DTYPE_I 16, DVALUE_I16 i1, DTYPE_Double
          | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Double
          | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Double =>
              Conv_Pure (DVALUE_Double (Float.of_longu (repr (signed i1))))

          | DTYPE_I 1, DVALUE_Poison t, DTYPE_Float
          | DTYPE_I 8, DVALUE_Poison t, DTYPE_Float
          | DTYPE_I 16, DVALUE_Poison t, DTYPE_Float
          | DTYPE_I 32, DVALUE_Poison t, DTYPE_Float
          | DTYPE_I 64, DVALUE_Poison t, DTYPE_Float
          | DTYPE_I 1, DVALUE_Poison t, DTYPE_Double
          | DTYPE_I 8, DVALUE_Poison t, DTYPE_Double
          | DTYPE_I 16, DVALUE_Poison t, DTYPE_Double
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

  Parameter eval_select :
    forall (M : Type -> Type) `{Monad M} (handler : dtyp -> M dvalue)
           (ERR_M : Type -> Type) `{Monad ERR_M} `{RAISE_ERROR ERR_M} `{RAISE_UB ERR_M} `{RAISE_OOM ERR_M}
           (lift_ue : forall A : Type, ERR_M A -> M A)
           (cnd : dvalue) (v1 v2 : uvalue), M dvalue.

  Definition pre_concretized (acc : NMap (list (uvalue * dvalue))) (uv : uvalue) (sid : store_id) : option dvalue
    := vs <- NM.find sid acc;;
       assoc uv vs.

  Definition new_concretized_byte
    (acc : NMap (list (uvalue * dvalue))) (uv : uvalue) (dv : dvalue) (sid : store_id) : NMap (list (uvalue * dvalue))
    := match NM.find sid acc with
       | Some vs =>
           match assoc uv vs with
           | Some _ =>
               acc
           | None =>
               NM.add sid (vs ++ [(uv, dv)]) acc
           end
       | None =>
           NM.add sid [(uv, dv)] acc
       end.
  (* Equations *)
  Parameter concretize_uvalueM_equation :
    forall (M : Type -> Type) {HM : Monad M} (undef_handler : dtyp -> M dvalue)
           (ERR_M : Type -> Type) {HM_ERR : Monad ERR_M} {ERR : RAISE_ERROR ERR_M} {UB : RAISE_UB ERR_M}
           {OOM : RAISE_OOM ERR_M} (lift_ue : forall A : Type, ERR_M A -> M A) (u : uvalue),
      concretize_uvalueM M undef_handler ERR_M lift_ue u =
        let
          eval_select
            (cnd : dvalue) (v1 v2 : uvalue) : M dvalue
          := match cnd with
             | DVALUE_Poison t =>
                 (* TODO: Should be the type of the result of the select... *)
                 ret (DVALUE_Poison t)
             | DVALUE_I1 i =>
                 if (Int1.unsigned i =? 1)%Z
                 then concretize_uvalueM M undef_handler ERR_M lift_ue v1
                 else concretize_uvalueM M undef_handler ERR_M lift_ue v2
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
                                       lift_ue _
                                         (raise_error "concretize_uvalueM: ill-typed select, condition in vector was not poison or i1.")
                                   end;;
                       rest <- loop conds xs ys;;
                       ret (selected :: rest)
                   | _, _, _ =>
                       lift_ue _ (raise_error "concretize_uvalueM: ill-typed vector select, length mismatch.")
                   end in
                 (* TODO: lazily concretize these vectors to avoid
                   evaluating elements that aren't chosen? *)
                 dv1 <- concretize_uvalueM M undef_handler ERR_M lift_ue v1;;
                 dv2 <- concretize_uvalueM M undef_handler ERR_M lift_ue v2;;
                 match dv1, dv2 with
                 | DVALUE_Poison t, _ =>
                     (* TODO: Should we make sure t is a vector type...? *)
                     @ret M _ _ (DVALUE_Poison t)
                 | DVALUE_Vector _, DVALUE_Poison t =>
                     (* TODO: Should we make sure t is a vector type...? *)
                     @ret M _ _ (DVALUE_Poison t)
                 | DVALUE_Vector xs, DVALUE_Vector ys =>
                     selected <- loop conds xs ys;;
                     @ret M _ _ (DVALUE_Vector selected)
                 | _, _ =>
                     lift_ue _ (raise_error "concretize_uvalueM: ill-typed vector select, non-vector arguments")
                 end
             | _ => lift_ue _ (raise_error "concretize_uvalueM: ill-typed select.")
             end
        in
        (* Concretize the uvalues in a list of UVALUE_ExtractBytes...

         *)
        (* Pick out uvalue bytes that are the same + have same sid

         Concretize these identical uvalues...
         *)
        let fix concretize_uvalue_bytes_helper (acc : NMap (list (uvalue * dvalue))) (uvs : list uvalue) {struct uvs} : M (list dvalue_byte)
          := match uvs with
             | [] => ret []
             | (uv::uvs) =>
                 match uv with
                 | UVALUE_ExtractByte byte_uv dt idx sid =>
                     (* Check if this uvalue has been concretized already *)
                     match pre_concretized acc byte_uv sid with
                     | Some dv =>
                         (* Use the pre_concretized value *)
                         let dv_byte := DVALUE_ExtractByte dv dt idx in
                         (* Concretize the rest of the bytes *)
                         rest <- concretize_uvalue_bytes_helper acc uvs;;
                         ret (dv_byte :: rest)
                     | None =>
                         (* Concretize the uvalue *)
                         dv <- concretize_uvalueM M undef_handler ERR_M lift_ue byte_uv;;
                         let dv_byte := DVALUE_ExtractByte dv dt idx in
                         let acc := new_concretized_byte acc byte_uv dv sid in
                         (* Concretize the rest of the bytes *)
                         rest <- concretize_uvalue_bytes_helper acc uvs;;
                         ret (dv_byte :: rest)
                     end
                 | _ =>
                     lift_ue _ (raise_error "concretize_uvalue_bytes_helper: non-byte in uvs.")
                 end
             end in

        let concretize_uvalue_bytes (uvs : list uvalue) : M (list dvalue_byte)
          := concretize_uvalue_bytes_helper (@NM.empty _) uvs in

        let extractbytes_to_dvalue (uvs : list uvalue) (dt : dtyp) : M dvalue
          := dvbs <- concretize_uvalue_bytes uvs;;
             lift_ue _ (ErrOOMPoison_handle_poison_and_oom DVALUE_Poison (dvalue_bytes_to_dvalue dvbs dt))
        in
        match u with
        | UVALUE_Addr a                          => ret (DVALUE_Addr a)
        | UVALUE_I1 x                            => ret (DVALUE_I1 x)
        | UVALUE_I8 x                            => ret (DVALUE_I8 x)
        | UVALUE_I16 x                           => ret (DVALUE_I16 x)
        | UVALUE_I32 x                           => ret (DVALUE_I32 x)
        | UVALUE_I64 x                           => ret (DVALUE_I64 x)
        | UVALUE_IPTR x                          => ret (DVALUE_IPTR x)
        | UVALUE_Double x                        => ret (DVALUE_Double x)
        | UVALUE_Float x                         => ret (DVALUE_Float x)
        | UVALUE_Undef t                         => undef_handler t
        | UVALUE_Poison t                        => ret (DVALUE_Poison t)
        | UVALUE_Oom t                           => ret (DVALUE_Oom t)
        | UVALUE_None                            => ret DVALUE_None
        | UVALUE_Struct fields                   => 'dfields <- map_monad (concretize_uvalueM M undef_handler ERR_M lift_ue) fields ;;
                                                    ret (DVALUE_Struct dfields)
        | UVALUE_Packed_struct fields            => 'dfields <- map_monad (concretize_uvalueM M undef_handler ERR_M lift_ue) fields ;;
                                                    ret (DVALUE_Packed_struct dfields)
        | UVALUE_Array elts                      => 'delts <- map_monad (concretize_uvalueM M undef_handler ERR_M lift_ue) elts ;;
                                                    ret (DVALUE_Array delts)
        | UVALUE_Vector elts                     => 'delts <- map_monad (concretize_uvalueM M undef_handler ERR_M lift_ue) elts ;;
                                                    ret (DVALUE_Vector delts)
        | UVALUE_IBinop iop v1 v2                => dv1 <- concretize_uvalueM M undef_handler ERR_M lift_ue v1 ;;
                                                    dv2 <- concretize_uvalueM M undef_handler ERR_M lift_ue v2 ;;
                                                    lift_ue _ (eval_iop iop dv1 dv2)
        | UVALUE_ICmp cmp v1 v2                  => dv1 <- concretize_uvalueM M undef_handler ERR_M lift_ue v1 ;;
                                                    dv2 <- concretize_uvalueM M undef_handler ERR_M lift_ue v2 ;;
                                                    lift_ue _ (eval_icmp cmp dv1 dv2)
        | UVALUE_FBinop fop fm v1 v2             => dv1 <- concretize_uvalueM M undef_handler ERR_M lift_ue v1 ;;
                                                    dv2 <- concretize_uvalueM M undef_handler ERR_M lift_ue v2 ;;
                                                    lift_ue _ (eval_fop fop dv1 dv2)
        | UVALUE_FCmp cmp v1 v2                  => dv1 <- concretize_uvalueM M undef_handler ERR_M lift_ue v1 ;;
                                                    dv2 <- concretize_uvalueM M undef_handler ERR_M lift_ue v2 ;;
                                                    lift_ue _ (eval_fcmp cmp dv1 dv2)

        | UVALUE_Conversion conv t_from v t_to    =>
            dv <- concretize_uvalueM M undef_handler ERR_M lift_ue v ;;
            match get_conv_case conv t_from dv t_to with
            | Conv_PtoI x =>
                match x, t_to with
                | DVALUE_Addr addr, DTYPE_I sz =>
                    lift_ue _ (coerce_integer_to_int (Some sz) (ptr_to_int addr))
                | DVALUE_Addr addr, DTYPE_IPTR =>
                    lift_ue _ (coerce_integer_to_int None (ptr_to_int addr))
                | _, _ =>
                    lift_ue _ (raise_error "Invalid PTOI conversion")
                end
            | Conv_ItoP x =>
                match int_to_ptr (dvalue_int_unsigned x) wildcard_prov with
                | NoOom a =>
                    ret (DVALUE_Addr a)
                | Oom msg =>
                    lift_ue _ (raise_oom ("concretize_uvalueM OOM in Conv_ItoP: " ++ msg))
                end
            | Conv_Pure x => ret x
            | Conv_Oom s => lift_ue _ (raise_oom s)
            | Conv_Illegal s => lift_ue _ (raise_error s)
            end

        | UVALUE_GetElementPtr t ua uvs =>
            da <- concretize_uvalueM M undef_handler ERR_M lift_ue ua;;
            dvs <- map_monad (concretize_uvalueM M undef_handler ERR_M lift_ue) uvs;;
            match handle_gep t da dvs with
            | inl err => lift_ue _ (raise_error err)
            | inr (Oom msg) => lift_ue _ (raise_oom ("concretize_uvalueM OOM in GetElementPtr: " ++ msg))
            | inr (NoOom dv) => ret dv
            end
        | UVALUE_ExtractValue t uv idxs =>
            str <- concretize_uvalueM M undef_handler ERR_M lift_ue uv;;
            let fix loop str idxs : ERR_M dvalue :=
              match idxs with
              | [] => ret str
              | i :: tl =>
                  v <- index_into_str_dv str i ;;
                  loop v tl
              end in
            lift_ue _ (loop str idxs)

        | UVALUE_Select cond v1 v2 =>
            dcond <- concretize_uvalueM M undef_handler ERR_M lift_ue cond;;
            eval_select dcond v1 v2

        | UVALUE_ConcatBytes bytes dt =>
            match N.eqb (N.of_nat (length bytes)) (sizeof_dtyp dt), Byte.all_extract_bytes_from_uvalue dt bytes with
            | true, Some uv =>
                match bytes with
                | (UVALUE_ExtractByte uv _ _ _ :: _) => concretize_uvalueM M undef_handler ERR_M lift_ue uv
                | _ => lift_ue _ (raise_error "ConcatBytes case... Should not happen.")
                end
            | _, _ => extractbytes_to_dvalue bytes dt
            end

        | UVALUE_ExtractByte byte dt idx sid =>
            (* TODO: maybe this is just an error? ExtractByte should be guarded by ConcatBytes? *)
            lift_ue _ (raise_error "Attempting to concretize UVALUE_ExtractByte, should not happen.")
        | UVALUE_InsertValue t uv et elt idxs =>
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
            lift_ue _ (loop str idxs)
        | UVALUE_ExtractElement vec_typ vec idx =>
            dvec <- concretize_uvalueM M undef_handler ERR_M lift_ue vec;;
            didx <- concretize_uvalueM M undef_handler ERR_M lift_ue idx;;
            elt_typ <- match vec_typ with
                       | DTYPE_Vector _ t => ret t
                       | _ => lift_ue _ (raise_error "Invalid vector type for ExtractElement")
                       end;;
            lift_ue _ (index_into_vec_dv elt_typ dvec didx)
        | UVALUE_InsertElement vec_typ vec elt idx =>
            dvec <- concretize_uvalueM M undef_handler ERR_M lift_ue vec;;
            didx <- concretize_uvalueM M undef_handler ERR_M lift_ue idx;;
            delt <- concretize_uvalueM M undef_handler ERR_M lift_ue elt;;
            lift_ue _ (insert_into_vec_dv vec_typ dvec delt didx)
        | _ => lift_ue _ (raise_error ("concretize_uvalueM: Attempting to convert a partially non-reduced uvalue to dvalue. Should not happen: " ++ uvalue_constructor_string u))
        end.

  Parameter eval_select_equation :
    forall (M : Type -> Type) {HM : Monad M} (undef_handler : dtyp -> M dvalue)
           (ERR_M : Type -> Type) {HM_ERR : Monad ERR_M} {ERR : RAISE_ERROR ERR_M} {UB : RAISE_UB ERR_M}
           {OOM : RAISE_OOM ERR_M} (lift_ue : forall A : Type, ERR_M A -> M A)
           (cnd : dvalue) (v1 v2 : uvalue),
      eval_select M undef_handler ERR_M lift_ue cnd v1 v2 =
        match cnd with
        | DVALUE_Poison t =>
            (* TODO: Should be the type of the result of the select... *)
            ret (DVALUE_Poison t)
        | DVALUE_I1 i =>
            if (Int1.unsigned i =? 1)%Z
            then concretize_uvalueM M undef_handler ERR_M lift_ue v1
            else concretize_uvalueM M undef_handler ERR_M lift_ue v2
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
                                  lift_ue dvalue
                                    (raise_error "concretize_uvalueM: ill-typed select, condition in vector was not poison or i1.")
                              end;;
                  rest <- loop conds xs ys;;
                  ret (selected :: rest)
              | _, _, _ =>
                  lift_ue (list dvalue) (raise_error "concretize_uvalueM: ill-typed vector select, length mismatch.")
              end in
            (* TODO: lazily concretize these vectors to avoid
                   evaluating elements that aren't chosen? *)
            dv1 <- concretize_uvalueM M undef_handler ERR_M lift_ue v1;;
            dv2 <- concretize_uvalueM M undef_handler ERR_M lift_ue v2;;
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
                lift_ue dvalue (raise_error "concretize_uvalueM: ill-typed vector select, non-vector arguments")
            end
        | _ => lift_ue dvalue (raise_error "concretize_uvalueM: ill-typed select.")
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
                             dvalue_has_dtyp dv dt /\ dv <> DVALUE_Poison dt
                         | _ => True
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
                             dvalue_has_dtyp dv dt /\ dv <> DVALUE_Poison dt
                         | _ => True
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
  Definition pick_uvalue (uv : uvalue) : PickUvalueE {dv : dvalue | True}
    := pick uv.

  (* TODO: should the post condition be concretize uv dv ? *)
  Definition pick_unique_uvalue (uv : uvalue) : PickUvalueE {dv : dvalue | True}
    := pickUnique uv.

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
      dv <> DVALUE_Poison dt ->
      concretize (UVALUE_Undef dt) dv.
  Proof.
    intros dt dv DVT H.
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
  Import DVALUE_BYTES.
  Open Scope list.

  Export Byte.

  Module MemHelpers := MemoryHelpers LP MP Byte.
  Import MemHelpers.

  Definition eval_icmp {M} `{Monad M} `{RAISE_ERROR M} icmp v1 v2 : M dvalue :=
    match v1, v2 with
    | DVALUE_I1 i1, DVALUE_I1 i2
    | DVALUE_I8 i1, DVALUE_I8 i2
    | DVALUE_I16 i1, DVALUE_I16 i2
    | DVALUE_I32 i1, DVALUE_I32 i2
    | DVALUE_I64 i1, DVALUE_I64 i2
    | DVALUE_IPTR i1, DVALUE_IPTR i2 => eval_int_icmp icmp i1 i2
    | DVALUE_Poison t1, DVALUE_Poison t2 => ret (DVALUE_Poison t1)
    | DVALUE_Poison t, _ => if is_DVALUE_IX v2 then ret (DVALUE_Poison t) else raise_error "ill_typed-iop"
    | _, DVALUE_Poison t => if is_DVALUE_IX v1 then ret (DVALUE_Poison t) else raise_error "ill_typed-iop"
    | DVALUE_Addr a1, DVALUE_Addr a2 =>
        let i1 := ptr_to_int a1 in
        let i2 := ptr_to_int a2 in
        eval_int_icmp icmp i1 i2
    | _, _ => raise_error ("ill_typed-icmp: " ++ show_dvalue v1 ++ ", " ++ show_dvalue v2)
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
          | DTYPE_I 16, DVALUE_I16 i1, DTYPE_I 1
          | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 1
          | DTYPE_I 64, DVALUE_I64 i1, DTYPE_I 1 =>
              Conv_Pure (DVALUE_I1 (repr (unsigned i1)))

          | DTYPE_I 16, DVALUE_I16 i1, DTYPE_I 8
          | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 8
          | DTYPE_I 64, DVALUE_I64 i1, DTYPE_I 8 =>
              Conv_Pure (DVALUE_I8 (repr (unsigned i1)))

          | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 16
          | DTYPE_I 64, DVALUE_I64 i1, DTYPE_I 16 =>
              Conv_Pure (DVALUE_I16 (repr (unsigned i1)))

          | DTYPE_I 64, DVALUE_I64 i1, DTYPE_I 32 =>
              Conv_Pure (DVALUE_I32 (repr (unsigned i1)))

          | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 1
          | DTYPE_I 16, DVALUE_Poison t, DTYPE_I 1
          | DTYPE_I 16, DVALUE_Poison t, DTYPE_I 8
          | DTYPE_I 32, DVALUE_Poison t, DTYPE_I 1
          | DTYPE_I 32, DVALUE_Poison t, DTYPE_I 8
          | DTYPE_I 32, DVALUE_Poison t, DTYPE_I 16
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

          | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 16
          | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 16 =>
              Conv_Pure (DVALUE_I16 (repr (unsigned i1)))

          | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 32
          | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 32
          | DTYPE_I 16, DVALUE_I16 i1, DTYPE_I 32 =>
              Conv_Pure (DVALUE_I32 (repr (unsigned i1)))

          | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 64
          | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 64
          | DTYPE_I 16, DVALUE_I16 i1, DTYPE_I 64
          | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 64 =>
              Conv_Pure (DVALUE_I64 (repr (unsigned i1)))

          | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 8
          | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 16
          | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 32
          | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 64
          | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 16
          | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 32
          | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 64
          | DTYPE_I 16, DVALUE_Poison t, DTYPE_I 32
          | DTYPE_I 16, DVALUE_Poison t, DTYPE_I 64
          | DTYPE_I 32, DVALUE_Poison t, DTYPE_I 64 =>
              Conv_Pure (DVALUE_Poison t)

          | _, _, _ => Conv_Illegal "ill-typed conv"
          end

      | Sext =>
          match t1, x, t2 with
          | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 8 =>
              Conv_Pure (DVALUE_I8 (repr (signed i1)))

          | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 16
          | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 16 =>
              Conv_Pure (DVALUE_I16 (repr (signed i1)))

          | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 32
          | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 32
          | DTYPE_I 16, DVALUE_I16 i1, DTYPE_I 32 =>
              Conv_Pure (DVALUE_I32 (repr (signed i1)))

          | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 64
          | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 64
          | DTYPE_I 16, DVALUE_I16 i1, DTYPE_I 64
          | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 64 =>
              Conv_Pure (DVALUE_I64 (repr (signed i1)))

          | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 8
          | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 16
          | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 32
          | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 64
          | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 16
          | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 32
          | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 64
          | DTYPE_I 16, DVALUE_Poison t, DTYPE_I 32
          | DTYPE_I 16, DVALUE_Poison t, DTYPE_I 64
          | DTYPE_I 32, DVALUE_Poison t, DTYPE_I 64 =>
              Conv_Pure (DVALUE_Poison t)

          | _, _, _ => Conv_Illegal "ill-typed conv"
          end

      | Bitcast =>
          if dtyp_eqb t1 t2
          then Conv_Pure x
          else if bit_sizeof_dtyp t1 =? bit_sizeof_dtyp t2
               then
                 let bytes := dvalue_to_dvalue_bytes x t1 in
                 let dv_conv := ErrOOMPoison_handle_poison_and_oom DVALUE_Poison (@dvalue_bytes_to_dvalue ErrOOMPoison _ _ _ _ bytes t2) in
                 match unIdent (unEitherT (unEitherT (unEitherT (unERR_UB_OOM dv_conv)))) with
                 | inl (OOM_message oom) =>
                     Conv_Oom ("Bitcast OOM: " ++ oom)
                 | inr (inl (UB_message ub)) =>
                     Conv_Illegal ("Bitcast UB: " ++ ub)
                 | inr (inr (inl (ERR_message err))) =>
                     Conv_Illegal ("Bitcast Error: " ++ err)
                 | inr (inr (inr dv)) =>
                     Conv_Pure dv
                 end
               else Conv_Illegal "unequal bitsize in cast"

      | Uitofp =>
          match t1, x, t2 with
          | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Float
          | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Float
          | DTYPE_I 16, DVALUE_I16 i1, DTYPE_Float
          | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Float
          | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Float =>
              Conv_Pure (DVALUE_Float (Float32.of_intu (repr (unsigned i1))))

          | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Double
          | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Double
          | DTYPE_I 16, DVALUE_I16 i1, DTYPE_Double
          | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Double
          | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Double =>
              Conv_Pure (DVALUE_Double (Float.of_longu (repr (unsigned i1))))

          | DTYPE_I 1, DVALUE_Poison t, DTYPE_Float
          | DTYPE_I 8, DVALUE_Poison t, DTYPE_Float
          | DTYPE_I 16, DVALUE_Poison t, DTYPE_Float
          | DTYPE_I 32, DVALUE_Poison t, DTYPE_Float
          | DTYPE_I 64, DVALUE_Poison t, DTYPE_Float
          | DTYPE_I 1, DVALUE_Poison t, DTYPE_Double
          | DTYPE_I 8, DVALUE_Poison t, DTYPE_Double
          | DTYPE_I 16, DVALUE_Poison t, DTYPE_Double
          | DTYPE_I 32, DVALUE_Poison t, DTYPE_Double
          | DTYPE_I 64, DVALUE_Poison t, DTYPE_Double =>
              Conv_Pure (DVALUE_Poison t)

          | _, _, _ => Conv_Illegal "ill-typed Uitofp"
          end

      | Sitofp =>
          match t1, x, t2 with
          | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Float
          | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Float
          | DTYPE_I 16, DVALUE_I16 i1, DTYPE_Float
          | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Float
          | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Float =>
              Conv_Pure (DVALUE_Float (Float32.of_intu (repr (signed i1))))

          | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Double
          | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Double
          | DTYPE_I 16, DVALUE_I16 i1, DTYPE_Double
          | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Double
          | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Double =>
              Conv_Pure (DVALUE_Double (Float.of_longu (repr (signed i1))))

          | DTYPE_I 1, DVALUE_Poison t, DTYPE_Float
          | DTYPE_I 8, DVALUE_Poison t, DTYPE_Float
          | DTYPE_I 16, DVALUE_Poison t, DTYPE_Float
          | DTYPE_I 32, DVALUE_Poison t, DTYPE_Float
          | DTYPE_I 64, DVALUE_Poison t, DTYPE_Float
          | DTYPE_I 1, DVALUE_Poison t, DTYPE_Double
          | DTYPE_I 8, DVALUE_Poison t, DTYPE_Double
          | DTYPE_I 16, DVALUE_Poison t, DTYPE_Double
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

  Section Concretize.
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

      Definition pre_concretized (acc : NMap (list (uvalue * dvalue))) (uv : uvalue) (sid : store_id) : option dvalue
        := vs <- NM.find sid acc;;
           assoc uv vs.

      Definition new_concretized_byte
        (acc : NMap (list (uvalue * dvalue))) (uv : uvalue) (dv : dvalue) (sid : store_id) : NMap (list (uvalue * dvalue))
        := match NM.find sid acc with
           | Some vs =>
               match assoc uv vs with
               | Some _ =>
                   acc
               | None =>
                   NM.add sid (vs ++ [(uv, dv)]) acc
               end
           | None =>
               NM.add sid [(uv, dv)] acc
           end.

      (* Take a UVALUE_ExtractByte, and replace the uvalue with a given dvalue...
       *)
      Definition uvalue_byte_replace_with_dvalue_byte (uv : uvalue) (dv : dvalue) : M dvalue_byte
        := match uv with
           | UVALUE_ExtractByte uv dt idx sid =>
               ret (DVALUE_ExtractByte dv dt idx)
           | _ => lift_ue (raise_error "uvalue_byte_replace_with_dvalue_byte called with non-UVALUE_ExtractByte value.")
           end.

      (* M will be err_or_ub / MPropT err_or_ub? *)
      (* Define a sum type f a, g b.... a + b. Mutual recursive
           function as one big function with sum type to select between
           which "function" is being called *)
      Fixpoint concretize_uvalueM (u : uvalue) : M dvalue :=
        let
          eval_select
            (cnd : dvalue) (v1 v2 : uvalue) : M dvalue
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
             end
        in
        (* Concretize the uvalues in a list of UVALUE_ExtractBytes...

         *)
        (* Pick out uvalue bytes that are the same + have same sid

         Concretize these identical uvalues...
         *)
        let fix concretize_uvalue_bytes_helper (acc : NMap (list (uvalue * dvalue))) (uvs : list uvalue) {struct uvs} : M (list dvalue_byte)
          := match uvs with
             | [] => ret []
             | (uv::uvs) =>
                 match uv with
                 | UVALUE_ExtractByte byte_uv dt idx sid =>
                     (* Check if this uvalue has been concretized already *)
                     match pre_concretized acc byte_uv sid with
                     | Some dv =>
                         (* Use the pre_concretized value *)
                         let dv_byte := DVALUE_ExtractByte dv dt idx in
                         (* Concretize the rest of the bytes *)
                         rest <- concretize_uvalue_bytes_helper acc uvs;;
                         ret (dv_byte :: rest)
                     | None =>
                         (* Concretize the uvalue *)
                         dv <- concretize_uvalueM byte_uv;;
                         let dv_byte := DVALUE_ExtractByte dv dt idx in
                         let acc := new_concretized_byte acc byte_uv dv sid in
                         (* Concretize the rest of the bytes *)
                         rest <- concretize_uvalue_bytes_helper acc uvs;;
                         ret (dv_byte :: rest)
                     end
                 | _ =>
                     lift_ue (raise_error "concretize_uvalue_bytes_helper: non-byte in uvs.")
                 end
             end in

        let concretize_uvalue_bytes (uvs : list uvalue) : M (list dvalue_byte)
          := concretize_uvalue_bytes_helper (@NM.empty _) uvs in

        let extractbytes_to_dvalue (uvs : list uvalue) (dt : dtyp) : M dvalue
          := dvbs <- concretize_uvalue_bytes uvs;;
             lift_ue (ErrOOMPoison_handle_poison_and_oom DVALUE_Poison (dvalue_bytes_to_dvalue dvbs dt))
        in
        match u with
        | UVALUE_Addr a                          => ret (DVALUE_Addr a)
        | UVALUE_I1 x                            => ret (DVALUE_I1 x)
        | UVALUE_I8 x                            => ret (DVALUE_I8 x)
        | UVALUE_I16 x                           => ret (DVALUE_I16 x)
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
            | Conv_Oom s => lift_ue (raise_oom s)
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
            | true, Some uv =>
                match bytes with
                | (UVALUE_ExtractByte uv _ _ _ :: _) => concretize_uvalueM uv
                | _ => lift_ue (raise_error "ConcatBytes case... Should not happen.")
                end
            | _, _ => extractbytes_to_dvalue bytes dt
            end

        | UVALUE_ExtractByte byte dt idx sid =>
            (* TODO: maybe this is just an error? ExtractByte should be guarded by ConcatBytes? *)
            lift_ue (raise_error "Attempting to concretize UVALUE_ExtractByte, should not happen.")
        | UVALUE_InsertValue t uv et elt idxs =>
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

      Lemma concretize_uvalueM_equation :
        forall (u : uvalue),
          concretize_uvalueM u =
            let
              eval_select
                (cnd : dvalue) (v1 v2 : uvalue) : M dvalue
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
                         @ret M _ _ (DVALUE_Poison t)
                     | DVALUE_Vector _, DVALUE_Poison t =>
                         (* TODO: Should we make sure t is a vector type...? *)
                         @ret M _ _ (DVALUE_Poison t)
                     | DVALUE_Vector xs, DVALUE_Vector ys =>
                         selected <- loop conds xs ys;;
                         @ret M _ _ (DVALUE_Vector selected)
                     | _, _ =>
                         lift_ue (raise_error "concretize_uvalueM: ill-typed vector select, non-vector arguments")
                     end
                 | _ => lift_ue (raise_error "concretize_uvalueM: ill-typed select.")
                 end
            in
            (* Concretize the uvalues in a list of UVALUE_ExtractBytes...

             *)
            (* Pick out uvalue bytes that are the same + have same sid

         Concretize these identical uvalues...
             *)
            let fix concretize_uvalue_bytes_helper (acc : NMap (list (uvalue * dvalue))) (uvs : list uvalue) {struct uvs} : M (list dvalue_byte)
              := match uvs with
                 | [] => ret []
                 | (uv::uvs) =>
                     match uv with
                     | UVALUE_ExtractByte byte_uv dt idx sid =>
                         (* Check if this uvalue has been concretized already *)
                         match pre_concretized acc byte_uv sid with
                         | Some dv =>
                             (* Use the pre_concretized value *)
                             let dv_byte := DVALUE_ExtractByte dv dt idx in
                             (* Concretize the rest of the bytes *)
                             rest <- concretize_uvalue_bytes_helper acc uvs;;
                             ret (dv_byte :: rest)
                         | None =>
                             (* Concretize the uvalue *)
                             dv <- concretize_uvalueM byte_uv;;
                             let dv_byte := DVALUE_ExtractByte dv dt idx in
                             let acc := new_concretized_byte acc byte_uv dv sid in
                             (* Concretize the rest of the bytes *)
                             rest <- concretize_uvalue_bytes_helper acc uvs;;
                             ret (dv_byte :: rest)
                         end
                     | _ =>
                         lift_ue (raise_error "concretize_uvalue_bytes_helper: non-byte in uvs.")
                     end
                 end in

            let concretize_uvalue_bytes (uvs : list uvalue) : M (list dvalue_byte)
              := concretize_uvalue_bytes_helper (@NM.empty _) uvs in

            let extractbytes_to_dvalue (uvs : list uvalue) (dt : dtyp) : M dvalue
              := dvbs <- concretize_uvalue_bytes uvs;;
                 lift_ue (ErrOOMPoison_handle_poison_and_oom DVALUE_Poison (dvalue_bytes_to_dvalue dvbs dt))
            in
            match u with
            | UVALUE_Addr a                          => ret (DVALUE_Addr a)
            | UVALUE_I1 x                            => ret (DVALUE_I1 x)
            | UVALUE_I8 x                            => ret (DVALUE_I8 x)
            | UVALUE_I16 x                           => ret (DVALUE_I16 x)
            | UVALUE_I32 x                           => ret (DVALUE_I32 x)
            | UVALUE_I64 x                           => ret (DVALUE_I64 x)
            | UVALUE_IPTR x                          => ret (DVALUE_IPTR x)
            | UVALUE_Double x                        => ret (DVALUE_Double x)
            | UVALUE_Float x                         => ret (DVALUE_Float x)
            | UVALUE_Undef t                         => undef_handler t
            | UVALUE_Poison t                        => ret (DVALUE_Poison t)
            | UVALUE_Oom t                           => ret (DVALUE_Oom t)
            | UVALUE_None                            => ret DVALUE_None
            | UVALUE_Struct fields                   => 'dfields <- map_monad (concretize_uvalueM) fields ;;
                                                        ret (DVALUE_Struct dfields)
            | UVALUE_Packed_struct fields            => 'dfields <- map_monad (concretize_uvalueM) fields ;;
                                                        ret (DVALUE_Packed_struct dfields)
            | UVALUE_Array elts                      => 'delts <- map_monad (concretize_uvalueM) elts ;;
                                                        ret (DVALUE_Array delts)
            | UVALUE_Vector elts                     => 'delts <- map_monad (concretize_uvalueM) elts ;;
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
                | Conv_Oom s => lift_ue (raise_oom s)
                | Conv_Illegal s => lift_ue (raise_error s)
                end

            | UVALUE_GetElementPtr t ua uvs =>
                da <- concretize_uvalueM ua;;
                dvs <- map_monad (concretize_uvalueM) uvs;;
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
                match N.eqb (N.of_nat (length bytes)) (sizeof_dtyp dt), Byte.all_extract_bytes_from_uvalue dt bytes with
                | true, Some uv =>
                    match bytes with
                    | (UVALUE_ExtractByte uv _ _ _ :: _) => concretize_uvalueM uv
                    | _ => lift_ue (raise_error "ConcatBytes case... Should not happen.")
                    end
                | _, _ => extractbytes_to_dvalue bytes dt
                end

            | UVALUE_ExtractByte byte dt idx sid =>
                (* TODO: maybe this is just an error? ExtractByte should be guarded by ConcatBytes? *)
                lift_ue (raise_error "Attempting to concretize UVALUE_ExtractByte, should not happen.")
            | UVALUE_InsertValue t uv et elt idxs =>
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
        induction u; try reflexivity.
      Qed.

      Fixpoint concretize_uvalue_bytes_helper (acc : NMap (list (uvalue * dvalue))) (uvs : list uvalue) : M (list dvalue_byte)
        := match uvs with
           | [] => ret []
           | (uv::uvs) =>
               match uv with
               | UVALUE_ExtractByte byte_uv dt idx sid =>
                   (* Check if this uvalue has been concretized already *)
                   match pre_concretized acc byte_uv sid with
                   | Some dv =>
                       (* Use the pre_concretized value *)
                       let dv_byte := DVALUE_ExtractByte dv dt idx in
                       (* Concretize the rest of the bytes *)
                       rest <- concretize_uvalue_bytes_helper acc uvs;;
                       ret (dv_byte :: rest)
                   | None =>
                       (* Concretize the uvalue *)
                       dv <- concretize_uvalueM byte_uv;;
                       let dv_byte := DVALUE_ExtractByte dv dt idx in
                       let acc := new_concretized_byte acc byte_uv dv sid in
                       (* Concretize the rest of the bytes *)
                       rest <- concretize_uvalue_bytes_helper acc uvs;;
                       ret (dv_byte :: rest)
                   end
               | _ =>
                   lift_ue (raise_error "concretize_uvalue_bytes_helper: non-byte in uvs.")
               end
           end.

      Lemma concretize_uvalue_bytes_helper_equation (acc : NMap (list (uvalue * dvalue))) (uvs : list uvalue) :
        concretize_uvalue_bytes_helper acc uvs
        = match uvs with
          | [] => ret []
          | (uv::uvs) =>
              match uv with
              | UVALUE_ExtractByte byte_uv dt idx sid =>
                  (* Check if this uvalue has been concretized already *)
                  match pre_concretized acc byte_uv sid with
                  | Some dv =>
                      (* Use the pre_concretized value *)
                      let dv_byte := DVALUE_ExtractByte dv dt idx in
                      (* Concretize the rest of the bytes *)
                      rest <- concretize_uvalue_bytes_helper acc uvs;;
                      ret (dv_byte :: rest)
                  | None =>
                      (* Concretize the uvalue *)
                      dv <- concretize_uvalueM byte_uv;;
                      let dv_byte := DVALUE_ExtractByte dv dt idx in
                      let acc := new_concretized_byte acc byte_uv dv sid in
                      (* Concretize the rest of the bytes *)
                      rest <- concretize_uvalue_bytes_helper acc uvs;;
                      ret (dv_byte :: rest)
                  end
              | _ =>
                  lift_ue (raise_error "concretize_uvalue_bytes_helper: non-byte in uvs.")
              end
          end.
      Proof.
        induction uvs; try reflexivity.
      Qed.

      Definition eval_select
        (cnd : dvalue) (v1 v2 : uvalue) : M dvalue
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
                   @ret M _ _ (DVALUE_Poison t)
               | DVALUE_Vector _, DVALUE_Poison t =>
                   (* TODO: Should we make sure t is a vector type...? *)
                   @ret M _ _ (DVALUE_Poison t)
               | DVALUE_Vector xs, DVALUE_Vector ys =>
                   selected <- loop conds xs ys;;
                   @ret M _ _ (DVALUE_Vector selected)
               | _, _ =>
                   lift_ue (raise_error "concretize_uvalueM: ill-typed vector select, non-vector arguments")
               end
           | _ => lift_ue (raise_error "concretize_uvalueM: ill-typed select.")
           end.

      Lemma eval_select_equation (cnd : dvalue) (v1 v2 : uvalue) :
        eval_select cnd v1 v2 =
          match cnd with
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
                  @ret M _ _ (DVALUE_Poison t)
              | DVALUE_Vector _, DVALUE_Poison t =>
                  (* TODO: Should we make sure t is a vector type...? *)
                  @ret M _ _ (DVALUE_Poison t)
              | DVALUE_Vector xs, DVALUE_Vector ys =>
                  selected <- loop conds xs ys;;
                  @ret M _ _ (DVALUE_Vector selected)
              | _, _ =>
                  lift_ue (raise_error "concretize_uvalueM: ill-typed vector select, non-vector arguments")
              end
          | _ => lift_ue (raise_error "concretize_uvalueM: ill-typed select.")
          end.
      Proof.
        destruct cnd; try reflexivity.
      Qed.

    End Concretize.

    Arguments concretize_uvalueM {_ _}.

  End Concretize.
End MakeBase.

Module Make (LP : LLVMParams) (MP : MemoryParams LP) (Byte : ByteModule LP.ADDR LP.IP LP.SIZEOF LP.Events MP.BYTE_IMPL) (SER : ConcretizationBase LP MP Byte) : Concretization LP MP Byte SER.
  Include Concretization LP MP Byte SER.
End Make.
