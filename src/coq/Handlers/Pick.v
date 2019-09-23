From Coq Require Import
     ZArith
     String.

From ExtLib Require Import
     Programming.Show
     Structures.Monads
     Structures.Maps.

From ITree Require Import 
     ITree
     Events.State.

From Vellvm Require Import
     LLVMAst
     AstLib
     MemoryAddress
     DynamicValues
     DynamicTypes
     LLVMEvents
     Error
     Util.

Require Import  Floats.

Module Make(A:MemoryAddress.ADDRESS)(LLVMIO: LLVM_INTERACTIONS(A)).

  Import LLVMIO.

  Section PickPropositional.

    (* YZ: TODO: better UB error message *)
    (* YZ: TODO: rename UBE *)
    Inductive Pick_handler: forall {X}, PickE X -> (itree UBE X -> Prop) :=
    | PickUB: forall uv C, ~ C -> Pick_handler (pick uv C) (raiseUB "Picking unsafe uvalue")
    | PickD: forall uv (C: Prop) dv, C -> concretize uv dv -> Pick_handler (pick uv C) (ret dv).

  End PickPropositional.

  Section PickImplementation.

    Open Scope Z_scope.

    (* Handler for PickE which concretizes everything to 0 *)
    Fixpoint default_dvalue_of_dtyp (dt : dtyp) : dvalue :=
      match dt with
      | DTYPE_I sz =>
        (* CB TODO: better way? *)
        match sz with
        | 1  => DVALUE_I1 (repr 0)
        | 8  => DVALUE_I8 (repr 0)
        | 32 => DVALUE_I32 (repr 0)
        | 64 => DVALUE_I64 (repr 0)
        | _  => DVALUE_None
        end
      | DTYPE_Pointer => DVALUE_Addr A.null
      | DTYPE_Void => DVALUE_None
      | DTYPE_Half => DVALUE_Float Float32.zero (* ??? *)
      | DTYPE_Float => DVALUE_Float Float32.zero
      | DTYPE_Double => DVALUE_Float Float32.zero (* ??? *)
      | DTYPE_X86_fp80 => DVALUE_Float Float32.zero (* ??? *)
      | DTYPE_Fp128 => DVALUE_Float Float32.zero (* ??? *)
      | DTYPE_Ppc_fp128 => DVALUE_Float Float32.zero (* ??? *)
      | DTYPE_Metadata => DVALUE_None (* ??? *)
      | DTYPE_X86_mmx => DVALUE_None (* ??? *)
      | DTYPE_Array sz t => DVALUE_Array (repeat (default_dvalue_of_dtyp t) (Z.to_nat sz))
      | DTYPE_Struct fields => DVALUE_Struct (map default_dvalue_of_dtyp fields)
      | DTYPE_Packed_struct fields => DVALUE_Packed_struct (map default_dvalue_of_dtyp fields)
      | DTYPE_Opaque => DVALUE_None (* ??? *)
      | DTYPE_Vector sz t => DVALUE_Vector (repeat (default_dvalue_of_dtyp t) (Z.to_nat sz))
      end.

    Import MonadNotation.
    Fixpoint concretize_uvalue (u : uvalue) : itree (FailureE +' UBE) dvalue :=
      match u with
      | UVALUE_Addr a                          => ret (DVALUE_Addr a)
      | UVALUE_I1 x                            => ret (DVALUE_I1 x)
      | UVALUE_I8 x                            => ret (DVALUE_I8 x)
      | UVALUE_I32 x                           => ret (DVALUE_I32 x)
      | UVALUE_I64 x                           => ret (DVALUE_I64 x)
      | UVALUE_Double x                        => ret (DVALUE_Double x)
      | UVALUE_Float x                         => ret (DVALUE_Float x)
      | UVALUE_Undef t                         => ret (default_dvalue_of_dtyp t)
      | UVALUE_Poison                          => ret (DVALUE_Poison)
      | UVALUE_None                            => ret DVALUE_None
      | UVALUE_Struct fields                   => 'dfields <- map_monad concretize_uvalue fields ;;
                                                          ret (DVALUE_Struct dfields)
      | UVALUE_Packed_struct fields            => 'dfields <- map_monad concretize_uvalue fields ;;
                                                          ret (DVALUE_Packed_struct dfields)
      | UVALUE_Array elts                      => 'delts <- map_monad concretize_uvalue elts ;;
                                                        ret (DVALUE_Array delts)
      | UVALUE_Vector elts                     => 'delts <- map_monad concretize_uvalue elts ;;
                                                        ret (DVALUE_Vector delts)
      | UVALUE_IBinop iop v1 v2                => dv1 <- concretize_uvalue v1 ;;
                                                     dv2 <- concretize_uvalue v2 ;;
                                                     lift_undef_or_err ret (eval_iop iop dv1 dv2) 
      | UVALUE_ICmp cmp v1 v2                  => dv1 <- concretize_uvalue v1 ;;
                                                     dv2 <- concretize_uvalue v2 ;;
                                                     lift_undef_or_err ret (eval_icmp cmp dv1 dv2) 
      | UVALUE_FBinop fop fm v1 v2             => dv1 <- concretize_uvalue v1 ;;
                                                     dv2 <- concretize_uvalue v2 ;;
                                                     lift_undef_or_err ret (eval_fop fop dv1 dv2)
      | UVALUE_FCmp cmp v1 v2                  => dv1 <- concretize_uvalue v1 ;;
                                                     dv2 <- concretize_uvalue v2 ;;
                                                     lift_undef_or_err ret (eval_fcmp cmp dv1 dv2)
      | _ => raise "unimplemented concretization of uvalue"
      (*
  | UVALUE_Conversion conv v t_to          => 
  | UVALUE_GetElementPtr t ptrval idxs     => _
  | UVALUE_ExtractElement vec idx          => _
  | UVALUE_InsertElement vec elt idx       => _
  | UVALUE_ShuffleVector vec1 vec2 idxmask => _
  | UVALUE_ExtractValue vec idxs           => _
  | UVALUE_InsertValue vec elt idxs        => _
  | UVALUE_Select cnd v1 v2                => _
       *)
      end.

    Program Definition concretize_picks {E} `{FailureE -< E} `{UBE -< E} : PickE ~> itree E.
    refine (fun T p => match p with
                    | pick u P => translate _ (concretize_uvalue u)
                    end).
    refine (fun T fu => _).
    destruct fu; auto.
    Defined.

  End PickImplementation.

End Make.
