From Coq Require Import
     ZArith
     String
     List.

From ExtLib Require Import
     Structures.Monads
     Structures.Maps.

From ITree Require Import
     ITree
     Eq
     Events.State.

From Vellvm Require Import
     LLVMAst
     AstLib
     MemoryAddress
     DynamicValues
     DynamicTypes
     LLVMEvents
     Error
     Util
     PropT.

Require Import Floats.

Set Implicit Arguments.
Set Contextual Implicit.

Import MonadNotation.


Module Make(A:MemoryAddress.ADDRESS)(LLVMIO: LLVM_INTERACTIONS(A)).

  Import LLVMIO.

  Section PickPropositional.

    (*  Semantics with the Pick + Predicates:
        expr = div 1 undef 
           intepreter: "evaluate"   div 1 0   ==> trigger UBE   ==> interpret UBE as trigger Fail
           model:  trigger UBE ==> all Trees  (including trigger Fail)

       expr = div 1 (1 - undef)
           interpreter:  div 1 1 ==> ret 1
           model:  trigger UBE ==> all Trees  (including ret 1)


       Four cases:
       C   exists dv, concretize_uvalue uv = ret dv  => easy by relation between concretize and 
       C   concretize_uvalue uv = trigger UBE        => in this case, later interpretation of UBE
       C   concretize_uvalue uv = trigger fail 
      ~C   --> pick UBE
    
       Lemma: concretize_uvalue uv = Ret dv  ->  concretize uv dv



       Semantics without the predicates in Pick:
        expr = div 1 undef 
           intepreter: "evaluate"   div 1 0      ==> trigger UB   ==> interpret UBE as trigger Fail
           model: after Pick_handler:  {trigger UBE, ret (1/n) | n }  ==> 
                  after UBE_handler :  { all trees }    (including trigger Fail)

       expr = div 1 (1 - undef)
           interpreter:  div 1 1 ==> ret 1
           model: after Pick_handler:  {trigger UBE, ret (1/n) | n }  ==> 
                  after UBE_handler :  { all trees }    (including ret 1)
    *)
    (* YZ: TODO: better UB error message *)
    (* SAZ: For now, leaving the "C" parameter, but just ignoring it here *)
    
    
    Inductive Pick_handler {E} `{FE:FailureE -< E} `{FO:UBE -< E}: PickE ~> PropT E :=
    | PickD: forall uv C res t,  concretize_u uv res -> t ≈ (lift_undef_or_err ret res) -> Pick_handler (pick uv C) t.
                                                                      
    Section PARAMS_MODEL.
      Variable (E F: Type -> Type).

      Definition E_trigger_prop : E ~> PropT (E +' F) :=
        fun R e => fun t => t = r <- trigger e ;; ret r.

      Definition F_trigger_prop : F ~> PropT (E +' F) :=
        fun R e => fun t => t = r <- trigger e ;; ret r.

      Definition model_undef `{FailureE -< E +' F} `{UBE -< E +' F} :
        forall (T:Type) (RR: T -> T -> Prop), itree (E +' PickE +' F) T -> PropT (E +' F) T :=
        interp_prop (case_ E_trigger_prop (case_ Pick_handler F_trigger_prop)).

    End PARAMS_MODEL.

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
      | DTYPE_Double => DVALUE_Double (Float32.to_double Float32.zero)
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
    Fixpoint concretize_uvalue (u : uvalue) : undef_or_err dvalue :=
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
                                                 eval_iop iop dv1 dv2
      | UVALUE_ICmp cmp v1 v2                  => dv1 <- concretize_uvalue v1 ;;
                                                  dv2 <- concretize_uvalue v2 ;;
                                                  eval_icmp cmp dv1 dv2
      | UVALUE_FBinop fop fm v1 v2             => dv1 <- concretize_uvalue v1 ;;
                                                  dv2 <- concretize_uvalue v2 ;;
                                                  eval_fop fop dv1 dv2
      | UVALUE_FCmp cmp v1 v2                  => dv1 <- concretize_uvalue v1 ;;
                                                  dv2 <- concretize_uvalue v2 ;;
                                                  eval_fcmp cmp dv1 dv2
      | _ => failwith "Attempting to convert a partially non-reduced uvalue to dvalue. Should not happen"
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

    Ltac do_it := constructor; cbn; auto; fail.

    Lemma dvalue_default : forall t,  dvalue_has_dtyp (default_dvalue_of_dtyp t) t.
    Proof.
      intros t.
      induction t using dtyp_ind; try do_it.
      - cbn. destruct (@IX_supported_dec sz).
        * inversion i; constructor; auto.
        * rewrite unsupported_cases; auto. constructor. auto.
    Admitted.          
      
    Lemma concretize_u_concretize_uvalue : forall u, concretize_u u (concretize_uvalue u).
    Proof.
      intros u.
      induction u using uvalue_ind'; try do_it.
      - cbn. apply Concretize_Undef. apply dvalue_default.
      - cbn. (* need to relate map_monad to the forall  *)
    Admitted.
      
    Definition concretize_picks {E} `{FailureE -< E} `{UBE -< E} : PickE ~> itree E :=
      fun T p => match p with
              | pick u P => lift_undef_or_err ret (concretize_uvalue u)
              end.

    Section PARAMS_INTERP.
      Variable (E F: Type -> Type).

      Definition E_trigger :  E ~> itree (E +' F) :=
        fun R e => r <- trigger e ;; ret r.

      Definition F_trigger : F ~> itree (E +' F) :=
        fun R e => r <- trigger e ;; ret r.

      Definition exec_undef `{FailureE -< E +' F} `{UBE -< E +' F} :
        itree (E +' PickE +' F) ~> itree (E +' F) :=
        interp (case_ E_trigger
               (case_ concretize_picks F_trigger)).

    End PARAMS_INTERP.

  End PickImplementation.

End Make.
