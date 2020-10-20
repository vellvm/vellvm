From Coq Require Import
     ZArith
     String
     List
     Lia.

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

    Definition default_dvalue_of_dtyp_i sz : err dvalue:=
      (if (sz =? 64) then ret (DVALUE_I64 (repr 0))
        else if (sz =? 32) then ret (DVALUE_I32 (repr 0))
            else if (sz =? 8) then ret (DVALUE_I8 (repr 0))
                  else if (sz =? 1) then ret (DVALUE_I1 (repr 0))
                       else failwith
              "Illegal size for generating default dvalue of DTYPE_I").


    (* Handler for PickE which concretizes everything to 0 *)
    Fixpoint default_dvalue_of_dtyp (dt : dtyp) : err dvalue :=
      match dt with
      | DTYPE_I sz => default_dvalue_of_dtyp_i sz
      | DTYPE_Pointer => ret (DVALUE_Addr A.null)
      | DTYPE_Void => ret DVALUE_None
      | DTYPE_Half => ret (DVALUE_Float Float32.zero) (* ??? *)
      | DTYPE_Float => ret (DVALUE_Float Float32.zero)
      | DTYPE_Double => ret (DVALUE_Double (Float32.to_double Float32.zero))
      | DTYPE_X86_fp80 => ret (DVALUE_Float Float32.zero) (* ??? *)
      | DTYPE_Fp128 => ret (DVALUE_Float Float32.zero) (* ??? *)
      | DTYPE_Ppc_fp128 => ret (DVALUE_Float Float32.zero) (* ??? *)
      | DTYPE_Metadata => ret DVALUE_None (* ??? *)
      | DTYPE_X86_mmx => ret DVALUE_None (* ??? *)
      | DTYPE_Opaque => ret DVALUE_None (* ??? *)
      | DTYPE_Array sz t =>
        if (0 <=? sz) then
          v <- default_dvalue_of_dtyp t ;;
          (ret (DVALUE_Array (repeat v (Z.to_nat sz))))
        else
          failwith ("Negative array length for generating default value" ++
          "of DTYPE_Array or DTYPE_Vector")

      (* Matching valid Vector types... *)
      | DTYPE_Vector sz (DTYPE_Half) =>
        if (0 <=? sz) then
          (ret (DVALUE_Vector
                  (repeat (DVALUE_Float Float32.zero) (Z.to_nat sz))))
        else
          failwith ("Negative array length for generating default value" ++
          "of DTYPE_Array or DTYPE_Vector")
      | DTYPE_Vector sz (DTYPE_Float) =>
        if (0 <=? sz) then
          (ret (DVALUE_Vector
                  (repeat (DVALUE_Float Float32.zero) (Z.to_nat sz))))
        else
          failwith ("Negative array length for generating default value" ++
          "of DTYPE_Array or DTYPE_Vector")
      | DTYPE_Vector sz (DTYPE_Double) =>
        if (0 <=? sz) then
          (ret (DVALUE_Vector
                  (repeat (DVALUE_Double (Float32.to_double Float32.zero))
                          (Z.to_nat sz))))
        else
          failwith ("Negative array length for generating default value" ++
          "of DTYPE_Array or DTYPE_Vector")
      | DTYPE_Vector sz (DTYPE_X86_fp80) =>
        if (0 <=? sz) then
          (ret (DVALUE_Vector
                  (repeat (DVALUE_Float Float32.zero) (Z.to_nat sz))))
        else
          failwith ("Negative array length for generating default value" ++
          "of DTYPE_Array or DTYPE_Vector")
      | DTYPE_Vector sz (DTYPE_Fp128) =>
        if (0 <=? sz) then
          (ret (DVALUE_Vector
                  (repeat (DVALUE_Float Float32.zero) (Z.to_nat sz))))
        else
          failwith ("Negative array length for generating default value" ++
          "of DTYPE_Array or DTYPE_Vector")
      | DTYPE_Vector sz (DTYPE_I n) =>
        if (0 <=? sz) then
          v <- default_dvalue_of_dtyp_i n ;;
          (ret (DVALUE_Vector (repeat v (Z.to_nat sz))))
        else
          failwith ("Negative array length for generating default value" ++
          "of DTYPE_Array or DTYPE_Vector")
      | DTYPE_Vector sz _ => failwith ("Non-valid vector type when" ++
          "generating default vector")
      | DTYPE_Struct fields =>
        v <- @map_monad err _ dtyp dvalue default_dvalue_of_dtyp fields;;
        ret (DVALUE_Struct v)
      | DTYPE_Packed_struct fields =>
        v <- @map_monad err _ dtyp dvalue default_dvalue_of_dtyp fields;;
        ret (DVALUE_Packed_struct v)
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
      | UVALUE_Undef t                         => lift (default_dvalue_of_dtyp t)
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
      | _ => (lift (failwith "Attempting to convert a partially non-reduced uvalue to dvalue. Should not happen"))
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

    Lemma forall_repeat_true:
      forall A (f : A -> Prop) n x, f x -> Forall (fun y : A => f y) (repeat x n).
    Proof.
      intros. induction n. cbn. constructor.
      constructor. auto. cbn. apply IHn.
    Qed.

    Lemma dvalue_default : forall t v,
        inr v = (default_dvalue_of_dtyp t) ->
        dvalue_has_dtyp v t.
    Proof.
      intros t v. revert v.
      induction t; try do_it;
        try (intros; subst; inversion H; constructor).
      - intros. subst. cbn in H.
        unfold default_dvalue_of_dtyp_i in H.
        destruct (@IX_supported_dec a).
        * inversion i; subst; cbn in H; inversion H; constructor; auto.
        * rewrite unsupported_cases in H; auto. inversion H.
      - intros. subst. inversion H. clear H.
        induction sz.
        + cbn in H1.
          destruct (default_dvalue_of_dtyp t) eqn: HT. inv H1. inv H1.
          pose proof DVALUE_Array_typ.
          specialize (H nil (Z.to_nat 0) t).
          rewrite Z2Nat.id in H. 2 : lia.
          apply H. auto. auto.
        + cbn in H1.
          destruct (default_dvalue_of_dtyp t) eqn: HT. inv H1. inv H1.
          pose proof DVALUE_Array_typ as ARR.
          specialize (ARR (repeat d (Pos.to_nat p)) (Z.to_nat (Z.pos p)) t).
          rewrite Z2Nat.id in ARR. 2 : lia.
          cbn in *.
          apply ARR.
          * apply forall_repeat_true.
            apply IHt. reflexivity.
          * apply repeat_length.
        + inv H1.
      - revert H. induction fields.
        + intros. inv H0. constructor.
        + intros.
          assert (forall u : dtyp,
              In u fields ->
              forall v : dvalue,
                inr v = default_dvalue_of_dtyp u -> dvalue_has_dtyp v u).
          { intros. apply H. apply in_cons. auto. auto. }
          specialize (IHfields H1). clear H1.
          Opaque map_monad.
          (* Reduce H0 *)
          cbn in H0.
          rewrite list_cons_app in H0.
          rewrite map_monad_app in H0. cbn in H0.
          Transparent map_monad.
          unfold map_monad at 1 in H0.
          Opaque map_monad. cbn in H0.
          destruct (default_dvalue_of_dtyp a) eqn: A_DEFAULT.
          inv H0.
          destruct (map_monad default_dvalue_of_dtyp fields) eqn: FIELDS.
          inv H0.
          inv H0. constructor. apply H. apply in_eq.
          symmetry. auto.
          apply IHfields. cbn. rewrite FIELDS. reflexivity.
      - revert H. induction fields.
        + intros. inv H0. constructor.
        + intros.
          assert (forall u : dtyp,
              In u fields ->
              forall v : dvalue,
                inr v = default_dvalue_of_dtyp u -> dvalue_has_dtyp v u).
          { intros. apply H. apply in_cons. auto. auto. }
          specialize (IHfields H1). clear H1.
          Opaque map_monad.
          (* Reduce H0 *)
          cbn in H0.
          rewrite list_cons_app in H0.
          rewrite map_monad_app in H0. cbn in H0.
          Transparent map_monad.
          unfold map_monad at 1 in H0.
          Opaque map_monad. cbn in H0.
          destruct (default_dvalue_of_dtyp a) eqn: A_DEFAULT.
          inv H0.
          destruct (map_monad default_dvalue_of_dtyp fields) eqn: FIELDS.
          inv H0.
          inv H0. constructor. apply H. apply in_eq.
          symmetry. auto.
          apply IHfields. cbn. rewrite FIELDS. reflexivity.
      - intros. subst. inversion H. clear H.
        revert H1. revert v. revert IHt. revert t.
        induction sz.
        + intros. cbn in H1.
          pose proof DVALUE_Vector_typ.
          specialize (H nil (Z.to_nat 0)).
          rewrite Z2Nat.id in H. 2 : lia.
          destruct t; inv H1;
              try
                (apply H;
                 [constructor | constructor |
                  unfold vector_dtyp; intuition]).
          destruct (default_dvalue_of_dtyp_i sz) eqn: HI; inv H2.
          apply H. constructor. auto. unfold vector_dtyp. left.
          exists sz. reflexivity.
        + intros. cbn in H1.
          destruct t; inv H1; try (
            rewrite <- positive_nat_Z;
                   constructor; [apply forall_repeat_true ; constructor |
                          apply repeat_length |
                          unfold vector_dtyp ; intuition ]).
          destruct (default_dvalue_of_dtyp_i sz) eqn: SZ; inv H0.
            pose proof DVALUE_Vector_typ.
            rewrite <- positive_nat_Z. apply H.
            apply forall_repeat_true. apply IHt. symmetry. auto.
            apply repeat_length.
            left. exists sz. reflexivity.
        + intros. inv H1. destruct t; inv H0.
    Qed.

   Transparent map_monad.
   Lemma concretize_u_concretize_uvalue : forall u, concretize_u u (concretize_uvalue u).
    Proof.
      intros u.
      induction u; try do_it.

      - cbn. destruct (default_dvalue_of_dtyp t) eqn: EQ.
        econstructor. Unshelve. 3 : { exact DVALUE_None. }
        intro. inv H.
        apply Concretize_Undef. apply dvalue_default. symmetry. auto.
      - cbn. induction fields.
        + cbn. constructor. auto.
        + rewrite list_cons_app. rewrite map_monad_app. cbn.
          assert (IN: forall u : uvalue, In u fields -> concretize_u u (concretize_uvalue u)).
          { intros. apply H. apply in_cons; auto. } specialize (IHfields IN).
          specialize (H a). assert (In a (a :: fields)) by apply in_eq. specialize (H H0).
          pose proof Concretize_Struct_Cons as CONS.
          specialize (CONS _ _ _ _ H IHfields). cbn in CONS.
          * destruct (unEitherT (concretize_uvalue a)).
            -- auto.
            -- destruct s; auto.
               destruct (unEitherT (map_monad concretize_uvalue fields)); auto.
               destruct s; auto.
      - cbn. induction fields.
        + cbn. constructor. auto.
        + rewrite list_cons_app. rewrite map_monad_app. cbn.
          assert (IN: forall u : uvalue, In u fields -> concretize_u u (concretize_uvalue u)).
          { intros. apply H. apply in_cons; auto. } specialize (IHfields IN).
          specialize (H a). assert (In a (a :: fields)) by apply in_eq. specialize (H H0).
          pose proof Concretize_Packed_struct_Cons as CONS.
          specialize (CONS _ _ _ _ H IHfields). cbn in CONS.
          * destruct (unEitherT (concretize_uvalue a)).
            -- auto.
            -- destruct s; auto.
               destruct (unEitherT (map_monad concretize_uvalue fields)); auto.
               destruct s; auto.
      - cbn. induction elts.
        + cbn. constructor. auto.
        + rewrite list_cons_app. rewrite map_monad_app. cbn.
          assert (IN: forall u : uvalue, In u elts -> concretize_u u (concretize_uvalue u)).
          { intros. apply H. apply in_cons; auto. } specialize (IHelts IN).
          specialize (H a). assert (In a (a :: elts)) by apply in_eq. specialize (H H0).
          pose proof Concretize_Array_Cons as CONS.
          specialize (CONS _ _ _ _ H IHelts). cbn in CONS.
          * destruct (unEitherT (concretize_uvalue a)).
            -- auto.
            -- destruct s; auto.
               destruct (unEitherT (map_monad concretize_uvalue elts)); auto.
               destruct s; auto.
      - cbn. induction elts.
        + cbn. constructor. auto.
        + rewrite list_cons_app. rewrite map_monad_app. cbn.
          assert (IN: forall u : uvalue, In u elts -> concretize_u u (concretize_uvalue u)).
          { intros. apply H. apply in_cons; auto. } specialize (IHelts IN).
          specialize (H a). assert (In a (a :: elts)) by apply in_eq. specialize (H H0).
          pose proof Concretize_Vector_Cons as CONS.
          specialize (CONS _ _ _ _ H IHelts). cbn in CONS.
          * destruct (unEitherT (concretize_uvalue a)).
            -- auto.
            -- destruct s; auto.
               destruct (unEitherT (map_monad concretize_uvalue elts)); auto.
               destruct s; auto.
      - cbn; apply (Pick_fail (v := DVALUE_None)); intro H'; inv H'.
      - cbn; apply (Pick_fail (v := DVALUE_None)); intro H'; inv H'.
      - cbn; apply (Pick_fail (v := DVALUE_None)); intro H'; inv H'.
      - cbn; apply (Pick_fail (v := DVALUE_None)); intro H'; inv H'.
      - cbn; apply (Pick_fail (v := DVALUE_None)); intro H'; inv H'.
      - cbn; apply (Pick_fail (v := DVALUE_None)); intro H'; inv H'.
      - cbn; apply (Pick_fail (v := DVALUE_None)); intro H'; inv H'.
      - cbn; apply (Pick_fail (v := DVALUE_None)); intro H'; inv H'.
    Qed.

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
