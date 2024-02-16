(* begin hide *)
From Coq Require Import
  ZArith
  String
  List
  Lia
  Relations
  RelationClasses
  Morphisms.

From ExtLib Require Import
  Structures.Monads
  Structures.Maps.

From ITree Require Import
  ITree
  Eq.Eqit
  Events.State.

From Vellvm Require Import
  Utilities
  Syntax.LLVMAst
  Syntax.AstLib
  Syntax.DynamicTypes
  Syntax.DataLayout
  Semantics.DynamicValues
  Semantics.MemoryAddress
  Semantics.GepM
  Semantics.Memory.Sizeof
  Semantics.Memory.MemBytes
  Semantics.LLVMEvents
  Semantics.LLVMParams
  Semantics.MemoryParams
  Semantics.Memory.MemBytes
  Semantics.ConcretizationParams
  Handlers.Concretization
  ErrUbOomProp.

From Vellvm.Utils Require Import
  InterpPropOOM.

From ExtLib Require Import
  Data.Monads.EitherMonad
  Data.Monads.IdentityMonad
  Structures.Functor.

Set Implicit Arguments.
Set Contextual Implicit.

Import MonadNotation.
(* end hide *)

(** * Pick handler
  Definition of the propositional and executable handlers for the [Pick] event.
  - The propositional one capture in [Prop] all possible values
  - The executable one interprets [undef] as 0 at the type
 *)
Module Make (LP : LLVMParams) (MP : MemoryParams LP) (Byte : ByteModule LP.ADDR LP.IP LP.SIZEOF LP.Events MP.BYTE_IMPL) (CP : ConcretizationParams LP MP Byte).
  Import CP.
  Import CONC.
  Import MP.
  Import LP.
  Import Events.

  Section PickPropositional.

    (* No UB, and the result is unique or the concretization fails *)
    Definition unique_prop (uv : uvalue) : Prop
      := (forall ub_msg, ~ concretize_u uv (UB_unERR_UB_OOM ub_msg)) /\
           (forall err_msg, ~ concretize_u uv (ERR_unERR_UB_OOM err_msg)) /\
           ((exists x, concretize uv x /\ forall dv, concretize uv dv -> dv = x) \/
              (forall dv, ~ concretize uv dv)).

    (* No UB or failure, and the result is not a poison value  *)
    Definition non_poison_prop (uv : uvalue) : Prop
      := (forall ub_msg, ~ concretize_u uv (UB_unERR_UB_OOM ub_msg)) /\
           (forall err_msg, ~ concretize_u uv (ERR_unERR_UB_OOM err_msg)) /\
           (forall dt, ~concretize uv (DVALUE_Poison dt)).

    Program Definition lift_err_ub_oom_post {A B} {E} `{FailureE -< E} `{UBE -< E} `{OOME -< E} (m:err_ub_oom A) (Post : B -> Prop) (f : forall (a : A), m = ret a -> itree E {b : B | Post b}) : itree E {b : B | Post b} :=
      match m with
      | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
          match m with
          | inl (OOM_message x) => raiseOOM x
          | inr (inl (UB_message x)) => raiseUB x
          | inr (inr (inl (ERR_message x))) => raise x
          | inr (inr (inr x)) => f x _
          end
      end.

    Arguments lift_err_ub_oom_post {_ _ _ _ _ _} _ _ _.

    Program Definition lift_err_ub_oom_post_ret
      {E} `{FE:FailureE -< E} `{FO:UBE -< E} `{OO: OOME -< E}
      {X Y} (f : X -> Y) (res : err_ub_oom X) (Post : Y -> Prop)
      (P : forall (y : Y), fmap f res = ret y -> Post y)
      : itree E {y : Y | Post y}
      := lift_err_ub_oom_post res Post _.
    Next Obligation.
      cbn in *.
      apply ret.
      econstructor; eauto.
    Defined.

    Arguments lift_err_ub_oom_post_ret {_ _ _ _ _ _} _ _ _.


    Inductive PickUvalue_handler  {E} `{FE:FailureE -< E} `{FO:UBE -< E} `{OO: OOME -< E} : PickUvalueE ~> PropT E :=
    | PickUV_UniqueUB : forall x t,
        ~ (unique_prop x) ->
        PickUvalue_handler (@pickUnique _ _ (fun _ _ => True) x) t
    | PickUV_UniqueRet :
      forall x (res : err_ub_oom dvalue) (t : itree E {y : dvalue | True})
        (Conc : concretize_u x res),
        unique_prop x ->
        t ≈ lift_err_ub_oom_post_ret id res (fun _ => True) (fun (dv : dvalue) (_ : fmap id res = ret dv) => I) ->
        PickUvalue_handler (@pickUnique _ _ (fun _ _ => True) x) t
    | PickUV_NonPoisonUB : forall x t,
        ~ (non_poison_prop x) ->
        PickUvalue_handler (@pickNonPoison _ _ (fun _ _ => True) x) t
    | PickUV_NonPoisonRet :
      forall x (res : err_ub_oom dvalue) (t : itree E {y : dvalue | True})
        (Conc : concretize_u x res),
        non_poison_prop x ->
        t ≈ lift_err_ub_oom_post_ret id res (fun _ => True) (fun (dv : dvalue) (_ : fmap id res = ret dv) => I) ->
        PickUvalue_handler (@pickNonPoison _ _ (fun _ _ => True) x) t
    | PickUV_Ret :
      forall x (res : err_ub_oom dvalue) (t : itree E {y : dvalue | True})
        (Conc : concretize_u x res),
        t ≈ lift_err_ub_oom_post_ret id res (fun _ => True) (fun (dv : dvalue) (_ : fmap id res = ret dv) => I) ->
        PickUvalue_handler (@pick _ _ (fun _ _ => True) x) t.

    Section PARAMS_MODEL.
      Variable (E F: Type -> Type).

      Definition E_trigger_prop : E ~> PropT (E +' F) :=
        fun R e => fun t => t ≈ r <- trigger e ;; ret r.

      Definition F_trigger_prop : F ~> PropT (E +' F) :=
        fun R e => fun t => t ≈ r <- trigger e ;; ret r.

      Require Import ContainsUB.
      Definition model_undef_k_spec
        `{UB: UBE -< E +' F}
        {T R : Type}
        (e : (E +' PickUvalueE +' F) T)
        (ta : itree (E +' F) T)
        (k2 : T -> itree (E +' F) R)
        (t2 : itree (E +' F) R) : Prop
        := contains_UB ta \/ eutt eq t2 (bind ta k2).

      #[global] Instance k_spec_WF_model_undef_k_spec `{FAIL: FailureE -< E +' F} `{UB: UBE -< E +' F} `{OOM_OUT : OOME -< F} : k_spec_WF (case_ E_trigger_prop (case_ PickUvalue_handler F_trigger_prop)) (@model_undef_k_spec UB).
      Proof using.
        split.
        - intros A R2 e ta k2.
          unfold Proper, respectful.
          intros x y H.
          unfold model_undef_k_spec.
          split; intros [? | ?]; eauto.
          + right. setoid_rewrite <- H.
            auto.
          + right. setoid_rewrite H.
            auto.
        - unfold model_undef_k_spec.
          red.
          intros T R2 e k2 t2 ta H H0.
          auto.
      Defined.

      Definition model_undef_h `{FAIL: FailureE -< E +' F} `{UB: UBE -< E +' F} `{OOM_OUT : OOME -< F} {R1 R2} (RR : R1 -> R2 -> Prop) :=
        interp_prop_oom_r (OOM:=OOME) (case_ E_trigger_prop (case_ PickUvalue_handler F_trigger_prop)) RR (@model_undef_k_spec UB).

      Definition model_undef `{FailureE -< E +' F} `{UBE -< E +' F} `{OOME -< F}
        {T} (RR : T -> T -> Prop) (ts : PropT (E +' PickUvalueE +' F) T) : PropT (E +' F) T:=
        fun t_picked => exists t_pre, ts t_pre /\ model_undef_h RR t_pre t_picked.
    End PARAMS_MODEL.

  End PickPropositional.

  Section PickImplementation.

    Open Scope N_scope.

    Import MonadNotation.

    Transparent map_monad.

    (* TODO: Move these *)
    Lemma default_dvalue_of_dtyp_i_not_poison :
      forall sz d t,
        default_dvalue_of_dtyp_i sz = inr d ->
        d <> DVALUE_Poison t.
    Proof.
      intros sz d t H.
      unfold default_dvalue_of_dtyp_i in *.
      repeat break_match_hyp_inv; discriminate.
    Qed.

    Lemma default_dvalue_of_dtyp_not_poison :
      forall t d t',
        default_dvalue_of_dtyp t = inr d ->
        d <> DVALUE_Poison t'.
    Proof.
      intros t d t' H.
      destruct t; cbn in *; inv H;
        try break_match_hyp_inv; try discriminate.
      - eapply default_dvalue_of_dtyp_i_not_poison; eauto.
      - break_match_hyp_inv; discriminate.
    Qed.

    Lemma map_monad_concretize_u_concretize_uvalue :
      forall uvs
        (IH : forall u,
            Exists (uvalue_subterm u) uvs ->
            concretize_u u (concretize_uvalue u)),
        @map_monad ErrUbOomProp Monad_ErrUbOomProp _ _ concretize_u uvs (map_monad concretize_uvalue uvs).
    Proof.
      induction uvs; intros IH; try reflexivity.

      Import MapMonadExtra.
      repeat rewrite map_monad_unfold.
      cbn.

      unfold concretize_u, concretize_uvalue in *.
      match goal with
      | [ |- context [ match ?X with _ => _ end ] ] =>
          remember X
      end.

      exists e.
      exists (fun e0 =>
           match
             map_monad
               (fun x0 : uvalue =>
                  concretize_uvalueM err_ub_oom
                    (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
                    err_ub_oom (fun (A : Type) (x : err_ub_oom A) => x) x0) uvs
           with
           | {| unERR_UB_OOM := ma |} =>
               {|
                 unERR_UB_OOM :=
                   {|
                     unEitherT :=
                       {|
                         unEitherT :=
                           {|
                             unEitherT :=
                               match
                                 unIdent (unEitherT (unEitherT (unEitherT ma)))
                               with
                               | inl x => {| unIdent := inl x |}
                               | inr x =>
                                   unEitherT
                                     match x with
                                     | inl x0 =>
                                         {|
                                           unEitherT :=
                                             {| unIdent := inr (inl x0) |}
                                         |}
                                     | inr x0 =>
                                         unEitherT
                                           match x0 with
                                           | inl x1 =>
                                               {|
                                                 unEitherT :=
                                                   {|
                                                     unEitherT :=
                                                       {|
                                                         unIdent := inr (inr (inl x1))
                                                       |}
                                                   |}
                                               |}
                                           | inr x1 =>
                                               {|
                                                 unEitherT :=
                                                   {|
                                                     unEitherT :=
                                                       {|
                                                         unIdent :=
                                                           inr (inr (inr (e0 :: x1)))
                                                       |}
                                                   |}
                                               |}
                                           end
                                     end
                               end
                           |}
                       |}
                   |}
               |}
           end).
      split.
      { subst.
        apply IH.
        constructor.
        apply rt_refl.
      }

      destruct_err_ub_oom e; cbn; split; eauto.
      right.
      intros; subst.

      match goal with
      | [ |- context [ match ?X with _ => _ end ] ] =>
          remember X
      end.
      exists e.
      exists (fun _ => match e with
               | {| unERR_UB_OOM := ma |} =>
                   {|
                     unERR_UB_OOM :=
                       {|
                         unEitherT :=
                           {|
                             unEitherT :=
                               {|
                                 unEitherT :=
                                   match unIdent (unEitherT (unEitherT (unEitherT ma))) with
                                   | inl x => {| unIdent := inl x |}
                                   | inr x =>
                                       unEitherT
                                         match x with
                                         | inl x0 => {| unEitherT := {| unIdent := inr (inl x0) |} |}
                                         | inr x0 =>
                                             unEitherT
                                               match x0 with
                                               | inl x1 =>
                                                   {|
                                                     unEitherT :=
                                                       {| unEitherT := {| unIdent := inr (inr (inl x1)) |} |}
                                                   |}
                                               | inr x1 =>
                                                   {|
                                                     unEitherT :=
                                                       {|
                                                         unEitherT := {| unIdent := inr (inr (inr (a0 :: x1))) |}
                                                       |}
                                                   |}
                                               end
                                         end
                                   end
                               |}
                           |}
                       |}
                   |}
               end).
      split; cbn; eauto.          
      destruct_err_ub_oom e; cbn; try reflexivity; split; auto.

      right.
      intros; subst.
      reflexivity.
    Qed.

    Lemma concretize_uvalue_bytes_helper_concretize_uvalue_bytes_helper :
      forall uvs acc
        (IH : forall u,
            Exists (uvalue_subterm u) uvs ->
            concretize_u u (concretize_uvalue u)),
        @CONCBASE.concretize_uvalue_bytes_helper ErrUbOomProp Monad_ErrUbOomProp
          (fun (dt0 : dtyp) (edv : err_ub_oom dvalue) =>
             match @unERR_UB_OOM ident dvalue edv with
             | {| unEitherT := {| unEitherT := {| unEitherT := {| unIdent := inr (inr (inr dv)) |} |} |} |} =>
                 dvalue_has_dtyp dv dt0 /\ dv <> DVALUE_Poison dt0
             | _ => True
             end) err_ub_oom (@Monad_err_ub_oom ident Monad_ident) (@RAISE_ERROR_err_ub_oom ident Monad_ident)
          (@RAISE_UB_err_ub_oom_T ident Monad_ident) (@RAISE_OOM_err_ub_oom_T ident Monad_ident)
          (fun (A : Type) (x ue : err_ub_oom A) => x = ue) acc uvs
          (@CONCBASE.concretize_uvalue_bytes_helper err_ub_oom (@Monad_err_ub_oom ident Monad_ident)
             (fun dt0 : dtyp =>
                @lift_err_RAISE_ERROR dvalue err_ub_oom (@Monad_err_ub_oom ident Monad_ident)
                  (@RAISE_ERROR_err_ub_oom ident Monad_ident) (default_dvalue_of_dtyp dt0)) err_ub_oom
             (@Monad_err_ub_oom ident Monad_ident) (@RAISE_ERROR_err_ub_oom ident Monad_ident)
             (@RAISE_UB_err_ub_oom_T ident Monad_ident) (@RAISE_OOM_err_ub_oom_T ident Monad_ident)
             (fun (A : Type) (x : err_ub_oom A) => x) acc uvs).
    Proof.
      induction uvs;
        intros acc IH; try reflexivity.
      setoid_rewrite CONCBASE.concretize_uvalue_bytes_helper_equation.
      rewrite (@CONCBASE.concretize_uvalue_bytes_helper_equation ErrUbOomProp).
      destruct a; try reflexivity.
      break_match.
      - (* Pare-concretization exists *)
        cbn.
        exists (CONCBASE.concretize_uvalue_bytes_helper err_ub_oom
             (fun dt0 : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt0)) err_ub_oom
             (fun (A : Type) (x : err_ub_oom A) => x) acc uvs).
        exists (fun e0 => success_unERR_UB_OOM (DVALUE_BYTES.DVALUE_ExtractByte d dt idx :: e0)).
        split.
        { apply IHuvs.
          intros u H.
          eapply IH.
          right.
          auto.
        }

        split; cbn; eauto.
      - (* No pre-concretization exists *)
        cbn.
        match goal with
        | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
            exists (CONCBASE.concretize_uvalueM err_ub_oom
                 (fun dt0 : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt0)) err_ub_oom
                 (fun (A : Type) (x : err_ub_oom A) => x) a);
            exists (fun _ => res)
        end.
        split.

        { eapply IH.
          repeat constructor.
        }

        remember
          (CONCBASE.concretize_uvalueM err_ub_oom
             (fun dt0 : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt0)) err_ub_oom
             (fun (A : Type) (x : err_ub_oom A) => x) a).
        destruct_err_ub_oom e;
          split; cbn; eauto;
          try reflexivity.

        right.
        intros ? ?; subst.

        match goal with
        | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
            exists (CONCBASE.concretize_uvalue_bytes_helper err_ub_oom
                 (fun dt0 : dtyp =>
                    lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt0)) err_ub_oom
                 (fun (A : Type) (x : err_ub_oom A) => x)
                 (CONCBASE.new_concretized_byte acc a a0 sid) uvs);
            exists (fun _ => res)
        end.
        split; subst.

        { eapply IHuvs; eauto.
        }

        remember (CONCBASE.concretize_uvalue_bytes_helper err_ub_oom
                    (fun dt0 : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt0)) err_ub_oom
                    (fun (A : Type) (x : err_ub_oom A) => x) (CONCBASE.new_concretized_byte acc a a0 sid) uvs).
        destruct_err_ub_oom e; cbn; auto.
        split; eauto.

        right.
        intros a1 H; subst.
        reflexivity.
    Qed.

    Lemma concretize_uvalue_bytes_concretize_uvalue_bytes :
      forall uvs
        (IH : forall u,
            Exists (uvalue_subterm u) uvs ->
            concretize_u u (concretize_uvalue u)),
        @CONCBASE.concretize_uvalue_bytes ErrUbOomProp Monad_ErrUbOomProp
          (fun (dt0 : dtyp) (edv : err_ub_oom dvalue) =>
             match @unERR_UB_OOM ident dvalue edv with
             | {| unEitherT := {| unEitherT := {| unEitherT := {| unIdent := inr (inr (inr dv)) |} |} |} |} =>
                 dvalue_has_dtyp dv dt0 /\ dv <> DVALUE_Poison dt0
             | _ => True
             end) err_ub_oom (@Monad_err_ub_oom ident Monad_ident) (@RAISE_ERROR_err_ub_oom ident Monad_ident)
          (@RAISE_UB_err_ub_oom_T ident Monad_ident) (@RAISE_OOM_err_ub_oom_T ident Monad_ident)
          (fun (A : Type) (x ue : err_ub_oom A) => x = ue) uvs
          (@CONCBASE.concretize_uvalue_bytes err_ub_oom (@Monad_err_ub_oom ident Monad_ident)
             (fun dt0 : dtyp =>
                @lift_err_RAISE_ERROR dvalue err_ub_oom (@Monad_err_ub_oom ident Monad_ident)
                  (@RAISE_ERROR_err_ub_oom ident Monad_ident) (default_dvalue_of_dtyp dt0)) err_ub_oom
             (@Monad_err_ub_oom ident Monad_ident) (@RAISE_ERROR_err_ub_oom ident Monad_ident)
             (@RAISE_UB_err_ub_oom_T ident Monad_ident) (@RAISE_OOM_err_ub_oom_T ident Monad_ident)
             (fun (A : Type) (x : err_ub_oom A) => x) uvs).
    Proof.
      intros uvs IH.
      repeat rewrite CONCBASE.concretize_uvalue_bytes_equation.
      apply concretize_uvalue_bytes_helper_concretize_uvalue_bytes_helper; auto.
    Qed.

    Lemma extractbytes_to_dvalue_extractbytes_to_dvalue :
      forall uvs dt
        (IH : forall u,
            Exists (uvalue_subterm u) uvs ->
            concretize_u u (concretize_uvalue u)),
        @CONCBASE.extractbytes_to_dvalue ErrUbOomProp Monad_ErrUbOomProp
          (fun (dt0 : dtyp) (edv : err_ub_oom dvalue) =>
             match @unERR_UB_OOM ident dvalue edv with
             | {| unEitherT := {| unEitherT := {| unEitherT := {| unIdent := inr (inr (inr dv)) |} |} |} |} =>
                 dvalue_has_dtyp dv dt0 /\ dv <> DVALUE_Poison dt0
             | _ => True
             end) err_ub_oom (@Monad_err_ub_oom ident Monad_ident) (@RAISE_ERROR_err_ub_oom ident Monad_ident)
          (@RAISE_UB_err_ub_oom_T ident Monad_ident) (@RAISE_OOM_err_ub_oom_T ident Monad_ident)
          (fun (A : Type) (x ue : err_ub_oom A) => x = ue) uvs dt
          (@CONCBASE.extractbytes_to_dvalue err_ub_oom (@Monad_err_ub_oom ident Monad_ident)
             (fun dt0 : dtyp =>
                @lift_err_RAISE_ERROR dvalue err_ub_oom (@Monad_err_ub_oom ident Monad_ident)
                  (@RAISE_ERROR_err_ub_oom ident Monad_ident) (default_dvalue_of_dtyp dt0)) err_ub_oom
             (@Monad_err_ub_oom ident Monad_ident) (@RAISE_ERROR_err_ub_oom ident Monad_ident)
             (@RAISE_UB_err_ub_oom_T ident Monad_ident) (@RAISE_OOM_err_ub_oom_T ident Monad_ident)
             (fun (A : Type) (x : err_ub_oom A) => x) uvs dt).
    Proof.
      intros uvs dt IH.
      repeat rewrite CONCBASE.extractbytes_to_dvalue_equation.
      remember
        (CONCBASE.concretize_uvalue_bytes err_ub_oom
           (fun dt0 : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt0)) err_ub_oom
           (fun (A : Type) (x : err_ub_oom A) => x) uvs).
      cbn.
      match goal with
      | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
          exists e; exists (fun _ => res)
      end.
      split.

      subst.
      apply concretize_uvalue_bytes_concretize_uvalue_bytes; auto.

      destruct_err_ub_oom e; cbn; split; auto.
      right.
      intros ? ?; subst.
      remember ((ErrOomPoison.ErrOOMPoison_handle_poison_and_oom DVALUE_Poison
                   (DVALUE_BYTES.dvalue_bytes_to_dvalue a dt))).
      destruct_err_ub_oom y; reflexivity.
    Qed.

    Lemma eval_select_loop_eval_select_loop :
      forall elts elts0 elts1,
        ((fix loop (conds xs ys : list dvalue) {struct conds} : ErrUbOomProp (list dvalue) :=
            match conds with
            | nil =>
                match xs with
                | nil =>
                    fun ys0 : list dvalue =>
                      match ys0 with
                      | nil => fun y0 : err_ub_oom (list dvalue) => success_unERR_UB_OOM (@nil dvalue) = y0
                      | _ :: _ =>
                          fun ue : err_ub_oom (list dvalue) =>
                            ERR_unERR_UB_OOM "concretize_uvalueM: ill-typed vector select, length mismatch." =
                              ue
                      end
                | _ :: _ =>
                    fun (_ : list dvalue) (ue : err_ub_oom (list dvalue)) =>
                      ERR_unERR_UB_OOM "concretize_uvalueM: ill-typed vector select, length mismatch." = ue
                end ys
            | c :: conds0 =>
                match xs with
                | nil =>
                    fun ue : err_ub_oom (list dvalue) =>
                      ERR_unERR_UB_OOM "concretize_uvalueM: ill-typed vector select, length mismatch." = ue
                | x0 :: xs0 =>
                    match ys with
                    | nil =>
                        fun ue : err_ub_oom (list dvalue) =>
                          ERR_unERR_UB_OOM "concretize_uvalueM: ill-typed vector select, length mismatch." =
                            ue
                    | y0 :: ys0 =>
                        @bind_ErrUbOomProp dvalue (list dvalue)
                          match c with
                          | DVALUE_I1 i =>
                              if (VellvmIntegers.Int1.unsigned i =? 1)%Z
                              then fun y1 : err_ub_oom dvalue => success_unERR_UB_OOM x0 = y1
                              else fun y1 : err_ub_oom dvalue => success_unERR_UB_OOM y0 = y1
                          | DVALUE_Poison t =>
                              fun y1 : err_ub_oom dvalue => success_unERR_UB_OOM (DVALUE_Poison t) = y1
                          | _ =>
                              fun ue : err_ub_oom dvalue =>
                                ERR_unERR_UB_OOM
                                  "concretize_uvalueM: ill-typed select, condition in vector was not poison or i1." =
                                  ue
                          end
                          (fun selected : dvalue =>
                             @bind_ErrUbOomProp (list dvalue) (list dvalue) (loop conds0 xs0 ys0)
                               (fun (rest : list dvalue) (y1 : err_ub_oom (list dvalue)) =>
                                  success_unERR_UB_OOM (selected :: rest) = y1))
                    end
                end
            end) elts elts0 elts1)
          ((fix loop (conds xs ys : list dvalue) {struct conds} :
             err_ub_oom (list dvalue) :=
              match conds with
              | nil =>
                  match xs with
                  | nil =>
                      fun ys0 : list dvalue =>
                        match ys0 with
                        | nil => success_unERR_UB_OOM (@nil dvalue)
                        | _ :: _ =>
                            ERR_unERR_UB_OOM
                              "concretize_uvalueM: ill-typed vector select, length mismatch."
                        end
                  | _ :: _ =>
                      fun _ : list dvalue =>
                        ERR_unERR_UB_OOM
                          "concretize_uvalueM: ill-typed vector select, length mismatch."
                  end ys
              | c :: conds0 =>
                  match xs with
                  | nil =>
                      ERR_unERR_UB_OOM
                        "concretize_uvalueM: ill-typed vector select, length mismatch."
                  | x0 :: xs0 =>
                      match ys with
                      | nil =>
                          ERR_unERR_UB_OOM
                            "concretize_uvalueM: ill-typed vector select, length mismatch."
                      | y0 :: ys0 =>
                          match
                            match c with
                            | DVALUE_I1 i =>
                                if (VellvmIntegers.Int1.unsigned i =? 1)%Z
                                then success_unERR_UB_OOM x0
                                else success_unERR_UB_OOM y0
                            | DVALUE_Poison t =>
                                success_unERR_UB_OOM (DVALUE_Poison t)
                            | _ =>
                                ERR_unERR_UB_OOM
                                  "concretize_uvalueM: ill-typed select, condition in vector was not poison or i1."
                            end
                          with
                          | {| unERR_UB_OOM := ma |} =>
                              {|
                                unERR_UB_OOM :=
                                  {|
                                    unEitherT :=
                                      {|
                                        unEitherT :=
                                          {|
                                            unEitherT :=
                                              match
                                                @unIdent
                                                  (OOM_MESSAGE + UB (ERR dvalue))
                                                  (@unEitherT OOM_MESSAGE ident
                                                     (UB (ERR dvalue))
                                                     (@unEitherT UB_MESSAGE
                                                        (eitherT OOM_MESSAGE ident)
                                                        (ERR dvalue)
                                                        (@unEitherT ERR_MESSAGE
                                                           (eitherT UB_MESSAGE
                                                              (eitherT OOM_MESSAGE ident))
                                                           dvalue ma)))
                                              with
                                              | inl x1 =>
                                                  {|
                                                    unIdent :=
                                                      @inl OOM_MESSAGE
                                                        (UB (ERR (list dvalue))) x1
                                                  |}
                                              | inr x1 =>
                                                  @unEitherT OOM_MESSAGE ident
                                                    (UB (ERR (list dvalue)))
                                                    match x1 with
                                                    | inl x2 =>
                                                        {|
                                                          unEitherT :=
                                                            {|
                                                              unIdent :=
                                                                @inr OOM_MESSAGE
                                                                  (UB (ERR (list dvalue)))
                                                                  (@inl UB_MESSAGE
                                                                     (ERR (list dvalue)) x2)
                                                            |}
                                                        |}
                                                    | inr x2 =>
                                                        @unEitherT UB_MESSAGE
                                                          (eitherT OOM_MESSAGE ident)
                                                          (ERR (list dvalue))
                                                          match x2 with
                                                          | inl x3 =>
                                                              {|
                                                                unEitherT :=
                                                                  {|
                                                                    unEitherT :=
                                                                      {|
                                                                        unIdent :=
                                                                          @inr OOM_MESSAGE
                                                                            (UB (ERR (list dvalue)))
                                                                            (@inr UB_MESSAGE
                                                                               (ERR (list dvalue))
                                                                               (@inl ERR_MESSAGE
                                                                                  (list dvalue) x3))
                                                                      |}
                                                                  |}
                                                              |}
                                                          | inr x3 =>
                                                              @unEitherT ERR_MESSAGE
                                                                (eitherT UB_MESSAGE
                                                                   (eitherT OOM_MESSAGE ident))
                                                                (list dvalue)
                                                                (@unERR_UB_OOM ident
                                                                   (list dvalue)
                                                                   match
                                                                     loop conds0 xs0 ys0
                                                                   with
                                                                   | {| unERR_UB_OOM := ma0 |} =>
                                                                       {|
                                                                         unERR_UB_OOM :=
                                                                           {|
                                                                             unEitherT :=
                                                                               {|
                                                                                 unEitherT :=
                                                                                   {|
                                                                                     unEitherT :=
                                                                                       match
                                                                                         @unIdent
                                                                                           (OOM_MESSAGE +
                                                                                              UB (ERR (list dvalue)))
                                                                                           (@unEitherT OOM_MESSAGE ident
                                                                                              (UB (ERR (list dvalue)))
                                                                                              (@unEitherT UB_MESSAGE
                                                                                                 (eitherT OOM_MESSAGE ident)
                                                                                                 (ERR (list dvalue))
                                                                                                 (@unEitherT ERR_MESSAGE
                                                                                                    (eitherT UB_MESSAGE
                                                                                                       (eitherT OOM_MESSAGE ident))
                                                                                                    (list dvalue) ma0)))
                                                                                       with
                                                                                       | inl x4 =>
                                                                                           {|
                                                                                             unIdent :=
                                                                                               @inl OOM_MESSAGE
                                                                                                 (UB (ERR (list dvalue))) x4
                                                                                           |}
                                                                                       | inr x4 =>
                                                                                           @unEitherT OOM_MESSAGE ident
                                                                                             (UB (ERR (list dvalue)))
                                                                                             match x4 with
                                                                                             | inl x5 =>
                                                                                                 {|
                                                                                                   unEitherT :=
                                                                                                     {|
                                                                                                       unIdent :=
                                                                                                         @inr OOM_MESSAGE
                                                                                                           (UB (ERR (list dvalue)))
                                                                                                           (@inl UB_MESSAGE
                                                                                                              (ERR (list dvalue)) x5)
                                                                                                     |}
                                                                                                 |}
                                                                                             | inr x5 =>
                                                                                                 @unEitherT UB_MESSAGE
                                                                                                   (eitherT OOM_MESSAGE ident)
                                                                                                   (ERR (list dvalue))
                                                                                                   match x5 with
                                                                                                   | inl x6 =>
                                                                                                       {|
                                                                                                         unEitherT :=
                                                                                                           {|
                                                                                                             unEitherT :=
                                                                                                               {|
                                                                                                                 unIdent :=
                                                                                                                   @inr OOM_MESSAGE
                                                                                                                     (UB (ERR (list dvalue)))
                                                                                                                     (@inr UB_MESSAGE
                                                                                                                        (ERR (list dvalue))
                                                                                                                        (@inl ERR_MESSAGE
                                                                                                                           (list dvalue) x6))
                                                                                                               |}
                                                                                                           |}
                                                                                                       |}
                                                                                                   | inr x6 =>
                                                                                                       {|
                                                                                                         unEitherT :=
                                                                                                           {|
                                                                                                             unEitherT :=
                                                                                                               {|
                                                                                                                 unIdent :=
                                                                                                                   @inr OOM_MESSAGE
                                                                                                                     (UB (ERR (list dvalue)))
                                                                                                                     (@inr UB_MESSAGE
                                                                                                                        (ERR (list dvalue))
                                                                                                                        (@inr ERR_MESSAGE
                                                                                                                           (list dvalue) 
                                                                                                                           (x3 :: x6)))
                                                                                                               |}
                                                                                                           |}
                                                                                                       |}
                                                                                                   end
                                                                                             end
                                                                                       end
                                                                                   |}
                                                                               |}
                                                                           |}
                                                                       |}
                                                                   end)
                                                          end
                                                    end
                                              end
                                          |}
                                      |}
                                  |}
                              |}
                          end
                      end
                  end
              end) elts elts0 elts1).
    Proof.
      intros conds.
      induction conds;
        intros xs ys;
        cbn in *; subst; auto;
        try reflexivity;
        destruct xs, ys; try reflexivity.

      match goal with
      | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
          exists (match a with
             | DVALUE_I1 i =>
                 if (VellvmIntegers.Int1.unsigned i =? 1)%Z
                 then success_unERR_UB_OOM d
                 else success_unERR_UB_OOM d0
             | DVALUE_Poison t => success_unERR_UB_OOM (DVALUE_Poison t)
             | _ =>
                 ERR_unERR_UB_OOM
                   "concretize_uvalueM: ill-typed select, condition in vector was not poison or i1."
             end);
          exists (fun _ => res)
      end.
      split.
      { destruct a; try reflexivity.
        break_match; reflexivity.
      }

      split.
      { destruct a; try reflexivity.
        break_match; reflexivity.
      }

      { destruct a; try reflexivity; cbn; auto.
        - right.
          intros a H.
          break_match_hyp_inv.
          + specialize (IHconds xs ys).
            remember ((fix loop (conds xs ys : list dvalue) {struct conds} : err_ub_oom (list dvalue) :=
                         match conds with
                         | nil =>
                             match xs with
                             | nil =>
                                 fun ys0 : list dvalue =>
                                   match ys0 with
                                   | nil => success_unERR_UB_OOM (@nil dvalue)
                                   | _ :: _ =>
                                       ERR_unERR_UB_OOM
                                         "concretize_uvalueM: ill-typed vector select, length mismatch."
                                   end
                             | _ :: _ =>
                                 fun _ : list dvalue =>
                                   ERR_unERR_UB_OOM
                                     "concretize_uvalueM: ill-typed vector select, length mismatch."
                             end ys
                         | c :: conds0 =>
                             match xs with
                             | nil =>
                                 ERR_unERR_UB_OOM
                                   "concretize_uvalueM: ill-typed vector select, length mismatch."
                             | x0 :: xs0 =>
                                 match ys with
                                 | nil =>
                                     ERR_unERR_UB_OOM
                                       "concretize_uvalueM: ill-typed vector select, length mismatch."
                                 | y0 :: ys0 =>
                                     match
                                       match c with
                                       | DVALUE_I1 i =>
                                           if (VellvmIntegers.Int1.unsigned i =? 1)%Z
                                           then success_unERR_UB_OOM x0
                                           else success_unERR_UB_OOM y0
                                       | DVALUE_Poison t => success_unERR_UB_OOM (DVALUE_Poison t)
                                       | _ =>
                                           ERR_unERR_UB_OOM
                                             "concretize_uvalueM: ill-typed select, condition in vector was not poison or i1."
                                       end
                                     with
                                     | {| unERR_UB_OOM := ma |} =>
                                         {|
                                           unERR_UB_OOM :=
                                             {|
                                               unEitherT :=
                                                 {|
                                                   unEitherT :=
                                                     {|
                                                       unEitherT :=
                                                         match
                                                           @unIdent (OOM_MESSAGE + UB (ERR dvalue))
                                                             (@unEitherT OOM_MESSAGE ident 
                                                                (UB (ERR dvalue))
                                                                (@unEitherT UB_MESSAGE
                                                                   (eitherT OOM_MESSAGE ident) 
                                                                   (ERR dvalue)
                                                                   (@unEitherT ERR_MESSAGE
                                                                      (eitherT UB_MESSAGE
                                                                         (eitherT OOM_MESSAGE ident)) dvalue
                                                                      ma)))
                                                         with
                                                         | inl x1 =>
                                                             {|
                                                               unIdent :=
                                                                 @inl OOM_MESSAGE (UB (ERR (list dvalue))) x1
                                                             |}
                                                         | inr x1 =>
                                                             @unEitherT OOM_MESSAGE ident
                                                               (UB (ERR (list dvalue)))
                                                               match x1 with
                                                               | inl x2 =>
                                                                   {|
                                                                     unEitherT :=
                                                                       {|
                                                                         unIdent :=
                                                                           @inr OOM_MESSAGE
                                                                             (UB (ERR (list dvalue)))
                                                                             (@inl UB_MESSAGE
                                                                                (ERR (list dvalue)) x2)
                                                                       |}
                                                                   |}
                                                               | inr x2 =>
                                                                   @unEitherT UB_MESSAGE
                                                                     (eitherT OOM_MESSAGE ident)
                                                                     (ERR (list dvalue))
                                                                     match x2 with
                                                                     | inl x3 =>
                                                                         {|
                                                                           unEitherT :=
                                                                             {|
                                                                               unEitherT :=
                                                                                 {|
                                                                                   unIdent :=
                                                                                     @inr OOM_MESSAGE
                                                                                       (UB (ERR (list dvalue)))
                                                                                       (@inr UB_MESSAGE
                                                                                          (ERR (list dvalue))
                                                                                          (@inl ERR_MESSAGE
                                                                                             (list dvalue) x3))
                                                                                 |}
                                                                             |}
                                                                         |}
                                                                     | inr x3 =>
                                                                         @unEitherT ERR_MESSAGE
                                                                           (eitherT UB_MESSAGE
                                                                              (eitherT OOM_MESSAGE ident))
                                                                           (list dvalue)
                                                                           (@unERR_UB_OOM ident 
                                                                              (list dvalue)
                                                                              match loop conds0 xs0 ys0 with
                                                                              | {| unERR_UB_OOM := ma0 |} =>
                                                                                  {|
                                                                                    unERR_UB_OOM :=
                                                                                      {|
                                                                                        unEitherT :=
                                                                                          {|
                                                                                            unEitherT :=
                                                                                              {|
                                                                                                unEitherT :=
                                                                                                  match
                                                                                                    @unIdent
                                                                                                      (OOM_MESSAGE +
                                                                                                         UB (ERR (list dvalue)))
                                                                                                      (@unEitherT OOM_MESSAGE ident
                                                                                                         (UB (ERR (list dvalue)))
                                                                                                         (@unEitherT UB_MESSAGE
                                                                                                            (eitherT OOM_MESSAGE ident)
                                                                                                            (ERR (list dvalue))
                                                                                                            (@unEitherT ERR_MESSAGE
                                                                                                               (eitherT UB_MESSAGE
                                                                                                                  (eitherT OOM_MESSAGE ident))
                                                                                                               (list dvalue) ma0)))
                                                                                                  with
                                                                                                  | inl x4 =>
                                                                                                      {|
                                                                                                        unIdent :=
                                                                                                          @inl OOM_MESSAGE
                                                                                                            (UB (ERR (list dvalue))) x4
                                                                                                      |}
                                                                                                  | inr x4 =>
                                                                                                      @unEitherT OOM_MESSAGE ident
                                                                                                        (UB (ERR (list dvalue)))
                                                                                                        match x4 with
                                                                                                        | inl x5 =>
                                                                                                            {|
                                                                                                              unEitherT :=
                                                                                                                {|
                                                                                                                  unIdent :=
                                                                                                                    @inr OOM_MESSAGE
                                                                                                                      (UB (ERR (list dvalue)))
                                                                                                                      (@inl UB_MESSAGE
                                                                                                                         (ERR (list dvalue)) x5)
                                                                                                                |}
                                                                                                            |}
                                                                                                        | inr x5 =>
                                                                                                            @unEitherT UB_MESSAGE
                                                                                                              (eitherT OOM_MESSAGE ident)
                                                                                                              (ERR (list dvalue))
                                                                                                              match x5 with
                                                                                                              | inl x6 =>
                                                                                                                  {|
                                                                                                                    unEitherT :=
                                                                                                                      {|
                                                                                                                        unEitherT :=
                                                                                                                          {|
                                                                                                                            unIdent :=
                                                                                                                              @inr OOM_MESSAGE
                                                                                                                                (UB (ERR (list dvalue)))
                                                                                                                                (@inr UB_MESSAGE
                                                                                                                                   (ERR (list dvalue))
                                                                                                                                   (@inl ERR_MESSAGE
                                                                                                                                      (list dvalue) x6))
                                                                                                                          |}
                                                                                                                      |}
                                                                                                                  |}
                                                                                                              | inr x6 =>
                                                                                                                  {|
                                                                                                                    unEitherT :=
                                                                                                                      {|
                                                                                                                        unEitherT :=
                                                                                                                          {|
                                                                                                                            unIdent :=
                                                                                                                              @inr OOM_MESSAGE
                                                                                                                                (UB (ERR (list dvalue)))
                                                                                                                                (@inr UB_MESSAGE
                                                                                                                                   (ERR (list dvalue))
                                                                                                                                   (@inr ERR_MESSAGE
                                                                                                                                      (list dvalue) 
                                                                                                                                      (x3 :: x6)))
                                                                                                                          |}
                                                                                                                      |}
                                                                                                                  |}
                                                                                                              end
                                                                                                        end
                                                                                                  end
                                                                                              |}
                                                                                          |}
                                                                                      |}
                                                                                  |}
                                                                              end)
                                                                     end
                                                               end
                                                         end
                                                     |}
                                                 |}
                                             |}
                                         |}
                                     end
                                 end
                             end
                         end) conds xs ys).
            match goal with
            | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
                exists e;
                exists (fun _ => res)
            end.
            split; auto.
            split.
            { destruct_err_ub_oom e; cbn; auto.
            }

            destruct_err_ub_oom e; cbn; auto.
            right.
            intros ? ?; subst; auto.
          + specialize (IHconds xs ys).
            remember ((fix loop (conds xs ys : list dvalue) {struct conds} : err_ub_oom (list dvalue) :=
                         match conds with
                         | nil =>
                             match xs with
                             | nil =>
                                 fun ys0 : list dvalue =>
                                   match ys0 with
                                   | nil => success_unERR_UB_OOM (@nil dvalue)
                                   | _ :: _ =>
                                       ERR_unERR_UB_OOM
                                         "concretize_uvalueM: ill-typed vector select, length mismatch."
                                   end
                             | _ :: _ =>
                                 fun _ : list dvalue =>
                                   ERR_unERR_UB_OOM
                                     "concretize_uvalueM: ill-typed vector select, length mismatch."
                             end ys
                         | c :: conds0 =>
                             match xs with
                             | nil =>
                                 ERR_unERR_UB_OOM
                                   "concretize_uvalueM: ill-typed vector select, length mismatch."
                             | x0 :: xs0 =>
                                 match ys with
                                 | nil =>
                                     ERR_unERR_UB_OOM
                                       "concretize_uvalueM: ill-typed vector select, length mismatch."
                                 | y0 :: ys0 =>
                                     match
                                       match c with
                                       | DVALUE_I1 i =>
                                           if (VellvmIntegers.Int1.unsigned i =? 1)%Z
                                           then success_unERR_UB_OOM x0
                                           else success_unERR_UB_OOM y0
                                       | DVALUE_Poison t => success_unERR_UB_OOM (DVALUE_Poison t)
                                       | _ =>
                                           ERR_unERR_UB_OOM
                                             "concretize_uvalueM: ill-typed select, condition in vector was not poison or i1."
                                       end
                                     with
                                     | {| unERR_UB_OOM := ma |} =>
                                         {|
                                           unERR_UB_OOM :=
                                             {|
                                               unEitherT :=
                                                 {|
                                                   unEitherT :=
                                                     {|
                                                       unEitherT :=
                                                         match
                                                           @unIdent (OOM_MESSAGE + UB (ERR dvalue))
                                                             (@unEitherT OOM_MESSAGE ident 
                                                                (UB (ERR dvalue))
                                                                (@unEitherT UB_MESSAGE
                                                                   (eitherT OOM_MESSAGE ident) 
                                                                   (ERR dvalue)
                                                                   (@unEitherT ERR_MESSAGE
                                                                      (eitherT UB_MESSAGE
                                                                         (eitherT OOM_MESSAGE ident)) dvalue
                                                                      ma)))
                                                         with
                                                         | inl x1 =>
                                                             {|
                                                               unIdent :=
                                                                 @inl OOM_MESSAGE (UB (ERR (list dvalue))) x1
                                                             |}
                                                         | inr x1 =>
                                                             @unEitherT OOM_MESSAGE ident
                                                               (UB (ERR (list dvalue)))
                                                               match x1 with
                                                               | inl x2 =>
                                                                   {|
                                                                     unEitherT :=
                                                                       {|
                                                                         unIdent :=
                                                                           @inr OOM_MESSAGE
                                                                             (UB (ERR (list dvalue)))
                                                                             (@inl UB_MESSAGE
                                                                                (ERR (list dvalue)) x2)
                                                                       |}
                                                                   |}
                                                               | inr x2 =>
                                                                   @unEitherT UB_MESSAGE
                                                                     (eitherT OOM_MESSAGE ident)
                                                                     (ERR (list dvalue))
                                                                     match x2 with
                                                                     | inl x3 =>
                                                                         {|
                                                                           unEitherT :=
                                                                             {|
                                                                               unEitherT :=
                                                                                 {|
                                                                                   unIdent :=
                                                                                     @inr OOM_MESSAGE
                                                                                       (UB (ERR (list dvalue)))
                                                                                       (@inr UB_MESSAGE
                                                                                          (ERR (list dvalue))
                                                                                          (@inl ERR_MESSAGE
                                                                                             (list dvalue) x3))
                                                                                 |}
                                                                             |}
                                                                         |}
                                                                     | inr x3 =>
                                                                         @unEitherT ERR_MESSAGE
                                                                           (eitherT UB_MESSAGE
                                                                              (eitherT OOM_MESSAGE ident))
                                                                           (list dvalue)
                                                                           (@unERR_UB_OOM ident 
                                                                              (list dvalue)
                                                                              match loop conds0 xs0 ys0 with
                                                                              | {| unERR_UB_OOM := ma0 |} =>
                                                                                  {|
                                                                                    unERR_UB_OOM :=
                                                                                      {|
                                                                                        unEitherT :=
                                                                                          {|
                                                                                            unEitherT :=
                                                                                              {|
                                                                                                unEitherT :=
                                                                                                  match
                                                                                                    @unIdent
                                                                                                      (OOM_MESSAGE +
                                                                                                         UB (ERR (list dvalue)))
                                                                                                      (@unEitherT OOM_MESSAGE ident
                                                                                                         (UB (ERR (list dvalue)))
                                                                                                         (@unEitherT UB_MESSAGE
                                                                                                            (eitherT OOM_MESSAGE ident)
                                                                                                            (ERR (list dvalue))
                                                                                                            (@unEitherT ERR_MESSAGE
                                                                                                               (eitherT UB_MESSAGE
                                                                                                                  (eitherT OOM_MESSAGE ident))
                                                                                                               (list dvalue) ma0)))
                                                                                                  with
                                                                                                  | inl x4 =>
                                                                                                      {|
                                                                                                        unIdent :=
                                                                                                          @inl OOM_MESSAGE
                                                                                                            (UB (ERR (list dvalue))) x4
                                                                                                      |}
                                                                                                  | inr x4 =>
                                                                                                      @unEitherT OOM_MESSAGE ident
                                                                                                        (UB (ERR (list dvalue)))
                                                                                                        match x4 with
                                                                                                        | inl x5 =>
                                                                                                            {|
                                                                                                              unEitherT :=
                                                                                                                {|
                                                                                                                  unIdent :=
                                                                                                                    @inr OOM_MESSAGE
                                                                                                                      (UB (ERR (list dvalue)))
                                                                                                                      (@inl UB_MESSAGE
                                                                                                                         (ERR (list dvalue)) x5)
                                                                                                                |}
                                                                                                            |}
                                                                                                        | inr x5 =>
                                                                                                            @unEitherT UB_MESSAGE
                                                                                                              (eitherT OOM_MESSAGE ident)
                                                                                                              (ERR (list dvalue))
                                                                                                              match x5 with
                                                                                                              | inl x6 =>
                                                                                                                  {|
                                                                                                                    unEitherT :=
                                                                                                                      {|
                                                                                                                        unEitherT :=
                                                                                                                          {|
                                                                                                                            unIdent :=
                                                                                                                              @inr OOM_MESSAGE
                                                                                                                                (UB (ERR (list dvalue)))
                                                                                                                                (@inr UB_MESSAGE
                                                                                                                                   (ERR (list dvalue))
                                                                                                                                   (@inl ERR_MESSAGE
                                                                                                                                      (list dvalue) x6))
                                                                                                                          |}
                                                                                                                      |}
                                                                                                                  |}
                                                                                                              | inr x6 =>
                                                                                                                  {|
                                                                                                                    unEitherT :=
                                                                                                                      {|
                                                                                                                        unEitherT :=
                                                                                                                          {|
                                                                                                                            unIdent :=
                                                                                                                              @inr OOM_MESSAGE
                                                                                                                                (UB (ERR (list dvalue)))
                                                                                                                                (@inr UB_MESSAGE
                                                                                                                                   (ERR (list dvalue))
                                                                                                                                   (@inr ERR_MESSAGE
                                                                                                                                      (list dvalue) 
                                                                                                                                      (x3 :: x6)))
                                                                                                                          |}
                                                                                                                      |}
                                                                                                                  |}
                                                                                                              end
                                                                                                        end
                                                                                                  end
                                                                                              |}
                                                                                          |}
                                                                                      |}
                                                                                  |}
                                                                              end)
                                                                     end
                                                               end
                                                         end
                                                     |}
                                                 |}
                                             |}
                                         |}
                                     end
                                 end
                             end
                         end) conds xs ys).
            match goal with
            | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
                exists e;
                exists (fun _ => res)
            end.
            split; auto.
            split.
            { destruct_err_ub_oom e; cbn; auto.
            }

            destruct_err_ub_oom e; cbn; auto.
            right.
            intros ? ?; subst; auto.
        - right.
          intros a H; subst; cbn.
          specialize (IHconds xs ys).
          remember ((fix loop (conds xs ys : list dvalue) {struct conds} : err_ub_oom (list dvalue) :=
                       match conds with
                       | nil =>
                           match xs with
                           | nil =>
                               fun ys0 : list dvalue =>
                                 match ys0 with
                                 | nil => success_unERR_UB_OOM (@nil dvalue)
                                 | _ :: _ =>
                                     ERR_unERR_UB_OOM
                                       "concretize_uvalueM: ill-typed vector select, length mismatch."
                                 end
                           | _ :: _ =>
                               fun _ : list dvalue =>
                                 ERR_unERR_UB_OOM
                                   "concretize_uvalueM: ill-typed vector select, length mismatch."
                           end ys
                       | c :: conds0 =>
                           match xs with
                           | nil =>
                               ERR_unERR_UB_OOM
                                 "concretize_uvalueM: ill-typed vector select, length mismatch."
                           | x0 :: xs0 =>
                               match ys with
                               | nil =>
                                   ERR_unERR_UB_OOM
                                     "concretize_uvalueM: ill-typed vector select, length mismatch."
                               | y0 :: ys0 =>
                                   match
                                     match c with
                                     | DVALUE_I1 i =>
                                         if (VellvmIntegers.Int1.unsigned i =? 1)%Z
                                         then success_unERR_UB_OOM x0
                                         else success_unERR_UB_OOM y0
                                     | DVALUE_Poison t => success_unERR_UB_OOM (DVALUE_Poison t)
                                     | _ =>
                                         ERR_unERR_UB_OOM
                                           "concretize_uvalueM: ill-typed select, condition in vector was not poison or i1."
                                     end
                                   with
                                   | {| unERR_UB_OOM := ma |} =>
                                       {|
                                         unERR_UB_OOM :=
                                           {|
                                             unEitherT :=
                                               {|
                                                 unEitherT :=
                                                   {|
                                                     unEitherT :=
                                                       match
                                                         @unIdent (OOM_MESSAGE + UB (ERR dvalue))
                                                           (@unEitherT OOM_MESSAGE ident 
                                                              (UB (ERR dvalue))
                                                              (@unEitherT UB_MESSAGE
                                                                 (eitherT OOM_MESSAGE ident) 
                                                                 (ERR dvalue)
                                                                 (@unEitherT ERR_MESSAGE
                                                                    (eitherT UB_MESSAGE
                                                                       (eitherT OOM_MESSAGE ident)) dvalue
                                                                    ma)))
                                                       with
                                                       | inl x1 =>
                                                           {|
                                                             unIdent :=
                                                               @inl OOM_MESSAGE (UB (ERR (list dvalue))) x1
                                                           |}
                                                       | inr x1 =>
                                                           @unEitherT OOM_MESSAGE ident
                                                             (UB (ERR (list dvalue)))
                                                             match x1 with
                                                             | inl x2 =>
                                                                 {|
                                                                   unEitherT :=
                                                                     {|
                                                                       unIdent :=
                                                                         @inr OOM_MESSAGE
                                                                           (UB (ERR (list dvalue)))
                                                                           (@inl UB_MESSAGE
                                                                              (ERR (list dvalue)) x2)
                                                                     |}
                                                                 |}
                                                             | inr x2 =>
                                                                 @unEitherT UB_MESSAGE
                                                                   (eitherT OOM_MESSAGE ident)
                                                                   (ERR (list dvalue))
                                                                   match x2 with
                                                                   | inl x3 =>
                                                                       {|
                                                                         unEitherT :=
                                                                           {|
                                                                             unEitherT :=
                                                                               {|
                                                                                 unIdent :=
                                                                                   @inr OOM_MESSAGE
                                                                                     (UB (ERR (list dvalue)))
                                                                                     (@inr UB_MESSAGE
                                                                                        (ERR (list dvalue))
                                                                                        (@inl ERR_MESSAGE
                                                                                           (list dvalue) x3))
                                                                               |}
                                                                           |}
                                                                       |}
                                                                   | inr x3 =>
                                                                       @unEitherT ERR_MESSAGE
                                                                         (eitherT UB_MESSAGE
                                                                            (eitherT OOM_MESSAGE ident))
                                                                         (list dvalue)
                                                                         (@unERR_UB_OOM ident 
                                                                            (list dvalue)
                                                                            match loop conds0 xs0 ys0 with
                                                                            | {| unERR_UB_OOM := ma0 |} =>
                                                                                {|
                                                                                  unERR_UB_OOM :=
                                                                                    {|
                                                                                      unEitherT :=
                                                                                        {|
                                                                                          unEitherT :=
                                                                                            {|
                                                                                              unEitherT :=
                                                                                                match
                                                                                                  @unIdent
                                                                                                    (OOM_MESSAGE +
                                                                                                       UB (ERR (list dvalue)))
                                                                                                    (@unEitherT OOM_MESSAGE ident
                                                                                                       (UB (ERR (list dvalue)))
                                                                                                       (@unEitherT UB_MESSAGE
                                                                                                          (eitherT OOM_MESSAGE ident)
                                                                                                          (ERR (list dvalue))
                                                                                                          (@unEitherT ERR_MESSAGE
                                                                                                             (eitherT UB_MESSAGE
                                                                                                                (eitherT OOM_MESSAGE ident))
                                                                                                             (list dvalue) ma0)))
                                                                                                with
                                                                                                | inl x4 =>
                                                                                                    {|
                                                                                                      unIdent :=
                                                                                                        @inl OOM_MESSAGE
                                                                                                          (UB (ERR (list dvalue))) x4
                                                                                                    |}
                                                                                                | inr x4 =>
                                                                                                    @unEitherT OOM_MESSAGE ident
                                                                                                      (UB (ERR (list dvalue)))
                                                                                                      match x4 with
                                                                                                      | inl x5 =>
                                                                                                          {|
                                                                                                            unEitherT :=
                                                                                                              {|
                                                                                                                unIdent :=
                                                                                                                  @inr OOM_MESSAGE
                                                                                                                    (UB (ERR (list dvalue)))
                                                                                                                    (@inl UB_MESSAGE
                                                                                                                       (ERR (list dvalue)) x5)
                                                                                                              |}
                                                                                                          |}
                                                                                                      | inr x5 =>
                                                                                                          @unEitherT UB_MESSAGE
                                                                                                            (eitherT OOM_MESSAGE ident)
                                                                                                            (ERR (list dvalue))
                                                                                                            match x5 with
                                                                                                            | inl x6 =>
                                                                                                                {|
                                                                                                                  unEitherT :=
                                                                                                                    {|
                                                                                                                      unEitherT :=
                                                                                                                        {|
                                                                                                                          unIdent :=
                                                                                                                            @inr OOM_MESSAGE
                                                                                                                              (UB (ERR (list dvalue)))
                                                                                                                              (@inr UB_MESSAGE
                                                                                                                                 (ERR (list dvalue))
                                                                                                                                 (@inl ERR_MESSAGE
                                                                                                                                    (list dvalue) x6))
                                                                                                                        |}
                                                                                                                    |}
                                                                                                                |}
                                                                                                            | inr x6 =>
                                                                                                                {|
                                                                                                                  unEitherT :=
                                                                                                                    {|
                                                                                                                      unEitherT :=
                                                                                                                        {|
                                                                                                                          unIdent :=
                                                                                                                            @inr OOM_MESSAGE
                                                                                                                              (UB (ERR (list dvalue)))
                                                                                                                              (@inr UB_MESSAGE
                                                                                                                                 (ERR (list dvalue))
                                                                                                                                 (@inr ERR_MESSAGE
                                                                                                                                    (list dvalue) 
                                                                                                                                    (x3 :: x6)))
                                                                                                                        |}
                                                                                                                    |}
                                                                                                                |}
                                                                                                            end
                                                                                                      end
                                                                                                end
                                                                                            |}
                                                                                        |}
                                                                                    |}
                                                                                |}
                                                                            end)
                                                                   end
                                                             end
                                                       end
                                                   |}
                                               |}
                                           |}
                                       |}
                                   end
                               end
                           end
                       end) conds xs ys).
          match goal with
          | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
              exists e;
              exists (fun _ => res)
          end.
          split; auto.
          split.
          { destruct_err_ub_oom e; cbn; auto.
          }

          destruct_err_ub_oom e; cbn; auto.
          right.
          intros ? ?; subst; auto.
      }
    Qed.

    Lemma eval_select_eval_select :
      forall cnd x y
        (X : concretize_u x (concretize_uvalue x))
        (Y : concretize_u y (concretize_uvalue y)),
        @eval_select ErrUbOomProp Monad_ErrUbOomProp
          (fun (dt : dtyp) (edv : err_ub_oom dvalue) =>
             match @unERR_UB_OOM ident dvalue edv with
             | {| unEitherT := {| unEitherT := {| unEitherT := {| unIdent := inr (inr (inr dv)) |} |} |} |} =>
                 dvalue_has_dtyp dv dt /\ dv <> DVALUE_Poison dt
             | _ => True
             end) err_ub_oom (@Monad_err_ub_oom ident Monad_ident) (@RAISE_ERROR_err_ub_oom ident Monad_ident)
          (@RAISE_UB_err_ub_oom_T ident Monad_ident) (@RAISE_OOM_err_ub_oom_T ident Monad_ident)
          (fun (A : Type) (x ue : err_ub_oom A) => x = ue) cnd x y
          (@eval_select err_ub_oom (@Monad_err_ub_oom ident Monad_ident)
             (fun dt : dtyp =>
                @lift_err_RAISE_ERROR dvalue err_ub_oom
                  (@Monad_err_ub_oom ident Monad_ident)
                  (@RAISE_ERROR_err_ub_oom ident Monad_ident)
                  (default_dvalue_of_dtyp dt)) err_ub_oom
             (@Monad_err_ub_oom ident Monad_ident)
             (@RAISE_ERROR_err_ub_oom ident Monad_ident)
             (@RAISE_UB_err_ub_oom_T ident Monad_ident)
             (@RAISE_OOM_err_ub_oom_T ident Monad_ident)
             (fun (A : Type) (x : err_ub_oom A) => x) cnd x y).
    Proof.
      intros cnd x y X Y.
      rewrite eval_select_equation.
      rewrite (@eval_select_equation err_ub_oom).
      destruct cnd; try reflexivity.
      - break_match.
        + apply X.
        + apply Y.
      - cbn.
        match goal with
        | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
            exists (concretize_uvalue x);
            exists (fun _ => res)
        end.
        split; auto.

        unfold concretize_uvalue.
        remember
          (concretize_uvalueM err_ub_oom (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
             err_ub_oom (fun (A : Type) (x0 : err_ub_oom A) => x0) x).
        split; cbn; eauto.
        + destruct_err_ub_oom e; try reflexivity.
        + destruct_err_ub_oom e; cbn; eauto.
          right.
          intros ? ?; subst.
          match goal with
          | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
              exists (concretize_uvalue y);
              exists (fun _ => res)
          end.
          split; auto.

          unfold concretize_uvalue.
          remember
            (concretize_uvalueM err_ub_oom (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
               err_ub_oom (fun (A : Type) (x0 : err_ub_oom A) => x0) y).
          split; cbn; eauto.
          -- destruct_err_ub_oom e; try reflexivity.
          -- destruct_err_ub_oom e; cbn; eauto.
             right.
             intros ? ?; subst.
             destruct a; try reflexivity.
             destruct a0; try reflexivity.

             match goal with
             | [ |- context [ match ?X with _ => _ end ] ] =>
                 remember X
             end.
             match goal with
             | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
                 exists e; exists (fun _ => res)
             end.

             split; auto.
             subst; apply eval_select_loop_eval_select_loop.

             split; subst; cbn; eauto.
             match goal with
             | [ |- context [ match ?X with _ => _ end ] ] =>
                 remember X
             end.
             destruct_err_ub_oom e; cbn; try reflexivity.
             match goal with
             | [ |- context [ match ?X with _ => _ end ] ] =>
                 remember X
             end.
             destruct_err_ub_oom e; cbn; try reflexivity; auto.

             right.
             intros ? ?; subst.
             reflexivity.
    Qed.

    Lemma concretize_u_concretize_uvalue : forall u, concretize_u u (concretize_uvalue u).
    Proof using.
      unfold concretize_u, concretize_uvalue.
      induction u using uvalue_strong_ind;
        try reflexivity.

      { (* Undef *)
        remember (concretize_uvalueM err_ub_oom
       (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
       err_ub_oom (fun (A : Type) (x : err_ub_oom A) => x)
       (UVALUE_Undef t)) as concuvalue.
        cbn.
        destruct (default_dvalue_of_dtyp t) eqn:DEF.
        + (* t could be unimplemented or void... *)
          cbn in *.
          subst.
          rewrite DEF.
          cbn in *; auto.
        + subst.
          cbn in *.
          rewrite DEF.
          cbn.
          split.
          eapply dvalue_default; eauto.
          eapply default_dvalue_of_dtyp_not_poison; eauto.
      }

      destruct u;
        try reflexivity.

      { (* Undef *)
          cbn.
          destruct (default_dvalue_of_dtyp t) eqn:DEF; cbn; auto.
          split.
          eapply dvalue_default; eauto.
          eapply default_dvalue_of_dtyp_not_poison; eauto.
      }

      { (* Structs *)
        cbn.
        pose proof @map_monad_concretize_u_concretize_uvalue fields.
        forward H0.
        { intros u H1.
          eapply H.
          eapply uvalue_struct_strict_subterm; auto.          
        }

        unfold concretize_u, concretize_uvalue in *.
        match goal with
        | [ |- context [ match ?X with _ => _ end ] ] =>
            remember X
        end.
        exists e.
        exists (fun a => ret (DVALUE_Struct a)).
        split; auto.
      }

      { (* Packed structs *)
        cbn.
        pose proof @map_monad_concretize_u_concretize_uvalue fields.
        forward H0.
        { intros u H1.
          eapply H.
          eapply uvalue_packed_struct_strict_subterm; auto.          
        }

        unfold concretize_u, concretize_uvalue in *.
        match goal with
        | [ |- context [ match ?X with _ => _ end ] ] =>
            remember X
        end.
        exists e.
        exists (fun a => ret (DVALUE_Packed_struct a)).
        split; auto.
      }

      { (* Array *)
        cbn.
        pose proof @map_monad_concretize_u_concretize_uvalue elts.
        forward H0.
        { intros u H1.
          eapply H.
          eapply uvalue_array_strict_subterm; auto.          
        }

        unfold concretize_u, concretize_uvalue in *.
        match goal with
        | [ |- context [ match ?X with _ => _ end ] ] =>
            remember X
        end.
        exists e.
        exists (fun a => ret (DVALUE_Array a)).
        split; auto.
      }

      { (* Vector *)
        cbn.
        pose proof @map_monad_concretize_u_concretize_uvalue elts.
        forward H0.
        { intros u H1.
          eapply H.
          eapply uvalue_vector_strict_subterm; auto.          
        }

        unfold concretize_u, concretize_uvalue in *.
        match goal with
        | [ |- context [ match ?X with _ => _ end ] ] =>
            remember X
        end.
        exists e.
        exists (fun a => ret (DVALUE_Vector a)).
        split; auto.
      }

      { (* IBinop *)
        cbn.
        unfold concretize_u, concretize_uvalue in *.
        match goal with
        | [ |- context [ match ?X with _ => _ end ] ] =>
            remember X
        end.
        match goal with
        | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
            exists e; exists (fun _ => res)
        end.
        split.

        subst.
        apply H.
        repeat constructor.

        destruct_err_ub_oom e; cbn; split; auto.
        right.
        intros a H0; subst.

        match goal with
        | [ |- context [ match ?X with _ => _ end ] ] =>
            remember X
        end.
        match goal with
        | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
            exists e; exists (fun _ => res)
        end.
        split.

        subst.
        apply H.
        repeat constructor.

        destruct_err_ub_oom e; cbn; split; auto.
        right.
        intros ? ?; subst.
        remember (eval_iop iop a a0).
        destruct_err_ub_oom y; reflexivity.
      }

      { (* ICmp *)
        cbn.
        unfold concretize_u, concretize_uvalue in *.
        match goal with
        | [ |- context [ match ?X with _ => _ end ] ] =>
            remember X
        end.
        match goal with
        | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
            exists e; exists (fun _ => res)
        end.
        split.

        subst.
        apply H.
        repeat constructor.

        destruct_err_ub_oom e; cbn; split; auto.
        right.
        intros a H0; subst.

        match goal with
        | [ |- context [ match ?X with _ => _ end ] ] =>
            remember X
        end.
        match goal with
        | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
            exists e; exists (fun _ => res)
        end.
        split.

        subst.
        apply H.
        repeat constructor.

        destruct_err_ub_oom e; cbn; split; auto.
        right.
        intros ? ?; subst.
        remember (eval_icmp cmp a a0).
        destruct_err_ub_oom y; reflexivity.
      }

      { (* FBinop *)
        cbn.
        unfold concretize_u, concretize_uvalue in *.
        match goal with
        | [ |- context [ match ?X with _ => _ end ] ] =>
            remember X
        end.
        match goal with
        | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
            exists e; exists (fun _ => res)
        end.
        split.

        subst.
        apply H.
        repeat constructor.

        destruct_err_ub_oom e; cbn; split; auto.
        right.
        intros a H0; subst.

        match goal with
        | [ |- context [ match ?X with _ => _ end ] ] =>
            remember X
        end.
        match goal with
        | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
            exists e; exists (fun _ => res)
        end.
        split.

        subst.
        apply H.
        repeat constructor.

        destruct_err_ub_oom e; cbn; split; auto.
        right.
        intros ? ?; subst.
        remember (eval_fop fop a a0).
        destruct_err_ub_oom y; reflexivity.
      }

      { (* FCmp *)
        cbn.
        unfold concretize_u, concretize_uvalue in *.
        match goal with
        | [ |- context [ match ?X with _ => _ end ] ] =>
            remember X
        end.
        match goal with
        | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
            exists e; exists (fun _ => res)
        end.
        split.

        subst.
        apply H.
        repeat constructor.

        destruct_err_ub_oom e; cbn; split; auto.
        right.
        intros a H0; subst.

        match goal with
        | [ |- context [ match ?X with _ => _ end ] ] =>
            remember X
        end.
        match goal with
        | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
            exists e; exists (fun _ => res)
        end.
        split.

        subst.
        apply H.
        repeat constructor.

        destruct_err_ub_oom e; cbn; split; auto.
        right.
        intros ? ?; subst.
        remember (eval_fcmp cmp a a0).
        destruct_err_ub_oom y; reflexivity.
      }

      { (* Conversion *)
        cbn.
        unfold concretize_u, concretize_uvalue in *.
        remember (concretize_uvalueM err_ub_oom
                    (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt)) err_ub_oom
                    (fun (A : Type) (x : err_ub_oom A) => x) u) as e.
        match goal with
        | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
            exists e; exists (fun _ => res)
        end.
        split.

        subst.
        apply H.
        repeat constructor.

        destruct_err_ub_oom e; cbn; split; auto.
        right.
        intros a H0; subst.

        repeat (break_match; try reflexivity).
      }

      { (* GEP *)
        cbn.
        pose proof @map_monad_concretize_u_concretize_uvalue idxs.
        forward H0.
        { intros u0 H1.
          eapply H.
          eapply uvalue_getelementptr_strict_subterm; auto.          
        }

        unfold concretize_u, concretize_uvalue in *.
        match goal with
        | [ |- context [ match ?X with _ => _ end ] ] =>
            remember X
        end.
        match goal with
        | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
            exists e; exists (fun _ => res)
        end.
        split.

        subst.
        apply H.
        repeat constructor.

        destruct_err_ub_oom e; cbn; split; auto.
        right.
        intros ? ?; subst.

        match goal with
        | [ |- context [ match ?X with _ => _ end ] ] =>
            remember X
        end.
        match goal with
        | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
            exists e; exists (fun _ => res)
        end.
        split; auto.
        destruct_err_ub_oom e; cbn; split; auto.
        right.
        intros ? ?; subst.

        repeat (break_match; try reflexivity).
      }

      { (* ExtractElement *)
        cbn.
        unfold concretize_u, concretize_uvalue in *.
        remember
          (concretize_uvalueM err_ub_oom
             (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt)) err_ub_oom
             (fun (A : Type) (x : err_ub_oom A) => x) u1) as e.
        match goal with
        | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
            exists e; exists (fun _ => res)
        end.
        split.

        subst.
        apply H.
        repeat constructor.

        destruct_err_ub_oom e; cbn; split; auto.
        right.
        intros a H0; subst.

        remember
          (concretize_uvalueM err_ub_oom
             (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
             err_ub_oom (fun (A : Type) (x : err_ub_oom A) => x) u2) as e.
        match goal with
        | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
            exists e; exists (fun _ => res)
        end.
        split.

        subst.
        apply H.
        repeat constructor.

        destruct_err_ub_oom e; cbn; split; auto.
        right.
        intros ? ?; subst.
        exists (match vec_typ with
           | DTYPE_Vector _ t => success_unERR_UB_OOM t
           | _ => ERR_unERR_UB_OOM "Invalid vector type for ExtractElement"
           end).
        exists (fun a1 => index_into_vec_dv a1 a a0).
        destruct vec_typ; split; cbn; eauto.
      }

      { (* InsertElement *)
        cbn.
        unfold concretize_u, concretize_uvalue in *.
        remember
          (concretize_uvalueM err_ub_oom
             (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt)) err_ub_oom
             (fun (A : Type) (x : err_ub_oom A) => x) u1) as e.
        match goal with
        | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
            exists e; exists (fun _ => res)
        end.
        split.

        subst.
        apply H.
        repeat constructor.

        destruct_err_ub_oom e; cbn; split; auto.
        right.
        intros a H0; subst.

        remember
          (concretize_uvalueM err_ub_oom
             (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
             err_ub_oom (fun (A : Type) (x : err_ub_oom A) => x) u3) as e.
        match goal with
        | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
            exists e; exists (fun _ => res)
        end.
        split.

        subst.
        apply H.
        repeat constructor.

        destruct_err_ub_oom e; cbn; split; auto.
        right.
        intros ? ?; subst.
        remember
          (concretize_uvalueM err_ub_oom
             (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
             err_ub_oom (fun (A : Type) (x : err_ub_oom A) => x) u2) as e.
        match goal with
        | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
            exists e; exists (fun _ => res)
        end.
        split.

        subst.
        apply H.
        repeat constructor.

        destruct_err_ub_oom e; cbn; split; auto.
        right.
        intros ? ?; subst.
        remember (insert_into_vec_dv vec_typ a a1 a0).
        destruct_err_ub_oom y; reflexivity.
      }

      { (* ExtractValue *)
        cbn.
        unfold concretize_u, concretize_uvalue in *.
        match goal with
        | [ |- context [ match ?X with _ => _ end ] ] =>
            remember X
        end.
        match goal with
        | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
            exists e; exists (fun _ => res)
        end.
        split.

        subst.
        apply H.
        repeat constructor.

        destruct_err_ub_oom e; cbn; split; auto.
        right.
        intros ? ?; subst.

        induction idxs; try reflexivity.
        remember (index_into_str_dv a a0).
        destruct_err_ub_oom y; reflexivity.
      }

      { (* InsertValue *)
        cbn.
        unfold concretize_u, concretize_uvalue in *.
        match goal with
        | [ |- context [ match ?X with _ => _ end ] ] =>
            remember X
        end.
        match goal with
        | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
            exists e; exists (fun _ => res)
        end.
        split.

        subst.
        apply H.
        repeat constructor.

        destruct_err_ub_oom e; cbn; split; auto.
        right.
        intros ? ?; subst.

        match goal with
        | [ |- context [ match ?X with _ => _ end ] ] =>
            remember X
        end.
        match goal with
        | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
            exists e; exists (fun _ => res)
        end.
        split.

        subst.
        apply H.
        repeat constructor.

        destruct_err_ub_oom e; cbn; split; auto.
        right.
        intros ? ?; subst.

        induction idxs; try reflexivity.
        destruct idxs.
        - remember (insert_into_str a a0 a1).
          destruct_err_ub_oom y; reflexivity.
        - remember (index_into_str_dv a a1).
          destruct_err_ub_oom y; reflexivity.
      }

      { (* Select *)
        rewrite concretize_uvalueM_equation.
        rewrite (@concretize_uvalueM_equation err_ub_oom).
        cbn.
        remember
          (concretize_uvalueM err_ub_oom
             (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt)) err_ub_oom
             (fun (A : Type) (x : err_ub_oom A) => x) u1) as e.
        match goal with
        | H : _ |- bind_ErrUbOomProp ?ma ?k ?res =>
            exists e; exists (fun _ => res)
        end.
        split.

        subst.
        apply H.
        repeat constructor.

        destruct_err_ub_oom e; cbn; split; auto.
        right.
        intros a H0; subst.

        pose proof eval_select_eval_select a u2 u3.
        forward H0.
        eapply H.
        repeat constructor.
        forward H0.
        eapply H.
        repeat constructor.

        remember (eval_select err_ub_oom
                                  (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
                                  err_ub_oom (fun (A : Type) (x : err_ub_oom A) => x) a u2 u3).
        destruct_err_ub_oom e; cbn in *; auto.
      }

      { (* ConcatBytes *)
        repeat rewrite CONCBASE.concretize_uvalueM_equation.
        break_match.
        { break_match.
          eapply H.
          eapply Byte.all_extract_bytes_from_uvalue_strict_subterm; auto.
          eapply extractbytes_to_dvalue_extractbytes_to_dvalue.
          intros u H0.
          apply H.
          apply uvalue_concat_bytes_strict_subterm; auto.
        }
        eapply extractbytes_to_dvalue_extractbytes_to_dvalue.
        intros.
        apply H.
        apply uvalue_concat_bytes_strict_subterm; auto.
      }
    Qed.

    Definition concretize_picks {E} `{FailureE -< E} `{UBE -< E} `{OOME -< E} : PickUvalueE ~> itree E :=
      fun T p =>
        match p with
        | pick u
        | pickNonPoison u
        | pickUnique u =>
            let res_t := concretize_uvalue u in
            fmap (fun dv => exist _ dv I) res_t
        end.

    Section PARAMS_INTERP.
      Variable (E F: Type -> Type).

      Definition E_trigger :  E ~> itree (E +' F) :=
        fun R e => r <- trigger e ;; ret r.

      Definition F_trigger : F ~> itree (E +' F) :=
        fun R e => r <- trigger e ;; ret r.

      Definition pick_exec_h `{FailureE -< E +' F} `{UBE -< E +' F} `{OOME -< E +' F} :
        (E +' PickE +' F) ~> itree (E +' F) :=
        case_ E_trigger
          (case_ concretize_picks F_trigger).

      Definition exec_undef `{FailureE -< E +' F} `{UBE -< E +' F} `{OOME -< E +' F} :
        itree (E +' PickE +' F) ~> itree (E +' F) :=
        interp pick_exec_h.

    End PARAMS_INTERP.

  End PickImplementation.

End Make.
