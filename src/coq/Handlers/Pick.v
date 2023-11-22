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
  Handlers.Concretization.

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

    (* Unique or the concretization fails *)
    Definition unique_prop (uv : uvalue) : Prop
      := (exists x, concretize uv x /\ forall dv, concretize uv dv -> dv = x) \/
           (forall dv, ~ concretize uv dv).

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
        ~ (forall dt, ~concretize x (DVALUE_Poison dt)) ->
        PickUvalue_handler (@pickNonPoison _ _ (fun _ _ => True) x) t
    | PickUV_NonPoisonRet :
      forall x (res : err_ub_oom dvalue) (t : itree E {y : dvalue | True})
        (Conc : concretize_u x res),
        (forall dt, ~concretize x (DVALUE_Poison dt)) ->
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
      Proof.
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
    Lemma concretize_u_concretize_uvalue : forall u, concretize_u u (concretize_uvalue u).
    Proof.
      (* intros u. *)
      (* induction u; try do_it. *)
      (* - (* cbn. *) (* destruct (default_dvalue_of_dtyp t) eqn: EQ. *) *)
      (*     econstructor. Unshelve. 3 : { exact DVALUE_None. } *)
      (*     intro. inv H. *)
      (*     apply Concretize_Undef. apply dvalue_default. symmetry. auto. *)
      (*   - cbn. induction fields. *)
      (*     + cbn. constructor. auto. *)
      (*     + rewrite list_cons_app. rewrite map_monad_app. cbn. *)
      (*       assert (IN: forall u : uvalue, In u fields -> concretize_u u (concretize_uvalue u)). *)
      (*       { intros. apply H. apply in_cons; auto. } specialize (IHfields IN). *)
      (*       specialize (H a). assert (In a (a :: fields)) by apply in_eq. specialize (H H0). *)
      (*       pose proof Concretize_Struct_Cons as CONS. *)
      (*       specialize (CONS _ _ _ _ H IHfields). cbn in CONS. *)
      (*       * destruct (unEitherT (concretize_uvalue a)). *)
      (*         -- auto. *)
      (*         -- destruct s; auto. *)
      (*            destruct (unEitherT (map_monad concretize_uvalue fields)); auto. *)
      (*            destruct s; auto. *)
      (*   - cbn. induction fields. *)
      (*     + cbn. constructor. auto. *)
      (*     + rewrite list_cons_app. rewrite map_monad_app. cbn. *)
      (*       assert (IN: forall u : uvalue, In u fields -> concretize_u u (concretize_uvalue u)). *)
      (*       { intros. apply H. apply in_cons; auto. } specialize (IHfields IN). *)
      (*       specialize (H a). assert (In a (a :: fields)) by apply in_eq. specialize (H H0). *)
      (*       pose proof Concretize_Packed_struct_Cons as CONS. *)
      (*       specialize (CONS _ _ _ _ H IHfields). cbn in CONS. *)
      (*       * destruct (unEitherT (concretize_uvalue a)). *)
      (*         -- auto. *)
      (*         -- destruct s; auto. *)
      (*            destruct (unEitherT (map_monad concretize_uvalue fields)); auto. *)
      (*            destruct s; auto. *)
      (*   - cbn. induction elts. *)
      (*     + cbn. constructor. auto. *)
      (*     + rewrite list_cons_app. rewrite map_monad_app. cbn. *)
      (*       assert (IN: forall u : uvalue, In u elts -> concretize_u u (concretize_uvalue u)). *)
      (*       { intros. apply H. apply in_cons; auto. } specialize (IHelts IN). *)
      (*       specialize (H a). assert (In a (a :: elts)) by apply in_eq. specialize (H H0). *)
      (*       pose proof Concretize_Array_Cons as CONS. *)
      (*       specialize (CONS _ _ _ _ H IHelts). cbn in CONS. *)
      (*       * destruct (unEitherT (concretize_uvalue a)). *)
      (*         -- auto. *)
      (*         -- destruct s; auto. *)
      (*            destruct (unEitherT (map_monad concretize_uvalue elts)); auto. *)
      (*            destruct s; auto. *)
      (*   - cbn. induction elts. *)
      (*     + cbn. constructor. auto. *)
      (*     + rewrite list_cons_app. rewrite map_monad_app. cbn. *)
      (*       assert (IN: forall u : uvalue, In u elts -> concretize_u u (concretize_uvalue u)). *)
      (*       { intros. apply H. apply in_cons; auto. } specialize (IHelts IN). *)
      (*       specialize (H a). assert (In a (a :: elts)) by apply in_eq. specialize (H H0). *)
      (*       pose proof Concretize_Vector_Cons as CONS. *)
      (*       specialize (CONS _ _ _ _ H IHelts). cbn in CONS. *)
      (*       * destruct (unEitherT (concretize_uvalue a)). *)
      (*         -- auto. *)
      (*         -- destruct s; auto. *)
      (*            destruct (unEitherT (map_monad concretize_uvalue elts)); auto. *)
      (*            destruct s; auto. *)
      (*   - cbn; apply (Pick_fail (v := DVALUE_None)); intro H'; inv H'. *)
      (*   - cbn; apply (Pick_fail (v := DVALUE_None)); intro H'; inv H'. *)
      (*   - cbn; apply (Pick_fail (v := DVALUE_None)); intro H'; inv H'. *)
      (*   - cbn; apply (Pick_fail (v := DVALUE_None)); intro H'; inv H'. *)
      (*   - cbn; apply (Pick_fail (v := DVALUE_None)); intro H'; inv H'. *)
      (*   - cbn; apply (Pick_fail (v := DVALUE_None)); intro H'; inv H'. *)
      (*   - cbn; apply (Pick_fail (v := DVALUE_None)); intro H'; inv H'. *)
      (*   - cbn; apply (Pick_fail (v := DVALUE_None)); intro H'; inv H'. *)
      (* Qed. *)
    Admitted.

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
