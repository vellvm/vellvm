(* TODO: clean up imports *)
From Coq Require Import List String Ascii ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

From Vellvm Require Import
     LLVMAst
     LLVMEvents
     UndefTests
     TopLevel
     Refinement
     TopLevelRefinements
     CFG
     DynamicTypes
     PropT
     Syntax.Traversal
     Semantics.LLVMParams
     Semantics.Lang.

From Vellvm.Semantics Require Import
     Memory.Sizeof
     Memory.MemBytes
     GepM.

From Vellvm.Utils Require Import
     Tactics
     Error
     MonadReturnsLaws.

From Vellvm.Handlers Require Import
     Stack
     Local
     Global
     Serialization.

From ITree Require Import
     ITree
     Basics
     Eq.Eq
     Events.State.

From ExtLib Require Import
     Structures.Monads
     Structures.Maps
     Core.RelDec
     Programming.Eqv.

Import EqvNotation.


Import ITree.Basics.Basics.Monads.

Import MonadNotation.
Import ListNotations.
Import Monads.

Require Import Morphisms.
Require Import Relations.

(* Import R. *)
(* Import TopLevelEnv. *)
(* Import IO. *)
(* Import D. *)

Import MemoryAddress.


Module Make (LP : LLVMParams) (LLVM : Lang LP).
  Import LLVM.CP.CONC.
  Import LLVM.Events.
  Import LLVM.MEMORY_THEORY.ST.

  Module Ref := Refinement.Make LP LLVM.
  Import Ref.

  Import RefineProp.

  (* -------------------------------------------------------- *)
  (* Facts about multiplication and undef                     *)
  (* -------------------------------------------------------- *)
  Lemma refine_uvalue_ub :
    forall uv1 uv2 (str : string),
      concretize_u uv1 (raise_ub str) ->
      refine_uvalue uv1 uv2.
  Proof.
    intros uv1 uv2 str CONC.
    constructor.
    intros dv H.
    destruct uv1.

    all:
      try solve [red in CONC;
                 rewrite concretize_uvalueM_equation in CONC;
                 inversion CONC].

    (* IBinop *)
    5: {
      red in CONC.
      rewrite concretize_uvalueM_equation in CONC.

      destruct CONC as (ma & k' & CONC' & mbeq & REST).

      cbn in mbeq.
      destruct ma as [[[[[[[oom_ma] | [[ub_ma] | [[err_ma] | a]]]]]]]] eqn:Hma.
      - (* OOM from uv1 *)
        do 2 red.
        rewrite concretize_uvalueM_equation.

        cbn.
        unfold bind_RefineProp.

        eexists.
        eexists.

        split.

        (* ma = inl ub *)
        apply CONC'.

        split; auto.

        left; cbn; auto.
      - (* UB in uv1 *)
        do 2 red.
        rewrite concretize_uvalueM_equation.

        cbn.
        unfold bind_RefineProp.

        eexists.
        eexists.

        split.

        (* ma = inl (inl err) *)
        apply CONC'.

        split; auto.
      - (* Failure in uv1 *)
        do 2 red.
        rewrite concretize_uvalueM_equation.

        cbn.
        unfold bind_RefineProp.

        eexists.
        eexists.

        split.

        (* ma = inl (inl err) *)
        apply CONC'.

        split; auto.
      - (* uv1 succeeds *)
        do 2 red.
        rewrite concretize_uvalueM_equation.

        destruct REST as [FAILS | REST].
        solve [inversion FAILS].

        (* Get fate of uv2 *)
        assert (@MReturns _ _ _ MonadReturns_ErrUBOOM dvalue a
                          {| unERR_UB_OOM :=
                            {|
                              EitherMonad.unEitherT :=
                              {|
                                EitherMonad.unEitherT :=
                                {|
                                  EitherMonad.unEitherT :=
                                  {| IdentityMonad.unIdent := inr (inr (inr a)) |}
                                |}
                              |}
                            |}
                          |}) as ARet by reflexivity.
        specialize (REST a ARet).

        (* Get past evaluation of uv1 *)
        eexists.
        exists (fun _ => ret dv).

        split.
        apply CONC'.

        split; cbn; auto.
        right.
        intros a0 H0; subst.

        destruct REST as (mb & k'' & CONC'' & mceq & REST).
        destruct mb as [[[[[[[oom_mb] | [[ub_mb] | [[err_mb] | b]]]]]]]] eqn:Hmb.
        + (* OOM from uv2 *)

          unfold bind_RefineProp.

          (* Evaluation of uv2 *)
          eexists.
          eexists.

          split.
          apply CONC''.

          Set Printing Notations.
          cbn in mceq.
          destruct (k' a0) as [[[[[[[oom_k'a0] | [[ub_k'a0] | [[err_k'a0] | k'a0]]]]]]]] eqn:Hk'a0; try contradiction.

          cbn in *.
          rewrite Hk'a0 in mbeq.
          cbn in mbeq.
          contradiction.
        + (* UB from uv2 *)

          (* Evaluation of uv2 *)
          eexists.
          eexists.

          split.
          apply CONC''.

          split; cbn; auto.
        + (* Failure from uv2 *)

          (* Evaluation of uv2 *)
          eexists.
          eexists.

          split.
          apply CONC''.

          split; cbn; auto.
        + (* uv2 succeeds *)
          eexists.
          exists (fun _ => ret dv).
          split; [eauto|].
          split; cbn; auto.

          right.
          intros a H0; subst.

          assert (@MReturns  _ _ _ MonadReturns_ErrUBOOM dvalue a (success_unERR_UB_OOM a)) as ARet' by reflexivity.

          destruct REST as [FAILS | REST].
          solve [inversion FAILS].
          specialize (REST a ARet').

          cbn in mceq.
          destruct (eval_iop iop a0 a) as [[[[[[[oom_eval_iopiopa0a] | [[ub_eval_iopiopa0a] | [[err_eval_iopiopa0a] | eval_iopiopa0a]]]]]]]] eqn:Heval_iopiopa0a; auto.

          * destruct (k'' a) as [[[[[[[oom_k''a] | [[ub_k''a] | [[err_k''a] | k''a]]]]]]]] eqn:Hk''a;
              auto; inversion REST; subst; auto.

            (* No UB / failure... *)
            destruct (k' a0) as [[[[[[[oom_k'a0] | [[ub_k'a0] | [[err_k'a0] | k'a0]]]]]]]] eqn:Hk'a0;
              cbn in mceq, mbeq; subst; try contradiction.

            rewrite Hk'a0 in mbeq;
              cbn in mbeq;
              contradiction.

          * destruct (k'' a) as [[[[[[[oom_k''a] | [[ub_k''a] | [[err_k''a] | k''a]]]]]]]] eqn:Hk''a;
              auto; inversion REST; subst; auto.

            -- cbn in mceq.

               (* No UB / failure... *)
               destruct (k' a0) as [[[[[[[oom_k'a0] | [[ub_k'a0] | [[err_k'a0] | k'a0]]]]]]]] eqn:Hk'a0;
                 cbn in mceq, mbeq; subst; try contradiction.

               rewrite Hk'a0 in mbeq.
               cbn in mbeq.
               contradiction.
            -- cbn in *.

               (* No UB / failure... *)
               destruct (k' a0) as [[[[[[[oom_k'a0] | [[ub_k'a0] | [[err_k'a0] | k'a0]]]]]]]] eqn:Hk'a0;
                 cbn in mceq, mbeq; subst; try contradiction.
    }

    (* Structs *)
    { induction fields.
      - red in CONC.
        rewrite concretize_uvalueM_equation in CONC.
        cbn in CONC.

        destruct CONC as (ma & k' & CONC' & mbeq & REST).
        destruct ma as [[[[[[[oom_ma] | [[ub_ma] | [[err_ma] | a]]]]]]]] eqn:Hma; try contradiction.
        subst.

        cbn in mbeq.

        destruct REST as [FAILS | REST].
        solve [inversion FAILS].
        specialize (REST []).
        forward REST; [reflexivity|].

        destruct (k' nil) as [[[[[[[oom_k'nil] | [[ub_k'nil] | [[err_k'nil] | k'nil]]]]]]]] eqn:Hk'nil; contradiction.
      - (* Multiple fields *)
        do 2 red.
        rewrite concretize_uvalueM_equation.
        red in CONC.
        rewrite concretize_uvalueM_equation in CONC.


        Import Util.
        rewrite Monads.map_monad_unfold in CONC.
        rewrite Monads.map_monad_unfold.

        match goal with
        | H: _ |- (x <- (bind ?conc_a ?conc_rest) ;; _) _ =>
          remember conc_a as conc_a';
            remember conc_rest as conc_rest'
        end.

        epose proof Monad.bind_bind _ _ _ conc_a' conc_rest' (fun x => ret (DVALUE_Struct x)).

        (* Unset Printing Notations. *)
        (* Set Printing Implicit. *)
        (* assert ((y <- conc_a';; x <- conc_rest' y;; (@ret err_or_ub Monad_err_or_ub dvalue (DVALUE_Struct x))) (@ret err_or_ub Monad_err_or_ub dvalue dv)). *)
        (* replace ((x <- (x <- conc_a';; conc_rest' x);; ret (DVALUE_Struct x)) (ret dv)) with ((y <- conc_a';; x <- conc_rest' y;; ret (DVALUE_Struct x)) (ret dv)). *)
        (* (fun b => conc_rest'). (ret (b :: bs)). *)

        (* erewrite  *)

        (* pose proof _ _ _ m *)
        (* rewrite Monad.bind_bind. *)
        (* rewrite map_monad_cons. *)
        admit.
    }

  Abort.

  Lemma refine_uvalue_op_poison_l :
    forall op dt uv2 dv2,
      NO_VOID dt ->
      concretize uv2 dv2 ->
      refine_uvalue (UVALUE_IBinop op (UVALUE_Poison dt) uv2) (UVALUE_Poison dt).
  Proof.
    intros op dt uv2 dv2 NV CONC.
    eapply UndefPoison.
    2: constructor.

    rewrite concretize_equation.
    red.
    rewrite concretize_uvalueM_equation.
    cbn.

    match goal with
    | |- bind_RefineProp ?pa ?k ?mb =>
      idtac pa;
        idtac k
    end.

    unfold bind_RefineProp.
    cbn.
    exists (ret (DVALUE_Poison dt)).
    exists (fun poison_res => ret poison_res). (* k' *)

    (* pa ma *)
    split.
    rewrite concretize_uvalueM_equation.
    reflexivity.

    (* Monad.eq1 mb (x <- ma;; k' x) *)
    split.
    cbn.
    reflexivity.

    right.
    intros poison_res MRets_poison.

    (* Goal is from k a (k' a) *)
    exists (ret dv2). (* ma' *)
    exists (fun _ => ret (DVALUE_Poison dt)). (* k'' *)

    (*
      poison_res <- eval poison (* ma *)
      (* k' *)
      dv2_res <- eval uv2 (* ma' *)
      (* k'' *)
      lift_ue (eval_iop poison_res edv2)
     *)

    (* pa' ma' *)
    split.
    apply CONC.

    (* Monad.eq' mb' (x <- ma';; k'' x) *)
    split; cbn; inversion MRets_poison; subst.
    reflexivity.

    right.
    intros dv2' MRets_dv2.
    inversion MRets_dv2; subst.
    cbn. reflexivity.

    auto.
  Qed.

  Lemma concretize_succeeds_dec :
    forall uv,
      concretize_fails uv \/ concretize_succeeds uv.
  Proof.
    intros uv; induction uv;
      try solve [unfold concretize_succeeds, concretize_fails; right;
             intros CONTRA;
             red in CONTRA;
             rewrite concretize_uvalueM_equation in CONTRA;
             cbn in CONTRA;
             contradiction
        ].
    - induction fields.
      + unfold concretize_succeeds, concretize_fails; right.
        intros CONTRA.
        red in CONTRA.
        rewrite concretize_uvalueM_equation in CONTRA.
        cbn in CONTRA.

        (* Move this *)
        Ltac destruct_err_ub_oom v :=
          let oom_name := fresh "OOM" in
          let ub_name := fresh "UB" in
          let err_name := fresh "ERR" in
          let success_name := fresh "SUCCESS" in
          let H_name := fresh "H_ERR" in
          destruct v as [[[[[[[oom_name] | [[ub_name] | [[err_name] | success_name]]]]]]]] eqn:H_name.


        unfold bind_RefineProp in CONTRA.
        destruct CONTRA as (ma & k' & CONC' & mbeq & REST).
        destruct REST as [FAILS | REST].
        * destruct_err_ub_oom ma;
            cbn in *; contradiction.
        * destruct_err_ub_oom ma; cbn in *; try contradiction.
          specialize (REST SUCCESS eq_refl).
          destruct_err_ub_oom (k' SUCCESS); cbn in *; contradiction.
      + unfold concretize_succeeds, concretize_fails; right.
        intros CONTRA.
        red in CONTRA.
        rewrite concretize_uvalueM_equation in CONTRA.
        cbn in CONTRA.

        destruct CONTRA as (ma & k' & CONC' & mbeq & REST).
        destruct CONC' as (ma' & k'' & CONC'' & mbeq' & REST').
        destruct REST as [FAILS | REST].
        * destruct_err_ub_oom ma;
            cbn in *; try contradiction.

          subst.
    -
  Qed.

  Instance proper_refine_uvalue_ibinop {op v2 rv} : Proper ((fun x y => refine_uvalue y x) ==> (fun (x y : Prop) => x -> y)) (fun v1 => refine_uvalue (UVALUE_IBinop op v1 v2) rv).
  Proof.
    unfold Proper, respectful.
    intros x y Ryx Ribop.

    transitivity (UVALUE_IBinop op x v2); auto.

    inversion Ryx; subst.
    - (* y could be refined to poison, so x can be any value of the same type *)
      rename H into HPoison.
      rename H0 into XTYP.

      (* If `(UVALUE_IBinop op x v2)` concretizes to some dvalue `dv`,
         then `(UVALUE_IBinop op y v2)` can also be concretized to the
         same dvalue. *)
      constructor; auto.
      intros dv Conc.

      (* Invert the concretization of x *)
      apply concretize_ibinop_inv in Conc as (dv1 & dv2 & Succ1 & Conc1 & Succ2 & Conc2 & EVAL).

      epose proof Concretize_IBinop op y (ret dv1) v2 (ret dv2) _ Conc2.
      cbn in H.

      rewrite concretize_equation.
      rewrite <- EVAL.
      cbn.
      replace (        {|
          unERR_UB_OOM :=
            {|
              EitherMonad.unEitherT :=
                {|
                  EitherMonad.unEitherT :=
                    {|
                      EitherMonad.unEitherT :=
                        EitherMonad.unEitherT
                          (EitherMonad.unEitherT
                             (EitherMonad.unEitherT (unERR_UB_OOM (eval_iop op dv1 dv2))))
                    |}
                |}
            |}
                |}) with (eval_iop op dv1 dv2) in H by
          (destruct (eval_iop op dv1 dv2) as [[[[[[[oom_eval_iopopdv1dv2] | [[ub_eval_iopopdv1dv2] | [[err_eval_iopopdv1dv2] | eval_iopopdv1dv2]]]]]]]] eqn:Heval_iopopdv1dv2; eauto).

      auto.


      destruct (eval_iop op dv1 dv2); cbn.
      pose proof Concretize_IBinop op.
      epose proof Concretize_IBinop op (UVALUE_Poison dt) _ v2 _.

      red.
      rewrite concretize_uvalueM_equation.
      cbn.

      unfold bind_RefineProp.
      eexists (ret (DVALUE_Poison dt)).
      eexists.
      cbn.
      constructor.
    - intros CONTRA. subst.
      apply refine_poison in Ribop. inversion Ribop.
    - intros dv0 Conc.
      inversion Ribop; subst.
      pose proof (H0 dv0 Conc).

      inversion Ryx; subst.
      + (* x could be a refinement of poison

           refine_uvalue has an UndefPoison case which means anything
           refines poison.
         *)
        (* In this case, eval_iop should return poison,


         *)

      inversion Ryx; subst.
      + red. red.
        rewrite concretize_uvalueM_equation.
        cbn.
        unfold bind_MPropT.
        eexists. exists (fun _ => ret dv0).
        split; [reflexivity|].
        split; [reflexivity|].
        intros a MReta.
        inversion MReta; subst.
        cbn.
        exists (ret dv0). exists ret.
        split.
        admit.
        split.
        cbn.
        reflexivity.
        intros a0 H2.
        inversion H2;  subst.
        cbn.
        destruct a0.
        cbn.
        inversion MReta; subst.
        cbn.


        { destruct v2.


          rewrite concretize_uvalueM_equation.
          cbn.

            rewrite c

        }

        [reflexivity|].
        split; [reflexivity|].

        admit.
        admit.
      + admit.



    constructor; [intros CONTRA; inversion CONTRA|].
    intros dv H.

    clear H. exfalso. clear dv.

    (*   eapply Concretize_IBinop. *)
    (* } *)

    (* eapply Concretize_IBinop. with (dv1:=DVALUE_I64 one) (dv2:=dv). *)
    (* - apply Concretize_Undef. constructor. *)
    (* - auto. *)
    (* - simpl. inversion H; subst. *)
    (*   + inversion H0. *)
    (*   + inversion H1; subst; auto. *)
    (*     unfold DynamicValues.Int64.mul. unfold DynamicValues.Int64.one. *)
    (*     replace (DynamicValues.Int64.unsigned (DynamicValues.Int64.repr 1) * *)
    (*              DynamicValues.Int64.unsigned x) with (DynamicValues.Int64.unsigned x). *)
    (*     * destruct (Eqv.eqv_dec_p 64%nat 1%nat); rewrite DynamicValues.Int64.repr_unsigned; reflexivity. *)
    (*     * rewrite Integers.Int64.unsigned_repr; try lia; cbn; try omega. *)

  Admitted.

  Theorem undef_refines_mul_1_undef :
    refine_uvalue
      (UVALUE_IBinop (Mul false false) (UVALUE_I64 one)
                     (UVALUE_Undef (DTYPE_I 64))) (UVALUE_Undef (DTYPE_I 64)).
  Proof.
    constructor.
    intros CONTRA; inversion CONTRA.

    intros dv H.
    rewrite concretize_equation in *.
    red in H; red.
    cbn in H.

    cbn.

    unfold bind_MPropT.
    eexists. exists (fun x => ret dv).
    split.
    - reflexivity.
    - split.
      + cbn. reflexivity.
      + intros a MRet.
        exists {| EitherMonad.unEitherT := inr (inr dv) |}. exists ret.
        split; auto.
        split; [cbn; reflexivity|].

        intros dv' MRetdv.
        inversion MRet.
        inversion MRetdv.
        subst.

        inversion H; subst.
        cbn.

        break_inner_match.
        rewrite DynamicValues.Int64.mul_commut.
        rewrite DynamicValues.Int64.mul_one.
        reflexivity.

        rewrite DynamicValues.Int64.mul_commut.
        rewrite DynamicValues.Int64.mul_one.
        reflexivity.
  Qed.

  Theorem undef_refines_mul_undef_undef:
    refine_uvalue (UVALUE_IBinop (Mul false false) (UVALUE_Undef (DTYPE_I 64)) (UVALUE_Undef (DTYPE_I 64))) (UVALUE_Undef (DTYPE_I 64)).
  Proof.
    assert (refine_uvalue (UVALUE_Undef (DTYPE_I 64)) (UVALUE_I64 one)).
    { constructor; intuition.
      inversion H.
      rewrite concretize_equation in *.
      red in H.
      red.
      cbn in *.

      inversion H.
      constructor.
    }

    eapply proper_refine_uvalue_ibinop; eauto.
    apply undef_refines_mul_1_undef.
  Qed.

  Lemma rel_prime_mod_mul :
    forall a b x,
      Znumtheory.rel_prime a b ->
      exists k, (a * k) mod b = x.
  Proof.
  Admitted.

  Lemma mod_range :
    forall x m, -1 < x mod m < m.
  Proof.
  Admitted.

  Lemma Int64_mul_mod :
    forall a b intrange,
      (DynamicValues.Int64.mul (DynamicValues.Int64.repr a)
                               (DynamicValues.Int64.repr b)) =
      {| DynamicValues.Int64.intval := ((a * b) mod DynamicValues.Int64.modulus);
         DynamicValues.Int64.intrange := intrange
      |}.
  Proof.
  Admitted.

  Theorem undef_refines_mul_undef_relprime :
    forall a,
      Znumtheory.rel_prime a DynamicValues.Int64.modulus ->
      refine_uvalue (UVALUE_Undef (DTYPE_I 64))
                    (UVALUE_IBinop (Mul false false)
                                   (UVALUE_Undef (DTYPE_I 64)) (UVALUE_I64 (DynamicValues.Int64.repr a))).
  Proof.
    intros a Hrp.
    constructor.
    intros dv H.
    inversion H; subst.
    - inversion H0.
    - inversion H1; subst; inversion H; subst.
      + inversion H0.
      + destruct x eqn:Hx.
        pose proof rel_prime_mod_mul a DynamicValues.Int64.modulus intval Hrp as Hmod.

        destruct Hmod as [k Hmod].
        rewrite Z.mul_comm in Hmod.

        match goal with
        | [ H : concretize (UVALUE_Undef ?t) ?dv |- concretize (UVALUE_IBinop _ (UVALUE_Undef ?t) (UVALUE_I64 ?v1)) ?dv ]
          => apply Concretize_IBinop with (dv2:=(DVALUE_I64 v1)) (dv1:=DVALUE_I64 (repr k))
        end.
        -- apply Concretize_Undef; constructor.
        -- constructor; reflexivity.
        -- subst; simpl.
           destruct (Eqv.eqv_dec_p 64%nat 1%nat);
             (rewrite (Int64_mul_mod k a intrange); reflexivity).
  Qed.

  Theorem undef_refines_mul_relprime_undef :
    forall a,
      Znumtheory.rel_prime a DynamicValues.Int64.modulus ->
      refine_uvalue (UVALUE_Undef (DTYPE_I 64))
                    (UVALUE_IBinop (Mul false false)
                                   (UVALUE_I64 (DynamicValues.Int64.repr a)) (UVALUE_Undef (DTYPE_I 64))).
  Proof.
    intros a Hrp.
    constructor.
    intros dv H.
    inversion H; subst.
    - inversion H0.
    - inversion H1; subst; inversion H; subst.
      + inversion H0.
      + destruct x eqn:Hx.
        pose proof rel_prime_mod_mul a DynamicValues.Int64.modulus intval Hrp as Hmod.

        destruct Hmod as [k Hmod].

        match goal with
        | [ H : concretize (UVALUE_Undef ?t) ?dv |- concretize (UVALUE_IBinop _ (UVALUE_I64 ?v1) (UVALUE_Undef ?t)) ?dv ]
          => apply Concretize_IBinop with (dv1:=(DVALUE_I64 v1)) (dv2:=DVALUE_I64 (repr k))
        end.
        -- constructor; reflexivity.
        -- apply Concretize_Undef; constructor.
        -- subst; simpl.
           destruct (Eqv.eqv_dec_p 64%nat 1%nat);
             (rewrite (Int64_mul_mod a k intrange); reflexivity).
  Qed.

  Lemma zero_refines_undef :
    refine_uvalue (UVALUE_I64 (DynamicValues.Int64.repr 0)) (UVALUE_Undef (DTYPE_I 64)).
  Proof.
    constructor. intros dv H.
    inversion H; subst.
    inversion H0; subst.
    apply Concretize_Undef.
    constructor.
  Qed.

  Lemma zero_refines_undef_mul_a :
    forall a,
      refine_uvalue (UVALUE_I64 (DynamicValues.Int64.repr 0))
                    (UVALUE_IBinop (Mul false false)
                                   (UVALUE_Undef (DTYPE_I 64)) (UVALUE_I64 a)).
  Proof.
    constructor. intros dv H.
    inversion H; subst.
    inversion H0; subst.
    simpl in *.
    clear H0.

    eapply Concretize_IBinop with
        (dv1:=DVALUE_I64 (DynamicValues.Int64.repr 0)).

    apply Concretize_Undef.
    constructor.
    constructor. reflexivity.
  Admitted.


  Lemma zero_refines_a_mul_undef :
    forall a,
      refine_uvalue (UVALUE_I64 (DynamicValues.Int64.repr 0))
                    (UVALUE_IBinop (Mul false false)
                                   (UVALUE_I64 a) (UVALUE_Undef (DTYPE_I 64))).
  Proof.
  Admitted.


  (* -------------------------------------------------------- *)
  (* Facts about undef and bitwise and                        *)
  (* -------------------------------------------------------- *)

  Theorem undef_refines_and_undef_undef:
    refine_uvalue (UVALUE_Undef (DTYPE_I 64)) (UVALUE_IBinop And (UVALUE_Undef (DTYPE_I 64)) (UVALUE_Undef (DTYPE_I 64))).
  Proof.
    constructor.
    intros dv H.
    apply Concretize_IBinop with (dv1:=DVALUE_I64 (DynamicValues.Int64.repr (Z.ones 64))) (dv2:=dv).
    - apply Concretize_Undef. constructor.
    - auto.
    - simpl. inversion H; subst.
      + inversion H0.
      + inversion H1; subst; auto.
        unfold DynamicValues.Int64.and.
        replace (Z.land
                   (DynamicValues.Int64.unsigned
                      (DynamicValues.Int64.repr (Z.ones 64)))
                   (DynamicValues.Int64.unsigned x))
          with (DynamicValues.Int64.unsigned x).
        * destruct (Eqv.eqv_dec_p 64%nat 1%nat); rewrite DynamicValues.Int64.repr_unsigned; reflexivity.
        * rewrite Integers.Int64.unsigned_repr by (cbn; lia).
          rewrite Z.land_comm.
          rewrite Z.land_ones by lia.
          rewrite Z.mod_small. reflexivity.

          cbn.
          pose proof DynamicValues.Int64.unsigned_range_2 x.
          cbn in H0.
          lia.
  Qed.

  (* -------------------------------------------------------- *)
  (* Facts about undef and bitwise or                         *)
  (* -------------------------------------------------------- *)

  Theorem undef_refines_or_undef_undef:
    refine_uvalue (UVALUE_Undef (DTYPE_I 64)) (UVALUE_IBinop Or (UVALUE_Undef (DTYPE_I 64)) (UVALUE_Undef (DTYPE_I 64))).
  Proof.
    constructor.
    intros dv H.
    apply Concretize_IBinop with (dv1:=DVALUE_I64 (DynamicValues.Int64.repr 0)) (dv2:=dv).
    - apply Concretize_Undef. constructor.
    - auto.
    - simpl. inversion H; subst.
      + inversion H0.
      + inversion H1; subst; auto.
        unfold DynamicValues.Int64.or.
        replace (Z.lor
                   (DynamicValues.Int64.unsigned
                      (DynamicValues.Int64.repr 0))
                   (DynamicValues.Int64.unsigned x))
          with (DynamicValues.Int64.unsigned x).
        * destruct (Eqv.eqv_dec_p 64%nat 1%nat); rewrite DynamicValues.Int64.repr_unsigned; reflexivity.
        * rewrite Integers.Int64.unsigned_repr by (cbn; lia).
          reflexivity.
  Qed.


  (* -------------------------------------------------- *)
  (* Division and undef facts                           *)
  (* -------------------------------------------------- *)

  Theorem undef_refines_undef_udiv_1:
    refine_uvalue (UVALUE_Undef (DTYPE_I 64)) (UVALUE_IBinop (UDiv false) (UVALUE_Undef (DTYPE_I 64)) (UVALUE_I64 (DynamicValues.Int64.repr 1))).
  Proof.
    constructor.
    intros dv H.
    apply Concretize_IBinop with (dv1:=dv) (dv2:=DVALUE_I64 (DynamicValues.Int64.repr 1)).
    - auto.
    - constructor; reflexivity.
    - inversion H; subst; simpl in *.
      + inversion H0.
      + inversion H1. simpl.
        destruct (DynamicValues.Int64.unsigned (DynamicValues.Int64.repr 1) =?
                  0)%Z eqn:Heq.
        inversion Heq.
        simpl.
        rewrite DynamicValues.Int64.divu_one.
        reflexivity.
  Qed.

  Theorem undef_refines_undef_sdiv_1:
    refine_uvalue (UVALUE_Undef (DTYPE_I 64)) (UVALUE_IBinop (SDiv false) (UVALUE_Undef (DTYPE_I 64)) (UVALUE_I64 (DynamicValues.Int64.repr 1))).
  Proof.
    constructor.
    intros dv H.
    apply Concretize_IBinop with (dv1:=dv) (dv2:=DVALUE_I64 (DynamicValues.Int64.repr 1)).
    - auto.
    - constructor; reflexivity.
    - inversion H; subst; simpl in *.
      + inversion H0.
      + inversion H1. simpl.
        destruct (DynamicValues.Int64.signed (DynamicValues.Int64.repr 1) =?
                  0)%Z eqn:Heq.
        inversion Heq.
        simpl.
        rewrite DynamicValues.Int64.divs_one.
        reflexivity.
        cbn.
        lia.
  Qed.

  Theorem zero_refines_undef_urem_1:
    refine_uvalue (UVALUE_I64 (DynamicValues.Int64.repr 0)) (UVALUE_IBinop URem (UVALUE_Undef (DTYPE_I 64)) (UVALUE_I64 (DynamicValues.Int64.repr 1))).
  Proof.
    constructor.
    intros dv H. inversion H; subst; inversion H0; subst.
    apply Concretize_IBinop with (dv1:=DVALUE_I64 (DynamicValues.Int64.repr 0)) (dv2:=DVALUE_I64 (DynamicValues.Int64.repr 1)).
    - apply Concretize_Undef. constructor.
    - constructor. reflexivity.
    - simpl.
      destruct (DynamicValues.Int64.unsigned (DynamicValues.Int64.repr 1) =?
                0)%Z eqn:Heq; simpl.
      inversion Heq.

      rewrite Integers.Int64.modu_one. reflexivity.
  Qed.

  Theorem zero_refines_undef_srem_1:
    refine_uvalue (UVALUE_I64 (DynamicValues.Int64.repr 0)) (UVALUE_IBinop SRem (UVALUE_Undef (DTYPE_I 64)) (UVALUE_I64 (DynamicValues.Int64.repr 1))).
  Proof.
    constructor.
    intros dv H. inversion H; subst; inversion H0; subst.
    apply Concretize_IBinop with (dv1:=DVALUE_I64 (DynamicValues.Int64.repr 0)) (dv2:=DVALUE_I64 (DynamicValues.Int64.repr 1)).
    - apply Concretize_Undef. constructor.
    - constructor. reflexivity.
    - simpl.
      destruct (DynamicValues.Int64.signed (DynamicValues.Int64.repr 1) =?
                0)%Z eqn:Heq; simpl.
      inversion Heq.
  Admitted.
