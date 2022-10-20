From Coq Require Import ZArith Lia List String.

From ExtLib Require Import
     Core.RelDec
     Structures.Monads.

From Vellvm Require Import
     Utils.Util
     Utils.Tactics
     Utils.ListUtil
     Utils.Error
     Utils.RefineProp
     Utils.Monads
     Utils.MapMonadExtra
     Handlers.MemoryModelImplementation
     Semantics.LLVMParams
     Semantics.Denotation
     Semantics.Memory.MemBytes
     Semantics.MemoryParams
     Semantics.ConcretizationParams.

Import MonadNotation.
Import MonadReturnsLaws.

Module MemBytesTheory (LP : LLVMParams) (MP : MemoryParams LP) (Byte : ByteModule LP.ADDR LP.IP LP.SIZEOF LP.Events MP.BYTE_IMPL) (CP : ConcretizationParams LP MP Byte).
  Import CP.
  Import CONC.
  Import MP.
  Import LP.

  Import Events.
  Import SIZEOF.
  Import PTOI.
  Import PROV.
  Import ITOP.
  Import DV.
  Import GEP.

  Export Byte.
  Import Byte.
  Import BYTE_IMPL.

  Ltac eval_nseq :=
    match goal with
    | |- context[Nseq ?start ?len] =>
      let HS := fresh "HS" in
      let HSeq := fresh "HSeq" in
      remember (Nseq start len) as HS eqn:HSeq;
      cbv in HSeq;
      subst HS
    end.

  Hint Resolve eq_dec_uvalue_correct : AllBytes.

  Hint Rewrite map_length : AllBytes.
  Hint Rewrite Nseq_length : AllBytes.
  Hint Rewrite N.eqb_refl : AllBytes.
  Hint Rewrite Z.eqb_refl : AllBytes.
  Hint Rewrite rel_dec_eq_true : AllBytes.
  Hint Rewrite sbyte_to_extractbyte_of_uvalue_sbyte : AllBytes.

  Ltac solve_guards_all_bytes :=
    repeat (cbn; autorewrite with AllBytes); eauto with AllBytes.

  Lemma all_bytes_helper_app :
    forall  sbytes sbytes2 start sid uv,
      all_bytes_from_uvalue_helper (Z.of_N start) sid uv sbytes = Some uv ->
      all_bytes_from_uvalue_helper (Z.of_N (start + N.of_nat (List.length sbytes))) sid uv sbytes2 = Some uv ->
      all_bytes_from_uvalue_helper (Z.of_N start) sid uv (sbytes ++ sbytes2) = Some uv.
  Proof.
    induction sbytes;
      intros sbytes2 start sid uv INIT REST.
    - now rewrite N.add_0_r in REST.
    - cbn.
      pose proof sbyte_to_extractbyte_inv a as (uvb & dtb & idxb & sidb & SBYTE).
      rewrite SBYTE.

      cbn in INIT; rewrite SBYTE in INIT.
      do 3 (break_match; [|solve [inv INIT]]).

      cbn in REST. auto.
      replace (Z.of_N (start + N.pos (Pos.of_succ_nat (Datatypes.length sbytes)))) with (Z.of_N (N.succ start + N.of_nat (Datatypes.length sbytes))) in REST by lia.

      rewrite <- N2Z.inj_succ in *.

      apply IHsbytes; auto.
  Qed.

  Lemma to_ubytes_all_bytes_from_uvalue_helper' :
    forall len uv dt sid sbytes start,
      is_supported dt ->
      map_monad (fun n : N =>
                   n' <- IP.from_Z (Z.of_N n);;
                   ret (uvalue_sbyte uv dt (UVALUE_IPTR n') sid)) (Nseq start len) = NoOom sbytes ->
      all_bytes_from_uvalue_helper (Z.of_N start) sid uv sbytes = Some uv.
  Proof.
    induction len;
      intros uv dt sid sbytes start SUP TO.
    - inv TO; reflexivity.
    - rewrite Nseq_S in TO.
      assert (Monad.eq1 (map_monad
                (fun n : N => n' <- IP.from_Z (Z.of_N n);; ret (uvalue_sbyte uv dt (UVALUE_IPTR n') sid))
                (Nseq start len ++ start + N.of_nat len :: nil)) (NoOom sbytes)) as EQ1.
      { unfold Monad.eq1, MonadEq1OOM.
        rewrite TO.
        auto.
      }

      setoid_rewrite -> map_monad_app in EQ1.
      destruct (map_monad
             (fun n : N => n' <- IP.from_Z (Z.of_N n);; ret (uvalue_sbyte uv dt (UVALUE_IPTR n') sid))
             (Nseq start len)) eqn:Hfirst; [|inversion EQ1].
      destruct (map_monad
             (fun n : N => n' <- IP.from_Z (Z.of_N n);; ret (uvalue_sbyte uv dt (UVALUE_IPTR n') sid))
             (start + N.of_nat len :: nil)) eqn:Hlast; [|inversion EQ1].

      cbn in EQ1; subst.
      apply all_bytes_helper_app.
      + eauto.
      + cbn in Hlast.
        break_match_hyp; inversion Hlast; subst.
        cbn.
        break_match_hyp; inversion Heqo; subst.
        rewrite sbyte_to_extractbyte_of_uvalue_sbyte.
        cbn.

        apply IP.from_Z_to_Z in Heqo0.
        rewrite Heqo0.
        assert (len = Datatypes.length l) as Hlen.

        { assert (MReturns l (map_monad
                                (fun n : N => n' <- IP.from_Z (Z.of_N n);; ret (uvalue_sbyte uv dt (UVALUE_IPTR n') sid))
                                (Nseq start len))) as RETS.
          { rewrite Hfirst.
            reflexivity.
          }

          apply MapMonadExtra.map_monad_length in RETS.
          rewrite Nseq_length in RETS.
          auto.
        }

        subst.
        rewrite Z.eqb_refl.
        rewrite eq_dec_eq.
        rewrite N.eqb_refl.
        cbn.
        reflexivity.
  Qed.

  Lemma to_ubytes_all_bytes_from_uvalue_helper :
    forall uv dt sid sbytes,
      is_supported dt ->
      to_ubytes uv dt sid = NoOom sbytes ->
      all_bytes_from_uvalue_helper 0 sid uv sbytes = Some uv.
  Proof.
    intros uv dt sid sbytes SUP TO.

    change 0%Z with (Z.of_N 0).
    eapply to_ubytes_all_bytes_from_uvalue_helper'; eauto.
  Qed.

  Lemma to_ubytes_sizeof_dtyp :
    forall uv dt sid sbytes,
      to_ubytes uv dt sid = NoOom sbytes ->
      N.of_nat (List.length sbytes) = sizeof_dtyp dt.
  Proof.
    intros uv dt sid sbytes TOUBYTES.
    unfold to_ubytes in *.
    assert (MReturns sbytes (map_monad
               (fun n : N =>
                n' <- IP.from_Z (Z.of_N n);; ret (uvalue_sbyte uv dt (UVALUE_IPTR n') sid))
               (Nseq 0 (N.to_nat (sizeof_dtyp dt))))) as RETS.
    { rewrite TOUBYTES; reflexivity.
    }

    apply MapMonadExtra.map_monad_length in RETS.
    rewrite Nseq_length in RETS.
    lia.
  Qed.

  Lemma to_ubytes_first_byte :
    forall uv dt sid s l,
      to_ubytes uv dt sid = NoOom (s :: l) ->
      s = uvalue_sbyte uv dt (UVALUE_IPTR IP.zero) sid.
  Proof.
    intros uv dt sid s l TO.
    unfold to_ubytes in TO.

    assert (N.to_nat (sizeof_dtyp dt) > 0)%nat.
    { destruct (N.to_nat (sizeof_dtyp dt)) eqn:Hsz.
      - cbn in TO. inversion TO.
      - lia.
    }

    assert (exists n, N.to_nat (sizeof_dtyp dt) = S n) as (n & Hsn).
    { destruct (N.to_nat (sizeof_dtyp dt)) eqn:Hsz.
      lia.
      eexists; auto.
    }

    rewrite Hsn in TO.
    cbn in TO.

    rewrite IP.from_Z_0 in TO.
    break_match_hyp; inversion TO; subst.
    auto.
  Qed.

  Lemma from_ubytes_to_ubytes :
    forall uv dt sid sbytes,
      is_supported dt ->
      sizeof_dtyp dt > 0 ->
      to_ubytes uv dt sid = NoOom sbytes ->
      from_ubytes sbytes dt = uv.
  Proof.
    intros uv dt sid sbytes SUP SIZE TOUBYTES.

    unfold from_ubytes.
    unfold all_bytes_from_uvalue.

    erewrite to_ubytes_sizeof_dtyp; eauto.
    rewrite N.eqb_refl.

    break_inner_match.
    - (* Contradiction by size *)
      subst.
      pose proof to_ubytes_sizeof_dtyp uv dt sid nil TOUBYTES.

      cbn in *.
      lia.
    - pose proof TOUBYTES as FIRST.
      apply to_ubytes_first_byte in FIRST.
      subst.
      rewrite sbyte_to_extractbyte_of_uvalue_sbyte.
      erewrite to_ubytes_all_bytes_from_uvalue_helper; eauto.

      rewrite DynamicTypes.dtyp_eqb_refl.
      cbn; eauto.
  Qed.
End MemBytesTheory.

Module SerializationTheory (LP : LLVMParams) (MP : MemoryParams LP) (Byte : ByteModule LP.ADDR LP.IP LP.SIZEOF LP.Events MP.BYTE_IMPL) (CP : ConcretizationParams LP MP Byte).
  Import CP.
  Import CONC.
  Import MP.
  Import LP.

  Import Events.

  Module MBT := MemBytesTheory LP MP Byte CP.
  Import MBT.
  Import Byte.
  Import SIZEOF.

  Module Mem := MakeFiniteMemory LP.
  Import Mem.

  Import DynamicTypes.

  (* TODO: move this *)
  Ltac tactic_on_non_aggregate_uvalues x t :=
    match x with
    | (UVALUE_Struct _) =>
      idtac
    | (UVALUE_Packed_struct _) =>
      idtac
    | (UVALUE_Array _ _) =>
      idtac
    | (UVALUE_Vector _ _) =>
      idtac
    | _ =>
      t
    end.

  Ltac tactic_on_non_aggregate_dtyps x t :=
    match x with
    | (DTYPE_Struct _) =>
      idtac
    | (DTYPE_Packed_struct _) =>
      idtac
    | (DTYPE_Array _ _) =>
      idtac
    | (DTYPE_Vector _ _) =>
      idtac
    | _ =>
      t
    end.


  (* Ltac eval_serialize_sbytes_hyp := *)
  (*   match goal with *)
  (*   (* Try easy case first for speedup *) *)
  (*   | H: ErrSID_evals_to *)
  (*          (serialize_sbytes ?x ?dt) *)
  (*          ?sbytes ?sid ?prov |- _ => *)
  (*     tactic_on_non_aggregate_uvalues x ltac:(cbn in H; inv H) *)
  (*   | H: context[serialize_sbytes ?x ?dt] |- _ => *)
  (*     tactic_on_non_aggregate_uvalues x ltac:(cbn in H; inv H) *)
  (*   end. *)

  Lemma eval_icmp_err_ub_oom_to_M :
    forall {M} `{HM : Monad M} `{HME : RAISE_ERROR M} op a b res,
      @eval_icmp err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
                 (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) op a b =
        success_unERR_UB_OOM res ->
      @eval_icmp M HM HME op a b = @ret M HM dvalue res.
  Proof.
    intros M HM HME op a b res EVAL.
    destruct op; cbn in *;
      destruct a, b; cbn in *; inversion EVAL;
      first [ break_match; inversion EVAL; reflexivity
            | auto
        ].
  Qed.


  From Vellvm.Utils Require Import Monads MonadExcLaws MonadEq1Laws.
  From ITree Require Import
       Basics.Monad.

  Require Import Morphisms.


  Lemma to_dvalue_OOM_NoOom :
    forall {Int} `{TD : ToDvalue Int} {M}
      `{HM : Monad M}
      `{HMO : RAISE_OOM M}
      `{EQM : Monad.Eq1 M}
      `{LAWS : @Monad.MonadLawsE M EQM HM}
      (v : Int),
      to_dvalue_OOM (NoOom v) ≈ @ret M HM dvalue (to_dvalue v).
  Proof.
    intros Int TD M HM HMO EQM LAWS v.
    unfold to_dvalue_OOM. cbn.
    destruct LAWS.
    eapply bind_ret_l.
  Qed.

Lemma eval_iop_integer_h_err_ub_oom_to_M :
    forall {M} `{HM : Monad M}
      `{HME : RAISE_ERROR M}
      `{HMU : RAISE_UB M}
      `{HMO : RAISE_OOM M}
      `{EQM : Monad.Eq1 M}
      `{LAWS : @Monad.MonadLawsE M EQM HM}
      `{REF : Reflexive (M dvalue) (@eq1 M EQM dvalue)}
      `{TRANS : Transitive (M dvalue) (@eq1 M EQM dvalue)}
      op a b res,
      @eval_iop_integer_h err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
                 (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) _ _ op a b =
        success_unERR_UB_OOM res ->
      @eval_iop_integer_h M HM HME HMU HMO op a b ≈ @ret M HM dvalue res.
  Proof.
    intros M HM HME HMU HMO EQM LAWS REF TRANS op a b res EVAL.
    destruct op; cbn in *.

    Ltac solve_iop a b :=
      destruct a, b; cbn in *;
      inversion EVAL; auto;
      try first
          [ repeat break_match; inversion EVAL; cbn; auto;
            unfold to_dvalue_OOM; cbn;
            match goal with
            | H: _ |- context [x <- ret ?v;; ret (?c x)]
              => eapply (bind_ret_l _ _ (fun x => ret (c x)))
            end
          | repeat break_match; inversion EVAL; cbn; auto;
            unfold to_dvalue_OOM; cbn;
            unfold lift_OOM;

            break_match; subst;
            inversion Heqs; inversion Heqe; subst;
            inversion Heqs; subst;

            match goal with
            | H: _ |- context [x <- ret ?v;; ret (?c x)]
              => eapply (bind_ret_l _ _ (fun x => ret (c x)))
            end
          ].

    - solve_iop a b.
    - solve_iop a b.
    - Opaque to_dvalue.
      destruct a, b; cbn in *; inversion EVAL; auto.
      apply to_dvalue_OOM_NoOom.

      Ltac solve_bind_res :=
        rewrite bind_ret_l;
        repeat break_match_goal; inversion EVAL; subst; auto.

      + rewrite bind_ret_l.
        repeat (break_match_goal; inversion EVAL; subst).

        setoid_rewrite Heqb in H1.
        inversion H1.
        reflexivity.

        setoid_rewrite Heqb in H1.
        inversion H1.
        reflexivity.
      + solve_bind_res.
      + solve_bind_res.
      + repeat break_match_goal;
          solve [ destruct (VellvmIntegers.mmul x x0); cbn in *; inversion EVAL;
                  apply to_dvalue_OOM_NoOom
                | unfold lift_OOM; break_match_goal; cbn in *; inversion EVAL;
                  rewrite bind_ret_l; repeat break_match_goal; inversion EVAL;
                  subst; solve [auto]
            ].
    - destruct a, b; cbn in *; inversion EVAL; auto.

      + rewrite bind_ret_l.
        cbn.
        break_match_goal.
        cbn in *.
        inversion H0.
        reflexivity.
  Abort.

  Lemma concretize_icmp_inv:
    forall {M} `{HM: Monad M} `{HME: RAISE_ERROR M} op x y dv,
      concretize_succeeds (UVALUE_ICmp op x y) ->
      concretize (UVALUE_ICmp op x y) dv ->
      exists dx dy,
        concretize_succeeds x /\
        concretize x dx /\
        concretize_succeeds y /\
        concretize y dy /\
        @eval_icmp M HM HME op dx dy = ret dv.
  Proof.
    intros M HM HME op x y dv SUCC CONC.

    rewrite concretize_equation in CONC.
    red in CONC.
    rewrite concretize_uvalueM_equation in CONC.

    cbn in CONC.
    destruct CONC as (ma & k' & pama & eqm & REST).

    destruct ma as [[[[[[[oom_ma] | [[ub_ma] | [[err_ma] | a]]]]]]]] eqn:Hma.
    (* First thing is oom... *)
    { cbn in SUCC.
      unfold concretize_succeeds, concretize_fails in SUCC.
      red in SUCC.
      exfalso. apply SUCC.

      red. rewrite concretize_uvalueM_equation. cbn.
      unfold bind_RefineProp.
      eexists. exists ret.

      split; [apply pama|].
      split; auto. left. reflexivity.
    }

    (* First thing is ub... *)
    (* This should be ruled out by SUCC *)
    { cbn in SUCC.
      unfold concretize_succeeds, concretize_fails in SUCC.
      red in SUCC.

      exfalso. apply SUCC.

      red. rewrite concretize_uvalueM_equation. cbn.
      unfold bind_RefineProp.

      eexists. exists ret.

      split; [apply pama|].
      split; auto.
    }

    (* First thing is failure... *)
    (* This should be ruled out by SUCC *)
    { cbn in SUCC.
      unfold concretize_succeeds, concretize_fails in SUCC.
      red in SUCC.

      exfalso. apply SUCC.

      red. rewrite concretize_uvalueM_equation. cbn.

      unfold bind_RefineProp. eexists. exists ret.

      split; [apply pama|].
      split; auto.
    }

    destruct REST as [FAILS | REST].
    inversion FAILS.
    specialize (REST a).
    forward REST; [reflexivity|].

    destruct REST as (mb & kb & pbmb & eqmb & REST).

    unfold concretize_succeeds, concretize_fails, concretize_u in SUCC.
    rewrite concretize_uvalueM_equation in SUCC.
    cbn in SUCC.
    unfold bind_RefineProp in SUCC.

    destruct mb as [[[[[[[oom_mb] | [[ub_mb] | [[err_mb] | b]]]]]]]] eqn:Hmb.

    (* y raises OOM *)
    { exfalso.
      apply SUCC.

      eexists.
      exists (fun _ => raise_ub "").

      split; [apply pama|]. split; cbn; auto.

      right. intros a0 H; subst.
      eexists. exists ret.
      split; [apply pbmb|]. cbn. split; auto.

      cbn in eqmb. cbn in *.

      destruct (k' a0) as [[[[[[[oom_k'a0] | [[ub_k'a0] | [[err_k'a0] | k'a0]]]]]]]];
        cbn in *; contradiction.
    }

    (* y raises UB *)
    { exfalso. apply SUCC.

      eexists. exists (fun _ => raise_ub "").
      split; [apply pama|]. split; cbn; auto.
      right. intros a0 H; subst. eexists.
      exists ret.
      split; [apply pbmb|].
      split; auto.
    }

    (* y fails *)
    { exfalso. apply SUCC.

      eexists. exists (fun _ => raise_ub "").
      split; [apply pama|]. split; cbn; auto.

      right. intros a0 H; subst.
      eexists. exists ret.

      split; [apply pbmb|].
      split; auto.
    }

    (* Both x and y successfully concretized. *)

  (*        Now eval_iop must succeed too. *)
  (*    *)
    destruct REST as [FAILS | REST].
    inversion FAILS.
    specialize (REST b).
    forward REST; [reflexivity|].

    destruct (eval_icmp op a b) as [[[[[[[oom_z] | [[ub_z] | [[err_z] | z]]]]]]]] eqn:Hmz.

    (* Eval raises OOM *)
    { exfalso. apply SUCC.

      eexists. exists (fun _ => raise_ub "").

      split; [apply pama|]. split; cbn; auto.

      right. intros a0 H; subst.

      eexists. exists (fun _ => raise_ub "").

      split; [apply pbmb|].
      split; cbn; auto.

      right.
      intros a H; subst.

      rewrite Hmz.
      destruct (kb a) as [[[[[[[oom_kba] | [[ub_kba] | [[err_kba] | kba]]]]]]]] eqn:Hkba;
        cbn in *; try contradiction.
      rewrite Hkba in eqmb.
      cbn in eqmb.
      destruct (k' a0) as [[[[[[[oom_k'a0] | [[ub_k'a0] | [[err_k'a0] | k'a0]]]]]]]] eqn:Hk'a0;
        cbn in eqm; contradiction.
    }

    (* Eval raises ub *)
    { exfalso. apply SUCC.

      eexists. exists (fun _ => raise_ub "").

      split; [apply pama|].
      split; cbn; auto.

      right.
      intros a0 H; subst.

      eexists.
      exists (fun _ => raise_ub "").

      split; [apply pbmb|].
      split; cbn; auto.

      right.
      intros a H; subst.

      rewrite Hmz.
      reflexivity.
    }

    (* Eval fails *)
    { exfalso.
      apply SUCC.

      eexists.
      exists (fun _ => raise_ub "").

      split; [apply pama|].
      split; cbn; auto.

      right.
      intros a0 H; subst.

      eexists.
      exists (fun _ => raise_ub "").

      split; [apply pbmb|].
      split; cbn; auto.

      right.
      intros a H; subst.

      rewrite Hmz.
      reflexivity.
    }

    cbn in eqmb.
    cbn in eqm.

    destruct (kb b) as [[[[[[[oom_kbb] | [[ub_kbb] | [[err_kbb] | kbb]]]]]]]] eqn:Hkbb;
      try contradiction; subst.
    cbn in eqmb.

    destruct (k' a) as [[[[[[[oom_k'a] | [[ub_k'a] | [[err_k'a] | k'a]]]]]]]] eqn:Hk'a;
      try contradiction; subst.
    cbn in eqm; subst.

    exists a. exists b.
    repeat split; auto.

    { unfold concretize_succeeds, concretize_fails, concretize_u.
      intros CONC.
      apply SUCC.

      eexists.
      exists (fun _ => raise_ub "").

      split.
      apply CONC.

      split; cbn; auto.
    }

    { unfold concretize_succeeds, concretize_fails, concretize_u.
      intros CONC.
      apply SUCC.

      eexists.
      exists (fun _ => raise_ub "").

      split; [apply pama|].
      split; cbn; auto.

      right.
      intros a0 H; subst.

      eexists.
      exists (fun _ => raise_ub "").

      split.
      apply CONC.

      split; cbn; auto.
    }

    apply eval_icmp_err_ub_oom_to_M.
    rewrite Hmz.
    cbn.

    destruct (k' a) as [[[[[[[oom_k'a] | [[ub_k'a] | [[err_k'a] | k'a]]]]]]]] eqn:Hk'a;
      cbn in eqm; try contradiction.
    cbn in eqmb.
    subst; auto.
  Qed.

  Lemma concretize_ibinop_inv:
    forall op x y dv,
      concretize_succeeds (UVALUE_IBinop op x y) ->
      concretize (UVALUE_IBinop op x y) dv ->
      exists dx dy,
        concretize_succeeds x /\
        concretize x dx /\
        concretize_succeeds y /\
        concretize y dy /\
        @eval_iop err_ub_oom _ _ _ _ op dx dy = ret dv.
  Proof.
    intros op x y dv SUCC CONC.

    rewrite concretize_equation in CONC.
    red in CONC.
    rewrite concretize_uvalueM_equation in CONC.

    cbn in CONC.
    destruct CONC as (ma & k' & pama & eqm & REST).

    destruct ma as [[[[[[[oom_ma] | [[ub_ma] | [[err_ma] | a]]]]]]]] eqn:Hma.

    (* First thing is oom... *)
    { cbn in SUCC.
      unfold concretize_succeeds, concretize_fails in SUCC.
      red in SUCC.

      exfalso.
      apply SUCC.

      red. rewrite concretize_uvalueM_equation.
      cbn.

      unfold bind_RefineProp.

      eexists.
      exists ret.

      split; [apply pama|].
      split; auto.

      left.
      reflexivity.
    }

    (* First thing is ub... *)
    (* This should be ruled out by SUCC *)
    { cbn in SUCC.
      unfold concretize_succeeds, concretize_fails in SUCC.
      red in SUCC.

      exfalso.
      apply SUCC.

      red. rewrite concretize_uvalueM_equation.
      cbn.

      unfold bind_RefineProp.

      eexists.
      exists ret.

      split; [apply pama|].
      split; auto.
    }

    (* First thing is failure... *)
    (* This should be ruled out by SUCC *)
    { cbn in SUCC.
      unfold concretize_succeeds, concretize_fails in SUCC.
      red in SUCC.

      exfalso.
      apply SUCC.

      red. rewrite concretize_uvalueM_equation.
      cbn.

      unfold bind_RefineProp.

      eexists.
      exists ret.

      split; [apply pama|].
      split; auto.
    }

    destruct REST as [FAILS | REST].
    inversion FAILS.
    specialize (REST a).
    forward REST; [reflexivity|].

    destruct REST as (mb & kb & pbmb & eqmb & REST).

    unfold concretize_succeeds, concretize_fails, concretize_u in SUCC.
    rewrite concretize_uvalueM_equation in SUCC.
    cbn in SUCC.
    unfold bind_RefineProp in SUCC.

    destruct mb as [[[[[[[oom_mb] | [[ub_mb] | [[err_mb] | b]]]]]]]] eqn:Hmb.

    (* y raises OOM *)
    { exfalso.
      apply SUCC.

      eexists.
      exists (fun _ => raise_ub "").


      split; [apply pama|].
      split; cbn; auto.

      right.
      intros a0 H; subst.

      eexists.
      exists ret.

      split; [apply pbmb|].
      cbn.
      split; auto.

      cbn in eqmb.
      cbn in *.

      destruct (k' a0) as [[[[[[[oom_k'a0] | [[ub_k'a0] | [[err_k'a0] | k'a0]]]]]]]];
        cbn in *; contradiction.
    }

    (* y raises UB *)
    { exfalso.
      apply SUCC.

      eexists.
      exists (fun _ => raise_ub "").


      split; [apply pama|].
      split; cbn; auto.

      right.
      intros a0 H; subst.

      eexists.
      exists ret.

      split; [apply pbmb|].
      split; auto.
    }

    (* y fails *)
    { exfalso.
      apply SUCC.

      eexists.
      exists (fun _ => raise_ub "").


      split; [apply pama|].
      split; cbn; auto.

      right.
      intros a0 H; subst.

      eexists.
      exists ret.

      split; [apply pbmb|].
      split; auto.
    }

    (* Both x and y successfully concretized.

         Now eval_iop must succeed too.
     *)
    destruct REST as [FAILS | REST].
    inversion FAILS.
    specialize (REST b).
    forward REST; [reflexivity|].

    destruct (eval_iop op a b) as [[[[[[[oom_z] | [[ub_z] | [[err_z] | z]]]]]]]] eqn:Hmz.

    (* Eval raises OOM *)
    { exfalso.
      apply SUCC.

      eexists.
      exists (fun _ => raise_ub "").

      split; [apply pama|].
      split; cbn; auto.

      right.
      intros a0 H; subst.

      eexists.
      exists (fun _ => raise_ub "").

      split; [apply pbmb|].
      split; cbn; auto.

      right.
      intros a H; subst.

      rewrite Hmz.
      destruct (kb a) as [[[[[[[oom_kba] | [[ub_kba] | [[err_kba] | kba]]]]]]]] eqn:Hkba;
        cbn in *; try contradiction.
      rewrite Hkba in eqmb.
      cbn in eqmb.
      destruct (k' a0) as [[[[[[[oom_k'a0] | [[ub_k'a0] | [[err_k'a0] | k'a0]]]]]]]] eqn:Hk'a0;
        cbn in eqm; contradiction.
    }

    (* Eval raises ub *)
    { exfalso.
      apply SUCC.

      eexists.
      exists (fun _ => raise_ub "").

      split; [apply pama|].
      split; cbn; auto.

      right.
      intros a0 H; subst.

      eexists.
      exists (fun _ => raise_ub "").

      split; [apply pbmb|].
      split; cbn; auto.

      right.
      intros a H; subst.

      rewrite Hmz.
      reflexivity.
    }

    (* Eval fails *)
    { exfalso.
      apply SUCC.

      eexists.
      exists (fun _ => raise_ub "").

      split; [apply pama|].
      split; cbn; auto.

      right.
      intros a0 H; subst.

      eexists.
      exists (fun _ => raise_ub "").

      split; [apply pbmb|].
      split; cbn; auto.

      right.
      intros a H; subst.

      rewrite Hmz.
      reflexivity.
    }

    cbn in eqmb.
    cbn in eqm.

    destruct (kb b) as [[[[[[[oom_kbb] | [[ub_kbb] | [[err_kbb] | kbb]]]]]]]] eqn:Hkbb;
      try contradiction; subst.
    cbn in eqmb.

    destruct (k' a) as [[[[[[[oom_k'a] | [[ub_k'a] | [[err_k'a] | k'a]]]]]]]] eqn:Hk'a;
      try contradiction; subst.
    cbn in eqm; subst.

    exists a. exists b.
    repeat split; auto.

    { unfold concretize_succeeds, concretize_fails, concretize_u.
      intros CONC.
      apply SUCC.

      eexists.
      exists (fun _ => raise_ub "").

      split.
      apply CONC.

      split; cbn; auto.
    }

    { unfold concretize_succeeds, concretize_fails, concretize_u.
      intros CONC.
      apply SUCC.

      eexists.
      exists (fun _ => raise_ub "").

      split; [apply pama|].
      split; cbn; auto.

      right.
      intros a0 H; subst.

      eexists.
      exists (fun _ => raise_ub "").

      split.
      apply CONC.

      split; cbn; auto.
    }

    cbn in *.
    destruct (k' a) as [[[[[[[oom_k'a] | [[ub_k'a] | [[err_k'a] | k'a]]]]]]]] eqn:Hk'a;
      cbn in eqm; try contradiction.
    cbn in eqmb.
    subst; auto.
  Qed.

  Lemma concretize_succeeds_poison :
    forall dt,
      concretize_succeeds (UVALUE_Poison dt).
  Proof.
    induction dt;
      unfold concretize_succeeds, concretize_fails, concretize_u;
      rewrite concretize_uvalueM_equation;
      cbn; auto.
  Qed.

  Lemma concretize_dtyp :
    forall uv dv dt,
      uvalue_has_dtyp uv dt ->
      concretize_succeeds uv ->
      concretize uv dv ->
      dvalue_has_dtyp dv dt.
  Proof.
    (* intros uv dv dt DTYP SUCC CONC. *)
    (* generalize dependent dv. *)
    (* induction DTYP; intros dv CONC. *)
    (* unfold concretize in CONC. *)
    (* cbn in CONC. *)
    (* unfold concretize_u in CONC. *)
    (* cbn in CONC. *)
    (* rewrite concretize_uvalueM_equation in CONC. *)
    (* cbn in CONC. inversion CONC. subst; solve [auto | constructor; try solve_no_void]. *)

    (* Ltac unfold_concretize H := *)
    (*   unfold concretize, concretize_u in H; *)
    (*   rewrite concretize_uvalueM_equation in H. *)

    (* Ltac invert_concretize H := *)
    (*   unfold_concretize H; inversion H. *)

    (* 1-7: invert_concretize CONC; subst; solve [auto | constructor; try solve_no_void]. *)

    (* (* Poison structs *) *)
    (* { invert_concretize CONC. *)
    (*   constructor. *)
    (*   rewrite NO_VOID_equation. *)
    (*   cbn. auto. *)
    (* } *)
    (* { invert_concretize CONC. *)
    (*   constructor. *)

    (*   subst. *)

    (*   (* Recover NO_VOID information *) *)
    (*   specialize (IHDTYP (concretize_succeeds_poison _) (DVALUE_Poison dt)). *)
    (*   forward IHDTYP. *)
    (*   { do 2 red. *)
    (*     rewrite concretize_uvalueM_equation; cbn. *)
    (*     reflexivity. *)
    (*   } *)

    (*   specialize (IHDTYP0 (concretize_succeeds_poison _) (DVALUE_Poison (DTYPE_Struct dts))). *)
    (*   forward IHDTYP0. *)
    (*   { do 2 red. *)
    (*     rewrite concretize_uvalueM_equation; cbn. *)
    (*     reflexivity. *)
    (*   } *)

    (*   inversion IHDTYP; subst. *)
    (*   inversion IHDTYP0; subst. *)

    (*   solve_no_void. *)
    (* } *)

    (* (* Poison packed structs *) *)
    (* { invert_concretize CONC. *)
    (*   constructor. *)
    (*   rewrite NO_VOID_equation. *)
    (*   cbn. auto. *)
    (* } *)
    (* { invert_concretize CONC. *)
    (*   constructor. *)

    (*   subst. *)

    (*   (* Recover NO_VOID information *) *)
    (*   specialize (IHDTYP (concretize_succeeds_poison _) (DVALUE_Poison dt)). *)
    (*   forward IHDTYP. *)
    (*   { do 2 red. *)
    (*     rewrite concretize_uvalueM_equation; cbn. *)
    (*     reflexivity. *)
    (*   } *)

    (*   specialize (IHDTYP0 (concretize_succeeds_poison _) (DVALUE_Poison (DTYPE_Packed_struct dts))). *)
    (*   forward IHDTYP0. *)
    (*   { do 2 red. *)
    (*     rewrite concretize_uvalueM_equation; cbn. *)
    (*     reflexivity. *)
    (*   } *)

    (*   inversion IHDTYP; subst. *)
    (*   inversion IHDTYP0; subst. *)

    (*   solve_no_void. *)
    (* } *)

    (* 1-11: invert_concretize CONC; subst; solve [auto | constructor; try solve_no_void]. *)

    (* (* Structs *) *)
    (* { (* Nil structs *) *)
    (*   unfold_concretize CONC. *)
    (*   cbn in CONC. *)
    (*   unfold bind_RefineProp in CONC. *)
    (*   destruct CONC as (ma & k' & pama & eqm & REST). *)
    (*   destruct ma as [[[[[[[oom_ma] | [[ub_ma] | [[err_ma] | a]]]]]]]] eqn:Hma; *)
    (*     cbn; auto; try contradiction. *)
    (*   subst. *)

    (*   destruct REST as [FAILS | REST]. *)
    (*   inversion FAILS. *)
    (*   specialize (REST nil). *)
    (*   forward REST; [reflexivity|]. *)

    (*   destruct (k' nil) as [[[[[[[oom_k'nil] | [[ub_k'nil] | [[err_k'nil] | k'nil]]]]]]]] eqn:Hk'nil; *)
    (*     cbn; auto; try contradiction; *)
    (*   subst; *)

    (*   cbn in eqm; *)
    (*   rewrite Hk'nil in eqm; *)
    (*   cbn in eqm. *)
    (*   contradiction. *)

    (*   subst; constructor. *)
    (* } *)
    (* { (* Non-nil structs *) *)
    (*   unfold_concretize CONC. *)
    (*   cbn in CONC. *)

    (*   (* Urgggghhh... Missing proper instance, I think *) *)
    (*   Fail rewrite RefineProp_bind_bind in CONC. *)

    (*   epose proof RefineProp_Proper_bind. *)
    (*   Import Morphisms. *)
    (*   unfold Proper, respectful in H. *)
    (*   eapply H in CONC; cycle 1. *)

    (*   admit. *)
    (*   admit. *)
    (*   admit. *)
    (* } *)

    (* (* Packed Structs *) *)
    (* admit. *)
    (* admit. *)

    (* (* Arrays *) *)
    (* { *)
    (*   admit. *)

    (* } *)

    (* (* Vectors *) *)
    (* { admit. *)

    (* } *)

    (* Ltac ret_inv := *)
    (*   match goal with *)
    (*   | |- MonadEq1Laws.Eq1_ret_inv _ => *)
    (*         let H := fresh "H" in *)
    (*         constructor; intros * H; subst; inv H; auto *)
    (*   end. *)

    (* Ltac euo_crush := *)
    (*   match goal with *)
    (*   | |- MonadEq1Laws.Eq1_ret_inv _ => ret_inv *)
    (*   | |- NoFailsRet err_ub_oom => constructor; intros; *)
    (*                                 eapply MReturns_MFails; apply MReturns_ret; eauto *)
    (*   | |- MFails_ERROR err_ub_oom => constructor; intros; constructor *)
    (*   | |- MFails_UB err_ub_oom => constructor; intros; constructor *)
    (*   end. *)

    (* (* Binops *) *)
    (* { eapply concretize_ibinop_inv in CONC; eauto. *)
    (*   destruct CONC as (dx & dy & SUCCx & CONCx & SUCCy & CONCy & EVAL). *)

    (*   eapply eval_iop_dtyp_i; try euo_crush. *)
    (*   eapply IHDTYP1; eauto. *)
    (*   eapply IHDTYP2; eauto. *)
    (*   rewrite EVAL. *)
    (*   reflexivity. *)
    (* } *)

    (* { eapply concretize_ibinop_inv in CONC; auto. *)
    (*   destruct CONC as (dx & dy & SUCCx & CONCx & SUCCy & CONCy & EVAL). *)

    (*   eapply eval_iop_dtyp_iptr; try euo_crush. *)
    (*   eapply IHDTYP1; eauto. *)
    (*   eapply IHDTYP2; eauto. *)
    (*   rewrite EVAL. *)
    (*   reflexivity. *)
    (* } *)

    (* (* Integer Comparisons *) *)
    (* admit. *)
    (* admit. *)
    (* admit. *)
    (* admit. *)
    (* admit. *)

    (* (* Floating point comparisons *) *)
    (* admit. *)
    (* admit. *)
    (* admit. *)
    (* admit. *)

    (* (* Conversions *) *)
    (* admit. *)
    (* admit. *)
    (* admit. *)
    (* admit. *)
    (* admit. *)
    (* admit. *)
    (* admit. *)
    (* admit. *)
    (* admit. *)
    (* admit. *)
    (* admit. *)
    (* admit. *)

    (* (* GetElementPtr *) *)
    (* admit. *)

    (* (* ExtractElement *) *)
    (* admit. *)
    (* admit. *)

    (* (* InsertElement *) *)
    (* admit. *)
    (* admit. *)

    (* (* ShuffleVector *) *)
    (* admit. *)

    (* (* ExtractValue *) *)
    (* admit. *)
    (* admit. *)
    (* admit. *)
    (* admit. *)
    (* admit. *)
    (* admit. *)

    (* (* InsertValue *) *)
    (* admit. *)

    (* (* Select *) *)
    (* admit. *)
    (* admit. *)

    (* (* ConcatBytes *) *)
    (* admit. *)
  Admitted.


(*   Lemma serialize_sbytes_deserialize_sbytes : *)
(*     forall uv dt sid prov sbytes , *)
(*       uvalue_has_dtyp uv dt -> *)
(*       is_supported dt -> *)
(*       sizeof_dtyp dt > 0 -> *)
(*       ErrSID_evals_to (serialize_sbytes uv dt) sid prov sbytes -> *)
(*       deserialize_sbytes sbytes dt = inr uv. *)
(*   Proof. *)
(*     intros uv dt sid prov sbytes TYP SUP SIZE SER. *)
(*     induction TYP. *)

(*     Ltac solve_deserialize_local := *)
(*       match goal with *)
(*       | SER : ErrSID_evals_to _ _ _ _ |- _ *)
(*         => rewrite serialize_sbytes_equation in SER; *)
(*           cbn in SER; inv SER; cbn; *)
(*           erewrite from_ubytes_to_ubytes; eauto; *)
(*           cbn in *; *)
(*           match goal with *)
(*           | H: context [BYTE.to_ubytes ?uv ?dt ?sid] |- _ *)
(*             => destruct (BYTE.to_ubytes uv dt sid) eqn:?; *)
(*                        inversion H; subst; eauto   *)
(*           end *)
(*       end. *)

(*     1-6: match goal with *)
(*           (* Try easy case first for speedup *) *)
(*           | |- _ = inr ?x => *)
(*               tactic_on_non_aggregate_uvalues x ltac:(try solve_deserialize_local) *)
(*           end. *)

(*     (* Poison arrays *) *)
(*     { admit. *)
(*     } *)

(*     (* Poison vectors *) *)
(*     { admit. *)
(*     } *)

(*     (* Poison structs *) *)
(*     { admit. *)
(*     } *)

(*     { admit. *)
(*     } *)

(*     (* Poison packed structs *) *)
(*     { admit. *)
(*     } *)

(*     { admit. *)
(*     } *)

(*     (* Poison *) *)
(*     { destruct H as (NV & NSTRUCT & NPACKED & NARRAY & NVECTOR). *)
(*       destruct t; *)
(*       match goal with *)
(*       (* Try easy case first for speedup *) *)
(*       | |- _ = inr (UVALUE_Poison DynamicTypes.DTYPE_Void) => *)
(*         cbn in NV; contradiction *)
(*       | |- _ = inr (UVALUE_Poison ?x) => *)
(*         tactic_on_non_aggregate_dtyps x ltac:(try solve_deserialize_local) *)
(*       end. *)

(*       all: exfalso; *)
(*         match goal with *)
(*         | H: _ |- _ => *)
(*           solve [eapply H; eauto] *)
(*         end. *)
(*     } *)

(*     (* Undef arrays *) *)
(*     { admit. *)
(*     } *)

(*     (* Undef vectors *) *)
(*     { admit. *)
(*     } *)

(*     (* Undef structs *) *)
(*     { admit. *)
(*     } *)

(*     { admit. *)
(*     } *)

(*     (* Undef packed structs *) *)
(*     { admit. *)
(*     } *)

(*     { admit. *)
(*     } *)


(*     (* Undef *) *)
(*     { destruct H as (NV & NSTRUCT & NPACKED & NARRAY & NVECTOR). *)
(*       destruct t; *)
(*       match goal with *)
(*       (* Try easy case first for speedup *) *)
(*       | |- _ = inr (UVALUE_Undef DynamicTypes.DTYPE_Void) => *)
(*         cbn in NV; contradiction *)
(*       | |- _ = inr (UVALUE_Undef ?x) => *)
(*         tactic_on_non_aggregate_dtyps x ltac:(try solve_deserialize_local) *)
(*       end. *)

(*       all: exfalso; *)
(*         match goal with *)
(*         | H: _ |- _ => *)
(*           solve [eapply H; eauto] *)
(*         end. *)
(*     } *)

(*     match goal with *)
(*     (* Try easy case first for speedup *) *)
(*     | |- _ = inr ?x => *)
(*       tactic_on_non_aggregate_uvalues x ltac:(try solve_deserialize_local) *)
(*     end.     *)

(* (*     { destruct t. *) *)
(* (*       1-12: match goal with *) *)
(* (*           (* Try easy case first for speedup *) *) *)
(* (*           | |- _ = inr ?x => *) *)
(* (*             tactic_on_non_aggregate_uvalues x ltac:(try (rewrite serialize_sbytes_equation in SER; cbn in SER; inv SER; cbn; rewrite from_ubytes_to_ubytes; eauto)) *) *)
(* (*           end. *) *)

(* (*       (* No void undefs *) *) *)
(* (*       contradiction. *) *)

(* (*       (* Aggregates *) *) *)
(* (*       (* Arrays *) *) *)
(* (*       - rewrite serialize_sbytes_equation in SER. *) *)

(* (*         (* Errr...  *) *)

(* (*            Right hand side is:  *) *)

(* (*            inr (UVALUE_Undef (DynamicTypes.DTYPE_Array sz t)) *) *)

(* (*            Because this lemma is saying that if I serialize *) *)
(* (*            UVALUE_Undef (DynamicTypes.DTYPE_Array sz t), then when I *) *)
(* (*            deserialize the result I should get *) *)
(* (*            UVALUE_Undef (DynamicTypes.DTYPE_Array sz t) back. *) *)

(* (*            I've added special cases for aggregate types in *) *)
(* (*            serialize_sbytes for undef so they get serialized with *) *)
(* (*            undef for each element / field... *) *)

(* (*            The problem is that when these are deserialized I should *) *)
(* (*            get, for instance... *) *)

(* (*            UVALUE_Array [UVALUE_Undef t; ... ; UVALUE_Undef t ] *) *)

(* (*            Instead of just *) *)

(* (*            UVALUE_Undef (DynamicTypes.DTYPE_Array sz t) *) *)

(* (*            These values should be equivalent, but they have different *) *)
(* (*            representations... *) *)
(* (*          *) *) *)
(* (*         (* unfold deserialize_sbytes,deserialize_sbytes_func. *) *) *)
(* (*         (* cbn. *) *) *)
(* (*         (* TODO: probably need an equation for rewriting *) *) *)

(* (*       match goal with *) *)
(* (*           (* Try easy case first for speedup *) *) *)
(* (*           | |- _ = inr ?x => *) *)
(* (*             tactic_on_non_aggregate_uvalues x ltac:(try (rewrite serialize_sbytes_equation in SER; cbn in SER; inv SER; cbn; rewrite from_ubytes_to_ubytes; eauto)) *) *)
(* (*           end. *) *)

(* (* (*       cbn. *) *) *)
(* (* (*       match goal with *) *) *)
(* (* (*       (* Try easy case first for speedup *) *) *) *)
(* (* (*       | |- _ = inr ?x => *) *) *)
(* (* (*         tactic_on_non_aggregate_uvalues x ltac:(try (rewrite serialize_sbytes_equation in SER; cbn in SER; inv SER; cbn; rewrite from_ubytes_to_ubytes; eauto)) *) *) *)
(* (* (*       end. *) *) *)


(* (* (*     } *) *) *)

(* (* (*     1-12: match goal with *) *) *)
(* (* (*           (* Try easy case first for speedup *) *) *) *)
(* (* (*           | |- _ = inr ?x => *) *) *)
(* (* (*             tactic_on_non_aggregate_uvalues x ltac:(try (rewrite serialize_sbytes_equation in SER; cbn in SER; inv SER; cbn; rewrite from_ubytes_to_ubytes; eauto)) *) *) *)
(* (* (*           end. *) *) *)

(* (* (*     { cbn in SER. *) *) *)
(* (* (*       inv SER. *) *) *)
(* (* (*       inv SUP. *) *) *)
(* (* (*       - cbn; rewrite from_ubytes_to_ubytes; [reflexivity|constructor|auto]. *) *) *)
(* (* (*       - cbn; rewrite from_ubytes_to_ubytes; [reflexivity|constructor|auto]. *) *) *)
(* (* (*       - cbn; rewrite from_ubytes_to_ubytes; [reflexivity|constructor|auto]. *) *) *)
(* (* (*       - cbn; rewrite from_ubytes_to_ubytes; [reflexivity|constructor|auto]. *) *) *)
(* (* (*       - cbn; rewrite from_ubytes_to_ubytes; [reflexivity|constructor|auto]. *) *) *)
(* (* (*       - (* Void... Shouldn't have void undef *) *) *) *)
(* (* (*         rewrite sizeof_dtyp_void in SIZE. lia. *) *) *)
(* (* (*       - cbn; rewrite from_ubytes_to_ubytes; [reflexivity|constructor|auto]. *) *) *)
(* (* (*       - cbn; rewrite from_ubytes_to_ubytes; [reflexivity|constructor|auto]. *) *) *)
(* (* (*       - (* Arrays... Aggregate types *) *) *) *)
(* (* (*         cbn. *) *) *)
(* (* (*         cbn; rewrite from_ubytes_to_ubytes; [reflexivity|constructor|auto]. *) *) *)

(* (* (*       cbn. *) *) *)
(* (* (*       rewrite from_ubytes_to_ubytes. *) *) *)
(* (* (*       reflexivity. *) *) *)
(* (* (*       unfold deserialize_sbytes, deserialize_sbytes_func. *) *) *)


(* (* (*       match goal with          (* Try easy case first for speedup *) *) *) *)
(* (* (*           | |- _ = inr ?x => *) *) *)
(* (* (*             tactic_on_non_aggregate_uvalues x ltac:(try (cbn in SER; inv SER; cbn; rewrite from_ubytes_to_ubytes; eauto)) *) *) *)
(* (* (*     end. *) *) *)

(* (* (*     cbn. *) *) *)
(* (* (*     cbn. *) *) *)


(* (* (*     cbn. *) *) *)
(* (* (*     cbn in SER. *) *) *)
(* (* (*     inv SER. *) *) *)
(* (* (*     cbn. *) *) *)
(* (* (*     rewrite from_ubytes_to_ubytes. *) *) *)
(* (* (*     eauto. *) *) *)
(* (* (* (*     match goal with *) *) *) *)
(* (* (* (*           (* Try easy case first for speedup *) *) *) *) *)
(* (* (* (*           | |- _ = inr ?x => *) *) *) *)
(* (* (* (*             tactic_on_non_aggregate_uvalues x ltac:(cbn in SER; inv SER) *) *) *) *)
(* (* (* (*           end; *) *) *) *)
(* (* (* (*       cbn; rewrite from_ubytes_to_ubytes; eauto. *) *) *) *)
(* (* (* (*     match goal with *) *) *) *)
(* (* (* (*           (* Try easy case first for speedup *) *) *) *) *)
(* (* (* (*           | |- _ = inr ?x => *) *) *) *)
(* (* (* (*             tactic_on_non_aggregate_uvalues x ltac:(cbn in SER; inv SER) *) *) *) *)
(* (* (* (*           end; *) *) *) *)
(* (* (* (*       cbn; rewrite from_ubytes_to_ubytes; eauto. *) *) *) *)
(* (* (* (*     match goal with *) *) *) *)
(* (* (* (*           (* Try easy case first for speedup *) *) *) *) *)
(* (* (* (*           | |- _ = inr ?x => *) *) *) *)
(* (* (* (*             tactic_on_non_aggregate_uvalues x ltac:(cbn in SER; inv SER) *) *) *) *)
(* (* (* (*           end; *) *) *) *)
(* (* (* (*       cbn; rewrite from_ubytes_to_ubytes; eauto. *) *) *) *)
(* (* (* (*     match goal with *) *) *) *)
(* (* (* (*           (* Try easy case first for speedup *) *) *) *) *)
(* (* (* (*           | |- _ = inr ?x => *) *) *) *)
(* (* (* (*             tactic_on_non_aggregate_uvalues x ltac:(cbn in SER; inv SER) *) *) *) *)
(* (* (* (*           end; *) *) *) *)
(* (* (* (*       cbn; rewrite from_ubytes_to_ubytes; eauto. *) *) *) *)
(* (* (* (*     match goal with *) *) *) *)
(* (* (* (*           (* Try easy case first for speedup *) *) *) *) *)
(* (* (* (*           | |- _ = inr ?x => *) *) *) *)
(* (* (* (*             tactic_on_non_aggregate_uvalues x ltac:(cbn in SER; inv SER) *) *) *) *)
(* (* (* (*           end; *) *) *) *)
(* (* (* (*       cbn; rewrite from_ubytes_to_ubytes; eauto. *) *) *) *)
(* (* (* (*     match goal with *) *) *) *)
(* (* (* (*           (* Try easy case first for speedup *) *) *) *) *)
(* (* (* (*           | |- _ = inr ?x => *) *) *) *)
(* (* (* (*             tactic_on_non_aggregate_uvalues x ltac:(cbn in SER; inv SER) *) *) *) *)
(* (* (* (*           end; *) *) *) *)
(* (* (* (*       cbn; rewrite from_ubytes_to_ubytes; eauto. *) *) *) *)

(* (* (* (*     - unfold deserialize_sbytes. *) *) *) *)
(* (* (* (*       cbn. *) *) *) *)
(* (* (* (* cbn in *; *) *) *) *)
(* (* (* (*         destruct t. *) *) *) *)
(* (* (* (*       cbn *) *) *) *)
(* (* (* (*       reflexivity. *) *) *) *)
(* (* (* (*       destruct t. *) *) *) *)

(* (* (* (*       cbn; inv SER. *) *) *) *)
(* (* (* (*           rewrite from_ubytes_to_ubytes; eauto. *) *) *) *)



(* (* (* (*     solve [match goal with *) *) *) *)
(* (* (* (*           (* Try easy case first for speedup *) *) *) *) *)
(* (* (* (*           | |- _ = inr ?x => *) *) *) *)
(* (* (* (*             tactic_on_non_aggregate_uvalues x ltac:(cbn in SER; inv SER) *) *) *) *)
(* (* (* (*           end; *) *) *) *)
(* (* (* (*       cbn; rewrite from_ubytes_to_ubytes; eauto]. *) *) *) *)
(* (* (* (*     match goal with *) *) *) *)
(* (* (* (*           (* Try easy case first for speedup *) *) *) *) *)
(* (* (* (*           | |- _ = inr ?x => *) *) *) *)
(* (* (* (*             tactic_on_non_aggregate_uvalues x ltac:(cbn in SER; inv SER) *) *) *) *)
(* (* (* (*           end; *) *) *) *)
(* (* (* (*       cbn; rewrite from_ubytes_to_ubytes; eauto. *) *) *) *)
(* (* (* (*     match goal with *) *) *) *)
(* (* (* (*           (* Try easy case first for speedup *) *) *) *) *)
(* (* (* (*           | |- _ = inr ?x => *) *) *) *)
(* (* (* (*             tactic_on_non_aggregate_uvalues x ltac:(cbn in SER; inv SER) *) *) *) *)
(* (* (* (*           end; *) *) *) *)
(* (* (* (*       cbn; rewrite from_ubytes_to_ubytes; eauto. *) *) *) *)
(* (* (* (*     match goal with *) *) *) *)
(* (* (* (*           (* Try easy case first for speedup *) *) *) *) *)
(* (* (* (*           | |- _ = inr ?x => *) *) *) *)
(* (* (* (*             tactic_on_non_aggregate_uvalues x ltac:(cbn in SER; inv SER) *) *) *) *)
(* (* (* (*           end; *) *) *) *)
(* (* (* (*       cbn; rewrite from_ubytes_to_ubytes; eauto. *) *) *) *)
(* (* (* (*     match goal with *) *) *) *)
(* (* (* (*           (* Try easy case first for speedup *) *) *) *) *)
(* (* (* (*           | |- _ = inr ?x => *) *) *) *)
(* (* (* (*             tactic_on_non_aggregate_uvalues x ltac:(cbn in SER; inv SER) *) *) *) *)
(* (* (* (*           end; *) *) *) *)
(* (* (* (*       cbn; rewrite from_ubytes_to_ubytes; eauto. *) *) *) *)
(* (* (* (*     match goal with *) *) *) *)
(* (* (* (*           (* Try easy case first for speedup *) *) *) *) *)
(* (* (* (*           | |- _ = inr ?x => *) *) *) *)
(* (* (* (*             tactic_on_non_aggregate_uvalues x ltac:(cbn in SER; inv SER) *) *) *) *)
(* (* (* (*           end; *) *) *) *)
(* (* (* (*       cbn; rewrite from_ubytes_to_ubytes; eauto. *) *) *) *)


(* (* (* (*     49: { eval_serialize_sbytes_hyp. *) *) *) *)
(* (* (* (*     56: { cbn in SER. destruct bytes. cbn in *. } *) *) *) *)
(* (* (* (*     all:eval_serialize_sbytes_hyp. *) *) *) *)
(* (* (* (*     1-30:eval_serialize_sbytes_hyp. *) *) *) *)
(* (* (* (*     12: { *) *) *) *)
(* (* (* (*       eval_serialize_sbytes_hyp. *) *) *) *)

(* (* (* (*       rewrite serialize_sbytes_equation in SER. *) *) *) *)
(* (* (* (*     } *) *) *) *)
(* (* (* (*     rewrite serialize_sbytes_equation in SER. *) *) *) *)
(* (* (* (*       try solve [cbn in SER; inv SER; cbn; rewrite from_ubytes_to_ubytes; eauto]. *) *) *) *)


(* (* (* (*     induction TYP; *) *) *) *)
(* (* (* (*       try solve [unfold serialize_sbytes in SER; *) *) *) *)
(* (* (* (*                  inv SER; *) *) *) *)
(* (* (* (*                  unfold deserialize_sbytes; *) *) *) *)
(* (* (* (*                  rewrite from_ubytes_to_ubytes; eauto *) *) *) *)
(* (* (* (*                 | cbn in *; *) *) *) *)
(* (* (* (*                   match goal with *) *) *) *)
(* (* (* (*                   | |- deserialize_sbytes _ ?t = _ => *) *) *) *)
(* (* (* (*                     cbn in *; *) *) *) *)
(* (* (* (*                     destruct t; cbn; inv SER; *) *) *) *)
(* (* (* (*                     rewrite from_ubytes_to_ubytes; eauto *) *) *) *)
(* (* (* (*                   end *) *) *) *)
(* (* (* (*                 ]. *) *) *) *)
(* (* (* (*     - inv SUP; exfalso; apply H; constructor. *) *) *) *)
(* (* (* (*     - rewrite sizeof_dtyp_void in SIZE. inv SIZE. *) *) *) *)
(* (* (* (*   Qed. *) *) *) *)
(*   Admitted. *)

    (** ** Deserialize - Serialize
        Starting from a dvalue [val] whose [dtyp] is [t], if:
        1. we serialize [val], getting a [list SByte]
        2. we add all these bytes to the memory block, starting from the position [off], getting back a new [mem_block] m'
        3. we lookup in this new memory [m'] the indices starting from [off] for the size of [t], getting back a [list SByte]
        4. we deserialize this final list of bytes
        then we should get back the initial value [val], albeit injected into [uvalue].

        The proof should go by induction over [TYP] I think, and rely on [lookup_all_index_add] notably.
     *)
    (* Lemma deserialize_serialize : forall val dt sid prov bytes, *)
    (*     uvalue_has_dtyp val dt -> *)
    (*     ErrSID_evals_to (serialize_sbytes val dt) sid prov bytes -> *)
    (*     deserialize_sbytes bytes dt = inr val. *)
    (* Proof. *)
    (*   intros val dt sid prov bytes TYP SER. *)
    (*   induction TYP. *)
    (*   - cbn in SER; inv SER. *)
    (*     cbn. *)
    (* Admitted. *)

    (* Lemma deserialize_serialize : forall val t (TYP : dvalue_has_dtyp val t), *)
    (*     forall off (bytes : mem_block) (SUP : is_supported t), *)
    (*       deserialize_sbytes (lookup_all_index off (sizeof_dtyp t) (add_all_index (serialize_dvalue val) off bytes) SUndef) t = dvalue_to_uvalue val. *)
    (* Proof. *)
    (*   induction 1; try auto; intros; *)
    (*     match goal with *)
    (*     | H: is_supported ?t |- _ => *)
    (*       try solve [inversion H] *)
    (*     end. *)
    (*   - unroll_lookup_all_index; cbn; f_equal. *)
    (*   - unroll_lookup_all_index; cbn; f_equal. *)
    (*     pose proof (unsigned_I1_in_range x). *)
    (*     assert (EQ :DynamicValues.Int1.unsigned x / 256 = 0). *)
    (*     apply Z.div_small; lia. *)
    (*     rewrite EQ. *)
    (*     repeat rewrite Zdiv_0_l. *)
    (*     repeat rewrite Byte.unsigned_repr. *)
    (*     all: unfold Byte.max_unsigned, Byte.modulus; cbn; try lia. *)
    (*     rewrite Z.add_0_r. *)
    (*     apply DynamicValues.Int1.repr_unsigned. *)
    (*   - solve_integer_deserialize. *)
    (*   - solve_integer_deserialize. *)
    (*   - solve_integer_deserialize. *)
    (*   - inversion SUP; subst; *)
    (*     exfalso; apply H; constructor. *)
    (*   - unroll_lookup_all_index; cbn; f_equal. *)
    (*     clear bytes off. *)
    (*     remember (Float.to_bits x) as xb. *)
    (*     pose proof (unsigned_I64_in_range xb). *)
    (*     repeat rewrite Byte.unsigned_repr_eq. *)
    (*     unfold Byte.modulus, Byte.wordsize, Wordsize_8.wordsize; cbn. *)
    (*     replace (two_power_nat 8) with 256 by reflexivity. *)
    (*     remember (Int64.unsigned xb) as xbv. *)
    (*     match goal with *)
    (*     | [|- context[Int64.repr ?zv]] => replace zv with xbv *)
    (*     end. *)
    (*     + *)
    (*       subst. *)
    (*       rewrite Int64.repr_unsigned. *)
    (*       apply Float.of_to_bits. *)
    (*     + *)
    (*       (* this is the same goal as I64 branch! *) *)
    (*       clear -H. *)
    (*       rewrite Z.add_0_r. *)
    (*       unfold Z.modulo. *)
    (*       repeat break_let. *)
    (*       repeat match goal with *)
    (*              | [H : Z.div_eucl _ _ = _ |- _] => apply Z_div_mod' in H; [destruct H | lia] *)
    (*              end. *)
    (*       subst. *)
    (*       repeat *)
    (*         match goal with *)
    (*         | H: context [(?d * ?x + ?z) / ?d] |- _ => *)
    (*           rewrite div_add_lemma in H; [|lia]; subst *)
    (*         end. *)
    (*       lia. *)
    (*   - unroll_lookup_all_index; cbn; f_equal. *)
    (*     clear bytes off. *)
    (*     remember (Float32.to_bits x) as xb. *)
    (*     pose proof (unsigned_I32_in_range xb). *)
    (*     repeat rewrite Byte.unsigned_repr_eq. *)
    (*     unfold Byte.modulus, Byte.wordsize, Wordsize_8.wordsize; cbn. *)
    (*     replace (two_power_nat 8) with 256 by reflexivity. *)
    (*     remember (Int32.unsigned xb) as xbv. *)
    (*     match goal with *)
    (*     | [|- context[Int32.repr ?zv]] => replace zv with xbv *)
    (*     end. *)
    (*     + *)
    (*       subst. *)
    (*       rewrite Int32.repr_unsigned. *)
    (*       apply Float32.of_to_bits. *)
    (*     + *)
    (*       clear -H. *)

    (*       rewrite Z.add_0_r. *)
    (*       unfold Z.modulo. *)
    (*       repeat break_let. *)
    (*       repeat match goal with *)
    (*              | [H : Z.div_eucl _ _ = _ |- _] => apply Z_div_mod' in H; [destruct H | lia] *)
    (*              end. *)
    (*       subst. *)
    (*       rewrite Z.add_comm, Z.mul_comm, Z_div_plus in * by lia. *)
    (*       rewrite Zdiv_small with (x:=z0) in * by lia. *)
    (*       rewrite Z.add_0_l in *. *)
    (*       subst. *)
    (*       rewrite Z.add_comm, Z.mul_comm, Z_div_plus in * by lia. *)
    (*       rewrite Zdiv_small with (x:=z2) in * by lia. *)
    (*       rewrite Z.add_0_l in *. *)
    (*       subst. *)
    (*       rewrite Z.add_comm, Z.mul_comm, Z_div_plus in * by lia. *)
    (*       rewrite Zdiv_small with (x:=z4) in * by lia. *)
    (*       rewrite Z.add_0_l in *. *)
    (*       subst. *)
    (*       lia. *)
    (*   - (* Structs *) *)
    (*     rewrite sizeof_struct_cons. *)

    (*     inversion SUP. *)
    (*     subst. *)
    (*     rename H0 into FIELD_SUP. *)
    (*     apply List.Forall_cons_iff in FIELD_SUP. *)
    (*     destruct FIELD_SUP as [dt_SUP dts_SUP]. *)
    (*     assert (is_supported (DTYPE_Struct dts)) as SUP_STRUCT by (constructor; auto). *)

    (*     cbn. *)
    (*     rewrite lookup_all_index_append; [|apply sizeof_serialized; auto]. *)

    (*     erewrite deserialize_struct_element; auto. *)
    (*     +  erewrite <- sizeof_serialized; eauto. *)
    (*       rewrite lookup_all_index_add_all_index_same_length; eauto. *)

    (*       apply dvalue_serialized_not_sundef. *)
    (*     + pose proof deserialize_sbytes_dvalue_all_not_sundef (DVALUE_Struct fields) (DTYPE_Struct dts) (lookup_all_index (off + Z.of_N (sizeof_dtyp dt)) (sizeof_dtyp (DTYPE_Struct dts)) *)
    (*                                                                                                                       (add_all_index (serialize_dvalue (DVALUE_Struct fields)) (off + Z.of_N (sizeof_dtyp dt)) bytes) SUndef). *)
    (*       cbn in H. *)
    (*       forward H; auto. *)
    (*     + rewrite lookup_all_index_length. *)
    (*       reflexivity. *)
    (*   - (* Packed structs *) *)
    (*     rewrite sizeof_packed_struct_cons. *)

    (*     inversion SUP. *)
    (*     subst. *)
    (*     rename H0 into FIELD_SUP. *)
    (*     apply List.Forall_cons_iff in FIELD_SUP. *)
    (*     destruct FIELD_SUP as [dt_SUP dts_SUP]. *)
    (*     assert (is_supported (DTYPE_Packed_struct dts)) as SUP_STRUCT by (constructor; auto). *)

    (*     cbn. *)
    (*     rewrite lookup_all_index_append; [|apply sizeof_serialized; auto]. *)

    (*     erewrite deserialize_packed_struct_element; auto. *)
    (*     + erewrite <- sizeof_serialized; eauto. *)
    (*       rewrite lookup_all_index_add_all_index_same_length; eauto. *)

    (*       apply dvalue_serialized_not_sundef. *)
    (*     + pose proof deserialize_sbytes_dvalue_all_not_sundef (DVALUE_Packed_struct fields) (DTYPE_Packed_struct dts) (lookup_all_index (off + Z.of_N (sizeof_dtyp dt)) (sizeof_dtyp (DTYPE_Packed_struct dts)) *)
    (*                                                                                                                       (add_all_index (serialize_dvalue (DVALUE_Packed_struct fields)) (off + Z.of_N (sizeof_dtyp dt)) bytes) SUndef). *)
    (*       cbn in H. *)
    (*       forward H; auto. *)
    (*     + rewrite lookup_all_index_length. *)
    (*       reflexivity. *)
    (*   - (* Arrays *) *)
    (*     rename H into SZ. *)
    (*     generalize dependent sz. *)
    (*     generalize dependent xs. *)
    (*     induction xs; *)
    (*       intros IH IHdtyp sz SZ SUP. *)
    (*     + cbn in *. *)
    (*       subst. *)
    (*       reflexivity. *)
    (*     + cbn in SZ. *)
    (*       subst. *)
    (*       rewrite Nnat.Nat2N.inj_succ. *)
    (*       cbn. *)

    (*       assert (dvalue_has_dtyp a dt) as DTa. *)
    (*       { *)
    (*         apply IHdtyp. *)
    (*         cbn. auto. *)
    (*       } *)

    (*       rewrite Nmult_Sn_m. *)
    (*       rewrite lookup_all_index_append; [|apply sizeof_serialized; auto]. *)

    (*       erewrite deserialize_array_element; auto. *)
    (*       * inversion SUP; constructor; auto. *)
    (*       * erewrite <- sizeof_serialized; eauto. *)
    (*         rewrite lookup_all_index_add_all_index_same_length; eauto. *)

    (*         apply dvalue_serialized_not_sundef. *)
    (*       * (* Should be serialization of DVALUE_array xs *) *)
    (*         replace (N.of_nat (Datatypes.length xs) * sizeof_dtyp dt)%N *)
    (*           with (N.of_nat (N.to_nat (N.of_nat (Datatypes.length xs) * sizeof_dtyp dt))) by lia. *)
    (*         rewrite lookup_all_index_add_all_index_same_length. *)

    (*         apply all_not_sundef_fold_right_serialize. *)

    (*         apply serialize_fold_length; intuition. *)
    (*       * replace (sizeof_dtyp dt) with (N.of_nat (N.to_nat (sizeof_dtyp dt))) by lia. *)
    (*         rewrite lookup_all_index_add_all_index_same_length. *)
    (*         erewrite <- sizeof_serialized; intuition. *)
    (*         lia. *)
    (*         erewrite <- sizeof_serialized; intuition. *)
    (*         lia. *)
    (*       * rewrite IH; intuition. *)
    (*         inversion SUP; auto. *)
    (*       * cbn. *)

    (*         unfold deserialize_sbytes. *)
    (*         break_match. *)

    (*         2: { *)
    (*           assert (all_not_sundef *)
    (*                     (lookup_all_index (off + Z.of_N (sizeof_dtyp dt)) *)
    (*                                       (N.of_nat (Datatypes.length xs) * sizeof_dtyp dt) *)
    (*                                       (add_all_index *)
    (*                                          (fold_right (fun (dv : dvalue) (acc : list SByte) => serialize_dvalue dv ++ acc) [] *)
    (*                                                      xs) (off + Z.of_N (sizeof_dtyp dt)) bytes) SUndef) = true) as CONTRA. *)
    (*           replace (N.of_nat (Datatypes.length xs) * sizeof_dtyp dt)%N *)
    (*             with (N.of_nat (N.to_nat (N.of_nat (Datatypes.length xs) * sizeof_dtyp dt))) by lia. *)
    (*           rewrite lookup_all_index_add_all_index_same_length. *)

    (*           apply all_not_sundef_fold_right_serialize. *)

    (*           apply serialize_fold_length; intuition. *)

    (*           rewrite Heqb in CONTRA. *)
    (*           inversion CONTRA. *)
    (*         } *)

    (*         forward IHxs; intuition. *)
    (*         forward IHxs; intuition. *)
    (*         specialize (IHxs (Datatypes.length xs) eq_refl). *)
    (*         forward IHxs. *)
    (*         { inversion SUP; constructor; eauto. } *)

    (*         cbn in IHxs. *)
    (*         rewrite <- IHxs. *)

    (*         rewrite all_not_sundef_deserialized; auto. *)
    (*         erewrite <- sizeof_serialized. *)

    (*         f_equal. *)

    (*         repeat rewrite <- Nnat.Nat2N.inj_mul. *)
    (*         rewrite lookup_all_index_add_all_index_same_length. *)
    (*         rewrite lookup_all_index_add_all_index_same_length. *)
    (*         reflexivity. *)

    (*         { erewrite <- serialize_fold_length. *)
    (*           erewrite <- sizeof_serialized. *)

    (*           repeat rewrite <- Nnat.Nat2N.inj_mul. *)
    (*           rewrite Nnat.Nat2N.id. *)
    (*           reflexivity. *)

    (*           eauto. *)
    (*           intuition. *)
    (*         } *)

    (*         { erewrite <- serialize_fold_length. *)
    (*           erewrite <- sizeof_serialized. *)

    (*           repeat rewrite <- Nnat.Nat2N.inj_mul. *)
    (*           rewrite Nnat.Nat2N.id. *)
    (*           reflexivity. *)

    (*           eauto. *)
    (*           intuition. *)
    (*         } *)

    (*         eauto. *)
    (*   - (* Vectors *) *)
    (*     rename H into SZ. *)
    (*     generalize dependent sz. *)
    (*     generalize dependent xs. *)
    (*     induction xs; *)
    (*       intros IH IHdtyp sz SZ SUP. *)
    (*     + cbn in *. *)
    (*       subst. *)
    (*       reflexivity. *)
    (*     + cbn in SZ. *)
    (*       subst. *)
    (*       rewrite Nnat.Nat2N.inj_succ. *)
    (*       cbn. *)

    (*       assert (dvalue_has_dtyp a dt) as DTa. *)
    (*       { *)
    (*         apply IHdtyp. *)
    (*         cbn. auto. *)
    (*       } *)

    (*       rewrite Nmult_Sn_m. *)
    (*       rewrite lookup_all_index_append; [|apply sizeof_serialized; auto]. *)

    (*       erewrite deserialize_vector_element; auto. *)
    (*       * inversion SUP; constructor; auto. *)
    (*       * erewrite <- sizeof_serialized; eauto. *)
    (*         rewrite lookup_all_index_add_all_index_same_length; eauto. *)

    (*         apply dvalue_serialized_not_sundef. *)
    (*       * (* Should be serialization of DVALUE_vector xs *) *)
    (*         replace (N.of_nat (Datatypes.length xs) * sizeof_dtyp dt)%N *)
    (*           with (N.of_nat (N.to_nat (N.of_nat (Datatypes.length xs) * sizeof_dtyp dt))) by lia. *)
    (*         rewrite lookup_all_index_add_all_index_same_length. *)

    (*         apply all_not_sundef_fold_right_serialize. *)

    (*         apply serialize_fold_length; intuition. *)
    (*       * replace (sizeof_dtyp dt) with (N.of_nat (N.to_nat (sizeof_dtyp dt))) by lia. *)
    (*         rewrite lookup_all_index_add_all_index_same_length. *)
    (*         erewrite <- sizeof_serialized; intuition. *)
    (*         lia. *)
    (*         erewrite <- sizeof_serialized; intuition. *)
    (*         lia. *)
    (*       * rewrite IH; intuition. *)
    (*         inversion SUP; subst; auto. *)
    (*       * cbn. *)

    (*         unfold deserialize_sbytes. *)
    (*         break_match. *)

    (*         2: { *)
    (*           assert (all_not_sundef *)
    (*                     (lookup_all_index (off + Z.of_N (sizeof_dtyp dt)) *)
    (*                                       (N.of_nat (Datatypes.length xs) * sizeof_dtyp dt) *)
    (*                                       (add_all_index *)
    (*                                          (fold_right (fun (dv : dvalue) (acc : list SByte) => serialize_dvalue dv ++ acc) [] *)
    (*                                                      xs) (off + Z.of_N (sizeof_dtyp dt)) bytes) SUndef) = true) as CONTRA. *)
    (*           replace (N.of_nat (Datatypes.length xs) * sizeof_dtyp dt)%N *)
    (*             with (N.of_nat (N.to_nat (N.of_nat (Datatypes.length xs) * sizeof_dtyp dt))) by lia. *)
    (*           rewrite lookup_all_index_add_all_index_same_length. *)

    (*           apply all_not_sundef_fold_right_serialize. *)

    (*           apply serialize_fold_length; intuition. *)

    (*           rewrite Heqb in CONTRA. *)
    (*           inversion CONTRA. *)
    (*         } *)

    (*         forward IHxs; intuition. *)
    (*         forward IHxs; intuition. *)
    (*         specialize (IHxs (Datatypes.length xs) eq_refl). *)
    (*         forward IHxs. *)
    (*         { inversion SUP; constructor; eauto. } *)

    (*         cbn in IHxs. *)
    (*         rewrite <- IHxs. *)

    (*         rewrite all_not_sundef_deserialized; auto. *)
    (*         erewrite <- sizeof_serialized. *)

    (*         f_equal. *)

    (*         repeat rewrite <- Nnat.Nat2N.inj_mul. *)
    (*         rewrite lookup_all_index_add_all_index_same_length. *)
    (*         rewrite lookup_all_index_add_all_index_same_length. *)
    (*         reflexivity. *)

    (*         { erewrite <- serialize_fold_length. *)
    (*           erewrite <- sizeof_serialized. *)

    (*           repeat rewrite <- Nnat.Nat2N.inj_mul. *)
    (*           rewrite Nnat.Nat2N.id. *)
    (*           reflexivity. *)

    (*           eauto. *)
    (*           intuition. *)
    (*         } *)

    (*         { erewrite <- serialize_fold_length. *)
    (*           erewrite <- sizeof_serialized. *)

    (*           repeat rewrite <- Nnat.Nat2N.inj_mul. *)
    (*           rewrite Nnat.Nat2N.id. *)
    (*           reflexivity. *)

    (*           eauto. *)
    (*           intuition. *)
    (*         } *)

    (*         eauto. *)
    (* Qed. *)

End SerializationTheory.
