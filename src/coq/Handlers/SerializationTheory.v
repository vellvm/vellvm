From Coq Require Import ZArith Lia List String.

From ExtLib Require Import
     Core.RelDec
     Structures.Monads.

From TwoPhase Require Import
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
      all_bytes_from_uvalue_helper start sid uv sbytes = Some uv ->
      all_bytes_from_uvalue_helper (start + N.of_nat (List.length sbytes)) sid uv sbytes2 = Some uv ->
      all_bytes_from_uvalue_helper start sid uv (sbytes ++ sbytes2) = Some uv.
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
      replace (start + N.pos (Pos.of_succ_nat (Datatypes.length sbytes))) with (N.succ start + N.of_nat (Datatypes.length sbytes)) in REST by lia.
      apply IHsbytes; auto.
  Qed.

  Lemma to_ubytes_all_bytes_from_uvalue_helper' :
    forall len uv dt sid sbytes start,
      is_supported dt ->
      map (fun n : N => uvalue_sbyte uv dt n sid) (Nseq start len) = sbytes ->
      all_bytes_from_uvalue_helper start sid uv sbytes = Some uv.
  Proof.
    induction len;
      intros uv dt sid sbytes start SUP TO.
    - inv TO; reflexivity.
    - rewrite Nseq_S in TO.
      rewrite map_app in TO.
      subst.
      eapply all_bytes_helper_app.
      eapply IHlen; eauto.
      cbn.
      rewrite sbyte_to_extractbyte_of_uvalue_sbyte.
      rewrite map_length.
      rewrite Nseq_length.
      unfold OptionUtil.guard_opt.
      rewrite N.eqb_refl.
      rewrite eq_dec_eq.
      rewrite N.eqb_refl.
      reflexivity.
  Qed.

  Lemma to_ubytes_all_bytes_from_uvalue_helper :
    forall uv dt sid sbytes,
      is_supported dt ->
      to_ubytes uv dt sid = sbytes ->
      all_bytes_from_uvalue_helper 0 sid uv sbytes = Some uv.
  Proof.
    intros uv dt sid sbytes SUP TO.
    eapply to_ubytes_all_bytes_from_uvalue_helper'; eauto.
  Qed.

  Lemma to_ubytes_sizeof_dtyp :
    forall uv dt sid sbytes,
      to_ubytes uv dt sid = sbytes ->
      N.of_nat (List.length sbytes) = sizeof_dtyp dt.
  Proof.
    intros uv dt sid sbytes TOUBYTES.
    unfold to_ubytes in *.
    subst.
    rewrite map_length.
    rewrite Nseq_length.
    rewrite Nnat.N2Nat.id.
    reflexivity.
  Qed.

  Lemma to_ubytes_first_byte :
    forall uv dt sid s l,
      to_ubytes uv dt sid = (s :: l) ->
      s = uvalue_sbyte uv dt 0 sid.
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

    inversion TO; subst.
    auto.
  Qed.

  Lemma from_ubytes_to_ubytes :
    forall uv dt sid sbytes,
      is_supported dt ->
      sizeof_dtyp dt > 0 ->
      uvalue_has_dtyp uv dt ->
      to_ubytes uv dt sid = sbytes ->
      from_ubytes sbytes dt = uv.
  Proof.
    intros uv dt sid sbytes SUP SIZE TYPE TOUBYTES.

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
      break_inner_match; auto.
      unfold OptionUtil.guard_opt in Heqo.
      break_match_hyp_inv.
      unfold Coqlib.proj_sumbool in Heqb.
      break_match_hyp_inv.
      contradiction.
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
      (forall {A B} (a : A) (k : A -> M B), @bind M HM _ _ (@ret M HM _ a) k = k a) ->
      @eval_icmp err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
                 (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) op a b =
        success_unERR_UB_OOM res ->
      @eval_icmp M HM HME op a b = @ret M HM dvalue res.
  Proof.
    intros M HM HME op a b res BIND_RET_L EVAL.
    destruct op; cbn in *;
    destruct a, b; cbn in *; inv EVAL;
      first [ unfold eval_int_icmp; cbn;
              try rewrite BIND_RET_L;
              reflexivity
            | unfold eval_icmp, eval_int_icmp in *;
              break_match;
              [ cbn in *; inv H0
              | cbn in *;
                rewrite BIND_RET_L; inv H0; auto
              ]
        ].
  Qed.

  From TwoPhase.Utils Require Import Monads MonadExcLaws MonadEq1Laws.
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
    (*   + solve_bind_res. *)
    (*   + solve_bind_res. *)
    (*   + repeat break_match_goal; *)
    (*       solve [ destruct (TwoPhaseIntegers.mmul x x0); cbn in *; inversion EVAL; *)
    (*               apply to_dvalue_OOM_NoOom *)
    (*             | unfold lift_OOM; break_match_goal; cbn in *; inversion EVAL; *)
    (*               rewrite bind_ret_l; repeat break_match_goal; inversion EVAL; *)
    (*               subst; solve [auto] *)
    (*         ]. *)
    (* - destruct a, b; cbn in *; inversion EVAL; auto. *)

    (*   + rewrite bind_ret_l. *)
    (*     cbn. *)
    (*     break_match_goal. *)
    (*     cbn in *. *)
    (*     inversion H0. *)
    (*     reflexivity. *)
  Abort.

  Lemma concretize_icmp_inv:
    forall {M} `{HM: Monad M} `{HME: RAISE_ERROR M} op x y dv,
      (forall {A B} (a : A) (k : A -> M B), @bind M HM _ _ (@ret M HM _ a) k = k a) ->
      concretize_succeeds (UVALUE_ICmp op x y) ->
      concretize (UVALUE_ICmp op x y) dv ->
      exists dx dy,
        concretize_succeeds x /\
        concretize x dx /\
        concretize_succeeds y /\
        concretize y dy /\
        @eval_icmp M HM HME op dx dy = ret dv.
  Proof.
    intros M HM HME op x y dv BIND_RET_L SUCC CONC.

    rewrite concretize_equation in CONC.
    red in CONC.
    rewrite concretize_uvalueM_equation in CONC.

    cbn in CONC.
    destruct CONC as (ma & k' & pama & eqm & REST).

    cbn in eqm.

    destruct ma as [[[[[[[oom_ma] | [[ub_ma] | [[err_ma] | a]]]]]]]] eqn:Hma;
      cbn in eqm; inv eqm.

    destruct REST as [[] | REST].
    specialize (REST a).
    forward REST; [reflexivity|].

    destruct REST as (mb & kb & pbmb & eqmb & REST).

    unfold concretize_succeeds, concretize_fails, concretize_u in SUCC.
    rewrite concretize_uvalueM_equation in SUCC.
    cbn in SUCC.
    unfold bind_RefineProp in SUCC.

    exists a.

    destruct mb as [[[[[[[oom_mb] | [[ub_mb] | [[err_mb] | b]]]]]]]] eqn:Hmb;
      cbn in eqmb; subst; cbn in *; eauto;
      rewrite <- eqmb in H0;
      cbn in H0;
      inv H0.

    (* Both x and y successfully concretized. *)

    (*        Now eval_iop must succeed too. *)
    (*    *)
    destruct REST as [[] | REST].
    specialize (REST b).
    forward REST; [reflexivity|].

    rewrite <- REST in H1.
    destruct (eval_icmp op a b) as [[[[[[[oom_z] | [[ub_z] | [[err_z] | z]]]]]]]] eqn:Hmz;
      cbn in H1; inv H1.

    exists b.
    repeat split; eauto.

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

    apply eval_icmp_err_ub_oom_to_M; eauto.
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

    cbn in eqm.

    destruct ma as [[[[[[[oom_ma] | [[ub_ma] | [[err_ma] | a]]]]]]]] eqn:Hma;
      cbn in eqm; inv eqm.

    destruct REST as [[] | REST].
    specialize (REST a).
    forward REST; [reflexivity|].

    destruct REST as (mb & kb & pbmb & eqmb & REST).

    unfold concretize_succeeds, concretize_fails, concretize_u in SUCC.
    rewrite concretize_uvalueM_equation in SUCC.
    cbn in SUCC.
    unfold bind_RefineProp in SUCC.

    exists a.

    destruct mb as [[[[[[[oom_mb] | [[ub_mb] | [[err_mb] | b]]]]]]]] eqn:Hmb;
      cbn in eqmb; subst; cbn in *; eauto;
      rewrite <- eqmb in H0;
      cbn in H0;
      inv H0.

    (* Both x and y successfully concretized. *)

    (*        Now eval_iop must succeed too. *)
    (*    *)
    destruct REST as [[] | REST].
    specialize (REST b).
    forward REST; [reflexivity|].

    rewrite <- REST in H1.
    destruct (eval_iop op a b) as [[[[[[[oom_z] | [[ub_z] | [[err_z] | z]]]]]]]] eqn:Hmz;
      cbn in H1; inv H1.

    exists b.
    repeat split; eauto.

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

    rewrite Hmz, <- REST.
    cbn.
    reflexivity.
  Qed.

  Lemma concretize_succeeds_poison :
    forall dt,
      concretize_succeeds (UVALUE_Poison dt).
  Proof.
    induction dt;
      unfold concretize_succeeds, concretize_fails, concretize_u;
      rewrite concretize_uvalueM_equation;
      cbn; auto.

    all: intros CONTRA; discriminate.
  Qed.

End SerializationTheory.
