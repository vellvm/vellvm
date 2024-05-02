From Vellvm.Syntax Require Import
     DataLayout
     DynamicTypes.

From Mem Require Import
  Addresses.MemoryAddress
  Addresses.Provenance.

From ITree Require Import
     ITree
     Basics.Basics
     Events.Exception
     Eq.Eqit
     Events.StateFacts
     Events.State.

From Vellvm.Utils Require Import
     Error
     PropT
     Util
     NMaps
     Tactics
     Monads
     MapMonadExtra
     MonadReturnsLaws
     MonadEq1Laws
     MonadExcLaws
     Inhabited.

From Vellvm.Numeric Require Import
     Integers.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor.

From Coq Require Import
     ZArith
     Strings.String
     List
     Lia
     Relations
     RelationClasses
     Wellfounded
     Structures.Equalities.

Require Import Morphisms.

Import ListNotations.
Import ListUtil.
Import Utils.Monads.

Import Basics.Basics.Monads.
Import MonadNotation.

Import Monad.
Import EitherMonad.

From Coq Require Import FunctionalExtensionality.

Module MemoryHelpers (LP : LLVMParams) (MP : MemoryParams LP) (Byte : ByteModule LP.ADDR LP.IP LP.SIZEOF LP.Events MP.BYTE_IMPL).
  (*** Other helpers *)
  Import MP.GEP.
  Import MP.BYTE_IMPL.
  Import LP.
  Import LP.ADDR.
  Import LP.Events.
  Import LP.SIZEOF.
  Import LP.PTOI.
  Import LP.ITOP.
  Import LP.PROV.
  Import IP.
  Import Byte.
  Import Util.

  (* TODO: Move this? *)
  Definition intptr_seq (start : Z) (len : nat) : OOM (list IP.intptr)
    := map_monad (IP.from_Z) (Zseq start len).

  (* TODO: Move this? *)
  Lemma intptr_seq_succ :
    forall off n,
      intptr_seq off (S n) =
        hd <- IP.from_Z off;;
        tail <- intptr_seq (Z.succ off) n;;
        ret (hd :: tail).
  Proof.
    intros off n.
    cbn.
    reflexivity.
  Qed.

  Lemma intptr_seq_nth :
    forall start len seq ix ixip,
      intptr_seq start len = NoOom seq ->
      Util.Nth seq ix ixip ->
      IP.from_Z (start + (Z.of_nat ix)) = NoOom ixip.
  Proof.
    intros start len seq. revert start len.
    induction seq; intros start len ix ixip SEQ NTH.
    - cbn in NTH.
      destruct ix; inv NTH.
    - cbn in *.
      destruct ix.
      + cbn in *; inv NTH.
        destruct len; cbn in SEQ; inv SEQ.
        break_match_hyp; inv H0.
        replace (start + 0)%Z with start by lia.
        break_match_hyp; cbn in *; inv H1; auto.
      + cbn in *; inv NTH.
        destruct len as [ | len']; cbn in SEQ; inv SEQ.
        break_match_hyp; inv H1.
        break_match_hyp; cbn in *; inv H2; auto.

        replace (start + Z.pos (Pos.of_succ_nat ix))%Z with
          (Z.succ start + Z.of_nat ix)%Z by lia.

        eapply IHseq with (start := Z.succ start) (len := len'); eauto.
  Qed.

  Lemma intptr_seq_ge :
    forall start len seq x,
      intptr_seq start len = NoOom seq ->
      In x seq ->
      (IP.to_Z x >= start)%Z.
  Proof.
    intros start len seq x SEQ IN.
    apply In_nth_error in IN.
    destruct IN as [n IN].

    pose proof (intptr_seq_nth start len seq n x SEQ IN) as IX.
    erewrite IP.from_Z_to_Z; eauto.
    lia.
  Qed.

  Lemma in_intptr_seq :
    forall len start n seq,
      intptr_seq start len = NoOom seq ->
      In n seq <-> (start <= IP.to_Z n < start + Z.of_nat len)%Z.
  Proof.
  intros len start.
  revert start. induction len as [|len IHlen]; simpl; intros start n seq SEQ.
  - cbn in SEQ; inv SEQ.
    split.
    + intros IN; inv IN.
    + lia.
  - cbn in SEQ.
    break_match_hyp; [|inv SEQ].
    break_match_hyp; inv SEQ.
    split.
    + intros [IN | IN].
      * subst.
        apply IP.from_Z_to_Z in Heqo; subst.
        lia.
      * pose proof (IHlen (Z.succ start) n l Heqo0) as [A B].
        specialize (A IN).
        cbn.
        lia.
    + intros BOUND.
      cbn.
      destruct (IP.eq_dec i n) as [EQ | NEQ]; auto.
      right.

      pose proof (IHlen (Z.succ start) n l Heqo0) as [A B].
      apply IP.from_Z_to_Z in Heqo; subst.
      assert (IP.to_Z i <> IP.to_Z n).
      { intros EQ.
        apply IP.to_Z_inj in EQ; auto.
      }

      assert ((Z.succ (IP.to_Z i) <= IP.to_Z n < Z.succ (IP.to_Z i) + Z.of_nat len)%Z) as BOUND' by lia.
      specialize (B BOUND').
      auto.
  Qed.

  Lemma intptr_seq_from_Z :
    forall start len seq,
      intptr_seq start len = NoOom seq ->
      (forall x,
          (start <= x < start + Z.of_nat len)%Z ->
          exists ipx, IP.from_Z x = NoOom ipx /\ In ipx seq).
  Proof.
    intros start len; revert start;
      induction len;
      intros start seq SEQ x BOUND.

    - lia.
    - rewrite intptr_seq_succ in SEQ.
      cbn in SEQ.
      break_match_hyp.
      + destruct (Z.eq_dec x start); subst.
        * exists i.
          split; auto.
          break_match_hyp; inv SEQ; cbn; auto.
        * break_match_hyp; inv SEQ.
          eapply IHlen with (x := x) in Heqo0 as (ipx & FROMZ & IN).
          exists ipx; split; cbn; auto.
          lia.
      + inv SEQ.
  Qed.

  Lemma intptr_seq_len :
    forall len start seq,
      intptr_seq start len = NoOom seq ->
      length seq = len.
  Proof.
    induction len;
      intros start seq SEQ.
    - inv SEQ. reflexivity.
    - rewrite intptr_seq_succ in SEQ.
      cbn in SEQ.
      break_match_hyp; [break_match_hyp|]; inv SEQ.
      cbn.
      apply IHlen in Heqo0; subst.
      reflexivity.
  Qed.

  Lemma intptr_seq_nil_len :
    forall start len,
      intptr_seq start len = NoOom [] ->
      len = 0%nat.
  Proof.
    intros start len SEQ.
    unfold intptr_seq in SEQ.
    assert (MReturns [] (map_monad IP.from_Z (Zseq start len))) as RET.
    { cbn. unfold OOMReturns.
      rewrite SEQ.
      reflexivity.
    }
    pose proof (@map_monad_ret_nil_inv OOM _ _ _ _ _ _ _ IP.from_Z _ RET) as SEQLEN.
    eapply Zseq_nil_len; eauto.
  Qed.

  Lemma intptr_seq_succ_last :
    forall l off len x,
      intptr_seq off (S len) = NoOom (l ++ [x]) ->
      intptr_seq off len = NoOom l.
  Proof.
    induction l;
      intros off len x SEQ.
    - cbn in *.
      break_match_hyp; [| solve [inv SEQ]].
      break_match_hyp; [| solve [inv SEQ]].
      inv SEQ.

      assert (MReturns [] (map_monad IP.from_Z (Zseq (Z.succ off) len))) as RET.
      { cbn. unfold OOMReturns.
        rewrite Heqo0.
        reflexivity.
      }

      pose proof (@map_monad_ret_nil_inv OOM _ _ _ _ _ _ _ IP.from_Z _ RET) as SEQLEN.
      apply Zseq_nil_len in SEQLEN.
      subst.
      cbn.
      reflexivity.
    - rewrite intptr_seq_succ in SEQ.
      cbn in SEQ.
      break_match_hyp; [| solve [inv SEQ]].
      break_match_hyp; [| solve [inv SEQ]].
      inv SEQ.

      pose proof (intptr_seq_len _ _ _ Heqo0) as LEN.
      rewrite last_length in LEN.
      subst len.
      pose proof (IHl (Z.succ off) _ _ Heqo0) as GENL.

      rewrite intptr_seq_succ.
      rewrite Heqo.
      rewrite GENL.
      cbn.
      reflexivity.
  Qed.

  Lemma intptr_seq_succ_last' :
    forall l off len x,
      intptr_seq off len = NoOom l ->
      IP.from_Z (off + Z.of_nat len) = NoOom x ->
      intptr_seq off (S len) = NoOom (l ++ [x]).
  Proof.
    induction l as [ | i l']; intros off len x SEQ EQ.
    - rewrite intptr_seq_succ.
      apply intptr_seq_nil_len in SEQ.
      subst.
      cbn in *.
      replace (off + 0)%Z with off in EQ by lia.
      rewrite EQ.
      reflexivity.
    - pose proof SEQ as LEN.
      apply intptr_seq_len in LEN.
      cbn in LEN; inv LEN.

      rewrite intptr_seq_succ in SEQ.
      cbn in SEQ.
      break_match_hyp; [| solve [inv SEQ]].
      break_match_hyp; [| solve [inv SEQ]].
      inv SEQ.
      rename Heqo0 into SEQ.

      pose proof (IHl' (Z.succ off) (length l') x SEQ) as SEQ'.
      forward SEQ'.
      { cbn in EQ.
        rewrite Zpos_P_of_succ_nat in EQ.
        rewrite Z.add_succ_comm.
        auto.
      }

      rewrite <- app_comm_cons.
      rewrite intptr_seq_succ.
      rewrite Heqo.
      rewrite SEQ'.
      cbn.
      reflexivity.
  Qed.

  Lemma intptr_seq_shifted :
    forall len l,
      intptr_seq 1 len = NoOom l ->
      exists l', intptr_seq 0 len = NoOom l' /\
              NoOom l = map_monad (fun ip => IP.from_Z (IP.to_Z ip + 1)) l'.
  Proof.
    intros len l SEQ.
    revert SEQ. revert len.
    induction l using rev_ind; intros len SEQ.
    - exists nil; split; auto.
      apply intptr_seq_nil_len in SEQ.
      subst; cbn; auto.
    - (* Follows from SEQ *)
      assert (exists len', len = S len') as [len' LENEQ].
      { destruct len; cbn in SEQ.
        - cbn in SEQ; inv SEQ.
          assert (length (l ++ [x]) = 0%nat) as LEN.
          rewrite <- H0; reflexivity.
          rewrite last_length in LEN.
          inv LEN.
        - exists len. reflexivity.
      }

      (* Also follows from SEQ and LENEQ *)
      assert (intptr_seq 1 len' = NoOom l) as SEQ_CUT.
      { eapply intptr_seq_succ_last; subst len; eauto.
      }

      subst len.

      pose proof (IHl len' SEQ_CUT) as [l_shifted [SEQ_SHIFTED MAP_SHIFTED]].

      pose proof MAP_SHIFTED as ALL_SHIFTED.
      symmetry in ALL_SHIFTED.
      eapply map_monad_oom_Forall2 in ALL_SHIFTED.

      pose proof ALL_SHIFTED as NTH_SHIFTED.
      eapply Forall2_forall in NTH_SHIFTED as [LEN_SHIFTED NTH_SHIFTED].

      assert (exists y, IP.from_Z (IP.to_Z x - 1) = NoOom y) as [y YEQ].
      { (* I know this because...??? *)
        (* shiftZ is the start, x is the final element in the sequence.

                 This actually computes (S len'), the length of the initial sequence...
                 But it's not clear if this length can actually be represented as an iptr.

                 We know 0 can be, and we know the range between
                 shiftZ and x can be, but we don't know anything else,
                 technically.

                 If shiftZ is just 1 this is knowable.
         *)

        pose proof (Nth_last l x) as NTH.
        pose proof (intptr_seq_nth _ _ _ _ _ SEQ NTH) as SEQNTH.
        apply IP.from_Z_to_Z in SEQNTH.
        rewrite SEQNTH.

        (* When len' is 0, y is just 0 *)
        destruct l using rev_ind.
        - exists IP.zero.
          cbn in SEQ_CUT.
          inv SEQ_CUT.
          cbn.
          apply IP.from_Z_0.
        - clear IHl0.
          exists x0.

          pose proof (Nth_last l x0) as NTH'.
          pose proof (intptr_seq_nth _ _ _ _ _ SEQ_CUT NTH') as SEQNTH'.
          apply IP.from_Z_to_Z in SEQNTH'.
          rewrite app_length.
          rewrite Nat2Z.inj_add.
          replace ((1 + (Z.of_nat (Datatypes.length l) + Z.of_nat (Datatypes.length [x0])) - 1))%Z with ((Z.of_nat (Datatypes.length l) + Z.of_nat (Datatypes.length [x0])))%Z by lia.
          cbn.
          replace (Z.of_nat (length l) + 1)%Z with (1 + Z.of_nat (length l))%Z by lia.
          rewrite <- SEQNTH'.
          apply IP.to_Z_from_Z.
      }

      exists (l_shifted ++ [y]).
      split.
      + apply intptr_seq_succ_last'; eauto.
        cbn.

        destruct len'.
        -- cbn in *.
           inv SEQ_CUT.
           break_match_hyp; inv SEQ.
           erewrite IP.from_Z_to_Z in YEQ; eauto.
           cbn in YEQ.
           auto.
        -- (* I know that x = S S len' *)
          pose proof intptr_seq_nth 1 (S (S len')) (l ++ [x]) (S len') x SEQ as LAST_SEQ.
          forward LAST_SEQ.
          { eapply intptr_seq_len in SEQ_CUT.
            rewrite <- SEQ_CUT.
            eapply Nth_last.
          }

          erewrite IP.from_Z_to_Z in YEQ; eauto.
          replace (1 + Z.of_nat (S len') - 1)%Z with (Z.of_nat (S len'))%Z in YEQ by lia.
          auto.
      + assert (Monad.eq1 (NoOom (l ++ [x])) (map_monad (fun ip : IP.intptr => IP.from_Z (IP.to_Z ip + 1)) (l_shifted ++ [y]))) as EQ.
        { rewrite map_monad_app.
          cbn.
          rewrite <- MAP_SHIFTED.
          (* Must be some way to prove that this match gives NoOom x... *)
          assert (IP.from_Z (IP.to_Z y + 1) = NoOom x) as EQ.
          { erewrite IP.from_Z_to_Z; eauto.
            assert (IP.to_Z x - 1 + 1 = IP.to_Z x)%Z as EQ by lia.
            rewrite EQ.
            apply IP.to_Z_from_Z.
          }

          rewrite EQ.
          reflexivity.
        }

        cbn in EQ.
        break_match_hyp; inv EQ.
        reflexivity.
  Qed.

  Definition get_consecutive_ptrs {M} `{Monad M} `{RAISE_OOM M} `{RAISE_ERROR M} (ptr : addr) (len : nat) : M (list addr) :=
    ixs <- lift_OOM (intptr_seq 0 len);;
    addrs <- lift_err_RAISE_ERROR
              (map_monad
                 (fun ix => handle_gep_addr (DTYPE_I 8) ptr [DVALUE_IPTR ix])
                 ixs (m:=err));;
    lift_OOM (sequence addrs).

  Ltac convert_to_ret :=
    match goal with
    | _:_ |- context [ success_unERR_UB_OOM ?x ] =>
        replace (success_unERR_UB_OOM x) with (@ret err_ub_oom _ _ x) by auto
    end.

  Ltac convert_to_ret_hyp :=
    repeat
      match goal with
      | H : context [ success_unERR_UB_OOM ?x ] |- _ =>
          replace (success_unERR_UB_OOM x) with (@ret err_ub_oom _ _ x) in H by auto
      end.

  Ltac convert_to_raise :=
    match goal with
    | _:_ |-
        context [
            ({| unERR_UB_OOM :=
               {|
                 EitherMonad.unEitherT :=
                 {|
                   EitherMonad.unEitherT :=
                   {|
                     EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (@inl _ (sum ERR_MESSAGE ?t) (UB_message ?ub_msg)) |}
                   |}
                 |}
               |}
             |}) ] =>
        replace (UB_unERR_UB_OOM ub_msg) with (@raise_ub err_ub_oom _ t ub_msg) by auto
    end.

  Ltac convert_to_raise_hyp :=
    repeat
      match goal with
      | H : context [
                ({| unERR_UB_OOM :=
                   {|
                     EitherMonad.unEitherT :=
                     {|
                       EitherMonad.unEitherT :=
                       {|
                         EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (@inl _ (sum ERR_MESSAGE ?t) (UB_message ?ub_msg)) |}
                       |}
                     |}
                   |}
                 |}) ] |- _ =>
          replace (UB_unERR_UB_OOM ub_msg) with (@raise_ub err_ub_oom _ t ub_msg) in H by eauto
      end.

   Lemma get_consecutive_ptrs_length :
    forall {M} `{HM : Monad M} `{EQM : Monad.Eq1 M}
      {Pre Post : Type}
      {B} `{MB : Monad B}
      `{WM : @Within M EQM B Pre Post}
      `{EQV : @Monad.Eq1Equivalence M HM EQM}
      `{WRET : @Within_ret_inv M B Pre Post HM _ EQM WM}
      `{MLAWS : @Monad.MonadLawsE M EQM HM}
      `{OOM: RAISE_OOM M} `{ERR: RAISE_ERROR M}
      `{RBMOOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
      `{RBMERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}
      `{RWOOM : @RaiseWithin M B Pre Post _ EQM WM string (@raise_oom M OOM)}
      `{RWERR : @RaiseWithin M B Pre Post _ EQM WM string (@raise_error M ERR)}
      (ptr : addr) (len : nat) (ptrs : list addr),
      (@ret B _ _ ptrs ∈ @get_consecutive_ptrs M HM OOM ERR ptr len)%monad ->
      len = length ptrs.
  Proof.
    intros M HM EQM Pre Post B MB WM EQV WRET MLAWS OOM ERR RBMOOM RBMERR RWOOM RWERR ptr len ptrs CONSEC.
    unfold get_consecutive_ptrs in CONSEC.
    Opaque handle_gep_addr.
    cbn in *.
    destruct (intptr_seq 0 len) eqn:SEQ.
    - (* No OOM *)
      cbn in *.
      setoid_rewrite Monad.bind_ret_l in CONSEC.

      (* rewrite bind_ret_l in CONSEC. *)
      destruct (map_monad (fun ix : IP.intptr => handle_gep_addr (DTYPE_I 8) ptr [DVALUE_IPTR ix]) l) eqn:HMAPM.
      + (* Error: should be a contradiction *)
        (* TODO: need inversion lemma. *)
        cbn in CONSEC.
        convert_to_ret_hyp.
        setoid_rewrite rbm_raise_bind in CONSEC; auto.
        eapply rw_ret_nin_raise in CONSEC; [contradiction | auto].
      + cbn in CONSEC.
        convert_to_ret_hyp.
        setoid_rewrite Monad.bind_ret_l in CONSEC.
        destruct (sequence l0) eqn:HSEQUENCE.
        { cbn in CONSEC.
          apply within_ret_ret in CONSEC; auto.
          assert (MReturns l0 (map_monad (fun ix : IP.intptr => handle_gep_addr (DTYPE_I 8) ptr [DVALUE_IPTR ix]) l)) as RETS.
          { auto. }

          epose proof MapMonadExtra.map_monad_length l _ _ RETS as LEN.
          apply intptr_seq_len in SEQ.
          subst.
          auto.

          apply sequence_OOM_length in HSEQUENCE.
          lia.
        }
        { cbn in *.
          eapply rw_ret_nin_raise in CONSEC; [contradiction | auto].
        }
    - (* OOM: CONSEC equivalent to ret is a contradiction. *)
      cbn in CONSEC.
      setoid_rewrite rbm_raise_bind in CONSEC; auto.
      convert_to_ret_hyp;
        eapply rw_ret_nin_raise in CONSEC; [contradiction | auto].
  Qed.

  Lemma get_consecutive_ptrs_covers_range :
    forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Monad.Eq1 M}
      {Pre Post : Type}
      {B} `{MB : Monad B}
      `{WM : @Within M EQM B Pre Post}
      `{EQV : @Monad.Eq1Equivalence M HM EQM}
      `{EQRET : @Eq1_ret_inv M EQM HM}
      `{WRET : @Within_ret_inv M B Pre Post HM _ EQM WM}
      `{LAWS : @Monad.MonadLawsE M EQM HM}
      `{RBMOOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
      `{RBMERR : @RaiseBindM M  HM EQM string (@raise_error M ERR)}
      `{RWOOM : @RaiseWithin M B _ _ _ EQM WM string (@raise_oom M OOM)}
      `{RWERR : @RaiseWithin M B _ _ _ EQM WM string (@raise_error M ERR)}
      ptr len ptrs,
      (ret ptrs ∈ @get_consecutive_ptrs M HM OOM ERR ptr len)%monad ->
      forall ix, (ptr_to_int ptr <= ix < ptr_to_int ptr + (Z.of_nat len))%Z ->
            exists p', ptr_to_int p' = ix /\ In p' ptrs.
  Proof.
    (* TODO: This is kind of related to get_consecutive_ptrs_nth *)
    intros M HM OOM ERR EQM' Pre Post B MB WM EQV EQRET WRET LAWS RBMOOM RBMERR RWOOM RWERR ptr len ptrs CONSEC ix RANGE.
    Transparent get_consecutive_ptrs.
    unfold get_consecutive_ptrs in CONSEC.
    Opaque get_consecutive_ptrs.

    (* Technically this can be more general with inversion lemma for raise_oom *)
    destruct (intptr_seq 0 len) eqn:HSEQ.
    - cbn in *.
      setoid_rewrite Monad.bind_ret_l in CONSEC.

      destruct (map_monad
                  (fun ix : IP.intptr =>
                     MP.GEP.handle_gep_addr (DTYPE_I 8) ptr [Events.DV.DVALUE_IPTR ix])
                  l) eqn:HMAPM.
      + cbn in CONSEC.
        setoid_rewrite rbm_raise_bind in CONSEC; auto.
        eapply rw_ret_nin_raise in CONSEC; [contradiction | try typeclasses eauto].
      + cbn in CONSEC.
        setoid_rewrite Monad.bind_ret_l in CONSEC.
        rename l0 into addrs.
        destruct (sequence addrs) eqn:HSEQUENCE.
        { apply within_ret_ret in CONSEC; eauto.
          inv CONSEC.

          pose proof (@exists_in_bounds_le_lt
                        (ptr_to_int ptr)
                        (ptr_to_int ptr + Z.of_nat len)
                        ix) as BOUNDS.

          forward BOUNDS. lia.
          destruct BOUNDS as [offset [[BOUNDLE BOUNDLT] EQ]].

          (* How does ix connect to HSEQ?

                       EQ: ix = ptr_to_int ptr + offset
                       BOUNDLE : 0 <= offset
                       BOUNDLT : offset < Z.of_nat len

                       Then with:

                       HSEQ: intptr_seq 0 len = NoOom l

                       I should know that:

                       exists ip_offset, In ip_offset l /\ from_Z ip_offset = offset

                       (or maybe to_Z ip_offset = NoOom offset)
           *)
          pose proof intptr_seq_from_Z 0 len l HSEQ offset as FROMZ.
          forward FROMZ; [lia|].
          destruct FROMZ as (ip_offset & FROMZ & INSEQ).

          eapply (@map_monad_err_In' err _ _ Monads.MonadLaws_sum) with (y:=ip_offset) in HMAPM; auto; try typeclasses eauto.

          destruct HMAPM as (p' & GEP & IN).
          symmetry in GEP.
          cbn in GEP.
          destruct p' as [p' | oom_msg].
          { apply MP.GEP.handle_gep_addr_ix in GEP.
            exists p'. split; auto.
            subst.

            rewrite sizeof_dtyp_i8 in GEP.
            erewrite IP.from_Z_to_Z in GEP; [|apply FROMZ].
            lia.

            unfold sequence in HSEQUENCE.
            eapply sequence_OOM_In; eauto.
          }
          { subst.
            eapply sequence_OOM_NoOom_In in HSEQUENCE.
            apply HSEQUENCE in IN.
            contradiction.
          }
        }
        { cbn in *.
          eapply rw_ret_nin_raise in CONSEC; [contradiction | typeclasses eauto].
        }
    - cbn in CONSEC.
      setoid_rewrite rbm_raise_bind in CONSEC; [|typeclasses eauto].
      eapply rw_ret_nin_raise in CONSEC; [contradiction | typeclasses eauto].
  Qed.

  Lemma get_consecutive_ptrs_covers_range_eq1 :
    forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
      {B} `{MB : Monad B}
      `{EQV : @Eq1Equivalence M HM EQM}
      `{EQRET : @Eq1_ret_inv M EQM HM}
      `{LAWS : @MonadLawsE M EQM HM}
      `{RBMOOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
      `{RBMERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}
      ptr len ptrs,
      (@get_consecutive_ptrs M HM OOM ERR ptr len ≈ ret ptrs)%monad ->
      forall ix, (ptr_to_int ptr <= ix < ptr_to_int ptr + (Z.of_nat len))%Z ->
            exists p', ptr_to_int p' = ix /\ In p' ptrs.
  Proof.
    intros M HM OOM ERR EQM B MB EQV EQRET LAWS RBMOOM RBMERR ptr len ptrs CONSEC ix IN.

    assert (@within M EQM M unit unit (Reflexive_Within) _
              (@get_consecutive_ptrs M HM OOM ERR ptr len)
              tt
              (@ret M HM (list addr) ptrs)
              tt
           ) as WITHIN.
    { cbn. red.
      auto.
    }

    eapply @get_consecutive_ptrs_covers_range with (B:=M);
      eauto; typeclasses eauto.
  Qed.

  Lemma get_consecutive_ptrs_cons :
    forall {M : Type -> Type}
      `{HM: Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM}
      {Pre Post : Type}
      {B} `{MB : Monad B}
      `{WM : @Within M EQM B Pre Post}
      `{EQRET : @Eq1_ret_inv M EQM HM}
      `{WRET : @Within_ret_inv M B Pre Post HM _ EQM WM}
      `{OOM: RAISE_OOM M} `{ERR: RAISE_ERROR M}
      `{LAWS: @MonadLawsE M EQM HM}
      `{RAISE_OOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
      `{RAISE_ERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}
      `{RWOOM : @RaiseWithin M B _ _ _ EQM WM string (@raise_oom M OOM)}
      `{RWERR : @RaiseWithin M B _ _ _ EQM WM string (@raise_error M ERR)}
      ptr len p ptrs,
      (ret (p :: ptrs) ∈ get_consecutive_ptrs ptr len)%monad ->
      p = ptr /\ ((ptrs = [] /\ len = 1%nat) \/ exists ptr' ip len', len = S len' /\ to_Z ip = 1%Z /\ handle_gep_addr (DTYPE_I 8) ptr [DVALUE_IPTR ip] = inr (NoOom ptr') /\ (ret ptrs ∈ get_consecutive_ptrs ptr' len')%monad).
  Proof.
    intros M HM EQM' Pre Post B MB WM EQRET WRET EQV OOM ERR LAWS RAISE_OOM RAISE_ERR RWOOM RWERR ptr len p ptrs CONSEC.

    Transparent get_consecutive_ptrs.
    unfold get_consecutive_ptrs in *.
    destruct (intptr_seq 0 len) eqn:SEQ.
    2: {
      cbn in CONSEC.
      setoid_rewrite rbm_raise_bind in CONSEC; eauto.
      convert_to_ret_hyp;
        eapply rw_ret_nin_raise in CONSEC; eauto; contradiction.
    }

    cbn in *.
    setoid_rewrite bind_ret_l in CONSEC.

    generalize dependent len.
    destruct len; intros SEQ.
    - cbn in SEQ.
      inv SEQ.
      cbn in CONSEC.
      setoid_rewrite bind_ret_l in CONSEC.
      eapply within_ret_ret in CONSEC; [|typeclasses eauto].
      inv CONSEC.
    - rewrite intptr_seq_succ in SEQ.
      cbn in *.
      break_match_hyp; [| solve [inv SEQ]].
      break_match_hyp; [| solve [inv SEQ]].
      rename l0 into l'.
      inv SEQ.

      cbn in *.
      rewrite IP.from_Z_0 in Heqo.
      inv Heqo.
      rewrite handle_gep_addr_0 in *.

      (* Break match of map_monad in CONSEC *)
      break_match_hyp.
      { (* map_monad fails *)
        cbn in CONSEC.
        setoid_rewrite rbm_raise_bind in CONSEC; eauto.
        apply rw_ret_nin_raise in CONSEC; eauto.
        contradiction.
      }

      (* map_monad succeeds *)
      cbn in CONSEC.
      convert_to_ret_hyp.
      setoid_rewrite bind_ret_l in CONSEC.
      destruct (sequence (NoOom ptr :: l)) eqn:SEQUENCE.
      { eapply within_ret_ret in CONSEC; eauto.
        inv CONSEC.
        inv SEQUENCE.
        break_match_hyp; inv H1.
        split; auto.

        destruct len.
        + cbn in Heqo0.
          inv Heqo0.
          cbn in Heqs.
          inv Heqs.
          inv Heqo.
          left.
          auto.
        + pose proof Heqo0 as SEQ.
          rewrite intptr_seq_succ in SEQ.
          cbn in SEQ.
          break_match_hyp; [| solve [inv SEQ]].
          rename i into one.

          break_match_hyp; [| solve [inv SEQ]].
          inv SEQ.

          pose proof Heqs as MAPM.
          rewrite map_monad_unfold in MAPM.
          cbn in MAPM.
          break_match_hyp; [ solve [inv MAPM] |].
          break_match_hyp; [ solve [inv MAPM] |].
          inv MAPM.
          destruct o as [p' | oom_msg]; [|inversion Heqo].
          rename l1 into ptrs'.
          right.
          exists p'. exists one. exists (S len).
          split; auto.
          split.
          apply from_Z_to_Z; auto.
          split; auto.

          (* Need something about sequences *)
      (* Since len is the length, `intptr_seq 1 len` is basically just `map (+1) (intptr_seq 0 len)` *)
      (* Unfortunately, I don't think I have a lemma that gives me
         `IP.from_Z (x+1) = NoOom (i+1) -> IP.from_Z (x+1) = NoOom i`

         Maybe something like this should be an axiom, but I think it
         gets messy because memory is bounded in the + and -
         direction.

         I *DO* know that `IP.from_Z 0 = NoOom zero`, however, and all of the other elements in
         `intptr_seq 0 len` are in `intptr_seq 1 len`.

         `intptr_seq 1 len =
             map (fun ip => handle_gep_addr (DTYPE_I 8) ip [Events.DV.DVALUE_IPTR 1])
                 (intptr_seq 0 len)`
       *)

        rename l0 into ixs.
        pose proof Heqo0 as SEQ_SHIFT.
        apply intptr_seq_shifted in Heqo0.
        destruct Heqo0 as [ixs_unshifted [SEQ SHIFT]].
        rewrite SEQ.
        cbn.

        setoid_rewrite bind_ret_l.
        match goal with
        | _ : _ |- context [map_monad ?f ?l] =>
            assert (map_monad f l = inr (NoOom p' :: ptrs')) as Heqs'
        end.
        {
          eapply map_monad_eqv; eauto.
          eapply Forall2_forall.
          split.
          { eapply intptr_seq_len in SEQ, SEQ_SHIFT.
            lia.
          }

          intros n a b NTH NTH'.
          pose proof (intptr_seq_nth _ _ _ _ _ SEQ_SHIFT NTH) as IX.
          pose proof (intptr_seq_nth _ _ _ _ _ SEQ NTH') as IX'.
          cbn in IX'.

          (* Exists n in ptrs *)
          pose proof sequence_OOM_length _ _ Heqo as PTRS_LENGTH.
          assert (length (NoOom p' :: ptrs') = length (one :: ixs)) as PTRS_SHIFTED_LENGTH.
          {
            symmetry.
            eapply map_monad_length with (f:=(fun ix : intptr => handle_gep_addr (DTYPE_I 8) p [DVALUE_IPTR ix])).
            cbn.
            red.
            rewrite Heqs0.
            rewrite Heqs1.
            reflexivity.
          }

          pose proof intptr_seq_len _ _ _ SEQ as UNSHIFTED_LENGTH.
          pose proof intptr_seq_len _ _ _ SEQ_SHIFT as SHIFTED_LENGTH.
          assert (n < S len)%nat as BOUND_n.
          { apply Nth_ix_lt_length in NTH.
            lia.
          }

          pose proof Nth_exists ptrs n as PTRS_n.
          forward PTRS_n; [lia|].
          destruct PTRS_n as [ptr_a PTRS_n].

          (* GEP with a *)
          apply handle_gep_addr_ix in Heqs0.
          pose proof Heqs as MAPM.
          eapply map_monad_err_Nth with (n:=n) in Heqs as [a' [GEP_a' NTH_a']].
          2: {
            (* Nth l'' n b *)
            (* Nth (one :: ixs) n a *)
            unfold sequence in Heqo.

            eapply map_monad_OOM_Nth with (n:=n) in Heqo as [pa [EQPA NTH_pa]].
            unfold id in EQPA. inv EQPA.
            eapply NTH_pa.
            eapply PTRS_n.
          }

          cbn in NTH, NTH_a'.
          rewrite NTH in NTH_a'.
          inv NTH_a'.

          rewrite sizeof_dtyp_i8 in Heqs0.
          rewrite from_Z_to_Z with (z:=1%Z) in Heqs0; auto.
          replace (ptr_to_int p + Z.of_N 1 * 1)%Z
            with (ptr_to_int p + 1)%Z in Heqs0 by lia.

          (* GEP with b *)
          assert (handle_gep_addr (DTYPE_I 8) p' [DVALUE_IPTR b] = ret (NoOom ptr_a)) as GEP_b.
          { rewrite handle_gep_addr_ix' with (p':= ptr_a).
            reflexivity.
            pose proof GEP_a' as GEP_a''.
            apply handle_gep_addr_ix in GEP_a'.
            rewrite Heqs0.
            rewrite from_Z_to_Z with (z:=Z.of_nat n); auto.
            rewrite from_Z_to_Z with (z:=(1 + Z.of_nat n)%Z) in GEP_a'; auto.
            rewrite sizeof_dtyp_i8.
            rewrite sizeof_dtyp_i8 in GEP_a'.
            replace (ptr_to_int p + 1 + Z.of_N 1 * Z.of_nat n)%Z
              with (ptr_to_int ptr_a) by lia.

            symmetry.
            eapply int_to_ptr_ptr_to_int.

            (* p' and ptr_a both have the same provenance as p *)
            assert (address_provenance p' = address_provenance p) as PROV.
            { rewrite map_monad_unfold in MAPM.
              cbn in MAPM.
              break_match_hyp; inv MAPM.
              break_match_hyp; inv H1.
              symmetry; eapply handle_gep_addr_preserves_provenance; eauto.
            }

            assert (address_provenance ptr_a = address_provenance p) as PROV_a.
            {
              symmetry; eapply handle_gep_addr_preserves_provenance; eauto.
            }

            congruence.
          }

          rewrite GEP_a'.
          rewrite GEP_b.
          reflexivity.
        }

        rewrite Heqs'.
        cbn.

        setoid_rewrite bind_ret_l.
        rewrite Heqo.
        cbn.

        eapply within_ret_refl; eauto.
      }
      { cbn in CONSEC.
        apply rw_ret_nin_raise in CONSEC; eauto.
        contradiction.
      }
  Qed.

  Lemma get_consecutive_ptrs_cons' :
    forall {M : Type -> Type}
      `{HM: Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM}
      {Pre : Type}
      {B} `{MB : Monad B}
      `{WM : @Within M EQM B Pre Pre}
      `{EQRET : @Eq1_ret_inv M EQM HM}
      `{WRET : @Within_ret_inv M B Pre Pre HM _ EQM WM}
      `{WRET_PP : @Within_ret_pre_post_inv M B Pre HM _ EQM WM}
      `{OOM: RAISE_OOM M} `{ERR: RAISE_ERROR M}
      `{LAWS: @MonadLawsE M EQM HM}
      `{RAISE_OOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
      `{RAISE_ERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}
      `{RWOOM : @RaiseWithin M B _ _ _ EQM WM string (@raise_oom M OOM)}
      `{RWERR : @RaiseWithin M B _ _ _ EQM WM string (@raise_error M ERR)}
      ptr len p ptrs pre post,
      (ret (p :: ptrs) {{pre}} ∈ {{post}} get_consecutive_ptrs ptr len)%monad ->
      p = ptr /\ ((ptrs = [] /\ len = 1%nat) \/ exists ptr' ip len', len = S len' /\ to_Z ip = 1%Z /\ handle_gep_addr (DTYPE_I 8) ptr [DVALUE_IPTR ip] = inr (NoOom ptr') /\ (ret ptrs {{pre}} ∈ {{post}} get_consecutive_ptrs ptr' len')%monad).
  Proof.
    intros M HM EQM' Pre B MB WM EQRET WRET WRET_PP EQV OOM ERR LAWS RAISE_OOM RAISE_ERR RWOOM RWERR ptr len p ptrs pre post CONSEC.

    assert (ret (p :: ptrs) ∈ get_consecutive_ptrs ptr len) as CONSEC_WITHIN.
    {
      exists pre. exists post.
      auto.
    }

    Transparent get_consecutive_ptrs.
    unfold get_consecutive_ptrs in *.
    destruct (intptr_seq 0 len) eqn:SEQ.
    2: {
      cbn in CONSEC_WITHIN.
      setoid_rewrite rbm_raise_bind in CONSEC_WITHIN; eauto.
      eapply rw_ret_nin_raise in CONSEC_WITHIN; eauto; contradiction.
    }

    cbn in *.
    setoid_rewrite bind_ret_l in CONSEC.
    setoid_rewrite bind_ret_l in CONSEC_WITHIN.

    generalize dependent len.
    destruct len; intros SEQ.
    - cbn in SEQ.
      inv SEQ.
      cbn in CONSEC_WITHIN.
      setoid_rewrite bind_ret_l in CONSEC_WITHIN.
      eapply within_ret_ret in CONSEC_WITHIN; [|typeclasses eauto].
      inv CONSEC_WITHIN.
    - rewrite intptr_seq_succ in SEQ.
      cbn in *.
      break_match_hyp; [| solve [inv SEQ]].
      break_match_hyp; [| solve [inv SEQ]].
      rename l0 into l'.
      inv SEQ.

      cbn in *.
      rewrite IP.from_Z_0 in Heqo.
      inv Heqo.
      rewrite handle_gep_addr_0 in *.

      (* Break match of map_monad in CONSEC *)
      break_match_hyp.
      { (* map_monad fails *)
        cbn in CONSEC_WITHIN.
        setoid_rewrite rbm_raise_bind in CONSEC_WITHIN; eauto.
        apply rw_ret_nin_raise in CONSEC_WITHIN; eauto.
        contradiction.
      }

      (* map_monad succeeds *)
      cbn in CONSEC.
      convert_to_ret_hyp.
      setoid_rewrite bind_ret_l in CONSEC.
      setoid_rewrite bind_ret_l in CONSEC_WITHIN.
      replace (sequence (ret ptr :: l)) with (sequence (NoOom ptr :: l)) in CONSEC_WITHIN; cbn; auto.
      destruct (sequence (NoOom ptr :: l)) eqn:SEQUENCE.
      { eapply within_ret_ret in CONSEC_WITHIN; subst; eauto.
        inv SEQUENCE.
        break_match_hyp; inv H0.
        split; auto.

        destruct len.
        + cbn in Heqo0.
          inv Heqo0.
          cbn in Heqs.
          inv Heqs.
          inv Heqo.
          left.
          auto.
        + pose proof Heqo0 as SEQ.
          rewrite intptr_seq_succ in SEQ.
          cbn in SEQ.
          break_match_hyp; [| solve [inv SEQ]].
          rename i into one.

          break_match_hyp; [| solve [inv SEQ]].
          inv SEQ.

          pose proof Heqs as MAPM.
          rewrite map_monad_unfold in MAPM.
          cbn in MAPM.
          break_match_hyp; [ solve [inv MAPM] |].
          break_match_hyp; [ solve [inv MAPM] |].
          inv MAPM.
          destruct o as [p' | oom_msg]; [|inversion Heqo].
          rename l1 into ptrs'.
          right.
          exists p'. exists one. exists (S len).
          split; auto.
          split.
          apply from_Z_to_Z; auto.
          split; auto.

          (* Need something about sequences *)
      (* Since len is the length, `intptr_seq 1 len` is basically just `map (+1) (intptr_seq 0 len)` *)
      (* Unfortunately, I don't think I have a lemma that gives me
         `IP.from_Z (x+1) = NoOom (i+1) -> IP.from_Z (x+1) = NoOom i`

         Maybe something like this should be an axiom, but I think it
         gets messy because memory is bounded in the + and -
         direction.

         I *DO* know that `IP.from_Z 0 = NoOom zero`, however, and all of the other elements in
         `intptr_seq 0 len` are in `intptr_seq 1 len`.

         `intptr_seq 1 len =
             map (fun ip => handle_gep_addr (DTYPE_I 8) ip [Events.DV.DVALUE_IPTR 1])
                 (intptr_seq 0 len)`
       *)

        rename l0 into ixs.
        pose proof Heqo0 as SEQ_SHIFT.
        apply intptr_seq_shifted in Heqo0.
        destruct Heqo0 as [ixs_unshifted [SEQ SHIFT]].
        rewrite SEQ.
        cbn.

        setoid_rewrite bind_ret_l.
        match goal with
        | _ : _ |- context [map_monad ?f ?l] =>
            assert (map_monad f l = inr (NoOom p' :: ptrs')) as Heqs'
        end.
        {
          eapply map_monad_eqv; eauto.
          eapply Forall2_forall.
          split.
          { eapply intptr_seq_len in SEQ, SEQ_SHIFT.
            lia.
          }

          intros n a b NTH NTH'.
          pose proof (intptr_seq_nth _ _ _ _ _ SEQ_SHIFT NTH) as IX.
          pose proof (intptr_seq_nth _ _ _ _ _ SEQ NTH') as IX'.
          cbn in IX'.

          (* Exists n in ptrs *)
          pose proof sequence_OOM_length _ _ Heqo as PTRS_LENGTH.
          assert (length (NoOom p' :: ptrs') = length (one :: ixs)) as PTRS_SHIFTED_LENGTH.
          {
            symmetry.
            eapply map_monad_length with (f:=(fun ix : intptr => handle_gep_addr (DTYPE_I 8) p [DVALUE_IPTR ix])).
            cbn.
            red.
            rewrite Heqs0.
            rewrite Heqs1.
            reflexivity.
          }

          pose proof intptr_seq_len _ _ _ SEQ as UNSHIFTED_LENGTH.
          pose proof intptr_seq_len _ _ _ SEQ_SHIFT as SHIFTED_LENGTH.
          assert (n < S len)%nat as BOUND_n.
          { apply Nth_ix_lt_length in NTH.
            lia.
          }

          pose proof Nth_exists ptrs n as PTRS_n.
          forward PTRS_n; [lia|].
          destruct PTRS_n as [ptr_a PTRS_n].

          (* GEP with a *)
          apply handle_gep_addr_ix in Heqs0.
          pose proof Heqs as MAPM.
          eapply map_monad_err_Nth with (n:=n) in Heqs as [a' [GEP_a' NTH_a']].
          2: {
            (* Nth l'' n b *)
            (* Nth (one :: ixs) n a *)
            unfold sequence in Heqo.

            eapply map_monad_OOM_Nth with (n:=n) in Heqo as [pa [EQPA NTH_pa]].
            unfold id in EQPA. inv EQPA.
            eapply NTH_pa.
            eapply PTRS_n.
          }

          cbn in NTH, NTH_a'.
          rewrite NTH in NTH_a'.
          inv NTH_a'.

          rewrite sizeof_dtyp_i8 in Heqs0.
          rewrite from_Z_to_Z with (z:=1%Z) in Heqs0; auto.
          replace (ptr_to_int p + Z.of_N 1 * 1)%Z
            with (ptr_to_int p + 1)%Z in Heqs0 by lia.

          (* GEP with b *)
          assert (handle_gep_addr (DTYPE_I 8) p' [DVALUE_IPTR b] = ret (NoOom ptr_a)) as GEP_b.
          { rewrite handle_gep_addr_ix' with (p':= ptr_a).
            reflexivity.
            pose proof GEP_a' as GEP_a''.
            apply handle_gep_addr_ix in GEP_a'.
            rewrite Heqs0.
            rewrite from_Z_to_Z with (z:=Z.of_nat n); auto.
            rewrite from_Z_to_Z with (z:=(1 + Z.of_nat n)%Z) in GEP_a'; auto.
            rewrite sizeof_dtyp_i8.
            rewrite sizeof_dtyp_i8 in GEP_a'.
            replace (ptr_to_int p + 1 + Z.of_N 1 * Z.of_nat n)%Z
              with (ptr_to_int ptr_a) by lia.

            symmetry.
            eapply int_to_ptr_ptr_to_int.

            (* p' and ptr_a both have the same provenance as p *)
            assert (address_provenance p' = address_provenance p) as PROV.
            { rewrite map_monad_unfold in MAPM.
              cbn in MAPM.
              break_match_hyp; inv MAPM.
              break_match_hyp; inv H0.
              symmetry; eapply handle_gep_addr_preserves_provenance; eauto.
            }

            assert (address_provenance ptr_a = address_provenance p) as PROV_a.
            {
              symmetry; eapply handle_gep_addr_preserves_provenance; eauto.
            }

            congruence.
          }

          rewrite GEP_a'.
          rewrite GEP_b.
          reflexivity.
        }

        rewrite Heqs'.
        cbn.

        setoid_rewrite bind_ret_l.
        rewrite Heqo.
        cbn.

        cbn in CONSEC.
        eapply within_ret_pre_post_always; eauto.
        eapply within_ret_refl_pre_post; eauto.
        Unshelve.
        auto.
      }
      { cbn in CONSEC_WITHIN.
        apply rw_ret_nin_raise in CONSEC_WITHIN; eauto.
        contradiction.
      }
  Qed.

  Lemma get_consecutive_ptrs_ge :
    forall {M : Type -> Type}
      `{HM: Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM}
      {Pre Post : Type}
      {B} `{MB : Monad B}
      `{WM : @Within M EQM B Pre Post}
      `{EQRET : @Eq1_ret_inv M EQM HM}
      `{WRET : @Within_ret_inv M B Pre Post HM _ EQM WM}
      `{OOM: RAISE_OOM M} `{ERR: RAISE_ERROR M}
      `{LAWS: @MonadLawsE M EQM HM}
      `{RAISE_OOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
      `{RAISE_ERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}
      `{RWOOM : @RaiseWithin M B _ _ _ EQM WM string (@raise_oom M OOM)}
      `{RWERR : @RaiseWithin M B _ _ _ EQM WM string (@raise_error M ERR)}
      ptr len ptrs,
      (ret ptrs ∈ get_consecutive_ptrs ptr len)%monad ->
      (forall p,
          In p ptrs ->
          (ptr_to_int ptr <= ptr_to_int p)%Z).
  Proof.
    intros M HM EQM' EQV Pre Post B MB WM EQRET WRET OOM ERR LAWS RAISE_OOM RAISE_ERR RWOOM RWERR ptr len ptrs.
    revert ptr len.
    induction ptrs; intros ptr len CONSEC p IN.
    - inv IN.
    - destruct IN as [IN | IN].
      + subst.
        eapply get_consecutive_ptrs_cons in CONSEC as (START & CONSEC).
        subst.
        lia.
      + pose proof CONSEC as CONSEC'.
        apply get_consecutive_ptrs_cons in CONSEC as (START & [(PTRS & LEN) | (ptr' & one & len' & LENEQ & ONE & GEP & CONSEC)]).
        { subst.
          inv IN.
        }

        subst.
        pose proof IHptrs as IHptrs'.
        specialize (IHptrs' _ _ CONSEC _ IN).

        (* `ptr'` is in `ptrs`, and everything in `ptrs >= ptr'`

           So, I know `ptr' <= p`

           I should know that `ptr < ptr'`...
         *)

        (* Could take get_consecutive_ptrs in CONSEC and CONSEC' and compare...

           What if ptrs = [ ]?

           I.e., len = 1... Then ptrs is nil and IN is a contradiction.
        *)

        destruct ptrs as [| ptr'0 ptrs].
        inv IN.

        (* Need to show that ptr'0 = ptr' *)
        pose proof CONSEC as CONSEC''.
        apply get_consecutive_ptrs_cons in CONSEC as (ptreq & [[PTRS LEN] | (ptr'' & one' & len'' & LENEQ & ONE' & GEP' & CONSEC)]).
        { subst.
          cbn in IN.
          destruct IN as [IN | []].
          subst.
          apply handle_gep_addr_ix in GEP.
          lia.
        }
        subst.

        assert (ptr_to_int ptr < ptr_to_int ptr')%Z.
        {
          unfold get_consecutive_ptrs in CONSEC'.
          cbn in CONSEC'.
          rewrite IP.from_Z_0 in CONSEC'.
          break_match_hyp.
          2: {
            cbn in CONSEC'.
            setoid_rewrite rbm_raise_bind in CONSEC'; eauto.
            eapply rw_ret_nin_raise in CONSEC'; eauto; contradiction.
          }

          cbn in CONSEC'.
          setoid_rewrite bind_ret_l in CONSEC'.

          break_match_hyp.
          2: {
            inv Heqo.
          }
          break_match_hyp; inv Heqo.
          cbn in CONSEC'.
          break_match_hyp; cbn in CONSEC'.
          setoid_rewrite rbm_raise_bind in CONSEC'; eauto.
          eapply rw_ret_nin_raise in CONSEC'; eauto; contradiction.
          break_match_hyp; cbn in CONSEC'.
          setoid_rewrite rbm_raise_bind in CONSEC'; eauto.
          eapply rw_ret_nin_raise in CONSEC'; eauto; contradiction.
          break_match_hyp; cbn in CONSEC'.
          inv Heqs0.
          break_match_hyp; inv Heqs0.

          setoid_rewrite bind_ret_l in CONSEC'.

          destruct o as [p' | oom_msg].
          2: {
            cbn in CONSEC'.
            eapply rw_ret_nin_raise in CONSEC'; eauto; contradiction.
          }

          destruct o0 as [p'' | oom_msg].
          2: {
            cbn in CONSEC'.
            eapply rw_ret_nin_raise in CONSEC'; eauto; contradiction.
          }

          apply handle_gep_addr_ix in Heqs.
          apply handle_gep_addr_ix in Heqs1.

          cbn in CONSEC'.
          break_match_hyp.
          2: {
            cbn in CONSEC'.
            eapply rw_ret_nin_raise in CONSEC'; eauto; contradiction.
          }

          cbn in CONSEC'.

          apply within_ret_ret in CONSEC'; eauto.
          inv CONSEC'.

          rewrite sizeof_dtyp_i8 in *.
          erewrite IP.from_Z_to_Z in Heqs1; eauto.
          break_match_hyp; inv Heqo.
          lia.
        }
        lia.
  Qed.

  Lemma get_consecutive_ptrs_ge_eq1 :
    forall {M : Type -> Type}
      `{HM: Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM}
      {B} `{MB : Monad B}
      `{EQRET : @Eq1_ret_inv M EQM HM}
      `{OOM: RAISE_OOM M} `{ERR: RAISE_ERROR M}
      `{LAWS: @MonadLawsE M EQM HM}
      `{RAISE_OOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
      `{RAISE_ERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}
      ptr len ptrs,
      (get_consecutive_ptrs ptr len ≈ ret ptrs)%monad ->
      (forall p,
          In p ptrs ->
          (ptr_to_int ptr <= ptr_to_int p)%Z).
  Proof.
    intros M HM EQM0 EQV B MB EQRET OOM ERR LAWS RAISE_OOM RAISE_ERR
      ptr len ptrs CONSEC p IN.

    assert (@within M EQM0 M unit unit (Reflexive_Within) _
              (@get_consecutive_ptrs M HM OOM ERR ptr len)
              tt
              (@ret M HM (list addr) ptrs)
              tt
           ) as WITHIN.
    { cbn. red.
      auto.
    }

    eapply @get_consecutive_ptrs_ge with (B:=M);
      eauto; typeclasses eauto.
  Qed.

  Lemma get_consecutive_ptrs_range :
    forall {M : Type -> Type}
      `{HM: Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM}
      {Pre Post : Type}
      {B} `{MB : Monad B}
      `{WM : @Within M EQM B Pre Post}
      `{EQRET : @Eq1_ret_inv M EQM HM}
      `{WRET : @Within_ret_inv M B Pre Post HM _ EQM WM}
      `{OOM: RAISE_OOM M} `{ERR: RAISE_ERROR M}
      `{LAWS: @MonadLawsE M EQM HM}
      `{RBMOOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
      `{RBMERR : @RaiseBindM M  HM EQM string (@raise_error M ERR)}
      `{RWOOM : @RaiseWithin M B _ _ _ EQM WM string (@raise_oom M OOM)}
      `{RWERR : @RaiseWithin M B _ _ _ EQM WM string (@raise_error M ERR)}
      ptr len ptrs,
      (ret ptrs ∈ get_consecutive_ptrs ptr len)%monad ->
      (forall p,
          In p ptrs ->
          (ptr_to_int ptr <= ptr_to_int p < ptr_to_int ptr + (Z.of_nat len))%Z).
  Proof.
    intros M HM EQM EQV Pre Post B MB WM EQRET WRET OOM ERR LAWS RBMOOM RBMERR RWOOM RWERR ptr len ptrs.
    revert ptr len.
    induction ptrs; intros ptr len CONSEC p IN.
    - inv IN.
    - induction IN as [IN | IN].
      + subst.
        apply get_consecutive_ptrs_cons in CONSEC as (START & [[PTRS LEN] | (ptr' & one & len' & LENEQ & ONE & GEP & CONSEC)]);
          subst; lia.
      + pose proof CONSEC as CONSEC'.
        apply get_consecutive_ptrs_cons in CONSEC as (START & [[PTRS LEN] | (ptr' & one & len' & LENEQ & ONE & GEP & CONSEC)]).
        { subst.
          inv IN.
        }

        subst.
        pose proof IHptrs as IHptrs'.
        specialize (IHptrs' _ _ CONSEC _ IN).

        (* `ptr'` is in `ptrs`, and everything in `ptrs >= ptr'`

           So, I know `ptr' <= p`

           I should know that `ptr < ptr'`...
         *)

        (* Could take get_consecutive_ptrs in CONSEC and CONSEC' and compare...

           What if ptrs = [ ]?

           I.e., len = 1... Then ptrs is nil and IN is a contradiction.
        *)

        destruct ptrs as [| ptr'0 ptrs].
        inv IN.

        (* Need to show that ptr'0 = ptr' *)
        pose proof CONSEC as CONSEC''.
        apply get_consecutive_ptrs_cons in CONSEC as (ptreq & [[PTRS LEN] | (ptr'' & one' & len'' & LENEQ' & ONE' & GEP' & CONSEC)]).
        {
          subst.
          destruct IN as [IN | []].
          subst.
          apply handle_gep_addr_ix in GEP.
          rewrite GEP.
          rewrite sizeof_dtyp_i8.
          lia.
        }

        subst.

        assert (Z.succ (ptr_to_int ptr) = ptr_to_int ptr')%Z.
        { unfold get_consecutive_ptrs in CONSEC'.
          cbn in CONSEC'.
          break_match_hyp.
          2: { cbn in CONSEC'.
               setoid_rewrite rbm_raise_bind in CONSEC'; [|typeclasses eauto].
               convert_to_ret_hyp.
               eapply rw_ret_nin_raise in CONSEC'; [contradiction | typeclasses eauto].
          }

          break_match_hyp.
          2: { cbn in CONSEC'.
               setoid_rewrite rbm_raise_bind in CONSEC'; [|typeclasses eauto].
               convert_to_ret_hyp.
               eapply rw_ret_nin_raise in CONSEC'; [contradiction | typeclasses eauto].
          }

          cbn in CONSEC'.
          setoid_rewrite bind_ret_l in CONSEC'.
          destruct (map_monad (fun ix : IP.intptr => handle_gep_addr (DTYPE_I 8) ptr [DVALUE_IPTR ix])
                              (i :: l)) eqn:HMAPM.
          { cbn in CONSEC'.
            setoid_rewrite rbm_raise_bind in CONSEC'; [|typeclasses eauto].
            eapply rw_ret_nin_raise in CONSEC'; [contradiction | typeclasses eauto].
          }

          cbn in CONSEC'.
          setoid_rewrite bind_ret_l in CONSEC'.
          destruct (sequence l0) eqn:HSEQUENCE.
          2: {
            cbn in CONSEC'.
            eapply rw_ret_nin_raise in CONSEC'; [contradiction | typeclasses eauto].
          }

          cbn in CONSEC'.
          apply within_ret_ret in CONSEC'; eauto.
          inv CONSEC'.
          break_match_hyp; inv Heqo0.
          break_match_hyp; inv H1.
          cbn in HMAPM.
          break_match_hyp; [inv HMAPM|].
          break_match_hyp; [inv HMAPM|].
          break_match_hyp; [inv Heqs0|].
          break_match_hyp; inv Heqs0.
          inv HMAPM.

          destruct o as [p' | oom_msg].
          2: {
            cbn in HSEQUENCE; inv HSEQUENCE.
          }

          destruct o0 as [p'' | oom_msg].
          2: {
            cbn in HSEQUENCE; inv HSEQUENCE.
          }

          apply handle_gep_addr_ix in Heqs1.
          rewrite sizeof_dtyp_i8 in Heqs1.
          rewrite (IP.from_Z_to_Z _ _ Heqo1) in Heqs1.
          cbn in HSEQUENCE.
          break_match_hyp; inv HSEQUENCE.
          break_match_hyp; inv Heqo2.
          lia.
        }
        lia.
  Qed.

  Lemma get_consecutive_ptrs_range_eq1 :
    forall {M : Type -> Type}
      `{HM: Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM}
      {B} `{MB : Monad B}
      `{EQRET : @Eq1_ret_inv M EQM HM}
      `{OOM: RAISE_OOM M} `{ERR: RAISE_ERROR M}
      `{LAWS: @MonadLawsE M EQM HM}
      `{RBMOOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
      `{RBMERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}
      ptr len ptrs,
      (get_consecutive_ptrs ptr len ≈ ret ptrs)%monad ->
      (forall p,
          In p ptrs ->
          (ptr_to_int ptr <= ptr_to_int p < ptr_to_int ptr + (Z.of_nat len))%Z).
  Proof.
    intros M HM EQM EQV B MB EQRET OOM ERR LAWS RBMOOM RBMERR
      ptr len ptrs CONSEC p IN.

    assert (@within M EQM M unit unit (Reflexive_Within) _
              (@get_consecutive_ptrs M HM OOM ERR ptr len)
              tt
              (@ret M HM (list addr) ptrs)
              tt
           ) as WITHIN.
    { cbn. red.
      auto.
    }

    eapply @get_consecutive_ptrs_range with (B:=M);
      eauto; typeclasses eauto.
  Qed.

  Lemma get_consecutive_ptrs_nth :
    forall {M : Type -> Type}
      `{HM: Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM}
      {Pre Post : Type}
      {B} `{MB : Monad B}
      `{WM : @Within M EQM B Pre Post}
      `{WRET : @Within_ret_inv M B Pre Post HM _ EQM WM}
      `{OOM: RAISE_OOM M} `{ERR: RAISE_ERROR M}
      `{LAWS: @MonadLawsE M EQM HM}
      `{RAISE_OOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
      `{RAISE_ERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}
      `{RWOOM : @RaiseWithin M B _ _ _ EQM WM string (@raise_oom M OOM)}
      `{RWERR : @RaiseWithin M B _ _ _ EQM WM string (@raise_error M ERR)}
      ptr len ptrs,
      (ret ptrs ∈ get_consecutive_ptrs ptr len)%monad ->
      (forall p ix_nat,
          Util.Nth ptrs ix_nat p ->
          exists ix,
            NoOom ix = IP.from_Z (Z.of_nat ix_nat) /\
              handle_gep_addr (DTYPE_I 8) ptr [Events.DV.DVALUE_IPTR ix] = inr (ret p)).
  Proof.
    intros M HM EQM EQV Pre Post B MB WM WRET OOM ERR LAWS RAISE_OOM RAISE_ERR RWOOM RWERR
      ptr len ptrs CONSEC p ix_nat NTH.

    pose proof CONSEC as CONSEC'.
    unfold get_consecutive_ptrs in CONSEC.
    destruct (intptr_seq 0 len) eqn:SEQ.
    2: {
      cbn in CONSEC.
      setoid_rewrite rbm_raise_bind in CONSEC; auto.
      convert_to_ret_hyp.
      apply rw_ret_nin_raise in CONSEC; try contradiction; auto.
    }

    cbn in CONSEC.
    setoid_rewrite bind_ret_l in CONSEC.
    destruct (map_monad
                (fun ix : IP.intptr => handle_gep_addr (DTYPE_I 8) ptr [Events.DV.DVALUE_IPTR ix]) l) eqn:MAP.
    { cbn in CONSEC.
      setoid_rewrite rbm_raise_bind in CONSEC; auto.
      apply rw_ret_nin_raise in CONSEC; try contradiction; auto.
    }

    cbn in CONSEC.
    setoid_rewrite bind_ret_l in CONSEC.
    destruct (sequence l0) eqn:HSEQUENCE.
    2: {
      cbn in CONSEC.
      apply rw_ret_nin_raise in CONSEC; try contradiction; auto.
    }

    apply within_ret_ret in CONSEC; auto.
    inv CONSEC.

    pose proof MAP as PTRS.
    eapply map_monad_err_Forall2 in PTRS.
    eapply Forall2_forall in PTRS.
    destruct PTRS as [PTRSLEN PTRS].

    pose proof HSEQUENCE.
    eapply map_monad_OOM_Nth in HSEQUENCE; eauto.
    destruct HSEQUENCE as [y [EQY NTHY]].
    unfold id in EQY; inv EQY.

    eapply map_monad_err_Nth in MAP as [ix [P NTH']]; eauto.
    exists ix; split; eauto.

    eapply intptr_seq_nth in SEQ; eauto.
  Qed.

  Lemma get_consecutive_ptrs_nth_eq1 :
    forall {M : Type -> Type}
      `{HM: Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM}
      `{EQRET : @Eq1_ret_inv M EQM HM}
      {B} `{MB : Monad B}
      `{OOM: RAISE_OOM M} `{ERR: RAISE_ERROR M}
      `{LAWS: @MonadLawsE M EQM HM}
      `{RAISE_OOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
      `{RAISE_ERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}
      ptr len ptrs,
      (get_consecutive_ptrs ptr len ≈ ret ptrs)%monad ->
      (forall p ix_nat,
          Util.Nth ptrs ix_nat p ->
          exists ix,
            NoOom ix = IP.from_Z (Z.of_nat ix_nat) /\
              handle_gep_addr (DTYPE_I 8) ptr [Events.DV.DVALUE_IPTR ix] = inr (ret p)).
  Proof.
    intros M HM EQM EQV EQRET B MB OOM ERR LAWS RAISE_OOM RAISE_ERR
      ptr len ptrs CONSEC p ix_nat NTH.

    assert (@within M EQM M unit unit (Reflexive_Within) _
              (@get_consecutive_ptrs M HM OOM ERR ptr len)
              tt
              (@ret M HM (list addr) ptrs)
              tt
           ) as WITHIN.
    { cbn. red.
      auto.
    }

    eapply @get_consecutive_ptrs_nth with (B:=M);
      eauto; typeclasses eauto.
  Qed.

  Lemma get_consecutive_ptrs_prov :
    forall {M : Type -> Type}
      `{HM: Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM}
      {Pre Post : Type}
      {B} `{MB : Monad B}
      `{WM : @Within M EQM B Pre Post}
      `{WRET : @Within_ret_inv M B Pre Post HM _ EQM WM}
      `{OOM: RAISE_OOM M} `{ERR: RAISE_ERROR M}
      `{LAWS: @MonadLawsE M EQM HM}
      `{RBMOOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
      `{RBMERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}
      `{RWOOM : @RaiseWithin M B _ _ _ EQM WM string (@raise_oom M OOM)}
      `{RWERR : @RaiseWithin M B _ _ _ EQM WM string (@raise_error M ERR)}
      ptr len ptrs,
      (ret ptrs ∈ get_consecutive_ptrs ptr len)%monad ->
      forall p, In p ptrs -> address_provenance p = address_provenance ptr.
  Proof.
    intros M HM EQM' EQV Pre Post B MB WM WRET OOM ERR LAWS RAISE_OOM RAISE_ERR RWOOM RWERR ptr len ptrs CONSEC p IN.
    apply In_nth_error in IN as (ix_nat & NTH).
    pose proof CONSEC as GEP.
    eapply get_consecutive_ptrs_nth in GEP; cbn; eauto.
    destruct GEP as (ix & IX & GEP).

    apply handle_gep_addr_preserves_provenance in GEP.
    eauto.
  Qed.

  Lemma get_consecutive_ptrs_prov_eq1 :
    forall {M : Type -> Type}
      `{HM: Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM}
      `{EQR : @Eq1_ret_inv M EQM HM}
      `{OOM: RAISE_OOM M} `{ERR: RAISE_ERROR M}
      `{LAWS: @MonadLawsE M EQM HM}
      `{RBMOOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
      `{RBMERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}
      ptr len ptrs,
      (get_consecutive_ptrs ptr len ≈ ret ptrs)%monad ->
      forall p, In p ptrs -> address_provenance p = address_provenance ptr.
  Proof.
    intros M HM EQM0 EQV EQR OOM ERR LAWS RBMOOM RBMERR ptr len ptrs CONSEC p IN.
    assert (@within M EQM0 M unit unit (Reflexive_Within) _
              (@get_consecutive_ptrs M HM OOM ERR ptr len)
              tt
              (@ret M HM (list addr) ptrs)
              tt
           ) as WITHIN.
    { cbn. red.
      auto.
    }

    eapply @get_consecutive_ptrs_prov with (B:=M);
      eauto; typeclasses eauto.
  Qed.

  Lemma get_consecutive_ptrs_inv :
    forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M}
      `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM} `{LAWS: @MonadLawsE M EQM HM}
      `{RAISE : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
      (ptr : addr) (len : nat),
      (exists msg, @get_consecutive_ptrs M HM OOM ERR ptr len ≈ raise_oom msg) \/
        (exists ptrs, @get_consecutive_ptrs M HM OOM ERR ptr len ≈ ret ptrs).
  Proof.
    intros M HM OOM ERR EQM' EQV LAWS RAISE ptr len.
    unfold get_consecutive_ptrs.
    destruct (intptr_seq 0 len) eqn:HSEQ.
    - pose proof (map_monad_err_succeeds
                    (fun ix : IP.intptr => handle_gep_addr (DTYPE_I 8) ptr [Events.DV.DVALUE_IPTR ix]) l) as HMAPM.
      forward HMAPM.
      { intros a IN.
        destruct (int_to_ptr (ptr_to_int ptr + Z.of_N (sizeof_dtyp (DTYPE_I 8)) * IP.to_Z a)%Z (address_provenance ptr)) eqn:IX.
        - exists (ret a0).
          apply handle_gep_addr_ix'; cbn; auto.
        - eapply handle_gep_addr_ix'_OOM in IX; auto.
          destruct IX as [msg IX].
          exists (Oom msg).
          cbn; auto.
      }

      destruct HMAPM as (ptrs & HMAPM).

      destruct (sequence ptrs) eqn:HSEQUENCE.
      { rename l0 into ptrs'.
        right.
        exists ptrs'.
        cbn.
        rewrite bind_ret_l.
        rewrite HMAPM.
        setoid_rewrite bind_ret_l.
        rewrite HSEQUENCE.
        cbn.
        reflexivity.
      }

      { left.
        exists s.
        cbn.
        rewrite bind_ret_l.
        rewrite HMAPM.
        setoid_rewrite bind_ret_l.
        rewrite HSEQUENCE.
        cbn.
        reflexivity.
      }
    - left.
      exists s.
      cbn.
      rewrite rbm_raise_bind; [reflexivity|eauto].
  Qed.

  Lemma get_consecutive_ptrs_no_ub:
    forall {M : Type -> Type}
      `{HM: Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM}
      {Pre Post : Type}
      {B} `{MB : Monad B}
      `{WM : @Within M EQM B Pre Post}
      `{WRET : @Within_ret_inv M B Pre Post HM MB EQM WM}
      `{OOM: RAISE_OOM M} `{ERR: RAISE_ERROR M}
      `{UBB: RAISE_UB B}
      `{LAWS: @MonadLawsE M EQM HM}
      `{RBMOOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
      `{RBMERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}
      `{RWOOM : @RaiseWithin M B _ _ MB EQM WM string (@raise_oom M OOM)}
      `{RWERR : @RaiseWithin M B _ _ MB EQM WM string (@raise_error M ERR)}
      `{RWUB : @RetWithin M B _ _ HM EQM WM string (@raise_ub B _)}
      `{DRUBOOM :  @DisjointRaiseWithin M B _ _ EQM WM string (@raise_ub B _) (@raise_oom M OOM)}
      msg ptr len,
      (raise_ub msg ∉ get_consecutive_ptrs ptr len)%monad.
  Proof.
    intros M HM EQM EQV Pre Post B MB WM WRET OOM ERR UBB LAWS RBMOOM RBMERR RWOOM RWERR RWUB DRUBOOM msg ptr len.
    intros CONTRA.

    unfold get_consecutive_ptrs in *.
    destruct (intptr_seq 0 len) eqn:HSEQ.

    2: {
      cbn in CONTRA.
      setoid_rewrite rbm_raise_bind in CONTRA; auto.

      convert_to_raise_hyp.
      eapply disjoint_raise_within in CONTRA; try contradiction; auto.
    }

    cbn in CONTRA.
    setoid_rewrite bind_ret_l in CONTRA.

    pose proof (map_monad_err_succeeds
                  (fun ix : IP.intptr => handle_gep_addr (DTYPE_I 8) ptr [Events.DV.DVALUE_IPTR ix]) l) as HMAPM.
      forward HMAPM.
      { intros a IN.
        destruct (int_to_ptr (ptr_to_int ptr + Z.of_N (sizeof_dtyp (DTYPE_I 8)) * IP.to_Z a)%Z (address_provenance ptr)) eqn:IX.
        - exists (ret a0).
          apply handle_gep_addr_ix'; cbn; auto.
        - eapply handle_gep_addr_ix'_OOM in IX; auto.
          destruct IX as [msg' IX].
          exists (Oom msg').
          cbn; auto.
      }

      destruct HMAPM as (ptrs & HMAPM).
      rewrite HMAPM in CONTRA.
      cbn in CONTRA.

      setoid_rewrite bind_ret_l in CONTRA.
      destruct (sequence ptrs) eqn:HSEQUENCE.
      2: {
        cbn in CONTRA.
        eapply disjoint_raise_within in CONTRA; eauto.
      }

      eapply rw_raise_nin_ret in CONTRA; eauto.
  Qed.

  Lemma get_consecutive_ptrs_success_always_succeeds :
    forall {M : Type -> Type}
      `{HM: Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM}
      {Pre Post : Type}
      {B} `{MB : Monad B}
      `{WM : @Within M EQM B Pre Post}
      `{WRET : @Within_ret_inv M B Pre Post HM _ EQM WM}
      `{OOM: RAISE_OOM M} `{ERR: RAISE_ERROR M}
      `{LAWS: @MonadLawsE M EQM HM}
      `{RBMOOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
      `{RBMERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}
      `{RWOOM : @RaiseWithin M B _ _ _ EQM WM string (@raise_oom M OOM)}
      `{RWERR : @RaiseWithin M B _ _ _ EQM WM string (@raise_error M ERR)}
      `{RIW : @RetInvWithin M B _ _ _ _ EQM WM}
      ptr len ptrs_res x,
      (ret ptrs_res ∈ get_consecutive_ptrs ptr len)%monad ->
      (x ∈ get_consecutive_ptrs ptr len)%monad ->
      x = ret ptrs_res.
  Proof.
    intros M HM EQM EQV Pre Post B MB WM WRET OOM ERR LAWS RBMOOM RBMERR RWOOM RWERR RIW ptr len ptrs_res x GCP GCP'.
    unfold get_consecutive_ptrs in *.
    destruct (intptr_seq 0 len) eqn:HSEQ.
    - pose proof (map_monad_err_succeeds
                    (fun ix : IP.intptr => handle_gep_addr (DTYPE_I 8) ptr [Events.DV.DVALUE_IPTR ix]) l) as HMAPM.
      forward HMAPM.
      { intros a IN.
        destruct (int_to_ptr (ptr_to_int ptr + Z.of_N (sizeof_dtyp (DTYPE_I 8)) * IP.to_Z a)%Z (address_provenance ptr)) eqn:IX.
        - exists (ret a0).
          apply handle_gep_addr_ix'; cbn; auto.
        - eapply handle_gep_addr_ix'_OOM in IX; auto.
          destruct IX as [msg IX].
          exists (Oom msg).
          cbn; auto.
      }

      destruct HMAPM as (ptrs & HMAPM).
      cbn in *.
      setoid_rewrite bind_ret_l in GCP.
      setoid_rewrite bind_ret_l in GCP'.
      rewrite HMAPM in GCP, GCP'.
      cbn in *.
      setoid_rewrite bind_ret_l in GCP.
      setoid_rewrite bind_ret_l in GCP'.

      destruct (sequence ptrs) eqn:HSEQUENCE.
      { rename l0 into ptrs'.
        cbn in *.
        apply within_ret_ret in GCP; eauto; subst.
        eapply rw_ret_inv in GCP'; eauto.
      }

      { cbn in *.
        apply rw_ret_nin_raise in GCP; eauto.
        contradiction.
      }
    - cbn in *.
      setoid_rewrite rbm_raise_bind in GCP; eauto.
      apply rw_ret_nin_raise in GCP; eauto.
      contradiction.
  Qed.

  Definition generate_num_undef_bytes_h (start_ix : N) (num : N) (dt : dtyp) (sid : store_id) : OOM (list SByte) :=
    N.recursion
      (fun (x : N) => ret [])
      (fun n mf x =>
         rest_bytes <- mf (N.succ x);;
         let byte := uvalue_sbyte (UVALUE_Undef dt) dt x sid in
         ret (byte :: rest_bytes))
      num start_ix.

  Definition generate_num_undef_bytes (num : N) (dt : dtyp) (sid : store_id) : OOM (list SByte) :=
    generate_num_undef_bytes_h 0 num dt sid.

  Definition generate_undef_bytes (dt : dtyp) (sid : store_id) : OOM (list SByte) :=
    generate_num_undef_bytes (sizeof_dtyp dt) dt sid.

  Lemma generate_num_undef_bytes_h_length :
    forall num start_ix dt sid bytes,
      generate_num_undef_bytes_h start_ix num dt sid = NoOom bytes ->
      num = N.of_nat (length bytes).
  Proof.
    intros num.
    induction num using N.peano_rect; intros start_ix dt sid bytes GEN.
    - cbn in *.
      inv GEN.
      reflexivity.
    - unfold generate_num_undef_bytes_h in GEN.
      pose proof @N.recursion_succ (N -> OOM (list SByte)) eq (fun _ : N => ret [])
           (fun (_ : N) (mf : N -> OOM (list SByte)) (x : N) =>
           rest_bytes <- mf (N.succ x);;
           ret (uvalue_sbyte (UVALUE_Undef dt) dt x sid :: rest_bytes))
           eq_refl.
      forward H.
      { unfold Proper, respectful.
        intros x y H0 x0 y0 H1; subst.
        reflexivity.
      }
      specialize (H num).
      rewrite H in GEN.
      clear H.

      destruct
        (N.recursion (fun _ : N => ret [])
                     (fun (_ : N) (mf : N -> OOM (list SByte)) (x : N) =>
                        rest_bytes <- mf (N.succ x);;
                        ret (uvalue_sbyte (UVALUE_Undef dt) dt x sid :: rest_bytes)) num
                     (N.succ start_ix)) eqn:HREC.
      + (* No OOM *)
        cbn in GEN.
        inv GEN.
        cbn.

        unfold generate_num_undef_bytes_h in IHnum.
        pose proof (IHnum (N.succ start_ix) dt sid l HREC) as IH.
        lia.
      + (* OOM *)
        cbn in GEN.
        inv GEN.
  Qed.

  Lemma generate_num_undef_bytes_length :
    forall num dt sid bytes,
      generate_num_undef_bytes num dt sid = NoOom bytes ->
      num = N.of_nat (length bytes).
  Proof.
    intros num dt sid bytes GEN.
    unfold generate_num_undef_bytes in *.
    eapply generate_num_undef_bytes_h_length; eauto.
  Qed.

  Lemma generate_undef_bytes_length :
    forall dt sid bytes,
      generate_undef_bytes dt sid = ret bytes ->
      sizeof_dtyp dt = N.of_nat (length bytes).
  Proof.
    intros dt sid bytes GEN_UNDEF.
    unfold generate_undef_bytes in *.
    apply generate_num_undef_bytes_length in GEN_UNDEF; auto.
  Qed.

  Section Serialization.
    (** ** Serialization *)
  (*      Conversion back and forth between values and their byte representation *)
  (*    *)
    (* Given a little endian list of bytes, match the endianess of `e` *)
    Definition correct_endianess {BYTES : Type} (e : Endianess) (bytes : list BYTES)
      := match e with
         | ENDIAN_BIG => rev bytes
         | ENDIAN_LITTLE => bytes
         end.

    (* Converts an integer [x] to its byte representation over [n] bytes. *)
  (*    The representation is little endian. In particular, if [n] is too small, *)
  (*    only the least significant bytes are returned. *)
  (*    *)
    Fixpoint bytes_of_int_little_endian (n: nat) (x: Z) {struct n}: list byte :=
      match n with
      | O => nil
      | S m => Byte.repr x :: bytes_of_int_little_endian m (x / 256)
      end.

    Definition bytes_of_int (e : Endianess) (n : nat) (x : Z) : list byte :=
      correct_endianess e (bytes_of_int_little_endian n x).

    (* *)
  (* Definition sbytes_of_int (e : Endianess) (count:nat) (z:Z) : list SByte := *)
  (*   List.map Byte (bytes_of_int e count z). *)

    Definition uvalue_bytes_little_endian (uv :  uvalue) (dt : dtyp) (sid : store_id) : list uvalue
      := map (fun n => UVALUE_ExtractByte uv dt n sid)
           (Nseq 0 (N.to_nat (sizeof_dtyp DTYPE_Pointer))).

    Definition uvalue_bytes (e : Endianess) (uv :  uvalue) (dt : dtyp) (sid : store_id) : list uvalue
      :=  (correct_endianess e) (uvalue_bytes_little_endian uv dt sid).

    (* TODO: move this *)
    Definition dtyp_eqb (dt1 dt2 : dtyp) : bool
      := match @dtyp_eq_dec dt1 dt2 with
         | left x => true
         | right x => false
         end.

    (* TODO: revive this *)
    (* Definition fp_alignment (bits : N) : option Alignment := *)
    (*   let fp_map := dl_floating_point_alignments datalayout *)
    (*   in NM.find bits fp_map. *)

    (*  TODO: revive this *)
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

    Definition dtyp_extract_fields (dt : dtyp) : err (list dtyp)
      := match dt with
         | DTYPE_Struct fields
         | DTYPE_Packed_struct fields =>
             ret fields
         | DTYPE_Array sz t
         | DTYPE_Vector sz t =>
             ret (repeat t (N.to_nat sz))
         | _ => inl "No fields."%string
         end.

    Definition extract_byte_to_sbyte (uv : uvalue) : ERR SByte
      := match uv with
         | UVALUE_ExtractByte uv dt idx sid =>
             ret (uvalue_sbyte uv dt idx sid)
         | _ => inl (ERR_message "extract_byte_to_ubyte invalid conversion.")
         end.

    Definition sbyte_sid_match (a b : SByte) : bool
      := match sbyte_to_extractbyte a, sbyte_to_extractbyte b with
         | UVALUE_ExtractByte uv dt idx sid, UVALUE_ExtractByte uv' dt' idx' sid' =>
             N.eqb sid sid'
         | _, _ => false
         end.

    Definition replace_sid (sid : store_id) (ub : SByte) : SByte
      := match sbyte_to_extractbyte ub with
         | UVALUE_ExtractByte uv dt idx sid_old =>
             uvalue_sbyte uv dt idx sid
         | _ =>
             ub (* Should not happen... *)
         end.

    Definition filter_sid_matches (byte : SByte) (sbytes : list (N * SByte)) : (list (N * SByte) * list (N * SByte))
      := filter_split (fun '(n, uv) => sbyte_sid_match byte uv) sbytes.

    (* TODO: should I move this? *)
    (* Assign fresh sids to ubytes while preserving entanglement *)
    (* Could potentially turn this into map (+max_sid) *)
    Program Fixpoint re_sid_ubytes_helper {M} `{Monad M} `{MonadStoreId M} `{RAISE_ERROR M}
            (bytes : list (N * SByte)) (acc : NMap SByte) {measure (length bytes)} : M (NMap SByte)
      := match bytes with
         | [] => ret acc
         | ((n, x)::xs) =>
             match sbyte_to_extractbyte x with
             | UVALUE_ExtractByte uv dt idx sid =>
                 let '(ins, outs) := filter_sid_matches x xs in
                 nsid <- fresh_sid;;
                 let acc := @NM.add _ n (replace_sid nsid x) acc in
                 (* Assign new sid to entangled bytes *)
                 let acc := fold_left (fun acc '(n, ub) => @NM.add _ n (replace_sid nsid ub) acc) ins acc in
                 re_sid_ubytes_helper outs acc
             | _ => raise_error "re_sid_ubytes_helper: sbyte_to_extractbyte did not yield UVALUE_ExtractByte"
             end
         end.
    Next Obligation.
      cbn.
      symmetry in Heq_anonymous.
      apply filter_split_out_length in Heq_anonymous.
      lia.
    Defined.

    Lemma re_sid_ubytes_helper_equation {M} `{Monad M} `{MonadStoreId M} `{RAISE_ERROR M}
          (bytes : list (N * SByte)) (acc : NMap SByte) :
      re_sid_ubytes_helper bytes acc =
        match bytes with
        | [] => ret acc
        | ((n, x)::xs) =>
            match sbyte_to_extractbyte x with
            | UVALUE_ExtractByte uv dt idx sid =>
                let '(ins, outs) := filter_sid_matches x xs in
                nsid <- fresh_sid;;
                let acc := @NM.add _ n (replace_sid nsid x) acc in
                (* Assign new sid to entangled bytes *)
                let acc := fold_left (fun acc '(n, ub) => @NM.add _ n (replace_sid nsid ub) acc) ins acc in
                re_sid_ubytes_helper outs acc
            | _ => raise_error "re_sid_ubytes_helper: sbyte_to_extractbyte did not yield UVALUE_ExtractByte"
            end
        end.
    Proof.
      unfold re_sid_ubytes_helper at 1.
      unfold re_sid_ubytes_helper_func at 1.
      rewrite Wf.WfExtensionality.fix_sub_eq_ext.
      destruct bytes.
      - reflexivity.
      - simpl. destruct p.
        destruct (sbyte_to_extractbyte s); try reflexivity.
        destruct (filter_sid_matches s bytes).
        apply f_equal.
        apply functional_extensionality.
        intros nsid.
        unfold re_sid_ubytes_helper.
        unfold re_sid_ubytes_helper_func.
        assert ((fun (acc : NM.t SByte) '(n, ub) => NM.add n (replace_sid nsid ub) acc) =
                  (fun (acc : NM.t SByte) (pat : NM.key * SByte) =>
                       (let
                        '(n, ub) as anonymous' := pat return (anonymous' = pat -> NM.t SByte) in
                         fun _ : (n, ub) = pat => NM.add n (replace_sid nsid ub) acc) eq_refl)) as EQN.
        { apply functional_extensionality. intros.
          apply functional_extensionality. intros.
          destruct x0.
          reflexivity. }
        rewrite EQN.
        reflexivity.
    Qed.

    (* Much easier to reason about this version. *)
    (*
    Definition re_sid_ubytes {M} `{Monad M} `{MonadStoreId M} `{RAISE_ERROR M}
               (bytes : list SByte) : M (list SByte)
      :=
      match bytes with
      | [] => ret []
      | b::bs =>
          n <- fresh_sid ;;   (* n > max > min *)
          (min,max) <- get_min_max_fresh_sid b bs ;;  (* forall b, In b bytes -> min <= sid b  /\ sid b <= max *)
          bytes' <- map_monad (bump_sid_by (n - min)) bytes ;;
          set_fresh (1 + (max + (n - min))) ;;  (* n < 1 + (max + (n - min)) *)
          ret bytes'
      end.
     *)

    Definition re_sid_ubytes {M} `{Monad M} `{MonadStoreId M} `{RAISE_ERROR M}
               (bytes : list SByte) : M (list SByte)
      := let len := length bytes in
         byte_map <- re_sid_ubytes_helper (zip (Nseq 0 len) bytes) (@NM.empty _);;
         trywith_error "re_sid_ubytes: missing indices." (NM_find_many (Nseq 0 len) byte_map).

    Definition sigT_of_prod {A B : Type} (p : A * B) : {_ : A & B} :=
      let (a, b) := p in existT (fun _ : A => B) a b.

    Definition uvalue_measure_rel (uv1 uv2 : uvalue) : Prop :=
      (uvalue_measure uv1 < uvalue_measure uv2)%nat.

    Lemma wf_uvalue_measure_rel :
      @well_founded uvalue uvalue_measure_rel.
    Proof.
      unfold uvalue_measure_rel.
      apply wf_inverse_image.
      apply Wf_nat.lt_wf.
    Defined.

    Definition lt_uvalue_dtyp (uvdt1 uvdt2 : (uvalue * dtyp)) : Prop :=
      lexprod uvalue (fun uv => dtyp) uvalue_measure_rel (fun uv dt1f dt2f => dtyp_measure dt1f < dtyp_measure dt2f)%nat (sigT_of_prod uvdt1) (sigT_of_prod uvdt2).

    Lemma wf_lt_uvalue_dtyp : well_founded lt_uvalue_dtyp.
    Proof.
      unfold lt_uvalue_dtyp.
      apply wf_inverse_image.
      apply wf_lexprod.
      - unfold well_founded; intros a.
        apply wf_uvalue_measure_rel.
      - intros uv.
        apply wf_inverse_image.
        apply Wf_nat.lt_wf.
    Defined.

    Definition lex_nats (ns1 ns2 : (nat * nat)) : Prop :=
      lexprod nat (fun n => nat) lt (fun _ => lt) (sigT_of_prod ns1) (sigT_of_prod ns2).

    Lemma well_founded_lex_nats :
      well_founded lex_nats.
    Proof.
      unfold lex_nats.
      apply wf_inverse_image.
      apply wf_lexprod; intros;
        apply Wf_nat.lt_wf.
    Qed.

    (* This is mostly to_ubytes, except it will also unwrap concatbytes *)
    Obligation Tactic := try Tactics.program_simpl; try solve [solve_uvalue_dtyp_measure
                                                              | intuition;
                                                               match goal with
                                                               | H: _ |- _ =>
                                                                   try solve [inversion H]
                                                               end
                                                    ].


    Fixpoint serialize_by_dtyp {M} `{Monad M} `{MonadStoreId M} `{RAISE_ERROR M} `{RAISE_OOM M}
      (CTR : dtyp -> uvalue)  (dt : dtyp) {struct dt} : M (list SByte) :=
      match dt with
      | DTYPE_Struct ts =>
          l <- map_monad (serialize_by_dtyp CTR) ts ;;
          ret (concat l)

      | DTYPE_Packed_struct (ts) =>
          l <- map_monad (serialize_by_dtyp CTR) ts ;;
          ret (concat l)

      | DTYPE_Array sz t =>
          bs <- serialize_by_dtyp CTR t ;;
          ret (concat (repeatN sz bs))

      | DTYPE_Vector sz t =>
          bs <- serialize_by_dtyp CTR t ;;
          ret (concat (repeatN sz bs))

      | _ =>
          sid <- fresh_sid;;
          ret (to_ubytes (CTR dt) dt sid)
      end.

    Definition serialize_sbytes {M} `{Monad M} `{MonadStoreId M}
      (uv : uvalue) (dt : dtyp) : M (list SByte)
      := sid <- fresh_sid;;
         ret (to_ubytes uv dt sid).
      (* match uv with *)
      (* (* Base types *) *)
      (* | UVALUE_Addr _ *)
      (* | UVALUE_I1 _ *)
      (* | UVALUE_I8 _ *)
      (* | UVALUE_I32 _ *)
      (* | UVALUE_I64 _ *)
      (* | UVALUE_IPTR _ *)
      (* | UVALUE_Float _ *)
      (* | UVALUE_Double _ *)

      (* (* Expressions *) *)
      (* | UVALUE_IBinop _ _ _ *)
      (* | UVALUE_ICmp _ _ _ *)
      (* | UVALUE_FBinop _ _ _ _ *)
      (* | UVALUE_FCmp _ _ _ *)
      (* | UVALUE_Conversion _ _ _ _ *)
      (* | UVALUE_GetElementPtr _ _ _ *)
      (* | UVALUE_ExtractElement _ _ _ *)
      (* | UVALUE_InsertElement _ _ _ _ *)
      (* | UVALUE_ShuffleVector _ _ _ _ *)
      (* | UVALUE_ExtractValue _ _ _ *)
      (* | UVALUE_InsertValue _ _ _ _ _ *)
      (* | UVALUE_Select _ _ _ => *)
      (*     sid <- fresh_sid;; *)
      (*     ret (to_ubytes uv dt sid) *)

      (* | UVALUE_Undef _ => serialize_by_dtyp UVALUE_Undef dt *)
      (* | UVALUE_Poison _ => serialize_by_dtyp UVALUE_Poison dt *)
      (* | UVALUE_Oom _ => serialize_by_dtyp UVALUE_Oom dt *)
      (* | UVALUE_Struct fields => *)
      (*     match dt with *)
      (*     | DTYPE_Struct ts => *)
      (*         l <- map_monad2 serialize_sbytes fields ts ;; *)
      (*         ret (concat l) *)
      (*     | _ => *)
      (*         raise_error "serialize_sbytes: UVALUE_Struct field / type mismatch." *)
      (*     end *)
      (* | UVALUE_Packed_struct fields => *)
      (*     match dt with *)
      (*     | DTYPE_Packed_struct ts => *)
      (*         l <- map_monad2 serialize_sbytes fields ts ;; *)
      (*         ret (concat l) *)
      (*     | _ => *)
      (*         raise_error "serialize_sbytes: UVALUE_Packed_struct field / type mismatch." *)
      (*     end *)

      (* | UVALUE_Array elts => *)
      (*     match dt with *)
      (*     | DTYPE_Array _ t => *)
      (*         l <- map_monad (fun elt => serialize_sbytes elt t) elts;; *)
      (*         ret (concat l) *)
      (*     | _ => *)
      (*         raise_error "serialize_sbytes: UVALUE_Array with incorrect type." *)
      (*     end *)

      (* | UVALUE_Vector elts => *)
      (*     match dt with *)
      (*     | DTYPE_Vector _ t => *)
      (*         l <- map_monad (fun elt => serialize_sbytes elt t) elts;; *)
      (*         ret (concat l) *)
      (*     | _ => *)
      (*         raise_error "serialize_sbytes: UVALUE_Vector with incorrect type." *)
      (*     end *)

      (* | UVALUE_None => ret nil *)

      (* | UVALUE_ExtractByte uv dt' idx sid => *)
      (*     raise_error "serialize_sbytes: UVALUE_ExtractByte not guarded by UVALUE_ConcatBytes." *)

      (* | UVALUE_ConcatBytes bytes t => *)
      (*     bytes' <- lift_ERR_RAISE_ERROR (map_monad extract_byte_to_sbyte bytes);; *)
      (*     re_sid_ubytes bytes' *)
      (* end. *)


  (* deserialize_sbytes takes a list of SBytes and turns them into a uvalue. *)

  (*    This relies on the similar, but different, from_ubytes function *)
  (*    which given a set of bytes checks if all of the bytes are from *)
  (*    the same uvalue, and if so returns the original uvalue, and *)
  (*    otherwise returns a UVALUE_ConcatBytes value instead. *)

  (*    The reason we also have deserialize_sbytes is in order to deal *)
  (*    with aggregate data types. *)
    Definition from_ubytes_extra :=
      fun (bytes : list SByte) (dt : dtyp) =>
        match split_n (N.to_nat (sizeof_dtyp dt)) bytes with
        | inr (bs1, bs2) =>
            (match all_bytes_from_uvalue dt bs1 with
             | Some uv => uv
             | None => UVALUE_ConcatBytes (map sbyte_to_extractbyte bytes) dt
             end, bs2)
        | inl _ =>
            (UVALUE_ConcatBytes (map sbyte_to_extractbyte bytes) dt, [])
        end.

    Lemma from_ubytes_extra_from_ubytes :
      forall bs dt uv,
        from_ubytes_extra bs dt = (uv, []) ->
          from_ubytes bs dt = uv.
    Proof.
      unfold from_ubytes_extra.
      unfold from_ubytes.
      intros.
      break_inner_match_goal.
        + break_match_hyp.
          * assert (exists s, split_n (N.to_nat (sizeof_dtyp dt)) bs = inl s) by (eexists; eauto).
            apply split_n_err in H0.
            apply Neqb_ok in Heqb.
            lia.
          * destruct p.
            apply split_n_correct in Heqs.
            destruct Heqs as [_ EQ].
            inversion H.
            subst.
            rewrite app_nil_r.
            reflexivity.
        + break_match_hyp.
          * inversion H.
            reflexivity.
          * destruct p.
            inversion H.
            subst.
            apply split_n_correct in Heqs.
            destruct Heqs as [EQ1 EQ2].
            rewrite app_nil_r in EQ2. subst.
            rewrite EQ1 in Heqb.
            rewrite Nnat.N2Nat.id in Heqb.
            rewrite N.eqb_refl in Heqb.
            inversion Heqb.
    Qed.

    (* Tries to deserialize a list of SBytes into a uvalue.
       - if [length bytes = size_of dt] then this always succeeds

       - if [length bytes < size_of dt] then
             + if [dt] is an aggregate type, it will fail
             + if [dt] is not aggregate, return a UVALUE_ConcatBytes with too few bytes

       - if [length bytes > size_of dt] then
            this operation succeeds, but:
            + if [dt] is an aggregate type, the extra bytes are discarded
            + if [dt] is not aggregate, return a UVALUE_ConcatBytes with too many bytes
     *)

    Definition deserialize_sbytes (bytes : list SByte) (dt : dtyp) : err uvalue :=
      match dt with
      | DTYPE_Void =>
          raise "deserialize_sbytes: Attempt to deserialize void."%string
      | _ => ret (from_ubytes bytes dt)
      end.

      (* let dsb_list : list SByte -> list dtyp -> err (list uvalue * list SByte) := *)
      (*   fix go (bytes : list SByte) (fields : list dtyp) : err (list uvalue * list SByte) :=  *)
      (*     match fields with *)
      (*     | [] => ret ([], bytes) *)
      (*     | t::ts =>  *)
      (*         '(bs1, bs2) <- split_n (N.to_nat (sizeof_dtyp t)) bytes ;; *)
      (*         u <- deserialize_sbytes bs1 t ;; *)
      (*         '(us, rest) <- go bs2 ts ;; *)
      (*         ret (u::us, rest) *)
      (*     end *)
      (* in *)
      (* let dsb_loop (dt:dtyp) : nat  -> list SByte -> err (list uvalue * list SByte) := *)
      (*   fix go n bytes := *)
      (*     match n with *)
      (*     | 0 => ret ([], bytes) *)
      (*     | S n => *)
      (*         '(bs1, bs2) <- split_n (N.to_nat (sizeof_dtyp dt)) bytes ;; *)
      (*         u <- deserialize_sbytes bs1 dt ;; *)
      (*         '(us, rest) <- go n bs2;; *)
      (*         ret (u::us, rest) *)
      (*     end  *)
      (* in  *)
      (* match dt with *)
      (* (* Base types *) *)
      (* | DTYPE_I _ *)
      (* | DTYPE_IPTR *)
      (* | DTYPE_Pointer *)
      (* | DTYPE_Half *)
      (* | DTYPE_Float *)
      (* | DTYPE_Double *)
      (* | DTYPE_X86_fp80 *)
      (* | DTYPE_Fp128 *)
      (* | DTYPE_Ppc_fp128 *)
      (* | DTYPE_X86_mmx *)
      (* | DTYPE_Opaque *)
      (* | DTYPE_Metadata => *)
      (*     ret (from_ubytes bytes dt) *)

      (* | DTYPE_Void => *)
      (*     raise "deserialize_sbytes: Attempt to deserialize void."%string *)

      (* | DTYPE_Struct fields => *)
      (*     '(uvs, _) <- dsb_list bytes fields ;; *)
      (*     ret (UVALUE_Struct uvs) *)

      (* | DTYPE_Packed_struct fields => *)
      (*     '(uvs, _) <- dsb_list bytes fields ;; *)
      (*     ret (UVALUE_Packed_struct uvs) *)

      (* | DTYPE_Array sz t => *)
      (*     '(uvs, _) <- dsb_loop t (N.to_nat sz) bytes ;; *)
      (*     ret (UVALUE_Array uvs) *)

      (* | DTYPE_Vector sz t => *)
      (*     '(uvs, _) <- dsb_loop t (N.to_nat sz) bytes ;; *)
      (*     ret (UVALUE_Vector uvs) *)
      (* end. *)


    (* Serialize a uvalue into bytes and combine them into UVALUE_ConcatBytes. Useful for bitcasts.

       dt should be the type of the thing you are casting to in the case of bitcasts.
     *)
    Definition uvalue_to_concatbytes
               {M} `{Monad M} `{MonadStoreId M} `{RAISE_ERROR M} `{RAISE_OOM M}
               (uv : uvalue) (dt : dtyp) : M uvalue :=
      bytes <- serialize_sbytes uv dt;;
      ret (UVALUE_ConcatBytes (map sbyte_to_extractbyte bytes) dt).

  (* (* TODO: *) *)

  (*  (*   What is the difference between a pointer and an integer...? *) *)

  (*  (*   Primarily, it's that pointers have provenance and integers don't? *) *)

  (*  (*   So, if we do PVI is there really any difference between an address *) *)
  (*  (*   and an integer, and should we actually distinguish between them? *) *)

  (*  (*   Provenance in UVALUE_IPTR probably means we need provenance in *all* *) *)
  (*  (*   data types... i1, i8, i32, etc, and even doubles and floats... *) *)
  (*  (*  *) *)

  (* (* TODO: *) *)

  (*  (*    Should uvalue have something like... UVALUE_ExtractByte which *) *)
  (*  (*    extracts a certain byte out of a uvalue? *) *)

  (*  (*    Will probably need an equivalence relation on UVALUEs, likely won't *) *)
  (*  (*    end up with a round-trip property with regular equality... *) *)
  (*  (* *) *)

  End Serialization.
End MemoryHelpers.

Module Type MemoryModelSpec (LP : LLVMParams) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP).
  Import LP.
  Import LP.Events.
  Import LP.ADDR.
  Import LP.SIZEOF.
  Import LP.PROV.
  Import LP.PTOI.
  Import MMSP.

  Module OVER := PTOIOverlaps ADDR PTOI SIZEOF.
  Import OVER.
  Module OVER_H := OverlapHelpers ADDR SIZEOF OVER.
  Import OVER_H.

  Import MemByte.

  Module MemHelpers := MemoryHelpers LP MP MemByte.
  Import MemHelpers.

  Definition read_byte_prop (ms : MemState) (ptr : addr) (byte : SByte) : Prop
    := read_byte_prop_memory ptr (MemState_get_memory ms) byte.

  Definition byte_allocated (ms : MemState) (ptr : addr) (aid : AllocationId) : Prop
    := addr_allocated_prop_memory ptr aid (MemState_get_memory ms).

  Definition byte_not_allocated (ms : MemState) (ptr : addr) : Prop
    := forall (aid : AllocationId), ~ byte_allocated ms ptr aid.

  (** Addresses *)
  Definition disjoint_ptr_byte (a b : addr) :=
    ptr_to_int a <> ptr_to_int b.

  #[global] Instance disjoint_ptr_byte_Symmetric : Symmetric disjoint_ptr_byte.
  Proof.
    unfold Symmetric.
    intros x y H.
    unfold disjoint_ptr_byte; auto.
  Qed.

  (** Utilities *)
  Definition lift_spec_to_MemPropT {A}
             (succeeds_spec : MemState -> A -> MemState -> Prop) (ub_spec : MemState -> Prop) :
    MemPropT MemState A :=
    fun m1 res =>
      match run_err_ub_oom res with
      | inl (OOM_message x) =>
          True
      | inr (inl (UB_message x)) =>
          ub_spec m1
      | inr (inr (inl (ERR_message x))) =>
          False
      | inr (inr (inr (m2, res))) =>
          succeeds_spec m1 res m2
      end.

  (*** Predicates *)

  (** Reads *)
  Definition read_byte_allowed (ms : MemState) (ptr : addr) : Prop :=
    exists aid, byte_allocated ms ptr aid /\ access_allowed (address_provenance ptr) aid = true.

  Definition read_byte_allowed_all_preserved (m1 m2 : MemState) : Prop :=
    forall ptr,
      read_byte_allowed m1 ptr <-> read_byte_allowed m2 ptr.

  Definition read_byte_prop_all_preserved (m1 m2 : MemState) : Prop :=
    forall ptr byte,
      read_byte_prop m1 ptr byte <-> read_byte_prop m2 ptr byte.

  Definition read_byte_preserved (m1 m2 : MemState) : Prop :=
    read_byte_allowed_all_preserved m1 m2 /\ read_byte_prop_all_preserved m1 m2.

  (** Writes *)
  Definition write_byte_allowed (ms : MemState) (ptr : addr) : Prop :=
    exists aid, byte_allocated ms ptr aid /\ access_allowed (address_provenance ptr) aid = true.

  Definition write_byte_allowed_all_preserved (m1 m2 : MemState) : Prop :=
    forall ptr,
      write_byte_allowed m1 ptr <-> write_byte_allowed m2 ptr.

  (** Freeing *)
  Definition free_byte_allowed (ms : MemState) (ptr : addr) : Prop :=
    exists aid, byte_allocated ms ptr aid /\ access_allowed (address_provenance ptr) aid = true.

  Definition free_byte_allowed_all_preserved (m1 m2 : MemState) : Prop :=
    forall ptr,
      free_byte_allowed m1 ptr <-> free_byte_allowed m2 ptr.

  (** Allocations *)
  Definition allocations_preserved (m1 m2 : MemState) : Prop :=
    forall ptr aid, byte_allocated m1 ptr aid <-> byte_allocated m2 ptr aid.

  (** Provenances / allocation ids *)
  Definition extend_provenance (ms : MemState) (new_pr : Provenance) (ms' : MemState) : Prop
    := (forall pr, used_provenance_prop ms pr -> used_provenance_prop ms' pr) /\
         ~ used_provenance_prop ms new_pr /\
         used_provenance_prop ms' new_pr.

  Definition preserve_allocation_ids (ms ms' : MemState) : Prop
    := forall p, used_provenance_prop ms p <-> used_provenance_prop ms' p.

  (** Store ids *)
  Definition used_store_id_prop (ms : MemState) (sid : store_id) : Prop
    := exists ptr byte, read_byte_prop ms ptr byte /\ sbyte_sid byte = inr sid.

  Definition fresh_store_id (ms : MemState) (new_sid : store_id) : Prop
    := ~ used_store_id_prop ms new_sid.

  (** Frame stack *)
  Definition frame_stack_preserved_memory (m1 m2 : memory_stack) : Prop
    := forall fs,
      memory_stack_frame_stack_prop m1 fs <-> memory_stack_frame_stack_prop m2 fs.

  Definition frame_stack_preserved (m1 m2 : MemState) : Prop
    := frame_stack_preserved_memory (MemState_get_memory m1) (MemState_get_memory m2).

  (* Definition Heap_in_bounds (ms_fin:FinMem.MMEP.MMSP.MemState) : Prop := *)
  (*   let h := Memory64BitIntptr.MMEP.MMSP.mem_state_heap ms_fin in *)
  (*   forall i, is_true (IntMaps.member i h) -> exists ptr, FinPTOI.ptr_to_int ptr = i. *)

  (** Heap *)
  (* SAZ: Add Heap_in_bounds *)
  Definition heap_preserved_memory (m1 m2 : memory_stack) : Prop
    := forall h,
        memory_stack_heap_prop m1 h <-> memory_stack_heap_prop m2 h.

  Definition heap_preserved (m1 m2 : MemState) : Prop
    := heap_preserved_memory (MemState_get_memory m1) (MemState_get_memory m2).

  Definition addr_allocated_prop_memory_preserved (m1 m2 : memory_stack) : Prop
    := forall addr aid,
      addr_allocated_prop_memory addr aid m1 <-> addr_allocated_prop_memory addr aid m2.

  Definition read_byte_prop_memory_preserved (m1 m2 : memory_stack) : Prop
    := forall ptr byte,
      read_byte_prop_memory ptr m1 byte <-> read_byte_prop_memory ptr m2 byte.

  Record memory_stack_eqv (m1 m2 : memory_stack) : Prop :=
    { memory_stack_eqv_preserves_addr_allocated : addr_allocated_prop_memory_preserved m1 m2;
      memory_stack_eqv_preserves_read_byte_MemPropT : read_byte_prop_memory_preserved m1 m2;
      memory_stack_eqv_frame_stack_preserved_memory : frame_stack_preserved_memory m1 m2;
      memory_stack_eqv_heap_preserved_memory : heap_preserved_memory m1 m2;
    }.

  Definition MemState_eqv' (ms1 ms2 : MemState) : Prop :=
    memory_stack_eqv (MemState_get_memory ms1) (MemState_get_memory ms2) /\
      preserve_allocation_ids ms1 ms2.

  Definition MemState_eqv (ms1 ms2 : MemState) : Prop :=
    preserve_allocation_ids ms1 ms2 /\
      read_byte_preserved ms1 ms2 /\
      write_byte_allowed_all_preserved ms1 ms2 /\
      free_byte_allowed_all_preserved ms1 ms2 /\
      allocations_preserved ms1 ms2 /\
      frame_stack_preserved ms1 ms2 /\
      heap_preserved ms1 ms2.

  Lemma MemState_eqv'_read_byte_allowed_all_preserved :
    forall ms1 ms2,
      memory_stack_eqv (MemState_get_memory ms1) (MemState_get_memory ms2) ->
      read_byte_allowed_all_preserved ms1 ms2.
  Proof.
    intros ms1 ms2 H.
    destruct H.
    red.
    intros ptr.
    split; intros RBA;
      red; red in RBA;
      destruct RBA as (aid&ALLOC&ACCESS).
    - exists aid.
      split; auto.
      red; red in ALLOC.
      apply memory_stack_eqv_preserves_addr_allocated0; auto.
    - exists aid.
      split; auto.
      red; red in ALLOC.
      apply memory_stack_eqv_preserves_addr_allocated0; auto.
  Qed.

  #[global] Hint Resolve MemState_eqv'_read_byte_allowed_all_preserved : MemEqv.

  Lemma MemState_eqv'_read_byte_prop_all_preserved :
    forall ms1 ms2,
      memory_stack_eqv (MemState_get_memory ms1) (MemState_get_memory ms2) ->
      read_byte_prop_all_preserved ms1 ms2.
  Proof.
    intros ms1 ms2 H.
    destruct H.
    red.
    intros ptr byte.
    split; intros RBP;
      red; red in RBP.
    - red in memory_stack_eqv_preserves_read_byte_MemPropT0.
      eapply memory_stack_eqv_preserves_read_byte_MemPropT0; eauto.
    - red in memory_stack_eqv_preserves_read_byte_MemPropT0.
      eapply memory_stack_eqv_preserves_read_byte_MemPropT0; eauto.
  Qed.

  #[global] Hint Resolve MemState_eqv'_read_byte_prop_all_preserved : MemEqv.

  Lemma MemState_eqv'_read_byte_preserved :
    forall ms1 ms2,
      memory_stack_eqv (MemState_get_memory ms1) (MemState_get_memory ms2) ->
      read_byte_preserved ms1 ms2.
  Proof.
    intros ms1 ms2 H.
    red.
    split; eauto with MemEqv.
  Qed.

  #[global] Hint Resolve MemState_eqv'_read_byte_preserved : MemEqv.

  Lemma MemState_eqv'_write_byte_allowed_all_preserved :
    forall ms1 ms2,
      memory_stack_eqv (MemState_get_memory ms1) (MemState_get_memory ms2) ->
      write_byte_allowed_all_preserved ms1 ms2.
  Proof.
    intros ms1 ms2 H.
    eapply MemState_eqv'_read_byte_allowed_all_preserved; eauto.
  Qed.

  #[global] Hint Resolve MemState_eqv'_write_byte_allowed_all_preserved : MemEqv.

  Lemma MemState_eqv'_free_byte_allowed_all_preserved :
    forall ms1 ms2,
      memory_stack_eqv (MemState_get_memory ms1) (MemState_get_memory ms2) ->
      free_byte_allowed_all_preserved ms1 ms2.
  Proof.
    intros ms1 ms2 H.
    eapply MemState_eqv'_read_byte_allowed_all_preserved; eauto.
  Qed.

  #[global] Hint Resolve MemState_eqv'_free_byte_allowed_all_preserved : MemEqv.

  Lemma MemState_eqv'_allocations_preserved :
    forall ms1 ms2,
      memory_stack_eqv (MemState_get_memory ms1) (MemState_get_memory ms2) ->
      allocations_preserved ms1 ms2.
  Proof.
    intros ms1 ms2 H.
    destruct H.
    red.
    intros ptr aid.
    split; intros ALLOC;
      repeat red in ALLOC;
      repeat red;
      eapply memory_stack_eqv_preserves_addr_allocated0; eauto.
  Qed.

  #[global] Hint Resolve MemState_eqv'_allocations_preserved : MemEqv.

  Lemma MemState_eqv'_frame_stack_preserved :
    forall ms1 ms2,
      memory_stack_eqv (MemState_get_memory ms1) (MemState_get_memory ms2) ->
      frame_stack_preserved ms1 ms2.
  Proof.
    intros ms1 ms2 H.
    destruct H.
    red; eauto.
  Qed.

  #[global] Hint Resolve MemState_eqv'_frame_stack_preserved : MemEqv.

  Lemma MemState_eqv'_heap_preserved :
    forall ms1 ms2,
      memory_stack_eqv (MemState_get_memory ms1) (MemState_get_memory ms2) ->
      heap_preserved ms1 ms2.
  Proof.
    intros ms1 ms2 H.
    destruct H.
    red; eauto.
  Qed.

  #[global] Hint Resolve MemState_eqv'_heap_preserved : MemEqv.

  Lemma MemState_eqv'_MemState_eqv :
    forall ms1 ms2,
      MemState_eqv' ms1 ms2 ->
      MemState_eqv ms1 ms2.
  Proof.
    intros ms1 ms2 EQV.
    destruct EQV.
    split; [|split; [|split; [|split; [|split; [|split]]]]]; eauto with MemEqv.
  Qed.

  (*** Provenance operations *)
  #[global] Instance MemPropT_MonadProvenance : MonadProvenance Provenance (MemPropT MemState).
  Proof.
    (* Need to be careful with allocation ids / provenances (more so than store ids)

       They can never be reused. E.g., if you have a pointer `p` with
       allocation id `aid`, and that block is freed, you can't reuse
       `aid` without causing problems. If you allocate a new block
       with `aid` again, then `p` may still be around and may be able
       to access the block.

       Therefore the MemState has to have some idea of what allocation
       ids have been used in the past, not just the allocation ids
       that are *currently* in use.
    *)
    split.
    - (* fresh_provenance *)
      unfold MemPropT.
      intros ms [[[[[[[oom_res] | [[ub_res] | [[err_res] | [ms' new_pr]]]]]]]]].
      + exact True.
      + exact False.
      + exact False.
      + exact
          ( extend_provenance ms new_pr ms' /\
              read_byte_preserved ms ms' /\
              write_byte_allowed_all_preserved ms ms' /\
              free_byte_allowed_all_preserved ms ms' /\
              allocations_preserved ms ms' /\
              frame_stack_preserved ms ms' /\
              heap_preserved ms ms'
          ).
  Defined.

  (*** Store id operations *)
  #[global] Instance MemPropT_MonadStoreID : MonadStoreId (MemPropT MemState).
  Proof.
    split.
    - (* fresh_sid *)
      unfold MemPropT.
      intros ms [[[[[[[oom_res] | [[ub_res] | [[err_res] | [ms' new_sid]]]]]]]]].
      + exact True.
      + exact False.
      + exact False.
      + exact
          ( fresh_store_id ms' new_sid /\
              preserve_allocation_ids ms ms' /\
              read_byte_preserved ms ms' /\
              write_byte_allowed_all_preserved ms ms' /\
              free_byte_allowed_all_preserved ms ms' /\
              allocations_preserved ms ms' /\
              frame_stack_preserved ms ms' /\
              heap_preserved ms ms'
          ).
  Defined.

  (*** Reading from memory *)
  Record read_byte_spec (ms : MemState) (ptr : addr) (byte : SByte) : Prop :=
    { read_byte_allowed_spec : read_byte_allowed ms ptr;
      read_byte_value : read_byte_prop ms ptr byte;
    }.

  Definition read_byte_spec_MemPropT (ptr : addr) : MemPropT MemState SByte :=
    lift_spec_to_MemPropT
      (fun m1 byte m2 =>
         m1 = m2 /\ read_byte_spec m1 ptr byte)
      (fun m1 => ~ read_byte_allowed m1 ptr).

  (*** Framestack operations *)
  Definition empty_frame (f : Frame) : Prop :=
    forall ptr, ~ ptr_in_frame_prop f ptr.

  Record add_ptr_to_frame (f1 : Frame) (ptr : addr) (f2 : Frame) : Prop :=
    {
      old_frame_lu : forall ptr', disjoint_ptr_byte ptr ptr' ->
                             ptr_in_frame_prop f1 ptr' <-> ptr_in_frame_prop f2 ptr';
      new_frame_lu : ptr_in_frame_prop f2 ptr;
    }.

  Record empty_frame_stack (fs : FrameStack) : Prop :=
    {
      no_pop : (forall f, ~ pop_frame_stack_prop fs f);
      empty_fs_empty_frame : forall f, peek_frame_stack_prop fs f -> empty_frame f;
    }.

  Record push_frame_stack_spec (fs1 : FrameStack) (f : Frame) (fs2 : FrameStack) : Prop :=
    {
      can_pop : pop_frame_stack_prop fs2 fs1;
      new_frame : peek_frame_stack_prop fs2 f;
    }.

  Definition ptr_in_current_frame (ms : MemState) (ptr : addr) : Prop
    := forall fs, memory_stack_frame_stack_prop (MemState_get_memory ms) fs ->
             forall f, peek_frame_stack_prop fs f ->
                  ptr_in_frame_prop f ptr.

  (** mempush *)
  Record mempush_operation_invariants (m1 : MemState) (m2 : MemState) :=
    {
      mempush_op_reads : read_byte_preserved m1 m2;
      mempush_op_write_allowed : write_byte_allowed_all_preserved m1 m2;
      mempush_op_free_allowed : free_byte_allowed_all_preserved m1 m2;
      mempush_op_allocations : allocations_preserved m1 m2;
      mempush_op_allocation_ids : preserve_allocation_ids m1 m2;
      mempush_heap_preserved : heap_preserved m1 m2;
    }.

  Record mempush_spec (m1 : MemState) (m2 : MemState) : Prop :=
    {
      fresh_frame :
      forall fs1 fs2 f,
        memory_stack_frame_stack_prop (MemState_get_memory m1) fs1 ->
        empty_frame f ->
        push_frame_stack_spec fs1 f fs2 ->
        memory_stack_frame_stack_prop (MemState_get_memory m2) fs2;

      mempush_invariants :
      mempush_operation_invariants m1 m2;
    }.

  Definition mempush_spec_MemPropT : MemPropT MemState unit :=
    lift_spec_to_MemPropT
      (fun m1 _ m2 =>
         mempush_spec m1 m2)
      (fun m1 => False).

  (** mempop *)
  Record mempop_operation_invariants (m1 : MemState) (m2 : MemState) :=
    {
      mempop_op_allocation_ids : preserve_allocation_ids m1 m2;
      mempop_heap_preserved : heap_preserved m1 m2;
    }.

  Record mempop_spec (m1 : MemState) (m2 : MemState) : Prop :=
    {
      (* all bytes in popped frame are freed. *)
      bytes_freed :
      forall ptr,
        ptr_in_current_frame m1 ptr ->
        byte_not_allocated m2 ptr;

      (* Bytes not allocated in the popped frame have the same allocation status as before *)
      non_frame_bytes_preserved :
      forall ptr aid,
        (~ ptr_in_current_frame m1 ptr) ->
        byte_allocated m1 ptr aid <-> byte_allocated m2 ptr aid;

      (* Bytes not allocated in the popped frame are the same when read *)
      non_frame_bytes_read :
      forall ptr byte,
        (~ ptr_in_current_frame m1 ptr) ->
        read_byte_spec m1 ptr byte <-> read_byte_spec m2 ptr byte;

      (* Set new framestack *)
      pop_frame :
      forall fs1 fs2,
        memory_stack_frame_stack_prop (MemState_get_memory m1) fs1 ->
        pop_frame_stack_prop fs1 fs2 ->
        memory_stack_frame_stack_prop (MemState_get_memory m2) fs2;

      (* Invariants *)
      mempop_invariants : mempop_operation_invariants m1 m2;
    }.

  Definition cannot_pop (ms : MemState) :=
    forall fs1 fs2,
      memory_stack_frame_stack_prop (MemState_get_memory ms) fs1 ->
      ~ pop_frame_stack_prop fs1 fs2.

  Definition mempop_spec_MemPropT : MemPropT MemState unit :=
    fun m1 res =>
      match run_err_ub_oom res with
      | inl (OOM_message x) =>
          True
      | inr (inl (UB_message x)) =>
          False
      | inr (inr (inl (ERR_message x))) =>
          (* Not being able to pop is an error, shouldn't happen *)
          cannot_pop m1
      | inr (inr (inr (m2, res))) =>
          mempop_spec m1 m2
      end.

  (* Add a pointer onto the current frame in the frame stack *)
  Definition add_ptr_to_frame_stack (fs1 : FrameStack) (ptr : addr) (fs2 : FrameStack) : Prop :=
    forall f,
      peek_frame_stack_prop fs1 f ->
      exists f', add_ptr_to_frame f ptr f' /\
              peek_frame_stack_prop fs2 f' /\
              (forall fs1_pop, pop_frame_stack_prop fs1 fs1_pop <-> pop_frame_stack_prop fs2 fs1_pop).

  Fixpoint add_ptrs_to_frame_stack (fs1 : FrameStack) (ptrs : list addr) (fs2 : FrameStack) : Prop :=
    match ptrs with
    | nil => frame_stack_eqv fs1 fs2
    | (ptr :: ptrs) =>
        exists fs',
          add_ptrs_to_frame_stack fs1 ptrs fs' /\
            add_ptr_to_frame_stack fs' ptr fs2
    end.

  Lemma add_ptrs_to_frame_stack_equation (fs1 : FrameStack) (ptrs : list addr) (fs2 : FrameStack) :
    add_ptrs_to_frame_stack fs1 ptrs fs2 =
      match ptrs with
      | nil => frame_stack_eqv fs1 fs2
      | (ptr :: ptrs) =>
          exists fs',
          add_ptrs_to_frame_stack fs1 ptrs fs' /\
            add_ptr_to_frame_stack fs' ptr fs2
      end.
  Proof.
    induction ptrs; cbn; auto.
  Qed.

  (*** Heap operations *)
  Record empty_heap (h : Heap) : Prop :=
    {
      empty_heap_no_roots : forall root,
        ~ root_in_heap_prop h root;

      empty_heap_no_ptrs : forall root ptr,
        ~ ptr_in_heap_prop h root ptr;
    }.

  Definition root_in_memstate_heap (ms : MemState) (root : addr) : Prop
    := forall h, memory_stack_heap_prop (MemState_get_memory ms) h ->
            root_in_heap_prop h root.

  Definition ptr_in_memstate_heap (ms : MemState) (root : addr) (ptr : addr) : Prop
    := forall h, memory_stack_heap_prop (MemState_get_memory ms) h ->
            ptr_in_heap_prop h root ptr.

  Record add_ptr_to_heap (h1 : Heap) (root : addr) (ptr : addr) (h2 : Heap) : Prop :=
    {
      old_heap_lu : forall ptr',
        disjoint_ptr_byte ptr ptr' ->
        ptr_in_heap_prop h1 root ptr' <-> ptr_in_heap_prop h2 root ptr';

      old_heap_lu_different_root : forall root',
        disjoint_ptr_byte root root' ->
        forall ptr', ptr_in_heap_prop h1 root' ptr' <-> ptr_in_heap_prop h2 root' ptr';

      old_heap_roots : forall root',
        disjoint_ptr_byte root root' ->
        root_in_heap_prop h1 root' <-> root_in_heap_prop h2 root';

      new_heap_lu :
      ptr_in_heap_prop h2 root ptr;

      new_heap_root :
      root_in_heap_prop h2 root;
    }.

  Fixpoint add_ptrs_to_heap' (h1 : Heap) (root : addr) (ptrs : list addr) (h2 : Heap) : Prop :=
    match ptrs with
    | nil => heap_eqv h1 h2
    | (ptr :: ptrs) =>
        exists h',
        add_ptrs_to_heap' h1 root ptrs h' /\
          add_ptr_to_heap h' root ptr h2
    end.

  Definition add_ptrs_to_heap (h1 : Heap) (ptrs : list addr) (h2 : Heap) : Prop :=
    match ptrs with
    | nil => heap_eqv h1 h2
    | (ptr :: _) =>
        add_ptrs_to_heap' h1 ptr ptrs h2
    end.

  (*** Writing to memory *)
  Record set_byte_memory (m1 : MemState) (ptr : addr) (byte : SByte) (m2 : MemState) : Prop :=
    {
      new_lu : read_byte_spec m2 ptr byte;
      old_lu : forall ptr',
        disjoint_ptr_byte ptr ptr' ->
        (forall byte', read_byte_spec m1 ptr' byte' <-> read_byte_spec m2 ptr' byte');
    }.

  Record write_byte_operation_invariants (m1 m2 : MemState) : Prop :=
    {
      write_byte_op_preserves_allocations : allocations_preserved m1 m2;
      write_byte_op_preserves_frame_stack : frame_stack_preserved m1 m2;
      write_byte_op_preserves_heap : heap_preserved m1 m2;
      write_byte_op_read_allowed : read_byte_allowed_all_preserved m1 m2;
      write_byte_op_write_allowed : write_byte_allowed_all_preserved m1 m2;
      write_byte_op_free_allowed : free_byte_allowed_all_preserved m1 m2;
      write_byte_op_allocation_ids : preserve_allocation_ids m1 m2;
    }.

  Record write_byte_spec (m1 : MemState) (ptr : addr) (byte : SByte) (m2 : MemState) : Prop :=
    {
      byte_write_succeeds : write_byte_allowed m1 ptr;
      byte_written : set_byte_memory m1 ptr byte m2;

      write_byte_invariants : write_byte_operation_invariants m1 m2;
    }.

  Definition write_byte_spec_MemPropT (ptr : addr) (byte : SByte) : MemPropT MemState unit
    :=
    lift_spec_to_MemPropT
      (fun m1 _ m2 =>
         write_byte_spec m1 ptr byte m2)
      (fun m1 => ~ write_byte_allowed m1 ptr).

  (*** Allocation utilities *)
  Record block_is_free (m1 : MemState) (len : nat) (pr : Provenance) (ptr : addr) (ptrs : list addr) : Prop :=
    { block_is_free_consecutive : ret ptrs {{m1}} ∈ {{m1}} get_consecutive_ptrs ptr len;
      block_is_free_ptr_provenance : address_provenance ptr = allocation_id_to_prov (provenance_to_allocation_id pr); (* Need this case if `ptrs` is empty (allocating 0 bytes) *)
      block_is_free_ptrs_provenance : forall ptr, In ptr ptrs -> address_provenance ptr = allocation_id_to_prov (provenance_to_allocation_id pr);

      (* Actual free condition *)
      block_is_free_bytes_are_free : forall ptr, In ptr ptrs -> byte_not_allocated m1 ptr;
    }.

  Definition find_free_block (len : nat) (pr : Provenance) : MemPropT MemState (addr * list addr)%type
    := fun m1 res =>
         match run_err_ub_oom res with
         | inl (OOM_message x) =>
             True
         | inr (inl (UB_message x)) =>
             False
         | inr (inr (inl (ERR_message x))) =>
             False
         | inr (inr (inr (m2, (ptr, ptrs)))) =>
             m1 = m2 /\ block_is_free m1 len pr ptr ptrs
         end.

  Record extend_read_byte_allowed (m1 : MemState) (ptrs : list addr) (m2 : MemState) : Prop :=
    { extend_read_byte_allowed_new_reads :
      forall p, In p ptrs ->
           read_byte_allowed m2 p;

      extend_read_byte_allowed_old_reads :
      forall ptr',
        (forall p, In p ptrs -> disjoint_ptr_byte p ptr') ->
        read_byte_allowed m1 ptr' <-> read_byte_allowed m2 ptr';
    }.

  Record extend_reads (m1 : MemState) (ptrs : list addr) (bytes : list SByte) (m2 : MemState) : Prop :=
    { extend_reads_new_reads :
      forall p ix byte,
        Util.Nth ptrs ix p ->
        Util.Nth bytes ix byte ->
        read_byte_prop m2 p byte;

      extend_reads_old_reads :
      forall ptr' byte,
        (forall p, In p ptrs -> disjoint_ptr_byte p ptr') ->
        read_byte_prop m1 ptr' byte <-> read_byte_prop m2 ptr' byte;
    }.

  Record extend_write_byte_allowed (m1 : MemState) (ptrs : list addr) (m2 : MemState) : Prop :=
    { extend_write_byte_allowed_new_writes :
      forall p, In p ptrs ->
           write_byte_allowed m2 p;

      extend_write_byte_allowed_old_writes :
      forall ptr',
        (forall p, In p ptrs -> disjoint_ptr_byte p ptr') ->
        write_byte_allowed m1 ptr' <-> write_byte_allowed m2 ptr';
    }.

  Record extend_free_byte_allowed (m1 : MemState) (ptrs : list addr) (m2 : MemState) : Prop :=
    { extend_free_byte_allowed_new :
      forall p, In p ptrs ->
           free_byte_allowed m2 p;

      extend_free_byte_allowed_old :
      forall ptr',
        (forall p, In p ptrs -> disjoint_ptr_byte p ptr') ->
        free_byte_allowed m1 ptr' <-> free_byte_allowed m2 ptr';
    }.

  Definition extend_stack_frame (m1 : MemState) (ptrs : list addr) (m2 : MemState) : Prop :=
    forall fs1 fs2,
      memory_stack_frame_stack_prop (MemState_get_memory m1) fs1 ->
      add_ptrs_to_frame_stack fs1 ptrs fs2 ->
      memory_stack_frame_stack_prop (MemState_get_memory m2) fs2.

  (*
    SAZ TODO: add Heap_in_bounds
  *)
  Definition extend_heap (m1 : MemState) (ptrs : list addr) (m2 : MemState) : Prop :=
    forall h1 h2,
      memory_stack_heap_prop (MemState_get_memory m1) h1 ->
      add_ptrs_to_heap h1 ptrs h2 ->
      memory_stack_heap_prop (MemState_get_memory m2) h2.

  Record extend_allocations (m1 : MemState) (ptrs : list addr) (pr : Provenance) (m2 : MemState) : Prop :=
    { extend_allocations_bytes_now_allocated :
      forall ptr, In ptr ptrs -> byte_allocated m2 ptr (provenance_to_allocation_id pr);

      extend_allocations_old_allocations_preserved :
      forall ptr aid,
        (forall p, In p ptrs -> disjoint_ptr_byte p ptr) ->
        (byte_allocated m1 ptr aid <-> byte_allocated m2 ptr aid);
    }.

  (*** Allocating bytes on the stack *)
  (* Post conditions for actually reserving bytes in memory and allocating them in the current stack frame *)
  Record allocate_bytes_post_conditions
    (m1 : MemState) (init_bytes : list SByte)
    (pr : Provenance) (m2 : MemState) (ptr : addr) (ptrs : list addr)
    : Prop :=
    { allocate_bytes_provenances_preserved :
      forall pr',
        (used_provenance_prop m1 pr' <-> used_provenance_prop m2 pr');

      (* byte_allocated *)
      allocate_bytes_extended_allocations : extend_allocations m1 ptrs pr m2;

      (* read permissions *)
      alloc_bytes_extended_reads_allowed : extend_read_byte_allowed m1 ptrs m2;

      (* reads *)
      alloc_bytes_extended_reads : extend_reads m1 ptrs init_bytes m2;

      (* write permissions *)
      alloc_bytes_extended_writes_allowed : extend_write_byte_allowed m1 ptrs m2;

      (* Add allocated bytes onto the stack frame *)
      allocate_bytes_add_to_frame : extend_stack_frame m1 ptrs m2;

      (* Heap preserved *)
      allocate_bytes_heap_preserved :
      heap_preserved m1 m2;
    }.

  Definition allocate_bytes_post_conditions_MemPropT
    (init_bytes : list SByte)
    (prov : Provenance) (ptr : addr) (ptrs : list addr)
    : MemPropT MemState (addr * list addr)
    := fun m1 res =>
         match run_err_ub_oom res with
         | inl (OOM_message x) =>
             False
         | inr (inl (UB_message x)) =>
             False
         | inr (inr (inl (ERR_message x))) =>
             False
         | inr (inr (inr (m2, (ptr', ptrs')))) =>
             allocate_bytes_post_conditions m1 init_bytes prov m2 ptr ptrs /\ ptr = ptr' /\ ptrs = ptrs'
         end.

  Definition allocate_bytes_with_pr_spec_MemPropT
    (init_bytes : list SByte) (prov : Provenance)
    : MemPropT MemState addr
    := '(ptr, ptrs) <- find_free_block (length init_bytes) prov;;
       allocate_bytes_post_conditions_MemPropT init_bytes prov ptr ptrs;;
       ret ptr.

  Definition allocate_bytes_spec_MemPropT
    (init_bytes : list SByte)
    : MemPropT MemState addr
    := prov <- fresh_provenance;;
       allocate_bytes_with_pr_spec_MemPropT init_bytes prov.

  (*** Allocating bytes in the heap *)
  Record malloc_bytes_post_conditions (m1 : MemState) (init_bytes : list SByte) (pr : Provenance) (m2 : MemState) (ptr : addr) (ptrs : list addr) : Prop :=
    { (* Provenance *)
      malloc_bytes_provenances_preserved :
      forall pr',
        (used_provenance_prop m1 pr' <-> used_provenance_prop m2 pr');

      (* byte_allocated *)
      malloc_bytes_extended_allocations : extend_allocations m1 ptrs pr m2;

      (* read permissions *)
      malloc_bytes_extended_reads_allowed : extend_read_byte_allowed m1 ptrs m2;

      (* reads *)
      malloc_bytes_extended_reads : extend_reads m1 ptrs init_bytes m2;

      (* write permissions *)
      malloc_bytes_extended_writes_allowed : extend_write_byte_allowed m1 ptrs m2;

      (* free permissions *)
      (* TODO: See #312, need to add this condition back later, but this currently complicates things *)
      (* free_root_allowed covers the case where 0 bytes are allocated *)
      (* malloc_bytes_extended_free_root_allowed : extend_free_byte_allowed m1 [ptr] m2; *)
      malloc_bytes_extended_free_allowed : extend_free_byte_allowed m1 ptrs m2;

      (* Framestack preserved *)
      malloc_bytes_frame_stack_preserved : frame_stack_preserved m1 m2;

      (* Heap extended *)
      malloc_bytes_add_to_frame : extend_heap m1 ptrs m2;
    }.

  Definition malloc_bytes_post_conditions_MemPropT (init_bytes : list SByte) (prov : Provenance) (ptr : addr) (ptrs : list addr) : MemPropT MemState (addr * list addr)
    := fun m1 res =>
         match run_err_ub_oom res with
         | inl (OOM_message x) =>
             False
         | inr (inl (UB_message x)) =>
             False
         | inr (inr (inl (ERR_message x))) =>
             False
         | inr (inr (inr (m2, (ptr', ptrs')))) =>
             malloc_bytes_post_conditions m1 init_bytes prov m2 ptr ptrs /\ ptr = ptr' /\ ptrs = ptrs'
         end.

  Definition malloc_bytes_with_pr_spec_MemPropT (init_bytes : list SByte) (prov : Provenance)
    : MemPropT MemState addr
    := '(ptr, ptrs) <- find_free_block (length init_bytes) prov;;
       malloc_bytes_post_conditions_MemPropT init_bytes prov ptr ptrs;;
       ret ptr.

  Definition malloc_bytes_spec_MemPropT (init_bytes : list SByte)
    : MemPropT MemState addr
    := prov <- fresh_provenance;;
       malloc_bytes_with_pr_spec_MemPropT init_bytes prov.

  (*** Freeing heap allocations *)
  Record free_operation_invariants (m1 : MemState) (m2 : MemState) :=
    {
      free_op_allocation_ids : preserve_allocation_ids m1 m2;
      free_frame_stack_preserved : frame_stack_preserved m1 m2;
    }.

  Record free_block_prop (h1 : Heap) (root : addr) (h2 : Heap) : Prop :=
    { free_block_ptrs_freed :
      forall ptr,
        ptr_in_heap_prop h1 root ptr ->
        ~ ptr_in_heap_prop h2 root ptr;

      free_block_root_freed :
      ~ root_in_heap_prop h2 root;

      (* TODO: make sure there's no weirdness about multiple roots *)
      free_block_disjoint_preserved :
      forall ptr root',
        disjoint_ptr_byte root root' ->
        ptr_in_heap_prop h1 root' ptr <-> ptr_in_heap_prop h2 root' ptr;

      free_block_disjoint_roots :
      forall root',
        disjoint_ptr_byte root root' ->
        root_in_heap_prop h1 root' <-> root_in_heap_prop h2 root';
    }.

  Record free_preconditions (m1 : MemState) (root : addr) : Prop :=
    { (* ptr being freed was a root *)
      free_was_root :
      root_in_memstate_heap m1 root;

      (* root being freed was allocated *)
      free_was_allocated :
      exists aid, byte_allocated m1 root aid;

      (* ptrs in block were allocated *)
      free_block_allocated :
      forall ptr,
        ptr_in_memstate_heap m1 root ptr ->
        exists aid, byte_allocated m1 ptr aid;

      (* root is allowed to be freed *)
      (* TODO: add this back. #312 / #313 *)
      (* Running into problems with exec_correct_free because of the
         implementation with size 0 allocations / frees *)
      (* free_root_allowed :
         free_byte_allowed m1 root; *)
    }.

  Record free_spec (m1 : MemState) (root : addr) (m2 : MemState) : Prop :=
    { (* all bytes in block are freed. *)
      free_bytes_freed :
      forall ptr,
        ptr_in_memstate_heap m1 root ptr ->
        byte_not_allocated m2 ptr;

      (* Bytes not allocated in the block have the same allocation status as before *)
      free_non_block_bytes_preserved :
      forall ptr aid,
        (~ ptr_in_memstate_heap m1 root ptr) ->
        byte_allocated m1 ptr aid <-> byte_allocated m2 ptr aid;

      (* Bytes not allocated in the freed block are the same when read *)
      free_non_frame_bytes_read :
      forall ptr byte,
        (~ ptr_in_memstate_heap m1 root ptr) ->
        read_byte_spec m1 ptr byte <-> read_byte_spec m2 ptr byte;

      (* Set new heap *)
      free_block :
      forall h1 h2,
        memory_stack_heap_prop (MemState_get_memory m1) h1 ->
        memory_stack_heap_prop (MemState_get_memory m2) h2 ->
        free_block_prop h1 root h2;

      (* Invariants *)
      free_invariants : free_operation_invariants m1 m2;
    }.

  Definition free_spec_MemPropT (root : addr) : MemPropT MemState unit :=
    lift_spec_to_MemPropT
      (fun m1 _ m2 =>
         free_preconditions m1 root /\ free_spec m1 root m2)
      (fun m1 => ~ free_preconditions m1 root).

  (*** Aggregate things *)

  (** Reading uvalues *)
  Definition read_bytes_spec (ptr : addr) (len : nat) : MemPropT MemState (list SByte) :=
    (* TODO: should this OOM, or should this count as walking outside of memory and be UB? *)
    ptrs <- get_consecutive_ptrs ptr len;;

    (* Actually perform reads *)
    map_monad (fun ptr => read_byte_spec_MemPropT ptr) ptrs.

  Definition read_uvalue_spec (dt : dtyp) (ptr : addr) : MemPropT MemState uvalue :=
    bytes <- read_bytes_spec ptr (N.to_nat (sizeof_dtyp dt));;
    lift_err_RAISE_ERROR (deserialize_sbytes bytes dt).

  (** Writing uvalues *)
  Definition write_bytes_spec (ptr : addr) (bytes : list SByte) : MemPropT MemState unit :=
    ptrs <- get_consecutive_ptrs ptr (length bytes);;
    let ptr_bytes := zip ptrs bytes in

    (* TODO: double check that this is correct... Should we check if all writes are allowed first? *)
    (* Actually perform writes *)
    map_monad_ (fun '(ptr, byte) => write_byte_spec_MemPropT ptr byte) ptr_bytes.

  Definition write_uvalue_spec (dt : dtyp) (ptr : addr) (uv : uvalue) : MemPropT MemState unit :=
    bytes <- serialize_sbytes uv dt;;
    write_bytes_spec ptr bytes.

  (** Allocating dtyps *)
  (* Need to make sure MemPropT has provenance and sids to generate the bytes. *)
  Definition allocate_dtyp_spec (dt : dtyp) (num_elements : N) : MemPropT MemState addr :=
    MemPropT_assert_pre (dt <> DTYPE_Void);;
    sid <- fresh_sid;;
    element_bytes <- repeatMN num_elements (lift_OOM (generate_undef_bytes dt sid));;
    let bytes := concat element_bytes in
    allocate_bytes_spec_MemPropT bytes.

  (** memcpy spec *)
  Definition memcpy_spec (src dst : addr) (len : Z) (volatile : bool) : MemPropT MemState unit :=
    if Z.ltb len 0
    then
      raise_ub "memcpy given negative length."
    else
      (* From LangRef: The ‘llvm.memcpy.*’ intrinsics copy a block of
       memory from the source location to the destination location, which
       must either be equal or non-overlapping.
       *)
      if orb (no_overlap dst len src len)
             (Z.eqb (ptr_to_int src) (ptr_to_int dst))
      then
        src_bytes <- read_bytes_spec src (Z.to_nat len);;

        (* TODO: Double check that this is correct... Should we check if all writes are allowed first? *)
        write_bytes_spec dst src_bytes
      else
        raise_ub "memcpy with overlapping or non-equal src and dst memory locations.".

  (** memset spec *)
  Definition memset_spec (dst : addr) (val : int8) (len : Z) (sid : store_id) (volatile : bool) : MemPropT MemState unit :=
    if Z.ltb len 0
    then
      raise_ub "memset given negative length."
    else
      let byte := uvalue_sbyte (UVALUE_I8 val) (DTYPE_I 8) 0 sid in
      write_bytes_spec dst (repeatN (Z.to_N len) byte).

  (*** Handling memory events *)
  Section Handlers.
    Definition handle_memory_prop : MemoryE ~> MemPropT MemState
      := fun T m =>
           match m with
           (* Unimplemented *)
           | MemPush =>
               mempush_spec_MemPropT
           | MemPop =>
               mempop_spec_MemPropT
           | Alloca t n align =>
               addr <- allocate_dtyp_spec t n;;
               ret (DVALUE_Addr addr)
           | Load t a =>
               match a with
               | DVALUE_Addr a =>
                   read_uvalue_spec t a
               | _ => raise_ub "Loading from something that isn't an address."
               end
           | Store t a v =>
               match a with
               | DVALUE_Addr a =>
                   write_uvalue_spec t a v
               | _ => raise_ub "Writing something to somewhere that isn't an address."
               end
           end.

    Definition handle_memcpy_prop (args : list dvalue) : MemPropT MemState unit :=
      match args with
      | DVALUE_Addr dst ::
                    DVALUE_Addr src ::
                    DVALUE_I32 len ::
                    DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          memcpy_spec src dst (unsigned len) (equ volatile VellvmIntegers.one)
      | DVALUE_Addr dst ::
                    DVALUE_Addr src ::
                    DVALUE_I64 len ::
                    DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          memcpy_spec src dst (unsigned len) (equ volatile VellvmIntegers.one)
      | DVALUE_Addr dst ::
                    DVALUE_Addr src ::
                    DVALUE_IPTR len ::
                    DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          memcpy_spec src dst (IP.to_Z len) (equ volatile VellvmIntegers.one)
      | _ => raise_error "Unsupported arguments to memcpy."
      end.

    Definition handle_memset_prop (args : list dvalue) : MemPropT MemState unit :=
      match args with
      | DVALUE_Addr dst ::
          DVALUE_I8 val ::
          DVALUE_I32 len ::
          DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          sid <- fresh_sid;;
          memset_spec dst val (unsigned len) sid (equ volatile VellvmIntegers.one)
      | DVALUE_Addr dst ::
          DVALUE_I8 val ::
          DVALUE_I64 len ::
          DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          sid <- fresh_sid;;
          memset_spec dst val (unsigned len) sid (equ volatile VellvmIntegers.one)
      | _ => raise_error "Unsupported arguments to memset."
      end.

    Definition handle_malloc_prop (args : list dvalue) : MemPropT MemState addr :=
      match args with
      | [DVALUE_I1 sz]
      | [DVALUE_I8 sz]
      | [DVALUE_I16 sz]
      | [DVALUE_I32 sz]
      | [DVALUE_I64 sz] =>
          sid <- fresh_sid;;
          bytes <- lift_OOM (generate_num_undef_bytes (Z.to_N (unsigned sz)) (DTYPE_I 8) sid);;
          malloc_bytes_spec_MemPropT bytes
      | [DVALUE_IPTR sz] =>
          sid <- fresh_sid;;
          bytes <- lift_OOM (generate_num_undef_bytes (Z.to_N (IP.to_unsigned sz)) (DTYPE_I 8) sid);;
          malloc_bytes_spec_MemPropT bytes
      | _ => raise_error "Malloc: invalid arguments."
      end.

    Definition handle_free_prop (args : list dvalue) : MemPropT MemState unit :=
      match args with
      | [DVALUE_Addr ptr] =>
          free_spec_MemPropT ptr
      | _ => raise_error "Free: invalid arguments."
      end.

    Definition handle_intrinsic_prop : IntrinsicE ~> MemPropT MemState
      := fun T e =>
           match e with
           | Intrinsic t name args =>
               (* Pick all arguments, they should all be unique. *)
               (* TODO: add more variants to memcpy *)
               (* FIXME: use reldec typeclass? *)
               if orb (Coqlib.proj_sumbool (string_dec name "llvm.memcpy.p0i8.p0i8.i32"))
                      (Coqlib.proj_sumbool (string_dec name "llvm.memcpy.p0i8.p0i8.i64"))
               then
                 handle_memcpy_prop args;;
                 ret DVALUE_None
               else
                 if orb (Coqlib.proj_sumbool (string_dec name "llvm.memset.p0i8.i32"))
                      (Coqlib.proj_sumbool (string_dec name "llvm.memset.p0i8.i64"))
                 then
                   handle_memset_prop args;;
                   ret DVALUE_None
                 else
                   if (Coqlib.proj_sumbool (string_dec name "malloc"))
                   then
                     addr <- handle_malloc_prop args;;
                     ret (DVALUE_Addr addr)
                   else
                     if (Coqlib.proj_sumbool (string_dec name "free"))
                     then
                       handle_free_prop args;;
                       ret DVALUE_None
                     else
                       raise_error ("Unknown intrinsic: " ++ name)
           end.

  End Handlers.

  (* TODO: Should these be here, or in another module? *)
  (* Useful helper lemmas and relations... *)
  #[global] Instance preserve_allocation_ids_Reflexive :
    Reflexive preserve_allocation_ids.
  Proof.
    red; intros ms.
    red.
    reflexivity.
  Qed.

  #[global] Instance read_byte_allowed_all_preserved_Reflexive :
    Reflexive read_byte_allowed_all_preserved.
  Proof.
    red; intros ms.
    red.
    reflexivity.
  Qed.

  #[global] Instance read_byte_prop_all_preserved_Reflexive :
    Reflexive read_byte_prop_all_preserved.
  Proof.
    red; intros ms.
    red.
    reflexivity.
  Qed.

  #[global] Instance read_byte_preserved_Reflexive :
    Reflexive read_byte_preserved.
  Proof.
    red; intros ms.
    red.
    split; reflexivity.
  Qed.

  #[global] Instance write_byte_allowed_all_preserved_Reflexive :
    Reflexive write_byte_allowed_all_preserved.
  Proof.
    red; intros ms.
    red.
    reflexivity.
  Qed.

  #[global] Instance free_byte_allowed_all_preserved_Reflexive :
    Reflexive free_byte_allowed_all_preserved.
  Proof.
    red; intros ms.
    red.
    reflexivity.
  Qed.

  #[global] Instance allocations_preserved_Reflexive :
    Reflexive allocations_preserved.
  Proof.
    red; intros ms.
    red.
    reflexivity.
  Qed.

  #[global] Instance frame_stack_preserved_memory_Reflexive :
    Reflexive frame_stack_preserved_memory.
  Proof.
    red; intros ms.
    red.
    reflexivity.
  Qed.

  #[global] Instance frame_stack_preserved_Reflexive :
    Reflexive frame_stack_preserved.
  Proof.
    red; intros ms.
    red.
    reflexivity.
  Qed.

  #[global] Instance heap_preserved_memory_Reflexive :
    Reflexive heap_preserved_memory.
  Proof.
    red; intros ms.
    red.
    reflexivity.
  Qed.

  #[global] Instance heap_preserved_Reflexive :
    Reflexive heap_preserved.
  Proof.
    red; intros ms.
    red.
    reflexivity.
  Qed.

  #[global] Instance addr_allocated_preserved_Reflexive : Reflexive addr_allocated_prop_memory_preserved.
  Proof.
    repeat red.
    intros x addr0 aid.
    split; intros ALLOC; auto.
  Qed.

  #[global] Instance read_byte_prop_memory_preserved_Reflexive : Reflexive read_byte_prop_memory_preserved.
  Proof.
    repeat red.
    intros x addr0 aid.
    split; intros ALLOC; auto.
  Qed.

  #[global] Instance memory_stack_Reflexive : Reflexive memory_stack_eqv.
  Proof.
    red.
    intros x.
    split; try reflexivity.
  Qed.

  #[global] Instance MemState_eqv'_Reflexive : Reflexive MemState_eqv'.
  Proof.
    red.
    intros ms.
    red.
    split; [|reflexivity].

    repeat (split; [reflexivity|]); reflexivity.
  Qed.

  #[global] Instance MemState_eqv_Reflexive : Reflexive MemState_eqv.
  Proof.
    red.
    intros ms.
    repeat (split; [reflexivity|]); reflexivity.
  Qed.

  Lemma fresh_sid_MemState_eqv :
    forall ms ms' sid,
      fresh_sid ms (ret (ms', sid)) ->
      MemState_eqv ms ms'.
  Proof.
    intros ms ms' sid H.
    destruct H.
    split; [|split; [|split; [|split; [|split; [|split]]]]];
      tauto.
  Qed.

  #[global] Instance preserve_allocation_ids_Transitive :
    Transitive preserve_allocation_ids.
  Proof.
    red; intros ms.
    red.
    intros y z H H0 p.
    split; intros USED.
    - apply H0, H; auto.
    - apply H, H0; auto.
  Qed.

  #[global] Instance read_byte_allowed_all_preserved_Transitive :
    Transitive read_byte_allowed_all_preserved.
  Proof.
    red; intros ms.
    red.
    intros y z H H0 ptr.
    split; intros READ.
    - apply H0, H; auto.
    - apply H, H0; auto.
  Qed.

  #[global] Instance read_byte_prop_all_preserved_Transitive :
    Transitive read_byte_prop_all_preserved.
  Proof.
    red; intros ms.
    red.
    intros y z H H0 ptr byte.
    split; intros READ.
    - apply H0, H; auto.
    - apply H, H0; auto.
  Qed.

  #[global] Instance read_byte_preserved_Transitive :
    Transitive read_byte_preserved.
  Proof.
    red; intros ms.
    red.
    intros y z H H0.
    destruct H, H0.
    split.
    - eapply read_byte_allowed_all_preserved_Transitive; eauto.
    - eapply read_byte_prop_all_preserved_Transitive; eauto.
  Qed.

  #[global] Instance write_byte_allowed_all_preserved_Transitive :
    Transitive write_byte_allowed_all_preserved.
  Proof.
    red; intros ms.
    red.
    intros y z H H0 ptr.
    split; intros WRITE.
    - apply H0, H; auto.
    - apply H, H0; auto.
  Qed.

  #[global] Instance free_byte_allowed_all_preserved_Transitive :
    Transitive free_byte_allowed_all_preserved.
  Proof.
    red; intros ms.
    red.
    intros y z H H0 ptr.
    split; intros FREE.
    - apply H0, H; auto.
    - apply H, H0; auto.
  Qed.

  #[global] Instance allocations_preserved_Transitive :
    Transitive allocations_preserved.
  Proof.
    red; intros ms.
    red.
    intros y z H H0 ptr aid.
    split; intros BYTE.
    - apply H0, H; auto.
    - apply H, H0; auto.
  Qed.

  #[global] Instance frame_stack_preserved_Transitive :
    Transitive frame_stack_preserved.
  Proof.
    red; intros ms.
    red.
    intros y z H H0 fs.
    split; intros FSP.
    - apply H0, H; auto.
    - apply H, H0; auto.
  Qed.

  #[global] Instance heap_preserved_Transitive :
    Transitive heap_preserved.
  Proof.
    red; intros ms.
    red.
    intros y z H H0 h.
    split; intros HEAP.
    - apply H0, H; auto.
    - apply H, H0; auto.
  Qed.

  #[global] Instance MemState_eqv_Transitive : Transitive MemState_eqv.
  Proof.
    red.
    intros x y z H H0.
    destruct H as (?&?&?&?&?&?&?).
    destruct H0 as (?&?&?&?&?&?&?).
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    - eapply preserve_allocation_ids_Transitive; eauto.
    - eapply read_byte_preserved_Transitive; eauto.
    - eapply write_byte_allowed_all_preserved_Transitive; eauto.
    - eapply free_byte_allowed_all_preserved_Transitive; eauto.
    - eapply allocations_preserved_Transitive; eauto.
    - eapply frame_stack_preserved_Transitive; eauto.
    - eapply heap_preserved_Transitive; eauto.
  Qed.

  #[global] Instance preserve_allocation_ids_Symmetric :
    Symmetric preserve_allocation_ids.
  Proof.
    red; intros ms.
    red.
    intros y H p.
    split; intros USED.
    - apply H; auto.
    - apply H; auto.
  Qed.

  #[global] Instance read_byte_allowed_all_preserved_Symmetric :
    Symmetric read_byte_allowed_all_preserved.
  Proof.
    red; intros ms.
    red.
    intros y H ptr.
    split; intros READ.
    - apply H; auto.
    - apply H; auto.
  Qed.

  #[global] Instance read_byte_prop_all_preserved_Symmetric :
    Symmetric read_byte_prop_all_preserved.
  Proof.
    red; intros ms.
    red.
    intros y H ptr byte.
    split; intros READ.
    - apply H; auto.
    - apply H; auto.
  Qed.

  #[global] Instance read_byte_preserved_Symmetric :
    Symmetric read_byte_preserved.
  Proof.
    red; intros ms.
    red.
    intros y H.
    destruct H.
    split.
    - eapply read_byte_allowed_all_preserved_Symmetric; eauto.
    - eapply read_byte_prop_all_preserved_Symmetric; eauto.
  Qed.

  #[global] Instance write_byte_allowed_all_preserved_Symmetric :
    Symmetric write_byte_allowed_all_preserved.
  Proof.
    red; intros ms.
    red.
    intros y H ptr.
    split; intros WRITE.
    - apply H; auto.
    - apply H; auto.
  Qed.

  #[global] Instance free_byte_allowed_all_preserved_Symmetric :
    Symmetric free_byte_allowed_all_preserved.
  Proof.
    red; intros ms.
    red.
    intros y H ptr.
    split; intros FREE.
    - apply H; auto.
    - apply H; auto.
  Qed.

  #[global] Instance allocations_preserved_Symmetric :
    Symmetric allocations_preserved.
  Proof.
    red; intros ms.
    red.
    intros y H ptr aid.
    split; intros BYTE.
    - apply H; auto.
    - apply H; auto.
  Qed.

  #[global] Instance frame_stack_preserved_Symmetric :
    Symmetric frame_stack_preserved.
  Proof.
    red; intros ms.
    red.
    intros y H fs.
    split; intros FSP.
    - apply H; auto.
    - apply H; auto.
  Qed.

  #[global] Instance heap_preserved_Symmetric :
    Symmetric heap_preserved.
  Proof.
    red; intros ms.
    red.
    intros y H h.
    split; intros HEAP.
    - apply H; auto.
    - apply H; auto.
  Qed.

  #[global] Instance MemState_eqv_Symmetric : Symmetric MemState_eqv.
  Proof.
    red.
    intros x y H.
    destruct H as (?&?&?&?&?&?&?).
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    - eapply preserve_allocation_ids_Symmetric; eauto.
    - eapply read_byte_preserved_Symmetric; eauto.
    - eapply write_byte_allowed_all_preserved_Symmetric; eauto.
    - eapply free_byte_allowed_all_preserved_Symmetric; eauto.
    - eapply allocations_preserved_Symmetric; eauto.
    - eapply frame_stack_preserved_Symmetric; eauto.
    - eapply heap_preserved_Symmetric; eauto.
  Qed.

End MemoryModelSpec.

Module MakeMemoryModelSpec (LP : LLVMParams) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) <: MemoryModelSpec LP MP MMSP.
  Include MemoryModelSpec LP MP MMSP.
End MakeMemoryModelSpec.

Module Type MemoryExecMonad (LP : LLVMParams) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) (MMS : MemoryModelSpec LP MP MMSP).
  Import LP.
  Import MMS.
  Import PROV.
  Import MMSP.
  Import MemHelpers.

  Definition MemMonad_valid_state (ms : MemState) (st : store_id) : Prop
    := let sid := st in
       (forall sid', used_store_id_prop ms sid' -> (sid' < sid)%N).

  Class MemMonad (M : Type -> Type) (RunM : Type -> Type)
        `{MM : Monad M} `{MRun: Monad RunM}
        `{MPROV : MonadProvenance Provenance M} `{MSID : MonadStoreId M} `{MMS: MonadMemState MemState M}
        `{MERR : RAISE_ERROR M} `{MUB : RAISE_UB M} `{MOOM :RAISE_OOM M}
        `{RunERR : RAISE_ERROR RunM} `{RunUB : RAISE_UB RunM} `{RunOOM :RAISE_OOM RunM}
        `{EQM : Eq1 M} `{EQRI : @Eq1_ret_inv M EQM MM} `{MLAWS : @MonadLawsE M EQM MM}
    : Type
    :=
    { #[global] MemMonad_eq1_runm :: Eq1 RunM;
      #[global] MemMonad_runm_monadlaws :: MonadLawsE RunM;
      #[global] MemMonad_eq1_runm_equiv :: Eq1Equivalence RunM;
      #[global] MemMonad_eq1_runm_eq1laws :: Eq1_ret_inv RunM;
      #[global] MemMonad_raisebindm_ub :: RaiseBindM RunM string (@raise_ub RunM RunUB);
      #[global] MemMonad_raisebindm_oom :: RaiseBindM RunM string (@raise_oom RunM RunOOM);
      #[global] MemMonad_raisebindm_err :: RaiseBindM RunM string (@raise_error RunM RunERR);
      #[global] MemMonad_within :: @Within M EQM RunM (store_id * MemState)%type (store_id * MemState)%type;

      #[global] MemMonad_eq1_runm_proper ::
                               (forall A, Proper ((@eq1 _ MemMonad_eq1_runm) A ==> (@eq1 _ MemMonad_eq1_runm) A ==> iff) ((@eq1 _ MemMonad_eq1_runm) A));

      MemMonad_run {A} (ma : M A) (ms : MemState) (st : store_id)
      : RunM (store_id * (MemState * A))%type;

      #[global] MemMonad_run_proper ::
        (forall A, Proper (@eq1 _ EQM A ==> eq ==> eq ==> @eq1 _ MemMonad_eq1_runm (store_id * (MemState * A))) MemMonad_run);

      (** Some lemmas about valid states *)
      (* This may not be true for infinite memory. Valid state is
         mostly used to ensure that we can find a store id that hasn't
         been used in memory yet...

         Unfortunately, if memory is infinite it's possible to
         construct a MemState that has a byte allocated for every
         store id... Even though store ids are unbounded integers,
         they have the same cardinality as the memory :|.
       *)
      (*
      MemMonad_has_valid_state :
      forall (ms : MemState), exists (st : store_id),
        MemMonad_valid_state ms st;
       *)
    (** Run bind / ret laws *)
    MemMonad_run_bind
      {A B} (ma : M A) (k : A -> M B) (ms : MemState) (st : store_id):
    eq1 (MemMonad_run (x <- ma;; k x) ms st)
        ('(st', (ms', x)) <- MemMonad_run ma ms st;; MemMonad_run (k x) ms' st');

    MemMonad_run_ret
      {A} (x : A) (ms : MemState) st:
    eq1 (MemMonad_run (ret x) ms st) (ret (st, (ms, x)));

    (** MonadMemState properties *)
    MemMonad_get_mem_state
      (ms : MemState) st :
    eq1 (MemMonad_run (get_mem_state) ms st) (ret (st, (ms, ms)));

    MemMonad_put_mem_state
      (ms ms' : MemState) st :
    eq1 (MemMonad_run (put_mem_state ms') ms st) (ret (st, (ms', tt)));

    (** Fresh store id property *)
    MemMonad_run_fresh_sid
      (ms : MemState) st (VALID : MemMonad_valid_state ms st):
    exists st' sid',
      eq1 (MemMonad_run (fresh_sid) ms st) (ret (st', (ms, sid'))) /\
        MemMonad_valid_state ms st' /\
        sid' <= st /\ st < st' /\
        ~ used_store_id_prop ms sid';

    (** Fresh provenance property *)
    (* TODO: unclear if this should exist, must change ms. *)
    MemMonad_run_fresh_provenance
      (ms : MemState) st (VALID : MemMonad_valid_state ms st):
    exists ms' pr',
      eq1 (MemMonad_run (fresh_provenance) ms st) (ret (st, (ms', pr'))) /\
        MemMonad_valid_state ms' st /\
        ms_get_memory ms = ms_get_memory ms' /\
        (* Analogous to extend_provenance *)
        (forall pr, used_provenance_prop ms pr -> used_provenance_prop ms' pr) /\
        ~ used_provenance_prop ms pr' /\
        used_provenance_prop ms' pr';

    (** Exceptions *)
    MemMonad_run_raise_oom :
    forall {A} ms oom_msg st,
      eq1 (MemMonad_run (@raise_oom _ _ A oom_msg) ms st) (raise_oom oom_msg);

    MemMonad_eq1_raise_oom_inv :
    forall {A} x oom_msg,
      ~ ((@eq1 _ MemMonad_eq1_runm) A (ret x) (raise_oom oom_msg));

    MemMonad_run_raise_ub :
    forall {A} ms ub_msg st,
      eq1 (MemMonad_run (@raise_ub _ _ A ub_msg) ms st) (raise_ub ub_msg);

    MemMonad_eq1_raise_ub_inv :
    forall {A} x ub_msg,
      ~ ((@eq1 _ MemMonad_eq1_runm) A (ret x) (raise_ub ub_msg));

    MemMonad_run_raise_error :
    forall {A} ms error_msg st,
      eq1 (MemMonad_run (@raise_error _ _ A error_msg) ms st) (raise_error error_msg);

    MemMonad_eq1_raise_error_inv :
    forall {A} x error_msg,
      ~ ((@eq1 _ MemMonad_eq1_runm) A (ret x) (raise_error error_msg));

    MemMonad_eq1_raise_oom_raise_error_inv :
    forall {A} oom_msg error_msg,
      ~ ((@eq1 _ MemMonad_eq1_runm) A (raise_oom oom_msg) (raise_error error_msg));

    MemMonad_eq1_raise_error_raise_oom_inv :
    forall {A} error_msg oom_msg,
      ~ ((@eq1 _ MemMonad_eq1_runm) A (raise_error error_msg) (raise_oom oom_msg));

    MemMonad_eq1_raise_ub_raise_error_inv :
    forall {A} ub_msg error_msg,
      ~ ((@eq1 _ MemMonad_eq1_runm) A (raise_ub ub_msg) (raise_error error_msg));

    MemMonad_eq1_raise_error_raise_ub_inv :
    forall {A} error_msg ub_msg,
      ~ ((@eq1 _ MemMonad_eq1_runm) A (raise_error error_msg) (raise_ub ub_msg));

    MemMonad_eq1_raise_oom_raise_ub_inv :
    forall {A} oom_msg ub_msg,
      ~ ((@eq1 _ MemMonad_eq1_runm) A (raise_oom oom_msg) (raise_ub ub_msg));

    MemMonad_eq1_raise_ub_raise_oom_inv :
    forall {A} ub_msg oom_msg,
      ~ ((@eq1 _ MemMonad_eq1_runm) A (raise_ub ub_msg) (raise_oom oom_msg));
  }.

  Definition within_RunM_MemMonad {MemM RunM} `{MM: MemMonad MemM RunM} {A} (memm : MemM A) (pre : (store_id * MemState)%type) (runm : RunM A) (post : (store_id * MemState)%type) : Prop :=
    let '(st1, ms1) := pre in
    let '(st2, ms2) := post in
    let t := MemMonad_run memm ms1 st1 in
    let run := a <- runm;; ret (st2, (ms2, a)) : RunM (store_id * (MemState * A))%type in
    let eqi := (@eq1 _ (@MemMonad_eq1_runm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MM)) in
    eqi _ t run.

  Lemma within_eq1_Proper_RunM_MemMonad {MemM RunM} `{MM: MemMonad MemM RunM} {A} :
    Proper (eq1 ==> eq ==> eq ==> eq ==> iff) (within_RunM_MemMonad (A:=A)).
  Proof.
    unfold Proper, respectful.
    intros x y H x0 y0 H0 x1 y1 H1 x2 y2 H2.
    subst.
    unfold within_RunM_MemMonad in *.
    destruct y0, y2.
    split; intros WITHIN.
    - rewrite H in WITHIN.
      auto.
    - rewrite H.
      auto.
  Qed.

  #[global] Instance Within_RunM_MemMonad {MemM RunM} `{MM: MemMonad MemM RunM} : @Within MemM _ RunM (store_id * MemState)%type (store_id * MemState)%type.
  Proof.
    esplit.
    Unshelve.
    2: {
      intros A m pre b post.
      eapply @within_RunM_MemMonad.
      3: apply pre.
      4: apply post.
      all: eauto.
    }

    intros A.
    unfold Proper, respectful.
    intros x y H x0 y0 H0 x1 y1 H1 x2 y2 H2.
    subst.
    eapply within_eq1_Proper_RunM_MemMonad; eauto.
  Defined.

  Definition within_err_ub_oom_itree
    {Pre Post : Type}
    {Eff}
    `{FAIL : FailureE -< Eff} `{UB : UBE -< Eff} `{OOM : OOME -< Eff}
    {A} (t : itree Eff A) (pre : Pre) (e : err_ub_oom A) (post : Post) : Prop :=
    t ≈ lift_err_ub_oom ret e.

  (* Version that uses RAISE_OOM etc explicitly *)
  Import IdentityMonad.
  Definition within_err_ub_oom_itree'
    {Pre Post : Type}
    {Eff}
    `{EQI : Eq1 (itree Eff)}
    `{MITREE : Monad (itree Eff)}
    `{FAIL : RAISE_ERROR (itree Eff)} `{UB : RAISE_UB (itree Eff)} `{OOM : RAISE_OOM (itree Eff)}
    {A} (t : itree Eff A) (pre : Pre) (e : err_ub_oom A) (post : Post) : Prop :=
    match e with
    | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
        match m with
        | inl (OOM_message x) =>
            exists oom_msg, t ≈ raise_oom oom_msg
        | inr (inl (UB_message x)) =>
            (* Should this be more permissive? *)
            exists ub_msg, t ≈ raise_ub ub_msg
        | inr (inr (inl (ERR_message x))) =>
            exists err_msg, t ≈ raise_error err_msg
        | inr (inr (inr x)) =>
            (t ≈ ret x)%monad
        end
    end.

  Lemma within_Proper_err_ub_oom_itree
    {Pre Post : Type}
    {Eff}
    `{FAIL : FailureE -< Eff} `{UB : UBE -< Eff} `{OOM : OOME -< Eff}
    {A} :
    Proper (eq1 ==> eq ==> eq ==> eq ==> iff) (within_err_ub_oom_itree (Eff:=Eff) (Pre:=Pre) (Post:=Post) (A:=A)).
  Proof.
    unfold Proper, respectful.
    intros x y H x0 y0 H0 x1 y1 H1 x2 y2 H2.
    subst.
    unfold within_err_ub_oom_itree in *.
    split; intros WITHIN.
    - rewrite H in WITHIN.
      auto.
    - rewrite H.
      auto.
  Qed.

  Lemma within_Proper_err_ub_oom_itree'
    {Pre Post : Type}
    {Eff}
    `{EQI : Eq1 (itree Eff)}
    `{MITREE : Monad (itree Eff)}
    `{EQV : @Eq1Equivalence (itree Eff) _ EQI}
    `{FAIL : RAISE_ERROR (itree Eff)} `{UB : RAISE_UB (itree Eff)} `{OOM : RAISE_OOM (itree Eff)}
    {A} :
    Proper (eq1 ==> eq ==> eq ==> eq ==> iff) (within_err_ub_oom_itree' (EQI:=EQI) (Pre:=Pre) (Post:=Post) (A:=A)).
  Proof.
    unfold Proper, respectful.
    intros x y H x0 y0 H0 x1 y1 H1 x2 y2 H2.
    subst.
    unfold within_err_ub_oom_itree' in *.
    split; intros WITHIN.
    - destruct y1 as [[[[[[[oom_y1] | [[ub_y1] | [[err_y1] | y1']]]]]]]] eqn:Hy1;
        setoid_rewrite H in WITHIN;
        auto.
    - destruct y1 as [[[[[[[oom_y1] | [[ub_y1] | [[err_y1] | y1']]]]]]]] eqn:Hy1;
        setoid_rewrite H;
        auto.
  Qed.

  #[global] Instance Within_err_ub_oom_itree'
    {Pre Post : Type}
    {Eff}
    `{EQI : Eq1 (itree Eff)}
    `{MITREE : Monad (itree Eff)}
    `{EQV : @Eq1Equivalence (itree Eff) _ EQI}
    `{FAIL : RAISE_ERROR (itree Eff)} `{UB : RAISE_UB (itree Eff)} `{OOM : RAISE_OOM (itree Eff)}
    : @Within (itree Eff) _ err_ub_oom Pre Post.
  Proof.
    esplit.
    intros A.
    unfold Proper, respectful.
    intros x y H x0 y0 H0 x1 y1 H1 x2 y2 H2.
    eapply within_Proper_err_ub_oom_itree'; eauto.
  Defined.

  (* Should probably be derivable with typeclasses eauto... *)
  #[global] Instance Within_err_ub_oom_MemM {MemM Eff}
    `{EQI : Eq1 (itree Eff)}
    `{MITREE : Monad (itree Eff)}
    `{EQV : @Eq1Equivalence (itree Eff) _ EQI}
    `{FAIL : RAISE_ERROR (itree Eff)} `{UB : RAISE_UB (itree Eff)} `{OOM : RAISE_OOM (itree Eff)}
    `{MM: MemMonad MemM (itree Eff)} : @Within MemM _ err_ub_oom (store_id * MemState)%type (store_id * MemState)%type.
  Proof.
    eapply @Transitive_Within with (M1:=err_ub_oom) (M2:=itree Eff) (M3:=MemM).
    - eapply Within_err_ub_oom_itree'.
    - eapply Within_RunM_MemMonad.
  Defined.

  (*** Correctness *)
  Definition exec_correct_post (X : Type) : Type := MemState -> store_id -> X -> MemState -> store_id -> Prop.
  Definition exec_correct_id_post {X} : exec_correct_post X :=
    fun _ _ _ _ _ => True.
  #[global] Hint Unfold exec_correct_id_post : core.
  Definition exec_correct_pre := MemState -> store_id -> Prop.

  Definition exec_correct_post_ret {X} (x : X) : exec_correct_post X
    := fun ms st x' ms' st' =>
         x = x' /\ ms = ms' /\ st = st'.

  Definition exec_correct_post_bind
    {A B}
    (ma : exec_correct_post A)
    (k : A -> exec_correct_post B)
    : exec_correct_post B
    := fun ms st b ms'' st'' =>
         exists a ms' st',
           ma ms st a ms' st' /\
             (k a) ms' st' b ms'' st''.

  Definition exec_correct_post_eqv {A} (a b : exec_correct_post A) :=
    forall ms st x ms' st',
      a ms st x ms' st' <-> b ms st x ms' st'.

  Lemma exec_correct_post_eqv_refl :
    forall {A} (a : exec_correct_post A),
      exec_correct_post_eqv a a.
  Proof.
    intros A a.
    red.
    reflexivity.
  Qed.

  #[global] Instance MonadStoreId_exec_correct_post : MonadStoreId exec_correct_post.
  split.
  refine (fun ms st sid ms' st' =>
            sid <= st /\ st < st' /\ ms = ms').
  Defined.

  #[global] Instance MonadProvenance_exec_correct_post : MonadProvenance Provenance exec_correct_post.
  split.
  refine (fun ms st pr ms' st' =>
            (forall pr0 : Provenance, used_provenance_prop ms pr0 -> used_provenance_prop ms' pr0) /\
              ~ used_provenance_prop ms pr /\ used_provenance_prop ms' pr /\
              st = st').
  Defined.

  #[global] Instance Proper_exec_correct_post_eqv {X} :
    Proper (@exec_correct_post_eqv X ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff) (fun post ms st x ms' st' => post ms st x ms' st').
  Proof.
    unfold Proper, respectful.
    intros; subst.
    apply H.
  Qed.

  Lemma exec_correct_post_left_identity :
    forall {A B} (a : A) (k : A -> exec_correct_post B),
      exec_correct_post_eqv (exec_correct_post_bind (exec_correct_post_ret a) k) (k a).
  Proof.
    intros A B a k ms st x ms' st'.
    unfold exec_correct_post_ret.
    unfold exec_correct_post_bind.
    split; intros H.
    - destruct H as (?&?&?&?&?); subst.
      destruct H as (?&?&?); subst.
      auto.
    - exists a, ms, st.
      auto.
  Qed.

  Lemma exec_correct_post_right_identity :
    forall {A} (ma : exec_correct_post A),
      exec_correct_post_eqv (exec_correct_post_bind ma exec_correct_post_ret) ma.
  Proof.
    intros A ma ms st x ms' st'.
    unfold exec_correct_post_ret.
    unfold exec_correct_post_bind.
    split; intros H.
    - destruct H as (?&?&?&?&?); subst.
      destruct H0 as (?&?&?); subst.
      auto.
    - exists x, ms', st'.
      auto.
  Qed.

  Lemma exec_correct_post_associativity :
    forall {A B C}
      (ma : exec_correct_post A)
      (mab : A -> exec_correct_post B)
      (mbc : B -> exec_correct_post C),
      exec_correct_post_eqv
        (exec_correct_post_bind (exec_correct_post_bind ma mab) mbc)
        (exec_correct_post_bind ma (fun a => exec_correct_post_bind (mab a) mbc)).
  Proof.
    intros A B C ma mab mbc.
    unfold exec_correct_post_ret.
    unfold exec_correct_post_bind.
    split; intros H.
    - destruct H as (?&?&?&?&?); subst.
      destruct H as (?&?&?&?&?); subst.
      exists x3, x4, x5.
      split; eauto.
    - destruct H as (?&?&?&?&?); subst.
      destruct H0 as (?&?&?&?&?); subst.
      exists x3, x4, x5.
      split; eauto.
  Qed.

  #[global] Instance Monad_exec_correct_post : Monad exec_correct_post.
  split.
  - intros; apply exec_correct_post_ret; auto.
  - intros; eapply exec_correct_post_bind; eauto.
  Defined.

  #[global] Instance Eq1_exec_correct_post : Eq1 exec_correct_post.
  red. intros. eapply exec_correct_post_eqv.
  apply X.
  apply X0.
  Defined.

  #[global] Instance MonadLawsE_exec_correct_post : MonadLawsE exec_correct_post.
  split.
  - intros. apply exec_correct_post_left_identity.
  - intros. apply exec_correct_post_right_identity.
  - intros. apply exec_correct_post_associativity.
  - intros A B.
    unfold Proper, respectful.
    intros x y H x0 y0 H0.
    repeat red in H.
    repeat red.
    intros ms st x1 ms' st'.
    split.
    + intros H1.
      red in H0.
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      specialize (H ms st x2 x3 x4).
      destruct H.
      eapply H in H1.
      repeat red.
      exists x2, x3, x4.
      split; eauto.
      apply H0; auto.
    + intros H1.
      red in H0.
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      specialize (H ms st x2 x3 x4).
      destruct H.
      eapply H3 in H1.
      repeat red.
      exists x2, x3, x4.
      split; eauto.
      apply H0; auto.
  Defined.

  Lemma exec_correct_post_bind_unfold :
    forall {A B}
      (ma : exec_correct_post A)
      (mab : A -> exec_correct_post B)
      ms st b ms'' st'',
      (exists a ms' st',
          ma ms st a ms' st' /\
            (mab a) ms' st' b ms'' st'') ->
      (a <- ma;;
       mab a) ms st b ms'' st''.
  Proof.
    intros A B ma mab ms st b ms'' st'' H.
    cbn.
    unfold exec_correct_post_bind.
    auto.
  Qed.

  Definition exec_correct {MemM Eff} `{MM: MemMonad MemM (itree Eff)} {X} (pre : exec_correct_pre) (exec : MemM X) (spec : MemPropT MemState X) (post : exec_correct_post X) : Prop :=
    forall ms st,
      (MemMonad_valid_state ms st) ->
      pre ms st ->
      (* UB catchall *)
      (exists ms' msg_spec,
          @raise_ub err_ub_oom _ X msg_spec {{ ms }} ∈ {{ ms' }} spec) \/
        ( (* exists a behaviour in exec that lines up with spec.

               Technically this should be something along the lines of...

               "There is at least one behaviour in exec, and for every
               behaviour in exec it is within the spec"

               For our purposes exec is deterministic, so "exists"
               should be fine here for simplicity.
             *)
           exists (e : err_ub_oom X) (st' : store_id) (ms' : MemState),
             (* Had to manually supply typeclasses, but this within expression is: (e {{(st, ms)}} ∈ {{(st', ms')}} exec))

                 I.e., The executable is correct if forall behaviours
                 in the executable those behaviours are in the spec as
                 well, and if the executable returns successfully it
                 gives a valid store_id / MemState pair.
              *)
             let WEM := (Within_err_ub_oom_MemM (EQI:=(@MemMonad_eq1_runm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MM)) (EQV:=(@MemMonad_eq1_runm_equiv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MM))) in
             (@within MemM _ err_ub_oom (store_id * MemState)%type (store_id * MemState)%type WEM X exec (st, ms) e (st', ms')) /\
               (e {{ms}} ∈ {{ms'}} spec) /\ ((exists x, e = ret x) -> (MemMonad_valid_state ms' st' /\ (exists x, e = ret x /\ post ms st x ms' st')))).

  (* TODO: Move this *)
  Lemma exec_correct_weaken_pre :
    forall {MemM Eff} `{MEMM : MemMonad MemM (itree Eff)}
      {A}
      (pre : exec_correct_pre)
      (post : exec_correct_post A)
      (weak_pre : exec_correct_pre)
      (exec : MemM A)
      (spec : MemPropT MemState A),
      (forall ms st, pre ms st -> weak_pre ms st) ->
      exec_correct weak_pre exec spec post ->
      exec_correct pre exec spec post.
  Proof.
    intros MemM Eff MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI MLAWS MEMM A pre post weak_pre exec spec WEAK EXEC.
    unfold exec_correct in *.
    intros ms st VALID PRE.
    apply WEAK in PRE.
    eauto.
  Qed.

  (* TODO: Move this *)
  Lemma exec_correct_strengthen_post :
    forall {MemM Eff} `{MEMM : MemMonad MemM (itree Eff)}
      {A}
      (pre : exec_correct_pre)
      (post : exec_correct_post A)
      (strong_post : exec_correct_post A)
      (exec : MemM A)
      (spec : MemPropT MemState A),
      (forall ms st a ms' st', pre ms st -> strong_post ms st a ms' st' -> post ms st a ms' st') ->
      exec_correct pre exec spec strong_post ->
      exec_correct pre exec spec post.
  Proof.
    intros MemM Eff MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI MLAWS MEMM A pre post strong_post exec spec STRONG EXEC.
    unfold exec_correct in *.
    intros ms st VALID PRE.
    specialize (EXEC _ _ VALID PRE).
    destruct EXEC as [UB | EXEC]; auto.
    right.
    destruct EXEC as (?&?&?&?&?&?).
    exists x, x0, x1.
    split; auto.
    split; auto.
    intros H2.
    forward H1; auto.
    destruct H1 as (?&(?&?&?)).
    subst.
    split; auto.
    exists x2.
    split; auto.
  Qed.

  (* TODO: move this *)
  Lemma exec_correct_bind :
    forall {MemM Eff} `{MEMM : MemMonad MemM (itree Eff)}
      {A B}
      (pre : exec_correct_pre)
      (post_a : exec_correct_post A)
      (post_b : A -> exec_correct_post B)
      (m_exec : MemM A) (k_exec : A -> MemM B)
      (m_spec : MemPropT MemState A) (k_spec : A -> MemPropT MemState B),
      exec_correct pre m_exec m_spec post_a ->
      (* This isn't true:

           (forall a ms ms', m_spec ms (ret (ms', a)) -> exec_correct (k_exec a) (k_spec a)) -> ...

           E.g., if 1 is a valid return value in m_spec, but m_exec can only return 0, then

           k_spec may ≈ ret 2

           But k_exec may ≈ \a => if a == 0 then ret 2 else raise_ub "blah"

           I.e., k_exec may be set up to only be valid when results are returned by m_exec.
       *)
      (* The exec continuation `k_exec a` agrees with `k_spec a`
           whenever `a` is a valid return value from the spec and the
           executable prefix

           Questions:

           - What if m_exec returns an `a` that isn't in the spec...
             + Should be covered by `exec_correct m_exec m_spec` assumption.
       *)
      (forall a ms_init ms_after_m st_init st_after_m,
          MemMonad_valid_state ms_after_m st_after_m ->
          post_a ms_init st_init a ms_after_m st_after_m ->
          ((@eq1 _ (@MemMonad_eq1_runm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MEMM)) _
                                                                                (MemMonad_run m_exec ms_init st_init)
                                                                                (ret (st_after_m, (ms_after_m, a))))%monad ->
          (* ms_k is a MemState after evaluating m *)
          let WEM := (Within_err_ub_oom_MemM (EQI:=(@MemMonad_eq1_runm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MEMM)) (EQV:=(@MemMonad_eq1_runm_equiv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MEMM))) in
          exec_correct (fun ms_k st_k =>
                          pre ms_init st_init /\
                            (@within MemM _ err_ub_oom (store_id * MemState)%type (store_id * MemState)%type WEM _ m_exec (st_init, ms_init) (ret a) (st_k, ms_k))
                          /\ m_spec ms_init (ret (ms_k, a))) (k_exec a) (k_spec a) (post_b a)) ->
      exec_correct pre (a <- m_exec;; k_exec a) (a <- m_spec;; k_spec a) (a <- post_a;; post_b a).
  Proof.
    intros MemM Eff MM MRun MPROV MSID MMS
      MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI
      MLAWS MEMM A B pre post_a post_b m_exec k_exec m_spec
      k_spec M_CORRECT K_CORRECT.

    unfold exec_correct in *.
    intros ms st VALID PRE.
    specialize (M_CORRECT ms st VALID PRE).
    destruct M_CORRECT as [[ub_ms' [msg M_UB]] | M_CORRECT].
    { (* UB *)
      left.
      exists ub_ms'. exists msg.
      left; auto.
    }

    destruct M_CORRECT as [e [st' [ms' [M_EXEC_CORRECT [M_SPEC_CORRECT M_POST]]]]].
    destruct e as [[[[[[[oom_e] | [[ub_e] | [[err_e] | e']]]]]]]] eqn:He.

    - (* OOM *)
      right.
      exists (raise_oom oom_e).
      exists st'.
      exists ms'.

      split.
      { (* Exec *)
        cbn in M_EXEC_CORRECT.
        red in M_EXEC_CORRECT.
        cbn. red.
        destruct M_EXEC_CORRECT as [m2 [[oom_msg OOM] EXEC]].
        exists (raise_oom oom_msg).
        split.
        cbn.
        eexists; reflexivity.
        cbn.
        cbn in EXEC.
        rewrite MemMonad_run_bind.
        rewrite EXEC.
        rewrite OOM.
        repeat (rewrite rbm_raise_bind; [| typeclasses eauto]).
        reflexivity.
      }

      split.
      { (* In spec *)
        cbn.
        left.
        apply M_SPEC_CORRECT.
      }

      intros [x CONTRA].
      inv CONTRA.
    - (* UB *)
      left.
      exists ms'. exists ub_e.
      cbn.
      left.
      apply M_SPEC_CORRECT.
    - (* Err *)
      right.
      exists (raise_error err_e).
      exists st'.
      exists ms'.

      split.
      { (* Exec *)
        cbn in M_EXEC_CORRECT.
        red in M_EXEC_CORRECT.
        cbn. red.
        destruct M_EXEC_CORRECT as [m2 [[err_msg ERR] EXEC]].
        exists (raise_error err_msg).
        split.
        cbn.
        eexists; reflexivity.
        cbn.
        cbn in EXEC.
        rewrite MemMonad_run_bind.
        rewrite EXEC.
        rewrite ERR.
        repeat (rewrite rbm_raise_bind; [| typeclasses eauto]).
        reflexivity.
      }

      split.
      { (* In spec *)
        cbn.
        left.
        apply M_SPEC_CORRECT.
      }

      intros [x CONTRA].
      cbn in CONTRA.
      inv CONTRA.
    - (* Success *)
      (* Need to know if there's UB in K... *)
      rename e' into a.
      forward M_POST.
      { eexists; reflexivity. }
      destruct M_POST as (VALID' & POST').
      destruct POST' as (?&?&POST').
      inv H.
      rename x into a.

      specialize (K_CORRECT a ms ms' st st').
      forward K_CORRECT; eauto.
      forward K_CORRECT; eauto.

      forward K_CORRECT.
      { cbn in M_EXEC_CORRECT.
        red in M_EXEC_CORRECT.
        destruct M_EXEC_CORRECT as [m2 [SUCC EXEC]].
        cbn in *.
        rewrite EXEC, SUCC.
        rewrite bind_ret_l.
        reflexivity.
      }

      specialize (K_CORRECT _ _ VALID').
      forward K_CORRECT.
      { split; auto. }

      destruct K_CORRECT as [[ub_ms [ub_msg K_UB]] | K_CORRECT].
      { (* UB in K *)
        left.
        exists ub_ms. exists ub_msg.
        right.
        exists ms'. exists a.
        split; auto.
      }

      (* UB not necessarily in K *)
      right.
      destruct K_CORRECT as [eb [st'' [ms'' [K_EXEC [K_SPEC K_POST]]]]].

      cbn in M_EXEC_CORRECT.
      red in M_EXEC_CORRECT.

      cbn in K_EXEC.
      red in K_EXEC.

      destruct M_EXEC_CORRECT as [tm [M_SUCC M_EXEC]].
      destruct K_EXEC as [tk [K_SUCC K_EXEC]].

      cbn in M_SUCC, M_EXEC.
      rewrite M_SUCC in M_EXEC.
      rewrite bind_ret_l in M_EXEC.

      exists eb. exists st''. exists ms''.
      split; [| split].

      { (* Exec *)
        exists tk.
        split; auto.

        cbn.
        rewrite MemMonad_run_bind.

        rewrite M_EXEC.
        rewrite bind_ret_l.
        rewrite K_EXEC.
        reflexivity.
      }

      { (* Spec *)
        (* TODO: Probably a good bind lemma for this *)
        destruct eb as [[[[[[[oom_eb] | [[ub_eb] | [[err_eb] | eb']]]]]]]] eqn:Heb;
          try right; cbn; exists ms'; exists a; split; auto.
      }

      { (* Post *)
        intros [x RET].
        subst.
        forward K_POST; eauto.
        destruct K_POST.
        split; eauto.
        exists x.
        split; auto.
        destruct H0 as (?&?&?).
        inv H0.

        repeat red.
        exists a, ms', st'.
        split; eauto.
      }
  Qed.

  Lemma exec_correct_ret :
    forall {MemM Eff} `{MemMonad MemM (itree Eff)}
      {X}
      (pre : exec_correct_pre)
      (x : X),
      exec_correct pre (ret x) (ret x) (exec_correct_post_ret x).
  Proof.
    intros MemM Eff MM MRun MPROV MSID MMS
      MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI
      MLAWS H X pre x.
    intros ms st VALID PRE.
    right.
    exists (ret x), st, ms.
    split.
    { (* TODO: cleaner lemma *)
      cbn.
      red.
      exists (ret x).
      split.
      - cbn. reflexivity.
      - cbn.
        rewrite MemMonad_run_ret.
        rewrite bind_ret_l.
        reflexivity.
    }

    split; cbn; auto.
    intros H0.
    split; eauto.
    exists x.
    split; eauto.
    red.
    auto.
  Qed.

  Lemma exec_correct_map_monad :
    forall {MemM Eff} `{MemMonad MemM (itree Eff)}
      {A B}
      xs
      (m_exec : A -> MemM B) (m_spec : A -> MemPropT MemState B)
      (post : A -> exec_correct_post B),
      (forall a (pre : _ -> _ -> Prop),
          exec_correct pre (m_exec a) (m_spec a) (post a)) ->
      forall pre, exec_correct pre (map_monad m_exec xs) (map_monad m_spec xs) (map_monad post xs).
  Proof.
    induction xs;
      intros m_exec m_spec HM pre post.

    - unfold map_monad.
      apply exec_correct_ret; auto.
    - rewrite map_monad_unfold.
      rewrite map_monad_unfold.

      eapply exec_correct_bind; eauto.
      intros * VALID POST RUN.

      eapply exec_correct_bind; eauto.
      intros * VALID2 POST2 RUN2.

      apply exec_correct_ret; auto.
  Qed.

  Lemma exec_correct_map_monad_ :
    forall {MemM Eff} `{MemMonad MemM (itree Eff)}
      {A B}
      (xs : list A)
      (m_exec : A -> MemM B) (m_spec : A -> MemPropT MemState B)
      (post : A -> exec_correct_post B),
      (forall a pre, exec_correct pre (m_exec a) (m_spec a) (post a)) ->
      forall pre, exec_correct pre (map_monad_ m_exec xs) (map_monad_ m_spec xs) (map_monad_ post xs).
  Proof.
    intros MemM Eff MM MRun SID_FRESH MPROV MSID MMS
      MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI
      MLAWS A B xs m_exec m_spec H0 pre post.
    eapply exec_correct_bind; auto.
    eapply exec_correct_map_monad; auto.
    intros * VALID POST RUN.
    apply exec_correct_ret; auto.
  Qed.

  Lemma exec_correct_map_monad_In :
    forall {MemM Eff} `{MemMonad MemM (itree Eff)}
      {A B}
      (xs : list A)
      (m_exec : forall (x : A), In x xs -> MemM B) (m_spec : forall (x : A), In x xs -> MemPropT MemState B)
      post,
      (forall a pre (IN : In a xs), exec_correct pre (m_exec a IN) (m_spec a IN) (post a IN)) ->
      forall pre, exec_correct pre (map_monad_In xs m_exec) (map_monad_In xs m_spec) (map_monad_In xs post).
  Proof.
    induction xs; intros m_exec m_spec HM pre post.
    - unfold map_monad_In.
      apply exec_correct_ret; auto.
    - rewrite map_monad_In_unfold.
      rewrite map_monad_In_unfold.

      eapply exec_correct_bind; eauto.
      intros * VALID1 POST1 RUN1.

      eapply exec_correct_bind; eauto.
      intros * VALID2 POST2 RUN2.

      apply exec_correct_ret; auto.
  Qed.

  Lemma exec_correct_raise_oom :
    forall {MemM Eff} `{MemMonad MemM (itree Eff)}
      {A} (msg : string),
    forall pre post, exec_correct pre (raise_oom msg) (raise_oom msg : MemPropT MemState A) post.
  Proof.
    intros MemM Eff MM MRun MPROV MSID MMS
      MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI
      MLAWS H A msg pre post.
    red.
    intros ms st VALID PRE.
    right.
    exists (raise_oom msg).
    exists st. exists ms.
    split.
    { (* TODO: cleaner lemma? *)
      cbn.
      red.
      exists (raise_oom msg).
      split; cbn.
      - eexists; reflexivity.
      - rewrite MemMonad_run_raise_oom.
        rewrite rbm_raise_bind; [| typeclasses eauto].
        reflexivity.
    }

    split; cbn; auto.
    intros [x CONTRA].
    inv CONTRA.
  Qed.

  Lemma exec_correct_raise_error :
    forall {MemM Eff} `{MemMonad MemM (itree Eff)}
      {A} (msg1 msg2 : string),
    forall pre post, exec_correct pre (raise_error msg1) (raise_error msg2 : MemPropT MemState A) post.
  Proof.
    intros MemM Eff MM MRun MPROV MSID MMS
      MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI
      MLAWS H A msg1 msg2 pre post.
    red.
    intros ms st VALID PRE.
    right.
    exists (raise_error msg2).
    exists st. exists ms.
    split.
    { (* TODO: cleaner lemma? *)
      cbn.
      red.
      exists (raise_error msg1).
      split; cbn.
      - eexists; reflexivity.
      - rewrite MemMonad_run_raise_error.
        rewrite rbm_raise_bind; [| typeclasses eauto].
        reflexivity.
    }

    split; cbn; auto.
    intros [x CONTRA].
    inv CONTRA.
  Qed.

  Lemma exec_correct_raise_ub :
    forall {MemM Eff} `{MemMonad MemM (itree Eff)}
      {A} (msg1 msg2 : string),
    forall pre post, exec_correct pre (raise_ub msg1) (raise_ub msg2 : MemPropT MemState A) post.
  Proof.
    intros MemM Eff MM MRun MPROV MSID MMS
      MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI
      MLAWS H A msg1 msg2 pre post.

    red.
    intros ms st VALID PRE.

    left.
    exists ms. exists msg2.
    cbn; auto.
  Qed.

  (* TODO: Move this *)
  #[global] Instance RAISE_OOM_exec_correct_post : RAISE_OOM exec_correct_post.
  split.
  intros A H.
  refine (fun ms st x ms' st' => False).
  Defined.

  (* TODO: Move this *)
  #[global] Instance RAISE_UB_exec_correct_post : RAISE_UB exec_correct_post.
  split.
  intros A H.
  refine (fun ms st x ms' st' => False).
  Defined.

  (* TODO: Move this *)
  #[global] Instance RAISE_ERROR_exec_correct_post : RAISE_ERROR exec_correct_post.
  split.
  intros A H.
  refine (fun ms st x ms' st' => True).
  Defined.

  Lemma exec_correct_lift_OOM :
    forall {MemM Eff} `{MemMonad MemM (itree Eff)}
      {A} (m : OOM A)
      (pre : exec_correct_pre),
      exec_correct pre (lift_OOM m) (lift_OOM m) (lift_OOM m).
  Proof.
    intros MemM Eff MM MRun MPROV MSID MMS
      MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI
      MLAWS H A [NOOM | OOM] pre post.
    - apply exec_correct_ret; auto.
    - apply exec_correct_raise_oom.
  Qed.

  Lemma exec_correct_lift_ERR_RAISE_ERROR :
    forall {MemM Eff} `{MemMonad MemM (itree Eff)}
      {A} (m : ERR A)
      (pre : _ -> _ -> Prop),
      exec_correct pre (lift_ERR_RAISE_ERROR m) (lift_ERR_RAISE_ERROR m) (lift_ERR_RAISE_ERROR m).
  Proof.
    intros MemM Eff MM MRun MPROV MSID MMS
      MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI
      MLAWS H A [[ERR] | NOERR] pre.
    - apply exec_correct_raise_error; auto.
    - cbn.
      repeat red.
      intros ms st H0 H1.
      right.
      exists (ret NOERR), st, ms.
      cbn; split; eauto.
      repeat red.
      cbn.
      exists (ret NOERR).
      split.
      reflexivity.
      rewrite MemMonad_run_ret.
      rewrite bind_ret_l.
      reflexivity.
      split; eauto.
      intros (?&?).
      inv H2.
      split; eauto.
      exists x.
      split; eauto.
      red; auto.
  Qed.

  Lemma exec_correct_lift_err_RAISE_ERROR :
    forall {MemM Eff} `{MemMonad MemM (itree Eff)}
      {A} (m : err A)
      (pre : _ -> _ -> Prop),
      exec_correct pre (lift_err_RAISE_ERROR m) (lift_err_RAISE_ERROR m) (lift_err_RAISE_ERROR m).
  Proof.
    intros MemM Eff MM MRun MPROV MSID MMS
      MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI
      MLAWS H A [ERR | NOERR] pre.
    - apply exec_correct_raise_error; auto.
    - repeat red.
      intros ms st H0 H1.
      right.
      exists (ret NOERR), st, ms.
      cbn; split; eauto.
      repeat red.
      cbn.
      exists (ret NOERR).
      split.
      reflexivity.
      rewrite MemMonad_run_ret.
      rewrite bind_ret_l.
      reflexivity.
      split; eauto.
      intros (?&?).
      inv H2.
      split; eauto.
      exists x.
      split; eauto.
      red; auto.
  Qed.

  Definition get_consecutive_ptrs_post len : exec_correct_post (list ADDR.addr) :=
    (fun ms st addrs ms' st' =>
           length addrs = len /\ ms = ms' /\ st = st').
  #[global] Hint Unfold get_consecutive_ptrs_post : core.

  Definition intptr_seq_post len : exec_correct_post (list IP.intptr) :=
    (fun ms st ips ms' st' => length ips = len /\ ms = ms' /\ st = st').
  #[global] Hint Unfold intptr_seq_post : core.

  Lemma exec_correct_get_consecutive_pointers :
    forall {MemM Eff} `{MemMonad MemM (itree Eff)}
      len ptr,
    forall pre,
      exec_correct
        pre
        (get_consecutive_ptrs ptr len)
        (get_consecutive_ptrs ptr len)
        (get_consecutive_ptrs ptr len).
  Proof.
    intros MemM Eff MM MRun MPROV MSID MMS
      MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI
      MLAWS H len ptr pre.
    unfold get_consecutive_ptrs.

    eapply exec_correct_bind.
    apply exec_correct_lift_OOM.

    intros a ms_init ms_after_m st_init st_after_m H0 H1 H2 WEM.
    unfold lift_OOM in H1.
    break_match_hyp_inv.
    destruct H4 as (?&?); subst.

    eapply exec_correct_bind.
    apply exec_correct_lift_err_RAISE_ERROR.

    intros * VALID POST RUN.
    apply exec_correct_lift_OOM.
  Qed.

  Lemma exec_correct_fresh_sid :
    forall {MemM Eff} `{MemMonad MemM (itree Eff)} pre,
      exec_correct pre fresh_sid fresh_sid fresh_sid.
  Proof.
    red.
    intros MemM Eff MM MRun MPROV MSID MMS
      MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI
      MLAWS H pre ms st H0 PRE.
    right.
    eapply (@MemMonad_run_fresh_sid MemM) in H0 as [st' [sid [EUTT [VALID [LT [NEW_ST FRESH]]]]]].
    exists (ret sid), st', ms.
    split; [| split]; auto.
    { cbn.
      red.
      exists (ret sid).
      split; cbn.
      - reflexivity.
      - rewrite EUTT, bind_ret_l.
        reflexivity.
    }
    2: {
      intros [x RET].
      inv RET.
      split; eauto.
      exists x.
      split; eauto.
      red; cbn.
      split; eauto.
    }

    cbn.
    split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]];
      try solve [red; reflexivity].
    - unfold fresh_store_id. auto.
    - unfold read_byte_preserved.
      split; red; reflexivity.
  Qed.

  Section Correctness.
    Context {MemM : Type -> Type}.
    Context {Eff : Type -> Type}.
    Context `{MM : MemMonad MemM (itree Eff)}.

    Import Monad.

    (* TODO: move this? *)
    Lemma byte_allocated_mem_eq :
      forall ms ms' ptr aid,
        byte_allocated ms ptr aid ->
        MemState_get_memory ms = MemState_get_memory ms' ->
        byte_allocated ms' ptr aid.
    Proof using Type.
      intros ms ms' ptr aid ALLOC EQ.
      unfold byte_allocated.
      cbn in *.
      red in ALLOC.
      rewrite <- EQ.
      auto.
    Qed.

    (* TODO: move this? *)
    Lemma read_byte_allowed_mem_eq :
      forall ms ms' ptr,
        read_byte_allowed ms ptr ->
        MemState_get_memory ms = MemState_get_memory ms' ->
        read_byte_allowed ms' ptr.
    Proof using Type.
      intros ms ms' ptr READ EQ.
      unfold read_byte_allowed in *.
      destruct READ as [aid [ALLOC ACCESS]].
      exists aid; split; auto.
      eapply byte_allocated_mem_eq; eauto.
    Qed.

    Lemma write_byte_allowed_mem_eq :
      forall ms ms' ptr,
        write_byte_allowed ms ptr ->
        MemState_get_memory ms = MemState_get_memory ms' ->
        write_byte_allowed ms' ptr.
    Proof using Type.
      intros ms ms' ptr WRITE EQ.
      unfold write_byte_allowed in *.
      destruct WRITE as [aid [ALLOC ACCESS]].
      exists aid; split; auto.
      eapply byte_allocated_mem_eq; eauto.
    Qed.

    Lemma free_byte_allowed_mem_eq :
      forall ms ms' ptr,
        free_byte_allowed ms ptr ->
        MemState_get_memory ms = MemState_get_memory ms' ->
        free_byte_allowed ms' ptr.
    Proof using Type.
      intros ms ms' ptr FREE EQ.
      unfold free_byte_allowed in *.
      destruct FREE as [aid [ALLOC ACCESS]].
      exists aid; split; auto.
      eapply byte_allocated_mem_eq; eauto.
    Qed.

    (* TODO: move this? *)
    Lemma read_byte_prop_mem_eq :
      forall ms ms' ptr byte,
        read_byte_prop ms ptr byte ->
        MemState_get_memory ms = MemState_get_memory ms' ->
        read_byte_prop ms' ptr byte.
    Proof using Type.
      intros ms ms' ptr byte READ EQ.
      unfold read_byte_prop.
      rewrite <- EQ.
      auto.
    Qed.

    Lemma read_byte_preserved_mem_eq :
      forall ms ms',
        MemState_get_memory ms = MemState_get_memory ms' ->
        read_byte_preserved ms ms'.
    Proof using Type.
      unfold read_byte_preserved.
      split; red.
      + intros ptr; split; intros READ_ALLOWED;
          eapply read_byte_allowed_mem_eq; eauto.
      + intros ptr byte; split; intros READ_ALLOWED;
          eapply read_byte_prop_mem_eq; eauto.
    Qed.

    Lemma write_byte_allowed_all_preserved_mem_eq :
      forall ms ms',
        MemState_get_memory ms = MemState_get_memory ms' ->
        write_byte_allowed_all_preserved ms ms'.
    Proof using Type.
      intros ms ms' EQ.
      unfold write_byte_allowed_all_preserved.
      intros ptr.
      split; red;
        intros WRITE_ALLOWED;
        eapply write_byte_allowed_mem_eq; eauto.
    Qed.

    Lemma free_byte_allowed_all_preserved_mem_eq :
      forall ms ms',
        MemState_get_memory ms = MemState_get_memory ms' ->
        free_byte_allowed_all_preserved ms ms'.
    Proof using Type.
      intros ms ms' EQ.
      unfold free_byte_allowed_all_preserved.
      intros ptr.
      split; red;
        intros FREE_ALLOWED;
        eapply free_byte_allowed_mem_eq; eauto.
    Qed.

    Lemma allocations_preserved_mem_eq :
      forall ms ms',
        MemState_get_memory ms = MemState_get_memory ms' ->
        allocations_preserved ms ms'.
    Proof using Type.
      intros ms ms' EQ.
      unfold write_byte_allowed_all_preserved.
      intros ptr aid.
      split; intros ALLOC; eapply byte_allocated_mem_eq; eauto.
    Qed.

    Lemma frame_stack_preserved_mem_eq :
      forall ms ms',
        MemState_get_memory ms = MemState_get_memory ms' ->
        frame_stack_preserved ms ms'.
    Proof using Type.
      intros ms ms' EQ.
      unfold frame_stack_preserved.
      intros fs.
      split; intros FS; [rewrite <- EQ | rewrite EQ]; eauto.
    Qed.

    #[global] Instance Proper_heap_preserved :
      Proper ((fun ms1 ms2 => MemState_get_memory ms1 = MemState_get_memory ms2) ==> (fun ms1 ms2 => MemState_get_memory ms1 = MemState_get_memory ms2) ==> iff) heap_preserved.
    Proof using Type.
      unfold Proper, respectful.
      intros x y H x0 y0 H0.
      unfold heap_preserved.
      rewrite H, H0.
      reflexivity.
    Qed.

    #[global] Instance Reflexive_heap_preserved : Reflexive heap_preserved.
    Proof using Type.
      unfold Reflexive.
      intros x.
      unfold heap_preserved.
      reflexivity.
    Qed.

    Lemma exec_correct_fresh_provenance :
      forall pre, exec_correct pre fresh_provenance fresh_provenance fresh_provenance.
    Proof using Type.
      red.
      intros pre ms st H PRE.
      right.
      eapply (@MemMonad_run_fresh_provenance MemM) in H as [ms' [pr [EUTT [VALID [MEM FRESH]]]]].
      exists (ret pr), st, ms'.
      split; [| split]; auto.
      { cbn.
        red.
        exists (ret pr).
        split; cbn.
        - reflexivity.
        - rewrite EUTT, bind_ret_l.
          reflexivity.
      }
      2: {
        intros [x RET].
        inv RET.
        split; eauto.
        exists x.
        split; eauto.
        cbn.
        split; [|split;[|split]]; eauto; apply FRESH.
      }

      cbn.
      split; [| split; [| split; [| split; [| split; [| split]]]]];
        try solve [red; reflexivity].
      - unfold extend_provenance. tauto.
      - eapply read_byte_preserved_mem_eq; eauto.
      - eapply write_byte_allowed_all_preserved_mem_eq; eauto.
      - eapply free_byte_allowed_all_preserved_mem_eq; eauto.
      - eapply allocations_preserved_mem_eq; eauto.
      - eapply frame_stack_preserved_mem_eq; eauto.
      - unfold ms_get_memory in MEM; cbn in MEM. eapply Proper_heap_preserved; eauto.
        reflexivity.
    Qed.
  End Correctness.

  Hint Resolve exec_correct_ret : EXEC_CORRECT.
  Hint Resolve exec_correct_bind : EXEC_CORRECT.
  Hint Resolve exec_correct_fresh_sid : EXEC_CORRECT.
  Hint Resolve exec_correct_lift_err_RAISE_ERROR : EXEC_CORRECT.
  Hint Resolve exec_correct_lift_ERR_RAISE_ERROR : EXEC_CORRECT.
  Hint Resolve exec_correct_lift_OOM : EXEC_CORRECT.
  Hint Resolve exec_correct_raise_error : EXEC_CORRECT.
  Hint Resolve exec_correct_raise_oom : EXEC_CORRECT.
  Hint Resolve exec_correct_raise_ub : EXEC_CORRECT.
  Hint Resolve exec_correct_map_monad : EXEC_CORRECT.
  Hint Resolve exec_correct_map_monad_ : EXEC_CORRECT.
  Hint Resolve exec_correct_map_monad_In : EXEC_CORRECT.
  Hint Resolve exec_correct_fresh_provenance : EXEC_CORRECT.

End MemoryExecMonad.

Module MakeMemoryExecMonad (LP : LLVMParams) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) (MMS : MemoryModelSpec LP MP MMSP) <: MemoryExecMonad LP MP MMSP MMS.
  Include MemoryExecMonad LP MP MMSP MMS.
End MakeMemoryExecMonad.

Module Type MemoryModelExecPrimitives (LP : LLVMParams) (MP : MemoryParams LP).
  Import LP.
  Import LP.ADDR.
  Import LP.SIZEOF.
  Import LP.PROV.
  Import MP.

  (** Specification of the memory model *)
  Declare Module MMSP : MemoryModelSpecPrimitives LP MP.
  Import MMSP.
  Import MMSP.MemByte.

  Module MemSpec := MakeMemoryModelSpec LP MP MMSP.
  Import MemSpec.

  Module MemExecM := MakeMemoryExecMonad LP MP MMSP MemSpec.
  Import MemExecM.

  Section MemoryPrimitives.
    Context {MemM : Type -> Type}.
    Context {Eff : Type -> Type}.
    Context `{MM : MemMonad MemM (itree Eff)}.

    (*** Data types *)
    Parameter initial_frame : Frame.
    Parameter initial_heap : Heap.

    (*** Primitives on memory *)
    (** Reads *)
    Parameter read_byte :
      forall `{MemMonad MemM (itree Eff)}, addr -> MemM SByte.

    (** Writes *)
    Parameter write_byte :
      forall `{MemMonad MemM (itree Eff)}, addr -> SByte -> MemM unit.

    (** Stack allocations *)
    Parameter allocate_bytes_with_pr :
      forall `{MemMonad MemM (itree Eff)}, list SByte -> Provenance -> MemM addr.

    (** Frame stacks *)
    Parameter mempush : forall `{MemMonad MemM (itree Eff)}, MemM unit.
    Parameter mempop : forall `{MemMonad MemM (itree Eff)}, MemM unit.

    (** Heap operations *)
    Parameter malloc_bytes_with_pr :
      forall `{MemMonad MemM (itree Eff)}, list SByte -> Provenance -> MemM addr.

    Parameter free :
      forall `{MemMonad MemM (itree Eff)}, addr -> MemM unit.

    (*** Correctness *)

    (** Correctness of the main operations on memory *)
    Parameter read_byte_correct :
      forall ptr pre,
        exec_correct pre (read_byte ptr) (read_byte_spec_MemPropT ptr)
          (fun ms st byte ms' st' => (exists s, MemByte.sbyte_sid byte = inr s /\ s < st) /\ ms = ms' /\ st = st').

    Parameter write_byte_correct :
      forall ptr byte,
        exec_correct
          (fun ms st => exists s, sbyte_sid byte = inr s /\ (s < st)%N)
          (write_byte ptr byte) (write_byte_spec_MemPropT ptr byte)
          (fun _ st _ _ st' => st = st').

    Parameter write_byte_preserves_store_id :
      forall st ms a b st' ms' res,
        @within MemM EQM err_ub_oom (prod store_id MemState) (prod store_id MemState)
          (@Within_err_ub_oom_MemM MemM Eff
             (@MemMonad_eq1_runm MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB
                RunOOM EQM EQRI MLAWS MM) MRun
             (@MemMonad_eq1_runm_equiv MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM RunERR
                RunUB RunOOM EQM EQRI MLAWS MM) RunERR RunUB RunOOM MM0 MRun MPROV MSID MMS MERR MUB
             MOOM RunERR RunUB RunOOM EQM EQRI MLAWS MM) unit
          (write_byte a b) (@pair store_id MemState st ms)
          (@ret err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) unit res)
          (@pair store_id MemState st' ms') ->
        st = st'.

    Parameter allocate_bytes_with_pr_correct :
      forall init_bytes pr,
        exec_correct
          (fun ms st =>
             Forall (fun b : SByte => exists s : store_id, sbyte_sid b = inr s /\ (s < st)%N) init_bytes)
          (allocate_bytes_with_pr init_bytes pr)
          (allocate_bytes_with_pr_spec_MemPropT init_bytes pr)
          exec_correct_id_post.

    (** Correctness of frame stack operations *)
    Parameter mempush_correct :
      forall pre, exec_correct pre mempush mempush_spec_MemPropT exec_correct_id_post.

    Parameter mempop_correct :
      forall pre, exec_correct pre mempop mempop_spec_MemPropT exec_correct_id_post.

    Parameter malloc_bytes_with_pr_correct :
      forall init_bytes pr,
        exec_correct
          (fun ms st =>
             Forall (fun b : SByte => exists s : store_id, sbyte_sid b = inr s /\ (s < st)%N) init_bytes)
          (malloc_bytes_with_pr init_bytes pr) (malloc_bytes_with_pr_spec_MemPropT init_bytes pr)
          exec_correct_id_post.

    Parameter free_correct :
      forall ptr pre,
        exec_correct pre (free ptr) (free_spec_MemPropT ptr) exec_correct_id_post.

    (*** Initial memory state *)
    Record initial_memory_state_prop : Prop :=
      {
        initial_memory_no_allocations :
        forall ptr aid,
          ~ byte_allocated initial_memory_state ptr aid;

        initial_memory_frame_stack :
        forall fs,
          memory_stack_frame_stack_prop (MemState_get_memory initial_memory_state) fs ->
          empty_frame_stack fs;

        initial_memory_heap :
        forall h,
          memory_stack_heap_prop (MemState_get_memory initial_memory_state) h ->
          empty_heap h;

        initial_memory_read_ub :
        forall ptr byte,
          ~ read_byte_prop initial_memory_state ptr byte
      }.

    Record initial_frame_prop : Prop :=
      {
        initial_frame_is_empty : empty_frame initial_frame;
      }.

    Record initial_heap_prop : Prop :=
      {
        initial_heap_is_empty : empty_heap initial_heap;
      }.

    Parameter initial_memory_state_correct : initial_memory_state_prop.
    Parameter initial_frame_correct : initial_frame_prop.
    Parameter initial_heap_correct : initial_heap_prop.
  End MemoryPrimitives.
End MemoryModelExecPrimitives.

Module Type MemoryModelExec (LP : LLVMParams) (MP : MemoryParams LP) (MMEP : MemoryModelExecPrimitives LP MP).
  Import LP.
  Import LP.ADDR.
  Import LP.SIZEOF.
  Import LP.PROV.
  Import LP.PTOI.
  Import LP.Events.
  Import MP.
  Import MMEP.
  Import MemExecM.
  Import MMSP.
  Import MMSP.MemByte.
  Import MMEP.MemSpec.
  Import MemHelpers.

  Module OVER := PTOIOverlaps ADDR PTOI SIZEOF.
  Import OVER.
  Module OVER_H := OverlapHelpers ADDR SIZEOF OVER.
  Import OVER_H.

  (*** Handling memory events *)
  Section Handlers.
    Context {MemM : Type -> Type}.
    Context {Eff : Type -> Type}.
    Context `{MM : MemMonad MemM (itree Eff)}.

    (** Reading uvalues *)
    Definition read_bytes `{MemMonad MemM (itree Eff)} (ptr : addr) (len : nat) : MemM (list SByte) :=
      (* TODO: this should maybe be UB and not OOM??? *)
      ptrs <- get_consecutive_ptrs ptr len;;

      (* Actually perform reads *)
      map_monad (fun ptr => read_byte ptr) ptrs.

    Definition read_uvalue `{MemMonad MemM (itree Eff)} (dt : dtyp) (ptr : addr) : MemM uvalue :=
      bytes <- read_bytes ptr (N.to_nat (sizeof_dtyp dt));;
      lift_err_RAISE_ERROR (deserialize_sbytes bytes dt).

    (** Writing uvalues *)
    Definition write_bytes `{MemMonad MemM (itree Eff)} (ptr : addr) (bytes : list SByte) : MemM unit :=
      (* TODO: Should this be UB instead of OOM? *)
      ptrs <- get_consecutive_ptrs ptr (length bytes);;
      let ptr_bytes := zip ptrs bytes in

      (* Actually perform writes *)
      map_monad_ (fun '(ptr, byte) => write_byte ptr byte) ptr_bytes.

    Definition write_uvalue `{MemMonad MemM (itree Eff)} (dt : dtyp) (ptr : addr) (uv : uvalue) : MemM unit :=
      bytes <- serialize_sbytes uv dt;;
      write_bytes ptr bytes.

    (** Allocating dtyps *)
    Definition allocate_bytes `{MemMonad MemM (itree Eff)}
      (init_bytes : list SByte)
      : MemM addr
      := pr <- fresh_provenance;;
         allocate_bytes_with_pr init_bytes pr.

    (* Need to make sure MemPropT has provenance and sids to generate the bytes. *)
    Definition allocate_dtyp `{MemMonad MemM (itree Eff)}
      (dt : dtyp) (num_elements : N)
      : MemM addr
      :=
      if dtyp_eqb dt DTYPE_Void
      then raise_ub "allocating void type"
      else sid <- fresh_sid;;
           element_bytes <- repeatMN num_elements (lift_OOM (generate_undef_bytes dt sid));;
           let bytes := concat element_bytes in
           allocate_bytes bytes.

    (** Malloc *)
    Definition malloc_bytes `{MemMonad MemM (itree Eff)} (init_bytes : list SByte) : MemM addr :=
      pr <- fresh_provenance;;
      malloc_bytes_with_pr init_bytes pr.

    (** Handle memcpy *)
    Definition memcpy `{MemMonad MemM (itree Eff)} (src dst : addr) (len : Z) (volatile : bool) : MemM unit :=
      if Z.ltb len 0
      then
        raise_ub "memcpy given negative length."
      else
        (* From LangRef: The ‘llvm.memcpy.*’ intrinsics copy a block of
       memory from the source location to the destination location, which
       must either be equal or non-overlapping.
         *)
        if orb (no_overlap dst len src len)
               (Z.eqb (ptr_to_int src) (ptr_to_int dst))
        then
          src_bytes <- read_bytes src (Z.to_nat len);;

          (* TODO: Double check that this is correct... Should we check if all writes are allowed first? *)
          write_bytes dst src_bytes
        else
          raise_ub "memcpy with overlapping or non-equal src and dst memory locations.".

    (** memset spec *)
    Definition memset `{MemMonad MemM (itree Eff)}
      (dst : addr) (val : int8) (len : Z) (sid : store_id) (volatile : bool) : MemM unit :=
      if Z.ltb len 0
      then
        raise_ub "memset given negative length."
      else
        let byte := uvalue_sbyte (UVALUE_I8 val) (DTYPE_I 8) 0 sid in
        write_bytes dst (repeatN (Z.to_N len) byte).

    Definition handle_memory `{MemMonad MemM (itree Eff)} : MemoryE ~> MemM
      := fun T m =>
           match m with
           (* Unimplemented *)
           | MemPush =>
               mempush
           | MemPop =>
               mempop
           | Alloca t num_elements align =>
               addr <- allocate_dtyp t num_elements;;
               ret (DVALUE_Addr addr)
           | Load t a =>
               match a with
               | DVALUE_Addr a =>
                   read_uvalue t a
               | _ =>
                   raise_ub "Loading from something that is not an address."
               end
           | Store t a v =>
               match a with
               | DVALUE_Addr a =>
                   write_uvalue t a v
               | _ =>
                   raise_ub "Store to somewhere that is not an address."
               end
           end.

    Definition handle_memcpy `{MemMonad MemM (itree Eff)} (args : list dvalue) : MemM unit :=
      match args with
      | DVALUE_Addr dst ::
                    DVALUE_Addr src ::
                    DVALUE_I32 len ::
                    DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          memcpy src dst (unsigned len) (equ volatile VellvmIntegers.one)
      | DVALUE_Addr dst ::
                    DVALUE_Addr src ::
                    DVALUE_I64 len ::
                    DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          memcpy src dst (unsigned len) (equ volatile VellvmIntegers.one)
      | DVALUE_Addr dst ::
                    DVALUE_Addr src ::
                    DVALUE_IPTR len ::
                    DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          memcpy src dst (IP.to_Z len) (equ volatile VellvmIntegers.one)
      | _ => raise_error "Unsupported arguments to memcpy."
      end.

    Definition handle_memset `{MemMonad MemM (itree Eff)} (args : list dvalue) : MemM unit :=
      match args with
      | DVALUE_Addr dst ::
          DVALUE_I8 val ::
          DVALUE_I32 len ::
          DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          sid <- fresh_sid;;
          memset dst val (unsigned len) sid (equ volatile VellvmIntegers.one)
      | DVALUE_Addr dst ::
          DVALUE_I8 val ::
          DVALUE_I64 len ::
          DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          sid <- fresh_sid;;
          memset dst val (unsigned len) sid (equ volatile VellvmIntegers.one)
      | _ => raise_error "Unsupported arguments to memset."
      end.

    Definition handle_malloc `{MemMonad MemM (itree Eff)} (args : list dvalue) : MemM addr :=
      match args with
      | [DVALUE_I1 sz]
      | [DVALUE_I8 sz]
      | [DVALUE_I16 sz]
      | [DVALUE_I32 sz]
      | [DVALUE_I64 sz] =>
          sid <- fresh_sid;;
          bytes <- lift_OOM (generate_num_undef_bytes (Z.to_N (unsigned sz)) (DTYPE_I 8) sid);;
          malloc_bytes bytes
      | [DVALUE_IPTR sz] =>
          sid <- fresh_sid;;
          bytes <- lift_OOM (generate_num_undef_bytes (Z.to_N (IP.to_unsigned sz)) (DTYPE_I 8) sid);;
          malloc_bytes bytes
      | _ => raise_error "Malloc: invalid arguments."
      end.

    Definition handle_free `{MemMonad MemM (itree Eff)} (args : list dvalue) : MemM unit :=
      match args with
      | [DVALUE_Addr ptr] =>
          free ptr
      | _ => raise_error "Free: invalid arguments."
      end.

    Definition handle_intrinsic `{MemMonad MemM (itree Eff)} : IntrinsicE ~> MemM
      := fun T e =>
           match e with
           | Intrinsic t name args =>
               (* Pick all arguments, they should all be unique. *)
               (* TODO: add more variants to memcpy *)
               (* FIXME: use reldec typeclass? *)
               if orb (Coqlib.proj_sumbool (string_dec name "llvm.memcpy.p0i8.p0i8.i32"))
                      (Coqlib.proj_sumbool (string_dec name "llvm.memcpy.p0i8.p0i8.i64"))
               then
                 handle_memcpy args;;
                 ret DVALUE_None
               else
                 if orb (Coqlib.proj_sumbool (string_dec name "llvm.memset.p0i8.i32"))
                      (Coqlib.proj_sumbool (string_dec name "llvm.memset.p0i8.i64"))
                 then
                   handle_memset args;;
                   ret DVALUE_None
                 else
                   if (Coqlib.proj_sumbool (string_dec name "malloc"))
                   then
                     addr <- handle_malloc args;;
                     ret (DVALUE_Addr addr)
                   else
                     if (Coqlib.proj_sumbool (string_dec name "free"))
                     then
                       handle_free args;;
                       ret DVALUE_None
                     else
                       raise_error ("Unknown intrinsic: " ++ name)
           end.

  End Handlers.
End MemoryModelExec.

Module MakeMemoryModelExec (LP : LLVMParams) (MP : MemoryParams LP) (MMEP : MemoryModelExecPrimitives LP MP) <: MemoryModelExec LP MP MMEP.
  Include MemoryModelExec LP MP MMEP.
End MakeMemoryModelExec.

Module MemoryModelTheory (LP : LLVMParams) (MP : MemoryParams LP) (MMEP : MemoryModelExecPrimitives LP MP) (MME : MemoryModelExec LP MP MMEP).
  Import MMEP.
  Import MME.
  Import MemSpec.
  Import MMSP.
  Import MemExecM.
  Import MemHelpers.
  Import LP.Events.

  (* TODO: move this *)
  Lemma zip_cons :
    forall {A B} (x : A) (y : B) xs ys,
      zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys.
  Proof.
    reflexivity.
  Qed.

  Section Correctness.
    Context {MemM : Type -> Type}.
    Context {Eff : Type -> Type}.
    Context `{MM : MemMonad MemM (itree Eff)}.

    Import Monad.

    Lemma exec_correct_re_sid_ubytes_helper :
      forall bytes pre nm,
        exec_correct pre
                     (re_sid_ubytes_helper bytes nm)
                     (re_sid_ubytes_helper bytes nm)
                     (re_sid_ubytes_helper bytes nm).
    Proof using Type.
      intros bytes.
      induction bytes using length_strong_ind; intros pre nm.
      - apply exec_correct_ret; auto.
      - repeat rewrite re_sid_ubytes_helper_equation.
        break_match_goal; auto with EXEC_CORRECT.
        break_match_goal; auto with EXEC_CORRECT.
        break_match_goal; auto with EXEC_CORRECT.
        break_match_goal; auto with EXEC_CORRECT.
        eapply exec_correct_bind; auto with EXEC_CORRECT.
        intros a0.
        intros ms_init ms_after_m st_init st_after_m VALID_FRESH POST_FRESH RUN_FRESH_SID.
        apply H.
        subst.

        cbn in H0.
        apply filter_split_out_length in Heqp1.
        lia.
    Qed.

    Hint Resolve exec_correct_re_sid_ubytes_helper : EXEC_CORRECT.

    Lemma exec_correct_trywith_error :
      forall {A} msg1 msg2 (ma : option A) pre,
        exec_correct pre
                     (trywith_error msg1 ma)
                     (trywith_error msg2 ma)
                     (trywith_error msg2 ma).
    Proof using Type.
      intros A msg1 msg2 [a |] pre;
        unfold trywith_error;
        auto with EXEC_CORRECT.
    Qed.

    Hint Resolve exec_correct_trywith_error : EXEC_CORRECT.

    Lemma exec_correct_re_sid_ubytes :
      forall bytes pre,
        exec_correct pre (re_sid_ubytes bytes) (re_sid_ubytes bytes)
                     (re_sid_ubytes bytes).
    Proof using Type.
      intros bytes pre.
      eapply exec_correct_bind; auto with EXEC_CORRECT.
    Qed.

    Hint Resolve exec_correct_re_sid_ubytes : EXEC_CORRECT.

    Lemma dtyp_measure_strong_ind:
      forall (P : dtyp -> Prop)
        (BASE: forall dt, dtyp_measure dt = 1%nat -> P dt)
        (IH: forall (n : nat) (dt: dtyp), (forall (dt : dtyp), dtyp_measure dt <= n -> P dt)%nat -> dtyp_measure dt = S n -> P dt),
      forall dt, P dt.
    Proof using Type.
      intros P BASE IH.
      assert (forall n dt, dtyp_measure dt <= n -> P dt)%nat as IHDT.
      { induction n using nat_strong_ind; intros dt SIZE.
        - destruct dt; cbn in SIZE; lia.
        - assert (dtyp_measure dt <= n \/ dtyp_measure dt = S n)%nat as [LEQ | EQ] by lia;
          eauto.
      }

      intros dt.
      eapply IHDT.
      reflexivity.
    Qed.


    Lemma exec_correct_serialize_by_dtyp_undef :
      forall dt CTR pre,
        exec_correct pre (serialize_by_dtyp CTR dt) (serialize_by_dtyp CTR dt) (serialize_by_dtyp CTR dt).
    Proof using Type.
      induction dt; intros;
        try solve [
            eapply exec_correct_bind; auto with EXEC_CORRECT
          ].

      - eapply exec_correct_bind; auto with EXEC_CORRECT.
        do 3 rewrite map_monad_map_monad_In.
        apply exec_correct_map_monad_In.
        intros.
        apply H.
        assumption.

      - eapply exec_correct_bind; auto with EXEC_CORRECT.
        do 3 rewrite map_monad_map_monad_In.
        apply exec_correct_map_monad_In.
        intros.
        apply H.
        assumption.
    Qed.

    Lemma exec_correct_serialize_sbytes_undef :
      forall dt t pre,
        exec_correct pre (serialize_sbytes (UVALUE_Undef t) dt) (serialize_sbytes (UVALUE_Undef t) dt) (serialize_sbytes (UVALUE_Undef t) dt).
    Proof using Type.
      intros.
      unfold serialize_sbytes.
      eauto with EXEC_CORRECT.
    Qed.

    Hint Resolve exec_correct_serialize_sbytes_undef : EXEC_CORRECT.

    Lemma exec_correct_serialize_sbytes_poison :
      forall dt t pre,
        exec_correct pre (serialize_sbytes (UVALUE_Poison t) dt) (serialize_sbytes (UVALUE_Poison t) dt) (serialize_sbytes (UVALUE_Poison t) dt).
    Proof using Type.
      intros.
      unfold serialize_sbytes.
      eauto with EXEC_CORRECT.
    Qed.

    Hint Resolve exec_correct_serialize_sbytes_poison : EXEC_CORRECT.

    Lemma exec_correct_serialize_sbytes_oom :
      forall dt t pre,
        exec_correct pre (serialize_sbytes (UVALUE_Oom t) dt) (serialize_sbytes (UVALUE_Oom t) dt) (serialize_sbytes (UVALUE_Oom t) dt).
    Proof using Type.
      intros.
      unfold serialize_sbytes.
      eauto with EXEC_CORRECT.
    Qed.

    Hint Resolve exec_correct_serialize_sbytes_oom : EXEC_CORRECT.


    Lemma exec_correct_pre_map_monad2 :
      forall {A B C}
        (f : forall {M : Type -> Type} {HM: Monad M} {HS:MonadStoreId M} {HR: RAISE_ERROR M} {HO: RAISE_OOM M}, A -> B -> M C)
        (pre : MemState -> store_id -> Prop) (l1 : list A) (l2: list B)
        (H : forall a, In a l1 -> forall b (pre : MemState -> store_id -> Prop), exec_correct pre (f a b) (f a b) (f a b)),
        exec_correct pre (map_monad2 f l1 l2) (map_monad2 f l1 l2) (map_monad2 f l1 l2).
    Proof using Type.
      intros.
      revert pre l2 H.
      induction l1.
      - intros.
        destruct l2.
        + apply exec_correct_ret; eauto.
        + apply exec_correct_raise_error.
      - intros.
        destruct l2.
        + apply exec_correct_raise_error.
        + apply exec_correct_bind.
          * eapply H. left. auto.
          * intros.
            eapply exec_correct_bind.
            -- apply IHl1.
               intros.
               apply H. right.  auto.
            -- intros.
               apply exec_correct_ret; auto.
    Qed.

    Lemma exec_correct_serialize_sbytes :
      forall uv dt pre,
        exec_correct pre (serialize_sbytes uv dt) (serialize_sbytes uv dt) (serialize_sbytes uv dt).
    Proof using Type.
      induction uv; intros dt' pre;
        try solve [
            auto with EXEC_CORRECT
          | eapply exec_correct_bind; eauto with EXEC_CORRECT
          ].
    Qed.

    Lemma read_bytes_correct :
      forall len ptr pre,
        exec_correct pre (read_bytes ptr len) (read_bytes_spec ptr len)
          (@get_consecutive_ptrs exec_correct_post Monad_exec_correct_post RAISE_OOM_exec_correct_post RAISE_ERROR_exec_correct_post ptr len;;
           (fun ms st bytes ms' st' =>
              (Forall (fun byte => exists s, MemByte.sbyte_sid byte = inr s /\ s < st) bytes /\ ms = ms' /\ st = st'))).
    Proof using Type.
      unfold read_bytes.
      unfold read_bytes_spec.
      intros len ptr pre.
      eapply exec_correct_bind.
      eapply exec_correct_get_consecutive_pointers.

      intros * VALID POST RUN.
      eapply exec_correct_strengthen_post; cycle 1.
      eapply exec_correct_map_monad.
      intros ptr'.
      apply read_byte_correct.

      clear.
      intros ms st a0 ms' st' _ MAP.
      generalize dependent a0.
      revert ms st ms' st'.
      induction a; intros ms st ms' st' bytes MAP.
      - cbn in *.
        destruct MAP as (?&?&?); subst.
        split; auto.
      - rewrite map_monad_unfold in MAP.
        destruct MAP as (?&?&?&?&?&?&?&?&?).
        cbn in *.
        red in H1.
        destruct H1 as (?&?&?); subst.
        destruct H as (?&?&?); subst.
        eapply IHa in H0.
        destruct H0 as (?&?&?); subst.
        split; auto.
    Qed.

    Lemma read_uvalue_correct :
      forall dt ptr pre,
        exec_correct pre (read_uvalue dt ptr) (read_uvalue_spec dt ptr)
          (a0 <-
             (_ <- get_consecutive_ptrs ptr (N.to_nat (LP.SIZEOF.sizeof_dtyp dt));;
              (fun (ms0 : MemState) (st0 : store_id) (bytes : list MP.BYTE_IMPL.SByte) 
                 (ms'0 : MemState) (st'0 : store_id) =>
                 Forall
                   (fun byte : MP.BYTE_IMPL.SByte =>
                      exists s : store_id, MemByte.sbyte_sid byte = inr s /\ s < st0) bytes /\
                   ms0 = ms'0 /\ st0 = st'0));;
           (fun a1 : list MP.BYTE_IMPL.SByte => lift_err_RAISE_ERROR (deserialize_sbytes a1 dt)) a0).
    Proof using Type.
      intros dt ptr pre.
      eapply exec_correct_bind.
      apply read_bytes_correct.
      intros * VALID POST RUN.
      apply exec_correct_lift_err_RAISE_ERROR; auto.
    Qed.

    (* TODO: move this? *)
    Import MP.
    Import LP.
    Import GEP.
    Lemma MemMonad_run_get_consecutive_ptrs:
      forall {M RunM : Type -> Type} {MM : Monad M} {MRun : Monad RunM}
        {MPROV : MonadProvenance LP.PROV.Provenance M} {MSID : MonadStoreId M} {MMS : MonadMemState MemState M}
        {MERR : RAISE_ERROR M} {MUB : RAISE_UB M} {MOOM : RAISE_OOM M} {RunERR : RAISE_ERROR RunM}
        {RunUB : RAISE_UB RunM} {RunOOM : RAISE_OOM RunM}
        `{EQM : Eq1 M} `{EQRI : @Eq1_ret_inv M EQM MM} `{MLAWS : @MonadLawsE M EQM MM}
        {MemMonad : MemMonad M RunM}
        `{EQV : @Eq1Equivalence RunM MRun (@MemMonad_eq1_runm M RunM MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM _ _ _ MemMonad)}
        `{LAWS: @MonadLawsE RunM (@MemMonad_eq1_runm M RunM MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM _ _ _ MemMonad) MRun}
        `{RAISEOOM : @RaiseBindM RunM MRun (@MemMonad_eq1_runm M RunM MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM _ _ _ MemMonad) string (@raise_oom RunM RunOOM)}
        `{RAISEERR : @RaiseBindM RunM MRun (@MemMonad_eq1_runm M RunM MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM _ _ _ MemMonad) string (@raise_error RunM RunERR)}
        (ms : MemState) ptr len (st : store_id),
        (@eq1 RunM
              (@MemMonad_eq1_runm M RunM MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM _ _ _ MemMonad)
              (prod store_id (prod MemState (list LP.ADDR.addr)))
              (@MemMonad_run
           M RunM MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM _ _ _ MemMonad (list LP.ADDR.addr)
           (@get_consecutive_ptrs M MM MOOM MERR ptr len) ms st)
              (fmap (fun ptrs => (st, (ms, ptrs))) (@get_consecutive_ptrs RunM MRun RunOOM RunERR ptr len)))%monad.
    Proof using.
      intros M RunM MM1 MRun0 MPROV0 MSID0 MMS0
        MERR0 MUB0 MOOM0 RunERR0 RunUB0 RunOOM0 EQM' EQRI' MLAWS' MemMonad0
        EQV LAWS RAISEOOM RAISEERR ms ptr len st.
      Opaque handle_gep_addr.

      unfold get_consecutive_ptrs.
      destruct (intptr_seq 0 len) as [NOOM_seq | OOM_seq] eqn:HSEQ.
      - cbn.
        rewrite MemMonad_run_bind.
        rewrite MemMonad_run_ret.
        unfold liftM.
        repeat rewrite bind_ret_l.

        destruct
          (map_monad
             (fun ix : IP.intptr => handle_gep_addr (DTYPE_I 8) ptr [Events.DV.DVALUE_IPTR ix])
             NOOM_seq) eqn:HMAPM.
        + cbn.
          rewrite MemMonad_run_bind.
          rewrite rbm_raise_bind; [|typeclasses eauto].

          rewrite MemMonad_run_raise_error.
          rewrite rbm_raise_bind; eauto.
          rewrite rbm_raise_bind; eauto.
          reflexivity.
        + cbn.
          rewrite MemMonad_run_bind.
          rewrite MemMonad_run_ret.
          rewrite bind_ret_l.
          rewrite bind_ret_l.
          destruct (Monads.sequence l) eqn:HSEQUENCE.
          * cbn; rewrite bind_ret_l.
            rewrite MemMonad_run_ret.
            reflexivity.
          * cbn.
            rewrite rbm_raise_bind; [|typeclasses eauto].
            rewrite MemMonad_run_raise_oom.
            reflexivity.
      - cbn.
        rewrite MemMonad_run_bind.
        unfold liftM.
        rewrite MemMonad_run_raise_oom.
        rewrite bind_bind.
        rewrite rbm_raise_bind; eauto.
        rewrite rbm_raise_bind; eauto.
        reflexivity.
    Qed.

    Lemma exec_correct_step_map_monad_In :
      forall {A B}
        xs
        (m_exec : forall (x : A), In x xs -> MemM B) (m_spec : forall (x : A), In x xs -> MemPropT MemState B)
        (pre : exec_correct_pre)
        (post_b : forall x : A, In x xs -> exec_correct_post B)
        (POST_STEP :
          forall ms_init st_init a b ms st IN,
            (@eq1 (itree Eff)
              (@MemMonad_eq1_runm MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB
                 RunOOM EQM EQRI MLAWS MM) (prod store_id (prod MemState B))
              (MemMonad_run (m_exec a IN) ms_init st_init) (ret (st, (ms, b))))%monad ->
          post_b a IN ms_init st_init b ms st)
        (STEP :
          forall ms_init st_init,
            pre ms_init st_init ->
            forall (ms : MemState) (st : store_id) a (IN : In a xs) res,
              (@within MemM EQM err_ub_oom (prod store_id MemState) (prod store_id MemState)
                 (@Within_err_ub_oom_MemM MemM Eff
                    (@MemMonad_eq1_runm MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM RunERR
                       RunUB RunOOM EQM EQRI MLAWS MM) MRun
                    (@MemMonad_eq1_runm_equiv MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM
                       RunERR RunUB RunOOM EQM EQRI MLAWS MM) RunERR RunUB RunOOM MM0 MRun MPROV MSID
                    MMS MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI MLAWS MM) B
                 (m_exec a IN) (@pair store_id MemState st_init ms_init)
                 (@ret err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) B
                    res) (@pair store_id MemState st ms)) /\
                (post_b a IN) ms_init st_init res ms st /\
                m_spec a IN ms_init (ret (ms, res)) ->
              pre ms st),
        (forall a (IN : In a xs), exec_correct pre (m_exec a IN) (m_spec a IN) (post_b a IN)) ->
        exec_correct pre (map_monad_In xs m_exec) (map_monad_In xs m_spec) (map_monad_In xs post_b).
    Proof.
      induction xs;
        intros m_exec m_spec pre post_b POST_STEP STEP HM.
      - unfold map_monad.
        apply exec_correct_ret.
      - rewrite map_monad_In_unfold.
        rewrite map_monad_In_unfold.

        eapply exec_correct_bind; auto.
        intros * VALID POST RUN.
        eapply exec_correct_bind.
        { eapply exec_correct_weaken_pre; cycle 1.
          eapply IHxs.
          { intros ms_init0 st_init0 a1 b ms st IN H.
            eapply POST_STEP; eauto.
          }
          { intros ms_init0 st_init0 H ms st a1 IN res H0.
            eapply STEP; cbn in *; eauto.
          }

          intros a1 IN.
          apply HM.

          cbn.
          intros ms st H.
          cbn.
          eapply STEP.
          apply H.
          split.
          apply H.
          split; [| apply H].
          destruct H as (?&?&?).
          cbn in H0.
          repeat red in H0.
          destruct H0 as (?&?&?).
          cbn in *.
          rewrite H0 in H2.
          rewrite bind_ret_l in H2.
          eapply POST_STEP; eauto.
        }

        intros * VALID2 POST2 RUN2.
        apply exec_correct_ret.
    Qed.

    Lemma exec_correct_step_map_monad :
      forall {A B}
        xs
        (m_exec : A -> MemM B) (m_spec : A -> MemPropT MemState B)
        (pre : exec_correct_pre)
        (post_b : A -> exec_correct_post B)
        (POST_STEP :
          forall ms_init st_init a b ms st,
            (@eq1 (itree Eff)
              (@MemMonad_eq1_runm MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB
                 RunOOM EQM EQRI MLAWS MM) (prod store_id (prod MemState B))
              (MemMonad_run (m_exec a) ms_init st_init) (ret (st, (ms, b))))%monad ->
          post_b a ms_init st_init b ms st)
        (STEP :
          forall ms_init st_init,
            pre ms_init st_init ->
            forall (ms : MemState) (st : store_id) a res,
              (@within MemM EQM err_ub_oom (prod store_id MemState) (prod store_id MemState)
                 (@Within_err_ub_oom_MemM MemM Eff
                    (@MemMonad_eq1_runm MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM RunERR
                       RunUB RunOOM EQM EQRI MLAWS MM) MRun
                    (@MemMonad_eq1_runm_equiv MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM
                       RunERR RunUB RunOOM EQM EQRI MLAWS MM) RunERR RunUB RunOOM MM0 MRun MPROV MSID
                    MMS MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI MLAWS MM) B
                 (m_exec a) (@pair store_id MemState st_init ms_init)
                 (@ret err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) B
                    res) (@pair store_id MemState st ms)) /\
                (post_b a) ms_init st_init res ms st /\
                m_spec a ms_init (ret (ms, res)) ->
              pre ms st),
        (forall a, exec_correct pre (m_exec a) (m_spec a) (post_b a)) ->
        exec_correct pre (map_monad m_exec xs) (map_monad m_spec xs) (map_monad post_b xs).
    Proof.
      induction xs;
        intros m_exec m_spec pre post_b POST_STEP STEP HM.
      - unfold map_monad.
        apply exec_correct_ret.
      - rewrite map_monad_unfold.
        rewrite map_monad_unfold.

        eapply exec_correct_bind; auto.
        intros * VALID POST RUN.
        eapply exec_correct_bind.
        { eapply exec_correct_weaken_pre; cycle 1.
          eapply IHxs.
          { intros ms_init0 st_init0 a1 b ms st H.
            eapply POST_STEP; eauto.
          }
          { intros ms_init0 st_init0 H ms st a1 res H0.
            eapply STEP; cbn in *; eauto.
          }

          intros a1 IN.
          apply HM.

          intros ms st H.
          eapply STEP.
          apply H.
          split.
          apply H.
          split; [| apply H].
          destruct H as (?&?&?).
          cbn in H0.
          repeat red in H0.
          destruct H0 as (?&?&?).
          cbn in *.
          rewrite H0 in H2.
          rewrite bind_ret_l in H2.
          eapply POST_STEP; eauto.
        }

        intros * VALID2 POST2 RUN2.
        apply exec_correct_ret.
    Qed.

    Lemma exec_correct_step_map_monad_ :
      forall {A B}
        xs
        (m_exec : A -> MemM B) (m_spec : A -> MemPropT MemState B)
        (pre : exec_correct_pre)
        (post_b : A -> exec_correct_post B)
        (POST_STEP :
          forall ms_init st_init a b ms st,
            (@eq1 (itree Eff)
              (@MemMonad_eq1_runm MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB
                 RunOOM EQM EQRI MLAWS MM) (prod store_id (prod MemState B))
              (MemMonad_run (m_exec a) ms_init st_init) (ret (st, (ms, b))))%monad ->
          post_b a ms_init st_init b ms st)
        (STEP :
          forall ms_init st_init,
            pre ms_init st_init ->
            forall (ms : MemState) (st : store_id) a res,
              (@within MemM EQM err_ub_oom (prod store_id MemState) (prod store_id MemState)
                 (@Within_err_ub_oom_MemM MemM Eff
                    (@MemMonad_eq1_runm MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM RunERR
                       RunUB RunOOM EQM EQRI MLAWS MM) MRun
                    (@MemMonad_eq1_runm_equiv MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM
                       RunERR RunUB RunOOM EQM EQRI MLAWS MM) RunERR RunUB RunOOM MM0 MRun MPROV MSID
                    MMS MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI MLAWS MM) B
                 (m_exec a) (@pair store_id MemState st_init ms_init)
                 (@ret err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) B
                    res) (@pair store_id MemState st ms)) /\
                (post_b a) ms_init st_init res ms st /\
                m_spec a ms_init (ret (ms, res)) ->
              pre ms st),
        (forall a, exec_correct pre (m_exec a) (m_spec a) (post_b a)) ->
        exec_correct pre (map_monad_ m_exec xs) (map_monad_ m_spec xs) (map_monad_ post_b xs).
    Proof.
      intros A B xs m_exec m_spec pre post_b POST_STEP STEP HM.
      unfold map_monad_.
      apply exec_correct_bind.
      apply exec_correct_step_map_monad; auto.

      intros * VALID POST RUN.
      apply exec_correct_ret.
    Qed.

    Lemma get_consecutive_ptrs_preserves_state :
      forall st ms st' ms' ptr bytes a,
        @within MemM EQM err_ub_oom (prod store_id MemState) (prod store_id MemState)
          (@Within_err_ub_oom_MemM MemM Eff
             (@MemMonad_eq1_runm MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB
                RunOOM EQM EQRI MLAWS MM) MRun
             (@MemMonad_eq1_runm_equiv MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM RunERR
                RunUB RunOOM EQM EQRI MLAWS MM) RunERR RunUB RunOOM MM0 MRun MPROV MSID MMS MERR MUB
             MOOM RunERR RunUB RunOOM EQM EQRI MLAWS MM) (list ADDR.addr)
          (@get_consecutive_ptrs MemM MM0 MOOM MERR ptr (@Datatypes.length BYTE_IMPL.SByte bytes))
          (@pair store_id MemState st ms)
          (@ret err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
             (list ADDR.addr) a) (@pair store_id MemState st' ms') ->
        (ms, st) = (ms', st').
    Proof.
      intros st ms st' ms' ptr bytes a H.
      cbn in H.
      repeat red in H.
      destruct H as (?&?&?).
      cbn in H, H0.
      rewrite H in H0.
      rewrite bind_ret_l in H0.
      rewrite MemMonad_run_get_consecutive_ptrs in H0.
      unfold fmap in H0.
      cbn in H0.
      unfold liftM in H0.
      pose proof get_consecutive_ptrs_inv ptr (Datatypes.length bytes).
      destruct H1 as [[msg OOM] | [ptrs GCP]].
      { rewrite OOM in H0.
        rewrite rbm_raise_bind in H0; try typeclasses eauto.
        symmetry in H0.
        apply MemMonad_eq1_raise_oom_inv in H0; contradiction.
      }

      rewrite GCP in H0.
      repeat rewrite bind_ret_l in H0.
      eapply eq1_ret_ret in H0; try typeclasses eauto.
      inv H0.
      auto.
    Qed.

    Lemma write_bytes_correct :
      forall ptr bytes,
        exec_correct
          (fun ms st => Forall (fun byte => exists s, MemByte.sbyte_sid byte = inr s /\ (s < st)%N) bytes)
          (write_bytes ptr bytes) (write_bytes_spec ptr bytes)
          (@exec_correct_post_bind (list ADDR.addr) unit
             (@exec_correct_post_bind (list IP.intptr) (list ADDR.addr)
                (@lift_OOM exec_correct_post Monad_exec_correct_post RAISE_OOM_exec_correct_post
                   (list IP.intptr) (intptr_seq 0 (@Datatypes.length BYTE_IMPL.SByte bytes)))
                (fun ixs : list IP.intptr =>
                   @exec_correct_post_bind (list (OOM ADDR.addr)) (list ADDR.addr)
                     (@lift_err_RAISE_ERROR (list (OOM ADDR.addr)) exec_correct_post Monad_exec_correct_post
                        RAISE_ERROR_exec_correct_post
                        (@map_monad (sum string) (EitherMonad.Monad_either string) IP.intptr
                           (OOM ADDR.addr)
                           (fun ix : IP.intptr =>
                              handle_gep_addr (DTYPE_I 8) ptr (@cons dvalue (DVALUE_IPTR ix) (@nil dvalue)))
                           ixs))
                     (fun addrs : list (OOM ADDR.addr) =>
                        @lift_OOM exec_correct_post Monad_exec_correct_post RAISE_OOM_exec_correct_post
                          (list ADDR.addr) (@sequence OOM MonadOOM ADDR.addr addrs))))
             (fun a : list ADDR.addr =>
                @exec_correct_post_bind (list unit) unit
                  (@map_monad_In exec_correct_post Monad_exec_correct_post (prod ADDR.addr BYTE_IMPL.SByte)
                     unit (@zip ADDR.addr BYTE_IMPL.SByte a bytes)
                     (fun (H : prod ADDR.addr BYTE_IMPL.SByte)
                        (_ : @In (prod ADDR.addr BYTE_IMPL.SByte) H (@zip ADDR.addr BYTE_IMPL.SByte a bytes))
                        (_ : MemState) (st : store_id) (_ : unit) (_ : MemState)
                        (st' : store_id) => @eq store_id st st'))
                  (fun _ : list unit => @exec_correct_post_ret unit tt))).
    Proof using Type.
      intros ptr bytes.
      eapply exec_correct_strengthen_post; cycle 1.
      { apply exec_correct_bind.
        apply exec_correct_get_consecutive_pointers.
        intros * VALID POST RUN.
        cbn in POST.
        destruct POST as (?&?&?&?&?&?&?&?&?).
        unfold lift_OOM in H.
        break_match_hyp_inv.
        destruct H3; subst.

        unfold map_monad_.
        eapply exec_correct_bind.
        { repeat rewrite map_monad_map_monad_In.
          eapply exec_correct_weaken_pre
            with
            (weak_pre:=(fun (ms_k : MemState) (st_k : store_id) =>
                          Forall
                            (fun byte : BYTE_IMPL.SByte => exists s : store_id, MemByte.sbyte_sid byte = inr s /\ s < x1)
                            bytes /\ x1 <= st_k)).
          { intros ms st (?&?&?).
            eapply get_consecutive_ptrs_preserves_state in H2; inv H2.
            split; eauto.
            lia.
          }

          eapply exec_correct_step_map_monad_In
            with (post_b := fun _ _ _ st _ _ st' => st = st').
          3: {
            intros [a' b] IN.
            eapply exec_correct_weaken_pre
              with (weak_pre:=(fun ms st => exists s, MemByte.sbyte_sid b = inr s /\ (s < st)%N)).
            { intros ms st (H&LT).
              apply zip_In_both in IN as (_&IN).
              eapply Forall_forall in H; eauto.
              destruct H as (?&?&?).
              exists x5; split; eauto.
              lia.
            }

            eapply write_byte_correct.
          }
          {
            intros ms_init st_init [a' b] [] ms st IN H.
            unfold lift_OOM in *; break_match_hyp_inv.
            destruct H3; subst.
            eapply write_byte_preserves_store_id.
            cbn.
            repeat red.
            eexists.
            split; cbn.
            reflexivity.
            rewrite bind_ret_l.
            apply H.
          }

          (* STEP for map_monad_In *)
          intros ms_init st_init (?&?) ms st [a' b] IN [] (?&?).
          split; eauto.
          destruct H4; subst.
          auto.
        }

        intros * VALID' POST' RUN'.
        apply exec_correct_ret.
      }

      intros.
      cbn in H.
      auto.
    Qed.

    Lemma to_ubytes_sids_bounded :
      forall uv dt sid st,
        sid < st ->
        Forall (fun byte : BYTE_IMPL.SByte => exists s : store_id, MemByte.sbyte_sid byte = inr s /\ s < st)
          (MemByte.to_ubytes uv dt sid).
    Proof.
      intros uv dt sid st H.
      apply Forall_map.
      remember (N.to_nat (SIZEOF.sizeof_dtyp dt)) as n.
      clear Heqn.
      remember 0 as start.
      clear Heqstart.
      revert start.
      induction n; intros start.
      - cbn.
        constructor.
      - cbn.
        constructor.
        + unfold MemByte.sbyte_sid.
          rewrite BYTE_IMPL.sbyte_to_extractbyte_of_uvalue_sbyte.
          exists sid; auto.
        + apply IHn.
    Qed.

    Lemma write_uvalue_correct :
      forall dt ptr uv pre,
        exec_correct pre (write_uvalue dt ptr uv) (write_uvalue_spec dt ptr uv)
          (@bind exec_correct_post Monad_exec_correct_post (list BYTE_IMPL.SByte) unit
             (@serialize_sbytes exec_correct_post Monad_exec_correct_post MonadStoreId_exec_correct_post uv
                dt)
             (fun a : list BYTE_IMPL.SByte =>
                (fun a0 : list BYTE_IMPL.SByte =>
                   @exec_correct_post_bind (list ADDR.addr) unit
                     (@exec_correct_post_bind (list IP.intptr) (list ADDR.addr)
                        (@lift_OOM exec_correct_post Monad_exec_correct_post RAISE_OOM_exec_correct_post
                           (list IP.intptr) (intptr_seq 0 (@Datatypes.length BYTE_IMPL.SByte a0)))
                        (fun ixs : list IP.intptr =>
                           @exec_correct_post_bind (list (OOM ADDR.addr)) (list ADDR.addr)
                             (@lift_err_RAISE_ERROR (list (OOM ADDR.addr)) exec_correct_post
                                Monad_exec_correct_post RAISE_ERROR_exec_correct_post
                                (@map_monad (sum string) (EitherMonad.Monad_either string) IP.intptr
                                   (OOM ADDR.addr)
                                   (fun ix : IP.intptr =>
                                      handle_gep_addr (DTYPE_I 8) ptr (@cons dvalue (DVALUE_IPTR ix) (@nil dvalue)))
                                   ixs))
                             (fun addrs : list (OOM ADDR.addr) =>
                                @lift_OOM exec_correct_post Monad_exec_correct_post RAISE_OOM_exec_correct_post
                                  (list ADDR.addr) (@sequence OOM MonadOOM ADDR.addr addrs))))
                     (fun a1 : list ADDR.addr =>
                        @exec_correct_post_bind (list unit) unit
                          (@map_monad_In exec_correct_post Monad_exec_correct_post
                             (prod ADDR.addr BYTE_IMPL.SByte) unit (@zip ADDR.addr BYTE_IMPL.SByte a1 a0)
                             (fun (H : prod ADDR.addr BYTE_IMPL.SByte)
                                (_ : @In (prod ADDR.addr BYTE_IMPL.SByte) H
                                       (@zip ADDR.addr BYTE_IMPL.SByte a1 a0)) (_ : MemState)
                                (st : store_id) (_ : unit) (_ : MemState) (st' : store_id) =>
                                @eq store_id st st')) (fun _ : list unit => @exec_correct_post_ret unit tt))) a)).
    Proof using Type.
      intros dt ptr uv pre.
      { apply exec_correct_bind.
        apply exec_correct_serialize_sbytes.
        intros * VALID POST RUN.
        eapply exec_correct_weaken_pre.
        2: apply write_bytes_correct.

        intros ms st (?&?&?).
        rename a into bytes.

        repeat red in POST.
        destruct POST as (?&?&?&?&?&?&?); subst.
        cbn in H2.
        destruct H2 as (?&?&?); subst.
        repeat red in H0.
        destruct H0 as (?&?&?).
        cbn in *.

        destruct H1 as (?&?&?&?&?).
        subst.

        rewrite H0 in H4.
        rewrite bind_ret_l in H4.
        rewrite RUN in H4.
        eapply eq1_ret_ret in H4; try typeclasses eauto.
        inv H4.

        eapply to_ubytes_sids_bounded; lia.
      }
    Qed.

    Lemma allocate_bytes_correct :
      forall bytes ,
        exec_correct
          (fun _ st =>
             Forall (fun b : BYTE_IMPL.SByte => exists s : store_id, MemByte.sbyte_sid b = inr s /\ s < st) bytes)
          (allocate_bytes bytes)
          (allocate_bytes_spec_MemPropT bytes)
          exec_correct_id_post.
    Proof using Type.
      intros bytes.
      eapply exec_correct_strengthen_post; cycle 1.
      { eapply exec_correct_bind.
        apply exec_correct_fresh_provenance.

        intros * VALID POST RUN.
        cbn in POST.
        eapply exec_correct_weaken_pre; cycle 1.
        apply allocate_bytes_with_pr_correct.

        intros ms st (?&?&?).
        cbn in *.
        repeat red in H0.
        destruct H0 as (?&?&?).
        cbn in *.
        rewrite H0 in H2.
        rewrite bind_ret_l in H2.
        rewrite RUN in H2.
        eapply eq1_ret_ret in H2; try typeclasses eauto.
        inv H2.
        destruct POST as (?&?&?&?); subst.
        apply H.
      }
      auto.
    Qed.

    Hint Resolve allocate_bytes_correct : EXEC_CORRECT.

    Lemma exec_correct_repeatMN :
      forall {A} (n : N) (m_exec : MemM A) (m_spec : MemPropT MemState A)
        (pre : exec_correct_pre)
        (post : exec_correct_post A)
        (POST_STEP :
          forall ms_init st_init res ms st,
            (@eq1 (itree Eff)
              (@MemMonad_eq1_runm MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB
                 RunOOM EQM EQRI MLAWS MM) (prod store_id (prod MemState A))
              (MemMonad_run m_exec ms_init st_init) (ret (st, (ms, res))))%monad ->
            post ms_init st_init res ms st)
        (STEP :
          forall ms_init st_init,
            pre ms_init st_init ->
            forall (ms : MemState) (st : store_id) res,
              m_spec ms_init (ret (ms, res)) ->
              post ms_init st_init res ms st ->
              pre ms st),
        (exec_correct pre m_exec m_spec post) ->
        exec_correct pre
          (repeatMN n m_exec)
          (repeatMN n m_spec)
          (repeatMN n post).
    Proof using Type.
      intros A n.
      induction n using N.peano_rect; intros pre m_exec m_spec post POST_STEP STEP HM.
      - eapply exec_correct_strengthen_post; cycle 1.
        eapply exec_correct_ret.
        eauto.
      - do 2 rewrite repeatMN_succ.
        eapply exec_correct_strengthen_post; cycle 1.
        { apply exec_correct_bind; auto.
          apply HM.

          intros * VALID POST RUN.
          eapply exec_correct_weaken_pre; cycle 1.
          apply exec_correct_bind.
          { eapply IHn.
            3: {
              apply HM.
            }

            { intros ms_init0 st_init0 res ms st H.
              apply POST_STEP; eauto.
            }

            intros ms_init0 st_init0 H ms st res H0.
            eapply STEP; eauto.
          }

          intros * VALID' POST' RUN'.
          apply exec_correct_ret.
          intros ms st (?&?&?).
          eapply STEP; eauto.
          apply POST_STEP.
          repeat red in H0.
          destruct H0 as (?&?&?).
          cbn in *.
          rewrite H0, bind_ret_l in H2.
          auto.
        }

        intros ms st a ms' st' H0 H.
        cbn in H.
        repeat red in H.
        destruct H as (?&?&?&?&?&?&?&?&?).
        rewrite repeatMN_succ.
        cbn.
        repeat red.
        exists x, x0, x1.
        split; eauto.
        repeat red.
        exists x2, x3, x4.
        split; eauto.
    Qed.

    Lemma exec_correct_repeatMN_Forall_simple :
      forall {A} (n : N) (m_exec : MemM A) (m_spec : MemPropT MemState A)
        (pre : exec_correct_pre)
        (post : exec_correct_post A),
        (exec_correct pre m_exec m_spec (fun ms st a ms' st' => post ms st a ms' st' /\ ms = ms' /\ st = st')) ->
        exec_correct pre
          (repeatMN n m_exec)
          (repeatMN n m_spec)
          (fun ms st res ms' st' => Forall (fun r => post ms st r ms' st') res /\ ms = ms' /\ st = st').
    Proof using Type.
      intros A n.
      induction n using N.peano_rect; intros pre m_exec m_spec post HM.
      - eapply exec_correct_strengthen_post; cycle 1.
        eapply exec_correct_ret.
        intros ms st a ms' st' ? (?&?&?); subst.
        eauto.
      - do 2 rewrite repeatMN_succ.
        eapply exec_correct_strengthen_post; cycle 1.
        { apply exec_correct_bind; auto.
          apply HM.

          intros * VALID POST RUN.
          eapply exec_correct_weaken_pre; cycle 1.
          apply exec_correct_bind.
          { eapply IHn.
            apply HM.
          }

          intros * VALID' POST' RUN'.
          apply exec_correct_ret.
          cbn in POST.
          destruct POST as (?&?&?); subst.
          intros ms st (?&?&?).
          cbn in H1.
          repeat red in H1.
          destruct H1 as (?&?&?).
          cbn in H3.
          cbn in H1.
          rewrite H1, bind_ret_l in H3.
          rewrite RUN in H3.
          eapply eq1_ret_ret in H3; try typeclasses eauto.
          inv H3.
          auto.
        }

        intros ms st a ms' st' SPEC H.
        cbn in H.
        repeat red in H.
        destruct H as (?&?&?&?&?&?&?&?&?).
        destruct H0 as (?&?&?); subst.
        destruct H as (?&?&?); subst.
        destruct H1 as (?&?&?); subst.
        auto.
    Qed.

    Lemma exec_correct_clear_assertion :
      forall {A} (pre : MemState -> store_id -> Prop) (m_exec : MemM A) (m_spec : MemPropT MemState A) (assertion : Prop) post,
        exec_correct pre m_exec m_spec post ->
        assertion ->
        exec_correct pre m_exec (MemPropT_assert_pre assertion;; m_spec) post.
    Proof using Type.
      intros A pre m_exec m_spec assertion post EXEC ASSERTION.
      repeat red.
      intros ms st H H0.
      repeat red in EXEC.
      specialize (EXEC _ _ H H0).
      destruct EXEC as [UB | EXEC].
      - left.
        destruct UB as (?&?&?).
        exists x, x0.
        cbn.
        right.
        exists ms, tt.
        split; eauto.
      - destruct EXEC as (?&?&?&?&?&?).
        right.
        exists x, x0, x1.
        split; eauto.
        split; eauto.
        destruct_err_ub_oom x; subst; cbn in *.
        + right.
          exists ms, tt.
          split; eauto.
        + right.
          exists ms, tt.
          split; eauto.
        + right.
          exists ms, tt.
          split; eauto.
        + exists ms, tt.
          split; eauto.
    Qed.

    Hint Resolve exec_correct_clear_assertion : EXEC_CORRECT.

    Lemma MemMonad_repeatMN_repeatN :
      forall ms st num_elements l,
        @eq1 (itree Eff)
          (@MemMonad_eq1_runm MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB
             RunOOM EQM EQRI MLAWS MM) (prod store_id (prod MemState (list (list BYTE_IMPL.SByte))))
          (@MemMonad_run MemM (itree Eff) MM0 MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM EQM
             EQRI MLAWS MM (list (list BYTE_IMPL.SByte))
             (@repeatMN (list BYTE_IMPL.SByte) MemM MM0 num_elements
                (@ret MemM MM0 (list BYTE_IMPL.SByte) l)) ms st)
          (@ret (itree Eff) MRun (prod store_id (prod MemState (list (list BYTE_IMPL.SByte))))
             (@pair store_id (prod MemState (list (list BYTE_IMPL.SByte))) st
                (@pair MemState (list (list BYTE_IMPL.SByte)) ms (repeatN num_elements l)))).
    Proof.
      intros ms st.
      induction num_elements using N.peano_ind;
        intros l.
      - cbn in *.
        rewrite MemMonad_run_ret.
        reflexivity.
      - rewrite repeatMN_succ.
        repeat setoid_rewrite MemMonad_run_bind.
        rewrite MemMonad_run_ret, bind_ret_l, MemMonad_run_bind.
        rewrite IHnum_elements.
        rewrite bind_ret_l.
        rewrite MemMonad_run_ret.
        rewrite repeatN_succ.
        reflexivity.
    Qed.

    Lemma generate_num_undef_bytes_bounded :
      forall sid st dt bytes n,
        sid < st ->
        generate_num_undef_bytes n dt sid = NoOom bytes ->
        Forall (fun b : BYTE_IMPL.SByte => exists s : store_id, MemByte.sbyte_sid b = inr s /\ s < st) bytes.
    Proof.
      intros sid st dt bytes n LT GEN.
      unfold generate_num_undef_bytes in GEN.
      remember 0 as start_idx.
      clear Heqstart_idx.
      revert start_idx bytes GEN.
      induction n using N.peano_ind;
        intros start_idx bytes GEN.
      - cbn in *.
        inv GEN.
        constructor.
      - unfold generate_num_undef_bytes_h in GEN.
        pose proof @N.recursion_succ (N -> OOM (list BYTE_IMPL.SByte)) eq (fun _ : N => ret [])
          (fun (_ : N) (mf : N -> OOM (list BYTE_IMPL.SByte)) (x : N) =>
             rest_bytes <- mf (N.succ x);;
             ret (BYTE_IMPL.uvalue_sbyte (UVALUE_Undef dt) dt x sid :: rest_bytes))
          eq_refl.
        forward H.
        { unfold Proper, respectful.
          intros x y H0 x0 y0 H1; subst.
          reflexivity.
        }
        specialize (H n).
        rewrite H in GEN.
        clear H.

        destruct
          (N.recursion (fun _ : N => ret [])
             (fun (_ : N) (mf : N -> OOM (list BYTE_IMPL.SByte)) (x : N) =>
                rest_bytes <- mf (N.succ x);;
                ret (BYTE_IMPL.uvalue_sbyte (UVALUE_Undef dt) dt x sid :: rest_bytes)) n
             (N.succ start_idx)) eqn:HREC.
        + (* No OOM *)
          cbn in GEN.
          inv GEN.
          constructor.
          { exists sid.
            unfold MemByte.sbyte_sid.
            rewrite BYTE_IMPL.sbyte_to_extractbyte_of_uvalue_sbyte.
            auto.
          }
          eapply IHn.
          unfold generate_num_undef_bytes_h.
          apply HREC.
        + (* OOM *)
          cbn in GEN.
          inv GEN.
    Qed.

    Lemma generate_undef_bytes_bounded :
      forall sid st dt bytes,
        sid < st ->
        generate_undef_bytes dt sid = NoOom bytes ->
        Forall (fun b : BYTE_IMPL.SByte => exists s : store_id, MemByte.sbyte_sid b = inr s /\ s < st) bytes.
    Proof.
      intros sid st dt bytes LT GEN.
      unfold generate_undef_bytes in GEN.
      eapply generate_num_undef_bytes_bounded; eauto.
    Qed.

    Lemma allocate_dtyp_correct :
      forall dt num_elements pre,
        exec_correct pre (allocate_dtyp dt num_elements) (allocate_dtyp_spec dt num_elements)
          (@bind exec_correct_post Monad_exec_correct_post store_id ADDR.addr
             (@fresh_sid exec_correct_post MonadStoreId_exec_correct_post)
             (fun a : store_id =>
                (fun a0 : store_id =>
                   @bind exec_correct_post Monad_exec_correct_post (list (list BYTE_IMPL.SByte)) ADDR.addr
                     (fun (ms : MemState) (st : store_id) (res : list (list BYTE_IMPL.SByte))
                        (ms' : MemState) (st' : store_id) =>
                        Logic.and
                          (@Forall (list BYTE_IMPL.SByte)
                             (fun r : list BYTE_IMPL.SByte => Forall (fun b : BYTE_IMPL.SByte => exists s : store_id, MemByte.sbyte_sid b = inr s /\ s < st) r) res)
                          (Logic.and (@eq MemState ms ms') (@eq store_id st st')))
                     (fun a1 : list (list BYTE_IMPL.SByte) =>
                        (fun _ : list (list BYTE_IMPL.SByte) => @exec_correct_id_post ADDR.addr) a1)) a)).
    Proof using Type.
      intros dt num_elements pre.
      destruct (dtyp_eqb dt DTYPE_Void) eqn:DT.
      { (* UB because of attempting to allocate a void type... *)
        unfold allocate_dtyp.
        rewrite DT.
        apply dtyp_eqb_eq in DT; subst.
        unfold allocate_dtyp_spec.
        repeat red.
        intros ms st H H0.
        left.
        exists ms.
        exists ""%string.
        left.
        cbn.
        eauto.
      }

      assert (dt <> DTYPE_Void) as NVOID.
      { intros CONTRA.
        subst.
        rewrite dtyp_eqb_refl in DT.
        discriminate.
      }

      apply exec_correct_clear_assertion; auto.
      unfold allocate_dtyp.
      rewrite DT.

      { apply exec_correct_bind.
        apply exec_correct_fresh_sid.
        intros * VALID1 POST1 RUN1.
        apply exec_correct_bind.
        { eapply exec_correct_repeatMN_Forall_simple.
          eapply exec_correct_strengthen_post; cycle 1.
          apply exec_correct_lift_OOM.
          intros ms st a0 ms' st' PRE POST.
          destruct PRE as (?&?&?).
          cbn in H0, H1.
          repeat red in H0.
          destruct H0 as (?&?&?).
          cbn in H0, H2.
          rewrite H0, bind_ret_l in H2.
          rewrite RUN1 in H2.
          eapply eq1_ret_ret in H2; try typeclasses eauto.
          inv H2.
          unfold lift_OOM in POST.
          break_match_hyp_inv.
          destruct H3; subst.
          split; eauto.

          eapply generate_undef_bytes_bounded; eauto.
          destruct POST1 as (?&?&?); subst.
          lia.
        }

        intros * VALID2 POST2 RUN2.
        eapply exec_correct_weaken_pre; cycle 1.
        apply allocate_bytes_correct.
        { intros ms st (?&?&?).
          destruct H as (?&?&?).
          destruct POST2 as (?&?&?).
          apply Forall_concat.
          subst.
          destruct H0 as (?&?&?).
          cbn in *.
          repeat red in H2.
          destruct H2 as (?&?&?).
          cbn in *.
          rewrite H2, bind_ret_l in H6.
          destruct POST1 as (?&?&?); subst.
          rewrite RUN1 in H6.
          eapply eq1_ret_ret in H6; try typeclasses eauto.
          inv H6.
          rewrite H0, bind_ret_l in H5.

          unfold lift_OOM in *.
          break_match_hyp.
          2: {
            induction num_elements using N.peano_ind.
            - cbn in *.
              rewrite MemMonad_run_ret in RUN2.
              eapply eq1_ret_ret in RUN2; try typeclasses eauto.
              inv RUN2.
              constructor.
            - clear - RUN2.
              rewrite repeatMN_succ in RUN2.
              rewrite MemMonad_run_bind in RUN2.
              rewrite MemMonad_run_raise_oom in RUN2.
              rewrite rbm_raise_bind in RUN2; try typeclasses eauto.
              symmetry in RUN2.
              eapply MemMonad_eq1_raise_oom_inv in RUN2; contradiction.
          }

          assert (st_after_m0 = st).
          { clear - H5.
            rewrite MemMonad_repeatMN_repeatN in H5.
            eapply eq1_ret_ret in H5; try typeclasses eauto.
            inv H5; auto.
          }
          subst.
          auto.
        }
      }
    Qed.

    Lemma memcpy_correct :
      forall src dst len volatile pre,
        exec_correct pre (memcpy src dst len volatile) (memcpy_spec src dst len volatile)
          (a0 <-
             (_ <-
                @get_consecutive_ptrs exec_correct_post Monad_exec_correct_post RAISE_OOM_exec_correct_post
                  RAISE_ERROR_exec_correct_post src (Z.to_nat len);;
              (fun (ms0 : MemState) (st0 : store_id) (bytes : list BYTE_IMPL.SByte) 
                 (ms'0 : MemState) (st'0 : store_id) =>
                 @Forall BYTE_IMPL.SByte
                   (fun byte : BYTE_IMPL.SByte =>
                      exists s : store_id, MemByte.sbyte_sid byte = @inr string store_id s /\ s < st0) bytes /\
                   ms0 = ms'0 /\ st0 = st'0));;
           (fun a1 : list BYTE_IMPL.SByte =>
              @exec_correct_post_bind (list ADDR.addr) unit
                (@exec_correct_post_bind (list IP.intptr) (list ADDR.addr)
                   (@lift_OOM exec_correct_post Monad_exec_correct_post RAISE_OOM_exec_correct_post
                      (list IP.intptr) (intptr_seq 0 (@Datatypes.length BYTE_IMPL.SByte a1)))
                   (fun ixs : list IP.intptr =>
                      @exec_correct_post_bind (list (OOM ADDR.addr)) (list ADDR.addr)
                        (@lift_err_RAISE_ERROR (list (OOM ADDR.addr)) exec_correct_post Monad_exec_correct_post
                           RAISE_ERROR_exec_correct_post
                           (@map_monad err (EitherMonad.Monad_either string) IP.intptr 
                              (OOM ADDR.addr)
                              (fun ix : IP.intptr => handle_gep_addr (DTYPE_I 8) dst [DVALUE_IPTR ix]) ixs))
                        (fun addrs : list (OOM ADDR.addr) =>
                           @lift_OOM exec_correct_post Monad_exec_correct_post RAISE_OOM_exec_correct_post
                             (list ADDR.addr) (@sequence OOM MonadOOM ADDR.addr addrs))))
                (fun a2 : list ADDR.addr =>
                   @exec_correct_post_bind (list unit) unit
                     (@map_monad_In exec_correct_post Monad_exec_correct_post (ADDR.addr * BYTE_IMPL.SByte) unit
                        (@zip ADDR.addr BYTE_IMPL.SByte a2 a1)
                        (fun (H : ADDR.addr * BYTE_IMPL.SByte)
                           (_ : @In (ADDR.addr * BYTE_IMPL.SByte) H (@zip ADDR.addr BYTE_IMPL.SByte a2 a1))
                           (_ : MemState) (st0 : store_id) (_ : unit) (_ : MemState) (st'0 : store_id) =>
                           st0 = st'0)) (fun _ : list unit => @exec_correct_post_ret unit tt))) a0).
    Proof using Type.
      intros src dst len volatile pre.
      unfold memcpy, memcpy_spec.
      break_match; [apply exec_correct_raise_ub|].
      unfold MME.OVER_H.no_overlap, MME.OVER.overlaps.
      unfold OVER_H.no_overlap, OVER.overlaps.
      break_match; [|apply exec_correct_raise_ub].

      { apply exec_correct_bind.
        apply read_bytes_correct.
        intros * VALID POST RUN.
        eapply exec_correct_weaken_pre; cycle 1.
        apply write_bytes_correct.

        intros ms st H.
        cbn.
        destruct H as (?&?&?).
        repeat red in H1.
        destruct H1 as (?&?&?&?).
        assert (x = ms_init).
        { red in H1.
          cbn in H1.
          destruct H1 as (?&?&?&?&?&?&?).
          unfold lift_OOM in *.
          unfold lift_err_RAISE_ERROR in *.
          repeat break_match_hyp_inv.
          auto.
        }

        destruct POST as (?&?&?&?&?&?&?); subst.
        destruct H4 as (?&?&?&?&?&?&?&?&?).
        unfold lift_OOM in *.
        repeat break_match_hyp_inv.
        destruct H8, H7; subst.
        unfold lift_err_RAISE_ERROR in H4.
        repeat red in H0.
        destruct H0 as (?&?&?).
        cbn in H0, H3.
        rewrite H0, bind_ret_l in H3.
        rewrite RUN in H3.
        eapply eq1_ret_ret in H3; try typeclasses eauto.
        inv H3.
        auto.
      }
    Qed.

    Lemma memset_correct :
      forall dst val len sid volatile,
        exec_correct
          (fun ms st => sid < st)
          (memset dst val len sid volatile) (memset_spec dst val len sid volatile)
          (@exec_correct_post_bind (list ADDR.addr) unit
             (@exec_correct_post_bind (list IP.intptr) (list ADDR.addr)
                (@lift_OOM exec_correct_post Monad_exec_correct_post RAISE_OOM_exec_correct_post
                   (list IP.intptr)
                   (intptr_seq 0
                      (@Datatypes.length BYTE_IMPL.SByte
                         (@repeatN BYTE_IMPL.SByte (Z.to_N len)
                            (BYTE_IMPL.uvalue_sbyte (UVALUE_I8 val) (DTYPE_I 8) 0 sid)))))
                (fun ixs : list IP.intptr =>
                   @exec_correct_post_bind (list (OOM ADDR.addr)) (list ADDR.addr)
                     (@lift_err_RAISE_ERROR (list (OOM ADDR.addr)) exec_correct_post Monad_exec_correct_post
                        RAISE_ERROR_exec_correct_post
                        (@map_monad err (EitherMonad.Monad_either string) IP.intptr (OOM ADDR.addr)
                           (fun ix : IP.intptr => handle_gep_addr (DTYPE_I 8) dst [DVALUE_IPTR ix]) ixs))
                     (fun addrs : list (OOM ADDR.addr) =>
                        @lift_OOM exec_correct_post Monad_exec_correct_post RAISE_OOM_exec_correct_post
                          (list ADDR.addr) (@sequence OOM MonadOOM ADDR.addr addrs))))
             (fun a0 : list ADDR.addr =>
                @exec_correct_post_bind (list unit) unit
                  (@map_monad_In exec_correct_post Monad_exec_correct_post (ADDR.addr * BYTE_IMPL.SByte) unit
                     (@zip ADDR.addr BYTE_IMPL.SByte a0
                        (@repeatN BYTE_IMPL.SByte (Z.to_N len)
                           (BYTE_IMPL.uvalue_sbyte (UVALUE_I8 val) (DTYPE_I 8) 0 sid)))
                     (fun (H : ADDR.addr * BYTE_IMPL.SByte)
                        (_ : @In (ADDR.addr * BYTE_IMPL.SByte) H
                               (@zip ADDR.addr BYTE_IMPL.SByte a0
                                  (@repeatN BYTE_IMPL.SByte (Z.to_N len)
                                     (BYTE_IMPL.uvalue_sbyte (UVALUE_I8 val) (DTYPE_I 8) 0 sid)))) 
                        (_ : MemState) (st0 : store_id) (_ : unit) (_ : MemState) (st'0 : store_id) => 
                        st0 = st'0)) (fun _ : list unit => @exec_correct_post_ret unit tt))).
    Proof using Type.
      intros dst val len sid volatile.
      unfold memset, memset_spec.
      break_match; [apply exec_correct_raise_ub|].
      eapply exec_correct_weaken_pre; cycle 1.
      eapply write_bytes_correct.
      { intros ms st H.
        cbn.
        apply Forall_repeatN.
        exists sid.
        unfold MemByte.sbyte_sid.
        rewrite BYTE_IMPL.sbyte_to_extractbyte_of_uvalue_sbyte.
        auto.
      }
    Qed.

    Lemma handle_memory_correct :
      forall T (m : MemoryE T) pre,
        exec_correct pre (handle_memory T m) (handle_memory_prop T m) exec_correct_id_post.
    Proof using Type.
      intros T m pre.
      destruct m.
      - (* MemPush *)
        cbn.
        apply mempush_correct.
      - (* MemPop *)
        cbn.
        apply mempop_correct.
      - (* Alloca *)
        unfold handle_memory.
        unfold handle_memory_prop.
        eapply exec_correct_strengthen_post; cycle 1.
        { apply exec_correct_bind.
          apply allocate_dtyp_correct.
          intros * VALID POST RUN.
          apply exec_correct_ret.
        }

        intros ms st a ms' st' H H0.
        auto.
      - (* Load *)
        unfold handle_memory, handle_memory_prop.
        destruct a; try apply exec_correct_raise_ub.
        eapply exec_correct_strengthen_post; cycle 1.
        apply read_uvalue_correct.
        intros ms st a0 ms' st' H H0.
        auto.
      - (* Store *)
        unfold handle_memory, handle_memory_prop.
        destruct a; try apply exec_correct_raise_ub.
        eapply exec_correct_strengthen_post; cycle 1.
        apply write_uvalue_correct.
        intros ms st a0 ms' st' H H0.
        auto.
    Qed.

    Lemma handle_memcpy_correct:
      forall args pre,
        exec_correct pre (handle_memcpy args) (handle_memcpy_prop args) exec_correct_id_post.
    Proof using Type.
      intros args pre.
      unfold handle_memcpy, handle_memcpy_prop.
      repeat (break_match; try eapply exec_correct_strengthen_post; try apply exec_correct_raise_error; eauto).
      all: eapply exec_correct_strengthen_post; cycle 1; [apply memcpy_correct|auto].
    Qed.

    Lemma handle_memset_correct:
      forall args pre,
        exec_correct pre (handle_memset args) (handle_memset_prop args) exec_correct_id_post.
    Proof using Type.
      intros args pre.
      unfold handle_memset, handle_memset_prop.
      repeat (break_match;
              try solve
                [ eapply exec_correct_strengthen_post; cycle 1;
                  [apply exec_correct_raise_error|eauto]]).
      { eapply exec_correct_strengthen_post; cycle 1.
        { apply exec_correct_bind.
          apply exec_correct_fresh_sid; eauto.
          intros a0 ms_init ms_after_m st_init st_after_m H H0 H1 WEM.
          eapply exec_correct_weaken_pre; cycle 1.
          apply memset_correct.
          intros ms st (?&?&?).
          cbn in *.
          repeat red in H3.
          destruct H3 as (?&?&?).
          cbn in *.
          rewrite H3, bind_ret_l, H1 in H5.
          eapply eq1_ret_ret in H5; try typeclasses eauto.
          inv H5.
          lia.
        }
        auto.
      }
      { eapply exec_correct_strengthen_post; cycle 1.
        { apply exec_correct_bind.
          apply exec_correct_fresh_sid; eauto.
          intros a0 ms_init ms_after_m st_init st_after_m H H0 H1 WEM.
          eapply exec_correct_weaken_pre; cycle 1.
          apply memset_correct.
          intros ms st (?&?&?).
          cbn in *.
          repeat red in H3.
          destruct H3 as (?&?&?).
          cbn in *.
          rewrite H3, bind_ret_l, H1 in H5.
          eapply eq1_ret_ret in H5; try typeclasses eauto.
          inv H5.
          lia.
        }
        auto.
      }
    Qed.

    Lemma malloc_bytes_correct :
      forall bytes,
        exec_correct
          (fun ms st => Forall (fun b : BYTE_IMPL.SByte => exists s : store_id, MemByte.sbyte_sid b = inr s /\ s < st) bytes)
          (malloc_bytes bytes) (malloc_bytes_spec_MemPropT bytes) exec_correct_id_post.
    Proof using Type.
      intros bytes.
      eapply exec_correct_strengthen_post; cycle 1.
      { apply exec_correct_bind.
        apply exec_correct_fresh_provenance.
        intros a ms_init ms_after_m st_init st_after_m H H0 H1 WEM.
        eapply exec_correct_weaken_pre; cycle 1.
        apply malloc_bytes_with_pr_correct.

        intros ms st (?&?&?).
        cbn in H3.
        repeat red in H3.
        destruct H3 as (?&?&?).
        cbn in H3.
        cbn in H5.
        rewrite H3, bind_ret_l, H1 in H5.
        eapply eq1_ret_ret in H5; try typeclasses eauto.
        inv H5.
        auto.
        destruct H0 as (?&?&?&?).
        subst.
        auto.
      }
      auto.
    Qed.

    Hint Resolve malloc_bytes_correct : EXEC_CORRECT.

    Lemma handle_malloc_correct:
      forall args pre,
        exec_correct pre (handle_malloc args) (handle_malloc_prop args) exec_correct_id_post.
    Proof using Type.
      intros args pre.
      unfold handle_malloc, handle_malloc_prop.
      repeat (break_match;
              try solve
                [ eapply exec_correct_strengthen_post; cycle 1;
                  [apply exec_correct_raise_error|eauto]]).

      { eapply exec_correct_weaken_pre; cycle 1.
        eapply exec_correct_strengthen_post; cycle 1.
        { eapply exec_correct_bind;
            eauto with EXEC_CORRECT.
          intros * VALID POST RUN.
          eapply exec_correct_bind;
            eauto with EXEC_CORRECT.
          intros * VALID' POST' RUN'.
          eapply exec_correct_weaken_pre; cycle 1.
          eapply malloc_bytes_correct.
          intros ms st H.
          cbn.
          unfold lift_OOM in POST'.
          break_match_hyp_inv.
          eapply generate_num_undef_bytes_bounded; eauto.
          destruct POST as (?&?&?); subst.
          destruct H as (?&?&?&?); subst.
          destruct H1; subst.
          destruct H as (?&?&?).
          repeat red in H3.
          destruct H3 as (?&?&?).
          cbn in H3.
          cbn in H6.
          rewrite H3 in H6.
          rewrite MemMonad_run_ret, bind_ret_l in H6.
          eapply eq1_ret_ret in H6; try typeclasses eauto.
          inv H6.
          cbn in H1.
          repeat red in H1.
          destruct H1 as (?&?&?).
          cbn in *.
          rewrite H1, bind_ret_l in H6.
          rewrite RUN in H6.
          eapply eq1_ret_ret in H6; try typeclasses eauto.
          inv H6.
          lia.
        }
        
        eauto with EXEC_CORRECT.
        eauto with EXEC_CORRECT.
      }
      { eapply exec_correct_weaken_pre; cycle 1.
        eapply exec_correct_strengthen_post; cycle 1.
        { eapply exec_correct_bind;
            eauto with EXEC_CORRECT.
          intros * VALID POST RUN.
          eapply exec_correct_bind;
            eauto with EXEC_CORRECT.
          intros * VALID' POST' RUN'.
          eapply exec_correct_weaken_pre; cycle 1.
          eapply malloc_bytes_correct.
          intros ms st H.
          cbn.
          unfold lift_OOM in POST'.
          break_match_hyp_inv.
          eapply generate_num_undef_bytes_bounded; eauto.
          destruct POST as (?&?&?); subst.
          destruct H as (?&?&?&?); subst.
          destruct H1; subst.
          destruct H as (?&?&?).
          repeat red in H3.
          destruct H3 as (?&?&?).
          cbn in H3.
          cbn in H6.
          rewrite H3 in H6.
          rewrite MemMonad_run_ret, bind_ret_l in H6.
          eapply eq1_ret_ret in H6; try typeclasses eauto.
          inv H6.
          cbn in H1.
          repeat red in H1.
          destruct H1 as (?&?&?).
          cbn in *.
          rewrite H1, bind_ret_l in H6.
          rewrite RUN in H6.
          eapply eq1_ret_ret in H6; try typeclasses eauto.
          inv H6.
          lia.
        }
        
        eauto with EXEC_CORRECT.
        eauto with EXEC_CORRECT.
      }
      { eapply exec_correct_weaken_pre; cycle 1.
        eapply exec_correct_strengthen_post; cycle 1.
        { eapply exec_correct_bind;
            eauto with EXEC_CORRECT.
          intros * VALID POST RUN.
          eapply exec_correct_bind;
            eauto with EXEC_CORRECT.
          intros * VALID' POST' RUN'.
          eapply exec_correct_weaken_pre; cycle 1.
          eapply malloc_bytes_correct.
          intros ms st H.
          cbn.
          unfold lift_OOM in POST'.
          break_match_hyp_inv.
          eapply generate_num_undef_bytes_bounded; eauto.
          destruct POST as (?&?&?); subst.
          destruct H as (?&?&?&?); subst.
          destruct H1; subst.
          destruct H as (?&?&?).
          repeat red in H3.
          destruct H3 as (?&?&?).
          cbn in H3.
          cbn in H6.
          rewrite H3 in H6.
          rewrite MemMonad_run_ret, bind_ret_l in H6.
          eapply eq1_ret_ret in H6; try typeclasses eauto.
          inv H6.
          cbn in H1.
          repeat red in H1.
          destruct H1 as (?&?&?).
          cbn in *.
          rewrite H1, bind_ret_l in H6.
          rewrite RUN in H6.
          eapply eq1_ret_ret in H6; try typeclasses eauto.
          inv H6.
          lia.
        }
        
        eauto with EXEC_CORRECT.
        eauto with EXEC_CORRECT.
      }
      { eapply exec_correct_weaken_pre; cycle 1.
        eapply exec_correct_strengthen_post; cycle 1.
        { eapply exec_correct_bind;
            eauto with EXEC_CORRECT.
          intros * VALID POST RUN.
          eapply exec_correct_bind;
            eauto with EXEC_CORRECT.
          intros * VALID' POST' RUN'.
          eapply exec_correct_weaken_pre; cycle 1.
          eapply malloc_bytes_correct.
          intros ms st H.
          cbn.
          unfold lift_OOM in POST'.
          break_match_hyp_inv.
          eapply generate_num_undef_bytes_bounded; eauto.
          destruct POST as (?&?&?); subst.
          destruct H as (?&?&?&?); subst.
          destruct H1; subst.
          destruct H as (?&?&?).
          repeat red in H3.
          destruct H3 as (?&?&?).
          cbn in H3.
          cbn in H6.
          rewrite H3 in H6.
          rewrite MemMonad_run_ret, bind_ret_l in H6.
          eapply eq1_ret_ret in H6; try typeclasses eauto.
          inv H6.
          cbn in H1.
          repeat red in H1.
          destruct H1 as (?&?&?).
          cbn in *.
          rewrite H1, bind_ret_l in H6.
          rewrite RUN in H6.
          eapply eq1_ret_ret in H6; try typeclasses eauto.
          inv H6.
          lia.
        }
        
        eauto with EXEC_CORRECT.
        eauto with EXEC_CORRECT.
      }
      { eapply exec_correct_weaken_pre; cycle 1.
        eapply exec_correct_strengthen_post; cycle 1.
        { eapply exec_correct_bind;
            eauto with EXEC_CORRECT.
          intros * VALID POST RUN.
          eapply exec_correct_bind;
            eauto with EXEC_CORRECT.
          intros * VALID' POST' RUN'.
          eapply exec_correct_weaken_pre; cycle 1.
          eapply malloc_bytes_correct.
          intros ms st H.
          cbn.
          unfold lift_OOM in POST'.
          break_match_hyp_inv.
          eapply generate_num_undef_bytes_bounded; eauto.
          destruct POST as (?&?&?); subst.
          destruct H as (?&?&?&?); subst.
          destruct H1; subst.
          destruct H as (?&?&?).
          repeat red in H3.
          destruct H3 as (?&?&?).
          cbn in H3.
          cbn in H6.
          rewrite H3 in H6.
          rewrite MemMonad_run_ret, bind_ret_l in H6.
          eapply eq1_ret_ret in H6; try typeclasses eauto.
          inv H6.
          cbn in H1.
          repeat red in H1.
          destruct H1 as (?&?&?).
          cbn in *.
          rewrite H1, bind_ret_l in H6.
          rewrite RUN in H6.
          eapply eq1_ret_ret in H6; try typeclasses eauto.
          inv H6.
          lia.
        }
        
        eauto with EXEC_CORRECT.
        eauto with EXEC_CORRECT.
      }
      { eapply exec_correct_weaken_pre; cycle 1.
        eapply exec_correct_strengthen_post; cycle 1.
        { eapply exec_correct_bind;
            eauto with EXEC_CORRECT.
          intros * VALID POST RUN.
          eapply exec_correct_bind;
            eauto with EXEC_CORRECT.
          intros * VALID' POST' RUN'.
          eapply exec_correct_weaken_pre; cycle 1.
          eapply malloc_bytes_correct.
          intros ms st H.
          cbn.
          unfold lift_OOM in POST'.
          break_match_hyp_inv.
          eapply generate_num_undef_bytes_bounded; eauto.
          destruct POST as (?&?&?); subst.
          destruct H as (?&?&?&?); subst.
          destruct H1; subst.
          destruct H as (?&?&?).
          repeat red in H3.
          destruct H3 as (?&?&?).
          cbn in H3.
          cbn in H6.
          rewrite H3 in H6.
          rewrite MemMonad_run_ret, bind_ret_l in H6.
          eapply eq1_ret_ret in H6; try typeclasses eauto.
          inv H6.
          cbn in H1.
          repeat red in H1.
          destruct H1 as (?&?&?).
          cbn in *.
          rewrite H1, bind_ret_l in H6.
          rewrite RUN in H6.
          eapply eq1_ret_ret in H6; try typeclasses eauto.
          inv H6.
          lia.
        }
        
        eauto with EXEC_CORRECT.
        eauto with EXEC_CORRECT.
      }
    Qed.

    Lemma handle_free_correct:
      forall args pre,
        exec_correct pre (handle_free args) (handle_free_prop args) exec_correct_id_post.
    Proof using Type.
      intros args pre.
      unfold handle_free, handle_free_prop.
      repeat (break_match;
              try solve
                [ eapply exec_correct_strengthen_post; cycle 1;
                  [apply exec_correct_raise_error|eauto]]).
      subst.
      all: apply free_correct.
    Qed.

    Lemma handle_intrinsic_correct:
      forall T (e : IntrinsicE T) pre,
        exec_correct pre (handle_intrinsic T e) (handle_intrinsic_prop T e) exec_correct_id_post.
    Proof using Type.
      intros T e pre.
      unfold handle_intrinsic, handle_intrinsic_prop.
      break_match.
      break_match.
      { (* Memcpy *)
        eapply exec_correct_strengthen_post; cycle 1.
        { apply exec_correct_bind.
          apply handle_memcpy_correct.
          intros * VALID POST RUN.
          apply exec_correct_ret.
        }
        auto.
      }

      break_match.
      { (* Memset *)
        eapply exec_correct_strengthen_post; cycle 1.
        { apply exec_correct_bind.
          apply handle_memset_correct.
          intros * VALID POST RUN.
          apply exec_correct_ret.
        }
        auto.
      }

      break_match.
      { (* Malloc *)
        eapply exec_correct_strengthen_post; cycle 1.
        { apply exec_correct_bind.
          apply handle_malloc_correct.
          intros * VALID POST RUN.
          eapply exec_correct_ret.
        }
        auto.
      }

      break_match.
      { (* Free *)
        eapply exec_correct_strengthen_post; cycle 1.
        { apply exec_correct_bind.
          apply handle_free_correct.
          intros * VALID POST RUN.
          eapply exec_correct_ret.
        }
        auto.
      }

      apply exec_correct_raise_error.
    Qed.
  End Correctness.

  Import LP.PROV.
  Import LP.SIZEOF.
  Import LP.ADDR.

  Lemma find_free_block_inv :
    forall len pr ms_init
      (res : err_ub_oom (MemState * (addr * list addr)))
      (FIND : find_free_block len pr ms_init res),
      (* Success *)
      (exists ptr ptrs,
          res = ret (ms_init, (ptr, ptrs))) \/
        (* OOM *)
        (exists oom_msg,
            res = raise_oom oom_msg).
  Proof.
    intros len pr ms_init res FIND.
    unfold find_free_block in FIND.
    cbn in *.
    destruct res as [[[[[[[oom_res] | [[ub_res] | [[err_res] | res']]]]]]]] eqn:Hres;
      cbn in *; try contradiction.

    - (* OOM *)
      right.
      exists oom_res.
      reflexivity.
    - (* Success *)
      destruct res' as [ms' [ptr ptrs]].
      destruct FIND as [MEQ BLOCKFREE].
      subst.
      left.
      do 2 eexists.
      reflexivity.
  Qed.

  Lemma allocate_bytes_spec_MemPropT_no_ub :
    forall (ms_init : MemState)
      bytes
      (ub_msg : string),
      ~ allocate_bytes_spec_MemPropT bytes ms_init (raise_ub ub_msg).
  Proof.
    intros ms_init bytes ub_msg CONTRA.

    unfold allocate_bytes_spec_MemPropT in CONTRA.
    cbn in CONTRA.
    destruct CONTRA as [[] | [ms' [pr' [FRESH [[] | CONTRA]]]]].
    destruct CONTRA as [ms'' [[ptr ptrs] [[EQ BLOCKFREE] CONTRA]]]; subst.
    destruct CONTRA as [CONTRA | CONTRA]; try contradiction.
    destruct CONTRA as [ms''' [[ptr' ptrs'] [POST CONTRA]]]; contradiction.
  Qed.

  Lemma allocate_bytes_spec_MemPropT_no_err :
    forall (ms_init : MemState)
      bytes
      (err_msg : string),
      ~ allocate_bytes_spec_MemPropT bytes ms_init (raise_error err_msg).
  Proof.
    intros ms_init bytes err_msg CONTRA.

    unfold allocate_bytes_spec_MemPropT in CONTRA.
    cbn in CONTRA.
    destruct CONTRA as [[] | [ms' [pr' [FRESH [[] | CONTRA]]]]].
    destruct CONTRA as [ms'' [[ptr ptrs] [[EQ BLOCKFREE] CONTRA]]]; subst.
    destruct CONTRA as [[] | [ms''' [[ptr' ptrs'] [POST []]]]].
  Qed.

  Lemma allocate_bytes_spec_MemPropT_inv :
    forall (ms_init : MemState)
      bytes
      (res : err_ub_oom (MemState * LP.ADDR.addr))
      (ALLOC : allocate_bytes_spec_MemPropT bytes ms_init res),
      (exists ms_final ptr,
          res = ret (ms_final, ptr)) \/
        (exists oom_msg,
            res = raise_oom oom_msg).
  Proof.
    intros ms_init bytes res ALLOC.
    unfold allocate_bytes_spec_MemPropT in ALLOC.
    destruct res as [[[[[[[oom_res] | [[ub_res] | [[err_res] | res']]]]]]]] eqn:Hres;
      cbn in *; try contradiction.
    - (* OOM *)
      right. eexists; reflexivity.
    - (* UB *)
      destruct ALLOC as [[] | [ms' [pr' [FRESH [[] | ALLOC]]]]].
      destruct ALLOC as [ms'' [[ptr ptrs] [[MEQ BLOCKFREE] [UB | ALLOC]]]];
        try contradiction; subst.

      destruct ALLOC as [ms''' [[ptr' ptrs'] ALLOC]].
      tauto.
    - (* Error *)
      destruct ALLOC as [[] | [ms' [pr' [FRESH [[] | ALLOC]]]]].
      destruct ALLOC as [ms'' [[ptr ptrs] [[MEQ BLOCKFREE] [[] | ALLOC]]]].
      destruct ALLOC as [ms''' [[ptr' ptrs'] ALLOC]].
      tauto.
    - (* Success *)
      destruct res' as [ms a].
      subst.
      left.

      destruct ALLOC as [ms' [pr' [FRESH ALLOC]]].
      destruct ALLOC as [ms'' [[ptr ptrs] [[MEQ BLOCKFREE] ALLOC]]]; subst.
      destruct ALLOC as [ms''' [[ptr' ptrs'] ALLOC]].
      destruct ALLOC as [[POST [PTREQ PTRSEQ]] [MEQ PTREQ']].
      subst.
      repeat eexists.
  Qed.

  Lemma repeatMN_MemPropT_length :
    forall {A} n (ma : MemPropT MemState A) ms ms' a,
      repeatMN n ma ms (ret (ms', a)) -> length a = N.to_nat n.
  Proof.
    intros A n.
    induction n using N.peano_rect; intros ma ms ms' a REP.
    - cbn in *.
      destruct REP as [MEQ AEQ]; subst.
      reflexivity.
    - rewrite repeatMN_succ in REP.
      cbn in REP.
      destruct REP as [ms1 [a0 [M [ms2 [a1 [REP [MEQ AEQ]]]]]]]; subst.
      cbn.
      apply IHn in REP.
      lia.
  Qed.

  Lemma allocate_dtyp_spec_inv :
    forall (ms_init : MemState) dt num_elements
      (NON_VOID : dt <> DTYPE_Void)
      (res : err_ub_oom (MemState * LP.ADDR.addr))
      (ALLOC : allocate_dtyp_spec dt num_elements ms_init res),
      (exists ms_final ptr,
          res = ret (ms_final, ptr)) \/
        (exists oom_msg,
            res = raise_oom oom_msg).
  Proof.
    intros ms_init dt num_elements NON_VOID res ALLOC.
    unfold allocate_dtyp_spec in *.
    Opaque allocate_bytes_spec_MemPropT.
    cbn in ALLOC.

    destruct res as [[[[[[[oom_res] | [[ub_res] | [[err_res] | res']]]]]]]] eqn:Hres;
      cbn in *; try contradiction.
    - (* OOM *)
      right. eexists; reflexivity.
    - (* UB *)
      destruct ALLOC as [UB | ALLOC]; try contradiction.
      destruct ALLOC as [ms' [[] [[MS NVOID] [UB | ALLOC]]]]; try contradiction.
      symmetry in MS; subst.
      destruct ALLOC as [ms' [sid [FRESH [GEN | ALLOC]]]].
      { induction num_elements using N.peano_rect; [cbn in *; contradiction|].
        rewrite repeatMN_succ in GEN.
        destruct (generate_undef_bytes dt sid); cbn in *.
        + destruct GEN as [[] | [ms'' [l' [[MEQ LEQ] GEN]]]]; subst.
          destruct GEN as [GEN | [ms'' [l' [GEN []]]]]; eauto.
        + destruct GEN as [[] | [ms'' [l' [[] GEN]]]].
      }

      destruct ALLOC as [ms'' [bytes [GEN ALLOC]]].
      destruct (generate_undef_bytes dt sid) eqn:HGEN; cbn in *.
      { assert (length bytes = N.to_nat num_elements) as LBYTES.
        { eapply repeatMN_MemPropT_length.
          eapply GEN.
        }

        assert (forall bs, In bs bytes -> length bs = N.to_nat (sizeof_dtyp dt)) as LBS.
        { apply generate_undef_bytes_length in HGEN.
          intros bs IN.
          clear - HGEN GEN IN.
          revert bytes GEN bs IN.
          induction num_elements using N.peano_rect; intros bytes GEN bs IN.
          - cbn in GEN.
            destruct GEN as [MEQ BYTES]; subst.
            inversion IN.
          - rewrite repeatMN_succ in GEN.
            cbn in GEN.
            destruct GEN as [ms''' [l' [[MEQ LEQ] GEN]]]; subst.
            destruct GEN as [ms''' [l' [GEN [MEQ LEQ]]]]; subst.
            destruct IN as [IN | IN]; subst; eauto; lia.
        }

        assert (length (concat bytes) = N.to_nat (sizeof_dtyp dt * num_elements)%N) as LCONCAT.
        { erewrite concat_length; eauto.
          lia.
        }

        clear - ALLOC NON_VOID GEN LCONCAT.
        Transparent allocate_bytes_spec_MemPropT.
        unfold allocate_bytes_spec_MemPropT in *.
        cbn in *.
        destruct ALLOC as [[] | [ms''' [pr [FRESH_PR [[] | ALLOC]]]]].
        destruct ALLOC as [ms'''' [[ptr ptrs] ALLOC]].
        destruct ALLOC as [[MEQ BLOCK_FREE] [UB | [_ [_ [_ []]]]]]; contradiction.
      }

      { induction num_elements using N.peano_rect.
        + cbn in GEN.
          destruct GEN as [MEQ BYTES]; subst.
          cbn in ALLOC.
          Transparent allocate_bytes_spec_MemPropT.
          unfold allocate_bytes_spec_MemPropT in *.
          cbn in *.
          destruct ALLOC as [[] | [ms'' [pr [FRESH_PR [[] | ALLOC]]]]].
          destruct ALLOC as [ms''' [[ptr ptrs] ALLOC]].
          destruct ALLOC as [[MEQ BLOCK_FREE] [UB | [_ [_ [_ []]]]]]; contradiction.
          Opaque allocate_bytes_spec_MemPropT.
        + rewrite repeatMN_succ in GEN.
          cbn in GEN.
          destruct GEN as [ms''' [a [[] _]]].
      }
    - (* Error *)
      destruct ALLOC as [UB | ALLOC]; try contradiction.
      destruct ALLOC as [ms' [[] [[MS NVOID] [UB | ALLOC]]]]; try contradiction.
      symmetry in MS; subst.
      destruct ALLOC as [ms' [sid [FRESH [GEN | ALLOC]]]].
      { induction num_elements using N.peano_rect; [cbn in *; contradiction|].
        rewrite repeatMN_succ in GEN.
        destruct (generate_undef_bytes dt sid); cbn in *.
        + destruct GEN as [[] | [ms'' [l' [[MEQ LEQ] GEN]]]]; subst.
          destruct GEN as [GEN | [ms'' [l' [GEN []]]]]; eauto.
        + destruct GEN as [[] | [ms'' [l' [[] GEN]]]].
      }

      destruct ALLOC as [ms'' [bytes [GEN ALLOC]]].
      destruct (generate_undef_bytes dt sid) eqn:HGEN; cbn in *.
      { cbn in ALLOC.
        Transparent allocate_bytes_spec_MemPropT.
        unfold allocate_bytes_spec_MemPropT in *.
        cbn in *.
        destruct ALLOC as [[] | [ms''' [pr [FRESH_PR [[] | ALLOC]]]]].
        destruct ALLOC as [ms'''' [[ptr ptrs] ALLOC]].
        destruct ALLOC as [[MEQ BLOCK_FREE] [[] | [_ [_ [_ []]]]]].
        Opaque allocate_bytes_spec_MemPropT.
      }

      { induction num_elements using N.peano_rect.
        + cbn in GEN.
          destruct GEN as [MEQ BYTES]; subst.
          cbn in ALLOC.
          Transparent allocate_bytes_spec_MemPropT.
          unfold allocate_bytes_spec_MemPropT in *.
          cbn in *.
          destruct ALLOC as [[] | [ms'' [pr [FRESH_PR [[] | ALLOC]]]]].
          destruct ALLOC as [ms''' [[ptr ptrs] ALLOC]].
          destruct ALLOC as [[MEQ BLOCK_FREE] [[] | [_ [_ [_ []]]]]].
          Opaque allocate_bytes_spec_MemPropT.
        + rewrite repeatMN_succ in GEN.
          cbn in GEN.
          destruct GEN as [ms''' [a [[] _]]].
      }
    - (* Success *)
      destruct res' as [ms a].
      subst.
      left.
      repeat eexists.
      Transparent allocate_bytes_spec_MemPropT.
  Qed.

End MemoryModelTheory.

Module MemStateInfiniteHelpers (LP : LLVMParamsBig) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) (MMS : MemoryModelSpec LP MP MMSP).
  (* Intptrs are "big" *)
  Import LP.Events.
  Import LP.ITOP.
  Import LP.PTOI.
  Import LP.IP_BIG.
  Import LP.IP.
  Import LP.ADDR.
  Import LP.PROV.
  Import LP.SIZEOF.

  Import MMSP.
  Import MMS.
  Import MemHelpers.

  Import Monad.
  Import MapMonadExtra.
  Import MP.GEP.
  Import MP.BYTE_IMPL.

  Import Util.

  (*
    Things that must succeed:

    - get_consecutive_ptrs: May need something in GepM for this.
    - byte_allocated: for all of the consecutive pointers

   *)

  (* TODO: Move to something like IP_BIG? *)
  Lemma big_intptr_seq_succeeds :
    forall start len,
    exists ips, intptr_seq start len = NoOom ips.
  Proof.
    intros start len.
    unfold intptr_seq.
    induction (Zseq start len).
    - cbn. exists []. reflexivity.
    - rewrite map_monad_unfold.
      cbn.
      break_match.
      2: {
        pose proof (from_Z_safe a) as CONTRA.
        rewrite Heqo in CONTRA.
        contradiction.
      }

      destruct IHl as (ips & IHl).
      exists (i :: ips).
      setoid_rewrite functional_extensionality.
      rewrite IHl.
      reflexivity.
      reflexivity.
  Qed.

  #[global] Instance lift_err_RAISE_ERROR_Proper {A M} `{HM: Monad M} `{RAISE: RAISE_ERROR M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM} :
    Proper (eq ==> eq1) (@lift_err_RAISE_ERROR A M HM RAISE).
  Proof.
    unfold Proper, respectful.
    intros x y H; subst.
    reflexivity.
  Defined.

  Lemma get_consecutive_ptrs_succeeds :
    forall {M : Type -> Type}
      `{HM: Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM}
      `{EQRET : @Eq1_ret_inv M EQM HM}
      `{OOM: RAISE_OOM M} `{ERR: RAISE_ERROR M}
      `{LAWS: @MonadLawsE M EQM HM}
      ptr len,
    exists ptrs, (get_consecutive_ptrs ptr len ≈ ret ptrs)%monad.
  Proof.
    intros M HM EQM EQV EQRET OOM ERR LAWS ptr len.

    Opaque handle_gep_addr.

    unfold get_consecutive_ptrs.
    pose proof big_intptr_seq_succeeds 0 len as (ips & SEQ).
    rewrite SEQ.
    cbn.

    pose proof map_monad_err_succeeds
         (fun ix : intptr =>
            handle_gep_addr (DTYPE_I 8) ptr [LP.Events.DV.DVALUE_IPTR ix])
         ips as HMAPM.

    forward HMAPM.
    { intros a IN.
      destruct (int_to_ptr (ptr_to_int ptr + Z.of_N (sizeof_dtyp (DTYPE_I 8)) * LP.IP.to_Z a)%Z (address_provenance ptr)) eqn:IX.
      - exists (ret a0).
        apply handle_gep_addr_ix'; cbn; auto.
      - eapply handle_gep_addr_ix'_OOM in IX; auto.
        destruct IX as [msg' IX].
        exists (Oom msg').
        cbn; auto.
    }

    destruct HMAPM as (res & HMAPM).
    destruct (Monads.sequence res) eqn:HSEQUENCE.
    { rename l into ptrs.
      exists ptrs.
      rewrite bind_ret_l.
      rewrite HMAPM.
      cbn.
      rewrite bind_ret_l.
      rewrite HSEQUENCE.
      cbn.
      reflexivity.
    }
    { apply map_monad_OOM_fail in HSEQUENCE as [a [IN EQA]].
      unfold id in EQA. subst.

      pose proof map_monad_err_In _ _ _ _ HMAPM IN as [ix [GEP INix]].
      apply handle_gep_addr_ix_OOM in GEP; auto.
      destruct GEP as [msg' GEP].
      pose proof
        (LP.I2P_BIG.int_to_ptr_safe (ptr_to_int ptr + Z.of_N (sizeof_dtyp (DTYPE_I 8)) * to_Z ix)
           (address_provenance ptr)) as SAFE.
      rewrite GEP in SAFE.
      contradiction.
    }
  Qed.

End MemStateInfiniteHelpers.

Module Type MemoryModelInfiniteSpec (LP : LLVMParamsBig) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) (MMS : MemoryModelSpec LP MP MMSP).
  (* Intptrs are "big" *)
  Import LP.Events.
  Import LP.ITOP.
  Import LP.PTOI.
  Import LP.IP_BIG.
  Import LP.IP.
  Import LP.ADDR.
  Import LP.PROV.
  Import LP.SIZEOF.

  Import MMSP.
  Import MMS.
  Import MemHelpers.

  Import Monad.
  Import MapMonadExtra.
  Import MP.GEP.
  Import MP.BYTE_IMPL.

  Parameter find_free_block_can_always_succeed :
    forall ms (len : nat) (pr : Provenance),
    exists ptr ptrs,
      ret (ptr, ptrs) {{ms}} ∈ {{ms}} find_free_block len pr.

  Parameter allocate_bytes_post_conditions_can_always_be_satisfied :
    forall (ms_init : MemState) bytes pr,
    exists ms_final ptr ptrs,
      (ret (ptr, ptrs) {{ms_init}} ∈ {{ms_init}} find_free_block (length bytes) pr) /\
      allocate_bytes_post_conditions ms_init bytes pr ms_final ptr ptrs.

End MemoryModelInfiniteSpec.

Module MemoryModelInfiniteSpecHelpers (LP : LLVMParamsBig) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) (MMS : MemoryModelSpec LP MP MMSP) (MMIS : MemoryModelInfiniteSpec LP MP MMSP MMS).
  Import LP.Events.
  Import LP.ITOP.
  Import LP.PTOI.
  Import LP.IP_BIG.
  Import LP.IP.
  Import LP.ADDR.
  Import LP.PROV.
  Import LP.SIZEOF.

  Import MMSP.
  Import MMS.
  Import MemHelpers.

  Import Monad.
  Import MapMonadExtra.
  Import MP.GEP.
  Import MP.BYTE_IMPL.

  Import MMIS.

  Lemma allocate_bytes_with_pr_spec_MemPropT_can_always_succeed :
    forall (ms_init : MemState)
      bytes pr,
    exists ms_final ptr,
      ret ptr {{ms_init}} ∈ {{ms_final}} allocate_bytes_with_pr_spec_MemPropT bytes pr.
  Proof.
    intros ms_init bytes pr.
    unfold allocate_bytes_spec_MemPropT.

    pose proof allocate_bytes_post_conditions_can_always_be_satisfied ms_init bytes pr as (ms_final & ptr & ptrs & (_ & BLOCK_FREE) & ALLOC).

    exists ms_final. exists ptr.
    cbn.

    (* Find free block *)
    exists ms_init. exists (ptr, ptrs).
    split; eauto.

    (* Post conditions *)
    exists ms_final. exists (ptr, ptrs).
    split; split; auto.
  Qed.

  Lemma allocate_bytes_spec_MemPropT_can_always_succeed :
    forall (ms_init ms_fresh_pr : MemState)
      bytes
      (pr : Provenance)
      (FRESH_PR : (fresh_provenance ms_init (ret (ms_fresh_pr, pr)))),
    exists ms_final ptr,
      ret ptr {{ms_init}} ∈ {{ms_final}} allocate_bytes_spec_MemPropT bytes.
  Proof.
    intros ms_init ms_fresh_pr bytes pr FRESH_PR.
    unfold allocate_bytes_spec_MemPropT.

    pose proof allocate_bytes_with_pr_spec_MemPropT_can_always_succeed ms_fresh_pr bytes pr as (ms_final & ptr & ALLOC).

    exists ms_final. exists ptr.
    exists ms_fresh_pr. exists pr.
    split; auto.
  Qed.

  (* TODO: should this be here? *)
  Lemma generate_num_undef_bytes_h_cons :
    forall dt len sid start bytes,
      generate_num_undef_bytes_h (N.succ start) len dt sid = NoOom bytes ->
      generate_num_undef_bytes_h start (N.succ len) dt sid =
        b <- generate_num_undef_bytes_h start 1 dt sid;;
        rest <- generate_num_undef_bytes_h (N.succ start) len dt sid;;
        NoOom (b ++ rest).
  Proof.
    intros dt len sid start bytes NOOM.
    cbn.
    unfold generate_num_undef_bytes_h in *.
    match goal with
    | H: _ |- N.recursion ?a ?f _ _ = _ =>
        pose proof
          (@N.recursion_succ (N -> OOM (list SByte)) eq
             a
             f
          ) as S
    end.
    forward S.
    reflexivity.
    forward S.
    { unfold Proper, respectful.
      intros x y H0 x0 y0 H1; subst.
      reflexivity.
    }

    specialize (S len).
    cbn in *.
    rewrite S.

    break_match; auto.
  Qed.

  (* TODO: should this be here? *)
  Lemma generate_num_undef_bytes_h_succeeds :
    forall dt sid start,
    exists bytes : list SByte, generate_num_undef_bytes_h start (sizeof_dtyp dt) dt sid = ret bytes.
  Proof.
    intros dt.
    induction (sizeof_dtyp dt) using N.peano_ind;
      intros sid start.

    - cbn; eexists; auto.
    - specialize (IHn sid (N.succ start)).
      destruct IHn as [bytes IHn].
      pose proof (from_Z_safe (Z.of_N start)).
      break_match_hyp; [|contradiction].

      eexists.
      erewrite generate_num_undef_bytes_h_cons; eauto.
      rewrite IHn.
      cbn.
      reflexivity.
  Qed.


  (* TODO: should this be here? *)
  Lemma generate_num_undef_bytes_succeeds :
    forall dt sid,
    exists bytes : list SByte, generate_num_undef_bytes (sizeof_dtyp dt) dt sid = ret bytes.
  Proof.
    intros dt sid.
    eapply generate_num_undef_bytes_h_succeeds.
  Qed.

  (* TODO: should this be here? *)
  Lemma generate_undef_bytes_succeeds :
    forall dt sid,
    exists bytes, generate_undef_bytes dt sid = ret bytes.
  Proof.
    intros dt sid.
    unfold generate_undef_bytes.
    apply generate_num_undef_bytes_succeeds.
  Qed.

  Lemma repeatMN_MemPropT_length :
    forall {A} n (ma : MemPropT MemState A) ms ms' a,
      repeatMN n ma ms (ret (ms', a)) -> length a = N.to_nat n.
  Proof.
    intros A n.
    induction n using N.peano_rect; intros ma ms ms' a REP.
    - cbn in *.
      destruct REP as [MEQ AEQ]; subst.
      reflexivity.
    - rewrite repeatMN_succ in REP.
      cbn in REP.
      destruct REP as [ms1 [a0 [M [ms2 [a1 [REP [MEQ AEQ]]]]]]]; subst.
      cbn.
      apply IHn in REP.
      lia.
  Qed.

  Lemma allocate_dtyp_spec_can_always_succeed :
    forall (ms_init ms_fresh_sid ms_fresh_pr : MemState) dt num_elements pr sid
      (FRESH_SID : (ret sid {{ms_init}} ∈ {{ms_fresh_sid}} fresh_sid))
      (FRESH_PR : (ret pr {{ms_fresh_sid}} ∈ {{ms_fresh_pr}} fresh_provenance))
      (NON_VOID : dt <> DTYPE_Void),
    exists ms_final ptr,
      ret ptr {{ms_init}} ∈ {{ms_final}} allocate_dtyp_spec dt num_elements.
  Proof.
    intros ms_init ms_fresh_sid ms_fresh_pr dt num_elements pr sid FRESH_SID FRESH_PR NON_VOID.

    unfold allocate_dtyp_spec.

    pose proof generate_undef_bytes_succeeds dt sid as (bytes_dt & UNDEF_BYTES).
    pose proof generate_undef_bytes_length dt sid bytes_dt UNDEF_BYTES as BYTES_SIZE.
    assert (exists bytes, repeatMN num_elements (@ret (MemPropT MemState) _ _ bytes_dt) ms_fresh_sid (ret (ms_fresh_sid, bytes))) as (bytes & BYTES).
    { exists (repeatN num_elements bytes_dt).
      induction num_elements using N.peano_rect.
      - cbn; split; auto.
      - rewrite repeatMN_succ.
        cbn.
        repeat eexists.
        + cbn in *; eauto.
        + rewrite repeatN_succ.
          auto.
    }

    assert (length bytes = N.to_nat num_elements) as LBYTES.
    { eapply repeatMN_MemPropT_length with (ma:=ret bytes_dt); eauto.
    }

    assert (forall bs, In bs bytes -> length bs = length bytes_dt) as LBS.
    {
      clear - BYTES_SIZE BYTES.
      revert bytes BYTES.
      induction num_elements using N.peano_rect; intros bytes BYTES bs IN.
      - cbn in *.
        destruct BYTES as [MEQ BYTES]; subst.
        inversion IN.
      - rewrite repeatMN_succ in BYTES.
        cbn in BYTES.
        destruct BYTES as [ms''' [l' [[MEQ LEQ] GEN]]]; subst.
        destruct GEN as [ms''' [l' [GEN [MEQ LEQ]]]]; subst.
        destruct IN as [IN | IN]; subst; eauto.
        eapply IHnum_elements; cbn; eauto.
    }

    assert (length (concat bytes) = N.to_nat (sizeof_dtyp dt * num_elements)%N) as LCONCAT.
    { erewrite concat_length with (len:=length bytes_dt); eauto.
      lia.
    }

    assert ((sizeof_dtyp dt * num_elements)%N = N.of_nat (Datatypes.length (concat bytes))) as SIZE by lia.

    pose proof allocate_bytes_spec_MemPropT_can_always_succeed
         ms_fresh_sid ms_fresh_pr (concat bytes) pr FRESH_PR
      as (ms_final & ptr & ALLOC_SUCCESS).

    exists ms_final, ptr.
    repeat red.
    exists ms_init, tt.
    split.
    { cbn.
      split; eauto.
    }
    exists ms_fresh_sid, sid; split; auto.

    rewrite UNDEF_BYTES.
    Opaque allocate_bytes_spec_MemPropT.
    cbn.
    Transparent allocate_bytes_spec_MemPropT.

    exists ms_fresh_sid, bytes.
    tauto.
  Qed.
End MemoryModelInfiniteSpecHelpers.
