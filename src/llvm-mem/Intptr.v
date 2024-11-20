From Stdlib Require Import
  ZArith
  List
  Lia.

From Vellvm Require Import
  Semantics.VellvmIntegers
  Util
  Utils.Error
  Utils.ListUtil
  Utils.Tactics
  Utils.MonadReturnsLaws
  Utils.MapMonadExtra
  DynamicTypes
  Monads.

From ExtLib Require Import
  Structures.Monad.

Import MonadNotation.
Import ListNotations.

Module Type INTPTR_CORE.
  Parameter intptr : Set.
  Parameter zero : intptr.

  Parameter VMemInt_intptr : VMemInt intptr.

  Parameter eq_dec : forall (a b : intptr), {a = b} + {a <> b}.
  Parameter eqb : forall (a b : intptr), bool.

  Parameter to_Z : forall (a : intptr), Z.
  Parameter to_unsigned : forall (a : intptr), Z.
  Parameter from_Z : Z -> OOM intptr.

  Parameter from_Z_to_Z :
    forall (z : Z) (i : intptr),
      from_Z z = NoOom i ->
      to_Z i = z.

  Parameter from_Z_injective :
    forall (z1 z2 : Z) (i : intptr),
      from_Z z1 = NoOom i ->
      from_Z z2 = NoOom i ->
      z1 = z2.

  Parameter to_Z_from_Z :
    forall (i : intptr),
      from_Z (to_Z i) = NoOom i.

  Parameter from_Z_0 :
    from_Z 0 = NoOom zero.

  Parameter to_Z_0 :
    to_Z zero = 0%Z.

  Parameter to_Z_inj :
    forall x y,
      to_Z x = to_Z y ->
      x = y.

  Parameter VMemInt_intptr_dtyp :
    @mdtyp_of_int intptr VMemInt_intptr = DTYPE_IPTR.

  Parameter VMemInt_intptr_mrepr_from_Z :
    forall x,
      @mrepr intptr VMemInt_intptr x = from_Z x.

  Parameter to_Z_to_unsigned :
    forall x,
      to_Z x = to_unsigned x.
End INTPTR_CORE.

Module INTPTR_SEQ (IP : INTPTR_CORE).
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
End INTPTR_SEQ.

Module Type INTPTR := INTPTR_CORE <+ INTPTR_SEQ.

Module Type INTPTR_BIG.
  Include INTPTR.

  Parameter from_Z_safe :
    forall z,
      match from_Z z with
      | NoOom _ => True
      | Oom _ => False
      end.
End INTPTR_BIG.
