  Lemma get_consecutive_ptrs_cons :
    forall ptr len p ptrs,
      get_consecutive_ptrs ptr len = ret (p :: ptrs) ->
      p = ptr /\ ((ptrs = [] /\ len = 1%nat) \/ exists ptr' ip len', len = S len' /\ to_Z ip = 1%Z /\ handle_gep_addr (DTYPE_I 8) ptr [DVALUE_IPTR ip] = inr (NoOom ptr') /\ (get_consecutive_ptrs ptr' len' = ret ptrs)%monad).
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

  Lemma get_consecutive_ptrs_covers_range :
    forall ptr len ptrs,
      get_consecutive_ptrs ptr len = ret ptrs ->
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
    intros M HM EQM0 EQV EQRET OOM ERR LAWS RAISE_OOM RAISE_ERR
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
    intros M HM EQM EQV EQRET OOM ERR LAWS RBMOOM RBMERR
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
    intros M HM EQM EQV EQRET OOM ERR LAWS RAISE_OOM RAISE_ERR
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
      (exists msg, @get_consecutive_ptrs M HM OOM ERR ptr len ≈ raise_oom msg)%monad \/
        (exists ptrs, @get_consecutive_ptrs M HM OOM ERR ptr len ≈ ret ptrs)%monad.
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
