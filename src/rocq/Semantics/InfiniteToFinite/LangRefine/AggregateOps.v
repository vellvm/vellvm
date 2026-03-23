From Stdlib Require Import
  Lia
  ZArith
  Program.Equality
  String
  List.

From ExtLib Require Import
  Structures.Monads
  Structures.Functor.

From Vellvm.Semantics Require Import
  MemoryAddress
  VellvmIntegers
  DynamicValues
  InterpretationStack
  TopLevel
  LLVMEvents.

From Vellvm Require Import
  TopLevelRefinements.

From Vellvm.Semantics.InfiniteToFinite.Conversions Require Import
  BaseConversions
  DvalueConversions
  EventConversions.

From Vellvm.Utils Require Import
  Error
  Tactics
  ListUtil
  OOMRutt
  OOMRuttProps.

From Vellvm.Semantics.InfiniteToFinite.LangRefine Require Import
  Events
  Sizeof
  Values
  Utils.

Import DynamicTypes.

From ITree Require Import
  ITree
  Basics
  Basics.HeterogeneousRelations
  Eq.Rutt
  Eq.RuttFacts
  Eq.Eqit
  Eq.EqAxiom.

Import MonadNotation.
Import ListNotations.
Open Scope list.

Module Type AggregateOpsRefine
  (IS1 : InterpreterStack)
  (IS2 : InterpreterStack)
  (LLVM1 : LLVMTopLevel IS1)
  (LLVM2 : LLVMTopLevel IS2)
  (TLR1 : TopLevelRefinements IS1 LLVM1)
  (TLR2 : TopLevelRefinements IS2 LLVM2)
  (AC1 : AddrConvert IS1.LP.ADDR IS1.LP.PTOI IS2.LP.ADDR IS2.LP.PTOI)
  (AC2 : AddrConvert IS2.LP.ADDR IS2.LP.PTOI IS1.LP.ADDR IS1.LP.PTOI)
  (IPS : IPConvertSafe IS2.LP.IP IS1.LP.IP)
  (ACS : AddrConvertSafe IS2.LP.ADDR IS2.LP.PTOI IS1.LP.ADDR IS1.LP.PTOI AC2 AC1)
  (DVC : DVConvert IS1.LP IS2.LP AC1)
  (DVCrev : DVConvert IS2.LP IS1.LP AC2)
  (EC : EventConvert IS1.LP IS2.LP AC1 AC2 DVC DVCrev)
  (SIZEOF_REF : Sizeof_Refine IS1.LP.SZ IS2.LP.SZ)
  (ER : EventRefine IS1 IS2 LLVM1 LLVM2 AC1 AC2 DVC DVCrev EC)
  (VAL_REF : ValueRefine 
               IS1 IS2
               LLVM1 LLVM2
               AC1 AC2
               IPS ACS
               DVC DVCrev
               EC SIZEOF_REF ER).

  Import EC.
  Import DV2.
  Import DVC.
  Import VAL_REF.


  Lemma index_into_vec_dv_fin_inf :
    forall t vec idx res,
      @index_into_vec_dv err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) t vec idx = ret res ->
      @DV1.index_into_vec_dv err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) t
        (fin_to_inf_dvalue vec) (fin_to_inf_dvalue idx) =
        ret (fin_to_inf_dvalue res).
  Proof.
    intros t vec idx res INDEX.
    unfold index_into_vec_dv in INDEX.
    unfold DV1.index_into_vec_dv.

    break_match_hyp_inv.
    { (* Arrays *)
      break_match_hyp_inv.
      { (* ix index *)
        generalize dependent res.
        generalize dependent x.
        induction elts; intros x res H0.
        - break_match_hyp_inv;
            unfold fin_to_inf_dvalue;
            try rename p into p';

            break_match_goal;
            break_match_hyp; clear Heqs; destruct p; clear e0;
            cbn in e; inv e; inv H0;

            break_match_goal;
            break_match_hyp; clear Heqs; destruct p; clear e0;
            cbn in e; inv e; inv H0;

            cbn;
            rewrite Heqz;

            break_match_goal; clear Heqs; destruct p; clear e0;
            cbn in e; inv e;

            auto.
        - cbn in H0.
          break_match_hyp_inv.
          + (* Index 0 *)
            clear IHelts.
            unfold fin_to_inf_dvalue.

            break_match_goal;
              break_match_hyp; clear Heqs; destruct p; clear e0;
              cbn in e; inv e;
              break_match_hyp_inv.

            break_match_goal;
              break_match_hyp; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; inv H0.

            destruct (dvalue_convert_strict_fin_inf_succeeds res).
            rewrite e in Heqo.
            cbn.
            rewrite Heqz.
            break_match_hyp_inv.
            cbn.
            break_match_goal; clear Heqs; destruct p.
            rewrite e in e0; inv e0.
            auto.
          + (* Index positive *)
            unfold fin_to_inf_dvalue.
            rename p into p'.

            break_match_goal;
              break_match_hyp; clear Heqs; destruct p; clear e0;
              cbn in e; inv e;
              break_match_hyp_inv;

            break_match_goal;
              break_match_hyp; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; inv H0.

            destruct (dvalue_convert_strict_fin_inf_succeeds res).
            break_match_hyp_inv.
            cbn; rewrite Heqz.
            break_match_hyp_inv.
            cbn.

            subst_existT.
            assert (exists x1, @Integers.signed sz0 x1 = Z.pred (Z.pos p')) as (x1' & X1').
            { exists (repr (Z.pred (Z.pos p'))).
              pose proof (@Integers.min_signed_neg sz0).
              unfold repr.
              cbn.
              rewrite (@Integers.signed_repr sz0); eauto.
              pose proof Integers.signed_range x0.
              break_match_goal; lia.
            }

            specialize (IHelts x1' res).
            forward IHelts.
            { rewrite X1'.
              cbn.
              destruct p'; cbn; auto.
            }

            unfold fin_to_inf_dvalue in IHelts.
            move IHelts after X1'.
            break_match_hyp_inv.
            { move Heqd0 after H0.
              break_match_hyp_inv; clear Heqs; destruct p; clear e1;
              cbn in e0; inv e0.
              break_match_hyp_inv.

              break_match_hyp_inv.
              { move Heqd0 after H2.
                break_match_hyp_inv; clear Heqs; destruct p; clear e1;
                  cbn in e0; inv e0.

                destruct (dvalue_convert_strict_fin_inf_succeeds res).
                rewrite e in e0; inv e0.
                inv H3; subst_existT;
                rewrite X1' in H2.
                rewrite X1'.

                cbn in H2.
                inv Heqo.
                destruct p'; cbn in *; eauto.
              }
            }

            { move Heqd0 after H0;
                break_match_hyp_inv; clear Heqs; destruct p; clear e1;
                cbn in e0;
                break_match_hyp_inv.
              inv H3.
            }
      }
    }

    { (* Vectors *)
      break_match_hyp_inv.
      { (* ix index *)
        generalize dependent res.
        generalize dependent x.
        induction elts; intros x res H0.
        - break_match_hyp_inv;
            unfold fin_to_inf_dvalue;
            try rename p into p';

            break_match_goal;
            break_match_hyp; clear Heqs; destruct p; clear e0;
            cbn in e; inv e; inv H0;

            break_match_goal;
            break_match_hyp; clear Heqs; destruct p; clear e0;
            cbn in e; inv e; inv H0;

            cbn;
            rewrite Heqz;

            break_match_goal; clear Heqs; destruct p; clear e0;
            cbn in e; inv e;

            auto.
        - cbn in H0.
          break_match_hyp_inv.
          + (* Index 0 *)
            clear IHelts.
            unfold fin_to_inf_dvalue.

            break_match_goal;
              break_match_hyp; clear Heqs; destruct p; clear e0;
              cbn in e; inv e;
              break_match_hyp_inv.

            break_match_goal;
              break_match_hyp; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; inv H0.

            destruct (dvalue_convert_strict_fin_inf_succeeds res).
            rewrite e in Heqo.
            cbn.
            rewrite Heqz.
            break_match_hyp_inv.
            cbn.
            break_match_goal; clear Heqs; destruct p.
            rewrite e in e0; inv e0.
            auto.
          + (* Index positive *)
            unfold fin_to_inf_dvalue.
            rename p into p'.

            break_match_goal;
              break_match_hyp; clear Heqs; destruct p; clear e0;
              cbn in e; inv e;
              break_match_hyp_inv;

            break_match_goal;
              break_match_hyp; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; inv H0.

            destruct (dvalue_convert_strict_fin_inf_succeeds res).
            break_match_hyp_inv.
            cbn; rewrite Heqz.
            break_match_hyp_inv.
            cbn.

            subst_existT.
            assert (exists x1, @Integers.signed sz0 x1 = Z.pred (Z.pos p')) as (x1' & X1').
            { exists (repr (Z.pred (Z.pos p'))).
              pose proof (@Integers.min_signed_neg sz0).
              unfold repr.
              cbn.
              rewrite (@Integers.signed_repr sz0); eauto.
              pose proof Integers.signed_range x0.
              break_match_goal; lia.
            }

            specialize (IHelts x1' res).
            forward IHelts.
            { rewrite X1'.
              cbn.
              destruct p'; cbn; auto.
            }

            unfold fin_to_inf_dvalue in IHelts.
            move IHelts after X1'.
            break_match_hyp_inv.

            { move Heqd0 after H0;
                break_match_hyp_inv; clear Heqs; destruct p; clear e1;
                cbn in e0;
                break_match_hyp_inv.
              inv H3.
            }

            { move Heqd0 after H0.
              break_match_hyp_inv; clear Heqs; destruct p; clear e1;
              cbn in e0; inv e0.
              break_match_hyp_inv.

              break_match_hyp_inv.
              { move Heqd0 after H2.
                break_match_hyp_inv; clear Heqs; destruct p; clear e1;
                  cbn in e0; inv e0.

                destruct (dvalue_convert_strict_fin_inf_succeeds res).
                rewrite e in e0; inv e0.
                inv H3; subst_existT;
                rewrite X1' in H2.
                rewrite X1'.

                cbn in H2.
                inv Heqo.
                destruct p'; cbn in *; eauto.
              }
            }
      }
    }
  Qed.

  Lemma insert_into_vec_dv_loop_fin_inf_succeeds :
    forall elts acc idx v res,
      (fix loop (acc elts : list dvalue) (i : LLVMAst.int_ast) {struct elts} :
        option (list dvalue) :=
         match elts with
         | [] => None
         | h :: tl =>
             if (i =? 0)%Z then Some (acc ++ v :: tl) else loop (acc ++ [h]) tl (i - 1)%Z
         end) acc elts idx = ret res ->
      (fix loop (acc elts : list DVCrev.DV2.dvalue) (i : LLVMAst.int_ast) {struct elts} :
        option (list DVCrev.DV2.dvalue) :=
         match elts with
         | [] => None
         | h :: tl =>
             if (i =? 0)%Z then Some (acc ++ (fin_to_inf_dvalue v) :: tl) else loop (acc ++ [h]) tl (i - 1)%Z
         end) (map fin_to_inf_dvalue acc) (map fin_to_inf_dvalue elts) idx = ret (map fin_to_inf_dvalue res).
  Proof.
    induction elts; intros acc idx v res LOOP.
    - discriminate.
    - break_match_hyp_inv.
      + (* Index 0 *)
        cbn. rewrite Heqb.
        rewrite map_app, map_cons.
        reflexivity.
      + destruct elts as [|b elts]; try discriminate.
        cbn. rewrite Heqb.
        break_match_hyp; inv H0.
        -- rewrite map_app, map_cons.
           rewrite map_app.
           reflexivity.
        -- specialize (IHelts (acc ++ [a]) (idx-1)%Z v res).
           rewrite Heqb0 in IHelts.
           specialize (IHelts H1).

           rewrite map_cons in IHelts.
           rewrite Heqb0 in IHelts.
           rewrite map_app in IHelts.
           cbn in IHelts.
           auto.
  Qed.

  Lemma insert_into_vec_dv_loop_fin_inf_fails :
    forall elts acc idx v,
      (fix loop (acc elts : list dvalue) (i : LLVMAst.int_ast) {struct elts} :
        option (list dvalue) :=
         match elts with
         | [] => None
         | h :: tl =>
             if (i =? 0)%Z then Some (acc ++ v :: tl) else loop (acc ++ [h]) tl (i - 1)%Z
         end) acc elts idx = None ->
      (fix loop (acc elts : list DVCrev.DV2.dvalue) (i : LLVMAst.int_ast) {struct elts} :
        option (list DVCrev.DV2.dvalue) :=
         match elts with
         | [] => None
         | h :: tl =>
             if (i =? 0)%Z then Some (acc ++ (fin_to_inf_dvalue v) :: tl) else loop (acc ++ [h]) tl (i - 1)%Z
         end) (map fin_to_inf_dvalue acc) (map fin_to_inf_dvalue elts) idx = None.
  Proof.
    induction elts; intros acc idx v LOOP.
    - cbn; auto.
    - break_match_hyp_inv.
      specialize (IHelts (acc ++ [a]) (idx-1)%Z v H0).
      cbn.
      rewrite Heqb.
      rewrite map_app in IHelts.
      cbn in IHelts.
      auto.
  Qed.

  (* TODO: Move this / generalize monad? *)
  (* TODO: Prove this *)
  Lemma insert_into_vec_dv_fin_inf :
    forall dv1_fin dv2_fin dv3_fin res_fin dv1_inf dv2_inf dv3_inf t,
      @insert_into_vec_dv err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        t dv1_fin dv2_fin dv3_fin = ret res_fin ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      fin_to_inf_dvalue dv3_fin = dv3_inf ->
      @DV1.insert_into_vec_dv err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        t dv1_inf dv2_inf dv3_inf = ret (fin_to_inf_dvalue res_fin).
  Proof.
    intros dv1_fin dv2_fin dv3_fin res_fin dv1_inf dv2_inf dv3_inf t INSERT LIFT1 LIFT2 LIFT3.
    subst.
    unfold insert_into_vec_dv in INSERT.
    unfold DV1.insert_into_vec_dv.

    break_match_hyp_inv.
    { (* Arrays *)
      break_match_hyp_inv.
      { (* ix index *)
        rewrite fin_to_inf_dvalue_array.
        rewrite fin_to_inf_dvalue_ix.
        cbn.
        break_match_hyp_inv.
        - (* Index 0 *)
          break_match_hyp_inv.
          + apply insert_into_vec_dv_loop_fin_inf_succeeds in Heqo.
            setoid_rewrite Heqo; cbn.
            rewrite fin_to_inf_dvalue_array.
            auto.
          + apply insert_into_vec_dv_loop_fin_inf_fails in Heqo.
            setoid_rewrite Heqo; cbn.
            rewrite fin_to_inf_dvalue_poison; auto.
        - (* Index positive *)
          break_match_hyp_inv.
          + apply insert_into_vec_dv_loop_fin_inf_succeeds in Heqo.
            setoid_rewrite Heqo; cbn.
            rewrite fin_to_inf_dvalue_array.
            auto.
          + apply insert_into_vec_dv_loop_fin_inf_fails in Heqo.
            setoid_rewrite Heqo; cbn.
            rewrite fin_to_inf_dvalue_poison; auto.
      }
    }

    { (* Vectors *)
      break_match_hyp_inv.
      { (* ix index *)
        rewrite fin_to_inf_dvalue_vector.
        rewrite fin_to_inf_dvalue_ix.
        cbn.
        break_match_hyp_inv.
        - (* Index 0 *)
          break_match_hyp_inv.
          + apply insert_into_vec_dv_loop_fin_inf_succeeds in Heqo.
            setoid_rewrite Heqo; cbn.
            rewrite fin_to_inf_dvalue_vector.
            auto.
          + apply insert_into_vec_dv_loop_fin_inf_fails in Heqo.
            setoid_rewrite Heqo; cbn.
            rewrite fin_to_inf_dvalue_poison; auto.
        - (* Index positive *)
          break_match_hyp_inv.
          + apply insert_into_vec_dv_loop_fin_inf_succeeds in Heqo.
            setoid_rewrite Heqo; cbn.
            rewrite fin_to_inf_dvalue_vector.
            auto.
          + apply insert_into_vec_dv_loop_fin_inf_fails in Heqo.
            setoid_rewrite Heqo; cbn.
            rewrite fin_to_inf_dvalue_poison; auto.
      }
    }
  Qed.

  Lemma index_into_str_dv_loop_fin_inf :
    forall {elts i res},
      (fix loop elts i :=
         match elts with
         | [] => raise_error "index_into_str_dv: index out of bounds"
         | h :: tl =>
             if (i =? 0)%Z then ret h else loop tl (i-1)%Z
         end) elts i = (res : err_ub_oom dvalue) ->
      (fix loop elts i :=
         match elts with
         | [] => raise_error "index_into_str_dv: index out of bounds"
         | h :: tl =>
             if (i =? 0)%Z then ret h else loop tl (i-1)%Z
         end) (map fin_to_inf_dvalue elts) i = (fmap fin_to_inf_dvalue res : err_ub_oom DVCrev.DV2.dvalue).
  Proof.
    induction elts;
      intros i res LOOP.
    - subst; cbn; auto.
    - break_match_hyp.
      + cbn; rewrite Heqb; inv LOOP.
        reflexivity.
      + apply IHelts in LOOP.
        cbn; rewrite Heqb.
        setoid_rewrite LOOP.
        reflexivity.
  Qed.

  Lemma index_into_str_dv_loop_no_ub_fin_inf :
    forall {elts i ub_msg},
      (fix loop elts i : err_ub_oom dvalue :=
         match elts with
         | [] => raise_error "index_into_str_dv: index out of bounds"
         | h :: tl =>
             if (i =? 0)%Z then ret h else loop tl (i-1)%Z
         end) elts i = UB_unERR_UB_OOM ub_msg -> False.
  Proof.
    induction elts;
      intros i res LOOP; inv LOOP.
    - break_match_hyp; inv H0.
      eapply IHelts; eauto.
  Qed.

  Lemma index_into_str_dv_fin_inf :
    forall {v idx} {res : err_ub_oom dvalue},
      index_into_str_dv v idx = res ->
      DV1.index_into_str_dv (fin_to_inf_dvalue v) idx = fmap fin_to_inf_dvalue res.
  Proof.
    intros v idx res H.
    unfold DV1.index_into_str_dv, index_into_str_dv in *.
    break_match_hyp;
      try solve
        [ unfold fin_to_inf_dvalue; break_match_goal; break_match_hyp_inv; clear Heqs; destruct p; clear e0;
          cbn in e; inv e;
          cbn; auto; try discriminate
        | unfold fin_to_inf_dvalue; break_match_goal; break_match_hyp_inv; clear Heqs; destruct p; clear e0;
          cbn in e; break_match_hyp_inv;
          cbn; auto; try discriminate
        ].

    - (* Structs *)
      rewrite fin_to_inf_dvalue_struct.
      apply index_into_str_dv_loop_fin_inf; auto.
    - (* Packed Structs *)
      rewrite fin_to_inf_dvalue_packed_struct.
      apply index_into_str_dv_loop_fin_inf; auto.
    - (* Array *)
      rewrite fin_to_inf_dvalue_array.
      apply index_into_str_dv_loop_fin_inf; auto.
  Qed.

  Lemma index_into_str_dv_no_ub_fin_inf :
    forall {v idx ub_msg},
      @index_into_str_dv err_ub_oom _ _ v idx = UB_unERR_UB_OOM ub_msg -> False.
  Proof.
    intros v idx ub_msg H.
    unfold index_into_str_dv in *.
    break_match_hyp; inv H;
      eapply index_into_str_dv_loop_no_ub_fin_inf; eauto.
  Qed.

  Lemma extract_value_loop_fin_inf_succeeds :
    forall idxs str res,
      (fix loop str idxs {struct idxs} : err_ub_oom dvalue :=
         match idxs with
         | [] => ret str
         | i :: tl =>
             v <- index_into_str_dv str i ;;
             loop v tl
         end) str idxs = ret res ->
      (fix loop str idxs {struct idxs} : err_ub_oom DVCrev.DV2.dvalue :=
         match idxs with
         | [] => ret str
         | i :: tl =>
             v <- DV1.index_into_str_dv str i ;;
             loop v tl
         end) (fin_to_inf_dvalue str) idxs = ret (fin_to_inf_dvalue res).
  Proof.
    induction idxs;
      intros str res LOOP.
    - inv LOOP; auto.
    - cbn in LOOP.
      repeat break_match_hyp_inv.
      destruct unERR_UB_OOM, unEitherT, unEitherT, unEitherT, unIdent;
        inv Heqs.

      pose proof index_into_str_dv_fin_inf Heqe as INDEX.
      rewrite INDEX.

      match goal with
      | H: EitherMonad.unEitherT
             (EitherMonad.unEitherT
                (EitherMonad.unEitherT
                   (unERR_UB_OOM
                      (?L)))) = _ |- _ =>
          remember L as LOOP
      end.

      destruct_err_ub_oom LOOP; inv H1.
      symmetry in HeqLOOP.
      apply IHidxs in HeqLOOP.

      cbn.
      setoid_rewrite HeqLOOP.
      reflexivity.
  Qed.

  Lemma insert_into_str_loop_fin_inf :
    forall {elts acc v i} {res : err_ub_oom (list dvalue)},
      (fix loop (acc elts:list dvalue) (i:LLVMAst.int_ast) :=
        match elts with
        | [] => raise_error "insert_into_str: index out of bounds"
        | h :: tl =>
          (if i =? 0 then ret (acc ++ (v :: tl))
          else loop (acc ++ [h]) tl (i-1))%Z
        end%list) acc elts i = res ->
      (fix loop (acc elts:list DVCrev.DV2.dvalue) (i:LLVMAst.int_ast) :=
        match elts with
        | [] => raise_error "insert_into_str: index out of bounds"
        | h :: tl =>
          (if i =? 0 then ret (acc ++ ((fin_to_inf_dvalue v) :: tl))
          else loop (acc ++ [h]) tl (i-1))%Z
        end%list) (fmap fin_to_inf_dvalue acc) (fmap fin_to_inf_dvalue elts) i = fmap (fmap fin_to_inf_dvalue) res.
  Proof.
    induction elts;
      intros acc v i res LOOP.
    - subst; cbn; auto.
    - break_match_hyp.
      + cbn; rewrite Heqb; subst; cbn.
        rewrite flat_map_app.
        reflexivity.
      + apply IHelts in LOOP.
        cbn; rewrite Heqb; subst; cbn.
        cbn in LOOP.
        rewrite flat_map_app in LOOP.
        setoid_rewrite LOOP.
        reflexivity.
  Qed.

  Lemma insert_into_str_fin_inf :
    forall {str v i} {res : err_ub_oom dvalue},
      insert_into_str str v i = res ->
      DV1.insert_into_str (fin_to_inf_dvalue str) (fin_to_inf_dvalue v) i = fmap fin_to_inf_dvalue res.
  Proof.
    intros str v i res INSERT.
    destruct str;
      try solve
        [ unfold fin_to_inf_dvalue; break_match_goal; clear Heqs; destruct p; clear e0;
          cbn in e; inv e;
          cbn; auto
        | unfold fin_to_inf_dvalue; break_match_goal; clear Heqs; destruct p; clear e0;
          cbn in e; break_match_hyp_inv;
          cbn; auto
        ].

    - (* Structs *)
      rewrite fin_to_inf_dvalue_struct;
        unfold DV1.insert_into_str, insert_into_str in *.
      cbn in INSERT.
      break_match_hyp.
      rewrite <- fmap_map.
      apply insert_into_str_loop_fin_inf in Heqe.
      cbn in Heqe.
      cbn.
      setoid_rewrite Heqe.
      subst; cbn.
      destruct unERR_UB_OOM, unEitherT, unEitherT, unEitherT, unIdent;
        inv Heqe; cbn in *; auto.
      destruct s; cbn in *; auto.
      destruct s; cbn in *; auto.

      rewrite fin_to_inf_dvalue_struct.
      reflexivity.
    - (* Packed Structs *)
      rewrite fin_to_inf_dvalue_packed_struct;
        unfold DV1.insert_into_str, insert_into_str in *.
      cbn in INSERT.
      break_match_hyp.
      rewrite <- fmap_map.
      apply insert_into_str_loop_fin_inf in Heqe.
      cbn in Heqe.
      cbn.
      setoid_rewrite Heqe.
      subst; cbn.
      destruct unERR_UB_OOM, unEitherT, unEitherT, unEitherT, unIdent;
        inv Heqe; cbn in *; auto.
      destruct s; cbn in *; auto.
      destruct s; cbn in *; auto.

      rewrite fin_to_inf_dvalue_packed_struct.
      reflexivity.
    - (* Array *)
      rewrite fin_to_inf_dvalue_array;
        unfold DV1.insert_into_str, insert_into_str in *.
      cbn in INSERT.
      break_match_hyp.
      rewrite <- fmap_map.
      apply insert_into_str_loop_fin_inf in Heqe.
      cbn in Heqe.
      cbn.
      setoid_rewrite Heqe.
      subst; cbn.
      destruct unERR_UB_OOM, unEitherT, unEitherT, unEitherT, unIdent;
        inv Heqe; cbn in *; auto.
      destruct s; cbn in *; auto.
      destruct s; cbn in *; auto.

      rewrite fin_to_inf_dvalue_array.
      reflexivity.
  Qed.


  Lemma insert_value_loop_fin_inf_succeeds :
    forall idxs str elt res,
      (fix loop str idxs : err_ub_oom dvalue :=
         match idxs with
         | [] => raise_error "Index was not provided"
         | i :: nil =>
             v <- insert_into_str str elt i;;
             ret v
         | i :: tl =>
             subfield <- index_into_str_dv str i;;
             modified_subfield <- loop subfield tl;;
             insert_into_str str modified_subfield i
         end) str idxs = res ->
      (fix loop str idxs : err_ub_oom DVCrev.DV2.dvalue :=
         match idxs with
         | [] => raise_error "Index was not provided"
         | i :: nil =>
             v <- DV1.insert_into_str str (fin_to_inf_dvalue elt) i;;
             ret v
         | i :: tl =>
             subfield <- DV1.index_into_str_dv str i;;
             modified_subfield <- loop subfield tl;;
             DV1.insert_into_str str modified_subfield i
         end) (fin_to_inf_dvalue str) idxs = fmap fin_to_inf_dvalue res.
  Proof.
    induction idxs;
      intros str elt res LOOP.
    - subst; auto.
    - break_match_hyp.
      + cbn in *.
        break_match_hyp.
        remember (insert_into_str str elt a) as insert.
        symmetry in Heqinsert.
        pose proof insert_into_str_fin_inf Heqinsert as Heqinsert'.
        rewrite Heqinsert'.
        destruct_err_ub_oom insert; subst; inv Heqe; cbn in *;
          auto.
      + remember (index_into_str_dv str a) as index.
        symmetry in Heqindex.
        pose proof index_into_str_dv_fin_inf Heqindex as Hindex.
        rewrite Hindex.

        destruct_err_ub_oom index;
          try solve [subst; cbn in *; auto].

        rename index0 into subf.
        cbn in LOOP.
        break_match_hyp.
        apply IHidxs in Heqe.

        setoid_rewrite err_ub_oom_bind_ret_l_eq.
        rewrite Heqe.
        destruct unERR_UB_OOM, unEitherT, unEitherT, unEitherT, unIdent.
        { subst; inv Heqe; cbn in *; auto. }
        destruct s.
        { subst; inv Heqe; cbn in *; auto. }
        destruct s.
        { subst; inv Heqe; cbn in *; auto. }

        setoid_rewrite err_ub_oom_bind_ret_l_eq.
        apply insert_into_str_fin_inf.
        subst; cbn in *.
        remember (insert_into_str str d a) as insert.
        destruct_err_ub_oom insert; auto.
  Qed.

  Lemma index_into_vec_dv_no_ub :
    forall t vec idx ub_msg,
      @index_into_vec_dv err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) t vec idx = UB_unERR_UB_OOM ub_msg -> False.
  Proof.
    intros t vec idx res INDEX.
    unfold index_into_vec_dv in INDEX.

    break_match_hyp_inv.
    { (* Arrays *)
      break_match_hyp_inv.
      { (* ix index *)
        repeat break_match_hyp_inv.
        - induction elts; cbn in *; inv H0.
        - clear Heqz.
          remember (Z.pos p) as z.
          clear Heqz p.
          generalize dependent z.
          induction elts; intros z CONTRA; cbn in *; inv CONTRA.
          break_match_hyp_inv.
          eapply IHelts in H1; auto.
      }
    }

    { (* Vectors *)
      break_match_hyp_inv.
      { (* ix index *)
        repeat break_match_hyp_inv.
        - induction elts; cbn in *; inv H0.
        - clear Heqz.
          remember (Z.pos p) as z.
          clear Heqz p.
          generalize dependent z.
          induction elts; intros z CONTRA; cbn in *; inv CONTRA.
          break_match_hyp_inv.
          eapply IHelts in H1; auto.
      }
    }
  Qed.

  (* TODO: Move this / generalize monad? *)
  Lemma insert_into_vec_dv_no_ub_fin_inf :
    forall dv1_fin dv2_fin dv3_fin ub_msg t,
      @insert_into_vec_dv err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        t dv1_fin dv2_fin dv3_fin = raise_ub ub_msg -> False.
  Proof.
    intros dv1_fin dv2_fin dv3_fin ub_msg t INSERT.
    unfold insert_into_vec_dv in INSERT.
    repeat break_match_hyp_inv.
  Qed.

  Lemma index_into_vec_dv_err_fin_inf:
    forall (t : dtyp) (vec idx : dvalue) err_msg,
      index_into_vec_dv t vec idx = ERR_unERR_UB_OOM err_msg ->
      DV1.index_into_vec_dv t (fin_to_inf_dvalue vec) (fin_to_inf_dvalue idx) = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros t vec idx err_msg INDEX.
    unfold index_into_vec_dv in INDEX.
    unfold DV1.index_into_vec_dv.

    break_match_hyp_inv; rewrite_fin_to_inf_dvalue; auto.
    { (* Arrays *)
      break_match_hyp_inv; rewrite_fin_to_inf_dvalue; auto.
      { (* ix index *)
        cbn in *.
        break_match_hyp_inv; auto.
        - remember (0%Z) as n.
          clear Heqn Heqz.
          generalize dependent n.
          induction elts; intros n H0.
          + inv H0.
          + rewrite Z.eqb_refl in H0. inv H0.
        - remember (Z.pos p) as n.
          clear Heqn Heqz.
          generalize dependent n.
          induction elts; intros n H0.
          + inv H0.
          + cbn.
            break_match_hyp_inv.
            rewrite IHelts; eauto.
      }
    }

    { (* Vectors *)
      break_match_hyp_inv; rewrite_fin_to_inf_dvalue; auto.
      { (* ix index *)
        cbn in *.
        break_match_hyp_inv; auto.
        - remember (0%Z) as n.
          clear Heqn Heqz.
          generalize dependent n.
          induction elts; intros n H0.
          + inv H0.
          + rewrite Z.eqb_refl in H0. inv H0.
        - remember (Z.pos p) as n.
          clear Heqn Heqz.
          generalize dependent n.
          induction elts; intros n H0.
          + inv H0.
          + cbn.
            break_match_hyp_inv.
            rewrite IHelts; eauto.
      }
    }
  Qed.

  Lemma insert_into_vec_dv_err_fin_inf :
    forall dv1_fin dv2_fin dv3_fin msg dv1_inf dv2_inf dv3_inf t,
      @insert_into_vec_dv err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        t dv1_fin dv2_fin dv3_fin = ERR_unERR_UB_OOM msg ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      fin_to_inf_dvalue dv3_fin = dv3_inf ->
      @DV1.insert_into_vec_dv err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        t dv1_inf dv2_inf dv3_inf = ERR_unERR_UB_OOM msg.
  Proof.
    intros dv1_fin dv2_fin dv3_fin msg dv1_inf dv2_inf dv3_inf t INSERT LIFT1 LIFT2 LIFT3.
    subst.
    unfold insert_into_vec_dv in INSERT.
    unfold DV1.insert_into_vec_dv.

    break_match_hyp_inv; rewrite_fin_to_inf_dvalue; auto.
    { (* Arrays *)
      break_match_hyp_inv; rewrite_fin_to_inf_dvalue; auto; cbn.
      { (* ix index *)
        cbn in *.
        break_match_hyp_inv; auto.
        - remember (0%Z) as n.
          clear Heqn Heqz.
          generalize dependent n.
          induction elts; intros n H0.
          + inv H0.
          + rewrite Z.eqb_refl in H0. inv H0.
        - remember (Z.pos p) as n.
          clear Heqn Heqz.
          generalize dependent n.
          induction elts; intros n H0.
          + inv H0.
          + cbn.
            break_match_hyp_inv.
      }
    }

    { (* Vectors *)
      break_match_hyp_inv; rewrite_fin_to_inf_dvalue; auto; cbn.
      { (* ix index *)
        cbn in *.
        break_match_hyp_inv; auto.
        - remember (0%Z) as n.
          clear Heqn Heqz.
          generalize dependent n.
          induction elts; intros n H0.
          + inv H0.
          + rewrite Z.eqb_refl in H0. inv H0.
        - remember (Z.pos p) as n.
          clear Heqn Heqz.
          generalize dependent n.
          induction elts; intros n H0.
          + inv H0.
          + cbn.
            break_match_hyp_inv.
      }
    }
  Qed.

  Lemma extract_value_loop_fin_inf_err :
    forall idxs str msg,
      (fix loop str idxs {struct idxs} : err_ub_oom dvalue :=
         match idxs with
         | [] => ret str
         | i :: tl =>
             v <- index_into_str_dv str i ;;
             loop v tl
         end) str idxs = ERR_unERR_UB_OOM msg ->
      (fix loop str idxs {struct idxs} : err_ub_oom DVCrev.DV2.dvalue :=
         match idxs with
         | [] => ret str
         | i :: tl =>
             v <- DV1.index_into_str_dv str i ;;
             loop v tl
         end) (fin_to_inf_dvalue str) idxs = ERR_unERR_UB_OOM msg.
  Proof.
    induction idxs;
      intros str res LOOP.
    - inv LOOP; auto.
    - cbn in LOOP.
      repeat break_match_hyp_inv.
      destruct unERR_UB_OOM, unEitherT, unEitherT, unEitherT, unIdent;
        inv Heqs.

      pose proof index_into_str_dv_fin_inf Heqe as INDEX.
      rewrite INDEX.
      cbn; auto.

      match goal with
      | H: EitherMonad.unEitherT
             (EitherMonad.unEitherT
                (EitherMonad.unEitherT
                   (Error.unERR_UB_OOM
                      (?L)))) = _ |- _ =>
          remember L as LOOP
      end.

      destruct_err_ub_oom LOOP; inv H1.
      symmetry in HeqLOOP.
      apply IHidxs in HeqLOOP.

      cbn.
      erewrite index_into_str_dv_fin_inf; eauto.
      remember {| unERR_UB_OOM := unERR_UB_OOM |} as x.
      destruct_err_ub_oom x; cbn in *; subst; inv Heqx; inv Heqs.
      setoid_rewrite HeqLOOP.
      reflexivity.
  Qed.

  (* TODO: Move this *)
  Lemma orutt_index_into_vec_dv :
    forall E1 E2
      `{OOM1 : OOME -< E1} `{OOM2 : OOME -< E2}
      `{UB1 : UBE -< E1} `{UB2 : UBE -< E2}
      `{ERR1: FailureE -< E1} `{ERR2: FailureE -< E2}
      (pre : prerel E1 E2) (post : postrel E1 E2)
      (UBDISC : forall e1 e2, @subevent UBE E2 UB2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (ERRDISC : forall e1 e2, @subevent FailureE E2 ERR2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (UBINJ : pre void void (@subevent UBE E1 UB1 void (ThrowUB tt)) (@subevent UBE E2 UB2 void (ThrowUB tt)))
      (ERRINJ : pre void void (@subevent FailureE E1 ERR1 void (Throw tt)) (@subevent FailureE E2 ERR2 void (Throw tt)))
      τ dv1_1 dv2_1 dv1_2 dv2_2,
      dvalue_refine_strict dv1_1 dv1_2 ->
      dvalue_refine_strict dv2_1 dv2_2 ->
      orutt pre post dvalue_refine_strict
        (DV1.index_into_vec_dv τ dv1_1 dv2_1) (index_into_vec_dv τ dv1_2 dv2_2)
        (OOM:=OOME).
  Proof.
    intros E1 E2 OOM1 OOM2 UB1 UB2 ERR1 ERR2 pre post UBDISC ERRDISC UBINJ ERRINJ τ dv1_1 dv2_1 dv1_2 dv2_2 REF1 REF2.
    rewrite TLR1.index_into_vec_dv_err_ub_oom_to_itree,
      TLR2.index_into_vec_dv_err_ub_oom_to_itree.

    erewrite (fin_to_inf_dvalue_refine_strict' dv1_1); eauto.
    erewrite (fin_to_inf_dvalue_refine_strict' dv2_1); eauto.

    remember (index_into_vec_dv τ dv1_2 dv2_2) as res.
    destruct_err_ub_oom res;
      symmetry in Heqres.
    - apply orutt_raiseOOM.
    - apply index_into_vec_dv_no_ub in Heqres; contradiction.
    - erewrite index_into_vec_dv_err_fin_inf; eauto.
      apply orutt_raise; auto.
    - erewrite index_into_vec_dv_fin_inf; cbn; eauto.
      apply orutt_Ret.
      apply fin_to_inf_dvalue_refine_strict.
  Qed.

  #[global] Hint Resolve
    orutt_index_into_vec_dv
    : ORUTT.

  (* TODO: Move this *)
  Lemma orutt_insert_into_vec_dv :
    forall E1 E2
      `{OOM1 : OOME -< E1} `{OOM2 : OOME -< E2}
      `{UB1 : UBE -< E1} `{UB2 : UBE -< E2}
      `{ERR1: FailureE -< E1} `{ERR2: FailureE -< E2}
      (pre : prerel E1 E2) (post : postrel E1 E2)
      (UBDISC : forall e1 e2, @subevent UBE E2 UB2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (ERRDISC : forall e1 e2, @subevent FailureE E2 ERR2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (UBINJ : pre void void (@subevent UBE E1 UB1 void (ThrowUB tt)) (@subevent UBE E2 UB2 void (ThrowUB tt)))
      (ERRINJ : pre void void (@subevent FailureE E1 ERR1 void (Throw tt)) (@subevent FailureE E2 ERR2 void (Throw tt)))
      τ dv1_1 dv2_1 dv3_1 dv1_2 dv2_2 dv3_2,
      dvalue_refine_strict dv1_1 dv1_2 ->
      dvalue_refine_strict dv2_1 dv2_2 ->
      dvalue_refine_strict dv3_1 dv3_2 ->
      orutt pre post dvalue_refine_strict
        (DV1.insert_into_vec_dv τ dv1_1 dv2_1 dv3_1) (insert_into_vec_dv τ dv1_2 dv2_2 dv3_2)
        (OOM:=OOME).
  Proof.
    intros E1 E2 OOM1 OOM2 UB1 UB2 ERR1 ERR2 pre post UBDISC ERRDISC UBINJ ERRINJ τ dv1_1 dv2_1 dv3_1 dv1_2 dv2_2 dv3_2 REF1 REF2 REF3.
    rewrite TLR1.insert_into_vec_dv_err_ub_oom_to_itree,
      TLR2.insert_into_vec_dv_err_ub_oom_to_itree.

    erewrite (fin_to_inf_dvalue_refine_strict' dv1_1); eauto.
    erewrite (fin_to_inf_dvalue_refine_strict' dv2_1); eauto.
    erewrite (fin_to_inf_dvalue_refine_strict' dv3_1); eauto.

    remember (insert_into_vec_dv τ dv1_2 dv2_2 dv3_2) as res.
    destruct_err_ub_oom res;
      symmetry in Heqres.
    - apply orutt_raiseOOM.
    - apply insert_into_vec_dv_no_ub_fin_inf in Heqres; contradiction.
    - erewrite insert_into_vec_dv_err_fin_inf; eauto.
      apply orutt_raise; auto.
    - erewrite insert_into_vec_dv_fin_inf; cbn; eauto.
      apply orutt_Ret.
      apply fin_to_inf_dvalue_refine_strict.
  Qed.

  #[global] Hint Resolve
    orutt_insert_into_vec_dv
    : ORUTT.

  (* TODO: Move this *)
  Lemma extract_value_loop_fin_inf_no_ub :
    forall idxs str msg,
      (fix loop str idxs {struct idxs} : err_ub_oom dvalue :=
         match idxs with
         | [] => ret str
         | i :: tl =>
             v <- index_into_str_dv str i ;;
             loop v tl
         end) str idxs = UB_unERR_UB_OOM msg -> False.
  Proof.
    induction idxs;
      intros str res LOOP.
    - inv LOOP; auto.
    - cbn in LOOP.
      repeat break_match_hyp_inv.
      destruct unERR_UB_OOM, unEitherT, unEitherT, unEitherT, unIdent;
        inv Heqs.
      + apply index_into_str_dv_no_ub_fin_inf in Heqe; auto.
      + match goal with
        | H: EitherMonad.unEitherT
               (EitherMonad.unEitherT
                  (EitherMonad.unEitherT
                     (Error.unERR_UB_OOM
                        (?L)))) = _ |- _ =>
            remember L as LOOP
        end.

        destruct_err_ub_oom LOOP; inv H1.
        symmetry in HeqLOOP.
        apply IHidxs in HeqLOOP; auto.
  Qed.

  (* TODO: Move this *)
  Lemma orutt_extractvalue_loop :
    forall E1 E2
      `{OOM1 : OOME -< E1} `{OOM2 : OOME -< E2}
      `{UB1 : UBE -< E1} `{UB2 : UBE -< E2}
      `{ERR1: FailureE -< E1} `{ERR2: FailureE -< E2}
      (pre : prerel E1 E2) (post : postrel E1 E2)
      (UBDISC : forall e1 e2, @subevent UBE E2 UB2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (ERRDISC : forall e1 e2, @subevent FailureE E2 ERR2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (UBINJ : pre void void (@subevent UBE E1 UB1 void (ThrowUB tt)) (@subevent UBE E2 UB2 void (ThrowUB tt)))
      (ERRINJ : pre void void (@subevent FailureE E1 ERR1 void (Throw tt)) (@subevent FailureE E2 ERR2 void (Throw tt)))
      dv1 dv2 idxs,
      dvalue_refine_strict dv1 dv2 ->
      orutt pre post dvalue_refine_strict
        ((fix loop (str : DV1.dvalue) (idxs0 : list LLVMAst.int_ast) {struct idxs0} :
           itree _ DV1.dvalue :=
            match idxs0 with
            | [] => Ret str
            | i :: tl =>
                ITree.bind (DV1.index_into_str_dv str i)
                  (fun v : DV1.dvalue => loop v tl)
            end) dv1 idxs)
        ((fix loop (str : dvalue) (idxs0 : list LLVMAst.int_ast) {struct idxs0} : itree _ dvalue :=
            match idxs0 with
            | [] => Ret str
            | i :: tl => ITree.bind (index_into_str_dv str i) (fun v : dvalue => loop v tl)
            end) dv2 idxs)
        (OOM:=OOME).
  Proof.
    intros E1 E2 OOM1 OOM2 UB1 UB2 ERR1 ERR2 pre post UBDISC ERRDISC UBINJ ERRINJ dv1 dv2 idxs REF.
    setoid_rewrite TLR1.extract_value_loop_err_ub_oom_to_itree;
      setoid_rewrite TLR2.extract_value_loop_err_ub_oom_to_itree.

    erewrite (fin_to_inf_dvalue_refine_strict' dv1); eauto.

    remember
      ((fix loop (str : dvalue) (idxs0 : list LLVMAst.int_ast) {struct idxs0} : err_ub_oom dvalue :=
          match idxs0 with
          | [] => ret str
          | i :: tl => v <- index_into_str_dv str i;; loop v tl
          end) dv2 idxs) as res.
    destruct_err_ub_oom res;
      symmetry in Heqres.
    - apply orutt_raiseOOM.
    - apply extract_value_loop_fin_inf_no_ub in Heqres; contradiction.
    - erewrite extract_value_loop_fin_inf_err; eauto.
      apply orutt_raise; auto.
    - erewrite extract_value_loop_fin_inf_succeeds; cbn; eauto.
      apply orutt_Ret.
      apply fin_to_inf_dvalue_refine_strict.
  Qed.

  Lemma orutt_insert_value_loop :
    forall E1 E2
      `{OOM1 : OOME -< E1} `{OOM2 : OOME -< E2}
      `{UB1 : UBE -< E1} `{UB2 : UBE -< E2}
      `{ERR1: FailureE -< E1} `{ERR2: FailureE -< E2}
      (pre : prerel E1 E2) (post : postrel E1 E2)
      (UBDISC : forall e1 e2, @subevent UBE E2 UB2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (ERRDISC : forall e1 e2, @subevent FailureE E2 ERR2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (UBINJ : pre void void (@subevent UBE E1 UB1 void (ThrowUB tt)) (@subevent UBE E2 UB2 void (ThrowUB tt)))
      (ERRINJ : pre void void (@subevent FailureE E1 ERR1 void (Throw tt)) (@subevent FailureE E2 ERR2 void (Throw tt)))
      dv1 dv2 dv1' dv2' idxs,
      dvalue_refine_strict dv1 dv2 ->
      dvalue_refine_strict dv1' dv2' ->
      orutt pre post dvalue_refine_strict
        ((fix loop (str : DV1.dvalue) (idxs0 : list LLVMAst.int_ast) {struct idxs0} :
           itree _ DV1.dvalue :=
            match idxs0 with
            | [] => LLVMEvents.raise "Index was not provided"
            | [i] =>
                ITree.bind (DV1.insert_into_str str dv1' i)
                  (fun v : DV1.dvalue => Ret v)
            | i :: (_ :: _) as tl =>
                ITree.bind (DV1.index_into_str_dv str i)
                  (fun subfield : DV1.dvalue =>
                     ITree.bind (loop subfield tl)
                       (fun modified_subfield : DV1.dvalue =>
                          DV1.insert_into_str str modified_subfield i))
            end) dv1 idxs)
        ((fix loop (str : dvalue) (idxs0 : list LLVMAst.int_ast) {struct idxs0} : itree _ dvalue :=
            match idxs0 with
            | [] => LLVMEvents.raise "Index was not provided"
            | [i] => ITree.bind (insert_into_str str dv2' i) (fun v : dvalue => Ret v)
            | i :: (_ :: _) as tl =>
                ITree.bind (index_into_str_dv str i)
                  (fun subfield : dvalue =>
                     ITree.bind (loop subfield tl)
                       (fun modified_subfield : dvalue => insert_into_str str modified_subfield i))
            end) dv2 idxs)
        (OOM:=OOME).
  Proof.
    intros E1 E2 OOM1 OOM2 UB1 UB2 ERR1 ERR2 pre post UBDISC ERRDISC UBINJ ERRINJ dv1 dv2 dv1' dv2' idxs REF1 REF2.
    setoid_rewrite TLR1.insert_value_loop_err_ub_oom_to_itree;
      setoid_rewrite TLR2.insert_value_loop_err_ub_oom_to_itree.

    erewrite (fin_to_inf_dvalue_refine_strict' dv1); eauto.
    erewrite (fin_to_inf_dvalue_refine_strict' dv1'); eauto.

    erewrite insert_value_loop_fin_inf_succeeds; eauto.
    remember
      ((fix loop (str : dvalue) (idxs0 : list LLVMAst.int_ast) {struct idxs0} : err_ub_oom dvalue :=
          match idxs0 with
          | [] => raise_error "Index was not provided"
          | [i] => v <- insert_into_str str dv2' i;; ret v
          | i :: (_ :: _) as tl =>
              subfield <- index_into_str_dv str i;;
              modified_subfield <- loop subfield tl;; insert_into_str str modified_subfield i
          end) dv2 idxs) as res.
    destruct_err_ub_oom res;
      symmetry in Heqres; cbn.
    - apply orutt_raiseOOM.
    - apply orutt_raiseUB; auto.
    - apply orutt_raise; auto.
    - apply orutt_Ret.
      apply fin_to_inf_dvalue_refine_strict.
  Qed.

End AggregateOpsRefine.
