From Vellvm.Syntax Require Import
     DataLayout
     DynamicTypes.

From Vellvm.Semantics Require Import
     MemoryAddress
     MemoryParams
     Memory.Overlaps
     LLVMParams
     LLVMEvents
     ItreeRaiseMReturns.

Require Import MemBytes.

From Vellvm.Handlers Require Import
  MemPropT
  MemoryModules.Within.

From Vellvm.Utils Require Import
     Error
     PropT
     Util
     NMaps
     Tactics
     Raise
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

From ITree Require Import
     ITree
     Basics.Basics
     Events.Exception
     Eq.Eq
     Events.StateFacts
     Events.State.

From Coq Require Import
     ZArith
     Strings.String
     List
     Lia
     Relations
     RelationClasses
     Wellfounded.

Require Import Morphisms.

Import ListNotations.
Import ListUtil.
Import Utils.Monads.

Import Basics.Basics.Monads.
Import MonadNotation.
Open Scope monad_scope.


Module Type MemoryModelSpecPrimitives (LP : LLVMParams) (MP : MemoryParams LP).
  Import LP.Events.
  Import LP.ADDR.
  Import LP.SIZEOF.
  Import LP.PROV.

  Import MemBytes.
  Module MemByte := Byte LP.ADDR LP.IP LP.SIZEOF LP.Events MP.BYTE_IMPL.
  Import MemByte.
  Import LP.SIZEOF.

  (*** Internal state of memory *)
  Parameter MemState : Type.
  Parameter memory_stack : Type.
  Parameter initial_memory_state : MemState.
  Parameter MemState_get_memory : MemState -> memory_stack.
  Parameter MemState_get_provenance : MemState -> Provenance.
  Parameter MemState_put_memory : memory_stack -> MemState -> MemState.

  (* Type for frames and frame stacks *)
  Parameter Frame : Type.
  Parameter FrameStack : Type.

  (* Heaps *)
  Parameter Heap : Type.

  (* TODO: Should DataLayout be here?

     It might make sense to move DataLayout to another module, some of
     the parameters in the DataLayout may be relevant to other
     modules, and we could enforce that everything agrees.

     For instance alignment may impact Sizeof, and there's also some
     stuff about pointer sizes in the DataLayout structure.
   *)
  (* Parameter datalayout : DataLayout. *)

  (*** Primitives on memory *)

  (** Reads *)
  Parameter read_byte_MemPropT : addr -> MemPropT memory_stack SByte.

  (** Allocations *)
  (* Returns true if a byte is allocated with a given AllocationId? *)
  Parameter addr_allocated_prop : addr -> AllocationId -> MemPropT memory_stack bool.

  (** Frame stacks *)
  (* Check if an address is allocated in a frame *)
  Parameter ptr_in_frame_prop : Frame -> addr -> Prop.

  (* Check for the current frame *)
  Parameter peek_frame_stack_prop : FrameStack -> Frame -> Prop.
  Parameter pop_frame_stack_prop : FrameStack -> FrameStack -> Prop.

  Parameter memory_stack_frame_stack_prop : memory_stack -> FrameStack -> Prop.

  Definition frame_eqv (f f' : Frame) : Prop :=
    forall ptr, ptr_in_frame_prop f ptr <-> ptr_in_frame_prop f' ptr.

  #[global] Instance frame_eqv_Equivalence : Equivalence frame_eqv.
  Proof.
    split.
    - intros f ptr.
      reflexivity.
    - intros f1 f2 EQV.
      unfold frame_eqv in *.
      firstorder.
    - intros x y z XY YZ.
      firstorder.
  Qed.

  Parameter frame_stack_eqv : FrameStack -> FrameStack -> Prop.
  #[global] Parameter frame_stack_eqv_Equivalence : Equivalence frame_stack_eqv.

  (** Heaps *)

  Parameter root_in_heap_prop : Heap -> addr -> Prop.

  (* 1) heap
     2) root pointer
     3) pointer

     The root pointer is the reference to a block that will be freed.
   *)
  Parameter ptr_in_heap_prop : Heap -> addr -> addr -> Prop.

  (* Memory stack's heap *)
  Parameter memory_stack_heap_prop : memory_stack -> Heap -> Prop.

  Record heap_eqv (h h' : Heap) : Prop :=
    {
      heap_roots_eqv : forall root, root_in_heap_prop h root <-> root_in_heap_prop h' root;
      heap_ptrs_eqv : forall root ptr, ptr_in_heap_prop h root ptr <-> ptr_in_heap_prop h' root ptr;
    }.

  #[global] Instance root_in_heap_prop_Proper :
    Proper (heap_eqv ==> eq ==> iff) root_in_heap_prop.
  Proof.
    intros h h' HEAPEQ ptr ptr' PTREQ; subst.
    inv HEAPEQ.
    eauto.
  Qed.

  #[global] Instance ptr_in_heap_prop_Proper :
    Proper (heap_eqv ==> eq ==> eq ==> iff) ptr_in_heap_prop.
  Proof.
    intros h h' HEAPEQ root root' ROOTEQ ptr ptr' PTREQ; subst.
    inv HEAPEQ.
    eauto.
  Qed.

  #[global] Instance heap_Equivalence : Equivalence heap_eqv.
  Proof.
    split.
    - intros h; split.
      + intros root.
        reflexivity.
      + intros root ptr.
        reflexivity.
    - intros h1 h2 EQV.
      firstorder.
    - intros x y z XY YZ.
      split.
      + intros root.
        rewrite XY, YZ.
        reflexivity.
      + intros root ptr.
        rewrite XY, YZ.
        reflexivity.
  Qed.

  (** Provenances *)
  Parameter used_provenance_prop : MemState -> Provenance -> Prop. (* Has a provenance *ever* been used. *)

  (* Allocate a new fresh provenance *)
  Parameter mem_state_fresh_provenance : MemState -> (Provenance * MemState)%type.
  Parameter mem_state_fresh_provenance_fresh :
    forall (ms ms' : MemState) (pr : Provenance),
      mem_state_fresh_provenance ms = (pr, ms') ->
      MemState_get_memory ms = MemState_get_memory ms' /\
        (forall pr, used_provenance_prop ms pr -> used_provenance_prop ms' pr) /\
      ~ used_provenance_prop ms pr /\ used_provenance_prop ms' pr.

  (** Lemmas about MemState *)
  Parameter MemState_get_put_memory :
    forall ms mem,
      MemState_get_memory (MemState_put_memory mem ms) = mem.

  #[global] Instance MemState_memory_MemStateMem : MemStateMem MemState memory_stack :=
    {| ms_get_memory := MemState_get_memory;
      ms_put_memory := MemState_put_memory;
      ms_get_put_memory := MemState_get_put_memory;
    |}.

  #[global] Instance Inhabited_MemState : Inhabited MemState :=
    { inhabitant := initial_memory_state
    }.

End MemoryModelSpecPrimitives.

Module MemoryHelpers (LP : LLVMParams) (MP : MemoryParams LP) (Byte : ByteModule LP.ADDR LP.IP LP.SIZEOF LP.Events MP.BYTE_IMPL).
  (*** Other helpers *)
  Import MP.GEP.
  Import MP.BYTE_IMPL.
  Import LP.
  Import LP.ADDR.
  Import LP.Events.
  Import LP.SIZEOF.
  Import LP.PTOI.
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

  Require Import MonadReturnsLaws.
  Import Monad.

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
      eapply map_monad_oom_forall2 in ALL_SHIFTED.

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
      + assert (eq1 (NoOom (l ++ [x])) (map_monad (fun ip : IP.intptr => IP.from_Z (IP.to_Z ip + 1)) (l_shifted ++ [y]))) as EQ.
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
    lift_err_RAISE_ERROR
      (map_monad
         (fun ix => handle_gep_addr (DTYPE_I 8) ptr [DVALUE_IPTR ix])
         ixs).

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
      `{EQV : @Eq1Equivalence M HM EQM}
      `{WRET : @Within_ret_inv M B Pre Post HM _ EQM WM}
      `{MLAWS : @MonadLawsE M EQM HM}
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
    cbn in *.
    destruct (intptr_seq 0 len) eqn:SEQ.
    - (* No OOM *)
      cbn in *.
      setoid_rewrite bind_ret_l in CONSEC.

      (* rewrite bind_ret_l in CONSEC. *)
      destruct (map_monad (fun ix : IP.intptr => handle_gep_addr (DTYPE_I 8) ptr [DVALUE_IPTR ix]) l) eqn:HMAPM.
      + (* Error: should be a contradiction *)
        (* TODO: need inversion lemma. *)
        cbn in CONSEC.
        convert_to_ret_hyp.
          eapply rw_ret_nin_raise in CONSEC; [contradiction | auto].
      + cbn in CONSEC.
        convert_to_ret_hyp.
        apply within_ret_ret in CONSEC; auto.
        assert (MReturns l0 (map_monad (fun ix : IP.intptr => handle_gep_addr (DTYPE_I 8) ptr [DVALUE_IPTR ix]) l)) as RETS.
        { auto. }

        epose proof MapMonadExtra.map_monad_length l _ _ RETS as LEN.
        apply intptr_seq_len in SEQ.
        subst.
        auto.
    - (* OOM: CONSEC equivalent to ret is a contradiction. *)
      cbn in CONSEC.
      setoid_rewrite rbm_raise_bind in CONSEC; auto.
      convert_to_ret_hyp;
        eapply rw_ret_nin_raise in CONSEC; [contradiction | auto].
  Qed.

  Lemma get_consecutive_ptrs_covers_range :
    forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
      {Pre Post : Type}
      {B} `{MB : Monad B}
      `{WM : @Within M EQM B Pre Post}
      `{EQV : @Eq1Equivalence M HM EQM}
      `{EQRET : @Eq1_ret_inv M EQM HM}
      `{WRET : @Within_ret_inv M B Pre Post HM _ EQM WM}
      `{LAWS : @MonadLawsE M EQM HM}
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
        convert_to_ret_hyp;
          eapply rw_ret_nin_raise in CONSEC; [contradiction | try typeclasses eauto].
      + cbn in CONSEC.
        convert_to_ret_hyp.
        apply within_ret_ret in CONSEC; eauto.
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
        apply MP.GEP.handle_gep_addr_ix in GEP.
        exists p'. split; auto.
        subst.

        rewrite sizeof_dtyp_i8 in GEP.
        erewrite IP.from_Z_to_Z in GEP; [|apply FROMZ].
        lia.
    - cbn in CONSEC.
      setoid_rewrite rbm_raise_bind in CONSEC; [|typeclasses eauto].
      convert_to_ret_hyp;
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
      p = ptr /\ (exists ptr' len', len = S len' /\ (ret ptrs ∈ get_consecutive_ptrs ptr' len')%monad).
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
      convert_to_ret_hyp.
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
        convert_to_ret_hyp.
        apply rw_ret_nin_raise in CONSEC; eauto.
        contradiction.
      }

      (* map_monad succeeds *)
      cbn in CONSEC.
      convert_to_ret_hyp.
      eapply within_ret_ret in CONSEC; eauto.
      inv CONSEC.
      split; auto.

      destruct len.
      + cbn in Heqo0.
        inv Heqo0.
        cbn in Heqs.
        inv Heqs.
        exists ptr. exists 0%nat.
        split; auto.
        cbn.
        setoid_rewrite bind_ret_l.
        cbn.
        eapply within_ret_refl; eauto.
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
        rename a into p'.
        rename l1 into ptrs'.
        inv MAPM.

        exists p'.
        exists (S len).
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
        pose proof Heqo0 as SEQ.
        apply intptr_seq_shifted in Heqo0.
        destruct Heqo0 as [l'' [SEQ_SHIFT SHIFT]].
        rewrite SEQ_SHIFT.
        cbn.

        setoid_rewrite bind_ret_l.
        match goal with
        | _ : _ |- context [map_monad ?f ?l] =>
            assert (map_monad f l = inr (p' :: ptrs')) as Heqs'
        end.
        {
          eapply map_monad_eqv; eauto.
          eapply Forall2_forall.
          split.
          { eapply intptr_seq_len in SEQ, SEQ_SHIFT.
            lia.
          }

          intros n a b NTH NTH'.
          pose proof (intptr_seq_nth _ _ _ _ _ SEQ NTH) as IX.
          pose proof (intptr_seq_nth _ _ _ _ _ SEQ_SHIFT NTH') as IX'.
          cbn in IX'.

          apply handle_gep_addr_ix in Heqs0.
          erewrite handle_gep_addr_ix'.
          erewrite handle_gep_addr_ix'.
          reflexivity.
          reflexivity.

          assert (address_provenance p' = address_provenance ptr) as PROV.
          { rewrite map_monad_unfold in Heqs.
            cbn in Heqs.
            break_match_hyp; inv Heqs.
            break_match_hyp; inv H0.
            symmetry; eapply handle_gep_addr_preserves_provenance; eauto.
          }

          rewrite PROV.

          rewrite Heqs0.
          rewrite IP.from_Z_to_Z with (z:=1%Z) (i:=one); auto.

          assert ((ptr_to_int ptr + Z.of_N (sizeof_dtyp (DTYPE_I 8)) * 1 +
                     Z.of_N (sizeof_dtyp (DTYPE_I 8)) * IP.to_Z b) =
                    (ptr_to_int ptr + Z.of_N (sizeof_dtyp (DTYPE_I 8)) * IP.to_Z a))%Z as EQ.
          { rewrite sizeof_dtyp_i8.
            unfold Z.of_N.

            rewrite IP.from_Z_to_Z with (z:=(1 + Z.of_nat n)%Z) (i:=a); auto.
            rewrite IP.from_Z_to_Z with (z:=Z.of_nat n) (i:=b); auto.
            lia.
          }

          rewrite EQ.
          reflexivity.
        }

        rewrite Heqs'.
        cbn.

        eapply within_ret_refl; eauto.
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
        apply get_consecutive_ptrs_cons in CONSEC as (START & ptr' & len' & LENEQ & CONSEC).
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
        apply get_consecutive_ptrs_cons in CONSEC as (ptreq & ptr'' & len'' & LENEQ & CONSEC).
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
            convert_to_ret_hyp;
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
          convert_to_ret_hyp;
            eapply rw_ret_nin_raise in CONSEC'; eauto; contradiction.
          break_match_hyp; cbn in CONSEC'.
          convert_to_ret_hyp;
            eapply rw_ret_nin_raise in CONSEC'; eauto; contradiction.
          break_match_hyp; cbn in CONSEC'.
          inv Heqs0.
          break_match_hyp; inv Heqs0.

          apply handle_gep_addr_ix in Heqs.
          apply handle_gep_addr_ix in Heqs1.
          convert_to_ret_hyp.
          apply within_ret_ret in CONSEC'; eauto.
          inv CONSEC'.

          rewrite sizeof_dtyp_i8 in *.
          erewrite IP.from_Z_to_Z in Heqs1; eauto.
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
        apply get_consecutive_ptrs_cons in CONSEC as (START & ptr' & len' & LENEQ & CONSEC).
        subst.
        lia.
      + pose proof CONSEC as CONSEC'.
        apply get_consecutive_ptrs_cons in CONSEC as (START & ptr' & len' & LENEQ & CONSEC).
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
        apply get_consecutive_ptrs_cons in CONSEC as (ptreq & ptr'' & len'' & LENEQ & CONSEC).
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
            convert_to_ret_hyp.
            eapply rw_ret_nin_raise in CONSEC'; [contradiction | typeclasses eauto].
          }

          cbn in CONSEC'.
          convert_to_ret_hyp.
          apply within_ret_ret in CONSEC'; eauto.
          inv CONSEC'.
          break_match_hyp; inv Heqo0.
          break_match_hyp; inv H0.
          cbn in HMAPM.
          break_match_hyp; [inv HMAPM|].
          break_match_hyp; [inv HMAPM|].
          break_match_hyp; [inv Heqs0|].
          break_match_hyp; inv Heqs0.
          inv HMAPM.

          apply handle_gep_addr_ix in Heqs1.
          rewrite sizeof_dtyp_i8 in Heqs1.
          rewrite (IP.from_Z_to_Z _ _ Heqo1) in Heqs1.
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
              handle_gep_addr (DTYPE_I 8) ptr [Events.DV.DVALUE_IPTR ix] = inr p).
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
      convert_to_ret_hyp.
      apply rw_ret_nin_raise in CONSEC; try contradiction; auto.
    }

    cbn in CONSEC.
    convert_to_ret_hyp.
    apply within_ret_ret in CONSEC; auto.
    inv CONSEC.

    pose proof MAP as PTRS.
    eapply map_monad_err_forall2 in PTRS.
    eapply Forall2_forall in PTRS.
    destruct PTRS as [PTRSLEN PTRS].

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
              handle_gep_addr (DTYPE_I 8) ptr [Events.DV.DVALUE_IPTR ix] = inr p).
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
    - right.

      pose proof (map_monad_err_succeeds
                    (fun ix : IP.intptr => handle_gep_addr (DTYPE_I 8) ptr [Events.DV.DVALUE_IPTR ix]) l) as HMAPM.
      forward HMAPM.
      { intros a IN.
        eexists; eapply handle_gep_addr_ix'.
        reflexivity.
      }

      destruct HMAPM as (ptrs & HMAPM).
      exists ptrs.
      cbn.
      rewrite bind_ret_l.
      rewrite HMAPM.
      reflexivity.
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
        eexists; eapply handle_gep_addr_ix'.
        reflexivity.
      }

      destruct HMAPM as (ptrs & HMAPM).
      rewrite HMAPM in CONTRA.
      cbn in CONTRA.

      convert_to_raise_hyp.
      eapply rw_raise_nin_ret in CONTRA; eauto.
  Qed.

  Definition generate_num_undef_bytes_h (start_ix : N) (num : N) (dt : dtyp) (sid : store_id) : OOM (list SByte) :=
    N.recursion
      (fun (x : N) => ret [])
      (fun n mf x =>
         rest_bytes <- mf (N.succ x);;
         x' <- IP.from_Z (Z.of_N x);;
         let byte := uvalue_sbyte (UVALUE_Undef dt) dt (UVALUE_IPTR x') sid in
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
           x' <- IP.from_Z (Z.of_N x);;
           ret (uvalue_sbyte (UVALUE_Undef dt) dt (UVALUE_IPTR x') sid :: rest_bytes))
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
                        x' <- IP.from_Z (Z.of_N x);;
                        ret (uvalue_sbyte (UVALUE_Undef dt) dt (UVALUE_IPTR x') sid :: rest_bytes)) num
                     (N.succ start_ix)) eqn:HREC.
      + (* No OOM *)
        cbn in GEN.
        break_match_hyp; inv GEN.
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

    Definition uvalue_bytes_little_endian (uv :  uvalue) (dt : dtyp) (sid : store_id) : OOM (list uvalue)
      := map_monad (fun n => n' <- IP.from_Z (Z.of_N n);;
                          ret (UVALUE_ExtractByte uv dt (UVALUE_IPTR n') sid)) (Nseq 0 (N.to_nat (sizeof_dtyp DTYPE_Pointer))).

    Definition uvalue_bytes (e : Endianess) (uv :  uvalue) (dt : dtyp) (sid : store_id) : OOM (list uvalue)
      := fmap (correct_endianess e) (uvalue_bytes_little_endian uv dt sid).

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

    From Coq Require Import FunctionalExtensionality.
    
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

    Program Fixpoint serialize_sbytes
            {M} `{Monad M} `{MonadStoreId M} `{RAISE_ERROR M} `{RAISE_OOM M}
            (uv : uvalue) (dt : dtyp) {measure (uvalue_measure uv, dtyp_measure dt) lex_nats} : M (list SByte)
      :=
      match uv with
      (* Base types *)
      | UVALUE_Addr _
      | UVALUE_I1 _
      | UVALUE_I8 _
      | UVALUE_I32 _
      | UVALUE_I64 _
      | UVALUE_IPTR _
      | UVALUE_Float _
      | UVALUE_Double _

      (* Expressions *)
      | UVALUE_IBinop _ _ _
      | UVALUE_ICmp _ _ _
      | UVALUE_FBinop _ _ _ _
      | UVALUE_FCmp _ _ _
      | UVALUE_Conversion _ _ _ _
      | UVALUE_GetElementPtr _ _ _
      | UVALUE_ExtractElement _ _ _
      | UVALUE_InsertElement _ _ _ _
      | UVALUE_ShuffleVector _ _ _
      | UVALUE_ExtractValue _ _ _
      | UVALUE_InsertValue _ _ _ _
      | UVALUE_Select _ _ _ =>
          sid <- fresh_sid;;
          lift_OOM (to_ubytes uv dt sid)

      (* Undef values, these can possibly be aggregates *)
      | UVALUE_Undef _ =>
          match dt with
          | DTYPE_Struct [] =>
              ret []
          | DTYPE_Struct (t::ts) =>
              f_bytes <- serialize_sbytes (UVALUE_Undef t) t;; (* How do I know this is smaller? *)
              fields_bytes <- serialize_sbytes (UVALUE_Undef (DTYPE_Struct ts)) (DTYPE_Struct ts);;
              ret (f_bytes ++ fields_bytes)

          | DTYPE_Packed_struct [] =>
              ret []
          | DTYPE_Packed_struct (t::ts) =>
              f_bytes <- serialize_sbytes (UVALUE_Undef t) t;; (* How do I know this is smaller? *)
              fields_bytes <- serialize_sbytes (UVALUE_Undef (DTYPE_Packed_struct ts)) (DTYPE_Packed_struct ts);;
              ret (f_bytes ++ fields_bytes)

          | DTYPE_Array sz t =>
              field_bytes <- map_monad_In (repeatN sz (UVALUE_Undef t)) (fun elt Hin => serialize_sbytes elt t);;
              ret (concat field_bytes)

          | DTYPE_Vector sz t =>
              field_bytes <- map_monad_In (repeatN sz (UVALUE_Undef t)) (fun elt Hin => serialize_sbytes elt t);;
              ret (concat field_bytes)
          | _ =>
              sid <- fresh_sid;;
              lift_OOM (to_ubytes uv dt sid)
          end

      (* Poison values, possibly aggregates *)
      | UVALUE_Poison _ =>
          match dt with
          | DTYPE_Struct [] =>
              ret []
          | DTYPE_Struct (t::ts) =>
              f_bytes <- serialize_sbytes (UVALUE_Poison t) t;; (* How do I know this is smaller? *)
              fields_bytes <- serialize_sbytes (UVALUE_Poison (DTYPE_Struct ts)) (DTYPE_Struct ts);;
              ret (f_bytes ++ fields_bytes)

          | DTYPE_Packed_struct [] =>
              ret []
          | DTYPE_Packed_struct (t::ts) =>
              f_bytes <- serialize_sbytes (UVALUE_Poison t) t;; (* How do I know this is smaller? *)
              fields_bytes <- serialize_sbytes (UVALUE_Poison (DTYPE_Packed_struct ts)) (DTYPE_Packed_struct ts);;
              ret (f_bytes ++ fields_bytes)

          | DTYPE_Array sz t =>
              field_bytes <- map_monad_In (repeatN sz (UVALUE_Poison t)) (fun elt Hin => serialize_sbytes elt t);;
              ret (concat field_bytes)

          | DTYPE_Vector sz t =>
              field_bytes <- map_monad_In (repeatN sz (UVALUE_Poison t)) (fun elt Hin => serialize_sbytes elt t);;
              ret (concat field_bytes)
          | _ =>
              sid <- fresh_sid;;
              lift_OOM (to_ubytes uv dt sid)
          end

      (* TODO: each field gets a separate store id... Is that sensible? *)
      (* Padded aggregate types *)
      | UVALUE_Struct [] =>
          ret []
      | UVALUE_Struct (f::fields) =>
          (* TODO: take padding into account *)
          match dt with
          | DTYPE_Struct (t::ts) =>
              f_bytes <- serialize_sbytes f t;;
              fields_bytes <- serialize_sbytes (UVALUE_Struct fields) (DTYPE_Struct ts);;
              ret (f_bytes ++ fields_bytes)
          | _ =>
              raise_error "serialize_sbytes: UVALUE_Struct field / type mismatch."
          end

      (* Packed aggregate types *)
      | UVALUE_Packed_struct [] =>
          ret []
      | UVALUE_Packed_struct (f::fields) =>
          (* TODO: take padding into account *)
          match dt with
          | DTYPE_Packed_struct (t::ts) =>
              f_bytes <- serialize_sbytes f t;;
              fields_bytes <- serialize_sbytes (UVALUE_Packed_struct fields) (DTYPE_Packed_struct ts);;
              ret (f_bytes ++ fields_bytes)
          | _ =>
              raise_error "serialize_sbytes: UVALUE_Packed_struct field / type mismatch."
          end

      | UVALUE_Array elts =>
          match dt with
          | DTYPE_Array sz t =>
              field_bytes <- map_monad_In elts (fun elt Hin => serialize_sbytes elt t);;
              ret (concat field_bytes)
          | _ =>
              raise_error "serialize_sbytes: UVALUE_Array with incorrect type."
          end
      | UVALUE_Vector elts =>
          match dt with
          | DTYPE_Vector sz t =>
              field_bytes <- map_monad_In elts (fun elt Hin => serialize_sbytes elt t);;
              ret (concat field_bytes)
          | _ =>
              raise_error "serialize_sbytes: UVALUE_Array with incorrect type."
          end

      | UVALUE_None => ret nil

      (* Byte manipulation. *)
      | UVALUE_ExtractByte uv dt' idx sid =>
          raise_error "serialize_sbytes: UVALUE_ExtractByte not guarded by UVALUE_ConcatBytes."

      | UVALUE_ConcatBytes bytes t =>
          (* TODO: should provide *new* sids... May need to make this function in a fresh sid monad *)
          bytes' <- lift_ERR_RAISE_ERROR (map_monad extract_byte_to_sbyte bytes);;
          re_sid_ubytes bytes'
      end.
    Next Obligation.
      unfold Wf.MR.
      unfold lex_nats.
      apply wf_inverse_image.
      apply wf_lexprod; intros;
        apply Wf_nat.lt_wf.
    Qed.

    Lemma serialize_sbytes_equation {M} `{Monad M} `{MonadStoreId M} `{RAISE_ERROR M} `{RAISE_OOM M} : forall (uv : uvalue) (dt : dtyp),
        @serialize_sbytes M _ _ _ _ uv dt =
          match uv with
          (* Base types *)
          | UVALUE_Addr _
          | UVALUE_I1 _
          | UVALUE_I8 _
          | UVALUE_I32 _
          | UVALUE_I64 _
          | UVALUE_IPTR _
          | UVALUE_Float _
          | UVALUE_Double _

          (* Expressions *)
          | UVALUE_IBinop _ _ _
          | UVALUE_ICmp _ _ _
          | UVALUE_FBinop _ _ _ _
          | UVALUE_FCmp _ _ _
          | UVALUE_Conversion _ _ _ _
          | UVALUE_GetElementPtr _ _ _
          | UVALUE_ExtractElement _ _ _
          | UVALUE_InsertElement _ _ _ _
          | UVALUE_ShuffleVector _ _ _
          | UVALUE_ExtractValue _ _ _
          | UVALUE_InsertValue _ _ _ _
          | UVALUE_Select _ _ _ =>
              sid <- fresh_sid;;
              lift_OOM (to_ubytes uv dt sid)

          (* Undef values, these can possibly be aggregates *)
          | UVALUE_Undef _ =>
              match dt with
              | DTYPE_Struct [] =>
                  ret []
              | DTYPE_Struct (t::ts) =>
                  f_bytes <- serialize_sbytes (UVALUE_Undef t) t;; (* How do I know this is smaller? *)
                  fields_bytes <- serialize_sbytes (UVALUE_Undef (DTYPE_Struct ts)) (DTYPE_Struct ts);;
                  ret (f_bytes ++ fields_bytes)

              | DTYPE_Packed_struct [] =>
                  ret []
              | DTYPE_Packed_struct (t::ts) =>
                  f_bytes <- serialize_sbytes (UVALUE_Undef t) t;; (* How do I know this is smaller? *)
                  fields_bytes <- serialize_sbytes (UVALUE_Undef (DTYPE_Packed_struct ts)) (DTYPE_Packed_struct ts);;
                  ret (f_bytes ++ fields_bytes)

              | DTYPE_Array sz t =>
                  field_bytes <- map_monad_In (repeatN sz (UVALUE_Undef t)) (fun elt Hin => serialize_sbytes elt t);;
                  ret (concat field_bytes)

              | DTYPE_Vector sz t =>
                  field_bytes <- map_monad_In (repeatN sz (UVALUE_Undef t)) (fun elt Hin => serialize_sbytes elt t);;
                  ret (concat field_bytes)
              | _ =>
                  sid <- fresh_sid;;
                  lift_OOM (to_ubytes uv dt sid)
              end

          (* Poison values, possibly aggregates *)
          | UVALUE_Poison _ =>
              match dt with
              | DTYPE_Struct [] =>
                  ret []
              | DTYPE_Struct (t::ts) =>
                  f_bytes <- serialize_sbytes (UVALUE_Poison t) t;; (* How do I know this is smaller? *)
                  fields_bytes <- serialize_sbytes (UVALUE_Poison (DTYPE_Struct ts)) (DTYPE_Struct ts);;
                  ret (f_bytes ++ fields_bytes)

              | DTYPE_Packed_struct [] =>
                  ret []
              | DTYPE_Packed_struct (t::ts) =>
                  f_bytes <- serialize_sbytes (UVALUE_Poison t) t;; (* How do I know this is smaller? *)
                  fields_bytes <- serialize_sbytes (UVALUE_Poison (DTYPE_Packed_struct ts)) (DTYPE_Packed_struct ts);;
                  ret (f_bytes ++ fields_bytes)

              | DTYPE_Array sz t =>
                  field_bytes <- map_monad_In (repeatN sz (UVALUE_Poison t)) (fun elt Hin => serialize_sbytes elt t);;
                  ret (concat field_bytes)

              | DTYPE_Vector sz t =>
                  field_bytes <- map_monad_In (repeatN sz (UVALUE_Poison t)) (fun elt Hin => serialize_sbytes elt t);;
                  ret (concat field_bytes)
              | _ =>
                  sid <- fresh_sid;;
                  lift_OOM (to_ubytes uv dt sid)
              end

          (* TODO: each field gets a separate store id... Is that sensible? *)
          (* Padded aggregate types *)
          | UVALUE_Struct [] =>
              ret []
          | UVALUE_Struct (f::fields) =>
              (* TODO: take padding into account *)
              match dt with
              | DTYPE_Struct (t::ts) =>
                  f_bytes <- serialize_sbytes f t;;
                  fields_bytes <- serialize_sbytes (UVALUE_Struct fields) (DTYPE_Struct ts);;
                  ret (f_bytes ++ fields_bytes)
              | _ =>
                  raise_error "serialize_sbytes: UVALUE_Struct field / type mismatch."
              end

          (* Packed aggregate types *)
          | UVALUE_Packed_struct [] =>
              ret []
          | UVALUE_Packed_struct (f::fields) =>
              (* TODO: take padding into account *)
              match dt with
              | DTYPE_Packed_struct (t::ts) =>
                  f_bytes <- serialize_sbytes f t;;
                  fields_bytes <- serialize_sbytes (UVALUE_Packed_struct fields) (DTYPE_Packed_struct ts);;
                  ret (f_bytes ++ fields_bytes)
              | _ =>
                  raise_error "serialize_sbytes: UVALUE_Packed_struct field / type mismatch."
              end

          | UVALUE_Array elts =>
              match dt with
              | DTYPE_Array sz t =>
                  field_bytes <- map_monad_In elts (fun elt Hin => serialize_sbytes elt t);;
                  ret (concat field_bytes)
              | _ =>
                  raise_error "serialize_sbytes: UVALUE_Array with incorrect type."
              end
          | UVALUE_Vector elts =>
              match dt with
              | DTYPE_Vector sz t =>
                  field_bytes <- map_monad_In elts (fun elt Hin => serialize_sbytes elt t);;
                  ret (concat field_bytes)
              | _ =>
                  raise_error "serialize_sbytes: UVALUE_Array with incorrect type."
              end

          | UVALUE_None => ret nil

          (* Byte manipulation. *)
          | UVALUE_ExtractByte uv dt' idx sid =>
              raise_error "serialize_sbytes: UVALUE_ExtractByte not guarded by UVALUE_ConcatBytes."

          | UVALUE_ConcatBytes bytes t =>
              (* TODO: should provide *new* sids... May need to make this function in a fresh sid monad *)
              bytes' <- lift_ERR_RAISE_ERROR (map_monad extract_byte_to_sbyte bytes);;
              re_sid_ubytes bytes'
          end.
    Proof.
      intros.
      unfold serialize_sbytes at 1.
      unfold serialize_sbytes_func at 1.
      (* rewrite Wf.WfExtensionality.fix_sub_eq_ext.  (* <<=== THIS STEP TAKES A LONG TIME *) *)
      (* simpl. (* <<=== my *goals* buffer goes from 4.5M to 37130 lines (2.5M) of text *) *)
      (* destruct uv; simpl; try reflexivity. *)
      (* - destruct dt; try reflexivity. *)
      (*   + destruct fields; try reflexivity. *)
      (*   + destruct fields; try reflexivity. *)
      (* - destruct dt; try reflexivity. *)
      (*   + destruct fields; try reflexivity. *)
      (*   + destruct fields; try reflexivity. *)
      (* - destruct fields; try reflexivity. *)
      (*   destruct dt; try reflexivity. *)
      (*   destruct fields0; try reflexivity. *)
      (* - destruct fields; try reflexivity. *)
      (*   destruct dt; try reflexivity. *)
      (*   destruct fields0; try reflexivity. *)
      (* - destruct dt; try reflexivity. *)
      (* - destruct dt; try reflexivity. *)
    Admitted.
          
    (* deserialize_sbytes takes a list of SBytes and turns them into a uvalue. *)

  (*    This relies on the similar, but different, from_ubytes function *)
  (*    which given a set of bytes checks if all of the bytes are from *)
  (*    the same uvalue, and if so returns the original uvalue, and *)
  (*    otherwise returns a UVALUE_ConcatBytes value instead. *)

  (*    The reason we also have deserialize_sbytes is in order to deal *)
  (*    with aggregate data types. *)
  (*    *)
    Obligation Tactic := try Tactics.program_simpl; try solve [solve_dtyp_measure].
    Program Fixpoint deserialize_sbytes (bytes : list SByte) (dt : dtyp) {measure (dtyp_measure dt)} : err uvalue
      :=
      match dt with
      (* TODO: should we bother with this? *)
      (* Array and vector types *)
      | DTYPE_Array sz t =>
          let elt_size := sizeof_dtyp t in
          fields <- monad_fold_right (fun acc idx => uv <- deserialize_sbytes (between (idx*elt_size) ((idx+1) * elt_size) bytes) t;; ret (uv::acc)) (Nseq 0 (N.to_nat sz)) [];;
          ret (UVALUE_Array fields)

      | DTYPE_Vector sz t =>
          let elt_size := sizeof_dtyp t in
          fields <- monad_fold_right (fun acc idx => uv <- deserialize_sbytes (between (idx*elt_size) ((idx+1) * elt_size) bytes) t;; ret (uv::acc)) (Nseq 0 (N.to_nat sz)) [];;
          ret (UVALUE_Vector fields)

      (* Padded aggregate types *)
      | DTYPE_Struct fields =>
          (* TODO: Add padding *)
          match fields with
          | [] => ret (UVALUE_Struct []) (* TODO: Not 100% sure about this. *)
          | (dt::dts) =>
              let sz := sizeof_dtyp dt in
              let init_bytes := take sz bytes in
              let rest_bytes := drop sz bytes in
              f <- deserialize_sbytes init_bytes dt;;
              rest <- deserialize_sbytes rest_bytes (DTYPE_Struct dts);;
              match rest with
              | UVALUE_Struct fs =>
                  ret (UVALUE_Struct (f::fs))
              | _ =>
                  inl "deserialize_sbytes: DTYPE_Struct recursive call did not return a struct."%string
              end
          end

      (* Structures with no padding *)
      | DTYPE_Packed_struct fields =>
          match fields with
          | [] => ret (UVALUE_Packed_struct []) (* TODO: Not 100% sure about this. *)
          | (dt::dts) =>
              let sz := sizeof_dtyp dt in
              let init_bytes := take sz bytes in
              let rest_bytes := drop sz bytes in
              f <- deserialize_sbytes init_bytes dt;;
              rest <- deserialize_sbytes rest_bytes (DTYPE_Packed_struct dts);;
              match rest with
              | UVALUE_Packed_struct fs =>
                  ret (UVALUE_Packed_struct (f::fs))
              | _ =>
                  inl "deserialize_sbytes: DTYPE_Struct recursive call did not return a struct."%string
              end
          end

      (* Base types *)
      | DTYPE_I _
      | DTYPE_IPTR
      | DTYPE_Pointer
      | DTYPE_Half
      | DTYPE_Float
      | DTYPE_Double
      | DTYPE_X86_fp80
      | DTYPE_Fp128
      | DTYPE_Ppc_fp128
      | DTYPE_X86_mmx
      | DTYPE_Opaque
      | DTYPE_Metadata =>
          ret (from_ubytes bytes dt)

      | DTYPE_Void =>
          inl "deserialize_sbytes: Attempt to deserialize void."%string
      end.

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
    := read_byte_MemPropT ptr (MemState_get_memory ms) (ret ((MemState_get_memory ms), byte)).

  Definition lift_memory_MemPropT {X} (m : MemPropT memory_stack X) : MemPropT MemState X :=
    fun ms res =>
      m (MemState_get_memory ms) (fmap (fun '(ms, x) => (MemState_get_memory ms, x)) res) /\
        (* Provenance should be preserved as memory operation shouldn't touch rest of MemState *)
        forall ms' x, res = ret (ms', x) -> MemState_get_provenance ms = MemState_get_provenance ms'.

  Definition byte_allocated_MemPropT (ptr : addr) (aid : AllocationId) : MemPropT MemState unit :=
    b <- lift_memory_MemPropT (addr_allocated_prop ptr aid);;
    MemPropT_assert (b = true).

  Definition byte_allocated (ms : MemState) (ptr : addr) (aid : AllocationId) : Prop
    := byte_allocated_MemPropT ptr aid ms (ret (ms, tt)).

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
  Definition frame_stack_preserved (m1 m2 : MemState) : Prop
    := forall fs,
      memory_stack_frame_stack_prop (MemState_get_memory m1) fs <-> memory_stack_frame_stack_prop (MemState_get_memory m2) fs.

  (** Heap *)
  Definition heap_preserved (m1 m2 : MemState) : Prop
    := forall h,
      memory_stack_heap_prop (MemState_get_memory m1) h <-> memory_stack_heap_prop (MemState_get_memory m2) h.

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
      (fun m1 =>
         forall byte, ~ read_byte_spec m1 ptr byte).

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
      (fun m1 =>
         forall m2, ~ mempush_spec m1 m2).

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
          ~ cannot_pop m1 /\ forall m2, ~ mempop_spec m1 m2
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
        forall root, ptr_in_heap_prop h1 root ptr' <-> ptr_in_heap_prop h2 root ptr';

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
      old_lu : forall ptr' byte',
        disjoint_ptr_byte ptr ptr' ->
        (read_byte_spec m1 ptr' byte' <-> read_byte_spec m2 ptr' byte');
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
      (fun m1 =>
         forall m2, ~ write_byte_spec m1 ptr byte m2).

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
    (m1 : MemState) (t : dtyp) (num_elements : N) (init_bytes : list SByte)
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

      (* Type is valid *)
      allocate_bytes_typ :
      t <> DTYPE_Void;

      allocate_bytes_typ_size :
      (sizeof_dtyp t * num_elements = N.of_nat (length init_bytes))%N;
    }.

  Definition allocate_bytes_post_conditions_MemPropT
    (t : dtyp) (num_elements : N) (init_bytes : list SByte)
    (prov : Provenance) (ptr : addr) (ptrs : list addr)
    : MemPropT MemState (addr * list addr)
    := fun m1 res =>
         match run_err_ub_oom res with
         | inl (OOM_message x) =>
             False
         | inr (inl (UB_message x)) =>
             t = DTYPE_Void \/ (sizeof_dtyp t * num_elements <> N.of_nat (length init_bytes))%N
         | inr (inr (inl (ERR_message x))) =>
             False
         | inr (inr (inr (m2, (ptr', ptrs')))) =>
             allocate_bytes_post_conditions m1 t num_elements init_bytes prov m2 ptr ptrs /\ ptr = ptr' /\ ptrs = ptrs'
         end.

  Definition allocate_bytes_with_pr_spec_MemPropT
    (t : dtyp) (num_elements : N) (init_bytes : list SByte) (prov : Provenance)
    : MemPropT MemState addr
    := '(ptr, ptrs) <- find_free_block (length init_bytes) prov;;
       allocate_bytes_post_conditions_MemPropT t num_elements init_bytes prov ptr ptrs;;
       ret ptr.

  Definition allocate_bytes_spec_MemPropT
    (t : dtyp) (num_elements : N) (init_bytes : list SByte)
    : MemPropT MemState addr
    := prov <- fresh_provenance;;
       allocate_bytes_with_pr_spec_MemPropT t num_elements init_bytes prov.

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

  Record free_spec (m1 : MemState) (root : addr) (m2 : MemState) : Prop :=
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

      (* all bytes in block are freed. *)
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
         free_spec m1 root m2)
      (fun m1 =>
         forall m2, ~ free_spec m1 root m2).

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
    sid <- fresh_sid;;
    element_bytes <- repeatMN num_elements (lift_OOM (generate_undef_bytes dt sid));;
    let bytes := concat element_bytes in
    allocate_bytes_spec_MemPropT dt num_elements bytes.

  (** memcpy spec *)
  Definition memcpy_spec (src dst : addr) (len : Z) (align : N) (volatile : bool) : MemPropT MemState unit :=
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
                    DVALUE_I32 align :: (* alignment ignored *)
                    DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          memcpy_spec src dst (unsigned len) (Z.to_N (unsigned align)) (equ volatile one)
      | DVALUE_Addr dst ::
                    DVALUE_Addr src ::
                    DVALUE_I64 len ::
                    DVALUE_I64 align :: (* alignment ignored *)
                    DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          memcpy_spec src dst (unsigned len) (Z.to_N (unsigned align)) (equ volatile one)
      | DVALUE_Addr dst ::
                    DVALUE_Addr src ::
                    DVALUE_IPTR len ::
                    DVALUE_IPTR align :: (* alignment ignored *)
                    DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          memcpy_spec src dst (IP.to_Z len) (Z.to_N (IP.to_Z align)) (equ volatile one)
      | _ => raise_error "Unsupported arguments to memcpy."
      end.

    Definition handle_malloc_prop (args : list dvalue) : MemPropT MemState addr :=
      match args with
      | [DVALUE_I1 sz]
      | [DVALUE_I8 sz]
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
End MemoryModelSpec.

Module MakeMemoryModelSpec (LP : LLVMParams) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) <: MemoryModelSpec LP MP MMSP.
  Include MemoryModelSpec LP MP MMSP.
End MakeMemoryModelSpec.

Module Type MemoryExecMonad (LP : LLVMParams) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) (MMS : MemoryModelSpec LP MP MMSP).
  (* TODO: move these imports *)
  Import EitherMonad.
  Import Monad.
  Require Import Morphisms.
  From Vellvm Require Import
       MonadEq1Laws
       Raise.

  Import LP.
  Import PROV.
  Import MMSP.
  Import MMS.
  Import MemHelpers.

  Require Import Within.

  Class MemMonad (ExtraState : Type) (M : Type -> Type) (RunM : Type -> Type)
        `{MM : Monad M} `{MRun: Monad RunM}
        `{MPROV : MonadProvenance Provenance M} `{MSID : MonadStoreId M} `{MMS: MonadMemState MemState M}
        `{MERR : RAISE_ERROR M} `{MUB : RAISE_UB M} `{MOOM :RAISE_OOM M}
        `{RunERR : RAISE_ERROR RunM} `{RunUB : RAISE_UB RunM} `{RunOOM :RAISE_OOM RunM}
        `{EQM : Eq1 M} `{EQRI : @Eq1_ret_inv M EQM MM} `{MLAWS : @MonadLawsE M EQM MM}
    : Type
    :=
    { MemMonad_eq1_runm :> Eq1 RunM;
      MemMonad_runm_monadlaws :> MonadLawsE RunM;
      MemMonad_eq1_runm_equiv :> Eq1Equivalence RunM;
      MemMonad_eq1_runm_eq1laws :> Eq1_ret_inv RunM;
      MemMonad_raisebindm_ub :> RaiseBindM RunM string (@raise_ub RunM RunUB);
      MemMonad_raisebindm_oom :> RaiseBindM RunM string (@raise_oom RunM RunOOM);
      MemMonad_raisebindm_err :> RaiseBindM RunM string (@raise_error RunM RunERR);
      MemMonad_within :> @Within M EQM RunM (ExtraState * MemState)%type (ExtraState * MemState)%type;

      MemMonad_eq1_runm_proper :>
                               (forall A, Proper ((@eq1 _ MemMonad_eq1_runm) A ==> (@eq1 _ MemMonad_eq1_runm) A ==> iff) ((@eq1 _ MemMonad_eq1_runm) A));

      MemMonad_run {A} (ma : M A) (ms : MemState) (st : ExtraState)
      : RunM (ExtraState * (MemState * A))%type;

      MemMonad_run_proper :>
        (forall A, Proper (@eq1 _ EQM A ==> eq ==> eq ==> @eq1 _ MemMonad_eq1_runm (ExtraState * (MemState * A))) MemMonad_run);

      (** Whether a piece of extra state is valid for a given execution *)
      MemMonad_valid_state : MemState -> ExtraState -> Prop;

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
      forall (ms : MemState), exists (st : ExtraState),
        MemMonad_valid_state ms st;
       *)
    (** Run bind / ret laws *)
    MemMonad_run_bind
      {A B} (ma : M A) (k : A -> M B) (ms : MemState) (st : ExtraState):
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

  Definition within_RunM_MemMonad {MemM RunM ExtraState} `{MM: MemMonad ExtraState MemM RunM} {A} (memm : MemM A) (pre : (ExtraState * MemState)%type) (runm : RunM A) (post : (ExtraState * MemState)%type) : Prop :=
    let '(st1, ms1) := pre in
    let '(st2, ms2) := post in
    let t := MemMonad_run memm ms1 st1 in
    let run := a <- runm;; ret (st2, (ms2, a)) : RunM (ExtraState * (MemState * A))%type in
    let eqi := (@eq1 _ (@MemMonad_eq1_runm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MM)) in
    eqi _ t run.

  Lemma within_eq1_Proper_RunM_MemMonad {MemM RunM ExtraState} `{MM: MemMonad ExtraState MemM RunM} {A} :
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

  #[global] Instance Within_RunM_MemMonad {MemM RunM ExtraState} `{MM: MemMonad ExtraState MemM RunM} : @Within MemM _ RunM (ExtraState * MemState)%type (ExtraState * MemState)%type.
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
    Proper (eq1 ==> eq ==> eq ==> eq ==> iff) (within_err_ub_oom_itree (Pre:=Pre) (Post:=Post) (A:=A)).
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
  #[global] Instance Within_err_ub_oom_MemM {MemM Eff ExtraState}
    `{EQI : Eq1 (itree Eff)}
    `{MITREE : Monad (itree Eff)}
    `{EQV : @Eq1Equivalence (itree Eff) _ EQI}
    `{FAIL : RAISE_ERROR (itree Eff)} `{UB : RAISE_UB (itree Eff)} `{OOM : RAISE_OOM (itree Eff)}
    `{MM: MemMonad ExtraState MemM (itree Eff)} : @Within MemM _ err_ub_oom (ExtraState * MemState)%type (ExtraState * MemState)%type.
  Proof.
    eapply @Transitive_Within with (M1:=err_ub_oom) (M2:=itree Eff) (M3:=MemM).
    - eapply Within_err_ub_oom_itree'.
    - eapply Within_RunM_MemMonad.
  Defined.

  (*** Correctness *)
  Definition exec_correct {MemM Eff ExtraState} `{MM: MemMonad ExtraState MemM (itree Eff)} {X} (pre : MemState -> ExtraState -> Prop) (exec : MemM X) (spec : MemPropT MemState X) : Prop :=
    forall ms st,
      (@MemMonad_valid_state ExtraState MemM (itree Eff) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ms st) ->
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
           exists (e : err_ub_oom X) (st' : ExtraState) (ms' : MemState),
             (* Had to manually supply typeclasses, but this within expression is: (e {{(st, ms)}} ∈ {{(st', ms')}} exec))

                 I.e., The executable is correct if forall behaviours
                 in the executable those behaviours are in the spec as
                 well, and if the executable returns successfully it
                 gives a valid ExtraState / MemState pair.
              *)
             let WEM := (Within_err_ub_oom_MemM (EQI:=(@MemMonad_eq1_runm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MM)) (EQV:=(@MemMonad_eq1_runm_equiv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MM))) in
             (@within MemM _ err_ub_oom (ExtraState * MemState)%type (ExtraState * MemState)%type WEM X exec (st, ms) e (st', ms')) /\
               (e {{ms}} ∈ {{ms'}} spec) /\ ((exists x, e = ret x) -> (@MemMonad_valid_state ExtraState MemM (itree Eff) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ms' st'))).

  Definition exec_correct_memory {MemM Eff ExtraState} `{MM: MemMonad ExtraState MemM (itree Eff)} {X} (pre : MemState -> ExtraState -> Prop) (exec : MemM X) (spec : MemPropT memory_stack X) : Prop :=
    exec_correct pre exec (lift_memory_MemPropT spec).

  Require Import Error.
  Require Import MonadReturnsLaws.



  (* TODO: Move this *)
  Lemma exec_correct_weaken_pre :
    forall {MemM Eff ExtraState} `{MEMM : MemMonad ExtraState MemM (itree Eff)}
      {A}
      (pre : MemState -> ExtraState -> Prop)
      (weak_pre : MemState -> ExtraState -> Prop)
      (exec : MemM A)
      (spec : MemPropT MemState A),
      (forall ms st, pre ms st -> weak_pre ms st) ->
      exec_correct weak_pre exec spec ->
      exec_correct pre exec spec.
  Proof.
    intros MemM Eff ExtraState MM MRun MPROV MSID MMS MERR MUB MOOM
           RunERR RunUB RunOOM EQM EQRI MLAWS MEMM A pre
           weak_pre exec spec WEAK EXEC.
    unfold exec_correct in *.
    intros ms st VALID PRE.
    apply WEAK in PRE.
    eauto.
  Qed.

  (* TODO: move this *)
  Lemma exec_correct_bind :
    forall {MemM Eff ExtraState} `{MEMM : MemMonad ExtraState MemM (itree Eff)}
      {A B}
      (pre : MemState -> ExtraState -> Prop)
      (m_exec : MemM A) (k_exec : A -> MemM B)
      (m_spec : MemPropT MemState A) (k_spec : A -> MemPropT MemState B),
      exec_correct pre m_exec m_spec ->
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
          ((@eq1 _ (@MemMonad_eq1_runm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MEMM)) _
                                                                                (MemMonad_run m_exec ms_init st_init)
                                                                                (ret (st_after_m, (ms_after_m, a))))%monad ->
          (* ms_k is a MemState after evaluating m *)
          exec_correct (fun ms_k st_k => pre ms_init st_init /\ m_spec ms_init (ret (ms_k, a))) (k_exec a) (k_spec a)) ->
      exec_correct pre (a <- m_exec;; k_exec a) (a <- m_spec;; k_spec a).
  Proof.
    intros MemM Eff ExtraState MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI MLAWS MEMM A B pre m_exec k_exec m_spec k_spec M_CORRECT K_CORRECT.

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
      specialize (K_CORRECT a ms ms' st st').
      forward K_CORRECT.
      { cbn in M_EXEC_CORRECT.
        red in M_EXEC_CORRECT.
        destruct M_EXEC_CORRECT as [m2 [SUCC EXEC]].
        cbn in *.
        rewrite EXEC, SUCC.
        rewrite bind_ret_l.
        reflexivity.
      }

      forward M_POST.
      { exists a. reflexivity. }

      specialize (K_CORRECT _ _ M_POST).
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

        eapply K_POST.
        eexists; reflexivity.
      }
  Qed.

  Lemma exec_correct_ret :
    forall {MemM Eff ExtraState} `{MemMonad ExtraState MemM (itree Eff)}
      {X} pre (x : X),
      exec_correct pre (ret x) (ret x).
  Proof.
    intros MemM Eff ExtraState MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI MLAWS H X pre x.
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
  Qed.

  Lemma exec_correct_map_monad :
    forall {MemM Eff ExtraState} `{MemMonad ExtraState MemM (itree Eff)}
      {A B}
      xs
      (m_exec : A -> MemM B) (m_spec : A -> MemPropT MemState B),
      (forall a pre, exec_correct pre (m_exec a) (m_spec a)) ->
      forall pre, exec_correct pre (map_monad m_exec xs) (map_monad m_spec xs).
  Proof.
    induction xs;
      intros m_exec m_spec HM pre.

    - unfold map_monad.
      apply exec_correct_ret.
    - rewrite map_monad_unfold.
      rewrite map_monad_unfold.

      eapply exec_correct_bind; eauto.
      intros * RUN.

      eapply exec_correct_bind; eauto.
      intros * RUN2.

      apply exec_correct_ret.
  Qed.

  Lemma exec_correct_map_monad_ :
    forall {MemM Eff ExtraState} `{MemMonad ExtraState MemM (itree Eff)}
      {A B}
      (xs : list A)
      (m_exec : A -> MemM B) (m_spec : A -> MemPropT MemState B),
      (forall a pre, exec_correct pre (m_exec a) (m_spec a)) ->
      forall pre, exec_correct pre (map_monad_ m_exec xs) (map_monad_ m_spec xs).
  Proof.
    intros MemM Eff ExtraState MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI MLAWS H A B xs m_exec m_spec H0 pre.
    apply exec_correct_bind.
    eapply exec_correct_map_monad; auto.
    intros * RUN.
    apply exec_correct_ret.
  Qed.

  Lemma exec_correct_map_monad_In :
    forall {MemM Eff ExtraState} `{MemMonad ExtraState MemM (itree Eff)}
      {A B}
      (xs : list A)
      (m_exec : forall (x : A), In x xs -> MemM B) (m_spec : forall (x : A), In x xs -> MemPropT MemState B),
      (forall a pre (IN : In a xs), exec_correct pre (m_exec a IN) (m_spec a IN)) ->
      forall pre, exec_correct pre (map_monad_In xs m_exec) (map_monad_In xs m_spec).
  Proof.
    induction xs; intros m_exec m_spec HM pre.
    - unfold map_monad_In.
      apply exec_correct_ret.
    - rewrite map_monad_In_unfold.
      rewrite map_monad_In_unfold.

      eapply exec_correct_bind; eauto.
      intros * RUN1.

      eapply exec_correct_bind; eauto.
      intros * RUN2.

      apply exec_correct_ret.
  Qed.

  Lemma exec_correct_raise_oom :
    forall {MemM Eff ExtraState} `{MemMonad ExtraState MemM (itree Eff)}
      {A} (msg : string),
    forall pre, exec_correct pre (raise_oom msg) (raise_oom msg : MemPropT MemState A).
  Proof.
    intros MemM Eff ExtraState MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI MLAWS MemMonad A msg pre.
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
  Qed.

  Lemma exec_correct_raise_error :
    forall {MemM Eff ExtraState} `{MemMonad ExtraState MemM (itree Eff)}
      {A} (msg1 msg2 : string),
    forall pre, exec_correct pre (raise_error msg1) (raise_error msg2 : MemPropT MemState A).
  Proof.
    intros MemM Eff ExtraState MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI MLAWS MemMonad A msg1 msg2 pre.
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
  Qed.

  Lemma exec_correct_raise_ub :
    forall {MemM Eff ExtraState} `{MemMonad ExtraState MemM (itree Eff)}
      {A} (msg1 msg2 : string),
    forall pre, exec_correct pre (raise_ub msg1) (raise_ub msg2 : MemPropT MemState A).
  Proof.
    intros MemM Eff ExtraState MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI MLAWS H A msg1 msg2 pre.

    red.
    intros ms st VALID PRE.

    left.
    exists ms. exists msg2.
    cbn; auto.
  Qed.

  Lemma exec_correct_lift_OOM :
    forall {MemM Eff ExtraState} `{MemMonad ExtraState MemM (itree Eff)}
      {A} (m : OOM A),
    forall pre, exec_correct pre (lift_OOM m) (lift_OOM m).
  Proof.
    intros MemM Eff ExtraState MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI MLAWS MemMonad
           A [NOOM | OOM] pre.
    - apply exec_correct_ret.
    - apply exec_correct_raise_oom.
  Qed.

  Lemma exec_correct_lift_err_RAISE_ERROR :
    forall {MemM Eff ExtraState} `{MemMonad ExtraState MemM (itree Eff)}
      {A} (m : err A),
    forall pre, exec_correct pre (lift_err_RAISE_ERROR m) (lift_err_RAISE_ERROR m).
  Proof.
    intros MemM Eff ExtraState MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI MLAWS MemMonad
           A [ERR | NOERR] pre.
    - apply exec_correct_raise_error.
    - apply exec_correct_ret.
  Qed.

  Lemma exec_correct_lift_ERR_RAISE_ERROR :
    forall {MemM Eff ExtraState} `{MemMonad ExtraState MemM (itree Eff)}
      {A} (m : ERR A),
    forall pre, exec_correct pre (lift_ERR_RAISE_ERROR m) (lift_ERR_RAISE_ERROR m).
  Proof.
    intros MemM Eff ExtraState MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI MLAWS MemMonad
           A [[ERR] | NOERR] pre.
    - apply exec_correct_raise_error.
    - apply exec_correct_ret.
  Qed.

  Lemma exec_correct_get_consecutive_pointers :
    forall {MemM Eff ExtraState} `{MemMonad ExtraState MemM (itree Eff)}
      len ptr,
    forall pre, exec_correct pre (get_consecutive_ptrs ptr len) (get_consecutive_ptrs ptr len).
  Proof.
    intros MemM Eff ExtraState MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI MLAWS MemMonad
           len ptr pre.
    unfold get_consecutive_ptrs.
    eapply exec_correct_bind.
    apply exec_correct_lift_OOM.

    intros * RUN.
    apply exec_correct_lift_err_RAISE_ERROR.
  Qed.

  Lemma exec_correct_fresh_sid :
    forall {MemM Eff ExtraState} `{MemMonad ExtraState MemM (itree Eff)} pre,
      exec_correct pre fresh_sid fresh_sid.
  Proof.
    red.
    intros MemM Eff ExtraState MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM EQM EQRI MLAWS MemMonad pre
           ms st H PRE.
    right.
    eapply MemMonad_run_fresh_sid in H as [st' [sid [EUTT [VALID FRESH]]]].
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
    Context {ExtraState : Type}.
    Context `{MM : MemMonad ExtraState MemM (itree Eff)}.

    Import Monad.

    (* TODO: move this? *)
    Lemma byte_allocated_mem_eq :
      forall ms ms' ptr aid,
        byte_allocated ms ptr aid ->
        MemState_get_memory ms = MemState_get_memory ms' ->
        byte_allocated ms' ptr aid.
    Proof.
      intros ms ms' ptr aid ALLOC EQ.
      unfold byte_allocated, byte_allocated_MemPropT in *.
      cbn in *.
      unfold lift_memory_MemPropT in *.
      cbn in *.
      destruct ALLOC as [sab [ab [[ALLOC PROV] [EQ1 EQ2]]]].
      subst.
      repeat eexists.
      rewrite <- EQ.
      auto.
      intros ms'0 x EQ'; inv EQ'.
      reflexivity.
    Qed.

    (* TODO: move this? *)
    Lemma read_byte_allowed_mem_eq :
      forall ms ms' ptr,
        read_byte_allowed ms ptr ->
        MemState_get_memory ms = MemState_get_memory ms' ->
        read_byte_allowed ms' ptr.
    Proof.
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
    Proof.
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
    Proof.
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
    Proof.
      intros ms ms' ptr byte READ EQ.
      unfold read_byte_prop.
      rewrite <- EQ.
      auto.
    Qed.

    Lemma read_byte_preserved_mem_eq :
      forall ms ms',
        MemState_get_memory ms = MemState_get_memory ms' ->
        read_byte_preserved ms ms'.
    Proof.
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
    Proof.
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
    Proof.
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
    Proof.
      intros ms ms' EQ.
      unfold write_byte_allowed_all_preserved.
      intros ptr aid.
      split; intros ALLOC; eapply byte_allocated_mem_eq; eauto.
    Qed.

    Lemma frame_stack_preserved_mem_eq :
      forall ms ms',
        MemState_get_memory ms = MemState_get_memory ms' ->
        frame_stack_preserved ms ms'.
    Proof.
      intros ms ms' EQ.
      unfold frame_stack_preserved.
      intros fs.
      split; intros FS; [rewrite <- EQ | rewrite EQ]; eauto.
    Qed.

    #[global] Instance Proper_heap_preserved :
      Proper ((fun ms1 ms2 => MemState_get_memory ms1 = MemState_get_memory ms2) ==> (fun ms1 ms2 => MemState_get_memory ms1 = MemState_get_memory ms2) ==> iff) heap_preserved.
    Proof.
      unfold Proper, respectful.
      intros x y H x0 y0 H0.
      unfold heap_preserved.
      rewrite H, H0.
      reflexivity.
    Qed.

    #[global] Instance Reflexive_heap_preserved : Reflexive heap_preserved.
    Proof.
      unfold Reflexive.
      intros x.
      unfold heap_preserved.
      reflexivity.
    Qed.

    Lemma exec_correct_fresh_provenance :
      forall pre, exec_correct pre fresh_provenance fresh_provenance.
    Proof.
      red.
      intros pre ms st H PRE.
      right.
      eapply MemMonad_run_fresh_provenance in H as [ms' [pr [EUTT [VALID [MEM FRESH]]]]].
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
    Context {ExtraState : Type}.
    Context `{MM : MemMonad ExtraState MemM (itree Eff)}.

    (*** Data types *)
    Parameter initial_frame : Frame.
    Parameter initial_heap : Heap.

    (*** Primitives on memory *)
    (** Reads *)
    Parameter read_byte :
      forall `{MemMonad ExtraState MemM (itree Eff)}, addr -> MemM SByte.

    (** Writes *)
    Parameter write_byte :
      forall `{MemMonad ExtraState MemM (itree Eff)}, addr -> SByte -> MemM unit.

    (** Stack allocations *)
    Parameter allocate_bytes_with_pr :
      forall `{MemMonad ExtraState MemM (itree Eff)}, dtyp -> N -> list SByte -> Provenance -> MemM addr.

    (** Frame stacks *)
    Parameter mempush : forall `{MemMonad ExtraState MemM (itree Eff)}, MemM unit.
    Parameter mempop : forall `{MemMonad ExtraState MemM (itree Eff)}, MemM unit.

    (** Heap operations *)
    Parameter malloc_bytes_with_pr :
      forall `{MemMonad ExtraState MemM (itree Eff)}, list SByte -> Provenance -> MemM addr.

    Parameter free :
      forall `{MemMonad ExtraState MemM (itree Eff)}, addr -> MemM unit.

    (*** Correctness *)

    (** Correctness of the main operations on memory *)
    Parameter read_byte_correct :
      forall ptr pre, exec_correct pre (read_byte ptr) (read_byte_spec_MemPropT ptr).

    Parameter write_byte_correct :
      forall ptr byte pre, exec_correct pre (write_byte ptr byte) (write_byte_spec_MemPropT ptr byte).

    Parameter allocate_bytes_with_pr_correct :
      forall dt num_elements init_bytes pr pre,
        exec_correct pre
          (allocate_bytes_with_pr dt num_elements init_bytes pr)
          (allocate_bytes_with_pr_spec_MemPropT dt num_elements init_bytes pr).

    (** Correctness of frame stack operations *)
    Parameter mempush_correct :
      forall pre, exec_correct pre mempush mempush_spec_MemPropT.

    Parameter mempop_correct :
      forall pre, exec_correct pre mempop mempop_spec_MemPropT.

    Parameter malloc_bytes_with_pr_correct :
      forall init_bytes pr pre,
        exec_correct pre (malloc_bytes_with_pr init_bytes pr) (malloc_bytes_with_pr_spec_MemPropT init_bytes pr).

    Parameter free_correct :
      forall ptr pre,
        exec_correct pre (free ptr) (free_spec_MemPropT ptr).

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
          read_byte_prop initial_memory_state ptr byte
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
    Context {ExtraState : Type}.
    Context `{MM : MemMonad ExtraState MemM (itree Eff)}.

    (** Reading uvalues *)
    Definition read_bytes `{MemMonad ExtraState MemM (itree Eff)} (ptr : addr) (len : nat) : MemM (list SByte) :=
      (* TODO: this should maybe be UB and not OOM??? *)
      ptrs <- get_consecutive_ptrs ptr len;;

      (* Actually perform reads *)
      map_monad (fun ptr => read_byte ptr) ptrs.

    Definition read_uvalue `{MemMonad ExtraState MemM (itree Eff)} (dt : dtyp) (ptr : addr) : MemM uvalue :=
      bytes <- read_bytes ptr (N.to_nat (sizeof_dtyp dt));;
      lift_err_RAISE_ERROR (deserialize_sbytes bytes dt).

    (** Writing uvalues *)
    Definition write_bytes `{MemMonad ExtraState MemM (itree Eff)} (ptr : addr) (bytes : list SByte) : MemM unit :=
      (* TODO: Should this be UB instead of OOM? *)
      ptrs <- get_consecutive_ptrs ptr (length bytes);;
      let ptr_bytes := zip ptrs bytes in

      (* Actually perform writes *)
      map_monad_ (fun '(ptr, byte) => write_byte ptr byte) ptr_bytes.

    Definition write_uvalue `{MemMonad ExtraState MemM (itree Eff)} (dt : dtyp) (ptr : addr) (uv : uvalue) : MemM unit :=
      bytes <- serialize_sbytes uv dt;;
      write_bytes ptr bytes.

    (** Allocating dtyps *)
    Definition allocate_bytes `{MemMonad ExtraState MemM (itree Eff)}
      (dt : dtyp) (num_elements : N) (init_bytes : list SByte)
      : MemM addr
      := pr <- fresh_provenance;;
         allocate_bytes_with_pr dt num_elements init_bytes pr.

    (* Need to make sure MemPropT has provenance and sids to generate the bytes. *)
    Definition allocate_dtyp `{MemMonad ExtraState MemM (itree Eff)}
      (dt : dtyp) (num_elements : N)
      : MemM addr
      := sid <- fresh_sid;;
         element_bytes <- repeatMN num_elements (lift_OOM (generate_undef_bytes dt sid));;
         let bytes := concat element_bytes in
         allocate_bytes dt num_elements bytes.

    (** Malloc *)
    Definition malloc_bytes `{MemMonad ExtraState MemM (itree Eff)} (init_bytes : list SByte) : MemM addr :=
      pr <- fresh_provenance;;
      malloc_bytes_with_pr init_bytes pr.

    (** Handle memcpy *)
    Definition memcpy `{MemMonad ExtraState MemM (itree Eff)} (src dst : addr) (len : Z) (align : N) (volatile : bool) : MemM unit :=
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

    Definition handle_memory `{MemMonad ExtraState MemM (itree Eff)} : MemoryE ~> MemM
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

    Definition handle_memcpy `{MemMonad ExtraState MemM (itree Eff)} (args : list dvalue) : MemM unit :=
      match args with
      | DVALUE_Addr dst ::
                    DVALUE_Addr src ::
                    DVALUE_I32 len ::
                    DVALUE_I32 align :: (* alignment ignored *)
                    DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          memcpy src dst (unsigned len) (Z.to_N (unsigned align)) (equ volatile one)
      | DVALUE_Addr dst ::
                    DVALUE_Addr src ::
                    DVALUE_I64 len ::
                    DVALUE_I64 align :: (* alignment ignored *)
                    DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          memcpy src dst (unsigned len) (Z.to_N (unsigned align)) (equ volatile one)
      | DVALUE_Addr dst ::
                    DVALUE_Addr src ::
                    DVALUE_IPTR len ::
                    DVALUE_IPTR align :: (* alignment ignored *)
                    DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          memcpy src dst (IP.to_Z len) (Z.to_N (IP.to_Z align)) (equ volatile one)
      | _ => raise_error "Unsupported arguments to memcpy."
      end.

    Definition handle_malloc `{MemMonad ExtraState MemM (itree Eff)} (args : list dvalue) : MemM addr :=
      match args with
      | [DVALUE_I1 sz]
      | [DVALUE_I8 sz]
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

    Definition handle_free `{MemMonad ExtraState MemM (itree Eff)} (args : list dvalue) : MemM unit :=
      match args with
      | [DVALUE_Addr ptr] =>
          free ptr
      | _ => raise_error "Free: invalid arguments."
      end.

    Definition handle_intrinsic `{MemMonad ExtraState MemM (itree Eff)} : IntrinsicE ~> MemM
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
    Context {ExtraState : Type}.
    Context `{MM : MemMonad ExtraState MemM (itree Eff)}.

    Import Monad.

    Lemma exec_correct_re_sid_ubytes_helper :
      forall bytes pre nm,
        exec_correct pre
                     (re_sid_ubytes_helper bytes nm)
                     (re_sid_ubytes_helper bytes nm).
    Proof.
      intros bytes.
      induction bytes using length_strong_ind; intros pre nm.
      - apply exec_correct_ret.
      - repeat rewrite re_sid_ubytes_helper_equation.
        break_match_goal; auto with EXEC_CORRECT.
        break_match_goal; auto with EXEC_CORRECT.
        break_match_goal; auto with EXEC_CORRECT.
        break_match_goal; auto with EXEC_CORRECT.
        apply exec_correct_bind; auto with EXEC_CORRECT.
        intros a0.
        intros ms_init ms_after_m st_init st_after_m RUN_FRESH_SID.
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
                     (trywith_error msg2 ma).
    Proof.
      intros A msg1 msg2 [a |] pre;
        unfold trywith_error;
        auto with EXEC_CORRECT.
    Qed.

    Hint Resolve exec_correct_trywith_error : EXEC_CORRECT.

    Lemma exec_correct_re_sid_ubytes :
      forall bytes pre,
        exec_correct pre (re_sid_ubytes bytes) (re_sid_ubytes bytes).
    Proof.
      intros bytes pre.
      apply exec_correct_bind; auto with EXEC_CORRECT.
    Qed.

    Hint Resolve exec_correct_re_sid_ubytes : EXEC_CORRECT.

    Lemma dtyp_measure_strong_ind:
      forall (P : dtyp -> Prop)
        (BASE: forall dt, dtyp_measure dt = 1 -> P dt)
        (IH: forall (n : nat) (dt: dtyp), (forall (dt : dtyp), dtyp_measure dt <= n -> P dt) -> dtyp_measure dt = S n -> P dt),
      forall dt, P dt.
    Proof.
      intros P BASE IH.
      assert (forall n dt, dtyp_measure dt <= n -> P dt) as IHDT.
      { induction n using nat_strong_ind; intros dt SIZE.
        - destruct dt; cbn in SIZE; lia.
        - assert (dtyp_measure dt <= n \/ dtyp_measure dt = S n) as [LEQ | EQ] by lia;
          eauto.
      }

      intros dt.
      eapply IHDT.
      reflexivity.
    Qed.

    Lemma exec_correct_serialize_sbytes_undef :
      forall dt t pre,
        exec_correct pre (serialize_sbytes (UVALUE_Undef t) dt) (serialize_sbytes (UVALUE_Undef t) dt).
    Proof.
      induction dt using dtyp_measure_strong_ind; intros t pre;
        do 2 rewrite serialize_sbytes_equation;
        auto with EXEC_CORRECT.

      { (* Size 1 *)
        destruct dt; inversion H; auto with EXEC_CORRECT.
      }

      { (* Larger sizes *)
        revert t pre.
        induction dt; intros t pre; try apply exec_correct_bind; auto with EXEC_CORRECT.

        { (* Arrays *)
          apply exec_correct_map_monad_In.
          intros a pre0 IN.
          apply In_repeatN in IN; subst.
          eapply H.
          cbn in H0.
          lia.
        }

        { (* Structs *)
          break_match_goal; auto with EXEC_CORRECT.
          apply exec_correct_bind; auto with EXEC_CORRECT.
          eapply H; cbn in *; auto; lia.

          intros a ms_init ms_after_m st_init st_after_m RUN.

          apply exec_correct_bind; auto with EXEC_CORRECT.

          eapply H; cbn in *; auto.
          unfold list_sum.
          assert (dtyp_measure d > 0) by (destruct d; cbn; lia).
          lia.
        }

        { (* Packed Structs *)
          break_match_goal; auto with EXEC_CORRECT.
          apply exec_correct_bind; auto with EXEC_CORRECT.
          eapply H; cbn in *; auto; lia.

          intros a ms_init ms_after_m st_init st_after_m RUN.

          apply exec_correct_bind; auto with EXEC_CORRECT.

          eapply H; cbn in *; auto.
          unfold list_sum.
          assert (dtyp_measure d > 0) by (destruct d; cbn; lia).
          lia.
        }

        { (* Vectors *)
          apply exec_correct_map_monad_In.
          intros a pre0 IN.
          apply In_repeatN in IN; subst.
          eapply H.
          cbn in H0.
          lia.
        }

      }
    Qed.

    Hint Resolve exec_correct_serialize_sbytes_undef : EXEC_CORRECT.

    Lemma exec_correct_serialize_sbytes_poison :
      forall dt t pre,
        exec_correct pre (serialize_sbytes (UVALUE_Poison t) dt) (serialize_sbytes (UVALUE_Poison t) dt).
    Proof.
      induction dt using dtyp_measure_strong_ind; intros t pre;
        do 2 rewrite serialize_sbytes_equation;
        auto with EXEC_CORRECT.

      { (* Size 1 *)
        destruct dt; inversion H; auto with EXEC_CORRECT.
      }

      { (* Larger sizes *)
        revert t pre.
        induction dt; intros t pre; try apply exec_correct_bind; auto with EXEC_CORRECT.

        { (* Arrays *)
          apply exec_correct_map_monad_In.
          intros a pre0 IN.
          apply In_repeatN in IN; subst.
          eapply H.
          cbn in H0.
          lia.
        }

        { (* Structs *)
          break_match_goal; auto with EXEC_CORRECT.
          apply exec_correct_bind; auto with EXEC_CORRECT.
          eapply H; cbn in *; auto; lia.

          intros a ms_init ms_after_m st_init st_after_m RUN.

          apply exec_correct_bind; auto with EXEC_CORRECT.

          eapply H; cbn in *; auto.
          unfold list_sum.
          assert (dtyp_measure d > 0) by (destruct d; cbn; lia).
          lia.
        }

        { (* Packed Structs *)
          break_match_goal; auto with EXEC_CORRECT.
          apply exec_correct_bind; auto with EXEC_CORRECT.
          eapply H; cbn in *; auto; lia.

          intros a ms_init ms_after_m st_init st_after_m RUN.

          apply exec_correct_bind; auto with EXEC_CORRECT.

          eapply H; cbn in *; auto.
          unfold list_sum.
          assert (dtyp_measure d > 0) by (destruct d; cbn; lia).
          lia.
        }

        { (* Vectors *)
          apply exec_correct_map_monad_In.
          intros a pre0 IN.
          apply In_repeatN in IN; subst.
          eapply H.
          cbn in H0.
          lia.
        }

      }
    Qed.

    Hint Resolve exec_correct_serialize_sbytes_poison : EXEC_CORRECT.

    Lemma exec_correct_serialize_sbytes :
      forall uv dt pre,
        exec_correct pre (serialize_sbytes uv dt) (serialize_sbytes uv dt).
    Proof.
      induction uv using uvalue_ind''; intros dt' pre;
        do 2 rewrite serialize_sbytes_equation;
        auto with EXEC_CORRECT.


      all: try solve
             [break_match; auto with EXEC_CORRECT;
              [
                (* Arrays *)
                apply exec_correct_bind; auto with EXEC_CORRECT;
                apply exec_correct_map_monad_In;
                intros a pre0 IN;
                apply In_repeatN in IN; subst;
                auto with EXEC_CORRECT
              |
                break_match_goal; auto with EXEC_CORRECT
              |
                break_match_goal; auto with EXEC_CORRECT
              |
                apply exec_correct_bind; auto with EXEC_CORRECT;
                apply exec_correct_map_monad_In;
                intros a pre0 IN;
                apply In_repeatN in IN; subst;
                auto with EXEC_CORRECT
              ]
             |
               break_match_goal; auto with EXEC_CORRECT;
               break_match_goal; auto with EXEC_CORRECT
             ].
    Qed.

    Lemma read_bytes_correct :
      forall len ptr pre,
        exec_correct pre (read_bytes ptr len) (read_bytes_spec ptr len).
    Proof.
      unfold read_bytes.
      unfold read_bytes_spec.
      intros len ptr pre.
      eapply exec_correct_bind.
      apply exec_correct_get_consecutive_pointers.

      intros * RUN.
      eapply exec_correct_map_monad.
      intros ptr'.
      apply read_byte_correct.
    Qed.

    Lemma read_uvalue_correct :
      forall dt ptr pre,
        exec_correct pre (read_uvalue dt ptr) (read_uvalue_spec dt ptr).
    Proof.
      intros dt ptr pre.
      eapply exec_correct_bind.
      apply read_bytes_correct.
      intros * RUN.
      apply exec_correct_lift_err_RAISE_ERROR.
    Qed.

    Lemma write_bytes_correct :
      forall ptr bytes pre,
        exec_correct pre (write_bytes ptr bytes) (write_bytes_spec ptr bytes).
    Proof.
      intros ptr bytes pre.
      apply exec_correct_bind.
      apply exec_correct_get_consecutive_pointers.
      intros * RUN.
      apply exec_correct_map_monad_.
      intros [a' b] PRE.
      apply write_byte_correct.
    Qed.

    Lemma write_uvalue_correct :
      forall dt ptr uv pre,
        exec_correct pre (write_uvalue dt ptr uv) (write_uvalue_spec dt ptr uv).
    Proof.
      intros dt ptr uv pre.
      apply exec_correct_bind.
      apply exec_correct_serialize_sbytes.
      intros * RUN.
      apply write_bytes_correct.
    Qed.

    Lemma allocate_bytes_correct :
      forall dt num_elements bytes pre,
        exec_correct pre
          (allocate_bytes dt num_elements bytes)
          (allocate_bytes_spec_MemPropT dt num_elements bytes).
    Proof.
      intros dt num_elements pr pre.
      apply exec_correct_bind.
      apply exec_correct_fresh_provenance.
      intros a ms_init ms_after_m st_init st_after_m RUN0.
      apply allocate_bytes_with_pr_correct.
    Qed.

    Hint Resolve allocate_bytes_correct : EXEC_CORRECT.

    Lemma exec_correct_repeatMN :
      forall {A} (n : N) (pre : MemState -> ExtraState -> Prop) (m_exec : MemM A) (m_spec : MemPropT MemState A),
        (forall pre, exec_correct pre m_exec m_spec) ->
        exec_correct pre
          (repeatMN n m_exec)
          (repeatMN n m_spec).
    Proof.
      intros A n.
      induction n using N.peano_rect; intros pre m_exec m_spec EXEC.
      - apply exec_correct_ret.
      - do 2 rewrite repeatMN_succ.
        apply exec_correct_bind; auto.

        intros a ms_init ms_after_m st_init st_after_m RUN.
        apply exec_correct_bind; auto.
        intros a0 ms_init0 ms_after_m0 st_init0 st_after_m0 H0.
        apply exec_correct_ret.
    Qed.

    Lemma allocate_dtyp_correct :
      forall dt num_elements pre,
        exec_correct pre (allocate_dtyp dt num_elements) (allocate_dtyp_spec dt num_elements).
    Proof.
      intros dt num_elements pre.
      apply exec_correct_bind.
      apply exec_correct_fresh_sid.
      intros * RUN1.
      apply exec_correct_bind.
      { eapply exec_correct_repeatMN.
        intros pre0.
        apply exec_correct_lift_OOM.
      }
      intros * RUN2.
      apply allocate_bytes_correct.
    Qed.

    Lemma memcpy_correct :
      forall src dst len align volatile pre,
        exec_correct pre (memcpy src dst len align volatile) (memcpy_spec src dst len align volatile).
    Proof.
      intros src dst len align volatile pre.
      unfold memcpy, memcpy_spec.
      break_match; [apply exec_correct_raise_ub|].
      unfold MME.OVER_H.no_overlap, MME.OVER.overlaps.
      unfold OVER_H.no_overlap, OVER.overlaps.
      break_match; [|apply exec_correct_raise_ub].

      apply exec_correct_bind.
      apply read_bytes_correct.
      intros * RUN.
      apply write_bytes_correct.
    Qed.

    Lemma handle_memory_correct :
      forall T (m : MemoryE T) pre,
        exec_correct pre (handle_memory T m) (handle_memory_prop T m).
    Proof.
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
        apply exec_correct_bind.
        apply allocate_dtyp_correct.
        intros * RUN.
        apply exec_correct_ret.
      - (* Load *)
        unfold handle_memory, handle_memory_prop.
        destruct a; try apply exec_correct_raise_ub.
        apply read_uvalue_correct.
      - (* Store *)
        unfold handle_memory, handle_memory_prop.
        destruct a; try apply exec_correct_raise_ub.
        apply write_uvalue_correct.
    Qed.

    Lemma handle_memcpy_correct:
      forall args pre,
        exec_correct pre (handle_memcpy args) (handle_memcpy_prop args).
    Proof.
      intros args.
      unfold handle_memcpy, handle_memcpy_prop.
      repeat (break_match; try apply exec_correct_raise_error).
      all: apply memcpy_correct.
    Qed.

    Lemma malloc_bytes_correct :
      forall bytes pre,
        exec_correct pre (malloc_bytes bytes) (malloc_bytes_spec_MemPropT bytes).
    Proof.
      intros bytes pre.
      apply exec_correct_bind.
      apply exec_correct_fresh_provenance.
      intros a ms_init ms_after_m st_init st_after_m RUN0.
      apply malloc_bytes_with_pr_correct.
    Qed.

    Hint Resolve malloc_bytes_correct : EXEC_CORRECT.

    Lemma handle_malloc_correct:
      forall args pre,
        exec_correct pre (handle_malloc args) (handle_malloc_prop args).
    Proof.
      intros args.
      unfold handle_malloc, handle_malloc_prop.
      repeat (break_match; try apply exec_correct_raise_error).
      all: eauto with EXEC_CORRECT.
    Qed.

    Lemma handle_free_correct:
      forall args pre,
        exec_correct pre (handle_free args) (handle_free_prop args).
    Proof.
      intros args pre.
      unfold handle_free, handle_free_prop.
      repeat (break_match; try apply exec_correct_raise_error).
      all: apply free_correct.
    Qed.

    Lemma handle_intrinsic_correct:
      forall T (e : IntrinsicE T) pre,
        exec_correct pre (handle_intrinsic T e) (handle_intrinsic_prop T e).
    Proof.
      intros T e pre.
      unfold handle_intrinsic, handle_intrinsic_prop.
      break_match.
      break_match.
      { (* Memcpy *)
        apply exec_correct_bind.
        apply handle_memcpy_correct.
        intros * RUN.
        apply exec_correct_ret.
      }

      break_match.
      { (* Malloc *)
        apply exec_correct_bind.
        apply handle_malloc_correct.
        eauto with EXEC_CORRECT.
      }

      break_match.
      { (* Free *)
        apply exec_correct_bind.
        apply handle_free_correct.
        eauto with EXEC_CORRECT.
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
      dt num_elements bytes
      (BYTES_SIZE : (sizeof_dtyp dt * num_elements)%N = N.of_nat (length bytes))
      (NON_VOID : dt <> DTYPE_Void)
      (ub_msg : string),
      ~ allocate_bytes_spec_MemPropT dt num_elements bytes ms_init (raise_ub ub_msg).
  Proof.
    intros ms_init dt num_elements bytes BYTES_SIZE NON_VOID ub_msg CONTRA.

    unfold allocate_bytes_spec_MemPropT in CONTRA.
    cbn in CONTRA.
    destruct CONTRA as [[] | [ms' [pr' [FRESH [[] | CONTRA]]]]].
    destruct CONTRA as [ms'' [[ptr ptrs] [[EQ BLOCKFREE] CONTRA]]]; subst.
    destruct CONTRA as [[CONTRA | CONTRA] | CONTRA]; try contradiction.
    destruct CONTRA as [ms''' [[ptr' ptrs'] [POST CONTRA]]]; contradiction.
  Qed.

  Lemma allocate_bytes_spec_MemPropT_no_err :
    forall (ms_init : MemState)
      dt num_elements bytes
      (BYTES_SIZE : (sizeof_dtyp dt * num_elements)%N = N.of_nat (length bytes))
      (NON_VOID : dt <> DTYPE_Void)
      (err_msg : string),
      ~ allocate_bytes_spec_MemPropT dt num_elements bytes ms_init (raise_error err_msg).
  Proof.
    intros ms_init dt num_elements bytes BYTES_SIZE NON_VOID err_msg CONTRA.

    unfold allocate_bytes_spec_MemPropT in CONTRA.
    cbn in CONTRA.
    destruct CONTRA as [[] | [ms' [pr' [FRESH [[] | CONTRA]]]]].
    destruct CONTRA as [ms'' [[ptr ptrs] [[EQ BLOCKFREE] CONTRA]]]; subst.
    destruct CONTRA as [[] | [ms''' [[ptr' ptrs'] [POST []]]]].
  Qed.

  Lemma allocate_bytes_spec_MemPropT_inv :
    forall (ms_init : MemState)
      dt num_elements bytes
      (BYTES_SIZE : (sizeof_dtyp dt * num_elements)%N = N.of_nat (length bytes))
      (NON_VOID : dt <> DTYPE_Void)
      (res : err_ub_oom (MemState * LP.ADDR.addr))
      (ALLOC : allocate_bytes_spec_MemPropT dt num_elements bytes ms_init res),
      (exists ms_final ptr,
          res = ret (ms_final, ptr)) \/
        (exists oom_msg,
            res = raise_oom oom_msg).
  Proof.
    intros ms_init dt num_elements bytes BYTES_SIZE NON_VOID res ALLOC.
    unfold allocate_bytes_spec_MemPropT in ALLOC.
    destruct res as [[[[[[[oom_res] | [[ub_res] | [[err_res] | res']]]]]]]] eqn:Hres;
      cbn in *; try contradiction.
    - (* OOM *)
      right. eexists; reflexivity.
    - (* UB *)
      destruct ALLOC as [[] | [ms' [pr' [FRESH [[] | ALLOC]]]]].
      destruct ALLOC as [ms'' [[ptr ptrs] [[MEQ BLOCKFREE] [[UB | UB] | ALLOC]]]];
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
      destruct ALLOC as [[] | [ms' [sid [FRESH [GEN | ALLOC]]]]].
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
        destruct ALLOC as [[MEQ BLOCK_FREE] [[UB | UB] | [_ [_ [_ []]]]]];
          [contradiction | lia].
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
          destruct ALLOC as [[MEQ BLOCK_FREE] [[UB | UB] | [_ [_ [_ []]]]]];
            [contradiction | lia].
          Opaque allocate_bytes_spec_MemPropT.
        + rewrite repeatMN_succ in GEN.
          cbn in GEN.
          destruct GEN as [ms''' [a [[] _]]].
      }
    - (* Error *)
      destruct ALLOC as [[] | [ms' [sid [FRESH [GEN | ALLOC]]]]].
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
      Require Import FunctionalExtensionality.
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
      eexists.
      eapply handle_gep_addr_ix'.
      reflexivity.
    }

    destruct HMAPM as (res & HMAPM).
    exists res.
    rewrite bind_ret_l.
    rewrite HMAPM.
    cbn.
    reflexivity.
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
    forall (ms_init : MemState) dt num_elements bytes pr
      (BYTES_SIZE : (sizeof_dtyp dt * num_elements)%N = N.of_nat (length bytes))
      (NON_VOID : dt <> DTYPE_Void),
    exists ms_final ptr ptrs,
      (ret (ptr, ptrs) {{ms_init}} ∈ {{ms_init}} find_free_block (length bytes) pr) /\
      allocate_bytes_post_conditions ms_init dt num_elements bytes pr ms_final ptr ptrs.

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
      dt num_elements bytes pr
      (BYTES_SIZE : (sizeof_dtyp dt * num_elements)%N = N.of_nat (length bytes))
      (NON_VOID : dt <> DTYPE_Void),
    exists ms_final ptr,
      ret ptr {{ms_init}} ∈ {{ms_final}} allocate_bytes_with_pr_spec_MemPropT dt num_elements bytes pr.
  Proof.
    intros ms_init dt num_elements bytes pr BYTES_SIZE NON_VOID.
    unfold allocate_bytes_spec_MemPropT.

    pose proof allocate_bytes_post_conditions_can_always_be_satisfied ms_init dt num_elements bytes pr BYTES_SIZE NON_VOID as (ms_final & ptr & ptrs & (_ & BLOCK_FREE) & ALLOC).

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
      dt num_elements bytes
      (pr : Provenance)
      (FRESH_PR : (fresh_provenance ms_init (ret (ms_fresh_pr, pr))))
      (BYTES_SIZE : (sizeof_dtyp dt * num_elements)%N = N.of_nat (length bytes))
      (NON_VOID : dt <> DTYPE_Void),
    exists ms_final ptr,
      ret ptr {{ms_init}} ∈ {{ms_final}} allocate_bytes_spec_MemPropT dt num_elements bytes.
  Proof.
    intros ms_init ms_fresh_pr dt num_elements bytes pr FRESH_PR BYTES_SIZE NON_VOID.
    unfold allocate_bytes_spec_MemPropT.

    pose proof allocate_bytes_with_pr_spec_MemPropT_can_always_succeed ms_fresh_pr dt num_elements bytes pr BYTES_SIZE NON_VOID as (ms_final & ptr & ALLOC).

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

    break_match; break_match; auto.
    inv NOOM.
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
      cbn; rewrite Heqo; cbn.
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
         ms_fresh_sid ms_fresh_pr dt num_elements (concat bytes) pr FRESH_PR SIZE NON_VOID
      as (ms_final & ptr & ALLOC_SUCCESS).

    exists ms_final, ptr.
    exists ms_fresh_sid, sid; split; auto.

    rewrite UNDEF_BYTES.
    Opaque allocate_bytes_spec_MemPropT.
    cbn.
    Transparent allocate_bytes_spec_MemPropT.

    exists ms_fresh_sid, bytes.
    tauto.
  Qed.
End MemoryModelInfiniteSpecHelpers.
