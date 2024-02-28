From Vellvm.Syntax Require Import
     DataLayout
     DynamicTypes.

From Vellvm.Semantics Require Import
     MemoryAddress
     MemoryParams
     LLVMParams
     LLVMEvents
     Lang
     Memory.FiniteProvenance
     Memory.Sizeof
     Memory.MemBytes
     Memory.DvalueBytes
     Memory.ErrSID
     GepM
     VellvmIntegers.

From Vellvm Require Import
     Numeric.Coqlib
     Numeric.Integers.

From Vellvm.Handlers Require Import
     MemPropT
     MemoryInterpreters.

From Vellvm.Utils Require Import
     Util
     Error
     PropT
     Tactics
     IntMaps
     Monads
     MonadEq1Laws
     MonadExcLaws
     MapMonadExtra
     Raise.

From ITree Require Import
     ITree
     Eq.Eqit.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Data.Monads.StateMonad.

From Coq Require Import
     ZArith
     Strings.String
     List
     Lia
     Relations
     RelationClasses.

Require Import Paco.paco.

Import ListNotations.
Import ListUtil.
Import Utils.Monads.

Import MonadNotation.
Open Scope monad_scope.

From Vellvm.Handlers Require Import
     MemoryModel.

From Vellvm.Handlers.MemoryModules Require Import
  FiniteAddresses
  InfiniteAddresses
  FiniteIntptr
  FiniteSizeof
  FiniteSpecPrimitives
  FiniteExecPrimitives
  Within.

#[local] Open Scope Z_scope.

(** * Memory Model

    This file implements VIR's memory model as an handler for the [MemoryE] family of events.
    The model is inspired by CompCert's memory model, but differs in that it maintains two
    representation of the memory, a logical one and a low-level one.
    Pointers (type signature [MemoryAddress.ADDRESS]) are implemented as a pair containing
    an address and an offset.
*)

(* Specifying the currently supported dynamic types.
       This is mostly to rule out:

       - arbitrary bitwidth integers
       - half
       - x86_fp80
       - fp128
       - ppc_fp128
       - metadata
       - x86_mmx
       - opaque
 *)
Inductive is_supported : dtyp -> Prop :=
| is_supported_DTYPE_I1 : is_supported (DTYPE_I 1)
| is_supported_DTYPE_I8 : is_supported (DTYPE_I 8)
| is_supported_DTYPE_I32 : is_supported (DTYPE_I 32)
| is_supported_DTYPE_I64 : is_supported (DTYPE_I 64)
| is_supported_DTYPE_Pointer : is_supported (DTYPE_Pointer)
| is_supported_DTYPE_Void : is_supported (DTYPE_Void)
| is_supported_DTYPE_Float : is_supported (DTYPE_Float)
| is_supported_DTYPE_Double : is_supported (DTYPE_Double)
| is_supported_DTYPE_Array : forall sz τ, is_supported τ -> is_supported (DTYPE_Array sz τ)
| is_supported_DTYPE_Struct : forall fields, Forall is_supported fields -> is_supported (DTYPE_Struct fields)
| is_supported_DTYPE_Packed_struct : forall fields, Forall is_supported fields -> is_supported (DTYPE_Packed_struct fields)
(* TODO: unclear if is_supported τ is good enough here. Might need to make sure it's a sized type *)
| is_supported_DTYPE_Vector : forall sz τ, is_supported τ -> vector_dtyp τ -> is_supported (DTYPE_Vector sz τ)
.

Module FinAddr := FiniteAddresses.FinAddr.
Module InfAddr := InfiniteAddresses.InfAddr.
Module IP64Bit := FiniteIntptr.IP64Bit.
Module BigIP := FiniteIntptr.BigIP.
Module FinSizeof := FiniteSizeof.FinSizeof.

Module MakeFiniteMemoryModelSpec (LP : LLVMParams) (MP : MemoryParams LP).
  Module FMSP := FiniteMemoryModelSpecPrimitives LP MP.
  Module FMS := MakeMemoryModelSpec LP MP FMSP.

  Export FMSP FMS.
End MakeFiniteMemoryModelSpec.

Module MakeFiniteMemoryModelExec (LP : LLVMParams) (MP : MemoryParams LP).
  Module FMEP := FiniteMemoryModelExecPrimitives LP MP.
  Module FME := MakeMemoryModelExec LP MP FMEP.
End MakeFiniteMemoryModelExec.

Module MakeFiniteMemory (LP : LLVMParams) <: Memory LP.
  Import LP.

  Module GEP := GepM.Make ADDR IP SIZEOF Events PTOI PROV ITOP.
  Module Byte := FinByte ADDR IP SIZEOF Events.
  Module DVALUE_BYTE := DvalueBytes.Make LP.

  Module MP := MemoryParams.Make LP GEP Byte DVALUE_BYTE.

  Module MMEP := FiniteMemoryModelExecPrimitives LP MP.
  Module MEM_MODEL := MakeMemoryModelExec LP MP MMEP.
  Module MEM_SPEC_INTERP := MakeMemorySpecInterpreter LP MP MMEP.MMSP MMEP.MemSpec MMEP.MemExecM.
  Module MEM_EXEC_INTERP := MakeMemoryExecInterpreter LP MP MMEP MEM_MODEL MEM_SPEC_INTERP.

  (* Concretization *)
  Module ByteM := MemBytes.Byte ADDR IP SIZEOF LP.Events MP.BYTE_IMPL.
  Module CP := ConcretizationParams.Make LP MP ByteM.

  Export GEP Byte MP MEM_MODEL CP.
End MakeFiniteMemory.

Module LLVMParamsBigIntptr := LLVMParams.MakeBig InfAddr BigIP FinSizeof InfPTOI InfPROV InfITOP BigIP_BIG InfITOP_BIG.
Module LLVMParams64BitIntptr := LLVMParams.Make FinAddr IP64Bit FinSizeof FinPTOI FinPROV FinITOP.

Module MemoryBigIntptr := MakeFiniteMemory LLVMParamsBigIntptr.
Module Memory64BitIntptr := MakeFiniteMemory LLVMParams64BitIntptr.

From Coq Require Import Program.Equality.

Tactic Notation "raise_abs:" hyp(H) :=
  unfold raise_oom, raise_ub, raise_error in H;
  cbn in H; unfold raiseOOM, raiseUB, LLVMEvents.raise in H;
  repeat rewrite bind_trigger in H;
  repeat red in H; unfold subevent in H;
  punfold H; inversion H; subst;
  try match goal with
  | [ H : existT _ _ _ = existT _ _ _ |- _] => dependent destruction H
  end; try inv H.

Module MemoryBigIntptrInfiniteSpec <: MemoryModelInfiniteSpec LLVMParamsBigIntptr MemoryBigIntptr.MP MemoryBigIntptr.MMEP.MMSP MemoryBigIntptr.MMEP.MemSpec.
  (* Intptrs are "big" *)
  Module LP := LLVMParamsBigIntptr.
  Module MP := MemoryBigIntptr.MP.

  Module MMSP := MemoryBigIntptr.MMEP.MMSP.
  Module MMS := MemoryBigIntptr.MMEP.MemSpec.
  Module MME := MemoryBigIntptr.MEM_MODEL.

  Import LP.Events.
  Import LP.ITOP.
  Import LP.PTOI.
  Import LP.IP_BIG.
  Import LP.I2P_BIG.
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

  Module MSIH := MemStateInfiniteHelpers LP MP MMSP MMS.
  Import MSIH.

  Import MemoryBigIntptr.
  Import MMEP.
  Import MP.BYTE_IMPL.
  Import MemExecM.

  Module MemTheory  := MemoryModelTheory LP MP MMEP MME.
  Import MemTheory.

  Module SpecInterp := MakeMemorySpecInterpreter LP MP MMSP MMS MemExecM.
  Module ExecInterp := MakeMemoryExecInterpreter LP MP MMEP MME SpecInterp.
  Import SpecInterp.
  Import ExecInterp.

  Context {E : Type -> Type}.
  Notation Eff := (E +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE).

  Import Eq.
  Import MMSP.

  (* TODO: Move out of infinite stuff *)
  Lemma find_free_block_never_ub :
    forall sz prov msg,
      raise_ub msg ∉ find_free_block sz prov.
  Proof using.
    intros sz prov msg FREE.
    destruct FREE as [ms [ms' FREE]].
    cbn in FREE; auto.
  Qed.

  (* TODO: Move out of infinite stuff *)
  Lemma find_free_block_never_err :
    forall sz prov msg,
      raise_error msg ∉ find_free_block sz prov.
  Proof using.
    intros sz prov msg FREE.
    destruct FREE as [ms [ms' FREE]].
    cbn in FREE.
    auto.
  Qed.

  Import MemSpec.MemHelpers.
  Import LLVMParamsBigIntptr.
  Import PROV.

  (* TODO: Move this? *)
  Definition list_maxN := fun l : list N => fold_right N.max 0%N l.
  Definition sbyte_sid_succeeds (s : SByte) : StoreId.store_id.
    remember (ByteM.sbyte_sid s).
    pose proof Byte.sbyte_to_extractbyte_inv s.
    destruct H as (?&?&?&?&?).
    unfold ByteM.sbyte_sid in *.
    rewrite e in Heqs0.
    apply x2.
  Defined.

  (* TODO: Move this? *)
  Definition largest_sbyte_sid (bytes : list SByte) : StoreId.store_id :=
    list_maxN (map sbyte_sid_succeeds bytes).

  Definition find_largest_sid_in_memory (m : memory) : StoreId.store_id
    := largest_sbyte_sid (map (fun '(_, (b, _)) => b) (IM.elements m)).

  Lemma largest_sbyte_sid_le :
    forall bytes,
      Forall (fun b : SByte => exists s : StoreId.store_id, MemByte.sbyte_sid b = inr s /\ (s <= largest_sbyte_sid bytes)%N) bytes.
  Proof.
    induction bytes.
    - cbn.
      constructor.
    - constructor.
      + cbn.
        pose proof Byte.sbyte_to_extractbyte_inv a as (?&?&?&?&?).
        unfold MemByte.sbyte_sid.
        rewrite e.
        exists x2.
        split; eauto.
        unfold sbyte_sid_succeeds.
        break_match.
        clear Heqs.
        destruct s as (?&?&?&?).
        rewrite e in e0.
        inv e0.
        lia.
      + eapply Forall_forall.
        intros x H.
        eapply Forall_forall in IHbytes; eauto.
        destruct IHbytes as (?&?&?).
        exists x0.
        split; eauto.
        unfold largest_sbyte_sid, list_maxN in *.
        cbn.
        lia.
  Qed.

  Lemma MemMonad_valid_state_exists :
    forall ms,
    exists st, MemMonad_valid_state ms st.
  Proof.
    intros ms.
    destruct ms as [[mem fs heap] pr'] eqn:Hms.
    unfold MemMonad_valid_state.
    destruct ms.
    unfold MemSpec.used_store_id_prop.
    unfold MemSpec.read_byte_prop.
    unfold read_byte_prop_memory.
    cbn.
    exists (N.succ (find_largest_sid_in_memory mem)).
    intros sid' (?&?&?&?).
    pose proof Byte.sbyte_to_extractbyte_inv x0 as (?&?&?&?&?).
    unfold MemByte.sbyte_sid in *.
    rewrite e in H0.
    inv H0.
    break_match_hyp; try contradiction.
    break_match_hyp; try contradiction.

    Transparent read_byte_raw.
    unfold read_byte_raw in *.
    Opaque read_byte_raw.

    rewrite IP.F.elements_o in Heqo.
    unfold find_largest_sid_in_memory.
    remember (IM.elements (elt:=mem_byte) mem) as l.

    pose proof largest_sbyte_sid_le (map (fun '(_, (b, _)) => b) l).
    clear Heql.
    induction l.
    - cbn in *; inv Heqo.
    - cbn in *.
      inv H0.
      destruct a, m0.
      break_match_hyp_inv.
      + cbn in *.
        destruct H3 as (?&?&?).
        unfold MemByte.sbyte_sid in H.
        rewrite e in H; inv H.
        lia.
      + destruct H3 as (?&?&?).
        unfold MemByte.sbyte_sid in H.
        rewrite Forall_forall in H4.
        specialize (H4 (fst m)).
        forward H4.
        { clear - H0.
          induction l.
          - inv H0.
          - cbn in *.
            destruct a, m0.
            break_match_hyp_inv; cbn; auto.
        }
        destruct H4 as (?&?&?).
        unfold MemByte.sbyte_sid in H2.
        rewrite e in H2; inv H2.
        lia.
  Qed.

  Lemma find_free_block_can_always_succeed :
    forall ms (len : nat) (pr : Provenance),
    exists ptr ptrs,
      ret (ptr, ptrs) {{ms}} ∈ {{ms}} find_free_block len pr.
  Proof using.
    intros ms len pr.
    pose proof @find_free_block_correct as GET_FREE.
    specialize (GET_FREE (MemStateFreshT (itree Eff)) Eff _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  MemStateFreshT_MemMonad len pr (fun _ _ => True)).
    red in GET_FREE.
    pose proof MemMonad_valid_state_exists ms as (st & VALID).
    pose proof MemState_eqv'_read_byte_allowed_all_preserved.
    specialize (GET_FREE _ _ VALID I).
    destruct GET_FREE as [UB | GET_FREE].

    { (* UB in find_free_block *)
      firstorder.
    }

    (* find_free_block doesn't necessarily UB *)
    destruct GET_FREE as [res [st' [ms' [GET_FREE [FIND_FREE POST_FREE]]]]].

    cbn in *.
    red in GET_FREE.
    destruct GET_FREE as [tptrs [IN REST]].
    cbn in *.

    pose proof big_intptr_seq_succeeds 0 len as [seq SEQ].
    rewrite SEQ in REST.
    cbn in REST.
    red in REST.

    destruct ms; cbn in *.
    destruct ms_memory_stack0; cbn in *.

    repeat rewrite bind_ret_l in REST.
    cbn in REST.

    repeat rewrite bind_ret_l in REST.
    cbn in REST.

    destruct_err_ub_oom res.

    { (* OOM *)
      exfalso.
      cbn in *.
      destruct IN as [oom_msg TPTRS].
      rewrite TPTRS in REST.
      setoid_rewrite (@rbm_raise_bind _ _ _ _ _ (RaiseBindM_OOM _)) in REST.
      pose proof (int_to_ptr_safe
                    (next_memory_key
                       {|
                         MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_memory := memory_stack_memory0;
                         MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_frame_stack :=
                           memory_stack_frame_stack0;
                         MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_heap := memory_stack_heap0
                       |})
                    (allocation_id_to_prov (provenance_to_allocation_id pr))) as HITP_SAFE.
      destruct (ITOP.int_to_ptr
                    (next_memory_key
                       {|
                         MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_memory := memory_stack_memory0;
                         MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_frame_stack :=
                           memory_stack_frame_stack0;
                         MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_heap := memory_stack_heap0
                       |}) (allocation_id_to_prov (provenance_to_allocation_id pr))) eqn:HITP;
        inv HITP_SAFE.

      cbn in REST.
      repeat setoid_rewrite bind_ret_l in REST.
      cbn in REST.
      destruct (map_monad
                  (fun ix : IP.intptr =>
                     GEP.handle_gep_addr (DTYPE_I 8) a [Events.DV.DVALUE_IPTR ix]) seq) eqn:HMAPM.

      { (* Error, should be contradiction *)
        cbn in REST.
        cbn in HMAPM.
        erewrite ptr_to_int_int_to_ptr in HMAPM; eauto.
        erewrite int_to_ptr_provenance in HMAPM; eauto.
        setoid_rewrite HMAPM in REST.
        repeat setoid_rewrite (@rbm_raise_bind _ _ _ _ _ (RaiseBindM_Fail _)) in REST.

        raise_abs: REST. }

      cbn in REST.
      repeat setoid_rewrite bind_ret_l in REST.
      cbn in REST.
      destruct (map_monad id l) eqn:HSEQUENCE.
      2: {
        (* One of the GEPs raised OOM, should not be possible *)
        cbn in *.
        apply map_monad_OOM_fail in HSEQUENCE as [a' [INl A'EQ]].
        unfold id in A'EQ. inv A'EQ.
        pose proof map_monad_err_In _ _ _ _ HMAPM INl as [ix [GEP INix]].
        apply GEP.handle_gep_addr_ix_OOM in GEP; auto.
        destruct GEP as [msg' GEP].
        pose proof
          (LP.I2P_BIG.int_to_ptr_safe (ptr_to_int a + Z.of_N (sizeof_dtyp (DTYPE_I 8)) * to_Z ix)
             (address_provenance a)) as SAFE.
        rewrite GEP in SAFE.
        contradiction.
      }

      cbn in HMAPM.
      erewrite ptr_to_int_int_to_ptr in HMAPM; eauto.
      erewrite int_to_ptr_provenance in HMAPM; eauto.
      setoid_rewrite HMAPM in REST.
      cbn in REST.
      rewrite bind_ret_l in REST.
      cbn in REST.

      setoid_rewrite HSEQUENCE in REST.
      cbn in REST.
      rewrite bind_ret_l in REST.
      cbn in REST.

      rewrite map_ret in REST.
      cbn in REST.
      symmetry in REST.
      apply raiseOOM_ret_inv_itree in REST.
      auto.
    }

    { (* UB *)
      cbn in *.
      contradiction.
    }

    { (* Error *)
      cbn in *.
      contradiction.
    }

    { (* Success *)
      cbn in *.
      destruct res0 as [ptr ptrs].
      exists ptr. exists ptrs.
      rewrite IN in REST.
      pose proof (int_to_ptr_safe
                    (next_memory_key
                       {|
                         MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_memory := memory_stack_memory0;
                         MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_frame_stack :=
                           memory_stack_frame_stack0;
                         MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_heap := memory_stack_heap0
                       |})
                    (allocation_id_to_prov (provenance_to_allocation_id pr))) as HITP_SAFE.
      destruct (ITOP.int_to_ptr
                    (next_memory_key
                       {|
                         MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_memory := memory_stack_memory0;
                         MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_frame_stack :=
                           memory_stack_frame_stack0;
                         MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_heap := memory_stack_heap0
                       |}) (allocation_id_to_prov (provenance_to_allocation_id pr))) eqn:HITP;
        inv HITP_SAFE.

      cbn in REST.
      repeat setoid_rewrite bind_ret_l in REST.
      cbn in REST.
      destruct (map_monad
                  (fun ix : IP.intptr =>
                     GEP.handle_gep_addr (DTYPE_I 8) a [Events.DV.DVALUE_IPTR ix]) seq) eqn:HMAPM.

      { (* Error, should be contradiction *)
        cbn in REST.
        cbn in HMAPM.
        erewrite ptr_to_int_int_to_ptr in HMAPM; eauto.
        erewrite int_to_ptr_provenance in HMAPM; eauto.
        setoid_rewrite HMAPM in REST.
        repeat setoid_rewrite (@rbm_raise_bind _ _ _ _ _ (RaiseBindM_Fail _)) in REST.
        raise_abs:REST. }

      tauto.
    }
  Qed.

  Lemma allocate_bytes_post_conditions_can_always_be_satisfied :
    forall (ms_init : MemState) bytes pr,
    exists ms_final ptr ptrs,
      (ret (ptr, ptrs) {{ms_init}} ∈ {{ms_init}} find_free_block (length bytes) pr) /\
      allocate_bytes_post_conditions ms_init bytes pr ms_final ptr ptrs.
  Proof using.
    intros ms_init bytes pr.

    Opaque find_free_block.
    pose proof MemMonad_valid_state_exists ms_init as (st_mem & VALID_MEM).
    remember (N.max (N.succ (largest_sbyte_sid bytes)) st_mem) as st.
    assert (MemMonad_valid_state ms_init st) as VALID.
    { red.
      intros sid' H.
      eapply VALID_MEM in H.
      lia.
    }

    (* Memory state pre allocation *)
    destruct ms_init as [mstack mprov] eqn:MSINIT.
    destruct mstack as [mem fs h] eqn:MSTACK.

    pose proof (allocate_bytes_with_pr_correct bytes pr (Eff := Eff) (MemM:=MemStateFreshT (itree Eff))) as ALLOC.
    red in ALLOC.
    specialize (ALLOC _ _ VALID).
    forward ALLOC.
    { clear - Heqst.
      pose proof largest_sbyte_sid_le bytes.
      eapply Forall_forall.
      intros x IN.
      eapply Forall_forall in H; eauto.
      destruct H as (?&?&?).
      exists x0.
      split; eauto.
      lia.
    }

    destruct ALLOC as [UB | ALLOC].

    { (* UB *)
      cbn in UB.
      destruct UB as [ub_ms [ub_msg [CONTRA | REST]]]; try contradiction.
      destruct REST as [ms'' [[ptr' ptrs'] [[MEQ FREE] [[] | REST]]]];
        firstorder.
    }

    (* allocate_bytes doesn't necessarily UB *)
    destruct ALLOC as [res [st' [ms' [ALLOC_EXEC [ALLOC_SPEC POST_ALLOC]]]]].

    cbn in ALLOC_EXEC.
    red in ALLOC_EXEC.
    destruct ALLOC_EXEC as [t_alloc [RES_T_ALLOC ALLOC_EXEC]].

    repeat setoid_rewrite bind_ret_l in ALLOC_EXEC.
    cbn in ALLOC_EXEC.
    red in ALLOC_EXEC.

    repeat setoid_rewrite bind_ret_l in ALLOC_EXEC.
    cbn in ALLOC_EXEC.

    pose proof big_intptr_seq_succeeds 0 (Datatypes.length bytes) as [seq SEQ].
    rewrite SEQ in ALLOC_EXEC.
    cbn in ALLOC_EXEC.

    repeat setoid_rewrite bind_ret_l in ALLOC_EXEC.
    cbn in ALLOC_EXEC.

    (*rewrite MSINIT in ALLOC_EXEC. *)
    cbn in ALLOC_EXEC.
    repeat setoid_rewrite bind_ret_l in ALLOC_EXEC.
    cbn in ALLOC_EXEC.

    pose proof (int_to_ptr_safe
                  (next_memory_key
                     {|
                       MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_memory := mem;
                       MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_frame_stack := fs;
                       MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_heap := h
                     |})
                  (allocation_id_to_prov (provenance_to_allocation_id pr))) as HITP_SAFE.
    destruct (ITOP.int_to_ptr
                (next_memory_key
                     {|
                       MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_memory := mem;
                       MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_frame_stack := fs;
                       MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_heap := h
                     |})
                (allocation_id_to_prov (provenance_to_allocation_id pr))) eqn:HITP;
      inv HITP_SAFE.

    cbn in ALLOC_EXEC.
    repeat setoid_rewrite bind_ret_l in ALLOC_EXEC.
    cbn in ALLOC_EXEC.

    destruct (map_monad
                (fun ix : IP.intptr =>
                   GEP.handle_gep_addr (DTYPE_I 8) a [Events.DV.DVALUE_IPTR ix]) seq) eqn:HMAPM.

    { (* Error *)
      cbn in HMAPM.
      erewrite ptr_to_int_int_to_ptr in HMAPM; eauto.
      erewrite int_to_ptr_provenance in HMAPM; eauto.
      setoid_rewrite HMAPM in ALLOC_EXEC.
      cbn in ALLOC_EXEC.
      repeat setoid_rewrite (@rbm_raise_bind _ _ _ _ _ (RaiseBindM_Fail _)) in ALLOC_EXEC.

      destruct_err_ub_oom res.
      - (* OOM *)
        exfalso.
        cbn in RES_T_ALLOC.
        destruct RES_T_ALLOC as [oom_msg RES_T_ALLOC].
        rewrite RES_T_ALLOC in ALLOC_EXEC.
        setoid_rewrite (@rbm_raise_bind _ _ _ _ _ (RaiseBindM_OOM _)) in ALLOC_EXEC.
        raise_abs: ALLOC_EXEC.
      - (* UB *)
        cbn in RES_T_ALLOC.
        destruct RES_T_ALLOC as [ub_msg RES_T_ALLOC].
        rewrite RES_T_ALLOC in ALLOC_EXEC.
        setoid_rewrite (@rbm_raise_bind _ _ _ _ _ (RaiseBindM_UB _)) in ALLOC_EXEC.
        raise_abs: ALLOC_EXEC.
      - (* Error *)
        exfalso.
        clear - ALLOC_SPEC.
        cbn in ALLOC_SPEC.
        destruct ALLOC_SPEC as [UB | REST]; [contradiction|].
        destruct REST as [ms''' [[ptr' ptrs'] [[MEQ FREE] [UB | REST]]]];
          firstorder.
      - (* Success *)
        cbn in RES_T_ALLOC.
        rewrite RES_T_ALLOC in ALLOC_EXEC.
        rewrite bind_ret_l in ALLOC_EXEC.
        eapply raise_ret_inv_itree in ALLOC_EXEC.
        contradiction.
    }

    { (* Success *)
      cbn in HMAPM.
      erewrite ptr_to_int_int_to_ptr in HMAPM; eauto.
      erewrite int_to_ptr_provenance in HMAPM; eauto.
      setoid_rewrite HMAPM in ALLOC_EXEC.
      cbn in ALLOC_EXEC.
      repeat setoid_rewrite bind_ret_l in ALLOC_EXEC.
      cbn in ALLOC_EXEC.
      repeat setoid_rewrite bind_ret_l in ALLOC_EXEC.
      repeat rewrite bind_ret_l in ALLOC_EXEC.
      cbn in ALLOC_EXEC.
      repeat rewrite bind_ret_l in ALLOC_EXEC.
      cbn in ALLOC_EXEC.

      destruct (map_monad id l) eqn:HSEQUENCE.
      2: {
        (* One of the GEPs raised OOM, should not be possible *)
        cbn in *.
        apply map_monad_OOM_fail in HSEQUENCE as [a' [INl A'EQ]].
        unfold id in A'EQ. inv A'EQ.
        pose proof map_monad_err_In _ _ _ _ HMAPM INl as [ix [GEP INix]].
        inv GEP.
      }

      cbn in ALLOC_EXEC.
      repeat setoid_rewrite bind_ret_l in ALLOC_EXEC.
      cbn in ALLOC_EXEC.
      repeat rewrite bind_ret_l in ALLOC_EXEC.
      cbn in ALLOC_EXEC.
      repeat rewrite bind_ret_l in ALLOC_EXEC.
      cbn in ALLOC_EXEC.

      rewrite map_ret in ALLOC_EXEC.

      destruct_err_ub_oom res.
      - (* OOM *)
        cbn in RES_T_ALLOC.
        destruct RES_T_ALLOC as [oom_msg RES_T_ALLOC].
        rewrite RES_T_ALLOC in ALLOC_EXEC.
        setoid_rewrite (@rbm_raise_bind _ _ _ _ _ (RaiseBindM_OOM _)) in ALLOC_EXEC.
        symmetry in ALLOC_EXEC.
        eapply raiseOOM_ret_inv_itree in ALLOC_EXEC; contradiction.
      - (* UB *)
        cbn in RES_T_ALLOC.
        destruct RES_T_ALLOC as [ub_msg RES_T_ALLOC].
        rewrite RES_T_ALLOC in ALLOC_EXEC.
        setoid_rewrite (@rbm_raise_bind _ _ _ _ _ (RaiseBindM_UB _)) in ALLOC_EXEC.
        symmetry in ALLOC_EXEC.
        eapply raiseUB_ret_inv_itree in ALLOC_EXEC; contradiction.
      - (* Error *)
        exfalso.
        clear - ALLOC_SPEC.
        cbn in ALLOC_SPEC.
        destruct ALLOC_SPEC as [UB | REST]; [contradiction|].
        destruct REST as [ms''' [[ptr' ptrs'] [[MEQ FREE] [UB | REST]]]];
          firstorder.
      - (* Success *)
        cbn in RES_T_ALLOC.
        rewrite RES_T_ALLOC in ALLOC_EXEC.
        rewrite bind_ret_l in ALLOC_EXEC.

        epose proof (@eq1_ret_ret (itree Eff) _ _ _ _ _ _ ALLOC_EXEC) as RETINV.
        inv RETINV.

        cbn in ALLOC_SPEC.
        exists {|
            MemoryBigIntptrInfiniteSpec.MMSP.ms_memory_stack :=
              add_all_to_frame
                {|
                  MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_memory :=
                    add_all_index
                      (map (fun b : SByte => (b, provenance_to_allocation_id pr)) bytes)
                      (next_memory_key
                         {|
                           MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_memory := mem;
                           MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_frame_stack :=
                             fs;
                           MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_heap := h
                         |})
                      mem;
                  MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_frame_stack := fs;
                  MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_heap := h
                |} l0;
            MemoryBigIntptrInfiniteSpec.MMSP.ms_provenance := mprov
          |}.

        cbn in ALLOC_SPEC.
        destruct ALLOC_SPEC as [ms_final' [[ptr'' ptrs''] [FIND_FREE' ALLOC_SPEC]]].
        pose proof FIND_FREE' as [MEQ BLOCK_FREE_SPEC].
        subst ms_final'.
        destruct ALLOC_SPEC as [ms_final' [[ptr''' ptrs'''] [[BYTES_POST [PTREQ PTRSEQ]] [MEQ ALLOC_SPEC]]]].
        subst ms_final' ptr'' ptr''' ptrs'''.

        exists (next_memory_key
                        {|
                          MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_memory := mem;
                          MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_frame_stack := fs;
                          MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_heap := h
                        |}, allocation_id_to_prov (provenance_to_allocation_id pr)).
        exists ptrs''.

        eauto.
    }
  Qed.

  Section MemoryPrimitives.
    Context {MemM : Type -> Type}.
    Context {Eff : Type -> Type}.
    (* Context `{Monad MemM}. *)
    (* Context `{MonadProvenance Provenance MemM}. *)
    (* Context `{MonadStoreID MemM}. *)
    (* Context `{MonadMemState MemState MemM}. *)
    (* Context `{RAISE_ERROR MemM} `{RAISE_UB MemM} `{RAISE_OOM MemM}. *)
    Context `{MemMonad MemM (itree Eff)}.

    (* Lemma find_free_block_always_succeeds : *)
    (*   forall sz prov ms (st : ExtraState), *)
    (*   exists ptr ptrs, *)
    (*     find_free_block sz prov ms (ret (ptr, ptrs)). *)
    (* Proof using. *)
    (*   intros sz prov ms st. *)
    (*   pose proof (find_free_block_correct sz prov (fun _ _ => True)) as GET_FREE. *)
    (*   unfold exec_correct in GET_FREE. *)
    (*   specialize (GET_FREE ms st). *)
    (*   forward GET_FREE. admit. *)
    (*   forward GET_FREE; auto. *)

    (*   destruct GET_FREE as [[ub_msg UB] | GET_FREE]. *)
    (*   apply find_free_block_never_ub in UB; inv UB. *)

    (*   destruct GET_FREE as [ERR | [OOM | RET]]. *)
    (*   - destruct ERR as [err_msg [RUN [err_msg_spec ERR]]]. *)
    (*     eapply find_free_block_never_err in ERR; inv ERR. *)
    (*   - cbn in *. *)
    (*     destruct OOM as [oom_msg [RUN _]]. *)
    (*     unfold get_free_block in RUN. *)
    (* Qed. *)

    (* Lemma allocate_bytes_post_conditions_can_always_be_satisfied : *)
    (*   forall (ms_init ms_fresh_pr : MemState) dt num_elements bytes pr ptr ptrs *)
    (*     (FRESH_PR : (@fresh_provenance Provenance (MemPropT MemState) _ ms_init (ret (ms_fresh_pr, pr)))) *)
    (*     (FIND_FREE : find_free_block (length bytes) pr ms_fresh_pr (ret (ms_fresh_pr, (ptr, ptrs)))) *)
    (*     (BYTES_SIZE : (sizeof_dtyp dt * num_elements)%N = N.of_nat (length bytes)) *)
    (*     (NON_VOID : dt <> DTYPE_Void), *)
    (*   exists ms_final, *)
    (*     allocate_bytes_post_conditions ms_fresh_pr dt num_elements bytes pr ms_final ptr ptrs. *)
    (* Proof using. *)
    (*   intros ms_init ms_fresh_pr dt num_elements bytes pr ptr ptrs FRESH_PR FIND_FREE BYTES_SIZE NON_VOID. *)

    (*   destruct ms_fresh_pr as [[mem fs h] pr'] eqn:HMS.       *)

    (*   pose proof (allocate_bytes_correct dt num_elements bytes (fun _ _ => True) ms_init) as CORRECT. *)
    (*   unfold exec_correct in CORRECT. *)
    (*   assert (ExtraState) as st by admit. *)
    (*   specialize (CORRECT st). *)
    (*   forward CORRECT. admit. *)
    (*   forward CORRECT; auto. *)

    (*   destruct CORRECT as [[ubmsg UB] | CORRECT]. *)
    (*   { cbn in UB. *)
    (*     destruct UB as [UB | UB]; [inv UB|]. *)
    (*     destruct UB as [ms [pr' [FRESH UB]]]. *)
    (*     destruct UB as [UB | UB]; [inv UB|]. *)
    (*     destruct UB as [ms' [[ptr' ptrs'] [[EQ FREE] UB]]]. *)
    (*     subst. *)
    (*     destruct UB as [[UB | UB] | UB]; try contradiction. *)
    (*     destruct UB as [ms'' [[ptr'' ptrs''] [[EQ FREE'] UB]]]. *)
    (*     contradiction. *)
    (*   } *)

    (*   destruct CORRECT as [[errmsg [ERR [errspecmsg ERRSPEC]]] | CORRECT]. *)
    (*   { cbn in ERRSPEC. *)
    (*     destruct ERRSPEC as [UB | UB]; [inv UB|]. *)
    (*     destruct UB as [ms [pr' [FRESH UB]]]. *)
    (*     destruct UB as [UB | UB]; [inv UB|]. *)
    (*     destruct UB as [ms' [[ptr' ptrs'] [[EQ FREE] UB]]]. *)
    (*     subst. *)
    (*     destruct UB as [UB | UB]; try contradiction. *)
    (*     destruct UB as [ms'' [[ptr'' ptrs''] [[EQ FREE'] UB]]]. *)
    (*     contradiction. *)
    (*   } *)

    (*   destruct CORRECT as [[oommsg [OOM [oomspecmsg OOMSPEC]]] | CORRECT]. *)
    (*   { cbn in *. *)
    (*   } *)

    (*   destruct ms_fresh_pr as [[mem fs h] pr'] eqn:HMS. *)
    (*   exists {| *)
    (*     MemoryBigIntptrInfiniteSpec.MMSP.ms_memory_stack := *)
    (*     {| *)
    (*       MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_memory := mem; *)
    (*       MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_frame_stack := fs; *)
    (*       MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_heap := h *)
    (*     |}; *)
    (*     MemoryBigIntptrInfiniteSpec.MMSP.ms_provenance := pr' *)
    (*   |}. *)
    (*   eexists. *)
    (*   split. *)





    (*   assert  *)
    (*   pose proof (@MemMonad_run *)
    (*                 ExtraState MemM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ *)
    (*                 (allocate_bytes dt num_elements bytes) *)
    (*                 ms_fresh_pr *)
    (*                 initial_state (* Probably wrong, not guaranteed to be valid. May need existence lemma *) *)
    (*              ). *)
    (*   (allocate_bytes dt num_elements bytes)). *)

    (*   unfold exec_correct in CORRECT. *)
    (*    destruct CORRECT. *)
    (* Qed. *)
    (* Admitted. *)

  End MemoryPrimitives.
End MemoryBigIntptrInfiniteSpec.

Module MemoryBigIntptrInfiniteSpecHelpers :=
  MemoryModelInfiniteSpecHelpers LLVMParamsBigIntptr MemoryBigIntptr.MP MemoryBigIntptr.MMEP.MMSP MemoryBigIntptr.MMEP.MemSpec MemoryBigIntptrInfiniteSpec.
