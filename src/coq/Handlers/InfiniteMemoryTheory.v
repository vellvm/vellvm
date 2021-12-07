From Vellvm Require Import
     Semantics.LLVMParams
     Semantics.LLVMEvents
     Semantics.MemoryAddress
     Semantics.MemoryParams
     Semantics.Lang
     Semantics.InterpretationStack
     Handlers.FiniteMemory
     FiniteMemoryTheory
     Tactics.

From ExtLib Require Import
     Structures.Monad.

Module Type InfiniteMemoryTheory (LP : LLVMParams) (Events : LLVM_INTERACTIONS LP.ADDR LP.IP LP.SIZEOF) (MP : MemoryParams LP Events) (FM : FinMemory LP Events MP).
  Import FM.
  Import ESID.
  Import DynamicTypes.

  Parameter allocate_succeeds :
    forall ms dt,
      dt <> DTYPE_Void ->
      ErrSID_succeeds (allocate ms dt).

End InfiniteMemoryTheory.

Module BigIntptrInfiniteMemoryTheory : InfiniteMemoryTheory InterpreterStackBigIntptr.LP InterpreterStackBigIntptr.LLVM.Events InterpreterStackBigIntptr.LLVM.MP InterpreterStackBigIntptr.LLVM.MEM.
  Import InterpreterStackBigIntptr.
  Import InterpreterStackBigIntptr.LLVM.MEM.
  Import ESID.
  Import LP.PROV.
  Import DynamicTypes.
  Import LP.SIZEOF.
  Import BinNat.N.
  Import BinNums.
  Import InterpreterStackBigIntptr.LP.IP.
  Import InterpreterStackBigIntptr.LP.IP_BIG.

  Lemma allocate_undef_bytes_size_succeeds :
    forall m f a dt x,
      ErrSID_succeeds
        (allocate_undef_bytes_size m (next_memory_key (m, f)) a
       (sizeof_dtyp dt) x
       dt).
  Proof.
    intros m f a dt.
    revert m f a.
    induction (sizeof_dtyp dt) using peano_ind.
    - intros m f a x sid pr; cbn; auto.
    - intros m f a x.
      unfold allocate_undef_bytes_size in *.

      match goal with
      | H : _ |- context [recursion ?a ?f ?n ?x]
        =>
          let AA := fresh AA in
          assert (a = a) as AA by reflexivity;
          pose proof (@recursion_succ (N -> ErrSID (memory * list Z)) Logic.eq a f AA) as REC
      end.

      unfold Morphisms.Proper, Morphisms.respectful in REC.
      rewrite REC; [| repeat intros; subst; reflexivity].
      clear REC.

      apply ErrSID_succeeds_bind; auto.

      intros sid pr a0 EVALS.
      destruct a0.

      apply ErrSID_succeeds_bind; [apply fresh_sid_succeeds|].
      intros sid0 pr0 a0 H.
      apply ErrSID_succeeds_bind.
      { match goal with
        | H : _ |- context [from_Z ?x]
          => pose proof from_Z_safe x as SAFE
        end.
        break_match_hyp; [|contradiction].
        unfold ErrSID_succeeds; cbn; auto.        
      }

      intros sid1 pr1 a1 EVALS'.
      apply ErrSID_succeeds_ret.
  Qed.

  Hint Resolve allocate_undef_bytes_size_succeeds : MEM_SUC.

  Lemma allocate_undef_bytes_succeeds :
    forall m f a dt,
      ErrSID_succeeds
        (allocate_undef_bytes m (next_memory_key (m, f)) a dt).
  Proof.
    intros m f a dt.
    unfold allocate_undef_bytes.
    apply allocate_undef_bytes_size_succeeds.
  Qed.

  Hint Resolve allocate_undef_bytes_succeeds : MEM_SUC.

  Hint Resolve
       ErrSID_succeeds_bind
       fresh_allocation_id_succeeds : MEM_SUC.

  Lemma allocate_succeeds :
    forall ms dt,
      dt <> DTYPE_Void ->
      ErrSID_succeeds (allocate ms dt).
  Proof.
    intros [m f] dt DT.
    destruct dt; try contradiction.

    all:
      apply ErrSID_succeeds_bind;
      auto with MEM_SUC;
      intros * ?;
      apply ErrSID_succeeds_bind;
      auto with MEM_SUC;
      intros * ?;
      break_match;
      auto with MEM_SUC.
  Qed.

End BigIntptrInfiniteMemoryTheory.
