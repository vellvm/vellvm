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
     Eq.Eq.

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

Import ListNotations.
Import ListUtil.
Import Utils.Monads.

Import MonadNotation.
Open Scope monad_scope.

From Vellvm.Handlers Require Import
     MemoryModel.

From Vellvm.Handlers.MemoryModules Require Import
     FiniteAddresses
     FiniteIntptr
     FiniteSizeof
     FiniteSpecPrimitives
     FiniteExecPrimitives.



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

Module Addr := FiniteAddresses.Addr.
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

  Module MP := MemoryParams.Make LP GEP Byte.

  Module MMEP := FiniteMemoryModelExecPrimitives LP MP.
  Module MEM_MODEL := MakeMemoryModelExec LP MP MMEP.
  Module MEM_SPEC_INTERP := MakeMemorySpecInterpreter LP MP MMEP.MMSP MMEP.MemSpec MMEP.MemExecM.
  Module MEM_EXEC_INTERP := MakeMemoryExecInterpreter LP MP MMEP MEM_MODEL MEM_SPEC_INTERP.

  (* Concretization *)
  Module CP := ConcretizationParams.Make LP MP.

  Export GEP Byte MP MEM_MODEL CP.
End MakeFiniteMemory.

Module LLVMParamsBigIntptr := LLVMParams.MakeBig Addr BigIP FinSizeof FinPTOI FinPROV FinITOP BigIP_BIG.
Module LLVMParams64BitIntptr := LLVMParams.Make Addr IP64Bit FinSizeof FinPTOI FinPROV FinITOP.

Module MemoryBigIntptr := MakeFiniteMemory LLVMParamsBigIntptr.
Module Memory64BitIntptr := MakeFiniteMemory LLVMParams64BitIntptr.


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

  Definition Eff := FailureE +' OOME +' UBE.

  Import Eq.
  Import MMSP.

  (* TODO: Move out of infinite stuff *)
  Lemma find_free_block_never_ub :
    forall sz prov ms msg,
      ~ find_free_block sz prov ms (raise_ub msg).
  Proof.
    intros sz prov ms msg FREE.
    cbn in FREE.
    auto.
  Qed.

  Lemma find_free_block_never_err :
    forall sz prov ms msg,
      ~ find_free_block sz prov ms (raise_error msg).
  Proof.
    intros sz prov ms msg FREE.
    cbn in FREE.
    auto.
  Qed.

  Lemma find_free_block_can_always_succeed :
    forall (ms : MemState) (len : nat) (pr : Provenance),
    exists ptr ptrs,
      find_free_block len pr ms (ret (ms, (ptr, ptrs))).
  Proof.
    intros ms len pr.

    (* assert (exists ptr ptrs, get_free_block sz prov ≈ ret (ptr, ptrs)) as [ptr [ptrs GET_FREE]]. *)
    (* admit. *)

    (* exists ptr. exists ptrs. *)

    (* pose proof (find_free_block_correct sz prov (fun _ _ => True)) as FREE. *)

    (* unfold exec_correct in GET_FREE. *)
    (* specialize (FREE ms st). *)
    (* forward FREE. admit. *)
    (* forward FREE; auto. *)

    (* destruct FREE as [[ub_msg UB] | FREE]. *)
    (* apply find_free_block_never_ub in UB; inv UB. *)

    (* destruct FREE as [ERR | [OOM | RET]]. *)
    (* - destruct ERR as [err_msg [RUN [err_msg_spec ERR]]]. *)
    (*   eapply find_free_block_never_err in ERR; inv ERR. *)
    (* - cbn in *. *)
    (*   split; auto. *)
    (*   destruct OOM as [oom_msg [RUN _]]. *)
    (*   unfold get_free_block in RUN. *)
    (*   rewrite MemMonad_run_bind in RUN. *)
    (*   rewrite MemMonad_get_mem_state in RUN. *)
    (*   rewrite Monad.bind_ret_l in RUN. *)
    (*   destruct ms as [[mem fs h] pr] eqn:HMS. *)
    (*   cbn in *. *)

    (*   epose proof (@get_consecutive_ptrs_succeeds *)
    (*                  MemM *)
    (*                  MM EQM _ _ _ _ MLAWS *)
    (*                  (LLVMParamsBigIntptr.ITOP.int_to_ptr *)
    (*                     (next_memory_key *)
    (*                        {| *)
    (*                          MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_memory := mem; *)
    (*                          MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_frame_stack := fs; *)
    (*                          MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_heap := h *)
    (*                        |}) *)
    (*                     (LLVMParamsBigIntptr.PROV.allocation_id_to_prov *)
    (*                        (LLVMParamsBigIntptr.PROV.provenance_to_allocation_id prov))) *)
    (*                  sz) as (ptrs' & GEP). *)

    (*   Set Nested Proofs Allowed. *)
    (*   #[global] Instance MemMonad_eq1_runm_proper : *)
    (*     forall A, *)
    (*       Proper (@eq1 _ EQM A ==> eq ==> eq ==> *)
    (*                    @eq1 (itree Eff) *)
    (*                    (@MemMonad_eq1_runm ExtraState MemM (itree Eff) MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB *)
    (*                                        RunOOM EQM EQRI MLAWS H) *)
    (*                    _) MemMonad_run. *)
    (*   Proof. *)

    (*     unfold Proper, respectful. *)
    (*     intros A x y H0 x0 y0 H1 x1 y1 H2; subst. *)
    (*   Admitted. *)

    (*   epose proof MemMonad_eq1_runm_proper. *)
    (*   specialize (H0 (prod LLVMParamsBigIntptr.ADDR.addr (list LLVMParamsBigIntptr.ADDR.addr))). *)
    (*   unfold Proper, respectful in H0. *)

    (*   specialize (H0 *)
    (*                 (ptrs <- (@MemSpec.MemHelpers.get_consecutive_ptrs *)
    (*                            MemM MM MOOM MERR *)
    (*                            (LLVMParamsBigIntptr.ITOP.int_to_ptr *)
    (*                               (next_memory_key *)
    (*                                  {| *)
    (*                                    MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_memory := mem; *)
    (*                                    MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_frame_stack := fs; *)
    (*                                    MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_heap := h *)
    (*                                  |}) *)
    (*                               (LLVMParamsBigIntptr.PROV.allocation_id_to_prov *)
    (*                                  (LLVMParamsBigIntptr.PROV.provenance_to_allocation_id prov))) sz);; *)
    (*                  ret *)
    (*                    (LLVMParamsBigIntptr.ITOP.int_to_ptr *)
    (*                       (next_memory_key *)
    (*                          {| *)
    (*                            MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_memory := mem; *)
    (*                            MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_frame_stack := fs; *)
    (*                            MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_heap := h *)
    (*                          |}) *)
    (*                       (LLVMParamsBigIntptr.PROV.allocation_id_to_prov *)
    (*                          (LLVMParamsBigIntptr.PROV.provenance_to_allocation_id prov)), ptrs)) *)

    (*                 (ret *)
    (*                    (LLVMParamsBigIntptr.ITOP.int_to_ptr *)
    (*                       (next_memory_key *)
    (*                          {| *)
    (*                            MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_memory := mem; *)
    (*                            MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_frame_stack := fs; *)
    (*                            MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_heap := h *)
    (*                          |}) *)
    (*                       (LLVMParamsBigIntptr.PROV.allocation_id_to_prov *)
    (*                          (LLVMParamsBigIntptr.PROV.provenance_to_allocation_id prov)), ptrs')) *)
    (*              ). *)
    (*   forward H0. *)
    (*   { admit. *)
    (*   } *)

    (*   specialize (H0 {| *)
    (*                   MemoryBigIntptrInfiniteSpec.MMSP.ms_memory_stack := *)
    (*                   {| *)
    (*                     MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_memory := mem; *)
    (*                     MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_frame_stack := fs; *)
    (*                     MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_heap := h *)
    (*                   |}; *)
    (*                   MemoryBigIntptrInfiniteSpec.MMSP.ms_provenance := pr *)
    (*                 |} *)
    (*                  {| *)
    (*                    MemoryBigIntptrInfiniteSpec.MMSP.ms_memory_stack := *)
    (*                    {| *)
    (*                      MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_memory := mem; *)
    (*                      MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_frame_stack := fs; *)
    (*                      MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_heap := h *)
    (*                    |}; *)
    (*                    MemoryBigIntptrInfiniteSpec.MMSP.ms_provenance := pr *)
    (*                  |} *)
    (*                  eq_refl). *)
    (*   specialize (H0 st st eq_refl). *)

    (*   rewrite H0 in RUN. *)
    (*   clear H0. *)
    (*   rewrite MemMonad_run_ret in RUN. *)

    (*   cbn in RUN. *)
    (*   apply MemMonad_eq1_raise_oom_inv in RUN. *)
    (*   contradiction. *)
    (* - destruct RET as [st' [ms' [[ptr' ptrs'] [RUN [FREE VALID]]]]]. *)
    (*   cbn in *. *)
    (*   destruct FREE as [MEMEQ FREE]. *)
    (*   subst. *)
    (*   split; [tauto|]. *)

    (*   unfold get_free_block in *. *)
    (*   rewrite MemMonad_run_bind in RUN. *)
    (*   rewrite MemMonad_get_mem_state in RUN. *)
    (*   rewrite Monad.bind_ret_l in RUN. *)

    (*   destruct ms' as [[mem fs h] pr] eqn:HMS. *)

    (*   epose proof (@get_consecutive_ptrs_succeeds *)
    (*                  MemM *)
    (*                  MM EQM _ _ _ _ MLAWS *)
    (*                  (LLVMParamsBigIntptr.ITOP.int_to_ptr *)
    (*                     (next_memory_key *)
    (*                        {| *)
    (*                          MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_memory := mem; *)
    (*                          MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_frame_stack := fs; *)
    (*                          MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_heap := h *)
    (*                        |}) *)
    (*                     (LLVMParamsBigIntptr.PROV.allocation_id_to_prov *)
    (*                        (LLVMParamsBigIntptr.PROV.provenance_to_allocation_id prov))) *)
    (*                  sz) as (ptrs_gep & GEP). *)
  Admitted.

  Lemma allocate_bytes_post_conditions_can_always_be_satisfied :
    forall (ms_init : MemState) dt bytes pr ptr ptrs
      (FIND_FREE : find_free_block (length bytes) pr ms_init (ret (ms_init, (ptr, ptrs))))
      (BYTES_SIZE : sizeof_dtyp dt = N.of_nat (length bytes))
      (NON_VOID : dt <> DTYPE_Void),
    exists ms_final,
      allocate_bytes_post_conditions ms_init dt bytes pr ms_final ptr ptrs.
  Admitted.

  Section MemoryPrimitives.
    Context {MemM : Type -> Type}.
    Context {Eff : Type -> Type}.
    (* Context `{Monad MemM}. *)
    (* Context `{MonadProvenance Provenance MemM}. *)
    (* Context `{MonadStoreID MemM}. *)
    (* Context `{MonadMemState MemState MemM}. *)
    (* Context `{RAISE_ERROR MemM} `{RAISE_UB MemM} `{RAISE_OOM MemM}. *)
    Context {ExtraState : Type}.
    Context `{MemMonad ExtraState MemM (itree Eff)}.

    (* Lemma find_free_block_always_succeeds : *)
    (*   forall sz prov ms (st : ExtraState), *)
    (*   exists ptr ptrs, *)
    (*     find_free_block sz prov ms (ret (ptr, ptrs)). *)
    (* Proof. *)
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
    (*   forall (ms_init ms_fresh_pr : MemState) dt bytes pr ptr ptrs *)
    (*     (FRESH_PR : (@fresh_provenance Provenance (MemPropT MemState) _ ms_init (ret (ms_fresh_pr, pr)))) *)
    (*     (FIND_FREE : find_free_block (length bytes) pr ms_fresh_pr (ret (ms_fresh_pr, (ptr, ptrs)))) *)
    (*     (BYTES_SIZE : sizeof_dtyp dt = N.of_nat (length bytes)) *)
    (*     (NON_VOID : dt <> DTYPE_Void), *)
    (*   exists ms_final, *)
    (*     allocate_bytes_post_conditions ms_fresh_pr dt bytes pr ms_final ptr ptrs. *)
    (* Proof. *)
    (*   intros ms_init ms_fresh_pr dt bytes pr ptr ptrs FRESH_PR FIND_FREE BYTES_SIZE NON_VOID. *)

    (*   destruct ms_fresh_pr as [[mem fs h] pr'] eqn:HMS.       *)

    (*   pose proof (allocate_bytes_correct dt bytes (fun _ _ => True) ms_init) as CORRECT. *)
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
    (*                 (allocate_bytes dt bytes) *)
    (*                 ms_fresh_pr *)
    (*                 initial_state (* Probably wrong, not guaranteed to be valid. May need existence lemma *) *)
    (*              ). *)
    (*   (allocate_bytes dt bytes)). *)

    (*   unfold exec_correct in CORRECT. *)
    (*    destruct CORRECT. *)
    (* Qed. *)
    (* Admitted. *)

  End MemoryPrimitives.
End MemoryBigIntptrInfiniteSpec.


Module MemoryBigIntptrInfiniteSpecHelpers :=
  MemoryModelInfiniteSpecHelpers  LLVMParamsBigIntptr MemoryBigIntptr.MP MemoryBigIntptr.MMEP.MMSP MemoryBigIntptr.MMEP.MemSpec MemoryBigIntptrInfiniteSpec.
