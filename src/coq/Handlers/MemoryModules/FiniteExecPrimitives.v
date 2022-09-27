From Coq Require Import
     ZArith
     Strings.String
     List
     Lia
     Relations
     RelationClasses
     Morphisms.

From Vellvm Require Import
     Numeric.Coqlib
     Numeric.Integers.

From Vellvm.Syntax Require Import
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

From Vellvm.Utils Require Import
     Util
     Error
     PropT
     Tactics
     IntMaps
     ListUtil
     Monads
     MonadEq1Laws
     MonadExcLaws
     MapMonadExtra
     Raise.

From Vellvm.Handlers Require Import
     MemPropT
     MemoryModel
     MemoryInterpreters.

From Vellvm.Handlers.MemoryModules Require Import
     FiniteAddresses
     FiniteIntptr
     FiniteSizeof
     FiniteSpecPrimitives.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Data.Monads.StateMonad.

From ITree Require Import
     ITree
     Eq.Eq.

Import ListNotations.

Import MonadNotation.
Open Scope monad_scope.

#[local] Open Scope Z_scope.

Module FiniteMemoryModelExecPrimitives (LP : LLVMParams) (MP : MemoryParams LP) <: MemoryModelExecPrimitives LP MP.
  Module MMSP := FiniteMemoryModelSpecPrimitives LP MP.
  Module MemSpec := MakeMemoryModelSpec LP MP MMSP.
  Module MemExecM := MakeMemoryExecMonad LP MP MMSP MemSpec.
  Import MemExecM.

  Import LP.
  Import LP.ADDR.
  Import LP.SIZEOF.
  Import LP.PROV.
  Import LP.PTOI.
  Import LP.ITOP.
  Import MMSP.
  Import MMSP.MemByte.
  Import MemSpec.
  Import MemHelpers.
  Import MP.
  Import GEP.

  (* Convenient to make these opaque so they don't get unfolded *)
  Section MemoryPrimatives.
    Context {MemM : Type -> Type}.
    Context {Eff : Type -> Type}.
    (* Context `{Monad MemM}. *)
    (* Context `{MonadProvenance Provenance MemM}. *)
    (* Context `{MonadStoreID MemM}. *)
    (* Context `{MonadMemState MemState MemM}. *)
    (* Context `{RAISE_ERROR MemM} `{RAISE_UB MemM} `{RAISE_OOM MemM}. *)
    Context {ExtraState : Type}.
    Context `{MemMonad ExtraState MemM (itree Eff)}.

    (*** Data types *)

    Definition initial_frame : Frame :=
      [].

    Definition initial_heap : Heap := IntMaps.empty.

    (** ** Fresh key getters *)

    (* Get the next key in the memory *)
    Definition next_memory_key (m : memory_stack) : Z :=
      next_key (memory_stack_memory m).

    Lemma next_memory_key_next_key :
      forall m f h,
        next_memory_key (mkMemoryStack m f h) = next_key m.
    Proof.
      auto.
    Qed.

    Lemma next_memory_key_next_key_memory_stack_memory :
      forall ms,
        next_memory_key ms = next_key (memory_stack_memory ms).
    Proof.
      auto.
    Qed.

    (*** Primitives on memory *)
    (** Reads *)
    Definition read_byte `{MemMonad ExtraState MemM (itree Eff)} (ptr : addr) : MemM SByte :=
      let addr := ptr_to_int ptr in
      let pr := address_provenance ptr in
      ms <- get_mem_state;;
      let mem := mem_state_memory ms in
      match read_byte_raw mem addr with
      | None => raise_ub "Reading from unallocated memory."
      | Some (byte, aid) =>
          if access_allowed pr aid
          then ret byte

          else
            raise_ub
              ("Read from memory with invalid provenance -- addr: " ++ Show.show addr ++ ", addr prov: " ++ show_prov pr ++ ", memory allocation id: " ++ Show.show (show_allocation_id aid) ++ " memory: " ++ Show.show (map (fun '(key, (_, aid)) => (key, show_allocation_id aid)) (IM.elements mem)))
      end.

    (** Writes *)
    Definition write_byte `{MemMonad ExtraState MemM (itree Eff)} (ptr : addr) (byte : SByte) : MemM unit :=
      let addr := ptr_to_int ptr in
      let pr := address_provenance ptr in
      ms <- get_mem_state;;
      let mem := mem_state_memory ms in
      let prov := mem_state_provenance ms in
      match read_byte_raw mem addr with
      | None => raise_ub "Writing to unallocated memory"
      | Some (_, aid) =>
          if access_allowed pr aid
          then
            let mem' := set_byte_raw mem addr (byte, aid) in
            let fs := mem_state_frame_stack ms in
            let h := mem_state_heap ms in
            put_mem_state (mkMemState (mkMemoryStack mem' fs h) prov)
          else raise_ub
                 ("Trying to write to memory with invalid provenance -- addr: " ++ Show.show addr ++ ", addr prov: " ++ show_prov pr ++ ", memory allocation id: " ++ show_allocation_id aid ++ " Memory: " ++ Show.show (map (fun '(key, (_, aid)) => (key, show_allocation_id aid)) (IM.elements mem)))
      end.

    (** Allocations *)
    Definition addr_allocated `{MemMonad ExtraState MemM (itree Eff)} (ptr : addr) (aid : AllocationId) : MemM bool :=
      ms <- get_mem_state;;
      match read_byte_raw (mem_state_memory ms) (ptr_to_int ptr) with
      | None => ret false
      | Some (byte, aid') =>
          ret (proj_sumbool (aid_eq_dec aid aid'))
      end.

    (* Register a concrete address in a frame *)
    Definition add_to_frame (m : memory_stack) (k : Z) : memory_stack :=
      let '(mkMemoryStack m s h) := m in
      match s with
      | Singleton f => mkMemoryStack m (Singleton (k :: f)) h
      | Snoc s f => mkMemoryStack m (Snoc s (k :: f)) h
      end.

    (* Register a list of concrete addresses in a frame *)
    Definition add_all_to_frame (m : memory_stack) (ks : list Z) : memory_stack
      := fold_left (fun ms k => add_to_frame ms k) ks m.

    (* Register a ptr with the heap *)
    Definition add_to_heap (m : memory_stack) (root : Z) (ptr : Z) : memory_stack :=
      let '(mkMemoryStack m s h) := m in
      let h' := add_with root ptr ret cons h in
      mkMemoryStack m s h'.

    (* Register a list of concrete addresses in the heap *)
    Definition add_all_to_heap' (m : memory_stack) (root : Z) (ks : list Z) : memory_stack
      := fold_left (fun ms k => add_to_heap ms root k) ks m.

    Definition add_all_to_heap (m : memory_stack) (ks : list Z) : memory_stack
      := match ks with
         | [] => m
         | (root :: _) =>
             add_all_to_heap' m root ks
         end.

    Lemma add_to_frame_preserves_memory :
      forall ms k,
        memory_stack_memory (add_to_frame ms k) = memory_stack_memory ms.
    Proof.
      intros [m fs] k.
      destruct fs; auto.
    Qed.

    Lemma add_to_heap_preserves_memory :
      forall ms root k,
        memory_stack_memory (add_to_heap ms root k) = memory_stack_memory ms.
    Proof.
      intros [m fs] root k.
      destruct fs; auto.
    Qed.

    Lemma add_to_frame_preserves_heap :
      forall ms k,
        memory_stack_heap (add_to_frame ms k) = memory_stack_heap ms.
    Proof.
      intros [m fs] k.
      destruct fs; auto.
    Qed.

    Lemma add_to_heap_preserves_frame_stack :
      forall ms root k,
        memory_stack_frame_stack (add_to_heap ms root k) = memory_stack_frame_stack ms.
    Proof.
      intros [m fs] root k.
      destruct fs; auto.
    Qed.

    Lemma add_all_to_frame_preserves_memory :
      forall ms ks,
        memory_stack_memory (add_all_to_frame ms ks) = memory_stack_memory ms.
    Proof.
      intros ms ks; revert ms;
        induction ks; intros ms; auto.
      cbn in *. unfold add_all_to_frame in IHks.
      specialize (IHks (add_to_frame ms a)).
      rewrite add_to_frame_preserves_memory in IHks.
      auto.
    Qed.

    Lemma add_all_to_heap'_preserves_memory :
      forall ms root ks,
        memory_stack_memory (add_all_to_heap' ms root ks) = memory_stack_memory ms.
    Proof.
      intros ms root ks; revert ms root;
        induction ks; intros ms root; auto.
      specialize (IHks (add_to_heap ms root a) root).
      cbn in *.
      unfold add_all_to_heap' in *.
      rewrite add_to_heap_preserves_memory in IHks.
      auto.
    Qed.

    Lemma add_all_to_heap_preserves_memory :
      forall ms ks,
        memory_stack_memory (add_all_to_heap ms ks) = memory_stack_memory ms.
    Proof.
      intros ms [|a ks]; auto.
      apply add_all_to_heap'_preserves_memory.
    Qed.

    Lemma add_all_to_frame_preserves_heap :
      forall ms ks,
        memory_stack_heap (add_all_to_frame ms ks) = memory_stack_heap ms.
    Proof.
      intros ms ks; revert ms;
        induction ks; intros ms; auto.
      cbn in *. unfold add_all_to_frame in IHks.
      specialize (IHks (add_to_frame ms a)).
      rewrite add_to_frame_preserves_heap in IHks.
      auto.
    Qed.

    Lemma add_all_to_heap'_preserves_frame_stack :
      forall ms root ks,
        memory_stack_frame_stack (add_all_to_heap' ms root ks) = memory_stack_frame_stack ms.
    Proof.
      intros ms root ks; revert root ms;
        induction ks; intros root ms; auto.
      cbn in *. unfold add_all_to_heap' in IHks.
      specialize (IHks root (add_to_heap ms root a)).
      rewrite add_to_heap_preserves_frame_stack in IHks.
      auto.
    Qed.

    Lemma add_all_to_heap_preserves_frame_stack :
      forall ms ks,
        memory_stack_frame_stack (add_all_to_heap ms ks) = memory_stack_frame_stack ms.
    Proof.
      intros ms [|a ks]; auto.
      apply add_all_to_heap'_preserves_frame_stack.
    Qed.

    Lemma add_all_to_frame_nil_preserves_frames :
      forall ms,
        memory_stack_frame_stack (add_all_to_frame ms []) = memory_stack_frame_stack ms.
    Proof.
      intros [m fs].
      destruct fs; auto.
    Qed.

    Lemma add_all_to_frame_nil :
      forall ms ms',
        add_all_to_frame ms [] = ms' ->
        ms = ms'.
    Proof.
      (* TODO: move to pre opaque *)
      Transparent add_all_to_frame.
      unfold add_all_to_frame.
      Opaque add_all_to_frame.
      cbn; eauto.
    Qed.

    Lemma add_all_to_frame_cons_inv :
      forall ptr ptrs ms ms'',
        add_all_to_frame ms (ptr :: ptrs) = ms'' ->
        exists ms',
          add_to_frame ms ptr = ms' /\
            add_all_to_frame ms' ptrs = ms''.
    Proof.
      (* TODO: move to pre opaque *)
      Transparent add_all_to_frame.
      unfold add_all_to_frame.
      Opaque add_all_to_frame.
      cbn; eauto.
    Qed.

    Lemma add_all_to_heap'_cons_inv :
      forall ptr ptrs root ms ms'',
        add_all_to_heap' ms root (ptr :: ptrs) = ms'' ->
        exists ms',
          add_to_heap ms root ptr = ms' /\
            add_all_to_heap' ms' root ptrs = ms''.
    Proof.
      cbn; eauto.
    Qed.

    Lemma add_all_to_heap_cons_inv :
      forall ptr ptrs ms ms'',
        add_all_to_heap ms (ptr :: ptrs) = ms'' ->
        exists ms',
          add_to_heap ms ptr ptr = ms' /\
            add_all_to_heap' ms' ptr ptrs = ms''.
    Proof.
      cbn; eauto.
    Qed.

    Lemma add_all_to_frame_cons :
      forall ptr ptrs ms ms' ms'',
        add_to_frame ms ptr = ms' ->
        add_all_to_frame ms' ptrs = ms'' ->
        add_all_to_frame ms (ptr :: ptrs) = ms''.
    Proof.
      (* TODO: move to pre opaque *)
      Transparent add_all_to_frame.
      unfold add_all_to_frame.
      Opaque add_all_to_frame.

      intros ptr ptrs ms ms' ms'' ADD ADD_ALL.
      cbn; subst; eauto.
    Qed.

    Lemma add_all_to_heap_cons :
      forall ptr ptrs root ms ms' ms'',
        add_to_heap ms root ptr = ms' ->
        add_all_to_heap' ms' root ptrs = ms'' ->
        add_all_to_heap' ms root (ptr :: ptrs) = ms''.
    Proof.
      intros ptr ptrs ms ms' ms'' ADD ADD_ALL.
      cbn; subst; eauto.
    Qed.

    Lemma add_to_frame_add_all_to_frame :
      forall ptr ms,
        add_to_frame ms ptr = add_all_to_frame ms [ptr].
    Proof.
      intros ptr ms.
      erewrite add_all_to_frame_cons.
      reflexivity.
      reflexivity.
      symmetry.
      apply add_all_to_frame_nil.
      reflexivity.
    Qed.

    Lemma add_to_heap_add_all_to_heap :
      forall ptr root ms,
        add_to_heap ms root ptr = add_all_to_heap' ms root [ptr].
    Proof.
      intros ptr root ms.
      erewrite add_all_to_heap_cons.
      reflexivity.
      reflexivity.
      symmetry.
      reflexivity.
    Qed.

    Lemma add_to_frame_swap :
      forall ptr1 ptr2 ms ms1' ms2' ms1'' ms2'',
        add_to_frame ms ptr1 = ms1' ->
        add_to_frame ms1' ptr2 = ms1'' ->
        add_to_frame ms ptr2 = ms2' ->
        add_to_frame ms2' ptr1 = ms2'' ->
        frame_stack_eqv (memory_stack_frame_stack ms1'') (memory_stack_frame_stack ms2'').
    Proof.
      intros ptr1 ptr2 ms ms1' ms2' ms1'' ms2'' ADD1 ADD1' ADD2 ADD2'.
      destruct ms, ms1', ms2', ms1'', ms2''.
      cbn in *.
      repeat break_match_hyp; subst;
        inv ADD1; inv ADD1'; inv ADD2; inv ADD2'.

      - unfold frame_stack_eqv.
        intros f n.
        destruct n; cbn; [|tauto].

        split; intros EQV.
        + unfold frame_eqv in *; cbn in *.
          intros ptr; split; firstorder.
        + unfold frame_eqv in *; cbn in *.
          intros ptr; split; firstorder.
      - unfold frame_stack_eqv.
        intros f' n.
        destruct n; cbn; [|tauto].

        split; intros EQV.
        + unfold frame_eqv in *; cbn in *.
          intros ptr; split; firstorder.
        + unfold frame_eqv in *; cbn in *.
          intros ptr; split; firstorder.
    Qed.

    Lemma add_to_heap_swap :
      forall ptr1 ptr2 root ms ms1' ms2' ms1'' ms2'',
        add_to_heap ms root ptr1 = ms1' ->
        add_to_heap ms1' root ptr2 = ms1'' ->
        add_to_heap ms root ptr2 = ms2' ->
        add_to_heap ms2' root ptr1 = ms2'' ->
        heap_eqv (memory_stack_heap ms1'') (memory_stack_heap ms2'').
    Proof.
      intros ptr1 ptr2 root ms ms1' ms2' ms1'' ms2'' ADD1 ADD1' ADD2 ADD2'.
      destruct ms, ms1', ms2', ms1'', ms2''.
      cbn in *.
      repeat break_match_hyp; subst;
        inv ADD1; inv ADD1'; inv ADD2; inv ADD2'.

      - split.
        { intros root'.
          unfold root_in_heap_prop.
          split; intros ROOT.
          - destruct (Z.eq_dec (ptr_to_int root') root) as [EQR | NEQR].
            + subst.
              unfold add_with in *.
              break_inner_match.
              { rewrite IP.F.add_eq_o in *; auto.
                apply member_add_eq.
              }
              { rewrite IP.F.add_eq_o in *; auto.
                apply member_add_eq.
              }
            + unfold add_with in *.
              break_inner_match.
              { rewrite IP.F.add_eq_o in *; auto.
                do 2 apply member_add_preserved.
                do 2 apply member_add_ineq in ROOT; auto.
              }
              { rewrite IP.F.add_eq_o in *; auto.
                do 2 apply member_add_preserved.
                do 2 apply member_add_ineq in ROOT; auto.
              }
          - destruct (Z.eq_dec (ptr_to_int root') root) as [EQR | NEQR].
            + subst.
              unfold add_with in *.
              break_inner_match.
              { rewrite IP.F.add_eq_o in *; auto.
                apply member_add_eq.
              }
              { rewrite IP.F.add_eq_o in *; auto.
                apply member_add_eq.
              }
            + unfold add_with in *.
              break_inner_match.
              { rewrite IP.F.add_eq_o in *; auto.
                do 2 apply member_add_preserved.
                do 2 apply member_add_ineq in ROOT; auto.
              }
              { rewrite IP.F.add_eq_o in *; auto.
                do 2 apply member_add_preserved.
                do 2 apply member_add_ineq in ROOT; auto.
              }
        }

        intros root' a.
        unfold ptr_in_heap_prop in *.
        split; intros EQV.
        + destruct (Z.eq_dec (ptr_to_int root') root) as [EQR | NEQR].
          * subst.
            unfold add_with in *.
            break_inner_match;
              rewrite IP.F.add_eq_o in *; auto;
              rewrite IP.F.add_eq_o in *; auto;
              firstorder.
          * subst.
            unfold add_with in *.
            break_inner_match.
            { rewrite IP.F.add_eq_o in *; auto.
              rewrite IP.F.add_neq_o in *; auto.
              rewrite IP.F.add_neq_o in *; auto.
            }
            { rewrite IP.F.add_eq_o in *; auto.
              rewrite IP.F.add_neq_o in *; auto.
              rewrite IP.F.add_neq_o in *; auto.
            }
        + destruct (Z.eq_dec (ptr_to_int root') root) as [EQR | NEQR].
          * subst.
            unfold add_with in *.
            break_inner_match;
              rewrite IP.F.add_eq_o in *; auto;
              rewrite IP.F.add_eq_o in *; auto;
              firstorder.
          * subst.
            unfold add_with in *.
            break_inner_match.
            { rewrite IP.F.add_eq_o in *; auto.
              rewrite IP.F.add_neq_o in *; auto.
              rewrite IP.F.add_neq_o in *; auto.
            }
            { rewrite IP.F.add_eq_o in *; auto.
              rewrite IP.F.add_neq_o in *; auto.
              rewrite IP.F.add_neq_o in *; auto.
            }
    Qed.

    (* TODO: move this *)
    #[global] Instance ptr_in_frame_prop_int_Proper :
      Proper (frame_eqv ==> (fun a b => ptr_to_int a = ptr_to_int b) ==> iff) ptr_in_frame_prop.
    Proof.
      unfold Proper, respectful.
      intros x y XY a b AB.
      unfold frame_eqv in *.
      unfold ptr_in_frame_prop in *.
      rewrite AB; auto.
    Qed.

    #[global] Instance ptr_in_frame_prop_Proper :
      Proper (frame_eqv ==> eq ==> iff) ptr_in_frame_prop.
    Proof.
      unfold Proper, respectful.
      intros x y XY a b AB; subst.
      unfold frame_eqv in *.
      auto.
    Qed.

    #[global] Instance frame_stack_eqv_add_ptr_to_frame_Proper :
      Proper (frame_eqv ==> eq ==> frame_eqv ==> iff) add_ptr_to_frame.
    Proof.
      unfold Proper, respectful.
      intros x y XY ptr ptr' TU r s RS; subst.

      split; intros ADD.
      - (* unfold frame_stack_eqv in *. *)
        (* unfold FSNth_eqv in *. *)
        inv ADD.
        split.
        + intros ptr'0 DISJOINT.
          split; intros IN.
          * rewrite <- RS.
            apply old_frame_lu0; eauto.
            rewrite XY.
            auto.
          * rewrite <- XY.
            apply old_frame_lu0; eauto.
            rewrite RS.
            auto.
        + rewrite <- RS.
          auto.
      - inv ADD.
        split.
        + intros ptr'0 DISJOINT.
          split; intros IN.
          * rewrite RS.
            apply old_frame_lu0; eauto.
            rewrite <- XY.
            auto.
          * rewrite XY.
            apply old_frame_lu0; eauto.
            rewrite <- RS.
            auto.
        + rewrite RS.
          auto.
    Qed.

    #[global] Instance frame_stack_eqv_add_ptr_to_frame_stack_Proper :
      Proper (frame_stack_eqv ==> eq ==> frame_stack_eqv ==> iff) add_ptr_to_frame_stack.
    Proof.
      unfold Proper, respectful.
      intros x y XY ptr ptr' TU r s RS; subst.

      split; intros ADD.
      - (* unfold frame_stack_eqv in *. *)
        (* unfold FSNth_eqv in *. *)

        unfold add_ptr_to_frame_stack in ADD.
        unfold add_ptr_to_frame_stack.
        intros f PEEK.

        rewrite <- XY in PEEK.
        specialize (ADD f PEEK).
        destruct ADD as [f' [ADD [PEEK' POP]]].
        eexists.
        split; eauto.
        split; [rewrite <- RS; eauto|].

        intros fs1_pop.
        rewrite <- XY.
        rewrite <- RS.
        auto.
      - unfold add_ptr_to_frame_stack in ADD.
        unfold add_ptr_to_frame_stack.
        intros f PEEK.

        rewrite XY in PEEK.
        specialize (ADD f PEEK).
        destruct ADD as [f' [ADD [PEEK' POP]]].
        eexists.
        split; eauto.
        split; [rewrite RS; eauto|].

        intros fs1_pop.
        rewrite XY.
        rewrite RS.
        auto.
    Qed.

    #[global] Instance heap_eqv_ptr_in_head_prop_Proper :
      Proper (heap_eqv ==> eq ==> eq ==> iff) ptr_in_heap_prop.
    Proof.
      unfold Proper, respectful.
      intros x y XY root root' EQR ptr ptr' EQPTR; subst.
      rewrite XY.
      reflexivity.
    Qed.

    #[global] Instance heap_eqv_add_ptr_to_heap_Proper :
      Proper (heap_eqv ==> eq ==> eq ==> heap_eqv ==> iff) add_ptr_to_heap.
    Proof.
      unfold Proper, respectful.
      intros x y XY root root' EQR ptr ptr' EQPTR r s RS; subst.

      split; intros ADD.
      - (* unfold heap_eqv in *. *)
        (* unfold FSNth_eqv in *. *)
        destruct ADD as [OLD NEW].
        split.
        + intros ptr'0 DISJOINT root.
          rewrite <- RS.
          rewrite <- XY.
          auto.
        + intros root'0 DISJOINT ptr'0.
          rewrite <- RS.
          rewrite <- XY.
          auto.
        + intros ptr'0 DISJOINT.
          rewrite <- RS.
          rewrite <- XY.
          auto.
        + rewrite <- RS.
          auto.
        + rewrite <- RS.
          auto.
      - destruct ADD as [OLD NEW].
        split.
        + intros ptr'0 DISJOINT root.
          rewrite RS.
          rewrite XY.
          auto.
        + intros ptr'0 DISJOINT root.
          rewrite RS.
          rewrite XY.
          auto.
        + intros root'0 DISJOINT.
          rewrite XY.
          rewrite RS.
          auto.
        + rewrite RS.
          auto.
        + rewrite RS.
          auto.
    Qed.

    #[global] Instance frame_stack_eqv_add_ptrs_to_frame_stack_Proper :
      Proper (frame_stack_eqv ==> eq ==> frame_stack_eqv ==> iff) add_ptrs_to_frame_stack.
    Proof.
      unfold Proper, respectful.
      intros x y XY ptrs ptrs' TU r s RS; subst.

      split; intros ADD.
      - revert x y XY r s RS ADD.
        induction ptrs' as [|a ptrs];
          intros x y XY r s RS ADD;
          subst.
        + cbn in *; subst.
          rewrite <- XY.
          rewrite <- RS.
          auto.
        + cbn in *.
          destruct ADD as [fs' [ADDPTRS ADD]].
          eexists.
          rewrite <- RS; split; eauto.

          eapply IHptrs; eauto.
          reflexivity.
      - revert x y XY r s RS ADD.
        induction ptrs' as [|a ptrs];
          intros x y XY r s RS ADD;
          subst.
        + cbn in *; subst.
          rewrite XY.
          rewrite RS.
          auto.
        + cbn in *.
          destruct ADD as [fs' [ADDPTRS ADD]].
          eexists.
          rewrite RS; split; eauto.

          eapply IHptrs; eauto.
          reflexivity.
    Qed.

    #[global] Instance heap_eqv_add_ptrs_to_heap'_Proper :
      Proper (heap_eqv ==> eq ==> eq ==> heap_eqv ==> iff) add_ptrs_to_heap'.
    Proof.
      unfold Proper, respectful.
      intros x y XY root root' ROOTS ptrs ptrs' TU r s RS; subst.

      split; intros ADD.
      - revert x y XY r s RS ADD.
        induction ptrs' as [|a ptrs];
          intros x y XY r s RS ADD;
          subst.
        + cbn in *; subst.
          rewrite <- XY.
          rewrite <- RS.
          auto.
        + cbn in *.
          destruct ADD as [h' [ADDPTRS ADD]].
          eexists.
          rewrite <- RS; split; eauto.

          eapply IHptrs; eauto.
          reflexivity.
      - revert x y XY r s RS ADD.
        induction ptrs' as [|a ptrs];
          intros x y XY r s RS ADD;
          subst.
        + cbn in *; subst.
          rewrite XY.
          rewrite RS.
          auto.
        + cbn in *.
          destruct ADD as [h' [ADDPTRS ADD]].
          eexists.
          rewrite RS; split; eauto.

          eapply IHptrs; eauto.
          reflexivity.
    Qed.

    #[global] Instance heap_eqv_add_ptrs_to_heap_Proper :
      Proper (heap_eqv ==> eq ==> heap_eqv ==> iff) add_ptrs_to_heap.
    Proof.
      unfold Proper, respectful.
      intros x y XY ptrs ptrs' TU r s RS; subst.
      destruct ptrs'.
      - cbn. rewrite XY, RS.
        reflexivity.
      - unfold add_ptrs_to_heap.
        rewrite XY, RS.
        reflexivity.
    Qed.

    (* TODO: move this? *)
    Lemma disjoint_ptr_byte_dec :
      forall p1 p2,
        {disjoint_ptr_byte p1 p2} + { ~ disjoint_ptr_byte p1 p2}.
    Proof.
      intros p1 p2.
      unfold disjoint_ptr_byte.
      pose proof Z.eq_dec (ptr_to_int p1) (ptr_to_int p2) as [EQ | NEQ].
      - rewrite EQ.
        right.
        intros CONTRA.
        contradiction.
      - left; auto.
    Qed.

    Lemma add_ptr_to_frame_inv :
      forall ptr ptr' f f',
        add_ptr_to_frame f ptr f' ->
        ptr_in_frame_prop f' ptr' ->
        ptr_in_frame_prop f ptr' \/ ptr_to_int ptr = ptr_to_int ptr'.
    Proof.
      intros ptr ptr' f f' F F'.
      inv F.
      pose proof disjoint_ptr_byte_dec ptr ptr' as [DISJOINT | NDISJOINT].
      - specialize (old_frame_lu0 _ DISJOINT).
        left.
        apply old_frame_lu0; auto.
      - unfold disjoint_ptr_byte in NDISJOINT.
        assert (ptr_to_int ptr = ptr_to_int ptr') as EQ by lia.
        right; auto.
    Qed.

    Lemma add_ptr_to_heap_inv :
      forall ptr ptr' root root' f f',
        add_ptr_to_heap f root ptr f' ->
        ptr_in_heap_prop f' root' ptr' ->
        ptr_in_heap_prop f root' ptr' \/ (ptr_to_int ptr = ptr_to_int ptr' /\ ptr_to_int root = ptr_to_int root').
    Proof.
      intros ptr ptr' root root' f f' F F'.
      inv F.
      pose proof disjoint_ptr_byte_dec ptr ptr' as [DISJOINT | NDISJOINT].
      - specialize (old_heap_lu0 _ DISJOINT).
        left.
        apply old_heap_lu0; auto.
      - unfold disjoint_ptr_byte in NDISJOINT.
        assert (ptr_to_int ptr = ptr_to_int ptr') as EQ by lia.
        pose proof disjoint_ptr_byte_dec root root' as [DISJOINT' | NDISJOINT'].
        + left.
          apply old_heap_lu_different_root0; auto.
        + unfold disjoint_ptr_byte in NDISJOINT'.
          assert (ptr_to_int root = ptr_to_int root') as EQR by lia.
          right; firstorder.
    Qed.

    Lemma add_ptr_to_frame_eqv :
      forall ptr f f1 f2,
        add_ptr_to_frame f ptr f1 ->
        add_ptr_to_frame f ptr f2 ->
        frame_eqv f1 f2.
    Proof.
      intros ptr f f1 f2 F1 F2.
      unfold frame_eqv.
      intros ptr0.
      split; intros IN.
      - eapply add_ptr_to_frame_inv in IN; eauto.
        destruct IN as [IN | IN].
        + destruct F2.
          pose proof disjoint_ptr_byte_dec ptr ptr0 as [DISJOINT | NDISJOINT].
          * eapply old_frame_lu0; eauto.
          * unfold disjoint_ptr_byte in NDISJOINT.
            assert (ptr_to_int ptr = ptr_to_int ptr0) as EQ by lia.
            unfold ptr_in_frame_prop in *.
            rewrite <- EQ.
            auto.
        + destruct F2.
          unfold ptr_in_frame_prop in *.
          rewrite <- IN.
          auto.
      - eapply add_ptr_to_frame_inv in IN; eauto.
        destruct IN as [IN | IN].
        + destruct F1.
          pose proof disjoint_ptr_byte_dec ptr ptr0 as [DISJOINT | NDISJOINT].
          * eapply old_frame_lu0; eauto.
          * unfold disjoint_ptr_byte in NDISJOINT.
            assert (ptr_to_int ptr = ptr_to_int ptr0) as EQ by lia.
            unfold ptr_in_frame_prop in *.
            rewrite <- EQ.
            auto.
        + destruct F1.
          unfold ptr_in_frame_prop in *.
          rewrite <- IN.
          auto.
    Qed.

    Lemma add_ptr_to_frame_stack_eqv_S :
      forall ptr f f' fs fs',
        add_ptr_to_frame_stack (Snoc fs f) ptr (Snoc fs' f') ->
        add_ptr_to_frame f ptr f' /\ frame_stack_eqv fs fs'.
    Proof.
      intros ptr f f' fs fs' ADD.
      unfold add_ptr_to_frame_stack in *.
      specialize (ADD f).
      forward ADD; [cbn; reflexivity|].
      destruct ADD as [f1 [ADD [PEEK POP]]].
      cbn in PEEK.
      split.
      - rewrite PEEK in ADD; auto.
      - cbn in POP.
        specialize (POP fs').
        apply POP; reflexivity.
    Qed.

    Lemma add_ptr_to_frame_stack_eqv :
      forall ptr fs fs1 fs2,
        add_ptr_to_frame_stack fs ptr fs1 ->
        add_ptr_to_frame_stack fs ptr fs2 ->
        frame_stack_eqv fs1 fs2.
    Proof.
      intros ptr fs fs1 fs2 F1 F2.
      unfold add_ptr_to_frame_stack in *.
      intros f n.

      revert ptr f n fs fs2 F1 F2.
      induction fs1 as [f1 | fs1 IHF1 f1];
        intros ptr f n fs fs2 F1 F2;
        destruct fs2 as [f2 | fs2 f2].

      - cbn. destruct n; [|reflexivity].
        destruct fs as [f' | fs' f'].
        + specialize (F1 f').
          forward F1; [cbn; reflexivity|].
          destruct F1 as [f1' [ADD1 [PEEK1 POP1]]].

          specialize (F2 f').
          forward F2; [cbn; reflexivity|].
          destruct F2 as [f2' [ADD2 [PEEK2 POP2]]].

          cbn in *.
          pose proof (add_ptr_to_frame_eqv _ _ _ _ ADD1 ADD2) as EQV12.

          rewrite <- PEEK1.
          rewrite <- PEEK2.
          rewrite EQV12.
          reflexivity.
        + specialize (F1 f').
          forward F1; [cbn; reflexivity|].
          destruct F1 as [f1' [ADD1 [PEEK1 POP1]]].

          specialize (F2 f').
          forward F2; [cbn; reflexivity|].
          destruct F2 as [f2' [ADD2 [PEEK2 POP2]]].

          cbn in *.
          pose proof (add_ptr_to_frame_eqv _ _ _ _ ADD1 ADD2) as EQV12.

          rewrite <- PEEK1.
          rewrite <- PEEK2.
          rewrite EQV12.
          reflexivity.
      - destruct fs as [f' | fs' f'].
        + specialize (F2 f').
          forward F2; [cbn; reflexivity|].
          destruct F2 as [f2' [ADD2 [PEEK2 POP2]]].

          cbn in *.
          exfalso; eapply POP2; reflexivity.
        + specialize (F1 f').
          forward F1; [cbn; reflexivity|].
          destruct F1 as [f1' [ADD1 [PEEK1 POP1]]].

          cbn in *.
          exfalso; eapply POP1; reflexivity.
      - destruct fs as [f' | fs' f'].
        + specialize (F1 f').
          forward F1; [cbn; reflexivity|].
          destruct F1 as [f1' [ADD1 [PEEK1 POP1]]].

          cbn in *.
          exfalso; eapply POP1; reflexivity.
        + specialize (F2 f').
          forward F2; [cbn; reflexivity|].
          destruct F2 as [f2' [ADD2 [PEEK2 POP2]]].

          cbn in *.
          exfalso; eapply POP2; reflexivity.
      - destruct fs as [f' | fs' f'].
        + specialize (F1 f').
          forward F1; [cbn; reflexivity|].
          destruct F1 as [f1' [ADD1 [PEEK1 POP1]]].

          cbn in *.
          exfalso; eapply POP1; reflexivity.
        + specialize (F1 f').
          forward F1; [cbn; reflexivity|].
          destruct F1 as [f1' [ADD1 [PEEK1 POP1]]].

          specialize (F2 f').
          forward F2; [cbn; reflexivity|].
          destruct F2 as [f2' [ADD2 [PEEK2 POP2]]].

          pose proof (add_ptr_to_frame_eqv _ _ _ _ ADD1 ADD2) as EQV12.

          cbn in *.
          destruct n.
          * rewrite <- PEEK1.
            rewrite <- PEEK2.
            rewrite EQV12; reflexivity.
          * eapply POP1.
            eapply POP2.
            reflexivity.
    Qed.

    Lemma add_ptrs_to_frame_eqv :
      forall ptrs fs fs1 fs2,
        add_ptrs_to_frame_stack fs ptrs fs1 ->
        add_ptrs_to_frame_stack fs ptrs fs2 ->
        frame_stack_eqv fs1 fs2.
    Proof.
      induction ptrs;
        intros fs fs1 fs2 ADD1 ADD2.
      - cbn in *.
        rewrite <- ADD1, ADD2.
        reflexivity.
      - cbn in *.
        destruct ADD1 as [fs1' [ADDPTRS1 ADD1]].
        destruct ADD2 as [fs2' [ADDPTRS2 ADD2]].

        pose proof (IHptrs _ _ _ ADDPTRS1 ADDPTRS2) as EQV.

        eapply add_ptr_to_frame_stack_eqv; eauto.
        rewrite EQV.
        auto.
    Qed.

    Lemma add_ptr_to_heap_eqv :
      forall ptr root h h1 h2,
        add_ptr_to_heap h root ptr h1 ->
        add_ptr_to_heap h root ptr h2 ->
        heap_eqv h1 h2.
    Proof.
      intros ptr root h h1 h2 H1 H2.
      split.
      { intros root0.
        split; intros ROOT.
        - inv H1; inv H2.
          pose proof disjoint_ptr_byte_dec root root0 as [DISJOINT | NDISJOINT].
          + eapply old_heap_roots1; eauto.
            eapply old_heap_roots0; eauto.
          + unfold disjoint_ptr_byte in NDISJOINT.
            assert (ptr_to_int root = ptr_to_int root0) as EQR by lia.
            unfold root_in_heap_prop in *.
            rewrite EQR in *.
            eapply new_heap_root1.
        - inv H1; inv H2.
          pose proof disjoint_ptr_byte_dec root root0 as [DISJOINT | NDISJOINT].
          + eapply old_heap_roots0; eauto.
            eapply old_heap_roots1; eauto.
          + unfold disjoint_ptr_byte in NDISJOINT.
            assert (ptr_to_int root = ptr_to_int root0) as EQR by lia.
            unfold root_in_heap_prop in *.
            rewrite EQR in *.
            eapply new_heap_root0.
      }

      intros root0 ptr0.
      split; intros IN.
      - eapply add_ptr_to_heap_inv with (f := h) (ptr := ptr) (root := root) in IN.
        + inv H1.
          inv H2.
          destruct IN as [IN | [IN1 IN2]].
          * pose proof disjoint_ptr_byte_dec root root0 as [DISJOINT | NDISJOINT].
            -- eapply old_heap_lu_different_root1; eauto.
            -- pose proof disjoint_ptr_byte_dec ptr ptr0 as [DISJOINT' | NDISJOINT'].
               ++ eapply old_heap_lu1; eauto.
               ++ unfold disjoint_ptr_byte in NDISJOINT'.
                  assert (ptr_to_int ptr = ptr_to_int ptr0) as EQ by lia.

                  unfold disjoint_ptr_byte in NDISJOINT.
                  assert (ptr_to_int root = ptr_to_int root0) as EQR by lia.

                  unfold ptr_in_heap_prop in *.
                  rewrite EQ in *.
                  rewrite EQR in *.
                  auto.
          * unfold ptr_in_heap_prop in *.
            rewrite IN1 in *.
            rewrite IN2 in *.
            auto.
        + auto.
      - eapply add_ptr_to_heap_inv with (f := h) (ptr := ptr) (root := root) in IN.
        + inv H1.
          inv H2.
          destruct IN as [IN | [IN1 IN2]].
          * pose proof disjoint_ptr_byte_dec root root0 as [DISJOINT | NDISJOINT].
            -- eapply old_heap_lu_different_root0; eauto.
            -- pose proof disjoint_ptr_byte_dec ptr ptr0 as [DISJOINT' | NDISJOINT'].
               ++ eapply old_heap_lu0; eauto.
               ++ unfold disjoint_ptr_byte in NDISJOINT'.
                  assert (ptr_to_int ptr = ptr_to_int ptr0) as EQ by lia.

                  unfold disjoint_ptr_byte in NDISJOINT.
                  assert (ptr_to_int root = ptr_to_int root0) as EQR by lia.

                  unfold ptr_in_heap_prop in *.
                  rewrite EQ in *.
                  rewrite EQR in *.
                  auto.
          * unfold ptr_in_heap_prop in *.
            rewrite IN1 in *.
            rewrite IN2 in *.
            auto.
        + auto.
    Qed.

    Lemma add_ptrs_to_heap_eqv :
      forall ptrs root h h1 h2,
        add_ptrs_to_heap' h root ptrs h1 ->
        add_ptrs_to_heap' h root ptrs h2 ->
        heap_eqv h1 h2.
    Proof.
      induction ptrs;
        intros root h h1 h2 ADD1 ADD2.
      - cbn in *.
        rewrite <- ADD1, ADD2.
        reflexivity.
      - cbn in *.
        destruct ADD1 as [h1' [ADDPTRS1 ADD1]].
        destruct ADD2 as [h2' [ADDPTRS2 ADD2]].

        pose proof (IHptrs _ _ _ _ ADDPTRS1 ADDPTRS2) as EQV.

        eapply add_ptr_to_heap_eqv; eauto.
        rewrite EQV.
        auto.
    Qed.


    #[global] Instance frame_stack_eqv_add_all_to_frame :
      Proper ((fun ms1 ms2 => frame_stack_eqv (memory_stack_frame_stack ms1) (memory_stack_frame_stack ms2)) ==> eq ==> (fun ms1 ms2 => frame_stack_eqv (memory_stack_frame_stack ms1) (memory_stack_frame_stack ms2))) add_all_to_frame.
    Proof.
      unfold Proper, respectful.
      intros ms1 ms2 EQV y x EQ; subst.

      revert ms1 ms2 EQV.
      induction x; intros ms1 ms2 EQV.
      Transparent add_all_to_frame.
      unfold add_all_to_frame.
      cbn in *.
      auto.
      Opaque add_all_to_frame.

      assert (add_all_to_frame ms1 (a :: x) = add_all_to_frame ms1 (a :: x)) as EQ by reflexivity.
      pose proof (@add_all_to_frame_cons_inv _ _ _ _ EQ)
        as [ms' [ADD ADD_ALL]].

      assert (add_all_to_frame ms2 (a :: x) = add_all_to_frame ms2 (a :: x)) as EQ2 by reflexivity.
      pose proof (@add_all_to_frame_cons_inv _ _ _ _ EQ2)
        as [ms2' [ADD2 ADD_ALL2]].
      cbn in *.

      unfold add_to_frame in *.
      destruct ms1 as [m1 fs1].
      destruct ms2 as [m2 fs2].

      subst.

      cbn in EQV.

      pose proof (frame_stack_inv _ _ EQV) as [SNOC | SING].
      - destruct SNOC as [fs1' [fs2' [f1 [f2 [SNOC1 [SNOC2 [SEQV FEQV]]]]]]].
        subst.

        rewrite <- ADD_ALL.
        rewrite <- ADD_ALL2.

        eapply IHx.
        cbn.
        unfold frame_stack_eqv.
        intros f n.
        destruct n.
        + cbn. rewrite FEQV. reflexivity.
        + cbn. auto.
      - destruct SING as [f1 [f2 [SING1 [SING2 FEQV]]]].
        subst.

        rewrite <- ADD_ALL.
        rewrite <- ADD_ALL2.

        eapply IHx.
        cbn.
        unfold frame_stack_eqv.
        intros f n.
        destruct n.
        + cbn. rewrite FEQV. reflexivity.
        + cbn. tauto.
    Qed.

    #[global] Instance heap_eqv_add_with :
      Proper (eq ==> eq ==> heap_eqv ==> heap_eqv) (fun root a => add_with root a ret cons).
    Proof.
      unfold Proper, respectful.
      intros a b EQKEY p1 p2 EQPTR h1 h2 EQHEAP; subst.
      unfold add_with.
      split.
      { intros root.
        inv EQHEAP.
        unfold root_in_heap_prop in *.
        break_match;
          break_match.
        - destruct (Z.eq_dec (ptr_to_int root ) b) as [EQR | NEQR]; subst.
          + split; intros ROOT; apply member_add_eq.
          + split; intros ROOT;
              apply member_add_ineq in ROOT; auto;
              apply member_add_preserved; firstorder.
        - destruct (Z.eq_dec (ptr_to_int root ) b) as [EQR | NEQR]; subst.
          + split; intros ROOT; apply member_add_eq.
          + split; intros ROOT;
              apply member_add_ineq in ROOT; auto;
              apply member_add_preserved; firstorder.
        - destruct (Z.eq_dec (ptr_to_int root ) b) as [EQR | NEQR]; subst.
          + split; intros ROOT; apply member_add_eq.
          + split; intros ROOT;
              apply member_add_ineq in ROOT; auto;
              apply member_add_preserved; firstorder.
        - destruct (Z.eq_dec (ptr_to_int root ) b) as [EQR | NEQR]; subst.
          + split; intros ROOT; apply member_add_eq.
          + split; intros ROOT;
              apply member_add_ineq in ROOT; auto;
              apply member_add_preserved; firstorder.
      }

      destruct EQHEAP as [_ EQHEAP].
      unfold ptr_in_heap_prop in *.
      cbn in *.
      intros root ptr.

      destruct (Z.eq_dec (ptr_to_int root ) b) as [EQR | NEQR].
      - subst.
        pose proof (EQHEAP root ptr) as EQROOT.

        break_inner_match.
        { rewrite IP.F.add_eq_o in *; auto.
          break_inner_match.
          { rewrite IP.F.add_eq_o in *; auto.
            setoid_rewrite Heqo in EQROOT.
            setoid_rewrite Heqo0 in EQROOT.
            firstorder.
          }

          { rewrite IP.F.add_eq_o in *; auto.
            setoid_rewrite Heqo in EQROOT.
            setoid_rewrite Heqo0 in EQROOT.
            firstorder.
          }
        }
        { rewrite IP.F.add_eq_o in *; auto.
          break_inner_match.
          { rewrite IP.F.add_eq_o in *; auto.
            setoid_rewrite Heqo in EQROOT.
            setoid_rewrite Heqo0 in EQROOT.
            firstorder.
          }

          { rewrite IP.F.add_eq_o in *; auto.
            setoid_rewrite Heqo in EQROOT.
            setoid_rewrite Heqo0 in EQROOT.
            firstorder.
          }
        }
      - subst.
        pose proof (EQHEAP root ptr) as EQROOT.

        break_inner_match.
        { rewrite IP.F.add_neq_o in *; auto.
          destruct (IM.find (elt:=list Iptr) b h2) eqn:Heqo0.
          rewrite IP.F.add_neq_o in *; auto.
          rewrite IP.F.add_neq_o in *; auto.
        }
        { rewrite IP.F.add_neq_o in *; auto.
          destruct (IM.find (elt:=list Iptr) b h2) eqn:Heqo0.
          rewrite IP.F.add_neq_o in *; auto.
          rewrite IP.F.add_neq_o in *; auto.
        }
    Qed.

    #[global] Instance heap_eqv_add_all_to_heap :
      Proper ((fun ms1 ms2 => heap_eqv (memory_stack_heap ms1) (memory_stack_heap ms2)) ==> eq ==> eq ==> (fun ms1 ms2 => heap_eqv (memory_stack_heap ms1) (memory_stack_heap ms2))) add_all_to_heap'.
    Proof.
      unfold Proper, respectful.
      intros ms1 ms2 EQV y x EQ z w EQ'; subst.

      revert ms1 ms2 x EQV.
      induction w; intros ms1 ms2 x EQV.
      Transparent add_all_to_heap.
      unfold add_all_to_heap.
      cbn in *.
      auto.
      Opaque add_all_to_heap.

      rename x into root.
      rename w into x.

      assert (add_all_to_heap' ms1 root (a :: x) = add_all_to_heap' ms1 root (a :: x)) as EQ by reflexivity.
      pose proof (@add_all_to_heap'_cons_inv _ _ _ _ _ EQ)
        as [ms' [ADD ADD_ALL]].

      assert (add_all_to_heap' ms2 root (a :: x) = add_all_to_heap' ms2 root (a :: x)) as EQ2 by reflexivity.
      pose proof (@add_all_to_heap'_cons_inv _ _ _ _ _ EQ2)
        as [ms2' [ADD2 ADD_ALL2]].
      cbn in *.

      unfold add_to_heap in *.
      destruct ms1 as [m1 fs1 h1].
      destruct ms2 as [m2 fs2 h2].

      subst.

      cbn in EQV.
      Transparent add_all_to_heap.
      cbn in *.
      Opaque add_all_to_heap.

      rewrite <- ADD_ALL.
      rewrite <- ADD_ALL2.

      eapply IHw.
      cbn.
      eapply heap_eqv_add_with; eauto.
    Qed.

    (* TODO: move *)
    #[global] Instance snoc_Proper :
      Proper (frame_stack_eqv ==> frame_eqv ==> frame_stack_eqv) Snoc.
    Proof.
      unfold Proper, respectful.
      intros x y XY f f' FF.
      red.
      intros f0 n.
      destruct n.
      - cbn.
        rewrite FF.
        reflexivity.
      - cbn.
        apply XY.
    Qed.

    (* TODO: move *)
    #[global] Instance push_frame_stack_spec_Proper :
      Proper (frame_stack_eqv ==> frame_eqv ==> frame_stack_eqv ==> iff) push_frame_stack_spec.
    Proof.
      unfold Proper, respectful.
      intros x y XY f f' TU r s RS; subst.

      split; intros ADD.
      - inv ADD.
        split.
        + rewrite <- RS.
          rewrite <- XY.
          auto.
        + rewrite <- RS.
          rewrite <- TU.
          auto.
      - inv ADD.
        split.
        + rewrite RS.
          rewrite XY.
          auto.
        + rewrite RS.
          rewrite TU.
          auto.
    Qed.

    #[global] Instance member_ptr_to_int_heap_eqv_Proper :
      Proper ((fun p1 p2 => ptr_to_int p1 = ptr_to_int p2) ==> heap_eqv ==> iff) (fun p => member (ptr_to_int p)).
    Proof.
      intros p1 p2 PTREQ h1 h2 HEAPEQ; subst.
      inv HEAPEQ.
      unfold root_in_heap_prop in *.
      rewrite PTREQ.
      auto.
    Qed.

    Lemma add_all_to_frame_cons_swap :
      forall ptrs ptr ms ms1' ms1'' ms2' ms2'',
        (* Add individual pointer first *)
        add_to_frame ms ptr = ms1' ->
        add_all_to_frame ms1' ptrs = ms1'' ->

        (* Add ptrs first *)
        add_all_to_frame ms ptrs = ms2' ->
        add_to_frame ms2' ptr = ms2'' ->

        frame_stack_eqv (memory_stack_frame_stack ms1'') (memory_stack_frame_stack ms2'').
    Proof.
      induction ptrs;
        intros ptr ms ms1' ms1'' ms2' ms2'' ADD ADD_ALL ADD_ALL' ADD'.

      rewrite add_to_frame_add_all_to_frame in *.

      - apply add_all_to_frame_nil in ADD_ALL, ADD_ALL'; subst.
        reflexivity.
      - apply add_all_to_frame_cons_inv in ADD_ALL, ADD_ALL'.
        destruct ADD_ALL as [msx [ADDx ADD_ALLx]].
        destruct ADD_ALL' as [msy [ADDy ADD_ALLy]].

        subst.

        (* ms + ptr + a ++ ptrs *)
        (* ms + a ++ ptrs + ptr *)

        (* ptrs ++ (a :: (ptr :: ms))

                         vs

                         ptr :: (ptrs ++ (a :: ms))

                         I have a lemma that's basically...

                         (ptrs ++ (ptr :: ms)) = (ptr :: (ptrs ++ ms))

                         ptr is generic, ptrs is fixed.

                         Can get...

                         ptrs ++ (a :: (ptr :: ms))
                         a :: (ptrs ++ (ptr :: ms))

                         and then

                         ptr :: (ptrs ++ (a :: ms))
                         ptrs ++ (ptr :: (a :: ms))
                         ptrs ++ (a :: (ptr :: ms))
                         a :: (ptrs ++ (ptr :: ms))
         *)

        (*
                         ptrs ++ (a :: (ptr :: ms))
                         a :: (ptrs ++ (ptr :: ms))
         *)

        assert (frame_stack_eqv
                  (memory_stack_frame_stack (add_all_to_frame (add_to_frame (add_to_frame ms ptr) a) ptrs))
                  (memory_stack_frame_stack (add_to_frame (add_all_to_frame (add_to_frame ms ptr) ptrs) a))) as EQ1.
        { eauto.
        }

        rewrite EQ1.

        assert (frame_stack_eqv
                  (memory_stack_frame_stack (add_to_frame (add_all_to_frame (add_to_frame ms a) ptrs) ptr))
                  (memory_stack_frame_stack (add_to_frame (add_all_to_frame (add_to_frame ms ptr) ptrs) a))) as EQ2.
        { assert (frame_stack_eqv
                    (memory_stack_frame_stack (add_to_frame (add_all_to_frame (add_to_frame ms a) ptrs) ptr))
                    (memory_stack_frame_stack (add_all_to_frame (add_to_frame (add_to_frame ms a) ptr) ptrs))) as EQ.
          { symmetry; eauto.
          }

          rewrite EQ.
          clear EQ.

          assert (frame_stack_eqv
                    (memory_stack_frame_stack (add_to_frame (add_to_frame ms a) ptr))
                    (memory_stack_frame_stack (add_to_frame (add_to_frame ms ptr) a))) as EQ.
          {
            eapply add_to_frame_swap; eauto.
          }

          epose proof frame_stack_eqv_add_all_to_frame (add_to_frame (add_to_frame ms a) ptr) (add_to_frame (add_to_frame ms ptr) a) as EQ'.
          forward EQ'. apply EQ.
          red in EQ'.
          specialize (EQ' ptrs ptrs eq_refl).
          rewrite EQ'.

          eauto.
        }

        rewrite EQ2.

        reflexivity.
    Qed.

    Lemma add_all_to_heap'_cons_swap :
      forall ptrs ptr root ms ms1' ms1'' ms2' ms2'',
        (* Add individual pointer first *)
        add_to_heap ms root ptr = ms1' ->
        add_all_to_heap' ms1' root ptrs = ms1'' ->

        (* Add ptrs first *)
        add_all_to_heap' ms root ptrs = ms2' ->
        add_to_heap ms2' root ptr = ms2'' ->

        heap_eqv (memory_stack_heap ms1'') (memory_stack_heap ms2'').
    Proof.
      induction ptrs;
        intros ptr root ms ms1' ms1'' ms2' ms2'' ADD ADD_ALL ADD_ALL' ADD'.

      rewrite add_to_heap_add_all_to_heap in *.

      - cbn in ADD_ALL, ADD_ALL'; subst.
        reflexivity.
      - apply add_all_to_heap'_cons_inv in ADD_ALL, ADD_ALL'.
        destruct ADD_ALL as [msx [ADDx ADD_ALLx]].
        destruct ADD_ALL' as [msy [ADDy ADD_ALLy]].

        subst.

        (* ms + ptr + a ++ ptrs *)
        (* ms + a ++ ptrs + ptr *)

        (* ptrs ++ (a :: (ptr :: ms))

                         vs

                         ptr :: (ptrs ++ (a :: ms))

                         I have a lemma that's basically...

                         (ptrs ++ (ptr :: ms)) = (ptr :: (ptrs ++ ms))

                         ptr is generic, ptrs is fixed.

                         Can get...

                         ptrs ++ (a :: (ptr :: ms))
                         a :: (ptrs ++ (ptr :: ms))

                         and then

                         ptr :: (ptrs ++ (a :: ms))
                         ptrs ++ (ptr :: (a :: ms))
                         ptrs ++ (a :: (ptr :: ms))
                         a :: (ptrs ++ (ptr :: ms))
         *)

        (*
                         ptrs ++ (a :: (ptr :: ms))
                         a :: (ptrs ++ (ptr :: ms))
         *)

        assert (heap_eqv
                  (memory_stack_heap (add_all_to_heap' (add_to_heap (add_to_heap ms root ptr) root a) root ptrs))
                  (memory_stack_heap (add_to_heap (add_all_to_heap' (add_to_heap ms root ptr) root ptrs) root a))) as EQ1.
        { eauto.
        }

        rewrite EQ1.

        assert (heap_eqv
                  (memory_stack_heap (add_to_heap (add_all_to_heap' (add_to_heap ms root a) root ptrs) root ptr))
                  (memory_stack_heap (add_to_heap (add_all_to_heap' (add_to_heap ms root ptr) root ptrs) root a))) as EQ2.
        { assert (heap_eqv
                    (memory_stack_heap (add_to_heap (add_all_to_heap' (add_to_heap ms root a) root ptrs) root ptr))
                    (memory_stack_heap (add_all_to_heap' (add_to_heap (add_to_heap ms root a) root ptr) root ptrs))) as EQ.
          { symmetry; eauto.
          }

          rewrite EQ.
          clear EQ.

          assert (heap_eqv
                    (memory_stack_heap (add_to_heap (add_to_heap ms root a) root ptr))
                    (memory_stack_heap (add_to_heap (add_to_heap ms root ptr) root a))) as EQ.
          {
            eapply add_to_heap_swap; eauto.
          }

          epose proof heap_eqv_add_all_to_heap (add_to_heap (add_to_heap ms root a) root ptr) (add_to_heap (add_to_heap ms root ptr) root a) as EQ'.
          forward EQ'. apply EQ.
          red in EQ'.
          specialize (EQ' root root eq_refl).
          specialize (EQ' ptrs ptrs eq_refl).
          rewrite EQ'.

          eauto.
        }

        rewrite EQ2.

        reflexivity.
    Qed.

    Lemma add_to_frame_correct :
      forall ptr (ms ms' : memory_stack),
        add_to_frame ms (ptr_to_int ptr) = ms' ->
        add_ptr_to_frame_stack (memory_stack_frame_stack ms) ptr (memory_stack_frame_stack ms').
    Proof.
      intros ptr ms ms' ADD.
      unfold add_ptr_to_frame_stack.
      intros f PEEK.
      exists (ptr_to_int ptr :: f).
      split; [|split].
      - (* add_ptr_to_frame *)
        split.
        + intros ptr' DISJOINT.
          split; intros IN; cbn; auto.

          destruct IN as [IN | IN];
            [contradiction | auto].
        + cbn; auto.
      - (* peek_frame_stack_prop *)
        destruct ms as [m fs].
        destruct ms' as [m' fs'].
        cbn in *.

        break_match_hyp; inv ADD;
          cbn in *; rewrite PEEK; reflexivity.
      - (* pop_frame_stack_prop *)
        destruct ms as [m fs].
        destruct ms' as [m' fs'].
        cbn in *.

        break_match_hyp; inv ADD.
        + intros fs1_pop; split; intros POP; inv POP.
        + intros fs1_pop; split; intros POP; cbn in *; auto.
    Qed.

    Lemma add_all_to_frame_correct :
      forall ptrs (ms : memory_stack) (ms' : memory_stack),
        add_all_to_frame ms (map ptr_to_int ptrs) = ms' ->
        add_ptrs_to_frame_stack (memory_stack_frame_stack ms) ptrs (memory_stack_frame_stack ms').
    Proof.
      induction ptrs;
        intros ms ms' ADD_ALL.
      - cbn in *.
        apply add_all_to_frame_nil in ADD_ALL; subst; auto.
        reflexivity.
      - cbn in *.
        eexists.
        split.
        + eapply IHptrs.
          reflexivity.
        + destruct ms as [m fs h].
          destruct ms' as [m' fs' h'].
          cbn.

          apply add_all_to_frame_cons_inv in ADD_ALL.
          destruct ADD_ALL as [ms' [ADD ADD_ALL]].

          destruct (add_all_to_frame (mkMemoryStack m fs h) (map ptr_to_int ptrs)) eqn:ADD_ALL'.
          cbn.

          rename memory_stack_memory0 into m0.
          rename memory_stack_frame_stack0 into f.
          rename memory_stack_heap0 into h0.

          assert (add_to_frame (mkMemoryStack m0 f h0) (ptr_to_int a) = add_to_frame (mkMemoryStack m0 f h0) (ptr_to_int a)) as ADD' by reflexivity.
          pose proof (add_all_to_frame_cons_swap _ _ _ _ _ _ _ ADD ADD_ALL ADD_ALL' ADD') as EQV.
          cbn in EQV.
          rewrite EQV.
          destruct f.
          * replace (Singleton f) with (memory_stack_frame_stack (mkMemoryStack m0 (Singleton f) h0)) by reflexivity.
            eapply add_to_frame_correct.
            reflexivity.
          * replace (Snoc f f0) with (memory_stack_frame_stack (mkMemoryStack m0 (Snoc f f0) h0))by reflexivity.
            eapply add_to_frame_correct.
            reflexivity.
    Qed.

    Lemma add_to_heap_correct :
      forall root ptr (ms : memory_stack) (ms' : memory_stack),
        add_to_heap ms (ptr_to_int root) (ptr_to_int ptr) = ms' ->
        add_ptr_to_heap (memory_stack_heap ms) root ptr (memory_stack_heap ms').
    Proof.
      intros root ptr ms ms' ADD.
      split.
      - (* Old *)
        intros ptr' DISJOINT root'.
        destruct ms as [mem fs h].
        unfold add_to_heap in *.
        unfold ptr_in_heap_prop in *.
        cbn in *.
        inv ADD.
        cbn.

        split; intros IN.
        + unfold add_with.
          destruct (Z.eq_dec (ptr_to_int root') (ptr_to_int root)) as [EQR | NEQR].
          * unfold Block in *.
            unfold Iptr in *.
            rewrite EQR in *.
            break_inner_match.
            -- rewrite IP.F.add_eq_o; firstorder.
            -- contradiction.
          * unfold Block in *.
            unfold Iptr in *.
            break_inner_match.
            -- rewrite IP.F.add_neq_o; firstorder.
            -- rewrite IP.F.add_neq_o; firstorder.
        + unfold add_with in *.
          destruct (Z.eq_dec (ptr_to_int root') (ptr_to_int root)) as [EQR | NEQR].
          * unfold Block in *.
            unfold Iptr in *.
            rewrite EQR in *.
            break_inner_match_hyp.
            -- rewrite IP.F.add_eq_o in IN; firstorder.
            -- rewrite IP.F.add_eq_o in IN; firstorder.
          * unfold Block in *.
            unfold Iptr in *.
            break_inner_match_hyp.
            -- rewrite IP.F.add_neq_o in IN; firstorder.
            -- rewrite IP.F.add_neq_o in IN; firstorder.
      - (* Disjoint roots *)
        intros root' H0 ptr'.
        inv ADD.
        destruct ms as [mem fs h].
        cbn.
        unfold add_with.
        break_match.
        + unfold ptr_in_heap_prop.
          rewrite IP.F.add_neq_o; auto.
          reflexivity.
        + unfold ptr_in_heap_prop.
          rewrite IP.F.add_neq_o; auto.
          reflexivity.
      - intros root' DISJOINT.
        inv ADD.
        destruct ms as [mem fs h].
        cbn.
        unfold add_with.
        break_match.
        + unfold root_in_heap_prop.
          rewrite member_add_ineq; auto.
          reflexivity.
        + unfold root_in_heap_prop.
          rewrite member_add_ineq; auto.
          reflexivity.
      - (* New *)
        destruct ms as [mem fs h].
        unfold add_to_heap in *.
        unfold ptr_in_heap_prop in *.
        cbn in *.
        inv ADD.
        cbn.

        unfold add_with.
        break_inner_match.
        -- rewrite IP.F.add_eq_o; firstorder.
        -- rewrite IP.F.add_eq_o; firstorder.
      - destruct ms as [mem fs h].
        unfold add_to_heap in *.
        unfold root_in_heap_prop in *.
        cbn in *.
        inv ADD.
        cbn.

        unfold add_with.
        break_inner_match.
        -- rewrite member_add_eq; firstorder.
        -- rewrite member_add_eq; firstorder.
    Qed.

    Lemma add_all_to_heap'_correct :
      forall ptrs root (ms : memory_stack) (ms' : memory_stack),
        add_all_to_heap' ms (ptr_to_int root) (map ptr_to_int ptrs) = ms' ->
        add_ptrs_to_heap' (memory_stack_heap ms) root ptrs (memory_stack_heap ms').
    Proof.
      induction ptrs;
        intros root ms ms' ADD_ALL.
      - cbn in *; subst; reflexivity.
      - cbn in *.
        eexists.
        split.
        + eapply IHptrs.
          reflexivity.
        + destruct ms as [m fs h].
          destruct ms' as [m' fs' h'].
          cbn.

          apply add_all_to_heap'_cons_inv in ADD_ALL.
          destruct ADD_ALL as [ms' [ADD ADD_ALL]].

          destruct (add_all_to_heap' (mkMemoryStack m fs h) (ptr_to_int root) (map ptr_to_int ptrs)) eqn:ADD_ALL'.
          cbn.

          rename memory_stack_memory0 into m0.
          rename memory_stack_frame_stack0 into f.
          rename memory_stack_heap0 into h0.

          assert (add_to_heap (mkMemoryStack m0 f h0) (ptr_to_int root) (ptr_to_int a) = add_to_heap (mkMemoryStack m0 f h0) (ptr_to_int root) (ptr_to_int a)) as ADD' by reflexivity.
          pose proof (add_all_to_heap'_cons_swap _ _ _ _ _ _ _ _ ADD ADD_ALL ADD_ALL' ADD') as EQV.
          cbn in EQV.
          replace h0 with (memory_stack_heap (mkMemoryStack m0 fs h0)) at 1 by reflexivity.
          rewrite EQV.
          replace (add_with (ptr_to_int root) (ptr_to_int a) (fun x : Z => [x]) cons h0)
            with (memory_stack_heap (mkMemoryStack m0 fs (add_with (ptr_to_int root) (ptr_to_int a) (fun x : Z => [x]) cons h0))) by reflexivity.
          eapply add_to_heap_correct.
          cbn.
          reflexivity.
    Qed.

    Lemma add_all_to_heap_correct :
      forall ptrs (ms : memory_stack) (ms' : memory_stack),
        add_all_to_heap ms (map ptr_to_int ptrs) = ms' ->
        add_ptrs_to_heap (memory_stack_heap ms) ptrs (memory_stack_heap ms').
    Proof.
      intros ptrs ms ms' H0.
      destruct ptrs.
      - cbn in *.
        Transparent add_all_to_heap.
        unfold add_all_to_heap in H0.
        Opaque add_all_to_heap.
        subst.
        reflexivity.
      - eapply add_all_to_heap'_correct; cbn in *.
        eauto.
    Qed.

    (* TODO: Move this *)
    Lemma initial_frame_empty :
      empty_frame initial_frame.
    Proof.
      unfold empty_frame.
      intros ptr.
      unfold initial_frame.
      cbn.
      auto.
    Qed.

    Lemma empty_frame_eqv :
      forall f1 f2,
        empty_frame f1 ->
        empty_frame f2 ->
        frame_eqv f1 f2.
    Proof.
      intros f1 f2 F1 F2.
      unfold empty_frame in *.
      unfold frame_eqv.
      intros ptr; split; intros IN; firstorder.
    Qed.

    (* TODO: Move this *)
    Lemma mem_state_frame_stack_prop_refl :
      forall ms fs,
        mem_state_frame_stack ms = fs ->
        mem_state_frame_stack_prop ms fs.
    Proof.
      intros [[m fsm] pr] fs EQ; subst.
      red; cbn.
      red.
      reflexivity.
    Qed.

    (* These should be opaque for convenience *)
    #[global] Opaque add_all_to_frame.
    #[global] Opaque add_all_to_heap.
    #[global] Opaque next_memory_key.

    Definition get_free_block `{MemMonad ExtraState MemM (itree Eff)} (len : nat) (pr : Provenance) : MemM (addr * list addr)%type :=
      ms <- get_mem_state;;
      let mem_stack := ms_memory_stack ms in
      let addr := next_memory_key mem_stack in
      let '(mkMemoryStack mem fs h) := ms_memory_stack ms in
      let aid := provenance_to_allocation_id pr in
      let ptr := (int_to_ptr addr (allocation_id_to_prov aid)) in
      ptrs <- get_consecutive_ptrs ptr len;;
      ret (ptr, ptrs).

    Definition sbytes_to_mem_bytes (aid : AllocationId) (bytes : list SByte) : list mem_byte :=
      map (fun b => (b, aid)) bytes.

    (** Add block to memory with a given allocation id *)
    Definition add_block `{MemMonad ExtraState MemM (itree Eff)} (aid : AllocationId) (ptr : addr) (ptrs : list addr) (init_bytes : list SByte) : MemM unit :=
      let mem_bytes := sbytes_to_mem_bytes aid init_bytes in
      ms <- get_mem_state;;
      let '(mkMemoryStack mem fs h) := mem_state_memory_stack ms in

      (* Add bytes to memory *)
      let mem' := add_all_index (map (fun b => (b, aid)) init_bytes) (ptr_to_int ptr) mem in
      put_mem_state (MemState_put_memory (mkMemoryStack mem' fs h) ms).

    (** Add pointers to the stack frame *)
    Definition add_ptrs_to_frame `{MemMonad ExtraState MemM (itree Eff)} (ptrs : list addr) : MemM unit :=
      modify_mem_state
        (fun ms =>
           let mem := MemState_get_memory ms in
           MemState_put_memory (add_all_to_frame mem (map ptr_to_int ptrs)) ms);;
      ret tt.

    Definition add_ptrs_to_heap `{MemMonad ExtraState MemM (itree Eff)} (ptrs : list addr) : MemM unit :=
      modify_mem_state
        (fun ms =>
           let mem := MemState_get_memory ms in
           MemState_put_memory (add_all_to_heap mem (map ptr_to_int ptrs)) ms);;
      ret tt.

    (** Add a block of bytes to memory, and register it in the current stack frame. *)
    Definition add_block_to_stack `{MemMonad ExtraState MemM (itree Eff)} (aid : AllocationId) (ptr : addr) (ptrs : list addr) (init_bytes : list SByte) : MemM unit :=
      add_block aid ptr ptrs init_bytes;;
      add_ptrs_to_frame ptrs.

    (** Add a block of bytes to memory, and register it in the heap. *)
    (* Should we make sure ptr (the root) is added even if ptrs is empty? *)
    Definition add_block_to_heap `{MemMonad ExtraState MemM (itree Eff)} (aid : AllocationId) (ptr : addr) (ptrs : list addr) (init_bytes : list SByte) : MemM unit :=
      add_block aid ptr ptrs init_bytes;;
      add_ptrs_to_heap ptrs.

    Definition allocate_bytes `{MemMonad ExtraState MemM (itree Eff)} (dt : dtyp) (init_bytes : list SByte) : MemM addr :=
      pr <- fresh_provenance;;
      let len := length init_bytes in
      '(ptr, ptrs) <- get_free_block len pr;;
      match dtyp_eq_dec dt DTYPE_Void with
      | left _ => raise_ub "Allocation of type void"
      | _ =>
          match N.eq_dec (sizeof_dtyp dt) (N.of_nat len) with
          | right _ => raise_ub "Sizeof dtyp doesn't match number of bytes for initialization in allocation."
          | _ =>
              let aid := provenance_to_allocation_id pr in
              add_block_to_stack aid ptr ptrs init_bytes;;
              ret ptr
          end
      end.

    (** Heap allocation *)
    Definition malloc_bytes `{MemMonad ExtraState MemM (itree Eff)} (init_bytes : list SByte) : MemM addr :=
      pr <- fresh_provenance;;
      let len := length init_bytes in
      '(ptr, ptrs) <- get_free_block len pr;;
      let aid := provenance_to_allocation_id pr in
      add_block_to_heap aid ptr ptrs init_bytes;;
      ret ptr.

    (** Frame stacks *)
    (* Check if an address is allocated in a frame *)
    Definition ptr_in_frame (f : Frame) (ptr : addr) : bool
      := existsb (fun p => Z.eqb (ptr_to_int ptr) p) f.

    (* Check for the current frame *)
    Definition peek_frame_stack (fs : FrameStack) : Frame :=
      match fs with
      | Singleton f => f
      | Snoc s f => f
      end.

    Definition push_frame_stack (fs : FrameStack) (f : Frame) : FrameStack :=
      Snoc fs f.

    (* TODO: Move this *)
    Lemma push_frame_stack_correct :
      forall fs1 f fs2,
        push_frame_stack fs1 f = fs2 ->
        push_frame_stack_spec fs1 f fs2.
    Proof.
      intros fs1 f fs2 PUSH.
      unfold push_frame_stack in PUSH.
      subst.
      split.
      - (* pop *)
        cbn. reflexivity.
      - (* peek *)
        cbn. reflexivity.
    Qed.

    (* TODO: move *)
    Lemma push_frame_stack_inj :
      forall fs1 f fs2 fs2',
        push_frame_stack_spec fs1 f fs2 ->
        push_frame_stack_spec fs1 f fs2' ->
        frame_stack_eqv fs2 fs2'.
    Proof.
      intros fs1 f fs2 fs2' PUSH1 PUSH2.
      inv PUSH1.
      inv PUSH2.

      destruct fs2, fs2'; try contradiction.
      cbn in *.
      rewrite <- new_frame0, <- new_frame1.
      rewrite can_pop0, can_pop1.
      reflexivity.
    Qed.

    Definition pop_frame_stack (fs : FrameStack) : err FrameStack :=
      match fs with
      | Singleton f => inl "Last frame, cannot pop."%string
      | Snoc s f => inr s
      end.

    Definition mem_state_set_frame_stack (ms : MemState) (fs : FrameStack) : MemState :=
      let '(mkMemoryStack mem _ h) := ms_memory_stack ms in
      let pr := mem_state_provenance ms in
      mkMemState (mkMemoryStack mem fs h) pr.

    Definition mem_state_set_heap (ms : MemState) (h : Heap) : MemState :=
      let '(mkMemoryStack mem fs _) := ms_memory_stack ms in
      let pr := mem_state_provenance ms in
      mkMemState (mkMemoryStack mem fs h) pr.

    Lemma mem_state_frame_stack_prop_set_refl :
      forall ms fs,
        mem_state_frame_stack_prop (mem_state_set_frame_stack ms fs) fs.
    Proof.
      intros [[m fsm] pr] fs.
      red; cbn.
      red.
      reflexivity.
    Qed.

    Lemma mem_state_heap_prop_set_refl :
      forall ms h,
        mem_state_heap_prop (mem_state_set_heap ms h) h.
    Proof.
      intros [[m fsm h] pr] h'.
      red; cbn.
      red.
      reflexivity.
    Qed.

    Lemma mem_state_frame_stack_prop_set_trans :
      forall ms fs fs' fs'',
        frame_stack_eqv fs' fs'' ->
        mem_state_frame_stack_prop (mem_state_set_frame_stack ms fs) fs' ->
        mem_state_frame_stack_prop (mem_state_set_frame_stack ms fs) fs''.
    Proof.
      intros [[m fsm] pr] fs fs' fs'' EQV MEMPROP.
      red; cbn.
      red in MEMPROP; cbn in MEMPROP.
      red. red in MEMPROP.
      rewrite <- EQV.
      auto.
    Qed.

    Lemma mem_state_heap_prop_set_trans :
      forall ms h h' h'',
        heap_eqv h' h'' ->
        mem_state_heap_prop (mem_state_set_heap ms h) h' ->
        mem_state_heap_prop (mem_state_set_heap ms h) h''.
    Proof.
      intros [[m fsm] pr] h h' h'' EQV MEMPROP.
      red; cbn.
      red in MEMPROP; cbn in MEMPROP.
      red. red in MEMPROP.
      rewrite <- EQV.
      auto.
    Qed.

    Definition mempush `{MemMonad ExtraState MemM (itree Eff)} : MemM unit :=
      ms <- get_mem_state;;
      let fs := mem_state_frame_stack ms in
      let fs' := push_frame_stack fs initial_frame in
      let ms' := mem_state_set_frame_stack ms fs' in
      put_mem_state ms'.

    Definition free_byte
               (b : Iptr)
               (m : memory) : memory
      := delete b m.

    Definition free_frame_memory (f : Frame) (m : memory) : memory :=
      fold_left (fun m key => free_byte key m) f m.

    Definition free_block_memory (block : Block) (m : memory) : memory :=
      fold_left (fun m key => free_byte key m) block m.

    (** Stack free *)
    Definition mempop `{MemMonad ExtraState MemM (itree Eff)} : MemM unit :=
      ms <- get_mem_state;;
      let '(mkMemoryStack mem fs h) := ms_memory_stack ms in
      let f := peek_frame_stack fs in
      fs' <- lift_err_RAISE_ERROR (pop_frame_stack fs);;
      let mem' := free_frame_memory f mem in
      let pr := mem_state_provenance ms in
      let ms' := mkMemState (mkMemoryStack mem' fs' h) pr in
      put_mem_state ms'.

    (** Free from heap *)
    Definition free `{MemMonad ExtraState MemM (itree Eff)} (ptr : addr) : MemM unit :=
      ms <- get_mem_state;;
      let '(mkMemoryStack mem fs h) := ms_memory_stack ms in
      let raw_addr := ptr_to_int ptr in
      match lookup raw_addr h with
      | None => raise_ub "Attempt to free non-heap allocated address."
      | Some block =>
          let mem' := free_block_memory block mem in
          let h' := delete raw_addr h in
          let pr := mem_state_provenance ms in
          let ms' := mkMemState (mkMemoryStack mem' fs h') pr in
          put_mem_state ms'
      end.

    (*** Correctness *)
    (* Import ESID. *)
    (* Definition MemStateM := ErrSID_T (state MemState). *)

    (* Instance MemStateM_MonadAllocationId : MonadAllocationId AllocationId MemStateM. *)
    (* Proof. *)
    (*   split. *)
    (*   apply ESID.fresh_allocation_id. *)
    (* Defined. *)

    (* Instance MemStateM_MonadStoreID : MonadStoreId MemStateM. *)
    (* Proof. *)
    (*   split. *)
    (*   apply ESID.fresh_sid. *)
    (* Defined. *)

    (* Instance MemStateM_MonadMemState : MonadMemState MemState MemStateM. *)
    (* Proof. *)
    (*   split. *)
    (*   - apply (lift MonadState.get). *)
    (*   - intros ms. *)
    (*     apply (lift (MonadState.put ms)). *)
    (* Defined. *)

    (* Instance ErrSIDMemMonad : MemMonad MemState ExtraState AllocationId (ESID.ErrSID_T (state MemState)). *)
    (* Proof. *)
    (*   split. *)
    (*   - (* MemMonad_runs_to *) *)
    (*     intros A ma ms. *)
    (*     destruct ms eqn:Hms. *)
    (*     pose proof (runState (runErrSID_T ma ms_sid0 ms_prov0) ms). *)
    (*     destruct X as [[[res sid'] pr'] ms']. *)
    (*     unfold err_ub_oom. *)
    (*     constructor. *)
    (*     repeat split. *)
    (*     destruct res. *)
    (*     left. apply o. *)
    (*     destruct s. *)
    (*     right. left. apply u. *)
    (*     destruct s. *)
    (*     right. right. left. apply e. *)
    (*     repeat right. apply (ms', a). *)
    (*   - (* MemMonad_lift_stateT *) *)
    (*     admit. *)
    (* Admitted. *)

    Import Monad.

  End MemoryPrimatives.

    Import Monad.

    (* TODO: Move these tactics *)
    Ltac MemMonad_go :=
      repeat match goal with
             | |- context [MemMonad_run (bind _ _)] => rewrite MemMonad_run_bind
             | |- context [MemMonad_run get_mem_state] => rewrite MemMonad_get_mem_state
             | |- context [MemMonad_run (put_mem_state _)] => rewrite MemMonad_put_mem_state
             | |- context [MemMonad_run (ret _)] => rewrite MemMonad_run_ret
             | |- context [MemMonad_run (raise_ub _)] => rewrite MemMonad_run_raise_ub
             end.

    Ltac break_memory_lookup :=
      match goal with
      | |- context [match read_byte_raw ?memory ?intptr with _ => _ end] =>
          let Hlookup := fresh "Hlookup" in
          let byte := fresh "byte" in
          let aid := fresh "aid" in
          destruct (read_byte_raw memory intptr) as [[byte aid] | ] eqn:Hlookup
      end.

    Ltac MemMonad_break :=
      first
        [ break_memory_lookup
        | match goal with
          | |- context [MemMonad_run (if ?X then _ else _)] =>
              let Hcond := fresh "Hcond" in
              destruct X eqn:Hcond
          end
        ].

    Ltac MemMonad_inv_break :=
      match goal with
      | H: Some _ = Some _ |- _ =>
          inv H
      | H: None = Some _ |- _ =>
          inv H
      | H: Some _ = None |- _ =>
          inv H
      end; cbn in *.

    Ltac MemMonad_subst_if :=
      match goal with
      | H: ?X = true |- context [if ?X then _ else _] =>
          rewrite H
      | H: ?X = false |- context [if ?X then _ else _] =>
          rewrite H
      end.

    Ltac intros_mempropt_contra :=
      intros [?err | [[?ms' ?res] | ?oom]];
      match goal with
      | |- ~ _ =>
          let CONTRA := fresh "CONTRA" in
          let err := fresh "err" in
          intros CONTRA;
          destruct CONTRA as [err [CONTRA | CONTRA]]; auto;
          destruct CONTRA as (? & ? & (? & ?) & CONTRA); subst
      | |- ~ _ =>
          let CONTRA := fresh "CONTRA" in
          let err := fresh "err" in
          intros CONTRA;
          destruct CONTRA as (? & ? & (? & ?) & CONTRA); subst
      end.

    Ltac subst_mempropt :=
      repeat
        match goal with
        | Hlup: read_byte_raw ?mem ?addr = _,
            H: context [match read_byte_raw ?mem ?addr with _ => _ end] |- _
          => rewrite Hlup in H; cbn in H
        | Hlup: read_byte_raw ?mem ?addr = _ |-
            context [match read_byte_raw ?mem ?addr with _ => _ end]
          => rewrite Hlup; cbn
        | HC: ?X = _,
            H: context [if ?X then _ else _] |- _
          => rewrite HC in H; cbn in H
        | HC: ?X = _ |-
            context [if ?X then _ else _]
          => rewrite HC; cbn
        end.

    Ltac solve_mempropt_contra :=
      intros_mempropt_contra;
      repeat
        (first
           [ progress subst_mempropt
           | tauto
        ]).

    Ltac MemMonad_solve :=
      repeat
        (first
           [ progress (MemMonad_go; cbn)
           | MemMonad_break; try MemMonad_inv_break; cbn
           | solve_mempropt_contra
           | MemMonad_subst_if; cbn
           | repeat eexists
           | tauto
        ]).

    Ltac unfold_MemState_get_memory :=
      unfold MemState_get_memory;
      unfold mem_state_memory_stack;
      unfold mem_state_memory.

    Ltac unfold_mem_state_memory :=
      unfold mem_state_memory;
      unfold fst;
      unfold ms_memory_stack.

    Ltac unfold_MemState_get_memory_in H :=
      unfold MemState_get_memory in H;
      unfold mem_state_memory_stack in H;
      unfold mem_state_memory in H.

    Ltac unfold_mem_state_memory_in H :=
      unfold mem_state_memory in H;
      unfold fst in H;
      unfold ms_memory_stack in H.

    Ltac solve_returns_provenance :=
      let EQ := fresh "EQ" in
      intros ? ? EQ; inv EQ; reflexivity.

    Ltac break_byte_allocated_in ALLOC :=
      destruct ALLOC as [?ms [?b [ALLOC [?EQ1 ?EQ2]]]]; subst;
      destruct ALLOC as [ALLOC ?LIFT];
      destruct ALLOC as [?ms' [?ms'' [[?EQ1 ?EQ2] ALLOC]]]; subst.

    Ltac break_read_byte_prop_in READ :=
      destruct READ as [?ms' [?ms'' [[?EQ1 ?EQ2] READ]]]; subst.

    (* TODO: move this *)
    Lemma byte_allocated_mem_stack :
      forall ms1 ms2 addr aid,
        byte_allocated ms1 addr aid ->
        mem_state_memory_stack ms1 = mem_state_memory_stack ms2 ->
        byte_allocated ms2 addr aid.
    Proof.
      intros [ms1 pr1] [ms2 pr2] addr aid ALLOC EQ.
      cbn in EQ; subst.
      break_byte_allocated_in ALLOC.
      repeat eexists; [| solve_returns_provenance].
      unfold mem_state_memory in *; cbn in *.
      break_match; [break_match|];
        tauto.
    Qed.

    (* TODO: move this *)
    Lemma read_byte_prop_mem_stack :
      forall ms1 ms2 addr sbyte,
        read_byte_prop ms1 addr sbyte ->
        mem_state_memory_stack ms1 = mem_state_memory_stack ms2 ->
        read_byte_prop ms2 addr sbyte.
    Proof.
      intros [ms1 pr1] [ms2 pr2] addr aid READ EQ.
      cbn in EQ; subst.
      break_read_byte_prop_in READ.
      repeat eexists.
      unfold mem_state_memory in *; cbn in *.
      break_match; [break_match|]; tauto.
    Qed.

    Lemma read_byte_prop_disjoint_set_byte_raw :
      forall ms1 ms2 ptr ptr' byte byte',
        disjoint_ptr_byte ptr ptr' ->
        mem_state_memory ms2 = set_byte_raw (mem_state_memory ms1) (ptr_to_int ptr') byte' ->
        read_byte_prop ms1 ptr byte <-> read_byte_prop ms2 ptr byte.
    Proof.
      intros ms1 ms2 ptr ptr' byte byte' DISJOINT MEM.
      split; intros READ.
      - unfold mem_state_memory in *.
        repeat eexists;
          first [ cbn; (*unfold_mem_state_memory; *)
                  rewrite set_byte_raw_eq; [|solve [eauto]]
                | subst_mempropt
            ].
        rewrite MEM.
        cbn.
        rewrite set_byte_raw_neq.
        break_read_byte_prop_in READ.
        cbn in READ.
        break_match; auto.
        2: {
          unfold disjoint_ptr_byte in *.
          auto.
        }

        break_match; tauto.
      - unfold mem_state_memory in *.
        repeat eexists;
          first [ cbn; (*unfold_mem_state_memory; *)
                  rewrite set_byte_raw_eq; [|solve [eauto]]
                | subst_mempropt
            ].
        break_read_byte_prop_in READ.
        rewrite MEM in READ.
        cbn in READ.
        rewrite set_byte_raw_neq in READ.

        cbn.
        break_match; auto.
        2: {
          unfold disjoint_ptr_byte in *.
          auto.
        }

        break_match; tauto.
    Qed.

    Ltac prove_ptr_to_int_eq p1 p2 :=
      match goal with
      | H : ~ disjoint_ptr_byte p1 p2 |- _ =>
          assert (ptr_to_int p1 = ptr_to_int p2) as ?PINTEQ by
            (unfold disjoint_ptr_byte in *; lia)
      | H : ~ disjoint_ptr_byte p2 p1 |- _ =>
          assert (ptr_to_int p1 = ptr_to_int p2) as ?PINTEQ by
            (unfold disjoint_ptr_byte in *; lia)
      end.

    Lemma read_byte_raw_byte_allocated_aid_eq :
      forall p1 p2 ms byte aid1 aid2,
        read_byte_raw (memory_stack_memory (MemState_get_memory ms)) (ptr_to_int p1) = Some (byte, aid1) ->
        byte_allocated ms p2 aid2 ->
        ptr_to_int p1 = ptr_to_int p2 ->
        aid1 = aid2.
    Proof.
      intros p1 p2 ms byte aid1 aid2 READ ALLOC PEQ.
      break_byte_allocated_in ALLOC.
      rewrite PEQ in *.
      rewrite READ in ALLOC.
      cbn in ALLOC.
      inv ALLOC.
      destruct aid_eq_dec; subst; auto.
      inv H0.
    Qed.

    Ltac prove_ptr_to_int_eq_subst p1 p2 :=
      match goal with
      | H : ptr_to_int p1 = ptr_to_int p2 |- _ =>
          rewrite H in *
      | H : ptr_to_int p2 = ptr_to_int p1 |- _ =>
          rewrite H in *
      | H : _ |- _ =>
          prove_ptr_to_int_eq p1 p2; prove_ptr_to_int_eq_subst p1 p2
      end.

    Ltac prove_aid_eq aid1 aid2 :=
      match goal with
      | READ :
        read_byte_raw (memory_stack_memory (MemState_get_memory ?ms)) (ptr_to_int ?p1) = Some (?byte, aid1),
          ALLOC : byte_allocated ?ms ?p2 aid2 |- _ =>
          let AIDEQ := fresh "AIDEQ" in
          prove_ptr_to_int_eq_subst p2 p1;
          assert (aid1 = aid2) as AIDEQ by
              (eapply read_byte_raw_byte_allocated_aid_eq; eauto)
      end.

    Ltac rewrite_set_byte_eq :=
      rewrite set_byte_raw_eq; [|solve [eauto]].

    Ltac rewrite_set_byte_neq :=
      first [
          match goal with
          | H: read_byte_raw (set_byte_raw _ _ _) _ = _ |- _
            => rewrite set_byte_raw_neq in H; [| solve [eauto]]
          end
        | rewrite set_byte_raw_neq; [| solve [eauto]]
        ].

    Ltac break_addr_allocated_prop_in ALLOCATED :=
       cbn in ALLOCATED;
       destruct ALLOCATED as (?ms' & ?b & ALLOCATED);
       destruct ALLOCATED as [[?C1 ?C2] ALLOCATED]; subst.

    Lemma byte_allocated_set_byte_raw_eq :
      forall ptr aid new new_aid m1 m2,
        byte_allocated m1 ptr aid ->
        mem_state_memory m2 = set_byte_raw (mem_state_memory m1) (ptr_to_int ptr) (new, new_aid) ->
        byte_allocated m2 ptr new_aid.
    Proof.
      intros ptr aid new new_aid m1 m2 [aid' [ms [[ALLOCATED LIFT] GET]]] MEM.
      cbn in GET.
      inversion GET; subst.
      break_addr_allocated_prop_in ALLOCATED.

      unfold mem_state_memory in *.
      do 2 eexists.
      split; [| cbn; tauto].
      split; [| solve_returns_provenance].
      cbn.
      repeat eexists.
      rewrite MEM.
      rewrite set_byte_raw_eq; auto.
      cbn; split; auto.
      apply aid_eq_dec_refl.
    Qed.

    Lemma byte_allocated_set_byte_raw_neq :
      forall ptr aid new_ptr new new_aid m1 m2,
        byte_allocated m1 ptr aid ->
        disjoint_ptr_byte ptr new_ptr ->
        mem_state_memory m2 = set_byte_raw (mem_state_memory m1) (ptr_to_int new_ptr) (new, new_aid) ->
        byte_allocated m2 ptr aid.
    Proof.
      intros ptr aid new_ptr new new_aid m1 m2 [aid' [ms [[ALLOCATED LIFT] GET]]] DISJOINT MEM.
      inversion GET; subst.
      cbn in ALLOCATED.
      destruct ALLOCATED as (ms' & b & ALLOCATED).
      destruct ALLOCATED as [[C1 C2] ALLOCATED]; subst.

      do 2 eexists.
      split; [| cbn; tauto].
      split; [| solve_returns_provenance].

      repeat eexists.
      unfold mem_state_memory in *.
      rewrite MEM.
      unfold mem_byte in *.
      rewrite set_byte_raw_neq; auto.
      break_match.
      break_match.
      destruct ALLOCATED.
      cbn; split; auto.
      destruct ALLOCATED.
      match goal with
      | H: true = false |- _ =>
          inv H
      end.
    Qed.

    Lemma byte_allocated_set_byte_raw_neq' :
      forall ptr aid new_ptr new new_aid m1 m2,
        byte_allocated m2 ptr aid ->
        disjoint_ptr_byte ptr new_ptr ->
        mem_state_memory m2 = set_byte_raw (mem_state_memory m1) (ptr_to_int new_ptr) (new, new_aid) ->
        byte_allocated m1 ptr aid.
    Proof.
      intros ptr aid new_ptr new new_aid m1 m2 [aid' [ms [[ALLOCATED LIFT] GET]]] DISJOINT MEM.
      inversion GET; subst.
      cbn in ALLOCATED.
      destruct ALLOCATED as (ms' & b & ALLOCATED).
      destruct ALLOCATED as [[C1 C2] ALLOCATED]; subst.

      do 2 eexists.
      split; [| cbn; tauto].
      split; [| solve_returns_provenance].

      repeat eexists.
      unfold mem_state_memory in *.
      rewrite MEM in ALLOCATED.
      unfold mem_byte in *.
      rewrite set_byte_raw_neq in ALLOCATED; auto.
      break_match.
      break_match.
      destruct ALLOCATED.
      cbn; split; auto.
      destruct ALLOCATED.
      match goal with
      | H: true = false |- _ =>
          inv H
      end.
    Qed.

    Lemma byte_allocated_set_byte_raw :
      forall ptr aid ptr_new new m1 m2,
        byte_allocated m1 ptr aid ->
        mem_state_memory m2 = set_byte_raw (mem_state_memory m1) (ptr_to_int ptr_new) new ->
        exists aid2, byte_allocated m2 ptr aid2.
    Proof.
      intros ptr aid ptr_new new m1 m2 ALLOCATED MEM.
      pose proof (Z.eq_dec (ptr_to_int ptr) (ptr_to_int ptr_new)) as [EQ | NEQ].
      - (* EQ *)
        destruct new.
        rewrite <- EQ in MEM.
        eexists.
        eapply byte_allocated_set_byte_raw_eq; eauto.
      - (* NEQ *)
        destruct new.
        subst.
        eexists.
        eapply byte_allocated_set_byte_raw_neq; eauto.
    Qed.

    Lemma byte_allocated_set_byte_raw' :
      forall ms ptr1 ptr2 byte rbyte aid aid' fs heap,
        read_byte_raw (mem_state_memory ms) (ptr_to_int ptr1) = Some (rbyte, aid) ->
        access_allowed (address_provenance ptr1) aid ->
        byte_allocated ms ptr2 aid' <->
          byte_allocated {| ms_memory_stack := {| memory_stack_memory := set_byte_raw (mem_state_memory ms) (ptr_to_int ptr1) (byte, aid); memory_stack_frame_stack := fs; memory_stack_heap := heap |}; ms_provenance := mem_state_provenance ms |} ptr2 aid'.
    Proof.
      intros ms ptr1 ptr2 byte rbyte aid aid' fs heap READ ALLOWED.
      split; intros ALLOC.
      - pose proof disjoint_ptr_byte_dec ptr2 ptr1 as [DISJOINT | NDISJOINT].
        { eapply byte_allocated_set_byte_raw_neq; [eauto | | cbn; eauto]; eauto.
        }
        { eapply byte_allocated_set_byte_raw_eq; eauto.
          cbn.

          unfold mem_state_memory in *.
          prove_aid_eq aid aid'; subst.
          eauto.
        }
      - pose proof disjoint_ptr_byte_dec ptr2 ptr1 as [DISJOINT | NDISJOINT].
        {  eapply byte_allocated_set_byte_raw_neq' in ALLOC; [eauto | | cbn; eauto]; eauto.
        }
        { prove_ptr_to_int_eq_subst ptr1 ptr2.

          repeat eexists.
          - unfold mem_state_memory in *.
            rewrite READ.
            cbn.
            split; auto.
            break_byte_allocated_in ALLOC.
            cbn in ALLOC.
            rewrite set_byte_raw_eq in ALLOC; auto.
            destruct ALLOC as [_ AIDEQ].
            auto.
          - intros ms' x RET.
            inv RET.
            auto.
        }
    Qed.

    Lemma byte_allocated_set_byte_raw'' :
      forall m1 m2 ptr_new ptr new_byte rbyte aid aid',
        read_byte_raw (mem_state_memory m1) (ptr_to_int ptr) = Some (rbyte, aid) ->
        access_allowed (address_provenance ptr) aid ->
        mem_state_memory m2 = set_byte_raw (mem_state_memory m1) (ptr_to_int ptr_new) (new_byte, aid) ->
        byte_allocated m1 ptr aid' <->
          byte_allocated m2 ptr aid'.
    Proof.
      intros m1 m2 ptr_new ptr new_byte rbyte aid aid' READ ALLOWED MEMEQ.
      split; intros ALLOC.
      - pose proof disjoint_ptr_byte_dec ptr ptr_new as [DISJOINT | NDISJOINT].
        { eapply byte_allocated_set_byte_raw_neq; [eauto | | cbn; eauto]; eauto.
        }
        { eapply byte_allocated_set_byte_raw_eq; eauto.
          cbn.

          unfold mem_state_memory in *.
          break_byte_allocated_in ALLOC.
          prove_ptr_to_int_eq_subst ptr ptr_new.
          rewrite READ in ALLOC.
          cbn in ALLOC.
          destruct ALLOC as [_ AID_EQ].
          destruct aid_eq_dec; inv AID_EQ.
          eauto.
        }
      - pose proof disjoint_ptr_byte_dec ptr ptr_new as [DISJOINT | NDISJOINT].
        {  eapply byte_allocated_set_byte_raw_neq' in ALLOC; [eauto | | cbn; eauto]; eauto.
        }
        { prove_ptr_to_int_eq_subst ptr_new ptr.

          repeat eexists.
          - unfold mem_state_memory in *.
            rewrite READ.
            cbn.
            split; auto.
            break_byte_allocated_in ALLOC.
            cbn in ALLOC.
            rewrite MEMEQ in ALLOC.
            rewrite set_byte_raw_eq in ALLOC; auto.
            destruct ALLOC as [_ AIDEQ].
            auto.
          - intros ms' x RET.
            inv RET.
            auto.
        }
    Qed.

    Ltac solve_byte_allocated :=
      match goal with
      | H: byte_allocated ?ms1 ?ptr ?aid1 |-
          byte_allocated ?ms2 ?ptr ?aid2 =>
          solve
            [ eapply byte_allocated_set_byte_raw' with (ms:=ms1); eauto
            | eapply byte_allocated_set_byte_raw' with (ms:=ms2); eauto
            ]
      | _ =>
          solve [ eapply byte_allocated_mem_stack; eauto
                | repeat eexists; [| solve_returns_provenance];
                  unfold mem_state_memory in *;
                  first [ cbn;
                          rewrite_set_byte_eq
                        | cbn;
                          rewrite_set_byte_neq
                        | subst_mempropt
                    ];
                  first
                    [ split; try reflexivity;
                      first [rewrite aid_access_allowed_refl | apply aid_eq_dec_refl]; auto
                    | break_match; [break_match|]; split; repeat inv_option; eauto
                    ]
            ]
      end.


    Ltac solve_allocations_preserved :=
      intros ?ptr ?aid; split; intros ALLOC;
      solve_byte_allocated.

    Ltac destruct_read_byte_allowed_in READ :=
      destruct READ as [?aid [?ALLOC ?ALLOWED]].

    Ltac destruct_free_byte_allowed_in FREE :=
      destruct FREE as [?aid [?ALLOC ?ALLOWED]].

    Ltac break_read_byte_allowed_in READ :=
      cbn in READ;
      destruct READ as [?aid READ];
      destruct READ as [READ ?ALLOWED];
      destruct READ as [?ms' [?ms'' [READ [?EQ1 ?EQ2]]]]; subst;
      destruct READ as [READ ?LIFT];
      destruct READ as [?ms' [?ms'' [[?EQ1 ?EQ2] READ]]]; subst;
      cbn in READ.

    Ltac break_write_byte_allowed_in WRITE :=
      destruct WRITE as [?aid WRITE];
      destruct WRITE as [WRITE ?ALLOWED];
      destruct WRITE as [?ms' [?b [WRITE [?EQ1 ?EQ2]]]]; subst;
      destruct WRITE as [WRITE ?LIFT];
      cbn in WRITE;
      destruct WRITE as [?ms' [?ms'' [[?EQ1 ?EQ2] ?WRITE]]]; subst;
      cbn in WRITE.

    Ltac break_free_byte_allowed_in FREE :=
      cbn in FREE;
      destruct FREE as [?aid FREE];
      destruct FREE as [FREE ?ALLOWED];
      destruct FREE as [?ms' [?ms'' [FREE [?EQ1 ?EQ2]]]]; subst;
      destruct FREE as [FREE ?LIFT];
      destruct FREE as [?ms' [?ms'' [[?EQ1 ?EQ2] FREE]]]; subst;
      cbn in FREE.

    Ltac destruct_write_byte_allowed_in WRITE :=
      destruct WRITE as [?aid [?ALLOC ?ALLOWED]].

    Ltac break_write_byte_allowed_hyps :=
      repeat
        match goal with
        | WRITE : write_byte_allowed _ _ |- _ =>
            destruct_write_byte_allowed_in WRITE
        end.

    Ltac break_read_byte_allowed_hyps :=
      repeat
        match goal with
        | READ : read_byte_allowed _ _ |- _ =>
            destruct_read_byte_allowed_in READ
        end.

    Ltac break_free_byte_allowed_hyps :=
      repeat
        match goal with
        | FREE : free_byte_allowed _ _ |- _ =>
            destruct_free_byte_allowed_in FREE
        end.

    Ltac break_access_hyps :=
      break_read_byte_allowed_hyps;
      break_write_byte_allowed_hyps;
      break_free_byte_allowed_hyps.

    Ltac break_lifted_addr_allocated_prop_in ALLOCATED :=
      cbn in ALLOCATED;
      destruct ALLOCATED as [?ms [?b [ALLOCATED [?EQ1 ?EQ2]]]]; subst;
      destruct ALLOCATED as [ALLOCATED ?LIFT];
      destruct ALLOCATED as [?ms' [?ms'' [[?EQ1 ?EQ2] ALLOCATED]]]; subst.

    Hint Rewrite int_to_ptr_provenance : PROVENANCE.
    Hint Resolve access_allowed_refl : ACCESS_ALLOWED.

      Ltac access_allowed_auto :=
        solve [autorewrite with PROVENANCE; eauto with ACCESS_ALLOWED].

      Ltac solve_access_allowed :=
        solve [match goal with
               | HMAPM :
                 map_monad _ _ = inr ?xs,
                   IN :
                   In _ ?xs |- _ =>
                   let GENPTR := fresh "GENPTR" in
                   pose proof map_monad_err_In _ _ _ _ HMAPM IN as [?ip [GENPTR ?INip]];
                   apply handle_gep_addr_preserves_provenance in GENPTR;
                   rewrite <- GENPTR
               end; access_allowed_auto
              | access_allowed_auto
          ].

    Lemma set_byte_raw_not_disjoint :
      forall p1 p2 mem byte aid1 aid2,
        ~disjoint_ptr_byte p1 p2 ->
        aid1 = aid2 ->
        set_byte_raw mem (ptr_to_int p1) (byte, aid1) = set_byte_raw mem (ptr_to_int p2) (byte, aid2).
    Proof.
      intros p1 p2 mem byte aid1 aid2 H0 H1.
      prove_ptr_to_int_eq_subst p1 p2.
      subst; auto.
    Qed.

    Lemma write_byte_allowed_set_byte_raw :
      forall ms ptr1 ptr2 byte rbyte aid fs heap,
        read_byte_raw (mem_state_memory ms) (ptr_to_int ptr1) = Some (rbyte, aid) ->
        access_allowed (address_provenance ptr1) aid ->
        write_byte_allowed ms ptr2 <->
          write_byte_allowed {| ms_memory_stack := {| memory_stack_memory := set_byte_raw (mem_state_memory ms) (ptr_to_int ptr1) (byte, aid); memory_stack_frame_stack := fs; memory_stack_heap := heap |}; ms_provenance := mem_state_provenance ms |} ptr2.
    Proof.
      intros ms ptr1 ptr2 byte rbyte aid fs heap READ.
      split; intros WRITE_ALLOWED.
      - break_access_hyps; eexists; split; [| solve_access_allowed].
        pose proof disjoint_ptr_byte_dec ptr2 ptr1 as [DISJOINT | NDISJOINT].
        { eapply byte_allocated_set_byte_raw_neq; [eauto | | cbn; eauto]; eauto.
        }
        { eapply byte_allocated_set_byte_raw_eq; eauto.
          cbn.

          unfold mem_state_memory in *.
          prove_aid_eq aid aid0; subst.
          eauto.
        }
      - break_access_hyps.
        pose proof disjoint_ptr_byte_dec ptr2 ptr1 as [DISJOINT | NDISJOINT].
        {  exists aid0; split.
           eapply byte_allocated_set_byte_raw_neq' in ALLOC; [eauto | | cbn; eauto]; eauto.
           solve_access_allowed.
        }
        { prove_ptr_to_int_eq_subst ptr1 ptr2.
          exists aid; split; auto.

          repeat eexists.
          - unfold mem_state_memory in *.
            rewrite READ.
            cbn.
            split; auto.
            apply aid_eq_dec_refl.
          - intros ms' x RET.
            inv RET.
            auto.
          - break_byte_allocated_in ALLOC.
            cbn in ALLOC.
            unfold mem_state_memory in *.
            rewrite set_byte_raw_eq in ALLOC; auto.
            destruct ALLOC as [ALLOC AID_EQ].
            destruct aid_eq_dec; inv AID_EQ.
            auto.
        }
    Qed.

    Lemma read_byte_allowed_set_byte_raw :
      forall ms ptr1 ptr2 byte rbyte aid fs heap,
        read_byte_raw (mem_state_memory ms) (ptr_to_int ptr1) = Some (rbyte, aid) ->
        access_allowed (address_provenance ptr1) aid ->
        read_byte_allowed ms ptr2 <->
          read_byte_allowed {| ms_memory_stack := {| memory_stack_memory := set_byte_raw (mem_state_memory ms) (ptr_to_int ptr1) (byte, aid); memory_stack_frame_stack := fs; memory_stack_heap := heap |}; ms_provenance := mem_state_provenance ms |} ptr2.
    Proof.
      intros ms ptr1 ptr2 byte rbyte aid fs heap READ.
      split; intros WRITE_ALLOWED.
      - break_access_hyps; eexists; split; [| solve_access_allowed].
        pose proof disjoint_ptr_byte_dec ptr2 ptr1 as [DISJOINT | NDISJOINT].
        { eapply byte_allocated_set_byte_raw_neq; [eauto | | cbn; eauto]; eauto.
        }
        { eapply byte_allocated_set_byte_raw_eq; eauto.
          cbn.

          unfold mem_state_memory in *.
          prove_aid_eq aid aid0; subst.
          eauto.
        }
      - break_access_hyps.
        pose proof disjoint_ptr_byte_dec ptr2 ptr1 as [DISJOINT | NDISJOINT].
        {  exists aid0; split.
           eapply byte_allocated_set_byte_raw_neq' in ALLOC; [eauto | | cbn; eauto]; eauto.
           solve_access_allowed.
        }
        { prove_ptr_to_int_eq_subst ptr1 ptr2.
          exists aid; split; auto.

          repeat eexists.
          - unfold mem_state_memory in *.
            rewrite READ.
            cbn.
            split; auto.
            apply aid_eq_dec_refl.
          - intros ms' x RET.
            inv RET.
            auto.
          - break_byte_allocated_in ALLOC.
            cbn in ALLOC.
            unfold mem_state_memory in *.
            rewrite set_byte_raw_eq in ALLOC; auto.
            destruct ALLOC as [ALLOC AID_EQ].
            destruct aid_eq_dec; inv AID_EQ.
            auto.
        }
    Qed.

    Lemma free_byte_allowed_set_byte_raw :
      forall ms ptr1 ptr2 byte rbyte aid fs heap,
        read_byte_raw (mem_state_memory ms) (ptr_to_int ptr1) = Some (rbyte, aid) ->
        access_allowed (address_provenance ptr1) aid ->
        free_byte_allowed ms ptr2 <->
          free_byte_allowed {| ms_memory_stack := {| memory_stack_memory := set_byte_raw (mem_state_memory ms) (ptr_to_int ptr1) (byte, aid); memory_stack_frame_stack := fs; memory_stack_heap := heap |}; ms_provenance := mem_state_provenance ms |} ptr2.
    Proof.
      intros ms ptr1 ptr2 byte rbyte aid fs heap READ.
      split; intros WRITE_ALLOWED.
      - break_access_hyps; eexists; split; [| solve_access_allowed].
        pose proof disjoint_ptr_byte_dec ptr2 ptr1 as [DISJOINT | NDISJOINT].
        { eapply byte_allocated_set_byte_raw_neq; [eauto | | cbn; eauto]; eauto.
        }
        { eapply byte_allocated_set_byte_raw_eq; eauto.
          cbn.

          unfold mem_state_memory in *.
          prove_aid_eq aid aid0; subst.
          eauto.
        }
      - break_access_hyps.
        pose proof disjoint_ptr_byte_dec ptr2 ptr1 as [DISJOINT | NDISJOINT].
        {  exists aid0; split.
           eapply byte_allocated_set_byte_raw_neq' in ALLOC; [eauto | | cbn; eauto]; eauto.
           solve_access_allowed.
        }
        { prove_ptr_to_int_eq_subst ptr1 ptr2.
          exists aid; split; auto.

          repeat eexists.
          - unfold mem_state_memory in *.
            rewrite READ.
            cbn.
            split; auto.
            apply aid_eq_dec_refl.
          - intros ms' x RET.
            inv RET.
            auto.
          - break_byte_allocated_in ALLOC.
            cbn in ALLOC.
            unfold mem_state_memory in *.
            rewrite set_byte_raw_eq in ALLOC; auto.
            destruct ALLOC as [ALLOC AID_EQ].
            destruct aid_eq_dec; inv AID_EQ.
            auto.
        }
    Qed.

    Ltac solve_allowed_base :=
      break_access_hyps; eexists; split; [| solve_access_allowed]; solve_byte_allocated.

    Ltac solve_write_byte_allowed :=
      match goal with
      | H: write_byte_allowed ?ms1 ?ptr |-
          write_byte_allowed ?ms2 ?ptr =>
          solve
            [ eapply write_byte_allowed_set_byte_raw with (ms:=ms1); eauto
            | eapply write_byte_allowed_set_byte_raw with (ms:=ms2); eauto
            ]
      | _ =>
          solve_allowed_base
      end.

    Ltac solve_read_byte_allowed :=
      match goal with
      | H: read_byte_allowed ?ms1 ?ptr |-
          read_byte_allowed ?ms2 ?ptr =>
          solve
            [ eapply write_byte_allowed_set_byte_raw with (ms:=ms1); eauto
            | eapply write_byte_allowed_set_byte_raw with (ms:=ms2); eauto
            ]
      | _ =>
          solve_allowed_base
      end.

    Ltac solve_free_byte_allowed :=
      solve_write_byte_allowed.

    Ltac solve_read_byte_allowed_all_preserved :=
      intros ?ptr; split; intros ?READ; solve_read_byte_allowed.

    Ltac solve_write_byte_allowed_all_preserved :=
      intros ?ptr; split; intros ?WRITE; solve_write_byte_allowed.

    Ltac solve_free_byte_allowed_all_preserved :=
      intros ?ptr; split; intros ?WRITE; solve_free_byte_allowed.

    Ltac solve_read_byte_prop :=
      match goal with
      | H: read_byte_prop ?mem1 ?ptr ?byte |-
          read_byte_prop ?mem2 ?ptr ?byte =>
          solve
            [ eapply read_byte_prop_disjoint_set_byte_raw with (ms1:=mem1);
              eauto; cbn; eauto; congruence
            | eapply read_byte_prop_disjoint_set_byte_raw with (ms1:=mem2);
              eauto; cbn; eauto; congruence
            ]
      | _ =>
      solve [ eapply read_byte_prop_mem_stack; eauto
            | repeat eexists;
              first [ cbn; (*unfold_mem_state_memory; *)
                      rewrite set_byte_raw_eq; [|solve [eauto]]
                    | subst_mempropt
                ];
              cbn; subst_mempropt;
              split; auto
        ]
      end.

    Ltac solve_read_byte_prop_all_preserved :=
      split; intros ?READ; solve_read_byte_prop.

    Ltac solve_read_byte_preserved :=
      split;
      [ solve_read_byte_allowed_all_preserved
      | solve_read_byte_prop_all_preserved
      ].

    Lemma read_byte_spec_disjoint_set_byte_raw:
      forall (ms1 ms2 : MemState) (ptr ptr' : addr) (byte : SByte) (byte' : mem_byte),
        disjoint_ptr_byte ptr ptr' ->
        mem_state_memory ms2 = set_byte_raw (mem_state_memory ms1) (ptr_to_int ptr') byte' ->
        read_byte_spec ms1 ptr byte <-> read_byte_spec ms2 ptr byte.
    Proof.
      intros ms1 ms2 ptr ptr' byte [byte' aid_byte'] DISJOINT MEMEQ.
      split; intros [[aid' [READ_ALLOC READ_ALLOWED]] READ_PROP].
      { split.
        + eexists; split; eauto.
          eapply byte_allocated_set_byte_raw_neq; eauto.
        + solve_read_byte_prop.
      }
      { split.
        + eexists; split; eauto.
          eapply byte_allocated_set_byte_raw_neq'; eauto.
        + solve_read_byte_prop.
      }
    Qed.

    Ltac solve_disjoint_ptr_byte :=
      solve [eauto | symmetry; eauto].

    Ltac solve_disjoint_read_byte_spec :=
      let ptr := fresh "ptr" in
      let byte := fresh "byte" in
      let DISJOINT := fresh "DISJOINT" in
      intros ptr byte DISJOINT;
      eapply read_byte_spec_disjoint_set_byte_raw; [solve_disjoint_ptr_byte |]; cbn; eauto.

    Ltac solve_read_byte_spec :=
      split; [solve_read_byte_allowed | solve_read_byte_prop].

    Ltac solve_set_byte_memory :=
      split; [solve_read_byte_spec | solve_disjoint_read_byte_spec].

    Ltac solve_frame_stack_preserved :=
      solve [
          let PROP := fresh "PROP" in
          intros ?fs; split; intros PROP; unfold mem_state_frame_stack_prop in *; auto
          (* intros ?fs; split; intros PROP; inv PROP; reflexivity *)
        ].

    (* TODO: move this? *)
    (* Probably general enough to live in MemoryModel.v *)
    Lemma heap_preserved_mem_state_heap_refl :
      forall ms1 ms2,
        heap_eqv (mem_state_heap ms1) (mem_state_heap ms2) ->
        heap_preserved ms1 ms2.
    Proof.
      intros ms1 ms2 EQ.
      destruct ms1, ms2.
      unfold mem_state_heap in *.
      cbn in *.
      red.
      intros h; cbn.
      unfold memory_stack_heap_prop.
      split; intros EQV.
      rewrite <- EQ; auto.
      rewrite EQ; auto.
    Qed.

    Ltac solve_heap_preserved :=
      solve [
          let PROP := fresh "PROP" in
          intros ?fs; split; intros PROP; unfold mem_state_frame_stack_prop in *; auto
        | eapply heap_preserved_mem_state_heap_refl;
          unfold mem_state_heap;
          cbn;
          rewrite add_all_to_frame_preserves_heap;
          cbn;
          reflexivity
        ].

    (* TODO: move this stuff? *)
    Hint Resolve
         provenance_lt_trans
         provenance_lt_next_provenance
         provenance_lt_nrefl : PROVENANCE_LT.

    Hint Unfold used_provenance_prop : PROVENANCE_LT.

    Ltac solve_used_provenance_prop :=
      unfold used_provenance_prop in *;
      eauto with PROVENANCE_LT.

    Ltac solve_provenances_preserved :=
      intros ?pr; split; eauto.

    Ltac solve_extend_provenance :=
      unfold extend_provenance;
      split; [|split]; solve_used_provenance_prop.

    Ltac solve_fresh_provenance_invariants :=
      split;
      [ solve_extend_provenance
      | split; [| split; [| split; [| split; [| split]]]];
        [ solve_read_byte_preserved
        | solve_write_byte_allowed_all_preserved
        | solve_free_byte_allowed_all_preserved
        | solve_allocations_preserved
        | solve_frame_stack_preserved
        | solve_heap_preserved
        ]
      ].

    Ltac solve_preserve_allocation_ids :=
      unfold preserve_allocation_ids; intros ?p; split; intros USED; solve_used_provenance_prop.

    Ltac solve_write_byte_operation_invariants :=
      split;
      [ solve_allocations_preserved
      | solve_frame_stack_preserved
      | solve_heap_preserved
      | solve_read_byte_allowed_all_preserved
      | solve_write_byte_allowed_all_preserved
      | solve_free_byte_allowed_all_preserved
      | solve_preserve_allocation_ids
      ].

    Ltac solve_write_byte_spec :=
      split; [solve_write_byte_allowed | solve_set_byte_memory | solve_write_byte_operation_invariants].

    Section MemoryPrimatives.
      Context {MemM : Type -> Type}.
      Context {Eff : Type -> Type}.
      (* Context `{Monad MemM}. *)
      (* Context `{MonadProvenance Provenance MemM}. *)
      (* Context `{MonadStoreID MemM}. *)
      (* Context `{MonadMemState MemState MemM}. *)
      (* Context `{RAISE_ERROR MemM} `{RAISE_UB MemM} `{RAISE_OOM MemM}. *)
      Context {ExtraState : Type}.
      Context `{MemMonad ExtraState MemM (itree Eff)}.

    (* TODO: add to solve_read_byte_allowed *)
    Lemma read_byte_allowed_set_frame_stack :
      forall ms f ptr,
        read_byte_allowed ms ptr <-> read_byte_allowed (mem_state_set_frame_stack ms f) ptr.
    Proof.
      intros [[ms prov] fs] f ptr.
      cbn.
      unfold read_byte_allowed;
        split; intros READ;
        cbn in *.

      - break_read_byte_allowed_in READ.

        exists aid.
        repeat eexists; [| solve_returns_provenance |]; auto.

        cbn in *.
        break_match; [break_match|]; tauto.
      - break_read_byte_allowed_in READ.

        exists aid.
        repeat eexists; [| solve_returns_provenance |]; auto.

        cbn in *.
        break_match; [break_match|]; tauto.
    Qed.

    (* TODO: add to write_byte_allowed *)
    Lemma write_byte_allowed_set_frame_stack :
      forall ms f ptr,
        write_byte_allowed ms ptr <-> write_byte_allowed (mem_state_set_frame_stack ms f) ptr.
    Proof.
      intros [[ms prov] fs] f ptr.
      cbn.
      unfold write_byte_allowed;
        split; intros WRITE;
        cbn in *.

      - break_write_byte_allowed_in WRITE.

        exists aid.
        repeat eexists; [| solve_returns_provenance |]; auto.

        cbn in *.
        break_match; [break_match|]; tauto.
      - break_write_byte_allowed_in WRITE.

        exists aid.
        repeat eexists; [| solve_returns_provenance |]; auto.

        cbn in *.
        break_match; [break_match|]; tauto.
    Qed.

    (* TODO: add to write_byte_allowed *)
    Lemma free_byte_allowed_set_frame_stack :
      forall ms f ptr,
        free_byte_allowed ms ptr <-> free_byte_allowed (mem_state_set_frame_stack ms f) ptr.
    Proof.
      intros [[ms prov] fs] f ptr.
      cbn.
      unfold free_byte_allowed;
        split; intros FREE;
        cbn in *.

      - break_free_byte_allowed_in FREE.

        exists aid.
        repeat eexists; [| solve_returns_provenance |]; auto.

        cbn in *.
        break_match; [break_match|]; tauto.
      - break_free_byte_allowed_in FREE.

        exists aid.
        repeat eexists; [| solve_returns_provenance |]; auto.

        cbn in *.
        break_match; [break_match|]; tauto.
    Qed.

    (* TODO: add to solve_read_byte_prop_all_preserved. *)
    Lemma read_byte_prop_set_frame_stack :
      forall ms f,
        read_byte_prop_all_preserved ms (mem_state_set_frame_stack ms f).
    Proof.
      intros [[ms prov] fs] f.
      cbn.
      unfold read_byte_prop_all_preserved, read_byte_prop.
      split; intros READ;
        cbn in *.

      - destruct READ as [ms' [ms'' [[EQ1 EQ2] READ]]]; subst.
        do 2 eexists; split; [tauto|].
        cbn in *.
        break_match; auto.
        break_match; tauto.
      - destruct READ as [ms' [ms'' [[EQ1 EQ2] READ]]]; subst.
        do 2 eexists; split; [tauto|].
        cbn in *.
        break_match; auto.
        break_match; tauto.
    Qed.

    (* TODO *)
    Lemma write_byte_allowed_all_preserved_set_frame_stack :
      forall ms f,
        write_byte_allowed_all_preserved ms (mem_state_set_frame_stack ms f).
    Proof.
      intros ms f ptr.
      eapply write_byte_allowed_set_frame_stack.
    Qed.

    Lemma free_byte_allowed_all_preserved_set_frame_stack :
      forall ms f,
        free_byte_allowed_all_preserved ms (mem_state_set_frame_stack ms f).
    Proof.
      intros ms f ptr.
      eapply free_byte_allowed_set_frame_stack.
    Qed.

    Lemma allocations_preserved_set_frame_stack :
      forall ms f,
        allocations_preserved ms (mem_state_set_frame_stack ms f).
    Proof.
      intros ms f ptr aid.
      split; intros ALLOC.

      - destruct ms as [[ms fs] pr].
        cbn in *.
        break_byte_allocated_in ALLOC.
        cbn in ALLOC.
        unfold mem_state_memory in ALLOC.
        cbn in ALLOC.

        repeat eexists; [| solve_returns_provenance].
        cbn.
        break_match; [break_match|]; tauto.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        break_byte_allocated_in ALLOC.
        cbn in ALLOC.
        unfold mem_state_memory in ALLOC.
        cbn in ALLOC.

        repeat eexists; [| solve_returns_provenance].
        cbn.
        break_match; [break_match|]; tauto.
    Qed.

    (* TODO: move *)
    Lemma preserve_allocation_ids_set_frame_stack :
      forall ms f,
        preserve_allocation_ids ms (mem_state_set_frame_stack ms f).
    Proof.
      intros ms f pr.
      split; intros USED.

      - destruct ms as [[ms fs] pr'].
        cbn in *; auto.
      - destruct ms as [[ms fs] pr'].
        cbn in *; auto.
    Qed.

    (** Correctness of the main operations on memory *)
    Lemma read_byte_correct_base :
      forall ptr pre, exec_correct_memory pre (read_byte ptr) (read_byte_MemPropT ptr).
    Proof.
      unfold exec_correct.
      intros ptr pre ms st VALID.

      Ltac solve_MemMonad_valid_state :=
        solve [auto].

      (* Need to destruct ahead of time so we know if UB happens *)
      destruct (read_byte_raw (mem_state_memory ms) (ptr_to_int ptr)) as [[sbyte aid]|] eqn:READ.
      destruct (access_allowed (address_provenance ptr) aid) eqn:ACCESS.
      - (* Success *)
        right; right; right.
        exists st, ms, sbyte.
        unfold read_byte, read_byte_MemPropT in *.
        split; [| split]; auto.

        { rewrite MemMonad_run_bind.
          rewrite MemMonad_get_mem_state.
          rewrite bind_ret_l.

          rewrite READ.
          rewrite ACCESS.

          rewrite MemMonad_run_ret.
          reflexivity.
        }

        { unfold lift_memory_MemPropT.
          split.
          - repeat eexists.
            unfold mem_state_memory in READ.
            rewrite READ.
            unfold snd.
            rewrite ACCESS.
            cbn; auto.
          - intros ms' x R.
            inv R.
            auto.
        }
      - (* UB from provenance mismatch *)
        left.
        Ltac solve_read_byte_MemPropT_contra READ ACCESS :=
          solve [repeat eexists; right;
                 repeat eexists; cbn;
                 unfold MemState_get_memory in *;
                 unfold mem_state_memory_stack in *;
                 unfold mem_state_memory in *;
                 try rewrite READ in *; cbn in *;
                 try rewrite ACCESS in *; cbn in *;
                 tauto].

        repeat eexists; [| solve_returns_provenance].
        unfold mem_state_memory in *.
        solve_read_byte_MemPropT_contra READ ACCESS.
      - (* UB from accessing unallocated memory *)
        left.
        repeat eexists; [| solve_returns_provenance].
        unfold mem_state_memory in *.
        solve_read_byte_MemPropT_contra READ ACCESS.

        Unshelve.
        all: exact (""%string).
    Qed.

    Lemma read_byte_correct :
      forall ptr pre, exec_correct pre (read_byte ptr) (read_byte_spec_MemPropT ptr).
    Proof.
      unfold exec_correct.
      intros ptr pre ms st VALID.

      (* Need to destruct ahead of time so we know if UB happens *)
      destruct (read_byte_raw (mem_state_memory ms) (ptr_to_int ptr)) as [[sbyte aid]|] eqn:READ.
      destruct (access_allowed (address_provenance ptr) aid) eqn:ACCESS.
      - (* Success *)
        right; right; right.
        exists st, ms, sbyte.
        unfold read_byte, read_byte_MemPropT in *.
        split; [| split]; auto.

        { rewrite MemMonad_run_bind.
          rewrite MemMonad_get_mem_state.
          rewrite bind_ret_l.

          rewrite READ.
          rewrite ACCESS.

          rewrite MemMonad_run_ret.
          reflexivity.
        }

        { unfold read_byte_spec_MemPropT.
          unfold lift_spec_to_MemPropT.
          cbn.
          split; auto.
          split.
          - solve_read_byte_allowed.
          - unfold mem_state_memory in *.
            solve_read_byte_prop.
        }
      - (* UB from provenance mismatch *)
        left.
        unfold read_byte_spec_MemPropT.
        unfold lift_spec_to_MemPropT.
        repeat eexists.
        cbn.
        intros byte.
        unfold mem_state_memory in *.
        intros READ'.
        destruct READ'.
        break_access_hyps.

        break_byte_allocated_in ALLOC.
        rewrite READ in ALLOC.
        cbn in ALLOC.
        destruct ALLOC as [_ AIDEQ].
        symmetry in AIDEQ.
        apply proj_sumbool_true in AIDEQ; subst.
        rewrite ACCESS in ALLOWED.
        inv ALLOWED.
      - (* UB from accessing unallocated memory *)
        left.
        repeat eexists.
        cbn.
        intros byte CONTRA.
        unfold mem_state_memory in *.
        destruct CONTRA.
        break_access_hyps.

        break_byte_allocated_in ALLOC.
        rewrite READ in ALLOC.
        cbn in ALLOC.
        destruct ALLOC as [_ AIDEQ].
        inv AIDEQ.

        Unshelve.
        all: exact (""%string).
    Qed.

    Lemma write_byte_correct :
      forall ptr byte pre, exec_correct pre (write_byte ptr byte) (write_byte_spec_MemPropT ptr byte).
    Proof.
      unfold exec_correct.
      intros ptr byte pre ms st VALID.

      (* Need to destruct ahead of time so we know if UB happens *)
      destruct (read_byte_raw (mem_state_memory ms) (ptr_to_int ptr)) as [[sbyte aid]|] eqn:READ.
      destruct (access_allowed (address_provenance ptr) aid) eqn:ACCESS.
      - (* Success *)
        right; right; right.
        exists st.
        exists {|
            ms_memory_stack :=
            {|
              memory_stack_memory := set_byte_raw (mem_state_memory ms) (ptr_to_int ptr) (byte, aid);
              memory_stack_frame_stack := mem_state_frame_stack ms;
              memory_stack_heap := mem_state_heap ms
            |};
            ms_provenance := mem_state_provenance ms
          |}.
        exists tt.
        unfold write_byte, write_byte_spec_MemPropT in *.
        unfold read_byte, read_byte_MemPropT in *.
        split; [| split]; auto.

        { rewrite MemMonad_run_bind.
          rewrite MemMonad_get_mem_state.
          rewrite bind_ret_l.

          rewrite READ.
          rewrite ACCESS.

          rewrite MemMonad_put_mem_state.
          cbn.
          reflexivity.
        }

        { unfold read_byte_spec_MemPropT.
          unfold lift_spec_to_MemPropT.
          cbn.
          solve_write_byte_spec.
        }

        (* TODO: Need something about valid_state being preserved with set_byte_raw...

           This is going to be a problem. I don't know what MemMonad_valid_state is.
         *)
        admit.
      - (* UB from provenance mismatch *)
        left.
        unfold write_byte_spec_MemPropT.
        unfold lift_spec_to_MemPropT.
        repeat eexists.
        cbn.
        intros m2.
        unfold mem_state_memory in *.
        intros WRITE'.
        destruct WRITE'.
        break_access_hyps.

        break_byte_allocated_in ALLOC.
        rewrite READ in ALLOC.
        cbn in ALLOC.
        destruct ALLOC as [_ AIDEQ].
        symmetry in AIDEQ.
        apply proj_sumbool_true in AIDEQ; subst.
        rewrite ACCESS in ALLOWED.
        inv ALLOWED.
      - (* UB from accessing unallocated memory *)
        left.
        repeat eexists.
        cbn.
        intros m2 CONTRA.
        unfold mem_state_memory in *.
        destruct CONTRA.
        break_access_hyps.

        break_byte_allocated_in ALLOC.
        rewrite READ in ALLOC.
        cbn in ALLOC.
        destruct ALLOC as [_ AIDEQ].
        inv AIDEQ.

        Unshelve.
        all: exact (""%string).
    Admitted.

    (* TODO: move this? *)
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

    (* TODO: move this? *)
    Lemma MemMonad_run_get_consecutive_ptrs:
      forall {ExtraState : Type} {M RunM : Type -> Type} {MM : Monad M} {MRun : Monad RunM}
        {MPROV : MonadProvenance Provenance M} {MSID : MonadStoreId M} {MMS : MonadMemState MemState M}
        {MERR : RAISE_ERROR M} {MUB : RAISE_UB M} {MOOM : RAISE_OOM M} {RunERR : RAISE_ERROR RunM}
        {RunUB : RAISE_UB RunM} {RunOOM : RAISE_OOM RunM}
        `{EQM : Eq1 M} `{EQRI : @Eq1_ret_inv M EQM MM} `{MLAWS : @MonadLawsE M EQM MM}
        {MemMonad : MemMonad ExtraState M RunM}
        `{EQV : @Eq1Equivalence RunM MRun (@MemMonad_eq1_runm ExtraState M RunM MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM _ _ _ MemMonad)}
        `{LAWS: @MonadLawsE RunM (@MemMonad_eq1_runm ExtraState M RunM MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM _ _ _ MemMonad) MRun}
        `{RAISEOOM : @RaiseBindM RunM MRun (@MemMonad_eq1_runm ExtraState M RunM MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM _ _ _ MemMonad) string (@raise_oom RunM RunOOM)}
        `{RAISEERR : @RaiseBindM RunM MRun (@MemMonad_eq1_runm ExtraState M RunM MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM _ _ _ MemMonad) string (@raise_error RunM RunERR)}
        (ms : MemState) ptr len (st : ExtraState),
        (@eq1 RunM
              (@MemMonad_eq1_runm ExtraState M RunM MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM _ _ _ MemMonad)
              (prod ExtraState (prod MemState (list addr)))
              (@MemMonad_run
           ExtraState M RunM MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM _ _ _ MemMonad (list addr)
           (@get_consecutive_ptrs M MM MOOM MERR ptr len) ms st)
              (fmap (fun ptrs => (st, (ms, ptrs))) (@get_consecutive_ptrs RunM MRun RunOOM RunERR ptr len)))%monad.
    Proof.
      intros ExtraState0 M RunM MM0 MRun0 MPROV0 MSID0 MMS0 MERR0 MUB0 MOOM0 RunERR0 RunUB0 RunOOM0 MemMonad0 EQM' EQRI' MLAWS' EQV
             LAWS RAISE RAISEERR ms ptr len st.

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
          rewrite MemMonad_run_raise_error.
          rewrite rbm_raise_bind; eauto.
          reflexivity.
        + cbn.
          rewrite MemMonad_run_ret.
          rewrite bind_ret_l.
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

    Lemma byte_not_allocated_ge_next_memory_key :
      forall (mem : memory_stack) (ms : MemState) (ptr : addr),
        MemState_get_memory ms = mem ->
        next_memory_key mem <= ptr_to_int ptr ->
        byte_not_allocated ms ptr.
    Proof.
      intros mem ms ptr MEM NEXT.
      unfold byte_not_allocated.
      unfold byte_allocated.
      unfold byte_allocated_MemPropT.
      intros aid CONTRA.
      cbn in CONTRA.
      destruct CONTRA as [ms' [a [CONTRA [EQ1 EQ2]]]]. subst ms' a.
      unfold lift_memory_MemPropT in CONTRA.
      destruct CONTRA as [CONTRA PROV].
      cbn in CONTRA.
      destruct CONTRA as [ms' [mem' [[EQ1 EQ2] CONTRA]]].
      subst.
      rewrite read_byte_raw_next_memory_key in CONTRA.
      - destruct CONTRA as [_ CONTRA]; inv CONTRA.
      - rewrite next_memory_key_next_key_memory_stack_memory in NEXT.
        lia.
    Qed.

  (* TODO: this can probably more somewhere else *)
  Lemma get_consecutive_ptrs_cons :
    forall {M : Type -> Type}
      `{HM: Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM}
      `{EQRET : @Eq1_ret_inv M EQM HM}
      `{OOM: RAISE_OOM M} `{ERR: RAISE_ERROR M}
      `{LAWS: @MonadLawsE M EQM HM}
      `{RAISE_OOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
      `{RAISE_ERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}
      ptr len p ptrs,
      (get_consecutive_ptrs ptr len ≈ ret (p :: ptrs))%monad ->
      p = ptr /\ (exists ptr' len', len = S len' /\ (get_consecutive_ptrs ptr' len' ≈ ret ptrs)%monad).
  Proof.
    intros M HM EQM' EQRET EQV OOM ERR LAWS RAISE_OOM RAISE_ERR ptr len p ptrs CONSEC.

    unfold get_consecutive_ptrs in *.
    destruct (intptr_seq 0 len) eqn:SEQ.
    2: {
      cbn in CONSEC.
      rewrite rbm_raise_bind in CONSEC; eauto.
      apply rbm_raise_ret_inv in CONSEC; eauto.
      contradiction.
    }

    cbn in *.
    rewrite bind_ret_l in CONSEC.

    generalize dependent len.
    destruct len; intros SEQ.
    - cbn in SEQ.
      inv SEQ.
      cbn in CONSEC.
      eapply eq1_ret_ret in CONSEC; [|typeclasses eauto].
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
        apply rbm_raise_ret_inv in CONSEC; eauto.
        contradiction.
      }

      (* map_monad succeeds *)
      cbn in CONSEC.
      eapply eq1_ret_ret in CONSEC; eauto.
      inv CONSEC.
      split; auto.

      destruct len.
      + cbn in Heqo0.
        inv Heqo0.
        cbn in Heqs.
        inv Heqs.
        exists p. exists 0%nat.
        split; auto.
        cbn.
        rewrite bind_ret_l.
        cbn.
        reflexivity.
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
        rename l0 into ptrs'.
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
        Set Nested Proofs Allowed.
        Require Import MonadReturnsLaws.
        Lemma Zseq_nil_len :
          forall start len,
            Zseq start len = [] ->
            len = 0%nat.
        Proof.
          intros start len SEQ.
          destruct len; cbn in *; auto.
          inv SEQ.
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

        Lemma Nth_last :
          forall {A} (l : list A) x,
            Util.Nth (l ++ [x]) (length l) x.
        Proof.
          intros A l x.
          induction l; cbn; auto.
        Qed.

        (* TODO: move / generalize these *)
        Lemma map_monad_err_forall2 :
          forall {A B} (f : A -> err B) l res,
            map_monad f l = inr res <->
            Forall2 (fun a b => f a = inr b) l res.
        Proof.
          intros A B f.
          induction l; intros res.
          - split; intros MAP.
            + cbn in *.
              inv MAP.
              auto.
            + inv MAP.
              reflexivity.
          - split; intros MAP.
            + rewrite map_monad_unfold in MAP.
              cbn in *.
              break_match_hyp; inv MAP.
              break_match_hyp; inv H1.

              pose proof (IHl l0) as FORALL.
              constructor; auto.
              eapply FORALL. reflexivity.
            + inv MAP.
              eapply IHl in H4.
              cbn.
              rewrite H2, H4.
              reflexivity.
        Qed.

        (* TODO: move / generalize these *)
        Lemma map_monad_oom_forall2 :
          forall {A B} (f : A -> OOM B) l res,
            map_monad f l = NoOom res <->
            Forall2 (fun a b => f a = NoOom b) l res.
        Proof.
          intros A B f.
          induction l; intros res.
          - split; intros MAP.
            + cbn in *.
              inv MAP.
              auto.
            + inv MAP.
              reflexivity.
          - split; intros MAP.
            + rewrite map_monad_unfold in MAP.
              cbn in *.
              break_match_hyp; inv MAP.
              break_match_hyp; inv H1.

              pose proof (IHl l0) as FORALL.
              constructor; auto.
              eapply FORALL. reflexivity.
            + inv MAP.
              eapply IHl in H4.
              cbn.
              rewrite H2, H4.
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
            replace (off + 0) with off in EQ by lia.
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
                rewrite <- H1; reflexivity.
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
                replace ((1 + (Z.of_nat (Datatypes.length l) + Z.of_nat (Datatypes.length [x0])) - 1)) with ((Z.of_nat (Datatypes.length l) + Z.of_nat (Datatypes.length [x0]))) by lia.
                cbn.
                replace (Z.of_nat (length l) + 1) with (1 + Z.of_nat (length l)) by lia.
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
                replace (1 + Z.of_nat (S len') - 1) with (Z.of_nat (S len')) in YEQ by lia.
                auto.
            + assert (eq1 (NoOom (l ++ [x])) (map_monad (fun ip : IP.intptr => IP.from_Z (IP.to_Z ip + 1)) (l_shifted ++ [y]))) as EQ.
              { rewrite map_monad_app.
                cbn.
                rewrite <- MAP_SHIFTED.
                (* Must be some way to prove that this match gives NoOom x... *)
                assert (IP.from_Z (IP.to_Z y + 1) = NoOom x) as EQ.
                { erewrite IP.from_Z_to_Z; eauto.
                  assert (IP.to_Z x - 1 + 1 = IP.to_Z x) as EQ by lia.
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

        Lemma map_monad_eqv :
          forall {M} `{MM: Monad M} {A B C} (f1 : A -> M C) (f2 : B -> M C) l1 l2 res,
            map_monad f1 l1 = res ->
            Forall2 (fun a b => f1 a = f2 b) l1 l2 ->
            map_monad f2 l2 = res.
        Proof.
          intros M MM0 A B C f1 f2 l1 l2 res MAP1 ZIP.
          revert MAP1. revert res.
          induction ZIP; intros res MAP1.
          - cbn in *; auto.
          - cbn in *.
            rewrite <- H0.
            erewrite IHZIP; eauto.
        Qed.

        rename l into ixs.
        pose proof Heqo0 as SEQ.
        apply intptr_seq_shifted in Heqo0.
        destruct Heqo0 as [l'' [SEQ_SHIFT SHIFT]].
        rewrite SEQ_SHIFT.
        cbn.

        rewrite bind_ret_l.
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

          assert (address_provenance p' = address_provenance p) as PROV.
          { rewrite map_monad_unfold in Heqs.
            cbn in Heqs.
            break_match_hyp; inv Heqs.
            break_match_hyp; inv H1.
            symmetry; eapply handle_gep_addr_preserves_provenance; eauto.
          }

          rewrite PROV.

          rewrite Heqs0.
          rewrite IP.from_Z_to_Z with (z:=1) (i:=one); auto.

          assert ((ptr_to_int p + Z.of_N (sizeof_dtyp (DTYPE_I 8)) * 1 +
                     Z.of_N (sizeof_dtyp (DTYPE_I 8)) * IP.to_Z b) =
                    (ptr_to_int p + Z.of_N (sizeof_dtyp (DTYPE_I 8)) * IP.to_Z a)) as EQ.
          { rewrite sizeof_dtyp_i8.
            unfold Z.of_N.

            rewrite IP.from_Z_to_Z with (z:=1 + Z.of_nat n) (i:=a); auto.
            rewrite IP.from_Z_to_Z with (z:=Z.of_nat n) (i:=b); auto.
            lia.
          }

          rewrite EQ.
          reflexivity.
        }

        rewrite Heqs'.
        cbn; reflexivity.
  Qed.

  (* TODO: this can probably more somewhere else *)
  Lemma get_consecutive_ptrs_ge :
    forall {M : Type -> Type}
      `{HM: Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM}
      `{EQRET : @Eq1_ret_inv M EQM HM}
      `{OOM: RAISE_OOM M} `{ERR: RAISE_ERROR M}
      `{LAWS: @MonadLawsE M EQM HM}
      `{RAISE_OOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
      `{RAISE_ERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}
      ptr len ptrs,
      (forall {A} msg (x : A), ~ (@eq1 M EQM _ (raise_oom msg) (ret x))) ->
      (forall {A} msg (x : A), ~ (@eq1 M EQM _ (raise_error msg) (ret x))) ->
      (get_consecutive_ptrs ptr len ≈ ret ptrs)%monad ->
      (forall p,
          In p ptrs ->
          (ptr_to_int ptr <= ptr_to_int p)%Z).
  Proof.
    intros M HM EQM' EQV EQRET OOM ERR LAWS RAISE_OOM RAISE_ERR ptr len ptrs RAISE_INV RAISE_ERROR_INV.
    revert ptr len.
    induction ptrs; intros ptr len CONSEC p IN.
    - inv IN.
    - destruct IN as [IN | IN].
      + subst.
        eapply get_consecutive_ptrs_cons in CONSEC as (START & CONSEC).
        Unshelve. all: try typeclasses eauto.
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
            rewrite rbm_raise_bind in CONSEC'.
            apply RAISE_INV in CONSEC'.
            contradiction.
            typeclasses eauto.
          }

          cbn in CONSEC'.
          rewrite bind_ret_l in CONSEC'.

          break_match_hyp.
          2: {
            inv Heqo.
          }
          break_match_hyp; inv Heqo.
          cbn in CONSEC'.
          break_match_hyp; cbn in CONSEC'.
          apply RAISE_ERROR_INV in CONSEC'; contradiction.
          break_match_hyp; cbn in CONSEC'.
          apply RAISE_ERROR_INV in CONSEC'; contradiction.
          break_match_hyp; cbn in CONSEC'.
          inv Heqs0.
          break_match_hyp; inv Heqs0.

          apply handle_gep_addr_ix in Heqs.
          apply handle_gep_addr_ix in Heqs1.
          apply eq1_ret_ret in CONSEC'; eauto.
          inv CONSEC'.

          rewrite sizeof_dtyp_i8 in *.
          erewrite IP.from_Z_to_Z in Heqs1; eauto.
          lia.
        }
        lia.
  Qed.

  Lemma byte_not_allocated_get_consecutive_ptrs :
    forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
      `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM} `{LAWS : @MonadLawsE M EQM HM}
      `{RBMOOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
      `{RBMERR : @RaiseBindM M  HM EQM string (@raise_error M ERR)}
      (mem : memory_stack) (ms : MemState) (ptr : addr) (len : nat) (ptrs : list addr),
      MemState_get_memory ms = mem ->
      next_memory_key mem <= ptr_to_int ptr ->
      (@get_consecutive_ptrs M HM OOM ERR ptr len ≈ ret ptrs)%monad ->
      forall p, In p ptrs -> byte_not_allocated ms p.
  Proof.
    intros M HM OOM ERR EQM' EQV EQRET LAWS RBMOOM RBMERR mem ms ptr len ptrs MEM NEXT CONSEC p IN.
    eapply get_consecutive_ptrs_ge with (p := p) in CONSEC; eauto;
      try (intros * CONTRA;
           eapply rbm_raise_ret_inv in CONTRA; eauto).
    eapply byte_not_allocated_ge_next_memory_key; eauto.
    lia.
  Qed.

  Lemma get_consecutive_ptrs_nth :
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
              handle_gep_addr (DTYPE_I 8) ptr [Events.DV.DVALUE_IPTR ix] = inr p).
  Proof.
    intros M HM EQM' EQV EQRET OOM ERR LAWS RAISE_OOM RAISE_ERR ptr len ptrs CONSEC p ix_nat NTH.
    pose proof CONSEC as CONSEC'.
    unfold get_consecutive_ptrs in CONSEC.
    destruct (intptr_seq 0 len) eqn:SEQ.
    2: {
      cbn in CONSEC.
      rewrite rbm_raise_bind in CONSEC; auto.
      apply rbm_raise_ret_inv in CONSEC; try contradiction; auto.
    }

    cbn in CONSEC.
    rewrite bind_ret_l in CONSEC.
    destruct (map_monad
                (fun ix : IP.intptr => handle_gep_addr (DTYPE_I 8) ptr [Events.DV.DVALUE_IPTR ix]) l) eqn:MAP.
    { cbn in CONSEC.
      apply rbm_raise_ret_inv in CONSEC; try contradiction; auto.
    }

    cbn in CONSEC.
    apply eq1_ret_ret in CONSEC; auto.
    inv CONSEC.

    pose proof MAP as PTRS.
    eapply map_monad_err_forall2 in PTRS.
    eapply Forall2_forall in PTRS.
    destruct PTRS as [PTRSLEN PTRS].

    eapply map_monad_err_Nth in MAP as [ix [P NTH']]; eauto.
    exists ix; split; eauto.

    eapply intptr_seq_nth in SEQ; eauto.
  Qed.

  Lemma get_consecutive_ptrs_prov :
    forall {M : Type -> Type}
      `{HM: Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM}
      `{EQRET : @Eq1_ret_inv M EQM HM}
      `{OOM: RAISE_OOM M} `{ERR: RAISE_ERROR M}
      `{LAWS: @MonadLawsE M EQM HM}
      `{RAISE_OOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
      `{RAISE_ERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}
      ptr len ptrs,
      (get_consecutive_ptrs ptr len ≈ ret ptrs)%monad ->
      forall p, In p ptrs -> address_provenance p = address_provenance ptr.
  Proof.
    intros M HM EQM' EQV EQRET OOM ERR LAWS RAISE_OOM RAISE_ERR ptr len ptrs CONSEC p IN.

    apply In_nth_error in IN as (ix_nat & NTH).
    pose proof CONSEC as GEP.
    eapply get_consecutive_ptrs_nth in GEP; cbn; eauto.
    destruct GEP as (ix & IX & GEP).

    apply handle_gep_addr_preserves_provenance in GEP.
    eauto.
  Qed.      

    Lemma find_free_block_correct :
      forall len pr pre,
        exec_correct pre (get_free_block len pr) (find_free_block len pr).
    Proof.
      unfold exec_correct.
      intros len pr pre ms st VALID.
      cbn.
      right.

      unfold get_free_block.
      unfold find_free_block.

      setoid_rewrite MemMonad_run_bind.
      setoid_rewrite MemMonad_get_mem_state.
      setoid_rewrite bind_ret_l.
      destruct ms as [[mem fs heap] pr'].
      cbn.

      match goal with
      | _ : _ |- context [@get_consecutive_ptrs ?MemM ?MM ?OOM ?ERR ?ptr ?len] =>
          epose proof (@get_consecutive_ptrs_inv (itree Eff) MRun RunOOM RunERR (@MemMonad_eq1_runm ExtraState MemM (itree Eff) MM MRun MPROV MSID MMS MERR MUB MOOM RunERR
                                                                                                    RunUB RunOOM _ _ _ H) _ _ _ ptr len)
          as [[oom_msg CONSEC_OOM] | [ptrs CONSEC_RET]]
      end.

      - (* OOM when finding consecutive pointers *)
        right; left.
        exists oom_msg; split; [| exists ""%string; auto].
        rewrite MemMonad_run_bind.
        rewrite MemMonad_run_get_consecutive_ptrs.

        (* TODO: Move this *)
        Set Nested Proofs Allowed.
        #[global] Instance fmap_Monad_Proper :
          forall A B M `{MM : Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M MM EQM} `{LAWS: @MonadLawsE M EQM MM}, Proper (eq ==> eq1 ==> eq1) (@fmap M (@Functor_Monad M MM) A B).
        Proof.
          intros A B M MM0 EQM' EQV LAWS.
          unfold Proper, respectful.
          intros f1 f2 FEQ ma1 ma2 MEQ.
          subst.
          cbn.
          unfold liftM.
          rewrite MEQ.
          reflexivity.
        Qed.

        setoid_rewrite CONSEC_OOM.
        cbn.
        unfold liftM.
        rewrite bind_bind.
        rewrite rbm_raise_bind; [reflexivity|].
        typeclasses eauto.
      - (* Finding consecutive block is successful *)
        right; right.
        exists st.
        exists {|
              ms_memory_stack :=
                {|
                  memory_stack_memory := mem; memory_stack_frame_stack := fs; memory_stack_heap := heap
                |};
              ms_provenance := pr'
          |}.
        eexists.

        rewrite MemMonad_run_bind.
        rewrite MemMonad_run_get_consecutive_ptrs.
        rewrite CONSEC_RET.
        cbn.
        unfold liftM.
        repeat rewrite bind_ret_l.
        rewrite MemMonad_run_ret.
        split.
        reflexivity.
        split; auto.
        split; auto.

        (* Block is free *)
        split.
        + (* Consecutive *)
          (* Annoyingly, because of the possibility of UB I don't know
             that CONSEC_RET (executable version of
             get_consecutive_ptrs succeeding) means that the spec
             contains ret.
           *)
          (* TODO: can probably clean this all up *)
          pose proof exec_correct_get_consecutive_pointers.
          pose proof (exec_correct_get_consecutive_pointers len (int_to_ptr
                     (next_memory_key
                        {|
                          memory_stack_memory := mem;
                          memory_stack_frame_stack := fs;
                          memory_stack_heap := heap
                        |}) (allocation_id_to_prov (provenance_to_allocation_id pr)))).
          unfold exec_correct in H1.
          specialize (H1 len
                         (int_to_ptr
                            (next_memory_key
                               {| memory_stack_memory := mem; memory_stack_frame_stack := fs; memory_stack_heap := heap |})
                            (allocation_id_to_prov (provenance_to_allocation_id pr)))
                         pre {|
              ms_memory_stack :=
                {|
                  memory_stack_memory := mem; memory_stack_frame_stack := fs; memory_stack_heap := heap
                |};
              ms_provenance := pr'
                        |} st VALID H0).
          destruct H1.
          { (* UB case, should be dischargeable *)
            (* Could use get_consecutive_ptrs_inv if RaiseBindM on it... *)
            (* TODO: Prove this *)
            admit.
          }

          destruct H1 as [ERR | BLAH].

          (* Error Case *)
          destruct ERR as [err_msg [ERR_EXEC ERR_SPEC]].
          rewrite MemMonad_run_get_consecutive_ptrs in ERR_EXEC.
          rewrite CONSEC_RET in ERR_EXEC.
          cbn in ERR_EXEC.
          unfold liftM in ERR_EXEC.
          repeat rewrite bind_ret_l in ERR_EXEC.
          apply MemMonad_eq1_raise_error_inv in ERR_EXEC.
          contradiction.

          destruct BLAH as [OOM | SUCC].

          (* OOM Case *)
          destruct OOM as [oom_msg [OOM_EXEC OOM_SPEC]].
          rewrite MemMonad_run_get_consecutive_ptrs in OOM_EXEC.
          rewrite CONSEC_RET in OOM_EXEC.
          cbn in OOM_EXEC.
          unfold liftM in OOM_EXEC.
          repeat rewrite bind_ret_l in OOM_EXEC.
          apply MemMonad_eq1_raise_oom_inv in OOM_EXEC.
          contradiction.

          (* Success *)
          destruct SUCC as [st' [ms' [addrs [EXEC [SPEC VALID_SPEC]]]]].
          rewrite MemMonad_run_get_consecutive_ptrs in EXEC.
          rewrite CONSEC_RET in EXEC.
          cbn in EXEC.
          unfold liftM in EXEC.
          repeat rewrite bind_ret_l in EXEC.
          apply eq1_ret_ret in EXEC; [|typeclasses eauto].
          inv EXEC.
          auto.
        + (* TODO: autorewrite tactic? *)
          rewrite int_to_ptr_provenance.
          reflexivity.
        + intros ptr IN.
          (* TODO: tactic? *)
          eapply get_consecutive_ptrs_prov in CONSEC_RET; eauto.
          rewrite int_to_ptr_provenance in CONSEC_RET.
          auto.
        + intros ptr IN.
          (* Should follow from VALID... *)
          (* May actually follow from next_memory_key *)
          unfold byte_not_allocated.
          intros aid CONTRA.
          break_byte_allocated_in CONTRA.
          cbn in *.
          erewrite read_byte_raw_next_memory_key in CONTRA.
          destruct CONTRA as [_ CONTRA].
          inv CONTRA.

          eapply get_consecutive_ptrs_ge  with (p := ptr) in CONSEC_RET; eauto.
          rewrite ptr_to_int_int_to_ptr in CONSEC_RET.
          rewrite next_memory_key_next_key in CONSEC_RET.
          lia.

          (* Silly inversion lemmas *)
          intros * CONTRA_OOM. symmetry in CONTRA_OOM; eapply MemMonad_eq1_raise_oom_inv in CONTRA_OOM; auto.
          intros * CONTRA_ERR. symmetry in CONTRA_ERR ; eapply MemMonad_eq1_raise_error_inv in CONTRA_ERR; auto.
    Admitted.

    Hint Resolve find_free_block_correct : EXEC_CORRECT.

    Lemma mem_state_fresh_provenance_correct :
      forall ms_init ms_fresh_pr (pr : Provenance),
        mem_state_fresh_provenance ms_init = (pr, ms_fresh_pr) ->
        @fresh_provenance Provenance (MemPropT MemState) _ ms_init (ret (ms_fresh_pr, pr)).
    Proof.
      intros ms_init ms_fresh_pr pr FRESH.
      cbn.
      unfold mem_state_fresh_provenance in FRESH.
      destruct ms_init as (ms & pr_init).
      inv FRESH.

      solve_fresh_provenance_invariants.
    Qed.

    Require Import Error.
    Require Import MonadReturnsLaws.
    Require Import ItreeRaiseMReturns.

    Lemma byte_allocated_add_all_index :
      forall (ms : MemState) (mem : memory) (bytes : list mem_byte) (ix : Z) (aid : AllocationId),
        mem_state_memory ms = add_all_index bytes ix mem ->
        (forall mb, In mb bytes -> snd mb = aid) ->
        (forall p, ix <= ptr_to_int p < ix + (Z.of_nat (length bytes)) -> byte_allocated ms p aid).
    Proof.
    Admitted.

    Lemma byte_allocated_get_consecutive_ptrs :
      forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
        `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
        `{LAWS : @MonadLawsE M EQM HM}

        (mem : memory) (ms : MemState) (ptr : addr) (len : nat) (ptrs : list addr)
        (bytes : list mem_byte) (aid : AllocationId),
        mem_state_memory ms = add_all_index bytes (ptr_to_int ptr) mem ->
        length bytes = len ->
        (forall mb, In mb bytes -> snd mb = aid) ->
        (@get_consecutive_ptrs M HM OOM ERR ptr len ≈ ret ptrs)%monad ->
        forall p, In p ptrs -> byte_allocated ms p aid.
    Proof.
      intros M HM OOM ERR EQM' EQV EQRET LAWS mem ms ptr len ptrs
             bytes aid MEM LEN AIDS CONSEC p IN.

      eapply byte_allocated_add_all_index; eauto.
      (* eapply get_consecutive_ptrs_range in CONSEC; eauto. *)
      (* lia. *)
    Admitted.

    (* (* TODO: Move this thing? *) *)
    Lemma get_consecutive_MemPropT_itree :
      forall ptr len ptrs,
        (@get_consecutive_ptrs (MemPropT MemState) (@MemPropT_Monad MemState) (@MemPropT_RAISE_OOM MemState)
                               (@MemPropT_RAISE_ERROR MemState) ptr len
                               ≈ @ret (MemPropT MemState) (@MemPropT_Monad MemState) (list addr) ptrs)%monad <->
          (@get_consecutive_ptrs (itree Eff) (@Monad_itree Eff)
                                 _ _
                                 ptr len
                                 ≈ Ret ptrs)%monad.
    Proof.
      intros ptr len ptrs.
      split; intros CONSEC.
      - unfold get_consecutive_ptrs in *.
        destruct (intptr_seq 0 len) eqn:HSEQ.
        + cbn in *.
          unfold eq1 in CONSEC.
          red in CONSEC.
          rewrite Eq.bind_ret_l.
          cbn.

          specialize (CONSEC initial_memory_state (ret (initial_memory_state, ptrs))).
          cbn in CONSEC.
          destruct CONSEC as [blah CONSEC].
          forward CONSEC; auto.
          destruct CONSEC as [ms' [a [[EQ1 EQ2] CONSEC]]].
          subst.
          destruct (map_monad
                      (fun ix : IP.intptr =>
                         GEP.handle_gep_addr (DTYPE_I 8) ptr [Events.DV.DVALUE_IPTR ix]) l);
            inv CONSEC.

          cbn.
          reflexivity.
        + cbn in *.
          unfold eq1 in CONSEC.
          specialize (CONSEC initial_memory_state (ret (initial_memory_state, ptrs))).
          cbn in CONSEC.
          destruct CONSEC as [blah CONSEC].
          forward CONSEC; auto.
          destruct CONSEC as [ms' [a [[]CONSEC]]].
      - unfold get_consecutive_ptrs in *.
        destruct (intptr_seq 0 len) eqn:HSEQ.
        + cbn in *.
          unfold eq1 in CONSEC.
          intros ms x.
          cbn.
          setoid_rewrite Eq.bind_ret_l in CONSEC.
          cbn in CONSEC.

          destruct (map_monad
                      (fun ix : IP.intptr =>
                         GEP.handle_gep_addr (DTYPE_I 8) ptr [Events.DV.DVALUE_IPTR ix]) l) eqn:HMAPM.
          { (* Error raised *)
            cbn in CONSEC.
            (* Contradition, need inversion lemma *)
            admit.
          }

          cbn in CONSEC.
          assert (l0 = ptrs) by admit; subst.
          rename H into MemMM.
          destruct_err_ub_oom x.
          * split; intros H.
            -- destruct H; auto.
               destruct H0 as [ms' [a' [[EQ1 EQ2] H']]]; subst.
               rewrite HMAPM in H'.
               cbn in H'.
               auto.
            -- inv H.
          * split; intros H.
            -- destruct H; auto.
               destruct H0 as [ms' [a' [[EQ1 EQ2] H']]]; subst.
               rewrite HMAPM in H'.
               cbn in H'.
               auto.
            -- inv H.
          * split; intros H.
            -- destruct H; auto.
               destruct H0 as [ms' [a' [[EQ1 EQ2] H']]]; subst.
               rewrite HMAPM in H'.
               cbn in H'.
               auto.
            -- inv H.
          * destruct x0.
            split; intros H.
            -- destruct H as [ms' [a' [[EQ1 EQ2] H']]]; subst.
               rewrite HMAPM in H'.
               cbn in H'.
               auto.
            -- exists ms. exists l.
               split; auto.
               rewrite HMAPM.
               cbn.
               auto.
        + cbn in *.
          unfold eq1 in CONSEC.
          intros ms x.
          (* need inversion lemma for consec *)
          admit.
    Admitted.

    Lemma get_consecutive_ptrs_MemPropT_MemState :
      forall ptr len ptrs ms1 ms2 ,
        (@get_consecutive_ptrs (MemPropT MemState) (@MemPropT_Monad MemState) (@MemPropT_RAISE_OOM MemState)
                               (@MemPropT_RAISE_ERROR MemState) ptr len ms1 (ret (ms1, ptrs))) ->
        (@get_consecutive_ptrs (MemPropT MemState) (@MemPropT_Monad MemState) (@MemPropT_RAISE_OOM MemState)
                               (@MemPropT_RAISE_ERROR MemState) ptr len ms2 (ret (ms2, ptrs))).
    Proof.
      intros ptr len ptrs ms1 ms2 CONSEC.
      cbn in *.
      destruct CONSEC as [ms' [ixs [SEQ MAPM]]].
      destruct (intptr_seq 0 len) eqn:HSEQ; cbn in SEQ; inv SEQ.
      cbn.
      exists ms2. exists l.
      split; auto.

      destruct (map_monad (fun ix : IP.intptr => handle_gep_addr (DTYPE_I 8) ptr [Events.DV.DVALUE_IPTR ix]) l) eqn:HMAPM; cbn in *; inv MAPM.
      tauto.
    Qed.

    Lemma get_consecutive_ptrs_MemPropT_eq1 :
      forall ptr len ptrs ms1,
        (@get_consecutive_ptrs (MemPropT MemState) (@MemPropT_Monad MemState) (@MemPropT_RAISE_OOM MemState)
                               (@MemPropT_RAISE_ERROR MemState) ptr len ms1 (ret (ms1, ptrs))) ->
        (@get_consecutive_ptrs (MemPropT MemState) (@MemPropT_Monad MemState) (@MemPropT_RAISE_OOM MemState)
                               (@MemPropT_RAISE_ERROR MemState) ptr len ≈ ret ptrs)%monad.
    Proof.
      intros ptr len ptrs ms1 CONSEC.
      cbn in *.
      destruct CONSEC as [ms' [ixs [SEQ MAPM]]].
      destruct (intptr_seq 0 len) eqn:HSEQ; cbn in SEQ; inv SEQ.
      destruct (map_monad
                  (fun ix : IP.intptr => handle_gep_addr (DTYPE_I 8) ptr [Events.DV.DVALUE_IPTR ix]) l) eqn:HMAPM; inv MAPM.
      cbn.
      red.
      red.
      intros ms x.
      split; intros CONSEC.
      - destruct_err_ub_oom x.
        + destruct CONSEC as [[] | CONSEC].
          destruct CONSEC as [ms_ [ixs [[EQ1 EQ2] MAPM2]]].
          inv EQ1.
          rewrite HMAPM in MAPM2.
          cbn in MAPM2; auto.
        + destruct CONSEC as [[] | CONSEC].
          destruct CONSEC as [ms_ [ixs [[EQ1 EQ2] MAPM2]]].
          inv EQ1.
          rewrite HMAPM in MAPM2.
          cbn in MAPM2; auto.
        + destruct CONSEC as [[] | CONSEC].
          destruct CONSEC as [ms_ [ixs [[EQ1 EQ2] MAPM2]]].
          inv EQ1.
          rewrite HMAPM in MAPM2.
          cbn in MAPM2; auto.
        + destruct x0.
          destruct CONSEC as [ms_ [ixs [[EQ1 EQ2] MAPM2]]].
          inv EQ1.
          rewrite HMAPM in MAPM2.
          cbn in MAPM2; auto.
      - destruct_err_ub_oom x; try inv CONSEC.
        destruct x0.
        inv CONSEC.
        repeat eexists.
        rewrite HMAPM.
        cbn. auto.
    Qed.

    Lemma byte_allocated_memory_eq :
      forall (ms ms' : MemState) (ptr : addr) (aid : AllocationId),
        byte_allocated ms ptr aid ->
        mem_state_memory ms = mem_state_memory ms' -> byte_allocated ms' ptr aid.
    Proof.
      intros ms ms' ptr aid ALLOC MEM.
      break_byte_allocated_in ALLOC.
      repeat eexists.
      - cbn in *.
        unfold mem_state_memory in *.
        rewrite <- MEM.
        repeat break_match_goal; tauto.
      - intros ms'0 x RET.
        inv RET.
        reflexivity.
    Qed.

    Lemma byte_allocated_preserved_get_consecutive_ptrs :
      forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
        `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
        `{LAWS : @MonadLawsE M EQM HM}

        (ms ms': MemState) (ptr_old ptr : addr) (len : nat) (ptrs : list addr)
        (bytes : list mem_byte) (aid : AllocationId),
        mem_state_memory ms' = add_all_index bytes (ptr_to_int ptr) (mem_state_memory ms) ->
        length bytes = len ->
        (forall p : addr, In p ptrs -> disjoint_ptr_byte p ptr_old) ->
        (@get_consecutive_ptrs M HM OOM ERR ptr len ≈ ret ptrs)%monad ->
        byte_allocated ms ptr_old aid <-> byte_allocated ms' ptr_old aid.
    Proof.
      intros M HM OOM ERR EQM0 EQV EQRET LAWS ms ms' ptr_old ptr len ptrs bytes aid MEM LEN DISJOINT CONSEC.
    Admitted.

    Lemma find_free_block_extend_allocations :
      forall ms_init ms_found_free ms_extended pr ptr ptrs init_bytes,
        find_free_block (length init_bytes) pr ms_init (ret (ms_found_free, (ptr, ptrs))) ->
        mem_state_memory ms_extended = add_all_index (map (fun b : SByte => (b, provenance_to_allocation_id pr)) init_bytes) (ptr_to_int ptr) (mem_state_memory ms_init) ->
        extend_allocations ms_init ptrs pr ms_extended.
    Proof.
      intros ms_init ms_found_free ms_extended pr ptr ptrs init_bytes [MS FREE] MEM.
      inv MS; inv FREE.
      split.
      - eapply @byte_allocated_get_consecutive_ptrs with (HM:=@Monad_itree Eff); try typeclasses eauto.
        unfold mem_state_memory in *.
        cbn; eauto.
        rewrite map_length; reflexivity.

        intros mb INMB.
        apply in_map_iff in INMB as (sb & MBEQ & INSB).
        inv MBEQ.
        cbn. reflexivity.

        eapply get_consecutive_MemPropT_itree;
          eapply get_consecutive_ptrs_MemPropT_eq1; eauto.
      - intros ptr' aid IN.
        eapply @byte_allocated_preserved_get_consecutive_ptrs with (HM:=@Monad_itree Eff); try typeclasses eauto.
        unfold mem_state_memory in *.
        cbn; eauto.
        rewrite map_length; reflexivity.
        eauto.

        eapply get_consecutive_MemPropT_itree;
          eapply get_consecutive_ptrs_MemPropT_eq1; eauto.
    Qed.

    Lemma find_free_block_ms_eq :
      forall ms1 ms2 len pr ptr ptrs,
        find_free_block len pr ms1 (ret (ms2, (ptr, ptrs))) ->
        ms1 = ms2.
    Proof.
      intros ms1 ms2 len pr ptr ptrs [MS FREE].
      auto.
    Qed.

    Ltac solve_mem_state_memory :=
      solve
        [ cbn; unfold mem_state_memory; cbn;
          rewrite add_all_to_frame_preserves_memory; cbn;
          reflexivity
        | cbn; unfold mem_state_memory; cbn;
          rewrite add_all_to_heap_preserves_memory; cbn;
          reflexivity
        ].

    Lemma get_consecutive_ptrs_covers_range :
      forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
        `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
        `{LAWS : @MonadLawsE M EQM HM}
        ptr len ptrs,
        (@get_consecutive_ptrs M HM OOM ERR ptr len ≈ ret ptrs)%monad ->
        forall ix, ptr_to_int ptr <= ix < ptr_to_int ptr + (Z.of_nat len) ->
              exists p', ptr_to_int p' = ix /\ In p' ptrs.
    Proof.
      (* TODO: This is kind of related to get_consecutive_ptrs_nth *)
      intros M HM OOM ERR EQM' EQV EQRET LAWS ptr len ptrs CONSEC ix RANGE.
      Transparent get_consecutive_ptrs.
      unfold get_consecutive_ptrs in CONSEC.
      Opaque get_consecutive_ptrs.

      (* Technically this can be more general with inversion lemma for raise_oom *)
      destruct (intptr_seq 0 len) eqn:HSEQ.
      - cbn in *.
        setoid_rewrite Monad.bind_ret_l in CONSEC.

        destruct (map_monad
                    (fun ix : IP.intptr =>
                       GEP.handle_gep_addr (DTYPE_I 8) ptr [Events.DV.DVALUE_IPTR ix])
                    l) eqn:HMAPM.
        + cbn in CONSEC.
          (* TODO: need inversion lemma *)
          admit.
        + cbn in CONSEC.
          apply eq1_ret_ret in CONSEC; eauto.
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
          apply GEP.handle_gep_addr_ix in GEP.
          exists p'. split; auto.
          subst.

          rewrite sizeof_dtyp_i8 in GEP.
          erewrite IP.from_Z_to_Z in GEP; [|apply FROMZ].
          lia.
    Admitted.

    (* TODO: move this *)
    Lemma get_consecutive_ptrs_range :
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
            (ptr_to_int ptr <= ptr_to_int p < ptr_to_int ptr + (Z.of_nat len))%Z).
    Proof.
      intros M HM EQM' EQV EQRET OOM ERR LAWS RAISE_OOM RAISE_ERR ptr len ptrs.
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
          { Transparent get_consecutive_ptrs.
            unfold get_consecutive_ptrs in CONSEC'.
            Opaque get_consecutive_ptrs.
            cbn in CONSEC'.
            break_match_hyp.
            2: { cbn in CONSEC'. rewrite rbm_raise_bind in CONSEC'; [| typeclasses eauto].
                 (* TODO: inversion lemma for CONSEC' *)
                 admit.
            }

            break_match_hyp.
            2: { cbn in CONSEC'. rewrite rbm_raise_bind in CONSEC'; [| typeclasses eauto].
                 (* TODO: inversion lemma for CONSEC' *)
                 admit.
            }

            cbn in CONSEC'.
            rewrite bind_ret_l in CONSEC'.
            destruct (map_monad (fun ix : IP.intptr => handle_gep_addr (DTYPE_I 8) ptr [Events.DV.DVALUE_IPTR ix])
                                (i :: l)) eqn:HMAPM.
            { cbn in CONSEC'.
              (* TODO: inversion lemma for CONSEC' *)
              admit.
            }

            cbn in CONSEC'.
            apply eq1_ret_ret in CONSEC'; eauto.
            inv CONSEC'.
            apply map_monad_err_In with (x := ptr') in HMAPM; [| intuition].
            admit.
          }
          lia.
    Admitted.

    Lemma read_byte_get_consecutive_ptrs :
      forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
        `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
        `{LAWS : @MonadLawsE M EQM HM}

        (ms ms' : MemState) (ptr : addr) (len : nat) (ptrs : list addr)
        (init_bytes : list SByte) (bytes : list mem_byte) pr (aid : AllocationId),
        mem_state_memory ms' = add_all_index bytes (ptr_to_int ptr) (mem_state_memory ms) ->
        (forall mb : mem_byte, In mb bytes -> snd mb = aid) ->
        bytes = map (fun b : SByte => (b, provenance_to_allocation_id pr)) init_bytes ->
        (@get_consecutive_ptrs M HM OOM ERR ptr len ≈ ret ptrs)%monad ->
        (length bytes = len) ->
        forall p ix byte,
          Util.Nth ptrs ix p ->
          Util.Nth init_bytes ix byte ->
          access_allowed (address_provenance p) aid ->
          read_byte_prop ms' p byte.
    Proof.
      intros M HM OOM ERR EQM' EQV EQRET LAWS ms ms' ptr len ptrs
             init_bytes bytes pr aid MEM2 INMB BYTES CONSEC BYTELEN
             p ix byte PTRNTH BYTENTH ACCESS.
      unfold read_byte_prop, read_byte_MemPropT.
      repeat eexists.
      unfold mem_state_memory in *.
      rewrite MEM2.
      rewrite read_byte_raw_add_all_index_in with (v:=(byte, aid)).
      unfold snd.
      rewrite ACCESS.
      cbn.
      tauto.

      - admit.
      - admit.
    Admitted.

    (* TODO: Move and reuse *)
    Lemma read_byte_preserved_get_consecutive_ptrs :
      forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
        `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
        `{LAWS : @MonadLawsE M EQM HM}

        (ms ms' : MemState) (ptr : addr) (len : nat) (ptrs : list addr)
        (bytes : list mem_byte) (p : addr) byte,
        mem_state_memory ms' = add_all_index bytes (ptr_to_int ptr) (mem_state_memory ms)->
        (@get_consecutive_ptrs M HM OOM ERR ptr len ≈ ret ptrs)%monad ->
        (length bytes = len) ->
        (forall new_p, In new_p ptrs -> disjoint_ptr_byte new_p p) ->
        read_byte_prop ms p byte <->
          read_byte_prop ms' p byte.
    Proof.
      intros M HM OOM ERR EQM' EQV EQRET LAWS ms ms' ptr len ptrs
             bytes p byte MEM2 CONSEC BYTELEN DISJOINT.

      unfold mem_state_memory in *.

      split; intros READ.
      - destruct READ as [?ms' [?ms'' [[?EQ1 ?EQ2] READ]]].
        subst ms'0 ms''.
        repeat eexists.
        rewrite MEM2.

        cbn in *.
        erewrite read_byte_raw_add_all_index_out.
        2: {
          pose proof (get_consecutive_ptrs_covers_range ptr len ptrs CONSEC) as INRANGE.
          subst.
          rewrite <- Zlength_correct in INRANGE.

          pose proof (Z_lt_ge_dec (ptr_to_int p) (ptr_to_int ptr)) as [LTNEXT | GENEXT]; auto.
          pose proof (Z_ge_lt_dec (ptr_to_int p) (ptr_to_int ptr + Zlength bytes)) as [LTNEXT' | GENEXT']; auto.

          specialize (INRANGE (ptr_to_int p)).
          forward INRANGE; [lia|].
          destruct INRANGE as (p' & EQ & INRANGE).
          specialize (DISJOINT p' INRANGE).
          unfold disjoint_ptr_byte in DISJOINT.
          lia.
        }

        cbn.
        break_match; [break_match|]; split; tauto.
      - destruct READ as [?ms' [?ms'' [[?EQ1 ?EQ2] READ]]].
        subst ms'0 ms''.
        repeat eexists.
        rewrite MEM2 in READ.

        cbn in *.
        erewrite read_byte_raw_add_all_index_out in READ.
        2: {
          pose proof (get_consecutive_ptrs_covers_range ptr len ptrs CONSEC) as INRANGE.
          subst.
          rewrite <- Zlength_correct in INRANGE.

          pose proof (Z_lt_ge_dec (ptr_to_int p) (ptr_to_int ptr)) as [LTNEXT | GENEXT]; auto.
          pose proof (Z_ge_lt_dec (ptr_to_int p) (ptr_to_int ptr + Zlength bytes)) as [LTNEXT' | GENEXT']; auto.

          specialize (INRANGE (ptr_to_int p)).
          forward INRANGE; [lia|].
          destruct INRANGE as (p' & EQ & INRANGE).
          specialize (DISJOINT p' INRANGE).
          unfold disjoint_ptr_byte in DISJOINT.
          lia.
        }

        cbn.
        break_match; [break_match|]; split; tauto.
    Qed.

    Lemma find_free_block_extend_reads :
      forall ms_init ms_found_free ms_extended pr ptr ptrs init_bytes,
        find_free_block (length init_bytes) pr ms_init (ret (ms_found_free, (ptr, ptrs))) ->
        mem_state_memory ms_extended = add_all_index (map (fun b : SByte => (b, provenance_to_allocation_id pr)) init_bytes) (ptr_to_int ptr) (mem_state_memory ms_init) ->
        extend_reads ms_init ptrs init_bytes ms_extended.
    Proof.
      intros ms_init ms_found_free ms_extended pr ptr ptrs init_bytes [MS FREE] MEM.
      inv MS; inv FREE.
      split.
      - intros p ix byte NTHptr NTHbyte.
        eapply @read_byte_get_consecutive_ptrs with (HM:=@Monad_itree Eff); try typeclasses eauto.
        unfold mem_state_memory in *.
        cbn; eauto.

        intros mb INMB.
        apply in_map_iff in INMB as (sb & MBEQ & INSB).
        inv MBEQ.
        cbn. reflexivity.

        reflexivity.

        eapply get_consecutive_MemPropT_itree;
          eapply get_consecutive_ptrs_MemPropT_eq1; eauto.

        rewrite map_length; reflexivity.
        eauto.
        eauto.

        setoid_rewrite block_is_free_ptrs_provenance0; eauto.
        apply access_allowed_refl.
        eapply Nth_In; eauto.
      - intros ptr' DISJOINT.
        eapply @read_byte_preserved_get_consecutive_ptrs with (HM:=@Monad_itree Eff); try typeclasses eauto.
        unfold mem_state_memory in *.
        cbn; eauto.

        eapply get_consecutive_MemPropT_itree;
          eapply get_consecutive_ptrs_MemPropT_eq1; eauto.

        rewrite map_length; reflexivity.
    Qed.

    (* TODO: Move and reuse *)
    Lemma read_byte_allowed_get_consecutive_ptrs :
      forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
        `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
        `{LAWS : @MonadLawsE M EQM HM}

        (ms ms' : MemState) (ptr : addr) (len : nat) (ptrs : list addr)
        (bytes : list mem_byte) (aid : AllocationId),
        mem_state_memory ms' = add_all_index bytes (ptr_to_int ptr) (mem_state_memory ms) ->
        (forall mb : mem_byte, In mb bytes -> snd mb = aid) ->
        (@get_consecutive_ptrs M HM OOM ERR ptr len ≈ ret ptrs)%monad ->
        (length bytes = len) ->
        forall p, In p ptrs ->
             access_allowed (address_provenance p) aid ->
             read_byte_allowed ms' p.
    Proof.
      intros M HM OOM ERR EQM' EQV EQRET LAWS ms ms' ptr len ptrs
             bytes aid MEM2 INMB CONSEC BYTELEN p IN ACCESS.
      unfold read_byte_allowed.
      eexists.
      split; eauto.
      - eapply byte_allocated_get_consecutive_ptrs;
          subst; eauto.
    Qed.

    (* TODO: Move and reuse *)
    Lemma read_byte_allowed_preserved_get_consecutive_ptrs :
      forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
        `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
        `{LAWS : @MonadLawsE M EQM HM}

        (ms ms' : MemState) (ptr : addr) (len : nat) (ptrs : list addr)
        (bytes : list mem_byte) (p : addr),
        mem_state_memory ms' = add_all_index bytes (ptr_to_int ptr) (mem_state_memory ms) ->
        (@get_consecutive_ptrs M HM OOM ERR ptr len ≈ ret ptrs)%monad ->
        (length bytes = len) ->
        (forall new_p, In new_p ptrs -> disjoint_ptr_byte new_p p) ->
        read_byte_allowed ms p <->
          read_byte_allowed ms' p.
    Proof.
      intros M HM OOM ERR EQM' EQV EQRET LAWS ms ms' ptr len ptrs
             bytes p MEM2 CONSEC BYTELEN DISJOINT.
      split; intros ALLOC.
      - break_read_byte_allowed_hyps.
        eexists; split; eauto.
        eapply byte_allocated_preserved_get_consecutive_ptrs with (ms := ms) (ms' := ms');
          subst; eauto.
      - break_read_byte_allowed_hyps.
        eexists; split; eauto.
        eapply byte_allocated_preserved_get_consecutive_ptrs with (ms := ms) (ms' := ms');
          eauto.
    Qed.

    Lemma find_free_block_extend_read_byte_allowed :
      forall ms_init ms_found_free ms_extended pr ptr ptrs init_bytes,
        find_free_block (length init_bytes) pr ms_init (ret (ms_found_free, (ptr, ptrs))) ->
        mem_state_memory ms_extended = add_all_index (map (fun b : SByte => (b, provenance_to_allocation_id pr)) init_bytes) (ptr_to_int ptr) (mem_state_memory ms_init) ->
        extend_read_byte_allowed ms_init ptrs ms_extended.
    Proof.
      intros ms_init ms_found_free ms_extended pr ptr ptrs init_bytes [MS FREE] MEM.
      inv MS; inv FREE.
      split.
      - intros p IN.
        eapply @read_byte_allowed_get_consecutive_ptrs with (HM:=@Monad_itree Eff); try typeclasses eauto.
        unfold mem_state_memory in *.
        cbn; eauto.

        intros mb INMB.
        apply in_map_iff in INMB as (sb & MBEQ & INSB).
        inv MBEQ.
        cbn. reflexivity.

        eapply get_consecutive_MemPropT_itree;
          eapply get_consecutive_ptrs_MemPropT_eq1; eauto.

        rewrite map_length; reflexivity.
        eauto.

        setoid_rewrite block_is_free_ptrs_provenance0; eauto.
        apply access_allowed_refl.                
      - intros ptr' DISJOINT.
        eapply @read_byte_allowed_preserved_get_consecutive_ptrs with (HM:=@Monad_itree Eff); try typeclasses eauto.
        unfold mem_state_memory in *.
        cbn; eauto.

        eapply get_consecutive_MemPropT_itree;
          eapply get_consecutive_ptrs_MemPropT_eq1; eauto.

        rewrite map_length; reflexivity.
        eauto.
    Qed.

    (* TODO: Move and reuse *)
    Lemma write_byte_allowed_get_consecutive_ptrs :
      forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
        `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
        `{LAWS : @MonadLawsE M EQM HM}

        (ms ms' : MemState) (ptr : addr) (len : nat) (ptrs : list addr)
        (bytes : list mem_byte) (aid : AllocationId),
        mem_state_memory ms' = add_all_index bytes (ptr_to_int ptr) (mem_state_memory ms) ->
        (forall mb : mem_byte, In mb bytes -> snd mb = aid) ->
        (@get_consecutive_ptrs M HM OOM ERR ptr len ≈ ret ptrs)%monad ->
        (length bytes = len) ->
        forall p, In p ptrs ->
             access_allowed (address_provenance p) aid ->
             write_byte_allowed ms' p.
    Proof.
      intros M HM OOM ERR EQM' EQV EQRET LAWS ms ms' ptr len ptrs
             bytes aid MEM2 INMB CONSEC BYTELEN p IN ACCESS.
      unfold write_byte_allowed.
      eexists.
      split; eauto.
      - eapply byte_allocated_get_consecutive_ptrs;
          subst; eauto.
    Qed.

    (* TODO: Move and reuse *)
    Lemma write_byte_allowed_preserved_get_consecutive_ptrs :
      forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
        `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
        `{LAWS : @MonadLawsE M EQM HM}

        (ms ms' : MemState) (ptr : addr) (len : nat) (ptrs : list addr)
        (bytes : list mem_byte) (p : addr),
        mem_state_memory ms' = add_all_index bytes (ptr_to_int ptr) (mem_state_memory ms) ->
        (@get_consecutive_ptrs M HM OOM ERR ptr len ≈ ret ptrs)%monad ->
        (length bytes = len) ->
        (forall new_p, In new_p ptrs -> disjoint_ptr_byte new_p p) ->
        write_byte_allowed ms p <->
          write_byte_allowed ms' p.
    Proof.
      intros M HM OOM ERR EQM' EQV EQRET LAWS ms ms' ptr len ptrs
             bytes p MEM2 CONSEC BYTELEN DISJOINT.
      split; intros ALLOC.
      - break_write_byte_allowed_hyps.
        eexists; split; eauto.
        eapply byte_allocated_preserved_get_consecutive_ptrs with (ms := ms) (ms' := ms');
          subst; eauto.
      - break_write_byte_allowed_hyps.
        eexists; split; eauto.
        eapply byte_allocated_preserved_get_consecutive_ptrs with (ms := ms) (ms' := ms');
          eauto.
    Qed.

    Lemma find_free_block_extend_write_byte_allowed :
      forall ms_init ms_found_free ms_extended pr ptr ptrs init_bytes,
        find_free_block (length init_bytes) pr ms_init (ret (ms_found_free, (ptr, ptrs))) ->
        mem_state_memory ms_extended = add_all_index (map (fun b : SByte => (b, provenance_to_allocation_id pr)) init_bytes) (ptr_to_int ptr) (mem_state_memory ms_init) ->
        extend_write_byte_allowed ms_init ptrs ms_extended.
    Proof.
      intros ms_init ms_found_free ms_extended pr ptr ptrs init_bytes [MS FREE] MEM.
      inv MS; inv FREE.
      split.
      - intros p IN.
        eapply @write_byte_allowed_get_consecutive_ptrs with (HM:=@Monad_itree Eff); try typeclasses eauto.
        unfold mem_state_memory in *.
        cbn; eauto.

        intros mb INMB.
        apply in_map_iff in INMB as (sb & MBEQ & INSB).
        inv MBEQ.
        cbn. reflexivity.

        eapply get_consecutive_MemPropT_itree;
          eapply get_consecutive_ptrs_MemPropT_eq1; eauto.

        rewrite map_length; reflexivity.
        eauto.

        setoid_rewrite block_is_free_ptrs_provenance0; eauto.
        apply access_allowed_refl.                
      - intros ptr' DISJOINT.
        eapply @read_byte_allowed_preserved_get_consecutive_ptrs with (HM:=@Monad_itree Eff); try typeclasses eauto.
        unfold mem_state_memory in *.
        cbn; eauto.

        eapply get_consecutive_MemPropT_itree;
          eapply get_consecutive_ptrs_MemPropT_eq1; eauto.

        rewrite map_length; reflexivity.
        eauto.
    Qed.

    (* TODO: Move and reuse *)
    Lemma free_byte_allowed_get_consecutive_ptrs :
      forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
        `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
        `{LAWS : @MonadLawsE M EQM HM}

        (ms ms' : MemState) (ptr : addr) (len : nat) (ptrs : list addr)
        (bytes : list mem_byte) (aid : AllocationId),
        mem_state_memory ms' = add_all_index bytes (ptr_to_int ptr) (mem_state_memory ms) ->
        (forall mb : mem_byte, In mb bytes -> snd mb = aid) ->
        (@get_consecutive_ptrs M HM OOM ERR ptr len ≈ ret ptrs)%monad ->
        (length bytes = len) ->
        forall p, In p ptrs ->
             access_allowed (address_provenance p) aid ->
             free_byte_allowed ms' p.
    Proof.
      intros M HM OOM ERR EQM' EQV EQRET LAWS ms ms' ptr len ptrs
             bytes aid MEM2 INMB CONSEC BYTELEN p IN ACCESS.
      unfold free_byte_allowed.
      eexists.
      split; eauto.
      - eapply byte_allocated_get_consecutive_ptrs;
          subst; eauto.
    Qed.

    (* TODO: Move and reuse *)
    Lemma free_byte_allowed_preserved_get_consecutive_ptrs :
      forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
        `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
        `{LAWS : @MonadLawsE M EQM HM}

        (ms ms' : MemState) (ptr : addr) (len : nat) (ptrs : list addr)
        (bytes : list mem_byte) (p : addr),
        mem_state_memory ms' = add_all_index bytes (ptr_to_int ptr) (mem_state_memory ms) ->
        (@get_consecutive_ptrs M HM OOM ERR ptr len ≈ ret ptrs)%monad ->
        (length bytes = len) ->
        (forall new_p, In new_p ptrs -> disjoint_ptr_byte new_p p) ->
        read_byte_allowed ms p <->
          read_byte_allowed ms' p.
    Proof.
      intros M HM OOM ERR EQM' EQV EQRET LAWS ms ms' ptr len ptrs
             bytes p MEM2 CONSEC BYTELEN DISJOINT.
      split; intros ALLOC.
      - break_read_byte_allowed_hyps.
        eexists; split; eauto.
        eapply byte_allocated_preserved_get_consecutive_ptrs with (ms := ms) (ms' := ms');
          subst; eauto.
      - break_read_byte_allowed_hyps.
        eexists; split; eauto.
        eapply byte_allocated_preserved_get_consecutive_ptrs with (ms := ms) (ms' := ms');
          eauto.
    Qed.

    Lemma find_free_block_extend_free_byte_allowed :
      forall ms_init ms_found_free ms_extended pr ptr ptrs init_bytes,
        find_free_block (length init_bytes) pr ms_init (ret (ms_found_free, (ptr, ptrs))) ->
        mem_state_memory ms_extended = add_all_index (map (fun b : SByte => (b, provenance_to_allocation_id pr)) init_bytes) (ptr_to_int ptr) (mem_state_memory ms_init) ->
        extend_free_byte_allowed ms_init ptrs ms_extended.
    Proof.
      intros ms_init ms_found_free ms_extended pr ptr ptrs init_bytes [MS FREE] MEM.
      inv MS; inv FREE.
      split.
      - intros p IN.
        eapply @free_byte_allowed_get_consecutive_ptrs with (HM:=@Monad_itree Eff); try typeclasses eauto.
        unfold mem_state_memory in *.
        cbn; eauto.

        intros mb INMB.
        apply in_map_iff in INMB as (sb & MBEQ & INSB).
        inv MBEQ.
        cbn. reflexivity.

        eapply get_consecutive_MemPropT_itree;
          eapply get_consecutive_ptrs_MemPropT_eq1; eauto.

        rewrite map_length; reflexivity.
        eauto.

        setoid_rewrite block_is_free_ptrs_provenance0; eauto.
        apply access_allowed_refl.                
      - intros ptr' DISJOINT.
        eapply @free_byte_allowed_preserved_get_consecutive_ptrs with (HM:=@Monad_itree Eff); try typeclasses eauto.
        unfold mem_state_memory in *.
        cbn; eauto.

        eapply get_consecutive_MemPropT_itree;
          eapply get_consecutive_ptrs_MemPropT_eq1; eauto.

        rewrite map_length; reflexivity.
        eauto.
    Qed.

    (* TODO: Pull out lemmas and clean up + fix admits *)
    Lemma add_block_to_stack_correct :
      forall dt pr ms_init ptr ptrs init_bytes,
        sizeof_dtyp dt = N.of_nat (Datatypes.length init_bytes) ->
        exec_correct
          (fun ms_k _ => find_free_block (Datatypes.length init_bytes) pr ms_init (ret (ms_k, (ptr, ptrs))))
          (_ <- add_block_to_stack (provenance_to_allocation_id pr) ptr ptrs init_bytes;; ret ptr)
          (_ <- allocate_bytes_post_conditions_MemPropT dt init_bytes pr ptr ptrs;; ret ptr).
    Proof.
      intros dt pr ms_init ptr ptrs init_bytes SIZE.
      unfold exec_correct.
      intros ms st VALID PRE.

      (* Need to destruct ahead of time so we know if UB happens *)
      pose proof (dtyp_eq_dec dt DTYPE_Void) as [VOID | NVOID].
      { (* UB because void type allocated to stack *)
        left.
        cbn.
        exists ""%string.
        tauto.
      }

      (* No UB because type allocated isn't void *)
      right.
      unfold add_block_to_stack, add_block, add_ptrs_to_frame.

      right.
      right.

      destruct ms.
      destruct ms_memory_stack0.

      eexists.
      eexists.
      exists ptr.

      repeat rewrite MemMonad_run_bind.
      repeat rewrite bind_bind.
      rewrite MemMonad_get_mem_state.
      rewrite bind_ret_l.

      cbn.

      rewrite MemMonad_put_mem_state.
      rewrite bind_ret_l.

      unfold modify_mem_state.
      repeat rewrite MemMonad_run_bind.
      repeat rewrite bind_bind.

      rewrite MemMonad_get_mem_state.
      rewrite bind_ret_l.
      repeat rewrite MemMonad_run_bind.
      repeat rewrite bind_bind.

      rewrite MemMonad_put_mem_state.
      repeat (first [rewrite MemMonad_run_ret; rewrite bind_ret_l]).
      rewrite bind_ret_l.
      repeat (first [rewrite MemMonad_run_ret; rewrite bind_ret_l]).
      rewrite MemMonad_run_ret.
      cbn.
      split; [reflexivity|].
      split.
      - eexists. exists (ptr, ptrs).
        split; auto.
        split; auto.

        (* TODO: solve_allocate_bytes_post_conditions *)
        (* TODO: move, generalize *)
        Lemma find_free_allocate_bytes_post_conditions :
          forall (ms_init ms_found_free ms_final : MemState) dt init_bytes pr ptr ptrs
            memory_stack_memory0 memory_stack_frame_stack0 memory_stack_heap0 ms_provenance0
            (SIZE : sizeof_dtyp dt = N.of_nat (length init_bytes))
            (NVOID : dt <> DTYPE_Void)
            (EQ : ms_found_free = {| ms_memory_stack :=
                                    {|
                                      memory_stack_memory := memory_stack_memory0;
                                      memory_stack_frame_stack := memory_stack_frame_stack0;
                                      memory_stack_heap := memory_stack_heap0
                                    |};
                                    ms_provenance := ms_provenance0
                                  |})
            (EQF : ms_final = 
                     {|
                       ms_memory_stack :=
                       add_all_to_frame
                         {|
                           memory_stack_memory :=
                           add_all_index (map (fun b : SByte => (b, provenance_to_allocation_id pr)) init_bytes)
                                         (ptr_to_int ptr) memory_stack_memory0;
                           memory_stack_frame_stack := memory_stack_frame_stack0;
                           memory_stack_heap := memory_stack_heap0
                         |} (map ptr_to_int ptrs);
                       ms_provenance := ms_provenance0
                     |})
            (FIND_FREE : find_free_block (length init_bytes) pr ms_init (ret (ms_found_free, (ptr, ptrs)))),
          allocate_bytes_post_conditions ms_found_free dt init_bytes pr ms_final ptr ptrs.
        Proof.
          intros ms_init ms_found_free ms_final dt init_bytes pr ptr ptrs memory_stack_memory0
                 memory_stack_frame_stack0 memory_stack_heap0 ms_provenance0 SIZE EQ EQF FIND_FREE.
          subst.
          split.
          + solve_used_provenance_prop.
            solve_provenances_preserved.
          + (* extend_allocations *)
            pose proof FIND_FREE as FIND_FREE'.
            eapply find_free_block_ms_eq in FIND_FREE'; subst.
            eapply find_free_block_extend_allocations; [solve [eauto] | solve_mem_state_memory].
          + (* extend_read_byte_allowed *)
            pose proof FIND_FREE as PRE.
            eapply find_free_block_ms_eq in PRE; subst.
            eapply find_free_block_extend_read_byte_allowed; [solve [eauto] | solve_mem_state_memory].
          + pose proof FIND_FREE as PRE.
            eapply find_free_block_ms_eq in PRE; subst.
            eapply find_free_block_extend_reads; [solve [eauto] | solve_mem_state_memory].
          + (* extend_write_byte_allowed *)
            pose proof FIND_FREE as PRE.
            eapply find_free_block_ms_eq in PRE; subst.
            eapply find_free_block_extend_write_byte_allowed; [solve [eauto] | solve_mem_state_memory].
          + (* extend_stack_frame *)
            (* TODO: Tactic or lemma? *)
            unfold extend_stack_frame.
            intros fs1 fs2 MFSP PTRS_ADDED.
            unfold memory_stack_frame_stack_prop in *.
            cbn in *.
            setoid_rewrite <- MFSP in PTRS_ADDED.
            apply add_ptrs_to_frame_eqv with (fs:=memory_stack_frame_stack0) (ptrs:=ptrs); auto.

            assert (memory_stack_frame_stack0 = memory_stack_frame_stack {|
                    memory_stack_memory := 
                     add_all_index (map (fun b : SByte => (b, provenance_to_allocation_id pr)) init_bytes)
                     (ptr_to_int ptr) memory_stack_memory0;
                    memory_stack_frame_stack := memory_stack_frame_stack0;
                    memory_stack_heap := memory_stack_heap0
                                                  |}) as EQFS by reflexivity.
            rewrite EQFS at 1.
            eapply add_all_to_frame_correct; auto.
          + solve_heap_preserved.
          + auto.
          + auto.
        Qed.

        (* TODO: move *)
        Lemma find_free_allocate_bytes_post_conditions_exists :
          forall (ms_init ms_found_free : MemState) dt init_bytes pr ptr ptrs
            (SIZE : sizeof_dtyp dt = N.of_nat (length init_bytes))
            (NVOID : dt <> DTYPE_Void)
            (FIND_FREE : find_free_block (length init_bytes) pr ms_init (ret (ms_found_free, (ptr, ptrs)))),
        exists ms_final,
          allocate_bytes_post_conditions ms_found_free dt init_bytes pr ms_final ptr ptrs.
        Proof.
          intros ms_init ms_found_free dt init_bytes pr ptr ptrs SIZE FIND_FREE.
          destruct ms_found_free.
          destruct ms_memory_stack0.
          eexists.
          eapply find_free_allocate_bytes_post_conditions; eauto.
        Qed.

        eapply find_free_allocate_bytes_post_conditions; eauto.
      - admit. (* MemMonad_valid_state *)
    Admitted.

    (* TODO: Pull out lemmas and clean up + fix admits *)
    Lemma add_block_to_heap_correct :
      forall pr ms_init ptr ptrs init_bytes,
        exec_correct
          (fun ms_k _ => find_free_block (Datatypes.length init_bytes) pr ms_init (ret (ms_k, (ptr, ptrs))))
          (_ <- add_block_to_heap (provenance_to_allocation_id pr) ptr ptrs init_bytes;; ret ptr)
          (_ <- malloc_bytes_post_conditions_MemPropT init_bytes pr ptr ptrs;; ret ptr).
    Proof.
      intros pr ms_init ptr ptrs init_bytes.
      unfold exec_correct.
      intros ms st VALID PRE.

      (* No UB because type allocated isn't void *)
      right.
      unfold add_block_to_heap, add_block, add_ptrs_to_heap.

      right.
      right.

      destruct ms.
      destruct ms_memory_stack0.

      eexists.
      eexists.
      exists ptr.

      repeat rewrite MemMonad_run_bind.
      repeat rewrite bind_bind.
      rewrite MemMonad_get_mem_state.
      rewrite bind_ret_l.

      cbn.

      rewrite MemMonad_put_mem_state.
      rewrite bind_ret_l.

      unfold modify_mem_state.
      repeat rewrite MemMonad_run_bind.
      repeat rewrite bind_bind.

      rewrite MemMonad_get_mem_state.
      rewrite bind_ret_l.
      repeat rewrite MemMonad_run_bind.
      repeat rewrite bind_bind.

      rewrite MemMonad_put_mem_state.
      repeat (first [rewrite MemMonad_run_ret; rewrite bind_ret_l]).
      rewrite bind_ret_l.
      repeat (first [rewrite MemMonad_run_ret; rewrite bind_ret_l]).
      rewrite MemMonad_run_ret.
      cbn.
      split; [reflexivity|].
      split.
      - eexists. exists (ptr, ptrs).
        split; auto.
        split; auto.

        (* TODO: solve_allocate_bytes_post_conditions *)
        (* TODO: I think this can be a lemma... *)

    (*          find_free_block -> allocate_bytes_post_conditions *)
    (*      *)
        split.
        + solve_used_provenance_prop.
          solve_provenances_preserved.
        + (* extend_allocations *)
          pose proof PRE as FREE.
          eapply find_free_block_ms_eq in PRE; subst.
          eapply find_free_block_extend_allocations; [solve [eauto] | solve_mem_state_memory].  
        + (* extend_read_byte_allowed *)
          pose proof PRE as FREE.
          eapply find_free_block_ms_eq in PRE; subst.
          eapply find_free_block_extend_read_byte_allowed; [solve [eauto] | solve_mem_state_memory].

        + pose proof PRE as FREE.
          eapply find_free_block_ms_eq in PRE; subst.
          eapply find_free_block_extend_reads; [solve [eauto] | solve_mem_state_memory].
        + (* extend_write_byte_allowed *)
          pose proof PRE as FREE.
          eapply find_free_block_ms_eq in PRE; subst.
          eapply find_free_block_extend_write_byte_allowed; [solve [eauto] | solve_mem_state_memory].
        + (* extend_free_byte_allowed *)
          pose proof PRE as FREE.
          eapply find_free_block_ms_eq in PRE; subst.
          eapply find_free_block_extend_free_byte_allowed; [solve [eauto] | solve_mem_state_memory].
        + admit.
        + (* TODO: extend heap *)
          admit.
      - admit. (* MemMonad_valid_state *)
    Admitted.

    Lemma allocate_bytes_correct :
      forall dt init_bytes pre, exec_correct pre (allocate_bytes dt init_bytes) (allocate_bytes_spec_MemPropT dt init_bytes).
    Proof.
      Opaque exec_correct.
      intros dt init_bytes pre.

      unfold allocate_bytes, allocate_bytes_spec_MemPropT.
      apply exec_correct_bind; eauto with EXEC_CORRECT.
      intros pr ms ms_fresh_pr st st' FRESH_EXEC.

      apply exec_correct_bind; eauto with EXEC_CORRECT.
      intros [ptr ptrs] ms' ms_find_free st'' st_find_free GET_FREE.

      (* Need to destruct ahead of time so we know if UB happens *)
      pose proof (dtyp_eq_dec dt DTYPE_Void) as [VOID | NVOID].

      { (* UB because dt is void *)
        break_match; try contradiction.

        unfold allocate_bytes_post_conditions_MemPropT.
        (* Can probably clean this up into a lemma *)
        Transparent exec_correct.
        left.
        Opaque exec_correct.
        cbn.
        exists ""%string. auto.
      }

      (* dt is non-void, allocation may succeed *)
      break_match; try contradiction.

      (* UB if size of dtyp and number of bytes being initialized differs *)
      break_match.
      2: { (* Size of bytes mismatch *)
        unfold allocate_bytes_post_conditions_MemPropT.
        (* Can probably clean this up into a lemma *)
        Transparent exec_correct.
        left.
        Opaque exec_correct.
        cbn.
        exists ""%string. auto.
      }

      eapply exec_correct_weaken_pre with (weak_pre := fun ms st => find_free_block (Datatypes.length init_bytes) pr ms' (ret (ms, (ptr, ptrs)))); [tauto|].
      eapply add_block_to_stack_correct; eauto.
    Qed.

    (* TODO: move and add to solve_read_byte_allowed *)
    Lemma read_byte_allowed_add_all_index :
      forall (ms : MemState) (mem : memory) (bytes : list mem_byte) (ix : Z) (aid : AllocationId),
        mem_state_memory ms = add_all_index bytes ix mem ->
        (forall mb, In mb bytes -> snd mb = aid) ->
        (forall p,
            ix <= ptr_to_int p < ix + (Z.of_nat (length bytes)) ->
            access_allowed (address_provenance p) aid ->
            read_byte_allowed ms p).
    Proof.
      intros ms mem bytes ix aid MEM AID p IN_BOUNDS ACCESS_ALLOWED.
      unfold read_byte_allowed.
      exists aid. split; auto.
      eapply byte_allocated_add_all_index; eauto.
    Qed.

    (* TODO: move and add to solve_read_byte_allowed *)
    Lemma read_byte_add_all_index :
      forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
        `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
        `{LAWS : @MonadLawsE M EQM HM}
        `{RAISE_OOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
        `{RAISE_ERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}

        (ms : MemState) (mem : memory) (bytes : list mem_byte)
        (byte : SByte) (offset : nat) (aid : AllocationId) p ptr ptrs,

        mem_state_memory ms = add_all_index bytes (ptr_to_int ptr) mem ->
        Util.Nth bytes offset (byte, aid) ->
        (@get_consecutive_ptrs M HM OOM ERR ptr (length bytes) ≈ ret ptrs)%monad ->
        Util.Nth ptrs offset p ->
        access_allowed (address_provenance p) aid ->
        read_byte_prop ms p byte.
    Proof.
      intros M HM OOM ERR EQM' EQV EQRET LAWS
             RAISE_OOM RAISE_ERR
             ms mem bytes byte offset aid p ptr ptrs
             MEM BYTE CONSEC PTR ACCESS_ALLOWED.

      unfold read_byte_prop, read_byte_MemPropT.
      cbn.
      do 2 eexists; split; auto.

      unfold mem_state_memory in *.
      rewrite MEM.
      erewrite read_byte_raw_add_all_index_in with (v := (byte, aid)).

      { cbn.
        rewrite ACCESS_ALLOWED.
        auto.
      }

      { eapply get_consecutive_ptrs_range with (p:=p) in CONSEC.
        rewrite Zlength_correct.
        lia.
        eapply Nth_In; eauto.
      }

      { eapply get_consecutive_ptrs_nth in CONSEC; eauto.
        destruct CONSEC as (ip_offset & FROMZ & GEP).
        eapply GEP.handle_gep_addr_ix in GEP.
        rewrite sizeof_dtyp_i8 in GEP.
        assert (ptr_to_int p - ptr_to_int ptr = IP.to_Z ip_offset) as EQOFF by lia.
        symmetry in FROMZ; apply IP.from_Z_to_Z in FROMZ.
        rewrite FROMZ in EQOFF.
        rewrite EQOFF.
        eapply Nth_list_nth_z; eauto.
      }
      all: typeclasses eauto.
    Qed.

    (* TODO: move and add to solve_read_byte_allowed *)
    Lemma write_byte_allowed_add_all_index :
      forall (ms : MemState) (mem : memory) (bytes : list mem_byte) (ix : Z) (aid : AllocationId),
        mem_state_memory ms = add_all_index bytes ix mem ->
        (forall mb, In mb bytes -> snd mb = aid) ->
        (forall p,
            ix <= ptr_to_int p < ix + (Z.of_nat (length bytes)) ->
            access_allowed (address_provenance p) aid ->
            write_byte_allowed ms p).
    Proof.
      intros ms mem bytes ix aid MEM AID p IN_BOUNDS ACCESS_ALLOWED.
      unfold read_byte_allowed.
      exists aid. split; auto.
      eapply byte_allocated_add_all_index; eauto.
    Qed.

    (** Malloc correctness *)
    Lemma malloc_bytes_correct :
      forall init_bytes pre, exec_correct pre (malloc_bytes init_bytes) (malloc_bytes_spec_MemPropT init_bytes).
    Proof.
      intros init_bytes pre.

      unfold malloc_bytes.
      apply exec_correct_bind; eauto with EXEC_CORRECT.
      intros pr ms ms_fresh_pr st st' FRESH_EXEC.

      apply exec_correct_bind; eauto with EXEC_CORRECT.
      intros [ptr ptrs] ms' ms_find_free st'' st_find_free GET_FREE.

      eapply exec_correct_weaken_pre with (weak_pre := fun ms st => find_free_block (Datatypes.length init_bytes) pr ms' (ret (ms, (ptr, ptrs)))); [tauto|].
      eapply add_block_to_heap_correct; eauto.
    Qed.

    (** Correctness of frame stack operations *)
    Lemma mempush_correct :
      forall pre, exec_correct pre mempush mempush_spec_MemPropT.
    Proof.
      Transparent exec_correct.
      unfold exec_correct.
      intros pre ms st VALID PRE.

      right; right; right.
      cbn.

      do 3 eexists.
      split.
      - unfold mempush.
        rewrite MemMonad_run_bind.
        rewrite MemMonad_get_mem_state.
        rewrite bind_ret_l.
        rewrite MemMonad_put_mem_state.
        reflexivity.
      - split.
        + split.
          -- (* fresh_frame *)
            intros fs1 fs2 f POP EMPTY PUSH.
            pose proof empty_frame_eqv _ _ EMPTY initial_frame_empty as EQinit.

            (* This:

               (mem_state_set_frame_stack ms (push_frame_stack (mem_state_frame_stack ms) initial_frame))

               Should be equivalent to (f :: fs1).
             *)
            eapply mem_state_frame_stack_prop_set_trans; [|apply mem_state_frame_stack_prop_set_refl].

            pose proof (eq_refl (push_frame_stack (mem_state_frame_stack ms) initial_frame)) as PUSH_INIT.
            apply push_frame_stack_correct in PUSH_INIT.

            unfold mem_state_frame_stack_prop in POP.
            red in POP.
            rewrite <- POP in PUSH.
            rewrite EQinit in PUSH.

            eapply push_frame_stack_inj; eauto.
          -- (* mempush_invariants *)
            split.
            ++ (* read_byte_preserved *)
              (* TODO: solve_read_byte_preserved. *)
              split.
              ** (* solve_read_byte_allowed_all_preserved. *)
                intros ?ptr; split; intros ?READ.
                --- (* read_byte_allowed *)
                  apply read_byte_allowed_set_frame_stack; eauto.
                --- (* read_byte_allowed *)
                  (* TODO: solve_read_byte_allowed *)
                  eapply read_byte_allowed_set_frame_stack; eauto.
              ** (* solve_read_byte_prop_all_preserved. *)
                apply read_byte_prop_set_frame_stack.
            ++ (* write_byte_allowed_all_preserved *)
              apply write_byte_allowed_all_preserved_set_frame_stack.
            ++ (* free_byte_allowed_all_preserved *)
              apply free_byte_allowed_all_preserved_set_frame_stack.
            ++ (* allocations_preserved *)
              (* TODO: move to solve_allocations_preserved *)
              apply allocations_preserved_set_frame_stack.
            ++ (* preserve_allocation_ids *)
              (* TODO: solve_preserve_allocation_ids *)
              apply preserve_allocation_ids_set_frame_stack.
            ++ (* TODO: solve_heap_preserved. *)
              unfold mem_state_set_frame_stack.
              red.
              unfold memory_stack_heap_prop. cbn.
              unfold memory_stack_heap.
              destruct ms.
              cbn.
              unfold MemState_get_memory.
              unfold mem_state_memory_stack.
              break_match.
              cbn.
              reflexivity.
        + (* MemMonad_valid_state *)
          admit.
    Admitted.

    (* TODO: move *)
    Lemma read_byte_raw_memory_empty :
      forall ptr,
        read_byte_raw memory_empty ptr = None.
    Proof.
      intros ptr.
      Transparent read_byte_raw.
      unfold read_byte_raw.
      Opaque read_byte_raw.
      unfold memory_empty.
      apply IP.F.empty_o.
    Qed.

    Lemma free_byte_read_byte_raw :
      forall m m' ptr,
        free_byte ptr m = m' ->
        read_byte_raw m' ptr = None.
    Proof.
      intros m m' ptr FREE.
      Transparent read_byte_raw.
      unfold read_byte_raw.
      Opaque read_byte_raw.
      unfold free_byte in FREE.
      subst.
      apply IP.F.remove_eq_o; auto.
    Qed.

    Lemma free_frame_memory_cons :
      forall f m m' a,
        free_frame_memory (a :: f) m = m' ->
        exists m'',
          free_byte a m  = m'' /\
            free_frame_memory f m'' = m'.
    Proof.
      intros f m m' a FREE.
      rewrite list_cons_app in FREE.
      unfold free_frame_memory in *.
      rewrite fold_left_app in FREE.
      set (m'' := fold_left (fun (m : memory) (key : Iptr) => free_byte key m) [a] m).
      exists m''.
      subst m''.
      cbn; split; auto.
    Qed.

    Lemma free_block_memory_cons :
      forall block m m' a,
        free_block_memory (a :: block) m = m' ->
        exists m'',
          free_byte a m  = m'' /\
            free_block_memory block m'' = m'.
    Proof.
      intros f m m' a FREE.
      rewrite list_cons_app in FREE.
      unfold free_block_memory in *.
      rewrite fold_left_app in FREE.
      set (m'' := fold_left (fun (m : memory) (key : Iptr) => free_byte key m) [a] m).
      exists m''.
      subst m''.
      cbn; split; auto.
    Qed.

    Lemma free_byte_no_add :
      forall m m' ptr ptr',
        read_byte_raw m ptr = None ->
        free_byte ptr' m = m' ->
        read_byte_raw m' ptr = None.
    Proof.
      intros m m' ptr ptr' READ FREE.
      Transparent read_byte_raw.
      unfold read_byte_raw in *.
      Opaque read_byte_raw.
      unfold free_byte in FREE.
      subst.
      rewrite IP.F.remove_o.
      break_match; auto.
    Qed.

    Lemma free_frame_memory_no_add :
      forall f m m' ptr,
        read_byte_raw m ptr = None ->
        free_frame_memory f m = m' ->
        read_byte_raw m' ptr = None.
    Proof.
      induction f; intros m m' ptr READ FREE.
      - inv FREE; auto.
      - apply free_frame_memory_cons in FREE.
        destruct FREE as [m'' [FREEBYTE FREE]].

        eapply IHf.
        eapply free_byte_no_add; eauto.
        eauto.
    Qed.

    Lemma free_block_memory_no_add :
      forall block m m' ptr,
        read_byte_raw m ptr = None ->
        free_block_memory block m = m' ->
        read_byte_raw m' ptr = None.
    Proof.
      apply free_frame_memory_no_add.
    Qed.

    Lemma free_frame_memory_read_byte_raw :
      forall (f : Frame) (m m' : memory) ptr,
        free_frame_memory f m = m' ->
        ptr_in_frame_prop f ptr ->
        read_byte_raw m' (ptr_to_int ptr) = None.
    Proof.
      induction f;
        intros m m' ptr FREE IN.

      - inv IN.
      - apply free_frame_memory_cons in FREE.
        destruct FREE as [m'' [FREEBYTE FREE]].

        destruct IN as [IN | IN].
        + subst a.
          eapply free_frame_memory_no_add; eauto.
          eapply free_byte_read_byte_raw; eauto.
        + eapply IHf; eauto.
    Qed.

    Lemma free_block_memory_read_byte_raw :
      forall (block : Block) (m m' : memory) ptr,
        free_block_memory block m = m' ->
        In (ptr_to_int ptr) block ->
        read_byte_raw m' (ptr_to_int ptr) = None.
    Proof.
      induction block;
        intros m m' ptr FREE IN.

      - inv IN.
      - apply free_block_memory_cons in FREE.
        destruct FREE as [m'' [FREEBYTE FREE]].

        destruct IN as [IN | IN].
        + subst a.
          eapply free_block_memory_no_add; eauto.
          eapply free_byte_read_byte_raw; eauto.
        + eapply IHblock; eauto.
    Qed.

    Lemma free_byte_byte_not_allocated :
      forall (ms ms' : MemState) (m m' : memory) (ptr : addr),
        free_byte (ptr_to_int ptr) m = m' ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        byte_not_allocated ms' ptr.
    Proof.
      intros ms ms' m m' ptr FREE MS MS'.
      intros aid CONTRA.
      break_byte_allocated_in CONTRA.
      cbn in CONTRA.
      break_match; [|inv CONTRA; inv H1].
      break_match. subst.

      symmetry in MS'.
      apply free_byte_read_byte_raw in MS'.
      unfold mem_state_memory in *.
      rewrite MS' in Heqo.
      inv Heqo.
    Qed.

    Lemma free_frame_memory_byte_not_allocated :
      forall (ms ms' : MemState) (m m' : memory) f (ptr : addr),
        free_frame_memory f m = m' ->
        ptr_in_frame_prop f ptr ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        byte_not_allocated ms' ptr.
    Proof.
      intros ms ms' m m' f ptr FREE IN MS MS'.
      intros aid CONTRA.
      break_byte_allocated_in CONTRA.
      cbn in CONTRA.
      break_match; [|inv CONTRA; inv H1].
      break_match. subst.

      symmetry in MS'.
      eapply free_frame_memory_read_byte_raw in MS'; eauto.
      unfold mem_state_memory in *.
      rewrite Heqo in MS'.
      inv MS'.
    Qed.

    Lemma free_block_memory_byte_not_allocated :
      forall (ms ms' : MemState) (m m' : memory) block (ptr : addr),
        free_block_memory block m = m' ->
        In (ptr_to_int ptr) block ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        byte_not_allocated ms' ptr.
    Proof.
      intros ms ms' m m' block ptr FREE IN MS MS'.
      intros aid CONTRA.
      break_byte_allocated_in CONTRA.
      cbn in CONTRA.
      break_match; [|inv CONTRA; inv H1].
      break_match. subst.

      symmetry in MS'.
      eapply free_frame_memory_read_byte_raw in MS'; eauto.
      unfold mem_state_memory in *.
      rewrite Heqo in MS'.
      inv MS'.
    Qed.

    (* TODO move these *)
    Lemma free_byte_disjoint :
      forall m m' ptr ptr',
        free_byte ptr' m = m' ->
        ptr <> ptr' ->
        read_byte_raw m' ptr = read_byte_raw m ptr.
    Proof.
      intros m m' ptr ptr' FREE NEQ.
      Transparent read_byte_raw.
      unfold read_byte_raw in *.
      Opaque read_byte_raw.
      unfold free_byte in FREE.
      subst.
      rewrite IP.F.remove_neq_o; auto.
    Qed.

    Lemma free_frame_memory_disjoint :
      forall f m m' ptr,
        ~ ptr_in_frame_prop f ptr ->
        free_frame_memory f m = m' ->
        read_byte_raw m' (ptr_to_int ptr) = read_byte_raw m (ptr_to_int ptr).
    Proof.
      induction f; intros m m' ptr NIN FREE.
      - inv FREE; auto.
      - apply free_frame_memory_cons in FREE.
        destruct FREE as [m'' [FREEBYTE FREE]].

        erewrite IHf with (m:=m'').
        eapply free_byte_disjoint; eauto.
        firstorder.
        firstorder.
        auto.
    Qed.

    Lemma free_frame_memory_read_byte_raw_disjoint :
      forall (f : Frame) (m m' : memory) ptr,
        free_frame_memory f m = m' ->
        ~ptr_in_frame_prop f ptr ->
        read_byte_raw m' (ptr_to_int ptr) = read_byte_raw m (ptr_to_int ptr).
    Proof.
      induction f;
        intros m m' ptr FREE IN.

      - inv FREE. cbn.
        auto.
      - apply free_frame_memory_cons in FREE.
        destruct FREE as [m'' [FREEBYTE FREE]].
        cbn in IN.

        erewrite free_frame_memory_disjoint with (m:=m''); eauto.
        erewrite free_byte_disjoint with (m:=m); eauto.
    Qed.

    Lemma free_byte_byte_disjoint_allocated :
      forall (ms ms' : MemState) (m m' : memory) (ptr ptr' : addr) aid,
        free_byte (ptr_to_int ptr) m = m' ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        disjoint_ptr_byte ptr ptr' ->
        byte_allocated ms ptr' aid <-> byte_allocated ms' ptr' aid.
    Proof.
      intros ms ms' m m' ptr ptr' aid FREE MS MS' DISJOINT.
      split; intro ALLOC.
      - destruct ms as [[ms fs] pr].
        break_byte_allocated_in ALLOC.
        cbn in ALLOC.
        unfold mem_state_memory in ALLOC.
        cbn in ALLOC.

        repeat eexists; [| solve_returns_provenance].
        unfold mem_state_memory in *.
        rewrite MS'.
        erewrite free_byte_disjoint; eauto.
        cbn in *.
        break_match.
        break_match.
        tauto.
        tauto.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        break_byte_allocated_in ALLOC.
        cbn in ALLOC.

        unfold mem_state_memory in *.
        rewrite MS' in ALLOC.
        erewrite free_byte_disjoint in ALLOC; eauto.

        repeat eexists; [| solve_returns_provenance].
        cbn.
        break_match.
        break_match.
        tauto.
        tauto.
    Qed.

    Lemma byte_allocated_mem_state_refl :
      forall (ms ms' : MemState) (m : memory) (ptr : addr) aid,
        mem_state_memory ms = m ->
        mem_state_memory ms' = m ->
        byte_allocated ms ptr aid <-> byte_allocated ms' ptr aid.
    Proof.
      intros ms ms' m ptr aid MEQ1 MEQ2.
      split; intros ALLOC.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        break_byte_allocated_in ALLOC.
        cbn in ALLOC.

        repeat eexists; [| solve_returns_provenance].
        unfold mem_state_memory in *.
        break_match.
        break_match.
        tauto.
        tauto.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        break_byte_allocated_in ALLOC.
        cbn in ALLOC.

        repeat eexists; [| solve_returns_provenance].
        unfold mem_state_memory in *.
        cbn.
        break_match.
        break_match.
        tauto.
        tauto.
    Qed.

    Lemma free_frame_memory_byte_disjoint_allocated :
      forall f (ms ms' : MemState) (m m' : memory) (ptr : addr) aid,
        free_frame_memory f m = m' ->
        ~ptr_in_frame_prop f ptr ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        byte_allocated ms ptr aid <-> byte_allocated ms' ptr aid.
    Proof.
      induction f;
        intros ms ms' m m' ptr aid FREE NIN MS MS'.
      - inv FREE.
        cbn in H0.
        eapply byte_allocated_mem_state_refl; eauto.
      - apply free_frame_memory_cons in FREE.
        destruct FREE as [m'' [FREEBYTE FREE]].

        set (aptr := int_to_ptr a nil_prov).
        erewrite free_byte_byte_disjoint_allocated
          with (ptr:=aptr) (ms':= mkMemState (mkMemoryStack m'' (Singleton initial_frame) initial_heap) initial_provenance).
        2: {
          subst aptr. rewrite ptr_to_int_int_to_ptr; eauto.
        }
        all: eauto.
        2: {
          subst aptr.
          unfold disjoint_ptr_byte.
          rewrite ptr_to_int_int_to_ptr.
          firstorder.
        }

        eapply IHf; eauto.
        firstorder.
    Qed.

    Lemma free_block_memory_byte_disjoint_allocated :
      forall block (ms ms' : MemState) (m m' : memory) (ptr : addr) aid,
        free_block_memory block m = m' ->
        ~In (ptr_to_int ptr) block ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        byte_allocated ms ptr aid <-> byte_allocated ms' ptr aid.
    Proof.
      induction block;
        intros ms ms' m m' ptr aid FREE NIN MS MS'.
      - inv FREE.
        cbn in H0.
        eapply byte_allocated_mem_state_refl; eauto.
      - apply free_block_memory_cons in FREE.
        destruct FREE as [m'' [FREEBYTE FREE]].

        set (aptr := int_to_ptr a nil_prov).
        erewrite free_byte_byte_disjoint_allocated
          with (ptr:=aptr) (ms':= mkMemState (mkMemoryStack m'' (Singleton initial_frame) initial_heap) initial_provenance).
        2: {
          subst aptr. rewrite ptr_to_int_int_to_ptr; eauto.
        }
        all: eauto.
        2: {
          subst aptr.
          unfold disjoint_ptr_byte.
          rewrite ptr_to_int_int_to_ptr.
          firstorder.
        }

        eapply IHblock; eauto.
        firstorder.
    Qed.

    Lemma peek_frame_stack_prop_frame_eqv :
      forall fs f f',
        peek_frame_stack_prop fs f ->
        peek_frame_stack_prop fs f' ->
        frame_eqv f f'.
    Proof.
      intros fs f f' PEEK1 PEEK2.
      destruct fs; cbn in *;
        rewrite <- PEEK2 in PEEK1;
        auto.
    Qed.

    Lemma ptr_nin_current_frame :
      forall ptr ms fs f,
        ~ ptr_in_current_frame ms ptr ->
        mem_state_frame_stack_prop ms fs ->
        peek_frame_stack_prop fs f ->
        ~ ptr_in_frame_prop f ptr.
    Proof.
      intros ptr ms fs f NIN FS PEEK IN.
      unfold ptr_in_current_frame in NIN.
      apply NIN.
      intros fs' FS' f' PEEK'.
      unfold mem_state_frame_stack_prop in *.
      unfold memory_stack_frame_stack_prop in *.
      rewrite FS in FS'.
      rewrite <- FS' in PEEK'.
      erewrite peek_frame_stack_prop_frame_eqv
        with (f:=f') (f':=f); eauto.
    Qed.

    (* TODO: move *)
    Lemma free_byte_byte_disjoint_read_byte_allowed :
      forall (ms ms' : MemState) (m m' : memory) (ptr ptr' : addr),
        free_byte (ptr_to_int ptr) m = m' ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        disjoint_ptr_byte ptr ptr' ->
        read_byte_allowed ms ptr' <-> read_byte_allowed ms' ptr'.
    Proof.
      intros ms ms' m m' ptr ptr' FREE MS MS' DISJOINT.
      split; intro READ.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        unfold read_byte_allowed in *.
        destruct READ as [aid READ].
        destruct READ as [READ ALLOWED].
        exists aid.
        split; eauto.
        subst ms.

        erewrite <- free_byte_byte_disjoint_allocated; eauto.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        unfold read_byte_allowed in *.
        destruct READ as [aid READ].
        destruct READ as [READ ALLOWED].
        exists aid.
        split; eauto.
        subst ms.

        erewrite free_byte_byte_disjoint_allocated; eauto.
    Qed.

    Lemma free_frame_memory_byte_disjoint_read_byte_allowed :
      forall f (ms ms' : MemState) (m m' : memory) (ptr : addr),
        free_frame_memory f m = m' ->
        ~ptr_in_frame_prop f ptr ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        read_byte_allowed ms ptr <-> read_byte_allowed ms' ptr.
    Proof.
      intros f ms ms' m m' ptr FREE DISJOINT MS MS'.
      split; intro READ.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        unfold read_byte_allowed in *.
        destruct READ as [aid READ].
        destruct READ as [READ ALLOWED].
        exists aid.
        split; eauto.
        subst ms.

        erewrite <- free_frame_memory_byte_disjoint_allocated; eauto.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        unfold read_byte_allowed in *.
        destruct READ as [aid READ].
        destruct READ as [READ ALLOWED].
        exists aid.
        split; eauto.
        subst ms.

        erewrite free_frame_memory_byte_disjoint_allocated; eauto.
    Qed.

    Lemma free_block_memory_byte_disjoint_read_byte_allowed :
      forall block (ms ms' : MemState) (m m' : memory) (ptr : addr),
        free_block_memory block m = m' ->
        ~In (ptr_to_int ptr) block ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        read_byte_allowed ms ptr <-> read_byte_allowed ms' ptr.
    Proof.
      intros block ms ms' m m' ptr FREE DISJOINT MS MS'.
      split; intro READ.
      - destruct ms as [[ms fs h] pr].
        cbn in *.
        unfold read_byte_allowed in *.
        destruct READ as [aid READ].
        destruct READ as [READ ALLOWED].
        exists aid.
        split; eauto.
        subst ms.

        erewrite <- free_block_memory_byte_disjoint_allocated; eauto.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        unfold read_byte_allowed in *.
        destruct READ as [aid READ].
        destruct READ as [READ ALLOWED].
        exists aid.
        split; eauto.
        subst ms.

        erewrite free_frame_memory_byte_disjoint_allocated; eauto.
    Qed.

    Lemma free_byte_byte_disjoint_read_byte_prop :
      forall (ms ms' : MemState) (m m' : memory) (ptr ptr' : addr) byte,
        free_byte (ptr_to_int ptr) m = m' ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        disjoint_ptr_byte ptr ptr' ->
        read_byte_prop ms ptr' byte <-> read_byte_prop ms' ptr' byte.
    Proof.
      intros ms ms' m m' ptr ptr' byte FREE MS MS' DISJOINT.
      split; intro READ.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        destruct READ as [ms'' [ms''' [[EQ1 EQ2] READ]]]; subst.
        repeat eexists.
        cbn in *.
        unfold mem_state_memory in *.
        rewrite MS'.
        erewrite free_byte_disjoint; eauto.
        break_match.
        break_match.
        all: tauto.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        destruct READ as [ms'' [ms''' [[EQ1 EQ2] READ]]]; subst.
        repeat eexists.
        cbn in *.
        unfold mem_state_memory in *.
        rewrite MS' in READ.
        erewrite free_byte_disjoint in READ; eauto.
        break_match.
        break_match.
        all: tauto.
    Qed.

    Lemma free_frame_memory_byte_disjoint_read_byte_prop :
      forall f (ms ms' : MemState) (m m' : memory) (ptr : addr) byte,
        free_frame_memory f m = m' ->
        ~ptr_in_frame_prop f ptr ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        read_byte_prop ms ptr byte <-> read_byte_prop ms' ptr byte.
    Proof.
      intros f ms ms' m m' ptr byte FREE DISJOINT MS MS'.
      split; intro READ.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        destruct READ as [ms'' [ms''' [[EQ1 EQ2] READ]]]; subst.
        repeat eexists.
        cbn in *.
        unfold mem_state_memory in *.
        rewrite MS'.
        erewrite free_frame_memory_disjoint; eauto.
        break_match.
        break_match.
        all: tauto.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        destruct READ as [ms'' [ms''' [[EQ1 EQ2] READ]]]; subst.
        repeat eexists.
        cbn in *.
        unfold mem_state_memory in *.
        rewrite MS' in READ.
        erewrite free_frame_memory_disjoint in READ; eauto.
        break_match.
        break_match.
        all: tauto.
    Qed.

    Lemma free_block_memory_byte_disjoint_read_byte_prop :
      forall block (ms ms' : MemState) (m m' : memory) (ptr : addr) byte,
        free_block_memory block m = m' ->
        ~In (ptr_to_int ptr) block ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        read_byte_prop ms ptr byte <-> read_byte_prop ms' ptr byte.
    Proof.
      intros block ms ms' m m' ptr byte FREE DISJOINT MS MS'.
      split; intro READ.
      - destruct ms as [[ms fs h] pr].
        cbn in *.
        destruct READ as [ms'' [ms''' [[EQ1 EQ2] READ]]]; subst.
        repeat eexists.
        cbn in *.
        unfold mem_state_memory in *.
        rewrite MS'.
        erewrite free_frame_memory_disjoint; eauto.
        break_match.
        break_match.
        all: tauto.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        destruct READ as [ms'' [ms''' [[EQ1 EQ2] READ]]]; subst.
        repeat eexists.
        cbn in *.
        unfold mem_state_memory in *.
        rewrite MS' in READ.
        erewrite free_frame_memory_disjoint in READ; eauto.
        break_match.
        break_match.
        all: tauto.
    Qed.

    (* TODO: Move this so it can be reused *)
    Lemma cannot_pop_singleton :
      forall ms f,
        mem_state_frame_stack_prop ms (Singleton f) ->
        cannot_pop ms.
    Proof.
      intros ms f FSP.
      unfold cannot_pop.
      intros fs1 fs2 FSP2.
      unfold mem_state_frame_stack_prop in FSP.
      red in FSP.
      red in FSP2.
      rewrite FSP2 in FSP.
      rewrite FSP.
      intros POP.
      unfold pop_frame_stack_prop in POP.
      auto.
    Qed.

    Lemma mempop_correct :
      forall pre, exec_correct pre mempop mempop_spec_MemPropT.
    Proof.
      unfold exec_correct.
      intros pre ms st VALID PRE.

      destruct ms as [[mem fs h] pr].
      destruct fs as [f | fs f].
      - (* Pop singleton, error *)
        right; left.
        cbn.
        exists "Last frame, cannot pop."%string.
        split.
        + unfold mempop.
          rewrite MemMonad_run_bind.
          rewrite MemMonad_get_mem_state.
          rewrite bind_ret_l.
          cbn.
          rewrite MemMonad_run_bind.
          rewrite MemMonad_run_raise_error.
          rewrite rbm_raise_bind; [|solve [typeclasses eauto]].
          reflexivity.
        + exists ""%string.
          eapply cannot_pop_singleton.
          do 2 red.
          cbn; reflexivity. 
      - (* Pop succeeds *)
        right; right; right.
        cbn.
        do 2 eexists.
        exists tt.
        split.
        + unfold mempop.
          rewrite MemMonad_run_bind.
          rewrite MemMonad_get_mem_state.
          rewrite bind_ret_l.
          cbn.
          rewrite MemMonad_run_bind.
          rewrite MemMonad_run_ret.
          rewrite bind_ret_l.
          rewrite MemMonad_put_mem_state.
          reflexivity.
        + split.
          -- (* mempop_spec *)
            split.
            ++ (* bytes_freed *)
              (* TODO : solve_byte_not_allocated? *)
              intros ptr IN.
              unfold ptr_in_current_frame in IN.
              specialize (IN (Snoc fs f)).
              forward IN.
              { apply mem_state_frame_stack_prop_refl.
                cbn. reflexivity.
              }
              specialize (IN f).
              forward IN.
              cbn. reflexivity.

              eapply free_frame_memory_byte_not_allocated
                with (ms := mkMemState (mkMemoryStack mem (Snoc fs f) h) pr); eauto.
            ++ (* non_frame_bytes_preserved *)
              intros ptr aid NIN.

              eapply free_frame_memory_byte_disjoint_allocated; cbn; eauto.
              eapply ptr_nin_current_frame; cbn; eauto.
              unfold mem_state_frame_stack_prop. red. reflexivity.
              cbn. reflexivity.
            ++ (* non_frame_bytes_read *)
              { intros ptr byte NIN.

                split; intros READ.
                + split.
                  * (* read_byte_allowed *)
                    eapply free_frame_memory_byte_disjoint_read_byte_allowed
                      with (ms := mkMemState (mkMemoryStack mem (Snoc fs f) h) pr); cbn;
                      eauto.
                    eapply ptr_nin_current_frame; eauto.
                    all: unfold mem_state_frame_stack_prop; cbn; red; try reflexivity.
                    cbn. reflexivity.
                    inv READ; solve_read_byte_allowed.
                  * (* read_byte_prop *)
                    eapply free_frame_memory_byte_disjoint_read_byte_prop
                      with (ms := mkMemState (mkMemoryStack mem (Snoc fs f) h) pr);
                      eauto.
                    eapply ptr_nin_current_frame; eauto.
                    all: unfold mem_state_frame_stack_prop; try solve [cbn; reflexivity].
                    cbn. red; reflexivity.
                    cbn. red; reflexivity.

                    inv READ; solve_read_byte_prop.
                + (* read_byte_spec *)
                  split.
                  * (* read_byte_allowed *)
                    eapply free_frame_memory_byte_disjoint_read_byte_allowed
                      with (ms := mkMemState (mkMemoryStack mem (Snoc fs f) h) pr)
                           (ms' := {|
                                    ms_memory_stack :=
                                    (mkMemoryStack (fold_left (fun (m : memory) (key : Iptr) => free_byte key m) f mem) fs h);
                                    ms_provenance := pr
                                  |});
                      eauto.
                    eapply ptr_nin_current_frame; eauto.
                    all: unfold mem_state_frame_stack_prop; try solve [cbn; reflexivity].
                    cbn. red. reflexivity.
                    cbn. red. reflexivity.
                    inv READ; solve_read_byte_allowed.
                  * (* read_byte_prop *)
                    eapply free_frame_memory_byte_disjoint_read_byte_prop
                      with (ms := mkMemState (mkMemoryStack mem (Snoc fs f) h) pr)
                           (ms' := {|
                                    ms_memory_stack :=
                                    (mkMemoryStack (fold_left (fun (m : memory) (key : Iptr) => free_byte key m) f mem) fs h);
                                    ms_provenance := pr
                                  |});
                      eauto.
                    eapply ptr_nin_current_frame; eauto.
                    all: unfold mem_state_frame_stack_prop; try solve [cbn; reflexivity].
                    cbn. red. reflexivity.
                    cbn. reflexivity.
                    inv READ; solve_read_byte_prop.
              }
            ++ (* pop_frame *)
              intros fs1 fs2 FS POP.
              unfold pop_frame_stack_prop in POP.
              destruct fs1; [contradiction|].
              red; cbn.
              red in FS; cbn in FS.
              apply frame_stack_snoc_inv_fs in FS.
              rewrite FS.
              rewrite POP.
              reflexivity.
            ++ (* mempop_invariants *)
              split.
              --- (* preserve_allocation_ids *)
                red. unfold used_provenance_prop.
                cbn. reflexivity.
              --- (* heap preserved *)
                solve_heap_preserved.
          -- (* MemMonad_valid_state *)
            admit.
    Admitted.

    Lemma byte_not_allocated_dec :
      forall ms ptr,
        {byte_not_allocated ms ptr} + {~ byte_not_allocated ms ptr}.
    Proof.
      intros ([m fs h] & pr) ptr.

      unfold byte_not_allocated.
      unfold byte_allocated, byte_allocated_MemPropT.
      unfold addr_allocated_prop.

      destruct (read_byte_raw m (ptr_to_int ptr)) as [[byte aid] |] eqn:READ.
      - (* Allocated *)
        right.
        cbn.
        intros CONTRA.
        specialize (CONTRA aid).
        apply CONTRA.
        clear CONTRA.
        repeat eexists.
        cbn.
        rewrite READ.
        split; auto.
        apply aid_eq_dec_refl.

        intros ms' x H0.
        cbn in H0.
        inv H0.
        reflexivity.
      - (* Not allocated *)
        left.
        intros aid CONTRA.

        cbn in CONTRA.
        destruct CONTRA as [ms [a [CONTRA [EQ1 EQ2]]]]; subst.
        destruct CONTRA as [[ms [ms' [[EQ1 EQ2] CONTRA]]] PR]; subst.
        cbn in CONTRA.
        rewrite READ in CONTRA.
        cbn in *.
        destruct CONTRA as [_ CONTRA].
        inv CONTRA.
    Qed.

    Lemma byte_allocated_dec :
      forall ms ptr,
        {exists aid, byte_allocated ms ptr aid} + {~ exists aid, byte_allocated ms ptr aid}.
    Proof.
      intros ([m fs h] & pr) ptr.

      unfold byte_not_allocated.
      unfold byte_allocated, byte_allocated_MemPropT.
      unfold addr_allocated_prop.

      destruct (read_byte_raw m (ptr_to_int ptr)) as [[byte aid] |] eqn:READ.
      - (* Allocated *)
        left.
        exists aid.
        repeat eexists.
        cbn.
        rewrite READ.
        split; auto.
        apply aid_eq_dec_refl.

        intros ms' x H0.
        cbn in H0.
        inv H0.
        reflexivity.
      - (* Not allocated *)
        right.
        intros (aid & CONTRA).

        cbn in CONTRA.
        destruct CONTRA as [ms [a [CONTRA [EQ1 EQ2]]]]; subst.
        destruct CONTRA as [[ms [ms' [[EQ1 EQ2] CONTRA]]] PR]; subst.
        cbn in CONTRA.
        rewrite READ in CONTRA.
        cbn in *.
        destruct CONTRA as [_ CONTRA].
        inv CONTRA.
    Qed.

    Lemma block_ptr_allocated_dec :
      forall m1 root ptr,
        ptr_in_memstate_heap m1 root ptr ->
        {exists aid, byte_allocated m1 ptr aid} + {byte_not_allocated m1 ptr}.
    Proof.
      intros ([m fs h] & pr) root ptr INBLOCK.

      red in INBLOCK.
      unfold memory_stack_heap_prop in INBLOCK.
      cbn in INBLOCK.
      specialize (INBLOCK h).
      forward INBLOCK; [reflexivity|].
      unfold ptr_in_heap_prop in INBLOCK.
      break_match_hyp; try inv INBLOCK.

      unfold byte_not_allocated.
      unfold byte_allocated, byte_allocated_MemPropT.
      unfold addr_allocated_prop.

      destruct (read_byte_raw m (ptr_to_int ptr)) as [[byte aid] |] eqn:READ.

      - (* Allocated *)
        left.
        repeat eexists.
        cbn.
        rewrite READ.
        split; auto.
        apply aid_eq_dec_refl.

        intros ms' x H0.
        cbn in *.
        inv H0.
        cbn.
        reflexivity.
      - (* Not allocated *)
        right.
        intros aid CONTRA.
        cbn in CONTRA.
        destruct CONTRA as [ms [a [CONTRA [EQ1 EQ2]]]]; subst.
        destruct CONTRA as [[ms [ms' [[EQ1 EQ2] CONTRA]]] PR]; subst.
        cbn in CONTRA.
        rewrite READ in CONTRA.
        destruct CONTRA as [_ CONTRA].
        inv CONTRA.
    Qed.

    Lemma byte_allocated_ignores_provenance :
      forall ms ptr1 ptr2 aid,
        byte_allocated ms ptr1 aid ->
        ptr_to_int ptr1 = ptr_to_int ptr2 ->
        byte_allocated ms ptr2 aid.
    Proof.
      intros ms ptr1 ptr2 aid ALLOC INTEQ.
      do 2 red.
      do 2 red in ALLOC.
      unfold addr_allocated_prop in *.
      rewrite INTEQ in ALLOC.
      auto.
    Qed.

    Lemma block_allocated_dec :
      forall m1 root,
        (forall ptr,
            ptr_in_memstate_heap m1 root ptr ->
            exists aid, byte_allocated m1 ptr aid) \/
          ~(forall ptr,
               ptr_in_memstate_heap m1 root ptr ->
               exists aid, byte_allocated m1 ptr aid).
    Proof.
      intros ms root.
      destruct ms as ([m fs h] & pr) eqn:MS.

      (* Is there a block? *)
      destruct (IM.find (elt:=Block) (ptr_to_int root) h) eqn:BLOCK.
      2: {
        (* No block, vacuously true. *)
        left.
        intros ptr CONTRA.
        unfold ptr_in_memstate_heap in CONTRA.
        specialize (CONTRA h).
        forward CONTRA; [cbn; red; cbn; reflexivity|].

        unfold ptr_in_heap_prop in CONTRA.
        rewrite BLOCK in CONTRA.
        inv CONTRA.
      }

      (* Block exists *)
      pose proof byte_allocated_dec ms as BADEC.
      pose proof List.Forall_dec _ BADEC as ALLOC.
      set (aid := provenance_to_allocation_id initial_provenance).
      set (prov := allocation_id_to_prov aid).
      set (block := map (fun ip => int_to_ptr ip prov) b).
      specialize (ALLOC block).
      destruct ALLOC as [ALL_ALLOCATED | NOT_ALL_ALLOCATED].
      - setoid_rewrite -> Forall_forall in ALL_ALLOCATED.
        left.
        intros ptr INHEAP.
        red in INHEAP.
        cbn in INHEAP.
        specialize (INHEAP h).
        forward INHEAP; [repeat red; reflexivity|].
        unfold ptr_in_heap_prop in INHEAP.
        rewrite BLOCK in INHEAP.
        assert (In (int_to_ptr (ptr_to_int ptr) prov) block) as INBLOCK.
        { subst block.
          pose proof in_map.
          specialize (H0 _ _ (fun ip : Z => int_to_ptr ip prov) b (ptr_to_int ptr) INHEAP).
          auto.
        }

        specialize (ALL_ALLOCATED _ INBLOCK).
        subst ms.
        destruct ALL_ALLOCATED as (aid' & ALL_ALLOCATED).
        exists aid'.
        eapply byte_allocated_ignores_provenance.
        apply ALL_ALLOCATED.
        rewrite ptr_to_int_int_to_ptr. reflexivity.
      - setoid_rewrite -> Forall_forall in NOT_ALL_ALLOCATED.
        right.
        intros CONTRA.
        apply NOT_ALL_ALLOCATED.
        intros ptr INBLOCK.
        specialize (CONTRA ptr).
        forward CONTRA.
        { red.
          intros h' HEAP.
          red in HEAP.
          cbn in HEAP.
          rewrite <- HEAP.
          red.
          rewrite BLOCK.
          subst block.
          eapply in_map with (f:=ptr_to_int) in INBLOCK.
          rewrite List.map_map in INBLOCK.
          apply in_map_iff in INBLOCK.
          destruct INBLOCK as (x & CAST & INBLOCK).
          rewrite ptr_to_int_int_to_ptr in CAST.
          subst.
          auto.
        }

        destruct CONTRA as (aid' & CONTRA).
        exists aid'.
        subst ms.
        eapply byte_allocated_ignores_provenance.
        apply CONTRA.
        reflexivity.
    Qed.

    Lemma free_correct :
      forall ptr pre,
        exec_correct pre (free ptr) (free_spec_MemPropT ptr).
    Proof.
      unfold exec_correct.
      intros ptr pre ms st VALID PRE.

      (* Need to determine if `ptr` is a root in the heap... If not,
         UB has occurred.
       *)

      destruct ms as [[mem fs h] pr] eqn:HMS.
      destruct (member (ptr_to_int ptr) h) eqn:ROOTIN.

      2: { (* UB, ptr not a root of the heap *)
        left.
        eexists.
        cbn.
        intros m2 FREE.
        inv FREE.
        unfold root_in_memstate_heap in *.
        specialize (free_was_root0 h).
        forward free_was_root0.
        cbn. red. cbn. reflexivity.
        unfold root_in_heap_prop in free_was_root0.
        rewrite ROOTIN in free_was_root0.
        inv free_was_root0.
      }

      (* Need to determine if the ptr is allocated, if not UB occurs. *)
      destruct (read_byte_raw mem (ptr_to_int ptr)) as [[root_byte root_aid] |] eqn:READ_ROOT.
      2: { (* Unallocated root, UB *)
        left.
        eexists.
        cbn.
        intros m2 FREE.
        inv FREE.
        destruct free_was_allocated0 as (aid & ALLOC).
        unfold byte_allocated, byte_allocated_MemPropT, addr_allocated_prop in ALLOC.
        pose proof ALLOC as ALLOC'.
        unfold lift_memory_MemPropT in ALLOC'.
        cbn in ALLOC'.
        destruct ALLOC' as [ms [a [ALLOC' [EQ1 EQ2]]]]; subst.
        destruct ALLOC' as [[ms [ms' [[EQ1 EQ2] ALLOC']]] PR]; subst.
        cbn in ALLOC'.
        rewrite READ_ROOT in ALLOC'.
        inv ALLOC'.
        inv H1.
      }

      (* Need to determine if block is allocated *)
      pose proof (block_allocated_dec ms ptr) as [BLOCK_ALLOCATED | BLOCK_NOTALLOCATED].
      2: {
        (* Block unallocated, UB *)
        left.
        eexists.
        cbn.
        intros m2 FREE.
        inv FREE.
        contradiction.
      }

      pose proof (member_lookup _ _ ROOTIN) as (block & FINDPTR).
      right; right; right.
      cbn.
      do 2 eexists.
      exists tt.

      split.
      { unfold free.
        rewrite MemMonad_run_bind.
        rewrite MemMonad_get_mem_state.
        rewrite bind_ret_l.
        cbn.
        rewrite FINDPTR.
        rewrite MemMonad_put_mem_state.
        reflexivity.
      }

      split.
      { (* Proof of free_spec *)
        split.
        - (* free_was_root *)
          red.
          intros h0 HEAP.
          cbn in *.
          red.
          unfold memory_stack_heap_prop in HEAP.
          cbn in HEAP.
          eapply member_ptr_to_int_heap_eqv_Proper.
          reflexivity.
          symmetry; eauto.
          eauto.
        - (* free_was_allocated *)
          exists root_aid.
          do 2 red.
          unfold addr_allocated_prop.
          repeat eexists.
          + cbn.
            rewrite READ_ROOT.
            split; auto.
            apply aid_eq_dec_refl.
          + intros ms' x H0.
            cbn in H0.
            inv H0.
            reflexivity.
        - (* free_block_allocated *)
          intros heap_ptr IN.
          subst.
          specialize (BLOCK_ALLOCATED heap_ptr IN).
          eauto.
        - (* free_bytes_freed *)
          (* TODO : solve_byte_not_allocated? *)
          intros ptr0 HEAP.
          red in HEAP.
          cbn in HEAP.
          specialize (HEAP h).
          forward HEAP.
          { unfold memory_stack_heap_prop; reflexivity.
          }

          unfold byte_not_allocated.
          intros aid ALLOCATED.

          unfold ptr_in_heap_prop in HEAP.
          break_match_hyp; try inv HEAP.
          unfold lookup in FINDPTR.
          rewrite FINDPTR in Heqo; inv Heqo.

          eapply free_block_memory_byte_not_allocated
            with (ms := mkMemState (mkMemoryStack mem fs h) pr); eauto.

          cbn.
          reflexivity.
        - (* free_non_block_bytes_preserved *)
          intros ptr0 aid NIN.

          eapply free_block_memory_byte_disjoint_allocated; cbn; eauto.
          { unfold ptr_in_memstate_heap in *.
            cbn in *.
            intros IN.
            apply NIN.
            intros h0 H0.
            red in H0.
            cbn in H0.
            rewrite <- H0.
            red.
            unfold lookup in FINDPTR.
            rewrite FINDPTR; auto.
          }
        - (* free_non_frame_bytes_read *)
          intros ptr0 byte NIN.

          split; intros READ.
          + split.
            * (* read_byte_allowed *)
              eapply free_block_memory_byte_disjoint_read_byte_allowed
                with (ms := mkMemState (mkMemoryStack mem fs h) pr); cbn;
                eauto.
              { unfold ptr_in_memstate_heap in *.
                cbn in *.
                intros IN.
                apply NIN.
                intros h0 H0.
                red in H0.
                cbn in H0.
                rewrite <- H0.
                red.
                unfold lookup in FINDPTR.
                rewrite FINDPTR; auto.
              }
              inv READ; solve_read_byte_allowed.
            * (* read_byte_prop *)
              eapply free_block_memory_byte_disjoint_read_byte_prop
                with (ms := mkMemState (mkMemoryStack mem fs h) pr);
                eauto.
              { unfold ptr_in_memstate_heap in *.
                cbn in *.
                intros IN.
                apply NIN.
                intros h0 H0.
                red in H0.
                cbn in H0.
                rewrite <- H0.
                red.
                unfold lookup in FINDPTR.
                rewrite FINDPTR; eauto.
              }
              inv READ; solve_read_byte_prop.
              inv READ; solve_read_byte_prop.
          + (* read_byte_spec *)
            split.
            * (* read_byte_allowed *)
              eapply free_block_memory_byte_disjoint_read_byte_allowed
                with (ms := mkMemState (mkMemoryStack mem fs h) pr)
                     (ms' := {|
                              ms_memory_stack :=
                              mkMemoryStack (free_block_memory block mem) fs (delete (ptr_to_int ptr) h);
                              ms_provenance := pr
                            |});
                eauto.
              { unfold ptr_in_memstate_heap in *.
                cbn in *.
                intros IN.
                apply NIN.
                intros h0 H0.
                red in H0.
                cbn in H0.
                rewrite <- H0.
                red.
                unfold lookup in FINDPTR.
                rewrite FINDPTR; eauto.
              }
              all: unfold mem_state_frame_stack_prop; try solve [cbn; reflexivity].
              inv READ; solve_read_byte_allowed.
            * (* read_byte_prop *)
              eapply free_frame_memory_byte_disjoint_read_byte_prop
                with (ms := mkMemState (mkMemoryStack mem fs h) pr)
                     (ms' := {|
                              ms_memory_stack :=
                              mkMemoryStack (free_block_memory block mem) fs (delete (ptr_to_int ptr) h);
                              ms_provenance := pr
                            |});
                eauto.
              { unfold ptr_in_memstate_heap in *.
                cbn in *.
                intros IN.
                apply NIN.
                intros h0 H0.
                red in H0.
                cbn in H0.
                rewrite <- H0.
                red.
                unfold lookup in FINDPTR.
                rewrite FINDPTR; eauto.
              }
              all: unfold mem_state_frame_stack_prop; try solve [cbn; reflexivity].
              inv READ; solve_read_byte_prop.
        - (* free_block *)
          intros h1 h2 HEAP1 HEAP2.
          cbn in *.
          unfold memory_stack_heap_prop in *.
          cbn in *.
          split.
          + (* free_block_ptrs_freed *)
            intros ptr0 IN CONTRA.
            inv HEAP2.
            apply heap_ptrs_eqv0 in CONTRA.
            unfold ptr_in_heap_prop in *.
            break_match_hyp; try inv CONTRA.
            unfold delete in *.
            rewrite IP.F.remove_eq_o in Heqo; auto; inv Heqo.
          + (* free_block_root_freed *)
            intros CONTRA.
            inv HEAP2.
            apply heap_roots_eqv0 in CONTRA.
            unfold root_in_heap_prop in *.
            unfold member, delete in *.
            rewrite IP.F.remove_eq_b in CONTRA; auto; inv CONTRA.
          + (* free_block_disjoint_preserved *)
            intros ptr0 root' DISJOINT.
            split; intros IN.
            * apply HEAP2.
              unfold ptr_in_heap_prop.
              unfold delete.
              rewrite IP.F.remove_neq_o; auto.
              apply HEAP1; auto.
            * apply HEAP2 in IN.
              unfold ptr_in_heap_prop in IN.
              unfold delete in IN.
              rewrite IP.F.remove_neq_o in IN; auto.
              apply HEAP1 in IN; auto.
          + (* free_block_disjoint_roots *)
            intros root' DISJOINT.
            split; intros IN.
            * apply HEAP2.
              unfold root_in_heap_prop.
              unfold delete.
              rewrite IP.F.remove_neq_b; auto.
              apply HEAP1; auto.
            * apply HEAP2 in IN.
              unfold root_in_heap_prop in IN.
              unfold delete in IN.
              rewrite IP.F.remove_neq_b in IN; auto.
              apply HEAP1 in IN; auto.
        - (* free_invariants *)
          split.
          + (* Allocation ids preserved *)
            red. unfold used_provenance_prop.
            cbn. reflexivity.
          + (* Framestack preserved *)
            solve_frame_stack_preserved.

            Unshelve.
            all: exact ""%string.
      }

      (* MemMonad_valid_state *)
      admit.
    Admitted.

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

    Lemma initial_frame_correct : initial_frame_prop.
    Proof.
      split.
      apply initial_frame_empty.
    Qed.

    Lemma initial_heap_correct : initial_heap_prop.
    Proof.
      split.
      split.
      - intros root.
        unfold initial_heap.
        unfold root_in_heap_prop.
        intros CONTRA.
        rewrite IP.F.empty_a in CONTRA.
        inv CONTRA.
      - intros ptr.
        unfold initial_heap.
        cbn.
        auto.
    Qed.

    (* TODO: move this? *)
    #[global] Instance empty_frame_stack_Proper :
      Proper (frame_stack_eqv ==> iff) empty_frame_stack.
    Proof.
      intros fs' fs FS.
      split; intros [NOPOP EMPTY].
      - split.
        + setoid_rewrite <- FS.
          auto.
        + setoid_rewrite <- FS.
          auto.
      - split.
        + setoid_rewrite FS.
          auto.
        + setoid_rewrite FS.
          auto.
    Qed.

    (* TODO: move this? *)
    #[global] Instance empty_frame_Proper :
      Proper (frame_eqv ==> iff) empty_frame.
    Proof.
      intros f' f F.
      unfold empty_frame.
      setoid_rewrite F.
      reflexivity.
    Qed.

    (* TODO: move this? *)
    Lemma empty_frame_nil :
      empty_frame [].
    Proof.
      red.
      cbn.
      auto.
    Qed.

    (* TODO: move this? *)
    Lemma empty_frame_stack_frame_empty :
      empty_frame_stack frame_empty.
    Proof.
      unfold frame_empty.
      split.
      - intros f CONTRA.
        cbn in *; auto.
      - intros f CONTRA.
        cbn in *.
        rewrite CONTRA.
        apply empty_frame_nil.
    Qed.

    (* TODO: move this? *)
    #[global] Instance empty_heap_Proper :
      Proper (heap_eqv ==> iff) empty_heap.
    Proof.
      intros f' f F.
      split; intros [ROOTS PTRS].
      - split; setoid_rewrite <- F; auto.
      - split; setoid_rewrite F; auto.
    Qed.

    (* TODO: move this? *)
    Lemma empty_heap_heap_empty :
      empty_heap heap_empty.
    Proof.
      unfold heap_empty.
      split.
      - intros root CONTRA.
        red in CONTRA.
        unfold member in CONTRA.
        rewrite IP.F.empty_a in CONTRA.
        inv CONTRA.
      - intros root ptr CONTRA.
        red in CONTRA.
        unfold member in CONTRA.
        rewrite IP.F.empty_o in CONTRA.
        inv CONTRA.
    Qed.

    Lemma initial_memory_state_correct : initial_memory_state_prop.
    Proof.
      split.
      - intros ptr aid CONTRA.
        unfold initial_memory_state in *.
        break_byte_allocated_in CONTRA.
        break_match_hyp; [break_match_hyp|].
        + cbn in *.
          rewrite read_byte_raw_memory_empty in Heqo.
          inv Heqo.
        + cbn in *.
          destruct CONTRA as [_ CONTRA].
          inv CONTRA.
      - intros fs FS.
        cbn in FS.
        red in FS.
        rewrite <- FS.
        cbn.
        apply empty_frame_stack_frame_empty.
      - intros h HEAP.
        cbn in HEAP.
        red in HEAP.
        rewrite <- HEAP.
        cbn.
        apply empty_heap_heap_empty.
      - intros ptr byte.
        solve_read_byte_prop.
    Qed.

    End MemoryPrimatives.

End FiniteMemoryModelExecPrimitives.
