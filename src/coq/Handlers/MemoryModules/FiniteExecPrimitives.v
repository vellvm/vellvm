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
     VellvmIntegers
     StoreId.

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
     FiniteSpecPrimitives
     Within.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Data.Monads.StateMonad.

From ITree Require Import
     ITree
     Eq.Eqit.

Require Import Error.

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
    Context `{MemMonad MemM (itree Eff)}.

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
    Proof using.
      auto.
    Qed.

    Lemma next_memory_key_next_key_memory_stack_memory :
      forall ms,
        next_memory_key ms = next_key (memory_stack_memory ms).
    Proof using.
      auto.
    Qed.

    (*** Primitives on memory *)
    (** Reads *)
    Definition read_byte `{MemMonad MemM (itree Eff)} (ptr : addr) : MemM SByte :=
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
              ("Read from memory with invalid provenance")
              (* This error message can get quite long, and the specific details cause issues with bugpoint... Maybe make a debug message instead? *)
              (* ("Read from memory with invalid provenance -- addr: " ++ Show.show addr ++ ", addr prov: " ++ show_prov pr ++ ", memory allocation id: " ++ Show.show (show_allocation_id aid) ++ " memory: " ++ Show.show (map (fun '(key, (_, aid)) => (key, show_allocation_id aid)) (IM.elements mem))) *)
      end.

    (** Writes *)
    Definition write_byte `{MemMonad MemM (itree Eff)} (ptr : addr) (byte : SByte) : MemM unit :=
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
          else
            raise_ub
              "Trying to write to memory with invalid provenance"
              (* This error message can get quite long, and the specific details cause issues with bugpoint... Maybe make a debug message instead? *)
              (* ("Trying to write to memory with invalid provenance -- addr: " ++ Show.show addr ++ ", addr prov: " ++ show_prov pr ++ ", memory allocation id: " ++ show_allocation_id aid ++ " Memory: " ++ Show.show (map (fun '(key, (_, aid)) => (key, show_allocation_id aid)) (IM.elements mem))) *)
      end.

    (** Allocations *)
    Definition addr_allocated `{MemMonad MemM (itree Eff)} (ptr : addr) (aid : AllocationId) : MemM bool :=
      ms <- get_mem_state;;
      match read_byte_raw (mem_state_memory ms) (ptr_to_int ptr) with
      | None => ret false
      | Some (byte, aid') =>
          ret (proj_sumbool (aid_eq_dec aid aid'))
      end.

    (* Register a concrete address in a frame *)
    Definition add_to_frame (m : memory_stack) (k : addr) : memory_stack :=
      let '(mkMemoryStack m s h) := m in
      match s with
      | Singleton f => mkMemoryStack m (Singleton (k :: f)) h
      | Snoc s f => mkMemoryStack m (Snoc s (k :: f)) h
      end.

    (* Register a list of concrete addresses in a frame *)
    Definition add_all_to_frame (m : memory_stack) (ks : list addr) : memory_stack
      := fold_left (fun ms k => add_to_frame ms k) ks m.

    (* Register a ptr with the heap *)
    Definition add_to_heap (m : memory_stack) (root : addr) (ptr : addr) : memory_stack :=
      let '(mkMemoryStack m s h) := m in
      let h' := add_with (ptr_to_int root) ptr ret cons h in
      mkMemoryStack m s h'.

    (* Register a list of concrete addresses in the heap *)
    Definition add_all_to_heap' (m : memory_stack) (root : addr) (ks : list addr) : memory_stack
      := fold_left (fun ms k => add_to_heap ms root k) ks m.

    Definition add_all_to_heap (m : memory_stack) (ks : list addr) : memory_stack
      := match ks with
         | [] => m
         | (root :: _) =>
             add_all_to_heap' m root ks
         end.

    Lemma add_to_frame_preserves_memory :
      forall ms k,
        memory_stack_memory (add_to_frame ms k) = memory_stack_memory ms.
    Proof using.
      intros [m fs] k.
      destruct fs; auto.
    Qed.

    Lemma add_to_heap_preserves_memory :
      forall ms root k,
        memory_stack_memory (add_to_heap ms root k) = memory_stack_memory ms.
    Proof using.
      intros [m fs] root k.
      destruct fs; auto.
    Qed.

    Lemma add_to_frame_preserves_heap :
      forall ms k,
        memory_stack_heap (add_to_frame ms k) = memory_stack_heap ms.
    Proof using.
      intros [m fs] k.
      destruct fs; auto.
    Qed.

    Lemma add_to_heap_preserves_frame_stack :
      forall ms root k,
        memory_stack_frame_stack (add_to_heap ms root k) = memory_stack_frame_stack ms.
    Proof using.
      intros [m fs] root k.
      destruct fs; auto.
    Qed.

    Lemma add_all_to_frame_preserves_memory :
      forall ms ks,
        memory_stack_memory (add_all_to_frame ms ks) = memory_stack_memory ms.
    Proof using.
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
    Proof using.
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
    Proof using.
      intros ms [|a ks]; auto.
      apply add_all_to_heap'_preserves_memory.
    Qed.

    Lemma add_all_to_frame_preserves_heap :
      forall ms ks,
        memory_stack_heap (add_all_to_frame ms ks) = memory_stack_heap ms.
    Proof using.
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
    Proof using.
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
    Proof using.
      intros ms [|a ks]; auto.
      apply add_all_to_heap'_preserves_frame_stack.
    Qed.

    Lemma add_all_to_frame_nil_preserves_frames :
      forall ms,
        memory_stack_frame_stack (add_all_to_frame ms []) = memory_stack_frame_stack ms.
    Proof using.
      intros [m fs].
      destruct fs; auto.
    Qed.

    Lemma add_all_to_frame_nil :
      forall ms ms',
        add_all_to_frame ms [] = ms' ->
        ms = ms'.
    Proof using.
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
    Proof using.
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
    Proof using.
      cbn; eauto.
    Qed.

    Lemma add_all_to_heap_cons_inv :
      forall ptr ptrs ms ms'',
        add_all_to_heap ms (ptr :: ptrs) = ms'' ->
        exists ms',
          add_to_heap ms ptr ptr = ms' /\
            add_all_to_heap' ms' ptr ptrs = ms''.
    Proof using.
      cbn; eauto.
    Qed.

    Lemma add_all_to_frame_cons :
      forall ptr ptrs ms ms' ms'',
        add_to_frame ms ptr = ms' ->
        add_all_to_frame ms' ptrs = ms'' ->
        add_all_to_frame ms (ptr :: ptrs) = ms''.
    Proof using.
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
    Proof using.
      intros ptr ptrs ms ms' ms'' ADD ADD_ALL.
      cbn; subst; eauto.
    Qed.

    Lemma add_to_frame_add_all_to_frame :
      forall ptr ms,
        add_to_frame ms ptr = add_all_to_frame ms [ptr].
    Proof using.
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
    Proof using.
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
    Proof using.
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
    Proof using.
      intros ptr1 ptr2 root ms ms1' ms2' ms1'' ms2'' ADD1 ADD1' ADD2 ADD2'.
      destruct ms, ms1', ms2', ms1'', ms2''.
      cbn in *.
      repeat break_match_hyp; subst;
        inv ADD1; inv ADD1'; inv ADD2; inv ADD2'.

      - split.
        { intros root'.
          unfold root_in_heap_prop.
          split; intros ROOT.
          - destruct (Z.eq_dec (ptr_to_int root') (ptr_to_int root)) as [EQR | NEQR].
            + rewrite EQR.
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
          - destruct (Z.eq_dec (ptr_to_int root') (ptr_to_int root)) as [EQR | NEQR].
            + rewrite EQR.
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
        + destruct (Z.eq_dec (ptr_to_int root') (ptr_to_int root)) as [EQR | NEQR].
          * rewrite EQR.
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
        + destruct (Z.eq_dec (ptr_to_int root') (ptr_to_int root)) as [EQR | NEQR].
          * rewrite EQR.
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
    Proof using.
      unfold Proper, respectful.
      intros x y XY a b AB.
      unfold frame_eqv in *.
      unfold ptr_in_frame_prop in *.
      rewrite AB; auto.
    Qed.

    #[global] Instance ptr_in_frame_prop_Proper :
      Proper (frame_eqv ==> eq ==> iff) ptr_in_frame_prop.
    Proof using.
      unfold Proper, respectful.
      intros x y XY a b AB; subst.
      unfold frame_eqv in *.
      auto.
    Qed.

    #[global] Instance frame_stack_eqv_add_ptr_to_frame_Proper :
      Proper (frame_eqv ==> eq ==> frame_eqv ==> iff) add_ptr_to_frame.
    Proof using.
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
    Proof using.
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

    (* TODO: Move this *)
    Lemma FSNth_frame_eqv :
      forall n fs f1 f2,
        frame_eqv f1 f2 ->
        FSNth_eqv fs n f1 ->
        FSNth_eqv fs n f2.
    Proof using.
      induction n;
        intros fs f1 f2 EQV NTHEQV.
      - destruct fs; cbn in *;
          rewrite NTHEQV; auto.
      - destruct fs; cbn in *; eauto.
    Qed.

    (* TODO: Move this *)
    #[global] Instance FSNth_eqv_Proper :
      Proper (frame_stack_eqv ==> eq ==> frame_eqv ==> iff) FSNth_eqv.
    Proof using.
      unfold Proper, respectful.
      intros x y H' x0 y0 H0 x1 y1 H1; subst.
      split; intros NTH.
      - red in H'.
        apply H'.
        eapply FSNth_frame_eqv; eauto.
      - red in H'.
        apply H'.
        eapply FSNth_frame_eqv; eauto.
        symmetry; auto.
    Qed.

    #[global] Instance heap_eqv_ptr_in_head_prop_Proper :
      Proper (heap_eqv ==> eq ==> eq ==> iff) ptr_in_heap_prop.
    Proof using.
      unfold Proper, respectful.
      intros x y XY root root' EQR ptr ptr' EQPTR; subst.
      rewrite XY.
      reflexivity.
    Qed.

    #[global] Instance heap_eqv_add_ptr_to_heap_Proper :
      Proper (heap_eqv ==> eq ==> eq ==> heap_eqv ==> iff) add_ptr_to_heap.
    Proof using.
      unfold Proper, respectful.
      intros x y XY root root' EQR ptr ptr' EQPTR r s RS; subst.

      split; intros ADD.
      - (* unfold heap_eqv in *. *)
        (* unfold FSNth_eqv in *. *)
        destruct ADD as [OLD NEW].
        split.
        + intros ptr'0 DISJOINT.
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
        + intros ptr'0 DISJOINT.
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
    Proof using.
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
    Proof using.
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
    Proof using.
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
    Proof using.
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
        (ptr_in_frame_prop f ptr' /\ disjoint_ptr_byte ptr ptr') \/ ptr_to_int ptr = ptr_to_int ptr'.
    Proof using.
      intros ptr ptr' f f' F F'.
      inv F.
      pose proof disjoint_ptr_byte_dec ptr ptr' as [DISJOINT | NDISJOINT].
      - left.
        split; auto.
        specialize (old_frame_lu0 _ DISJOINT).
        apply old_frame_lu0; auto.
      - unfold disjoint_ptr_byte in NDISJOINT.
        assert (ptr_to_int ptr = ptr_to_int ptr') as EQ by lia.
        right; auto.
    Qed.

    Lemma add_ptr_to_heap_inv :
      forall ptr ptr' root root' f f',
        add_ptr_to_heap f root ptr f' ->
        ptr_in_heap_prop f' root' ptr' ->
        (ptr_in_heap_prop f root' ptr' /\ disjoint_ptr_byte ptr ptr') \/
          (ptr_in_heap_prop f root' ptr' /\ ptr_to_int ptr = ptr_to_int ptr' /\ disjoint_ptr_byte root root') \/
          (ptr_to_int ptr = ptr_to_int ptr' /\ ptr_to_int root = ptr_to_int root').
    Proof using.
      intros ptr ptr' root root' f f' F F'.
      inv F.
      pose proof disjoint_ptr_byte_dec ptr ptr' as [DISJOINT | NDISJOINT].
      - left.
        split; auto.
        specialize (old_heap_lu0 _ DISJOINT).
        pose proof disjoint_ptr_byte_dec root root' as [DISJOINT' | NDISJOINT'].
        + eapply old_heap_lu_different_root0; eauto.
        + apply Classical_Prop.NNPP in NDISJOINT'.
          red.
          rewrite <- NDISJOINT'.
          apply old_heap_lu0.
          red.
          rewrite NDISJOINT'.
          apply F'.
      - unfold disjoint_ptr_byte in NDISJOINT.
        assert (ptr_to_int ptr = ptr_to_int ptr') as EQ by lia.
        right.
        pose proof disjoint_ptr_byte_dec root root' as [DISJOINT' | NDISJOINT'].
        + left.
          split; auto.
          apply old_heap_lu_different_root0; auto.
        + right.
          unfold disjoint_ptr_byte in NDISJOINT'.
          assert (ptr_to_int root = ptr_to_int root') as EQR by lia.
          split; auto. 
    Qed.

    Lemma add_ptr_to_frame_eqv :
      forall ptr f f1 f2,
        add_ptr_to_frame f ptr f1 ->
        add_ptr_to_frame f ptr f2 ->
        frame_eqv f1 f2.
    Proof using.
      intros ptr f f1 f2 F1 F2.
      unfold frame_eqv.
      intros ptr0.
      split; intros IN.
      - eapply add_ptr_to_frame_inv in IN; eauto.
        destruct IN as [[IN _]| IN].
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
        destruct IN as [[IN _] | IN].
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
    Proof using.
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
    Proof using.
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
    Proof using.
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
    Proof using.
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
          destruct IN as [[IN _]| [[IN1 _] | [IN1 IN2]]].
          * pose proof disjoint_ptr_byte_dec root root0 as [DISJOINT | NDISJOINT].
            -- eapply old_heap_lu_different_root1; eauto.
            -- pose proof disjoint_ptr_byte_dec ptr ptr0 as [DISJOINT' | NDISJOINT'].
               ++ apply Classical_Prop.NNPP in NDISJOINT.
                  red. rewrite <- NDISJOINT.
                  red in new_heap_lu1.
                  eapply old_heap_lu1; eauto.
                  red. rewrite NDISJOINT.
                  apply IN.
               ++ unfold disjoint_ptr_byte in NDISJOINT'.
                  assert (ptr_to_int ptr = ptr_to_int ptr0) as EQ by lia.

                  unfold disjoint_ptr_byte in NDISJOINT.
                  assert (ptr_to_int root = ptr_to_int root0) as EQR by lia.

                  unfold ptr_in_heap_prop in *.
                  rewrite EQ in *.
                  rewrite EQR in *.
                  auto.
          * pose proof disjoint_ptr_byte_dec root root0 as [DISJOINT | NDISJOINT].
            -- eapply old_heap_lu_different_root1; eauto.
            -- pose proof disjoint_ptr_byte_dec ptr ptr0 as [DISJOINT' | NDISJOINT'].
               ++ apply Classical_Prop.NNPP in NDISJOINT.
                  red. rewrite <- NDISJOINT.
                  red in new_heap_lu1.
                  eapply old_heap_lu1; eauto.
                  red. rewrite NDISJOINT.
                  apply IN1.
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
          destruct IN as [[IN _]| [[IN1 _] | [IN1 IN2]]].
          * pose proof disjoint_ptr_byte_dec root root0 as [DISJOINT | NDISJOINT].
            -- eapply old_heap_lu_different_root0; eauto.
            -- pose proof disjoint_ptr_byte_dec ptr ptr0 as [DISJOINT' | NDISJOINT'].
               ++ apply Classical_Prop.NNPP in NDISJOINT.
                  red. rewrite <- NDISJOINT.
                  red in new_heap_lu0.
                  eapply old_heap_lu0; eauto.
                  red. rewrite NDISJOINT.
                  apply IN.
               ++ unfold disjoint_ptr_byte in NDISJOINT'.
                  assert (ptr_to_int ptr = ptr_to_int ptr0) as EQ by lia.

                  unfold disjoint_ptr_byte in NDISJOINT.
                  assert (ptr_to_int root = ptr_to_int root0) as EQR by lia.

                  unfold ptr_in_heap_prop in *.
                  rewrite EQ in *.
                  rewrite EQR in *.
                  auto.
          * pose proof disjoint_ptr_byte_dec root root0 as [DISJOINT | NDISJOINT].
            -- eapply old_heap_lu_different_root0; eauto.
            -- pose proof disjoint_ptr_byte_dec ptr ptr0 as [DISJOINT' | NDISJOINT'].
               ++ apply Classical_Prop.NNPP in NDISJOINT.
                  red. rewrite <- NDISJOINT.
                  red in new_heap_lu0.
                  eapply old_heap_lu0; eauto.
                  red. rewrite NDISJOINT.
                  apply IN1.
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
    Proof using.
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
    Proof using.
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
    Proof using.
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
          destruct (IM.find (elt:=list addr) b h2) eqn:Heqo0.
          rewrite IP.F.add_neq_o in *; auto.
          rewrite IP.F.add_neq_o in *; auto.
        }
        { rewrite IP.F.add_neq_o in *; auto.
          destruct (IM.find (elt:=list addr) b h2) eqn:Heqo0.
          rewrite IP.F.add_neq_o in *; auto.
          rewrite IP.F.add_neq_o in *; auto.
        }
    Qed.

    #[global] Instance heap_eqv_add_all_to_heap :
      Proper ((fun ms1 ms2 => heap_eqv (memory_stack_heap ms1) (memory_stack_heap ms2)) ==> eq ==> eq ==> (fun ms1 ms2 => heap_eqv (memory_stack_heap ms1) (memory_stack_heap ms2))) add_all_to_heap'.
    Proof using.
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
    Proof using.
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
    Proof using.
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
    Proof using.
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
    Proof using.
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
    Proof using.
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
        add_to_frame ms ptr = ms' ->
        add_ptr_to_frame_stack (memory_stack_frame_stack ms) ptr (memory_stack_frame_stack ms').
    Proof using.
      intros ptr ms ms' ADD.
      unfold add_ptr_to_frame_stack.
      intros f PEEK.
      exists (ptr :: f).
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
        add_all_to_frame ms ptrs = ms' ->
        add_ptrs_to_frame_stack (memory_stack_frame_stack ms) ptrs (memory_stack_frame_stack ms').
    Proof using.
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

          destruct (add_all_to_frame (mkMemoryStack m fs h) ptrs) eqn:ADD_ALL'.
          cbn.

          rename memory_stack_memory0 into m0.
          rename memory_stack_frame_stack0 into f.
          rename memory_stack_heap0 into h0.

          assert (add_to_frame (mkMemoryStack m0 f h0) a = add_to_frame (mkMemoryStack m0 f h0) a) as ADD' by reflexivity.
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
        add_to_heap ms root ptr = ms' ->
        add_ptr_to_heap (memory_stack_heap ms) root ptr (memory_stack_heap ms').
    Proof using.
      intros root ptr ms ms' ADD.
      split.
      - (* Old *)
        intros ptr' DISJOINT.
        destruct ms as [mem fs h].
        unfold add_to_heap in *.
        unfold ptr_in_heap_prop in *.
        cbn in *.
        inv ADD.
        cbn.

        split; intros IN.
        + unfold add_with.
          * unfold Block in *.
            unfold Iptr in *.
            break_inner_match.
            -- rewrite IP.F.add_eq_o; firstorder.
            -- contradiction.
        + unfold add_with in *.
          * unfold Block in *.
            unfold Iptr in *.
            break_inner_match_hyp.
            -- rewrite IP.F.add_eq_o in IN; firstorder.
            -- rewrite IP.F.add_eq_o in IN; firstorder.
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
        add_all_to_heap' ms root ptrs = ms' ->
        add_ptrs_to_heap' (memory_stack_heap ms) root ptrs (memory_stack_heap ms').
    Proof using.
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

          destruct (add_all_to_heap' (mkMemoryStack m fs h) root ptrs) eqn:ADD_ALL'.
          cbn.

          rename memory_stack_memory0 into m0.
          rename memory_stack_frame_stack0 into f.
          rename memory_stack_heap0 into h0.

          assert (add_to_heap (mkMemoryStack m0 f h0) root a = add_to_heap (mkMemoryStack m0 f h0) root a) as ADD' by reflexivity.
          pose proof (add_all_to_heap'_cons_swap _ _ _ _ _ _ _ _ ADD ADD_ALL ADD_ALL' ADD') as EQV.
          cbn in EQV.
          replace h0 with (memory_stack_heap (mkMemoryStack m0 fs h0)) at 1 by reflexivity.
          rewrite EQV.
          replace (add_with (ptr_to_int root) a (fun x : addr => [x]) cons h0)
            with (memory_stack_heap (mkMemoryStack m0 fs (add_with (ptr_to_int root) a (fun x : addr => [x]) cons h0))) by reflexivity.
          eapply add_to_heap_correct.
          cbn.
          reflexivity.
    Qed.

    Lemma add_all_to_heap_correct :
      forall ptrs (ms : memory_stack) (ms' : memory_stack),
        add_all_to_heap ms ptrs = ms' ->
        add_ptrs_to_heap (memory_stack_heap ms) ptrs (memory_stack_heap ms').
    Proof using.
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
    Proof using.
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
    Proof using.
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
    Proof using.
      intros [[m fsm] pr] fs EQ; subst.
      red; cbn.
      red.
      reflexivity.
    Qed.

    (* These should be opaque for convenience *)
    #[global] Opaque add_all_to_frame.
    #[global] Opaque add_all_to_heap.
    #[global] Opaque next_memory_key.

    Definition get_free_block `{MemMonad MemM (itree Eff)} (len : nat) (pr : Provenance) : MemM (addr * list addr)%type :=
      ms <- get_mem_state;;
      let mem_stack := ms_memory_stack ms in
      let addr := next_memory_key mem_stack in
      let '(mkMemoryStack mem fs h) := ms_memory_stack ms in
      let aid := provenance_to_allocation_id pr in
      ptr <- lift_OOM (int_to_ptr addr (allocation_id_to_prov aid));;
      ptrs <- get_consecutive_ptrs ptr len;;
      ret (ptr, ptrs).

    Definition sbytes_to_mem_bytes (aid : AllocationId) (bytes : list SByte) : list mem_byte :=
      map (fun b => (b, aid)) bytes.

    (** Add block to memory with a given allocation id *)
    Definition add_block `{MemMonad MemM (itree Eff)} (aid : AllocationId) (ptr : addr) (ptrs : list addr) (init_bytes : list SByte) : MemM unit :=
      let mem_bytes := sbytes_to_mem_bytes aid init_bytes in
      ms <- get_mem_state;;
      let '(mkMemoryStack mem fs h) := mem_state_memory_stack ms in

      (* Add bytes to memory *)
      let mem' := add_all_index (map (fun b => (b, aid)) init_bytes) (ptr_to_int ptr) mem in
      put_mem_state (MemState_put_memory (mkMemoryStack mem' fs h) ms).

    (** Add pointers to the stack frame *)
    Definition add_ptrs_to_frame `{MemMonad MemM (itree Eff)} (ptrs : list addr) : MemM unit :=
      modify_mem_state
        (fun ms =>
           let mem := MemState_get_memory ms in
           MemState_put_memory (add_all_to_frame mem ptrs) ms);;
      ret tt.

    Definition add_ptrs_to_heap `{MemMonad MemM (itree Eff)} (ptrs : list addr) : MemM unit :=
      modify_mem_state
        (fun ms =>
           let mem := MemState_get_memory ms in
           MemState_put_memory (add_all_to_heap mem ptrs) ms);;
      ret tt.

    (** Add a block of bytes to memory, and register it in the current stack frame. *)
    Definition add_block_to_stack `{MemMonad MemM (itree Eff)} (aid : AllocationId) (ptr : addr) (ptrs : list addr) (init_bytes : list SByte) : MemM unit :=
      add_block aid ptr ptrs init_bytes;;
      add_ptrs_to_frame ptrs.

    (** Add a block of bytes to memory, and register it in the heap. *)
    (* Should we make sure ptr (the root) is added even if ptrs is empty? *)
    Definition add_block_to_heap `{MemMonad MemM (itree Eff)} (aid : AllocationId) (ptr : addr) (ptrs : list addr) (init_bytes : list SByte) : MemM unit :=
      add_block aid ptr ptrs init_bytes;;
      add_ptrs_to_heap ptrs.

    Definition allocate_bytes_with_pr `{MemMonad MemM (itree Eff)}
      (init_bytes : list SByte) (pr : Provenance)
      : MemM addr
      := let len := length init_bytes in
         '(ptr, ptrs) <- get_free_block len pr;;
         let aid := provenance_to_allocation_id pr in
         add_block_to_stack aid ptr ptrs init_bytes;;
         ret ptr.

    Definition allocate_bytes `{MemMonad MemM (itree Eff)}
      (init_bytes : list SByte) : MemM addr :=
      pr <- fresh_provenance;;
      allocate_bytes_with_pr init_bytes pr.

    (** Heap allocation *)
    Definition malloc_bytes_with_pr `{MemMonad MemM (itree Eff)} (init_bytes : list SByte) (pr : Provenance) : MemM addr :=
      let len := length init_bytes in
      '(ptr, ptrs) <- get_free_block len pr;;
      let aid := provenance_to_allocation_id pr in
      add_block_to_heap aid ptr ptrs init_bytes;;
      ret ptr.

    Definition malloc_bytes `{MemMonad MemM (itree Eff)} (init_bytes : list SByte) : MemM addr :=
      pr <- fresh_provenance;;
      malloc_bytes_with_pr init_bytes pr.

    (** Frame stacks *)
    (* Check if an address is allocated in a frame *)
    Definition ptr_in_frame (f : Frame) (ptr : addr) : bool
      := existsb (fun p => Z.eqb (ptr_to_int ptr) p) (map ptr_to_int f).

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
    Proof using.
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
    Proof using.
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
    Proof using.
      intros [[m fsm] pr] fs.
      red; cbn.
      red.
      reflexivity.
    Qed.

    Lemma mem_state_heap_prop_set_refl :
      forall ms h,
        mem_state_heap_prop (mem_state_set_heap ms h) h.
    Proof using.
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
    Proof using.
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
    Proof using.
      intros [[m fsm] pr] h h' h'' EQV MEMPROP.
      red; cbn.
      red in MEMPROP; cbn in MEMPROP.
      red. red in MEMPROP.
      rewrite <- EQV.
      auto.
    Qed.

    Definition mempush `{MemMonad MemM (itree Eff)} : MemM unit :=
      ms <- get_mem_state;;
      let fs := mem_state_frame_stack ms in
      let fs' := push_frame_stack fs initial_frame in
      let ms' := mem_state_set_frame_stack ms fs' in
      put_mem_state ms'.

    Definition free_byte
               (b : Z)
               (m : memory) : memory
      := delete b m.

    Definition free_frame_memory (f : Frame) (m : memory) : memory :=
      fold_left (fun m key => free_byte (ptr_to_int key) m) f m.

    Definition free_block_memory (block : Block) (m : memory) : memory :=
      fold_left (fun m key => free_byte (ptr_to_int key) m) block m.

    (** Stack free *)
    Definition mempop `{MemMonad MemM (itree Eff)} : MemM unit :=
      ms <- get_mem_state;;
      let '(mkMemoryStack mem fs h) := ms_memory_stack ms in
      let f := peek_frame_stack fs in
      fs' <- lift_err_RAISE_ERROR (pop_frame_stack fs);;
      let mem' := free_frame_memory f mem in
      let pr := mem_state_provenance ms in
      let ms' := mkMemState (mkMemoryStack mem' fs' h) pr in
      put_mem_state ms'.

    (** Free from heap *)
    Definition free `{MemMonad MemM (itree Eff)} (ptr : addr) : MemM unit :=
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
    Proof using.
      intros [ms1 pr1] [ms2 pr2] addr aid ALLOC EQ.
      cbn in EQ; subst.
      cbn in *; auto.
    Qed.

    (* TODO: move this *)
    Lemma read_byte_prop_mem_stack :
      forall ms1 ms2 addr sbyte,
        read_byte_prop ms1 addr sbyte ->
        mem_state_memory_stack ms1 = mem_state_memory_stack ms2 ->
        read_byte_prop ms2 addr sbyte.
    Proof using.
      intros [ms1 pr1] [ms2 pr2] addr aid READ EQ.
      cbn in EQ; subst.
      repeat red.
      repeat red in READ.
      cbn in *; auto.
    Qed.

    Lemma read_byte_prop_disjoint_set_byte_raw :
      forall ms1 ms2 ptr ptr' byte byte',
        disjoint_ptr_byte ptr ptr' ->
        mem_state_memory ms2 = set_byte_raw (mem_state_memory ms1) (ptr_to_int ptr') byte' ->
        read_byte_prop ms1 ptr byte <-> read_byte_prop ms2 ptr byte.
    Proof using.
      intros ms1 ms2 ptr ptr' byte byte' DISJOINT MEM.
      split; intros READ.
      - unfold mem_state_memory in *.
        repeat eexists;
          first [ cbn; (*unfold_mem_state_memory; *)
                  rewrite set_byte_raw_eq; [|solve [eauto]]
                | subst_mempropt
            ].
        repeat red; repeat red in READ.
        rewrite MEM.
        cbn.
        rewrite set_byte_raw_neq; eauto.
      - unfold mem_state_memory in *.
        repeat eexists;
          first [ cbn; (*unfold_mem_state_memory; *)
                  rewrite set_byte_raw_eq; [|solve [eauto]]
                | subst_mempropt
            ].
        repeat red; repeat red in READ.
        rewrite MEM in READ.
        rewrite set_byte_raw_neq in READ; eauto.
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
    Proof using.
      intros p1 p2 ms byte aid1 aid2 READ ALLOC PEQ.
      repeat red in ALLOC.
      rewrite <- PEQ in ALLOC.
      rewrite READ in ALLOC.
      destruct aid_eq_dec; subst; auto.
      inv ALLOC.
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
    Proof using.
      intros ptr aid new new_aid m1 m2 ALLOC MEM.
      repeat red in ALLOC.
      break_match_hyp; try contradiction.
      destruct m.
      repeat red.

      unfold mem_state_memory in *.
      rewrite MEM.
      rewrite set_byte_raw_eq; auto.
      red.
      symmetry.
      apply aid_eq_dec_refl.
    Qed.

    Lemma byte_allocated_set_byte_raw_neq :
      forall ptr aid new_ptr new new_aid m1 m2,
        byte_allocated m1 ptr aid ->
        disjoint_ptr_byte ptr new_ptr ->
        mem_state_memory m2 = set_byte_raw (mem_state_memory m1) (ptr_to_int new_ptr) (new, new_aid) ->
        byte_allocated m2 ptr aid.
    Proof using.
      intros ptr aid new_ptr new new_aid m1 m2 ALLOC DISJOINT MEM.
      repeat red in ALLOC.
      repeat red.

      unfold mem_state_memory in *.
      rewrite MEM.
      rewrite set_byte_raw_neq; auto.
    Qed.

    Lemma byte_allocated_set_byte_raw_neq' :
      forall ptr aid new_ptr new new_aid m1 m2,
        byte_allocated m2 ptr aid ->
        disjoint_ptr_byte ptr new_ptr ->
        mem_state_memory m2 = set_byte_raw (mem_state_memory m1) (ptr_to_int new_ptr) (new, new_aid) ->
        byte_allocated m1 ptr aid.
    Proof using.
      intros ptr aid new_ptr new new_aid m1 m2 ALLOC DISJOINT MEM.
      repeat red in ALLOC.
      repeat red.

      unfold mem_state_memory in *.
      rewrite MEM in ALLOC.
      rewrite set_byte_raw_neq in ALLOC; auto.
    Qed.

    Lemma byte_allocated_set_byte_raw :
      forall ptr aid ptr_new new m1 m2,
        byte_allocated m1 ptr aid ->
        mem_state_memory m2 = set_byte_raw (mem_state_memory m1) (ptr_to_int ptr_new) new ->
        exists aid2, byte_allocated m2 ptr aid2.
    Proof using.
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
    Proof using.
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
          repeat red.
          unfold mem_state_memory in *.
          rewrite READ.
          repeat red in ALLOC.
          cbn in ALLOC.
          rewrite set_byte_raw_eq in ALLOC; eauto.
        }
    Qed.

    Lemma byte_allocated_set_byte_raw'' :
      forall m1 m2 ptr_new ptr new_byte rbyte aid aid',
        read_byte_raw (mem_state_memory m1) (ptr_to_int ptr) = Some (rbyte, aid) ->
        access_allowed (address_provenance ptr) aid ->
        mem_state_memory m2 = set_byte_raw (mem_state_memory m1) (ptr_to_int ptr_new) (new_byte, aid) ->
        byte_allocated m1 ptr aid' <->
          byte_allocated m2 ptr aid'.
    Proof using.
      intros m1 m2 ptr_new ptr new_byte rbyte aid aid' READ ALLOWED MEMEQ.
      split; intros ALLOC.
      - pose proof disjoint_ptr_byte_dec ptr ptr_new as [DISJOINT | NDISJOINT].
        { eapply byte_allocated_set_byte_raw_neq; [eauto | | cbn; eauto]; eauto.
        }
        { eapply byte_allocated_set_byte_raw_eq; eauto.
          cbn.

          unfold mem_state_memory in *.
          repeat red in ALLOC.
          rewrite READ in ALLOC.
          prove_ptr_to_int_eq_subst ptr ptr_new.
          destruct aid_eq_dec; inv ALLOC.
          eauto.
        }
      - pose proof disjoint_ptr_byte_dec ptr ptr_new as [DISJOINT | NDISJOINT].
        {  eapply byte_allocated_set_byte_raw_neq' in ALLOC; [eauto | | cbn; eauto]; eauto.
        }
        { prove_ptr_to_int_eq_subst ptr_new ptr.

          unfold mem_state_memory in *.
          repeat red.
          rewrite READ.

          repeat red in ALLOC.
          rewrite MEMEQ in ALLOC.
          rewrite set_byte_raw_eq in ALLOC; eauto.
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
                | unfold mem_state_memory in *;
                  repeat red;
                  first [ cbn;
                          rewrite_set_byte_eq
                        | cbn;
                          rewrite_set_byte_neq
                        | subst_mempropt
                    ];
                  first
                    [ try reflexivity;
                      first [rewrite aid_access_allowed_refl | setoid_rewrite <- aid_eq_dec_refl]; auto
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
    Proof using.
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
    Proof using.
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
          unfold mem_state_memory in *.
          repeat red in ALLOC.
          repeat red; cbn in *.
          rewrite set_byte_raw_eq in ALLOC; eauto.
          destruct aid_eq_dec; inv ALLOC.

          exists aid; split; eauto.
          repeat red.
          rewrite READ; auto.
          symmetry.
          apply aid_eq_dec_refl.
        }
    Qed.

    Lemma read_byte_allowed_set_byte_raw :
      forall ms ptr1 ptr2 byte rbyte aid fs heap,
        read_byte_raw (mem_state_memory ms) (ptr_to_int ptr1) = Some (rbyte, aid) ->
        access_allowed (address_provenance ptr1) aid ->
        read_byte_allowed ms ptr2 <->
          read_byte_allowed {| ms_memory_stack := {| memory_stack_memory := set_byte_raw (mem_state_memory ms) (ptr_to_int ptr1) (byte, aid); memory_stack_frame_stack := fs; memory_stack_heap := heap |}; ms_provenance := mem_state_provenance ms |} ptr2.
    Proof using.
      eapply write_byte_allowed_set_byte_raw.
    Qed.

    Lemma free_byte_allowed_set_byte_raw :
      forall ms ptr1 ptr2 byte rbyte aid fs heap,
        read_byte_raw (mem_state_memory ms) (ptr_to_int ptr1) = Some (rbyte, aid) ->
        access_allowed (address_provenance ptr1) aid ->
        free_byte_allowed ms ptr2 <->
          free_byte_allowed {| ms_memory_stack := {| memory_stack_memory := set_byte_raw (mem_state_memory ms) (ptr_to_int ptr1) (byte, aid); memory_stack_frame_stack := fs; memory_stack_heap := heap |}; ms_provenance := mem_state_provenance ms |} ptr2.
    Proof using.
      eapply write_byte_allowed_set_byte_raw.
    Qed.

    Ltac solve_allowed_base :=
      eauto with AccessHints.

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
            [ eapply read_byte_allowed_set_byte_raw with (ms:=ms1); eauto
            | eapply read_byte_allowed_set_byte_raw with (ms:=ms2); eauto
            ]
      | _ =>
          solve
            [ solve_allowed_base
            | repeat red;
              cbn in *; eexists; split; [| solve_access_allowed]; solve_byte_allocated
            ]
      end.

    Ltac solve_free_byte_allowed :=
      match goal with
      | H: free_byte_allowed ?ms1 ?ptr |-
          free_byte_allowed ?ms2 ?ptr =>
          solve
            [ eapply free_byte_allowed_set_byte_raw with (ms:=ms1); eauto
            | eapply free_byte_allowed_set_byte_raw with (ms:=ms2); eauto
            ]
      | _ =>
          solve
            [ solve_allowed_base
            | repeat red;
              cbn in *; eexists; split; [| solve_access_allowed]; solve_byte_allocated
            ]
      end.

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
          eauto with ReadBytePropHints;
          solve [ eapply read_byte_prop_mem_stack; eauto
                | repeat red;
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
    Proof using.
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
    Proof using.
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

    Lemma read_byte_raw_read_byte_allowed :
      forall ms ptr sbyte aid,
        read_byte_raw (mem_state_memory ms) (ptr_to_int ptr) = Some (sbyte, aid) ->
        access_allowed (address_provenance ptr) aid = true ->
        read_byte_allowed ms ptr.
    Proof using.
      intros ms ptr sbyte aid RBR ACCESS.
      repeat red.
      exists aid.
      split; eauto.
      repeat red.
      unfold mem_state_memory in *.
      rewrite RBR.
      symmetry. apply aid_eq_dec_refl.
    Qed.

    Lemma read_byte_raw_write_byte_allowed :
      forall ms ptr sbyte aid,
        read_byte_raw (mem_state_memory ms) (ptr_to_int ptr) = Some (sbyte, aid) ->
        access_allowed (address_provenance ptr) aid = true ->
        write_byte_allowed ms ptr.
    Proof using.
      eapply read_byte_raw_read_byte_allowed.
    Qed.

    Lemma read_byte_raw_free_byte_allowed :
      forall ms ptr sbyte aid,
        read_byte_raw (mem_state_memory ms) (ptr_to_int ptr) = Some (sbyte, aid) ->
        access_allowed (address_provenance ptr) aid = true ->
        free_byte_allowed ms ptr.
    Proof using.
      eapply read_byte_raw_read_byte_allowed.
    Qed.

    #[global] Hint Resolve read_byte_raw_read_byte_allowed : AccessHints.
    #[global] Hint Resolve read_byte_raw_write_byte_allowed : AccessHints.
    #[global] Hint Resolve read_byte_raw_free_byte_allowed : AccessHints.

    Lemma read_byte_raw_read_byte_prop :
      forall ms ptr sbyte aid,
        read_byte_raw (mem_state_memory ms) (ptr_to_int ptr) = Some (sbyte, aid) ->
        access_allowed (address_provenance ptr) aid = true ->
        read_byte_prop ms ptr sbyte.
    Proof using.
      intros ms ptr sbyte aid RBR ACCESS.
      repeat red.
      unfold mem_state_memory in *.
      rewrite RBR; cbn.
      rewrite ACCESS.
      reflexivity.
    Qed.

    #[global] Hint Resolve read_byte_raw_read_byte_prop : ReadBytePropHints.

    Section MemoryPrimatives.
      Context {MemM : Type -> Type}.
      Context {Eff : Type -> Type}.
      (* Context `{Monad MemM}. *)
      (* Context `{MonadProvenance Provenance MemM}. *)
      (* Context `{MonadStoreID MemM}. *)
      (* Context `{MonadMemState MemState MemM}. *)
      (* Context `{RAISE_ERROR MemM} `{RAISE_UB MemM} `{RAISE_OOM MemM}. *)
      Context `{MemMonad MemM (itree Eff)}.

    (* TODO: add to solve_read_byte_allowed *)
    Lemma read_byte_allowed_set_frame_stack :
      forall ms f ptr,
        read_byte_allowed ms ptr <-> read_byte_allowed (mem_state_set_frame_stack ms f) ptr.
    Proof using.
      intros [[ms prov] fs] f ptr.
      cbn.
      unfold read_byte_allowed;
        split; intros READ;
        cbn in *; eauto.
    Qed.

    (* TODO: add to write_byte_allowed *)
    Lemma write_byte_allowed_set_frame_stack :
      forall ms f ptr,
        write_byte_allowed ms ptr <-> write_byte_allowed (mem_state_set_frame_stack ms f) ptr.
    Proof using.
      intros [[ms prov] fs] f ptr.
      cbn.
      unfold write_byte_allowed;
        split; intros WRITE;
        cbn in *; eauto.
    Qed.

    (* TODO: add to write_byte_allowed *)
    Lemma free_byte_allowed_set_frame_stack :
      forall ms f ptr,
        free_byte_allowed ms ptr <-> free_byte_allowed (mem_state_set_frame_stack ms f) ptr.
    Proof using.
      intros [[ms prov] fs] f ptr.
      cbn.
      unfold free_byte_allowed;
        split; intros FREE;
        cbn in *; eauto.
    Qed.

    (* TODO: add to solve_read_byte_prop_all_preserved. *)
    Lemma read_byte_prop_set_frame_stack :
      forall ms f,
        read_byte_prop_all_preserved ms (mem_state_set_frame_stack ms f).
    Proof using.
      intros [[ms prov] fs] f.
      cbn.
      unfold read_byte_prop_all_preserved, read_byte_prop.
      split; intros READ;
        cbn in *; eauto.
    Qed.

    (* TODO *)
    Lemma write_byte_allowed_all_preserved_set_frame_stack :
      forall ms f,
        write_byte_allowed_all_preserved ms (mem_state_set_frame_stack ms f).
    Proof using.
      intros ms f ptr.
      eapply write_byte_allowed_set_frame_stack.
    Qed.

    Lemma free_byte_allowed_all_preserved_set_frame_stack :
      forall ms f,
        free_byte_allowed_all_preserved ms (mem_state_set_frame_stack ms f).
    Proof using.
      intros ms f ptr.
      eapply free_byte_allowed_set_frame_stack.
    Qed.

    Lemma allocations_preserved_set_frame_stack :
      forall ms f,
        allocations_preserved ms (mem_state_set_frame_stack ms f).
    Proof using.
      intros ms f ptr aid.
      destruct ms as [[ms fs] pr].
      split; intros ALLOC; repeat red in ALLOC; repeat red; cbn in *; auto.
    Qed.

    (* TODO: move *)
    Lemma preserve_allocation_ids_set_frame_stack :
      forall ms f,
        preserve_allocation_ids ms (mem_state_set_frame_stack ms f).
    Proof using.
      intros ms f pr.
      destruct ms as [[ms fs] pr'].
      split; intros USED;
        cbn in *; eauto.
    Qed.

    (** Correctness of the main operations on memory *)
    Lemma read_byte_correct :
      forall ptr pre,
        exec_correct pre (read_byte ptr) (read_byte_spec_MemPropT ptr)
          (fun ms st byte ms' st' => (exists s, MemByte.sbyte_sid byte = inr s /\ (s < st)%N) /\ ms = ms' /\ st = st').
    Proof using.
      unfold exec_correct.
      intros ptr pre ms st VALID.

      (* Need to destruct ahead of time so we know if UB happens *)
      destruct (read_byte_raw (mem_state_memory ms) (ptr_to_int ptr)) as [[sbyte aid]|] eqn:READ.
      destruct (access_allowed (address_provenance ptr) aid) eqn:ACCESS.
      - (* Success *)
        right.
        exists (ret sbyte), st, ms.
        unfold read_byte, read_byte_spec_MemPropT in *.
        split; [| split]; auto.

        { exists (ret sbyte).
          split.
          - cbn. reflexivity.
          - cbn.
            rewrite MemMonad_run_bind.
            rewrite MemMonad_get_mem_state.
            rewrite bind_ret_l.

            rewrite READ.
            rewrite ACCESS.

            rewrite MemMonad_run_ret.
            rewrite bind_ret_l.
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

        intros H1.
        destruct H1; inv H1.
        split; eauto.
        eexists; split; eauto.
        split; eauto.
        red in VALID.
        pose proof sbyte_to_extractbyte_inv x as (?&?&?&?&?).
        unfold sbyte_sid.
        rewrite e.
        exists x3.
        split; eauto.
        eapply VALID.
        repeat red.
        exists ptr. exists x.
        unfold sbyte_sid.
        rewrite e.
        split; auto.
        eapply read_byte_raw_read_byte_prop; eauto.
      - (* UB from provenance mismatch *)
        left.
        unfold read_byte_spec_MemPropT.
        unfold lift_spec_to_MemPropT.
        exists ms. exists (""%string).
        cbn.
        intros ALLOWED.
        repeat red in ALLOWED.
        destruct ALLOWED as (?&?&?).
        repeat red in H1.
        unfold mem_state_memory in *.
        rewrite READ in H1.
        apply proj_sumbool_true in H1; subst.
        rewrite ACCESS in H2.
        discriminate.
      - (* UB from accessing unallocated memory *)
        left.
        exists ms. exists (""%string).
        cbn.
        intros CONTRA.
        unfold mem_state_memory in *.
        break_access_hyps.
        repeat red in ALLOC.
        rewrite READ in ALLOC.
        auto.
    Qed.

    Lemma write_byte_correct :
      forall ptr byte,
        exec_correct
          (fun ms st => exists s, sbyte_sid byte = inr s /\ (s < st)%N)
          (write_byte ptr byte) (write_byte_spec_MemPropT ptr byte)
          (fun _ st _ _ st' => st = st').
    Proof using.
      unfold exec_correct.
      intros ptr byte ms st VALID.

      (* Need to destruct ahead of time so we know if UB happens *)
      destruct (read_byte_raw (mem_state_memory ms) (ptr_to_int ptr)) as [[sbyte aid]|] eqn:READ.
      destruct (access_allowed (address_provenance ptr) aid) eqn:ACCESS.
      - (* Success *)
        right.
        exists (ret tt).
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
        unfold write_byte, write_byte_spec_MemPropT in *.
        unfold read_byte, read_byte_spec_MemPropT in *.
        split; [| split]; auto.

        { exists (ret tt).
          split.
          - cbn. reflexivity.
          - cbn.
            rewrite MemMonad_run_bind.
            rewrite MemMonad_get_mem_state.
            rewrite bind_ret_l.

            rewrite READ.
            rewrite ACCESS.

            rewrite MemMonad_put_mem_state.
            rewrite bind_ret_l.
            reflexivity.
        }

        { cbn.
          unfold mem_state_memory in *.
          solve_write_byte_spec.
        }

        intros _.
        split; eauto.
        repeat red in VALID.
        repeat red.
        intros sid' USED.
        repeat red in USED.
        destruct USED as (?&?&?&?).
        repeat red in H1.
        cbn in *.
        (* Depends if x = ptr *)
        pose proof (Z.eq_dec (ptr_to_int ptr) (ptr_to_int x)) as [EQ | NEQ].
        { rewrite EQ in H1.
          rewrite set_byte_raw_eq in H1; eauto.
          break_match_hyp_inv.
          cbn in *.
          destruct H0 as (?&?&?).
          rewrite H0 in H2; inv H2.
          apply N.compare_lt_iff; auto.
        }

        rewrite set_byte_raw_neq in H1; eauto.
        break_match_hyp; try contradiction.
        break_match_hyp; try contradiction.
        eapply VALID.
        repeat red.
        exists x.
        exists x0.
        split; eauto.
        repeat red.
        cbn.
        rewrite memory_stack_memory_mem_state_memory.
        rewrite Heqo, Heqb.
        auto.
      - (* UB from provenance mismatch *)
        left.
        exists ms. exists (""%string).
        cbn.
        intros CONTRA.
        unfold mem_state_memory in *.
        break_access_hyps.
        repeat red in ALLOC.
        rewrite READ in ALLOC.
        auto.
        apply proj_sumbool_true in ALLOC; subst.
        rewrite ACCESS in ALLOWED.
        discriminate.
      - (* UB from accessing unallocated memory *)
        left.
        exists ms. exists (""%string).
        cbn.
        intros CONTRA.
        unfold mem_state_memory in *.
        break_access_hyps.
        repeat red in ALLOC.
        rewrite READ in ALLOC.
        auto.
    Qed.

    Lemma write_byte_preserves_store_id :
      forall st ms a b st' ms' res,
        @within MemM EQM err_ub_oom (prod store_id MemState) (prod store_id MemState)
          (@Within_err_ub_oom_MemM MemM Eff
             (@MemMonad_eq1_runm MemM (itree Eff) MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB
                RunOOM EQM EQRI MLAWS H) MRun
             (@MemMonad_eq1_runm_equiv MemM (itree Eff) MM MRun MPROV MSID MMS MERR MUB MOOM RunERR
                RunUB RunOOM EQM EQRI MLAWS H) RunERR RunUB RunOOM MM MRun MPROV MSID MMS MERR MUB
             MOOM RunERR RunUB RunOOM EQM EQRI MLAWS H) unit
          (write_byte a b) (@pair store_id MemState st ms)
          (@ret err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) unit res)
          (@pair store_id MemState st' ms') ->
        st = st'.
    Proof.
      intros st ms a b st' ms' res WRITE.
      repeat red in WRITE.
      destruct WRITE as (?&?&?).
      cbn in *.
      rewrite H0, bind_ret_l in H1.
      unfold write_byte in *.
      rewrite MemMonad_run_bind in H1.
      rewrite MemMonad_get_mem_state, bind_ret_l in H1.
      break_match_hyp.
      { (* Byte read from memory *)
        destruct m.
        break_match_hyp.
        { (* Access allowed *)
          rewrite MemMonad_put_mem_state in H1.
          eapply eq1_ret_ret in H1; try typeclasses eauto.
          inv H1; auto.
        }

        { (* Access not allowed *)
          symmetry in H1.
          rewrite MemMonad_run_raise_ub in H1.
          eapply MemMonad_eq1_raise_ub_inv in H1; try contradiction.
        }
      }

      { (* No byte in memory *)
        symmetry in H1.
        rewrite MemMonad_run_raise_ub in H1.
        eapply MemMonad_eq1_raise_ub_inv in H1; try contradiction.
      }
    Qed.

    (* TODO: move this? *)
    Lemma MemMonad_run_get_consecutive_ptrs:
      forall {M RunM : Type -> Type} {MM : Monad M} {MRun : Monad RunM}
        {MPROV : MonadProvenance Provenance M} {MSID : MonadStoreId M} {MMS : MonadMemState MemState M}
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
              (prod store_id (prod MemState (list addr)))
              (@MemMonad_run
           M RunM MM MRun MPROV MSID MMS MERR MUB MOOM RunERR RunUB RunOOM _ _ _ MemMonad (list addr)
           (@get_consecutive_ptrs M MM MOOM MERR ptr len) ms st)
              (fmap (fun ptrs => (st, (ms, ptrs))) (@get_consecutive_ptrs RunM MRun RunOOM RunERR ptr len)))%monad.
    Proof using.
      intros M RunM MM0 MRun0 MPROV0 MSID0 MMS0 MERR0 MUB0 MOOM0 RunERR0 RunUB0 RunOOM0 EQM'
        EQRI' MLAWS' MemMonad0 EQV LAWS RAISEOOM RAISEERR ms ptr len st.
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

    Lemma byte_not_allocated_ge_next_memory_key :
      forall (mem : memory_stack) (ms : MemState) (ptr : addr),
        MemState_get_memory ms = mem ->
        next_memory_key mem <= ptr_to_int ptr ->
        byte_not_allocated ms ptr.
    Proof using.
      intros mem ms ptr MEM NEXT.
      unfold byte_not_allocated.
      unfold byte_allocated.
      intros aid CONTRA.
      cbn in CONTRA.
      repeat red in CONTRA.
      rewrite read_byte_raw_next_memory_key in CONTRA; eauto.
      rewrite next_memory_key_next_key_memory_stack_memory in NEXT.
      subst.
      lia.
    Qed.

  Lemma byte_not_allocated_get_consecutive_ptrs :
    forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
      `{EQV : @Eq1Equivalence M HM EQM}
      `{WM : @Within M EQM err_ub_oom MemState MemState}
      `{EQRET : @Eq1_ret_inv M EQM HM}
      `{WRET : @Within_ret_inv M err_ub_oom MemState MemState HM _ EQM WM}
      `{LAWS : @MonadLawsE M EQM HM}
      `{RBMOOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
      `{RBMERR : @RaiseBindM M  HM EQM string (@raise_error M ERR)}
      `{RWOOM : @RaiseWithin M err_ub_oom _ _ _ EQM WM string (@raise_oom M OOM)}
      `{RWERR : @RaiseWithin M err_ub_oom _ _ _ EQM WM string (@raise_error M ERR)}
      (mem : memory_stack) (ms : MemState) (ms' : MemState) (ptr : addr) (len : nat) (ptrs : list addr),
      MemState_get_memory ms = mem ->
      next_memory_key mem <= ptr_to_int ptr ->
      (ret ptrs {{ms}} ∈ {{ms'}} @get_consecutive_ptrs M HM OOM ERR ptr len)%monad ->
      forall p, In p ptrs -> byte_not_allocated ms p.
  Proof using.
    intros M HM OOM ERR EQM' EQV WM EQRET WRET LAWS RBMOOM RBMERR RWOOM RWERR mem ms ms' ptr len ptrs MEM NEXT CONSEC p IN.
    pose proof get_consecutive_ptrs_ge ptr len ptrs (B:=err_ub_oom) as GE.
    forward GE.
    { exists ms. exists ms'.
      auto.
    }
    specialize (GE _ IN).
    eapply byte_not_allocated_ge_next_memory_key; eauto.
    lia.
  Qed.

    Lemma find_free_block_correct :
      forall len pr pre,
        exec_correct pre (get_free_block len pr) (find_free_block len pr) exec_correct_id_post.
    Proof using.
      unfold exec_correct.
      intros len pr pre ms st VALID.
      cbn.
      right.

      unfold get_free_block.
      unfold find_free_block.

      unfold transitive_within.
      cbn.
      setoid_rewrite MemMonad_run_bind.
      setoid_rewrite MemMonad_get_mem_state.
      setoid_rewrite bind_ret_l.
      destruct ms as [[mem fs heap] pr'] eqn:Hms.
      cbn.

      destruct (int_to_ptr (next_memory_key {| memory_stack_memory := mem; memory_stack_frame_stack := fs; memory_stack_heap := heap |})
                  (allocation_id_to_prov (provenance_to_allocation_id pr))) eqn:HI2P.
      2: {
        (* OOM when getting the next pointer *)
        cbn.
        rename s into oom_msg.
        exists (raise_oom oom_msg).
        exists st. exists ms.
        split.
        { exists (raise_oom oom_msg).
          cbn.
          split.
          - eexists; reflexivity.
          - rewrite MemMonad_run_bind.
            rewrite MemMonad_run_raise_oom.
            rewrite rbm_raise_bind; [|typeclasses eauto].
            rewrite rbm_raise_bind; [|typeclasses eauto].
            reflexivity.
        }

        cbn.
        split; auto.
        intros [x CONTRA]; inv CONTRA.
      }

      cbn.
      setoid_rewrite bind_ret_l.

      match goal with
      | _ : _ |- context [@get_consecutive_ptrs ?MemM ?MM ?OOM ?ERR ?ptr ?len] =>
          epose proof (@get_consecutive_ptrs_inv (itree Eff) MRun RunOOM RunERR (@MemMonad_eq1_runm MemM (itree Eff) MM MRun MPROV MSID MMS MERR MUB MOOM RunERR
                                                                                                    RunUB RunOOM _ _ _ H) _ _ _ ptr len)
          as [[oom_msg CONSEC_OOM] | [ptrs CONSEC_RET]]
      end.

      - (* OOM when finding consecutive pointers *)
        exists (raise_oom oom_msg).
        exists st. exists ms.
        split.
        { exists (raise_oom oom_msg).
          cbn.
          split.
          - eexists; reflexivity.
          - rewrite MemMonad_run_bind.
            rewrite MemMonad_run_get_consecutive_ptrs.

            setoid_rewrite CONSEC_OOM.
            cbn.
            unfold liftM.
            rewrite bind_bind.
            rewrite rbm_raise_bind; [|typeclasses eauto].
            rewrite rbm_raise_bind; [|typeclasses eauto].
            reflexivity.
        }

        cbn.
        split; auto.
        intros [x CONTRA]; inv CONTRA.
      - (* Finding consecutive block is successful *)
        exists (ret (a, ptrs)).
        exists st.
        exists {|
              ms_memory_stack :=
                {|
                  memory_stack_memory := mem; memory_stack_frame_stack := fs; memory_stack_heap := heap
                |};
              ms_provenance := pr'
          |}.

        split.
        { exists (ret (a, ptrs)).
          cbn.
          split.
          - reflexivity.
          - rewrite MemMonad_run_bind.
            rewrite MemMonad_run_get_consecutive_ptrs.
            rewrite CONSEC_RET.
            cbn.
            unfold liftM.
            repeat rewrite bind_ret_l.
            rewrite MemMonad_run_ret.
            reflexivity.
        }

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
          pose proof (exec_correct_get_consecutive_pointers len a).

          unfold exec_correct in H1.

          specialize (H1 len
                         a
                         pre {|
              ms_memory_stack :=
                {|
                  memory_stack_memory := mem; memory_stack_frame_stack := fs; memory_stack_heap := heap
                |};
              ms_provenance := pr'
                        |} st VALID H0).
          destruct H1.
          { (* UB case, should be dischargeable *)
            destruct H1 as [ms_ub [ubmsg CONTRA]].
            exfalso.

            assert (@raise_ub err_ub_oom _ _ ubmsg ∈
                      @get_consecutive_ptrs
                      (MemPropT MemState) (@MemPropT_Monad MemState)
                         (@MemPropT_RAISE_OOM MemState) (@MemPropT_RAISE_ERROR MemState)
                         a len) as CONTRA'.
            { do 2 eexists.
              eapply CONTRA.
            }

            eapply get_consecutive_ptrs_no_ub in CONTRA'; eauto.
          }

          destruct H1 as [e_gep [st_gep [ms_gep [GEP_EXEC [GEP_SPEC GEP_POST]]]]].

          cbn in GEP_EXEC.
          red in GEP_EXEC.
          destruct GEP_EXEC as [t_gep [GEP_EXEC T_GEP_EXEC]].
          cbn in GEP_EXEC.
          red in GEP_EXEC.

          cbn in T_GEP_EXEC.

          rewrite MemMonad_run_get_consecutive_ptrs in T_GEP_EXEC.
          rewrite CONSEC_RET in T_GEP_EXEC.
          cbn in T_GEP_EXEC.
          unfold liftM in T_GEP_EXEC.
          rewrite bind_ret_l in T_GEP_EXEC.

          destruct e_gep as [[[[[[[oom_e_gep] | [[ub_e_gep] | [[err_e_gep] | e_gep_res]]]]]]]] eqn:He_gep.
          { (* OOM *)
            destruct GEP_EXEC as [msg GEP_EXEC].
            rewrite GEP_EXEC in T_GEP_EXEC.
            rewrite rbm_raise_bind in T_GEP_EXEC; [| typeclasses eauto].
            apply MemMonad_eq1_raise_oom_inv in T_GEP_EXEC.
            contradiction.
          }

          { (* UB *)
            destruct GEP_EXEC as [msg GEP_EXEC].
            rewrite GEP_EXEC in T_GEP_EXEC.
            rewrite rbm_raise_bind in T_GEP_EXEC; [| typeclasses eauto].
            apply MemMonad_eq1_raise_ub_inv in T_GEP_EXEC.
            contradiction.
          }

          { (* Error *)
            destruct GEP_EXEC as [msg GEP_EXEC].
            rewrite GEP_EXEC in T_GEP_EXEC.
            rewrite rbm_raise_bind in T_GEP_EXEC; [| typeclasses eauto].
            apply MemMonad_eq1_raise_error_inv in T_GEP_EXEC.
            contradiction.
          }

          { (* Success *)
            rewrite GEP_EXEC in T_GEP_EXEC.
            rewrite bind_ret_l in T_GEP_EXEC.
            apply eq1_ret_ret in T_GEP_EXEC; [| typeclasses eauto].
            inv T_GEP_EXEC.
            auto.
          }
        + (* TODO: autorewrite tactic? *)
          erewrite int_to_ptr_provenance; eauto.
        + intros ptr IN.

          eapply get_consecutive_ptrs_prov_eq1 in CONSEC_RET; eauto.
          apply int_to_ptr_provenance in HI2P; congruence.
        + intros ptr IN.
          (* Should follow from VALID... *)
          (* May actually follow from next_memory_key *)
          unfold byte_not_allocated.
          intros aid CONTRA.
          repeat red in CONTRA.
          cbn in *.
          erewrite read_byte_raw_next_memory_key in CONTRA; eauto.

          eapply get_consecutive_ptrs_ge_eq1 with (p := ptr) in CONSEC_RET; eauto.
          erewrite ptr_to_int_int_to_ptr in CONSEC_RET; eauto.
          rewrite next_memory_key_next_key in CONSEC_RET.
          lia.
        + intros [[a' addrs'] ADDRS]; inv ADDRS.
          split; eauto.
          eexists; split; eauto.
          reflexivity.
    Qed.

    Hint Resolve find_free_block_correct : EXEC_CORRECT.

    Lemma mem_state_fresh_provenance_correct :
      forall ms_init ms_fresh_pr (pr : Provenance),
        mem_state_fresh_provenance ms_init = (pr, ms_fresh_pr) ->
        @fresh_provenance Provenance (MemPropT MemState) _ ms_init (ret (ms_fresh_pr, pr)).
    Proof using.
      intros ms_init ms_fresh_pr pr FRESH.
      cbn.
      unfold mem_state_fresh_provenance in FRESH.
      destruct ms_init as (ms & pr_init).
      inv FRESH.

      solve_fresh_provenance_invariants.
    Qed.

    Lemma byte_allocated_add_all_index :
      forall (ms : MemState) (mem : memory) (bytes : list mem_byte) (ix : Z) (aid : AllocationId),
        mem_state_memory ms = add_all_index bytes ix mem ->
        (forall mb, In mb bytes -> snd mb = aid) ->
        (forall p, ix <= ptr_to_int p < ix + (Z.of_nat (length bytes)) -> byte_allocated ms p aid).
    Proof using.
      intros ms mem bytes ix aid MEM IN p RANGE.
      repeat red.

      unfold mem_state_memory in MEM.
      cbn in MEM.
      rewrite MEM.

      pose proof read_byte_raw_add_all_index_in_exists mem bytes ix (ptr_to_int p) as READ.
      forward READ.
      { rewrite Zlength_correct.
        lia.
      }

      destruct READ as [[b aid'] [NTH READ]].
      rewrite READ.
      apply list_nth_z_in in NTH.
      apply IN in NTH.
      inv NTH.
      cbn.
      symmetry; apply aid_eq_dec_refl.
    Qed.

    Lemma byte_allocated_get_consecutive_ptrs :
      forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
        {Pre Post : Type}
        {B} `{MB : Monad B}
        `{WM : @Within M EQM B Pre Post}
        `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
        `{WRET : @Within_ret_inv M B Pre Post HM _ EQM WM}
        `{LAWS: @MonadLawsE M EQM HM}
        `{RBMOOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
        `{RBMERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}
        `{RWOOM : @RaiseWithin M B _ _ _ EQM WM string (@raise_oom M OOM)}
        `{RWERR : @RaiseWithin M B _ _ _ EQM WM string (@raise_error M ERR)}

        (mem : memory) (ms : MemState) (ptr : addr) (len : nat) (ptrs : list addr)
        (bytes : list mem_byte) (aid : AllocationId),
        mem_state_memory ms = add_all_index bytes (ptr_to_int ptr) mem ->
        length bytes = len ->
        (forall mb, In mb bytes -> snd mb = aid) ->
        (ret ptrs ∈ @get_consecutive_ptrs M HM OOM ERR ptr len)%monad ->
        forall p, In p ptrs -> byte_allocated ms p aid.
    Proof using.
      intros M HM OOM ERR EQM' Pre Post B MB WM EQV EQRET WRET LAWS
        RBMOOM RBMERR RWOOM RWERR
        mem ms ptr len ptrs
        bytes aid MEM LEN AIDS CONSEC p IN.

      eapply byte_allocated_add_all_index; eauto.
      eapply get_consecutive_ptrs_range in CONSEC; eauto.
      lia.
    Qed.

    Lemma get_consecutive_ptrs_MemPropT_MemState :
      forall ptr len ptrs ms1 ms2 ,
        (@get_consecutive_ptrs (MemPropT MemState) (@MemPropT_Monad MemState) (@MemPropT_RAISE_OOM MemState)
                               (@MemPropT_RAISE_ERROR MemState) ptr len ms1 (ret (ms1, ptrs))) ->
        (@get_consecutive_ptrs (MemPropT MemState) (@MemPropT_Monad MemState) (@MemPropT_RAISE_OOM MemState)
                               (@MemPropT_RAISE_ERROR MemState) ptr len ms2 (ret (ms2, ptrs))).
    Proof using.
      intros ptr len ptrs ms1 ms2 CONSEC.
      cbn in *.
      destruct CONSEC as [ms' [ixs [SEQ MAPM]]].
      destruct (intptr_seq 0 len) eqn:HSEQ; cbn in SEQ; inv SEQ.
      cbn.
      exists ms2. exists l.
      split; auto.

      destruct (map_monad (fun ix : IP.intptr => handle_gep_addr (DTYPE_I 8) ptr [Events.DV.DVALUE_IPTR ix]) l) eqn:HMAPM; cbn in *.
      destruct MAPM as [_ [_ [[] _]]].
      destruct MAPM as [sab [a [[EQSAB EQA] SEQUENCE]]]; subst.
      exists ms2. exists l0.
      split; auto.

      destruct (Monads.sequence l0) eqn:HSEQUENCE;
        cbn in *; tauto.
    Qed.

    Lemma get_consecutive_ptrs_MemPropT_MemState_eq :
      forall ptr len ptrs ms1 ms2 ,
        (@get_consecutive_ptrs (MemPropT MemState) (@MemPropT_Monad MemState) (@MemPropT_RAISE_OOM MemState)
           (@MemPropT_RAISE_ERROR MemState) ptr len ms1 (ret (ms2, ptrs))) ->
        ms1 = ms2.
    Proof using.
      intros ptr len ptrs ms1 ms2 CONSEC.
      cbn in *.
      destruct CONSEC as [ms' [ixs [SEQ MAPM]]].
      destruct (intptr_seq 0 len) eqn:HSEQ; cbn in SEQ; inv SEQ.
      cbn.
      destruct (map_monad (fun ix : IP.intptr => handle_gep_addr (DTYPE_I 8) ptr [Events.DV.DVALUE_IPTR ix]) l) eqn:HMAPM; cbn in *.
      destruct MAPM as [_ [_ [[] _]]].
      destruct MAPM as [sab [a [[EQSAB EQA] SEQUENCE]]]; subst.
      destruct (Monads.sequence l0) eqn:HSEQUENCE;
        cbn in *; inv SEQUENCE; auto.
    Qed.

    Lemma get_consecutive_ptrs_MemPropT_eq1 :
      forall ptr len ptrs ms1,
        (@get_consecutive_ptrs (MemPropT MemState) (@MemPropT_Monad MemState) (@MemPropT_RAISE_OOM MemState)
                               (@MemPropT_RAISE_ERROR MemState) ptr len ms1 (ret (ms1, ptrs))) ->
        (@get_consecutive_ptrs (MemPropT MemState) (@MemPropT_Monad MemState) (@MemPropT_RAISE_OOM MemState)
                               (@MemPropT_RAISE_ERROR MemState) ptr len ≈ ret ptrs)%monad.
    Proof using.
      intros ptr len ptrs ms1 CONSEC.
      cbn in *.
      destruct CONSEC as [ms' [ixs [SEQ MAPM]]].
      destruct (intptr_seq 0 len) eqn:HSEQ; cbn in SEQ; inv SEQ.
      destruct (map_monad
                  (fun ix : IP.intptr => handle_gep_addr (DTYPE_I 8) ptr [Events.DV.DVALUE_IPTR ix]) l) eqn:HMAPM.
      destruct MAPM as [_ [_ [[] _]]].
      destruct MAPM as [sab [a [[EQSAB EQA] SEQUENCE]]]; subst.
      destruct (Monads.sequence l0) eqn:HSEQUENCE.
      2: {
        exfalso.
        cbn in *.
        auto.
      }

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
          cbn in *.
          destruct MAPM2 as [[] | MAPM2].
          destruct MAPM2 as [sab [a [[EQSAB EQA] SEQUENCE']]]; subst.
          rewrite HSEQUENCE in SEQUENCE'.
          cbn in *.
          auto.
        + destruct CONSEC as [[] | CONSEC].
          destruct CONSEC as [ms_ [ixs [[EQ1 EQ2] MAPM2]]].
          inv EQ1.
          rewrite HMAPM in MAPM2.
          cbn in *.
          destruct MAPM2 as [[] | MAPM2].
          destruct MAPM2 as [sab [a [[EQSAB EQA] SEQUENCE']]]; subst.
          rewrite HSEQUENCE in SEQUENCE'.
          cbn in SEQUENCE'.
          auto.
        + destruct CONSEC as [[] | CONSEC].
          destruct CONSEC as [ms_ [ixs [[EQ1 EQ2] MAPM2]]].
          inv EQ1.
          rewrite HMAPM in MAPM2.
          destruct MAPM2 as [[] | MAPM2].
          destruct MAPM2 as [sab [a [[EQSAB EQA] SEQUENCE']]]; subst.
          rewrite HSEQUENCE in SEQUENCE'.
          cbn in *.
          auto.
        + destruct x0.
          destruct CONSEC as [ms_ [ixs [[EQ1 EQ2] MAPM2]]].
          inv EQ1.
          rewrite HMAPM in MAPM2.
          destruct MAPM2 as [sab [a [[EQSAB EQA] SEQUENCE']]]; subst.
          rewrite HSEQUENCE in SEQUENCE'.
          cbn in *.
          inv SEQUENCE.
          inv SEQUENCE'.
          auto.
      - destruct_err_ub_oom x; try inv CONSEC.
        destruct x0.
        inv CONSEC.
        exists ms. exists l.
        split; auto.
        eexists. exists l0.
        rewrite HMAPM.
        rewrite HSEQUENCE.
        cbn. split; auto.
        cbn in *.
        tauto.
    Qed.

    Lemma byte_allocated_memory_eq :
      forall (ms ms' : MemState) (ptr : addr) (aid : AllocationId),
        byte_allocated ms ptr aid ->
        mem_state_memory ms = mem_state_memory ms' -> byte_allocated ms' ptr aid.
    Proof using.
      intros ms ms' ptr aid ALLOC MEM.
      repeat red in ALLOC.
      repeat red.
      cbn in *.
      unfold mem_state_memory in *.
      rewrite <- MEM.
      repeat break_match_goal; tauto.
    Qed.

    Lemma byte_allocated_preserved_get_consecutive_ptrs :
      forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
        {Pre Post : Type}
        {B} `{MB : Monad B}
        `{WM : @Within M EQM B Pre Post}
        `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
        `{WRET : @Within_ret_inv M B Pre Post HM _ EQM WM}
        `{LAWS: @MonadLawsE M EQM HM}
        `{RBMOOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
        `{RBMERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}
        `{RWOOM : @RaiseWithin M B _ _ _ EQM WM string (@raise_oom M OOM)}
        `{RWERR : @RaiseWithin M B _ _ _ EQM WM string (@raise_error M ERR)}

        (ms ms': MemState) (ptr_old ptr : addr) (len : nat) (ptrs : list addr)
        (bytes : list mem_byte) (aid : AllocationId),
        mem_state_memory ms' = add_all_index bytes (ptr_to_int ptr) (mem_state_memory ms) ->
        length bytes = len ->
        (forall p : addr, In p ptrs -> disjoint_ptr_byte p ptr_old) ->
        (ret ptrs ∈ @get_consecutive_ptrs M HM OOM ERR ptr len)%monad ->
        byte_allocated ms ptr_old aid <-> byte_allocated ms' ptr_old aid.
    Proof using.
      intros M HM OOM ERR EQM0 Pre Post B MB WM
        EQV EQRET WRET LAWS RBMOOM RBMERR RWOOM RWERR ms ms' ptr_old ptr
        len ptrs bytes aid MEM LEN DISJOINT CONSEC.

      unfold mem_state_memory in *.

      split; intros ALLOC.
      - repeat red in ALLOC.
        repeat red.
        rewrite MEM.
        erewrite read_byte_raw_add_all_index_out.
        2: {
          subst.
          pose proof (get_consecutive_ptrs_covers_range ptr (Datatypes.length bytes) ptrs CONSEC) as INRANGE.
          subst.
          rewrite <- Zlength_correct in INRANGE.

          pose proof (Z_lt_ge_dec (ptr_to_int ptr_old) (ptr_to_int ptr)) as [LTNEXT | GENEXT]; auto.
          pose proof (Z_ge_lt_dec (ptr_to_int ptr_old) (ptr_to_int ptr + Zlength bytes)) as [LTNEXT' | GENEXT']; auto.

          specialize (INRANGE (ptr_to_int ptr_old)).
          forward INRANGE; [lia|].
          destruct INRANGE as (p' & EQ & INRANGE).
          specialize (DISJOINT p' INRANGE).
          unfold disjoint_ptr_byte in DISJOINT.
          lia.
        }

        auto.
      - repeat red in ALLOC.
        repeat red.
        rewrite MEM in ALLOC.
        erewrite read_byte_raw_add_all_index_out in ALLOC.
        2: {
          subst.
          pose proof (get_consecutive_ptrs_covers_range ptr (Datatypes.length bytes) ptrs CONSEC) as INRANGE.
          subst.
          rewrite <- Zlength_correct in INRANGE.

          pose proof (Z_lt_ge_dec (ptr_to_int ptr_old) (ptr_to_int ptr)) as [LTNEXT | GENEXT]; auto.
          pose proof (Z_ge_lt_dec (ptr_to_int ptr_old) (ptr_to_int ptr + Zlength bytes)) as [LTNEXT' | GENEXT']; auto.

          specialize (INRANGE (ptr_to_int ptr_old)).
          forward INRANGE; [lia|].
          destruct INRANGE as (p' & EQ & INRANGE).
          specialize (DISJOINT p' INRANGE).
          unfold disjoint_ptr_byte in DISJOINT.
          lia.
        }

        auto.
    Qed.

    Lemma find_free_block_extend_allocations :
      forall ms_init ms_found_free ms_extended pr ptr ptrs init_bytes,
        ret (ptr, ptrs) {{ms_init}} ∈ {{ms_found_free}} find_free_block (length init_bytes) pr ->
        mem_state_memory ms_extended = add_all_index (map (fun b : SByte => (b, provenance_to_allocation_id pr)) init_bytes) (ptr_to_int ptr) (mem_state_memory ms_init) ->
        extend_allocations ms_init ptrs pr ms_extended.
    Proof using.
      intros ms_init ms_found_free ms_extended pr ptr ptrs init_bytes [MS FREE] MEM.
      inv MS; inv FREE.
      split.
      - eapply @byte_allocated_get_consecutive_ptrs
          with (HM:=@MemPropT_Monad MemState) (B:= err_ub_oom); try typeclasses eauto.

        unfold mem_state_memory in *.
        cbn; eauto.
        rewrite map_length; reflexivity.

        intros mb INMB.
        apply in_map_iff in INMB as (sb & MBEQ & INSB).
        inv MBEQ.
        cbn. reflexivity.

        exists ms_found_free.
        exists ms_found_free.
        auto.
      - intros ptr' aid IN.
        eapply @byte_allocated_preserved_get_consecutive_ptrs
          with (HM:=@MemPropT_Monad MemState) (B:= err_ub_oom); try typeclasses eauto.

        unfold mem_state_memory in *.
        cbn; eauto.
        rewrite map_length; reflexivity.
        eauto.

        exists ms_found_free.
        exists ms_found_free.
        auto.
    Qed.

    Lemma find_free_block_ms_eq :
      forall ms1 ms2 len pr ptr ptrs,
        ret (ptr, ptrs) {{ms1}} ∈ {{ms2}} find_free_block len pr ->
        ms1 = ms2.
    Proof using.
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

    Lemma read_byte_get_consecutive_ptrs :
      forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
        {Pre Post : Type}
        {B} `{MB : Monad B}
        `{WM : @Within M EQM B Pre Post}
        `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
        `{WRET : @Within_ret_inv M B Pre Post HM _ EQM WM}
        `{LAWS: @MonadLawsE M EQM HM}
        `{RBMOOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
        `{RBMERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}
        `{RWOOM : @RaiseWithin M B _ _ _ EQM WM string (@raise_oom M OOM)}
        `{RWERR : @RaiseWithin M B _ _ _ EQM WM string (@raise_error M ERR)}

        (ms ms' : MemState) (ptr : addr) (len : nat) (ptrs : list addr)
        (init_bytes : list SByte) (bytes : list mem_byte) pr (aid : AllocationId),
        mem_state_memory ms' = add_all_index bytes (ptr_to_int ptr) (mem_state_memory ms) ->
        (forall mb : mem_byte, In mb bytes -> snd mb = aid) ->
        bytes = map (fun b : SByte => (b, provenance_to_allocation_id pr)) init_bytes ->
        (ret ptrs ∈ @get_consecutive_ptrs M HM OOM ERR ptr len) ->
        (length bytes = len) ->
        forall p ix byte,
          Util.Nth ptrs ix p ->
          Util.Nth init_bytes ix byte ->
          access_allowed (address_provenance p) aid ->
          read_byte_prop ms' p byte.
    Proof using.
      intros M HM OOM ERR EQM0 Pre Post B MB WM EQV EQRET WRET LAWS RBMOOM RBMERR RWOOM RWERR ms ms' ptr len ptrs
        init_bytes bytes pr aid MEM2 INMB BYTES CONSEC BYTELEN p ix
        byte PTRNTH BYTENTH ACCESS.

      unfold read_byte_prop, read_byte_spec_MemPropT.
      repeat red.
      unfold mem_state_memory in *.
      rewrite MEM2.

      eapply get_consecutive_ptrs_nth with (ix_nat := ix) (p:=p) in CONSEC; eauto.
      destruct CONSEC as [ix_ip [IXIP_IX GEP]].
      eapply handle_gep_addr_ix in GEP.
      rewrite sizeof_dtyp_i8 in GEP.
      erewrite IP.from_Z_to_Z in GEP; eauto.

      rewrite read_byte_raw_add_all_index_in with (v:=(byte, aid)).
      unfold snd.
      rewrite ACCESS.
      cbn.
      tauto.

      - assert (Z.of_nat ix < Zlength bytes).
        {
          subst bytes.
          rewrite Zlength_map.
          eapply Nth_ix_lt_Zlength; eauto.
        }

        lia.
      - assert ((ptr_to_int p - ptr_to_int ptr) = Z.of_nat ix) as IX by lia.
        rewrite IX.
        subst bytes.
        eapply Nth_list_nth_z.
        eapply Nth_map; eauto.
        specialize (INMB (byte, provenance_to_allocation_id pr)).
        forward INMB.
        { eapply Nth_In in BYTENTH.
          eapply in_map with (f:= (fun b : SByte => (b, provenance_to_allocation_id pr))).
          eauto.
        }
        inv INMB; auto.
    Qed.

    (* TODO: Move and reuse *)
    Lemma read_byte_preserved_get_consecutive_ptrs :
      forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
        {Pre Post : Type}
        {B} `{MB : Monad B}
        `{WM : @Within M EQM B Pre Post}
        `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
        `{WRET : @Within_ret_inv M B Pre Post HM _ EQM WM}
        `{LAWS: @MonadLawsE M EQM HM}
        `{RBMOOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
        `{RBMERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}
        `{RWOOM : @RaiseWithin M B _ _ _ EQM WM string (@raise_oom M OOM)}
        `{RWERR : @RaiseWithin M B _ _ _ EQM WM string (@raise_error M ERR)}

        (ms ms' : MemState) (ptr : addr) (len : nat) (ptrs : list addr)
        (bytes : list mem_byte) (p : addr) byte,
        mem_state_memory ms' = add_all_index bytes (ptr_to_int ptr) (mem_state_memory ms)->
        (ret ptrs ∈ @get_consecutive_ptrs M HM OOM ERR ptr len)%monad ->
        (length bytes = len) ->
        (forall new_p, In new_p ptrs -> disjoint_ptr_byte new_p p) ->
        read_byte_prop ms p byte <->
          read_byte_prop ms' p byte.
    Proof using.
      intros M HM OOM ERR EQM0 Pre Post B MB WM EQV EQRET WRET LAWS RBMOOM RBMERR RWOOM RWERR
        ms ms' ptr len ptrs
        bytes p byte MEM2 CONSEC BYTELEN DISJOINT.

      unfold mem_state_memory in *.

      split; intros READ.
      - repeat red in READ; repeat red.
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

        auto.
      - repeat red in READ; repeat red.
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
        break_match; [break_match|]; auto; split; tauto.
    Qed.

    Lemma find_free_block_extend_reads :
      forall ms_init ms_found_free ms_extended pr ptr ptrs init_bytes,
        ret (ptr, ptrs) {{ms_init}} ∈ {{ms_found_free}} find_free_block (length init_bytes) pr ->
        mem_state_memory ms_extended = add_all_index (map (fun b : SByte => (b, provenance_to_allocation_id pr)) init_bytes) (ptr_to_int ptr) (mem_state_memory ms_init) ->
        extend_reads ms_init ptrs init_bytes ms_extended.
    Proof using.
      intros ms_init ms_found_free ms_extended pr ptr ptrs init_bytes [MS FREE] MEM.
      inv MS; inv FREE.
      split.
      - intros p ix byte NTHptr NTHbyte.
        eapply @read_byte_get_consecutive_ptrs with (HM:=@MemPropT_Monad MemState) (B:=err_ub_oom);
          eauto; try typeclasses eauto.

        { intros mb INMB.
          apply in_map_iff in INMB as (sb & MBEQ & INSB).
          inv MBEQ.
          cbn. reflexivity.
        }

        { rewrite map_length; auto.
        }

        { setoid_rewrite block_is_free_ptrs_provenance0; eauto.
          apply access_allowed_refl.
          eapply Nth_In; eauto.
        }

      - intros ptr' byte DISJOINT.
        eapply @read_byte_preserved_get_consecutive_ptrs
          with (HM:=@MemPropT_Monad MemState) (B:=err_ub_oom);
          eauto; try typeclasses eauto.

        rewrite map_length; eauto.
    Qed.

    (* TODO: Move and reuse *)
    Lemma read_byte_allowed_get_consecutive_ptrs :
      forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
        {Pre Post : Type}
        {B} `{MB : Monad B}
        `{WM : @Within M EQM B Pre Post}
        `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
        `{WRET : @Within_ret_inv M B Pre Post HM _ EQM WM}
        `{LAWS: @MonadLawsE M EQM HM}
        `{RBMOOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
        `{RBMERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}
        `{RWOOM : @RaiseWithin M B _ _ _ EQM WM string (@raise_oom M OOM)}
        `{RWERR : @RaiseWithin M B _ _ _ EQM WM string (@raise_error M ERR)}

        (ms ms' : MemState) (ptr : addr) (len : nat) (ptrs : list addr)
        (bytes : list mem_byte) (aid : AllocationId),
        mem_state_memory ms' = add_all_index bytes (ptr_to_int ptr) (mem_state_memory ms) ->
        (forall mb : mem_byte, In mb bytes -> snd mb = aid) ->
        (ret ptrs ∈ @get_consecutive_ptrs M HM OOM ERR ptr len)%monad ->
        (length bytes = len) ->
        forall p, In p ptrs ->
             access_allowed (address_provenance p) aid ->
             read_byte_allowed ms' p.
    Proof using.
      intros M HM OOM ERR EQM0 Pre Post B MB WM EQV EQRET WRET LAWS RBMOOM RBMERR RWOOM RWERR
        ms ms' ptr len ptrs
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
        {Pre Post : Type}
        {B} `{MB : Monad B}
        `{WM : @Within M EQM B Pre Post}
        `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
        `{WRET : @Within_ret_inv M B Pre Post HM _ EQM WM}
        `{LAWS: @MonadLawsE M EQM HM}
        `{RBMOOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
        `{RBMERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}
        `{RWOOM : @RaiseWithin M B _ _ _ EQM WM string (@raise_oom M OOM)}
        `{RWERR : @RaiseWithin M B _ _ _ EQM WM string (@raise_error M ERR)}

        (ms ms' : MemState) (ptr : addr) (len : nat) (ptrs : list addr)
        (bytes : list mem_byte) (p : addr),
        mem_state_memory ms' = add_all_index bytes (ptr_to_int ptr) (mem_state_memory ms) ->
        (ret ptrs ∈ @get_consecutive_ptrs M HM OOM ERR ptr len)%monad ->
        (length bytes = len) ->
        (forall new_p, In new_p ptrs -> disjoint_ptr_byte new_p p) ->
        read_byte_allowed ms p <->
          read_byte_allowed ms' p.
    Proof using.
      intros M HM OOM ERR EQM0 Pre Post B MB WM EQV EQRET WRET LAWS RBMOOM RBMERR RWOOM RWERR ms ms' ptr len ptrs
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
        ret (ptr, ptrs) {{ms_init}} ∈ {{ms_found_free}} find_free_block (length init_bytes) pr ->
        mem_state_memory ms_extended = add_all_index (map (fun b : SByte => (b, provenance_to_allocation_id pr)) init_bytes) (ptr_to_int ptr) (mem_state_memory ms_init) ->
        extend_read_byte_allowed ms_init ptrs ms_extended.
    Proof using.
      intros ms_init ms_found_free ms_extended pr ptr ptrs init_bytes [MS FREE] MEM.
      inv MS; inv FREE.
      split.
      - intros p IN.
        eapply @read_byte_allowed_get_consecutive_ptrs
          with (HM:=@MemPropT_Monad MemState) (B:=err_ub_oom); try typeclasses eauto.
        unfold mem_state_memory in *.
        cbn; eauto.

        intros mb INMB.
        apply in_map_iff in INMB as (sb & MBEQ & INSB).
        inv MBEQ.
        cbn. reflexivity.

        exists ms_found_free.
        exists ms_found_free.
        eauto.

        rewrite map_length; reflexivity.
        eauto.

        setoid_rewrite block_is_free_ptrs_provenance0; eauto.
        apply access_allowed_refl.
      - intros ptr' DISJOINT.
        eapply @read_byte_allowed_preserved_get_consecutive_ptrs
          with (HM:=@MemPropT_Monad MemState) (B:=err_ub_oom); try typeclasses eauto.
        unfold mem_state_memory in *.
        cbn; eauto.

        eauto.

        rewrite map_length; reflexivity.
        eauto.
    Qed.

    (* TODO: Move and reuse *)
    Lemma write_byte_allowed_get_consecutive_ptrs :
      forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
        {Pre Post : Type}
        {B} `{MB : Monad B}
        `{WM : @Within M EQM B Pre Post}
        `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
        `{WRET : @Within_ret_inv M B Pre Post HM _ EQM WM}
        `{LAWS: @MonadLawsE M EQM HM}
        `{RBMOOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
        `{RBMERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}
        `{RWOOM : @RaiseWithin M B _ _ _ EQM WM string (@raise_oom M OOM)}
        `{RWERR : @RaiseWithin M B _ _ _ EQM WM string (@raise_error M ERR)}

        (ms ms' : MemState) (ptr : addr) (len : nat) (ptrs : list addr)
        (bytes : list mem_byte) (aid : AllocationId),
        mem_state_memory ms' = add_all_index bytes (ptr_to_int ptr) (mem_state_memory ms) ->
        (forall mb : mem_byte, In mb bytes -> snd mb = aid) ->
        (ret ptrs ∈ @get_consecutive_ptrs M HM OOM ERR ptr len)%monad ->
        (length bytes = len) ->
        forall p, In p ptrs ->
             access_allowed (address_provenance p) aid ->
             write_byte_allowed ms' p.
    Proof using.
      intros M HM OOM ERR EQM0 Pre Post B MB WM EQV EQRET WRET LAWS RBMOOM RBMERR RWOOM RWERR ms ms' ptr len ptrs
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
        {Pre Post : Type}
        {B} `{MB : Monad B}
        `{WM : @Within M EQM B Pre Post}
        `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
        `{WRET : @Within_ret_inv M B Pre Post HM _ EQM WM}
        `{LAWS: @MonadLawsE M EQM HM}
        `{RBMOOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
        `{RBMERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}
        `{RWOOM : @RaiseWithin M B _ _ _ EQM WM string (@raise_oom M OOM)}
        `{RWERR : @RaiseWithin M B _ _ _ EQM WM string (@raise_error M ERR)}

        (ms ms' : MemState) (ptr : addr) (len : nat) (ptrs : list addr)
        (bytes : list mem_byte) (p : addr),
        mem_state_memory ms' = add_all_index bytes (ptr_to_int ptr) (mem_state_memory ms) ->
        (ret ptrs ∈ @get_consecutive_ptrs M HM OOM ERR ptr len)%monad ->
        (length bytes = len) ->
        (forall new_p, In new_p ptrs -> disjoint_ptr_byte new_p p) ->
        write_byte_allowed ms p <->
          write_byte_allowed ms' p.
    Proof using.
      intros M HM OOM ERR EQM0 Pre Post B MB WM EQV EQRET WRET LAWS RBMOOM RBMERR RWOOM RWERR ms ms' ptr len ptrs
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
        ret (ptr, ptrs) {{ms_init}} ∈ {{ms_found_free}} find_free_block (length init_bytes) pr ->
        mem_state_memory ms_extended = add_all_index (map (fun b : SByte => (b, provenance_to_allocation_id pr)) init_bytes) (ptr_to_int ptr) (mem_state_memory ms_init) ->
        extend_write_byte_allowed ms_init ptrs ms_extended.
    Proof using.
      intros ms_init ms_found_free ms_extended pr ptr ptrs init_bytes [MS FREE] MEM.
      inv MS; inv FREE.
      split.
      - intros p IN.
        eapply @write_byte_allowed_get_consecutive_ptrs
          with (HM:=@MemPropT_Monad MemState) (B:=err_ub_oom); try typeclasses eauto.
        unfold mem_state_memory in *.
        cbn; eauto.

        intros mb INMB.
        apply in_map_iff in INMB as (sb & MBEQ & INSB).
        inv MBEQ.
        cbn. reflexivity.

        eauto.

        rewrite map_length; reflexivity.
        eauto.

        setoid_rewrite block_is_free_ptrs_provenance0; eauto.
        apply access_allowed_refl.
      - intros ptr' DISJOINT.
        eapply @write_byte_allowed_preserved_get_consecutive_ptrs
          with (HM:=@MemPropT_Monad MemState) (B:=err_ub_oom); try typeclasses eauto.

        unfold mem_state_memory in *.
        cbn; eauto.

        eauto.

        rewrite map_length; reflexivity.
        eauto.
    Qed.

    (* TODO: Move and reuse *)
    Lemma free_byte_allowed_get_consecutive_ptrs :
      forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
        {Pre Post : Type}
        {B} `{MB : Monad B}
        `{WM : @Within M EQM B Pre Post}
        `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
        `{WRET : @Within_ret_inv M B Pre Post HM _ EQM WM}
        `{LAWS: @MonadLawsE M EQM HM}
        `{RBMOOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
        `{RBMERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}
        `{RWOOM : @RaiseWithin M B _ _ _ EQM WM string (@raise_oom M OOM)}
        `{RWERR : @RaiseWithin M B _ _ _ EQM WM string (@raise_error M ERR)}

        (ms ms' : MemState) (ptr : addr) (len : nat) (ptrs : list addr)
        (bytes : list mem_byte) (aid : AllocationId),
        mem_state_memory ms' = add_all_index bytes (ptr_to_int ptr) (mem_state_memory ms) ->
        (forall mb : mem_byte, In mb bytes -> snd mb = aid) ->
        (ret ptrs ∈ @get_consecutive_ptrs M HM OOM ERR ptr len)%monad ->
        (length bytes = len) ->
        forall p, In p ptrs ->
             access_allowed (address_provenance p) aid ->
             free_byte_allowed ms' p.
    Proof using.
      intros M HM OOM ERR EQM0 Pre Post B MB WM EQV EQRET WRET LAWS RBMOOM RBMERR RWOOM RWERR ms ms' ptr len ptrs
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
        {Pre Post : Type}
        {B} `{MB : Monad B}
        `{WM : @Within M EQM B Pre Post}
        `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
        `{WRET : @Within_ret_inv M B Pre Post HM _ EQM WM}
        `{LAWS: @MonadLawsE M EQM HM}
        `{RBMOOM : @RaiseBindM M HM EQM string (@raise_oom M OOM)}
        `{RBMERR : @RaiseBindM M HM EQM string (@raise_error M ERR)}
        `{RWOOM : @RaiseWithin M B _ _ _ EQM WM string (@raise_oom M OOM)}
        `{RWERR : @RaiseWithin M B _ _ _ EQM WM string (@raise_error M ERR)}

        (ms ms' : MemState) (ptr : addr) (len : nat) (ptrs : list addr)
        (bytes : list mem_byte) (p : addr),
        mem_state_memory ms' = add_all_index bytes (ptr_to_int ptr) (mem_state_memory ms) ->
        (ret ptrs ∈ @get_consecutive_ptrs M HM OOM ERR ptr len)%monad ->
        (length bytes = len) ->
        (forall new_p, In new_p ptrs -> disjoint_ptr_byte new_p p) ->
        read_byte_allowed ms p <->
          read_byte_allowed ms' p.
    Proof using.
      intros M HM OOM ERR EQM0 Pre Post B MB WM EQV EQRET WRET LAWS RBMOOM RBMERR RWOOM RWERR ms ms' ptr len ptrs
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
        ret (ptr, ptrs) {{ms_init}} ∈ {{ms_found_free}} find_free_block (length init_bytes) pr ->
        mem_state_memory ms_extended = add_all_index (map (fun b : SByte => (b, provenance_to_allocation_id pr)) init_bytes) (ptr_to_int ptr) (mem_state_memory ms_init) ->
        extend_free_byte_allowed ms_init ptrs ms_extended.
    Proof using.
      intros ms_init ms_found_free ms_extended pr ptr ptrs init_bytes [MS FREE] MEM.
      inv MS; inv FREE.
      split.
      - intros p IN.
        eapply @free_byte_allowed_get_consecutive_ptrs
          with (HM:=@MemPropT_Monad MemState) (B:=err_ub_oom); try typeclasses eauto.
        unfold mem_state_memory in *.
        cbn; eauto.

        intros mb INMB.
        apply in_map_iff in INMB as (sb & MBEQ & INSB).
        inv MBEQ.
        cbn. reflexivity.

        eauto.

        rewrite map_length; reflexivity.
        eauto.

        setoid_rewrite block_is_free_ptrs_provenance0; eauto.
        apply access_allowed_refl.
      - intros ptr' DISJOINT.
        eapply @free_byte_allowed_preserved_get_consecutive_ptrs
          with (HM:=@MemPropT_Monad MemState) (B:=err_ub_oom); try typeclasses eauto.
        unfold mem_state_memory in *.
        cbn; eauto.

        eauto.

        rewrite map_length; reflexivity.
        eauto.
    Qed.

    (* TODO: solve_allocate_bytes_post_conditions *)
    (* TODO: move, generalize *)
    Lemma find_free_allocate_bytes_post_conditions :
      forall (ms_init ms_found_free ms_final : MemState) init_bytes pr ptr ptrs
        memory_stack_memory0 memory_stack_frame_stack0 memory_stack_heap0 ms_provenance0
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
                       |} ptrs;
                   ms_provenance := ms_provenance0
                 |})
        (FIND_FREE : ret (ptr, ptrs) {{ms_init}} ∈ {{ms_found_free}} find_free_block (length init_bytes) pr),
        allocate_bytes_post_conditions ms_found_free init_bytes pr ms_final ptr ptrs.
    Proof using.
      intros ms_init ms_found_free ms_final init_bytes pr ptr ptrs memory_stack_memory0
        memory_stack_frame_stack0 memory_stack_heap0 ms_provenance0 EQ EQF FIND_FREE.
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
    Qed.

    (* TODO: move *)
    Lemma find_free_allocate_bytes_post_conditions_exists :
      forall (ms_init ms_found_free : MemState) init_bytes pr ptr ptrs
        (FIND_FREE : ret (ptr, ptrs) {{ms_init}} ∈ {{ms_found_free}} find_free_block (length init_bytes) pr),
      exists ms_final,
        allocate_bytes_post_conditions ms_found_free init_bytes pr ms_final ptr ptrs.
    Proof using.
      intros ms_init ms_found_free init_bytes pr ptr ptrs FIND_FREE.
      destruct ms_found_free.
      destruct ms_memory_stack0.
      eexists.
      eapply find_free_allocate_bytes_post_conditions; eauto.
    Qed.

    Lemma add_to_frame_valid_state :
      forall ms a mprov st,
        MemMonad_valid_state {| ms_memory_stack := ms; ms_provenance := mprov |} st <->
        MemMonad_valid_state {| ms_memory_stack := add_to_frame ms a; ms_provenance := mprov |} st.
    Proof.
      split.
      { revert ms a mprov st.
        intros ms a mprov st VALID.
        destruct ms.
        cbn.
        break_match_goal.
        - repeat red.
          repeat red in VALID.
          intros sid' H0.
          eapply VALID.
          red in H0.
          destruct H0 as (?&?&?&?).
          repeat red in H0.
          cbn in *.
          repeat red.
          eauto.
        - repeat red.
          repeat red in VALID.
          intros sid' H0.
          eapply VALID.
          red in H0.
          destruct H0 as (?&?&?&?).
          repeat red in H0.
          cbn in *.
          repeat red.
          eauto.
      }
      { revert ms a mprov st.
        intros ms a mprov st VALID.
        destruct ms.
        cbn in *.
        break_match_hyp.
        - repeat red.
          repeat red in VALID.
          intros sid' H0.
          eapply VALID.
          red in H0.
          destruct H0 as (?&?&?&?).
          repeat red in H0.
          cbn in *.
          repeat red.
          eauto.
        - repeat red.
          repeat red in VALID.
          intros sid' H0.
          eapply VALID.
          red in H0.
          destruct H0 as (?&?&?&?).
          repeat red in H0.
          cbn in *.
          repeat red.
          eauto.
      }
    Qed.

    Lemma add_all_to_frame_valid_state :
      forall ptrs ms st mprov,
        MemMonad_valid_state
          {|
            ms_memory_stack := ms;
            ms_provenance := mprov
          |} st <->
        MemMonad_valid_state
          {|
            ms_memory_stack :=
              add_all_to_frame ms ptrs;
            ms_provenance := mprov
          |} st.
    Proof.
      split.
      { revert ptrs ms st mprov.
        induction ptrs; intros ms st mprov VALID.
        - cbn; auto.
        - remember (add_all_to_frame ms (a :: ptrs)).
          symmetry in Heqm.
          apply add_all_to_frame_cons_inv in Heqm.
          destruct Heqm as (?&?&?).
          subst.
          eapply IHptrs.
          apply -> add_to_frame_valid_state; auto.
      }

      { revert ptrs ms st mprov.
        induction ptrs; intros ms st mprov VALID.
        - cbn; auto.
        - remember (add_all_to_frame ms (a :: ptrs)).
          symmetry in Heqm.
          apply add_all_to_frame_cons_inv in Heqm.
          destruct Heqm as (?&?&?).
          subst.
          eapply IHptrs in VALID.
          eapply add_to_frame_valid_state in VALID; auto.
      }
    Qed.

    Lemma add_valid_state :
      forall ms fs h mprov st addr byte aid sid,
        sbyte_sid byte = inr sid ->
        (sid < st)%N ->
        MemMonad_valid_state
          {|
            ms_memory_stack :=
              {|
                memory_stack_memory := ms;
                memory_stack_frame_stack := fs;
                memory_stack_heap := h
              |};
            ms_provenance := mprov
          |} st ->
        MemMonad_valid_state
          {|
            ms_memory_stack :=
              {|
                memory_stack_memory :=
                  add addr (byte, aid) ms;
                memory_stack_frame_stack := fs;
                memory_stack_heap := h
              |};
            ms_provenance := mprov
          |} st.
    Proof.
      intros ms fs h mprov st addr0 byte aid sid SID LT VALID.
      repeat red.
      repeat red in VALID.
      intros sid' USED.
      repeat red in USED.
      destruct USED as (?&?&?&?).
      repeat red in H0.
      cbn in *.
      pose proof (Z.eq_dec (ptr_to_int x) addr0) as [EQ | NEQ].
      - replace (add addr0 (byte, aid) ms) with (set_byte_raw ms addr0 (byte, aid)) in H0.
        2: reflexivity.
        rewrite set_byte_raw_eq in H0; auto.
        break_match_hyp_inv.
        cbn in *.
        rewrite SID in H1; inv H1.
        apply N.compare_lt_iff; auto.
      - replace (add addr0 (byte, aid) ms) with (set_byte_raw ms addr0 (byte, aid)) in H0.
        2: reflexivity.
        rewrite set_byte_raw_neq in H0; auto.
        eapply VALID.
        repeat red.
        eauto.
    Qed.

    Lemma add_all_index_valid_state :
      forall ms fs h mprov st addr init_bytes aid,
        (Forall (fun (b : SByte) => exists (s : store_id), sbyte_sid b = inr s /\ (s < st)%N) init_bytes) ->
        MemMonad_valid_state
          {|
            ms_memory_stack :=
              {|
                memory_stack_memory := ms;
                memory_stack_frame_stack := fs;
                memory_stack_heap := h
              |};
            ms_provenance := mprov
          |} st ->
        MemMonad_valid_state
          {|
            ms_memory_stack :=
              {|
                memory_stack_memory :=
                  add_all_index (map (fun b : SByte => (b, aid)) init_bytes)
                    addr ms;
                memory_stack_frame_stack := fs;
                memory_stack_heap := h
              |};
            ms_provenance := mprov
          |} st.
    Proof.
      intros ms fs h mprov st addr0 init_bytes aid ALL VALID.
      revert addr0.
      induction ALL; intros p.
      - cbn; auto.
      - cbn.
        destruct H0 as (?&?&?).
        specialize (IHALL (p+1)%Z).
        eapply add_valid_state; eauto.
    Qed.

    Lemma add_to_heap_valid_state :
      forall ms mprov st root a,
        MemMonad_valid_state {| ms_memory_stack := ms; ms_provenance := mprov |} st <->
        MemMonad_valid_state {| ms_memory_stack := add_to_heap ms root a; ms_provenance := mprov |} st.
    Proof.
      split; intros VALID.
      { destruct ms.
        cbn in *.
        repeat red.
        repeat red in VALID.
        intros ? ?.
        repeat red in H0.
        destruct H0 as (?&?&?&?).
        repeat red in H0.
        cbn in *.
        eapply VALID.
        repeat red.
        eauto.        
      }
      { destruct ms.
        cbn in *.
        repeat red.
        repeat red in VALID.
        intros ? ?.
        repeat red in H0.
        destruct H0 as (?&?&?&?).
        repeat red in H0.
        cbn in *.
        eapply VALID.
        repeat red.
        eauto.        
      }
    Qed.

    Lemma add_all_to_heap'_valid_state :
      forall ptrs root ms st mprov,
        MemMonad_valid_state
          {|
            ms_memory_stack := ms;
            ms_provenance := mprov
          |} st <->
        MemMonad_valid_state
          {|
            ms_memory_stack :=
              add_all_to_heap' ms root ptrs;
            ms_provenance := mprov
          |} st.
    Proof.
      split.
      { revert ptrs root ms st mprov.
        induction ptrs; intros root ms st mprov VALID.
        - cbn; auto.
        - remember (add_all_to_heap' ms root (a :: ptrs)).
          symmetry in Heqm.
          apply add_all_to_heap'_cons_inv in Heqm.
          destruct Heqm as (?&?&?).
          subst.
          eapply IHptrs.
          apply -> add_to_heap_valid_state; auto.
      }

      { revert ptrs ms st mprov.
        induction ptrs; intros ms st mprov VALID.
        - cbn; auto.
        - remember (add_all_to_heap' ms root (a :: ptrs)).
          symmetry in Heqm.
          apply add_all_to_heap'_cons_inv in Heqm.
          destruct Heqm as (?&?&?).
          subst.
          eapply IHptrs in VALID.
          eapply add_to_heap_valid_state in VALID; auto.
      }
    Qed.

    Lemma add_all_to_heap_valid_state :
      forall ptrs ms st mprov,
        MemMonad_valid_state
          {|
            ms_memory_stack := ms;
            ms_provenance := mprov
          |} st <->
        MemMonad_valid_state
          {|
            ms_memory_stack :=
              add_all_to_heap ms ptrs;
            ms_provenance := mprov
          |} st.
    Proof.
      split.
      { revert ptrs ms st mprov.
        induction ptrs; intros ms st mprov VALID.
        - cbn; auto.
        - Transparent add_all_to_heap.
          apply -> add_all_to_heap'_valid_state; auto.
          Opaque add_all_to_heap.
      }
      { revert ptrs ms st mprov.
        induction ptrs; intros ms st mprov VALID.
        - cbn; auto.
        - Transparent add_all_to_heap.
          apply <- add_all_to_heap'_valid_state; auto.
          apply VALID.
          Opaque add_all_to_heap.
      }
    Qed.

    (* TODO: Pull out lemmas and clean up + fix admits *)
    Lemma add_block_to_stack_correct :
      forall pr ms_init ptr ptrs init_bytes,
        exec_correct
          (fun ms_k st =>
             (Forall (fun (b : SByte) => exists (s : store_id), sbyte_sid b = inr s /\ (s < st)%N) init_bytes) /\
               (ret (ptr, ptrs) {{ms_init}} ∈ {{ms_k}} find_free_block (Datatypes.length init_bytes) pr))
          (_ <- add_block_to_stack (provenance_to_allocation_id pr) ptr ptrs init_bytes;; ret ptr)
          (_ <- allocate_bytes_post_conditions_MemPropT init_bytes pr ptr ptrs;; ret ptr)
          exec_correct_id_post.
    Proof using.
      intros pr ms_init ptr ptrs init_bytes.
      unfold exec_correct.
      intros ms st VALID PRE.

      right.
      unfold add_block_to_stack, add_block, add_ptrs_to_frame.

      destruct ms.
      destruct ms_memory_stack0.

      exists (ret ptr).
      eexists.
      eexists.
      split.
      { exists (ret ptr).
        cbn.
        split; [reflexivity|].
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
        cbn.
        reflexivity.
      }

      split.
      - eexists. exists (ptr, ptrs).
        destruct PRE as (PRE1&PRE2).
        split; auto.
        2: split; eauto.
        split; auto.
        (* TODO: solve_allocate_bytes_post_conditions *)
        eapply find_free_allocate_bytes_post_conditions; eauto.
      - destruct PRE as (PRE1&PRE2).
        intros (?&?).
        inv H0.
        rename x into ptr.

        clear PRE2.
        split; eauto.
        apply add_all_to_frame_valid_state.
        apply add_all_index_valid_state; auto.
    Qed.

    (* TODO: move *)
    Lemma find_free_malloc_bytes_post_conditions :
      forall (ms_init ms_found_free ms_final : MemState) init_bytes pr ptr ptrs
        memory_stack_memory0 memory_stack_frame_stack0 memory_stack_heap0 ms_provenance0
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
                     add_all_to_heap
                       {|
                         memory_stack_memory :=
                           add_all_index (map (fun b : SByte => (b, provenance_to_allocation_id pr)) init_bytes)
                             (ptr_to_int ptr) memory_stack_memory0;
                         memory_stack_frame_stack := memory_stack_frame_stack0;
                         memory_stack_heap := memory_stack_heap0
                       |} ptrs;
                   ms_provenance := ms_provenance0
                 |})
        (FIND_FREE : ret (ptr, ptrs) {{ms_init}} ∈ {{ms_found_free}} find_free_block (length init_bytes) pr),
        malloc_bytes_post_conditions ms_found_free init_bytes pr ms_final ptr ptrs.
    Proof using.
      intros ms_init ms_found_free ms_final init_bytes pr ptr ptrs memory_stack_memory0
        memory_stack_frame_stack0 memory_stack_heap0 ms_provenance0 EQ EQF FIND_FREE.
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
      + (* extend_free_byte_allowed *)
        pose proof FIND_FREE as PRE.
        eapply find_free_block_ms_eq in PRE; subst.
        eapply find_free_block_extend_free_byte_allowed; [solve [eauto] | solve_mem_state_memory].
      + (* frame_stack_preserved *)
        (* TODO: make part of solve_frame_stack_preserved *)
        red.
        intros fs.
        cbn.
        unfold memory_stack_frame_stack_prop.
        setoid_rewrite add_all_to_heap_preserves_frame_stack.
        reflexivity.
      + (* extend_heap_frame *)
        (* TODO: Tactic or lemma? *)
        unfold extend_heap.
        intros h1 h2 MSHP PTRS_ADDED.
        unfold memory_stack_frame_stack_prop in *.
        cbn in *.

        destruct FIND_FREE as [FIND_FREE BLOCK_IS_FREE].
        inv BLOCK_IS_FREE.

        setoid_rewrite <- MSHP in PTRS_ADDED.
        apply add_ptrs_to_heap_eqv with (root:=ptr) (h:=memory_stack_heap0) (ptrs:=ptrs); auto.
        {
          assert (memory_stack_heap0 = memory_stack_heap {|
                                           memory_stack_memory :=
                                             add_all_index (map (fun b : SByte => (b, provenance_to_allocation_id pr)) init_bytes)
                                               (ptr_to_int ptr) memory_stack_memory0;
                                           memory_stack_frame_stack := memory_stack_frame_stack0;
                                           memory_stack_heap := memory_stack_heap0
                                         |}) as EQFS by reflexivity.
          rewrite EQFS at 1.

          destruct ptrs as [|p ptrs].
          { (* Length of get_consecutive_ptrs was 0 *)
            eapply add_all_to_heap'_correct; eauto.
          }

          { (* Actually got consecutive pointers *)
            assert (p = ptr).
            { eapply @get_consecutive_ptrs_cons with (M:=MemPropT MemState) (B:=err_ub_oom);
                eauto; typeclasses eauto.
            }

            subst.
            eapply add_all_to_heap'_correct; eauto.
          }
        }

        unfold MemSpec.add_ptrs_to_heap in PTRS_ADDED.
        destruct ptrs as [|p ptrs]; auto.
        assert (p = ptr).
        { eapply @get_consecutive_ptrs_cons with (M:=MemPropT MemState) (B:=err_ub_oom);
            eauto; typeclasses eauto.
        }
        subst; cbn in *; auto.
    Qed.


    (* TODO: Pull out lemmas and clean up + fix admits *)
    Lemma add_block_to_heap_correct :
      forall pr ms_init ptr ptrs init_bytes,
        exec_correct
          (fun ms_k st =>
             (Forall (fun (b : SByte) => exists (s : store_id), sbyte_sid b = inr s /\ (s < st)%N) init_bytes) /\
               (ret (ptr, ptrs) {{ms_init}} ∈ {{ms_k}} find_free_block (Datatypes.length init_bytes) pr))
          (_ <- add_block_to_heap (provenance_to_allocation_id pr) ptr ptrs init_bytes;; ret ptr)
          (_ <- malloc_bytes_post_conditions_MemPropT init_bytes pr ptr ptrs;; ret ptr)
          exec_correct_id_post.
    Proof using.
      intros pr ms_init ptr ptrs init_bytes.
      unfold exec_correct.
      intros ms st VALID PRE.

      (* No UB because type allocated isn't void *)
      right.
      unfold add_block_to_heap, add_block, add_ptrs_to_heap.

      destruct ms.
      destruct ms_memory_stack0.

      exists (ret ptr).
      eexists.
      eexists.

      split.
      { exists (ret ptr).
        cbn.
        split; [reflexivity|].
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
        cbn.
        reflexivity.
      }

      split.
      - eexists. exists (ptr, ptrs).
        destruct PRE as (PRE1&PRE2).
        split; auto.
        2: split; eauto.
        split; auto.
        eapply find_free_malloc_bytes_post_conditions; eauto.
      - intros (?&?).
        destruct PRE as (PRE&PRE2).
        inv H0.
        rename x into ptr.
        split; eauto.
        apply add_all_to_heap_valid_state; eauto.
        apply add_all_index_valid_state; auto.
    Qed.

    Lemma allocate_bytes_with_pr_correct :
      forall init_bytes pr,
        exec_correct
          (fun ms st =>
             Forall (fun b : SByte => exists s : store_id, sbyte_sid b = inr s /\ (s < st)%N) init_bytes)
          (allocate_bytes_with_pr init_bytes pr) (allocate_bytes_with_pr_spec_MemPropT init_bytes pr)
          exec_correct_id_post.
    Proof using.
      Opaque exec_correct.
      intros init_bytes pr.

      unfold allocate_bytes_with_pr, allocate_bytes_with_pr_spec_MemPropT.
      eapply exec_correct_strengthen_post; cycle 1.
      { apply exec_correct_bind with (post_b:=fun _ => exec_correct_id_post); eauto with EXEC_CORRECT.
        intros [ptr ptrs] ms' ms_find_free st'' st_find_free VALID POST GET_FREE.
        eapply exec_correct_weaken_pre; auto.
        2: {
          eapply exec_correct_strengthen_post; cycle 1.
          apply add_block_to_stack_correct; auto.
          auto.
        }

        cbn.
        intros ms st H0.
        destruct H0 as (?&?&?&?); subst.
        split; eauto.
        repeat red in H1.
        destruct H1 as (?&?&?).
        cbn in *.
        unfold get_free_block in H2.
        rewrite MemMonad_run_bind in H2.
        rewrite MemMonad_get_mem_state in H2.
        rewrite bind_ret_l in H2.
        destruct ms; cbn in *.
        destruct ms_memory_stack0; cbn in *.
        rewrite MemMonad_run_bind in H2.
        rewrite H1 in H2.
        destruct (int_to_ptr
                    (next_memory_key
                       {|
                         memory_stack_memory := memory_stack_memory0;
                         memory_stack_frame_stack := memory_stack_frame_stack0;
                         memory_stack_heap := memory_stack_heap0
                       |}) (allocation_id_to_prov (provenance_to_allocation_id pr))) eqn:ITP;
          cbn in *.
        - rewrite MemMonad_run_ret in H2.
          rewrite bind_ret_l in H2.
          rewrite MemMonad_run_bind in H2.
          rewrite MemMonad_run_get_consecutive_ptrs in H2.
          rewrite bind_ret_l in H2.
          pose proof get_consecutive_ptrs_inv a (Datatypes.length init_bytes)
            as [[msg OOM] | [ptrs' GCP]].
          + rewrite OOM in H2.
            cbn in H2.
            unfold liftM in *.
            do 2 rewrite rbm_raise_bind in H2; try typeclasses eauto.
            symmetry in H2.
            apply MemMonad_eq1_raise_oom_inv in H2; contradiction.
          + rewrite GCP in H2.
            cbn in H2.
            unfold liftM in H2.
            repeat rewrite bind_ret_l in H2.
            rewrite MemMonad_run_ret in H2.
            cbn in H2.
            eapply eq1_ret_ret in H2; try typeclasses eauto.
            inv H2.
            auto.
        - rewrite MemMonad_run_raise_oom in H2.
          rewrite rbm_raise_bind in H2; try typeclasses eauto.
          rewrite bind_ret_l in H2.
          symmetry in H2.
          apply MemMonad_eq1_raise_oom_inv in H2; contradiction.
      }
      auto.
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
    Proof using.
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
    Proof using.
      intros M HM OOM ERR EQM' EQV EQRET LAWS
             RAISE_OOM RAISE_ERR
             ms mem bytes byte offset aid p ptr ptrs
             MEM BYTE CONSEC PTR ACCESS_ALLOWED.

      unfold read_byte_prop, read_byte_spec_MemPropT.
      cbn.
      repeat red.
      unfold mem_state_memory in *.
      rewrite MEM.
      erewrite read_byte_raw_add_all_index_in with (v := (byte, aid)).
      { cbn.
        rewrite ACCESS_ALLOWED.
        auto.
      }

      { eapply get_consecutive_ptrs_range_eq1 with (p:=p) in CONSEC.
        rewrite Zlength_correct.
        lia.
        eapply Nth_In; eauto.
      }

      { eapply get_consecutive_ptrs_nth_eq1 in CONSEC; eauto.
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
    Proof using.
      intros ms mem bytes ix aid MEM AID p IN_BOUNDS ACCESS_ALLOWED.
      unfold read_byte_allowed.
      exists aid. split; auto.
      eapply byte_allocated_add_all_index; eauto.
    Qed.

    (** Malloc correctness *)
    Lemma malloc_bytes_with_pr_correct :
      forall init_bytes pr,
        exec_correct
          (fun ms st =>
             Forall (fun b : SByte => exists s : store_id, sbyte_sid b = inr s /\ (s < st)%N) init_bytes)
          (malloc_bytes_with_pr init_bytes pr) (malloc_bytes_with_pr_spec_MemPropT init_bytes pr)
          exec_correct_id_post.
    Proof using.
      intros init_bytes pr.

      unfold malloc_bytes_with_pr.
      eapply exec_correct_strengthen_post; cycle 1.
      { apply exec_correct_bind with (post_b:=fun _ => exec_correct_id_post); eauto with EXEC_CORRECT.
        intros [ptr ptrs] ms' ms_find_free st'' st_find_free VALID POST GET_FREE.

        eapply exec_correct_weaken_pre; auto.
        2: apply add_block_to_heap_correct.

        cbn.
        intros ms st H0.
        destruct H0 as (?&?&?&?); subst.
        split; eauto.
        repeat red in H1.
        destruct H1 as (?&?&?).
        cbn in *.
        unfold get_free_block in H2.
        rewrite MemMonad_run_bind in H2.
        rewrite MemMonad_get_mem_state in H2.
        rewrite bind_ret_l in H2.
        destruct ms; cbn in *.
        destruct ms_memory_stack0; cbn in *.
        rewrite MemMonad_run_bind in H2.
        rewrite H1 in H2.
        destruct (int_to_ptr
                    (next_memory_key
                       {|
                         memory_stack_memory := memory_stack_memory0;
                         memory_stack_frame_stack := memory_stack_frame_stack0;
                         memory_stack_heap := memory_stack_heap0
                       |}) (allocation_id_to_prov (provenance_to_allocation_id pr))) eqn:ITP;
          cbn in *.
        - rewrite MemMonad_run_ret in H2.
          rewrite bind_ret_l in H2.
          rewrite MemMonad_run_bind in H2.
          rewrite MemMonad_run_get_consecutive_ptrs in H2.
          rewrite bind_ret_l in H2.
          pose proof get_consecutive_ptrs_inv a (Datatypes.length init_bytes)
            as [[msg OOM] | [ptrs' GCP]].
          + rewrite OOM in H2.
            cbn in H2.
            unfold liftM in *.
            do 2 rewrite rbm_raise_bind in H2; try typeclasses eauto.
            symmetry in H2.
            apply MemMonad_eq1_raise_oom_inv in H2; contradiction.
          + rewrite GCP in H2.
            cbn in H2.
            unfold liftM in H2.
            repeat rewrite bind_ret_l in H2.
            rewrite MemMonad_run_ret in H2.
            cbn in H2.
            eapply eq1_ret_ret in H2; try typeclasses eauto.
            inv H2.
            auto.
        - rewrite MemMonad_run_raise_oom in H2.
          rewrite rbm_raise_bind in H2; try typeclasses eauto.
          rewrite bind_ret_l in H2.
          symmetry in H2.
          apply MemMonad_eq1_raise_oom_inv in H2; contradiction.
      }
      auto.
    Qed.

    (** Correctness of frame stack operations *)
    Lemma mempush_correct :
      forall pre, exec_correct pre mempush mempush_spec_MemPropT exec_correct_id_post.
    Proof using.
      Transparent exec_correct.
      unfold exec_correct.
      intros pre ms st VALID PRE.
      cbn.

      right.
      exists (ret tt).
      do 2 eexists.
      split.
      { red.
        exists (ret tt).
        split; cbn; [reflexivity|].
        rewrite bind_ret_l.
        unfold mempush.
        rewrite MemMonad_run_bind.
        rewrite MemMonad_get_mem_state.
        rewrite bind_ret_l.
        rewrite MemMonad_put_mem_state.
        reflexivity.
      }

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
              red.
              reflexivity.
        + (* MemMonad_valid_state *)
          intros _.
          split.
          { (* TODO: pull this out into lemma *)
            red.
            intros sid' USED.
            eapply VALID.
            destruct ms as [[mem fs heap] pr'] eqn:Hms.
            auto.
          }

          exists tt; split; eauto.
    Qed.

    (* TODO: move *)
    Lemma read_byte_raw_memory_empty :
      forall ptr,
        read_byte_raw memory_empty ptr = None.
    Proof using.
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
    Proof using.
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
          free_byte (ptr_to_int a) m  = m'' /\
            free_frame_memory f m'' = m'.
    Proof using.
      intros f m m' a FREE.
      rewrite list_cons_app in FREE.
      unfold free_frame_memory in *.
      rewrite fold_left_app in FREE.
      set (m'' := fold_left (fun (m : memory) (key : addr) => free_byte (ptr_to_int key) m) [a] m).
      exists m''.
      subst m''.
      cbn; split; auto.
    Qed.

    Lemma free_block_memory_cons :
      forall block m m' a,
        free_block_memory (a :: block) m = m' ->
        exists m'',
          free_byte (ptr_to_int a) m  = m'' /\
            free_block_memory block m'' = m'.
    Proof using.
      intros f m m' a FREE.
      rewrite list_cons_app in FREE.
      unfold free_block_memory in *.
      rewrite fold_left_app in FREE.
      set (m'' := fold_left (fun (m : memory) (key : addr) => free_byte (ptr_to_int key) m) [a] m).
      exists m''.
      subst m''.
      cbn; split; auto.
    Qed.

    Lemma free_byte_no_add :
      forall m m' ptr ptr',
        read_byte_raw m ptr = None ->
        free_byte ptr' m = m' ->
        read_byte_raw m' ptr = None.
    Proof using.
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
    Proof using.
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
    Proof using.
      apply free_frame_memory_no_add.
    Qed.

    Lemma free_frame_memory_read_byte_raw :
      forall (f : Frame) (m m' : memory) ptr,
        free_frame_memory f m = m' ->
        ptr_in_frame_prop f ptr ->
        read_byte_raw m' (ptr_to_int ptr) = None.
    Proof using.
      induction f;
        intros m m' ptr FREE IN.

      - inv IN.
      - apply free_frame_memory_cons in FREE.
        destruct FREE as [m'' [FREEBYTE FREE]].

        destruct IN as [IN | IN].
        + rewrite <- IN.
          eapply free_frame_memory_no_add; eauto.
          eapply free_byte_read_byte_raw; eauto.
        + eapply IHf; eauto.
    Qed.

    Lemma free_block_memory_read_byte_raw :
      forall (block : Block) (m m' : memory) ptr,
        free_block_memory block m = m' ->
        In (ptr_to_int ptr) (map ptr_to_int block) ->
        read_byte_raw m' (ptr_to_int ptr) = None.
    Proof using.
      induction block;
        intros m m' ptr FREE IN.

      - inv IN.
      - apply free_block_memory_cons in FREE.
        destruct FREE as [m'' [FREEBYTE FREE]].

        destruct IN as [IN | IN].
        + rewrite <- IN.
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
    Proof using.
      intros ms ms' m m' ptr FREE MS MS'.
      intros aid CONTRA.
      repeat red in CONTRA.
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
    Proof using.
      intros ms ms' m m' f ptr FREE IN MS MS'.
      intros aid CONTRA.
      repeat red in CONTRA.
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
        In (ptr_to_int ptr) (map ptr_to_int block) ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        byte_not_allocated ms' ptr.
    Proof using.
      intros ms ms' m m' block ptr FREE IN MS MS'.
      intros aid CONTRA.
      repeat red in CONTRA.
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
    Proof using.
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
    Proof using.
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
    Proof using.
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
    Proof using.
      intros ms ms' m m' ptr ptr' aid FREE MS MS' DISJOINT.
      split; intro ALLOC.
      - destruct ms as [[ms fs] pr].
        repeat red in ALLOC.
        cbn in ALLOC.
        repeat red.
        unfold mem_state_memory in *.
        rewrite MS'.

        erewrite free_byte_disjoint; eauto.
        cbn in *; subst; auto.
      - destruct ms as [[ms fs] pr].
        repeat red in ALLOC.
        cbn in ALLOC.
        repeat red.
        cbn.
        unfold mem_state_memory in *.
        rewrite MS' in ALLOC.

        erewrite free_byte_disjoint in ALLOC; eauto.
        cbn in *; subst; auto.
    Qed.

    Lemma byte_allocated_mem_state_refl :
      forall (ms ms' : MemState) (m : memory) (ptr : addr) aid,
        mem_state_memory ms = m ->
        mem_state_memory ms' = m ->
        byte_allocated ms ptr aid <-> byte_allocated ms' ptr aid.
    Proof using.
      intros ms ms' m ptr aid MEQ1 MEQ2.
      split; intros ALLOC.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        repeat red in ALLOC.
        cbn in ALLOC; subst.
        unfold mem_state_memory in *.
        repeat red; auto.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        repeat red in ALLOC.
        cbn in ALLOC; subst.
        unfold mem_state_memory in *.
        repeat red; auto.
    Qed.

    (** If a frame `f` is freed, and a pointer `ptr` does not appear
        in the stack frame, then the allocation status of that `ptr`
        does not change.
     *)
    Lemma free_frame_memory_byte_disjoint_allocated :
      forall f (ms ms' : MemState) (m m' : memory) (ptr : addr) aid,
        free_frame_memory f m = m' ->
        ~ptr_in_frame_prop f ptr ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        byte_allocated ms ptr aid <-> byte_allocated ms' ptr aid.
    Proof using.
      induction f;
        intros ms ms' m m' ptr aid FREE NIN MS MS'.
      - inv FREE.
        cbn in H0.
        eapply byte_allocated_mem_state_refl; eauto.
      - apply free_frame_memory_cons in FREE.
        destruct FREE as [m'' [FREEBYTE FREE]].

        erewrite free_byte_byte_disjoint_allocated
          with (ptr:=a) (ms':= mkMemState (mkMemoryStack m'' (Singleton initial_frame) initial_heap) initial_provenance).
        2: {
          cbn in *.
          erewrite ptr_to_int_int_to_ptr; eauto.
          rewrite int_to_ptr_ptr_to_int; auto.
        }
        all: eauto.
        2: {
          unfold disjoint_ptr_byte.
          firstorder.
        }

        eapply IHf; eauto.
        firstorder.
    Qed.

    Lemma free_block_memory_byte_disjoint_allocated :
      forall block (ms ms' : MemState) (m m' : memory) (ptr : addr) aid,
        free_block_memory block m = m' ->
        ~In (ptr_to_int ptr) (map ptr_to_int block) ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        byte_allocated ms ptr aid <-> byte_allocated ms' ptr aid.
    Proof using.
      induction block;
        intros ms ms' m m' ptr aid FREE NIN MS MS'.
      - inv FREE.
        cbn in H0.
        eapply byte_allocated_mem_state_refl; eauto.
      - apply free_block_memory_cons in FREE.
        destruct FREE as [m'' [FREEBYTE FREE]].

        erewrite free_byte_byte_disjoint_allocated
          with (ptr:=a) (ms':= mkMemState (mkMemoryStack m'' (Singleton initial_frame) initial_heap) initial_provenance).
        2: {
          erewrite ptr_to_int_int_to_ptr; eauto.
          rewrite int_to_ptr_ptr_to_int; auto.
        }
        all: eauto.
        2: {
          unfold disjoint_ptr_byte.
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
    Proof using.
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
    Proof using.
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
    Proof using.
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
    Proof using.
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
        ~In (ptr_to_int ptr) (map ptr_to_int block) ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        read_byte_allowed ms ptr <-> read_byte_allowed ms' ptr.
    Proof using.
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
    Proof using.
      intros ms ms' m m' ptr ptr' byte FREE MS MS' DISJOINT.
      split; intro READ.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        repeat red in READ.
        subst.
        cbn in READ.
        repeat red.
        unfold mem_state_memory in *.
        rewrite MS'.
        erewrite free_byte_disjoint; eauto.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        repeat red in READ.
        subst.
        cbn in READ.
        repeat red; cbn.
        unfold mem_state_memory in *.
        rewrite MS' in READ.
        erewrite free_byte_disjoint in READ; eauto.
    Qed.

    Lemma free_frame_memory_byte_disjoint_read_byte_prop :
      forall f (ms ms' : MemState) (m m' : memory) (ptr : addr) byte,
        free_frame_memory f m = m' ->
        ~ptr_in_frame_prop f ptr ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        read_byte_prop ms ptr byte <-> read_byte_prop ms' ptr byte.
    Proof using.
      intros f ms ms' m m' ptr byte FREE DISJOINT MS MS'.
      split; intro READ.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        repeat red in READ.
        repeat red.
        cbn in READ.
        subst.
        cbn in *.
        unfold mem_state_memory in *.
        rewrite MS'.
        erewrite free_frame_memory_disjoint; eauto.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        repeat red in READ.
        repeat red.
        cbn in READ.
        subst.
        cbn in *.
        unfold mem_state_memory in *.
        rewrite MS' in READ.
        erewrite free_frame_memory_disjoint in READ; eauto.
    Qed.

    Lemma free_block_memory_byte_disjoint_read_byte_prop :
      forall block (ms ms' : MemState) (m m' : memory) (ptr : addr) byte,
        free_block_memory block m = m' ->
        ~In (ptr_to_int ptr) (map ptr_to_int block) ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        read_byte_prop ms ptr byte <-> read_byte_prop ms' ptr byte.
    Proof using.
      intros block ms ms' m m' ptr byte FREE DISJOINT MS MS'.
      split; intro READ.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        repeat red in READ.
        repeat red.
        cbn in READ.
        subst.
        cbn in *.
        unfold mem_state_memory in *.
        rewrite MS'.
        erewrite free_frame_memory_disjoint; eauto.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        repeat red in READ.
        repeat red.
        cbn in READ.
        subst.
        cbn in *.
        unfold mem_state_memory in *.
        rewrite MS' in READ.
        erewrite free_frame_memory_disjoint in READ; eauto.
    Qed.

    (* TODO: Move this so it can be reused *)
    Lemma cannot_pop_singleton :
      forall ms f,
        mem_state_frame_stack_prop ms (Singleton f) ->
        cannot_pop ms.
    Proof using.
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
      forall pre, exec_correct pre mempop mempop_spec_MemPropT exec_correct_id_post.
    Proof using.
      unfold exec_correct.
      intros pre ms st VALID PRE.

      destruct ms as [[mem fs h] pr].
      destruct fs as [f | fs f].
      - (* Pop singleton, error *)
        right.
        cbn.
        exists (raise_error "Last frame, cannot pop.").
        do 2 eexists.
        split.
        { red.
          exists (raise_error "Last frame, cannot pop.").
          cbn. split; [eexists; reflexivity|].
          unfold mempop.
          rewrite MemMonad_run_bind.
          rewrite MemMonad_get_mem_state.
          repeat rewrite bind_ret_l.
          cbn.
          rewrite MemMonad_run_bind.
          rewrite MemMonad_run_raise_error.
          rewrite rbm_raise_bind; [|solve [typeclasses eauto]].
          rewrite rbm_raise_bind; [|solve [typeclasses eauto]].
          reflexivity.
        }

        { cbn.
          split.
          { eapply cannot_pop_singleton.
            do 2 red.
            cbn; reflexivity.
          }

          { intros [x CONTRA]; inv CONTRA.
          }
        }

      - (* Pop succeeds *)
        right.
        exists (ret tt).
        do 2 eexists.
        split.
        { red.
          exists (ret tt).
          cbn. split; [reflexivity|].
          unfold mempop.
          rewrite MemMonad_run_bind.
          rewrite MemMonad_get_mem_state.
          repeat rewrite bind_ret_l.
          cbn.
          rewrite MemMonad_run_bind.
          rewrite MemMonad_run_ret.
          rewrite bind_ret_l.
          rewrite MemMonad_put_mem_state.
          reflexivity.
        }

        { split.
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
                                    (mkMemoryStack (fold_left (fun (m : memory) (key : addr) => free_byte (ptr_to_int key) m) f mem) fs h);
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
                                    (mkMemoryStack (fold_left (fun (m : memory) (key : addr) => free_byte (ptr_to_int key) m) f mem) fs h);
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
            intros _.
            split.
            { (* TODO: pull this out into lemma *)
              red.
              intros sid' USED.
              repeat red in USED.
              destruct USED as (?&?&?&?).
              repeat red in H0.
              cbn in H0.
              repeat (break_match_hyp; try contradiction).
              subst.
              erewrite free_frame_memory_read_byte_raw_disjoint in Heqo; try reflexivity.
              2: {
                intros CONTRA.
                erewrite free_frame_memory_read_byte_raw in Heqo; try discriminate; eauto.
              }
              eapply VALID.
              red.
              exists x, (fst m).
              split; eauto.
              repeat red.
              cbn.
              rewrite Heqo.
              rewrite Heqb.
              reflexivity.
            }

            exists tt; split; eauto.
        }

        Unshelve.
        apply st.
        apply ({|
              ms_memory_stack :=
                {|
                  memory_stack_memory := mem;
                  memory_stack_frame_stack := Singleton f;
                  memory_stack_heap := h
                |};
              ms_provenance := pr
            |}).
    Qed.

    Lemma byte_not_allocated_dec :
      forall ms ptr,
        {byte_not_allocated ms ptr} + {~ byte_not_allocated ms ptr}.
    Proof using.
      intros ([m fs h] & pr) ptr.

      unfold byte_not_allocated.
      unfold byte_allocated.
      unfold addr_allocated_prop_memory.
      cbn.

      destruct (read_byte_raw m (ptr_to_int ptr)) as [[byte aid] |] eqn:READ.
      - (* Allocated *)
        right.
        cbn.
        intros CONTRA.
        specialize (CONTRA aid).
        apply CONTRA.
        clear CONTRA.
        symmetry; apply aid_eq_dec_refl.
      - (* Not allocated *)
        left.
        intros aid CONTRA.
        auto.
    Qed.

    Lemma byte_allocated_dec :
      forall ms ptr,
        {exists aid, byte_allocated ms ptr aid} + {~ exists aid, byte_allocated ms ptr aid}.
    Proof using.
      intros ([m fs h] & pr) ptr.

      unfold byte_not_allocated.
      unfold byte_allocated.
      unfold addr_allocated_prop_memory.
      cbn.

      destruct (read_byte_raw m (ptr_to_int ptr)) as [[byte aid] |] eqn:READ.
      - (* Allocated *)
        left.
        exists aid.
        repeat eexists.
        cbn.
        symmetry; apply aid_eq_dec_refl.
      - (* Not allocated *)
        right.
        intros (aid & CONTRA).
        auto.
    Qed.

    Lemma block_ptr_allocated_dec :
      forall m1 root ptr,
        ptr_in_memstate_heap m1 root ptr ->
        {exists aid, byte_allocated m1 ptr aid} + {byte_not_allocated m1 ptr}.
    Proof using.
      intros ([m fs h] & pr) root ptr INBLOCK.

      red in INBLOCK.
      unfold memory_stack_heap_prop in INBLOCK.
      cbn in INBLOCK.
      specialize (INBLOCK h).
      forward INBLOCK; [reflexivity|].
      unfold ptr_in_heap_prop in INBLOCK.
      break_match_hyp; try inv INBLOCK.

      unfold byte_not_allocated.
      unfold byte_allocated.
      unfold addr_allocated_prop_memory.
      cbn.

      destruct (read_byte_raw m (ptr_to_int ptr)) as [[byte aid] |] eqn:READ.
      - (* Allocated *)
        left.
        repeat eexists.
        cbn.
        symmetry; apply aid_eq_dec_refl.
      - (* Not allocated *)
        right.
        intros aid CONTRA.
        auto.
    Qed.

    Lemma byte_allocated_ignores_provenance :
      forall ms ptr1 ptr2 aid,
        byte_allocated ms ptr1 aid ->
        ptr_to_int ptr1 = ptr_to_int ptr2 ->
        byte_allocated ms ptr2 aid.
    Proof using.
      intros ms ptr1 ptr2 aid ALLOC INTEQ.
      do 2 red.
      do 2 red in ALLOC.
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
    Proof using.
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
      set (block := b).
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

        pose proof INHEAP as INHEAP'.
        apply list_in_map_inv in INHEAP'.
        destruct INHEAP' as [ptr' [PEQ IN]].
        assert (In ptr' block) as INBLOCK.
        { subst block; auto.
        }

        specialize (ALL_ALLOCATED _ INBLOCK).
        subst ms.
        destruct ALL_ALLOCATED as (aid' & ALL_ALLOCATED).
        exists aid'.
        eapply byte_allocated_ignores_provenance.
        apply ALL_ALLOCATED.
        auto.
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
        exec_correct pre (free ptr) (free_spec_MemPropT ptr) exec_correct_id_post.
    Proof using.
      unfold exec_correct.
      intros ptr pre ms st VALID PRE.

      (* Need to determine if `ptr` is a root in the heap... If not,
         UB has occurred.
       *)

      destruct ms as [[mem fs h] pr] eqn:HMS.
      destruct (member (ptr_to_int ptr) h) eqn:ROOTIN.

      2: { (* UB, ptr not a root of the heap *)
        left.
        exists ms. exists ""%string.
        cbn.
        intros FREE.
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
        exists ms. exists ""%string.
        cbn.
        intros FREE.
        inv FREE.
        destruct free_was_allocated0 as (aid & ALLOC).
        unfold byte_allocated, addr_allocated_prop_memory in ALLOC.
        pose proof ALLOC as ALLOC'.
        cbn in ALLOC'.
        break_match_hyp; auto.
        inv READ_ROOT.
      }

      (* Need to determine if block is allocated *)
      pose proof (block_allocated_dec ms ptr) as [BLOCK_ALLOCATED | BLOCK_NOTALLOCATED].
      2: {
        (* Block unallocated, UB *)
        left.
        exists ms. exists ""%string.
        cbn.
        intros FREE.
        inv FREE.
        contradiction.
      }

      pose proof (member_lookup _ _ ROOTIN) as (block & FINDPTR).
      right.
      cbn.
      exists (ret tt).
      do 2 eexists.

      split.
      { red.
        exists (ret tt).
        split; cbn; [reflexivity|].
        unfold free.
        cbn.
        rewrite MemMonad_run_bind.
        rewrite MemMonad_get_mem_state.
        repeat rewrite bind_ret_l.
        cbn.
        rewrite FINDPTR.
        rewrite MemMonad_put_mem_state.
        reflexivity.
      }

      split.
      { (* Proof of free_spec *)
        split; split.
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
          cbn.
          rewrite READ_ROOT.
          symmetry; apply aid_eq_dec_refl.
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
      }

      (* MemMonad_valid_state *)
      intros _.
      split.
      { (* TODO: pull this out into lemma *)
        red.
        intros sid' USED.
        repeat red in USED.
        destruct USED as (?&?&?&?).
        repeat red in H0.
        cbn in H0.
        repeat (break_match_hyp; try contradiction).
        subst.
        erewrite free_frame_memory_read_byte_raw_disjoint in Heqo; try reflexivity.
        2: {
          intros CONTRA.
          erewrite free_frame_memory_read_byte_raw in Heqo; try discriminate; eauto.
        }
        eapply VALID.
        red.
        exists x, (fst m).
        split; eauto.
        repeat red.
        cbn.
        rewrite Heqo.
        rewrite Heqb.
        reflexivity.
      }

      exists tt; split; eauto.
    Qed.

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

    Lemma initial_frame_correct : initial_frame_prop.
    Proof using.
      split.
      apply initial_frame_empty.
    Qed.

    Lemma initial_heap_correct : initial_heap_prop.
    Proof using.
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
    Proof using.
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
    Proof using.
      intros f' f F.
      unfold empty_frame.
      setoid_rewrite F.
      reflexivity.
    Qed.

    (* TODO: move this? *)
    Lemma empty_frame_nil :
      empty_frame [].
    Proof using.
      red.
      cbn.
      auto.
    Qed.

    (* TODO: move this? *)
    Lemma empty_frame_stack_frame_empty :
      empty_frame_stack frame_empty.
    Proof using.
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
    Proof using.
      intros f' f F.
      split; intros [ROOTS PTRS].
      - split; setoid_rewrite <- F; auto.
      - split; setoid_rewrite F; auto.
    Qed.

    (* TODO: move this? *)
    Lemma empty_heap_heap_empty :
      empty_heap heap_empty.
    Proof using.
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
    Proof using.
      split.
      - intros ptr aid CONTRA.
        unfold initial_memory_state in *.
        repeat red in CONTRA.
        cbn in *.
        break_match_hyp; auto.
        rewrite read_byte_raw_memory_empty in Heqo.
        discriminate.
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
      - intros ptr byte CONTRA.
        repeat red in CONTRA.
        break_match_hyp; auto.
        cbn in Heqo.
        rewrite read_byte_raw_memory_empty in Heqo.
        discriminate.
    Qed.

    (* TODO: Move this earlier? *)
    Lemma read_byte_allowed_byte_not_allocated :
        forall ms ptr,
          byte_not_allocated ms ptr ->
          ~ read_byte_allowed ms ptr.
    Proof using.
      intros ms ptr NALLOC.
      intros CONTRA.
      red in CONTRA, NALLOC.
      destruct CONTRA as (?&?&?).
      eapply NALLOC; eauto.
    Qed.

    (* TODO: Move this earlier? *)
    Lemma read_byte_prop_byte_not_allocated :
        forall ms ptr byte,
          byte_not_allocated ms ptr ->
          ~ read_byte_prop ms ptr byte.
    Proof using.
      intros ms ptr byte NALLOC.
      intros CONTRA.
      red in CONTRA, NALLOC.
      red in CONTRA.
      break_match_hyp; try contradiction.
      break_match_hyp_inv.
      destruct m.
      eapply NALLOC; eauto.
      repeat red.
      rewrite Heqo.
      symmetry; apply aid_eq_dec_refl.      
    Qed.

    (* TODO: Move this earlier? *)
    Lemma write_byte_allowed_byte_not_allocated :
        forall ms ptr,
          byte_not_allocated ms ptr ->
          ~ write_byte_allowed ms ptr.
    Proof using.
      intros ms ptr NALLOC.
      intros CONTRA.
      red in CONTRA, NALLOC.
      destruct CONTRA as (?&?&?).
      eapply NALLOC; eauto.
    Qed.

    (* TODO: Move this earlier? *)
    Lemma free_byte_allowed_byte_not_allocated :
        forall ms ptr,
          byte_not_allocated ms ptr ->
          ~ free_byte_allowed ms ptr.
    Proof using.
      intros ms ptr NALLOC.
      intros CONTRA.
      red in CONTRA, NALLOC.
      destruct CONTRA as (?&?&?).
      eapply NALLOC; eauto.
    Qed.

    End MemoryPrimatives.

End FiniteMemoryModelExecPrimitives.
