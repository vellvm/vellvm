From Mem Require Import
  Addresses.MemoryAddress
  FiniteMaps.

From Stdlib Require Import
  List
  Relations
  RelationClasses
  Structures.Equalities
  ZArith.

Require Import Morphisms.

Import ListNotations.

Module Type CORE_HEAP
  (Import ADDR : BASIC_ADDRESS) <: Typ.
  Parameter t : Type.
  Parameter empty_heap : t.

  (*** Heap operations *)

  (** Is a pointer a root pointer of the heap *)
  Parameter root_ptr_in_heap : t -> addr -> bool.

  (** Is a pointer allocated in the heap under a root pointer *)
  Parameter ptr_in_heap : t -> addr -> addr -> bool.
  Parameter ptrs_in_heap : t -> addr -> list Z.

  (** Add a pointer to the heap under a root pointer *)
  Parameter add_ptr_to_heap : t -> addr -> addr -> t.

  (** Free a root pointer *)
  Parameter free_root_in_heap : t -> addr -> option t.

  (*** Heap properties *)

  Parameter empty_heap_ptr_spec :
    forall root ptr,
      ptr_in_heap empty_heap root ptr = false.

  Parameter empty_heap_root_spec :
    forall ptr,
      root_ptr_in_heap empty_heap ptr = false.

  Parameter add_ptr_to_heap_ptr_in_heap_new :
    forall h root ptr,
      ptr_in_heap (add_ptr_to_heap h root ptr) root ptr = true.

  (* May not hold for `ptr_in_heap h ptr = false`, because we may
     consider different pointers with the same provenance to be in a
     heap if they share a physical address *)
  Parameter add_ptr_to_heap_ptr_in_heap_old :
    forall h root ptr root_old ptr_old,
      ptr_in_heap h root_old ptr_old = true ->
      ptr_in_heap (add_ptr_to_heap h root ptr) root_old ptr_old = true.

  Parameter add_ptr_to_heap_root_ptr_in_heap_new :
    forall h root ptr,
      root_ptr_in_heap (add_ptr_to_heap h root ptr) root = true.

  (* May not hold for `root_ptr_in_heap h root = false`, because we may
     consider different pointers with the same provenance to be in a
     heap if they share a physical address *)
  Parameter add_ptr_to_heap_root_ptr_in_heap_old :
    forall h root ptr root_old,
      root_ptr_in_heap h root_old = true ->
      root_ptr_in_heap (add_ptr_to_heap h root ptr) root_old = true.

  Parameter ptr_in_heap_ptrs_in_heap :
    forall h root ptr,
      ptr_in_heap h root ptr = true <-> In (ptr_to_int ptr) (ptrs_in_heap h root).

  Parameter free_root_in_heap_root_not_in_heap :
    forall h root,
      root_ptr_in_heap h root = false ->
      free_root_in_heap h root = None.

  Parameter free_root_in_heap_removes_root :
    forall h root h',
      free_root_in_heap h root = Some h' ->
      root_ptr_in_heap h' root = false.

  Parameter free_root_in_heap_removes_ptrs :
    forall h root h',
      free_root_in_heap h root = Some h' ->
      forall ptr, ptr_in_heap h root ptr = true -> ptr_in_heap h' root ptr = false.

  Parameter free_root_in_heap_preserves_other_roots :
    forall h root root' h',
      ptr_to_int root <> ptr_to_int root' ->
      free_root_in_heap h root = Some h' ->
      forall ptr, ptr_in_heap h root' ptr = ptr_in_heap h' root' ptr.
End CORE_HEAP.

Module Type HEAP_NOTATIONS
  (Import ADDR : BASIC_ADDRESS)
  (Import H : CORE_HEAP ADDR).
  Notation Heap := H.t.
End HEAP_NOTATIONS.

Module Type HEAP_EQV
  (Import ADDR : BASIC_ADDRESS)
  (Import H : CORE_HEAP ADDR)
  (Import HN : HEAP_NOTATIONS ADDR H).

  Record heap_eqv (h h' : Heap) : Prop :=
    {
      heap_roots_eqv : forall root, root_ptr_in_heap h root = root_ptr_in_heap h' root;
      heap_ptrs_eqv : forall root ptr, ptr_in_heap h root ptr = ptr_in_heap h' root ptr;
    }.

  #[global] Instance root_in_heap_prop_Proper :
    Proper (heap_eqv ==> @Logic.eq addr  ==> @Logic.eq bool) root_ptr_in_heap.
  Proof.
    intros h h' HEAPEQ ptr ptr' PTREQ; subst.
    inversion HEAPEQ.
    eauto.
  Qed.

  #[global] Instance ptr_in_heap_prop_Proper :
    Proper (heap_eqv ==> @Logic.eq addr ==> @Logic.eq addr ==> @Logic.eq bool) ptr_in_heap.
  Proof.
    intros h h' HEAPEQ root root' ROOTEQ ptr ptr' PTREQ; subst.
    inversion HEAPEQ.
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
End HEAP_EQV.

Module Type HEAP_EXTRAS
  (Import ADDR : BASIC_ADDRESS)
  (Import F : CORE_HEAP ADDR)
  (Import FN : HEAP_NOTATIONS ADDR F).

  Definition add_ptrs_to_heap' (h : Heap) (root : addr) (ptrs : list addr) : Heap :=
    fold_left (fun h' ptr => add_ptr_to_heap h' root ptr) ptrs h.

  Definition add_ptrs_to_heap (h : Heap) (ptrs : list addr) : Heap :=
    match ptrs with
    | nil => h
    | (root :: _) =>
        add_ptrs_to_heap' h root ptrs
    end.
End HEAP_EXTRAS.

Module Type HEAP (ADDR : BASIC_ADDRESS) := CORE_HEAP ADDR <+ HEAP_NOTATIONS ADDR <+ HEAP_EQV ADDR <+ HEAP_EXTRAS ADDR.


(*** IntMap based heap implementation *)
Module CORE_HEAP_INTMAP (Import ADDR : BASIC_ADDRESS) <: CORE_HEAP ADDR.
  Definition Block := IS.t.

  Definition t := IM.t Block.
  Definition empty_heap : t := @IM.empty Block.

  (*** Heap operations *)

  (** Is a pointer a root pointer of the heap *)
  Definition root_ptr_in_heap (h : t) (ptr : addr) : bool :=
    IM.mem (ptr_to_int ptr) h.

  (** Is a pointer allocated in the heap under a root pointer *)
  Definition ptr_in_heap (h : t) (root ptr : addr) : bool :=
    match IM.find (ptr_to_int root) h with
    | None => false
    | Some ptrs =>
        IS.mem (ptr_to_int ptr) ptrs
    end.

  Definition ptrs_in_heap (h : t) (root : addr) : list Z :=
    match IM.find (ptr_to_int root) h with
    | None => nil
    | Some ptrs => IS.elements ptrs
    end.

  (** Add a pointer to the heap under a root pointer *)
  Definition add_ptr_to_heap (h : t) (root ptr : addr) : t :=
    if ptr_in_heap h root ptr
    then h
    else
      match IM.find (ptr_to_int root) h with
      | None =>
          IM.add (ptr_to_int root) (IS.singleton (ptr_to_int ptr)) h
      | Some ptrs =>
          IM.add (ptr_to_int root) (IS.add (ptr_to_int ptr) ptrs) h
      end.

  (** Free a root pointer *)
  Definition free_root_in_heap (h : t) (root : addr) : option t :=
    if root_ptr_in_heap h root
    then Some (IM.remove (ptr_to_int root) h)
    else None.

  (*** Heap properties *)

  Lemma empty_heap_ptr_spec :
    forall root ptr,
      ptr_in_heap empty_heap root ptr = false.
  Proof.
    intros root ptr; cbn; auto.
  Qed.

  Lemma empty_heap_root_spec :
    forall ptr,
      root_ptr_in_heap empty_heap ptr = false.
  Proof.
    intros ptr; cbn; auto.
  Qed.

  Lemma add_ptr_to_heap_ptr_in_heap_new :
    forall h root ptr,
      ptr_in_heap (add_ptr_to_heap h root ptr) root ptr = true.
  Proof.
    intros h root ptr.
    unfold add_ptr_to_heap.
    destruct (ptr_in_heap h root ptr) eqn:PTR; auto.
    unfold ptr_in_heap.
    destruct (IM.find (ptr_to_int root) h) eqn:FIND;
      rewrite find_add_eq.
    - apply IS_mem_add_eq.
    - apply IS.mem_1. apply IS.singleton_2; auto.
  Qed.

  (* May not hold for `ptr_in_heap h ptr = false`, because we may
     consider different pointers with the same provenance to be in a
     heap if they share a physical address *)
  Lemma add_ptr_to_heap_ptr_in_heap_old :
    forall h root ptr root_old ptr_old,
      ptr_in_heap h root_old ptr_old = true ->
      ptr_in_heap (add_ptr_to_heap h root ptr) root_old ptr_old = true.
  Proof.
    intros h root ptr root_old ptr_old IN.
    destruct (BinInt.Z.eq_dec (ptr_to_int root) (ptr_to_int root_old)) as [EQROOT | NEQROOT].
    {
      unfold add_ptr_to_heap.
      destruct (ptr_in_heap h root ptr) eqn:PTR; auto.
      unfold ptr_in_heap in *.
      rewrite EQROOT in PTR.
      rewrite EQROOT.
      destruct (IM.find (elt:=Block) (ptr_to_int root_old) h) eqn:FIND; try discriminate.

      rewrite find_add_eq.
      apply IS_mem_add_neq; auto.
      { intros CONTRA.
        rewrite CONTRA in IN.
        rewrite PTR in IN; discriminate.
      }
    }

    {
      unfold add_ptr_to_heap.
      destruct (ptr_in_heap h root ptr) eqn:PTR; auto.
      unfold ptr_in_heap in *.
      destruct (IM.find (elt:=Block) (ptr_to_int root_old) h) eqn:FIND_OLD; try discriminate.
      apply IM.find_2 in FIND_OLD.
      destruct (IM.find (ptr_to_int root) h) eqn:FIND;
        erewrite find_add_neq; eauto;
        apply IM.find_1; auto.
    }
  Qed.

  Lemma add_ptr_to_heap_root_ptr_in_heap_new :
    forall h root ptr,
      root_ptr_in_heap (add_ptr_to_heap h root ptr) root = true.
  Proof.
    intros h root ptr.
    unfold add_ptr_to_heap.
    destruct (ptr_in_heap h root ptr) eqn:PTR; auto.
    - unfold root_ptr_in_heap.
      unfold ptr_in_heap in *.
      destruct (IM.find (elt:=Block) (ptr_to_int root) h) eqn:FIND; try discriminate.
      apply IM.mem_1.
      exists b.
      apply IM.find_2; auto.
    - unfold root_ptr_in_heap.
      unfold ptr_in_heap in *.
      destruct (IM.find (elt:=Block) (ptr_to_int root) h) eqn:FIND; try discriminate;
        apply IM.mem_1;
        eexists; apply IM.add_1; eauto.
  Qed.

  (* May not hold for `root_ptr_in_heap h root = false`, because we may
     consider different pointers with the same provenance to be in a
     heap if they share a physical address *)
  Lemma add_ptr_to_heap_root_ptr_in_heap_old :
    forall h root ptr root_old,
      root_ptr_in_heap h root_old = true ->
      root_ptr_in_heap (add_ptr_to_heap h root ptr) root_old = true.
  Proof.
    intros h root ptr root_old ROOT.
    unfold add_ptr_to_heap.
    unfold root_ptr_in_heap in *.
    unfold ptr_in_heap in *.
    destruct (BinInt.Z.eq_dec (ptr_to_int root) (ptr_to_int root_old)) as [EQ | NEQ].
    - destruct (IM.find (elt:=Block) (ptr_to_int root) h) eqn:FIND.
      + destruct (IS.mem (ptr_to_int ptr) b) eqn:EX; auto.
        apply IM.mem_1.
        eexists; apply IM.add_1; auto.
      + apply IM.mem_1.
        eexists; apply IM.add_1; auto.
    - destruct (IM.find (elt:=Block) (ptr_to_int root) h) eqn:FIND.
      + destruct (IS.mem (ptr_to_int ptr) b) eqn:EX; auto.
        apply IM.mem_1.
        apply IM.mem_2 in ROOT as (x & ROOT).
        eexists; apply IM.add_2; eauto.
      + apply IM.mem_1.
        apply IM.mem_2 in ROOT as (x & ROOT).
        eexists; apply IM.add_2; eauto.
  Qed.

  Lemma ptr_in_heap_ptrs_in_heap :
    forall h root ptr,
      ptr_in_heap h root ptr = true <-> In (ptr_to_int ptr) (ptrs_in_heap h root).
  Proof.
    intros h root ptr.
    unfold ptr_in_heap, ptrs_in_heap.
    split; intros IN.
    - destruct (IM.find (elt:=Block) (ptr_to_int root) h) eqn:FIND; try discriminate.
      apply IS.mem_2 in IN.
      apply IS.elements_1 in IN.
      apply SetoidList.InA_alt in IN as (y&EQV&IN); subst; auto.
    - destruct (IM.find (elt:=Block) (ptr_to_int root) h) eqn:FIND.
      + apply IS.mem_1.
        apply IS.elements_2.
        apply SetoidList.InA_alt.
        eexists; split; eauto.
      + inversion IN.
  Qed.

  Lemma free_root_in_heap_root_not_in_heap :
    forall h root,
      root_ptr_in_heap h root = false ->
      free_root_in_heap h root = None.
  Proof.
    intros h root ROOT.
    unfold free_root_in_heap.
    rewrite ROOT.
    auto.
  Qed.

  Lemma free_root_in_heap_removes_root :
    forall h root h',
      free_root_in_heap h root = Some h' ->
      root_ptr_in_heap h' root = false.
  Proof.
    intros h root h' FREE.
    unfold free_root_in_heap in *.
    unfold root_ptr_in_heap in *.
    destruct (IM.mem (elt:=Block) (ptr_to_int root) h) eqn:MEM; try discriminate.
    inversion FREE.
    destruct (IM.mem (elt:=Block) (ptr_to_int root) (IM.remove (elt:=Block) (ptr_to_int root) h)) eqn:REM; auto.
    apply IM.mem_2 in REM.
    exfalso.
    eapply IM.remove_1; [|apply REM]; auto.
  Qed.

  Lemma free_root_in_heap_removes_ptrs :
    forall h root h',
      free_root_in_heap h root = Some h' ->
      forall ptr, ptr_in_heap h root ptr = true -> ptr_in_heap h' root ptr = false.
  Proof.
    intros h root h' FREE ptr IN.
    unfold free_root_in_heap in *.
    unfold root_ptr_in_heap in *.
    unfold ptr_in_heap in *.
    destruct (IM.find (elt:=Block) (ptr_to_int root) h) eqn:FIND; try discriminate.
    assert (IM.mem (elt:=Block) (ptr_to_int root) h = true) as ROOT_IN.
    { apply IM.mem_1.
      exists b. apply IM.find_2; eauto.
    }

    rewrite ROOT_IN in FREE.
    inversion FREE.

    destruct (IM.find (elt:=Block) (ptr_to_int root) (IM.remove (elt:=Block) (ptr_to_int root) h)) eqn:REM; auto.
    exfalso.

    eapply IM.remove_1; cycle 1.
    exists b0. apply IM.find_2; eauto.
    auto.
  Qed.

  Lemma free_root_in_heap_preserves_other_roots :
    forall h root root' h',
      ptr_to_int root <> ptr_to_int root' ->
      free_root_in_heap h root = Some h' ->
      forall ptr, ptr_in_heap h root' ptr = ptr_in_heap h' root' ptr.
  Proof.
    intros h root root' h' NEQ FREE ptr.
    unfold free_root_in_heap in *.
    unfold root_ptr_in_heap in *.
    unfold ptr_in_heap in *.

    destruct (IM.mem (elt:=Block) (ptr_to_int root) h) eqn:MEM; try discriminate.
    inversion FREE; subst.

    destruct (IM.find (elt:=Block) (ptr_to_int root') (IM.remove (elt:=Block) (ptr_to_int root) h)) eqn:REM.
    + erewrite IM.find_1; try reflexivity.
      eapply IM.remove_3; apply IM.find_2; eauto.
    + destruct (IM.find (elt:=Block) (ptr_to_int root') h) eqn:FIND; auto.
      exfalso.
      replace (IM.find (elt:=Block) (ptr_to_int root') (IM.remove (elt:=Block) (ptr_to_int root) h)) with (Some b) in REM; cycle 1.

      symmetry.
      apply IM.find_1. apply IM.remove_2; auto.
      apply IM.find_2; auto.

      discriminate.
  Qed.
End CORE_HEAP_INTMAP.

Module HEAP_IMPL (ADDR : BASIC_ADDRESS) <: HEAP ADDR := CORE_HEAP_INTMAP ADDR <+ HEAP_NOTATIONS ADDR <+ HEAP_EQV ADDR <+ HEAP_EXTRAS ADDR.
