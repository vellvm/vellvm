From Mem Require Import
  Addresses.MemoryAddress.

From Coq Require Import
  List
  Relations
  RelationClasses
  Structures.Equalities.

Require Import Morphisms.

Module Type CORE_HEAP
  (Import ADDR : BASIC_ADDRESS) <: Typ.
  Parameter t : Type.
  Parameter empty_heap : t.

  (*** Heap operations *)

  (** Is a pointer a root pointer of the heap *)
  Parameter root_ptr_in_heap : t -> addr -> bool.

  (** Is a pointer allocated in the heap under a root pointer *)
  Parameter ptr_in_heap : t -> addr -> addr -> bool.
  Parameter ptrs_in_heap : t -> addr -> list addr.

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
      ptr_in_heap h root ptr = true <-> In ptr (ptrs_in_heap h root).

  Parameter free_root_in_heap_root_not_in_heap :
    forall h root,
      root_ptr_in_heap h root = false ->
      free_root_in_heap h root = None.

  Parameter free_root_in_heap_removes_root :
    forall h root h',
      free_root_in_heap h root = Some h' ->
      root_ptr_in_heap h root = false.

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
