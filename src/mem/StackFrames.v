From Mem Require Import
  Addresses.MemoryAddress.

From Coq Require Import
  List
  Relations
  RelationClasses
  Structures.Equalities.

From ExtLib Require Import
  Structures.Monads
  Structures.Functor.

Require Import Morphisms.

Import MonadNotation.
Import ListNotations.

Module Type CORE_FRAME
  (Import ADDR : CORE_ADDRESS) <: Typ.
  Parameter t : Type.
  Parameter ptr_in_frame : t -> addr -> bool.
  Parameter ptrs_in_frame : t -> list addr.
  Parameter add_to_frame : t -> addr -> t.
  Parameter empty_frame : t.

  Parameter empty_frame_spec :
    forall ptr,
      ptr_in_frame empty_frame ptr = false.

  Parameter add_to_frame_new :
    forall ptr f,
      ptr_in_frame (add_to_frame f ptr) ptr = true.

  (* May not hold for `ptr_in_frame f p = false`, because we may
     consider different pointers with the same provenance to be in a
     frame if they share a physical address *)
  Parameter add_to_frame_old :
    forall ptr p f,
      ptr_in_frame f p = true ->
      ptr_in_frame (add_to_frame f ptr) p = true.

  Parameter ptr_in_frame_ptrs_in_frame :
    forall f ptr,
      ptr_in_frame f ptr = true <-> In ptr (ptrs_in_frame f).
End CORE_FRAME.

Module Type FRAME_NOTATIONS
  (Import ADDR : CORE_ADDRESS)
  (Import F : CORE_FRAME ADDR).
  Notation Frame := F.t.
End FRAME_NOTATIONS.

Module Type FRAME_EQV
  (Import ADDR : CORE_ADDRESS)
  (Import F : CORE_FRAME ADDR)
  (Import FN : FRAME_NOTATIONS ADDR F).
  Definition frame_eqv (f f' : Frame) : Prop :=
    forall ptr, ptr_in_frame f ptr = ptr_in_frame f' ptr.

  #[global] Instance frame_eqv_Equivalence : Equivalence frame_eqv.
  Proof.
    split.
    - intros f ptr.
      reflexivity.
    - intros f1 f2 EQV.
      unfold frame_eqv in *.
      firstorder.
    - intros x y z XY YZ.
      unfold frame_eqv in *.
      congruence.
  Qed.
End FRAME_EQV.

Module Type FRAME_EXTRAS
  (Import ADDR : CORE_ADDRESS)
  (Import F : CORE_FRAME ADDR)
  (Import FN : FRAME_NOTATIONS ADDR F).

  Definition add_all_to_frame (f : Frame) (ptrs : list addr) : Frame
    := fold_left add_to_frame ptrs f.
End FRAME_EXTRAS.

Module Type FRAME (ADDR : CORE_ADDRESS) := CORE_FRAME ADDR <+ FRAME_NOTATIONS ADDR <+ FRAME_EQV ADDR <+ FRAME_EXTRAS ADDR.

Module Type CORE_FRAME_STACK
  (Import ADDR : CORE_ADDRESS)
  (Import F : CORE_FRAME ADDR) <: Typ.
  Parameter t : Type.
  Parameter initial_frame_stack : t.

  Parameter peek : t -> option F.t.
  Parameter pop : t -> option (F.t * t).
  Parameter push : t -> F.t -> t.

  Parameter push_peek :
    forall fs1 f fs2,
      fs2 = push fs1 f ->
      peek fs2 = Some f.

  Parameter push_pop :
    forall fs1 f fs2,
      fs2 = push fs1 f ->
      pop fs2 = Some (f, fs1).

  Parameter peek_pop :
    forall fs1,
      peek fs1 = fmap fst (pop fs1).

  Parameter pop_empty :
    pop initial_frame_stack = None.
End CORE_FRAME_STACK.

Module Type FRAME_STACK_NOTATIONS
  (Import ADDR : CORE_ADDRESS)
  (Import F : CORE_FRAME ADDR)
  (Import FS : CORE_FRAME_STACK ADDR F).
  Notation FrameStack := FS.t.
End FRAME_STACK_NOTATIONS.

Module Type FRAME_STACK_EXTRAS
  (Import ADDR : CORE_ADDRESS)
  (Import F : FRAME ADDR)
  (Import FN : FRAME_NOTATIONS ADDR F)
  (Import FS : CORE_FRAME_STACK ADDR F)
  (Import FSN : FRAME_STACK_NOTATIONS ADDR F FS).

  Definition modify_current_frame (fs : FrameStack) (g : Frame -> Frame) : option FrameStack
    := '(f, fs') <- pop fs;;
       ret (push fs' (g f)).

  Definition add_all_to_current_frame (fs : FrameStack) (ptrs : list addr) : option FrameStack
    := modify_current_frame fs (fun f => add_all_to_frame f ptrs).
End FRAME_STACK_EXTRAS.

Module Type FRAME_STACK (ADDR : CORE_ADDRESS) (F : FRAME ADDR) := CORE_FRAME_STACK ADDR F <+ FRAME_STACK_NOTATIONS ADDR F <+ FRAME_STACK_EXTRAS ADDR F.

(*** List implementation of frames *)

Module FRAME_LIST_CORE
  (Import ADDR : CORE_ADDRESS) <: CORE_FRAME ADDR.
  Definition t := list addr.
  Definition ptr_in_frame (f : t) (p : addr) : bool :=
    existsb (fun z => Coqlib.proj_sumbool (ADDR.eq_dec p z)) f.
  Definition ptrs_in_frame (f : t) : list addr :=
    f.
  Definition empty_frame : t := [].

  Definition add_to_frame (f : t) (p : addr) : t :=
    cons p f.

  Lemma empty_frame_spec :
    forall ptr,
      ptr_in_frame empty_frame ptr = false.
  Proof.
    intros ptr.
    cbn. reflexivity.
  Qed.

  Lemma add_to_frame_new :
    forall ptr f,
      ptr_in_frame (add_to_frame f ptr) ptr = true.
  Proof.
    intros ptr f.
    cbn.
    apply Bool.orb_true_iff.
    left.
    unfold Coqlib.proj_sumbool.
    destruct (eq_dec ptr ptr); auto.
  Qed.

  (* May not hold for `ptr_in_frame f p = false`, because we may
     consider different pointers with the same provenance to be in a
     frame if they share a physical address *)
  Lemma add_to_frame_old :
    forall ptr p f,
      ptr_in_frame f p = true ->
      ptr_in_frame (add_to_frame f ptr) p = true.
  Proof.
    intros ptr p f IN.
    cbn.
    apply Bool.orb_true_iff.
    unfold Coqlib.proj_sumbool.
    destruct (eq_dec p ptr); auto.
  Qed.

  Lemma ptr_in_frame_ptrs_in_frame :
    forall f ptr,
      ptr_in_frame f ptr = true <-> In ptr (ptrs_in_frame f).
  Proof.
    intros f ptr.
    unfold ptr_in_frame, ptrs_in_frame.
    split; intros IN.
    - apply existsb_exists in IN.
      destruct IN as (?&?&?).
      apply Coqlib.proj_sumbool_true in H0; subst; auto.
    - apply existsb_exists.
      exists ptr.
      split; auto.
      apply Coqlib.proj_sumbool_is_true; auto.
  Qed.
End FRAME_LIST_CORE.

Module FRAME_LIST (ADDR : CORE_ADDRESS) <: FRAME ADDR := FRAME_LIST_CORE ADDR <+ FRAME_NOTATIONS ADDR <+ FRAME_EQV ADDR <+ FRAME_EXTRAS ADDR.

(*** List implementation of frame stacks *)
Module CORE_FRAME_STACK_LIST (Import ADDR: CORE_ADDRESS) (Import F : FRAME ADDR) <: CORE_FRAME_STACK ADDR F.
  Definition t := list Frame.

  Definition initial_frame_stack : t := [].

  Definition peek (fs : t) : option F.t := hd_error fs.

  Definition pop (fs : t) : option (F.t * t) :=
    match fs with
    | [] => None
    | (f::fs) => ret (f, fs)
    end.

  Definition push (fs : t) (f : F.t) : t := f :: fs.

  Lemma push_peek :
    forall fs1 f fs2,
      fs2 = push fs1 f ->
      peek fs2 = Some f.
  Proof.
    intros fs1 f fs2 H.
    rewrite H.
    cbn; auto.
  Qed.

  Lemma peek_pop :
    forall fs1,
      peek fs1 = fmap fst (pop fs1).
  Proof.
    intros fs1.
    destruct fs1; cbn; auto.
  Qed.

  Lemma push_pop :
    forall fs1 f fs2,
      fs2 = push fs1 f ->
      pop fs2 = Some (f, fs1).
  Proof.
    intros fs1 f fs2 H.
    rewrite H.
    cbn; auto.
  Qed.

  Lemma pop_empty :
    pop initial_frame_stack = None.
  Proof.
    cbn; auto.
  Qed.
    
End CORE_FRAME_STACK_LIST.

Module FRAME_STACK_LIST (ADDR : CORE_ADDRESS) (F : FRAME ADDR) <: FRAME_STACK ADDR F := CORE_FRAME_STACK_LIST ADDR F <+ FRAME_STACK_NOTATIONS ADDR F <+ FRAME_STACK_EXTRAS ADDR F.
