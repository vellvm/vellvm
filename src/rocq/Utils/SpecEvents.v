From Paco Require Import paco.

From ITree Require Import
  ITree
  Basics
  Basics.Basics
  HeterogeneousRelations
  Eqit.

From ITreeSpec Require Import
  ITreeSpecDefinition
  ITreeSpecFacts
  ITreeSpecCombinatorFacts.

From ExtLib Require Import
  Structures.Functor
  Structures.Monads.

From Vellvm Require Import
  Utils.IntMaps
  Semantics.RuttProps.

From Stdlib Require Import ZArith String.

From Vellvm Require Import LLVMEvents.

(* Memory that's just an IntMap of possibly allocated nat "bytes" *)
Definition memory := IntMap nat.

Variant MemE : Type -> Type :=
  | LoadE (key : Z) : MemE nat
  | StoreE (key : Z) (val : nat) : MemE unit
  | AllocE : MemE Z.

Import Basics.Basics.Monads.

Definition handle_mem {E} `{FailureE -< E} : MemE ~> stateT memory (itree E) :=
  fun _ e mem =>
    match e with
    | LoadE k =>
        match lookup k mem with
        | Some v => ret (mem, v)
        | None => raise "Load from unallocated address."
        end
    | StoreE k v =>
        match lookup k mem with
        | Some v =>
            let mem' := add k v mem in
            ret (mem', tt)
        | None => raise "Store to unallocated address."
        end
    | AllocE =>
        let k := next_key mem in
        ret (add k 0 mem, k)
    end.

Definition handle_mem_spec {E} `{FailureE -< E} : MemE ~> stateT memory (itree_spec E) :=
  fun _ e mem =>
    match e with
    | LoadE k =>
        match lookup k mem with
        | Some v => ret (mem, v)
        | None => raise "Load from unallocated address."
        end
    | StoreE k v =>
        match lookup k mem with
        | Some v =>
            let mem' := add k v mem in
            ret (mem', tt)
        | None => raise "Store to unallocated address."
        end
    | AllocE =>
        let alloc_spec k := member k mem = false in
        Vis (Spec_forall _)
          (fun (key : {k : Z | alloc_spec k}) =>
             let k := proj1_sig key in
             ret (add k 0 mem, k))
    end.


Notation Effin := (MemE +' FailureE).
Notation Effout := FailureE.

Definition in_rel : prerel Effin Effin.
  intros A B e1 e2.
  destruct e1, e2.
  - apply
      (match m, m0 with
       | LoadE k1, LoadE k2 =>
           k1 = k2
       | StoreE k1 v1, StoreE k2 v2 =>
           k1 = k2 /\ v1 = v2
       | AllocE, AllocE =>
           True
       | _, _ =>
           False
       end
      ).
  - apply False.
  - apply False.
  - apply True.
Defined.

Require Import Stdlib.Program.Equality.
From Stdlib Require Import Lia.

Definition in_post_rel : postrel Effin Effin.
  intros A B e1 a e2 b.
  destruct e1, e2.
  - remember m. dependent destruction m;
      remember m0; dependent destruction m0.
    + apply (key = key0 /\ a = b).
    + apply False.
    + apply False.
    + apply False.
    + (* Store *)
      apply (key = key0 /\ val = val0 /\ a = b).
    + apply False.
    + apply False.
    + apply False.
    + apply True.
  - apply False.
  - apply False.
  - apply True.
Defined.

Lemma spec_refines_raise T s :
  @refines
    Effin Effin (memory * T) (memory * T)
    in_rel
    in_post_rel
    eq
    (raise s)
    (raise s).
Proof.
  apply refines_bind with (RR:=eq); cbn.
  - apply refines_vis; cbn; auto.
    intros [] [].
  - intros [].  
Qed.

Lemma handle_mem_correct {T} (e : MemE T) (m : memory) :
  @refines
    Effin Effin (memory * T) (memory * T)
    in_rel
    in_post_rel
    eq
    (handle_mem_spec T e m)
    (handle_mem T e m).
Proof.
  revert e m.
  intros e m.
  destruct e.
  - (* Load *)
    cbn.
    destruct (lookup key m).
    + pstep; constructor; auto.
    + apply spec_refines_raise.
  - cbn.
    destruct (lookup key m).
    + pstep; constructor; auto.
    + apply spec_refines_raise.
  - cbn.
    pstep.
    red; cbn.
    eapply refinesF_forallL.
    Unshelve.
    2: {
      exists (next_key m).
      destruct (member (next_key m) m) eqn:MEM; auto.
      apply IM.mem_2 in MEM.
      apply next_key_correct in MEM.
      lia.
    }
    cbn.
    constructor.
    reflexivity.
Qed.

Lemma alloca_empty :
  forall k,
    @refines
      Effin Effin (memory * Z) (memory * Z)
      in_rel
      in_post_rel
      eq
      (handle_mem_spec Z (AllocE) empty)
      (ret (add k 0 empty, k)).
Proof.
  intros k.
  cbn.
  pstep. red; cbn.
  apply refinesF_forallL with (a:=exist (fun k => false = false) k eq_refl).
  cbn.
  constructor; auto.
Qed.

Import MonadNotation.
Open Scope monad.
Import State.

Definition double_alloc : itree MemE bool
  := k <- trigger AllocE;;
     p <- trigger AllocE;;
     ret (Z.eqb k p).

Lemma alloc_disjoint :
  exists m,
    @refines
      Effin Effin (memory * bool) (memory * bool)
      in_rel
      in_post_rel
      eq
      (interp_state handle_mem_spec double_alloc empty)
      (ret (m, false)).
Proof.
  eexists.
  cbn.
  rewrite bind_trigger.
  setoid_rewrite StateFacts.interp_state_vis.
  cbn.
Admitted.
