Unset Universe Checking.

From CTree Require Import
  CTree CTreeDefinitions Eq Fold FoldStateT.

From Vellvm.Utils Require Import Tactics.

From Stdlib Require Import
  FSets.FMapAVL
  FMapFacts
  ZArith
  Lia.

Module IM := FMapAVL.Make(Stdlib.Structures.OrderedTypeEx.Z_as_OT).

(* (* For some reason this causes universe inconsistencies *) *)
(* From Vellvm Require Import *)
(*   Utils.IntMaps. *)

(* From ITree Require Import *)
(*   ITree *)
(*   Basics *)
(*   Basics.Basics *)
(*   Monad *)
(*   HeterogeneousRelations *)
(*   Eqit. *)

(* From ITreeSpec Require Import *)
(*   ITreeSpecDefinition *)
(*   ITreeSpecFacts *)
(*   ITreeSpecCombinatorFacts. *)

From ExtLib Require Import
  Structures.Functor
  Structures.Monads.


From Stdlib Require Import ZArith String.

(* Universe issues... *)
(* From Vellvm Require Import LLVMEvents. *)

Import CTreeNotations.

(* Memory that's just an IntMap of possibly allocated nat "bytes" *)
Definition memory := IM.t nat.

Variant MemE : Type -> Type :=
  | LoadE (key : Z) : MemE nat
  | StoreE (key : Z) (val : nat) : MemE unit
  | AllocE : MemE Z.

(* Failure. Carries a string for a message. *)
Variant FailureE : Type -> Type :=
  | Throw : unit -> FailureE void.

(* This function can be replaced with print_string during extraction
     to print the error messages of Throw and (indirectly) ThrowUB. *)
Definition print_msg (msg : string) : unit := tt.

Definition raise {E B} {A} `{FailureE -< E} (msg : string) : ctree E B A :=
  v <- trigger (Throw (print_msg msg));; match v: void with end.

Fixpoint IM_raw_greatest_key {A} (m : IM.Raw.tree A) : option Z
  := match m with
     | IM.Raw.Leaf _ => None
     | IM.Raw.Node l k _ (@IM.Raw.Leaf _) _ =>
         ret k
     | IM.Raw.Node l k _ r _ =>
         IM_raw_greatest_key r
     end.

Definition IM_greatest_key {A} (m : IM.t A) : option Z
  := IM_raw_greatest_key (IM.this m).

Definition next_key {A} (m : IM.t A) : Z
  := match IM_greatest_key m with
     | Some k => 1 + k
     | None => 0
     end.

  Lemma IM_greatest_key_none' :
    forall {A} (m : IM.t A), IM.Empty m -> IM_greatest_key m = None.
  Proof.
    intros A m H.
    induction m; cbn in *.
    induction this; cbn in *; auto.
    - exfalso; eapply H.
      cbn.
      constructor; reflexivity.
  Qed.

  Lemma IM_greatest_key_none'' :
    forall {A} (m : IM.t A), IM_greatest_key m = None -> IM.Empty m.
  Proof.
    intros A m H.
    induction m; cbn in *.
    induction this; cbn in *; auto.
    - intros k e CONTRA.
      inv CONTRA.
    - exfalso.
      destruct (IM_raw_greatest_key this2) eqn:THIS2.
      + break_match_hyp_inv.
      + break_match_hyp_inv.
        inv is_bst.
        specialize (IHthis2 H5 eq_refl).
        eapply IHthis2.
        constructor; reflexivity.
  Qed.

  Lemma IM_greatest_key_none :
    forall {A} (m : IM.t A), IM_greatest_key m = None <-> IM.Empty m.
  Proof.
    intros A m.
    split; intros H.
    + apply IM_greatest_key_none''; auto.
    + apply IM_greatest_key_none'; auto.
  Qed.

  Lemma IM_greatest_key_In :
    forall {A} (m : IM.t A) gk,
      IM_greatest_key m = Some gk -> IM.In gk m.
  Proof.
    intros A m.
    intros gk H.
    apply IM.mem_2.
    revert gk H.
    destruct m; cbn in *.
    induction this; intros gk GK.
    - cbn in *. inv GK.
    - rename k into current_key.
      cbn.
      (* gk is the greatest key. It should be larger than current_key *)
      cbn in GK.
      pose proof is_bst as is_bst2.
      inv is_bst.
      destruct (IM_raw_greatest_key this2) eqn:THIS2;
        destruct this2; inv GK.
      + (* At a leaf eq *)
        break_match; cbn in *;
          solve
            [ red in l; lia
            | discriminate
            ].
      + (* Not at a leaf... *)
        pose proof H5.
        eapply IHthis2 in H5; eauto.
        eapply IM.Raw.Proofs.mem_2 in H5; eauto.

        red in H7.
        apply H7 in H5.

        break_match; cbn in *;
          try solve
            [ red in l; lia
            | discriminate
            ]; auto.
      + break_match; cbn in *; auto;
          solve
            [ red in l; lia
            | discriminate
            ].
  Qed.

  Lemma IM_greatest_key_In' :
    forall {A} (m : IM.t A) k,
      IM.In k m ->
      exists gk, IM_greatest_key m = Some gk.
  Proof.
    intros A m k IN.
    destruct (IM_greatest_key m) eqn:GK.
    exists z; auto.
    apply IM_greatest_key_none in GK.
    destruct IN.
    apply GK in H.
    contradiction.
  Qed.

  Lemma IM_greatest_key_lt :
    forall {A} (m : IM.t A) gk,
      IM_greatest_key m = Some gk -> IM.Raw.lt_tree (1 + gk) (IM.this m).
  Proof.
    intros A m.
    destruct m; cbn in *.
    induction this; intros gk GK.
    - cbn in *. inv GK.
    - rename k into current_key.
      cbn.
      (* gk is the greatest key. It should be larger than current_key *)
      cbn in GK.
      pose proof is_bst as is_bst2.
      inv is_bst.
      destruct (IM_raw_greatest_key this2) eqn:THIS2;
        destruct this2; inv GK.
      + (* At a leaf eq *)
        break_match; cbn in *;
          solve
            [ red in l; lia
            | discriminate
            ].
      + (* Not at a leaf... *)
        pose proof H5.
        eapply IHthis2 in H5; eauto.
        red.
        intros y H0.
        inv H0.
        * (* Root *)
          red in H5.
          specialize (H5 k).
          forward H5.
          constructor; auto.
          specialize (H7 k).
          forward H7.
          constructor; auto.
          cbn in H7.
          lia.
        * (* Left *)
          red in H6.
          specialize (H6 y H2).
          red in H5.
          specialize (H5 k).
          forward H5.
          constructor; auto.
          specialize (H7 k).
          forward H7.
          constructor; auto.
          cbn in H7.
          lia.
        * (* Right *)
          red in H5.
          specialize (H5 y H2).
          auto.
      + red.
        intros y H.
        assert (gk < 1 + gk)%Z by lia.
        inv H; auto.
        * apply H6 in H2.
          cbn in *; lia.
        * inv H2.
  Qed.

  Lemma IM_raw_greatest_key_lr :
    forall {elt} m k (e : elt) l t r kl kr,
      IM.this m = (IM.Raw.Node l k e r t) ->
      IM_raw_greatest_key l = Some kl ->
      IM_raw_greatest_key r = Some kr ->
      (kl < kr)%Z.
  Proof.
    intros elt m k e l t r kl kr NODE GL GR.
    destruct m.
    cbn in *.
    inv is_bst.
    inv H.
    inv H3.

    unfold IM.Raw.gt_tree in *.
    unfold IM.Raw.lt_tree in *.

    assert (IM_greatest_key (@IM.Bst elt l H) = Some kl) as GL' by (cbn; auto).
    assert (IM_greatest_key (@IM.Bst elt r H0) = Some kr) as GR' by (cbn; auto).

    apply IM_greatest_key_In in GL', GR'.
    unfold IM.In in *.
    apply IM.Raw.Proofs.In_alt in GL', GR'.
    apply H2 in GR'.
    apply H1 in GL'.

    lia.
  Qed.

  Lemma next_key_correct :
    forall {A} (m : IM.t A) (a : Z),
      IM.In a m ->
      (a < next_key m)%Z.
  Proof.
    intros A m a IN.
    pose proof IN as GK.
    unfold next_key.
    eapply IM_greatest_key_In' in GK.
    destruct GK as (gk & GK).
    rewrite GK.
    apply IM_greatest_key_lt in GK.
    red in GK.
    specialize (GK a).
    destruct m; cbn in IN.
    unfold IM.In in IN.
    apply IM.Raw.Proofs.In_alt in IN.
    apply GK in IN.
    auto.
  Qed.


Definition handle_mem {E} `{FailureE -< E} : MemE ~> Monads.stateT memory (ctree E void1) :=
  fun _ e mem =>
    match e with
    | LoadE k =>
        match IM.find k mem with
        | Some v => ret (mem, v)
        | None => raise "Load from unallocated address."
        end
    | StoreE k v =>
        match IM.find k mem with
        | Some _ =>
            let mem' := IM.add k v mem in
            ret (mem', tt)
        | None => raise "Store to unallocated address."
        end
    | AllocE =>
        let k := next_key mem in
        ret (IM.add k 0 mem, k)
    end.

Variant AllocC : Type -> Type :=
  | allocC (m : memory) : AllocC ({k | IM.mem k m = false}).

Definition do_alloc {E} `{FailureE -< E} (mem : memory) : ctree E AllocC (memory * Z) :=
  res <- branch (allocC mem);;
  let k := proj1_sig res in
  ret (IM.add k 0 mem, k).

Definition handle_mem_spec {E} `{FailureE -< E} : MemE ~> Monads.stateT memory (ctree E AllocC) :=
  fun _ e mem =>
    match e with
    | LoadE k =>
        match IM.find k mem with
        | Some v => ret (mem, v)
        | None => raise "Load from unallocated address."
        end
    | StoreE k v =>
        match IM.find k mem with
        | Some _ =>
            let mem' := IM.add k v mem in
            ret (mem', tt)
        | None => raise "Store to unallocated address."
        end
    | AllocE => do_alloc mem
    end.

Notation Effin := (MemE +' FailureE).
Notation Bspec := AllocC.
Notation Bexec := void1.
Notation Effout := FailureE.

#[global] Instance Functor_VoidE : Functor void1.
split.
intros A B X H.
destruct H.
Defined.

#[global] Instance Functor_Bexec : Functor Bexec.
try typeclasses eauto.
Defined.

#[global] Instance Functor_AllocC : Functor AllocC.
split.
intros A B X H.
inversion H; subst.
forward X.
exists (next_key m).
destruct (IM.mem (elt:=nat) (next_key m) m) eqn:MEM; auto.
apply IM.mem_2 in MEM.
apply next_key_correct in MEM.
lia.

Abort.

(* 
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

 *)

Require Import Vellvm.Utils.Tactics.

Import SSimNotations.

Lemma spec_refines_raise E `{Effout -< E} F `{Effout -< F} C D X Y L s :
  @ssim
    E F C D X Y L
    (@raise E C _ _ s)
    (@raise F D _ _ s).
Proof.
  unfold raise.
  eapply ssim_clo_bind.
  2: intros [].
  apply ssim_vis.
  intros [].
  Unshelve.
  apply eq.
Qed.

Lemma ssim_raise_ret E `{Effout -< E} F C D X Y L s y :
  ~ @ssim
    E F C D X Y L
    (@raise E C _ _ s)
    (ret y).
Proof.
  intros CONTRA.
  unfold raise in *.
  (* NEED vis / ret inv *)
  unfold CTree.trigger in *.
  cbn in *.
  rewrite bind_vis in CONTRA.
  step in CONTRA.
  cbn in *.
Admitted.

Lemma ssim_ret_raise E F `{Effout -< F} C D X Y L s y :
  ~ @ssim
    E F C D X Y L
    (ret y)
    (@raise F D _ _ s).
Proof.
  intros CONTRA.
  unfold raise in *.
  (* NEED vis / ret inv *)
  unfold CTree.trigger in *.
  cbn in *.
  rewrite bind_vis in CONTRA.
  step in CONTRA.
  cbn in *.
  specialize (CONTRA (val y) Stuck).
  forward CONTRA.
  constructor.
  destruct CONTRA as (?&?&?&?&?).
  apply trans_vis_inv in H0.
  destruct H0 as [[] _].
Qed.

Lemma handle_mem_correct {T} (e : MemE T) (m : memory):
  @ssim Effin Effin _ _ _ _ eq (handle_mem T e m) (handle_mem_spec T e m).
Proof.
  destruct e.
  - cbn.
    break_match_goal.
    + apply ssim_ret; auto.
    + apply spec_refines_raise.
  - cbn.
    break_match_goal.
    + apply ssim_ret; auto.
    + apply spec_refines_raise.
  - cbn.
    unfold do_alloc.
    rewrite bind_branch.
    eapply ssim_br_r.
    Unshelve.
    2: {
      exists (next_key m).
      destruct (IM.mem (elt:=nat) (next_key m) m) eqn:MEM; auto.
      apply IM.mem_2 in MEM.
      apply next_key_correct in MEM.
      lia.
    }
    cbn.
    apply ssim_ret.
    reflexivity.
Qed.

Lemma alloca_empty :
  forall k,
  @ssim Effin Effin void1 _ _ _ eq (ret (IM.add k 0 (IM.empty _), k))
      (handle_mem_spec Z (AllocE) (IM.empty _)).
Proof.
  intros k.
  cbn.
  unfold do_alloc.
  rewrite bind_branch.
  eapply ssim_br_r.
  Unshelve.
  2: {
    exists k.
    destruct (IM.mem (elt:=nat) k (IM.empty nat)) eqn:MEM; auto.
  }

  cbn.
  apply ssim_ret.
  reflexivity.
Qed.

Lemma load_succeeds_spec :
  forall m k v,
    IM.find k m = Some v <->
      @ssim Effin Effin void1 _ _ _ eq (ret (m, v))
        (handle_mem_spec nat (LoadE k) m).
Proof.
  intros m k v.
  split.
  { intros LUP.
    cbn; rewrite LUP.
    apply ssim_ret.
    auto.
  }
  { intros REF.
    cbn in REF.
    destruct (IM.find k m) eqn:LUP.
    - apply ssim_ret_inv in REF.
      apply val_eq_inv in REF; inv REF; auto.
    - apply ssim_ret_l_inv in REF.
      destruct REF as (?&?&?&?); subst.
      unfold raise in H.
      apply trans_trigger_inv in H.
      destruct H as [[] _].
  }
Qed.

Lemma load_fails_spec :
  forall T m k,
    IM.find k m = None <->
      @ssim Effin Effin void1 _ T _ eq
        (raise "Load from unallocated address.")
        (handle_mem_spec _ (LoadE k) m).
Proof.
  intros T m k.
  split.
  { intros LUP.
    cbn; rewrite LUP.
    apply spec_refines_raise.
  }
  { intros REF.
    cbn in REF.
    destruct (IM.find k m) eqn:LUP; auto.
    apply ssim_raise_ret in REF.
    contradiction.
  }
Qed.

Lemma store_succeeds_spec :
  forall m m' k v,
    IM.mem k m = true /\
      m' = IM.add k v m
    <->
      @ssim Effin Effin void1 _ _ _ eq
        (ret (m', tt))
        (handle_mem_spec _ (StoreE k v) m).

  (*

      @refines
        Effin Effin (memory * _) (memory * _)
        in_rel
        in_post_rel
        (fun r1 r2 =>
           r1 = r2 /\
             fst r2 = m'
        ) *)
Proof.
  intros m m' k v.
  split.
  { intros [MEM ADD]; subst.
    cbn.
    apply IM.mem_2 in MEM.
    destruct MEM.
    erewrite IM.find_1; eauto.
    apply ssim_ret.
    auto.
  }
  { intros REF.
    cbn in REF.
    destruct (IM.find k m) eqn:LUP; subst.
    - apply ssim_ret_inv in REF.
      apply val_eq_inv in REF.
      inv REF.
      split; auto.
      apply IM.mem_1.
      exists n.
      eapply IM.find_2; eauto.
    - apply ssim_ret_raise in REF; contradiction.
  }
Qed.

Lemma store_fails_spec :
  forall T m k v,
    IM.find k m = None
    <->
      @ssim Effin Effin void1 _ T _ eq
        (raise "Store to unallocated address.")
        (handle_mem_spec _ (StoreE k v) m).
Proof.
  intros T m k v.
  split.
  { intros LUP.
    cbn; rewrite LUP.
    apply spec_refines_raise.
  }
  { intros REF.
    cbn in REF.
    destruct (IM.find k m) eqn:LUP; auto.
    apply ssim_raise_ret in REF.
    contradiction.
  }
Qed.

Lemma alloc_spec :
  forall (m m' : memory) k,
    IM.mem k m = false /\
      m' = IM.add k 0 m
    <->
      @ssim Effin Effin void1 _ _ _ eq
        (ret (m', k))
        (handle_mem_spec Z (AllocE) m).
(* (fun r1 r2 =>
        r1 = r2 /\
          let m2 := fst r2 in
          let k2 := snd r2 in
          k2 = k /\
            m2 = add k 0 m) *)
Proof.
  intros m m' k.
  split.
  { intros [NMEM ADD].
    cbn; unfold do_alloc.
    rewrite bind_branch.
    eapply ssim_br_r.
    Unshelve.
    2: {
      exists k.
      destruct (IM.mem (elt:=nat) k (IM.empty nat)) eqn:MEM; auto.
    }

    cbn; subst.
    apply ssim_ret.
    reflexivity.
  }
  { intros REF.
    cbn in *.
    unfold do_alloc in *.
    apply ssim_ret_l_inv in REF.
    destruct REF as (?&?&?&?); subst.
    rewrite bind_branch in H.
    apply trans_br_inv in H.
    destruct H as (?&?).
    apply trans_ret_inv in H.
    destruct H.
    apply val_eq_inv in H0. inv H0.
    destruct x; subst; cbn in *.
    eauto.
  }
Qed.

Lemma alloc_spec_exists :
  forall (m : memory),
  exists m' k,
    IM.mem k m = false /\
      m' = IM.add k 0 m /\
      @ssim Effin Effin void1 _ _ _ eq
        (ret (m', k))
        (handle_mem_spec Z (AllocE) m).
(* (fun r1 r2 =>
         r1 = r2 /\
           fst r2 = m' /\
           snd r2 = k) *)
Proof.
  intros m.
  destruct (IM.mem (next_key m) m) eqn:MEM; auto.
  apply IM.mem_2 in MEM.
  apply next_key_correct in MEM.
  lia.

  exists (IM.add (next_key m) 0 m), (next_key m).
  split; auto.
  split; auto.

  cbn.
  unfold do_alloc.
  rewrite bind_branch.
  
  cbn.
  eapply ssim_br_r.
  Unshelve.
  2: {
    exists (next_key m); auto.
  }

  cbn.
  apply ssim_ret.
  reflexivity.
Qed.

Definition double_alloc : ctree MemE void1 bool
  := k <- trigger AllocE;;
     p <- trigger AllocE;;
     ret (Z.eqb k p).


Lemma next_key_not_member :
  forall {A} (m : IM.t A),
    IM.mem (next_key m) m = false.
Proof.
  intros A m.
  destruct (IM.mem (next_key m) m) eqn:MEM; auto.
  apply IM.mem_2 in MEM.
  apply next_key_correct in MEM.
  lia.
Qed.

Lemma alloc_sigma :
  forall {A} (m : IM.t A),
    {k | IM.mem k m = false}.
Proof.
  intros A m.
  exists (next_key m).
  eapply next_key_not_member.
Defined.


(* Definition interp_state {E B M S} *)
(*            {FM : Functor M} {MM : Monad M} *)
(*            {IM : MonadIter M} *)
(*            (h : E ~> Monads.stateT S M) : *)
(*   ctree E B ~> Monads.stateT S M := interp h. *)

Import Monads.

#[global] Instance ctree_monad {E B} : Monad (ctree E B).
split.
- intros.
  apply ret; apply X.
- intros t u X X0.
  eapply bind.
  apply X.
  apply X0.
Defined.

#[global] Instance MonadStepState {S M} `{HM : Monad M} `{MS : MonadStep M} : MonadStep (Monads.stateT S M).
red.
intros s.
eapply bind.
apply mstep.
intros _.
apply (ret (s, tt)).
Defined.

#[global] Instance MonadStuckState {S M} `{HM : Monad M} `{MS : MonadStuck M} : MonadStuck (Monads.stateT S M).
red.
intros X.
red.
intros s.
apply mstuck.
Defined.

#[global] Instance MonadBrState {B S M} `{HM : Monad M} `{MB : MonadBr B M} : MonadBr B (stateT S M).
red.
intros X b s.
apply mbr in b.
eapply fmap; cycle 1; eauto.
Defined.

Lemma alloc_disjoint :
  exists m,
    @ssim Effin Effin void1 Bspec (memory * bool)%type (memory * bool)%type eq
      (ret (m, false))
      (interp_state handle_mem_spec double_alloc (IM.empty _)).
Proof.
  eexists.
  unfold double_alloc.
  repeat setoid_rewrite interp_state_bind.
  setoid_rewrite interp_state_trigger.
  repeat setoid_rewrite bind_bind.
  rewrite bind_branch.
  apply ssim_br_r with (x:=alloc_sigma _); cbn.
  rewrite bind_ret_l.
  rewrite bind_guard.
  apply ssim_guard_r.
  rewrite bind_ret_l.
  rewrite bind_branch.
  apply ssim_br_r with (x:=alloc_sigma _); cbn.
  rewrite bind_ret_l.
  rewrite bind_guard.
  apply ssim_guard_r.
  rewrite bind_ret_l.
  rewrite interp_state_ret; cbn.
  apply ssim_ret.
  reflexivity.
Qed.

Lemma mem_add_eq {a}: forall k v (m: IM.t a),
    IM.mem k (IM.add k v m) = true.
Proof using.
  intros.
  cbn.
  apply IM.Raw.Proofs.mem_1.
  apply IM.Raw.Proofs.add_bst, IM.is_bst.
  rewrite IM.Raw.Proofs.add_in; auto.
Qed.

Lemma find_add_eq {a}: forall k v (m: IM.t a),
    IM.find k (IM.add k v m) = Some v.
Proof using.
  intros.
  apply IM.find_1.
  apply IM.add_1; auto.
Qed.

Lemma mem_add_neq {a}: forall k1 k2 v (m: IM.t a),
    k1 <> k2 ->
    IM.mem k1 (IM.add k2 v m) = IM.mem k1 m.
Proof using.
  intros.
  cbn.
Admitted.

Lemma alloc_disjoint' :
  forall m,
    @ssim Effin Effin Bspec Bexec bool bool eq
      (fmap snd (interp_state handle_mem_spec double_alloc m))
      (ret false).
Proof.
  intros m.
  Opaque IM.mem.
  setoid_rewrite interp_state_bind.
  setoid_rewrite interp_state_bind.
  setoid_rewrite interp_state_trigger.
  repeat setoid_rewrite map_bind.
  cbn.
  repeat setoid_rewrite bind_bind; cbn.
  rewrite bind_branch.
  apply ssim_br_l.
  intros [k KSPEC].

  rewrite bind_ret_l; cbn.
  rewrite bind_guard.
  apply ssim_guard_l.
  rewrite bind_ret_l; cbn.

  rewrite bind_branch.
  apply ssim_br_l.
  intros [p PSPEC].

  rewrite bind_ret_l; cbn.
  rewrite bind_guard.
  apply ssim_guard_l.
  rewrite bind_ret_l; cbn.

  rewrite interp_state_ret.
  rewrite map_ret.
  cbn.

  destruct (Z.eq_dec k p) as [EQ | NEQ]; cbn in *; subst.
  rewrite mem_add_eq in PSPEC; try discriminate.

  assert ((k =? p)%Z = false) by lia.
  rewrite H.
  apply ssim_ret.
  reflexivity.
Qed.


Lemma double_alloc_spec :
  forall m m' b,
    (b = false /\
       exists k1 k2,
         m' = IM.add k2 0 (IM.add k1 0 m) /\
           k1 <> k2 /\
           IM.mem k1 m = false /\
           IM.mem k2 m = false) ->
    @ssim Effin Effin void1 Bspec (memory * bool)%type (memory * bool)%type eq
      (ret (m', b))
      (interp_state handle_mem_spec double_alloc m).
Proof.
  intros m m' b.
  { intros [B K].
    destruct K as (k1&k2&M'&NK1K2&MEM1&MEM2).
    cbn.
    repeat setoid_rewrite interp_state_bind.
    repeat setoid_rewrite interp_state_trigger.
    repeat setoid_rewrite bind_bind.

    rewrite bind_branch.
    apply ssim_br_r with (x:=exist _ k1 MEM1); cbn.
    rewrite bind_ret_l.
    rewrite bind_guard.
    eapply ssim_guard_r.
    repeat setoid_rewrite bind_ret_l.

    rewrite bind_branch; cbn.
    assert (IM.mem (elt:=nat) k2 (IM.add k1 0 m) = false) as MEM2'.
    rewrite mem_add_neq; eauto.

    apply ssim_br_r with (x:=exist _ k2 MEM2'); cbn.
    rewrite bind_guard.
    apply ssim_guard_r.
    rewrite bind_ret_l.
    rewrite interp_state_ret.
    cbn.
    subst.
    apply ssim_ret.

    assert ((k1 =? k2)%Z = false) by lia.
    rewrite H.
    reflexivity.
  }
Qed.

Definition store_prog (v : nat) : ctree MemE Bspec nat :=
  k <- trigger AllocE;;
  trigger (StoreE k v);;
  trigger (LoadE k).

Lemma alloc_lemma :
  forall m m_final k,
    IM.mem k m = false ->
    m_final = IM.add k 0 m ->
    @ssim Effin Effin Bspec Bspec (memory * IM.key)%type (memory * IM.key)%type eq
      (ret (m_final, k))
      (interp_state handle_mem_spec (trigger AllocE : ctree MemE Bspec Z) m).
Proof.
  intros m m_final k MEM FINAL.
  setoid_rewrite interp_state_trigger.
  cbn.

  unfold do_alloc.
  rewrite bind_branch.
  rewrite bind_br.
  eapply ssim_br_r with (x:=exist _ k MEM); cbn.
  rewrite bind_ret_l.
  apply ssim_guard_r.
  apply ssim_ret.
  subst.
  reflexivity.
Qed.

Lemma alloc_lemma' :
  forall m,
    @ssim Effin Effin Bspec Bspec (memory * IM.key)%type (memory * IM.key)%type eq
      (ret (IM.add (next_key m) 0 m, next_key m))
      (interp_state handle_mem_spec (trigger AllocE : ctree MemE Bspec Z) m).
Proof.
  intros m.
  eapply alloc_lemma.
  apply next_key_not_member.
  reflexivity.
Qed.

Lemma store_succ_lemma :
  forall m m_final k v,
    IM.mem k m = true ->
    m_final = IM.add k v m ->
    (interp_state (@handle_mem_spec Effin _) (trigger (StoreE k v) : ctree MemE Bspec unit) m) ~
      (ret (m_final, tt) : ctree Effin Bspec (memory * unit)%type).
Proof.
  intros m m_final k v MEM FINAL.
  setoid_rewrite interp_state_trigger.
  cbn.
  apply IM.mem_2 in MEM.
  destruct MEM.
  erewrite IM.find_1; eauto.
  rewrite bind_ret_l.

  apply sb_guard_l.
  subst.
  reflexivity.
Qed.

Lemma load_succ_lemma :
  forall m k v,
    IM.find k m = Some v ->
    (interp_state (@handle_mem_spec Effin _) (trigger (LoadE k) : ctree MemE Bspec nat) m) ~
      (ret (m, v) : ctree Effin Bspec (memory * nat)%type).
Proof.
  intros m k v LUP.
  setoid_rewrite interp_state_trigger.
  cbn.
  rewrite LUP.
  rewrite bind_ret_l.
  apply sb_guard_l.
  reflexivity.
Qed.

Ltac inj_pair2_existT :=
  repeat
      match goal with
      | H : _ |- _ => apply Eqdep.EqdepTheory.inj_pair2 in H
      end.

Ltac subst_existT :=
  inj_pair2_existT; subst.

(* #[global] Instance Reflexive_update_val_rel {E X} L R0 : *)
(*   Reflexive L -> *)
(*   Reflexive R0 -> *)
(*   Reflexive (@update_val_rel E E X X L R0). *)
(* Proof. *)
(*   red. intros. destruct x. *)
(*   1-2: constructor; eauto; intros VAL; inversion VAL. *)
(*   assert (X = X0 \/ X <> X0) as [EQ | NEQ] by admit. *)
(*   - subst. *)
(*     apply update_Val. *)
(*     reflexivity. *)
(*   - constructor. *)
(*     + intros VAL. *)
(*       inv VAL. *)
(*       subst_existT. *)
(*     inv VAL. *)
(* Qed. *)

Lemma raise_bind :
  forall E `{FailureE -< E} B R1 R2 R3 msg (k : R1 -> ctree E B R2),
    ((raise msg : ctree E B R1) >>= k) ~ (raise msg : ctree E B R3).
Proof.
  intros E H B R1 R2 R3 msg k.
  cbn.
  unfold raise.
  rewrite bind_bind.
  apply sbisim_clo_bind with (R0:=eq).
  - eapply Lequiv_sbisim; [| reflexivity].
    symmetry.
    apply update_val_rel_eq.
  - intros [].
Qed.

Lemma store_fail_lemma :
  forall m k v,
    IM.mem k m = false ->
    (interp_state handle_mem_spec (trigger (StoreE k v) : ctree MemE Bspec unit) m) ~
      (raise "Store to unallocated address." : ctree Effin Bspec (memory * unit)%type).
Proof.
  intros m k v MEM.
  setoid_rewrite interp_state_trigger.
  cbn.
  destruct (IM.find k m) eqn:LUP.
  - exfalso.
    apply IM.find_2 in LUP.
    assert (IM.In k m) as IN.
    exists n. apply LUP.
    apply IM.mem_1 in IN.
    rewrite MEM in IN; discriminate.
  - rewrite raise_bind.
    reflexivity.
Qed.

Lemma load_fails_lemma :
  forall m k,
    IM.mem k m = false ->
    (interp_state handle_mem_spec (trigger (LoadE k) : ctree MemE Bspec nat) m) ~
      (raise "Load from unallocated address." : ctree Effin Bspec (memory * unit)%type).
Proof.
  intros m k MEM.
  setoid_rewrite interp_state_trigger.
  cbn.
  destruct (IM.find k m) eqn:LUP.
  - exfalso.
    apply IM.find_2 in LUP.
    assert (IM.In k m) as IN.
    exists n. apply LUP.
    apply IM.mem_1 in IN.
    rewrite MEM in IN; discriminate.
  - cbn.
    (* Why can't I just rewrite? *)
    pose proof (@raise_bind Effin _ Bspec (memory * nat)%type (memory * nat)%type (memory * unit)%type "Load from unallocated address." (fun x => Guard (Ret x))).
    cbn in *.
    apply H.
Qed.

Variant ForallE : Type -> Type :=
  | Spec_forall A : ForallE A.

Definition forall_spec {E} (A : Type) : ctree E ForallE A :=
  Br (Spec_forall A) (fun (a : A) => Ret a).

Lemma blah :
  @ssim Effin Effin void1 ForallE nat nat eq
  (ret 1) (forall_spec nat).
Proof.
  unfold forall_spec.
  apply ssim_br_r with (x:=1).
  apply ssim_ret.
  reflexivity.
Qed.

(* This doesn't work. The thing on the right is an empty set, and the
refinement relation doesn't hold vacuously *)
Lemma ub_test :
  @ssim Effin Effin ForallE ForallE nat nat eq
    (ret 1) (x <- forall_spec void;; ret 9).
Proof.
  unfold forall_spec.
  cbn.
  rewrite bind_br.
  (* No way to instantiate x *)
  Fail apply ssim_br_r.
Abort.

(* This *does* work. The smaller set on the left is empty, and therefore a
   subset of the thing on the right. *)
Lemma ub_test_l :
  @ssim Effin Effin ForallE ForallE nat nat eq
    (x <- forall_spec void;; ret 9) (ret 1).
Proof.
  unfold forall_spec.
  cbn.
  rewrite bind_br.
  apply ssim_br_l.
  intros [].
Qed.

Lemma blah' :
  @ssim Effin Effin ForallE ForallE nat nat eq
    (forall_spec nat)
    (forall_spec nat).
Proof.
  unfold forall_spec.
  apply ssim_br_id.
  intros x.
  apply ssim_ret; reflexivity.
Qed.

Lemma store_forward_with_rewrites' :
  forall m v,
    @ssim Effin Effin Bspec Bspec _ _ eq
      (ret v)
      (fmap snd (interp_state handle_mem_spec (store_prog v) m)).
Proof.
  intros m v.
  unfold store_prog.
  cbn.
  repeat setoid_rewrite interp_state_bind.
  repeat setoid_rewrite bind_bind.

  rewrite <- alloc_lemma'; cbn.
  rewrite bind_ret_l; cbn.
  rewrite store_succ_lemma; cbn; eauto.
  2: apply mem_add_eq.

  rewrite bind_ret_l; cbn.
  rewrite load_succ_lemma; [cbn; eauto | apply find_add_eq].

  rewrite bind_ret_l.
  cbn.
  reflexivity.
Qed.

Hint Rewrite
  @bind_bind
  @bind_branch
  @bind_vis
  @bind_ret_l
  @interp_state_bind
  @interp_state_trigger
  alloc_lemma'
  store_succ_lemma
  load_succ_lemma : SolveMem.

Hint Resolve
  @bind_bind
  @bind_vis
  @bind_ret_l
  @interp_state_bind
  @interp_state_trigger
  @ssim_br_r
  @ssim_br_l
  @ssim_guard_r
  @ssim_guard_l
  @ssim_ret
  alloc_lemma'
  store_succ_lemma
  load_succ_lemma 
  mem_add_eq
  find_add_eq : SolveMem.

Ltac solve_refines :=
  cbn;
  repeat setoid_rewrite interp_state_bind;
  cbn;
  repeat (autorewrite with SolveMem; cbn);
  eauto with SolveMem.

Lemma store_forward_with_rewrites'' :
  forall m v,
    @ssim Effin Effin Bspec Bspec _ _ eq
      (ret v)
      (fmap snd (interp_state handle_mem_spec (store_prog v) m)).
Proof.
  intros m v.
  cbn.
  unfold CTree.map.
  unfold store_prog.
  solve_refines.
  unfold do_alloc.
  rewrite bind_bind.
  rewrite bind_branch.
  eapply ssim_br_r.
  cbn.
  rewrite bind_ret_l.
  rewrite bind_guard.
  apply ssim_guard_r.
  solve_refines.
  Unshelve.
  apply alloc_sigma.
Qed.

Lemma store_forward_with_rewrites :
  forall m v,
    @ssim Effin Effin Bspec Bspec _ _ eq
      (fmap snd (interp_state handle_mem_spec (store_prog v) m))
      (ret v).
Proof.
  intros m v.
  cbn.
  unfold CTree.map.
  cbn.

  Opaque IM.mem IM.find IM.add.
  setoid_rewrite interp_state_bind.
  setoid_rewrite interp_state_bind.
  cbn.
  repeat setoid_rewrite bind_bind.
  cbn.

  (* This first alloc is hard to rewrite :|

     alloc is generally not a refinement of a ret because it can
     return many values. The overall lemma holds, however, because
     this detail is hidden from the outside.
   *)
  setoid_rewrite interp_state_trigger at 1.
  cbn.
  unfold do_alloc.
  repeat rewrite bind_bind.
  rewrite bind_branch.
  apply ssim_br_l.
  intros [k m'].
  solve_refines.
  rewrite bind_guard.
  apply ssim_guard_l.
  solve_refines.
Qed.


(* (* May need complete simulations to break this proof up like this... May be resolved in askrcv ctrees branch *) *)
(* Lemma store_forward_stronger : *)
(*   forall m v, *)
(*     (ret v : ctree Effin Bspec nat) ~ *)
(*       (fmap snd (interp_state (@handle_mem_spec Effin _) (store_prog v) m)). *)
(* Proof. *)
(*   intros m v. *)
(*   sbisim *)
(*   rewrite store_forward_with_rewrites'. *)
(*   split. *)
(*   apply store_forward_with_rewrites. *)
(*   apply store_forward_with_rewrites'. *)
(* Qed. *)
