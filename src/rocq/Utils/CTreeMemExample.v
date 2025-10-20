From Paco Require Import paco.

From CTree Require Import
  CTree CTreeDefinitions Eq Fold.

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

#[global] Instance MonadStepState {S M} `{HM : Monad M} `{MS : MonadStep M} : MonadStep (stateT S M).
red.
intros s.
eapply bind.
apply mstep.
intros _.
apply (ret (s, tt)).
Defined.

#[global] Instance MonadStuckState {S M} `{HM : Monad M} `{MS : MonadStuck M} : MonadStuck (stateT S M).
red.
intros X.
red.
intros s.
apply mstuck.
Defined.

#[global] Instance MonadBrState {B S M} `{HM : Monad M} `{MB : MonadBr B M} `{FB : Functor B}: MonadBr B (stateT S M).
red.
intros X b s.
apply mbr.
eapply fmap in b.
apply b.
intros x.
apply (s, x).
Defined.

Definition interp_state {E B M S}
  {FB : Functor B}
  {FM : Functor M} {MM : Monad M}
  {IM : MonadIter M}
  {MSTUCK : MonadStuck M}
  {MSTEP : MonadStep M}
  {MBR : MonadBr B M}
  (h : E ~> stateT S M) :
  ctree E B ~> stateT S M := interp h.

Arguments interp_state {E B M S FB FM MM IM MSTUCK MSTEP MBR} h [T].

(* Definition _interp_state {E F C D S R} *)
(*            (f : E ~> stateT S (ctree F D)) (ot : ctreeF E C R _) *)
(*   : stateT S (ctree F D) R := *)
(*   fun s => *)
(*     match ot with *)
(*     | RetF r => Ret (s, r) *)
(*     | StuckF => Stuck *)
(*     | StepF t => StepF  *)
(*     | GuardF t => _ *)
(*     | VisF X e k => _ *)
(*     | BrF X c k => _ *)
(*     end. *)
(*   match ot with *)
(*   | RetF r => Ret (s, r) *)
(*   | TauF t => Tau (interp_state f t s) *)
(*   | VisF e k => f _ e s >>= (fun sx => Tau (interp_state f (k (snd sx)) (fst sx))) *)
(*   end. *)

(* Lemma unfold_interp_state {E F S R} (h : E ~> Monads.stateT S (itree F)) *)
(*       (t : itree E R) s : *)
(*     eq_itree eq *)
(*       (interp_state h t s) *)
(*       (_interp_state h (observe t) s). *)
(* Proof. *)
(*   unfold interp_state, interp, Basics.iter, MonadIter_stateT0, Basics.iter, MonadIter_itree; cbn. *)
(*   rewrite unfold_iter; cbn. *)
(*   destruct observe; cbn. *)
(*   - rewrite 2 bind_ret_l. reflexivity. *)
(*   - rewrite 2 bind_ret_l. *)
(*     reflexivity. *)
(*   - rewrite bind_map, bind_bind; cbn. setoid_rewrite bind_ret_l. *)
(*     apply eqit_bind; reflexivity. *)
(* Qed. *)

(* #[global] *)
(* Instance eq_itree_interp_state {E F S R} (h : E ~> Monads.stateT S (itree F)) : *)
(*   Proper (eq_itree eq ==> eq ==> eq_itree eq) *)
(*          (@interp_state _ _ _ _ _ _ h R). *)
(* Proof. *)
(*   revert_until R. *)
(*   ginit. pcofix CIH. intros h x y H0 x2 _ []. *)
(*   rewrite !unfold_interp_state. *)
(*   punfold H0; repeat red in H0. *)
(*   destruct H0; subst; pclearbot; try discriminate; cbn. *)
(*   - gstep; constructor; auto. *)
(*   - gstep; constructor; auto with paco. *)
(*   - guclo eqit_clo_bind. econstructor. *)
(*     + reflexivity. *)
(*     + intros [] _ []. gstep; constructor; auto with paco itree. *)
(* Qed. *)

(* Lemma interp_state_ret {E F : Type -> Type} {R S : Type} *)
(*       (f : forall T, E T -> S -> itree F (S * T)%type) *)
(*       (s : S) (r : R) : *)
(*   (interp_state f (Ret r) s) ≅ (Ret (s, r)). *)
(* Proof. *)
(*   rewrite itree_eta. reflexivity. *)
(* Qed. *)

(* Lemma interp_state_vis {E F : Type -> Type} {S T U : Type} *)
(*       (e : E T) (k : T -> itree E U) (h : E ~> Monads.stateT S (itree F)) (s : S) *)
(*   : interp_state h (Vis e k) s *)
(*   ≅ h T e s >>= fun sx => Tau (interp_state h (k (snd sx)) (fst sx)). *)
(* Proof. *)
(*   rewrite unfold_interp_state; reflexivity. *)
(* Qed. *)

(* Lemma interp_state_tau {E F : Type -> Type} S {T : Type} *)
(*       (t : itree E T) (h : E ~> Monads.stateT S (itree F)) (s : S) *)
(*   : interp_state h (Tau t) s ≅ Tau (interp_state h t s). *)
(* Proof. *)
(*   rewrite unfold_interp_state; reflexivity. *)
(* Qed. *)

(* Lemma interp_state_trigger_eqit {E F : Type -> Type} {R S : Type} *)
(*       (e : E R) (f : E ~> Monads.stateT S (itree F)) (s : S) *)
(*   : (interp_state f (ITree.trigger e) s) ≅ (f _ e s >>= fun x => Tau (Ret x)). *)
(* Proof. *)
(*   unfold ITree.trigger. rewrite interp_state_vis. *)
(*   eapply eqit_bind; try reflexivity. *)
(*   intros []. rewrite interp_state_ret. reflexivity. *)
(* Qed. *)

(* Lemma interp_state_trigger {E F : Type -> Type} {R S : Type} *)
(*       (e : E R) (f : E ~> Monads.stateT S (itree F)) (s : S) *)
(*   : interp_state f (ITree.trigger e) s ≈ f _ e s. *)
(* Proof. *)
(*   unfold ITree.trigger. rewrite interp_state_vis. *)
(*   match goal with *)
(*     |- ?y ≈ ?x => remember y; rewrite <- (bind_ret_r x); subst *)
(*   end. *)
(*   eapply eqit_bind; try reflexivity. *)
(*   intros []; rewrite interp_state_ret,tau_eutt. *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma interp_state_bind {E F : Type -> Type} {A B S : Type} *)
(*       (f : forall T, E T -> S -> itree F (S * T)%type) *)
(*       (t : itree E A) (k : A -> itree E B) *)
(*       (s : S) : *)
(*   (interp_state f (t >>= k) s) *)
(*     ≅ *)
(*   (interp_state f t s >>= fun st => interp_state f (k (snd st)) (fst st)). *)
(* Proof. *)
(*   revert t k s. *)
(*   ginit. pcofix CIH. *)
(*   intros t k s. *)
(*   rewrite unfold_bind. *)
(*   rewrite (unfold_interp_state f t). *)
(*   destruct (observe t). *)
(*   - cbn. rewrite !bind_ret_l. cbn. *)
(*     apply reflexivity. *)
(*   - cbn. rewrite !bind_tau, interp_state_tau. *)
(*     gstep. econstructor. gbase. apply CIH. *)
(*   - cbn. rewrite interp_state_vis, bind_bind. *)
(*     guclo eqit_clo_bind. econstructor. *)
(*     + reflexivity. *)
(*     + intros u2 ? []. *)
(*       rewrite bind_tau. *)
(*       gstep; constructor. *)
(*       ITree.fold_subst. *)
(*       auto with paco. *)
(* Qed. *)

(* #[global] *)
(* Instance eutt_interp_state {E F: Type -> Type} {S : Type} *)
(*          (h : E ~> Monads.stateT S (itree F)) R RR : *)
(*   Proper (eutt RR ==> eq ==> eutt (prod_rel eq RR)) (@interp_state E (itree F) S _ _ _ h R). *)
(* Proof. *)
(*   repeat intro. subst. revert_until RR. *)
(*   einit. ecofix CIH. intros. *)

(*   rewrite !unfold_interp_state. punfold H0. red in H0. *)
(*   induction H0; intros; subst; simpl; pclearbot. *)
(*   - eret. *)
(*   - etau. *)
(*   - ebind. econstructor; [reflexivity|]. *)
(*     intros; subst. *)
(*     etau. ebase. *)
(*   - rewrite tau_euttge, unfold_interp_state; eauto. *)
(*   - rewrite tau_euttge, unfold_interp_state; eauto. *)
(* Qed. *)

(* #[global] *)
(* Instance eutt_interp_state_eq {E F: Type -> Type} {S : Type} *)
(*          (h : E ~> Monads.stateT S (itree F)) R : *)
(*   Proper (eutt eq ==> eq ==> eutt eq) (@interp_state E (itree F) S _ _ _ h R). *)
(* Proof. *)
(*   repeat intro. subst. revert_until R. *)
(*   einit. ecofix CIH. intros. *)

(*   rewrite !unfold_interp_state. punfold H0. red in H0. *)
(*   induction H0; intros; subst; simpl; pclearbot. *)
(*   - eret. *)
(*   - etau. *)
(*   - ebind. econstructor; [reflexivity|]. *)
(*     intros; subst. *)
(*     etau. ebase. *)
(*   - rewrite tau_euttge, unfold_interp_state; eauto. *)
(*   - rewrite tau_euttge, unfold_interp_state; eauto. *)
(* Qed. *)


(* Lemma eutt_interp_state_aloop {E F S I I' A A'} *)
(*       (RA : A -> A' -> Prop) (RI : I -> I' -> Prop) *)
(*       (RS : S -> S -> Prop) *)
(*       (h : E ~> Monads.stateT S (itree F)) *)
(*       (t1 : I -> itree E (I + A)) *)
(*       (t2 : I' -> itree E (I' + A')): *)
(*   (forall i i' s1 s2, RS s1 s2 -> RI i i' -> *)
(*      eutt (prod_rel RS (sum_rel RI RA)) *)
(*                      (interp_state h (t1 i) s1) *)
(*                      (interp_state h (t2 i') s2)) -> *)
(*   (forall i i' s1 s2, RS s1 s2 -> RI i i' -> *)
(*      eutt (fun a b => RS (fst a) (fst b) /\ RA (snd a) (snd b)) *)
(*           (interp_state h (ITree.iter t1 i) s1) *)
(*           (interp_state h (ITree.iter t2 i') s2)). *)
(* Proof. *)
(*   intro Ht. *)
(*   einit. ecofix CIH. intros. *)
(*   rewrite 2 unfold_iter. *)
(*   rewrite 2 interp_state_bind. *)
(*   ebind; econstructor. *)
(*   - eapply Ht; auto. *)
(*   - intros [s1' i1'] [s2' i2'] [? []]; cbn. *)
(*     + rewrite 2 interp_state_tau. auto with paco. *)
(*     + rewrite 2 interp_state_ret. auto with paco. *)
(* Qed. *)

(* Lemma eutt_interp_state_iter {E F S A A' B B'} *)
(*       (RA : A -> A' -> Prop) (RB : B -> B' -> Prop) *)
(*       (RS : S -> S -> Prop) *)
(*       (h : E ~> Monads.stateT S (itree F)) *)
(*       (t1 : A -> itree E (A + B)) *)
(*       (t2 : A' -> itree E (A' + B')) : *)
(*   (forall ca ca' s1 s2, RS s1 s2 -> *)
(*                         RA ca ca' -> *)
(*      eutt (prod_rel RS (sum_rel RA RB)) *)
(*           (interp_state h (t1 ca) s1) *)
(*           (interp_state h (t2 ca') s2)) -> *)
(*   (forall a a' s1 s2, RS s1 s2 -> RA a a' -> *)
(*      eutt (fun a b => RS (fst a) (fst b) /\ RB (snd a) (snd b)) *)
(*           (interp_state h (iter (C := ktree _) t1 a) s1) *)
(*           (interp_state h (iter (C := ktree _) t2 a') s2)). *)
(* Proof. *)
(*   apply eutt_interp_state_aloop. *)
(* Qed. *)

(* Lemma eutt_eq_interp_state_iter {E F S} (f: E ~> stateT S (itree F)) {I A} *)
(*     (t : I -> itree E (I + A)): *)
(*   forall i s, interp_state f (ITree.iter t i) s ≈ *)
(*     Basics.iter (fun i => interp_state f (t i)) i s. *)
(* Proof. *)
(*   unfold Basics.iter, MonadIter_stateT0, Basics.iter, MonadIter_itree in *; cbn. *)
(*   ginit. gcofix CIH; intros i s. *)
(*   rewrite 2 unfold_iter; cbn. *)
(*   rewrite !bind_bind. *)
(*   setoid_rewrite bind_ret_l. *)
(*   rewrite interp_state_bind. *)
(*   guclo eqit_clo_bind; econstructor; eauto. reflexivity. *)
(*   intros [s' []] _ []; cbn. *)
(*   - rewrite interp_state_tau. *)
(*     gstep; constructor. *)
(*     auto with paco. *)
(*   - rewrite interp_state_ret; apply reflexivity. *)
(* Qed. *)

(* Lemma eutt_interp_state_loop {E F S A B C} (RS : S -> S -> Prop) *)
(*       (h : E ~> Monads.stateT S (itree F)) *)
(*       (t1 t2 : C + A -> itree E (C + B)) : *)
(*   (forall ca s1 s2, RS s1 s2 -> *)
(*      eutt (fun a b => RS (fst a) (fst b) /\ snd a = snd b) *)
(*           (interp_state h (t1 ca) s1) *)
(*           (interp_state h (t2 ca) s2)) -> *)
(*   (forall a s1 s2, RS s1 s2 -> *)
(*      eutt (fun a b => RS (fst a) (fst b) /\ snd a = snd b) *)
(*           (interp_state h (loop (C := ktree E) t1 a) s1) *)
(*           (interp_state h (loop (C := ktree E) t2 a) s2)). *)
(* Proof. *)
(*   intros. *)
(*   unfold loop, bimap, Bimap_Coproduct, case_, Case_Kleisli, Function.case_sum, id_, Id_Kleisli, cat, Cat_Kleisli, inr_, Inr_Kleisli, inl_, Inl_Kleisli, lift_ktree_; cbn. *)
(*   rewrite 2 bind_ret_l. *)
(*   eapply (eutt_interp_state_iter eq eq); auto; intros. *)
(*   rewrite 2 interp_state_bind. *)
(*   subst. *)
(*   eapply eutt_clo_bind; eauto. *)
(*   intros. *)
(*   cbn in H2; destruct H2 as [H21 H22]. *)
(*   destruct (snd u1); rewrite <- H22. *)
(*   - rewrite bind_ret_l, 2 interp_state_ret. *)
(*     pstep. *)
(*     constructor. *)
(*     split; cbn; auto using H21. *)
(*   - rewrite bind_ret_l, 2 interp_state_ret. pstep. constructor. *)
(*     split; cbn; auto using H21. *)
(* Qed. *)

(* (* SAZ: These are probably too specialized. *) *)
(* Definition state_eq {E S X} *)
(*   : (stateT S (itree E) X) -> (stateT S (itree E) X) -> Prop := *)
(*   fun t1 t2 => forall s, eq_itree eq (t1 s) (t2 s). *)

(* Lemma interp_state_iter {E F } S (f : E ~> stateT S (itree F)) {I A} *)
(*       (t  : I -> itree E (I + A)) *)
(*       (t' : I -> stateT S (itree F) (I + A)) *)
(*       (EQ_t : forall i, state_eq (State.interp_state f (t i)) (t' i)) *)
(*   : forall i, state_eq (State.interp_state f (ITree.iter t i)) *)
(*                   (Basics.iter t' i). *)
(* Proof. *)
(*   unfold Basics.iter, MonadIter_stateT0, Basics.iter, MonadIter_itree in *; cbn. *)
(*   ginit. pcofix CIH; intros i s. *)
(*   rewrite 2 unfold_iter; cbn. *)
(*   rewrite !bind_bind. *)
(*   setoid_rewrite bind_ret_l. *)
(*   rewrite interp_state_bind. *)
(*   guclo eqit_clo_bind; econstructor; eauto. *)
(*   - apply EQ_t. *)
(*   - intros [s' []] _ []; cbn. *)
(*     + rewrite interp_state_tau. *)
(*       gstep; constructor. *)
(*       auto with paco. *)
(*     + rewrite interp_state_ret; apply reflexivity. *)
(* Qed. *)

(* Lemma interp_state_iter' {E F } S (f : E ~> stateT S (itree F)) {I A} *)
(*       (t  : I -> itree E (I + A)) *)
(*   : forall i, state_eq (State.interp_state f (ITree.iter t i)) *)
(*                        (Basics.iter (fun i => State.interp_state f (t i)) i). *)
(* Proof. *)
(*   eapply interp_state_iter. *)
(*   intros i. *)
(*   red. reflexivity. *)
(* Qed. *)

(* Lemma interp_state_iter'_eutt {E F S} (f: E ~> stateT S (itree F)) {I A} *)
(*     (t : I -> itree E (I + A)) *)
(*     (t': I -> stateT S (itree F) (I + A)) *)
(*     (Heq: forall i s, interp_state f (t i) s ≈ (t' i) s): *)
(*   forall i s, interp_state f (ITree.iter t i) s ≈ Basics.iter t' i s. *)
(* Proof. *)
(*   unfold Basics.iter, MonadIter_stateT0, Basics.iter, MonadIter_itree in *; cbn. *)
(*   ginit. gcofix CIH; intros i s. *)
(*   rewrite 2 unfold_iter; cbn. *)
(*   rewrite !bind_bind. *)
(*   setoid_rewrite bind_ret_l. *)
(*   rewrite interp_state_bind. *)
(*   guclo eqit_clo_bind; econstructor; eauto. *)
(*   - apply Heq. *)
(*   - intros [s' []] _ []; cbn. *)
(*     + rewrite interp_state_tau. *)
(*       gstep; constructor. *)
(*       auto with paco. *)
(*     + rewrite interp_state_ret; apply reflexivity. *)
(* Qed. *)

Lemma interp_state_bind {E F C D : Type -> Type} {A B S : Type}
  `{FC : Functor C}
  `{FD : Functor D}
  `{C -< D}
  (f : forall T, E T -> S -> ctree F D (S * T)%type)
  (t : ctree E C A) (k : A -> ctree E C B)
  (s : S) :
  (interp_state f (t >>= k) s)
  ~
  (interp_state f t s >>= fun st => interp_state f (k (snd st)) (fst st)).
Proof.
Admitted.

Unset Universe Checking.
Lemma alloc_disjoint :
  exists m,
    @ssim Effin Effin void1 Bspec (memory * bool)%type (memory * bool)%type eq
      (ret (m, false))
      (interp_state handle_mem_spec double_alloc (IM.empty _)).
Proof.
  eexists.
  unfold double_alloc.
  assert ((@CTree.bind MemE void1 Z bool
          (@CTree.trigger MemE void1 Z
             (@subevent MemE MemE (@CategoryOps.ReSum_id (forall _ : Type, Type) IFun Id_IFun MemE) Z
                AllocE))
          (fun k : Z =>
           @CTree.bind MemE void1 Z bool
             (@CTree.trigger MemE void1 Z
                (@subevent MemE MemE (@CategoryOps.ReSum_id (forall _ : Type, Type) IFun Id_IFun MemE)
                   Z AllocE))
             (fun p : Z => @ret (ctree MemE void1) (@Monad_ctree MemE void1) bool (Z.eqb k p)))) ~
            (  vis AllocE
    (fun k : Z =>
     vis AllocE (fun p : Z => @ret (ctree MemE Bexec) (@Monad_ctree MemE Bexec) bool (k =? p)%Z))
)).
  admit.

  setoid_rewrite H.
  setoid_rewrite bind_bind.
  rewrite interp_state_bind.


  setoid_rewrite H.
    ((k <- trigger AllocE;; p <- trigger AllocE;; ret (k =? p)%Z) ~ (k <- trigger AllocE;; p <- trigger AllocE;; ret (k =? p)%Z)).
  rewrite interp_state_bind.
  setoid_rewrite interp_state_bind.
  setoid_rewrite interp_state_trigger.
  cbn.
  setoid_rewrite bind_vis.

  eapply refines_padded_refines.
  pstep; red; cbn.
  apply refinesF_forallL with (a:=alloc_sigma _).

  cbn.
  apply refinesF_forallL with (a:=alloc_sigma _).
  cbn.

  constructor.
  reflexivity.
  Unshelve.
  all: constructor.
Qed.

Lemma alloc_disjoint' :
  forall m,
    @padded_refines
      Effin Effin _ _
      in_rel
      in_post_rel
      eq
      (ret false)
      (fmap snd (interp_state handle_mem_spec double_alloc m)).
Proof.
  intros m.
  Opaque member.
  setoid_rewrite interp_state_bind.
  setoid_rewrite interp_state_bind.
  setoid_rewrite interp_state_trigger.
  cbn.
  setoid_rewrite bind_vis.

  apply refines_padded_refines with (b1:=true) (b2:=true).
  pstep; red; cbn.
  apply refinesF_forallR.
  intros [k KSPEC].

  cbn.
  apply refinesF_forallR.
  intros [p PSPEC].

  cbn.
  destruct (Z.eq_dec k p); subst.
  rewrite member_add_eq in PSPEC.
  discriminate.

  replace (k =? p)%Z with false by lia.
  constructor.
  reflexivity.
Qed.


Lemma double_alloc_spec :
  forall m m' b,
    (b = false /\
       exists k1 k2,
         m' = add k2 0 (add k1 0 m) /\
           k1 <> k2 /\
           member k1 m = false /\
           member k2 m = false) ->
    @padded_refines
      Effin Effin (memory * bool) (memory * bool)
      in_rel
      in_post_rel
      eq
      (interp_state handle_mem_spec double_alloc m)
      (ret (m', b)).
Proof.
  intros m m' b.
  { intros [B K].
    destruct K as (k1&k2&M'&NK1K2&MEM1&MEM2).
    cbn.
    repeat setoid_rewrite interp_state_bind.
    repeat setoid_rewrite interp_state_trigger.

    assert
      ((@ret (itree (SpecEvent (sum1 MemE FailureE))) _ _ (add k2 0 (add k1 0 m), false))
         ≈
         '(m, x) <- ret (add k1 0 m, k1);;
       '(m, y) <- ret (add k2 0 m, k2);;
       ret (m, false)) as RET.
    { repeat (cbn; setoid_rewrite bind_ret_l).
      reflexivity.
    }

    subst.
    setoid_rewrite RET.

    eapply padded_refines_bind.
    apply refines_padded_refines with (b1:=true) (b2:=true).
    apply alloc_spec; auto.
    intros r1 [m' k] (?&?&?); cbn in *; subst.

    eapply padded_refines_bind.
    apply refines_padded_refines with (b1:=true) (b2:=true).
    apply alloc_spec.
    unfold fst; split; auto.
    Transparent member.
    unfold member.
    rewrite IP.F.add_neq_b; eauto.
    intros r1 [m'' k'] (?&?&?); cbn in *; subst.

    pstep; red; cbn.
    constructor.
    replace (k1 =? k2)%Z with false by lia.
    reflexivity.
  }
Qed.

Import HasPost.

Definition store_prog (v : nat) : itree MemE nat :=
  k <- trigger AllocE;;
  trigger (StoreE k v);;
  trigger (LoadE k).

Lemma alloc_lemma :
  forall m m_final k,
    member k m = false ->
    m_final = add k 0 m ->
    @strict_refines
      Effin _
      (interp_state handle_mem_spec (trigger AllocE) m)
      (ret (m_final, k)).
Proof.
  intros m m_final k MEM FINAL.
  setoid_rewrite interp_state_trigger.
  cbn.
  eapply padded_refines_forallL.
  Unshelve.
  2: {
    exists k; auto.
  }

  cbn.
  subst.
  pstep; red; cbn; constructor; auto.
Qed.

Lemma alloc_lemma' :
  forall m,
    @strict_refines
      Effin _
      (interp_state handle_mem_spec (trigger AllocE) m)
      (ret (add (next_key m) 0 m, next_key m)).
Proof.
  intros m.
  eapply alloc_lemma.
  apply next_key_not_member.
  reflexivity.
Qed.

Lemma store_succ_lemma :
  forall m m_final k v,
    member k m ->
    m_final = add k v m ->
    eutt eq (interp_state (@handle_mem_spec Effin _) (trigger (StoreE k v)) m)
      (ret (m_final, tt)).
Proof.
  intros m m_final k v MEM FINAL.
  setoid_rewrite interp_state_trigger.
  cbn.
  apply member_lookup in MEM.
  destruct MEM.
  rewrite H.
  subst.
  reflexivity.
Qed.

Lemma load_succ_lemma :
  forall m k v,
    lookup k m = Some v ->
    eutt eq (interp_state (@handle_mem_spec Effin _) (trigger (LoadE k)) m)
      (ret (m, v)).
Proof.
  intros m k v LUP.
  setoid_rewrite interp_state_trigger.
  cbn.
  rewrite LUP.
  reflexivity.
Qed.

Lemma store_fail_lemma :
  forall m k v,
    member k m = false ->
    eutt eq (interp_state handle_mem_spec (trigger (StoreE k v)) m)
      (raise "Store to unallocated address.").
Proof.
  intros m k v MEM.
  setoid_rewrite interp_state_trigger.
  cbn.
  destruct (lookup k m) eqn:LUP.
  apply lookup_member in LUP.
  rewrite LUP in MEM; discriminate.
  reflexivity.
Qed.

Lemma load_fails_lemma :
  forall m k,
    member k m = false ->
    eutt eq (interp_state handle_mem_spec (trigger (LoadE k)) m)
      (raise "Load from unallocated address.").
Proof.
  intros m k MEM.
  setoid_rewrite interp_state_trigger.
  cbn.
  destruct (lookup k m) eqn:LUP.

  apply lookup_member in LUP.
  rewrite LUP in MEM.
  discriminate.
  reflexivity.
Qed.


Lemma blah :
  @strict_refines Effin _
    (forall_spec nat) (ret 1).
Proof.
  unfold forall_spec.
  eapply padded_refines_forallL.
  pstep; red; cbn; constructor; auto.
Qed.

(* This doesn't work. The thing on the left is an empty set, and the
refinement relation doesn't hold vacuously *)
Lemma ub_test :
  @strict_refines Effin _
    (x <- forall_spec void;; ret 9) (ret 1).
Proof.
  unfold forall_spec.
  cbn.
  rewrite bind_vis.
  eapply padded_refines_forallL.
  Unshelve.
Abort.

(* This *does* work. The set on the right is empty, and therefore a
   subset of the thing on the left. *)
Lemma ub_test_r :
  @strict_refines Effin _
    (ret 1) (x <- forall_spec void;; ret 9).
Proof.
  unfold forall_spec.
  cbn.
  rewrite bind_vis.
  eapply padded_refines_forallR.
  intros [].
Qed.

Lemma blah' :
  @strict_refines Effin _
    (forall_spec nat)
    (forall_spec nat).
Proof.
  unfold forall_spec.
  eapply padded_refines_forallR.
  intros a.
  eapply padded_refines_forallL.
  pstep; red; cbn; constructor; auto.
Qed.

Lemma store_forward_with_rewrites' :
  forall m v,
    @strict_refines
      Effin _
      (fmap snd (interp_state handle_mem_spec (store_prog v) m))
      (ret v).
Proof.
  intros m v.
  cbn.
  unfold ITree.map.
  cbn.

  Opaque member lookup add.
  setoid_rewrite interp_state_bind.
  setoid_rewrite interp_state_bind.
  repeat setoid_rewrite bind_bind.
  cbn.

  rewrite alloc_lemma'; cbn.
  setoid_rewrite bind_ret_l.
  rewrite store_succ_lemma; cbn; eauto.
  2: apply member_add_eq.

  setoid_rewrite bind_ret_l.
  rewrite load_succ_lemma; cbn; eauto.
  2: apply lookup_add_eq.

  setoid_rewrite bind_ret_l.
  cbn.
  reflexivity.
Qed.

Hint Rewrite
  @bind_bind
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
  strict_refines_refl
  strict_refines_trans
  strict_refines_proper
  padded_refines_bind_proper
  padded_refines_proper_eq_itree
  padded_refines_proper_eutt
  refines_padded_refines
  alloc_lemma'
  store_succ_lemma
  load_succ_lemma 
  member_add_eq
  lookup_add_eq : SolveMem.

Hint Extern 100 (@strict_refines _ _ _ _) => reflexivity : SolveMem.

Ltac solve_refines :=
  cbn;
  repeat setoid_rewrite interp_state_bind;
  cbn;
  repeat (autorewrite with SolveMem; cbn);
  eauto with SolveMem.

Lemma store_forward_with_rewrites'' :
  forall m v,
    @strict_refines
      Effin _
      (fmap snd (interp_state handle_mem_spec (store_prog v) m))
      (ret v).
Proof.
  intros m v.
  cbn.
  unfold ITree.map.
  solve_refines.
Qed.

Lemma store_forward_with_rewrites :
  forall m v,
    @strict_refines
      Effin _
      (ret v)
      (fmap snd (interp_state handle_mem_spec (store_prog v) m)).
Proof.
  intros m v.
  cbn.
  unfold ITree.map.
  cbn.

  Opaque member lookup add.
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
  rewrite bind_vis.
  apply padded_refines_forallR.
  intros [k m'].
  solve_refines.
  reflexivity.
Qed.

Lemma store_forward_stronger :
  forall m v,
    eq1 (ret v)
      (fmap snd (interp_state (@handle_mem_spec Effin _) (store_prog v) m)).
Proof.
  intros m v.
  repeat red.
  split.
  apply store_forward_with_rewrites.
  apply store_forward_with_rewrites'.
Qed.
