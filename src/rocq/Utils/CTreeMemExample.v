From Paco Require Import paco.

From CTree Require Import
  CTree CTreeDefinitions Eq Fold.

From Stdlib Require Import
  FSets.FMapAVL
  FMapFacts
  ZArith.

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

Variant voidE (X : Type) :=.

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

Definition handle_mem {E} `{FailureE -< E} : MemE ~> Monads.stateT memory (ctree E voidE) :=
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
Notation Bexec := voidE.
Notation Effout := FailureE.

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

Lemma ssim_raise_ret E `{Effout -< E} F `{Effout -< F} C D X Y L s y :
  ~ @ssim
    E F C D X Y L
    (@raise E C _ _ s)
    (ret y).
Proof.
  intros CONTRA.
  unfold raise in *.
  unfold CTree.trigger in *.
  (* Need vis / ret inv *)
  step in CONTRA.
  eapply ss_vis_l_inv in CONTRA.
  destruct ss.
  cbn in *.
  inversion CONTRA.
  
  
  apply ssim_vis_l_inv in CONTRA.
  destruct CONTRA as (?&?&?&?&?).
  rewrite bind_ret_l in H2.
  break_match_hyp.
  Unshelve.
  eapply ssim_clo_bind.
  2: intros [].
  apply ssim_vis.
  intros [].
  Unshelve.
  apply eq.
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
      admit.
    }
    cbn.
    apply ssim_ret.
    reflexivity.
Admitted.

Lemma alloca_empty :
  forall k,
  @ssim Effin Effin voidE _ _ _ eq (ret (IM.add k 0 (IM.empty _), k))
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
    admit.
  }

  cbn.
  apply ssim_ret.
  reflexivity.
Admitted.

Lemma load_succeeds_spec :
  forall m k v,
    IM.find k m = Some v <->
      @ssim Effin Effin voidE _ _ _ eq (ret (m, v))
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
      @ssim Effin Effin voidE _ T _ eq
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

    unfold raise in *.
    eapply SSim.ssim_vis_inv in REF.
    2: {
      reflexivity.
    }
    eapply trans_trigger_inv in REF.
    
    - admit.
    - apply ssim_ret_r_inv in REF.
      destruct REF as (?&?&?&?); subst.
      unfold raise in H.
      apply trans_trigger_inv in H.
      destruct H as [[] _]. 
      punfold REF; inversion REF; subst.
  }
Qed.

Lemma store_succeeds_spec :
  forall m m' k v,
    member k m /\
      m' = add k v m
    <->
      @refines
        Effin Effin (memory * _) (memory * _)
        in_rel
        in_post_rel
        (fun r1 r2 =>
           r1 = r2 /\
             fst r2 = m'
        )
        (handle_mem_spec _ (StoreE k v) m)
        (ret (m', tt)).
Proof.
  intros m m' k v.
  split.
  { intros [MEM ADD]; subst.
    cbn.
    apply member_lookup in MEM as (v'&MEM).
    rewrite MEM.
    pstep; red; cbn; constructor.
    cbn; auto.
  }
  { intros REF.
    cbn in REF.
    destruct (lookup k m) eqn:LUP;
      punfold REF; inversion REF; subst.
    destruct H1 as (?&?).
    cbn in *; subst; auto.
    inversion H; subst; split; auto.
    eapply lookup_member; eauto.
  }
Qed.

Lemma store_fails_spec :
  forall m k v,
    member k m = false
    <->
      @refines
        Effin Effin (memory * _) (memory * _)
        in_rel
        in_post_rel
        eq
        (handle_mem_spec _ (StoreE k v) m)
        (raise "Store to unallocated address.").
Proof.
  intros m k v.
  split.
  { intros MEM; subst.
    cbn.
    destruct (lookup k m) eqn:LUP.
    apply lookup_member in LUP.
    rewrite LUP in MEM.
    discriminate.

    pstep; red; cbn; constructor.
    cbn; auto.
    intros [].
  }
  { intros REF.
    cbn in REF.
    destruct (lookup k m) eqn:LUP;
      punfold REF; inversion REF; subst.
    inj_existT; subst.
    cbn in *.
    destruct (member k m) eqn:MEM; auto.
    apply member_lookup in MEM as (?&?).
    rewrite LUP in H; discriminate.
  }
Qed.

Lemma alloc_spec :
  forall (m m' : memory) k,
    member k m = false /\
      m' = add k 0 m
    <->
    @refines
      Effin Effin (memory * Z) (memory * Z)
      in_rel
      in_post_rel
      (fun r1 r2 =>
        r1 = r2 /\
          let m2 := fst r2 in
          let k2 := snd r2 in
          k2 = k /\
            m2 = add k 0 m)
      (handle_mem_spec Z (AllocE) m)
      (ret (m', k)).
Proof.
  intros m m' k.
  split.
  { intros [NMEM ADD].
    cbn.
    pstep; red; cbn.
    apply refinesF_forallL
      with (a:=exist (fun k => member k m = false) k NMEM).
    constructor; cbn; subst; auto.
  }
  { intros REF.
    cbn in *.
    (* Should this be a lemma? *)
    punfold REF.
    red in REF; cbn in REF.
    apply refinesF_Vis_forallL in REF.
    inversion REF; subst.
    destruct a; auto.
    cbn in *.
    inversion H; subst.
    inversion H2; subst; auto.
    destruct H1; cbn in *; subst.
    split; auto.
    inversion H0; subst; auto.
    auto.
  }
Qed.

Lemma alloc_spec_exists :
  forall (m : memory),
  exists m' k,
    member k m = false /\
      m' = add k 0 m /\
    @refines
      Effin Effin (memory * Z) (memory * Z)
      in_rel
      in_post_rel
      (fun r1 r2 =>
         r1 = r2 /\
           fst r2 = m' /\
           snd r2 = k)
      (handle_mem_spec Z (AllocE) m)
      (ret (m', k)).
Proof.
  intros m.
  destruct (member (next_key m) m) eqn:MEM; auto.
  apply IM.mem_2 in MEM.
  apply next_key_correct in MEM.
  lia.

  exists (add (next_key m) 0 m), (next_key m).
  split; auto.
  split; auto.

  cbn.
  pstep; red; cbn.

  eapply refinesF_forallL.
  Unshelve.
  2: {
    exists (next_key m).
    auto.
  }

  constructor; cbn; auto.
Qed.


Lemma handle_mem_spec_alloc_bind :
  forall RR m (k : memory * Z -> itree_spec Effin (memory * Z)) t,
    (exists (x : (memory * Z)),
        (fun r1 r2 =>
        r1 = r2 /\
          let m2 := fst r2 in
          let k2 := snd r2 in
          m2 = add k2 0 m) x x ->
        @padded_refines
          Effin Effin (memory * Z) (memory * Z)
          in_rel
          in_post_rel
          (fun r1 r2 =>
             r1 = r2 /\
               let m2 := fst r2 in
               let k2 := snd r2 in
               m2 = add k2 0 m)
          (k x) (* This is wrong *)
          t) ->
    @padded_refines
      Effin Effin (memory * Z) (memory * Z)
      in_rel
      in_post_rel
      RR
      (ITree.bind (handle_mem_spec _ AllocE m) k)
      t.
Proof.
Abort.

Definition double_alloc : itree MemE bool
  := k <- trigger AllocE;;
     p <- trigger AllocE;;
     ret (Z.eqb k p).

Import StateFacts.
Import Padded.
Import Utils.Tactics.

(* TODO: Move this *)
Lemma padded_ret :
  forall {X E} x,
    padded (@ret (itree E) _ X x).
Proof.
  intros X E x.
  pstep; red; cbn.
  constructor.
Qed.

Lemma padded_Ret :
  forall {X E} x,
    @padded E X (Ret x).
Proof.
  intros X E x.
  apply padded_ret.
Qed.

#[global] Hint Resolve padded_ret padded_Ret : solve_padded.


Lemma next_key_not_member :
  forall {A} (m : IntMap A),
    member (next_key m) m = false.
Proof.
  intros A m.
  destruct (member (next_key m) m) eqn:MEM; auto.
  apply IM.mem_2 in MEM.
  apply next_key_correct in MEM.
  lia.
Qed.

Lemma alloc_sigma :
  forall {A} (m : IntMap A),
    {k | member k m = false}.
Proof.
  intros A m.
  exists (next_key m).
  eapply next_key_not_member.
Defined.

Lemma alloc_disjoint :
  exists m,
    @padded_refines
      Effin Effin (memory * bool) (memory * bool)
      in_rel
      in_post_rel
      eq
      (interp_state handle_mem_spec double_alloc empty)
      (ret (m, false)).
Proof.
  eexists.
  Opaque member.
  setoid_rewrite interp_state_bind.
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
