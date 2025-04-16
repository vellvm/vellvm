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
        | Some _ =>
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
        | Some _ =>
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
Import Morphisms.

Lemma load_succeeds_spec :
  forall m k v,
    lookup k m = Some v <->
    @refines
      Effin Effin (memory * _) (memory * _)
      in_rel
      in_post_rel
      (fun r1 r2 =>
         r1 = r2 /\
           fst r2 = m /\
           snd r2 = v
      )
      (handle_mem_spec _ (LoadE k) m)
      (ret (m, v)).
Proof.
  intros m k v.
  split.
  { intros LUP.
    cbn; rewrite LUP.
    pstep; red; cbn; constructor.
    cbn; auto.
  }
  { intros REF.
    cbn in REF.
    destruct (lookup k m) eqn:LUP;
      punfold REF; inversion REF; subst.
    destruct H1 as (?&?&?).
    cbn in *; subst; auto.
    inversion H; subst; auto.
  }
Qed.

Lemma load_fails_spec :
  forall m k,
    lookup k m = None <->
    @refines
      Effin Effin (memory * _) (memory * _)
      in_rel
      in_post_rel
      eq
      (handle_mem_spec _ (LoadE k) m)
      (raise "Load from unallocated address.").
Proof.
  intros m k.
  split.
  { intros LUP.
    cbn; rewrite LUP.
    pstep; red; cbn; constructor.
    cbn; auto.
    intros [].
  }
  { intros REF.
    cbn in REF.
    destruct (lookup k m) eqn:LUP;
      punfold REF; inversion REF; subst.
  }
Qed.

Lemma store_succeeds_spec :
  forall m m' k v,
    member k m = true /\
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
  cbn.
  setoid_rewrite interp_state_bind.
  setoid_rewrite interp_state_bind.
  setoid_rewrite interp_state_trigger.

  assert
    ((@ret (itree (SpecEvent (sum1 MemE FailureE))) _ _ (add 1%Z 0 (add 0%Z 0 empty), false))
       ≈
       '(m, x) <- ret (add 0%Z 0 empty, 0%Z);;
       '(m, y) <- ret (add 1%Z 0 m, 1%Z);;
       ret (m, false)) as RET.
  { repeat (cbn; setoid_rewrite bind_ret_l).
    reflexivity.
  }

  setoid_rewrite RET.
  Opaque handle_mem_spec.
  cbn.
  eapply padded_refines_bind.
  apply refines_padded_refines.
  cbn.
  apply alloc_spec.
  cbn; auto.

  intros r1 [m k] (?&?&?).
  cbn in *; subst.

  eapply padded_refines_bind.
  apply refines_padded_refines.
  cbn.
  apply alloc_spec.
  cbn; auto.

  intros r1 [m' k'] (?&?&?).
  cbn in *; subst.

  cbn.
  rewrite interp_state_ret.
  apply padded_refines_ret.
  reflexivity.
Qed.

(* Lemma alloc_disjoint' : *)
(*   forall m m' b, *)
(*     @padded_refines *)
(*       Effin Effin (memory * bool) (memory * bool) *)
(*       in_rel *)
(*       in_post_rel *)
(*       eq *)
(*       (interp_state handle_mem_spec double_alloc m) *)
(*       (ret (m', b)) -> b = false. *)
(* Proof. *)
(*   intros m m' b REF. *)
(*   cbn in REF. *)
(*   setoid_rewrite interp_state_bind in REF. *)
(*   setoid_rewrite interp_state_bind in REF. *)
(*   setoid_rewrite interp_state_trigger in REF. *)
(*   cbn in REF. *)
(*   setoid_rewrite bind_vis in REF. *)

(*   punfold REF; red in REF; *)
(*     cbn in REF. *)
(*   apply Spec_vis_inv in REF. *)
(*   4: { *)

(*   } *)


  
(*   exists (add 1%Z 0 (add 0%Z 0 empty)). *)
(*   assert *)
(*     ((@ret (itree (SpecEvent (sum1 MemE FailureE))) _ _ (add 1%Z 0 (add 0%Z 0 empty), false)) *)
(*        ≈ *)
(*        '(m, x) <- ret (add 0%Z 0 empty, 0%Z);; *)
(*        '(m, y) <- ret (add 1%Z 0 m, 1%Z);; *)
(*        ret (m, false)) as RET. *)
(*   { repeat (cbn; setoid_rewrite bind_ret_l). *)
(*     reflexivity. *)
(*   } *)
(*   cbn. *)
(*   rewrite bind_trigger. *)
(*   setoid_rewrite StateFacts.interp_state_vis. *)
(*   rewrite RET. *)
(*   eapply padded_refines_bind. *)
(*   apply -> alloc_spec. *)
(*   apply  *)
(* Qed. *)

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
    apply refines_padded_refines.
    apply alloc_spec; auto.
    intros r1 [m' k] (?&?&?); cbn in *; subst.

    eapply padded_refines_bind.
    apply refines_padded_refines.
    apply alloc_spec.
    unfold fst; split; auto.
    unfold member.
    rewrite IP.F.add_neq_b; eauto.
    intros r1 [m'' k'] (?&?&?); cbn in *; subst.

    pstep; red; cbn.
    constructor.
    replace (k1 =? k2)%Z with false by lia.
    reflexivity.
  }
Qed.

Definition store_prog (v : nat) : itree MemE nat :=
  k <- trigger AllocE;;
  trigger (StoreE k v);;
  trigger (LoadE k).

Import HasPost.

Lemma refines_strengthen_RR :
  forall E1 E2 X Y PRE POST RR1 RR2 t1 t2,
    (forall x y, RR1 x y -> RR2 x y) ->
    @refines E1 E2 X Y
                    PRE POST RR1 t1 t2 ->
    @refines E1 E2 X Y
      PRE POST RR2 t1 t2.
Proof.
  intros E1 E2 X Y PRE POST RR1 RR2 t1 t2 STRENGTHEN REF.
  punfold REF; red in REF; cbn in REF.
  setoid_rewrite itree_eta.
  genobs t1 ot1.
  genobs t2 ot2.
  clear t1 t2 Heqot1 Heqot2.
  revert ot1 ot2 REF.
  pcofix CIH; intros ot1 ot2 REF.
  induction REF; cbn in *; subst; pclearbot;
    try solve
      [pstep; red; cbn;
       constructor; eauto with paco].
  - pstep; red; cbn;
    constructor; eauto.
    right.
    setoid_rewrite EqAxiom.itree_eta_.
    punfold H.
  - pstep; red; cbn;
    constructor; eauto.
    right.
    apply H0 in H1.
    setoid_rewrite EqAxiom.itree_eta_.
    eapply CIH; eauto.
    punfold H1.
  - pstep; red; cbn;
    constructor; eauto.
    punfold IHREF.
  - pstep; red; cbn;    
    constructor; eauto.
    punfold IHREF.
  - pstep; red; cbn;    
    constructor; eauto.

    intros a.
    specialize (H0 a).
    punfold H0.
  - pstep; red; cbn.
    econstructor; eauto.
    punfold IHREF.
  - pstep; red; cbn.
    econstructor; eauto.
    punfold IHREF.
  - pstep; red; cbn;    
    constructor; eauto.

    intros a.
    specialize (H0 a).
    punfold H0.
Qed.

Lemma padded_refines_strengthen_RR :
  forall E1 E2 X Y PRE POST RR1 RR2 t1 t2,
    (forall x y, RR1 x y -> RR2 x y) ->
    @padded_refines E1 E2 X Y
                    PRE POST RR1 t1 t2 ->
    @padded_refines E1 E2 X Y
      PRE POST RR2 t1 t2.
Proof.
  intros E1 E2 X Y PRE POST RR1 RR2 t1 t2 H H0.
  eapply refines_strengthen_RR; eauto.
Qed.

Lemma store_forward :
  forall m v,
    exists m',
    @padded_refines
      Effin Effin (memory * nat) (memory * nat)
      in_rel
      in_post_rel
      eq
      (interp_state handle_mem_spec (store_prog v) m)
      (ret (m', v)).
Proof.
  intros m v.
  cbn.
  repeat setoid_rewrite interp_state_bind.
  repeat setoid_rewrite interp_state_trigger.

  pose proof alloc_spec_exists m as (m' & k & MEM & M' & ALLOC).
  apply refines_padded_refines in ALLOC.

  exists (add k v m').

  assert
    ((@ret (itree (SpecEvent (sum1 MemE FailureE))) _ _ (add k v m', v))
       ≈
       '(m, x) <- ret (add k 0 m, k);;
       '(m, x) <- ret (add k v m, tt);;
       ret (m, v)).
  { repeat (cbn; setoid_rewrite bind_ret_l).
    subst.
    reflexivity.
  }

  rewrite H.
  eapply padded_refines_bind with (RR:=(fun r1 r2 : memory * Z => r1 = r2 /\ fst r2 = m' /\ snd r2 = k));
  subst.
  apply ALLOC.

  intros r1 [m' k'] (?&?&?).
  cbn in *; subst.

  eapply padded_refines_bind.
  cbn.
  eapply refines_padded_refines.
  eapply store_succeeds_spec.
  split; auto.
  apply member_add_eq.

  intros r1 [m'' []] (?&?).
  cbn in *; subst.
  cbn.

  eapply padded_refines_strengthen_RR; cycle 1.
  eapply refines_padded_refines.
  apply load_succeeds_spec.
  apply lookup_add_eq.

  intros x [m'' n] (?&?&?).
  cbn in *; subst.
  auto.
Qed.

Lemma next_key_not_member :
  forall (m : memory),
    member (next_key m) m = false.
Proof.
Admitted.

Ltac do_trans :=
  eapply padded_refines_strengthen_PRE; cycle 1;
  [eapply padded_refines_weaken_post; cycle 1;
   [eapply padded_refines_strengthen_RR; cycle 1;
    [eapply padded_refines_trans|]
   |]
  |].

Lemma store_forward_ignore_mem :
  forall m v,
    @padded_refines
      Effin Effin _ _
      in_rel
      in_post_rel
      eq
      (fmap snd (interp_state handle_mem_spec (store_prog v) m))
      (ret v).
Proof.
  intros m v.
  cbn.
  repeat setoid_rewrite interp_state_bind.
  repeat setoid_rewrite interp_state_trigger.
  repeat setoid_rewrite map_bind.
  do_trans.

  { eapply padded_refines_bind.
    eapply refines_padded_refines; eapply alloc_spec with (k:=next_key m).
    split; [apply next_key_not_member | reflexivity].
    intros r1 [m' k'] [EQ [K' M']]; cbn in *; subst.

    do_trans.
    { eapply padded_refines_bind.
      cbn.
      eapply refines_padded_refines.
      eapply store_succeeds_spec.
      split; auto.
      apply member_add_eq.

      intros r1 [m' []] [EQ M']; cbn in *; subst.

      do_trans.
      { eapply padded_refines_bind with (k2:=(fun x => Ret (snd x))).
        cbn.
        eapply refines_padded_refines.
        eapply load_succeeds_spec.
        apply lookup_add_eq.

        intros r1 [m' k'] [EQ [M' K']]; cbn in *; subst.
        cbn.
        apply padded_refines_ret.
        reflexivity.
      }

      cbn.
      all: admit.      
    }
    all: admit.
  }

  all: admit.
Abort.

(* Lemma padded_refines_bind_inv: *)
(*   forall (E1 E2 : Type -> Type) (R1 R2 S1 S2 : Type) (RPre : prerel E1 E2)  *)
(*     (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop) (RS : S1 -> S2 -> Prop)  *)
(*     (t1 : itree_spec E1 R1) (t2 : itree_spec E2 R2) (k1 : R1 -> itree_spec E1 S1) *)
(*     (k2 : R2 -> itree_spec E2 S2), *)
(*   padded_refines RPre RPost RS (ITree.bind t1 k1) (ITree.bind t2 k2) -> *)
(*   padded_refines RPre RPost RR t1 t2 /\ *)
(*     (forall (r1 : R1) (r2 : R2), RR r1 r2 -> padded_refines RPre RPost RS (k1 r1) (k2 r2)). *)

(* Lemma double_alloc_spec' : *)
(*   forall m m' b, *)
(*     @padded_refines *)
(*       Effin Effin (memory * bool) (memory * bool) *)
(*       in_rel *)
(*       in_post_rel *)
(*       eq *)
(*       (interp_state handle_mem_spec double_alloc m) *)
(*       (ret (m', b)) -> *)
(*     (b = false /\ *)
(*        exists k1 k2, *)
(*          m' = add k2 0 (add k1 0 m) /\ *)
(*            k1 <> k2 /\ *)
(*            member k1 m = false /\ *)
(*            member k2 m = false). *)
(* Proof. *)
(*   intros m m' b REF. *)
  
(* Qed. *)
