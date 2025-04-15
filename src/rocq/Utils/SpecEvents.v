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
Import Morphisms.

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
            m2 = add k 0 m
      )
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

Definition double_alloc : itree MemE bool
  := k <- trigger AllocE;;
     p <- trigger AllocE;;
     ret (Z.eqb k p).

Import StateFacts.
Import Padded.
Import Utils.Tactics.

(* Lemma refines_eutt_padded_l_tau_aux: *)
(*   forall (E1 E2 : Type -> Type) (R2 : Type) *)
(*     (R1 : Type) (RPre : prerel E1 E2) *)
(*     (RPost : postrel E1 E2) (RR : R1 -> R2 -> Prop) *)
(*     (r : itree_spec E1 R1 -> itree_spec E2 R2 -> Prop) *)
(*     (m1 m2 : itree_spec E1 R1) (t3 : itree_spec E2 R2), *)
(*     (forall (t1 t2 : itree_spec E1 R1) (t4 : itree_spec E2 R2), *)
(*         padded t2 -> t1 ≈ t2 -> refines RPre RPost RR t1 t4 -> r t2 t4) -> *)
(*     paco2 (eqit_ eq true true id) bot2 m1 m2 -> *)
(*     paddedF (upaco1 padded_ bot1) (TauF m2) -> *)
(*     refinesF RPre RPost RR (upaco2 (refines_ RPre RPost RR) bot2) *)
(*              (TauF m1) (observe t3) -> *)
(*     refinesF RPre RPost RR (upaco2 (refines_ RPre RPost RR) r) *)
(*              (TauF m2) (observe t3). *)
(* Proof. *)
(*   intros E1 E2 R2 R1 RPre RPost RR r m1 m2 t3 CIH REL Hpad2 Href. *)
(*   remember (observe t3) as ot3. clear Heqot3 t3. *)
(*   assert (HDEC : (exists t4, ot3 = TauF t4) \/ (forall t4, ot3 <> TauF t4)). *)
(*   { destruct ot3; eauto; right; repeat intro; discriminate. } *)
(*   destruct HDEC as [ [t4 Ht4] |  Ht3]; subst. *)
(*   { *)
(*     constructor. right. eapply CIH; eauto. inv Hpad2. pclearbot. auto. *)
(*     pclearbot. auto. *)
(*     apply refines_TauL_inv. apply refines_TauR_inv. pstep. auto. *)
(*   } *)
(*   destruct ot3; try (exfalso; eapply Ht3; eauto; fail); try destruct e. *)
(*   + inv Href. constructor. punfold REL. red in REL. *)
(*     remember (RetF r0) as y. hinduction H0 before r; intros; inv Heqy; subst; eauto with itree_spec. *)
(*     * remember (RetF r1) as x. hinduction REL before r; intros; inv Heqx; subst; eauto with itree_spec. *)
(*     * eapply IHrefinesF; eauto. pstep_reverse. *)
(*       (* need to move tau_eutt and tau_euttge into this branch, *) *)
(*       setoid_rewrite <- (tau_eutt t1). pstep. auto. *)
(*     * inv Hpad2. pclearbot. punfold H2. red in H2. *)
(*       remember (VisF (Spec_forall A) k) as x. *)

(*       hinduction REL before r; intros; inv Heqx; inj_existT; subst; *)
(*         eauto with solve_padded. *)

(*       econstructor. eapply IHrefinesF; eauto. pclearbot. pstep_reverse. *)
(*       inv H2; inj_existT; subst. *)
(*       specialize (H3 a). *)
(*       pclearbot. *)
(*       constructor; left. *)
(*       pstep; constructor; left; auto. *)

(*       constructor. *)
(*       eapply IHREL; eauto. *)
(*       pstep_reverse. *)
(*       inv H2; pclearbot; eauto with solve_padded. *)
(*     * inv Hpad2. pclearbot. punfold H3. red in H3. *)
(*       remember (VisF (Spec_exists A) k) as x. hinduction REL before r; intros; inv Heqx; inj_existT; subst; *)
(*         eauto with solve_padded. *)
(*       econstructor. intros. pclearbot. *)

(*       eapply H0; eauto with solve_padded. pstep_reverse. *)
(*       inv H3; inj_existT; subst; pclearbot. *)
(*       specialize (H4 a). *)
(*       constructor. left. *)
(*       pstep; constructor; left. *)
(*       eauto with solve_padded. *)

(*       constructor. *)
(*       eapply IHREL; try pstep_reverse; eauto with solve_padded. *)
(*       inv H3; inj_existT; subst; pclearbot. *)
(*       eauto with solve_padded. *)
(*       (* left off here *) *)
(*   + inv Href. constructor. *)
(*     inv Hpad2. pclearbot. punfold H1. red in H1. punfold REL. red in REL. *)
(*     hinduction H0 before r; intros; inj_existT; subst; eauto with solve_padded. *)
(*     * admit. *)
(*     * specialize (Ht3 t2); contradiction. *)
(*     * inv REL; inj_existT; subst; *)
(*         eauto with solve_padded. *)
(*       -- constructor; eauto. *)
(*          intros * POST. *)
(*          right. *)
(*          eapply CIH. *)
(*          right. *)
(*       hinduction REL before r; intros. inj_existT; subst; eauto with solve_padded. *)
(*       inv H1. *)
(*       admit. *)
(*       constructor. *)
    
(*     rewrite itree_eta'. *)
(*     pstep_reverse. *)
(*     eapply paddedF_Tau_inv_hint *)

    
(*     remember (@VisF _ R2 _ _ (Spec_vis e) (fun a : _  => Tau (k a))) as y. *)
(*     assert (Hy : paddedF (upaco1 padded_ bot1) y). *)
(*     { subst. constructor. auto. } *)
(*     hinduction H0 before r; intros; inv Heqy; inj_existT; subst; eauto with solve_padded. *)
(*     (* * eapply IHrefinesF; eauto. pstep_reverse. rewrite <- (tau_eutt phi). pstep. auto. *) *)
(*     * remember (VisF (Spec_vis e1) k1) as y. *)
(*       (* *) *)
(* (*        * dholland 20250131: with coq-paco 4.2.3 this pclearbot changes *) *)
(* (*        * the upaco2 in H0 to paco2; with coq-paco 4.2.2 and earlier *) *)
(* (*        * it's missed. *) *)
(* (*        *) *)
(*       pclearbot. *)
(*       (* shouldn't I know that k2 is padded here? *) *)
(*       hinduction REL before r; intros; inv Heqy; inj_existT; subst. *)
(*       -- pclearbot. constructor; auto. intros. eapply H0 in H3. *)
(*          (* dholland 20250131: consequently this is no longer needed *) *)
(*          (*destruct H3; try contradiction.*) *)
(*          right. pclearbot. inv Hy. inj_existT. subst. eapply CIH; eauto with solve_padded; try apply REL. *)
(*       -- constructor. eapply IHREL; eauto. *)
(*          inv H1. pclearbot. pstep_reverse. *)
(*     * eapply IHrefinesF; eauto with solve_padded. pstep_reverse. rewrite <- (tau_eutt t1). *)
(*       pstep. auto. *)
(*     * remember (VisF (Spec_forall A) k) as x. *)
(*       hinduction REL before r; intros; inv Heqx; inj_existT; subst; eauto with solve_padded. *)
(*       econstructor. pclearbot. eapply IHrefinesF; eauto with solve_padded. pstep_reverse. *)
(*     * remember (VisF (Spec_exists A) k) as x. *)
(*       hinduction REL before r; intros; inv Heqx; inj_existT; subst; eauto with solve_padded. *)
(*       econstructor. intros. eapply H0; eauto. pclearbot. pstep_reverse. *)
(*       inv H1; inj_existT; subst. constructor. auto. *)
(*   + inv Hpad3. inj_existT. subst. apply refinesF_forallR. intros. constructor. *)
(*     right. eapply CIH; pclearbot; eauto with solve_padded. *)
(*     inv Hpad2. pclearbot. eapply refines_TauR_inv. *)
(*     set (fun a => Tau (k1 a)) as k2'. assert (Tau (k1 a) = k2' a). auto. *)
(*     rewrite H. *)
(*     apply refines_Vis_forallR. unfold k2'. apply refines_TauL_inv. pstep. auto. *)
(*   + inv Hpad3. inj_existT. subst. *)
(*     assert ( refinesF RPre RPost RR *)
(*                       (upaco2 (refines_ RPre RPost RR) bot2) *)
(*                       (observe m1) *)
(*                       (VisF (Spec_exists A) (fun a => Tau (k1 a))) ). *)
(*     { rewrite itree_eta'. pstep_reverse. apply refines_TauL_inv. pstep. auto. } *)
(*     clear Href. rename H into Href. pclearbot. *)
(*     eapply refinesF_Vis_existsR in Href. punfold REL. red in REL. *)
(*     hinduction Href before r; intros; eauto. *)
(*     * eapply refinesF_existsR. constructor. right. *)
(*       eapply CIH; eauto with solve_padded. pstep. Unshelve. 3 : exact a. *)
(*       3: { *)
(*         apply go. *)
(*         apply phi. *)
(*       } *)
(*       red. auto. red. apply refines_TauR_inv. pstep. auto. *)
(*     * inv Hpad2. pclearbot. punfold H1. red in H1. *)
(*       remember (VisF (Spec_forall B) kphi1) as x. remember (observe m2) as om2. *)
(*       hinduction REL before r; intros; inv Heqx; inj_existT; subst. *)
(*       -- inv H1. inj_existT. subst. constructor. rewrite <- Heqom2. *)
(*          eapply refinesF_forallL. Unshelve. 2 : exact b. eapply IHHref; eauto. *)
(*          pclearbot. pstep_reverse. rewrite <- (tau_eutt (k1 b)). auto. *)
(*          constructor. auto. *)
(*       -- constructor. rewrite <- Heqom2. inv H1. pclearbot. punfold H2. *)
(*     * inv Hpad2. pclearbot. punfold H3. red in H3. *)
(*       remember (VisF (Spec_exists B) kphi1) as x. remember (observe m2) as om2. *)
(*       hinduction REL before r; intros; inv Heqx; inj_existT; subst. *)
(*       -- inv H3. inj_existT. subst. constructor. intros. *)
(*          rewrite <- Heqom2. constructor. intros. eapply H0; eauto. Unshelve. all : auto. *)
(*          pclearbot. pstep_reverse.  setoid_rewrite tau_eutt in REL. auto. *)
(*          constructor. auto. *)
(*       -- constructor. rewrite <- Heqom2. *)
(*          eapply IHREL; eauto. inv H3. pclearbot. pstep_reverse. *)
(*     * eapply IHHref; eauto. pstep_reverse. rewrite <- (tau_eutt phi1). pstep. auto. *)
(* Qed. *)

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

(* Lemma refines_eutt_padded E1 E2 R1 R2 RPre RPost RR : *)
(*   forall (t1 t3 : itree_spec E1 R1) (t2 t4 : itree_spec E2 R2), *)
(*     padded t3 -> padded t4 -> t1 ≈ t3 -> t2 ≈ t4 -> *)
(*     refines RPre RPost RR t1 t2 -> refines RPre RPost RR t3 t4. *)
(* Proof. *)
(*   intros t1 t3 t2 t4 Hpad3 Hpad4 Heutt1 Heutt2 Href. *)
(*   revert t1 t3 t2 t4 Hpad3 Hpad4 Heutt1 Heutt2 Href. *)
(*   pcofix CIH. intros t1 t3 t2 t4 Hpad3 Hpad4 Heutt1 Heutt2 Href. *)
(*   punfold Hpad3. red in Hpad3. *)
(*   punfold Hpad4. red in Hpad4. *)
(*   punfold Heutt1. red in Heutt2. *)
(*   punfold Href. red in Href. pstep. *)
(*   red. *)
(*   hinduction Heutt1 before r; intros; pclearbot; eauto. *)
(*   - subst. setoid_rewrite itree_eta'. pstep_reverse. *)
(*     eapply paco2_mon. *)
(*     eapply refines_eutt_padded_r. *)
(*     4: { *)
(*       pstep; red. *)
(*       apply Href. *)
(*     } *)
(*     all: eauto with solve_padded. *)
(*     pstep; red; cbn; eauto with solve_padded. *)
(*     rewrite Heutt2. *)
(*     rewrite itree_eta at 1; reflexivity. *)
(*     intros * BOT. *)
(*     inv BOT. *)
(*   - eapply refines_eutt_padded_l_tau_aux; eauto. *)
(*     intros t0 t5 t6 H H0 H1 H2. *)
(*     eapply CIH; eauto; reflexivity. *)
(*     punfold Heutt2; red in Heutt2. *)
(*     hinduction Heutt2 before r; intros; pclearbot; subst; eauto. *)
(*     + constructor; left. *)
(*       pstep; red. *)
(*       left. *)

    
(*     eapply refines_eutt_padded_r_tau_aux; eauto. *)
(*     eapply refines_eutt_padded_r; eauto with solve_padded. *)
(*   - (* need to figure this out *) *)
(*     destruct e. *)
(*     + assert (Hx : Vis (Spec_vis e) k1 ≈ Vis (Spec_vis e) k2). *)
(*       pstep. constructor. left. auto. *)
(*       punfold Hx. red in Hx. cbn in *. *)
(*       remember (VisF (Spec_vis e) k1) as x. *)
(*       hinduction Href before r; intros; inv Heqx; inj_existT; subst; eauto. *)
(*       * constructor; auto. intros a b Hab. *)
(*         eapply H0 in Hab. destruct Hab; try contradiction. *)
(*         right. eapply CIH; eauto with solve_padded. inv Hpad2. *)
(*         inj_existT. subst. pstep. constructor. auto. *)
(*         inv Hpad3. inj_existT. subst. (* pstep. constructor. auto. *) *)
(*         inv Hx. inj_existT. subst. destruct (REL0 a); try contradiction. auto. *)
(*         pclearbot. *)
(*         rewrite tau_eutt in H2. *)
(*         punfold H2. *)
(*       * constructor. auto. eapply IHHref; eauto with solve_padded. *)
(*       * constructor; auto. intros. *)
(*         eapply H0; eauto with solve_padded. *)
(*       * econstructor. eapply IHHref; eauto with solve_padded. *)
(*     + inv Hpad2. inj_existT. subst. pclearbot. *)
(*       eapply refinesF_Vis_forallL in Href. *)
(*       induction Href. *)
(*       * constructor. intros. eapply H1. eauto with solve_padded. *)
(*       * econstructor. Unshelve. all : auto. *)
(*         rewrite itree_eta'. *)
(*         eapply refines_eutt_padded_l_tau_aux; eauto. *)
(*         setoid_rewrite tau_eutt in REL. auto. constructor. left. auto. *)
(*         constructor. auto. *)
(*       * eapply refinesF_existsR. eapply IHHref; eauto with solve_padded. *)
(*       * constructor. eapply IHHref. inv Hpad3. pclearbot. pstep_reverse. *)
(*     + inv Hpad2. inj_existT. subst. *)
(*       (* this should be fine, exists L is invertible and then I just *) *)
(* (*          further invert Href until I learn more about t3 *) *)
(* (*        *) *)
(*       constructor. intros. *)
(*       assert (forall a, refinesF RPre RPost RR (upaco2 (refines_ RPre RPost RR) bot2) (observe (k1 a)) (observe t3)). *)
(*       intros. pstep_reverse. eapply refines_existsL. pstep. auto. *)
(*       clear Href. rename H into Href. specialize (Href a). *)
(*       eapply refines_eutt_padded_l_tau_aux; eauto. *)
(*       setoid_rewrite tau_eutt in REL. auto. *)
(*       constructor. auto. constructor. auto. *)
(*   - eapply IHHeutt; eauto. *)
(*     pstep_reverse. apply refines_TauL_inv. pstep. auto. *)
(*   - constructor. eapply IHHeutt; eauto with solve_padded. *)
(* Qed. *)


(*   pcofix CIH. intros t1 t3 t2 t4 Hpad3 Hpad4 Heutt1 Heutt2 Href. *)
(*   punfold Href. red in Href. *)
(*   punfold Heutt2. red in Heutt2. *)
(*   punfold Hpad3. red in Hpad3. punfold Hpad4. red in Hpad4. *)
(*   pstep. red. hinduction Heutt2 before r; intros; pclearbot. *)
(*   - subst. setoid_rewrite itree_eta'. pstep_reverse. *)
(*     eapply paco2_mon; [ pstep; eapply Href | intros; contradiction]. *)
(*   - eapply refines_eutt_padded_r_tau_aux; eauto. *)
(*   - destruct e. *)
(*     + assert (Hx : Vis (Spec_vis e) k1 ≈ Vis (Spec_vis e) k2). *)
(*       pstep. constructor. left. auto. punfold Hx. red in Hx. *)
(*       cbn in Hx. *)
(*       remember (VisF (Spec_vis e) k1) as y. *)
(*       hinduction Href before r; intros; inv Heqy; inj_existT; subst; eauto with solve_padded. *)
(*       constructor. auto. right. eapply CIH; eauto with solve_padded. *)
(*       inv Hpad1. inj_existT. cbn in *. subst. *)
(*       apply REL. *)
(*       inversion Hx. subst. inj_existT. subst. destruct (REL0 b); try contradiction. *)
(*       apply H0 in H1. destruct H1; auto; try contradiction. *)
(*     + inv Hpad3. inj_existT. subst. *)
(*       constructor. intros. *)
(*       eapply refines_eutt_padded_r_tau_aux with (m1 := k1 a); auto. *)
(*       constructor. pstep_reverse. apply refines_Vis_forallR. pstep. auto. *)
(*       constructor. auto. setoid_rewrite tau_eutt in REL. auto. *)
(*     + eapply refinesF_Vis_existsR in Href. *)
(*       hinduction Href before r; intros; eauto. *)
(*       * econstructor. inv Hpad3. inj_existT. subst. *)
(*         Unshelve. all : auto. cbn. *)
(*         rewrite itree_eta' at 1. *)
(*         eapply refines_eutt_padded_r_tau_aux; auto. eauto. *)
(*         constructor. eauto. *)
(*         constructor. auto. setoid_rewrite tau_eutt in REL. auto. *)
(*       * eapply refinesF_forallL. eapply IHHref; eauto. *)
(*         inv Hpad1. inj_existT. subst. constructor. auto. *)
(*       * apply refinesF_existsL. intros. eapply H0; eauto. *)
(*         inv Hpad1. inj_existT. subst. constructor. auto. *)
(*       * constructor. eapply IHHref; eauto. inv Hpad1. pclearbot. pstep_reverse. *)
(*   - eapply IHHeutt; eauto. pstep_reverse. apply refines_TauR_inv. pstep. auto. *)
(*   - constructor. eapply IHHeutt; eauto. inv Hpad3. pclearbot. pstep_reverse. *)
(* Qed. *)

(* TODO: May not be true? *)
Lemma refines_padded_refines :
  forall E1 E2 R1 R2 in_rel in_post_rel RR t1 t2,
    @refines
      E1 E2 R1 R2
      in_rel
      in_post_rel
      RR
      t1 t2 ->
    @padded_refines
      E1 E2 R1 R2
      in_rel
      in_post_rel
      RR
      t1 t2.
Proof.
  intros E1 E2 R1 R2 in_rel0 in_post_rel0 RR t1 t2 H.
  unfold padded_refines.
  eapply refines_eutt_padded_l; eauto using pad_is_padded.
  apply pad_eutt.
  eapply refines_eutt_padded_r; eauto using pad_is_padded.
  admit.
  apply pad_eutt.
Admitted.

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
