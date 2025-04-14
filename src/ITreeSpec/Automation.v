From Stdlib Require Export
  Datatypes
  Arith.PeanoNat
  Arith.Peano_dec
  Arith.Compare
  Wf_nat
  Morphisms
  Setoid
  Program.Equality
  Lists.List
  Logic.Eqdep_dec
  Logic.EqdepFacts
  Eqdep EqdepFacts
  Logic.ProofIrrelevance.

From ITree Require Import
  Basics.HeterogeneousRelations
  Eq.Eqit.

From ITreeSpec Require Import
  ITreeSpecDefinition
  ITreeSpecFacts
  ITreeSpecCombinatorFacts
  RecSpecFix
  SpecM
  MRecSpec
  SpecMFacts
  LetRecRefines
  DefRefines.

From Paco Require Import paco.

Export SigTNotations.

Import SpecMNotations.
Local Open Scope entree_scope.

(* FIXME: There has to be a better way... *)
Ltac resum_unfold :=
  unfold (* SubEvent.v *)
         resum, resum_ret,
         ReSum_inl, ReSumRet_inl,
         ReSum_inr, ReSumRet_inr,
         (* EnTreeDefinition.v *)
         SpecEventReSum, SpecEventReSumRet,
         (* RecSpecFix.v *)
         ReSum_id, ReSumRet_id,
         callESpecReSum, callESpecReSumRet,
         (* SpecM.v *)
         ReSum_FunStackE_E, ReSumRet_FunStackE_E,
         ReSum_FunStackE_Error, ReSumRet_FunStackE_Error,
         ReSum_LRTInput_FunStackE, ReSumRet_LRTInput_FunStackE,
         ReSum_FrameCall_FunStackE, ReSumRet_FrameCall_FunStackE.
Ltac encodes_unfold_in H :=
  unfold (* HeterogeneousRelations.v *)
         encodes,
         EncodingSum,
         (* QuantEnc.v *)
         EncodingType_QuantEnc, encodes_QuantEnc,
         (* EnTreeSpecDefinition *)
         SpecEventEncoding,
         (* SpecM.v *)
         EncodingType_LRTInput,
         EncodingType_FrameCall,
         EncodingType_ErrorE,
         EncodingType_FunStackE,
         EncodingType_EncType in H.

(***
 *** Definition and basic properties of spec_refines
 ***)


(* FIXME: need rules to add binds to all the unary combinators *)

(** Refinement rules for recursion **)

Definition callSPost {E1 E2 : EncType} {Γ1 Γ2 R1 R2}
  (RPost : SpecPostRel E1 E2 Γ1 Γ2)
  (call1 : FrameCallWithRet Γ1 R1) (call2 : FrameCallWithRet Γ2 R2)
  (r1 : R1) (r2 : R2) : Prop :=
  RPost
    (inl (proj1_sig call1)) (inl (proj1_sig call2))
    (eq_rect _ (fun T => T) r1 _ (eq_sym (proj2_sig call1)))
    (eq_rect _ (fun T => T) r2 _ (eq_sym (proj2_sig call2))).

Lemma spec_refines_call (E1 E2 : EncType) Γ1 Γ2 R1 R2
      (RPre : SpecPreRel E1 E2 Γ1 Γ2)
      (RPost : SpecPostRel E1 E2 Γ1 Γ2)
      (call1 : FrameCallWithRet Γ1 R1) (call2 : FrameCallWithRet Γ2 R2)
      (RR : Rel R1 R2) :
  RPre (inl (proj1_sig call1)) (inl (proj1_sig call2)) ->
  (forall r1 r2, callSPost RPost call1 call2 r1 r2 -> RR r1 r2) ->
  spec_refines RPre RPost RR (CallS _ _ _ call1) (CallS _ _ _ call2).
Proof.
  intros. apply padded_refines_vis; [ auto | ].
  intros. apply padded_refines_ret. apply H0.
  unfold callSPost.
  rewrite rew_compose. rewrite rew_compose.
  rewrite <- eq_rect_eq. rewrite <- eq_rect_eq. assumption.
Qed.

(* The bind of one recursive call refines the bind of another if the recursive
   calls are in the current RPre and, for all return values for them in RPost,
   the bind continuations refine each other *)
Lemma spec_refines_call_bind (E1 E2 : EncType) Γ1 Γ2 R1 R2 T1 T2
      (RPre : SpecPreRel E1 E2 Γ1 Γ2)
      (RPost : SpecPostRel E1 E2 Γ1 Γ2)
      (RR : T1 -> T2 -> Prop)
      (call1 : FrameCallWithRet Γ1 R1) (call2 : FrameCallWithRet Γ2 R2)
      (k1 : R1 -> SpecM E1 Γ1 T1)
      (k2 : R2 -> SpecM E2 Γ2 T2) :
  RPre (inl (proj1_sig call1)) (inl (proj1_sig call2)) ->
  (forall r1 r2,
      callSPost RPost call1 call2 r1 r2 ->
      spec_refines RPre RPost RR (k1 r1) (k2 r2)) ->
  spec_refines RPre RPost RR (CallS _ _ _ call1 >>= k1) (CallS _ _ _ call2 >>= k2).
Proof.
  intros. eapply padded_refines_bind; try eapply spec_refines_call; eauto.
Qed.

(* Add a bind to a RetS to a CallS on the left *)
Lemma spec_refines_call_bind_ret_l (E1 E2 : EncType) Γ1 Γ2 R1 R2
      (RPre : SpecPreRel E1 E2 Γ1 Γ2)
      (RPost : SpecPostRel E1 E2 Γ1 Γ2)
      (call1 : FrameCallWithRet Γ1 R1) t2 (RR : Rel R1 R2) :
  spec_refines RPre RPost RR (CallS _ _ _ call1 >>= RetS) t2 ->
  spec_refines RPre RPost RR (CallS _ _ _ call1) t2.
Proof. intro; rewrite <- (bind_ret_r (CallS _ _ _ _)); eauto. Qed.

(* Add a bind to a RetS to a CallS on the right *)
Lemma spec_refines_call_bind_ret_r (E1 E2 : EncType) Γ1 Γ2 R1 R2
      (RPre : SpecPreRel E1 E2 Γ1 Γ2)
      (RPost : SpecPostRel E1 E2 Γ1 Γ2)
      t1 (call2 : FrameCallWithRet Γ2 R2) (RR : Rel R1 R2) :
  spec_refines RPre RPost RR t1 (CallS _ _ _ call2 >>= RetS) ->
  spec_refines RPre RPost RR t1 (CallS _ _ _ call2).
Proof. intro H; rewrite <- (bind_ret_r (CallS _ _ _ _)); eauto. Qed.





(* Add a precondition relation for a new frame on the FunStack *)
Definition pushPreRel {E1 E2 : EncType} {Γ1 Γ2}
           (precond : Rel (FrameCall Γ1) (FrameCall Γ2))
           (RPre : SpecPreRel E1 E2 Γ1 Γ2) :
  SpecPreRel E1 E2 Γ1 Γ2 :=
  fun a1 a2 => match a1,a2 with
               | inl args1, inl args2 => precond args1 args2
               | inr ev1, inr ev2 => RPre ev1 ev2
               | _, _ => False
               end.

(* Add a postcondition relation for a new frame on the FunStack *)
Definition pushPostRel {E1 E2 : EncType} {Γ1 Γ2 frame1 frame2}
           (postcond : PostRel (FrameCall frame1) (FrameCall frame2))
           (RPost : SpecPostRel E1 E2 Γ1 Γ2) :
  SpecPostRel E1 E2 (frame1 :: Γ1) (frame2 :: Γ2) :=
  fun a1 a2 => match a1,a2 with
               | inl args1, inl args2 => postcond args1 args2
               | inr ev1, inr ev2 => RPost ev1 ev2
               | _, _ => fun _ _ => False
               end.

Lemma spec_refines_multifix (E1 E2 : EncType) Γ1 Γ2 frame1 frame2 
      (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
      (bodies1 : FrameTuple E1 (frame1 :: Γ1) frame1)
      (bodies2 : FrameTuple E2 (frame2 :: Γ2) frame2)
      (call1 : FrameCall frame1) (call2 : FrameCall frame2)
      (RR : Rel (encodes call1) (encodes call2))
      (precond : Rel (FrameCall frame1) (FrameCall frame2))
      (postcond : PostRel (FrameCall frame1) (FrameCall frame2)) :
  precond call1 call2 ->
  (forall r1 r2, postcond call1 call2 r1 r2 -> RR r1 r2) ->
  (forall call1' call2',
      precond call1' call2' ->
      spec_refines (pushPreRel precond RPre) (pushPostRel postcond RPost)
                   (postcond call1' call2')
                   (applyFrameTuple _ _ _ bodies1 call1')
                   (applyFrameTuple _ _ _ bodies2 call2')) ->
  spec_refines RPre RPost RR
               (MultiFixS E1 Γ1 frame1 bodies1 call1)
               (MultiFixS E2 Γ2 frame2 bodies2 call2).

Proof.
  intros Hcalls HRR Hbody.
  unfold MultiFixS. 
  eapply padded_refines_interp_mrec_spec with (RPreInv := precond) (RPostInv := postcond).
  - intros. apply Hbody in H. eapply padded_refines_monot; try apply H; auto; clear - E1.
    + intros call1 call2 Hcall. 
      destruct call1; destruct call2; cbn in *; try contradiction;
        constructor; auto.
    + intros call1 call2 r1 r2 H. destruct H; auto.
  - apply Hbody in Hcalls.
    eapply padded_refines_monot; try apply Hcalls; auto; clear - E1.
    + intros call1 call2 Hcall. 
      destruct call1; destruct call2; cbn in *; try contradiction;
        constructor; auto.
    + intros call1 call2 r1 r2 H. destruct H; auto.
Qed.

(* The bind of one multifix refines the bind of another if: the recursive calls
   which start the multifixes are related to each other by the supplied
   precondition; the bodies of the multifixes refine each other and return
   values that satisfy the supplied postcondition for all calls that satisfy the
   precondition; and that the bind continuations refine each other for all
   outputs in the supplied postcondition *)
Lemma spec_refines_multifix_bind (E1 E2 : EncType) Γ1 Γ2 frame1 frame2 R1 R2
      (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2) RR
      (bodies1 : FrameTuple E1 (frame1 :: Γ1) frame1)
      (bodies2 : FrameTuple E2 (frame2 :: Γ2) frame2)
      (call1 : FrameCall frame1) (call2 : FrameCall frame2)
      (k1 : FrameCallRet frame1 call1 -> SpecM E1 Γ1 R1)
      (k2 : FrameCallRet frame2 call2 -> SpecM E2 Γ2 R2)
      (precond : Rel (FrameCall frame1) (FrameCall frame2))
      (postcond : PostRel (FrameCall frame1) (FrameCall frame2)) :
  precond call1 call2 ->
  (forall call1' call2',
      precond call1' call2' ->
      spec_refines (pushPreRel precond RPre) (pushPostRel postcond RPost)
                   (postcond call1' call2')
                   (applyFrameTuple _ _ _ bodies1 call1')
                   (applyFrameTuple _ _ _ bodies2 call2')) ->
  (forall r1 r2,
      postcond call1 call2 r1 r2 ->
      spec_refines RPre RPost RR (k1 r1) (k2 r2)) ->
  spec_refines RPre RPost RR
               (MultiFixS E1 Γ1 frame1 bodies1 call1 >>= k1)
               (MultiFixS E2 Γ2 frame2 bodies2 call2 >>= k2).
Proof.
  intros.
  eapply padded_refines_bind; try eapply spec_refines_multifix; eauto.
Qed.

(* Build a RecFrame with a single, unary function *)
Definition unary1Frame (A B : Type) : RecFrame :=
  cons (LRT_Fun A (fun _ => LRT_Ret B)) nil.

Notation unary1Call x := (mkFrameCall (unary1Frame _ _) 0 x).


(* The total correctness specification *)
Definition total_spec {E Γ A B} `{QuantType B}
           (pre : A -> Prop) (post : A -> B -> Prop) (a : A) : SpecM E Γ B :=
  AssumeS (pre a);;
  b <- ExistsS B;;
  AssertS (post a b);;
  RetS b.

Definition uncall_unary1Frame {A B} (c : FrameCall (unary1Frame A B)) : A.
destruct c. cbn in args. destruct n.
- destruct args as [a ?]. exact a.
- destruct args as [[] []].
Defined.

Definition call_unary1Frame {A B} (c : FrameCall (unary1Frame A B)) (b : B) : encodes c.
destruct c. destruct n. destruct args. cbn. exact b.
cbn in args. destruct args as [ [] _].
Defined.

(* The one-step unfolding of total_spec with recursive calls *)
Definition total_spec_fix_body {E Γ A B} `{QuantType A} `{QuantType B}
           (pre : A -> Prop) (post : A -> B -> Prop) (rdec : A -> A -> Prop)
           (a : A) : SpecM E (unary1Frame A B :: Γ) B :=
  AssumeS (pre a);;
  n <- ExistsS nat;;
  trepeat n (a' <- ExistsS A;;
             AssertS (pre a' /\ rdec a' a);;
             CallS E Γ _ (mkFrameCall (unary1Frame A B) 0 a'));;
  b <- ExistsS B;;
  AssertS (post a b);;
  RetS b.

(* total_spec defined with recursive calls, primarily written as part of a proof*)
Definition total_spec_fix {E Γ A B} `{QuantType A} `{QuantType B}
           (pre : A -> Prop) (post : A -> B -> Prop) (rdec : A -> A -> Prop)
           (a : A) : SpecM E Γ B.
  eapply @interp_mrec_spec with (D := (FrameCall (unary1Frame A B)));
    try  (apply (total_spec_fix_body pre post rdec a)).
  clear a.
  intros call. specialize (uncall_unary1Frame call) as a. cbn. 
  eapply EnTree.bind.
  exact (total_spec_fix_body pre post rdec (uncall_unary1Frame call)).
  intros b. exact (Ret (call_unary1Frame call b)).
Defined.

(* Add a precondition relation for proving total_spec refinement *)
Definition pushTSPreRel {E1 E2 : EncType} {Γ1 Γ2 frame1 A2 B2}
           (tsPre : A2 -> Prop)
           (precond : Rel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
           (RPre : SpecPreRel E1 E2 Γ1 Γ2) :
  SpecPreRel E1 E2 (frame1 :: Γ1) (unary1Frame A2 B2 :: Γ2) :=
  fun a1 a2 => match a1,a2 with
               | inl args1, inl (FrameCallOfArgs _ 0 (existT _ a2 _)) =>
                 tsPre a2 /\ precond args1 (unary1Call a2)
               | inr ev1, inr ev2 => RPre ev1 ev2
               | _, _ => False
               end.

(* Add a postcondition relation for proving total_spec refinement *)
Definition pushTSPostRel {E1 E2 : EncType} {Γ1 Γ2 frame1 A2 B2}
           (tsPost : A2 -> B2 -> Prop)
           (postcond : PostRel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
           (RPost : SpecPostRel E1 E2 Γ1 Γ2) :
  SpecPostRel E1 E2 (frame1 :: Γ1) (unary1Frame A2 B2 :: Γ2) :=
  fun a1 a2 => match a1,a2 return encodes a1 -> encodes a2 -> Prop with
               | inl args1, inl (FrameCallOfArgs _ 0 (existT _ a2 _)) =>
                 fun r1 b2 => tsPost a2 b2 /\ postcond args1 (unary1Call a2) r1 b2
               | inr a1', inr a2' => RPost a1' a2'
               | _, _ => fun _ _ => False
               end.

(* Add a postcondition to the return relation for proving total_spec refinement *)
Definition pushTSRR {frame1 A2 B2}
           (tsPost : A2 -> B2 -> Prop)
           (postcond : PostRel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
           (call1 : FrameCall frame1) (a2 : A2) :
  Rel (FrameCallRet frame1 call1) B2 :=
  fun r1 r2 => tsPost a2 r2 /\ postcond call1 (unary1Call a2) r1 r2.

Ltac quantr := apply padded_refines_assumer || apply padded_refines_assertr ||
                     apply interp_mrec_spec_assumer || apply interp_mrec_spec_assertr || 
                     apply padded_refines_exists_specr || 
                     apply padded_refines_forall_specr ||
                     apply interp_mrec_spec_forall_specr ||
                     apply interp_mrec_spec_exists_specr
.

Ltac quantl := apply padded_refines_assumel || apply padded_refines_assertl ||
                     apply interp_mrec_spec_assumel || apply interp_mrec_spec_assertl ||
                     apply padded_refines_exists_specl || 
                     apply padded_refines_forall_specl ||
                     apply interp_mrec_spec_forall_specl ||
                     apply interp_mrec_spec_exists_specl.

Lemma total_spec_fix_refines_total_spec_aux1:
  forall (E : EncType) (Γ : FunStack) (A B : Type) (H : QuantType A) (H0 : QuantType B)
    (pre : A -> Prop) (post : Rel A B) (rdec : Rel A A) (a : A),
    strict_refines
     (interp_mrec_spec
        (fun call : FrameCall (unary1Frame A B) =>
           EnTree.bind
             (EnTree.bind (AssumeS (pre (uncall_unary1Frame call)))
                (fun _ : unit =>
                    EnTree.bind (ExistsS nat) (fun n : nat =>
                       EnTree.bind
                         (trepeat n
                           (EnTree.bind (ExistsS A)
                                        (fun a' : A =>
                                           EnTree.bind (AssertS (pre a' /\ rdec a' (uncall_unary1Frame call)))
                                                       (fun _ : unit =>
                                                          CallS E Γ (unary1Frame A B)
                                                                (FrameCallOfArgs (unary1Frame A B) 0
                                                                                 (existT (fun _ : A => unit) a' tt))))))
                         (fun _ : unit =>
                            EnTree.bind (exists_spec B)
                                        (fun b : B =>
                                           EnTree.bind (AssertS (post (uncall_unary1Frame call) b))
                                                       (fun _ : unit => RetS b)))))) (fun b : B => RetS (call_unary1Frame call b)))
        (CallS E Γ (unary1Frame A B)
               (FrameCallOfArgs (unary1Frame A B) 0 (existT (fun _ : A => unit) a tt))))
     (total_spec_fix pre post rdec a).
Proof.
  intros E Γ A B H H0 pre post rdec a. setoid_rewrite interp_mrec_spec_inl at 1.
  rewrite tau_eutt. match goal with |- strict_refines (interp_mrec_spec ?b _) _ =>
                                      set b as body end.
  eapply padded_refines_interp_mrec_spec with (RPreInv := eq) (RPostInv := PostRelEq).
  - intros. subst. destruct d2.
    destruct n. 2 : destruct args as [ [] _].
    destruct args as [a' []]. cbn. cbn. eapply padded_refines_bind with (RR := eq).
    2 : { intros. apply padded_refines_ret. subst. constructor. }
    quantr. intros. apply padded_refines_assumel. auto.
    apply padded_refines_exists_specl. intros.
    quantr. exists a0. eapply padded_refines_bind with (RR := eq).
    + eapply padded_refines_monot; try apply strict_refines_refl; intros; subst.
      destruct x1; constructor; auto. destruct PR. destruct H2. constructor.
      destruct H2. constructor. auto.
    + intros. subst. quantl. intros. quantr. exists a1. quantl.
      intros. quantr. auto. apply padded_refines_ret. auto.
 - cbn. quantr. intros. (* lets get a better way to rewrite bind_bind *)
   eapply padded_refines_monot with (RPre1 := eq) (RPost1 := PostRelEq) (RR1 := eq); eauto.
   + intros. subst. destruct x1; constructor; auto.
   + intros. destruct e1; dependent destruction PR. dependent destruction H6.
     constructor. dependent destruction H6. constructor.
   + repeat apply padded_refines_bind_bind_l. quantl. eexists. eauto.
     apply padded_refines_ret_bind_l. apply padded_refines_bind_bind_l.
     eapply padded_refines_bind. apply strict_refines_refl.
     intros. subst. apply padded_refines_bind_bind_l.
     eapply padded_refines_bind. apply strict_refines_refl.
     intros [] [] _. apply padded_refines_bind_bind_l. 
     quantl. intros. quantr. exists a0. apply padded_refines_bind_bind_l.
     quantl. intros. quantr. auto. repeat apply padded_refines_ret_bind_l.
     apply padded_refines_ret. cbv. auto.
Qed.
   
Lemma total_spec_fix_refines_total_spec {E Γ A B} `{QuantType A} `{QuantType B}
           (pre : A -> Prop) (post : A -> B -> Prop) (rdec : A -> A -> Prop)
           (a : A) : 
  well_founded rdec ->
  strict_refines (total_spec_fix pre post rdec a) (@total_spec E Γ A B _ pre post a).
Proof.
  intros Hwf. revert a. apply well_founded_ind with (R := rdec). auto.
  intros x Hind. unfold total_spec_fix. unfold total_spec_fix_body. cbn.
  match goal with |- strict_refines (interp_mrec_spec ?b _) _ =>
                    set b as body end.
  quantr. intro. quantl. auto. apply interp_mrec_spec_exists_specl. intros n.
  induction n.
  - cbn. rewrite bind_ret_l. apply interp_mrec_spec_exists_specl.
    intros b. quantr. exists b. apply interp_mrec_spec_assertl.
    intros. quantr. auto. rewrite interp_mrec_spec_ret.
    apply padded_refines_ret. auto.
  - cbn. repeat rewrite bind_bind. apply interp_mrec_spec_exists_specl.
    intros a. rewrite bind_bind. apply interp_mrec_spec_assertl.
    intros [Hpre Hdec]. rewrite interp_mrec_spec_bind.
    specialize (Hind a Hdec). 
    match goal with |- padded_refines eq PostRelEq eq (EnTree.bind ?tf _ ) _ =>
                      assert (strict_refines tf (total_spec_fix pre post rdec a)) end.
    apply total_spec_fix_refines_total_spec_aux1.
    eapply padded_refines_weaken_r
           with (phi2 := EnTree.bind (total_spec pre post a)  (fun _  =>
              EnTree.bind (exists_spec B)
                (fun b : B => EnTree.bind (AssertS (post x b)) (fun _ : unit => RetS b))) )
    .
    { eapply padded_refines_bind; eauto. eapply padded_refines_weaken_l; eauto. } 
    clear - Hwf Hpre Hdec. cbn.
    apply padded_refines_bind_bind_l. quantl. auto.
    apply padded_refines_bind_bind_l. quantl. intros b. apply padded_refines_bind_bind_l.
    quantl. intros. rewrite bind_ret_l. quantl. intros bf.
    quantl. intros Hbf. quantr. exists bf. quantr. auto. apply padded_refines_ret.
    auto.
Qed.

Definition lift_ts_pre
  {frame1 : RecFrame} {A2 B2 : Type} (tsPre : A2 -> Prop)
  (precond : Rel (FrameCall frame1) (FrameCall (unary1Frame A2 B2))) :
  Rel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)) :=
  fun c1 c2 => exists a : A2, FrameCallOfArgs (unary1Frame A2 B2) 0 (existT _ a tt) = c2 /\ precond c1 (unary1Call a) /\ tsPre a.

Definition lift_ts_post:
  forall {frame1 : RecFrame} {A2 B2 : Type} (tsPost : A2 -> B2 -> Prop)
    (postcond : PostRel (FrameCall frame1) (FrameCall (unary1Frame A2 B2))),
    PostRel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)).
  intros frame1 A2 B2 tsPost postcond.
  intros c1 c2 a b.
  specialize (postcond c1 c2).
  destruct c2. cbn in b. destruct n.
  cbn in b. destruct args. apply (tsPost x b /\ postcond a b).
  destruct args. destruct x.
Defined.
(*with some strategic lemmas this should be doable *)

Lemma spec_refines_total_spec_monot_aux1:
  forall (E1 E2 : EncType) (Γ1 Γ2 : FunStack) (frame1 : RecFrame) (A2 B2 : Type) (RPre : SpecPreRel E1 E2 Γ1 Γ2)
    (precond : Rel (FrameCall frame1) (FrameCall (unary1Frame A2 B2))) (tsPre : A2 -> Prop)
    (x0 : FrameCall frame1 +
            (fix FunStackE (E : Type) (Γ : FunStack) {struct Γ} : Type :=
               match Γ with
               | nil => (ErrorE + E)%type
               | frame :: Γ' => (FrameCall frame + FunStackE E Γ')%type
               end) E1 Γ1) (x1 : FrameCall (unary1Frame A2 B2) + FunStackE E2 Γ2),
    pushTSPreRel tsPre precond RPre x0 x1 -> HeterogeneousRelations.sum_rel (lift_ts_pre tsPre precond) RPre x0 x1.
Proof.
  intros E1 E2 Γ1 Γ2 frame1 A2 B2 RPre preEq pre.
  intros x c PR. destruct x.
  - cbn in PR. destruct c.
    + destruct f0. destruct n. destruct args. 2 :destruct PR. 
      cbn. constructor. exists x. destruct l. destruct PR. auto.
    + destruct PR.
  - destruct c; try (destruct PR; fail). red in PR. constructor. auto.
Qed.

Lemma spec_refines_total_spec_monot_aux2:
  forall (E1 E2 : EncType) (Γ1 Γ2 : FunStack) (frame1 : RecFrame) (A2 B2 : Type) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
    (postcond : PostRel (FrameCall frame1) (FrameCall (unary1Frame A2 B2))) (tsPost : A2 -> B2 -> Prop)
    (e1 : FrameCall frame1 +
            (fix FunStackE (E : Type) (Γ : FunStack) {struct Γ} : Type :=
               match Γ with
               | nil => (ErrorE + E)%type
               | frame :: Γ' => (FrameCall frame + FunStackE E Γ')%type
               end) E1 Γ1) (e2 : FrameCall (unary1Frame A2 B2) + FunStackE E2 Γ2) (x0 : encodes e1) (x1 : encodes e2),
    SumPostRel (lift_ts_post tsPost postcond) RPost e1 e2 x0 x1 -> pushTSPostRel tsPost postcond RPost e1 e2 x0 x1.
Proof.
  intros E1 E2 Γ1 Γ2 frame1 A2 B2 RPost postcond tsPost.
  intros c1 c2 a b Hab.
  destruct c1.
  - destruct Hab; auto.
    destruct e2. cbn in args. destruct n. cbn in args.
    2 : destruct args as [ [] _ ].
    destruct args as [ a2 [] ]. auto.
  - cbn in *.  destruct c2; auto.
    + dependent destruction Hab.
    + dependent destruction Hab. auto.
Qed.

(*
Lemma spec_refines_total_spec_post_aux {E1 Γ1 E2 Γ2 A B} `{EncodingType E1} `{EncodingType E2} `{QuantType A} `{QuantType B}
           (pre : A -> Prop) (post : A -> B -> Prop) (rdec : A -> A -> Prop) (phi1) : 
. *)

Axiom inj_FrameCallOfArgs : forall frame n x y, FrameCallOfArgs frame n x = FrameCallOfArgs frame n y ->
                                        x = y.

Lemma spec_refines_total_spec (E1 E2 : EncType) Γ1 Γ2 frame1
      A2 B2 `{QuantType A2} `{QuantType B2}
      (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
      (bodies1 : FrameTuple E1 (frame1 :: Γ1) frame1)
      (call1 : FrameCall frame1) (a2 : A2)
      (RR : Rel (FrameCallRet frame1 call1) B2)
      (precond : Rel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
      (postcond : PostRel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
      (tsPre : A2 -> Prop) (tsPost : A2 -> B2 -> Prop)
      (rdec : A2 -> A2 -> Prop) :
  well_founded rdec ->
  precond call1 (unary1Call a2) ->
  (forall r1 r2, tsPost a2 r2 -> postcond call1 (unary1Call a2) r1 r2 -> RR r1 r2) ->
  (forall call1' a2',
      precond call1' (unary1Call a2') ->
      spec_refines (pushTSPreRel tsPre precond RPre)
                   (pushTSPostRel tsPost postcond RPost)
                   (pushTSRR tsPost postcond call1' a2')
                   (applyFrameTuple _ _ _ bodies1 call1')
                   (total_spec_fix_body tsPre tsPost rdec a2')) ->
  spec_refines RPre RPost RR
               (MultiFixS E1 Γ1 frame1 bodies1 call1)
               (total_spec tsPre tsPost a2).
Proof.
  intros Hwf Hca HPost HPost'. intros.
  eapply total_spec_fix_refines_total_spec in Hwf as Hstrict. Unshelve. all : auto.
  eapply padded_refines_weaken_l; eauto.
  apply padded_refines_weaken_l with (phi2 := AssumeS (tsPre a2);; (total_spec_fix tsPre tsPost rdec a2)).
  {
    quantr. intros. quantl. auto. quantl. auto. reflexivity.
  }
  quantr. intros Ha2.
  eapply padded_refines_interp_mrec_spec with (RPreInv := lift_ts_pre tsPre precond)
                                              (RPostInv := lift_ts_post tsPost postcond). Unshelve.
  - clear Hca Hstrict . rename a2 into a0. intros c1 c2 Hpre. destruct c2. destruct n.
    2 : { destruct args as [ [] _]. }
    cbn in args. destruct args as [a2 [] ]. simpl. setoid_rewrite bind_ret_r.
    idtac. red in Hpre. destruct Hpre as [a2' [Heq [H1 H2] ]].
    assert (a2 = a2'). apply inj_FrameCallOfArgs in Heq. dependent destruction Heq.
    auto.
    subst.
    eapply padded_refines_monot; try apply HPost'; eauto.
    + apply spec_refines_total_spec_monot_aux1.
    + apply spec_refines_total_spec_monot_aux2.
  - eapply padded_refines_monot; try eapply HPost'; eauto.
    + apply spec_refines_total_spec_monot_aux1.
    + apply spec_refines_total_spec_monot_aux2.
    + intros. destruct PR. auto.
Qed.


(***
 *** Hints for automation
 ***)

Create HintDb refines.
Create HintDb prepostcond.

(* If nothing else works, shelve the current refinement goal *)
#[global] Hint Extern 999 (spec_refines _ _ _ _ _) => shelve : refines.


(** IntroArg Definition and Hints **)

(* Classes of variables and their associated naming conventions *)
Inductive ArgName := Any | RetAny | Hyp | Call |
                     SAWLet | Assert | Assume | Exists | Forall |
                     If | Match | Destruct.
Ltac argName n :=
  match n with
  | Any      => fresh "a"
  | RetAny   => fresh "r"
  | Hyp      => fresh "H"
  | Call     => fresh "call"
  | SAWLet   => fresh "e_let"
  | Assert   => fresh "e_assert"
  | Assume   => fresh "e_assume"
  | Exists   => fresh "e_exists"
  | Forall   => fresh "e_forall"
  | If       => fresh "e_if"
  | Match    => fresh "e_match"
  | Destruct => fresh "e_destruct"
  end.

(* IntroArg marks a goal which introduces a variable. This is used to control
   how variables are introduced, allowing them to be eliminated and to give them
   meaningful names using argName above *)
Polymorphic Definition IntroArg (n : ArgName) A (goal : A -> Type) :=
  forall a, goal a.

#[global] Hint Opaque IntroArg : refines prepostcond.

Polymorphic Lemma IntroArg_fold n A goal : IntroArg n A goal -> forall a, goal a.
Proof. intros H a; exact (H a). Qed.

(* Polymorphic Lemma IntroArg_unfold n A (goal : A -> Prop) : (forall a, goal a) -> IntroArg n A goal. *)
(* Proof. unfold IntroArg; intro H; exact H. Qed. *)

Ltac IntroArg_intro e := intro e.

Ltac IntroArg_forget := let e := fresh in intro e; clear e.

Polymorphic Definition IntroArg_beta n A (f : A -> Type) x goal :
  IntroArg n (f x) goal ->
  IntroArg n ((fun x' => f x') x) goal := fun f x => f x.

Polymorphic Definition IntroArg_prod n A B (goal : A * B -> Type) :
  IntroArg n A (fun a => IntroArg n B (fun b => goal (a , b))) ->
  IntroArg n _ goal := fun H '(a, b) => H a b.

Polymorphic Definition IntroArg_sigT n A P (goal : sigT P -> Type) :
  IntroArg n A (fun a => IntroArg n (P a) (fun p => goal (existT _ a p))) ->
  IntroArg n _ goal := fun H '(a ; p) => H a p.

Polymorphic Definition IntroArg_unit n (goal : unit -> Type) :
  goal tt -> IntroArg n _ goal := fun H 'tt => H.

Polymorphic Lemma IntroArg_and n P Q (goal : P /\ Q -> Prop)
  : IntroArg n P (fun p => IntroArg n Q (fun q => goal (conj p q))) ->
    IntroArg n _ goal.
Proof. intros H [ p q ]; apply H. Qed.

Polymorphic Lemma IntroArg_true n (goal : True -> Prop) : goal I -> IntroArg n _ goal.
Proof. intros H []; eauto. Qed.

Polymorphic Lemma IntroArg_false n (goal : False -> Prop) : IntroArg n _ goal.
Proof. intros []. Qed.

Polymorphic Lemma IntroArg_eq_prod_const n A B (a a' : A) (b b' : B) (goal : Type)
  : IntroArg n (a = a') (fun _ => IntroArg n (b = b') (fun _ => goal)) ->
    IntroArg n ((a,b) = (a',b')) (fun _ => goal).
Proof. intros H eq; apply H; injection eq; eauto. Qed.

Polymorphic Lemma IntroArg_eq_sigT_const n A B (a a' : A) (b b' : B) (goal : Type)
  : IntroArg n (a = a') (fun _ => IntroArg n (b = b') (fun _ => goal)) ->
    IntroArg n (existT _ a b = existT _ a' b') (fun _ => goal).
Proof. intros H eq; apply H; injection eq; eauto. Qed.

Polymorphic Lemma IntroArg_eq_dep1_const n A B (a : A) (b b' : B a) (goal : Type)
  : IntroArg n (b = b') (fun _ => goal) ->
    IntroArg n (eq_dep1 A B a b a b') (fun _ => goal).
Proof.
  intro H. unfold IntroArg in *. intro Heqdep. apply H.
  apply eq_dep1_dep in Heqdep. apply eq_dep_eq. auto.
Qed.

Polymorphic Lemma IntroArg_eq_rect_const_l n A B (a1 a2 : A) b1 b2 eq goal :
  IntroArg n (b1 = b2) (fun _ => goal) ->
  IntroArg n (eq_rect a1 (fun _ => B) b1 a2 eq = b2) (fun _ => goal).
Proof. destruct eq; do 2 intro; eauto. Qed.

Polymorphic Lemma IntroArg_eqPostRel n E Γ e a1 a2 (goal : _ -> Prop) :
  IntroArg n (a1 = a2) (fun pf => goal (eq_dep1_intro _ _ _ _ _ _ (eq_refl e) pf)) ->
  IntroArg n (@eqPostRel E Γ e e a1 a2) goal.
Proof.
  intros H H0; dependent destruction H0.
  apply H.
Qed.

Polymorphic Lemma IntroArg_pushPreRel_inl n E1 E2 Γ1 Γ2 frame1 frame2
            (precond : Rel (FrameCall frame1) (FrameCall frame2))
            (RPre : SpecPreRel E1 E2 Γ1 Γ2) e1 e2 (goal : _ -> Prop) :
  IntroArg n (precond e1 e2) goal ->
  IntroArg n (@pushPreRel E1 E2 Γ1 Γ2 frame1 frame2
                          precond RPre (inl e1) (inl e2)) goal.
Proof. intro H. apply H. Qed.

Polymorphic Lemma IntroArg_pushPreRel_inr n E1 E2 Γ1 Γ2 frame1 frame2
            (precond : Rel (FrameCall frame1) (FrameCall frame2))
            (RPre : SpecPreRel E1 E2 Γ1 Γ2) e1 e2 (goal : _ -> Prop) :
  IntroArg n (RPre e1 e2) goal ->
  IntroArg n (@pushPreRel E1 E2 Γ1 Γ2 frame1 frame2
                          precond RPre (inr e1) (inr e2)) goal.
Proof. intro H. apply H. Qed.

Polymorphic Lemma IntroArg_pushPostRel_inl n E1 E2 Γ1 Γ2 frame1 frame2
            (postcond : PostRel (FrameCall frame1) (FrameCall frame2))
            (RPost : SpecPostRel E1 E2 Γ1 Γ2)
            (call1 : FrameCall frame1) (call2 : FrameCall frame2)
            r1 r2 (goal : _ -> Prop) :
  IntroArg n (postcond _ _ r1 r2) goal ->
  IntroArg n (@pushPostRel E1 E2 Γ1 Γ2 frame1 frame2
                           postcond RPost (inl call1) (inl call2) r1 r2) goal.
Proof. intro H. apply H. Qed.

Polymorphic Lemma IntroArg_pushPostRel_inr n E1 E2 Γ1 Γ2 frame1 frame2
            (postcond : PostRel (FrameCall frame1) (FrameCall frame2))
            (RPost : SpecPostRel E1 E2 Γ1 Γ2)
            e1 e2 r1 r2 (goal : _ -> Prop) :
  IntroArg n (RPost _ _ r1 r2) goal ->
  IntroArg n (@pushPostRel E1 E2 Γ1 Γ2 frame1 frame2
                           postcond RPost (inr e1) (inr e2) r1 r2) goal.
Proof. intro H. apply H. Qed.

Polymorphic Lemma IntroArg_pushTSPreRel_inl n E1 E2 Γ1 Γ2 frame1 A2 B2
            (tsPre : A2 -> Prop)
            (precond : Rel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
            (RPre : SpecPreRel E1 E2 Γ1 Γ2)
            args1 a2 (goal : _ -> Prop) :
  IntroArg n (tsPre a2 /\ precond args1 (unary1Call a2)) goal ->
  IntroArg n (@pushTSPreRel E1 E2 Γ1 Γ2 frame1 A2 B2
                            tsPre precond RPre (inl args1)
                            (inl (mkFrameCall (unary1Frame A2 B2) 0 a2))) goal.
Proof. intro H. apply H. Qed.

Polymorphic Lemma IntroArg_pushTSPreRel_inr n E1 E2 Γ1 Γ2 frame1 A2 B2
            (tsPre : A2 -> Prop)
            (precond : Rel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
            (RPre : SpecPreRel E1 E2 Γ1 Γ2)
            e1 e2 (goal : _ -> Prop) :
  IntroArg n (RPre e1 e2) goal ->
  IntroArg n (@pushTSPreRel E1 E2 Γ1 Γ2 frame1 A2 B2
                            tsPre precond RPre (inr e1) (inr e2)) goal.
Proof. intro H. apply H. Qed.

Polymorphic Lemma IntroArg_pushTSPostRel_inl n E1 E2 Γ1 Γ2 frame1 A2 B2
            (tsPost : A2 -> B2 -> Prop)
            (postcond : PostRel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
            (RPost : SpecPostRel E1 E2 Γ1 Γ2)
            args1 a2 r1 b2 (goal : _ -> Prop) :
  IntroArg n (tsPost a2 b2 /\ postcond args1 (unary1Call a2) r1 b2) goal ->
  IntroArg n (@pushTSPostRel E1 E2 Γ1 Γ2 frame1 A2 B2
                             tsPost postcond RPost (inl args1)
                             (inl (mkFrameCall (unary1Frame A2 B2) 0 a2)) r1 b2) goal.
Proof. intro H. apply H. Qed.

Polymorphic Lemma IntroArg_pushTSPostRel_inr n E1 E2 Γ1 Γ2 frame1 A2 B2
            (tsPost : A2 -> B2 -> Prop)
            (postcond : PostRel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
            (RPost : SpecPostRel E1 E2 Γ1 Γ2)
            e1 e2 r1 r2 (goal : _ -> Prop) :
  IntroArg n (RPost e1 e2 r1 r2) goal ->
  IntroArg n (@pushTSPostRel E1 E2 Γ1 Γ2 frame1 A2 B2
                             tsPost postcond RPost (inr e1) (inr e2) r1 r2) goal.
Proof. intro H. apply H. Qed.

Polymorphic Lemma IntroArg_pushTSRR n frame1 A2 B2
            (tsPost : A2 -> B2 -> Prop)
            (postcond : PostRel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
            call1 a2 r1 r2 (goal : _ -> Prop) :
  IntroArg n (tsPost a2 r2 /\ postcond call1 (unary1Call a2) r1 r2) goal ->
  IntroArg n (@pushTSRR frame1 A2 B2 tsPost postcond call1 a2 r1 r2) goal.
Proof. intro H. apply H. Qed.

(*
Polymorphic Lemma IntroArg_FrameCall_nil n goal :
  IntroArg n (FrameCall nil) goal.
Proof.
  intro call. destruct call. destruct args. destruct x.
Qed.

Polymorphic Lemma IntroArg_FrameCall_cons n lrt frame goal :
  IntroArg n (LRTInput lrt)
           (fun args => goal (FrameCallOfArgs (lrt :: frame) 0 args)) ->
  IntroArg n (FrameCall frame) (fun call => goal (consFrameCall call)) ->
  IntroArg n (FrameCall (cons lrt frame)) goal.
Proof.
  intros H H0. intro call. destruct call. destruct n0.
  - apply H.
  - apply (H0 (FrameCallOfArgs frame n0 args)).
Qed.
*)

(* A FrameCall whose index is guaranteed to be below a given upper bound *)
Definition FrameCallIxBelow frame k : Type@{entree_u} :=
  { call : FrameCall frame | FrameCallIndex call < k }.

Definition incrFrameCallIxBelow {frame k} (fcib : FrameCallIxBelow frame k) :
  FrameCallIxBelow frame (S k) :=
  match fcib with
  | exist _ call ix_lt => exist _ call (le_S _ _ ix_lt)
  end.

Definition mkFrameCallIxBelow {frame k} (args : LRTInput (nthLRT frame k)) :
  FrameCallIxBelow frame (S k) :=
  exist _ (FrameCallOfArgs _ k args) (le_n _).

Polymorphic Definition IntroArg_FrameCall n frame goal :
  IntroArg n (FrameCallIxBelow frame (length frame))
           (fun fcib => goal (proj1_sig fcib)) ->
  IntroArg n (FrameCall frame) goal :=
  fun H call => H (exist _ call (FrameCallIndexLt frame call)).

Polymorphic Definition IntroArg_FrameCallIxBelow0 n frame goal :
  IntroArg n (FrameCallIxBelow frame 0) goal.
Proof.
  intro. destruct a. elimtype False. eapply Lt.lt_n_0. eassumption.
Defined.

Lemma le_n_equals_le_n n (pf : n <= n) : pf = le_n n.
Proof.
  assert (forall n m (pf : n <= m) (e : n = m),
             pf = eq_rect n (fun x => n <= x) (le_n n) m e).
  - clear n pf. intros n m pf. destruct pf.
    + intros. apply eq_rect_eq_dec. apply Nat.eq_dec.
    + intros. subst n. elimtype False.
      eapply (Lt.lt_not_le _ _ pf). apply le_n.
  - etransitivity; [ apply (H _ _ _ (eq_refl _)) | ].
    symmetry. apply eq_rect_eq_dec. apply Nat.eq_dec.
Qed.

(* NOTE: this should be provable just using UIP in a manner similar to the
above, but we use full proof irrelevance because it is easier *)
Lemma le_S_equals_le_S n m (pf : n <= S m) (pf2 : n <= m) :
  { pf' | pf = le_S _ _ pf' }.
Proof.
  exists pf2. apply proof_irrelevance.
Qed.

Polymorphic Lemma IntroArg_FrameCallIxBelowS n frame k goal :
  IntroArg n (FrameCallIxBelow frame k)
           (fun fcib => goal (incrFrameCallIxBelow fcib)) ->
  IntroArg n (LRTInput (nthLRT frame k))
           (fun args => goal (mkFrameCallIxBelow args)) ->
  IntroArg n (FrameCallIxBelow frame (S k)) goal.
Proof.
  intros H H0 [ call ix_lt ].
  destruct (le_decide _ _ (Le.le_S_n _ _ ix_lt)).
  - destruct (le_S_equals_le_S _ _ ix_lt g) as [ pf' e ]. rewrite e.
    apply (H (exist _ call pf')).
  - destruct call. simpl in e; subst n0.
    rewrite (le_n_equals_le_n _ ix_lt).
    apply H0.
Qed.

Polymorphic Definition IntroArg_LRTInput_Ret {n R goal} :
  goal tt -> IntroArg n (LRTInput (LRT_Ret R)) goal :=
  fun H 'tt => H.

Polymorphic Definition IntroArg_LRTInput_Fun {n A lrt goal} :
  IntroArg n A (fun a => IntroArg n (LRTInput (lrt a)) (fun args => goal (existT _ a args))) ->
  IntroArg n (LRTInput (LRT_Fun A lrt)) goal :=
  fun H '(existT _ x l) => H x l.

Polymorphic Definition IntroArg_LRTOutput_Ret {n R goal} :
  IntroArg n R goal ->
  IntroArg n (LRTOutput (LRT_Ret R) tt) goal :=
  fun H r => H r.

Polymorphic Definition IntroArg_LRTOutput_Fun {n A lrt a args goal} :
  IntroArg n (LRTOutput (lrt a) args) goal ->
  IntroArg n (LRTOutput (LRT_Fun A lrt) (existT _ a args)) goal :=
  fun H r => H r.

Ltac IntroArg_intro_dependent_destruction n :=
  let e := argName n in
    IntroArg_intro e; dependent destruction e.

Ltac IntroArg_base_tac n A g :=
  lazymatch A with
  | (fun _ => _) _ => simple apply IntroArg_beta
  | prod _ _ => simple apply IntroArg_prod
  | sigT _ => simple apply IntroArg_sigT
  | unit => simple apply IntroArg_unit
  | _ /\ _ => simple apply IntroArg_and
  | True => simple apply IntroArg_true
  | False => simple apply IntroArg_false
  | @eq (prod _ _) _ _  => simple apply IntroArg_eq_prod_const
  | eq_rect _ _ _ _ _ = _ => simple apply IntroArg_eq_rect_const_l
  | eq_dep1 _ _ _ _ _ _ => simple apply IntroArg_eq_dep1_const
  | @pushPreRel _ _ _ _ _ _ _ _ (inl _) (inl _) =>
    simple apply IntroArg_pushPreRel_inl
  | @pushPreRel _ _ _ _ _ _ _ _ (inr _) (inr _) =>
    simple apply IntroArg_pushPreRel_inr
  | @pushPostRel _ _ _ _ _ _ _ _ (inl _) (inl _) _ _ =>
    simple apply IntroArg_pushPostRel_inl
  | @pushPostRel _ _ _ _ _ _ _ _ (inr _) (inr _) _ _ =>
    simple apply IntroArg_pushPostRel_inr
  | @pushTSPreRel _ _ _ _ _ _ _ _ _ _ (inl _) (inl _) =>
    simple apply IntroArg_pushTSPreRel_inl
  | @pushTSPreRel _ _ _ _ _ _ _ _ _ _ (inr _) (inr _) =>
    simple apply IntroArg_pushTSPreRel_inr
  | @pushTSPostRel _ _ _ _ _ _ _ _ _ _ (inl _) (inl _) _ _ =>
    simple apply IntroArg_pushTSPostRel_inl
  | @pushTSPostRel _ _ _ _ _ _ _ _ _ _ (inr _) (inr _) _ _ =>
    simple apply IntroArg_pushTSPostRel_inr
  | @pushTSRR _ _ _ _ _ _ _ _ _ =>
    simple apply IntroArg_pushTSRR
  | eqPostRel _ _ _ _ _ _ => apply IntroArg_eqPostRel
  | true  = true  => IntroArg_intro_dependent_destruction n
  | false = false => IntroArg_intro_dependent_destruction n
  | true  = false => IntroArg_intro_dependent_destruction n
  | false = true  => IntroArg_intro_dependent_destruction n
  end.

#[global] Hint Extern 101 (IntroArg ?n ?A ?g) =>
  IntroArg_base_tac n A g : refines prepostcond.

#[global] Hint Extern 101 (IntroArg ?n (FrameCall ?frame) _) =>
  apply (@IntroArg_FrameCall n) : refines.
#[global] Hint Extern 101 (IntroArg ?n (FrameCallIxBelow ?frame (length ?frame)) ?goal) =>
  let k := eval cbn in (length frame) in
  change (IntroArg n (FrameCallIxBelow frame k) goal) : refines.
#[global] Hint Extern 101 (IntroArg ?n (FrameCallIxBelow _ 0) _) =>
  apply (@IntroArg_FrameCallIxBelow0 n) : refines.
#[global] Hint Extern 101 (IntroArg ?n (FrameCallIxBelow _ (S _)) _) =>
  apply (@IntroArg_FrameCallIxBelowS n) : refines.

#[global] Hint Extern 101 (IntroArg ?n (encodes ?x) ?g) =>
  let e := argName n in IntroArg_intro e;
  progress encodes_unfold_in e;
  revert e; apply (IntroArg_fold n _ _) : refines.

#[global] Hint Extern 101 (IntroArg ?n (LRTInput _) _) =>
  apply IntroArg_LRTInput_Fun || apply IntroArg_LRTInput_Ret : refines prepostcond.
#[global] Hint Extern 101 (IntroArg ?n (LRTOutput _ _) _) =>
  apply IntroArg_LRTOutput_Fun || apply IntroArg_LRTOutput_Ret : refines prepostcond.

#[global] Hint Extern 101 (IntroArg ?n (FrameCallRet ?frame ?args) ?g) =>
  let args' := eval hnf in args in
  let A' := eval unfold FrameCallRet in (FrameCallRet frame args') in
  progress change (IntroArg n A' g) : refines.

#[global] Hint Extern 101 (IntroArg ?n (existT _ _ _ = existT _ _ _) _) =>
  let e1 := argName n in IntroArg_intro e1;
  let e2 := argName n in inversion_sigma e1 as [e1 e2];
  revert e2; apply (IntroArg_fold n _ _);
  revert e1; apply (IntroArg_fold n _ _) : refines.
#[global] Hint Extern 101 (IntroArg ?n (eqPreRel (existT _ _ _) (existT _ _ _)) _) =>
  let e := argName n in IntroArg_intro e;
  unfold eqPreRel in e;
  revert e; apply (IntroArg_fold n _ _) : refines.

#[global] Hint Extern 199 (IntroArg SAWLet _ _) =>
  let e := argName SAWLet in IntroArg_intro e : refinesFun.

#[global] Hint Extern 201 (IntroArg ?n (@eq bool _ _) _) =>
  let e := argName n in IntroArg_intro e; rewrite e in * : refines prepostcond.

#[global] Hint Extern 299 (IntroArg ?n (?x = ?y) _) =>
  let e := argName n in IntroArg_intro e;
    try first [ is_var x; subst x | is_var y; subst y ] : refines.

#[global] Hint Extern 999 (IntroArg ?n _ _) =>
  let e := argName n in IntroArg_intro e : refines prepostcond.


(** Hints for Relation Goals **)

(* RelGoal marks a relation goal *)
Definition RelGoal (goal : Prop) := goal.

#[global] Hint Opaque RelGoal : refines.

Polymorphic Lemma RelGoal_fold goal : RelGoal goal -> goal.
Proof. eauto. Qed.

(* If nothing else works for a RelGoal, try reflexivity and then shelve it *)
#[global] Hint Extern 999 (RelGoal _) =>
  unfold RelGoal, lt;
  (timeout 1 reflexivity || apply RelGoal_fold; shelve) : refines.

#[global] Lemma RelGoal_and P Q :
  RelGoal P -> RelGoal Q -> RelGoal (P /\ Q).
Proof. split; eauto. Qed.

#[global] Hint Extern 101 (RelGoal (_ /\ _)) =>
  simple apply RelGoal_and : refines.

#[global] Lemma RelGoal_beta A (f : A -> Prop) x :
  RelGoal (f x) -> RelGoal ((fun x' => f x') x).
Proof. eauto. Qed.

#[global] Hint Extern 101 (RelGoal ((fun _ => _) _)) =>
  simple apply RelGoal_beta : refines.

Lemma RelGoal_eqPreRel_refl {E Γ e} :
  RelGoal (@eqPreRel E Γ e e).
Proof. constructor. Qed.

#[global] Hint Extern 101 (RelGoal (eqPreRel _ _ _ _)) =>
  apply RelGoal_eqPreRel_refl : refines.

Lemma RelGoal_eq_dep1_refl {U P p x} :
  RelGoal (eq_dep1 U P p x p x).
Proof. unshelve econstructor; eauto. Qed.

#[global] Hint Extern 101 (RelGoal (eq_dep1 _ _ _ _ _ _)) =>
  apply RelGoal_eq_dep1_refl : refines.

Polymorphic Lemma RelGoal_pushPreRel_inl E1 E2 Γ1 Γ2 frame1 frame2
            (precond : Rel (FrameCall frame1) (FrameCall frame2))
            (RPre : SpecPreRel E1 E2 Γ1 Γ2) e1 e2 :
  RelGoal (precond e1 e2) ->
  RelGoal (@pushPreRel E1 E2 Γ1 Γ2 frame1 frame2 precond RPre (inl e1) (inl e2)).
Proof. intro H. apply H. Qed.

#[global] Hint Extern 101 (RelGoal
                             (@pushPreRel _ _ _ _ _ _ _ _ (inl _) (inl _))) =>
  apply RelGoal_pushPreRel_inl : refines.


Polymorphic Lemma RelGoal_pushPreRel_inr E1 E2 Γ1 Γ2 frame1 frame2
            (precond : Rel (FrameCall frame1) (FrameCall frame2))
            (RPre : SpecPreRel E1 E2 Γ1 Γ2) e1 e2 :
  RelGoal (RPre e1 e2) ->
  RelGoal (@pushPreRel E1 E2 Γ1 Γ2 frame1 frame2 precond RPre (inr e1) (inr e2)).
Proof. intro H. apply H. Qed.

#[global] Hint Extern 101 (RelGoal
                             (@pushPreRel _ _ _ _ _ _ _ _ (inr _) (inr _))) =>
  apply RelGoal_pushPreRel_inr : refines.


Polymorphic Lemma RelGoal_pushPostRel_inl E1 E2 Γ1 Γ2 frame1 frame2
            (postcond : PostRel (FrameCall frame1) (FrameCall frame2))
            (RPost : SpecPostRel E1 E2 Γ1 Γ2)
            (call1 : FrameCall frame1) (call2 : FrameCall frame2)
            r1 r2 :
  RelGoal (postcond _ _ r1 r2) ->
  RelGoal (@pushPostRel E1 E2 Γ1 Γ2 frame1 frame2
                           postcond RPost (inl call1) (inl call2) r1 r2).
Proof. intro H. apply H. Qed.

#[global] Hint Extern 101 (RelGoal
                             (@pushPostRel _ _ _ _ _ _ _ _ (inl _) (inl _))) =>
  apply RelGoal_pushPostRel_inl : refines.


Polymorphic Lemma RelGoal_pushPostRel_inr E1 E2 Γ1 Γ2 frame1 frame2
            (postcond : PostRel (FrameCall frame1) (FrameCall frame2))
            (RPost : SpecPostRel E1 E2 Γ1 Γ2)
            e1 e2 r1 r2 :
  RelGoal (RPost _ _ r1 r2) ->
  RelGoal (@pushPostRel E1 E2 Γ1 Γ2 frame1 frame2
                           postcond RPost (inr e1) (inr e2) r1 r2).
Proof. intro H. apply H. Qed.

#[global] Hint Extern 101 (RelGoal
                             (@pushPostRel _ _ _ _ _ _ _ _ (inr _) (inr _))) =>
  apply RelGoal_pushPostRel_inr : refines.


Polymorphic Lemma RelGoal_pushTSPreRel_inl E1 E2 Γ1 Γ2 frame1 A2 B2
            (tsPre : A2 -> Prop)
            (precond : Rel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
            (RPre : SpecPreRel E1 E2 Γ1 Γ2)
            args1 a2 :
  RelGoal (tsPre a2 /\ precond args1 (unary1Call a2)) ->
  RelGoal (@pushTSPreRel E1 E2 Γ1 Γ2 frame1 A2 B2
                            tsPre precond RPre (inl args1)
                            (inl (mkFrameCall (unary1Frame A2 B2) 0 a2))).
Proof. intro H. apply H. Qed.

#[global] Hint Extern 101 (RelGoal
                             (@pushTSPreRel _ _ _ _ _ _ _ _ _ _ (inl _) (inl _))) =>
  apply RelGoal_pushTSPreRel_inl : refines.

Polymorphic Lemma RelGoal_pushTSPreRel_inr E1 E2 Γ1 Γ2 frame1 A2 B2
            (tsPre : A2 -> Prop)
            (precond : Rel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
            (RPre : SpecPreRel E1 E2 Γ1 Γ2)
            e1 e2 :
  RelGoal (RPre e1 e2) ->
  RelGoal (@pushTSPreRel E1 E2 Γ1 Γ2 frame1 A2 B2
                            tsPre precond RPre (inr e1) (inr e2)).
Proof. intro H. apply H. Qed.

#[global] Hint Extern 101 (RelGoal
                             (@pushTSPreRel _ _ _ _ _ _ _ _ _ _ (inr _) (inr _))) =>
  apply RelGoal_pushTSPreRel_inr : refines.


Polymorphic Lemma RelGoal_pushTSPostRel_inl E1 E2 Γ1 Γ2 frame1 A2 B2
            (tsPost : A2 -> B2 -> Prop)
            (postcond : PostRel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
            (RPost : SpecPostRel E1 E2 Γ1 Γ2)
            args1 a2 r1 b2 :
  RelGoal (tsPost a2 b2 /\ postcond args1 (unary1Call a2) r1 b2) ->
  RelGoal (@pushTSPostRel E1 E2 Γ1 Γ2 frame1 A2 B2
                             tsPost postcond RPost (inl args1)
                             (inl (mkFrameCall (unary1Frame A2 B2) 0 a2)) r1 b2).
Proof. intro H. apply H. Qed.

#[global] Hint Extern 101 (RelGoal
                             (@pushTSPostRel _ _ _ _ _ _ _ _ _ _ (inl _) (inl _))) =>
  apply RelGoal_pushTSPostRel_inl : refines.


Polymorphic Lemma RelGoal_pushTSPostRel_inr E1 E2 Γ1 Γ2 frame1 A2 B2
            (tsPost : A2 -> B2 -> Prop)
            (postcond : PostRel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
            (RPost : SpecPostRel E1 E2 Γ1 Γ2)
            e1 e2 r1 r2 :
  RelGoal (RPost e1 e2 r1 r2) ->
  RelGoal (@pushTSPostRel E1 E2 Γ1 Γ2 frame1 A2 B2
                             tsPost postcond RPost (inr e1) (inr e2) r1 r2).
Proof. intro H. apply H. Qed.

#[global] Hint Extern 101 (RelGoal
                             (@pushTSPostRel _ _ _ _ _ _ _ _ _ _ (inr _) (inr _))) =>
  apply RelGoal_pushTSPostRel_inr : refines.


Polymorphic Lemma RelGoal_pushTSRR frame1 A2 B2
            (tsPost : A2 -> B2 -> Prop)
            (postcond : PostRel (FrameCall frame1) (FrameCall (unary1Frame A2 B2)))
            call1 a2 r1 r2 :
  RelGoal (tsPost a2 r2 /\ postcond call1 (unary1Call a2) r1 r2) ->
  RelGoal (@pushTSRR frame1 A2 B2 tsPost postcond call1 a2 r1 r2).
Proof. intro H. apply H. Qed.

#[global] Hint Extern 101 (RelGoal (@pushTSRR _ _ _ _ _ _ _ _ _)) =>
  apply RelGoal_pushTSRR : refines.


(** Hints for Goals to Shelve **)

Polymorphic Definition Shelve (A : Type) := A.

#[global] Hint Opaque Shelve : refines prepostcond.

Ltac Shelve_fold :=
  match goal with
  | |- ?A => change (Shelve A)
  end.

#[global] Hint Extern 999 (Shelve _) => shelve : refines.

#[global] Hint Extern 101 (Shelve (_ /\ _)) =>
  unfold Shelve; split; Shelve_fold : refines.
#[global] Hint Extern 101 (Shelve ({ _ : _ & _ })) =>
  unfold Shelve; split; Shelve_fold : refines.
#[global] Hint Extern 101 (Shelve (_ * _)) =>
  unfold Shelve; split; Shelve_fold : refines.
#[global] Hint Extern 101 (Shelve unit) =>
  unfold Shelve; exact tt : refines.
#[global] Hint Extern 101 (Shelve True) =>
  unfold Shelve; trivial : refines.


(** Refinement hints using IntroArg and RelGoal **)

(* RetS |= RetS *)
Polymorphic Definition spec_refines_ret_IntroArg E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR r1 r2 :
  (RelGoal (RR r1 r2 : Prop)) ->
  @spec_refines E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR (RetS r1) (RetS r2) :=
  spec_refines_ret E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR r1 r2.

#[global] Hint Extern 102 (spec_refines _ _ _ (RetS _) (RetS _)) =>
  apply spec_refines_ret_IntroArg : refines.


(* Monad laws *)

#[global]
Hint Extern 101 (spec_refines _ _ _ _ (RetS _ >>= _)) =>
  simple apply spec_refines_ret_bind_r : refines.
#[global]
Hint Extern 101 (spec_refines _ _ _ (RetS _ >>= _) _) =>
  simple apply spec_refines_ret_bind_l : refines.

#[global]
Hint Extern 101 (spec_refines _ _ _ _ ((_ >>= _) >>= _)) =>
  simple apply spec_refines_bind_bind_r : refines.
#[global]
Hint Extern 101 (spec_refines _ _ _ ((_ >>= _) >>= _) _) =>
  simple apply spec_refines_bind_bind_l : refines.


(* Trigger |= Trigger *)

Definition spec_refines_trigger_bind_IntroArg (E1 E2 : EncType) Γ1 Γ2 R1 R2
      (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
      RR (e1 : E1) (e2 : E2)
      (k1 : encodes e1 -> SpecM E1 Γ1 R1)
      (k2 : encodes e2 -> SpecM E2 Γ2 R2) :
  RelGoal (RPre (resum e1) (resum e2)) ->
  (IntroArg Any _ (fun a =>
     IntroArg Any _ (fun b =>
       IntroArg Hyp (RPost (resum e1) (resum e2) a b) (fun _ =>
         spec_refines RPre RPost RR (k1 (resum_ret e1 a)) (k2 (resum_ret e2 b)))))) ->
  spec_refines RPre RPost RR (TriggerS e1 >>= k1) (TriggerS e2 >>= k2) :=
  spec_refines_trigger_bind E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR e1 e2 k1 k2.

#[global]
Hint Extern 102 (spec_refines _ _ _ (TriggerS _ >>= _) (TriggerS _ >>= _)) =>
  apply spec_refines_trigger_bind_IntroArg; resum_unfold : refines.


(* Rules for quantifiers *)

Definition spec_refines_exists_l_IntroArg E1 E2 Γ1 Γ2 R1 R2 A `{QuantType A}
      RPre RPost RR (phi : SpecM E2 Γ2 R2) (kphi : A -> SpecM E1 Γ1 R1) :
  (IntroArg Exists A (fun a =>spec_refines RPre RPost RR (kphi a) phi)) ->
  spec_refines RPre RPost RR (ExistsS A >>= kphi) phi :=
  spec_refines_exists_l E1 E2 Γ1 Γ2 R1 R2 A RPre RPost RR phi kphi.

Definition spec_refines_forall_r_IntroArg E1 E2 Γ1 Γ2 R1 R2 A `{QuantType A}
      RPre RPost RR (phi : SpecM E1 Γ1 R1) (kphi : A -> SpecM E2 Γ2 R2) :
  (IntroArg Forall A (fun a => spec_refines RPre RPost RR phi (kphi a))) ->
  spec_refines RPre RPost RR phi (ForallS A >>= kphi) :=
  spec_refines_forall_r E1 E2 Γ1 Γ2 R1 R2 A RPre RPost RR phi kphi.

#[global] Hint Extern 101 (spec_refines _ _ _ _ (ForallS _ >>= _)) =>
  simple apply spec_refines_forall_r_IntroArg : refines.
#[global] Hint Extern 101 (spec_refines _ _ _ (ExistsS _ >>= _) _) =>
  simple apply spec_refines_exists_l_IntroArg : refines.

#[global] Hint Extern 202 (spec_refines _ _ _ _ (ExistsS _ >>= _)) =>
  unshelve simple eapply spec_refines_exists_r; [ Shelve_fold |] : refines.
#[global] Hint Extern 202 (spec_refines _ _ _ (ForallS _ >>= _) _) =>
  unshelve simple eapply spec_refines_forall_l; [ Shelve_fold |] : refines.


(* Rules for assume and assert *)

Definition spec_refines_assert_l_IntroArg E1 E2 Γ1 Γ2 R1 R2 (P:Prop)
      RPre RPost RR (phi : SpecM E2 Γ2 R2) (kphi : unit -> SpecM E1 Γ1 R1) :
  (IntroArg Assert P (fun _ => spec_refines RPre RPost RR (kphi tt) phi)) ->
  spec_refines RPre RPost RR (AssertS P >>= kphi) phi :=
  spec_refines_assert_l E1 E2 Γ1 Γ2 R1 R2 P RPre RPost RR phi kphi.

Definition spec_refines_assume_r_IntroArg E1 E2 Γ1 Γ2 R1 R2 (P:Prop)
      RPre RPost RR (phi : SpecM E1 Γ1 R1) (kphi : unit -> SpecM E2 Γ2 R2) :
  (IntroArg Assume P (fun _ => spec_refines RPre RPost RR phi (kphi tt))) ->
  spec_refines RPre RPost RR phi (AssumeS P >>= kphi) :=
  spec_refines_assume_r E1 E2 Γ1 Γ2 R1 R2 P RPre RPost RR phi kphi.

Definition spec_refines_assert_r_IntroArg E1 E2 Γ1 Γ2 R1 R2 (P:Prop)
      RPre RPost RR (phi : SpecM E1 Γ1 R1) (kphi : unit -> SpecM E2 Γ2 R2) :
  RelGoal P -> spec_refines RPre RPost RR phi (kphi tt) ->
  spec_refines RPre RPost RR phi (AssertS P >>= kphi) :=
  spec_refines_assert_r E1 E2 Γ1 Γ2 R1 R2 P RPre RPost RR phi kphi.

Definition spec_refines_assume_l_IntroArg E1 E2 Γ1 Γ2 R1 R2 (P:Prop)
      RPre RPost RR (phi : SpecM E2 Γ2 R2) (kphi : unit -> SpecM E1 Γ1 R1) :
      RelGoal P -> spec_refines RPre RPost RR (kphi tt) phi ->
  spec_refines RPre RPost RR (AssumeS P >>= kphi) phi :=
  spec_refines_assume_l E1 E2 Γ1 Γ2 R1 R2 P RPre RPost RR phi kphi.

#[global] Hint Extern 101 (spec_refines _ _ _ _ (AssumeS _ >>= _)) =>
  simple apply spec_refines_assume_r_IntroArg : refines.
#[global] Hint Extern 101 (spec_refines _ _ _ (AssertS _ >>= _) _) =>
  simple apply spec_refines_assert_l_IntroArg : refines.

#[global] Hint Extern 101 (spec_refines _ _ _ _ (AssertS _ >>= _)) =>
  simple apply spec_refines_assert_r_IntroArg : refines.
#[global] Hint Extern 101 (spec_refines _ _ _ (AssumeS _ >>= _) _) =>
  simple apply spec_refines_assume_l_IntroArg : refines.


(** * Rules for Coq quantifiers *)

Lemma exists_IntroArg n A (P : A -> Prop) (goal : Prop) :
  IntroArg Any A (fun x => IntroArg n (P x) (fun _ => goal)) ->
  IntroArg n (exists x, P x) (fun _ => goal).
Proof. intros H []; eapply H; eauto. Qed.

#[global] Hint Extern 101 (IntroArg _ (@ex _ _) _) =>
  simple apply exists_IntroArg : refines.

Lemma exists_RelGoal A P (x : A) :
  RelGoal (P x) -> RelGoal (exists x, P x).
Proof. intro; econstructor; eauto. Qed.

Lemma forall_RelGoal A P :
  IntroArg Any A (fun x => RelGoal (P x)) ->
  RelGoal (forall x, P x).
Proof. intros H x; apply H; eauto. Qed.

Lemma impl_RelGoal P Q :
  IntroArg Hyp P (fun _ => RelGoal Q) ->
  RelGoal (P -> Q).
Proof. intros H x; apply H; eauto. Qed.

#[global] Hint Extern 202 (RelGoal (@ex _ _)) =>
  unshelve simple eapply exists_RelGoal; [ Shelve_fold |] : refines.
#[global] Hint Extern 102 (RelGoal (forall _, _)) =>
  simple apply forall_RelGoal : refines.
#[global] Hint Extern 101 (RelGoal (_ -> _)) =>
  simple apply impl_RelGoal : refines.
  

(* Rules for if-then-else *)

Definition spec_refines_if_r_IntroArg E1 E2 Γ1 Γ2 R1 R2
           RPre RPost RR (t1 : SpecM E1 Γ1 R1) (t2 t3 : SpecM E2 Γ2 R2) b :
  (IntroArg If (b = true) (fun _ => spec_refines RPre RPost RR t1 t2)) ->
  (IntroArg If (b = false) (fun _ => spec_refines RPre RPost RR t1 t3)) ->
  spec_refines RPre RPost RR t1 (if b then t2 else t3) :=
  spec_refines_if_r E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR t1 t2 t3 b.

Definition spec_refines_if_l_IntroArg E1 E2 Γ1 Γ2 R1 R2
           RPre RPost RR (t1 t2 : SpecM E1 Γ1 R1) (t3 : SpecM E2 Γ2 R2) b :
  (IntroArg If (b = true) (fun _ => spec_refines RPre RPost RR t1 t3)) ->
  (IntroArg If (b = false) (fun _ => spec_refines RPre RPost RR t2 t3)) ->
  spec_refines RPre RPost RR (if b then t1 else t2) t3 :=
  spec_refines_if_l E1 E2 Γ1 Γ2 R1 R2 RPre RPost RR t1 t2 t3 b.

#[global] Hint Extern 101 (spec_refines _ _ _ _ (if _ then _ else _)) =>
  apply spec_refines_if_r_IntroArg : refines.
#[global] Hint Extern 101 (spec_refines _ _ _ (if _ then _ else _) _) =>
  apply spec_refines_if_l_IntroArg : refines.

#[global] Hint Extern 101 (spec_refines _ _ _ _ ((if _ then _ else _) >>= _)) =>
  apply spec_refines_if_bind_r : refines.
#[global] Hint Extern 101 (spec_refines _ _ _ ((if _ then _ else _) >>= _) _) =>
  apply spec_refines_if_bind_l : refines.


(* Rules for pattern-matching on lists *)

Definition spec_refines_match_list_r_IntroArg E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR A
           (t1 : SpecM E1 Γ1 R1) (t2 : A -> list A -> SpecM E2 Γ2 R2)
           (t3 : SpecM E2 Γ2 R2) xs :
  (IntroArg Any A (fun x =>
     IntroArg Any (list A) (fun xs' =>
       IntroArg Match (xs = x :: xs') (fun _ =>
         spec_refines RPre RPost RR t1 (t2 x xs'))))) ->
  (IntroArg Match (xs = nil) (fun _ => spec_refines RPre RPost RR t1 t3)) ->
  spec_refines RPre RPost RR t1 (match xs with
                                 | x :: xs' => t2 x xs' | nil => t3 end) :=
  spec_refines_match_list_r E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR A t1 t2 t3 xs.

Definition spec_refines_match_list_l_IntroArg E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR A
           (t3 : SpecM E2 Γ2 R2)
           (t1 : A -> list A -> SpecM E1 Γ1 R1) (t2 : SpecM E1 Γ1 R1) xs :
  (IntroArg Any A (fun x =>
     IntroArg Any (list A) (fun xs' =>
       IntroArg Match (xs = x :: xs') (fun _ =>
         spec_refines RPre RPost RR (t1 x xs') t3)))) ->
  (IntroArg Match (xs = nil) (fun _ => spec_refines RPre RPost RR t2 t3)) ->
  spec_refines RPre RPost RR (match xs with
                              | x :: xs' => t1 x xs' | nil => t2 end) t3 :=
  spec_refines_match_list_l E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR A t3 t1 t2 xs.

#[global]
Hint Extern 101 (spec_refines _ _ _ _ (match _ with | _ :: _ => _ | nil => _ end)) =>
  apply spec_refines_match_list_r_IntroArg : refines.
#[global]
Hint Extern 101 (spec_refines _ _ _ (match _ with | _ :: _ => _ | nil => _ end) _) =>
  apply spec_refines_match_list_l_IntroArg : refines.

#[global]
Hint Extern 101 (spec_refines _ _ _ _ ((match _ with | _ :: _ => _ | nil => _ end) >>= _)) =>
  apply spec_refines_match_list_bind_r : refines.
#[global]
Hint Extern 101 (spec_refines _ _ _ ((match _ with | _ :: _ => _ | nil => _ end) >>= _) _) =>
  apply spec_refines_match_list_bind_l : refines.


(* Rules for pattern-matching on pairs *)

Definition spec_refines_match_pair_r_IntroArg E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR A B
           (t1 : SpecM E1 Γ1 R1) (t2 : A -> B -> SpecM E2 Γ2 R2) pr :
  (IntroArg Any A (fun x =>
     IntroArg Any B (fun y =>
       IntroArg Match (pr = (x, y)) (fun _ =>
         spec_refines RPre RPost RR t1 (t2 x y))))) ->
  spec_refines RPre RPost RR t1 (match pr with | (x,y) => t2 x y end) :=
  spec_refines_match_pair_r E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR A B t1 t2 pr.

Definition spec_refines_match_pair_l_IntroArg E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR A B
           (t1 : A -> B -> SpecM E1 Γ1 R1) (t2 : SpecM E2 Γ2 R2) pr :
  (IntroArg Any A (fun x =>
     IntroArg Any B (fun y =>
       IntroArg Match (pr = (x, y)) (fun _ =>
         spec_refines RPre RPost RR (t1 x y) t2)))) ->
  spec_refines RPre RPost RR (match pr with | (x,y) => t1 x y end) t2 :=
  spec_refines_match_pair_l E1 E2 Γ1 Γ2 RPre RPost R1 R2 RR A B t1 t2 pr.

#[global]
Hint Extern 101 (spec_refines _ _ _ _ (match _ with | (_,_) => _ end)) =>
  apply spec_refines_match_pair_r_IntroArg : refines.
#[global]
Hint Extern 101 (spec_refines _ _ _ (match _ with | (_,_) => _ end) _) =>
  apply spec_refines_match_pair_l_IntroArg : refines.

#[global]
Hint Extern 101 (spec_refines _ _ _ _ ((match _ with | (_,_) => _ end) >>= _)) =>
  apply spec_refines_match_pair_bind_r : refines.
#[global]
Hint Extern 101 (spec_refines _ _ _ ((match _ with | (_,_) => _ end) >>= _) _) =>
  apply spec_refines_match_pair_bind_l : refines.


(** * Rules for liftStackS  *)

Lemma spec_refines_liftStackS_ret_bind_l (E1 E2 : EncType) Γ1 Γ2 R1 R2
  (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
  (RR : Rel R1 R2) A1 a k1 t2 :
  spec_refines RPre RPost RR (k1 a) t2 ->
  spec_refines RPre RPost RR (liftStackS A1 (RetS a) >>= k1) t2.
Proof.
  intros. setoid_rewrite resumEntree_Ret. setoid_rewrite bind_ret_l.
  auto.
Qed.

Lemma spec_refines_liftStackS_bind_bind_l (E1 E2 : EncType) Γ1 Γ2 R1 R2
  (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
  (RR : Rel R1 R2) A1 B1 t1 k1 k2 t2 :
  spec_refines RPre RPost RR (x <- liftStackS A1 t1 ;; liftStackS B1 (k1 x) >>= k2) t2 ->
  spec_refines RPre RPost RR (liftStackS B1 (t1 >>= k1) >>= k2) t2.
Proof.
  intros. setoid_rewrite resumEntree_bind. setoid_rewrite bind_bind. eauto.
Qed.

Lemma spec_refines_liftStackS_assume_bind_l (E1 E2 : EncType) Γ1 Γ2 R1 R2
  (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
  (RR : Rel R1 R2) P k1 t2 :
  spec_refines RPre RPost RR (AssumeS P >>= k1) t2 ->
  spec_refines RPre RPost RR (liftStackS _ (AssumeS P) >>= k1) t2.
Proof.
  intros.
  enough (@liftStackS E1 Γ1 unit (AssumeS P) ≅ AssumeS P).
  rewrite H0. auto.
  setoid_rewrite resumEntree_Vis.
  setoid_rewrite bind_vis. cbn. apply eqit_Vis.
  cbn. intros. rewrite bind_ret_l. setoid_rewrite resumEntree_Ret. 
  apply eqit_Ret. auto.
Qed.

Lemma spec_refines_liftStackS_assert_bind_l (E1 E2 : EncType) Γ1 Γ2 R1 R2
  (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
  (RR : Rel R1 R2) P k1 t2 :
  spec_refines RPre RPost RR (AssertS P >>= k1) t2 ->
  spec_refines RPre RPost RR (liftStackS _ (AssertS P) >>= k1) t2.
Proof.
  intros.
  enough (@liftStackS E1 Γ1 unit (AssertS P) ≅ AssertS P).
  rewrite H0. auto.
  setoid_rewrite resumEntree_Vis.
  setoid_rewrite bind_vis. cbn. apply eqit_Vis.
  cbn. intros. rewrite bind_ret_l. setoid_rewrite resumEntree_Ret. 
  apply eqit_Ret. auto.
Qed.

Lemma spec_refines_liftStackS_forall_bind_l (E1 E2 : EncType) Γ1 Γ2 R1 R2
  (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
  (RR : Rel R1 R2) A1 `{QuantType A1} k1 t2 :
  spec_refines RPre RPost RR (ForallS A1 >>= k1) t2 ->
  spec_refines RPre RPost RR (liftStackS _ (ForallS A1) >>= k1) t2.
Proof.
  intros.
  enough (@liftStackS E1 Γ1 A1 (ForallS A1) ≅ ForallS A1).
  rewrite H1. auto.
  setoid_rewrite resumEntree_Vis.
  apply eqit_Vis.
  cbn. intros. setoid_rewrite resumEntree_Ret. apply eqit_Ret. 
  auto.
Qed.

Lemma spec_refines_liftStackS_exists_bind_l (E1 E2 : EncType) Γ1 Γ2 R1 R2
  (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
  (RR : Rel R1 R2) A1 `{QuantType A1} k1 t2 :
  spec_refines RPre RPost RR (ExistsS A1 >>= k1) t2 ->
  spec_refines RPre RPost RR (liftStackS _ (ExistsS A1) >>= k1) t2.
Proof.
  intros.
  enough (@liftStackS E1 Γ1 A1 (ExistsS A1) ≅ ExistsS A1).
  rewrite H1. auto.
  setoid_rewrite resumEntree_Vis.
  apply eqit_Vis.
  cbn. intros. setoid_rewrite resumEntree_Ret. apply eqit_Ret. 
  auto.
Qed.

#[global] Hint Extern 101 (spec_refines _ _ _ (liftStackS _ (RetS _) >>= _) _) =>
  simple apply spec_refines_liftStackS_ret_bind_l : refines.
#[global] Hint Extern 101 (spec_refines _ _ _ (liftStackS _ (_ >>= _) >>= _) _) =>
  simple apply spec_refines_liftStackS_bind_bind_l : refines.
#[global] Hint Extern 101 (spec_refines _ _ _ (liftStackS _ (AssumeS _) >>= _) _) =>
  simple apply spec_refines_liftStackS_assume_bind_l : refines.
#[global] Hint Extern 101 (spec_refines _ _ _ (liftStackS _ (AssertS _) >>= _) _) =>
  simple apply spec_refines_liftStackS_assert_bind_l : refines.
#[global] Hint Extern 101 (spec_refines _ _ _ (liftStackS _ (ForallS _) >>= _) _) =>
  simple apply spec_refines_liftStackS_forall_bind_l : refines.
#[global] Hint Extern 101 (spec_refines _ _ _ (liftStackS _ (ExistsS _) >>= _) _) =>
  simple apply spec_refines_liftStackS_exists_bind_l : refines.

#[global] Hint Extern 101 (spec_refines _ _ _ (liftStackS _ (total_spec _ _ _) >>= _) _) =>
  apply spec_refines_liftStackS_bind_bind_l : refines.

Lemma spec_refines_liftStackS_bind_ret_l (E1 E2 : EncType) Γ1 Γ2 frame1 frame2 R1 R2
      (RPre : SpecPreRel E1 E2 (frame1 :: Γ1) (frame2 :: Γ2))
      (RPost : SpecPostRel E1 E2 (frame1 :: Γ1) (frame2 :: Γ2))
      t1 t2 (RR : Rel R1 R2) :
  spec_refines RPre RPost RR (liftStackS _ t1 >>= RetS) t2 ->
  spec_refines RPre RPost RR (liftStackS _ t1) t2.
Proof. intro; rewrite <- (bind_ret_r (liftStackS _ _)); eauto. Qed.

#[global] Hint Extern 101 (spec_refines _ _ _ (liftStackS _ ?t1) _) =>
  simple apply (spec_refines_liftStackS_bind_ret_l _ _ _ _ _ _ _ _ _ _ t1) : refines.


Lemma spec_refines_liftStackS_proper:
  forall (E1 : EncType) (Γ1 : list RecFrame) (frame1 : RecFrame) (R1 : Type) (t1 t2 : SpecM E1 nil R1),
    spec_refines eqPreRel eqPostRel eq t1 t2 ->
    spec_refines eqPreRel eqPostRel eq (@liftStackS E1 (frame1 :: Γ1) R1 t1) (liftStackS R1 t2).
Proof.
  intros E1 Γ1 frame1 R1 t1 t2 H. 
  enough (strict_refines  (@liftStackS E1 (frame1 :: Γ1) R1 t1) (liftStackS R1 t2)).
  {
    eapply padded_refines_monot; try apply H0; auto.
    intros. red in PR. dependent destruction PR. subst. cbn. constructor.
  }
  apply padded_refines_liftStackS_proper.
  eapply padded_refines_monot; try apply H; auto.
  intros. dependent destruction PR. red. econstructor.
  Unshelve. all : auto. simpl. auto.
Qed.

(* I think this is backwards *)
Lemma spec_refines_liftStackS_trans_bind_l {E1 E2 Γ1 Γ2 frame1 frame2 R1 R2}
      {RPre : SpecPreRel E1 E2 (frame1 :: Γ1) (frame2 :: Γ2)}
      {RPost : SpecPostRel E1 E2 (frame1 :: Γ1) (frame2 :: Γ2)}
      {RR : Rel R1 R2} {A t1 t2 k1 t3} :
  spec_refines eqPreRel eqPostRel eq t1 t2 ->
  spec_refines RPre RPost RR (liftStackS A t2 >>= k1) t3 ->
  spec_refines RPre RPost RR (liftStackS A t1 >>= k1) t3.
Proof.
  intros.
  assert (spec_refines eqPreRel eqPostRel eq (@liftStackS E1 (frame1 :: Γ1) A t1) (liftStackS A t2)).
  apply spec_refines_liftStackS_proper. auto.
  eapply padded_refines_weaken_r; try eapply H0.
  eapply padded_refines_bind with (RR := eq).
  - red in H1. eapply padded_refines_monot; try apply H1; auto.
    intros. dependent destruction PR. red. econstructor. auto. Unshelve. 2 : auto.
    cbn. auto.
  - intros. subst. reflexivity.
Qed.

Create HintDb refines_proofs.
#[global] Hint Extern 201 (spec_refines _ _ _ (liftStackS _ _ >>= _) _) =>
  (simple eapply spec_refines_liftStackS_trans_bind_l;
   [ typeclasses eauto with refines_proofs |]) || shelve : refines.


(** * Refinement Hints About Recursion *)

Polymorphic Definition WellFoundedRelation A := sig (@well_founded A).
Polymorphic Definition PreAndPostConditions frame1 frame2 : Type :=
  Rel (FrameCall frame1) (FrameCall frame2) *
  PostRel (FrameCall frame1) (FrameCall frame2).
Polymorphic Definition from_user {A} {x : A} := x.

Polymorphic Definition wfRelOf {A} :
  WellFoundedRelation A -> Rel A A := @proj1_sig _ (@well_founded A).
Polymorphic Definition preOf {frame1 frame2} :
  PreAndPostConditions frame1 frame2 ->
  Rel (FrameCall frame1) (FrameCall frame2) := fst.
Polymorphic Definition postOf {frame1 frame2} :
  PreAndPostConditions frame1 frame2 ->
  PostRel (FrameCall frame1) (FrameCall frame2) := snd.

Definition Continue {precond : Prop} {goal1 goal2} : Type :=
  precond * goal1 * goal2.

Lemma Continue_unfold precond goal1 goal2 :
  RelGoal precond -> goal1 -> goal2 ->
  @Continue precond goal1 goal2.
Proof. split; eauto. Qed.
Ltac Continue_unfold := simple apply Continue_unfold.

#[global] Hint Opaque WellFoundedRelation : refines prepostcond.
#[global] Hint Opaque PreAndPostConditions : refines prepostcond.
#[global] Hint Opaque Continue : refines prepostcond.

#[global] Hint Extern 999 (WellFoundedRelation _) => shelve : refines prepostcond.
#[global] Hint Extern 999 (PreAndPostConditions _ _) => shelve : refines prepostcond.
#[global] Hint Extern 999 (Continue) => shelve : refines prepostcond.

Lemma spec_refines_multifix_bind_IntroArg (E1 E2 : EncType) Γ1 Γ2 frame1 frame2 R1 R2
      (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2) RR
      (bodies1 : FrameTuple E1 (frame1 :: Γ1) frame1)
      (bodies2 : FrameTuple E2 (frame2 :: Γ2) frame2)
      (call1 : FrameCall frame1) (call2 : FrameCall frame2)
      (k1 : FrameCallRet frame1 call1 -> SpecM E1 Γ1 R1)
      (k2 : FrameCallRet frame2 call2 -> SpecM E2 Γ2 R2)
      (prepostconds : PreAndPostConditions frame1 frame2) :
  @Continue (preOf prepostconds call1 call2)
            (IntroArg Call _ (fun call1' => IntroArg Call _ (fun call2' =>
              IntroArg Hyp (preOf prepostconds call1' call2') (fun _ =>
              spec_refines (pushPreRel (preOf prepostconds) RPre)
                           (pushPostRel (postOf prepostconds) RPost)
                           (postOf prepostconds call1' call2')
                           (applyFrameTuple _ _ _ bodies1 call1')
                           (applyFrameTuple _ _ _ bodies2 call2')))))
            (IntroArg RetAny _ (fun r1 => IntroArg RetAny _ (fun r2 =>
              IntroArg Hyp (postOf prepostconds call1 call2 r1 r2) (fun _ =>
              spec_refines RPre RPost RR (k1 r1) (k2 r2))))) ->
  spec_refines RPre RPost RR
               (MultiFixS E1 Γ1 frame1 bodies1 call1 >>= k1)
               (MultiFixS E2 Γ2 frame2 bodies2 call2 >>= k2).
Proof.
  destruct prepostconds; intros [[]].
  unfold IntroArg in *; eapply spec_refines_multifix_bind; eauto.
Qed.

Lemma spec_refines_multifix_IntroArg (E1 E2 : EncType) Γ1 Γ2 frame1 frame2
      (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
      (bodies1 : FrameTuple E1 (frame1 :: Γ1) frame1)
      (bodies2 : FrameTuple E2 (frame2 :: Γ2) frame2)
      (call1 : FrameCall frame1) (call2 : FrameCall frame2)
      (RR : Rel (encodes call1) (encodes call2))
      (prepostconds : PreAndPostConditions frame1 frame2) :
  @Continue (preOf prepostconds call1 call2)
            (IntroArg RetAny _ (fun r1 => IntroArg RetAny _ (fun r2 =>
              IntroArg Hyp (postOf prepostconds call1 call2 r1 r2) (fun _ =>
              RelGoal (RR r1 r2)))))
            (IntroArg Call _ (fun call1' => IntroArg Call _ (fun call2' =>
              IntroArg Hyp (preOf prepostconds call1' call2') (fun _ =>
              spec_refines (pushPreRel (preOf prepostconds) RPre)
                           (pushPostRel (postOf prepostconds) RPost)
                           (postOf prepostconds call1' call2')
                           (applyFrameTuple _ _ _ bodies1 call1')
                           (applyFrameTuple _ _ _ bodies2 call2'))))) ->
  spec_refines RPre RPost RR
               (MultiFixS E1 Γ1 frame1 bodies1 call1)
               (MultiFixS E2 Γ2 frame2 bodies2 call2).
Proof.
  destruct prepostconds; intros [[]].
  unfold IntroArg in *; eapply spec_refines_multifix; eauto.
Qed.

Lemma spec_refines_total_spec_IntroArg (E1 E2 : EncType) Γ1 Γ2 frame1
      A2 B2 `{QuantType A2} `{QuantType B2}
      (RPre : SpecPreRel E1 E2 Γ1 Γ2) (RPost : SpecPostRel E1 E2 Γ1 Γ2)
      (bodies1 : FrameTuple E1 (frame1 :: Γ1) frame1)
      (call1 : FrameCall frame1) (a2 : A2)
      (RR : Rel (FrameCallRet frame1 call1) B2)
      (tsPre : A2 -> Prop) (tsPost : A2 -> B2 -> Prop)
      (rdec : WellFoundedRelation A2)
      (prepostconds : PreAndPostConditions frame1 (unary1Frame A2 B2)) :
  @Continue (preOf prepostconds call1 (unary1Call a2))
            (IntroArg RetAny _ (fun r1 => IntroArg RetAny _ (fun r2 =>
              IntroArg Hyp (tsPost a2 r2) (fun _ =>
              IntroArg Hyp (postOf prepostconds call1 (unary1Call a2) r1 r2) (fun _ =>
              RelGoal (RR r1 r2))))))
            (IntroArg Call _ (fun call1' => IntroArg Any _ (fun a2' =>
              IntroArg Hyp (preOf prepostconds call1' (unary1Call a2')) (fun _ =>
              spec_refines (pushTSPreRel tsPre (preOf prepostconds) RPre)
                           (pushTSPostRel tsPost (postOf prepostconds) RPost)
                           (pushTSRR tsPost (postOf prepostconds) call1' a2')
                           (applyFrameTuple _ _ _ bodies1 call1')
                           (total_spec_fix_body tsPre tsPost (wfRelOf rdec) a2'))))) ->
  spec_refines RPre RPost RR
               (MultiFixS E1 Γ1 frame1 bodies1 call1)
               (total_spec tsPre tsPost a2).
Proof.
  destruct rdec, prepostconds; intros [[]].
  unfold IntroArg, RelGoal in *; simpl in *.
  unshelve eapply spec_refines_total_spec; eauto.
Qed.

#[global]
Hint Extern 101 (spec_refines ?RPre ?RPost ?RR
                              (MultiFixS ?E1 ?Γ1 ?frame1 ?bodies1 ?call1 >>= ?k1)
                              (MultiFixS ?E2 ?Γ2 ?frame2 ?bodies2 ?call2 >>= ?k2)) =>
  unshelve (
    let HPrePost := fresh "HPrePost" in
    epose (HPrePost := from_user (A:=PreAndPostConditions frame1 frame2));
    apply (spec_refines_multifix_bind_IntroArg E1 E2 Γ1 Γ2 frame1 frame2 _ _
              RPre RPost RR bodies1 bodies2 call1 call2 k1 k2 HPrePost)) : refines.
#[global]
Hint Extern 101 (spec_refines ?RPre ?RPost ?RR
                              (MultiFixS ?E1 ?Γ1 ?frame1 ?bodies1 ?call1)
                              (MultiFixS ?E2 ?Γ2 ?frame2 ?bodies2 ?call2)) =>
  unshelve (
    let HPrePost := fresh "HPrePost" in
    epose (HPrePost := from_user (A:=PreAndPostConditions frame1 frame2));
    apply (spec_refines_multifix_IntroArg E1 E2 Γ1 Γ2 frame1 frame2
              RPre RPost bodies1 bodies2 call1 call2 RR HPrePost)) : refines.
#[global]
Hint Extern 101 (spec_refines ?RPre ?RPost ?RR
                              (MultiFixS ?E1 ?Γ1 ?frame1 ?bodies1 ?call1)
                              (@total_spec ?E2 ?Γ2 ?A2 ?B2 _ ?tsPre ?tsPost ?a2)) =>
  unshelve (
    let HWf := fresh "HWf" in
    epose (HWf := from_user (A:=WellFoundedRelation A2));
    let HPrePost := fresh "HPrePost" in
    epose (HPrePost := from_user (A:=PreAndPostConditions frame1 (unary1Frame A2 B2)));
    apply (spec_refines_total_spec_IntroArg E1 E2 Γ1 Γ2 frame1 A2 B2
              RPre RPost bodies1 call1 a2 RR tsPre tsPost HWf HPrePost));
  unfold total_spec_fix_body : refines.

Lemma spec_refines_call_bind_IntroArg (E1 E2 : EncType) Γ1 Γ2 frame1 frame2 R1 R2
      (RPre : SpecPreRel E1 E2 (frame1 :: Γ1) (frame2 :: Γ2))
      (RPost : SpecPostRel E1 E2 (frame1 :: Γ1) (frame2 :: Γ2))
      RR (call1 : FrameCall frame1) (call2 : FrameCall frame2)
      (k1 : FrameCallRet frame1 call1 -> SpecM E1 (frame1 :: Γ1) R1)
      (k2 : FrameCallRet frame2 call2 -> SpecM E2 (frame2 :: Γ2) R2) :
  RelGoal (RPre (inl call1) (inl call2)) ->
  (IntroArg RetAny _ (fun r1 => IntroArg RetAny _ (fun r2 =>
   IntroArg Hyp (RPost (inl call1) (inl call2) r1 r2) (fun _ =>
   spec_refines RPre RPost RR (k1 (resum_ret call1 r1)) (k2 (resum_ret call2 r2)))))) ->
  spec_refines RPre RPost RR (CallS _ _ _ call1 >>= k1) (CallS _ _ _ call2 >>= k2).
Proof. apply spec_refines_call_bind. Qed.

Lemma spec_refines_call_IntroArg (E1 E2 : EncType) Γ1 Γ2 frame1 frame2
      (RPre : SpecPreRel E1 E2 (frame1 :: Γ1) (frame2 :: Γ2))
      (RPost : SpecPostRel E1 E2 (frame1 :: Γ1) (frame2 :: Γ2))
      (call1 : FrameCall frame1) (call2 : FrameCall frame2)
      (RR : Rel (FrameCallRet frame1 call1) (FrameCallRet frame2 call2)) :
  RelGoal (RPre (inl call1) (inl call2)) ->
  IntroArg RetAny _ (fun r1 => IntroArg RetAny _ (fun r2 =>
   IntroArg Hyp (RPost (inl call1) (inl call2) r1 r2) (fun _ =>
   RelGoal (RR r1 r2)))) ->
  spec_refines RPre RPost RR (CallS _ _ _ call1) (CallS _ _ _ call2).
Proof. intros; apply spec_refines_call; eauto. Qed.

#[global] Hint Extern 101 (spec_refines _ _ _ (CallS _ _ _ _ >>= _) (CallS _ _ _ _ >>= _)) =>
  apply spec_refines_call_bind_IntroArg; resum_unfold : refines.
#[global] Hint Extern 101 (spec_refines _ _ _ (CallS _ _ _ _) (CallS _ _ _ _)) =>
  apply spec_refines_call_IntroArg : refines.

#[global] Hint Extern 102 (spec_refines _ _ _ (CallS _ _ _ ?call1) _) =>
  simple apply (spec_refines_call_bind_ret_l _ _ _ _ _ _ _ _ _ call1) : refines.
#[global] Hint Extern 102 (spec_refines _ _ _ _ (CallS _ _ _ ?call2)) =>
  simple apply (spec_refines_call_bind_ret_r _ _ _ _ _ _ _ _ _ _ _ call2) : refines.

#[global] Hint Extern 991 (spec_refines _ _ _ (CallS _ _ _ _ >>= _) (trepeat _ _)) =>
  simple apply spec_refines_trepeat_suc_r : refines.
#[global] Hint Extern 991 (spec_refines _ _ _ (CallS _ _ _ _ >>= _) (trepeat _ _ >>= _)) =>
  simple apply spec_refines_trepeat_bind_suc_r : refines.

#[global] Hint Extern 992 (spec_refines _ _ _ _ (trepeat _ _)) =>
  simple apply spec_refines_trepeat_zero_r : refines.
#[global] Hint Extern 992 (spec_refines _ _ _ _ (trepeat _ _ >>= _)) =>
  simple apply spec_refines_trepeat_bind_zero_r : refines.

#[global] Hint Extern 101 (spec_refines ?RPre ?RPost ?RR
                                        (applyFrameTuple ?E ?Γ ?frame ?bodies ?call) ?t2) =>
  let call' := eval hnf in call in
  let frame' := eval cbv in frame in
  let t1' := eval cbv [ applyFrameTuple nthLRT nth_default'
                        lrtApply nthFrameTupleFun fst snd ]
                   in (applyFrameTuple E Γ frame' bodies call') in
  progress change (spec_refines RPre RPost RR t1' t2) : refines.
#[global] Hint Extern 101 (spec_refines ?RPre ?RPost ?RR ?t1
                                        (applyFrameTuple ?E ?Γ ?frame ?bodies ?call)) =>
  let call' := eval hnf in call in
  let frame' := eval cbv in frame in
  let t2' := eval cbv [ applyFrameTuple nthLRT nth_default'
                        lrtApply nthFrameTupleFun fst snd ]
                   in (applyFrameTuple E Γ frame' bodies call') in
  progress change (spec_refines RPre RPost RR t1 t2') : refines.

(** * Tactics for proving refinement *)

Ltac unfold_RelGoal_goals :=
  match goal with
  | |- RelGoal _ => unfold RelGoal
  | |- _ => idtac
  end.

Ltac prove_refinement_rewrite :=
  match goal with
  | |- spec_refines _ _ _ _ _ => idtac
  | |- _ => try unshelve rewrite_strat (bottomup (hints refines))
  end.

Ltac prove_refinement_prepostcond :=
  unshelve typeclasses eauto with prepostcond;
  unfold_RelGoal_goals; cbn [ FrameCallIndex ];
  prove_refinement_rewrite.

Tactic Notation "prove_refinement_eauto_then" tactic(tac) :=
  unshelve typeclasses eauto with refines;
  match goal with
  | |- Shelve _ => unfold Shelve; shelve
  | |- RelGoal _ => tac
  | |- _ => idtac
  end.

Ltac prove_refinement_eauto :=
  (prove_refinement_eauto_then (prove_refinement_eauto_then idtac)).

Ltac prove_refinement_solve :=
  try solve [ assumption | reflexivity | contradiction ].

Variant ProveRefOpt := NoRewrite | NoSolve.

Definition in_opts (o : ProveRefOpt) (os : list ProveRefOpt) : bool.
Proof.
  refine (proj1_sig (bool_of_sumbool (in_dec _ o os))).
  destruct x, y ; (left; reflexivity) || (right; discriminate).
Defined.

Ltac prove_refinement_with opts :=
  prove_refinement_eauto; unfold_RelGoal_goals;
  let noRewrite := eval vm_compute in (in_opts NoRewrite opts) in
  first [ constr_eq_strict noRewrite true | prove_refinement_rewrite ];
  let noSolve := eval vm_compute in (in_opts NoSolve opts) in
  first [ constr_eq_strict noSolve true | prove_refinement_solve   ].

Ltac prove_refinement :=
  prove_refinement_with (@nil ProveRefOpt).
Tactic Notation "prove_refinement" "with" constr(o) :=
  prove_refinement_with (cons o nil).
Tactic Notation "prove_refinement" "with" constr(o1) constr(o2) :=
  prove_refinement_with (cons o1 (cons o2 nil)).

Ltac prove_refinement_continue :=
  Continue_unfold; prove_refinement.
Tactic Notation "prove_refinement_continue" "with" constr(o) :=
  Continue_unfold; prove_refinement with o.
Tactic Notation "prove_refinement_continue" "with" constr(o1) constr(o2) :=
  Continue_unfold; prove_refinement with o1 o2.


(** * Tactics for pre/post-conditions and well-founded relations *)

Definition DecreasingNat {A} (_ : A) := nat.
#[global] Hint Opaque DecreasingNat : prepostcond.
#[global] Hint Extern 999 (DecreasingNat _) => shelve : prepostcond.

Tactic Notation "wellfounded_decreasing_nat" :=
  let f := fresh "f" in
  enough (IntroArg Any _ DecreasingNat) as f
    by (exact (exist _ (fun a b => f a < f b) (well_founded_ltof _ f)));
  prove_refinement_prepostcond.
Tactic Notation "wellfounded_decreasing_nat" uconstr(f) :=
  exact (exist _ (fun a b => f a < f b) (well_founded_ltof _ f)).

Definition well_founded_False {A} :
  @well_founded A (fun _ _ => False).
Proof. constructor; contradiction. Defined.

Ltac wellfounded_none :=
  exact (exist _ (fun _ _ => False) well_founded_False).

Polymorphic Definition PreCase {frame1 frame2} i j
  (a1 : LRTInput (nthLRT frame1 i))
  (a2 : LRTInput (nthLRT frame2 j)) := Prop.
Polymorphic Definition PostCase {frame1 frame2} i j args1 args2
  (r1 : LRTOutput (nthLRT frame1 i) args1)
  (r2 : LRTOutput (nthLRT frame2 j) args2) := Prop.

#[global] Hint Opaque PreCase : prepostcond.
#[global] Hint Opaque PostCase : prepostcond.

#[global] Hint Extern 999 (PreCase _ _ _ _) => shelve : prepostcond.
#[global] Hint Extern 999 (PostCase _ _ _ _ _ _) => shelve : prepostcond.

Polymorphic Definition prepost_case {frame1 frame2} i j
  (pre : IntroArg Any (LRTInput (nthLRT frame1 i)) (fun a1 =>
         IntroArg Any (LRTInput (nthLRT frame2 j)) (fun a2 =>
         PreCase i j a1 a2)))
  (post : IntroArg Any _ (fun args1 => IntroArg Any _ (fun args2 =>
          IntroArg RetAny (LRTOutput (nthLRT frame1 i) args1) (fun r1 =>
          IntroArg RetAny (LRTOutput (nthLRT frame2 j) args2) (fun r2 =>
          PostCase i j args1 args2 r1 r2)))))
  (prepostcond : PreAndPostConditions frame1 frame2) :
  PreAndPostConditions frame1 frame2.
Proof.
  unfold IntroArg, PreCase, PostCase in *; split.
  all: intros [m args1] [n args2].
  all: destruct (Nat.eq_dec m i) as [p1|];
       [ destruct p1; destruct (Nat.eq_dec n j) as [p2|];
                      [ destruct p2 |] |].
  1: apply pre; eauto.
  1-2: exact (preOf prepostcond (FrameCallOfArgs _ m args1)
                                (FrameCallOfArgs _ n args2)).
  1: apply post; eauto.
  1-2: exact (postOf prepostcond (FrameCallOfArgs _ m args1)
                                 (FrameCallOfArgs _ n args2)).
Defined.

Notation eqPreCase :=
  (fun (args1 : LRTInput (nthLRT _ _)) (args2 : LRTInput (nthLRT _ _)) =>
       eq args1 args2)
  (only parsing).
Notation eqPostCase :=
  (ltac:(intros args1 args2 r1 r2;
         apply (eq_dep1 _ _ args1 r1 args2 r2)))
  (only parsing).

Tactic Notation "prepost_case" constr(i) constr(j) :=
  apply (prepost_case i j); prove_refinement_prepostcond.
Tactic Notation "prepost_case" constr(i) constr(j) "withPre" uconstr(pre) :=
  apply (prepost_case i j); [ exact pre | prove_refinement_prepostcond |].
Tactic Notation "prepost_case" constr(i) constr(j) "withPost" uconstr(post) :=
  apply (prepost_case i j); [ prove_refinement_prepostcond | exact post |].
Tactic Notation "prepost_case" constr(i) constr(j) "with" uconstr(pre) "," uconstr(post) :=
  apply (prepost_case i j); [exact pre | exact post |].

Definition PreExcludedCase (i j : nat) := False.
Definition PostExcludedCase (i j : nat) := False.

#[global] Hint Extern 101 (IntroArg ?n (PreExcludedCase _ _) _) =>
  apply IntroArg_false : refines.
#[global] Hint Extern 101 (IntroArg ?n (PostExcludedCase _ _) _) =>
 apply IntroArg_false : refines.

Tactic Notation "prepost_exclude_case" constr(i) constr(j) :=
  apply (prepost_case i j); [ exact (fun _ _ => PreExcludedCase i j)
                            | exact (fun _ _ _ _ => PostExcludedCase i j)].
Tactic Notation "prepost_exclude_remaining" :=
  exact (fun calli callj => PreExcludedCase (FrameCallIndex calli) (FrameCallIndex callj),
         fun calli callj _ _ => PostExcludedCase (FrameCallIndex calli) (FrameCallIndex callj)).

Ltac wf_pre_post_IntroArg_unfold A :=
  let A' := eval cbv [ wfRelOf proj1_sig preOf fst postOf snd prepost_case
                       Nat.eq_dec nat_rec nat_rect f_equal_nat f_equal
                       IntroArg_prod IntroArg_sigT IntroArg_unit IntroArg_FrameCall
                       IntroArg_FrameCallIxBelow0
                       IntroArg_LRTInput_Fun IntroArg_LRTInput_Ret
                       IntroArg_LRTOutput_Fun IntroArg_LRTOutput_Ret ]
              in A in A'.

#[global] Hint Extern 101 (IntroArg ?n (wfRelOf ?H ?a1 ?a2) ?g) =>
  let H' := eval unfold H, from_user in H in
  let A' := wf_pre_post_IntroArg_unfold (wfRelOf H' a1 a2) in
  progress change (IntroArg n A' g) : refines.
#[global] Hint Extern 101 (RelGoal (wfRelOf ?H ?a1 ?a2)) =>
  let H' := eval unfold H, from_user in H in
  let A' := wf_pre_post_IntroArg_unfold (wfRelOf H' a1 a2) in
  progress change (RelGoal A') : refines.

#[global] Hint Extern 101 (IntroArg ?n (preOf ?H ?call1 ?call2) ?g) =>
  let H' := eval unfold H, from_user in H in
  let call1' := eval hnf in call1 in
  let call2' := eval hnf in call2 in
  let A' := wf_pre_post_IntroArg_unfold (preOf H' call1' call2') in
  progress change (IntroArg n A' g) : refines.
#[global] Hint Extern 101 (RelGoal (preOf ?H ?call1 ?call2)) =>
  let H' := eval unfold H, from_user in H in
  let call1' := eval hnf in call1 in
  let call2' := eval hnf in call2 in
  let A' := wf_pre_post_IntroArg_unfold (preOf H' call1' call2') in
  progress change (RelGoal A') : refines.

#[global] Hint Extern 101 (IntroArg ?n (postOf ?H ?call1 ?call2 ?r1 ?r2) ?g) =>
  let H' := eval unfold H, from_user in H in
  let call1' := eval hnf in call1 in
  let call2' := eval hnf in call2 in
  let A' := wf_pre_post_IntroArg_unfold (postOf H' call1' call2' r1 r2) in
  progress change (IntroArg n A' g) : refines.
#[global] Hint Extern 101 (RelGoal (postOf ?H ?call1 ?call2 ?r1 ?r2)) =>
  let H' := eval unfold H, from_user in H in
  let call1' := eval hnf in call1 in
  let call2' := eval hnf in call2 in
  let A' := wf_pre_post_IntroArg_unfold (postOf H' call1' call2' r1 r2)  in
  progress change (RelGoal A') : refines.


(** * Testing *)

Open Scope nat_scope.

Lemma test_ifs E x :
  @spec_refines E E nil nil eqPreRel eqPostRel nat nat eq
                  (if 0 <=? x then if x <? 256 then RetS 1 else RetS 0 else RetS 0)
                  (if x <? 256 then if 0 <=? x then RetS 1 else RetS 0 else RetS 0).
Proof.
  prove_refinement.
Qed.

Lemma test_exists E x y :
  @spec_refines E E nil nil eqPreRel eqPostRel nat nat eq
                  (RetS ((x+1) + (y+2)))
                  ('(x', y') <- ExistsS (nat * nat) ;; RetS (x' + y')).
Proof.
  prove_refinement.
Qed.

Lemma test_spins E (x : nat) :
  @spec_refines E E nil nil eqPreRel eqPostRel nat nat eq
                  (MultiFixS E nil (unary1Frame nat nat)
                    ((fun a => CallS _ _ _ (mkFrameCall (unary1Frame nat nat) 0 a)), tt)
                    (mkFrameCall (unary1Frame nat nat) 0 x))
                  (MultiFixS E nil (unary1Frame nat nat)
                    ((fun a => CallS _ _ _ (mkFrameCall (unary1Frame nat nat) 0 a)), tt)
                    (mkFrameCall (unary1Frame nat nat) 0 x)).
Proof.
  prove_refinement.
  - prepost_case 0 0 with eqPreCase, eqPostCase.
    prepost_exclude_remaining.
  - prove_refinement_continue.
Qed.

Definition testFrame1 : RecFrame :=
  LRT_Fun nat (fun _ => LRT_Ret nat) :: LRT_Fun nat (fun _ => LRT_Ret nat) :: nil.

Lemma test_spins_rets E (x : nat) :
  @spec_refines E E nil nil eqPreRel eqPostRel nat nat eq
                  (MultiFixS E nil testFrame1
                    ((fun a => CallS _ _ _ (mkFrameCall testFrame1 0 a)),
                     ((fun a => RetS a), tt))
                    (mkFrameCall testFrame1 1 x))
                  (MultiFixS E nil testFrame1
                    ((fun a => RetS a),
                     ((fun a => CallS _ _ _ (mkFrameCall testFrame1 1 a)), tt))
                    (mkFrameCall testFrame1 0 x)).
Proof.
  prove_refinement.
  - prepost_case 1 0 with eqPreCase, eqPostCase.
    prepost_case 0 1 with eqPreCase, eqPostCase.
    prepost_exclude_remaining.
  - prove_refinement_continue.
Qed.

Lemma test_total_spec_easy E (x : nat) :
  @spec_refines E E nil nil eqPreRel eqPostRel nat nat eq
                  (MultiFixS E nil (unary1Frame nat nat)
                    ((fun a => RetS (a + 1)), tt)
                    (mkFrameCall (unary1Frame nat nat) 0 x))
                  (total_spec (fun _ => True)
                              (fun a b => b = (a + 1)) x).
Proof.
  prove_refinement.
  - wellfounded_none.
  - prepost_case 0 0 withPre eqPreCase; [ exact (r = r0) |].
    prepost_exclude_remaining.
  - prove_refinement_continue.
Qed.

Lemma test_total_spec_loop E (x : nat) :
  @spec_refines E E nil nil eqPreRel eqPostRel nat nat eq
                  (MultiFixS E nil (unary1Frame nat nat)
                    ((fun a => if a =? 0 then RetS 0
                               else a' <- CallS _ _ _ (mkFrameCall (unary1Frame nat nat)
                                                      0 (pred a)) ;;
                                    RetS (S a')), tt)
                    (mkFrameCall (unary1Frame nat nat) 0 x))
                  (total_spec (fun _ => True)
                              (fun a b => a = b) x).
Proof.
  prove_refinement.
  - wellfounded_decreasing_nat; exact a.
  - prepost_case 0 0 withPre eqPreCase; [ exact (r = r0) |].
    prepost_exclude_remaining.
  - prove_refinement_continue.
    + apply Nat.eqb_eq in e_if; eauto.
    + destruct a; [ discriminate e_if | eauto ].
    + destruct a; [ discriminate e_if | eauto ].
Qed.

(* 
Lemma test_total_spec_less_easy E (x : nat) :
  @spec_refines E E nil nil eqPreRel eqPostRel nat nat eq
                  (MultiFixS E nil testFrame1
                    ((fun a => CallS _ _ _ (mkFrameCall testFrame1 1 (a + 1))),
                     ((fun a => RetS (a + 1)), tt))
                    (mkFrameCall testFrame1 1 x))
                  (total_spec (fun _ => True)
                              (fun a b => a = (b + 2)) x).
Proof.
  prove_refinement.
  - wellfounded_none.
  - prepost_case 0 0 withPre eqPreCase.
    { simpl; intros. exact () } *)
