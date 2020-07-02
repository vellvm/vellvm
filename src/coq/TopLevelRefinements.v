From ITree Require Import
     ITree
     ITreeFacts
     Events.State
     Events.StateFacts
     InterpFacts
     KTreeFacts
     Eq.Eq.

(* YZ TODO : Revisit the dependency w.r.t. Refinement *)
From Vellvm Require Import
     Util
     PropT
     DynamicTypes
     CFG
     Memory
     Refinement
     TopLevel
     LLVMAst
     InterpreterMCFG
     InterpreterCFG
     Handlers.Handlers.

From ExtLib Require Import
     Structures.Functor.

From Coq Require Import
     Strings.String
     Logic
     Morphisms
     Relations
     List.

From ITree Require Import
     Basics.Monad
     Basics.MonadState.
Require Import Paco.paco.

Import ListNotations.
Import ITree.Basics.Basics.Monads.

Module R := Refinement.Make Memory.Addr LLVMEvents.
Import R. 

(**
   YZ: Trying to figure how to tidy up everything. This file is currently a holdall.
   In here, we have:
   * partial interpreters to each levels;
   * hierarchies of refinements of mcfgs and proofs of inclusions;
   * lemmas for each partial interpreter of commutation with bind and ret;
   * some misc proper instances;
   * admitted statement of inclusion of the intepreter into the model;
 **)


(** The module _Refinement.Make_ defines a series of refinements between
    [itree]s at the various signatures of events a Vellvm goes through during
    the chain of interpretations leading to the definition of the model.
    These refinements state set inclusion of the concretization of the
    returned under-defined values, but impose no constraints on the states.

    In this module, we show that these refinements define a chain of growing
    relations when composed with the bits of interpretations relating each
    level.

    Finally, this allows us to lift these relations on [itree]s to a growing
    chain of relations on [mcfg typ].
 *)

(** BEGIN TO MOVE *)
Lemma subrelation_R_TT:
  forall A (R : relation A), subrelation R TT.
Proof. firstorder. Qed.

Lemma subrelation_prod_left :
  forall A B (R R' : relation A) (R2 : relation B), subrelation R R' -> subrelation (R × R2) (R' × R2).
Proof.
  intros A B R R' R2 H.
  unfold subrelation in *.
  intros x y HRR2.
  inversion HRR2; firstorder.
Qed.

Lemma eutt_tt_to_eq_prod :
  forall X R (RR : relation R) E (t1 t2 : itree E (X * R)),
    eutt (eq × RR) t1 t2 -> eutt (TT × RR) t1 t2.
Proof.
  intros X R RR E t1 t2 Heutt.
  unfold eutt.
  apply (eqit_mon (eq × RR) (TT × RR) true true true true); trivial.
  intros x0 x1 PR.
  eapply subrelation_prod_left. apply subrelation_R_TT. all: apply PR.
Qed.

(*  SAZ: Unfortunately it doesn't look this this version of 
    Proper for interp_prop can be proved.  The problem is that 
    we need the RR parameter for the Proper instance  because it is instantiated with 
    the refinement relation in the refine_34 and refine_45 lemmas
    This is fine, except that the definition of iter_PropT that we use
    bakes in a use of [eutt eq]   

  Global Polymorphic Instance MonadIter_Prop {E} : MonadIter (PropT E) :=
    fun R I (step : I -> PropT E (I + R)) i =>
      fun (r : itree E R) =>
        (exists step' : I -> itree E (I + R)%type,
            (* How do we state that something is out of bounds? *)
            (forall j, step j (step' j)) /\
            CategoryOps.iter step' i ≈ r).   (* <---- eutt eq used here, but "should" be eutt RR *)

    We can't parameterize the definition above by RR because the type of 
    iter is too polymorphic -- there's no way to pass in the RR instance 
    we need.

    What are the alternatives?
     - somehow define specialized versions of interp_prop ?  (maybe without using interp?)
     - somehow avoid using the MonadIter typeclass?



 *)
Lemma eutt_iter'' {E I1 I2 R1 R2}
      (RI1 RI2 : I1 -> I2 -> Prop)
      (HSUB: RI2 <2= RI1)
      (RR : R1 -> R2 -> Prop)
      (body1 : I1 -> itree E (I1 + R1))
      (body2 : I2 -> itree E (I2 + R2))
      (eutt_body
       : forall j1 j2, RI1 j1 j2 -> eutt (sum_rel RI2 RR) (body1 j1) (body2 j2))
  : forall (i1 : I1) (i2 : I2) (RI_i : RI1 i1 i2),
    @eutt E _ _ RR (ITree.iter body1 i1) (ITree.iter body2 i2).
Proof.
  einit. ecofix CIH. intros.
  specialize (eutt_body i1 i2 RI_i).
  do 2 rewrite unfold_iter.
  ebind; econstructor; eauto with paco.
  intros ? ? [].
  - etau.
  - eauto with paco.
Qed.

Definition eutt_iter_gen' {F A B R1 R2 S} (HS : R2 <2= R1) :
  @Proper ((A -> itree F (A + B)) -> A -> itree F B)
          ((R1 ==> eutt (sum_rel R2 S)) ==> R1 ==> (eutt S))
          (iter (C := ktree F)).
Proof.
  do 3 red;
  intros body1 body2 EQ_BODY x y Hxy. red in EQ_BODY.
  eapply eutt_iter''; eauto.
Qed.


Lemma transpose_transpose_id1 {A} (RR : relation A) : transpose (transpose RR) <2= RR.
Proof. intros. unfold transpose in *. assumption.
Qed.
       
Lemma transpose_transpose_id2 {A} (RR : relation A) : RR <2= transpose (transpose RR).
Proof. intros. unfold transpose in *. assumption.
Qed.
       
Lemma eutt_transpose_symmetric : forall
  {E A} (RR : relation A) (t1 t2 : itree E A),
    eutt RR t1 t2 <-> eutt (transpose RR) t2 t1.
Proof.
Admitted.

Lemma transpose_eutt : forall
  {E A} (RR : relation A) (t1 t2 : itree E A),
    transpose (eutt RR) t1 t2 <-> eutt (transpose RR) t1 t2.
Proof.
Admitted.


Lemma interp_prop_correct_exec:
  forall {E F} (h_spec: E ~> PropT F) (h: E ~> itree F),
    handler_correct h_spec h ->
    forall R RR `{Reflexive _ RR} t, interp_prop h_spec R RR t (interp h t).
Proof.
  intros.
  exists h; split; auto. reflexivity.
Qed.


Lemma tau_eutt_RR_l : forall E R (RR : relation R) (HRR: Reflexive RR) (HRT: Transitive RR) (t s : itree E R),
    eutt RR (Tau t) s <-> eutt RR t s.
Proof.
  intros.
  split; intros H.
  - eapply transitivity. 2 : { apply H. }
    red. apply eqit_tauR. reflexivity.
  - red. red. pstep. econstructor. auto. punfold H.
Qed.  

Lemma tau_eutt_RR_r : forall E R (RR : relation R) (HRR: Reflexive RR) (HRT: Transitive RR) (t s : itree E R),
    eutt RR t (Tau s) <-> eutt RR t s.
Proof.
  intros.
  split; intros H.
  - eapply transitivity. apply H.
    red. apply eqit_tauL. reflexivity.
  - red. red. pstep. econstructor. auto. punfold H.
Qed.  

Lemma eutt_bind_RR : forall E X R (RR : relation R) (HRR: Reflexive RR) (HRT: Transitive RR)
                       (t : itree E X) (k1 k2 : X -> itree E R) (s : itree E R),
    eutt RR (bind t k1) s ->
    forall x, eutt RR (k1 x) (k2 x) ->
         eutt RR (bind t k2) s.
Proof.
  intros E X R RR HRR HRT t k1 k2 s Ht x Hk.
Admitted.  


Instance interp_prop_Proper_eq :
  forall R (RR : relation R) (HR: Reflexive RR) (HT : Transitive RR) E F (h_spec : E ~> PropT F),
    Proper (@eutt _ _ _ RR ==> eq ==> flip Basics.impl) (@interp_prop E _ h_spec R RR).
Proof.
  intros.
  do 5 red.
  intros t1 t2 eqt s' s eqs HI.
  subst.
  unfold interp_prop, interp in HI. red in HI.

  destruct HI as (h & HC & HE).

  exists h. split; auto.

  eapply transitivity. 2 : { apply HE. } clear HE s.
  
  revert t1 t2 eqt.

  ginit.
  gcofix CIH.

  intros.

  unfold interp. 
  unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree in *.
  do 2 rewrite unfold_iter.

  punfold eqt. red in eqt.

  guclo eqit_clo_bind. apply Eq.pbc_intro_h with (RU := sum_rel (eutt RR) RR).
  - genobs t1 obt1.
    genobs t2 obt2.

    revert t1 t2 Heqobt1 Heqobt2.

    induction eqt; intros; cbn in *.
    + pstep. red. econstructor. right. assumption.
    + pstep. red. econstructor. left. pclearbot. pinversion REL.
    + unfold ITree.map. eapply eutt_clo_bind with (UU := eq).
      reflexivity.
      intros; subst. pstep. red. econstructor.
      left. specialize (REL u2). pclearbot. pinversion REL.
    + admit.
      (* Surprisingly, the case with a Tau on one side but not the other is the
          hardest!  The problem is that the iterator used by interp runs a "no
          op" loop when it hits the Tau case, which means that, even though two
          computations might be eutt, they might unroll the loop a different
          number of times. This proof strategy that I'm following here unrolls
          both loops in parallel and expects their iterations to line up...

          This observation might mean that we need a different, more wholistic
          approach to this proof... :-(
       *)
    + admit.
  - intros.
    cbn.
    inversion H.
    + cbn. gstep. red. econstructor.
    change (ITree.iter
          (fun t : itree (fun H : Type => E H) R =>
           match observe t with
           | RetF r0 => Ret (inr r0)
           | TauF t0 => Ret (inl t0)
           | @VisF _ _ _ X e k => ITree.map (fun x : X => inl (k x)) (h X e)
           end) a1) with (interp h a1).
    change (ITree.iter
          (fun t : itree (fun H : Type => E H) R =>
           match observe t with
           | RetF r0 => Ret (inr r0)
           | TauF t0 => Ret (inl t0)
           | @VisF _ _ _ X e k => ITree.map (fun x : X => inl (k x)) (h X e)
           end) a2) with (interp h a2).
    gfinal. left.
    apply CIH. assumption.
    + cbn.
      gstep. red. econstructor. assumption.
Admitted.      

    
  
Hint Unfold TT : core.
Instance TT_equiv :
  forall A, Equivalence (@TT A).
Proof.
  intros A; split; repeat intro; auto.
Qed.

(** END TO MOVE *)


(** We first prove that the [itree] refinement at level [i] entails the
    refinement at level [i+1] after running the [i+1] level of interpretation
 *)

Lemma refine_01: forall t1 t2 g,
    refine_L0 t1 t2 -> refine_L1 (interp_global t1 g) (interp_global t2 g).
Proof.
  intros t1 t2 g H.
  apply eutt_tt_to_eq_prod, eutt_interp_state; auto.
Qed.

Lemma refine_12 : forall t1 t2 l,
    refine_L1 t1 t2 -> refine_L2 (interp_local_stack (handle_local (v:=uvalue)) t1 l) (interp_local_stack (handle_local (v:=uvalue)) t2 l).
Proof.
  intros t1 t2 l H.
  apply eutt_tt_to_eq_prod, eutt_interp_state; auto.
Qed.

Lemma refine_23 : forall t1 t2 m,
    refine_L2 t1 t2 -> refine_L3 (interp_memory t1 m) (interp_memory t2 m).
Proof.
  intros t1 t2 m H.
  apply eutt_tt_to_eq_prod, eutt_interp_state; auto.
Qed.

Lemma transpose_reflexive : forall {A} (RR : A -> A -> Prop) (HR : Reflexive RR), Reflexive (transpose RR).
Proof.
  intros. repeat red. apply HR.
Qed.  


(* Things are different for L4 and L5: we get into the [Prop] monad. *)
Lemma refine_34 : forall t1 t2,
    refine_L3 t1 t2 -> refine_L4 (model_undef (transpose refine_res3) t1) (model_undef (transpose refine_res3) t2).
Proof.
  intros t1 t2 H t Ht.
  exists t; split.
  - unfold model_undef in *.
    unfold L3 in *.
    match goal with |- PropT.interp_prop ?x _ _ _ _ => remember x as h end.
    eapply interp_prop_Proper_eq in Ht.
    apply Ht.
    + apply transpose_reflexive. typeclasses eauto.
    + admit. (* follows from transitivity of refine_res3 *)
    + rewrite <- eutt_transpose_symmetric. assumption.
    + reflexivity.
  - reflexivity.
Admitted.

Lemma refine_45 : forall Pt1 Pt2,
    refine_L4 Pt1 Pt2 -> refine_L5 (model_UB (transpose refine_res3) Pt1) (model_UB (transpose refine_res3) Pt2).
Proof.
  intros Pt1 Pt2 HR t2 HM.
  exists t2; split; [| reflexivity].
  destruct HM as (t2' & HPt2 & HPT2).
  apply HR in HPt2; destruct HPt2 as (t1' & HPt1 & HPT1).
  exists t1'; split; auto.
  match type of HPT2 with | PropT.interp_prop ?h' ?t _ _ _ => remember h' as h end.
  eapply interp_prop_Proper_eq with (RR := transpose (refine_res3)); eauto.
  - apply transpose_reflexive. typeclasses eauto.
  - admit. (* follows from transitivity of refine_res3 *)
  - rewrite <- eutt_transpose_symmetric. assumption.
Admitted.

Section TopLevelInputs.
  Variable ret_typ : dtyp.
  Variable entry : string.
  Variable args : list uvalue.
  Variable user_intrinsics: IS.intrinsic_definitions.

  Definition denote_vellvm_init := denote_vellvm ret_typ entry args.
  
(**
   In particular, we can therefore define top-level models
   short-circuiting the interpretation early.
 *)

Definition model_to_L1  (prog: mcfg dtyp) :=
  let L0_trace := denote_vellvm_init prog in
  interp_to_L1 user_intrinsics L0_trace [].

Definition model_to_L2 (prog: mcfg dtyp) :=
  let L0_trace := denote_vellvm_init prog in
  interp_to_L2 user_intrinsics L0_trace [] ([],[]).

Definition model_to_L3 (prog: mcfg dtyp) :=
  let L0_trace := denote_vellvm_init prog in
  interp_to_L3 user_intrinsics L0_trace [] ([],[]) empty_memory_stack.

Definition model_to_L4 (prog: mcfg dtyp) :=
  let L0_trace := denote_vellvm_init prog in
  interp_to_L4 (transpose refine_res3) user_intrinsics L0_trace [] ([],[]) empty_memory_stack.

Definition model_to_L5 (prog: mcfg dtyp) :=
  let L0_trace := denote_vellvm_init prog in
  interp_to_L5 (transpose refine_res3) user_intrinsics L0_trace [] ([],[]) empty_memory_stack.

(**
   Which leads to five notion of equivalence of [mcfg]s.
   Note that all reasoning is conducted after conversion to [mcfg] and
   normalization of types.
 *)
Definition refine_mcfg_L1 (p1 p2: mcfg dtyp): Prop :=
  R.refine_L1 (model_to_L1 p1) (model_to_L1 p2).

Definition refine_mcfg_L2 (p1 p2: mcfg dtyp): Prop :=
  R.refine_L2 (model_to_L2 p1) (model_to_L2 p2).

Definition refine_mcfg_L3 (p1 p2: mcfg dtyp): Prop :=
  R.refine_L3 (model_to_L3 p1) (model_to_L3 p2).

Definition refine_mcfg_L4 (p1 p2: mcfg dtyp): Prop :=
  R.refine_L4 (model_to_L4 p1) (model_to_L4 p2).

Definition refine_mcfg  (p1 p2: mcfg dtyp): Prop :=
  R.refine_L5 (model_to_L5 p1) (model_to_L5 p2).

(**
   The chain of refinements is monotone, legitimating the ability to
   conduct reasoning before interpretation when suitable.
 *)
Lemma refine_mcfg_L1_correct: forall p1 p2,
    refine_mcfg_L1 p1 p2 -> refine_mcfg p1 p2.
Proof.
  intros p1 p2 HR.
  apply refine_45, refine_34, refine_23, refine_12, HR.
Qed.

Lemma refine_mcfg_L2_correct: forall p1 p2,
    refine_mcfg_L2 p1 p2 -> refine_mcfg p1 p2.
Proof.
  intros p1 p2 HR.
  apply refine_45, refine_34, refine_23, HR.
Qed.

Lemma refine_mcfg_L3_correct: forall p1 p2,
    refine_mcfg_L3 p1 p2 -> refine_mcfg p1 p2.
Proof.
  intros p1 p2 HR.
  apply refine_45, refine_34, HR.
Qed.

Lemma refine_mcfg_L4_correct: forall p1 p2,
    refine_mcfg_L4 p1 p2 -> refine_mcfg p1 p2.
Proof.
  intros p1 p2 HR.
  apply refine_45, HR.
Qed.

(* MOVE *)
Ltac flatten_goal :=
  match goal with
  | |- context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

Ltac flatten_hyp h :=
  match type of h with
  | context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

Ltac flatten_all :=
  match goal with
  | h: context[match ?x with | _ => _ end] |- _ => let Heq := fresh "Heq" in destruct x eqn:Heq
  | |- context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

(* Instance pick_handler_proper {E R} `{LLVMEvents.UBE -< E}: *)
(*   Proper (eq ==> eq_itree eq ==> iff) (@Pick_handler E _ R). *)
(* Admitted. *)


(* Lemma interp_prop_mon: *)
(*   forall {E F} (h h': E ~> (PropT (itree F))), *)
(*     (forall e t, h _ e t -> h' _ e t) -> *)
(*     forall t, interp_prop h _ t -> interp_prop h' _ t. *)

  
    
  
(*  
  3: {  unfold interp. unfold iter, Iter_Kleisli. reflexivity. }
  - do 2 red.

    ginit.
    gcofix CIH.
    intros.
    punfold H2. red in H2.
    destruct (observe x).
    + destruct (observe y).
      * inversion H2. subst. gstep. red.  econstructor. 
Admitted.
  - intros t'.    
  destruct (observe t') eqn:EQ; cbn; rewrite EQ; try reflexivity.
  exists (h _ e); auto.
Qed.
*)

Lemma case_prop_handler_correct:
  forall {E1 E2 F}
    (h1_spec: E1 ~> PropT F)
    (h2_spec: E2 ~> PropT F)
    (h1: E1 ~> itree F)
    (h2: E2 ~> itree F)
    (C1: handler_correct h1_spec h1)
    (C2: handler_correct h2_spec h2),
    handler_correct (case_ h1_spec h2_spec) (case_ h1 h2).
Proof.
  intros E1 E2 F h1_spec h2_spec h1 h2 C1 C2.
  unfold handler_correct in *.
  intros T e.
  destruct e. apply C1. apply C2.
Qed.

Lemma UB_handler_correct: handler_correct UB_handler UB_exec.
Proof.
  unfold UB_handler. unfold UB_exec.
  unfold handler_correct.
  intros. auto.
Qed.  


Definition prop_compose :=
  fun {F G : Type -> Type } {T : Type} (TT : relation T)
    (g_spec : F ~> PropT G) (PF: PropT F T) (g:itree G T) =>
    exists f : itree F T, PF f /\ (interp_prop g_spec) T TT f g.

(* Level 5 interpreter Prop to Prop *)
(* h_spec is the PickHandler *)
Definition handler_correct_prop
           {E F G}
           (h_spec: E ~> PropT F) (h: E ~> itree F)
           (g_spec: F ~> PropT G) (g: F ~> itree G)
  :=
    (forall T TT e,
        (prop_compose TT g_spec (h_spec T e))
          (interp g (h T e))).


(* L4 = ExternalCallE +' LLVMEvents.UBE +' LLVMEvents.DebugE +' LLVMEvents.FailureE *)

(* Check (case_ (E_trigger_prop (F:=LLVMEvents.DebugE +' LLVMEvents.FailureE)) (case_ UB_handler (F_trigger_prop (F:=LLVMEvents.DebugE +' LLVMEvents.FailureE)))). *)

(*
Check (@F_trigger_prop LLVMEvents.ExternalCallE (LLVMEvents.DebugE +' LLVMEvents.FailureE)).
Check (case_ (@E_trigger_prop LLVMEvents.ExternalCallE)
              (case_ UB_handler (@F_trigger_prop _ (LLVMEvents.DebugE +' LLVMEvents.FailureE))): PropT L4 ~> PropT L5).

Check  ((case_ E_trigger_prop (case_ UB_handler F_trigger_prop)) : L4 ~> PropT L5).
*)

(*
Lemma pickE_UB_correct `{LLVMEvents.UBE -< L4} `{LLVMEvents.FailureE -< L4} :
  handler_correct_prop
    (Pick_handler : PickE ~> PropT L4)
    (concretize_picks : PickE ~> itree L4)
    (case_ (E_trigger_prop (F:=LLVMEvents.DebugE +' LLVMEvents.FailureE)) (case_ UB_handler (F_trigger_prop (F:=LLVMEvents.DebugE +' LLVMEvents.FailureE))))
    (case_ (E_trigger (F:=LLVMEvents.DebugE +' LLVMEvents.FailureE))
           (case_ UB_exec (F_trigger (F:=LLVMEvents.DebugE +' LLVMEvents.FailureE)))).
Proof.
  unfold handler_correct_prop.
  intros.
  unfold prop_compose.
  destruct e.
  cbn.
  assert (P \/ ~P).
  { admit. (* TODO: Classical logic *) }
  destruct H1.
  - eexists (translate _ (concretize_uvalue u)).
    Unshelve. 2 :
    {  refine (fun T fu => _).
       destruct fu; auto. }
    cbn. split. 
  
Abort.    
*)  

Lemma refine_UB
  : forall E F `{LLVMEvents.FailureE -< E +' F} T TT (HR: Reflexive TT)
                      (x : _ -> Prop)
                      (y : itree (E +' LLVMEvents.UBE +' F) T),
      x y -> model_UB TT x (exec_UB y).
  Proof.
    intros E F H T TT HR x y H0.
    unfold model_UB. unfold exec_UB.
    exists y. split. assumption.
    apply interp_prop_correct_exec.
    intros.
    apply case_prop_handler_correct.
    unfold handler_correct. intros. reflexivity.
    apply case_prop_handler_correct.
    apply UB_handler_correct.
    unfold handler_correct. intros. reflexivity.
    assumption.
Qed.

Lemma Pick_handler_correct :
  forall E `{LLVMEvents.FailureE -< E} `{LLVMEvents.UBE -< E},
    handler_correct (@Pick_handler E _ _) concretize_picks.
Proof.  
  unfold handler_correct.
  intros.
  destruct e.
  cbn. apply PickD with (res := concretize_uvalue u).
  - apply Pick.concretize_u_concretize_uvalue.
  - reflexivity.
Qed.
  
Lemma refine_undef
  : forall (E F:Type -> Type) T TT (HR: Reflexive TT)  `{LLVMEvents.UBE -< F} `{LLVMEvents.FailureE -< F}
                      (x : itree _ T),
      model_undef TT x (@exec_undef E F _ _ _ x).
Proof.
  intros E F H H0 T TT HR x.
  cbn in *.
  unfold model_undef.
  unfold exec_undef.
  apply interp_prop_correct_exec.
  apply case_prop_handler_correct.
  unfold handler_correct. intros. reflexivity.
  apply case_prop_handler_correct.
  apply Pick_handler_correct.

  unfold handler_correct. intros. reflexivity.
  assumption.
Qed.

(**
   SAZ : Possible entry point here
   We should be able to prove that the interpreter belongs to the model.
 *)
Theorem interpreter_sound: forall p, model p (interpreter p).
Proof.
  intros p.
  unfold model, model_user.
  unfold interpreter, interpreter_user.
  unfold interp_to_L5.
  unfold interp_to_L5_exec.
  apply refine_UB.  auto.
  apply refine_undef. auto.
Qed.
  
(**
   Each interpreter commutes with [bind] and [ret].
 **)

(** We hence can also commute them at the various levels of interpretation *)

(** BEGIN MOVE *)


(* Instance runState_proper_eqit {E A env} : Proper (Monad.eqm ==> Logic.eq ==> eutt Logic.eq) (@runState E A env). *)
(* Proof. *)
(*   repeat intro; subst. unfold runState. *)
(*   unfold eqm, ITreeMonad.EqM_ITree in H. *)
(*   rewrite H; reflexivity. *)
(* Qed. *)

Instance interp_state_proper {T E F S}
         (h: forall T : Type, E T -> Monads.stateT S (itree F) T)
  : Proper (eutt Logic.eq ==> Monad.eqm) (State.interp_state h (T := T)).
Proof.
  einit. ecofix CIH. intros.

  rewrite !unfold_interp_state. punfold H0. red in H0.
  induction H0; intros; subst; simpl; pclearbot.
  - eret.
  - etau.
  - ebind. econstructor; [reflexivity|].
    intros; subst.
    etau. ebase.
  - rewrite tau_euttge, unfold_interp_state; eauto.
  - rewrite tau_euttge, unfold_interp_state; eauto.
Qed.

(** END MOVE *)

Lemma interp_to_L2_bind:
  forall ui {R S} (t: itree L0 R) (k: R -> itree L0 S) s1 s2,
    interp_to_L2 ui (ITree.bind t k) s1 s2 ≈
                 (ITree.bind (interp_to_L2 ui t s1 s2) (fun '(s1',(s2',x)) => interp_to_L2 ui (k x) s2' s1')).
Proof.
  intros.
  unfold interp_to_L2.
  rewrite interp_intrinsics_bind, interp_global_bind, interp_local_stack_bind.
  apply eutt_clo_bind with (UU := Logic.eq); [reflexivity | intros ? (? & ? & ?) ->; reflexivity].
Qed.

Lemma interp_to_L2_ret: forall ui (R : Type) s1 s2 (x : R), interp_to_L2 ui (Ret x) s1 s2 ≈ Ret (s2, (s1, x)).
Proof.
  intros; unfold interp_to_L2.
  rewrite interp_intrinsics_ret, interp_global_ret, interp_local_stack_ret; reflexivity.
Qed.

Definition interp_cfg {R: Type} (trace: itree instr_E R) g l m :=
  let uvalue_trace   := interp_intrinsics [] trace in
  let L1_trace       := interp_global uvalue_trace g in
  let L2_trace       := interp_local L1_trace l in
  let L3_trace       := interp_memory L2_trace m in
  let L4_trace       := model_undef Logic.eq L3_trace in
  let L5_trace       := model_UB Logic.eq L4_trace in
  L5_trace.

Definition model_to_L5_cfg (prog: cfg dtyp) :=
  let trace := D.denote_cfg prog in
  interp_cfg trace [] [] empty_memory_stack.

Definition refine_cfg_ret: relation (PropT L5 (memory_stack * (local_env * (global_env * uvalue)))) :=
  fun ts ts' => forall t, ts t -> exists t', ts' t' /\ eutt  (TT × (TT × (TT × refine_uvalue))) t t'.

(* Definition refine_cfg  (p1 p2: cfg dtyp): Prop := *)
(*   refine_cfg_ret (model_to_L5_cfg p1) (model_to_L5_cfg p2). *)

End TopLevelInputs.
