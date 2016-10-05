Generalizable All Variables.
Set Implicit Arguments.

Add LoadPath "../../papers/ssa-semantics/coq".
Require Import Util Mach.

Require Import Arith List.

Import ListNotations.

(* A machine state is some subset of st_ty that is "well-formed" *)
Record State :=
  { st_ty :> Type
  ; st_dec : forall (x y : st_ty), {x = y} + {x <> y}
  ; st_wf : st_ty -> Prop
  }.

(* A machine is a transition system on well-formed states *)
Record Mach (X:State) :=
  { m_step : X -> option X
  ; m_pres : forall x x', st_wf X x -> m_step x = Some x' -> st_wf X x'
  }.

(* A simulation relation between machines (partial fns on states)
   preserving termination.

   Note: we're not interested in the greatest such relation, defined
   as the greatest fixpoint (vR. mach_sim_step M M' R):

CoInductive mach_similarity {X:State} (M M':Mach X) : X -> X -> Prop :=
mach_sim_fix : forall x x',
  mach_sim_step M M' (mach_similarity M M') x x' ->
  mach_similarity M M' x x'.

   Instead, we define what it means for a relation R to be a
   simulation w.r.t machines M and M' or, alternatively, the relation
   on machines for a given simulation relation R. Note that when R is
   an equivalence on states, this is just extensional functional
   equivalence.

   TODO: is it possible/desirable to augment mach_sim_step to indicate
   that some states are unobservable? I.e. in addition to quotienting
   states, can we introduce some flexibility w.r.t step size? This
   would destroy the intuitivively appealing interpretation of
   mach_sim as fn equivalence... *)

Inductive mach_sim_step {X:State} (M M':Mach X) (R:X -> X -> Prop) : X -> X -> Prop :=
| mach_sim_step_none : forall x x',
  m_step M x = None ->
  m_step M' x' = None ->
  mach_sim_step M M' R x x'
| mach_sim_step_one : forall x x' y y',
  m_step M x = Some y ->
  m_step M' x' = Some y' ->
  R y y' ->
  mach_sim_step M M' R x x'.

Definition mach_sim {X:State} (R:X -> X -> Prop) (M M':Mach X) : Prop :=
  forall x x', st_wf X x -> st_wf X x' ->
  R x x' -> mach_sim_step M M' R x x'.




(* Homomorphic embedding of machines (partial functions) *)
Record HEmbed `(M:Mach X, N:Mach Y, U:X -> option Y) :=
  { he_L : Y -> option X        (* loading *)

  (* well-formedness and totality of load/unload *)
  ; he_U_wf : forall x y, st_wf X x -> U x = Some y -> st_wf Y y
  ; he_L_wf : forall x y, st_wf Y y -> he_L y = Some x -> st_wf X x
  ; he_U_tot : forall x, st_wf X x -> exists y, U x = Some y
  ; he_L_tot : forall y, st_wf Y y -> exists x, he_L y = Some x

  (* definition of homomorphic embedding *)
  ; he_epi : forall y, st_wf Y y -> option_bind (he_L y) U = Some y
  ; he_spec : forall x, st_wf X x ->
    option_bind (m_step M x) U = option_bind (U x) (m_step N)
  }.

(* The main point is that when the "machine equivalence" diagram H
   between a machine M and a "more abstract" machine N, we have an
   induced machine "hembed_mach H" defined in terms of the transitions
   N, loading and unloading, where the equivalence induced by
   unloading is a simulation between M and hembed_mach H. *)
Section HEMBED_SIM.

Context `(M:Mach X, N:Mach Y, H:HEmbed M N U).

Definition hembed_mach : Mach X.
  refine
    {| m_step x := option_bind (option_bind (U x) (m_step N)) (he_L H) |}.
Proof.
  abstract
    (intros x x' Hwfx;
     destruct (U x) as [y|] eqn:Heqy; simpl; [|inversion 1];
     destruct (m_step N y) as [y'|] eqn:Heqy'; simpl; [|inversion 1];
     intros Heqx';
     apply he_L_wf in Heqx'; auto;
     apply (m_pres N) in Heqy'; auto;
     apply (he_U_wf H) in Heqy; auto).
Defined.

Lemma hembed_sim :
  mach_sim (fun x x' => U x = U x') M hembed_mach.
Proof.
  unfold mach_sim. 
  intros ? ? Hwfx Hwfx' Heqxx'.
  destruct (m_step M x) as [x0|] eqn:Hstep, 
           (m_step hembed_mach x') as [x0'|] eqn:Hstep';
    unfold hembed_mach in Hstep'; simpl in Hstep'.
  - eapply mach_sim_step_one; eauto.
    rewrite <- Heqxx' in Hstep'.
    rewrite <- (he_spec H) in Hstep'; auto.
    rewrite Hstep in Hstep'. simpl in Hstep'.
    destruct (U x0) as [y0 |] eqn:Heqs'; [|inversion Hstep'].
    apply f_equal with (f:= fun x => option_bind x U) in Hstep'.
    simpl in Hstep'. rewrite (he_epi H) in Hstep'. auto.
    apply (he_U_wf H) in Heqs'; auto.
    eapply (m_pres M) with (x:=x); eauto.
  - exfalso.
    rewrite <- Heqxx' in Hstep'.
    rewrite <- (he_spec H) in Hstep'; auto.
    rewrite Hstep in Hstep'. simpl in Hstep'.
    destruct (U x0) as [y0|] eqn:Heqs'; [|inversion Hstep'].
    + simpl in Hstep'. 
      eapply f_equal with (f := fun x => option_bind x U) in Hstep'.
      simpl in *.
      rewrite (he_epi H) in Hstep'. congruence. 
      apply (he_U_wf H) in Heqs'; auto.
      eapply (m_pres M) with (x:=x); eauto.
    + apply m_pres, (he_U_tot H) in Hstep as [? ?]; auto. congruence.
  - exfalso.
    rewrite <- Heqxx' in Hstep'.
    rewrite <- (he_spec H) in Hstep'; auto.
    rewrite Hstep in Hstep'. simpl in Hstep'. congruence.
  - eapply mach_sim_step_none; auto.
Qed.

End HEMBED_SIM.


(* To use the above fact, for example to replace reasoning about
   equivalence of abstract machine programs with SOS, we would first
   have to show that the property we want to reason about doesn't
   depend on the "intensional details" of states that are quotiented
   out by unloading. I.E. we're only observing the transition system
   up to machine simulation. Then, whatever we want to show about
   the abstract machine (e.g. an instance of some program equivalence)
   can instead be proven using SOS transitions.

   Note that unloading and loading do essentially nothing for initial
   states. For example, in a CEK-like machine 
   (c, [], []) -> c -> (c, [], [])
   So the traces of the "induced" machine are just the SOS. We don't
   have to worry about proving things about unloading. *)
Section P_QUOT_HEMBED.

Context `(P:Mach X -> Prop, M:Mach X, N:Mach Y, H:HEmbed M N U).

Hypothesis Pinv : forall (M M':Mach X),
  mach_sim (fun x x' => U x = U x') M M' ->
  (P M <-> P M').

Lemma p_quot_hembed : P M <-> P (hembed_mach H).
Proof.
  apply Pinv. apply hembed_sim.
Qed.

End P_QUOT_HEMBED.



Section EXAMPLES.

Definition admit {A} : A. Admitted.

Definition SOS_st :=
  {| st_ty := tm
   ; st_dec := admit
   ; st_wf m := tm_bwf Cmp m = true |}.

Definition CFG_st :=
  {| st_ty := tm * CFG1.st
   ; st_dec := admit
   ; st_wf := prod_curry CFG1.wf_st
   |}.

Context `(SOS:Mach SOS_st, 
          CFG:Mach CFG_st, 
          H:HEmbed CFG SOS (prod_curry CFG1.unload_full)).

Definition return_st (s:CFG_st) (n:nat) : Prop :=
  match s with 
  | (P, (p,e,[])) =>
    match CFG1.compile P p with
    | Some (CFG0.RET o) => CFG0.eval_oval e o = PEAK.DNat n
    | Some (CFG0.ORET a o o') => 
      match CFG0.eval_oval e o, CFG0.eval_oval e o' with
      | PEAK.DNat m, PEAK.DNat m' => eval_op a m m' = n
      | _, _ => False
      end
    | _ => False
    end
  | _ => False
  end.

Definition return_tm (m:tm) (n:nat) : Prop :=
  match m with
  | Prd (Nat n) => True
  | Aop a (Nat u) (Nat v) => eval_op a u v = n
  | _ => False
  end.

Example peq0 (M:Mach CFG_st) (P Q:tm) : Prop :=
  forall n,
    (exists i s,
        option_iter (m_step M) (P, ([],[],[])) i = Some s /\
        return_st s n)
    <->
    (exists i s,
        option_iter (m_step M) (Q, ([],[],[])) i = Some s /\
        return_st s n).

Lemma return_state_unload : forall s m n,
  prod_curry CFG1.unload_full s = Some m ->
  return_tm m n ->
  return_st s n.
Proof.
Admitted.

Lemma mach_sim_iter_ex_iff : forall X (M N:Mach X) R,
  mach_sim R M N ->
  forall i x y, R x y ->
     ((exists x', option_iter (m_step M) x i = Some x')
     <->
     (exists y', option_iter (m_step N) y i = Some y')).
Proof.
Admitted.    

Lemma mach_sim_iter_R : forall X (M N:Mach X) R,
  mach_sim R M N ->
  forall i x y x' y', R x y ->
    option_iter (m_step M) x i = Some x' ->
    option_iter (m_step N) y i = Some y' ->
    R x' y'.
Proof.
Admitted.    

Lemma peq0__abs : forall m m',
  peq0 CFG m m' <-> peq0 (hembed_mach H) m m'.
Proof.
  intros m m'.
  apply p_quot_hembed with (P := fun M => peq0 M m m').
  intros M M' Hsim.
  split.
  - unfold peq0. intros Heq n. split.
    + intros [i [s [Hstep Hret]]].
      pose proof (mach_sim_iter_ex_iff Hsim i (m, ([],[],[])) (m, ([],[],[]))) as Hstep'.
      simpl in Hstep'. 
      pattern s in Hstep.
      specialize (Hstep' eq_refl).
      pose proof (ex_intro _ s Hstep). apply Hstep' in H0 as [s' ?].
      eapply Heq.
      exists i, s'. split.
      specialize (Heq n).
      eapply Heq.

      
      eapply Hstep' in Hstep.
Abort.

End EXAMPLES.