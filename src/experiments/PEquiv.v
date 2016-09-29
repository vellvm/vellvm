Generalizable All Variables.
Set Implicit Arguments.

Require Import Arith List.

Import ListNotations.

Record Equiv {A} (R:A -> A -> Prop) :=
  { equiv_refl : forall a, R a a
  ; equiv_sym : forall a b, R a b -> R b a
  ; equiv_trans : forall a b c, R a b -> R b c -> R a c
  }.

Record State :=
  { st_ty :> Type
  ; st_dec : forall (x y : st_ty), {x = y} + {x <> y}
  ; st_wf : st_ty -> Prop
  }.

Record Mach (X:State) :=
  { m_step : X -> option X
  ; m_pres : forall x, st_wf X x -> 
      match m_step x with 
      | None => True 
      | Some x' => st_wf X x' 
      end
  }.

(* Homomorphic embedding *)
Record HEmbed `(M:Mach X, N:Mach Y) :=
  { he_U : X -> Y
  ; he_U_wf : forall x, st_wf X x -> st_wf Y (he_U x)
  ; he_L : Y -> X
  ; he_L_wf : forall y, st_wf Y y -> st_wf X (he_L y)
  ; he_epi : forall y, st_wf Y y -> he_U (he_L y) = y
  ; he_spec : forall x, st_wf X x ->
    option_map he_U (m_step M x) = m_step N (he_U x)
  }.

(* Simulation between machines (partial fns on states) *)
Definition mach_sim {X:State} (R:X -> X -> Prop) (M M':Mach X) : Prop :=
  forall x x', st_wf X x -> st_wf X x' -> 
    R x x' -> 
    match m_step M x, m_step M' x' with
    | Some y, Some y' => R y y'
    | None, None => True
    | _, _ => False
    end.

(* The main point is that when the "machine equivalence" diagram H
   between a machine M and a "more abstract" machine N, we have an
   induced machine "hembed_mach H" defined in terms of the transitions
   N, loading and unloading, where the equivalence induced by
   unloading is a simulation between M and hembed_mach H. *)
Section HEMBED_SIM.

Context `(M:Mach X, N:Mach Y, H:HEmbed M N).

Definition hembed_mach : Mach X.
  refine
    {| m_step x := option_map (he_L H) (m_step N (he_U H x)) |}.
Proof.
  abstract 
    (intros; apply (he_U_wf H), (m_pres N) in H0;
     destruct (m_step N (he_U H x)) eqn:Heqx;
     [ simpl; apply (he_L_wf H) | ]; auto).
Defined.

Lemma hembed_sim :
  mach_sim (fun x x' => he_U H x = he_U H x') M hembed_mach.
Proof.
  unfold hembed_mach, mach_sim. simpl.
  intros ? ? Hx Hx' Hxx'.
  destruct (m_step M x) eqn:Hstep, (m_step N (he_U H x')) eqn:Hstep';
    simpl; auto.
  - rewrite <- Hxx' in Hstep'.
    rewrite <- (he_spec H) in Hstep'; auto.
    rewrite Hstep in Hstep'. inversion Hstep'; subst s0.
    rewrite (he_epi H); auto. 
    eapply (he_U_wf H). 
    apply (m_pres M) in Hx. rewrite Hstep in Hx. assumption.
  - rewrite <- Hxx' in Hstep'.
    rewrite <- (he_spec H) in Hstep'; auto.
    rewrite Hstep in Hstep'. simpl in *. congruence.
  - rewrite <- Hxx' in Hstep'.
    rewrite <- (he_spec H) in Hstep'; auto.
    rewrite Hstep in Hstep'. simpl in *. congruence.
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

Context `(P:Mach X -> Prop, M:Mach X, N:Mach Y, H:HEmbed M N).

Hypothesis Pinv : forall (M M':Mach X),
  mach_sim (fun x x' => he_U H x = he_U H x') M M' ->
  (P M <-> P M').

Lemma p_quot_hembed : P M <-> P (hembed_mach H).
Proof.
  apply Pinv. apply hembed_sim.
Qed.

End P_QUOT_HEMBED.


(* TODO: Actual CEK machine is a bit too tricky ... 
   easier example from mini branch? *)
Section EXAMPLES.

Inductive tm :=
| Var : nat -> tm
| Lam : tm -> tm
| App : tm -> tm -> tm.

Scheme Equality for tm.

Fixpoint csubst (x:nat) (m v:tm) : tm :=
  match m with
  | Var y => if eq_nat_dec x y then v else (Var y)
  | Lam m => Lam (csubst (S x) m v)
  | App m n => App (csubst x m v) (csubst x n v)
  end.

Fixpoint sos_step (m:tm) : option tm :=
  match m with
  | Var x => None
  | Lam x => None
  | App (Lam m) (Lam n) => Some (csubst 0 m (Lam n))
  | App m (Lam n) => option_map (fun m' => App m' (Lam n)) (sos_step m)
  | App m n => option_map (fun n' => App m n') (sos_step n) 
  end.

Fixpoint closed (x:nat) (m:tm) : bool :=
  match m with
  | Var y => leb (S y) x
  | Lam m => closed (S x) m
  | App m n => andb (closed x m) (closed x n)
  end.

Definition TM : State :=
  {| st_ty := tm
   ; st_dec := tm_eq_dec
   ; st_wf m := closed 0 m = true
  |}.

Require Omega.

Lemma closed_weaken : forall m x,
  closed x m = true ->
  closed (S x) m = true.
Proof.
  induction m.
  - unfold closed. intros. apply leb_iff. apply leb_iff in H. omega.
  - intros. apply IHm. simpl in H. assumption.
  - intros. simpl. rewrite IHm1, IHm2; auto; simpl in *.
    + destruct (closed x m2); auto.  destruct (closed x m1); inversion H. 
    + destruct (closed x m1); auto.
Qed.

Lemma substitution : forall m n x,
  closed x (Lam m) = true ->
  closed x n = true ->
  closed x (csubst x m n) = true.
Proof.
  induction m.
  - intros.
    unfold csubst. destruct (eq_nat_dec x n) as [Heqn|Heqn].
    subst. assumption.
    unfold closed. unfold closed in H. 
    apply leb_iff. apply leb_iff in H. omega.
  - simpl. intros. apply IHm; auto.
    apply closed_weaken. assumption.
  - simpl. intros. rewrite IHm1, IHm2; auto.
    + simpl. destruct (closed (S x) m2); auto. 
      destruct (closed (S x) m1); inversion H.
    + simpl. destruct (closed (S x) m1); auto. 
Qed.    

Definition SOS : Mach TM.
Proof.
  refine (Build_Mach TM sos_step _).
  induction x; simpl; auto.
  intros Hwf.
  destruct x1.
  - inversion Hwf.
  - destruct x2.
    + simpl in Hwf. destruct (closed 1 x1); inversion Hwf.
    + apply Bool.andb_true_iff in Hwf.
      apply substitution; tauto.
    + destruct (sos_step (App _ _)) eqn:Heq' in *.
      apply Bool.andb_true_iff in Hwf.
      simpl. apply Bool.andb_true_iff. split.
      simpl in Hwf; tauto.
      apply IHx2; tauto.
      simpl; auto.
  - destruct x2.
    + simpl; auto.
    + destruct (sos_step (App _ _)) eqn:Heq' in *.
      apply Bool.andb_true_iff in Hwf.
      simpl. apply Bool.andb_true_iff. tauto.
      simpl. auto.
    + destruct (sos_step (App x2_1 _)) eqn:Heq' in *.
      apply Bool.andb_true_iff in Hwf.
      simpl. apply Bool.andb_true_iff. tauto.
      simpl. auto.
Defined.


Inductive clo := Clo : tm -> list clo -> clo.

Inductive frame :=
| farg : clo -> frame
| ffun : clo -> frame.

Definition cek := (clo * list frame)%type.

Fixpoint cek_step (m:tm) (e:list clo) (k:list frame) : option cek :=
  match m, k with
  | Var x, _ => option_map (fun c => (c, k)) (nth_error e x)
  | Lam f, farg (Clo m' e')::k' => 
    Some (Clo m' e', ffun (Clo (Lam f) e)::k')
  | Lam m', ffun (Clo (Lam f) e')::k' =>
    Some (Clo f (Clo (Lam m') e::e'), k')
  | App m' v, _ =>
    Some (Clo m' e, (farg (Clo v e))::k)
  | _, _ => None
  end.

End EXAMPLES.