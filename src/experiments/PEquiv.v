Generalizable All Variables.
Set Implicit Arguments.

Require Import Arith List.

Import ListNotations.

Record State :=
  { st_ty :> Type
  ; st_dec : forall (x y : st_ty), {x = y} + {x <> y}
  }.

Record Mach (X:State) :=
  { m_step : X -> option X
  ; m_wf : X -> Prop
  ; m_pres : forall x, m_wf x -> 
      match m_step x with 
      | None => True 
      | Some x' => m_wf x' 
      end
  }.


Record HEmbed `(M:Mach X, N:Mach Y) :=
  { he_unload :> X -> Y
  ; he_unload_wf : forall x, m_wf M x -> m_wf N (he_unload x)
  ; he_load : Y -> X
  ; he_load_wf : forall y, m_wf N y -> m_wf M (he_load y)
  ; he_epi : forall y, m_wf N y -> he_unload (he_load y) = y
  ; he_spec : forall x, m_wf M x ->
    option_map he_unload (m_step M x) = m_step N (he_unload x)
  }.




CoInductive stream X := 
  { s_hd : X
  ; s_tl : option (stream X)
  }.

Definition stream_id {X} (s:stream X) : stream X :=
  let 'Build_stream hd tl := s in
  {| s_hd := hd; s_tl := tl |}.

Lemma stream_id_eq X : forall s : stream X,
  s = stream_id s.
Proof.
  intro. destruct s. simpl. reflexivity.
Qed.

CoInductive trace {X} (M:Mach X) : stream X -> Prop :=
| trace_one : forall x,
  m_wf M x ->
  m_step M x = None -> 
  trace M {| s_hd := x; s_tl := None |}
| trace_cons : forall x s, 
  m_wf M x ->
  trace M s ->
  m_step M x = Some (s_hd s) -> 
  trace M {| s_hd := x; s_tl := Some s |}.

Definition mtrace {X} M : Type := { s | @trace X M s }.

CoFixpoint mktrace `(M:Mach X) (x:X) : stream X :=
  {| s_hd := x
   ; s_tl := option_map (mktrace M) (m_step M x)
  |}.

Lemma mktrace__trace `(M:Mach X) : forall x, 
  m_wf M x -> trace M (mktrace M x).
Proof.
  cofix CIH. intros x Hwf.
  rewrite stream_id_eq. simpl.
  pose proof (m_pres M x Hwf) as Hpres.
  destruct (m_step M x) eqn:Heq.
  - simpl. constructor; simpl; auto. 
  - simpl. constructor; assumption.
Qed.

Definition mkmtrace `(M:Mach X) (x:X) (Hwf:m_wf M x) : mtrace M :=
  exist _ (mktrace M x) (mktrace__trace M _ Hwf).


(* maybe it's hard to define an equivalence on traces without this representation? *)
Record Equiv {A} (R:A -> A -> Prop) :=
  { equiv_refl : forall a, R a a
  ; equiv_sym : forall a b, R a b -> R b a
  ; equiv_trans : forall a b c, R a b -> R b c -> R a c
  }.


Section MAIN.

Variables (X Y:State) (M:Mach X) (N:Mach Y) (U:HEmbed M N).

Definition conc (s:mtrace N) : mtrace M.
Proof.
  refine (mkmtrace M (he_load U (s_hd (proj1_sig s))) _).
  abstract (apply he_load_wf; destruct s; simpl;
            inversion t; subst; assumption).
Defined.

Definition abs (s:mtrace M) : mtrace N :=
  refine (mkmtrace M (he_load U (s_hd (proj1_sig s))) _).
  abstract (apply he_load_wf; destruct s; simpl;
            inversion t; subst; assumption).
  

Definition liftrel (R:mtrace M -> mtrace M -> Prop) : mtrace N -> mtrace N -> Prop :=
  fun s t => R (conc s) (conc t).



Definition ueq (s t:mtrace M) : Prop :=
  U (s_hd (proj1_sig s)) = U (s_hd (proj1_sig t)).

Parameter ueq_equiv : Equiv ueq.

Theorem main : forall
  (R:mtrace M -> mtrace M -> Prop) (Hequiv:Equiv R)
  (Hincl:forall s t, ueq s t -> R s t),
  Equiv (lift_hembed R) /\
  forall s t, R s t <-> (lift_hembed R) (he_unload U s) (he_unload U t).
  




  

  