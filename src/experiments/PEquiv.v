(* Notes
- loading each state of a SOS execution produces an execution that technically
  isn't a abstract machine execution -- suggests we might not want to limit
  ourselves to the type of machine executions
- alternatively, it might be necessary to define the machine induced by the
  the SOS step relation on machine states. That is, where the step function is
  load o SOS.step o unload
*)


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
  Stream { s_hd : X
         ; s_tl : option (stream X)
         }.

Definition stream_id {X} (s:stream X) : stream X :=
  let 'Stream hd tl := s in
  Stream hd tl.

Lemma stream_id_eq X : forall s : stream X,
  s = stream_id s.
Proof.
  intro. destruct s. simpl. reflexivity.
Qed.

CoFixpoint map_stream {X Y} (f:X -> Y) (s:stream X) : stream Y :=
  match s with
  | Stream hd None => Stream (f hd) None
  | Stream hd (Some tl) => Stream (f hd) (Some (map_stream f tl))
  end.



Record Equiv {A} (R:A -> A -> Prop) :=
  { equiv_refl : forall a, R a a
  ; equiv_sym : forall a b, R a b -> R b a
  ; equiv_trans : forall a b c, R a b -> R b c -> R a c
  }.


Inductive fbisim_step {X Y} (R:stream X -> stream X -> Prop) (U:X -> Y) 
  : stream X -> stream X -> Prop :=
| ueq_one : forall x x',
    U x = U x' ->
    fbisim_step R U {| s_hd := x; s_tl := None |} 
                    {| s_hd := x'; s_tl := None |}
| ueq_step : forall x x' s' t',
    U x = U x' ->
    R s' t' ->
    fbisim_step R U {| s_hd := x; s_tl := Some s' |} 
                    {| s_hd := x'; s_tl := Some t' |}.


CoInductive fbisim {X Y} (U:X->Y) (s t:stream X) : Prop :=
fbism_fix : 
  fbisim_step (fbisim U) U s t ->
  fbisim U s t.

Section FBISIM_COIND.

  Variables (X Y:Type) (U:X -> Y) (R:stream X -> stream X -> Prop).

  Hypothesis H : forall s t, R s t -> fbisim_step R U s t.
  
  Lemma fbisim_coind : forall s t,
    R s t -> fbisim U s t.
  Proof.
    cofix CIH.
    intros s t Hrst. 
    destruct s as [? [s'|]], t as [? [t'|]]; apply H in Hrst; inversion Hrst; subst.
    - constructor. constructor. assumption. apply CIH. assumption.
    - constructor. constructor. assumption.
  Qed.

End FBISIM_COIND.

Section MAIN.

Variables (X Y:State) (M:Mach X) (N:Mach Y) (U:HEmbed M N).

Definition liftrel (R:stream X -> stream X -> Prop) : stream Y -> stream Y -> Prop :=
  fun s t => R (map_stream (he_load U) s) (map_stream (he_load U) t).
    

Variable R : stream X -> stream X -> Prop.

Hypothesis Hequiv : Equiv R.

Hypothesis Hincl : forall s t, fbisim U s t -> R s t.

Lemma unload_load_R : forall s,
  fbisim U (map_stream (he_load U) (map_stream U s)) s.
Proof.
  intros s.
  eapply fbisim_coind with (R:=fun s t => s = (map_stream (he_load U) (map_stream U t))).
  - intros s' t ?; subst s'.
    destruct t as [? [t'|]]. 
    + rewrite stream_id_eq at 1. simpl. constructor.
      rewrite (he_epi U). reflexivity. admit.
      reflexivity.
    + rewrite stream_id_eq at 1. simpl. constructor.
      rewrite (he_epi U). reflexivity. admit.
  - reflexivity.
Admitted.    

(* TODO: need to assume s, t only contain wf states *)
Theorem main :
  Equiv (liftrel R) /\
  forall s t, R s t <-> liftrel R (map_stream U s) (map_stream U t).
Proof.
  intros. split.
  - admit.
  - unfold liftrel. intros s t. split.
    + intros HRst. 
      eapply (equiv_trans Hequiv). apply Hincl. apply unload_load_R.
      eapply (equiv_trans Hequiv). apply HRst.
      eapply (equiv_sym Hequiv). apply Hincl. apply unload_load_R.
    + intros HRst.
      eapply (equiv_trans Hequiv). apply (equiv_sym Hequiv). apply Hincl. apply unload_load_R.
      eapply (equiv_trans Hequiv). apply HRst.
      apply Hincl. apply unload_load_R.
Admitted.
  

End MAIN.
