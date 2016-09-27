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

Record Equiv {A} (R:A -> A -> Prop) :=
  { equiv_refl : forall a, R a a
  ; equiv_sym : forall a b, R a b -> R b a
  ; equiv_trans : forall a b c, R a b -> R b c -> R a c
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

Section STREAM_REL_QUOT.

Variables (X Y:Type) (U:X -> Y) (L:Y -> X).
Hypothesis Hepi : forall y, U (L y) = y.

Lemma unload_load_R : forall s,
  fbisim U (map_stream L (map_stream U s)) s.
Proof.
  intros s.
  eapply fbisim_coind with (R:=fun s t => s = (map_stream L (map_stream U t))).
  - intros s' t ?; subst s'.
    destruct t as [? [t'|]]. 
    + rewrite stream_id_eq at 1. simpl. constructor.
      rewrite Hepi. reflexivity. reflexivity.
    + rewrite stream_id_eq at 1. simpl. constructor.
      rewrite Hepi. reflexivity. 
  - reflexivity.
Qed.

Variable R : stream X -> stream X -> Prop.
Hypothesis Hequiv : Equiv R.
Hypothesis Hincl : forall s t, fbisim U s t -> R s t.

Theorem stream_rel_quot :
  forall s t, R s t <-> R (map_stream L (map_stream U s))
                          (map_stream L (map_stream U t)).
Proof.
  intros s t. split.
  + intros HRst. 
    eapply (equiv_trans Hequiv). apply Hincl. apply unload_load_R.
    eapply (equiv_trans Hequiv). apply HRst.
    eapply (equiv_sym Hequiv). apply Hincl. apply unload_load_R.
  + intros HRst.
    eapply (equiv_trans Hequiv). apply (equiv_sym Hequiv). apply Hincl. apply unload_load_R.
    eapply (equiv_trans Hequiv). apply HRst.
    apply Hincl. apply unload_load_R.
Qed.
  
End STREAM_REL_QUOT.

(* This formulation of program equivalence isn't flexible enough to define, for
   example, terminal states that act as input, or variations of applicative
   similarity. *)

Definition prog_eq {X} : Type := (X -> option X) -> X -> X -> Prop.




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
  { he_U :> X -> Y
  ; he_U_wf : forall x, m_wf M x -> m_wf N (he_U x)
  ; he_L : Y -> X
  ; he_L_wf : forall y, m_wf N y -> m_wf M (he_L y)
  ; he_epi : forall y, m_wf N y -> he_U (he_L y) = y
  ; he_spec : forall x, m_wf M x ->
    option_map he_U (m_step M x) = m_step N (he_U x)
  }.

CoInductive trace `(M:Mach X) : stream X -> Prop :=
| trace_one : forall x,
  m_wf M x ->
  m_step M x = None ->
  trace M (Stream x None)
| trace_step : forall x x' s,
  m_wf M x ->
  m_step M x = Some x' ->
  s_hd s = x' ->
  trace M s ->
  trace M (Stream x (Some s)).

