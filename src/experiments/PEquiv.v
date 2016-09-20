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
| s_nil : stream X
| s_cons : X -> stream X -> stream X.

CoFixpoint map_stream A B (f:A -> B) (s:stream A) : stream B :=
  match s with
  | s_nil _ => s_nil _
  | s_cons a s' => s_cons (f a) (map_stream f s')
  end.

Arguments s_nil [_].

CoInductive trace {X} (M:Mach X) : stream X -> Prop :=
| trace_one : forall x, 
  m_wf M x ->
  m_step M x = None -> 
  trace M (s_cons x s_nil)
| trace_cons : forall x x' s, 
  m_wf M x ->
  m_step M x = Some x' -> 
  trace M (s_cons x' s) ->
  trace M (s_cons x (s_cons x' s)).

Definition mtrace {X} M : Type := { s | @trace X M s }.

(* maybe it's hard to define an equivalence on traces without this representation? *)
Record Equiv {A} (R:A -> A -> Prop) :=
  { equiv_refl : forall a, R a a
  ; equiv_sym : forall a b, R a b -> R b a
  ; equiv_trans : forall a b c, R a b -> R b c -> R a c
  }.


Section FOO.

Variables (X Y:State) (M:Mach X) (N:Mach Y) (U:HEmbed M N).

Definition lift_hembed (R:mtrace M -> mtrace M -> Prop) : mtrace N -> mtrace N -> Prop.
  refine 
    (fun s t =>
       R (exist _ (map_stream (he_load U) (proj1_sig s)) _)
         (exist _ (map_stream (he_load U) (proj1_sig t)) _)).
  admit.
  admit.
Admitted.

Definition lower_hembed (R:mtrace N -> mtrace N -> Prop) : mtrace M -> mtrace M -> Prop.
  refine 
    (fun s t =>
       R (exist _ (map_stream (he_unload U) (proj1_sig s)) _)
         (exist _ (map_stream (he_unload U) (proj1_sig t)) _)).
  admit.
  admit.
Admitted.


Definition ueq (s t:mtrace M) : Prop :=
  match proj1_sig s, proj1_sig t with
  | s_nil, _ | _, s_nil => False
  | s_cons x _, s_cons y _ => U x = U y
  end.

Parameter ueq_equiv : Equiv ueq.

Theorem main : forall
  (R:mtrace M -> mtrace M -> Prop) (Hequiv:Equiv R)
  (Hincl:forall s t, ueq s t -> R s t),
  Equiv (lift_hembed R) /\
  forall s t, R s t <-> (lift_hembed R) (he_unload U s) (he_unload U t).
  




  

  