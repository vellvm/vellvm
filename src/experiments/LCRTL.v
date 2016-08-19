Require Import List.

Import ListNotations.

Definition Nth {A:Type} (l:list A) (n:nat) (a:A) : Prop := nth_error l n = Some a.

Definition reg : Type := nat.
Definition id : Type := nat.
Definition fid : Type := nat.

Require FMapAVL.
Require OrderedTypeEx.

Module Regmap := FMapAVL.Make(OrderedTypeEx.Nat_as_OT).

Module Type PARAMS.
  Parameters op val : Type.
  Parameter op_denote : op -> list val -> option val.
  Parameter bool_val : val -> option bool.
  Parameter ty : Type.
  Parameter op_ty : op -> list ty -> ty -> Prop.
  Parameter bool_ty : ty -> Prop.
End PARAMS.

Module Trans (Import P:PARAMS).

Module ANF.

  Inductive tm : Type :=
  | Ret : id -> tm
  | Pri : op -> list id -> tm -> tm
  | If0 : id -> tm -> tm -> tm
  | App : id -> list id -> tm
  | Rec : tm -> tm -> tm.

  (** Semantics with closures
    - Easy to relate to the reduction theory where let-bound continuations are
      substituted into the term
    - We can come up with all manner of fancy abstract machines where we don't
      need to allocate closures for first order ANF, including: 
      + LLCPS with reduction under let rec
      + Some sort of marker in the venv to restore E' from E (merge D and F?)
      + Remember size of E when adding bindings to F
      but it's not clear that any of these will aid in the translation from 
      lexically scoped variables to a (possibly finite) register machine.
  *)

  Notation venv := (list val).
  Inductive fenv' := Fenv : list (venv * fenv' * tm) -> fenv'.
  Notation fenv := (list (venv * fenv' * tm)).

  Inductive eval (F:fenv) (E:venv) : tm -> val -> Prop :=

  | eval_ret : forall x v,
    Nth E x v -> 
    eval F E (Ret x) v

  | eval_pri : forall u v vs op args t,
    Forall2 (Nth E) args vs ->
    op_denote op vs = Some u ->
    eval F (u::E) t v ->
    eval F E (Pri op args t) v

  | eval_if0 : forall u v b x t t',
    Nth E x u ->
    bool_val u = Some b ->
    eval F E (if b then t else t') v ->
    eval F E (If0 x t t') v

  | eval_app : forall E' F' v vs t f args,
    Nth F f (E', Fenv F',t) ->
    Forall2 (Nth E) args vs ->
    eval F' (vs ++ E') t v ->
    eval F E (App f args) v

  | eval_rec : forall v s t,
    eval ((E,Fenv F,s)::F) E t v ->
    eval F E (Rec s t) v.

End ANF.

Module RTL.
  
  Inductive tm : Type :=
  | Ret : reg -> tm
  | Pri : reg -> op -> list reg -> tm -> tm
  | Mov : reg -> reg -> tm -> tm
  | If0 : reg -> tm -> tm -> tm
  | Jmp : fid -> tm.

  Notation venv := (Regmap.t val).
  Notation fenv := (list tm).

  Definition prog : Type := (fenv * tm)%type.

  Inductive eval (R:venv) : prog -> val -> Prop :=

  | eval_ret : forall F r v,
    Regmap.find r R = Some v ->
    eval R (F, Ret r) v

  | eval_pri : forall F u v vs r d op rs t, 
    map (fun r => Regmap.find r R) rs = map (@Some _) vs ->
    op_denote op vs = Some u ->             
    eval (Regmap.add r u R) (F, t) v ->
    eval R (F, Pri d op rs t) v

  | eval_mov : forall F u v d r t,
    Regmap.find r R = Some u ->
    eval (Regmap.add d u R) (F, t) v ->
    eval R (F, Mov d r t) v

  | eval_if0 : forall F u v r b t t',
    Regmap.find r R = Some u ->
    bool_val u = Some b ->
    eval R (F, if b then t else t') v ->
    eval R (F, If0 r t t') v

  | eval_app : forall F v f t,
    Nth F f t ->
    eval R (F, t) v ->
    eval R (F, Jmp f) v.

End RTL.

Notation vtenv := (list ty).
Notation ftenv := (list (list ty)).

  Inductive wt_tm (D:ftenv) (G:vtenv) : ANF.tm -> Prop :=
  | wt_ret : forall x T,
    Nth G x T ->
    wt_tm D G (ANF.Ret x)

  | wt_pri : forall op args t T Ts,
    Forall2 (Nth G) args Ts ->
    op_ty op Ts T ->
    wt_tm D (T::G) t ->
    wt_tm D G (ANF.Pri op args t)

  | wt_if0 : forall x t t' T,
    Nth G x T ->
    bool_ty T ->
    wt_tm D G t ->
    wt_tm D G t' ->
    wt_tm D G (ANF.If0 x t t')

  | wt_app : forall f args Ts,
    Nth D f Ts ->
    Forall2 (Nth G) args Ts ->
    wt_tm D G (ANF.App f args)

  | wt_rec : forall s t Ts,
    wt_tm (Ts::D) (Ts++G) s ->
    wt_tm (Ts::D) G t ->
    wt_tm D G (ANF.Rec s t).

Notation lctenv := (list (option id * reg)).
Notation fctenv := (list (list ty * list reg * lctenv)).

Definition shift_lc (P:lctenv) : lctenv :=
  map (fun c => match c with
                  | (None, _) => c
                  | (Some x, r) => (Some (S x), r)
                end) P.

Definition shift_fc (D:fctenv) : fctenv :=
  map (fun f => let '(Ts, rs, P) := f in (Ts, rs, shift_lc P)) D.

Inductive ssplit {A:Type} (l:list A) : list A -> list A -> Prop :=
| split_nil : ssplit l nil l
| split_cons : forall m n' n'' a, 
                 ssplit l m (n' ++ a :: n'') ->
                 ssplit l (a::m) (n' ++ n'').
  
Definition Cap (P:lctenv) (x:id) (r:reg) : Prop := In (Some x, r) P.

Inductive cwt_tm (P:lctenv) (D:fctenv) (G:vtenv) : ANF.tm -> Prop :=
  | cwt_ret : forall x r T,
    Nth G x T ->
    Cap P x r ->
    cwt_tm P D G (ANF.Ret x)

  | cwt_pri : forall op xs t T Ts P' x r rs,
    Forall2 (Nth G) xs Ts ->
    op_ty op Ts T ->
    ssplit P [(x, r)] P' ->
    Forall2 (Cap P) xs rs ->
    cwt_tm ((Some 0,r)::shift_lc P') (shift_fc D) (T::G) t ->
    cwt_tm P D G (ANF.Pri op xs t)

  | cwt_if0 : forall x t t' r T,
    Nth G x T ->
    bool_ty T ->
    cwt_tm P D G t ->
    cwt_tm P D G t' ->
    Cap P x r ->
    cwt_tm P D G (ANF.If0 x t t')

  | cwt_app : forall f xs Ts rs P',
    Nth D f (Ts, rs, P') ->
    Forall2 (Nth G) xs Ts ->
    Forall2 (Cap P) xs rs ->
    incl P' P ->
    cwt_tm P D G (ANF.App f xs)

  | cwt_rec : forall s t Ts P' rs,
    cwt_tm P' ((Ts, rs, P')::D) (Ts++G) s ->
    cwt_tm P ((Ts, rs, P')::D) G t ->
    cwt_tm P D G (ANF.Rec s t)

  | cwt_phi : forall t x y r d P' T,
    Nth G x T ->
    Cap P x r ->
    ssplit P [(y, d)] P' ->
    cwt_tm ((Some x,r)::P') D G t ->
    cwt_tm P D G t.

(* sanity check: *)

Definition erase_fctenv (D:fctenv) : ftenv :=
  map (fun f => (fst (fst f))) D.

Lemma erase_shift_fctenv : forall D, erase_fctenv D = erase_fctenv (shift_fc D).
Proof.
  induction D. auto.
  destruct a as [[? ?] ?].
  simpl. f_equal; auto.
Qed.

Lemma cwt__wt : forall P D G t (Hcwt: cwt_tm P D G t), 
                  wt_tm (erase_fctenv D) G t.
Proof.
  intros. induction Hcwt.
  econstructor; eauto.
  econstructor; eauto. rewrite erase_shift_fctenv; auto.
  econstructor; eauto.
  econstructor; eauto.
    unfold erase_fctenv. unfold Nth. 
    set (fn := fun f => fst (fst f)).
    replace Ts with (fn (Ts, rs, P')).
    apply map_nth_error. auto. auto.
  econstructor; eauto.
  auto.
Qed.

Inductive transl (P:lctenv) (D:fctenv) (G:vtenv) : ANF.tm -> RTL.prog -> Prop :=
| tr_ret : forall F x r T,
  Nth G x T ->
  Cap P x r ->
  transl P D G (ANF.Ret x) (F, RTL.Ret r)

| tr_pri : forall F op xs t d rs t' T Ts P' x r,
  Forall2 (Nth G) xs Ts ->
  Forall2 (Cap P) xs rs ->
  op_ty op Ts T ->
  ssplit P [(x, r)] P' ->
  transl ((Some 0,r)::shift_lc P') (shift_fc D) (T::G) t (F, t') ->
  transl P D G (ANF.Pri op xs t) (F, RTL.Pri d op rs t')

| tr_if0 : forall F x t1 t2 r t1' t2' T,
  bool_ty T ->
  Nth G x T ->
  Cap P x r -> 
  transl P D G t1 (F, t1') ->
  transl P D G t2 (F, t2') ->
  transl P D G (ANF.If0 x t1 t2) (F, RTL.If0 r t1' t2')

| tr_app : forall F P' f f' xs rs Ts,
  Nth D f (Ts, rs, P') ->
  Forall2 (Nth G) xs Ts ->
  Forall2 (Cap P) xs rs ->
  incl P' P ->
  transl P D G (ANF.App f xs) (F, RTL.Jmp f')

| tr_rec : forall P' s s' t t' Ts rs,
  transl P' ((Ts, rs, P')::D) (Ts++G) s s' ->
  transl P ((Ts, rs, P')::D) G t t' ->
  transl P D G (ANF.Rec s t) (RTL.Rec s' t')

| tr_phi : forall t t' d r x y T P',
  Nth G x T ->
  Cap P x r ->
  ssplit P [(y, d)] P' ->
  transl ((Some x,r)::P') D G t t' ->
  transl P D G t (RTL.Mov d r t').

Definition venv_rel P (E:ANF.venv) (E':RTL.venv) : Prop :=
  forall x r v, Cap P x r -> Nth E x v -> Regmap.find r E' = Some v.

Inductive fenv_rel : fctenv -> ANF.fenv -> RTL.fenv -> Prop :=
| fenv_rel_nil : forall D, fenv_rel D [] []
| fenv_rel_cons : forall D P F F' E t t' Ts rs,
    fenv_rel D F F' ->
    (forall v vs E', 
       venv_rel P (vs++E) E' -> 
       fenv_rel D F1 F1' ->
       ANF.eval F1 (vs++E) t v -> 
       RTL.eval F1' E' t' v) ->
    fenv_rel ((Ts,rs,P)::D) ((E,t)::F) (t'::F').
    
(* Lemma fenv_rel_nth : forall F F' f E t t',  *)
(*     fenv_rel F F' -> Nth F f (E,t) -> Nth F' f t' /\ exists P, *)
(*     forall v vs E', ANF.eval F (vs++E) t v -> venv_rel P (vs++E) E' -> RTL.eval F' E' t' v. *)
(* Proof. *)
(* Admitted. *)

(* Definition fenv_rel P (F:ANF.fenv) (F':RTL.fenv) : Prop := *)
(*   forall f E t t', Nth F f (E,t) -> Nth F' f t' /\ *)
(*     forall v vs E', ANF.eval F (vs++E) t v -> venv_rel P (vs++E) E' -> RTL.eval F' E' t' v. *)

Theorem transl_eval : forall P D G t t' 
                      (Htransl: transl P D G t t') 
                      F E F' E' v 
                      (Heval: ANF.eval F E t v)
                      (Hvrel: venv_rel P E E')
                      (Hfrel: fenv_rel D F F'),
                      RTL.eval F' E' t' v.
Proof.
  induction 1; intros.

  (* ret *)
  - constructor. inversion Heval; subst. eapply Hvrel; eauto.

  (* pri *)
  - inversion Heval; subst. constructor 2 with (u:=u) (r:=r) (vs:=vs); auto.
    clear - H0 H6 Hvrel.
    generalize dependent vs.
    induction rs. admit. admit.

    eapply IHHtransl. eauto.
    (* reestablish simulation *) admit. admit.
  
  (* if0 *)
  - inversion Heval; subst. econstructor; eauto. 
    destruct b; eauto.

  (* app *)
  - inversion Heval; subst. 
      clear - Hfrel H5 H8. admit.

  (* rec *)
  - inversion Heval; subst. constructor.
      eapply IHHtransl2; eauto.
      
      econstructor. auto. intros.
      eapply IHHtransl1. eauto. eauto.


      apply fenv_rel_cons. auto.
      apply fenv_rel_cons; auto. intros.
      eapply IHHtransl1; eauto. 
        eauto. 
      
      (* show fenv_rel -- essentaily IHHtransl1 *)
      admit.

  (* phi *)
  - admit.

Abort.