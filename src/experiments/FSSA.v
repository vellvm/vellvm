Require Import List.

Import ListNotations.

Notation nth := (nth_error).

Parameters vtyc ctyc : Set.             (* type constructors *)

Inductive vty : Set := 
| P : vtyc -> list vty -> vty           (* primitive type, e.g. Int, V x V *)
| U : list vty -> vty -> vty.           (* functions *)

Inductive cty : Set :=
| Q : ctyc -> list cty -> cty           (* prim. comp type, e.g. CBPV Pi<C .. C> *)
| F : vty -> cty                        (* producer taking no args *)
| K : list vty -> cty.                  (* continuation *)

Inductive ty : Set := Vty :> vty -> ty | Cty :> cty -> ty.


Definition env : Set := list ty.
Definition glb : Set := list vty.


Parameter pri : Set.                    (* de/constructors *)

Inductive tm : Set :=

| Pri : pri -> list tm -> tm            (* primitives *)
| Var : nat -> tm                       (* local variables *)
| Glb : nat -> tm                       (* global variables (references?) *)

| Abs : nat -> tm -> tm                 (* abstraction *)
| App : list tm -> tm -> tm             (* application *)

| Seq : tm -> tm -> tm                  (* sequencing *)
| Pro : tm -> tm                        (* producer *)

| Fix : tm -> tm                        (* fixed point of computations *)

| Fun : tm -> tm                        (* function (thunk) *)
| Cal : list tm -> tm -> tm             (* function call *)

| Frm : tm -> tm                        (* call frame *)
| Ret : tm -> tm.                       (* return *)


Inductive prog : Set := Prog : list tm -> tm -> prog.


(* Fixpoint shift (m:nat) (s:tm) : tm := *)
(*   match s with *)
(*     | Pri p ts => Pri p (map (shift m) ts) *)
(*     | Var x => Var (m + x) *)
(*     | Glb x => Glb x *)
(*     | Abs n t => Abs n (shift (m + n)  *)
(*     | App x x0 => *)
(*     | Seq x x0 => *)
(*     | Pro x => *)
(*     | Fix x => *)
(*     | Fun x => *)
(*     | Cal x x0 => *)
(*     | Frm x => *)
(*     | Ret x => *)
(*   end *)
    
Parameter shift : nat -> tm -> tm.

Definition shift_ss (n:nat) (ss:list tm) : list tm :=
  map Var (seq 0 n) ++ map (shift n) ss.

Fixpoint sub (ss:list tm) (s:tm) : tm :=
  match s with
    | Pri p ts => Pri p (map (sub ss) ts)
    | Var x => nth_default s ss x
    | Glb x => Glb x
    | Abs n t => Abs n (sub (shift_ss n ss) t) 
    | App ts t => App (map (sub ss) ts) (sub ss t)
    | Seq t t' => Seq (sub ss t) (sub (shift_ss 1 ss) t')
    | Pro t => Pro (sub ss t)
    | Fix t => Fix (sub (shift_ss 1 ss) t)
    | Fun t => Fun (sub ss t)
    | Cal ts t => Cal (map (sub ss) ts) (sub ss t)
    | Frm t => Frm (sub ss t)
    | Ret t => Ret (sub ss t)
  end.
    

Parameter substitute : list tm -> tm -> tm. 





Parameter pri_wt_val : pri -> list vty -> vtyc -> list vty -> Prop.
Parameter pri_wt_cmp : pri -> list cty -> cty -> Prop.

Inductive wt_val (E:glb) (G:env) : tm -> vty -> Prop :=

| wt_pri_v : forall p vs Vs Vc Va,
  pri_wt_val p Vs Vc Va ->
  Forall2 (wt_val E G) vs Vs ->
  wt_val E G (Pri p vs) (P Vc Va)

| wt_var_v : forall x V,
  nth G x = Some (Vty V) ->
  wt_val E G (Var x) V

| wt_glb : forall x V,
  nth E x = Some V ->
  wt_val E G (Glb x) V

| wt_fun : forall c R Vs,
  wt_cmp E [] R c (K Vs) ->
  wt_val E G (Fun c) (U Vs R)

with wt_cmp (E:glb) (G:env) : vty -> tm -> cty -> Prop :=

| wt_pri_c : forall R p cs Cs C,
  pri_wt_cmp p Cs C ->
  Forall2 (wt_cmp E G R) cs Cs ->
  wt_cmp E G R (Pri p cs) C

| wt_cmp_c : forall R x C,
  nth G x = Some (Cty C) ->
  wt_cmp E G R (Var x) C

| wt_abs : forall R c Vs n,
  S n = length Vs ->
  wt_cmp E (map Vty Vs ++ G) R c (K []) ->
  wt_cmp E G R (Abs n c) (K Vs)

| wt_app : forall R c vs Vs,
  Forall2 (wt_val E G) vs Vs ->
  wt_cmp E G R c (K Vs) ->
  wt_cmp E G R (App vs c) (K [])

| wt_seq : forall R f c V Vs,
  wt_cmp E G R f (F V) ->
  wt_cmp E (Vty V::G) R c (K Vs) ->
  wt_cmp E G R (Seq f c) (K Vs)

| wt_pro : forall R v V,
  wt_val E G v V ->
  wt_cmp E G R (Pro v) (F V)

| wt_fix : forall R c C,
  wt_cmp E (Cty C::G) R c C ->
  wt_cmp E G R (Fix c) C

| wt_cal : forall R f vs S Vs,
  Forall2 (wt_val E G) vs Vs ->
  wt_val E G f (U Vs S) ->
  wt_cmp E G R (Cal vs f) (F S)

| wt_frm : forall R c S,
  wt_cmp E [] S c (K []) ->
  wt_cmp E G R (Frm c) (F S)

| wt_ret : forall R v,
  wt_val E G v R ->
  wt_cmp E G R (Ret v) (K []).


Inductive wt_tm (E:glb) (G:env) (R:vty) : tm -> ty -> Prop :=
| wt_tm_val : forall t V, 
  wt_val E G t V -> wt_tm E G R t (Vty V)
| wt_tm_cmp : forall t C,
  wt_cmp E G R t C -> wt_tm E G R t (Cty C).


Inductive wt_prog (E:glb) (R:vty) : prog -> cty -> Prop :=
| wt_prog_intro : forall C gs m,
  Forall2 (wt_val E []) gs E ->
  wt_cmp E [] R m C ->
  wt_prog E R (Prog gs m) C.



Parameter pri_step : list tm -> pri -> list tm -> tm -> Prop.


Inductive step (g:list tm) : tm -> tm -> Prop :=

| step_pri : forall p cs c, 
  pri_step g p cs c ->
  step g (Pri p cs) c

| step_app_abs : forall n vs c,
  step g (App vs (Abs n c)) (substitute vs c)

| step_app : forall vs c c',
  step g c c' ->
  step g (App vs c) (App vs c')

| step_seq_pro : forall v k,
  step g (Seq (Pro v) k) (substitute [v] k)

| step_seq : forall f f' k,
  step g f f' ->
  step g (Seq f k) (Seq f' k)

| step_fix : forall c, 
  step g (Fix c) (substitute [Fix c] c)

| step_cal_deref : forall x v vs,
  nth g x = Some v ->
  step g (Cal vs (Glb x)) (Cal vs v)

| step_cal_fun : forall vs c,
  step g (Cal vs (Fun c)) (Frm (App vs c))

| step_frm : forall c c',
  step g c c' ->
  step g (Frm c) (Frm c')

| step_frm_ret : forall v,
  step g (Frm (Ret v)) (Pro v).



Lemma forall2__nth {A B} : forall (P:A -> B -> Prop) L M m n,
  Forall2 P L M ->
  nth M n = Some m ->
  exists l, nth L n = Some l.
Proof.
Admitted.

Lemma forall2__nth__P {A B} : forall (P:A -> B -> Prop) L M l m n,
  Forall2 P L M ->
  nth M n = Some m ->
  nth L n = Some l ->
  P l m.
Proof.
Admitted.

Parameter pri_nf : pri -> list tm -> Prop.
Axiom pri_nf_restrict : forall p cs Cs C,
  pri_nf p cs ->
  pri_wt_cmp p Cs C ->
  exists a b, C = Q a b.

Axiom pri_progress : forall g p cs Cs C,
  pri_wt_cmp p Cs C ->
  pri_nf p cs \/ exists c, pri_step g p cs c.

Axiom pri_preservation : forall E G R p cs g c C,
  wt_cmp E G R (Pri p cs) C ->
  pri_step g p cs c ->
  wt_cmp E G R c C. 


Inductive nf : tm -> Prop :=
| nf_pro : forall v, nf (Pro v)
| nf_ret : forall v, nf (Ret v)
| nf_abs : forall n c, nf (Abs n c)
| nf_pri : forall p cs, pri_nf p cs -> nf (Pri p cs).

Lemma canon_pro : forall E G R c V,
  nf c ->
  wt_cmp E G R c (F V) ->
  exists v, c = (Pro v).
Proof.
Admitted.

Lemma canon_abs : forall E G R c Vs,
  nf c ->
  wt_cmp E G R c (K Vs) ->
  exists n c', c = (Abs n c').
Proof.
Admitted.

Lemma canon_ret : forall E G R c,
  nf c ->
  wt_cmp E G R c (K []) ->
  exists v, c = (Ret v).
Proof.
  intros. inversion H0; subst; try solve [inversion H].
  inversion H; subst. eapply pri_nf_restrict in H4; eauto. 
    destruct H4 as [? [? ?]]. discriminate.
  inversion H2. eexists; eauto.
Qed.


Lemma step_progress : forall E R g c C,
  wt_prog E R (Prog g c) C ->
    nf c \/ exists c', step g c c'.
Proof.
  inversion_clear 1. remember [] as G.
  induction H1; subst.

  (* wt_pri_c *)   eapply pri_progress in H. destruct H. 
                   left; constructor; eauto.
                   destruct H. right; eexists. constructor; eauto.
  (* wt_var_c *)   destruct x; inversion H.
  (* wt_abs *)     left; constructor.
  (* wt_app_abs *) right. ecase IHwt_cmp; auto; intros.
                   ecase canon_abs; eauto; intros ? [? ?]. subst c. eexists; eapply step_app_abs.
                   destruct H2. eexists. apply step_app; eauto.
  (* wt_seq *)     ecase IHwt_cmp1; intros; auto. 
                   ecase canon_pro; eauto; intros. subst f. 
                   right. eexists; constructor; auto.
                   right. inversion H. eexists; econstructor; eauto. 
  (* wt_pro *)     left; constructor.
  (* wt_fix *)     right. eexists; constructor.
  (* wt_cal *)     inversion H1; subst. destruct x; inversion H2.
                   eapply forall2__nth in H0; eauto. inversion H0.
                   right. eexists. apply step_cal_deref; eauto. 
                   right. eexists. apply step_cal_fun.
  (* wt_frm *)     ecase IHwt_cmp; intros; auto.
                   ecase canon_ret; eauto; intros. subst.
                   right. eexists. apply step_frm_ret.
                   right. inversion H. eexists. apply step_frm; eauto.
  (* wt_ret *)     left; constructor.
Qed.


(* possibly easier? *)
Lemma substitute_wt : forall E R T ts Ts Ts' t,
  Forall2 (wt_tm E [] R) ts Ts ->
  wt_tm E (Ts ++ Ts') R t T ->
  wt_tm E Ts' R (substitute ts t) T.
Proof.
Admitted.

Lemma substitute_wt_val : forall E R C vs Vs Vs' c,
 Forall2 (wt_val E []) vs Vs ->
 wt_cmp E (map Vty Vs ++ Vs') R c C ->
 wt_cmp E Vs' R (substitute vs c) C.
Proof. 
  intros.
  cut (wt_tm E Vs' R (substitute vs c) C). inversion 1; auto.
  eapply substitute_wt with (Ts:=map Vty Vs); eauto.

  clear - H. induction H. simpl; auto.
  simpl. repeat constructor; auto.
  constructor. auto.
Qed.

Lemma substitute_wt_cmp : forall E R C cs Cs Vs' c,
 Forall2 (wt_cmp E [] R) cs Cs ->
 wt_cmp E (map Cty Cs ++ Vs') R c C ->
 wt_cmp E Vs' R (substitute cs c) C.
Proof.
  intros.
  cut (wt_tm E Vs' R (substitute cs c) C). inversion 1; auto.
  eapply substitute_wt with (Ts:=map Cty Cs); eauto.

  clear - H. induction H. simpl; auto.
  simpl. repeat constructor; auto.
  constructor. auto.
Qed.

Lemma step_preservation : forall g c c' E R C,
  step g c c' ->
  wt_prog E R (Prog g c) C ->
  wt_prog E R (Prog g c') C.
Proof.
  intros. inversion_clear H0; subst. constructor. assumption.
  generalize dependent E. revert R C.
  induction H; inversion 2; intros; subst.

  (* step_pri *)       eapply pri_preservation; eauto.
  (* step_app_abs *)   inversion H6; subst. 
                       eapply substitute_wt_val; rewrite app_nil_r in *; eauto. 
  (* step_app *)       econstructor; eauto.
  (* step_seq_pro *)   eapply substitute_wt_val; eauto. apply Forall2_cons. inversion H4; subst; eauto. auto. rewrite app_nil_r; auto. 
  (* step_seq *)       eapply IHstep in H1; eauto. econstructor; eauto.
  (* step_fix *)       eapply substitute_wt_cmp; eauto.
  (* step_cal_deref *) econstructor; eauto. inversion H7; subst. 
                       eapply forall2__nth__P with (L:=g); eauto.
  (* step_cal_fun *)   inversion H6. constructor. econstructor; eauto.
  (* step_frm *)       constructor; auto. 
  (* step_frm_ret *)   inversion H3; constructor; auto. 
Qed.
