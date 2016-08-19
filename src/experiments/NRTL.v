Require Import List.
Require Vector.

Import ListNotations.

Definition Nth {A:Type} (l:list A) (n:nat) (a:A) : Prop := nth_error l n = Some a.

Fixpoint replace {A:Type} (l:list A) (n:nat) (a:A) : list A :=
  match n, l with
    | O, _::l' => a::l'
    | S n', a'::l' => a'::replace l' n' a
    | _, [] => []
  end.

Definition reg : Type := nat.
Definition id : Type := nat.
Definition lbl : Type := nat.

Module Type PARAMS.
  Parameters op bas : Type.
  Parameter op_denote : op -> list bas -> option bas.
  Parameter bool_val : bas -> option bool.
  Parameter ty : Type.
  Parameter bas_ty : bas -> ty -> Prop.
  Parameter op_ty : op -> list ty -> ty -> Prop.
  Parameter bool_ty : ty -> Prop.
End PARAMS.

Module Langs (Import P:PARAMS).

Module RTL.

  Inductive tm : Type :=
  | Ret : reg -> tm
  | Pri : op -> list reg -> reg -> tm -> tm
  | If0 : reg -> tm -> tm -> tm
  | Jmp : lbl -> tm
  | Lbl : tm -> tm -> tm.

  Definition regty : Type := list (option ty).
  Inductive lblty : Type := Arr : regty -> ty -> lblty.

  Inductive lt_ty : option ty -> option ty -> Prop :=
  | lt_ty_eq : forall t, lt_ty (Some t) (Some t)
  | lt_ty_none : forall t, lt_ty (Some t) None.

  Definition lt_reg (H H':regty) : Prop := Forall2 lt_ty H H'.

  Section N_REGS.
  Variable n_regs : nat.

  Definition wf_regty (H:regty) : Prop :=
    length H = n_regs.

  Inductive wt_tm (D:list lblty) (H:regty) (t:ty) : tm -> Prop :=
  | wt_ret : forall r,
               wf_regty H ->
               Nth H r (Some t) ->
               wt_tm D H t (Ret r)
  | wt_pri : forall d rs op ts dt M,
               wf_regty H ->
               op_ty op ts dt ->
               Forall2 (Nth H) rs (map (@Some ty) ts) ->
               wt_tm D (replace H d (Some dt)) t M ->
               wt_tm D H t (Pri op rs d M)
  | wt_if0 : forall r M N rt,
               wf_regty H ->
               Nth H r (Some rt) ->
               bool_ty rt ->
               wt_tm D H t M ->
               wt_tm D H t N ->
               wt_tm D H t (If0 r M N)
  | wt_jmp : forall l H',
               wf_regty H ->
               Nth D l (Arr H' t) ->
               lt_reg H H' ->
               wt_tm D H t (Jmp l)
  | wt_lbl : forall t' M N H',
               wf_regty H ->
               wf_regty H' ->
               wt_tm (Arr H' t'::D) H' t' M ->
               wt_tm (Arr H' t'::D) H t N ->
               wt_tm D H t (Lbl M N)
  .


  (* register states *)

  Definition regst : Type := list bas.

  Inductive wt_bas (v:bas) : option ty -> Prop :=
  | wt_top : wt_bas v None
  | wt_ty : forall t, bas_ty v t -> wt_bas v (Some t).

  Definition wt_regst (R:regst) (H:regty) : Prop := Forall2 wt_bas R H.


  (* configurations *)

  Definition cfg : Type := (tm * regst) % type.

  Inductive wt_cfg (D:list lblty) (t:ty) : cfg -> Prop :=
    wt_cfg_intro : forall M R H,
                     wt_tm D H t M ->
                     wt_regst R H ->
                     wt_cfg D t (M, R).

  (* smallstep sos *)

  Inductive step : cfg -> cfg -> Prop :=
  | step_pri : forall op rs d M R vs v,
      Forall2 (Nth R) rs vs ->
      op_denote op vs = Some v ->
      step (Pri op rs d M, R) (M, replace R d v)
  | step_if0 : forall r v b M N R,
      Nth R r v ->
      bool_val v = Some b ->
      step (If0 r M N, R) (if b then M else N, R)
  | step_lbl : forall M N R N' R',
      step (N, R) (N', R') ->
      step (Lbl M N, R) (Lbl M N', R')
  | step_lbl_ret : forall r M R,
      step (Lbl M (Ret r), R) (Ret r, R)
  | step_lbl_S : forall l M R,
      step (Lbl M (Jmp (S l)), R) (Jmp l, R)
  | step_lbl_O : forall M R,
      step (Lbl M (Jmp O), R) (Lbl M M, R).
  
  Inductive rtc {A:Type} (R:A -> A -> Prop) : A -> A -> Prop :=
  | rtc_refl : forall a, rtc R a a
  | rtc_step : forall a b c, R a b -> rtc R b c -> rtc R a c.

  (* normal forms *)

  Inductive nf : cfg -> Prop :=
  | nf_ret : forall r R, nf (Ret r, R)
  | nf_jmp : forall l R, nf (Jmp l, R).
  

  (* operational equivalence *)

  (* Note: to generalize to more interesting relational properties,
     we would define some refinement of regty, for example by annotating
     registers with the source register they are related to.
     Reg_equiv would then require that the 'injection' holds.
     - This isn't quite the analog of memory injections, since the mapping
       can change at different program points. Strictly more general?
     - We can swap subterms that reestablish the same relation, but use a 
       different mapping between registers (or none at all!) internally.
     - If that's true, this is really -much- better than compcert's approach
     - Need to figure out how this scales up to a language with functions
   *)

  Definition reg_equiv (R S:regst) (H:regty) : Prop :=
    wt_regst R H /\
    wt_regst S H /\
    forall r t, Nth H r (Some t) ->
              (exists v, bas_ty v t /\ Nth R r v /\ Nth S r v).

  (* RTL terms are equivalent when they evaluate to related normal forms
     - The extension to a language with I/O is unsurprising: replace step to
       nf with bisimulation
   *)

  Inductive nf_equiv (D:list lblty) (t:ty) : cfg -> cfg -> Prop :=
  | nf_equiv_ret : forall v r s R S,
      Nth R r v ->
      Nth S s v ->
      bas_ty v t ->
      nf_equiv D t (Ret r, R) (Ret s, S)
  | nf_equiv_jmp : forall l H R S,
      reg_equiv R S H ->
      Nth D l (Arr H t) ->
      nf_equiv D t (Jmp l, R) (Jmp l, S).

  Definition cfg_equiv (D:list lblty) (t:ty) (c c': cfg) : Prop :=
    wt_cfg D t c /\
    wt_cfg D t c' /\
    (forall d, nf d -> rtc step c d -> 
               exists d', rtc step c' d' /\ nf_equiv D t d d') /\
    (forall d', nf d' -> rtc step c' d' -> 
               exists d, rtc step c d /\ nf_equiv D t d' d).

  Definition tm_equiv (D:list lblty) (H:regty) (t:ty) (M N: tm) : Prop :=
    wt_tm D H t M /\
    wt_tm D H t N /\
    forall R S, reg_equiv R S H ->
                cfg_equiv D t (M, R) (N, S).
    

  Lemma cfg_equiv_step : forall D t c1 c1' c2 c2',
    cfg_equiv D t c1' c2' ->
    step c1 c1' ->
    step c2 c2' ->
    cfg_equiv D t c1 c2.
  Proof.
  Admitted.

  Section WT_REL.

    Hint Constructors wt_tm rtc wt_cfg nf_equiv.

    (* tm_equiv is an equivalence *)

    Lemma tm_equiv_refl : forall D H t M,
      wt_tm D H t M ->
      tm_equiv D H t M M.
    Proof.
      intros. unfold tm_equiv, cfg_equiv.
      intuition eauto. 
      inversion H1; intuition eauto.
      inversion H1; intuition eauto.
      admit.                    (* step preserves reg_equiv *)
      admit.
    Admitted.

    Lemma tm_equiv_trans : forall D H t M N O,
      wt_tm D H t M ->
      wt_tm D H t N ->
      wt_tm D H t O ->
      tm_equiv D H t M N ->
      tm_equiv D H t N O ->
      tm_equiv D H t M O.
    Proof.
    Admitted.

    Lemma tm_equiv_symm : forall D H t M N,
      wt_tm D H t M ->
      wt_tm D H t N ->
      tm_equiv D H t M N ->
      tm_equiv D H t N M.
    Proof.
    Admitted.

    (* tm_equiv is a congruence for wtt *)

    Proposition wt_ret_rel : forall D H t r,
      wf_regty H ->
      Nth H r (Some t) -> 
      tm_equiv D H t (Ret r) (Ret r).
    Proof.
      intros. unfold tm_equiv, cfg_equiv.
      split; auto. split; auto.
      intros. destruct H2 as [? [? ?]]; intuition eauto.
      - inversion H6; subst.
        + eexists. intuition eauto. 
          apply H4 in H1 as [? [? [? ?]]]. econstructor; eauto. 
        + inversion H7.
      - inversion H6; subst.
        + eexists. intuition eauto.
          apply H4 in H1 as [? [? [? ?]]].
          econstructor; eauto.
        + inversion H7.
    Qed.
        
    Proposition wt_pri_rel : forall D H t d rs op ts dt M N,
      wf_regty H ->
      op_ty op ts dt ->
      Forall2 (Nth H) rs (map (@Some ty) ts) ->
      tm_equiv D (replace H d (Some dt)) t M N ->
      tm_equiv D H t (Pri op rs d M) (Pri op rs d N).
    Proof.
      intros. unfold tm_equiv.
      destruct H3 as [? [? ?]].
      intuition eauto. 
      inversion H6; unfold cfg_equiv; intuition eauto. 

      inversion H11; subst. inversion H8. inversion H12; subst.
      eapply cfg_equiv_step with (c1:=(Pri op0 rs d M, R)); auto.
      apply H5 with (S:=replace S d v) (R:=replace R d v); eauto. 
        admit. eauto. 
        eapply step_pri; eauto. admit.

      inversion H11; subst. inversion H8. inversion H12; subst.
      eapply cfg_equiv_step with (c2:=(Pri op0 rs d N, S)); auto.
      apply H5 with (S:=replace S d v) (R:=replace R d v); eauto. 
        admit. 
        eapply step_pri; eauto. admit.
        eauto.
    Admitted.
        
    Proposition wt_if0_rel : forall D H t r rt M M' N N',
      wf_regty H ->
      Nth H r (Some rt) ->
      bool_ty rt ->
      tm_equiv D H t M M' ->
      tm_equiv D H t N N' ->
      tm_equiv D H t (If0 r M N) (If0 r M' N').
    Proof.
    Admitted.

    Proposition wt_jmp_rel : forall D H H' t l,
      wf_regty H ->
      Nth D l (Arr H' t) ->
      lt_reg H H' ->
      tm_equiv D H t (Jmp l) (Jmp l).
    Proof.
    Admitted.

    Proposition wt_lbl_rel : forall D H H' t t' M M' N N',
      wf_regty H ->
      wf_regty H'->
      tm_equiv (Arr H' t' :: D) H' t' M M' ->
      tm_equiv (Arr H' t' :: D) H t N N' -> 
      tm_equiv D H t (Lbl M N) (Lbl M' N').
    Proof.
    Admitted.
    
    (* an example optimization *)
    Proposition dead_reg_rel : forall D H t d rs dt ts op M N,
      wf_regty H ->
      op_ty op ts dt ->
      Forall2 (Nth H) rs (map (@Some ty) ts) ->
      Nth H d None ->
      tm_equiv D H t M N ->
      tm_equiv D H t (Pri op rs d M) N.
    Proof.
      intros. unfold tm_equiv in *. intuition eauto.
      econstructor; eauto.
      admit.
      admit.
    Admitted.

  End WT_REL.


  End N_REGS.

End RTL.


Module SSA.

  Inductive val : Type :=
  | Bas : bas -> val
  | Var : id -> val.

  Inductive tm : Type :=
  | Prod : val -> tm
  | Bind : op -> list val -> tm -> tm
  | Case : val -> tm -> tm -> tm
  | Call : lbl -> list val -> tm
  | Lrec : list ty -> tm -> tm -> tm.

  Inductive lblty : Type := Arr : list ty -> ty -> lblty.

  Inductive wt_val (G:list ty) (t:ty) : val -> Prop :=
  | wt_bas : forall v,
      bas_ty v t ->
      wt_val G t (Bas v)
  | wt_var : forall x,
      Nth G x t ->
      wt_val G t (Var x).

  Inductive wt_tm (D:list lblty) (G:list ty) (t:ty) : tm -> Prop :=
  | wt_prod : forall v,
      wt_val G t v ->
      wt_tm D G t (Prod v)
  | wt_bind : forall op vs M ts t',
      op_ty op ts t' ->
      Forall2 (wt_val G) ts vs ->
      wt_tm D (t'::G) t M ->
      wt_tm D G t (Bind op vs M)
  | wt_case : forall v M N vt,
      wt_val G vt v ->
      bool_ty vt ->
      wt_tm D G t M ->
      wt_tm D G t N ->
      wt_tm D G t (Case v M N)
  | wt_call : forall l vs ts,
      Forall2 (wt_val G) ts vs ->
      Nth D l (Arr ts t) ->
      wt_tm D G t (Call l vs)
  | wt_lrec : forall ts t' M N,
      wt_tm (Arr ts t'::D) (ts++G) t' M ->
      wt_tm (Arr ts t'::D) G t N ->
      wt_tm D G t (Lrec ts M N).

  (* smallstep sos *)

  Definition vsubst (n:nat) (bs:list bas) (v:val) : val :=
    match v with
      | Bas _ => v
      | Var x => (nth (n + x) (map Bas bs) v)
    end.

  Fixpoint psubst (n:nat) (bs:list bas) (M:tm) : tm :=
    match M with
      | Prod v => Prod (vsubst n bs v)
      | Bind o vs N => Bind o (map (vsubst n bs) vs) (psubst (S n) bs N)
      | Case v M N => Case (vsubst n bs v) (psubst n bs M) (psubst n bs N)
      | Call l vs => Call l (map (vsubst n bs) vs)
      | Lrec ts M N => Lrec ts (psubst (n + length ts) bs M) (psubst n bs N)
    end.

  Inductive step : tm -> tm -> Prop :=
  | step_bind : forall op vs M bs v ,
      map Bas bs = vs ->
      op_denote op bs = Some v ->
      step (Bind op vs M) (psubst 0 [v] M)
  | step_case : forall b x M N,
      bool_val b = Some x ->
      step (Case (Bas b) M N) (if x then M else N)
  | step_lrec : forall ts M N N',
      step N N' ->
      step (Lrec ts M N) (Lrec ts M N')
  | step_call_prod : forall ts v M,
      step (Lrec ts M (Prod v)) (Prod v)
  | step_call_S : forall ts l vs M,
      step (Lrec ts M (Call (S l) vs)) (Call l vs)
  | step_call_O : forall ts bs vs M,
      map Bas bs = vs ->
      step (Lrec ts M (Call O vs)) (Lrec ts M (psubst 0 bs M)).

End SSA.

(* 1. not entirely sure about the relationship between base ts, refinement, 
      unary, and relational systems
   2. easier to state all rules as a single relation, then prove?
   3. regst equality baked into cfg_equiv, but this should be able to change
      based on our choice of refinement
      + similar problem with value refinement?
      + these are just the primitives of the language, need to parameterize
        definition of op equiv for different systems
      + doest it make sense to define regst equiv extensionally?

 *)