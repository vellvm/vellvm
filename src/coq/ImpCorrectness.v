(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import Vellvm.Maps Vellvm.Imp.

Require Import ZArith String Omega List Equalities MSets RelationClasses.
Import ListNotations.

(* Vellvm dependencies *)
Require Import Vellvm.Ollvm_ast Vellvm.CFGProp Vellvm.Compiler Vellvm.AstLib Vellvm.CFG Vellvm.StepSemantics Vellvm.Memory.
Require Import Vellvm.Classes.


(* Logical Foundations dependencies *)
Require Import Vellvm.Imp Vellvm.Maps Vellvm.ImpCEvalFun.
Import ListNotations.
Open Scope list_scope.
Require Import Program.



(* Move to Compiler.v *)
Ltac unfold_llvm H :=
  progress (simpl in H; unfold llvm_bind in H; unfold llvm_ret in H; unfold lift in H).

Arguments Z.add _ _ : simpl nomatch.

(* relational specification of aeval ---------------------------------------- *)

Inductive aevalR : Imp.state -> aexp -> int64 -> Prop :=
  | E_ANum  : forall s (ans: int64),
      aevalR s (ANum ans) ans
  | E_AId : forall s id,
      aevalR s (AId id) (s id)
  | E_APlus : forall s (a1 a2: aexp) (ans1 ans2: int64),
      aevalR s a1 ans1 ->
      aevalR s a2 ans2 ->
      aevalR s (APlus a1 a2) (Int64.add ans1 ans2)
  | E_AMinus: forall s (a1 a2: aexp) (ans1 ans2: int64),
      aevalR s a1 ans1 ->
      aevalR s a2 ans2 ->
      aevalR s (AMinus a1 a2) (Int64.sub ans1 ans2)
  | E_AMult : forall s (a1 a2: aexp) (ans1 ans2: int64),
      aevalR s a1 ans1 ->
      aevalR s a2 ans2 ->
      aevalR s (AMult a1 a2) (Int64.mul ans1 ans2).
Hint Constructors aevalR.

Lemma aeval_iff_aevalR : forall s a ans, aeval s a = ans <-> aevalR s a ans.
Proof.
  intros s a ans.
  split.
  - revert ans.
    induction a; intros an H; simpl in H; subst; auto.
  - intros H.
    induction H; subst; simpl; auto.
Qed.

Inductive bevalR : Imp.state -> bexp -> bool -> Prop :=
  | E_BTrue : forall s,
      bevalR s BTrue true
  | E_BFalse : forall s,
      bevalR s BFalse false
  | E_BEq : forall s a1 a2 ans1 ans2,
      aevalR s a1 ans1 ->
      aevalR s a2 ans2 ->
      bevalR s (BEq a1 a2) (Int64.eq ans1 ans2)
  | E_BLe : forall s a1 a2 ans1 ans2,
      aevalR s a1 ans1 ->
      aevalR s a2 ans2 ->
      bevalR s (BLe a1 a2) (Int64.cmp Integers.Cle ans1 ans2)
  | E_BNot : forall s b1 ans,
      bevalR s b1 ans ->
      bevalR s (BNot b1) (negb ans)
  | E_BAnd : forall s b1 b2 ans1 ans2,
      bevalR s b1 ans1 ->
      bevalR s b2 ans2 ->
      bevalR s (BAnd b1 b2) (ans1 && ans2).
Hint Constructors bevalR.

Lemma beval_iff_bevalR : forall s b ans, beval s b = ans <-> bevalR s b ans.
Proof.
  split; generalize dependent ans.
  - induction b; intros; rewrite <- H; simpl; try constructor; try rewrite <- aeval_iff_aevalR;
      auto; reflexivity.
  - induction b; intros; inversion H; subst; try rewrite <- aeval_iff_aevalR in *;
      subst; try reflexivity; simpl; try apply IHb in H2; try rewrite H2; auto.
    apply IHb1 in H3. apply IHb2 in H5. rewrite H3. rewrite H5. reflexivity.
Qed.  


Ltac compile_aexp_monotonic_case X :=
  match goal with [
  IHa1 : forall (n m : int) (code : list elt) (v : Ollvm_ast.value) (n' m' : int) (code' : list elt),
         compile_aexp ?g ?a1 (n, m, code) = (n', m', code', inr v) ->
         n <= n' /\ m <= m' /\ (exists code'' : list elt, code' = code'' ++ code),
  IHa2 : forall (n m : int) (code : list elt) (v : Ollvm_ast.value) (n' m' : int) (code' : list elt),
         compile_aexp ?g ?a2 (n, m, code) = (n', m', code', inr v) ->
         n <= n' /\ m <= m' /\ (exists code'' : list elt, code' = code'' ++ code),
  Hcomp : compile_aexp ?g (_ ?a1 ?a2) (?n1, ?m1, ?code1) = (?n2, ?m2, ?code2, ?inr ?v)
  |- _ ] =>
    unfold_llvm Hcomp;
    specialize IHa1 with (n:=n1)(m:=m1)(code:=code1);
    destruct (compile_aexp g a1 (n1, m1, code1)) as [[[n1' m1'] code1']  [err1|v1']];
    try solve [inversion Hcomp];
    specialize IHa1 with (v:=v1')(n':=n1')(m':=m1')(code':=code1');
    destruct IHa1 as [Hnlt [HMlt [code1'' Heq]]]; auto;
    specialize IHa2 with (n:=n1')(m:=m1')(code:=code1');

    destruct (compile_aexp g a2 (n1', m1', code1')) as [[[n2' m2'] code2']  [err2|v2']];
    try solve [inversion Hcomp];

    specialize IHa2 with (v:=v2')(n':=n2')(m':=m2')(code':=code2');
    destruct IHa2 as [Hnlt1 [HMlt2 [code2'' Heq2]]]; auto;
    simpl in Hcomp;
    inversion Hcomp; subst;
    repeat split; try omega; auto;
    exists (I (IId (lid_of_Z n2')) (INSTR_Op (SV (OP_IBinop (X false false) i64 v1' v2'))) :: code2'' ++ code1'');
    simpl; rewrite app_assoc; reflexivity
  end.

                  
Lemma compile_aexp_monotonic :
  forall g a
    n m code (v : Ollvm_ast.value) n' m' code'
    (Hcomp : compile_aexp g a (n,m,code) = ((n',m',code'),inr v)),
    n <= n' /\ m <= m' /\   exists code'', code' = code'' ++ code.
Proof.
  intros g a.
  induction a; intros n1 m1 code1 v n2 m2 code2 Hcomp.  simpl in Hcomp.
  - unfold_llvm Hcomp.
    inversion Hcomp; subst. repeat split; try omega. exists []. simpl. reflexivity.

  - unfold_llvm Hcomp.
    destruct (g i); simpl in Hcomp; try inversion Hcomp.
    repeat split; try omega.
    exists [I (IId (lid_of_Z n1)) (INSTR_Load false i64 (i64ptr, v0) None)]. simpl. reflexivity.

  - compile_aexp_monotonic_case Add.
  - compile_aexp_monotonic_case Sub.
  - compile_aexp_monotonic_case Mul.
Qed.    
    

Definition iid n (id:instr_id) : Prop := (IId (lid_of_Z n)) = id.
Definition add_env_Z n dv (e:env) := add_env (lid_of_Z n) dv e.


(* Related final values *)
Definition  Rv64 (v:value) (i:int64) : Prop :=
    v = DVALUE_I64 i.
Hint Unfold Rv64.

(* For IMP, bexps compute Coq bools, so we relate those *)
Definition  Rv1 (v:value) (b:bool) : Prop :=
  if b then v = (DVALUE_I1 Int1.one) else v = (DVALUE_I1 Int1.zero).
Hint Unfold Rv1.


(* Lift Rv64 to error terms *)
Inductive Rv64e : err value -> int64 -> Prop :=
| Rv64e_inr : forall v i, Rv64 v i -> Rv64e (inr v) i.
Hint Constructors Rv64e.

(* Lift Rv1 to error terms *)
Inductive Rv1e : err value -> bool -> Prop :=
| Rv1e_inr : forall v i, Rv1 v i -> Rv1e (inr v) i.
Hint Constructors Rv1e.



Definition memory_invariant (g:ctxt) (e:env) (m:memory) (st:Imp.state) : Prop :=
  forall x v, g x = Some v ->
         exists n, (v = (local (lid_of_Z n)) /\
               exists a, (lookup_env e (lid_of_Z n) = Some (DVALUE_Addr a) /\
                     Rv64 (nth_default undef m a) (st x))).

Inductive env_lt (n:int) : env -> Prop :=
| env_lt_nil : env_lt n []
| env_lt_cons : forall e m dv, m < n -> env_lt n e -> env_lt n (add_env_Z m dv e)
.
Hint Constructors env_lt.

Lemma env_lt_weaken : forall n n' e, env_lt n e -> n <= n' -> env_lt n' e.
Proof.
  intros n n' e H Hlt.
  induction H; eauto.
  apply env_lt_cons. omega. assumption.
Qed.  

Lemma env_lt_lookup_neq :
  forall n e id v
    (Henv : env_lt n e)
    (Hl : lookup_env e id = Some v),
    id <> (lid_of_Z n).
Proof.
  intros n e id v Henv.
  revert id v.
  induction Henv; intros id v Hl.
  - inversion Hl.
  - unfold lookup_env in Hl.
    unfold add_env_Z in Hl.
    simpl in Hl.
    destruct (RawID.eq_dec id (lid_of_Z m)).
    subst.
    apply lid_of_Z_inj. unfold not. intros. subst. omega.
    eapply  IHHenv. unfold lookup_env. apply Hl.
Qed.    

Lemma env_lt_lookup_inv :
  forall n n' e v
    (Henv: env_lt n e)
    (Hl: lookup_env e (lid_of_Z n') = Some v),
    n' < n.
Proof.
  intros n n' e v Henv.
  revert n' v.
  induction Henv; intros n' v Hl.
  - unfold lookup_env in Hl. simpl in Hl. inversion Hl.
  - unfold add_env_Z in Hl.
    destruct lookup_add_env_inv with (id1:=lid_of_Z m)(v:=dv)(e:=e)(id2:=lid_of_Z n')(u:=v) as [[H1 H2]|H1]. assumption.
    apply lid_of_Z_inj2 in H1. subst. assumption.
    apply IHHenv with (v:=v). exact H1.
Qed.    

Lemma memory_invariant_extension :
  forall g e n mem st dv
    (Henv: env_lt n e)
    (Hmem: memory_invariant g e mem st),
    memory_invariant g (add_env_Z n dv e) mem st.
Proof.
  intros g e n mem st dv Henv Hmem.
  unfold memory_invariant in *.
  intros x v Hg.
  apply Hmem in Hg. clear Hmem.
  destruct Hg as [n0 [Hv [a [Ha Hrv]]]].
  exists n0. split; auto.
  exists a. eapply env_lt_lookup_inv with (n':=n0) in Henv.
  split; auto. unfold add_env_Z. rewrite lookup_env_tl; auto. apply lid_of_Z_inj.
  unfold not. intros. subst. omega. exact Ha.
Qed.  


(* AstProp.v *)
Inductive straight : code -> Prop :=
| straight_nil : straight []
| straight_Op : forall id i tl
    (IHS: straight tl)
    (Hi: is_Op i),
    straight ((id,i)::tl)
| straight_Eff : forall id i tl
    (IHS: straight tl)
    (Hi: is_Eff i),
    straight ((id,i)::tl)
.             
Hint Constructors straight.

(* AstProp.v *)
Lemma straight_app : forall cd1 cd2,
    straight cd1 ->
    straight cd2 ->
    straight (cd1 ++ cd2).
Proof.
  intros cd1 cd2 H H0.
  generalize dependent cd2.
  induction H; intros cd2 H0; simpl; auto; try solve [constructor; eauto].
Qed.  

(* Excludes labels and terminators *)
Inductive compiled_code : list elt -> code -> Prop :=
| cc_nil : compiled_code [] []

| cc_cons_Op : forall id i tl cd
    (IHs: compiled_code tl cd),
    compiled_code ((I id i)::tl) ((id, i)::cd)
.    
Hint Constructors compiled_code.

Lemma compiled_code_app : forall x1 cd1 x2 cd2,
    compiled_code x1 cd1 ->
    compiled_code x2 cd2 ->
    compiled_code (x1++x2) (cd1++cd2).
Proof.
  intros x1 cd1 x2 cd2 H.
  revert x2 cd2.
  induction H; intros x2 cd2 H0; simpl; auto; try solve [constructor; eauto].
Qed.  

(*
(* AstProp.v *)
Inductive pc_prefix (p:pc) (cd:code) : Prop :=
| pc_prefix_intro :
    forall cd'
      (H: fetch p = cd ++ cd'),
      pc_prefix p cd.

(* AstProp.v *)
Lemma pc_prefix_app :
  forall p cd1 cd2
    (HP: pc_prefix p (cd1 ++ cd2)),
    pc_prefix p cd1.
Proof.
  intros p cd1.
  destruct cd1; intros cd2 HP. 
  - inversion HP. simpl in H.
    eapply pc_prefix_intro. simpl. apply H.
  - simpl in HP.
    inversion HP.
    simpl in H.
    eapply pc_prefix_intro. simpl. rewrite <- app_assoc in H.
    apply H.
Qed.  
 *)

(*
  Holds if the machine runs in zero or more steps to a configuration that satisfies R
 *)
Inductive step_star (CFG:mcfg) (R : SS.state -> memory -> Prop) : SS.state -> memory -> Prop :=
| step_zero :
    forall s m
      (HR : R s m),
      step_star CFG R s m
    
| step_tau :
    forall s m s'
      (HS: stepD CFG s = Step s')
      (IH: step_star CFG R s' m),
      step_star CFG R s m

| step_eff :
    forall s m e m' v k
      (HS : stepD CFG s = Obs (Eff e))
      (HM : mem_step e m = inr (m', v, k))
      (Hstep : step_star CFG R (k v) m'),
      step_star CFG R s m

| step_jump :
    forall s m s'
      (HS : stepD CFG s = Jump s')
      (IH : step_star CFG R s' m),
      step_star CFG R s m
.

Lemma step_star_app :
  forall (CFG:mcfg) R1 s1 m1
    (HS1: step_star CFG R1 s1 m1)
    R2
    (HS2: forall s2 m2, R1 s2 m2 -> step_star CFG R2 s2 m2),
    step_star CFG R2 s1 m1.
Proof.
  intros CFG R1 s1 m1 HS1.
  induction HS1; intros R2 HS2; eauto.
  - eapply step_tau; eauto.
  - eapply step_eff; eauto.
  - eapply step_jump; eauto.
Qed.    
    
(*
(* AstProp.v *)
Definition pc_app (p:pc) (c:code) :=
  let b := bk p in
  mk_pc (fn p) (mk_block (blk_id b) (blk_phis b) ((blk_code b) ++ c) (blk_term b)).

(* AstProp.v *)
Lemma pc_app_nil :
  forall (p:pc) (c:code)
    (Hnil : fetch p = []),
    fetch (pc_app p c) = c.
Proof.
  intros.
  destruct p.
  destruct bk0. unfold fetch in *. simpl in *.
  subst. reflexivity.
Qed.    


Lemma pc_app_slc :
    forall fn bid phis term,
      let slc := slc_pc fn bid phis term in
      forall cd1 cd2,
        pc_app (slc cd1) cd2 = slc (cd1 ++ cd2).
Proof.
  intros fn bid phis term slc cd1 cd2. reflexivity.
Qed.

Lemma fetch_slc :
  forall fn bid phis term,
    let slc := slc_pc fn bid phis term in
    forall cd,
      fetch (slc cd) = cd.
Proof.
  intros fn0 bid phis term slc cd.
  reflexivity.
Qed.

Lemma pc_prefix_id :
    forall fn bid phis term,
      let slc := slc_pc fn bid phis term in
      forall cd,
        pc_prefix (slc cd) cd.
Proof.
  intros fn bid phis term slc cd.
  apply pc_prefix_intro with (cd' := []).
  rewrite app_nil_r. reflexivity.
Qed.  
*)  

(*
Lemma step_code_app :
  forall CFG fn bid phis term,
    let slc := slc_pc fn bid phis term in
    forall R1 cd1 e1 k1 mem1 
      (HS1 : step_code CFG R1 cd1 (slc cd1, e1, k1) mem1)
      R2 cd2  
      (HR1 : forall st mem, R1 st mem ->
             (fetch (pc_of st)) = [] /\ step_code CFG R2 cd2 (pc_app (pc_of st) cd2, env_of st, stack_of st) mem),
      step_code CFG R2 (cd1++cd2) (slc (cd1++cd2), e1, k1) mem1.
Proof.
  intros CFG fn bid phis term slc R1 cd1 e1 k1 mem1 HS1.
  remember (slc cd1, e1, k1) as s1.
  generalize dependent e1. revert k1.
  induction HS1; intros k1 e1 Heqs1 R2 cd2 HR1. 
  -  simpl.
     destruct (HR1 s m) as [Hf HR2]; auto.
     destruct s as [[pc2 e2] k2].
     simpl in *.
     inversion Heqs1. subst.
     unfold slc in HR2. rewrite pc_app_slc in HR2. auto.

  - simpl.
    destruct s' as [[pc2 e2] k2]. subst.
    assert (pc2 = slc cd) as Hpc2. eapply stepD_Op_inversion; eauto.
    rewrite Hpc2 in HS.
    apply step_tau with (s' := (slc (cd++cd2), e2, k2)); auto. 
    + apply pc_prefix_id.
    + replace (slc ((id, i) :: cd ++ cd2)) with (pc_app (slc ((id,i)::cd)) cd2).
      replace (slc (cd ++ cd2)) with (pc_app (slc cd) cd2) by reflexivity.
      eapply stepD_Op_weakening; auto.
      reflexivity.
    + eapply IHHS1; auto. rewrite Hpc2. reflexivity.

  - simpl.
    inversion Hi.
    + assert (exists lid, id = IId lid /\ e = Alloca t (fun (a:value) => (slc cd, add_env lid a e1, k1))).
      eapply stepD_Eff_Alloca_inversion. subst. apply HS.
      destruct H0 as [lid [Hid Heq]].

      apply step_eff with (e := (fmap (fun st => (pc_app (pc_of st) cd2, env_of st, stack_of st)) e))(m':=m')(v:=v)
            (k:=fun a0 : value => (pc_app (slc cd) cd2, add_env lid a0 e1, k1)); auto.
      * apply pc_prefix_id.
      * replace (slc ((id, i) :: cd ++ cd2)) with (pc_app (slc ((id,i)::cd)) cd2).
        eapply stepD_Eff_weakening; auto.
        subst.
        apply HS.
        reflexivity.
      * subst. simpl. 
        simpl in HM. inversion HM. reflexivity.
      * eapply IHHS1; auto. rewrite Heq in HM. inversion HM. subst. reflexivity.

    + assert (exists lid a, id = IId lid /\ e = Load a (fun (dv:dvalue) => (slc cd, add_env lid dv e1, k1))).
      eapply stepD_Eff_Load_inversion. subst. apply HS.
      destruct H0 as [lid [addr [Hid Heq]]].

      apply step_eff with (e := (fmap (fun st => (pc_app (pc_of st) cd2, env_of st, stack_of st)) e))(m':=m')(v:=v)
            (k:=fun a0 : value => (pc_app (slc cd) cd2, add_env lid a0 e1, k1)); auto.
      * apply pc_prefix_id.
      * replace (slc ((id, i) :: cd ++ cd2)) with (pc_app (slc ((id,i)::cd)) cd2).
        eapply stepD_Eff_weakening; auto.
        subst.
        apply HS.
        reflexivity.
      * subst. simpl. 
        simpl in HM. inversion HM. reflexivity.
      * eapply IHHS1; auto. rewrite Heq in HM. inversion HM. subst. reflexivity.

    + assert (exists vid a dv, id = IVoid vid /\ e = Store a dv (fun _ => (slc cd, e1, k1))).
      eapply stepD_Eff_Store_inversion. subst. apply HS.
      destruct H0 as [vid [addr [dv [Hid Heq]]]].

      apply step_eff with (e := (fmap (fun st => (pc_app (pc_of st) cd2, env_of st, stack_of st)) e))(m':=m')(v:=v)
            (k:=fun _ => (pc_app (slc cd) cd2, e1, k1)); auto.
      * apply pc_prefix_id.
      * replace (slc ((id, i) :: cd ++ cd2)) with (pc_app (slc ((id,i)::cd)) cd2).
        eapply stepD_Eff_weakening; auto.
        subst.
        apply HS.
        reflexivity.
      * subst. simpl. 
        simpl in HM. inversion HM. reflexivity.
      * eapply IHHS1; auto. rewrite Heq in HM. inversion HM. subst. reflexivity.
Qed.
*)        
  
Definition env_extends (e e':env) : Prop :=
  forall op t dv, eval_op e t op = inr dv -> eval_op e' t op  = inr dv.

Lemma env_extends_trans :
  forall (e1 e2 e3:env)
    (He12 : env_extends e1 e2)
    (He23 : env_extends e2 e3),
    env_extends e1 e3.
Proof.
  intros.
  unfold env_extends in *.
  intros op dv Heq; eauto.
Qed.

Lemma env_extends_refl :
  forall e, env_extends e e.
Proof.
  intros e.  unfold env_extends; auto.
Qed.  

Lemma env_extends_lt :
  forall e n dv
    (Henv: env_lt n e),
    env_extends e (add_env_Z n dv e).
Proof.
(*  
  intros e n dv Henv o.
  induction o using value_ind'; simpl in *; try inversion Hev; intros; subst; auto.
  - destruct id; try solve [inversion H].
    unfold eval_expr in *. simpl in *.
    unfold add_env_Z. rewrite lookup_env_tl. 
    destruct (lookup_env e id); inversion H; auto.
  (* <> should be symmetric! *)
    unfold not. intros. symmetry in H0. eapply env_lt_lookup_neq in H0; eauto.
    destruct (lookup_env e id); inversion H; auto.
    
  - unfold eval_expr in *. simpl in *.   (* Need a lemma about the interaction of map_monad and H *)
    admit.
  - admit.
  - admit.
  - admit.
  - unfold eval_expr in *. simpl in *.
    destruct (eval_op e (Some t) o1); try solve [inversion H].
    destruct (eval_op e (Some t) o2); try solve [inversion H].
    erewrite IHo1; try solve [reflexivity].
    erewrite IHo2; try solve [reflexivity].
    exact H.
  - unfold eval_expr in *. simpl in *.
    destruct (eval_op e o1); try solve [inversion H].
    destruct (eval_op e o2); try solve [inversion H].
    erewrite IHo1; try solve [reflexivity].
    erewrite IHo2; try solve [reflexivity].
    assumption.
  - unfold eval_expr in *. simpl in *.
    destruct (eval_op e o1); try solve [inversion H].
    destruct (eval_op e o2); try solve [inversion H].
  - unfold eval_expr in *. simpl in *.
    destruct (eval_op e o1); try solve [inversion H].
    destruct (eval_op e o2); try solve [inversion H].
  - unfold eval_expr in *. simpl in *.
    destruct (eval_op e o); try solve [inversion H].
    erewrite  IHo; try solve [reflexivity].
    assumption.
  - unfold eval_expr in *. simpl in *.  (* Need lemma about monad_app_snd *)
    admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
    
*)    
    (* maybe cut down on cases from eval_expr to simplify for now. *)
Admitted.    

Lemma rev_nil_inv : forall {A} (l:list A), rev l = [] -> l = [].
Proof.
  destruct l; intros; auto.
  simpl in H.  apply app_eq_nil in H. destruct H. inversion H0.
Qed.  

Ltac simplify_lists :=
  repeat (match goal with
          | [H : rev ?x = [] |- _] => apply rev_nil_inv in H; inversion H; subst; clear H
          | [H : ?x ++ ?y = [] |- _ ] => apply app_eq_nil in H; let y := fresh in destruct H as [_ y]; inversion y
          | [H : [] = ?x ++ [?y] |- _ ] => symmetry in H
          | [H : [] <> [] |- _] => contradiction H
          | [H : ?x::?l = [] |- _] => inversion H
          | [H : [] = ?x::?l |- _] => inversion H
          | [H : context[rev[]] |- _] => simpl in H
          | [H : [] = [] |- _ ] => clear H
          | [H : ?x = [] |- _ ] => subst
          | [H : (_, _, _, inl _) = (_, _, _, inr _) |- _ ] => inversion H
          | [H : (_, _, _, inr _) = (_, _, _, inl _) |- _ ] => inversion H                                                                      
          end).


Ltac simplify_step :=
  repeat (simpl; match goal with
          | [H : context[i64] |- _] => unfold i64 in H
          | [  |- context[i64] ] => unfold i64
          | [H : Rv64e ?E _ |- context[match ?E with _ => _ end ]] => inversion_clear H 
          | [H : Rv64 _ _ |- _ ] => inversion_clear H
          | [H : ?E = ?V |- context[do _ <- trywith _ ?E; _]] => rewrite H
          | [H : ?E = ?V |- context[match ?E with _ => _ end]] => rewrite H
          | [H : _ |- context[do _ <- eval_expr _ _ _ _; _]] => unfold eval_expr

          | [ HEXT : env_extends ?E ?E2,
              H : Rv64e (eval_op ?E ?T ?V) _ |-
              context[match eval_op ?E2 ?T ?V with _ => _ end]] => 
            let V := fresh "v" in
            let RV := fresh "rv" in
            let EVAL := fresh "Heval" in
            let EQ := fresh "eq" in
            inversion H as [V I RV EVAL EQ];
            unfold env_extends in HEXT; symmetry in EVAL;
            apply HEXT in EVAL; rewrite EVAL

       end); simpl.

Ltac instantiate_H :=
  repeat (match goal with
  | [ H1 : forall g n m cd n' m' cd' v, compile_aexp g ?A (n, m, cd) = _ -> _ , 
      H2 : context[match compile_aexp ?G ?A (?N, ?M, ?CD) with _ => _ end] |- _
    ] =>
    let FX := fresh "F" in
    let FEQ := fresh "FEQ" in
    let nX := fresh "n" in
    let mX := fresh "m" in
    let cdX := fresh "cd" in
    let errX := fresh "err" in
    let vX := fresh "v" in
    remember (compile_aexp G A (N, M, CD)) as FX eqn:FEQ;
    destruct FX as [[[nX mX] cdX] [errX|vX]]; simplify_lists;
    specialize H1 with (g:=G)(n:=N)(m:=M)(cd:=CD)(n':=nX)(m':=mX)(cd':=cdX)(v:=vX);
    symmetry in FEQ;
    lapply H1; clear H1; [intros H1;
                          apply compile_aexp_monotonic in FEQ;
                          let ltnX := fresh "ltn" in
                          let ltmX := fresh "ltm" in
                          let cdX2 := fresh "cd" in
                          let eqcdX := fresh "eqcd" in
                          destruct FEQ as [ltnX [ltmX [cdX2 eqcdX]]]


                         | auto]
  | [ H : exists cd_a, exists c_a, ?C0 = cd_a ++ ?CD /\ _ |- _ ] => 
    let cd_aX := fresh "cd_a" in
    let c_aX := fresh "c_a" in
    let cd_eqX := fresh "cd_eq" in
    let ccX := fresh "cc" in
    destruct H as [cd_aX [c_aX [cd_eqX [ccX H]]]]

  | [ H : context[match binop _ _ _ _ (_, _, _) with _ => _ end] |- _ ] => simpl in H; inversion_clear H; subst

  | [ H : ?X ++ ?TL = ?Y ++ ?TL |- _ ] => apply app_inv_tail in H; subst

  | [ H0 : compiled_code ?CD0 ?CDA0 ,
      H1 : compiled_code ?CD1 ?CDA1 
     |- exists cd_a, exists c_a,
        (I (IId (?X)) (?INS)) :: ?CD0 ++ ?CD1 ++ ?CD = cd_a ++ ?CD /\ _
    ] =>
    exists ((I (IId (X)) (INS)) :: CD0 ++ CD1);
    exists ((IId (X), INS) :: CDA0 ++ CDA1)

  | [ |- _ /\ _ ] => split; instantiate_H
                    
  | [ |- ?X :: ?A ++ ?B ++ ?C = (?X :: ?A ++ ?B) ++ ?C ] => simpl; rewrite app_assoc; reflexivity

  | [ |- compiled_code ((I ?X ?INS)::_) ((?X, ?INS)::_) ] => econstructor

  | [ H1 : compiled_code ?C1 ?CA1,
      H2 : compiled_code ?C2 ?CA2
      |- compiled_code (?C1 ++ ?C2) (?CA1 ++ ?CA2) ] => apply compiled_code_app; assumption
                                                                                      
 end).

Ltac exploit_CFG_code :=
  repeat (match goal with
          | [ H : CFG_has_code_at _ _ _ (?L1 ++ ?L2) |- _ ] =>
            apply CFG_has_code_app_inv in H;
            let HC := fresh "Hc" in
            let PC := fresh "pc" in
            let HL := fresh "HL" in
            let HR := fresh "HR" in
            destruct H as [PC [HL HR]]; simplify_lists

          | [H : CFG_has_code_at _ _ _ [] |- _] => inversion_clear H

          | [H : CFG_has_code_at _ _ _ (?X::_) |- _] => inversion_clear H
          end).

Ltac normalize_lists :=
  repeat progress (match goal with
                   | [ H : context[(?A ++ ?B) ++ ?C] |- _ ] => rewrite <- app_assoc in H; simpl in H
                   | [ |- context[(?A ++ ?B) ++ ?C] ] => rewrite <- app_assoc; simpl
                   | [ H : context[rev (?A ++ ?B)] |- _ ] => rewrite rev_app_distr in H; simpl in H
                   | [ |- context[rev (?A ++ ?B)] ] => rewrite rev_app_distr; simpl
                   | [ H : context[rev (?X :: ?L)] |- _ ] => simpl in H 
                   | [ |- context[rev (?X :: ?L) ] ] => simpl
                   end).

Ltac exploit_IH :=
  match goal with
  | [ HMEM : memory,
      H : forall (e : env) (mem : memory),
          env_lt _ e ->
          memory_invariant _ e mem _ ->
          ([] = [] /\ Rv64e (eval_op e (Some (TYPE_I 64)) ?V) _) \/ _ 
      |- context[match eval_op ?E _ ?V with _ => _ end] ] => specialize H with (e:=?E)(mem:=HMEM)
  end.

Ltac weakening :=
  repeat (match goal with
          | [ H : ?E |- ?E ] => assumption
          | [ H : env_lt ?N ?E |- env_lt ?M ?E ] => eapply env_lt_weaken; [exact H | omega]
          | [ |- env_lt _ (add_env _ _ _) ] => apply env_lt_cons; [omega | weakening]
          | [ |- env_extends ?E ?E ] => eapply env_extends_refl
          | [ |- env_extends ?E1 (add_env _ _ ?E1) ] => apply env_extends_lt; weakening
          | [ H : env_extends ?E1 ?E2 |- env_extends ?E1 ?E3 ] => apply (env_extends_trans E1 E2 E3); weakening
          | [ H : memory_invariant ?G ?E ?MEM ?S  |- memory_invariant ?G (add_env _ _ ?E) ?MEM ?S ] =>
            eapply memory_invariant_extension        
          end). 

Ltac specialize_IH H e' mem' :=
        specialize H with (e:=e') (mem:=mem');
          let K := fresh "K" in
          let Hl := fresh "Hl" in
          let Heval := fresh "Heval" in
          pose (K:=H ltac:(weakening) ltac:(assumption)); clearbody K; clear H;
          destruct K as [[Hl Heval] | [Hl K]]; simplify_lists; exploit_CFG_code; subst; auto.

Ltac solve_step_star :=
  match goal with
  | [ H : fetch ?CFG ?P = Some (CFG.Step (INSTR_Op _)) |-  step_star ?CFG _ (?P, _, _) _ ] =>
      eapply step_tau
  end.

Lemma compile_aexp_correct :
  forall 
    (a:aexp) (st:Imp.state) (ans:int64)
    (HAexp: aeval st a = ans)

    (g:ctxt)
    (n m:int) (cd:list elt)
    (n' m':int) (cd':list elt)
    (v : Ollvm_ast.value)
    (Hcomp : compile_aexp g a (n,m,cd) = ((n',m',cd'),inr v)),

  exists cd_a c_a,
    cd' = cd_a ++ cd
    /\ compiled_code cd_a c_a
    /\ forall
    (e:env)
    (mem:memory) (Hlt:env_lt n e)
    (HM: memory_invariant g e mem st),
        forall (CFG : mcfg) (p:pc) (k:stack) (P:pc -> Prop)
          (HCFG: CFG_has_code_at CFG P p (List.rev c_a)),
          step_star CFG
                    (fun '(pc', e', k') mem' =>
                       P pc' /\
                       memory_invariant g e' mem' st /\
                       Rv64e (eval_op e' (Some (TYPE_I 64)) v) ans /\
                       env_extends e e' /\
                       env_lt n' e' /\ k = k'
                    )
                    (p, e, k) mem.
Proof.
  intros a st ans HAexp.
  rewrite aeval_iff_aevalR in HAexp.

  induction HAexp; intros g n m cd n' m' cd' v Hcomp; unfold_llvm Hcomp.
  - inversion_clear Hcomp. 
    exists []. exists [].
    repeat split; auto.
    + intros e mem Hlt HM.
      intros CFG p k P HCFG.
      simpl in HCFG.
      exploit_CFG_code.
      eapply step_zero.
      repeat split; auto.  rewrite Int64.repr_signed; auto.
      weakening.

  - unfold trywith in Hcomp.
    remember (g id) as X.
    destruct X; simpl in Hcomp; inversion_clear Hcomp.
    exists [I (IId (lid_of_Z n)) (INSTR_Load false i64 (i64ptr, v0) None)].
    exists [(IId (lid_of_Z n), (INSTR_Load false i64 (i64ptr, v0) None))].
    simpl. repeat split; auto.
    intros e mem Hlt Hmem.
    intros CFG p k P HCFG.
    exploit_CFG_code.

    destruct (Hmem id v0) as [nv [Hv [a [Ha Hr]]]]; auto. subst.
    eapply step_eff.
    simplify_step. 
    reflexivity.
    simpl. reflexivity.
      
    apply step_zero.
    repeat split; auto; weakening.
    unfold eval_expr; simpl. rewrite lookup_env_hd; eauto. 

  - instantiate_H.
    intros e mem Hlt HM.
    intros CFG p k P HCFG.
    normalize_lists.
    exploit_CFG_code.

    eapply step_star_app.
    eapply IHHAexp1; weakening; eauto.
    intros [[pc1 e1] k1] mem1 [Hpc1 [Hmem1 [Heval1 [Hext1 [Hlt1 Hk1]]]]].
    subst.
    eapply step_star_app.
    eapply IHHAexp2; weakening; eauto.
    intros [[pc2 e2] k2] mem2 [Hpc2 [Hmem2 [Heval2 [Hext2 [Hlt2 Hk2]]]]].    
    subst;
    eapply step_tau;
    simplify_step.
    reflexivity.

    eapply step_zero.
    repeat split; auto; weakening.
    simpl. unfold eval_expr. simpl. rewrite lookup_env_hd. eauto.
      
  - instantiate_H.
    intros e mem Hlt HM.
    intros CFG p k P HCFG.
    normalize_lists.
    exploit_CFG_code.

    eapply step_star_app.
    eapply IHHAexp1; weakening; eauto.
    intros [[pc1 e1] k1] mem1 [Hpc1 [Hmem1 [Heval1 [Hext1 [Hlt1 Hk1]]]]].
    subst.
    eapply step_star_app.
    eapply IHHAexp2; weakening; eauto.
    intros [[pc2 e2] k2] mem2 [Hpc2 [Hmem2 [Heval2 [Hext2 [Hlt2 Hk2]]]]].    
    subst;
    eapply step_tau;
    simplify_step.
    reflexivity.

    eapply step_zero.
    repeat split; auto; weakening.
    simpl. unfold eval_expr. simpl. rewrite lookup_env_hd. eauto.

  - instantiate_H.
    intros e mem Hlt HM.
    intros CFG p k P HCFG.
    normalize_lists.
    exploit_CFG_code.

    eapply step_star_app.
    eapply IHHAexp1; weakening; eauto.
    intros [[pc1 e1] k1] mem1 [Hpc1 [Hmem1 [Heval1 [Hext1 [Hlt1 Hk1]]]]].
    subst.
    eapply step_star_app.
    eapply IHHAexp2; weakening; eauto.
    intros [[pc2 e2] k2] mem2 [Hpc2 [Hmem2 [Heval2 [Hext2 [Hlt2 Hk2]]]]].    
    subst;
    eapply step_tau;
    simplify_step.
    reflexivity.

    eapply step_zero.
    repeat split; auto; weakening.
    simpl. unfold eval_expr. simpl. rewrite lookup_env_hd. eauto.
Qed.


Lemma compile_bexp_correct :
  forall 
    (b:bexp) (st:Imp.state) (ans:bool)
    (HBexp: beval st b = ans)

    (g:ctxt)
    (n m:int) (cd:list elt)
    (n' m':int) (cd':list elt)
    (v : Ollvm_ast.value)
    (Hcomp : compile_bexp g b (n,m,cd) = ((n',m',cd'),inr v)),

  exists cd_a c_a,
    cd' = cd_a ++ cd
    /\ compiled_code cd_a c_a
    /\ forall
    (e:env)
    (mem:memory) (Hlt:env_lt n e)
    (HM: memory_invariant g e mem st),
        forall (CFG : mcfg) (p:pc) (k:stack) (P:pc -> Prop)
          (HCFG: CFG_has_code_at CFG P p (List.rev c_a)),
          step_star CFG
                    (fun '(pc', e', k') mem' =>
                       P pc' /\
                       memory_invariant g e' mem' st /\
                       Rv1e (eval_op e' (Some (TYPE_I 1)) v) ans /\
                       env_extends e e' /\
                       env_lt n' e' /\ k = k'
                    )
                    (p, e, k) mem.
Proof.
Admitted.  



Definition CFG_has_compilation_of CFG fid g cmd :=
  exists n m cd cd_c n' m' cd' bid term blks,
    compile_com g cmd (n,m,cd) = ((n',m',cd'), inr ())
    /\ cd' = cd_c ++ cd
    /\ blocks_of_elts bid cd_c (IVoid m', term) = inr blks
    /\ CFG_fun_has_blocks CFG fid blks.
               
(*
Lemma compile_com_correct :
  forall (cmd:com) (k:Imp.cont) (st:Imp.state) cmd' k' st'
    (HStep: cmd / k / st ==> cmd' / k' / st')
    (g:ctxt) (CFG:mcfg) (fn:function_id)
    s mem
    (Hrelated: related_configuration g cmd k st fn s mem),
    step_star CFG (fun s' mem' =>
                      let '(pc', e', k') := s' in
                      related_configuration g cmd' st' fn s' mem'
                   )
               s mem.
Proof.
  intros cmd res st st' Hceval.
  induction Hceval; intros g CFG fn s mem Hrel; inversion Hrel; clear Hrel; subst; auto.

  - unfold_llvm Hcomp.
    inversion Hcomp; subst.
    eapply step_zero2. left.
    split; auto.
    destruct s as [[pc e] k].
    simpl in Hpc.
    rewrite <- app_nil_l in H2 at 1.
    apply app_inv_tail in H2.
    subst. simpl in *.
    unfold blocks_of_elts in Hblks.
    simpl in Hblks. inversion Hblks. subst.
    exists m'. exists bid. exists term.
    split; auto.

  - unfold_llvm Hcomp.
    remember (compile_aexp


Lemma compile_com_correct :
  forall 
    (cmd:com) (res:option com) (st st':Imp.state)
    (HStep: ceval_small cmd st res st')

    (g:ctxt)
    (n m:int) (cd:list elt)
    (n' m':int) (cd':list elt)
    (Hcomp : compile_com g cmd (n,m,cd) = ((n',m',cd'),inr ())),

  exists cd_a,
    cd' = cd_a ++ cd
    /\ forall (bid: block_id) term,
      exists blk, exists blks,
        blocks_of_elts bid cd_a (IVoid m', term) = inr (blk :: blks)
        /\ forall (e:env) (mem:memory)
            (HM: memory_invariant g e mem st)
            (k:stack)
            (CFG : mcfg) (fn : function_id) 
            (HCFG: cfg_has_blocks CFG fn (blk::blks)),
            step_code2
        CFG
        (fun s' mem' =>
           let '(pc', e', k') := s' in
           pc' = slc_pc fn bid [] (IVoid m', term) [] /\
           memory_invariant g e' mem' st 
        )
        (mk_pc fn blk, e, k) mem.
Proof.
  intros cmd res st st' Hceval.
  
  
*)