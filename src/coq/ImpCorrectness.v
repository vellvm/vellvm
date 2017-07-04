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


Lemma rev_nil_inv : forall {A} (l:list A), rev l = [] -> l = [].
Proof.
  destruct l; intros; auto.
  simpl in H.  apply app_eq_nil in H. destruct H. inversion H0.
Qed.

Lemma app_same_inv : forall {A} (l1 l2:list A), l1 = l2 ++ l1 -> l2 = [].
Proof.
  induction l1; intros l2 H.
  - rewrite app_nil_r in H. auto.
  - destruct l2; auto.
    inversion H. subst.
    assert ((l2 ++ a0 :: l1) = ((l2 ++ [a0]) ++ l1)).
    rewrite <- app_assoc. simpl. reflexivity.
    rewrite H0 in H2. apply IHl1 in H2. apply app_eq_nil in H2. inversion H2. inversion H3.
Qed.  
  
Ltac simplify_lists :=
  repeat (match goal with
          | [H : ?x = ?y ++ ?x |- _ ] => apply app_same_inv in H
          | [H : ?x = ?y ++ ?z ++ ?x |- _ ] => rewrite app_assoc in H
          | [H : ?x ++ ?y = [] |- _ ] => apply app_eq_nil in H; let y := fresh in destruct H as [_ y]; inversion y
          | [H : [] = ?x ++ [?y] |- _ ] => symmetry in H
          | [H : [] <> [] |- _] => contradiction H
          | [H : ?x::?l = [] |- _] => inversion H
          | [H : [] = ?x::?l |- _] => inversion H
          | [H : context[rev[]] |- _] => simpl in H
          | [H : [] = [] |- _ ] => clear H
          | [H : ?x = [] |- _ ] => subst
          | [H : (_, _, _, inl _) = (_, _, _, inr _) |- _ ] => inversion H
          end).

(* Move to Compiler.v *)
Ltac unfold_compiler H :=
  progress (simpl in H; unfold cmd_bind in H; unfold cmd_ret in H; unfold exp_bind in H; unfold exp_ret in H; unfold lift_cmd in H; unfold lift_exp in H).

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

Definition list_le {A} (cd1 cd2 : list A) : Prop :=
  exists cd, cd2 = cd ++ cd1.

Lemma list_le_refl : forall {A} (cd:list A), list_le cd cd.
Proof.
  intros.
  exists []. reflexivity.
Qed.

Lemma list_le_trans : forall {A} (cd1 cd2 cd3:list A), list_le cd1 cd2 -> list_le cd2 cd3 -> list_le cd1 cd3.
Proof.
  intros A cd1 cd2 cd3 H12 H23.
  destruct H12 as [cd12 Heq12].
  destruct H23 as [cd23 Heq23].
  subst. exists (cd23 ++ cd12).
  rewrite app_assoc. reflexivity.
Qed.  

Lemma list_le_antireflexive : forall {A} (l1 l2:list A), list_le l1 l2 -> list_le l2 l1 -> l1 = l2.
Proof.
  intros A l1 l2 H1 H2.
  unfold list_le in H1.
  unfold list_le in H2.
  destruct H1 as [l3 Eq3].
  destruct H2 as [l4 Eq4].
  subst.
  simplify_lists. reflexivity.
Qed.

Definition string_le (s t:string) : Prop := exists u, t = (u ++ s)%string.


Inductive raw_id_le : raw_id -> raw_id -> Prop :=
| id_Raw_Raw :
    forall n m (Hlt: n <= m),
      raw_id_le (Raw n) (Raw m)
| id_Raw_Anon :
    forall n m,
      raw_id_le (Raw n) (Anon m)
| id_Raw_Name :
    forall n s,
      raw_id_le (Raw n) (Name s)
| id_Anon_Anon :
    forall n m (Hlt: n <= m),
      raw_id_le (Anon n) (Anon m)
| id_Anon_Name :
    forall n s,
      raw_id_le (Anon n) (Name s)
| id_Name_Name :
    forall s t
      (Hlt: string_le s t),
      raw_id_le (Name s) (Name t)
.                
  
Definition exp_state_le : (int * code) -> (int * code) -> Prop :=
  fun '(n1,cd1) '(n2, cd2) => 
  n1 <= n2 /\ list_le cd1 cd2.

Lemma exp_state_le_refl: forall (s:int * code), exp_state_le s s.
Proof.
  intros. destruct s. simpl. split; auto. omega. apply list_le_refl.
Qed.

Lemma exp_state_le_trans : forall (s1 s2 s3:int * code), exp_state_le s1 s2 -> exp_state_le s2 s3 -> exp_state_le s1 s3.
Proof.
Admitted.

Lemma exp_state_le_antireflexive : forall s1 s2, exp_state_le s1 s2 -> exp_state_le s2 s1 -> s1 = s2.
Proof.
Admitted.  



Inductive  cmd_state_le : cmd_state -> cmd_state -> Prop :=
| cmd_same_block :
    forall n1 m1 is1 t1 bs1 n2 m2 is2 t2 bs2
      (Hn: n1 <= n2)
      (Hm: m1 <= m2)
      (His: list_le is1 is2)
      (Ht: t1 = t2)
      (Hbs: bs1 = bs2),
      cmd_state_le (mk_cs n1 m1 is1 t1 bs1) (mk_cs n2 m2 is2 t2 bs2)
| cmd_new_block :
    forall n1 m1 is1 t1 bs1 n2 m2 is2 t2 bs2
      (Hn: n1 <= n2)
      (Hm: m1 <= m2)
      (Hcd: exists n, n1 <= n /\ n <= n2 /\ exists m, m1 <= m /\ m <= m2 /\
            exists is', list_le ((mk_block (lid_of_Z n) [] (rev (is' ++ is1)) (IVoid m, t1))::bs1) bs2),
      
      cmd_state_le (mk_cs n1 m1 is1 t1 bs1) (mk_cs n2 m2 is2 t2 bs2)
.

Ltac exploit_cmd_state_le :=
  repeat (match goal with
          | [ H : cmd_state_le ?S1 ?S2 |- _ ] => destruct ?S1; destruct ?S2; inversion H; exploit_cmd_state_le
          | [ H : exists b, _ |- _ ] => let X := fresh "c" in destruct H as [X H]; exploit_cmd_state_le
          | [ H : ?a /\ ?b |- _ ] => let A := fresh "H" in destruct H as [A H]; exploit_cmd_state_le
          end).


Lemma cmd_state_le_refl : forall (cs:cmd_state), cmd_state_le cs cs.
Proof.
  destruct cs.
  eapply cmd_same_block; eauto; try omega; try apply list_le_refl.
Qed.  
  

Lemma cmd_state_le_trans : forall s1 s2 s3, cmd_state_le s1 s2 -> cmd_state_le s2 s3 -> cmd_state_le s1 s3.
Proof.
  intros s1 s2 s3 H12 H23.
  destruct s1. destruct s2. destruct s3.
  inversion H12; subst; auto.
  - inversion H23; subst; auto.
    + eapply cmd_same_block; eauto; try omega; try solve [eapply list_le_trans; eauto].
    + exploit_cmd_state_le.
      eapply cmd_new_block; eauto; try omega.
      exists c. repeat split; try omega.
      exists c0. repeat split; try omega.
      destruct His as [is' H'].
      exists (c1 ++ is').
      subst. rewrite <- app_assoc. exact Hcd.
  - inversion H23; subst; auto.
    + exploit_cmd_state_le.
      eapply cmd_new_block; eauto; try omega.
      exists c. repeat split; try omega.
      exists c0. repeat split; try omega.
      exists c1. exact Hcd.
    + exploit_cmd_state_le.
      destruct Hcd as [cd' Hcd']. subst.
      destruct Hcd0 as [cd0' Hcd0'].  subst.
      eapply cmd_new_block; eauto; try omega.
      exists c0. repeat split; try omega.
      exists c3. repeat split; try omega.
      exists c4. exists (cd0' ++
     {| blk_id := lid_of_Z c; blk_phis := []; blk_code := rev (c2 ++ is0); blk_term := (IVoid c1, tm0) |}
     :: cd').
      simpl. rewrite <- app_assoc. reflexivity.
Qed.      
      

(*
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
*)
                  
Lemma compile_aexp_monotonic :
  forall g a
    s v s'
    (Hcomp : compile_aexp g a s = (s',inr v)),
    exp_state_le s s'.
Proof.
  intros g a.
  (* induction a; intros n1 m1 code1 v n2 m2 code2 Hcomp.  simpl in Hcomp. *)
  (* - unfold_llvm Hcomp. *)
  (*   inversion Hcomp; subst. repeat split; try omega. exists []. simpl. reflexivity. *)

  (* - unfold_llvm Hcomp. *)
  (*   destruct (g i); simpl in Hcomp; try inversion Hcomp. *)
  (*   repeat split; try omega. *)
  (*   exists [I (IId (lid_of_Z n1)) (INSTR_Load false i64 (i64ptr, v0) None)]. simpl. reflexivity. *)

  (* - compile_aexp_monotonic_case Add. *)
  (* - compile_aexp_monotonic_case Sub. *)
  (* - compile_aexp_monotonic_case Mul. *)
Admitted.
    

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

Section Correctness.

  Variable (g:ctxt).
  Variable g_inj :
    forall (x y:id) a b
      (Hid: beq_id x y = false)
      (Hx: g x = Some a)
      (Hy: g y = Some b),
      a <> b.

Definition memory_invariant (e:env) (m:memory) (st:Imp.state) : Prop :=
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
  forall e n mem st dv
    (Henv: env_lt n e)
    (Hmem: memory_invariant e mem st),
    memory_invariant (add_env_Z n dv e) mem st.
Proof.
  intros e n mem st dv Henv Hmem.
  unfold memory_invariant in *.
  intros x v Hg.
  apply Hmem in Hg. clear Hmem.
  destruct Hg as [n0 [Hv [a [Ha Hrv]]]].
  exists n0. split; auto.
  exists a. eapply env_lt_lookup_inv with (n':=n0) in Henv.
  split; auto. unfold add_env_Z. rewrite lookup_env_tl; auto. apply lid_of_Z_inj.
  unfold not. intros. subst. omega. exact Ha.
Qed.  


(* Relational step semantics ------------------------------------------------ *)

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

  | [ |- _ /\ _ ] => split; instantiate_H
                    
  | [ |- ?X :: ?A ++ ?B ++ ?C = (?X :: ?A ++ ?B) ++ ?C ] => simpl; rewrite app_assoc; reflexivity

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

(*
  lbl: 
   pc0 i0
   pc1 i1
   ...

 P pcN [...]
   ...
   pcM ....
 Q?   
*)

(*
Lemma compile_aexp_correct :
  forall g a n cd0
      (n', cd, inr v) = compile_aexp g a (n, cd0)
      CFG_has_code_at CFG P p1 (rev cd)
      memory_invariant g e mem1 st
      exists s2,
        step_star CFG (fun '(p2, e2, k2) mem =>
                         memory_invariant g e2 mem1 st /\
                         Rv64e (eval_op e' (Some (TYPE_I 64)) v) (aeval st a) /\
                         mem = mem1 /\ env_extends e e' /\ 
                         (P p2) /\  k2 = k1)
                         
              (fun '(pc', e', k') mem' =>
                 memory_invariant g e' mem' st /\

                 env_extends e e' /\
                 env_lt (fst cs') e' /\ k = k'
              )
*)

Lemma compile_aexp_correct :
  forall (a:aexp) (st:Imp.state) 
    n0 cd0 n1 cd1 (v : Ollvm_ast.value)
    (Hcomp : (n1, cd1, inr v) = compile_aexp g a (n0, cd0)),
    exists cd2,
      cd1 = cd2 ++ cd0 /\
      forall           
        (CFG : mcfg) P (p1:pc) (e:env) (k:stack) 
        (Hcfg: CFG_has_code_at CFG P p1 (rev cd2))
        (mem:memory) (* (Hlt:env_lt n0 e) *)
        (HM: memory_invariant e mem st),
        step_star CFG
                  (fun '(pc', e', k') mem' =>
                     P pc' /\ (fn pc' = fn p1) /\
                     memory_invariant e' mem' st /\
                     Rv64e (eval_op e' (Some (TYPE_I 64)) v) (aeval st a) /\
                     env_extends e e' /\
(*                     env_lt n1 e' /\ *)
                     k = k'
                  )
                  (p1, e, k) mem.
Proof.
Admitted.
(*
  intros a st ans HAexp.
  rewrite aeval_iff_aevalR in HAexp.

  induction HAexp; intros g cs cs' v Hcomp CFG fid P p HCFG e k mem Hlt HM. 
  - simpl in Hcomp. unfold_llvm Hcomp. inversion Hcomp. 

    inversion HCFG. subst.
          eapply step_zero.
      repeat split; auto.  rewrite Int64.repr_signed; auto.
      weakening.
      subst. simpl in *.
      eapply step_zero.
      repeat split; auto.  

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
*)

Lemma compile_bexp_correct :
  forall (b:bexp) (st:Imp.state) 
    n0 cd0 n1 cd1 (v : Ollvm_ast.value)
    (Hcomp : (n1, cd1, inr v) = compile_bexp g b (n0, cd0)),
    exists cd2,
      cd1 = cd2 ++ cd0 /\
      forall           
        (CFG : mcfg) P (p1:pc) (e:env) (k:stack) 
        (Hcfg: CFG_has_code_at CFG P p1 (rev cd2))
        (mem:memory) (* (Hlt:env_lt n0 e) *)
        (HM: memory_invariant e mem st),
        step_star CFG
                  (fun '(pc', e', k') mem' =>
                     P pc' /\ (fn pc' = fn p1) /\
                     memory_invariant e' mem' st /\
                     Rv1e (eval_op e' (Some (TYPE_I 1)) v) (beval st b) /\
                     env_extends e e' /\
(*                     env_lt n1 e' /\ *)
                     k = k'
                  )
                  (p1, e, k) mem.
Proof.
Admitted.



Inductive matching_state (CFG:mcfg) (fid:function_id) (P:pc -> Prop) : pc -> com -> Prop :=
| match_skip:
    forall p
      (Hp: P p),
      matching_state CFG fid P p SKIP

| match_assn:
    forall p a x n v cd n' m ptr
      (Ha: ((n',cd), inr v) = compile_aexp g a (n, []))
      (Hx: (g x) = Some ptr)
      (HCFG: CFG_has_code_at CFG P p (rev ((IVoid m, (INSTR_Store false (i64, v) (i64ptr, ptr) None))::cd))),
      matching_state CFG fid P p (CAss x a)

| match_seq:
    forall p q c1 c2 
      (Hc1: matching_state CFG fid (fun pc => pc = q \/ exists b, fetch CFG pc = Some (Term (TERM_Br_1 b)) /\ CFG_fun_has_block_id CFG fid b [] q) p c1)
      (Hc2: matching_state CFG fid P q c2),
      matching_state CFG fid P p (CSeq c1 c2) 
                     
| match_if:
    forall p b n v cd n' br1 br2 merge c1 c2 p1 p2 pmerge
      (Ha: ((n', cd), inr v) = compile_bexp g b (n, []))
      (HCFG: CFG_has_code_at CFG (fun q => fetch CFG q = Some (Term (TERM_Br (i1, v) br1 br2)))
                             p (rev cd))
      (HBR1: CFG_fun_has_block_id CFG fid br1 [] p1)
      (*      (IH1: matching_state CFG g fid (fun q => fetch CFG q = Some (Term (TERM_Br_1 merge))) p1 c1) *)
      (IH1: matching_state CFG fid P p1 c1) 
      (HBR2: CFG_fun_has_block_id CFG fid br2 [] p2)
      (IH2: matching_state CFG fid P p2 c2)
      (Hmerge: CFG_fun_has_block_id CFG fid merge [] pmerge)
      (IHmerge: matching_state CFG fid P pmerge SKIP),
      matching_state CFG fid P p (CIf b c1 c2)

| match_while0:
    forall p b n v cd n' body entry exit c pentry pbody pexit
      (Hpcd: fetch CFG p = Some (Term (TERM_Br_1 entry)))
      (Hentry: CFG_fun_has_block_id CFG fid entry [] pentry)
      (Ha: ((n', cd), inr v) = compile_bexp g b (n, []))
      (HCFG: CFG_has_code_at CFG (fun q => fetch CFG q = Some (Term (TERM_Br (i1, v) body exit)))
                           pentry (rev cd))
      (Hbody: CFG_fun_has_block_id CFG fid body [] pbody)
      (IH1: matching_state CFG fid (fun q => fetch CFG q = Some (Term (TERM_Br_1 entry))) pbody c)
      (Hexit: CFG_fun_has_block_id CFG fid exit [] pexit)
      (IHexit: matching_state CFG fid P pexit SKIP),
      matching_state CFG fid P p (CWhile b c)

| match_while1:
    forall p b n v cd n' body entry exit c pbody pexit
      (Hentry: CFG_fun_has_block_id CFG fid entry [] p)
      (Ha: ((n', cd), inr v) = compile_bexp g b (n, []))
      (HCFG: CFG_has_code_at CFG (fun q => fetch CFG q = Some (Term (TERM_Br (i1, v) body exit)))
                           p (rev cd))
      (Hbody: CFG_fun_has_block_id CFG fid body [] pbody)
      (IH1: matching_state CFG fid (fun q => fetch CFG q = Some (Term (TERM_Br_1 entry))) pbody c)
      (Hexit: CFG_fun_has_block_id CFG fid exit [] pexit)
      (IHexit: matching_state CFG fid P pexit SKIP),
      matching_state CFG fid P p (CWhile b c)

.
Hint Constructors matching_state.  

Lemma CFG_has_code_at_weakening : 
  forall CFG (P:pc -> Prop) (Q:pc -> Prop) p cd
    (HP: forall q, P q -> Q q)
    (Hc: CFG_has_code_at CFG P p cd),
    CFG_has_code_at CFG Q p cd.
Proof.
  intros CFG P Q p cd HP Hc.
  induction Hc; eauto.
Qed.  
    
    
Lemma matching_state_weakening :
  forall CFG fid (P:pc -> Prop) (Q:pc -> Prop) p cmd
    (HP: forall q, P q -> Q q)
    (Hm: matching_state CFG fid P p cmd),
    matching_state CFG fid Q p cmd.
Proof.
  intros CFG fid P Q p cmd HP Hm.
  induction Hm; intros; eauto.
  eapply match_assn. eauto. eauto. eapply CFG_has_code_at_weakening. eauto. eauto.
Qed.  
  


Inductive related_configuration (CFG:mcfg) fid (cmd:com) (st:Imp.state) (s:SS.state) (mem:memory) P : Prop :=
| config_intro :
    forall p e k
    (Hs: s = (p, e, k))
    (Hmem : memory_invariant e mem st)
    (Hcfg: matching_state CFG fid P p cmd)
    (Hpc: (fn p) = fid)
    ,
    related_configuration CFG fid cmd st s mem P.
Hint Constructors related_configuration.    

Lemma compile_com_correct :
  forall (cmd1 cmd2:com) (st1 st2:Imp.state)
    (HStep: cmd1 / st1 ==> cmd2 / st2)
    (CFG:mcfg) (fid:function_id) (s1:SS.state) (mem1:memory) P
    (Hrel: related_configuration CFG fid cmd1 st1 s1 mem1 P),
    step_star CFG (fun s2 mem2 =>
                     related_configuration CFG fid cmd2 st2 s2 mem2 P
                  )
              s1 mem1.
Proof.
  intros cmd1 cmd2 st1 st2 HStep.
  induction HStep; intros.

  - inversion Hrel. inversion Hcfg; subst.
    simpl in HCFG.
    exploit_CFG_code.
    pose (compile_aexp_correct a1 st n0 [] n' cd v ltac:(auto)) as K; clearbody K.
    destruct K as [cd2 [Heqcd K]].
    rewrite app_nil_r in Heqcd. subst.
    pose (K CFG _ p e k HL mem1 ltac:(auto)) as HA; clearbody HA; clear K.
    eapply step_star_app.
    eapply HA.
    intros [[pc2 e2] k2]. intros mem2. intros [Heq [Hfn [Hmem2 [Heval [Hext Hk2]]]]].
    subst.
      
    inversion Heval. simplify_step.
    unfold memory_invariant in Hmem2. 
    apply Hmem2 in Hx.
    destruct Hx. destruct H1. destruct H3. destruct H3.
    subst. 

    eapply step_eff.
    simplify_step.
    rewrite <- H0. simpl.
      reflexivity.
      reflexivity.
      eapply step_zero.
      eapply config_intro.
      reflexivity.
      unfold memory_invariant.
      intros.
      apply Hmem2 in H1.
      destruct H1. destruct H1. destruct H2. destruct H2.
      exists x3. repeat split; eauto.
      exists x4. repeat split; auto.
      subst. 
      inversion Heval.
      subst.
      inversion H5.
      unfold Rv64.
      inversion H6.
      inversion H4.
      (* Needs injectivity of g and some other facts about nth_default and replace *)
      admit.

      eauto. rewrite <- Hfn. apply incr_pc_in_block in Hincr. destruct Hincr. rewrite H1. reflexivity.

      (*
      eapply step_jump.
      simpl. rewrite Hp. simpl.
      unfold jump. inversion Hb. rewrite H. simpl. reflexivity.
      eapply step_zero. eapply config_intro. reflexivity. inversion Hcfg. subst. *)

  - inversion Hrel.
    inversion Hcfg. subst.
    
    eapply step_star_app.
    eapply IHHStep.
    econstructor. reflexivity. eauto. apply Hc1. reflexivity.
    intros [[pc2 e2] k2]. intros mem2 HR.
    inversion HR. 
    eapply step_zero.
    econstructor.  exact Hs. eauto.
    econstructor. eauto. eauto. eauto.

  - inversion Hrel.
    inversion Hcfg.
    inversion Hc1.

    subst.
    destruct Hp. subst.
    + eapply step_zero.
      econstructor; eauto.

    + destruct H as [b [Hf Hh]].
      eapply step_jump.
      simpl.
      rewrite Hf. simpl.
      unfold jump.
      inversion Hh. rewrite H. simpl. reflexivity.
      eapply step_zero.
      econstructor; eauto. inversion Hh. apply find_block_same_fid in H. auto.

  - inversion Hrel.
    inversion Hcfg.
    subst.
    eapply step_star_app.
    pose (compile_bexp_correct b st n [] n' cd v ltac:(auto)) as K; clearbody K.
    destruct K as [cd2 [Heqcd K]].
    rewrite app_nil_r in Heqcd. subst.
    pose (K CFG _ p e k HCFG mem1 ltac:(auto)) as HA; clearbody HA; clear K.
    eapply HA.
    intros [[pc2 e2] k2]. intros mem2. intros [Heq [Hpc [Hmem2 [Heval [Hext Hk2]]]]].
    subst.

    inversion HBR1.
    inversion Heval. subst. 
    unfold Rv1 in H3.
    rewrite H in H3.
    eapply step_jump.
    simplify_step.
    unfold i1. rewrite <- H2. simpl. subst. simpl.
    unfold jump.
    rewrite Hpc. 
    rewrite H0.
    simpl.
    reflexivity.
    eapply step_zero.
    eapply config_intro. reflexivity. eauto. 
    
    subst. simpl.
    unfold jump. eauto.
    apply find_block_same_fid in H0. auto.

  -  admit. (* Similar to previous case *)

  - inversion Hrel.
    + inversion Hcfg.
    subst.
    eapply step_star_app.
    eapply step_jump.
    simpl.
    rewrite Hpcd. simpl.
    unfold jump.
    inversion Hentry.
    rewrite H0.
    simpl.
    reflexivity.
    pose (compile_bexp_correct b st n [] n' cd v ltac:(auto)) as K; clearbody K.
    destruct K as [cd2 [Heqcd K]].
    rewrite app_nil_r in Heqcd. subst.
    pose (K CFG _ pentry e k HCFG mem1 ltac:(auto)) as HA; clearbody HA; clear K.
    eapply HA.
    intros [[pc2 e2] k2]. intros mem2. intros [Heq [Hpc [Hmem2 [Heval [Hext Hk2]]]]].
    subst.
    eapply step_jump.
    simpl.
    rewrite Heq. simpl. unfold i1. inversion Heval. subst. unfold Rv1 in H1. rewrite H in H1. subst. simpl.
    unfold jump.
    inversion Hexit. inversion Hentry. apply find_block_same_fid in H3. rewrite Hpc. rewrite H3. rewrite H1.
    simpl. reflexivity.
    eapply step_zero.
    eapply config_intro. reflexivity. eauto. econstructor.  inversion IHexit. subst. auto.
    inversion Hexit. apply find_block_same_fid in H0. auto.

    subst.
    eapply step_star_app.
    pose (compile_bexp_correct b st n [] n' cd v ltac:(auto)) as K; clearbody K.
    destruct K as [cd2 [Heqcd K]].
    rewrite app_nil_r in Heqcd. subst.
    pose (K CFG _ p e k HCFG mem1 ltac:(auto)) as HA; clearbody HA; clear K.
    eapply HA.
    intros [[pc2 e2] k2]. intros mem2. intros [Heq [Hpc [Hmem2 [Heval [Hext Hk2]]]]].
    subst.
    eapply step_jump.
    simpl.
    rewrite Heq. simpl. unfold i1. inversion Heval. subst. unfold Rv1 in H1. rewrite H in H1. subst. simpl.
    unfold jump.
    inversion Hexit. inversion Hentry. apply find_block_same_fid in H3. rewrite Hpc. rewrite H1. 
    simpl. reflexivity.
    eapply step_zero.
    eapply config_intro. reflexivity. eauto. econstructor.  inversion IHexit. subst. auto.
    inversion Hexit. apply find_block_same_fid in H0. auto.
    
  - inversion Hrel.
    inversion Hcfg; subst.
    +
    eapply step_star_app.
    eapply step_jump.
    simpl.
    rewrite Hpcd. simpl.
    unfold jump.
    inversion Hentry.
    rewrite H0.
    simpl.
    reflexivity.
    pose (compile_bexp_correct b st n [] n' cd v ltac:(auto)) as K; clearbody K.
    destruct K as [cd2 [Heqcd K]].
    rewrite app_nil_r in Heqcd. subst.
    pose (K CFG _ pentry e k HCFG mem1 ltac:(auto)) as HA; clearbody HA; clear K.
    eapply HA.
    intros [[pc2 e2] k2]. intros mem2. intros [Heq [Hpc [Hmem2 [Heval [Hext Hk2]]]]].
    subst.
    eapply step_jump.
    simpl. rewrite Heq.
    simpl. simpl. unfold i1. inversion Heval. subst. unfold Rv1 in H1. rewrite H in H1. subst. simpl.
    unfold jump.
    inversion Hbody. inversion Hentry. apply find_block_same_fid in H3. rewrite Hpc. rewrite H3. rewrite H1.
    simpl.
    reflexivity.
    inversion Hbody.
    
    eapply step_zero.
    eapply config_intro. reflexivity. eauto. econstructor.
    Focus 2. eapply match_while1. apply Hentry. eauto. eapply HCFG. eapply Hbody. eapply IH1. eapply Hexit.
    inversion IHexit. subst. econstructor. exact Hp.
    
    eapply matching_state_weakening with (P:= (fun q : pc => fetch CFG q = Some (Term (TERM_Br_1 entry)))).
    intros.
    right. exists entry. split; auto. apply IH1.
    apply find_block_same_fid in H0. exact H0.

    + eapply step_star_app.
      pose (compile_bexp_correct b st n [] n' cd v ltac:(auto)) as K; clearbody K.
      destruct K as [cd2 [Heqcd K]].
      rewrite app_nil_r in Heqcd. subst.
      pose (K CFG _ p e k HCFG mem1 ltac:(auto)) as HA; clearbody HA; clear K.
      eapply HA.
      intros [[pc2 e2] k2]. intros mem2. intros [Heq [Hpc [Hmem2 [Heval [Hext Hk2]]]]].
      subst.
      eapply step_jump.
      simpl.
      rewrite Heq. simpl. unfold i1. inversion Heval.  subst. simpl. unfold Rv1 in H1. rewrite Hpc. rewrite H in H1. subst.
      simpl. unfold jump.
      inversion Hbody. rewrite H1. simpl. reflexivity.
      eapply step_zero.
      eapply config_intro. reflexivity. eauto. econstructor.
      Focus 2. eapply match_while1. apply Hentry. eauto. eapply HCFG. eapply Hbody. eapply IH1. eapply Hexit.
      inversion IHexit. subst. econstructor. exact Hp.
    
      eapply matching_state_weakening with (P:= (fun q : pc => fetch CFG q = Some (Term (TERM_Br_1 entry)))).
      intros.
      right. exists entry. split; auto. apply IH1.
      inversion Hbody.
      apply find_block_same_fid in H0. exact H0.
Admitted.      
      

End Correctness.      


      

(*
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