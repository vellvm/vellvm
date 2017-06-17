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

Require Import ZArith String Omega List Equalities MSets.
Import ListNotations.

(* Vellvm dependencies *)
Require Import Vellvm.Ollvm_ast Vellvm.Compiler Vellvm.AstLib Vellvm.CFG Vellvm.StepSemantics Vellvm.Memory.
Require Import Vellvm.Classes.

(* Logical Foundations dependencies *)
Require Import Vellvm.Imp Vellvm.Maps Vellvm.ImpCEvalFun.
Import ListNotations.
Open Scope list_scope.

(* Move to Compiler.v *)
Ltac unfold_llvm H :=
  progress (unfold llvm_bind in H; unfold llvm_ret in H; unfold lift in H).

Arguments Z.add _ _ : simpl nomatch.


(* relational specification of aeval ---------------------------------------- *)

Inductive aevalR : Imp.state -> aexp -> nat -> Prop :=
  | E_ANum  : forall s (ans: nat),
      aevalR s (ANum ans) ans
  | E_AId : forall s id,
      aevalR s (AId id) (s id)
  | E_APlus : forall s (a1 a2: aexp) (ans1 ans2: nat),
      aevalR s a1 ans1 ->
      aevalR s a2 ans2 ->
      aevalR s (APlus a1 a2) (ans1 + ans2)
  | E_AMinus: forall s (a1 a2: aexp) (ans1 ans2: nat),
      aevalR s a1 ans1 ->
      aevalR s a2 ans2 ->
      aevalR s (AMinus a1 a2) (ans1 - ans2)
  | E_AMult : forall s (a1 a2: aexp) (ans1 ans2: nat),
      aevalR s a1 ans1 ->
      aevalR s a2 ans2 ->
      aevalR s (AMult a1 a2) (ans1 * ans2).
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
    simpl in Hcomp;
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
    inversion Hcomp. repeat split; try omega. exists []. simpl; auto.

  - simpl in Hcomp.
    unfold_llvm Hcomp.
    destruct (g i); simpl in Hcomp; try inversion Hcomp.
    repeat split; try omega.
    exists [I (IId (lid_of_Z n1)) (INSTR_Load false i64 (i64ptr, v0) None)]. simpl. reflexivity.

  - compile_aexp_monotonic_case Add.
  - compile_aexp_monotonic_case Sub.
  - compile_aexp_monotonic_case Mul.
Qed.    
    


Definition iid n (id:instr_id) : Prop := (IId (lid_of_Z n)) = id.

Definition add_env_Z n dv (e:env) := add_env (lid_of_Z n) dv e.

(* 
  The compiler emits code in "reverse" order, so when loaded into a CFG machine 
  
*)
Inductive code_at (CFG:mcfg) (f:function_id) (id_start:instr_id) : instr_id -> list elt -> Prop :=
| code_at_nil : code_at CFG f id_start id_start []
| code_at_uid :                         
    forall id i id_next code
      (HF: fetch CFG (mk_pc f id) = Some (Step i id_next))
      (IHC: code_at CFG f id_start id code),
      code_at CFG f id_start id_next ((I id i)::code).
Hint Constructors code_at.

(*
Inductive code_at (CFG:mcfg) (f:function_id) : list elt -> Prop := 
| code_at_nil : code_at CFG f []
| code_at_uid :                         
    forall id i id' code
      (HF: fetch CFG (mk_pc f id) = Some (Step i id'))
      (IHC: code_at CFG f code),
      code_at CFG f ((I id i)::code)
| code_at_term :
    forall id bid term code
      (HF: fetch CFG (mk_pc f id) = Some (Jump bid term))
      (IHC: code_at CFG f code),
      code_at CFG f ((T id term)::code)
| code_at_label :
    forall bid code
      (ICH: code_at CFG f code),
      code_at CFG f ((L bid)::code)
.
*)

Lemma code_at_append_1 :
  forall (CFG:mcfg) (f:function_id) (code1 code2:list elt) k2 k0 (H:code_at CFG f k2 k0 (code1 ++ code2)),
    exists k1, code_at CFG f k1 k0 code1.
Proof.
  intros CFG f code1 code2 k2 k0 H.
  remember (code1 ++ code2) as code. generalize dependent code2. revert code1.
  induction H; intros code1 code2 Heqcode.
  - apply eq_sym in Heqcode; apply app_eq_nil in Heqcode;
    destruct Heqcode as [H1 H2].
    exists k2. subst.  apply code_at_nil.
  -  destruct code1 as [|code1_tl].
     + exists id. apply code_at_nil.
     + simpl in Heqcode. inversion Heqcode.  subst. 
       edestruct IHcode_at as [k1 Heq].
       reflexivity.
       exists k1. eapply code_at_uid. apply HF. exact Heq.
Qed.


Lemma code_at_append_2 :
  forall (CFG:mcfg) (f:function_id) (code1 code2:list elt) k2 k0 (H:code_at CFG f k2 k0 (code1 ++ code2)),
    exists k1, code_at CFG f k2 k1 code2.
Proof.
  intros CFG f code1.
  induction code1; intros code2 k2 k0 H; simpl in *; inversion H; subst; eauto.
Qed.    

Lemma code_at_cons_id : forall CFG f k1 k0 id i code,
    code_at CFG f k1 k0 ((I id i)::code) -> id = k0.
Proof.
  intros CFG f k1 k0 id i code H.
  inversion H. reflexivity.
Qed.  

(* These definitions should probably go in a library *)
Definition dvalue_of_nat (n:nat) : value :=
  DV (VALUE_Integer (Z.of_nat n)).
Hint Unfold dvalue_of_nat.

Definition Rv (v:value) (n:nat) : Prop := dvalue_of_nat n = v.
Hint Unfold Rv.

Lemma lookup_env_hd : forall id dv e, lookup_env (add_env id dv e) id = inr dv.
Proof.
  intros id dv e.  unfold lookup_env. unfold trywith.
  unfold add_env.
  rewrite Util.assoc_hd. reflexivity.
Qed.  

Require Import Program.

Lemma lookup_env_tl : forall id1 v1 e id2 v2,
    id1 <> id2 -> lookup_env (add_env id1 v1 e) id2 = inr v2 <-> lookup_env e id2 = inr v2.
Proof.
  unfold lookup_env.
  unfold trywith.
  intros id1 v1 e id2 v2 H.
  split; intros H1.
  -  unfold add_env in H1.
     rewrite Util.assoc_tl in H1; auto.
     unfold local_id in *. (* Shows up only in the implicit instantiation of Util.assoc! *)
     destruct (Util.assoc RawID.eq_dec id2 e); eauto.
     inversion H1.
  - unfold add_env. rewrite Util.assoc_tl; auto.
    unfold local_id in *. 
    destruct (Util.assoc RawID.eq_dec id2 e); eauto.
    inversion H1.
Qed.  

Definition memory_invariant (g:ctxt) (e:env) n (m:memory) (st:Imp.state) : Prop :=
  forall x v, g x = Some v ->
         exists n', n' < n /\  (v = (local (lid_of_Z n')) /\
                 exists a, (lookup_env e (lid_of_Z n') = inr (DVALUE_Addr a) /\
                       Rv (nth_default undef m a) (st x))).


Lemma memory_invariant_extension : forall g e n m st n' dv,
  memory_invariant g e n m st -> n <= n' ->
  memory_invariant g (add_env_Z n' dv e) n m st.
Proof.
  intros g e n m st n' dv Hm Hlt.
  unfold memory_invariant in *.
  intros x v H.
  destruct (Hm x v) as [n'' [Hlt' [Heq [a [HL HR]]]]]; auto.
  exists n''. repeat split; auto.
  exists a; split; auto.
  unfold add_env_Z. eapply lookup_env_tl; eauto. apply lid_of_Z_inj.
  unfold not. intros. subst. omega.
Qed.  
  
(*
  Finitely many steps to some state / memory sequence related by R.
*)
Inductive step_star_invariant (CFG:mcfg) (R : SS.state -> memory -> Prop) : SS.state -> memory -> Prop :=
| step_zero :
    forall s m
      (HR : R s m),
      step_star_invariant CFG R s m
    
| step_tau :
    forall s s' m
      (HS : stepD CFG s = inl s')
      (Hstep : step_star_invariant CFG R s' m),
      step_star_invariant CFG R s m

| step_eff :
    forall s e m m' v k
      (HS : stepD CFG s = inr (Eff e))
      (HM : mem_step e m = inr (m', v, k))
      (Hstep : step_star_invariant CFG R (k v) m'),
      step_star_invariant CFG R s m
.

Lemma step_star_invariant_app :
  forall (CFG:mcfg) R1 R2 s1 m1
    (HS1: step_star_invariant CFG R1 s1 m1)
    (HR: forall s2 m2, R1 s2 m2 -> step_star_invariant CFG R2 s2 m2),
    step_star_invariant CFG R2 s1 m1.
Proof.
  intros CFG R1 R2 s1 m1 HS1 HR. 
  induction HS1; auto.
  - eapply step_tau. eapply HS.
    apply IHHS1.
  - eapply step_eff. eapply HS. eapply HM. eapply IHHS1.
Qed.    
                                  



(* LLVM A = ST (int * int * code) (err A) 
   = (int * int * code) -> ((int * int * code) * err A)

  e :: LLVM A
  {P} e {x:Q} 
  P int -> int -> code -> Prop 
  Q int -> int -> code -> A -> Prop ->
  forall n m code, 
     P n m code  ->
     exists n' m' code', 
     e (n,m,code) = ((n',m',code'), inr res) ->
     Q n' m' code' res
 *)
(*
Definition llvm_state := (int * int * list elt)%type.
Definition LLVM_Pre := llvm_state -> Prop.
Definition LLVM_Post (A:Type) := llvm_state -> llvm_state -> A -> Prop.

Definition LLVM_INV {A} (P:LLVM_Pre) (lc:LLVM A) (Q:LLVM_Post A) :=
  forall st,
    P st ->
    exists st' res,
      (lc st = (st',inr res)) /\
      (Q st st' res).

Lemma llvm_ret_INV : forall {A} (P:LLVM_Pre) (Q:LLVM_Post A) v (Hpq: forall st, (P st -> Q st st v)),
    LLVM_INV P (llvm_ret _ v) Q.
Proof.
  intros A P Q v Hpq.
  unfold LLVM_INV.
  intros st Hp.
  exists st. exists v.
  unfold llvm_ret; auto.
Qed.

Lemma llvm_bind_INV:
  forall {A B} (P:LLVM_Pre) (Q:LLVM_Post A) (R:LLVM_Post B)
    (e   : LLVM A)
    (f   : A -> LLVM B)
    (He  : LLVM_INV P e Q)
    (Hf  : forall s v, LLVM_INV (fun s2 => Q s s2 v) (f v) R)
    (Hqr : forall st st' st'' res res', Q st st' res -> R st' st'' res' -> R st st'' res')
  ,
    LLVM_INV P (llvm_bind _ _ e f) R.
Proof.
  intros A B P Q R e f He Hf Hqr. 
  unfold llvm_bind.
  unfold LLVM_INV in *.
  intros st HP.
  apply He in HP.
  destruct HP as [st'[res[Heq HQ]]].
  assert (Q st st' res) as HQ'. exact HQ.
  apply Hf in HQ.
  destruct HQ as [st''[res'[Heq' HR]]].
  exists st''. exists res'. rewrite Heq.
  split; auto. eapply Hqr.  apply HQ'. apply HR.
Qed.  

Definition start n := (IId (lid_of_Z n)).

Definition CPre g e mem st : LLVM_Pre :=
  fun (s:llvm_state) =>
    memory_invariant g e mem st.

Definition stepD_correct n code v ans :=
  forall CFG fn e k mem,
    code_at CFG fn (start n) code ->
    exists pc' e' k' m' u,
      step_star_invariant CFG (fun s m => s = (pc', e', k') /\ m' = m) (mk_pc fn (start n), e, k) mem
      /\ eval_op e' v = inr u      
      /\ Rv u ans.

Definition CPost g e mem st ans (f : LLVM Ollvm_ast.value) : LLVM_Post Ollvm_ast.value :=
  fun '((n,m,code):llvm_state) '((n',m',code'):llvm_state) (v:Ollvm_ast.value) =>
    memory_invariant g e mem st /\
    f (n,m,code) = (n',m',code', inr v) /\
    exists code'', code' = code'' ++ code /\
    stepD_correct n code'' v ans.

Lemma compile_aexp_correct :
  forall 
    (a:aexp)
    (st:Imp.state)
    (ans:nat)
    (Ha: aeval st a = ans)
    (g:ctxt)
    (f : LLVM Ollvm_ast.value)
    (HComp: compile_aexp g a = f)
    (mem:memory)
    (e:env)
  ,
    LLVM_INV (CPre g e mem st) f (CPost g e mem st ans f).
Proof.
  intros a st ans Ha.
  apply aeval_iff_aevalR in Ha.
  induction Ha; intros g f HComp mem e.
  - subst. simpl.
    eapply llvm_ret_INV.
    intros.
    unfold CPre in H.
    unfold CPost.
    destruct st as [[n m] code].
    split; eauto. unfold llvm_ret. split; eauto.
    exists []. simpl. split; eauto.
    unfold stepD_correct.
    intros CFG fn e0 k mem0 H0.
    exists (mk_pc fn (start n)). exists e0. exists k. exists mem0. exists (dvalue_of_nat ans).
    simpl. split. eapply step_zero. split; eauto.
    split. reflexivity. reflexivity.
  - simpl in HComp.
    unfold_llvm HComp.
    unfold CPre.
    unfold CPost.
    unfold LLVM_INV.
    intros [[n m] code] Hmem.
    destruct (g id).
    simpl in *.
    subst. simpl.
    exists (1 + n, m, I (IId (lid_of_Z n)) (INSTR_Load false i64 (i64ptr, v) None) :: code).
    exists (local (lid_of_Z n)).
    repeat split; auto.
    exists [I (IId (lid_of_Z n)) (INSTR_Load false i64 (i64ptr, v) None)].
    simpl. split; auto.
    unfold stepD_correct.
    intros CFG fn e0 k mem0 H.
    exists (mk_pc fn (start n)).
Abort.
*)    
(*    
    subst. simpl.
    eapply llvm_bind_INV.
    Focus 2.
    intros. 
    eapply llvm_bind_INV.
    Focus 2.
    intros.
    eapply llvm_ret_INV.
    intros.
    unfold CPost.
    destruct st as [[n2 m2] code2].
    split.
*)    

  
Lemma compile_aexp_correct :
  forall 
    (a:aexp)
    (st:Imp.state)
    (ans:nat)
    (HAexp: aeval st a = ans)

    (g:ctxt)
    n0
    n m code
    (Hlt:n0 <= n)
    n' m' code'
    (v : Ollvm_ast.value)
    (Hcomp : compile_aexp g a (n,m,code) = ((n',m',code'),inr v))

    (e:env)
    (k:stack)
    (mem:memory)
    (HM: memory_invariant g e n0 mem st)

  ,
  exists e' u,
     memory_invariant g e' n0 mem st
     /\
     forall
       (CFG : mcfg)
       (fn : function_id)
       (id_start:instr_id),
       exists id_end,
       forall (Hload: code_at CFG fn id_end id_start code'),
    step_star_invariant
      CFG (fun s mem' => s = (mk_pc fn id_end, e',k) /\ mem' = mem)
      (mk_pc fn id_start, e, k) mem

    /\ eval_op e' v = inr u      

    /\ Rv u ans.
Proof.
  intros a st ans HAexp.
  rewrite aeval_iff_aevalR in HAexp.
(*  
  intros g n m code n' m' code' v Hcomp.
  assert (exists code0, code' = code0 ++ code).
  eapply compile_aexp_adds_code. apply Hcomp.
  destruct H as [code0 HeqCode0].
  generalize dependent code0. generalize dependent n'. revert n m code v code' m'. 
*)
  induction HAexp; intros g n0 n m code Hlt n' m' code' v Hcomp e k mem HM.
  Focus 1.
  (* destruct (compile_aexp_monotonic _ _ _ _ _ _ _ _ _ Hcomp) as [Hlt1 [Hlt2 [code1 Heq]]]. *)
    simpl in Hcomp. unfold_llvm Hcomp.
    inversion Hcomp.
    subst. exists e. exists (dvalue_of_nat ans).
    split; auto.
    intros CFG fn id_start. exists id_start.
    split. eapply step_zero; auto. simpl. split. unfold dvalue_of_nat. reflexivity.
    unfold Rv. reflexivity.

  Focus 2.
    
  - simpl in Hcomp;
    unfold_llvm Hcomp;
    specialize IHHAexp1 with (g:=g)(n0:=n0)(n:=n)(m:=m)(code:=code);
    remember (compile_aexp g a1 (n, m, code)) as f;
    destruct f as [[[n1 m1] code1] [err1|v1]];
    try solve [inversion Hcomp];
    lapply IHHAexp1; clear IHHAexp1; [intros IHHAexp1 | auto];
(*    
    apply eq_sym in Heqf.
    assert (exists code11, code1 = code11 ++ code).
    eapply compile_aexp_adds_code. apply Heqf.
    destruct H as [code11 HeqCode11].
*)
    specialize IHHAexp1 with (n':=n1)(m':=m1)(code':=code1)(v:=v1);
    lapply IHHAexp1; clear IHHAexp1; [intros IHHAexp1 | auto];
    specialize IHHAexp1 with (e:=e)(k:=k)(mem:=mem);
    lapply IHHAexp1; clear IHHAexp1; [intros IHHAexp1 | auto];
    destruct IHHAexp1 as [e1 [u1 [HM1 H1]]];

    symmetry in Heqf;
    apply compile_aexp_monotonic in Heqf;
    destruct Heqf as [ltn1 [ltm1 [code1' Heq_code1]]].

    
    specialize IHHAexp2 with (g:=g)(n0:=n0)(n:=n1)(m:=m1)(code:=code1);
    remember (compile_aexp g a2 (n1, m1, code1)) as f2;
    destruct f2 as [[[n2 m2] code2] [err2|v2]];
    try solve [inversion Hcomp];
    lapply IHHAexp2; clear IHHAexp2; [intros IHHAexp2 | omega];
    specialize IHHAexp2 with (n':=n2)(m':=m2)(code':=code2)(v:=v2);
    lapply IHHAexp2; clear IHHAexp2; [intros IHHAexp2 | auto];
    specialize IHHAexp2 with (e:=e1)(k:=k)(mem:=mem);
    lapply IHHAexp2; clear IHHAexp2; [intros IHHAexp2 | auto];
    destruct IHHAexp2 as [e2 [u2 [HM2 H2]]];

    symmetry in Heqf2;
    apply compile_aexp_monotonic in Heqf2;
    destruct Heqf2 as [ltn2 [ltm12[code2' Heq_code2]]].


    simpl in Hcomp.
    inversion Hcomp. clear Hcomp.
    exists ((lid_of_Z n2, dvalue_of_nat (ans1 + ans2))::e2).
    exists (dvalue_of_nat (ans1 + ans2)).
    repeat split.
    eapply memory_invariant_extension; [auto | omega].

    intros.
    specialize H1 with (CFG:=CFG)(fn:=fn)(id_start:=id_start).
    destruct H1 as [id_end1 HA].
    
    Focus 3. 
    subst.
    eapply step_star_invariant_app.
    apply H1. 
      assert ((I (IId (lid_of_Z n2)) (INSTR_Op (SV (OP_IBinop (Add false false) i64 v1 v2))) :: code2' ++ code1' ++ code) = ((I (IId (lid_of_Z n2)) (INSTR_Op (SV (OP_IBinop (Add false false) i64 v1 v2))) :: code2') ++ code1' ++ code)) by reflexivity.
      rewrite H in Hload.
      eapply code_at_append_2. apply Hload.
      intros.  simpl in H. destruct H as [Hseq Hmeq].
      subst.
      eapply step_star_invariant_app.
      eapply H2.

    
    Focus 2.
    + intros CFG fn Hload.
      subst.
      
      

      

                                      

