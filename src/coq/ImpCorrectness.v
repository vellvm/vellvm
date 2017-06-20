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
Require Import Program.



(* Move to Compiler.v *)
Ltac unfold_llvm H :=
  progress (unfold llvm_bind in H; unfold llvm_ret in H; unfold lift in H).

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
  - simpl in Hcomp.
    unfold_llvm Hcomp. simpl in Hcomp.
    inversion Hcomp. repeat split; try omega.
     exists [I (IId (lid_of_Z n1)) (INSTR_Op (SV (OP_IBinop (Add false false) i64 (val_of_int64 i) (val_of_int64 Integers.Int64.zero))))]. simpl; auto.

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
  

Inductive code_at (CFG:mcfg) (f:function_id) (id_start:instr_id) : instr_id -> list elt -> Prop :=
| code_at_nil : code_at CFG f id_start id_start []
| code_at_uid :                         
    forall id i id_next code
      (HF: fetch CFG (mk_pc f id) = Some (Step i id_next))
      (IHC: code_at CFG f id_start id code),
      code_at CFG f id_start id_next ((I id i)::code).
Hint Constructors code_at.
*)
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
(*
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
*)
(* These definitions should probably go in a library *)

(*
Definition dvalue_of_nat (n:nat) : value :=
  DVALUE_I64 (toi64 (Z.of_nat n)).
Hint Unfold dvalue_of_nat.
*)

(* Related final values *)
Definition  Rv (v:value) (i:int64) : Prop :=
    v = DVALUE_I64 i.
Hint Unfold Rv.

(* Life Rv to error terms *)
Inductive Rve : err value -> int64 -> Prop :=
| Rve_inr : forall v i, Rv v i -> Rve (inr v) i.

Lemma lookup_env_hd : forall id dv e, lookup_env (add_env id dv e) id = inr dv.
Proof.
  intros id dv e.  unfold lookup_env. unfold trywith.
  unfold add_env.
  rewrite Util.assoc_hd. reflexivity.
Qed.  

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

Definition memory_invariant (g:ctxt) (e:env) (m:memory) (st:Imp.state) : Prop :=
  forall x v, g x = Some v ->
         exists n, (v = (local (lid_of_Z n)) /\
               exists a, (lookup_env e (lid_of_Z n) = inr (DVALUE_Addr a) /\
                     Rv (nth_default undef m a) (st x))).

Inductive env_lt (n:int) : env -> Prop :=
| env_lt_nil : env_lt n []
| env_lt_cons : forall e m dv, m < n -> env_lt n e -> env_lt n (add_env_Z m dv e)
.                                                        

Lemma env_lt_lookup_inv :
  forall n n' e v
    (Henv: env_lt n e)
    (Hl: lookup_env e (lid_of_Z n') = inr v),
    n' < n.
Proof.
  intros n n' e v Henv.
  revert n' v.
  unfold lookup_env. unfold trywith. unfold raise. 
  induction Henv; intros n' v Hl.
  - simpl in Hl. inversion Hl.
  - unfold add_env_Z in Hl. unfold add_env in Hl.
    unfold Util.assoc in Hl.
    destruct (RawID.eq_dec (lid_of_Z n') (lid_of_Z m)).

    Focus 2.
    eapply IHHenv.
    fold (@Util.assoc raw_id) in Hl.
    destruct (Util.assoc RawID.eq_dec (lid_of_Z n') e).
    exact Hl.
    inversion Hl.

    (* string_of n = string_of m -> n = m *)
    unfold lid_of_Z in e0.
Admitted.


Lemma memory_invariant_extension : forall g e n mem st n' dv,
    env_lt n e ->
    n <= n' ->
  memory_invariant g e mem st -> 
  memory_invariant g (add_env_Z n' dv e) mem st.
Proof.
  intros g e n mem st n' dv Henv Hlt Hmem.
  unfold memory_invariant in *.
  intros x v Hg.
  apply Hmem in Hg. clear Hmem.
  destruct Hg as [n0 [Hv [a [Ha Hrv]]]].
  exists n0. split; auto.
  exists a. eapply env_lt_lookup_inv with (n':=n0) in Henv.
  split; auto. apply lookup_env_tl. apply lid_of_Z_inj.
  unfold not. intros. subst. omega. auto. exact Ha.
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
                                  

Inductive straightline_code : list elt -> code -> Prop :=
| slc_nil : straightline_code [] []
| slc_cons : forall id i tl cd,
    straightline_code tl cd ->
    straightline_code ((I id i)::tl) ((id, i)::cd)
.
Hint Constructors straightline_code.

Lemma straightline_code_app : forall x1 cd1 x2 cd2,
    straightline_code x1 cd1 ->
    straightline_code x2 cd2 ->
    straightline_code (x1++x2) (cd1++cd2).
Proof.
  intros x1 cd1 x2 cd2 H.
  revert x2 cd2.
  induction H; intros x2 cd2 H0; auto. 
  simpl. apply slc_cons. eapply IHstraightline_code. exact H0.
Qed.  

Definition slc_pc fn bid phis term cd :=
  mk_pc fn (mk_block bid phis cd term).

Lemma step_star_invariant_app2 :
  forall CFG fn bid phis term,
    let slc := slc_pc fn bid phis term in
    forall R1 cd1 mem0 e0 k0
      (HS1 : step_star_invariant CFG R1 ((slc cd1), e0, k0) mem0)
      R2 cd2
      (HR1 : forall st1 mem1, R1 st1 mem1 -> pc_of st1 = (slc []) /\
                                          step_star_invariant CFG R2 ((slc cd2), env_of st1, stack_of st1) mem1),
    step_star_invariant CFG R2 (slc (cd1++cd2), e0, k0) mem0.
Proof.
  intros CFG fn0 bid phis term slc R1 cd1.
  induction cd1; intros mem0 e0 k0 HS1 R2 cd2 HR1.
  - simpl in *. unfold slc in HS1. unfold slc_pc in HS1. 
    + simpl.
Admitted.        
  
(*                                                   
                      

  step_star_invariant R1 (slc_pc fn bid phis 
                         , e, k) mem 
                      


  step_star_invariant R (mk_pc fn
                               {
                                 blk_id = id;
                                 blk_phis = phis;
                                 blk_code = cd1 ++ cd2;
                                 blk_term = term;
                               }



                         , e, k) mem 
*)
  
Definition finish_pc (p:pc) : pc :=
  let 'mk_pc f b := p in
  mk_pc f
  {| blk_id := blk_id b;
    blk_phis := [];
    blk_code := List.tl (blk_code b);
    blk_term := blk_term b;
  |}.


Definition env_extends (e e':env) : Prop :=
  forall op dv, eval_op e op = inr dv -> eval_op e' op  = inr dv.

Lemma env_extends_lt :
  forall e n n' dv
    (Henv: env_lt n e)
    (Hlt: n <= n'),
    env_extends e (add_env_Z n' dv e).
Proof.
  intros e n n' dv Henv Hlt.
  unfold env_extends.
  intros op dv' Hev.
  generalize dependent n.
  revert n' dv.
  destruct op as [op].
  induction op; simpl in *; try inversion Hev; intros; subst; auto.
  - destruct id; simpl in *; inversion H0.
    unfold add_env_Z.
    destruct (RawID.eq_dec (lid_of_Z n') id).
    + subst. assert (n' < n). eapply env_lt_lookup_inv. apply Henv. apply H1.
      rewrite H1.
      apply lookup_env_tl.
      apply lid_of_Z_inj. omega.
      exact H1.
    + rewrite H1.
      apply lookup_env_tl; auto.
  -
    (* maybe cut down on cases from eval_expr to simplify for now. *)
Admitted.    
    
    

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
    /\ straightline_code cd_a c_a
    /\ forall
    (e:env)
    (mem:memory) (n0:int)  (Hlt:n0 <= n)
    (HM: memory_invariant g e mem st)
    (k:stack)
    (CFG : mcfg)
    (fn : function_id)
    (bid: block_id)
    phis term,
      step_star_invariant
        CFG
        (fun s' mem' =>
           let '(pc', e', k') := s' in
           pc' = slc_pc fn bid phis term [] /\
           memory_invariant g e' mem' st /\
           Rve (eval_op e' v) ans /\
           env_extends e e'
        )
        (slc_pc fn bid phis term (List.rev c_a), e, k) mem.
      
    exists (e':env) (u:dvalue), 
      step_star_invariant
        CFG
        (fun s mem' => s = (slc_pc fn bid phis term [], e',k) /\ mem' = mem)
        (slc_pc fn bid phis term (List.rev c_a), e, k) mem

       /\ memory_invariant g e' n0 mem st
       /\ eval_op e' v = inr u      
       /\ Rv u ans
       /\ forall op w, eval_op e op = inr w -> eval_op e' op = inr w.
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
  induction HAexp; intros g n m cd n' m' cd' v Hcomp.
  - simpl in Hcomp. unfold_llvm Hcomp. simpl in Hcomp.
    inversion Hcomp. clear Hcomp.
    exists [I (IId (lid_of_Z n))
         (INSTR_Op (SV (OP_IBinop (Add false false) i64 (val_of_int64 ans) (val_of_int64 Integers.Int64.zero))))].   exists [((IId (lid_of_Z n)),
         (INSTR_Op (SV (OP_IBinop (Add false false) i64 (val_of_int64 ans) (val_of_int64 Integers.Int64.zero)))))].
    repeat split; auto.
    intros e mem n0 Hlt Hmem.
    exists (add_env (lid_of_Z n) (DVALUE_I64 ans) e).
    exists (DVALUE_I64 ans).
    simpl.
    repeat split; auto.
    +  eapply step_tau. simpl. eauto.
       eapply step_zero. split; auto.
       repeat rewrite Int64.repr_signed. rewrite Int64.add_zero. reflexivity.
    + eapply memory_invariant_extension; eauto.
    + eapply lookup_env_hd.

  - simpl in Hcomp. unfold_llvm Hcomp.
    unfold trywith in Hcomp.
    remember (g id) as X.
    destruct X; simpl in Hcomp; try inversion Hcomp.
    clear Hcomp.
    exists [I (IId (lid_of_Z n)) (INSTR_Load false i64 (i64ptr, v0) None)].
    exists [(IId (lid_of_Z n), (INSTR_Load false i64 (i64ptr, v0) None))].
    simpl. repeat split; auto.
    intros e mem n0 Hlt Hmem k CFG fn bid phis term.
    destruct Hmem with (x:=id)(v:=v0) as [n1 [Hlt1 [Hv [a [Hlookup HRa]]]]]; auto.
    exists (add_env (lid_of_Z n) (nth_default undef mem a) e).
    exists (DVALUE_I64 (s id)). subst. 
    repeat split; auto.
      + subst. simpl. 
        eapply step_eff. simpl.
        rewrite Hlookup. simpl. eauto.
        simpl. eauto.
        simpl. eapply step_zero. simpl. split; auto.
      + eapply memory_invariant_extension; eauto.
      + rewrite lookup_env_hd.
        inversion HRa as [H]. rewrite H.  reflexivity.
        
  - simpl in Hcomp;
    unfold_llvm Hcomp;
    specialize IHHAexp1 with (g:=g)(n:=n)(m:=m)(cd:=cd).
    remember (compile_aexp g a1 (n, m, cd)) as f;
    destruct f as [[[n1 m1] cd1] [err1|v1]];
    try solve [inversion Hcomp].
    specialize IHHAexp1 with (n':=n1)(m':=m1)(cd':=cd1)(v:=v1).
    lapply IHHAexp1; clear IHHAexp1; [intros IHHAexp1 | auto].
    destruct IHHAexp1 as [cd_a1 [c_a1 [Hcd_eq1 [HSlc1 IHHAexp1]]]].

    symmetry in Heqf;
    apply compile_aexp_monotonic in Heqf;
    destruct Heqf as [ltn1 [ltm1 [cd1' Heq_cd1]]].

    
    specialize IHHAexp2 with (g:=g)(n:=n1)(m:=m1)(cd:=cd1).
    remember (compile_aexp g a2 (n1, m1, cd1)) as f2;
    destruct f2 as [[[n2 m2] cd2] [err2|v2]];
    try solve [inversion Hcomp].
    specialize IHHAexp2 with (n':=n2)(m':=m2)(cd':=cd2)(v:=v2).
    lapply IHHAexp2; clear IHHAexp2; [intros IHHAexp2 | auto].
    destruct IHHAexp2 as [cd_a2 [c_a2 [Hcd_eq2 [HSlc2 IHHAexp2]]]].

    symmetry in Heqf2;
    apply compile_aexp_monotonic in Heqf2;
    destruct Heqf2 as [ltn2 [ltm2 [cd2' Heq_cd2]]].


    simpl in Hcomp.
    inversion Hcomp. clear Hcomp.

    subst.
    exists (I (IId (lid_of_Z n2)) (INSTR_Op (SV (OP_IBinop (Add false false) i64 v1 v2)))::cd2' ++ cd1').
    exists (((IId (lid_of_Z n2)),(INSTR_Op (SV (OP_IBinop (Add false false) i64 v1 v2))))::c_a2 ++ c_a1).
    simpl. repeat split.
    + rewrite app_assoc. reflexivity.
    + apply slc_cons. apply straightline_code_app; auto.
      apply app_inv_tail in Hcd_eq2. rewrite Hcd_eq2. auto.
      apply app_inv_tail in Hcd_eq1. rewrite Hcd_eq1. auto.
    + intros e mem n0 Hlt0 Hmem k CFG fn bid phis term.
      
      specialize IHHAexp1 with (e:=e)(mem:=mem)(n0:=n0).
      lapply IHHAexp1; clear IHHAexp1; [intros IHHAexp1 | auto].
      lapply IHHAexp1; clear IHHAexp1; [intros IHHAexp1 | auto].
      destruct IHHAexp1 with (k:=k)(CFG:=CFG)(fn:=fn)(bid:=bid)(phis:=phis)(term:=term)
        as [e1 [u1 [HS1 [Hmem1 [Heval1 HRv1]]]]].
      clear IHHAexp1.

      specialize IHHAexp2 with (e:=e1)(mem:=mem)(n0:=n0).
      lapply IHHAexp2; clear IHHAexp2; [intros IHHAexp2 | auto].
      lapply IHHAexp2; clear IHHAexp2; [intros IHHAexp2 | auto].
      destruct IHHAexp2 with (k:=k)(CFG:=CFG)(fn:=fn)(bid:=bid)(phis:=phis)(term:=term)
        as [e2 [u2 [HS2 [Hmem2 [Heval2 HRv2]]]]].
      clear IHHAexp2.

      exists (add_env (lid_of_Z n2) (DVALUE_I64 (Int64.add ans1 ans2)) e2). exists (DVALUE_I64 (Int64.add ans1 ans2)).
      repeat split.
      * rewrite rev_app_distr. eapply step_star_invariant_app2.
        eapply step_star_invariant_app2.
        apply HS1.
        intros.
        simpl in H. destruct H as [Hst1 Hmem1eq].
        subst. simpl.
        split. reflexivity.
        apply HS2.
        intros.
        simpl in H. destruct H as [Hst2 Hmem2eq].
        subst.
        simpl. split. reflexivity.
        eapply step_tau. simpl. rewrite Heval2. inversion HRv2. subst.
        unfold slc_pc.
      
      
      
      

      

                                      

