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
Require Import Vellvm.Ollvm_ast Vellvm.Compiler Vellvm.AstLib Vellvm.CFG Vellvm.StepSemantics Vellvm.Memory.
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
    inversion Hcomp. repeat split; try omega.
    exists [I (IId (lid_of_Z n1)) (INSTR_Op (SV (OP_IBinop (Add false false) i64 (val_of_int64 i) (val_of_int64 Integers.Int64.zero))))].
    simpl; auto.

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


(* StepSemanticsProp.v *)
Lemma lookup_env_hd : forall id dv e, lookup_env (add_env id dv e) id = Some dv.
Proof.
  intros id dv e.  unfold lookup_env. 
  unfold add_env.
  rewrite Util.assoc_hd. reflexivity.
Qed.  

(* StepSemanticsProp.v *)
Lemma lookup_env_tl : forall id1 v1 e id2,
    id1 <> id2 -> lookup_env (add_env id1 v1 e) id2 = lookup_env e id2.
Proof.
  unfold lookup_env.
  intros id1 v1 e id2 H.
  unfold add_env. 
  rewrite Util.assoc_tl; auto.
Qed.  

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

(* StepSemanticsProp.v *)
Lemma lookup_add_env_inv :
  forall id1 v e id2 u
    (Hl: lookup_env (add_env id1 v e) id2 = Some u),
    (id1 = id2 /\ v = u) \/ (lookup_env e id2 = Some u).
Proof.
  intros id1 v e id2 u Hl.
  unfold add_env in Hl.
  unfold lookup_env in Hl.
  remember (Util.assoc RawID.eq_dec id2 ((id1, v)::e)) as res.
  destruct res; simpl in Hl; try solve [inversion Hl].
  symmetry in Heqres.
  apply Util.assoc_cons_inv in Heqres.
  destruct Heqres as [[H1 H2]|[H1 H2]]. subst; auto.
  (* destruct (@Util.assoc_cons_inv raw_id value id2 id1 v v0 e RawID.eq_dec)  *)
  inversion Hl. tauto. 
  right. inversion Hl. subst. unfold lookup_env. exact H2.
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
    destruct (lookup_add_env_inv (lid_of_Z m) dv e (lid_of_Z n') v) as [[H1 H2]|H1]. assumption.
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

(* StepSemanticsProp.v *)
Inductive is_Op : instr -> Prop :=
| is_Op_intro : forall v, is_Op (INSTR_Op v)
.
Hint Constructors is_Op.

(* StepSemanticsProp.v *)
Inductive is_Eff : instr -> Prop :=
| is_Alloca : forall t nb a, is_Eff (INSTR_Alloca t nb a)
| is_Load : forall v t p a, is_Eff (INSTR_Load v t p a)
| is_Store : forall v val p a, is_Eff (INSTR_Store v val p a)
.
Hint Constructors is_Eff.

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

(*
  Runs a piece of straight code from some starting state to arrive at a state satisfying R.
  Note: there may be more straightline code available to continue with, unless
        fetch (pc_of s) = []
*)
Inductive step_code (CFG:mcfg) (R : SS.state -> memory -> Prop) : code -> SS.state -> memory -> Prop :=
| step_zero :
    forall s m
      (HR : R s m),
      step_code CFG R [] s m
    
| step_tau :
    forall id i cd s s' m
      (Hi : is_Op i)
      (Hpc : pc_prefix (pc_of s) ((id,i)::cd))
      (HS :  stepD CFG s = Step s')
      (Hstep : step_code CFG R cd s' m),
      step_code CFG R ((id,i)::cd) s m

| step_eff :
    forall id i cd s e m m' v k
      (Hi : is_Eff i)
      (Hpc : pc_prefix (pc_of s) ((id,i)::cd))
      (HS : stepD CFG s = Obs (Eff e))
      (HM : mem_step e m = inr (m', v, k))
      (Hstep : step_code CFG R cd (k v) m'),
      step_code CFG R ((id,i)::cd) s m
.

(* AstProp.v *)
Definition slc_pc fn bid phis term cd :=
  mk_pc fn (mk_block bid phis cd term).

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

(* StepSemanticsProp.v *)
Lemma stepD_Op_inversion :
  forall CFG fn bid phis term,
    let slc := slc_pc fn bid phis term in
    forall cd1 e1 k1 id i pc2 e2 k2 
      (Hi: is_Op i)
      (HS1 : stepD CFG (slc ((id,i)::cd1), e1, k1) = Step (pc2, e2, k2)),
      pc2 = slc cd1.
Proof.
  intros CFG fn0 bid phis term slc cd1 e1 k1 id i pc2 e2 k2 Hi HS1.
  inversion Hi.
  subst.
  simpl in HS1.
  destruct id; simpl in *.
  destruct (eval_op e1 None v); inversion HS1; auto.
  inversion HS1.
Qed.

(* StepSemanticsProp.v *)
Lemma stepD_Eff_weakening :
  forall CFG fn bid phis term,
    let slc := slc_pc fn bid phis term in
    forall cd1 e1 k1 id i eff
      (Hi: is_Eff i)
      (HS1 : stepD CFG (slc ((id,i)::cd1), e1, k1) = Obs (Eff eff))
      cd2,
      stepD CFG (pc_app (slc ((id,i)::cd1)) cd2, e1, k1) = Obs (Eff (fmap (fun st => (pc_app (pc_of st) cd2, env_of st, stack_of st)) eff)).
Proof.
  intros CFG fn0 bid phis term slc cd1 e1 k1 id i eff Hi HS1 cd2.
  inversion Hi; subst; simpl in HS1; destruct id; simpl in *; inversion HS1; simpl.
  - reflexivity.
  - destruct p as [u ptr]; destruct (eval_op e1 (Some u) ptr).  simpl in HS1. inversion HS1. simpl in HS1.
    destruct v0; try solve [inversion HS1].
    simpl in *. inversion HS1.
    reflexivity.
  - destruct val as [t val]; destruct p as [u p].
    destruct (eval_op e1 (Some t) val); try solve [inversion HS1].
    destruct (eval_op e1 (Some u) p); try solve [inversion HS1].
    simpl in *.
    destruct v1; try solve [inversion HS1].
    inversion HS1.
    reflexivity.
Qed.    

(* StepSemanticsProp.v *)
Lemma stepD_Eff_Alloca_inversion :
  forall CFG fn bid phis term,
    let slc := slc_pc fn bid phis term in
    forall cd e k id t nb al eff
      (HS1 : stepD CFG (slc ((id,INSTR_Alloca t nb al)::cd), e, k) = Obs (Eff eff)),
    exists lid,
      id = IId lid /\
      eff = Alloca t (fun (a:value) => (slc cd, add_env lid a e, k)).
Proof.
  intros CFG fn0 bid phis term slc cd e k id t nb al eff HS1.
  simpl in HS1.
  inversion HS1.
  destruct id as [lid | lv].
  exists lid. split; auto. inversion H0.
  reflexivity.
  inversion H0.
Qed.

(* StepSemanticsProp.v *)
Lemma stepD_Eff_Load_inversion :
  forall CFG fn bid phis term,
    let slc := slc_pc fn bid phis term in
    forall cd e k id v t p al eff
      (HS1 : stepD CFG (slc ((id,INSTR_Load v t p al)::cd), e, k) = Obs (Eff eff)),
    exists lid a, 
      id = IId lid /\
      eff = (Load a (fun dv => (slc cd, add_env lid dv e, k))).
Proof.
  intros CFG fn0 bid phis term slc cd e k id v t p al eff HS1. 
  simpl in HS1.
  inversion HS1.
  destruct id as [lid | lv].
  exists lid.
  destruct p as [u p].
  destruct (eval_op e (Some u) p); try solve [inversion H0].
  destruct v0; try solve [inversion H0].
  simpl in H0.
  exists a. split; auto. inversion H0. reflexivity.
  inversion HS1.
Qed.

(* StepSemanticsProp.v *)
Lemma stepD_Eff_Store_inversion :
  forall CFG fn bid phis term,
    let slc := slc_pc fn bid phis term in
    forall cd e k id v val p al eff
      (HS1 : stepD CFG (slc ((id,INSTR_Store v val p al)::cd), e, k) = Obs (Eff eff)),
    exists vid a dv, 
      id = IVoid vid /\
      eff = (Store a dv (fun _ => (slc cd, e, k))).
Proof.
  intros CFG fn0 bid phis term slc cd e k id v val p al eff HS1. 
  simpl in HS1.
  destruct id as [lid | lvid].
  - inversion HS1.
  - exists lvid.
    destruct val as [u val].
    destruct p as [w p].
    destruct (eval_op e (Some u) val); try solve [inversion HS1].
    destruct (eval_op e (Some w) p); try solve [inversion HS1].
    simpl in HS1.
    destruct v1; try solve [inversion HS1].
    exists a. exists v0. inversion HS1.
     subst. split; auto.
Qed.

(* StepSemanticsProp.v *)
Lemma stepD_Op_weakening :
  forall CFG fn bid phis term,
    let slc := slc_pc fn bid phis term in
    forall id i cd1 e1 k1 pc2 e2 k2
    (Hi : is_Op i)
    (HS : stepD CFG (slc ((id,i)::cd1), e1, k1) = Step (pc2, e2, k2))
    cd2,
    stepD CFG (pc_app (slc ((id,i)::cd1)) cd2, e1, k1) = Step (pc_app pc2 cd2, e2, k2).
Proof.
  intros CFG fn0 bid phis term slc id i cd1 e1 k1 pc2 e2 k2 Hi HS cd2.
  inversion Hi.
  subst.
  simpl in HS.
  destruct id; simpl in *.
  destruct (eval_op e1 None v); inversion HS; auto.
  inversion HS.
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

Lemma env_extends_monad_app_snd :
   forall e dv n t a (tv:Ollvm_ast.typ) (v:Ollvm_ast.value)
    (H :forall (t : option typ) (a : value),
        eval_op e t v = inr a -> eval_op (add_env_Z n dv e) t v = inr a),
    monad_app_snd (eval_op e t) (tv, v) = inr a ->
    monad_app_snd (eval_op (add_env_Z n dv e) t) (tv, v) = inr a.
Proof.
  intros. simpl in *.
  
  destruct (eval_op e t v) eqn:He. inversion H0.
  inversion H0. subst. apply H in He. rewrite He; reflexivity.
Qed.
  
Lemma env_extends_map_monad :
  forall e dv n fields t a
    (H : forall p : Ollvm_ast.typ * Ollvm_ast.value,
        In p fields ->
        forall (t : option typ) (a : value),
          eval_op e t (snd p) = inr a -> eval_op (add_env_Z n dv e) t (snd p) = inr a),
    map_monad (monad_app_snd (eval_op e t)) fields = inr a ->
    map_monad (monad_app_snd (eval_op (add_env_Z n dv e) t)) fields = inr a.
Proof.
  induction fields; intros; simpl in *; try assumption.
  
  destruct (monad_app_snd (eval_op e t) a) eqn:Hm1. inversion H0.
  destruct (map_monad (monad_app_snd (eval_op e t)) fields) eqn:Hm2. inversion H0.

  assert (forall p, In p fields ->
      forall (t0 : option typ) (a0 : value),
              eval_op e t0 (snd p) = inr a0 -> eval_op (add_env_Z n dv e) t0 (snd p) = inr a0).
  intros. apply H; try right; assumption.

  destruct a.
  
  assert (monad_app_snd (eval_op (add_env_Z n dv e) t) (t0, v) = inr p).
  { apply env_extends_monad_app_snd.
    - specialize H with (p:=(t0, v)). apply H. left; reflexivity.
    - assumption. }

  eapply IHfields in H1.
  - rewrite <- H0. rewrite H1.
    inversion H0. rewrite H2. reflexivity.
  - assumption.
Qed. 
  
Lemma env_extends_lt :
  forall e n dv
    (Henv: env_lt n e),
    env_extends e (add_env_Z n dv e).
Proof. 
  intros e n dv Henv o.
  induction o using value_ind'; simpl in *; try inversion Hev; intros; subst; auto.
  - destruct id; try solve [inversion H].
    unfold eval_expr in *. simpl in *.
    unfold add_env_Z. rewrite lookup_env_tl. 
    destruct (lookup_env e id); inversion H; auto.
  (* <> should be symmetric! *)
    unfold not. intros. symmetry in H0. eapply env_lt_lookup_neq in H0; eauto.
    destruct (lookup_env e id); inversion H; auto.
    
  - unfold eval_expr in *. simpl in *. 
    destruct (map_monad (monad_app_snd (eval_op e t)) fields) eqn:Hm. inversion H0.
    eapply env_extends_map_monad in H. rewrite H. rewrite H0. reflexivity.
    assumption.
  - unfold eval_expr in *. simpl in *. 
    destruct (map_monad (monad_app_snd (eval_op e t)) fields) eqn:Hm. inversion H0.
    eapply env_extends_map_monad in H. rewrite H. rewrite H0. reflexivity.
    assumption.
  - unfold eval_expr in *. simpl in *. 
    destruct (map_monad (monad_app_snd (eval_op e t)) elts) eqn:Hm. inversion H0.
    eapply env_extends_map_monad in H. rewrite H. rewrite H0. reflexivity.
    assumption.
  - unfold eval_expr in *. simpl in *. 
    destruct (map_monad (monad_app_snd (eval_op e t)) elts) eqn:Hm. inversion H0.
    eapply env_extends_map_monad in H. rewrite H. rewrite H0. reflexivity.
    assumption.
  - unfold eval_expr in *. simpl in *.
    destruct (eval_op e (Some t) o1) eqn:He1; try solve [inversion H].
    destruct (eval_op e (Some t) o2) eqn:He2; try solve [inversion H].
    erewrite IHo1; try solve [reflexivity].
    erewrite IHo2; try solve [reflexivity].
    exact H. auto. auto.    
  - unfold eval_expr in *. simpl in *.
    destruct (eval_op e (Some t) o1) eqn:He1; try solve [inversion H].
    destruct (eval_op e (Some t) o2) eqn:He2; try solve [inversion H].
    erewrite IHo1; try solve [reflexivity].
    erewrite IHo2; try solve [reflexivity].
    exact H. auto. auto.
  - unfold eval_expr in *. simpl in *.
    destruct (eval_op e (Some t) o1); try solve [inversion H].
    destruct (eval_op e (Some t) o2); try solve [inversion H].
  - unfold eval_expr in *. simpl in *.
    destruct (eval_op e (Some t) o1); try solve [inversion H].
    destruct (eval_op e (Some t) o2); try solve [inversion H].
  - unfold eval_expr in *. simpl in *.
    destruct (eval_op e (Some t_from) o) eqn:He; try solve [inversion H].
    erewrite  IHo; try solve [reflexivity].
    apply H. auto.
  - unfold eval_expr in *. simpl in *. 
    destruct (monad_app_snd (eval_op e (Some t)) ptrval) eqn:Hm1. inversion H0.    
    destruct ptrval eqn:Hptrval.
    eapply env_extends_monad_app_snd with (a:=p) in IHo. rewrite IHo.
    destruct (map_monad (monad_app_snd (eval_op e (Some (TYPE_I 32)))) idxs) eqn:Hm2.
    inversion H0.
    eapply env_extends_map_monad in H. rewrite H. assumption.
    apply Hm2.
    assumption.
  - destruct vec. unfold eval_expr in *. simpl in *.
    destruct (eval_op e (Some t0) v) eqn:He1. inversion H.
    apply IHo in He1.
    induction idxs; rewrite He1; auto.
Qed.

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
    /\ straight c_a
    /\ forall
    (e:env)
    (mem:memory) (Hlt:env_lt n e)
    (HM: memory_invariant g e mem st)
    (k:stack)
    (CFG : mcfg) (fn : function_id) (bid: block_id) phis term,
      step_code
        CFG
        (fun s' mem' =>
           let '(pc', e', k') := s' in
           pc' = slc_pc fn bid phis term [] /\
           memory_invariant g e' mem' st /\
           Rv64e (eval_op e' (Some (TYPE_I 64)) v) ans /\
           env_extends e e' /\
           env_lt n' e'
        )
        (List.rev c_a)
        (slc_pc fn bid phis term (List.rev c_a), e, k) mem.
Proof.
  intros a st ans HAexp.
  rewrite aeval_iff_aevalR in HAexp.

  induction HAexp; intros g n m cd n' m' cd' v Hcomp; unfold_llvm Hcomp.
  - inversion_clear Hcomp. 
    exists [I (IId (lid_of_Z n))
         (INSTR_Op (SV (OP_IBinop (Add false false) i64 (val_of_int64 ans) (val_of_int64 Integers.Int64.zero))))].
    exists [((IId (lid_of_Z n)),
         (INSTR_Op (SV (OP_IBinop (Add false false) i64 (val_of_int64 ans) (val_of_int64 Integers.Int64.zero)))))].
    repeat split; auto.
    * repeat econstructor.
    
    * intros e mem Hlt HM k CFG fn0 bid phis term. 
      eapply step_tau; auto.
      apply pc_prefix_id.
      eapply step_zero. repeat split; auto.
    + eapply memory_invariant_extension; eauto; try omega.
    + simpl. unfold eval_expr. simpl. rewrite lookup_env_hd.
      repeat rewrite Int64.repr_signed. rewrite Int64.add_zero. auto.
    + eapply env_extends_lt. apply Hlt. 
    + apply env_lt_cons; [omega | eapply env_lt_weaken; eauto; omega].

  - unfold trywith in Hcomp.
    remember (g id) as X.
    destruct X; simpl in Hcomp; inversion_clear Hcomp.
    exists [I (IId (lid_of_Z n)) (INSTR_Load false i64 (i64ptr, v0) None)].
    exists [(IId (lid_of_Z n), (INSTR_Load false i64 (i64ptr, v0) None))].
    simpl. repeat split; auto.
    * apply straight_Eff; auto; econstructor.
    * intros e mem Hlt HM k CFG fn0 bid phis term.
     destruct HM with (x:=id)(v:=v0) as [n1 [Hlt1 [a [Hlookup HRa]]]]; auto.
     eapply step_eff; auto.
    + apply pc_prefix_id.
    + subst; simpl; unfold eval_expr; simpl; rewrite Hlookup; simpl;  eauto.
    + eauto.
    + eapply step_zero.
      repeat split; auto.
      -- eapply memory_invariant_extension; eauto. 
      -- unfold eval_expr; simpl; rewrite lookup_env_hd; auto.
      -- eapply env_extends_lt; eauto. 
      -- apply env_lt_cons; [omega | eapply env_lt_weaken; eauto; omega].
        
  - simpl in Hcomp;
    unfold_llvm Hcomp;
    specialize IHHAexp1 with (g:=g)(n:=n)(m:=m)(cd:=cd).
    remember (compile_aexp g a1 (n, m, cd)) as f.
    destruct f as [[[n1 m1] cd1] [err1|v1]];
    try solve [inversion Hcomp].
    specialize IHHAexp1 with (n':=n1)(m':=m1)(cd':=cd1)(v:=v1).
    lapply IHHAexp1; clear IHHAexp1; [intros IHHAexp1 | auto].
    destruct IHHAexp1 as [cd_a1 [c_a1 [Hcd_eq1 [Hcc1 [HSlc1 IHHAexp1]]]]].

    symmetry in Heqf;
    apply compile_aexp_monotonic in Heqf;
    destruct Heqf as [ltn1 [ltm1 [cd1' Heq_cd1]]].

    
    specialize IHHAexp2 with (g:=g)(n:=n1)(m:=m1)(cd:=cd1).
    remember (compile_aexp g a2 (n1, m1, cd1)) as f2;
    destruct f2 as [[[n2 m2] cd2] [err2|v2]];
    try solve [inversion Hcomp].
    specialize IHHAexp2 with (n':=n2)(m':=m2)(cd':=cd2)(v:=v2).
    lapply IHHAexp2; clear IHHAexp2; [intros IHHAexp2 | auto].
    destruct IHHAexp2 as [cd_a2 [c_a2 [Hcd_eq2 [Hcc2 [HSlc2 IHHAexp2]]]]].

    symmetry in Heqf2;
    apply compile_aexp_monotonic in Heqf2;
    destruct Heqf2 as [ltn2 [ltm2 [cd2' Heq_cd2]]].


    simpl in Hcomp.
    inversion Hcomp. clear Hcomp.

    subst.
    exists (I (IId (lid_of_Z n2)) (INSTR_Op (SV (OP_IBinop (Add false false) i64 v1 v2)))::cd2' ++ cd1').
    exists (((IId (lid_of_Z n2)),(INSTR_Op (SV (OP_IBinop (Add false false) i64 v1 v2))))::c_a2 ++ c_a1).
    simpl. repeat split; auto.
    + rewrite app_assoc. reflexivity.
    + apply cc_cons_Op. apply compiled_code_app; auto.
      apply app_inv_tail in Hcd_eq2. rewrite Hcd_eq2. auto.
      apply app_inv_tail in Hcd_eq1. rewrite Hcd_eq1. auto.
    + apply straight_Op; auto. apply straight_app; auto.
    + intros e mem Hlt Hmem k CFG fn bid phis term.
      rewrite rev_app_distr.
      specialize IHHAexp1 with (e:=e)(mem:=mem).
      lapply IHHAexp1; clear IHHAexp1; [intros IHHAexp1 | auto].
      lapply IHHAexp1; clear IHHAexp1; [intros IHHAexp1 | auto].
      specialize IHHAexp1 with (k:=k)(CFG:=CFG)(fn:=fn)(bid:=bid)(phis:=phis)(term:=term).

      rewrite <- app_assoc.
      eapply step_code_app. apply IHHAexp1. clear IHHAexp1.
      intros st1 mem1 H. 
      destruct st1 as [[pc1 e1] k1].
      destruct H as [Hpc1 [Hmem1 [Hr1 [He1 Hlte1]]]].
      split; subst; auto.

      specialize IHHAexp2 with (e:=e1)(mem:=mem1).
      lapply IHHAexp2; clear IHHAexp2; [intros IHHAexp2 | auto].
      lapply IHHAexp2; clear IHHAexp2; [intros IHHAexp2 | auto].
      specialize IHHAexp2 with (k:=k1)(CFG:=CFG)(fn:=fn)(bid:=bid)(phis:=phis)(term:=term).

      simpl.
      rewrite pc_app_slc. simpl.
      eapply step_code_app.
      apply IHHAexp2.
      intros st2 mem2 H2.
      destruct st2 as [[pc2 e2] k2].
      destruct H2 as [Hpc2 [Hmem2 [Hr2 [He2 Hlte2]]]].
      split; subst; auto.
      
      eapply step_tau; auto.
      * simpl. unfold pc_app. simpl. apply pc_prefix_id.
      * simpl.
        inversion Hr1. subst. inversion Hr2. subst.
        symmetry in H.
        assert (eval_op e2 (Some (TYPE_I 64)) v1 = inr v).
        apply He2; auto.
        simpl.
        unfold eval_expr. simpl. unfold i64.
        rewrite H3. rewrite <- H1. simpl.
        inversion H0. inversion H2. simpl.
        eauto.
      * simpl. eapply step_zero.
        repeat split; auto.
        ++ eapply memory_invariant_extension; eauto. 
        ++ unfold eval_expr; simpl; rewrite lookup_env_hd; auto.
        ++ eapply env_extends_trans. apply He1.
           eapply env_extends_trans. apply He2.
           eapply env_extends_lt. apply Hlte2. 
        ++ apply env_lt_cons. omega. eapply env_lt_weaken; eauto. omega.

  - simpl in Hcomp;
    unfold_llvm Hcomp;
    specialize IHHAexp1 with (g:=g)(n:=n)(m:=m)(cd:=cd).
    remember (compile_aexp g a1 (n, m, cd)) as f;
    destruct f as [[[n1 m1] cd1] [err1|v1]];
    try solve [inversion Hcomp].
    specialize IHHAexp1 with (n':=n1)(m':=m1)(cd':=cd1)(v:=v1).
    lapply IHHAexp1; clear IHHAexp1; [intros IHHAexp1 | auto].
    destruct IHHAexp1 as [cd_a1 [c_a1 [Hcd_eq1 [Hcc1 [HSlc1 IHHAexp1]]]]].

    symmetry in Heqf;
    apply compile_aexp_monotonic in Heqf;
    destruct Heqf as [ltn1 [ltm1 [cd1' Heq_cd1]]].

    
    specialize IHHAexp2 with (g:=g)(n:=n1)(m:=m1)(cd:=cd1).
    remember (compile_aexp g a2 (n1, m1, cd1)) as f2;
    destruct f2 as [[[n2 m2] cd2] [err2|v2]];
    try solve [inversion Hcomp].
    specialize IHHAexp2 with (n':=n2)(m':=m2)(cd':=cd2)(v:=v2).
    lapply IHHAexp2; clear IHHAexp2; [intros IHHAexp2 | auto].
    destruct IHHAexp2 as [cd_a2 [c_a2 [Hcd_eq2 [Hcc2 [HSlc2 IHHAexp2]]]]].

    symmetry in Heqf2;
    apply compile_aexp_monotonic in Heqf2;
    destruct Heqf2 as [ltn2 [ltm2 [cd2' Heq_cd2]]].


    simpl in Hcomp.
    inversion Hcomp. clear Hcomp.

    subst.
    exists (I (IId (lid_of_Z n2)) (INSTR_Op (SV (OP_IBinop (Sub false false) i64 v1 v2)))::cd2' ++ cd1').
    exists (((IId (lid_of_Z n2)),(INSTR_Op (SV (OP_IBinop (Sub false false) i64 v1 v2))))::c_a2 ++ c_a1).
    simpl. repeat split; auto.
    + rewrite app_assoc. reflexivity.
    + apply cc_cons_Op. apply compiled_code_app; auto.
      apply app_inv_tail in Hcd_eq2. rewrite Hcd_eq2. auto.
      apply app_inv_tail in Hcd_eq1. rewrite Hcd_eq1. auto.
    + apply straight_Op; auto. apply straight_app; auto.
    + intros e mem Hlt Hmem k CFG fn bid phis term.
      rewrite rev_app_distr.
      specialize IHHAexp1 with (e:=e)(mem:=mem).
      lapply IHHAexp1; clear IHHAexp1; [intros IHHAexp1 | auto].
      lapply IHHAexp1; clear IHHAexp1; [intros IHHAexp1 | auto].
      specialize IHHAexp1 with (k:=k)(CFG:=CFG)(fn:=fn)(bid:=bid)(phis:=phis)(term:=term).

      rewrite <- app_assoc.
      eapply step_code_app. apply IHHAexp1. clear IHHAexp1.
      intros st1 mem1 H. 
      destruct st1 as [[pc1 e1] k1].
      destruct H as [Hpc1 [Hmem1 [Hr1 [He1 Hlte1]]]].
      split; subst; auto.

      specialize IHHAexp2 with (e:=e1)(mem:=mem1).
      lapply IHHAexp2; clear IHHAexp2; [intros IHHAexp2 | auto].
      lapply IHHAexp2; clear IHHAexp2; [intros IHHAexp2 | auto].
      specialize IHHAexp2 with (k:=k1)(CFG:=CFG)(fn:=fn)(bid:=bid)(phis:=phis)(term:=term).

      simpl.
      rewrite pc_app_slc. simpl.
      eapply step_code_app.
      apply IHHAexp2.
      intros st2 mem2 H2.
      destruct st2 as [[pc2 e2] k2].
      destruct H2 as [Hpc2 [Hmem2 [Hr2 [He2 Hlte2]]]].
      split; subst; auto.
      
      eapply step_tau; auto.
      * simpl. unfold pc_app. simpl. apply pc_prefix_id.
      * simpl.
        inversion Hr1. subst. inversion Hr2. subst.
        symmetry in H.
        assert (eval_op e2 (Some (TYPE_I 64)) v1 = inr v).
        apply He2; auto.
        simpl.
        unfold eval_expr. simpl. unfold i64.
        rewrite H3. rewrite <- H1. simpl.
        inversion H0. inversion H2. simpl.
        eauto.
      * simpl. eapply step_zero.
        repeat split; auto.
        ++ eapply memory_invariant_extension; eauto. 
        ++ unfold eval_expr; simpl; rewrite lookup_env_hd; auto.
        ++ eapply env_extends_trans. apply He1.
           eapply env_extends_trans. apply He2.
           eapply env_extends_lt. apply Hlte2. 
        ++ apply env_lt_cons. omega. eapply env_lt_weaken; eauto. omega.

  - simpl in Hcomp;
    unfold_llvm Hcomp;
    specialize IHHAexp1 with (g:=g)(n:=n)(m:=m)(cd:=cd).
    remember (compile_aexp g a1 (n, m, cd)) as f;
    destruct f as [[[n1 m1] cd1] [err1|v1]];
    try solve [inversion Hcomp].
    specialize IHHAexp1 with (n':=n1)(m':=m1)(cd':=cd1)(v:=v1).
    lapply IHHAexp1; clear IHHAexp1; [intros IHHAexp1 | auto].
    destruct IHHAexp1 as [cd_a1 [c_a1 [Hcd_eq1 [Hcc1 [HSlc1 IHHAexp1]]]]].

    symmetry in Heqf;
    apply compile_aexp_monotonic in Heqf;
    destruct Heqf as [ltn1 [ltm1 [cd1' Heq_cd1]]].

    
    specialize IHHAexp2 with (g:=g)(n:=n1)(m:=m1)(cd:=cd1).
    remember (compile_aexp g a2 (n1, m1, cd1)) as f2;
    destruct f2 as [[[n2 m2] cd2] [err2|v2]];
    try solve [inversion Hcomp].
    specialize IHHAexp2 with (n':=n2)(m':=m2)(cd':=cd2)(v:=v2).
    lapply IHHAexp2; clear IHHAexp2; [intros IHHAexp2 | auto].
    destruct IHHAexp2 as [cd_a2 [c_a2 [Hcd_eq2 [Hcc2 [HSlc2 IHHAexp2]]]]].

    symmetry in Heqf2;
    apply compile_aexp_monotonic in Heqf2;
    destruct Heqf2 as [ltn2 [ltm2 [cd2' Heq_cd2]]].


    simpl in Hcomp.
    inversion Hcomp. clear Hcomp.

    subst.
    exists (I (IId (lid_of_Z n2)) (INSTR_Op (SV (OP_IBinop (Mul false false) i64 v1 v2)))::cd2' ++ cd1').
    exists (((IId (lid_of_Z n2)),(INSTR_Op (SV (OP_IBinop (Mul false false) i64 v1 v2))))::c_a2 ++ c_a1).
    simpl. repeat split; auto.
    + rewrite app_assoc. reflexivity.
    + apply cc_cons_Op. apply compiled_code_app; auto.
      apply app_inv_tail in Hcd_eq2. rewrite Hcd_eq2. auto.
      apply app_inv_tail in Hcd_eq1. rewrite Hcd_eq1. auto.
    + apply straight_Op; auto. apply straight_app; auto.
    + intros e mem Hlt Hmem k CFG fn bid phis term.
      rewrite rev_app_distr.
      specialize IHHAexp1 with (e:=e)(mem:=mem).
      lapply IHHAexp1; clear IHHAexp1; [intros IHHAexp1 | auto].
      lapply IHHAexp1; clear IHHAexp1; [intros IHHAexp1 | auto].
      specialize IHHAexp1 with (k:=k)(CFG:=CFG)(fn:=fn)(bid:=bid)(phis:=phis)(term:=term).

      rewrite <- app_assoc.
      eapply step_code_app. apply IHHAexp1. clear IHHAexp1.
      intros st1 mem1 H. 
      destruct st1 as [[pc1 e1] k1].
      destruct H as [Hpc1 [Hmem1 [Hr1 [He1 Hlte1]]]].
      split; subst; auto.

      specialize IHHAexp2 with (e:=e1)(mem:=mem1).
      lapply IHHAexp2; clear IHHAexp2; [intros IHHAexp2 | auto].
      lapply IHHAexp2; clear IHHAexp2; [intros IHHAexp2 | auto].
      specialize IHHAexp2 with (k:=k1)(CFG:=CFG)(fn:=fn)(bid:=bid)(phis:=phis)(term:=term).

      simpl.
      rewrite pc_app_slc. simpl.
      eapply step_code_app.
      apply IHHAexp2.
      intros st2 mem2 H2.
      destruct st2 as [[pc2 e2] k2].
      destruct H2 as [Hpc2 [Hmem2 [Hr2 [He2 Hlte2]]]].
      split; subst; auto.
      
      eapply step_tau; auto.
      * simpl. unfold pc_app. simpl. apply pc_prefix_id.
      * simpl.
        inversion Hr1. subst. inversion Hr2. subst.
        symmetry in H.
        assert (eval_op e2 (Some (TYPE_I 64)) v1 = inr v).
        apply He2; auto.
        simpl.
        unfold eval_expr. simpl. unfold i64.
        rewrite H3. rewrite <- H1. simpl.
        inversion H0. inversion H2. simpl.
        eauto.
      * simpl. eapply step_zero.
        repeat split; auto.
        ++ eapply memory_invariant_extension; eauto. 
        ++ unfold eval_expr; simpl; rewrite lookup_env_hd; auto.
        ++ eapply env_extends_trans. apply He1.
           eapply env_extends_trans. apply He2.
           eapply env_extends_lt. apply Hlte2. 
        ++ apply env_lt_cons. omega. eapply env_lt_weaken; eauto. omega.
Qed.


Lemma compile_bexp_correct :
  forall 
    (b:bexp) (st:Imp.state) (ans:bool)
    (HAexp: beval st b = ans)

    (g:ctxt)
    (n m:int) (cd:list elt)
    (n' m':int) (cd':list elt)
    (v : Ollvm_ast.value)
    (Hcomp : compile_bexp g b (n,m,cd) = ((n',m',cd'),inr v)),

  exists cd_a c_a,
    cd' = cd_a ++ cd
    /\ compiled_code cd_a c_a
    /\ straight c_a
    /\ forall
    (e:env)
    (mem:memory) (Hlt:env_lt n e)
    (HM: memory_invariant g e mem st)
    (k:stack)
    (CFG : mcfg) (fn : function_id) (bid: block_id) phis term,
      step_code
        CFG
        (fun s' mem' =>
           let '(pc', e', k') := s' in
           pc' = slc_pc fn bid phis term [] /\
           memory_invariant g e' mem' st /\
           Rv1e (eval_op e' (Some (TYPE_I 1)) v) ans /\
           env_extends e e' /\
           env_lt n' e'
        )
        (List.rev c_a)
        (slc_pc fn bid phis term (List.rev c_a), e, k) mem.
Proof.
  intros b st ans HAexp.
  rewrite beval_iff_bevalR in HAexp.

  induction HAexp; intros g n m cd n' m' cd' v Hcomp.
  - (* E_BTrue *)
    simpl in Hcomp. unfold_llvm Hcomp. simpl in Hcomp.
    inversion Hcomp. clear Hcomp.
    exists [I (IId (lid_of_Z n))
         (INSTR_Op (SV (OP_ICmp Eq i64 (val_of_int64 (Integers.Int64.repr 0))
                  (val_of_int64 (Integers.Int64.repr 0)))))].
    exists [((IId (lid_of_Z n)),
         (INSTR_Op (SV (OP_ICmp Eq i64 (val_of_int64 (Integers.Int64.repr 0))
                  (val_of_int64 (Integers.Int64.repr 0))))))].
    repeat split; auto.
    * repeat econstructor.
    
    * intros e mem Hlt HM k CFG fn0 bid phis term. 
      eapply step_tau; auto.
      apply pc_prefix_id.
      simpl.
    eapply step_zero. repeat split; auto.
    + eapply memory_invariant_extension; eauto; try omega.
    + unfold eval_expr.  simpl. rewrite lookup_env_hd.
      repeat rewrite Int1.repr_signed. auto.
    + eapply env_extends_lt. apply Hlt. 
    + apply env_lt_cons. omega. eapply env_lt_weaken; eauto. omega.

  - (* E_BFalse *)
    simpl in Hcomp. unfold_llvm Hcomp. simpl in Hcomp.
    inversion Hcomp. clear Hcomp.
    exists [I (IId (lid_of_Z n))
         (INSTR_Op (SV (OP_ICmp Eq i64 (val_of_int64 (Integers.Int64.repr 1))
                  (val_of_int64 (Integers.Int64.repr 0)))))].
    exists [((IId (lid_of_Z n)),
         (INSTR_Op (SV (OP_ICmp Eq i64 (val_of_int64 (Integers.Int64.repr 1))
                  (val_of_int64 (Integers.Int64.repr 0))))))].
    repeat split; auto.
    * repeat econstructor.
    
    * intros e mem Hlt HM k CFG fn0 bid phis term. 
      eapply step_tau; auto.
      apply pc_prefix_id.
      simpl.
    eapply step_zero. repeat split; auto.
    + eapply memory_invariant_extension; eauto; try omega.
    + unfold eval_expr.  simpl. rewrite lookup_env_hd.
      repeat rewrite Int1.repr_signed. auto.
    + eapply env_extends_lt. apply Hlt. 
    + apply env_lt_cons. omega. eapply env_lt_weaken; eauto. omega.
        
  - (* E_Beq *)
    simpl in Hcomp.
    unfold_llvm Hcomp.
    rewrite <- aeval_iff_aevalR in H, H0.
    remember (compile_aexp g a1 (n, m, cd)) as f.
    destruct f as [[[n1 m1] cd1] [err1|v1]];
      try solve [inversion Hcomp].
    
    
    apply compile_aexp_correct
    with (g:=g) (n:=n) (m:=m) (cd:=cd) (n':= n1) (m':=m1) (cd':=cd1) (v:=v1) in H.
    
    destruct H as [cd_a1 [c_a1 [Hcd_eq1 [Hcc1 [HSlc1 IHHAexp1]]]]].

    symmetry in Heqf;
    apply compile_aexp_monotonic in Heqf;
    destruct Heqf as [ltn1 [ltm1 [cd1' Heq_cd1]]].

    remember (compile_aexp g a2 (n1, m1, cd1)) as f2;
    destruct f2 as [[[n2 m2] cd2] [err2|v2]];
    try solve [inversion Hcomp].
    apply compile_aexp_correct
    with (g:=g) (n:=n1) (m:=m1) (cd:=cd1) (n':= n2) (m':=m2) (cd':=cd2) (v:=v2) in H0.
    
    destruct H0 as [cd_a2 [c_a2 [Hcd_eq2 [Hcc2 [HSlc2 IHHAexp2]]]]].

    symmetry in Heqf2;
    apply compile_aexp_monotonic in Heqf2;
    destruct Heqf2 as [ltn2 [ltm2 [cd2' Heq_cd2]]].


    simpl in Hcomp.
    inversion Hcomp. clear Hcomp.

    subst.
    exists (I (IId (lid_of_Z n2)) (INSTR_Op (SV (OP_ICmp Eq i64 v1 v2)))::cd2' ++ cd1').
    exists (((IId (lid_of_Z n2)),(INSTR_Op (SV (OP_ICmp Eq i64 v1 v2))))::c_a2 ++ c_a1).
    simpl. repeat split; auto.
    + rewrite Heq_cd2. rewrite Heq_cd1. rewrite app_assoc. reflexivity.
    + apply cc_cons_Op. apply compiled_code_app; auto.
      apply app_inv_tail in Heq_cd2. rewrite <- Heq_cd2. auto.
      apply app_inv_tail in Heq_cd1. rewrite <- Heq_cd1. auto.
    + apply straight_Op; auto. apply straight_app; auto.
    + intros e mem Hlt Hmem k CFG fn bid phis term.
      rewrite rev_app_distr.
      specialize IHHAexp1 with (e:=e)(mem:=mem).
      lapply IHHAexp1; clear IHHAexp1; [intros IHHAexp1 | auto].
      lapply IHHAexp1; clear IHHAexp1; [intros IHHAexp1 | auto].
      specialize IHHAexp1 with (k:=k)(CFG:=CFG)(fn:=fn)(bid:=bid)(phis:=phis)(term:=term).

      rewrite <- app_assoc.
      eapply step_code_app. apply IHHAexp1. clear IHHAexp1.
      intros st1 mem1 H. 
      destruct st1 as [[pc1 e1] k1].
      destruct H as [Hpc1 [Hmem1 [Hr1 [He1 Hlte1]]]].
      split; subst; auto.

      specialize IHHAexp2 with (e:=e1)(mem:=mem1).
      lapply IHHAexp2; clear IHHAexp2; [intros IHHAexp2 | auto].
      lapply IHHAexp2; clear IHHAexp2; [intros IHHAexp2 | auto].
      specialize IHHAexp2 with (k:=k1)(CFG:=CFG)(fn:=fn)(bid:=bid)(phis:=phis)(term:=term).

      simpl.
      rewrite pc_app_slc. simpl.
      eapply step_code_app.
      apply IHHAexp2.
      intros st2 mem2 H2.
      destruct st2 as [[pc2 e2] k2].
      destruct H2 as [Hpc2 [Hmem2 [Hr2 [He2 Hlte2]]]].
      split; subst; auto.
      
      eapply step_tau; auto.
      * simpl. unfold pc_app. simpl. apply pc_prefix_id.
      * simpl.
        inversion Hr1. subst. inversion Hr2. subst.
        symmetry in H.
        assert (eval_op e2 (Some (TYPE_I 64)) v1 = inr v).
        apply He2; auto.
        simpl.
        unfold eval_expr. simpl. unfold i64.
        
        rewrite H3. rewrite <- H1. simpl.
        inversion H0. inversion H2. simpl.
        eauto.
      * simpl. eapply step_zero.
        repeat split; auto.
        ++ eapply memory_invariant_extension; eauto. 
        ++ unfold eval_expr; simpl; rewrite lookup_env_hd; auto. unfold eval_i64_icmp.
           apply Rv1e_inr. simpl. unfold Rv1. simpl. destruct (Int64.eq ans1 ans2); reflexivity.
        ++ eapply env_extends_trans. apply He1.
           eapply env_extends_trans. apply He2.
           eapply env_extends_lt. apply Hlte2. 
        ++ apply env_lt_cons. omega. eapply env_lt_weaken; eauto. omega.
    + symmetry. apply Heqf2.
    + symmetry. apply Heqf.

  - (* E_BLe *)
    simpl in Hcomp.
    unfold_llvm Hcomp.
    rewrite <- aeval_iff_aevalR in H, H0.
    remember (compile_aexp g a1 (n, m, cd)) as f.
    destruct f as [[[n1 m1] cd1] [err1|v1]];
      try solve [inversion Hcomp].
    
    
    apply compile_aexp_correct
    with (g:=g) (n:=n) (m:=m) (cd:=cd) (n':= n1) (m':=m1) (cd':=cd1) (v:=v1) in H.
    
    destruct H as [cd_a1 [c_a1 [Hcd_eq1 [Hcc1 [HSlc1 IHHAexp1]]]]].

    symmetry in Heqf;
    apply compile_aexp_monotonic in Heqf;
    destruct Heqf as [ltn1 [ltm1 [cd1' Heq_cd1]]].

    remember (compile_aexp g a2 (n1, m1, cd1)) as f2;
    destruct f2 as [[[n2 m2] cd2] [err2|v2]];
    try solve [inversion Hcomp].
    apply compile_aexp_correct
    with (g:=g) (n:=n1) (m:=m1) (cd:=cd1) (n':= n2) (m':=m2) (cd':=cd2) (v:=v2) in H0.
    
    destruct H0 as [cd_a2 [c_a2 [Hcd_eq2 [Hcc2 [HSlc2 IHHAexp2]]]]].

    symmetry in Heqf2;
    apply compile_aexp_monotonic in Heqf2;
    destruct Heqf2 as [ltn2 [ltm2 [cd2' Heq_cd2]]].


    simpl in Hcomp.
    inversion Hcomp. clear Hcomp.

    subst.
    exists (I (IId (lid_of_Z n2)) (INSTR_Op (SV (OP_ICmp Sle i64 v1 v2)))::cd2' ++ cd1').
    exists (((IId (lid_of_Z n2)),(INSTR_Op (SV (OP_ICmp Sle i64 v1 v2))))::c_a2 ++ c_a1).
    simpl. repeat split; auto.
    + rewrite Heq_cd2. rewrite Heq_cd1. rewrite app_assoc. reflexivity.
    + apply cc_cons_Op. apply compiled_code_app; auto.
      apply app_inv_tail in Heq_cd2. rewrite <- Heq_cd2. auto.
      apply app_inv_tail in Heq_cd1. rewrite <- Heq_cd1. auto.
    + apply straight_Op; auto. apply straight_app; auto.
    + intros e mem Hlt Hmem k CFG fn bid phis term.
      rewrite rev_app_distr.
      specialize IHHAexp1 with (e:=e)(mem:=mem).
      lapply IHHAexp1; clear IHHAexp1; [intros IHHAexp1 | auto].
      lapply IHHAexp1; clear IHHAexp1; [intros IHHAexp1 | auto].
      specialize IHHAexp1 with (k:=k)(CFG:=CFG)(fn:=fn)(bid:=bid)(phis:=phis)(term:=term).

      rewrite <- app_assoc.
      eapply step_code_app. apply IHHAexp1. clear IHHAexp1.
      intros st1 mem1 H. 
      destruct st1 as [[pc1 e1] k1].
      destruct H as [Hpc1 [Hmem1 [Hr1 [He1 Hlte1]]]].
      split; subst; auto.

      specialize IHHAexp2 with (e:=e1)(mem:=mem1).
      lapply IHHAexp2; clear IHHAexp2; [intros IHHAexp2 | auto].
      lapply IHHAexp2; clear IHHAexp2; [intros IHHAexp2 | auto].
      specialize IHHAexp2 with (k:=k1)(CFG:=CFG)(fn:=fn)(bid:=bid)(phis:=phis)(term:=term).

      simpl.
      rewrite pc_app_slc. simpl.
      eapply step_code_app.
      apply IHHAexp2.
      intros st2 mem2 H2.
      destruct st2 as [[pc2 e2] k2].
      destruct H2 as [Hpc2 [Hmem2 [Hr2 [He2 Hlte2]]]].
      split; subst; auto.
      
      eapply step_tau; auto.
      * simpl. unfold pc_app. simpl. apply pc_prefix_id.
      * simpl.
        inversion Hr1. subst. inversion Hr2. subst.
        symmetry in H.
        assert (eval_op e2 (Some (TYPE_I 64)) v1 = inr v).
        apply He2; auto.
        simpl.
        unfold eval_expr. simpl. unfold i64.
        
        rewrite H3. rewrite <- H1. simpl.
        inversion H0. inversion H2. simpl.
        eauto.
      * simpl. eapply step_zero.
        repeat split; auto.
        ++ eapply memory_invariant_extension; eauto. 
        ++ unfold eval_expr; simpl; rewrite lookup_env_hd; auto. unfold eval_i64_icmp.
           apply Rv1e_inr. simpl. unfold Rv1. destruct (Int64.lt ans2 ans1); reflexivity.
        ++ eapply env_extends_trans. apply He1.
           eapply env_extends_trans. apply He2.
           eapply env_extends_lt. apply Hlte2. 
        ++ apply env_lt_cons. omega. eapply env_lt_weaken; eauto. omega.
    + symmetry. apply Heqf2.
    + symmetry. apply Heqf.

  - (* E_BNot *)
    simpl in Hcomp;
    unfold_llvm Hcomp;
    specialize IHHAexp with (g:=g)(n:=n)(m:=m)(cd:=cd).
    remember (compile_bexp g b1 (n, m, cd)) as f.
    destruct f as [[[n1 m1] cd1] [err1|v1]];
    try solve [inversion Hcomp].
    specialize IHHAexp with (n':=n1)(m':=m1)(cd':=cd1)(v:=v1).
    lapply IHHAexp; clear IHHAexp; [intros IHHAexp | auto].
    destruct IHHAexp as [cd_a1 [c_a1 [Hcd_eq1 [Hcc1 [HSlc1 IHHAexp]]]]].

    simpl in Hcomp.
    inversion Hcomp. clear Hcomp.

    subst.
    exists (I (IId (lid_of_Z n1)) (INSTR_Op (SV (OP_ICmp Eq i1 (val_of_int1 (Compiler.Int1.repr 0)) v1)))::cd_a1).
    exists (((IId (lid_of_Z n1)),(INSTR_Op (SV (OP_ICmp Eq i1 (val_of_int1 (Compiler.Int1.repr 0)) v1))))::c_a1).
    simpl. repeat split; auto.
    + apply straight_Op; auto.
    + intros e mem Hlt Hmem k CFG fn bid phis term.

      specialize IHHAexp with (e:=e)(mem:=mem).
      lapply IHHAexp; clear IHHAexp; [intros IHHAexp | auto].
      lapply IHHAexp; clear IHHAexp; [intros IHHAexp | auto].
      specialize IHHAexp with (k:=k)(CFG:=CFG)(fn:=fn)(bid:=bid)(phis:=phis)(term:=term).

      eapply step_code_app. apply IHHAexp. clear IHHAexp.
      intros st1 mem1 H. 
      destruct st1 as [[pc1 e1] k1].
      destruct H as [Hpc1 [Hmem1 [Hr1 [He1 Hlte1]]]].
      split; subst; auto.

      simpl.
      rewrite pc_app_slc. simpl.

      simpl. inversion Hr1. subst.
      unfold Rv1 in H0. unfold i1.
      
      eapply step_tau with (s':=({| fn := fn; bk := {| blk_id := bid; blk_phis := phis; blk_code := []; blk_term := term |} |},
    add_env (lid_of_Z n1)
      (eval_i1_icmp Eq Int1.zero (if ans then Int1.one else Int1.zero)) e1, k1)); auto.
      * simpl. unfold pc_app. simpl. apply pc_prefix_id.
      * unfold eval_expr. 

        simpl. unfold eval_expr. simpl.
        rewrite <- H.
        simpl.
        destruct ans; subst; reflexivity.
      * simpl. eapply step_zero.
        repeat split; auto.
        ++ eapply memory_invariant_extension; eauto. 
        ++ unfold eval_expr; simpl;rewrite lookup_env_hd.
           destruct ans; unfold eval_i1_icmp; simpl; apply Rv1e_inr; reflexivity.
        ++ eapply env_extends_trans. apply He1.
           eapply env_extends_lt. apply Hlte1. 
        ++ apply env_lt_cons. omega. eapply env_lt_weaken; eauto. omega.
  - (* E_BAnd *)
    simpl in Hcomp.
    unfold_llvm Hcomp.
    rewrite <- beval_iff_bevalR in HAexp1, HAexp2.
    remember (compile_bexp g b1 (n, m, cd)) as f.
    destruct f as [[[n1 m1] cd1] [err1|v1]];
      try solve [inversion Hcomp].

    remember (compile_bexp g b2 (n1, m1, cd1)) as f2;
    destruct f2 as [[[n2 m2] cd2] [err2|v2]];
    try solve [inversion Hcomp].

    simpl in Hcomp.
    inversion Hcomp. clear Hcomp.

    symmetry in Heqf.
    apply IHHAexp1
    with (g:=g) (n:=n) (m:=m) (cd:=cd) (n':= n1) (m':=m1) (cd':=cd1) (v:=v1) in Heqf.
    clear IHHAexp1.
    destruct Heqf as [cd_a1 [c_a1 [Hcd_eq1 [Hcc1 [HSlc1 IHHAexp1]]]]].

    symmetry in Heqf2.
    apply IHHAexp2
    with (g:=g) (n:=n1) (m:=m1) (cd:=cd1) (n':= n2) (m':=m2) (cd':=cd2) (v:=v2) in Heqf2.
    clear IHHAexp2.
    destruct Heqf2 as [cd_a2 [c_a2 [Hcd_eq2 [Hcc2 [HSlc2 IHHAexp2]]]]].

    subst.
    exists (I (IId (lid_of_Z n2)) (INSTR_Op (SV (OP_IBinop And i1 v1 v2)))::cd_a2 ++ cd_a1).
    exists (((IId (lid_of_Z n2)),(INSTR_Op (SV (OP_IBinop And i1 v1 v2))))::c_a2 ++ c_a1).
    simpl. repeat split; auto.
    + rewrite app_assoc. reflexivity.
    + apply cc_cons_Op. apply compiled_code_app; auto.
    + apply straight_Op; auto. apply straight_app; auto.
    + intros e mem Hlt Hmem k CFG fn bid phis term.
      rewrite rev_app_distr.
      specialize IHHAexp1 with (e:=e)(mem:=mem).
      lapply IHHAexp1; clear IHHAexp1; [intros IHHAexp1 | auto].
      lapply IHHAexp1; clear IHHAexp1; [intros IHHAexp1 | auto].
      specialize IHHAexp1 with (k:=k)(CFG:=CFG)(fn:=fn)(bid:=bid)(phis:=phis)(term:=term).

      rewrite <- app_assoc.
      eapply step_code_app. apply IHHAexp1. clear IHHAexp1.
      intros st1 mem1 H. 
      destruct st1 as [[pc1 e1] k1].
      destruct H as [Hpc1 [Hmem1 [Hr1 [He1 Hlte1]]]].
      split; subst; auto.

      specialize IHHAexp2 with (e:=e1)(mem:=mem1).
      lapply IHHAexp2; clear IHHAexp2; [intros IHHAexp2 | auto].
      lapply IHHAexp2; clear IHHAexp2; [intros IHHAexp2 | auto].
      specialize IHHAexp2 with (k:=k1)(CFG:=CFG)(fn:=fn)(bid:=bid)(phis:=phis)(term:=term).

      simpl.
      rewrite pc_app_slc. simpl.
      eapply step_code_app.
      apply IHHAexp2.
      intros st2 mem2 H2.
      destruct st2 as [[pc2 e2] k2].
      destruct H2 as [Hpc2 [Hmem2 [Hr2 [He2 Hlte2]]]].
      split; subst; auto.
      
      eapply step_tau with (s' := ({| fn := fn; bk := {| blk_id := bid; blk_phis := phis; blk_code := []; blk_term := term |} |},
    add_env (lid_of_Z n2) (eval_i1_op And (if beval s b1 then Int1.one else Int1.zero) (if beval s b2 then Int1.one else Int1.zero)) e2, k2)); auto.
      * simpl. unfold pc_app. simpl. apply pc_prefix_id.
      * simpl.
        inversion Hr1. subst. inversion Hr2. subst.
        symmetry in H.
        assert (eval_op e2 (Some (TYPE_I 1)) v1 = inr v).
        apply He2; auto.
        simpl.
        unfold eval_expr. simpl. unfold i1.
        
        rewrite H3. rewrite <- H1.
        unfold Rv1 in *. destruct (beval s b1); destruct (beval s b2); subst; auto.        
      * simpl. eapply step_zero.
        repeat split; auto.
        ++ eapply memory_invariant_extension; eauto. 
        ++ unfold eval_expr; simpl; rewrite lookup_env_hd; auto. unfold eval_i64_icmp.
           apply Rv1e_inr. simpl. unfold Rv1. simpl.
           destruct (beval s b1); destruct (beval s b2); reflexivity.
        ++ eapply env_extends_trans. apply He1.
           eapply env_extends_trans. apply He2.
           eapply env_extends_lt. apply Hlte2. 
        ++ apply env_lt_cons. omega. eapply env_lt_weaken; eauto. omega.
Qed.