From Coq Require Import List String Ascii ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

From Vellvm Require Import
     LLVMAst
     LLVMEvents
     UndefTests
     UndefRefinementFacts
     TopLevel
     Refinement
     TopLevelRefinements
     CFG
     DynamicTypes
     PropT
     Transformations.Traversal.

From Vellvm.Handlers Require Import
     Stack
     Local
     Global.

From ITree Require Import
     ITree
     Basics
     Eq.Eq
     Events.State.

From ExtLib Require Import
     Structures.Monads
     Structures.Maps
     Core.RelDec
     Programming.Eqv.

Import EqvNotation.


Import ITree.Basics.Basics.Monads.

Import MonadNotation.
Import ListNotations.
Import Monads.

Require Import Morphisms.
Require Import Relations.

Import R.
Import TopLevelEnv.
Import IO.
Import D.


(* -------------------------------------------------- *)
(* Interpretation / refinement of blocks.             *)
(* -------------------------------------------------- *)
Definition block_interp_uvalue (b: block dtyp) := denote_block b.
Definition block_interp_L1 (b : block dtyp) g := run_state (interp_global (block_interp_uvalue b)) g.
Definition block_interp_L2 (b : block dtyp) g l := run_state (interp_local (block_interp_L1 b g)) l.
Definition block_interp_L3 (b : block dtyp) g l m := run_state (M.interp_memory (block_interp_L2 b g l)) m.

Definition _failure_UB_to_block_L4 : (FailureE +' UBE) ~> (CallE +' UBE +' FailureE) :=
  fun T e =>
    match e with
    | inl1 x => inr1 (inr1 x)
    | inr1 x => inr1 (inl1 x)
    end.

Definition concretize_block_uv (res : (block_id + res_uvalue)) : itree (FailureE +' UBE) (block_id + dvalue)
  := match res with
     | inl bid => ret (inl bid)
     | inr uv => ITree.map inr (P.concretize_uvalue uv)
     end.

Definition block_interp_L4 (b : block dtyp) g l m : itree (CallE +' UBE +' DebugE +' FailureE) (M.memory_stack * (list (raw_id * res_uvalue) * (list (raw_id * dvalue) * (block_id + dvalue)))) :=
  '(m, (env, (genv, buv))) <- P.interp_undef (block_interp_L3 b g l m);;
   bdv <- translate _failure_UB_to_L4 (concretize_block_uv buv);;
   ret (m, (env, (genv, bdv))).


Definition refine_block_L2 b1 b2 g l := eutt (TT × (TT × (sum_rel Logic.eq refine_uvalue))) (block_interp_L2 b1 g l) (block_interp_L2 b2 g l).

Hint Unfold refine_block_L2.
Hint Unfold block_interp_L1.
Hint Unfold block_interp_L2.

Ltac step_refine := autounfold;
                    tau_steps.

Ltac simple_refine := step_refine;
                      apply eqit_Ret; repeat (apply prod_morphism; firstorder);
                      apply inr_morphism.


Ltac refine_a_times_undef :=
  match goal with
  | [ |-
      refine_uvalue (UVALUE_Undef (DTYPE_I 64))
                    (UVALUE_IBinop (Mul false false)
                                   (UVALUE_I64 ?a)
                                   (UVALUE_Undef (DTYPE_I 64)))
    ] => apply undef_refines_mul_relprime_undef
  | [ |-
      refine_uvalue (UVALUE_Undef (DTYPE_I 64))
                    (UVALUE_IBinop (Mul false false)
                                   (UVALUE_Undef (DTYPE_I 64))
                                   (UVALUE_I64 ?a))
    ] => apply undef_refines_mul_undef_relprime
  end;
  unfold Znumtheory.rel_prime;
  match goal with
  | [ |- Znumtheory.Zis_gcd ?a ?m ?x ] =>  replace x with (Z.gcd a m) by (cbv; auto)
  end; apply Znumtheory.Zgcd_is_gcd.

(* These should probably be hint databases? *)
Ltac refine_mul_uvalue :=
  solve [ refine_a_times_undef
        | apply zero_refines_undef_mul_a
        | apply zero_refines_a_mul_undef
        | apply undef_refines_mul_undef_undef
        ].

Ltac refine_div_uvalue :=
  solve [ apply undef_refines_undef_udiv_1
        | apply undef_refines_undef_sdiv_1
        | apply zero_refines_undef_urem_1
        | apply zero_refines_undef_srem_1
        ].

Ltac refine_and_uvalue :=
  solve [ apply undef_refines_and_undef_undef
        ].

Ltac refine_or_uvalue :=
  solve [ apply undef_refines_or_undef_undef
        ].

Ltac refine_uvalue :=
  solve [ refine_mul_uvalue
        | refine_div_uvalue
        | refine_and_uvalue
        | refine_or_uvalue
        ].

Theorem undef_test6 :
  forall g l,
    refine_block_L2 undef_test6_block_refine undef_test6_block g l.
Proof.
  intros g l.
  simple_refine.
  refine_uvalue.
Qed.

Theorem undef_test0 :
  forall g l,
    refine_block_L2 undef_test0_block_refine undef_test0_block g l.
Proof.
  intros g l.
  simple_refine.
  refine_uvalue.
Qed.

Theorem undef_test1 :
  forall g l,
    refine_block_L2 undef_test1_block_refine undef_test1_block g l.
Proof.
  intros g l.
  simple_refine.
  refine_uvalue.
Qed.

Theorem undef_test2 :
  forall g l,
    refine_block_L2 undef_test2_block_refine undef_test2_block g l.
Proof.
  intros g l.
  simple_refine.
  refine_uvalue.  
Qed.

Theorem undef_test3 :
  forall g l
    refine_block_L2 undef_test3_block_refine undef_test3_block g l.
Proof.
  intros g l.
  simple_refine.
  refine_uvalue.
Qed.

Theorem undef_test4 :
  forall g l
    refine_block_L2 undef_test4_block_refine undef_test4_block g l.
Proof.
  intros g l.
  simple_refine.
  refine_uvalue.
Qed.

Theorem undef_test5 :
  forall g l,
    refine_block_L2 undef_test5_block_refine undef_test5_block g l.
Proof.
  intros g l.
  simple_refine.
  refine_uvalue.
Qed.

Theorem undef_test6 :
  forall g l,
    refine_block_L2 undef_test6_block_refine undef_test6_block g l.
Proof.
  intros g l.
  simple_refine.
  refine_uvalue.
Qed.

Theorem undef_test7 :
  forall g l,
    refine_block_L2 undef_test7_block_refine undef_test7_block g l.
Proof.
  intros g l.
  simple_refine.
  refine_uvalue.
Qed.

Theorem undef_test8 :
  forall g l,
    refine_block_L2 undef_test8_block_refine undef_test8_block g l.
Proof.
  intros g l.
  simple_refine.
  refine_uvalue.
Qed.

Theorem undef_test9 :
  forall g l,
    refine_block_L2 undef_test9_block_refine undef_test9_block g l.
Proof.
  intros g l.
  simple_refine.
  refine_uvalue.
Qed.

Theorem undef_test10 :
  forall g l,
    refine_block_L2 undef_test10_block_refine undef_test10_block g l.
Proof.
  intros g l.
  simple_refine.

  simpl.
  refine_uvalue.
Qed.


(* -------------------------------------------------- *)
(* CFG interpretation / refinement                    *)
(* -------------------------------------------------- *)
Definition cfg_interp_uvalue (c : cfg dtyp) := denote_cfg c.
Definition cfg_interp_L1 (c : cfg dtyp) := interp_global (cfg_interp_uvalue c) [].
Definition cfg_interp_L2 (c : cfg dtyp) := interp_local (cfg_interp_L1 c) [].
Definition cfg_interp_L3 (c : cfg dtyp) := M.interp_memory (cfg_interp_L2 c) (M.empty, [[]]).

Definition refine_cfg_L2 c1 c2 := eutt (TT × (TT × refine_uvalue)) (cfg_interp_L2 c1) (cfg_interp_L2 c2).

(* -------------------------------------------------- *)
(* Block substitution into CFG.                       *)
(* -------------------------------------------------- *)

(* Replace a block with a given block r if the ids match *)
Definition replace_block {T} (r : block T) (b : block T) : block T :=
  if blk_id b ~=? blk_id r then r else b.

(* Endomorphism for replacing blocks that have the same id as a given block *)
Section block_replace.
  Variable T : Set.
  Variable b : block T.

  Definition blah := b.

  Instance block_replace_endo : endo (block T)
    := replace_block b.

  Definition cfg_replace_block : endo (cfg T)
    := f_endo.
End block_replace.

(* CB TODO: bad name *)
Lemma blk_id_eq :
  forall T b bid,
    (if @blk_id T b ~=? bid then true else false) = true ->
    bid = @blk_id T b.
Proof.
  intros T b bid H.
  destruct (blk_id b ~=? bid) eqn:Hbid; firstorder.
Qed.

Lemma find_map :
  forall T p (l : list T) x y,
    find p l = Some x ->
    (p x = true -> p y = true) ->
    find p (map (fun x => if p x then y else x) l) = Some y.
Proof.
  intros T p l; induction l; intros x y Hf Hp.
  - inversion Hf.
  - pose proof (find_some _ _ Hf) as [Hin Hpx].
    destruct Hin as [Hxa | Hinl].
    + simpl; subst. rewrite Hpx.
      simpl. rewrite (Hp Hpx).
      reflexivity.
    + simpl. simpl in Hf.
      destruct (p a) eqn:Hpa.
      * simpl. rewrite (Hp Hpx). reflexivity.
      * simpl. rewrite Hpa.
        eapply IHl; eauto.
Qed.

(* CB: TODO bad name *)
Lemma blk_id_eq_if :
  forall T x y bid,
    blk_id x = blk_id y ->
    (if @blk_id T x ~=? bid then true else false) = true ->
    (if @blk_id T y ~=? bid then true else false) = true.
Proof.
  intros T x y bid H H0.
  apply blk_id_eq in H0. rewrite H0.
  subst. rewrite H.
  destruct (blk_id y ~=? blk_id y); firstorder.
Qed.

(* CB: TODO bad name *)
Lemma if_lift :
  forall A T (b0 b : block T) (x y : A),
    (if blk_id b0 ~=? blk_id b then x else y) = (if (if blk_id b0 ~=? blk_id b then true else false) then x else y).
Proof.
  intros A T b0 b x y.
  destruct (blk_id b0 ~=? blk_id b); reflexivity.
Qed.

Lemma map_if_lift :
  forall b blks,
    map (fun b0 : block dtyp => if if blk_id b0 ~=? blk_id b then true else false then b else b0) blks =
    map (fun b0 : block dtyp => if blk_id b0 ~=? blk_id b then b else b0) blks.
Proof.
  intros b blks. revert b.
  induction blks; intros b.
  - reflexivity.
  - simpl. rewrite <- if_lift.
    rewrite IHblks.
    reflexivity.
 Qed.

Lemma cfg_replace_block_find :
  forall c b bid b',
    bid = blk_id b ->
    find_block dtyp (CFG.blks dtyp c) bid = Some b' ->
    find_block dtyp (CFG.blks dtyp (cfg_replace_block dtyp b c)) bid = Some b.
Proof.
  intros c b bid b' Hid Hfind.
  unfold find_block in *;
    destruct c; simpl in *; subst.

  unfold f_endo, endo_list, f_endo, block_replace_endo, replace_block.
  rewrite <- map_if_lift.
  eapply find_map; eauto.
  apply blk_id_eq_if.
  
  apply find_some in Hfind.
  destruct Hfind as [Hin Hideq].
  apply blk_id_eq in Hideq; firstorder.
Qed.


Inductive is_read_exp {T} : exp T -> ident -> Prop :=
| is_read_Ident  : forall id, is_read_exp (EXP_Ident id) id
| is_read_Struct : forall id t fields e, In (t, e) fields -> is_read_exp e id -> is_read_exp (EXP_Struct fields) id
| is_read_Packed : forall id t fields e, In (t, e) fields -> is_read_exp e id -> is_read_exp (EXP_Packed_struct fields) id
| is_read_Array  : forall id t elts e, In (t, e) elts -> is_read_exp e id -> is_read_exp (EXP_Array elts) id
| is_read_Vector  : forall id t elts e, In (t, e) elts -> is_read_exp e id -> is_read_exp (EXP_Vector elts) id
| is_read_IBinop_left : forall id op t l r, is_read_exp l id -> is_read_exp (OP_IBinop op t l r) id
| is_read_IBinop_right : forall id op t l r, is_read_exp r id -> is_read_exp (OP_IBinop op t l r) id
| is_read_FBinop_left : forall id op fm t l r, is_read_exp l id -> is_read_exp (OP_FBinop op fm t l r) id
| is_read_FBinop_right : forall id op fm t l r, is_read_exp r id -> is_read_exp (OP_FBinop op fm t l r) id
| is_read_FCMP_left : forall cmp t l r id, is_read_exp l id -> is_read_exp (OP_FCmp cmp t l r) id
| is_read_FCMP_right : forall cmp t l r id, is_read_exp r id -> is_read_exp (OP_FCmp cmp t l r) id
| is_read_Conversion : forall conv t_f v t_t id, is_read_exp v id -> is_read_exp (OP_Conversion conv t_f v t_t) id
| is_read_GetElementPtr_ptr: forall (t:T) (ptrval:(T * exp T)) (idxs:list (T * exp T)) id,
    is_read_exp (snd ptrval) id ->
    is_read_exp (OP_GetElementPtr t ptrval idxs) id
| is_read_GetElementPtr_idx: forall (t:T) t' e (ptrval:(T * exp T)) (idxs:list (T * exp T)) id,
    In (t', e) idxs -> is_read_exp e id ->
    is_read_exp (OP_GetElementPtr t ptrval idxs) id

| is_read_ExtractElement_vec: forall (vec:(T * exp T)) (idx:(T * exp T)) id,
    is_read_exp (snd vec) id ->
    is_read_exp (OP_ExtractElement vec idx) id
| is_read_ExtractElement_idx: forall (vec:(T * exp T)) (idx:(T * exp T)) id,
    is_read_exp (snd idx) id ->
    is_read_exp (OP_ExtractElement vec idx) id

| is_read_InsertElement_vec: forall (vec:(T * exp T)) (elt:(T * exp T)) (idx:(T * exp T)) id,
    is_read_exp (snd vec) id ->
    is_read_exp (OP_InsertElement vec elt idx) id
| is_read_InsertElement_idx: forall (vec:(T * exp T)) (elt:(T * exp T)) (idx:(T * exp T)) id,
    is_read_exp (snd idx) id ->
    is_read_exp (OP_InsertElement vec elt idx) id

| is_read_ShuffleVector_left: forall (vec1:(T * exp T)) (vec2:(T * exp T)) (idxmask:(T * exp T)) id,
    is_read_exp (snd vec1) id ->
    is_read_exp (OP_ShuffleVector vec1 vec2 idxmask) id
| is_read_ShuffleVector_right: forall (vec1:(T * exp T)) (vec2:(T * exp T)) (idxmask:(T * exp T)) id,
    is_read_exp (snd vec2) id ->
    is_read_exp (OP_ShuffleVector vec1 vec2 idxmask) id
| is_read_ShuffleVector_idx: forall (vec1:(T * exp T)) (vec2:(T * exp T)) (idxmask:(T * exp T)) id,
    is_read_exp (snd idxmask) id ->
    is_read_exp (OP_ShuffleVector vec1 vec2 idxmask) id

| is_read_ExtractValue: forall (vec:(T * exp T)) (idxs:list int) id,
    is_read_exp (snd vec) id ->
    is_read_exp (OP_ExtractValue vec idxs) id

| is_read_InsertValue_vec: forall (vec:(T * exp T)) (elt:(T * exp T)) (idxs:list int) id,
    is_read_exp (snd vec) id ->
    is_read_exp (OP_InsertValue vec elt idxs) id
| is_read_InsertValue_elt: forall (vec:(T * exp T)) (elt:(T * exp T)) (idxs:list int) id,
    is_read_exp (snd elt) id ->
    is_read_exp (OP_InsertValue vec elt idxs) id

| is_read_Select_cnd: forall (cnd:(T * exp T)) (v1:(T * exp T)) (v2:(T * exp T)) id,
    is_read_exp (snd cnd) id ->
    is_read_exp (OP_Select cnd v1 v2) id
| is_read_Select_v1: forall (cnd:(T * exp T)) (v1:(T * exp T)) (v2:(T * exp T)) id,
    is_read_exp (snd v1) id ->
    is_read_exp (OP_Select cnd v1 v2) id
| is_read_Select_v2: forall (cnd:(T * exp T)) (v1:(T * exp T)) (v2:(T * exp T)) id,
    is_read_exp (snd v2) id ->
    is_read_exp (OP_Select cnd v1 v2) id.

Fixpoint is_read_instr {T} (id : ident) (i : instr T) : Prop :=
  match i with
  | INSTR_Comment msg       => False
  | INSTR_Op op             => is_read_exp op id
  | INSTR_Call fn args      => is_read_exp (snd fn) id \/ Exists (fun '(_,e) => is_read_exp e id) args
  | INSTR_Alloca t nb align => match nb with
                              | None => False
                              | Some (_, e) => is_read_exp e id
                              end

  | INSTR_Load volatile t ptr align    => is_read_exp (snd ptr) id
  | INSTR_Store volatile val ptr align => is_read_exp (snd ptr) id \/ is_read_exp (snd val) id
  | INSTR_Fence                        => False
  | INSTR_AtomicCmpXchg                => False
  | INSTR_AtomicRMW                    => False
  | INSTR_Unreachable                  => False
  | INSTR_VAArg                        => False
  | INSTR_LandingPad                   => False
  end.

Definition is_read_phi {T} (id : ident) (p : phi T) : Prop :=
  match p with
  | Phi _ args => Exists (fun '(_, e) => is_read_exp e id) args
  end.

Fixpoint is_read_block {T} (id : ident) (b : block T) : Prop :=
  let phis   := map snd (blk_phis b) in
  let instrs := map snd (blk_code b) in
  Exists (is_read_phi id) phis \/ Exists (is_read_instr id) instrs
.

Fixpoint is_read {T} (c : cfg T) (id : ident) (b : block T) : Prop :=
  match c with
  | mkCFG init blks args =>
    let bid := blk_id b in
    Exists (fun b' => if blk_id b' ~=? bid
                   then False
                   else is_read_block id b') blks
  end.

Theorem bl2_subst_cfgl2 :
  forall (b1 b2 : block dtyp) (blks : list (block dtyp)) (c : cfg dtyp),
    refine_block_L2 b1 b2 ->
    blk_id b1 = blk_id b2 ->
    refine_cfg_L2 (cfg_replace_block _ b1 c)
                  (cfg_replace_block _ b2 c).
Proof.
  intros b1 b2 blks c Hrefb Hids.
  unfold refine_cfg_L2, refine_block_L2 in *.
  unfold cfg_interp_L2, cfg_interp_L1, block_interp_L2, block_interp_L1 in *.
  tau_steps.
  cbn. unfold f_endo. unfold endo_list. rewrite cfg_replace_block_find.
  unfold cat.
Qed.


(* SCRAPYARD. Will probably need some of these things, but not sure about all of them. *)

(*
Instance interp_local_Proper
         {E F G : Type -> Type} `{FailureE -< E +' F +' G}
         k v map `{Map k v map} `{Serialize.Serialize k} (st : map)
         R (RR : relation R)
         (f : itree (E +' F +' LocalE k v +' G) R -> itree (E +' F +' LocalE k v +' G) R) :
  Proper ((fun t1 t2 => @eutt (E +' F +' G) _ _ (TT × RR) (interp_local t1 st) (interp_local t2 st)) ==> (fun t1 t2 => @eutt (E +' F +' G) _ _ (TT × RR) (interp_local t1 st) (interp_local t2 st))) f.
intros t1 t2 ?.
Admitted.
*)

(*
Instance interp_global_Proper
         {E F G : Type -> Type} `{FailureE -< E +' F +' G}
         k v map `{Map k v map} `{Serialize.Serialize k} (st : map)
         R (RR : relation R)
         (f : itree (E +' F +' GlobalE k v +' G) R -> itree (E +' F +' GlobalE k v +' G) R) :
  Proper ((fun t1 t2 => @eutt (E +' F +' G) _ _ (TT × RR) (interp_global t1 st) (interp_global t2 st)) ==> (fun t1 t2 => @eutt (E +' F +' G) _ _ (TT × RR) (interp_global t1 st) (interp_global t2 st))) f.
intros t1 t2 ?.
Admitted.
*)

(*
Theorem interp_bind_st
  : forall (E F : Type -> Type) (R S : Type) (ST : Type) (st : ST)
      (f : forall T : Type, E T -> stateT ST (itree F) T) (t : itree E R) (k : R -> itree E S),
    interp f (ITree.bind t k) st ≅ ITree.bind (interp f t st) (fun '(s, r) => interp f (k r) s).
Proof.
Admitted.

Theorem interp_translate_st
     : forall (E F G : Type -> Type) (ST : Type) (st : ST) (f : forall T : Type, E T -> F T)
         (h : forall T : Type, F T -> stateT ST (itree G) T) (R : Type) 
         (t : itree E R),
       interp h (translate f t) st
       ≅ interp (fun (T : Type) (e : E T) => h T (f T e)) t st.
Proof.
Admitted.

Theorem interp_ret_st :
  forall (E F : Type -> Type) (R : Type) (ST : Type) (st : ST) (f : forall T : Type, E T -> stateT ST (itree F) T) (x : R),
    interp f (Ret x) st ≅ ITree.map (fun x => (st, x)) (Ret x).
Proof.
Admitted.

Theorem interp_trigger_st :
  forall (E F : Type -> Type) (R : Type) (ST : Type) (st : ST) (f : forall T : Type, E T -> stateT ST (itree F) T)
    (e : E R), interp f (ITree.trigger e) st ≳ f R e st.
Proof.
Admitted.
 *)
