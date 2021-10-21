From Coq Require Import
     Lia
     (* Arith *)
     (* Strings.String *)
     Lists.List
     ZArith.

From Vellvm Require Import Syntax Semantics .
From Imp2Vir Require Import Relabel.

Import ListNotations.

From ExtLib Require Import
     Structures.Monads.
From ITree Require Import
     ITree
     ITreeFacts
     Eq.

From Vellvm Require Import Tactics.


Section CvirSyntax.

(** -- Misc -- *)
Fixpoint mk_map (l : list block_id) (l' : list block_id) : bid_map :=
  match l with
  | [] => []
  | x1::l1 => (match l' with
             | [] => []
             | x2::l2 => (x1,x2)::(mk_map l1 l2)
             end)
  end.

Definition cycle {A} (l : list A) : list A :=
    match l with
    | [] => []
    | x::tl => tl ++ [x]
    end.

Definition eq_bid b b' :=
  match b,b' with
  | Name s, Name s' => String.eqb s s'
  | Anon n, Anon n' => @RelDec.eq_dec int eq_dec_int n n'
  | Raw n, Raw n' => @RelDec.eq_dec int eq_dec_int n n'
  | _,_ => false
  end.

Fixpoint find_nth_error' (l : list block_id) (x : block_id) (n : nat) : option nat :=
  match l with
  | [] => None
  | h::t =>  if eq_bid x h then Some n else find_nth_error' t x (n+1)
  end.

Definition find_nth_error (l : list block_id) (x : block_id) : option nat :=
  find_nth_error' l x 0.


Fixpoint find_nth' (l : list block_id) (x : block_id) (n : nat) : nat:=
  match l with
  | [] => 0
  | h::t => if eq_bid x h then n else find_nth' t x (n+1)
  end.

Definition find_nth (l : list block_id) (x : block_id) := find_nth' l x 0.

Lemma nth_error_none : forall {A} (l : list A) k,
  nth_error l (Nat.modulo k (length l)) = None -> l = [].
Proof.
  intros.
  induction l ; auto.
  rewrite nth_error_None in H.
  simpl in H. lia.
Qed.

Definition mk_anon (n : nat) := Anon (Z.of_nat n).

Variant block_typ : Type :=
  | Simple
  | Return ( _ : texp typ )
  | Void
  | Branch ( _ : texp typ ).

Inductive icvir : Type :=
| Block (_ : block_typ) ( _ : code typ )
| PermuteInputs (_ : icvir)  (* Do we want more generally an arbitrary permutation? *)
| PermuteOutputs (_ : icvir)
| Loop (_ : nat) (_ : icvir)
| Merge (_ : icvir) (_ : icvir)
| Join (_ : nat) (_ : icvir).

Definition Sequence (c1 c2 : icvir) : icvir :=
  Loop 1 (PermuteInputs (Merge c1 c2)).

(* Definition If (e : texp typ) (ct cf : icvir) := *)
(*   let cond := Block (Branch e) [] in *)
(*   let body := Join 2 (Merge ct cf) in *)
(*   Sequence cond body. *)


Record FST := mk_FST
  {
    inputs_visibles : list block_id;
    outputs_visibles : list block_id;
    counter_reg : nat; 
    counter_bid : nat
  }.

Definition fresh_init : FST := mk_FST [] [] 0 0.

Definition fresh : Type -> Type := fun X => FST -> (FST * X).

#[global] Instance freshM : Monad fresh := 
 {|
  ret := fun _ x s => (s,x);
  bind := fun _ _ c k s => let '(s',x) := c s in k x s'
  |}.
Import MonadNotation.  

(* Variable (name : nat -> block_id). *)
Definition name := mk_anon.

Definition getReg : fresh block_id :=
  fun '(mk_FST i o r b) =>
    (mk_FST i o (S r) b , name r).

Definition getLab : fresh block_id :=
  fun '(mk_FST i o r b) =>
    (mk_FST i o r (S b) , name b).

Definition setInputs (inputs : list block_id) : fresh _ :=
  fun '(mk_FST _ o r b) => (mk_FST inputs o r (S b), tt).

Definition setOutputs (outputs : list block_id) : fresh _ :=
  fun '(mk_FST i _ r b) => (mk_FST i outputs r (S b), tt).

Definition getInputs : fresh (list block_id) :=
  fun '(mk_FST i o r b) =>
    (mk_FST i o r b, i).

Definition getOutputs : fresh (list block_id) :=
  fun '(mk_FST i o r b) =>
    (mk_FST i o r b, o).


Fixpoint eval (cir : icvir) : fresh (list (block typ)) :=
  match cir with

  | Block Simple c =>
    input <- getLab;;
    output <- getLab;;
    setInputs [input];;
    setOutputs [output];;
    ret [mk_block input [] c (TERM_Br_1 output) None]

  | Block (Return e) c =>
    input <- getLab;;
    setInputs [input];;
    setOutputs [];;
    ret [mk_block input [] c (TERM_Ret e) None]

 | Block Void c =>
    input <- getLab;;
    setInputs [input];;
    setOutputs [];;
    ret [mk_block input [] c TERM_Ret_void None]

 | Block (Branch e) c =>
    input <- getLab;;
    outL <- getLab;;
    outR <- getLab;;
    setInputs [input];;
    setOutputs [outL;outR];;
    ret [mk_block input [] c (TERM_Br e outL outR) None]

  | PermuteInputs ir => (* Note: has been simplified. General Case? *)
    g <- eval ir;;
    ins <- getInputs ;;
    outs <- getOutputs ;;
    let rename_map := (mk_map ins (cycle ins)) in
    ret (ocfg_relabel rename_map g)

  | PermuteOutputs ir => (* Note: has been simplified. General Case? *)
    g <- eval ir;;
    ins <- getInputs ;;
    outs <- getOutputs ;;
    let rename_map := (mk_map outs (cycle outs)) in
    ret (ocfg_relabel rename_map g)

  | Join k ir =>
    g <- eval ir;;
    ins <- getInputs ;;
    outs <- getOutputs ;;
    merge <- getLab;;
    let rename_map := (mk_map (firstn k outs) (List.repeat merge k)) in
    setInputs ins;;
    setOutputs (merge :: skipn k outs);; (* we rename the k-first and don't touch the others *)
    ret (ocfg_relabel rename_map g)

  | Loop k ir =>
    g <- eval ir;;
    ins <- getInputs ;;
    outs <- getOutputs ;;
    let rename_map := (mk_map (firstn k ins) (firstn k outs)) in
    setInputs (skipn k ins);;
    setOutputs (skipn k outs);;
    ret (ocfg_relabel rename_map g)

  | Merge ir1 ir2 =>
    g1 <- eval ir1;;
    ins1 <- getInputs ;;
    outs1 <- getOutputs ;;
    g2 <- eval ir2;;
    ins2 <- getInputs ;;
    outs2 <- getOutputs ;;
    setInputs (ins1 ++ ins2);;
    setOutputs (outs1 ++ outs2);;
    ret (g1++g2)
  end.

Definition eval_top (cir : icvir) :=
  eval cir fresh_init.

Notation conv := (convert_typ []).

Lemma norepet_singleton : forall {A} (x : A),
  Coqlib.list_norepet [x].
Proof.
  intros.
  apply Coqlib.list_norepet_cons ; auto.
  apply Coqlib.list_norepet_nil.
Qed.

(** -- Well-Formness -- *)

Lemma getInputs_invariant :
 forall σ σ' l, getInputs σ = (σ', l) -> σ = σ'.
Proof.
  unfold getInputs.
  intros.
  flatten_all.
  inv H. reflexivity.
Qed.

Lemma getOutputs_invariant :
 forall σ σ' l, getOutputs σ = (σ', l) -> σ = σ'.
Proof.
  unfold getOutputs.
  intros.
  flatten_all.
  inv H. reflexivity.
Qed.

(* Ltac unfold_freshness := *)
(*   repeat ( *)
(*   match goal with *)
(*   | h: context[(_,_) = (_,_)] |- _ => inv h *)
(*   | h: context[getInputs _ = (_,_)] |- _ => apply getInputs_invariant in h ; try subst *)
(*   | h: context[getOutputs _ = (_,_)] |- _ => apply getOutputs_invariant in h ; try subst *)
(*   | h: context[setInputs _ _ = (_,_)] |- _ => *)
(*     unfold setInputs in h ; try (flatten_hyp h) ; inv h *)
(*   | h: context[setOutputs _ _ = (_,_)] |- _ => *)
(*     unfold setOutputs in h ; try (flatten_hyp h) ; inv h *)
(*   | |- _ => idtac *)
(*   end ; simpl in * *)
(*     ). *)

Ltac unfold_freshness :=
  repeat (
  match goal with
  | h: context[(_,_) = (_,_)] |- _ => inv h
  | h: context[getInputs _ = (_,_)] |- _ =>
    unfold getInputs in h ; try (flatten_hyp h) ; inv h ; subst
  | h: context[getOutputs _ = (_,_)] |- _ =>
    unfold getOutputs in h ; try (flatten_hyp h) ; inv h ; subst
  | h: context[setInputs _ _ = (_,_)] |- _ =>
    unfold setInputs in h ; try (flatten_hyp h) ; inv h ; subst
  | h: context[setOutputs _ _ = (_,_)] |- _ =>
    unfold setOutputs in h ; try (flatten_hyp h) ; inv h ; subst
  | |- _ => idtac
  end ; simpl in *
    ).


(* NOTE this lemma is too strong: we want that the invariant holds for an arbitrary number
        of getLab calls *)
Lemma freshness_get_label : forall (σ σ' σ'' : FST) l l',
  getLab σ = (σ', l) ->
  getLab σ' = (σ'', l') ->
  (l <> l')%nat.
Proof.
  intros.
  destruct σ,  σ'.
  unfold getLab in *.
  inv H; inv H0. unfold name,mk_anon.
  intro; injection H; lia.
Qed.

Theorem ins_outs_disjoints : forall (ir : icvir) (σ s s' s'' : FST) li lo b,
  (eval ir σ) = (s,b) ->
  getInputs s = (s',li) ->
  getOutputs s' = (s'',lo) ->
  Coqlib.list_disjoint li lo.
Proof.
  induction ir ; intros.
  - (* Block *)
    destruct b;
    simpl in H;
    repeat flatten_hyp H.
    + apply (freshness_get_label σ f f0 b b1) in Heq; auto.
      unfold_freshness.
      unfold Coqlib.list_disjoint ; intros ; simpl in H, H0.
      intuition; now subst.
    + unfold_freshness.
      unfold Coqlib.list_disjoint ; intros ; simpl in H0 ; contradiction.
    + unfold_freshness.
      unfold Coqlib.list_disjoint ; intros ; simpl in H0 ; contradiction.
    + apply (freshness_get_label σ f f0 b b1) in Heq; auto.
      unfold_freshness.
      apply (freshness_get_label f f0 {|
            inputs_visibles := inputs_visibles0;
            outputs_visibles := outputs_visibles0;
            counter_reg := counter_reg0;
            counter_bid := counter_bid1
          |} b1 b2) in Heq0; auto.
      unfold Coqlib.list_disjoint ; intros ; simpl in H, H0.
      assert ( b <> b2). { admit. }
      intuition; now subst.
  - (* PermuteInputs *)
    simpl in H ; repeat flatten_hyp H.
    apply (IHir σ f f0 f1 li lo l);
    try (assumption) ;
    try (
    inv H;
    unfold_freshness; reflexivity).
  - (* PermuteOutputs *) admit.
  - (* Loop *)
    simpl in H ; repeat flatten_hyp H.
    assert (Hdisjoint : Coqlib.list_disjoint l0 l1).
    {apply (IHir σ f f0 f1 l0 l1 l); assumption. }
    unfold_freshness.
    (* l0 ## l1 => (skipn n l0)##(skipn n l1)*)
    admit.
  - (* Merge *)
    simpl in H ; repeat flatten_hyp H.
    assert (Hdisjoint1 : Coqlib.list_disjoint l0 l1).
    {apply (IHir1 σ f f0 f1 l0 l1 l); assumption. }
    assert (Hdisjoint2 : Coqlib.list_disjoint l3 l4).
    {apply (IHir2 f1 f2 f3 f4 l3 l4 l2); assumption. }
    unfold_freshness.
    apply Util.list_disjoint_app_l ; split ;
    apply Util.list_disjoint_app_r ; split; (try assumption).
    admit. admit.
  - (* Join *)
    simpl in H ; repeat flatten_hyp H.
    assert (Hdisjoint : Coqlib.list_disjoint l0 l1).
    {apply (IHir σ f f0 f1 l0 l1 l); assumption. }
    (* we should ensure something about the new bid *)
    unfold_freshness.
Admitted.

Theorem uniqueness : forall (ir : icvir) (σ : FST),
  wf_ocfg_bid (snd ((eval ir) σ)).
Proof.
  induction ir ; intros.
  - (* Block *)
    destruct b ; simpl ;
    repeat flatten_all ; simpl ;
    unfold wf_ocfg_bid;
    unfold inputs;
    simpl ; apply norepet_singleton.
  - (* PermuteInputs *)
    simpl ;
    repeat flatten_all ; simpl.
    specialize (IHir σ).
    rewrite Heq in IHir. simpl in IHir.
    (* we need to prove that ocfg_relabel preserve the uniqueness if
       - the mapping is injective (1)
       - the list of block was unique (OK)

      For 1, we need to prove that cycle is injective, thus the mapping will
      be injective
     *)
    admit.
  - (* PermuteOutputs *)
    simpl ; repeat flatten_all ; simpl.
    specialize (IHir σ). rewrite Heq in IHir. simpl in IHir.
    (* Similar as PermuteInputs*)
    admit.
  - (* Loop n *)
    simpl ; repeat flatten_all ; simpl.
    specialize (IHir σ). rewrite Heq in IHir. simpl in IHir.
    (* Same as PermuteInput, but prove that
    (mk_map (firstn n l0) (firstn n l1)) is injective *)
    admit.
  - (* Merge *)
    simpl ; repeat flatten_all ; simpl.
    unfold_freshness.
    set (σ' := {|
             inputs_visibles := l0;
             outputs_visibles := l1;
             counter_reg := counter_reg1;
             counter_bid := counter_bid1
           |}) ; replace ( {|
             inputs_visibles := l0;
             outputs_visibles := l1;
             counter_reg := counter_reg1;
             counter_bid := counter_bid1
           |} ) with σ' in * ; auto.
    specialize ( IHir1 σ ).
    specialize ( IHir2 σ' ).
    rewrite Heq in IHir1; rewrite Heq2 in IHir2 ; simpl in *.
    unfold wf_ocfg_bid in *.
    rewrite ScopeTheory.inputs_app.
    apply Coqlib.list_norepet_append ; auto.
    (* disjointness between the ID produces by the monad *)
    admit.
  -  (* Join *)
    simpl ; repeat flatten_all ; simpl.
    (* Steps:
        1. For each evaluation, the list of exposed inputs and outputs are
           disjoints
        2. l1 contains only outputs. Using (1), l1 ## inputs l.
        3. first n l1 ⊆ l1, thus (first n l1) ## inputs l.
        4. ocfg_relabel do not rename inputs, thus it suffice to prove
          (wf_ocfg_bid l) (with is an hypothesis)
     *)
    admit.
Admitted.

(** -- Semantics -- *)

From Vellvm Require Import Semantics.
Import ITreeNotations.

Definition sem (i : icvir) : fresh _ :=
  bks <- eval i;;
  ret (denote_ocfg (conv bks)).

Lemma blockSimple_sound :
  forall c σ fto,
  eutt eq
       (snd (sem (Block Simple c) σ) fto)
       (let (src,target) :=
          (snd ((input <- getLab ;;
                 output <- getLab ;;
                 ret (input,output)) σ)) in
        x <- denote_code (conv c) ;; ret (inl (src,target))).
Proof.
  intros.
  unfold sem.
  simpl. repeat flatten_all.
  unfold_freshness.
  clear -Heq1.
  unfold getLab in Heq1.
  unfold denote_ocfg.
  (* it seems to be false (because of the fto...) *)
Admitted.

(* TODO blockRet *)
(* TODO blockBranch *)
(* TODO blockRetVoid *)

Lemma merge_sound :
 forall (ir1 ir2 : icvir) (σ : FST) (fto : block_id * block_id),
 eutt eq
      (snd (sem (Merge ir1 ir2) σ) fto)
      (let (σ1, t1) := (sem ir1 σ) in
       let (σ2, t2) := (sem ir2 σ1) in
       let (_,to) := fto in
       if (existsb (fun e => eq_bid to e) (inputs_visibles σ1))
       then t1 fto (* the field "to" points to the left CIR *)
       else t2 fto (* the field "to" points to the right CIR *)
      ).
Proof.
  intros.
  unfold sem.
  simpl.
  repeat flatten_all ;
  unfold_freshness ;
  rewrite Heq3 in Heq9 ; clear Heq3 ; inv Heq9.
Admitted.

(* Permute is WRONG:
   we can't just permute the list, we have to apply the relabeling in the CFG
 *)
Lemma permuteInput_sound :
 forall (ir : icvir) (σ : FST) (fto : block_id * block_id),
 eutt eq
      (snd (sem (PermuteInputs ir) σ) fto)
      (let (σ', t) := sem ir σ in
       let inputs := inputs_visibles σ' in
       let outputs := outputs_visibles σ' in
       let (from, src) := fto in
       let i := find_nth_error inputs src in
       match i with
       | None => t fto
       | Some i =>
         (let nsrc := nth_error inputs ((i+1) mod (length inputs)) in
          match nsrc with
          | None => t (from, src) (* impossible because of mod *)
          | Some nsrc => t (from, nsrc)
          end)
       end ).
Proof.
  intros.
  unfold sem.
  simpl.
  repeat flatten_all ; simpl ;
  unfold_freshness.
  2:{apply nth_error_none in Heq5. rewrite Heq5 in Heq4. cbn in Heq4 ; discriminate. }
Admitted.


Lemma loop_sound :
  forall (ir : icvir) (k : nat) (σ : FST) (fto : block_id * block_id),
  eutt eq
       (snd (sem (Loop k ir) σ) fto)
       (iter (C := Kleisli _)
               (fun '(from,src) =>
                  let (σ', t) := sem ir σ in
                  let inputs := inputs_visibles σ' in
                  let outputs := outputs_visibles σ' in
                  fto' <- t (from,src) ;; (* : fto' : (bid*bid + dvalue)*)
                  match fto' with
                  | inr dv => ret (inr (inr dv)) (* if dvalue, stops the iter and return the value*)
                  | inl (src,target) =>
                    (let i := find_nth outputs target in
                     if (Nat.ltb i k)
                     then (
                        match nth_error inputs (i mod (length inputs)) with
                        | None => ret (inl (src,target)) (* TODO : raise an error ? *)
                        | Some ntarget => ret (inl (src,ntarget))
                        end)
                     else
                       ret (inr (inl (src,target))))
                  end)
               fto).
Proof.
  intros.
  unfold sem.
  simpl.
  repeat flatten_all ;
  unfold_freshness.

  rewrite unfold_iter_ktree.
  unfold denote_ocfg at 1.
Admitted.

Lemma join_sound :
  forall (ir : icvir) (k : nat) (σ : FST) (fto : block_id * block_id),
  eutt eq
       (snd (sem (Join k ir) σ) fto)
       (let (σ', t) := sem ir σ in
        let outputs := outputs_visibles σ' in
        fto' <- t fto ;; (* : fto' : (bid*bid + dvalue)*)
        match fto' with
        | inr dv => ret (inr dv) (* if dvalue, stops the iter and return the value*)
        | inl (src,target) =>
          let i := find_nth outputs target in
          if (Nat.ltb i k)
          then ret (inl (src,(snd ((new_lab <- getLab ;; ret new_lab) σ)))) (* target new label *)
          else ret (inl (src,target)) (* no change *)
        end).
Proof.
  intros.
  unfold sem.
  simpl.
  repeat flatten_all.
  simpl.
  unfold_freshness.
  (* unfold getLab in H0. *)
  (* unfold getLab in Heq6. *)
Admitted.

Lemma seq_sound : forall (ir1 ir2 : icvir) σ fto,
    (snd (sem (Sequence ir1 ir2) σ) fto)
      ≈
      (let (σ',t) := sem ir1 σ in
       fto' <- (t fto) ;;
       match fto' with
       | inr dv => ret (inr dv)
       | inl fto' => snd (sem ir2 σ') fto'
       end).
Proof.
  intros.
  simpl.
  unfold Sequence.
  rewrite loop_sound.
  simpl.
  repeat flatten_goal.
  assert (Hi0 : i0 = snd (sem ir1 σ)).
  { rewrite Heq0 ; reflexivity. }
  subst i0.
  unfold sem in Heq.
  simpl in Heq.
  repeat flatten_all.
  unfold_freshness.
Admitted.


From ExtLib Require Import
     Structures.Monads
     Data.Monads.OptionMonad.

Import MonadNotation.


From Vellvm Require Import
     Utils.Tactics.
From Imp2Vir Require Import Imp.
From Vellvm Require Import SurfaceSyntax.
Import VIR_Notations.
From Coq Require Import Strings.String.
Require Import CompileExpr.

Fixpoint compile_imp (next_reg : int) (s : stmt) (env: StringMap.t int)
  : option (int * (StringMap.t int) * icvir) :=
  match s with
  | Skip => Some(next_reg, env, Block Simple [])
  | Assign x e =>
    '(next_reg, env, ir) <- compile_assign next_reg x e env;;
    ret (next_reg, env, Block Simple ir)

  | Seq l r =>
    '(next_reg, env, ir_l) <- compile_imp next_reg l env;;
    '(next_reg, env, ir_r) <- compile_imp next_reg r env;;
    ret (next_reg, env, (Sequence ir_l ir_r))

  | While e b =>
    '(cond_reg, expr_ir) <- compile_cond next_reg e env;;
    '(next_reg, _, ir) <- compile_imp (cond_reg + 1) b env;;
    ret (next_reg, env, ir) (* TODO *)

  | If e l r =>
    '(cond_reg, expr_code) <- compile_cond next_reg e env;;
    '(next_reg, _, ir_l) <- compile_imp (cond_reg + 1) l env;;
    '(next_reg, _, ir_r) <- compile_imp next_reg r env;;
    ret (next_reg, env, ir_l) (* TODO *)
  end.

Definition compile_icvir (s : stmt) :=
  '(_, _, ir) <- compile_imp 0 s (StringMap.empty int);;
  ret (snd (eval_top ir)).

Compute (compile_imp 0 (trivial_seq "a" "b" 42) (StringMap.empty int)).
Compute (compile_icvir (trivial_seq "a" "b" 42)).


End CvirSyntax.
