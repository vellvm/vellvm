From Coq Require Import
     (* Arith *)
     (* Strings.String *)
     Lists.List
     ZArith.

From Vellvm Require Import Syntax Semantics .
From Imp2Vir Require Import Relabel.

Import ListNotations.

Section CvirSyntax.

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

Definition Seq (c1 c2 : icvir) : icvir := 
  Loop 1 (PermuteInputs (Merge c1 c2)).

Record cvir := mk_cvir {
    ins : list block_id;
    outs : list block_id;
    cfg : list (block typ);
  }.

Definition relabel_cvir (m : bid_map) (ir : cvir) : cvir :=
  mk_cvir (ins ir) (outs ir) (ocfg_relabel m (cfg ir)).

From ExtLib Require Import
     Structures.Monads.
From ITree Require Import ITree.
From ITree Require Import Eq.

Record FST := mk_FST
  { 
    counter_reg : nat; 
    counter_bid : nat
  }.

Definition fresh_init : FST := mk_FST 0 0.

Definition bump_bid : FST -> FST  :=
  fun '(mk_FST r b) => mk_FST r (S b).

Definition bump_reg : FST -> FST  :=
  fun '(mk_FST r b) => mk_FST (S r) b.

Definition fresh : Type -> Type := fun X => FST -> (FST * X). 

#[global] Instance freshM : Monad fresh := 
 {|
  ret := fun _ x s => (s,x);
  bind := fun _ _ c k s => let '(s',x) := c s in k x s'
  |}.
Import MonadNotation.  

Variable (name : nat -> block_id).

Definition getReg : fresh block_id :=
  fun '(mk_FST r b) => 
    (mk_FST (S r) b , name r).

Definition getLab : fresh block_id :=
  fun '(mk_FST r b) => 
    (mk_FST r (S b) , name b).

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

Fixpoint eval_icvir (cir : icvir) : fresh cvir :=
  match cir with

  | Block Simple c =>
    input <- getLab;;
    output <- getLab;;
    ret (mk_cvir [input] [output]
                 [mk_block input [] c (TERM_Br_1 output) None]
    )

  | Block (Return e) c =>
    input <- getLab;;
    ret (mk_cvir [input] [] [mk_block input [] c (TERM_Ret e) None])

 | Block Void c =>
    input <- getLab;;
    ret (mk_cvir [input] [] [mk_block input [] c TERM_Ret_void None])

 | Block (Branch e) c =>
    input <- getLab;;
    outL <- getLab;;
    outR <- getLab;;
    ret (mk_cvir [input] [outL;outR] [mk_block input [] c (TERM_Br e outL outR) None])

  | PermuteInputs ir => (* Note: has been simplified. General Case? *)
    '(mk_cvir ins outs g) <- eval_icvir ir;;
    ret (mk_cvir
        (cycle ins)
        outs
        g)
    
  | PermuteOutputs ir => (* Note: has been simplified. General Case? Is it useful at all anyway? *)
    '(mk_cvir ins outs g) <- eval_icvir ir;;
    ret (mk_cvir
        ins
        (cycle outs)
        g)
    
  | Join k ir =>
    '(mk_cvir ins outs g) <- eval_icvir ir;;
    merge <- getLab;;
    let rename_map := (mk_map (firstn k outs) (List.repeat merge k)) in
    ret (mk_cvir ins                     (* inputs stays untouched *)
                 (merge :: skipn k outs) (* we rename the k-first and don't touch the others *)
        (ocfg_relabel rename_map g)
    )

 | Loop k ir =>
    '(mk_cvir ins outs g) <- eval_icvir ir;;
    let rename_map := (mk_map (firstn k ins) (firstn k outs)) in
    ret (mk_cvir (skipn k ins)
                 (skipn k outs)
                 (ocfg_relabel rename_map g))

  | Merge ir1 ir2 =>
    '(mk_cvir ins1 outs1 g1) <- eval_icvir ir1;;
    '(mk_cvir ins2 outs2 g2) <- eval_icvir ir2;;
    ret (mk_cvir (ins1 ++ ins2)
                 (outs1 ++ outs2)
                 (g1 ++ g2))

 end.

Definition eval (cir : icvir) : fresh _ :=
  ir <- eval_icvir cir;; 
  ret (cfg ir). 

Definition eval_top (cir : icvir) :=
  eval cir fresh_init.

Notation conv := (convert_typ []).

Definition sem (i : icvir): fresh _ :=
   bks <- eval i;;
   ret (denote_ocfg (conv bks)).

Lemma seq_sound : Prop. 
refine (forall (ir1 ir2 : icvir), _ : Prop).
refine (forall σ fto, 
eutt eq _ _).

refine (snd (sem (Seq ir1 ir2) σ) fto).
refine (x <- snd (sem ir1 σ) fto;; _ (sem ir2)).
 sem (Seq ir1 ir2)) == _ (sem ir1) (sem ir2). 




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

Fixpoint compile (next_reg : int) (s : stmt) (env: StringMap.t int)
  : option (int * (StringMap.t int) * icvir) :=
  match s with
  | Skip => Some(next_reg, env, Block Simple [])
  | Assign x e =>
    '(next_reg, env, ir) <- compile_assign next_reg x e env;;
    ret (next_reg, env, Block Simple ir)

  | Seq l r =>
    '(next_reg, env, ir_l) <- compile next_reg l env;;
    '(next_reg, env, ir_r) <- compile next_reg r env;;
    ret (next_reg, env, (Merge ir_l ir_r))

  | While e b =>
    '(cond_reg, expr_ir) <- compile_cond next_reg e env;;
    '(next_reg, _, ir) <- compile (cond_reg + 1) b env;;
    ret (next_reg, env, ir)

  | If e l r =>
    '(cond_reg, expr_code) <- compile_cond next_reg e env;;
    '(next_reg, _, ir_l) <- compile (cond_reg + 1) l env;;
    '(next_reg, _, ir_r) <- compile next_reg r env;;
    ret (next_reg, env, ir_l)
  end.

Definition compile_eval (s : stmt) :=
  '(_, _, ir) <- compile 0 s (StringMap.empty int);;
    ret (eval_icvir 0 ir).

Compute (compile 0 (trivial_seq "a" "b" 42) (StringMap.empty int)).
Compute (compile_eval (trivial_seq "a" "b" 42)).





End CvirSyntax.

(* Inductive ext_cvir (id_typ : Type) : Type := *)
(* | Core (_ : cvir id_typ) *)
(* | Seq (_ : ext_cvir) (_ : ext_cvir) *)
(* | IfThenElse (branch : ext_cvir) (if_true : ext_cvir) (if_false : ext_cvir) *)
(* | While (cond : ext_cvir). *)
(* (* extended cvir *) *)
