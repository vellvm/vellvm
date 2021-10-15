From Coq Require Import
     (* Arith *)
     (* Strings.String *)
     Lists.List
     ZArith.

From Vellvm Require Import Syntax.
From Imp2Vir Require Import Relabel.

Import ListNotations.

Section CvirSyntax.

Definition mk_anon (n : nat) := Anon (Z.of_nat n).

Variant block_typ : Type :=
  | Simple
  | Ret ( _ : texp typ )
  | Void
  | Branch ( _ : texp typ ).

Inductive icvir : Type :=
| Block (_ : block_typ) ( _ : code typ )
| PermuteInputs ( _ : (list block_id) -> (list block_id)) (_ : icvir)
| PermuteOutputs ( _ : (list block_id) -> (list block_id)) (_ : icvir)
| Loop (_ : nat) (_ : icvir)
| Merge (_ : icvir) (_ : icvir)
| Join (_ : nat) (_ : icvir).

Record cvir := {
    ins : list block_id;
    outs : list block_id;
    cfg : list (block typ);
  }.

Definition mk_cvir (ins outs : list block_id) (cfg : list (block typ))
  : cvir :=
  {|
    ins := ins ;
    outs := outs ;
    cfg := cfg;
  |}.

Definition relabel_cvir (m : bid_map) (ir : cvir) : cvir :=
  mk_cvir (ins ir) (outs ir) (ocfg_relabel m (cfg ir)).

Fixpoint mk_map (l : list block_id) (l' : list block_id) : bid_map :=
  match l with
  | [] => []
  | x1::l1 => (match l' with
             | [] => []
             | x2::l2 => (x1,x2)::(mk_map l1 l2)
             end)
  end.


(* TODO monadic version *)
Fixpoint eval_icvir (n : nat) (cir : icvir) : (nat * cvir) :=
  match cir with
  | Block Simple c =>
    ( n+2, mk_cvir [(mk_anon n)] [(mk_anon (n+1))]
                   [mk_block (mk_anon n) List.nil c (TERM_Br_1 (mk_anon (n+1))) None]
    )
  | Block (Ret e) c =>
    ( n+1, mk_cvir [(mk_anon n)] []
                   [mk_block (mk_anon n) List.nil c (TERM_Ret e) None])
  | Block Void c =>
    ( n+1, mk_cvir [(mk_anon n)] []
                   [mk_block (mk_anon n) List.nil c TERM_Ret_void None])
  | Block (Branch e) c =>
    ( n+3, mk_cvir [(mk_anon n)] [(mk_anon (n+1));(mk_anon (n+2))]
                   [mk_block (mk_anon n) (List.nil) c (TERM_Br e (mk_anon (n+1)) (mk_anon (n+2))) None])
  (* TODO *)
  | PermuteInputs f ir =>
    let (n', ir') := eval_icvir n ir in
    (n',
      mk_cvir
        (f (ins ir'))
        (outs ir')
        (cfg ir')
    )
  | PermuteOutputs f ir =>
    let (n', ir') := eval_icvir n ir in (n', ir')
  | Join k ir =>
    let (n', ir') := eval_icvir n ir in
    let rename_map := (mk_map (firstn k (outs ir')) (List.repeat (mk_anon (n'+1)) k)) in
    (n'+1,
      mk_cvir
        (ins ir') (* inputs stays untouched *)
        (skipn k (outs ir')) (* we rename the k-first and don't touch the others *)
        (ocfg_relabel rename_map (cfg ir'))
    )
  | Loop k ir =>
    let (n', ir') := eval_icvir n ir in
    let rename_map := (mk_map (firstn k (ins ir')) (firstn k (outs ir'))) in
    ( n', mk_cvir
            (skipn k (ins ir'))
            (skipn k (outs ir'))
            (ocfg_relabel rename_map (cfg ir')))
  | Merge ir1 ir2 =>
    let (n1', ir1') := eval_icvir n ir1 in
    let (n2', ir2') := eval_icvir n1' ir2 in
    (n2',
      mk_cvir ((ins ir1')++(ins ir2'))
              ((outs ir1')++(outs ir2'))
              ((cfg ir1')++(cfg ir2')))
  end.

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
