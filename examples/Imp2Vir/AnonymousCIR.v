(* DEPRECIATED *)

From Coq Require Import
     Lists.List
     ZArith.

From Vellvm Require Import Syntax.

Import ListNotations.

From ExtLib Require Import Structures.Monads.

Require Import Vec.

Section AnonymousCIR.

  Record cvir : Type :=
    mk_cvir' {
        n_int : nat;
        blocks : forall
          (i o : block_id)
          (v_int : Vec.t block_id n_int),
          list (block typ);
      }.


  (* Given a blocks, returns the corresponding CVIR *)
  Definition mk_cvir
             {n_int : nat}
             (blocks : forall
                 (i o : block_id)
                 (v_int : Vec.t block_id n_int),
                 list (block typ)
             ) : cvir :=
    {|
      n_int := n_int;
      blocks := blocks
    |}.

  Definition block_cvir (c : code typ) : cvir :=
    mk_cvir (fun i o (vt : Vec.t raw_id 0)
             => [mk_block i List.nil c (TERM_Br_1 o) None]
            ).

  Definition branch_cvir (c : code typ) (cond : texp typ) (c_true c_false : cvir) : cvir :=
    let '(mk_cvir' n_int1 b1) := c_true in
    let '(mk_cvir' n_int2 b2) := c_false in
    mk_cvir ( fun i o (vt : Vec.t raw_id (2+n_int1+n_int2)) =>
                let bid_true := Vec.hd vt in
                let vt := (Vec.tl vt) in
                let bid_false := (Vec.hd vt) in
                let vt := (Vec.tl vt) in
                let '(v_int1,v_int2) := Vec.splitat n_int1 vt in
                ([mk_block i [] c (TERM_Br cond bid_true bid_false) None]
                )++ (b1 bid_true o v_int1) ++ (b2 bid_false o v_int2)
            ).

  Definition seq_cvir (c1 c2 : cvir) : cvir :=
    let '(mk_cvir' n_int1 b1) := c1 in
    let '(mk_cvir' n_int2 b2) := c2 in
    mk_cvir ( fun i o (vt : Vec.t raw_id (1+n_int1+n_int2)) =>
                let bid_seq := Vec.hd vt in
                let '(v_int1,v_int2) := Vec.splitat n_int1 (Vec.tl vt) in
                (b1 i bid_seq v_int1) ++ (b2 bid_seq o v_int2)
            ).
  Definition while_cvir (c : code typ) (cond : texp typ) (body : cvir) : cvir :=
    let '(mk_cvir' n_int1 b1) := body in
    mk_cvir ( fun i o (vt : Vec.t raw_id (1+n_int1)) =>
                let bid_body := Vec.hd vt in
                let vt := (Vec.tl vt) in
                ([mk_block i [] c (TERM_Br cond bid_body o) None]
                )++(b1 bid_body i vt)).

  (* Compilation *)
  From Imp2Vir Require Import Imp.
  From Coq Require Import Strings.String.
  Require Import CompileExpr.
  From ExtLib Require Import
       Structures.Monads
       Data.Monads.OptionMonad.
  Import MonadNotation.

  From Vellvm Require Import SurfaceSyntax.
  Import VIR_Notations.



  Definition entry_block : block typ :=
    mk_block (Anon 0) List.nil List.nil (TERM_Br_1 (Anon 1)) None.
  Definition fnbody := (block typ * list (block typ))%type.
  Definition program := toplevel_entity typ fnbody.

  Fixpoint compile (next_reg : int) (s : stmt) (env: StringMap.t int)
    : option (int * (StringMap.t int) * cvir) :=
    match s with
    | Skip => Some(next_reg, env, block_cvir [])
    | Assign x e =>
        '(next_reg, env, ir) <- compile_assign next_reg x e env;;
        ret (next_reg, env, block_cvir ir)
    | Seq l r =>
        '(next_reg, env, ir_l) <- compile next_reg l env;;
        '(next_reg, env, ir_r) <- compile next_reg r env;;
        ret (next_reg, env, seq_cvir ir_l ir_r)
    | If e l r =>
        '(cond_reg, expr_code) <- compile_cond next_reg e env;;
        '(next_reg, _, ir_l) <- compile (cond_reg + 1) l env;;
        '(next_reg, _, ir_r) <- compile next_reg r env;;
        let ir := branch_cvir expr_code (texp_i1 cond_reg) ir_l ir_r in
        ret (next_reg, env, ir)
    | While e b =>
      '(cond_reg, expr_ir) <- compile_cond next_reg e env;;
      '(next_reg, _, ir) <- compile (cond_reg + 1) b env;;
      let ir := while_cvir expr_ir (texp_i1 cond_reg) ir in
      ret (next_reg, env, ir)
    end.

  Definition compile_imp_cvir (ir : cvir) : program :=
    let ir := seq_cvir ir (block_cvir []) in (* hack to print the result of fact *)
    let n_internals := n_int ir in
    let vt_seq := map Anon (map Z.of_nat (seq 2 n_internals)) in
    let blocks := (blocks ir) (Anon 1) (Anon 2) vt_seq in
    let body := (entry_block, blocks) in
    let decl := mk_declaration
                  (Name "main")
                  (TYPE_Function (TYPE_I 32) [TYPE_I 64 ; TYPE_Pointer (TYPE_Pointer (TYPE_I 8))])
                  (nil, nil) None None None None nil None None None
    in
    let def := mk_definition fnbody decl nil body in
    TLE_Definition def.

  Definition compile_program (s : stmt) (env : StringMap.t int) :
    option program :=
    '(_, _, ir) <- compile 0 s env;;
    ret (compile_imp_cvir ir).

  Definition fact_ir := (compile_program (fact "a" "b" 5) (StringMap.empty int)).
  Definition infinite_loop_ir := (compile_program (infinite_loop) (StringMap.empty int)).
  Definition if_ir := (compile_program (trivial_if "a" "b" 0) (StringMap.empty int)).
  (* Definition seq_ir := (compile_program (trivial_seq "a" "b" 42) (StringMap.empty int)). *)
  Definition nested_if_ir := (compile_program (nested_if "a" "b" 42 43) (StringMap.empty int)).
  (* Definition nested_if2_ir := (compile_program (nested_if2 "a" "b" 42 43) (StringMap.empty int)). *)
  Eval compute in fact_ir.
  Eval compute in infinite_loop_ir.
  Eval compute in if_ir.
  Eval compute in nested_if_ir.



  (* Semantic matters *)
From ExtLib Require Import FMapAList.

Definition build_map a b := map Anon (map Z.of_nat (seq a b)).


From ITree Require Import
     ITree
     ITreeFacts.

From Vellvm Require Import
     Semantics
     Syntax.

Definition denote_cvir_gen (ir : cvir) i o vt bid_from bid_to :=
  denote_ocfg (convert_typ nil (blocks ir i o vt)) (bid_from, bid_to).

Definition denote_cvir (ir : cvir) bid bid' :=
  let vt := build_map 2 (n_int ir) in
  denote_cvir_gen ir (Anon 0%Z) (Anon 1%Z) vt bid bid'.

From Vellvm Require Import
     Handlers.Handlers
     Semantics
     Syntax
     Syntax.ScopeTheory
     Utils.AListFacts
     Utils.PostConditions
     Utils.Tactics
     Theory.

  Theorem denote_block_cvir :
    forall c bid_from bid_to,
      eutt eq
           (denote_cvir (block_cvir c) bid_from bid_to)
           ((denote_code (convert_typ nil c)) ;; ret (inl (Anon 0%Z , Anon 1%Z))) .
  Proof.
    unfold block_cvir.
    intros. simpl.
    unfold denote_cvir.
    unfold denote_cvir_gen.
    simpl.
    (* unfold denote_ocfg. *)
  Admitted.



  Theorem denote_seq_cvir :
    forall (ir1 ir2 : cvir) bid_from bid_to,
      eutt eq
           (denote_cvir (seq_cvir ir1 ir2) bid_from bid_to)
           (d <- (denote_cvir ir1 bid_from bid_to) ;;
            match d with
            | inr dv => ret (inr dv)
            | inl (src, target) => denote_cvir ir2 src target (* denote_cvir ir2 should not begin to 0 *)
            end).
  Proof.
    unfold seq_cvir.
    intros. simpl.
  Admitted.


End AnonymousCIR.
