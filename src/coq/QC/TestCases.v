(** This file contains some interesting test cases generated from QC,
    and some lemmas related to them.
 *)
From QuickChick Require Import QuickChick.
From Vellvm Require Import ShowAST ReprAST GenAST QCVellvm TopLevel LLVMAst DynamicValues.
Require Import Semantics.LLVMEvents.
Require Import Semantics.InterpretationStack.
Require Import Handlers.Handlers.

Require Import String.
Require Import ZArith.

From ITree Require Import
     ITree
     Interp.Recursion
     Events.Exception.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Require Import List.
Import ListNotations.



(*** Extraction Bug *)

(* There seems to be an issue with how QuickChick is running the test cases.

   More info here: https://github.com/vellvm/vellvm/issues/161

   QC sometimes reports that vellvm disagrees with clang. However,
   when the test case is run with `./vellvm -interpret`, we see that
   vellvm does actually agree with clang.

   Initially we thought the issue might have to do with how we are
   serializing the Vellvm AST to a LLVM file, or parsing it in,
   however, I am confident at this point that this is *NOT* the
   problem.

   Below is an example of a program where this problem occurs.

   - repr_prog is the representation returned by ReprAST.
   - parsed_prog is what we get from `./vellvm -print-ast`.

   Both of these programs should be equivalent, and they
   are... However, when generated and run through the interpreter in
   QC it returns the wrong value.
 *)


Definition repr_prog : list (toplevel_entity typ (block typ * list (block typ))) := [(TLE_Definition (mk_definition _ (mk_declaration (Name "main") (TYPE_Function ((TYPE_I 8)) []) ([], []) None None None None [] None None None) [] ((mk_block (Name "b0") [] [] (TERM_Br_1 (Name "b1")) None), [(mk_block (Name "b1") [] [((IId (Name "v0")), (INSTR_Op (OP_IBinop And (TYPE_I 64) (EXP_Integer (-3)%Z) (EXP_Integer (-3)%Z)))); ((IId (Name "v1")), (INSTR_Op (OP_ICmp Ule (TYPE_I 64) (EXP_Ident (ID_Local (Name "v0"))) (EXP_Integer (8)%Z)))); ((IId (Name "v2")), (INSTR_Op (OP_Select ( (TYPE_I 1), (EXP_Ident (ID_Local (Name "v1")))) ((TYPE_I 64), (EXP_Ident (ID_Local (Name "v0")))) ((TYPE_I 64), (EXP_Integer (8)%Z))))); ((IId (Name "v3")), (INSTR_Op (OP_ICmp Ugt (TYPE_I 64) (EXP_Ident (ID_Local (Name "v2"))) (EXP_Integer (0)%Z))))] (TERM_Br ((TYPE_I 1), (EXP_Ident (ID_Local (Name "v3")))) (Name "b4") (Name "b2")) None); (mk_block (Name "b4") [((Name "v5"), (Phi (TYPE_I 64)[((Name "b1"), (EXP_Ident (ID_Local (Name "v2")))); ((Name "b3"), (EXP_Ident (ID_Local (Name "v6"))))]))] [((IId (Name "v8")), (INSTR_Op (OP_IBinop And (TYPE_I 32) (EXP_Integer (1)%Z) (EXP_Integer (-3)%Z)))); ((IId (Name "v9")), (INSTR_Alloca (TYPE_I 8) None None)); ((IVoid (1)%Z), (INSTR_Store false ((TYPE_I 8), (EXP_Integer (0)%Z)) ((TYPE_Pointer (TYPE_I 8)), (EXP_Ident (ID_Local (Name "v9")))) None)); ((IId (Name "v10")), (INSTR_Alloca (TYPE_I 8) None None)); ((IVoid (2)%Z), (INSTR_Store false ((TYPE_I 8), (EXP_Integer (0)%Z)) ((TYPE_Pointer (TYPE_I 8)), (EXP_Ident (ID_Local (Name "v10")))) None))] (TERM_Ret ((TYPE_I 8), (EXP_Integer (0)%Z))) None); (mk_block (Name "b3") [] [((IId (Name "v6")), (INSTR_Op (OP_IBinop (Sub false false) (TYPE_I 64) (EXP_Ident (ID_Local (Name "v5"))) (EXP_Integer (1)%Z)))); ((IId (Name "v7")), (INSTR_Op (OP_ICmp Ugt (TYPE_I 64) (EXP_Ident (ID_Local (Name "v6"))) (EXP_Integer (0)%Z))))] (TERM_Br ((TYPE_I 1), (EXP_Ident (ID_Local (Name "v7")))) (Name "b4") (Name "b2")) None); (mk_block (Name "b2") [] [((IId (Name "v4")), (INSTR_Alloca (TYPE_I 1) None None)); ((IVoid (0)%Z), (INSTR_Store true ((TYPE_I 1), (EXP_Ident (ID_Local (Name "v3")))) ((TYPE_Pointer (TYPE_I 1)), (EXP_Ident (ID_Local (Name "v4")))) None))] (TERM_Ret ((TYPE_I 8), (EXP_Integer (3)%Z))) None)])))].

Compute (show repr_prog).

Definition parsed_prog : list (toplevel_entity typ (block typ * list (block typ))) :=
  [TLE_Definition {|
       df_prototype := {|dc_name := (Name "main");
                         dc_type := (TYPE_Function (TYPE_I 8%N) []);
                         dc_param_attrs := ([], []);
                         dc_linkage := None;
                         dc_visibility := None;
                         dc_dll_storage := None;
                         dc_cconv := None;
                         dc_attrs := [];
                         dc_section := None;
                         dc_align := None;
                         dc_gc := None|};
       df_args := [];
       df_instrs := (
                     {|
                       blk_id := (Name "b0");
                       blk_phis := [];
                       blk_code := [];
                       blk_term := TERM_Br_1 (Name "b1");
                       blk_comments := None
                     |},
                       [{|
                         blk_id := (Name "b1");
                         blk_phis := [];
                         blk_code := [(IId (Name "v0"), (INSTR_Op (OP_IBinop And (TYPE_I 64%N) (EXP_Integer (-3)%Z) (EXP_Integer (-3)%Z))));
                                     (IId (Name "v1"), (INSTR_Op (OP_ICmp Ule (TYPE_I 64%N) (EXP_Ident (ID_Local (Name "v0"))) (EXP_Integer (8)%Z))));
                                     (IId (Name "v2"), (INSTR_Op (OP_Select ((TYPE_I 1%N),(EXP_Ident (ID_Local (Name "v1")))) ((TYPE_I 64%N),(EXP_Ident (ID_Local (Name "v0")))) ((TYPE_I 64%N),(EXP_Integer (8)%Z)))));
                                     (IId (Name "v3"), (INSTR_Op (OP_ICmp Ugt (TYPE_I 64%N) (EXP_Ident (ID_Local (Name "v2"))) (EXP_Integer (0)%Z))))];
                         blk_term := TERM_Br ((TYPE_I 1%N), (EXP_Ident (ID_Local (Name "v3")))) (Name "b4") (Name "b2");
                         blk_comments := None
                       |};
                   {|
                     blk_id := (Name "b4");
                     blk_phis := [((Name "v5"), Phi (TYPE_I 64%N) [((Name "b3"), (EXP_Ident (ID_Local (Name "v6")))); ((Name "b1"), (EXP_Ident (ID_Local (Name "v2"))))])];
                     blk_code := [(IId (Name "v8"), (INSTR_Op (OP_IBinop And (TYPE_I 32%N) (EXP_Integer (1)%Z) (EXP_Integer (-3)%Z))));
                                 (IId (Name "v9"), (INSTR_Alloca (TYPE_I 8%N) None None));
                                 (IVoid 0%Z, (INSTR_Store false ((TYPE_I 8%N), (EXP_Integer (0)%Z)) ((TYPE_Pointer (TYPE_I 8%N)), (EXP_Ident (ID_Local (Name "v9")))) None));
                                 (IId (Name "v10"), (INSTR_Alloca (TYPE_I 8%N) None None));
                                 (IVoid 1%Z, (INSTR_Store false ((TYPE_I 8%N), (EXP_Integer (0)%Z)) ((TYPE_Pointer (TYPE_I 8%N)), (EXP_Ident (ID_Local (Name "v10")))) None))];
                     blk_term := TERM_Ret ((TYPE_I 8%N), (EXP_Integer (0)%Z));
                     blk_comments := None
                   |};
                   {|
                     blk_id := (Name "b3");
                     blk_phis := [];
                     blk_code := [(IId (Name "v6"), (INSTR_Op (OP_IBinop (Sub false false) (TYPE_I 64%N) (EXP_Ident (ID_Local (Name "v5"))) (EXP_Integer (1)%Z))));
                                 (IId (Name "v7"), (INSTR_Op (OP_ICmp Ugt (TYPE_I 64%N) (EXP_Ident (ID_Local (Name "v6"))) (EXP_Integer (0)%Z))))];
                     blk_term := TERM_Br ((TYPE_I 1%N), (EXP_Ident (ID_Local (Name "v7")))) (Name "b4") (Name "b2");
                     blk_comments := None
                   |};
                   {|
                     blk_id := (Name "b2");
                     blk_phis := [];
                     blk_code := [(IId (Name "v4"), (INSTR_Alloca (TYPE_I 1%N) None None));
                                 (IVoid 2%Z, (INSTR_Store false ((TYPE_I 1%N), (EXP_Ident (ID_Local (Name "v3")))) ((TYPE_Pointer (TYPE_I 1%N)), (EXP_Ident (ID_Local (Name "v4")))) None))];
                     blk_term := TERM_Ret ((TYPE_I 8%N), (EXP_Integer (3)%Z));
                     blk_comments := None
                   |}])
     |}].


Extract Constant defNumTests    => "1".

(* For some reason both of these programs disagree with clang when run
   through QC, even though they both agree when run with
   `./vellvm -interpret`. *)
QuickChick (vellvm_agrees_with_clang repr_prog).
QuickChick (vellvm_agrees_with_clang parsed_prog).

(** This is a simpler program, that is shrunk from the above that exhibits the same problem.

    Note that it is not an issue with branching being wrong. If we
    change Ule to Ne, we would expect the branching to be the same,
    but the problem goes away.

    Similarly, it shouldn't be the case the Ule is implemented incorrectly, because
    `./vellvm -interpret` does the correct thing, and it runs Ule in the exact same fashion.
 *)
Definition shrunk_program : list (toplevel_entity typ (block typ * list (block typ))) :=
  [TLE_Definition {|
       df_prototype := {|dc_name := (Name "main");
                         dc_type := (TYPE_Function (TYPE_I 8%N) []);
                         dc_param_attrs := ([], []);
                         dc_linkage := None;
                         dc_visibility := None;
                         dc_dll_storage := None;
                         dc_cconv := None;
                         dc_attrs := [];
                         dc_section := None;
                         dc_align := None;
                         dc_gc := None|};
       df_args := [];
       df_instrs := (
                     {|
                       blk_id := (Name "b1");
                       blk_phis := [];
                       blk_code := [(IId (Name "v0"), (INSTR_Op (OP_IBinop Or (TYPE_I 64%N) (EXP_Integer (0)%Z) (EXP_Integer (-3)%Z))));
                                   (IId (Name "v1"), (INSTR_Op (OP_ICmp Ule (TYPE_I 64%N) (EXP_Ident (ID_Local (Name "v0"))) (EXP_Integer (8)%Z))))
                                   ];
                       blk_term := (* TERM_Ret ((TYPE_I 8%N), (EXP_Ident (ID_Local (Name "result")))); *)
                         TERM_Br ((TYPE_I 1%N), (EXP_Ident (ID_Local (Name "v1")))) (Name "b4") (Name "b2");
                       blk_comments := None
                     |},
                       [
                   {|
                     blk_id := (Name "b4");
                     blk_phis := [];
                     blk_code := [];
                     blk_term := TERM_Ret ((TYPE_I 8%N), (EXP_Integer (0)%Z));
                     blk_comments := None
                   |};
                   {|
                     blk_id := (Name "b2");
                     blk_phis := [];
                     blk_code := [];
                     blk_term := TERM_Ret ((TYPE_I 8%N), (EXP_Integer (3)%Z));
                     blk_comments := None
                   |}])
     |}].

QuickChick (vellvm_agrees_with_clang shrunk_program).


From ITree Require Import
     ITree
     Eq.Eqit
     TranslateFacts.

From Vellvm Require Import
     Utils.Tactics
     Syntax.LLVMAst
     Syntax.CFG
     Syntax.Traversal
     Syntax.Scope
     Syntax.ScopeTheory
     Syntax.TypToDtyp
     Semantics.InterpretationStack
     Semantics.TopLevel
     Theory.DenotationTheory
     Theory.ExpLemmas
     Theory.InstrLemmas
     Theory.InterpreterCFG
     Theory.SymbolicInterpreter.


Ltac vred_r :=
  let R := fresh
  in eutt_hide_rel_named R;
     let X := fresh
     in eutt_hide_left_named X; vred_C3;
        subst X; subst R.

Check interp_cfg3.


From Vellvm Require Import
     Utilities
     Syntax
     Semantics.LLVMEvents
     Semantics.Denotation
     Handlers.Handlers.

(* This just extracts the main function (the only one) from the shrunk program *)
Definition shrunk_cfg : cfg dtyp :=
    {|
      init := (Name "b1");
      blks := [{|
                  blk_id := (Name "b1");
                  blk_phis := [];
                  blk_code := [(IId (Name "v0"), (INSTR_Op (OP_IBinop Or (DTYPE_I 64%N) (EXP_Integer (0)%Z) (EXP_Integer (-3)%Z))));
                              (IId (Name "v1"), (INSTR_Op (OP_ICmp Ule (DTYPE_I 64%N) (EXP_Ident (ID_Local (Name "v0"))) (EXP_Integer (8)%Z))))
                              ];
                  blk_term := (* TERM_Ret ((TYPE_I 8%N), (EXP_Ident (ID_Local (Name "result")))); *)
                    TERM_Br ((DTYPE_I 1%N), (EXP_Ident (ID_Local (Name "v1")))) (Name "b4") (Name "b2");
                  blk_comments := None
                |};
                 {|
                   blk_id := (Name "b4");
                   blk_phis := [];
                   blk_code := [];
                   blk_term := TERM_Ret ((DTYPE_I 8%N), (EXP_Integer (0)%Z));
                   blk_comments := None
                 |};
               {|
                 blk_id := (Name "b2");
                 blk_phis := [];
                 blk_code := [];
                 blk_term := TERM_Ret ((DTYPE_I 8%N), (EXP_Integer (3)%Z));
                 blk_comments := None
               |}];
      args := []
    |}.


(** Here we prove that the shrunk program should in fact agree with clang...

    For some reason, though, running this program with QC returns 0 instead of 3.
*)
Lemma shrunk_prog_agrees_with_clang :
  forall g l ms,
  eutt (fun uv1 '(ms, (l, (g, uv2))) => uv1 = uv2) (ret (UVALUE_I8 (repr 3))) (interp_cfg3 (denote_cfg shrunk_cfg)  g l ms).
Proof.
  intros g l ms.
  cbn.
  vred_r.

  rewrite denote_ocfg_unfold_in_eq_itree.
  2: {
    rewrite find_block_eq; reflexivity.
  }

  cbn.
  vred_r.

  setoid_rewrite bind_ret_l.
  cbn.
  setoid_rewrite bind_ret_l.
  setoid_rewrite bind_ret_l.
  repeat setoid_rewrite bind_bind.
  repeat setoid_rewrite bind_ret_l.
  vred_r.
  cbn.
  vred_r.

  repeat rewrite translate_ret.
  repeat setoid_rewrite bind_ret_l.
  cbn.

  progress vred_r.
  rewrite interp_cfg3_LW.
  cbn.

  vred_r.
  setoid_rewrite translate_bind.
  setoid_rewrite translate_trigger.
  setoid_rewrite translate_trigger.
  rewrite LU_to_exp_Local.
  rewrite exp_to_instr_Local.
  rewrite bind_trigger.
  cbn.
  rewrite interp_cfg3_vis.
  setoid_rewrite interp_cfg3_LR.
  2: {
    cbn. reflexivity.
  }

  vred_r.
  cbn.

  rewrite translate_ret.
  rewrite interp_cfg3_ret.
  rewrite bind_ret_l.

  progress vred_r.
  rewrite interp_cfg3_LW.
  cbn.

  rewrite bind_ret_l.
  setoid_rewrite translate_bind.
  setoid_rewrite interp_cfg3_bind.
  rewrite bind_bind.
  vred_r.

  setoid_rewrite translate_trigger.
  setoid_rewrite translate_trigger.
  rewrite LU_to_exp_Local.
  rewrite exp_to_instr_Local.

  setoid_rewrite interp_cfg3_LR.
  2: {
    cbn. reflexivity.
  }

  rewrite bind_ret_l.
  cbn.

  rewrite translate_bind.
  cbn.
  progress vred_r.

  replace (eval_int_icmp Ule (Int64.or (Int64.repr 0) (Int64.repr (-3))) (Int64.repr 8)) with (DVALUE_I1 Int1.zero).
  2: {
    reflexivity.
  }

  cbn.
  rewrite translate_ret.
  rewrite interp_cfg3_ret.
  rewrite bind_ret_l.
  cbn.
  rewrite translate_ret.
  rewrite interp_cfg3_ret.
  rewrite bind_ret_l.
  cbn.

  tau_steps.
  rewrite denote_ocfg_unfold_in_eq_itree.
  2: {
    rewrite find_block_ineq.
    2: {
      cbn.
      intros CONTRA. inversion CONTRA.
    }
    rewrite find_block_ineq.
    2: {
      cbn.
      intros CONTRA. inversion CONTRA.
    }
    rewrite find_block_eq; reflexivity.
  }

  cbn.
  apply eqit_Ret.
  reflexivity.
Qed.
