(** Framework for running QC vellvm tests.

    This sets up a step function which mimics the step function in
    interpreter.ml in Coq. This function may not terminate (e.g., when
    given an LLVM program that loops forever), and as such we need to
    disable the Coq termination checker to define it.
 *)
From QuickChick Require Import QuickChick.
From Vellvm Require Import ShowAST ReprAST GenAST TopLevel LLVMAst DynamicValues.
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

(* TODO: Use the existing vellvm version of this? *)
Inductive MlResult a e :=
| MlOk : a -> MlResult a e
| MlError : e -> MlResult a e.

Extract Inductive MlResult => "result" [ "Ok" "Error" ].

Unset Guard Checking.
Fixpoint step (t : ITreeDefinition.itree L5 TopLevel.res_L4) : MlResult DV.uvalue string
  := match observe t with
     | RetF (_,(_,(_,x))) => MlOk _ string x
     | TauF t => step t
     | VisF _ e k => MlError _ string "Uninterpreted event"
     end.
Set Guard Checking.

Definition interpret (prog : list (toplevel_entity typ (block typ * list (block typ)))) : MlResult uvalue string
  := step (TopLevel.interpreter prog).

Axiom to_caml_str : string -> string.
Extract Constant to_caml_str =>
"fun (s: char list) ->
  let r = Bytes.create (List.length s) in
  let rec fill pos = function
  | [] -> r
  | c :: s -> Bytes.set r pos c; fill (pos + 1) s
  in Bytes.to_string (fill 0 s)".


(** Write our LLVM program to a file ("temporary_vellvm.ll"), and then
    use clang to compile this file to an executable, which we then run in
    order to get the return code. *)
Axiom llc_command : string -> int. 
Extract Constant llc_command => "fun prog -> let f = open_out ""temporary_vellvm.ll"" in Printf.fprintf f ""%s"" prog; close_out f; Sys.command ""clang -Wno-everything temporary_vellvm.ll -o vellvmqc && ./vellvmqc""".

Axiom vellvm_print_ll : list (toplevel_entity typ (block typ * list (block typ))) -> string.
Extract Constant vellvm_print_ll => "fun prog -> Llvm_printer.toplevel_entities Format.str_formatter prog; Format.flush_str_formatter".

(** Use the *llc_command* Axiom to run a Vellvm program with clang,
    and wrap up the exit code as a uvalue. *)
Definition run_llc (prog : list (toplevel_entity typ (block typ * list (block typ)))) : uvalue
  := UVALUE_I8 (repr (llc_command (to_caml_str (show prog)))).

(** Basic property to make sure that Vellvm and Clang agree when they
    both produce values *)
Definition vellvm_agrees_with_clang (prog : list (toplevel_entity typ (block typ * list (block typ)))) : Checker
  := 
    (* collect (show prog) *)
            match interpret prog, run_llc prog with
            | MlOk (UVALUE_I8 x), UVALUE_I8 y =>
              whenFail ("Vellvm: " ++ show (unsigned x) ++ " | Clang: " ++ show (unsigned y) ++ " | Ast: " ++ ReprAST.repr prog) (equ x y)
            | _, _ => checker true
            end.

Definition agrees := (forAll (run_GenLLVM gen_llvm) vellvm_agrees_with_clang).
Extract Constant defNumTests    => "1000".
QCInclude "../../ml/*".
QCInclude "../../ml/libvellvm/*".
(* QCInclude "../../ml/libvellvm/llvm_printer.ml". *)
(* QCInclude "../../ml/libvellvm/Camlcoq.ml". *)
(* QCInclude "../../ml/extracted/*ml". *)
QuickChickDebug Debug On.
QuickChick (forAll (run_GenLLVM gen_llvm) vellvm_agrees_with_clang).
(*! QuickChick agrees. *)



Require Import List.
Import ListNotations.


QuickChick (vellvm_agrees_with_clang [(TLE_Definition (mk_definition _ (mk_declaration (Name "main") (TYPE_Function ((TYPE_I 8)) []) ([], []) None None None None [] None None None) [] ((mk_block (Name "b0") [] [] (TERM_Br_1 (Name "b1")) None), [(mk_block (Name "b1") [] [((IId (Name "v0")), (INSTR_Op (OP_IBinop Or (TYPE_I 64) (EXP_Integer (1)%Z) (EXP_Integer (1)%Z)))); ((IId (Name "v1")), (INSTR_Op (OP_ICmp Ule (TYPE_I 64) (EXP_Ident (ID_Local (Name "v0"))) (EXP_Integer (10)%Z)))); ((IId (Name "v2")), (INSTR_Op (OP_Select ( (TYPE_I 1), (EXP_Ident (ID_Local (Name "v1")))) ((TYPE_I 64), (EXP_Ident (ID_Local (Name "v0")))) ((TYPE_I 64), (EXP_Integer (10)%Z))))); ((IId (Name "v3")), (INSTR_Op (OP_ICmp Ugt (TYPE_I 64) (EXP_Ident (ID_Local (Name "v2"))) (EXP_Integer (0)%Z))))] (TERM_Br ((TYPE_I 1), (EXP_Ident (ID_Local (Name "v3")))) (Name "b4") (Name "b2")) None); (mk_block (Name "b4") [((Name "v4"), (Phi (TYPE_I 64)[((Name "b1"), (EXP_Ident (ID_Local (Name "v2")))); ((Name "b3"), (EXP_Ident (ID_Local (Name "v5"))))]))] [] (TERM_Ret ((TYPE_I 8), (EXP_Integer (-1)%Z))) None); (mk_block (Name "b3") [] [((IId (Name "v5")), (INSTR_Op (OP_IBinop (Sub false false) (TYPE_I 64) (EXP_Ident (ID_Local (Name "v4"))) (EXP_Integer (1)%Z)))); ((IId (Name "v6")), (INSTR_Op (OP_ICmp Ugt (TYPE_I 64) (EXP_Ident (ID_Local (Name "v5"))) (EXP_Integer (0)%Z))))] (TERM_Br ((TYPE_I 1), (EXP_Ident (ID_Local (Name "v6")))) (Name "b4") (Name "b2")) None); (mk_block (Name "b2") [] [] (TERM_Ret ((TYPE_I 8), (EXP_Integer (0)%Z))) None)])))]).


Check [(TLE_Definition (mk_definition _ (mk_declaration (Name "main") (TYPE_Function ((TYPE_I 8)) []) ([], []) None None None None [] None None None) [] ((mk_block (Name "b0") [] [] (TERM_Br_1 (Name "b1")) None), [(mk_block (Name "b1") [] [((IId (Name "v0")), (INSTR_Op (OP_IBinop Or (TYPE_I 64) (EXP_Integer (-1)%Z) (EXP_Integer (-1)%Z)))); ((IId (Name "v1")), (INSTR_Op (OP_ICmp Ule (TYPE_I 64) (EXP_Ident (ID_Local (Name "v0"))) (EXP_Integer (10)%Z)))); ((IId (Name "v2")), (INSTR_Op (OP_Select ( (TYPE_I 1), (EXP_Ident (ID_Local (Name "v1")))) ((TYPE_I 64), (EXP_Ident (ID_Local (Name "v0")))) ((TYPE_I 64), (EXP_Integer (10)%Z))))); ((IId (Name "v3")), (INSTR_Op (OP_ICmp Ugt (TYPE_I 64) (EXP_Ident (ID_Local (Name "v2"))) (EXP_Integer (0)%Z))))] (TERM_Br ((TYPE_I 1), (EXP_Ident (ID_Local (Name "v3")))) (Name "b4") (Name "b2")) None); (mk_block (Name "b4") [((Name "v4"), (Phi (TYPE_I 64)[((Name "b1"), (EXP_Ident (ID_Local (Name "v2")))); ((Name "b3"), (EXP_Ident (ID_Local (Name "v5"))))]))] [] (TERM_Ret ((TYPE_I 8), (EXP_Integer (-1)%Z))) None); (mk_block (Name "b3") [] [((IId (Name "v5")), (INSTR_Op (OP_IBinop (Sub false false) (TYPE_I 64) (EXP_Ident (ID_Local (Name "v4"))) (EXP_Integer (1)%Z)))); ((IId (Name "v6")), (INSTR_Op (OP_ICmp Ugt (TYPE_I 64) (EXP_Ident (ID_Local (Name "v5"))) (EXP_Integer (0)%Z))))] (TERM_Br ((TYPE_I 1), (EXP_Ident (ID_Local (Name "v6")))) (Name "b4") (Name "b2")) None); (mk_block (Name "b2") [] [] (TERM_Ret ((TYPE_I 8), (EXP_Integer (0)%Z))) None)])))].

Definition repr_prog : list (toplevel_entity typ (block typ * list (block typ))) := [(TLE_Definition (mk_definition _ (mk_declaration (Name "main") (TYPE_Function ((TYPE_I 8)) []) ([], []) None None None None [] None None None) [] ((mk_block (Name "b0") [] [] (TERM_Br_1 (Name "b1")) None), [(mk_block (Name "b1") [] [((IId (Name "v0")), (INSTR_Op (OP_IBinop And (TYPE_I 64) (EXP_Integer (-3)%Z) (EXP_Integer (-3)%Z)))); ((IId (Name "v1")), (INSTR_Op (OP_ICmp Ule (TYPE_I 64) (EXP_Ident (ID_Local (Name "v0"))) (EXP_Integer (8)%Z)))); ((IId (Name "v2")), (INSTR_Op (OP_Select ( (TYPE_I 1), (EXP_Ident (ID_Local (Name "v1")))) ((TYPE_I 64), (EXP_Ident (ID_Local (Name "v0")))) ((TYPE_I 64), (EXP_Integer (8)%Z))))); ((IId (Name "v3")), (INSTR_Op (OP_ICmp Ugt (TYPE_I 64) (EXP_Ident (ID_Local (Name "v2"))) (EXP_Integer (0)%Z))))] (TERM_Br ((TYPE_I 1), (EXP_Ident (ID_Local (Name "v3")))) (Name "b4") (Name "b2")) None); (mk_block (Name "b4") [((Name "v5"), (Phi (TYPE_I 64)[((Name "b1"), (EXP_Ident (ID_Local (Name "v2")))); ((Name "b3"), (EXP_Ident (ID_Local (Name "v6"))))]))] [((IId (Name "v8")), (INSTR_Op (OP_IBinop And (TYPE_I 32) (EXP_Integer (1)%Z) (EXP_Integer (-3)%Z)))); ((IId (Name "v9")), (INSTR_Alloca (TYPE_I 8) None None)); ((IVoid (1)%Z), (INSTR_Store false ((TYPE_I 8), (EXP_Integer (0)%Z)) ((TYPE_Pointer (TYPE_I 8)), (EXP_Ident (ID_Local (Name "v9")))) None)); ((IId (Name "v10")), (INSTR_Alloca (TYPE_I 8) None None)); ((IVoid (2)%Z), (INSTR_Store false ((TYPE_I 8), (EXP_Integer (0)%Z)) ((TYPE_Pointer (TYPE_I 8)), (EXP_Ident (ID_Local (Name "v10")))) None))] (TERM_Ret ((TYPE_I 8), (EXP_Integer (0)%Z))) None); (mk_block (Name "b3") [] [((IId (Name "v6")), (INSTR_Op (OP_IBinop (Sub false false) (TYPE_I 64) (EXP_Ident (ID_Local (Name "v5"))) (EXP_Integer (1)%Z)))); ((IId (Name "v7")), (INSTR_Op (OP_ICmp Ugt (TYPE_I 64) (EXP_Ident (ID_Local (Name "v6"))) (EXP_Integer (0)%Z))))] (TERM_Br ((TYPE_I 1), (EXP_Ident (ID_Local (Name "v7")))) (Name "b4") (Name "b2")) None); (mk_block (Name "b2") [] [((IId (Name "v4")), (INSTR_Alloca (TYPE_I 1) None None)); ((IVoid (0)%Z), (INSTR_Store true ((TYPE_I 1), (EXP_Ident (ID_Local (Name "v3")))) ((TYPE_Pointer (TYPE_I 1)), (EXP_Ident (ID_Local (Name "v4")))) None))] (TERM_Ret ((TYPE_I 8), (EXP_Integer (3)%Z))) None)])))].

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

Lemma blah :
  repr_prog = parsed_prog.
Proof.
Admitted.
