
Require Import Vellvm.Maps Vellvm.Imp.
Require Import Vellvm.ImpQuickChick.

Require Import Vellvm.CompilerProp Vellvm.Compiler.

Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Require Import List ZArith.
Import ListNotations.
Require Import String.

Require Import Vellvm.Classes Vellvm.Ollvm_ast.



Check compile_aexp.

Example empty_ctxt : ctxt := t_empty (None : option Ollvm_ast.value).
Example test_ctxt :=
  t_update (t_update empty_ctxt
                     idX (Some (Ollvm_ast.SV (Ollvm_ast.VALUE_Integer 2%Z))))
           idY (Some (Ollvm_ast.SV (Ollvm_ast.VALUE_Integer 3%Z))).

Check (compile_aexp empty_ctxt (ANum 2)).
Compute (compile_aexp empty_ctxt (ANum 2)).
Compute (compile_aexp empty_ctxt (AId idX)).

Definition test_state := (2, 3, ([]: list elt))%Z.
Definition test_instr : instr :=
  INSTR_Op (SV (OP_IBinop (Add false false)
                          i64
                          (SV (VALUE_Integer 2%Z))
                          (SV (VALUE_Integer 2%Z)))).

Definition test_compiled_aexp := compile_aexp test_ctxt (APlus (AId idX) (ANum 3)).

Check fold_left.

(*
Definition compile (c:com) : err (toplevel_entities (list block)) :=
  '(fvs, elts) <-
          run (
            let fvs := IDSet.elements (fv c) in
            'g <- compile_fv fvs;  
(*            '; compile_com g c; *)
(*            '; print_fv fvs g;  (* UNCOMMENT to enable imp state printing *) *)
            '; term TERM_Ret_void;    
            mret fvs
          );
  'blocks <- blocks_of_elts (Anon 0)%Z elts;
  mret
   ((List.map (fun x => let 'Id s := x in TLE_Declaration (print_decl ("print_" ++ s))) fvs) ++
   [
    TLE_Definition
    {|
    df_prototype := imp_decl;
    df_args := [];
    df_instrs := blocks
  |}]).

Print toplevel_entity.

Definition ctxt_generator := 
*)
                                                

(* Example program that fails imp_compiler_correct here:
Eample prog1 := X ::= APlus (AId W) (AId W).
 *)

Example prog1 := (X ::= ANum 1).
Example prog2 := (W ::= AId W).
Example prog3 := X ::= APlus (AId W) (AId W).
Example prog4 := X ::= APlus (AId W) (AId X). (* fails compilation because not VALUE_Integer *)

Eval vm_compute in (compile prog2).

Definition show_aexp_compilation_result (result : err (value * list elt)) :=
  match result with
  | inl _ => "err" 
  | inr (_, elts) => string_of elts
  end.

Check (compile prog4).

Definition show_result (result : err (toplevel_entities (list block))) :=
  match result with
  | inl _ => "error"
  | inr l => fold_left (fun s tle_blk => (s ++ "; " ++ (string_of tle_blk))%string) l ""
  end.

Compute (show_aexp_compilation_result
           (compile_aexp_wrapper (AMult (AId idX) (APlus (ANum 1) (ANum 2))))).

Compute (show_result (compile prog4)).


QuickChick (forAll arbitrary
                   imp_compiler_correct_aux).



Compute (imp_compiler_correct_aux prog1).



Definition result1 := imp_compiler_correct_aux prog1.
(* Recursive Extraction result1.  *)
(* Eval vm_compute in (imp_compiler_correct_aux prog1). *)