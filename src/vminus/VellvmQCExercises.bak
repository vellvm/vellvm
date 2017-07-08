Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Require Import List ZArith.
Import ListNotations.
Require Import String.

Require Import compcert.lib.Integers.

(* Vellvm dependencies *)
Require Import Vellvm.Ollvm_ast.
Require Import Vellvm.AstLib.
Require Import Vellvm.CFG.
Require Import Vellvm.StepSemantics.
Require Import Vellvm.Memory.
Require Import Vellvm.Classes.

(* Imp dependencies *)
Require Import Vellvm.Maps Vellvm.Imp.
Require Import Vellvm.ImpCEvalFun.

Require Import Vellvm.Compiler.

(** ** QuickChick and Vellvm **************************************************)
(** One may expect a compiler for a language as simple as IMP to be relatively 
    straightforward, and a proof of its correctness to be correspondingly
    so. However, as seen in the Vellvm lectures, LLVM is a full-featured IR, 
    and hence has a formalization that is complex and large. When the compiler
    is under development, even stating the correctness of the compiler can be 
    difficult, much less prove it.

    But if we have interpreters for both the source and target, testing the 
    compiler is a much simpler affair. Moreover, the simplicity of the source 
    language, i.e. Imp. means that it is really easy to test! *)

(** Following the lecture on compiler correctness, the first step is to define
    what it means for an Imp state and an LLVM "state" to be equivalent. 
    For correct compilation, it should be that all variables in the Imp state
    can be mapped to their corresponding entities in the LLVM "state" following
    the compiler, and that their values are equal. 

    In this case, Imp variables are allocated a distinct address in memory. 
    Equivalence is thus checked by taking an ordering of the Imp variables and
    checking the value at each corresponding address. *)

(** Hence we have the following. *)

Definition dvalue_of_int64 (n: int64) : dvalue :=
  DVALUE_I64 n.

Definition imp_val_eqb (v1 v2 : dvalue) : bool :=
  match v1, v2 with
  | (DVALUE_I64 z1), (DVALUE_I64 z2) => Int64.eq z1 z2
  | _, _ => false
  end.

Fixpoint imp_memory_eqb (m1 : list dvalue) (m2 : list dvalue) : bool :=
  match m1, m2 with
  | [], [] => true
  | x::xs, y::ys => if imp_val_eqb x y then imp_memory_eqb xs ys else false
  | _, _ => false 
  end.  

(** With this in place, a Checker for it could look like the following *)

(* Insert bare-bones Checker, and highlight its different parts *)

Definition basic_imp_compiler_checker (p:Imp.com) : bool :=
  let fvs := IDSet.elements (fv p) in
  match compile p with
  | inl e => false 
  | inr ll_prog =>
    let m := modul_of_toplevel_entities ll_prog in
    match mcfg_of_modul m with
    | None => false 
    | Some mcfg =>
      match init_state mcfg "imp_command" with
      | inl e => false 
      | inr initial_state =>
        let semantics := sem mcfg initial_state in
        let llvm_final_state := MemDFin [] semantics 10000 in
        let imp_state := ceval_step empty_state p 100 in
        match (llvm_final_state, imp_state) with
        (* false when out of steps, because it is unexpected *)
        | (None, None) => false
        | (Some llvm_st, None) => false 
        | (None, Some imp_st) => false 
        | (Some llvm_st, Some imp_st) => 
          let ans_state := List.map (fun x => dvalue_of_int64 (imp_st x)) fvs in
          imp_memory_eqb (List.rev llvm_st)
                         ans_state
        end        
      end
    end
  end.

(** To begin testing, we usually would write simple test cases, in this 
    case simple Imp programs, and see if we get the expected output. With
    QuickChick however, we can just automatically generate them. 

    To do so, we first need to define/derive the generators, Shows, and
    shrinkers for com.
 *)

(* Go through steps to build them up *)

(** Now let's try it. *)

(** EX: Write a generator that generates only negative constants between 100
    and 200. *)

(** EX: Write a generator that generates only "small" boolean expressions in
    the sense that all arithmetic expressions within use only one operator. *)

(** EX: Write a generator that generates only boolean expressions where all
    arithmetic expressions within are either constants or use at least three
    (not necessarily distinct) operators. *)

(** EX: Write a generator that generates only sequences of assignments and 
    has no other constructs. *)

(** EX: Write a generator that generates only IF-THEN-ELSE, assignments, and
    and SKIP statements, where SKIPs are generated with low probability. *) 

(*
Definition simple_checker :=
  forAll arbitrary basic_imp_compiler_checker.

QuickChick simple_checker. 
*)

(** Unfortunately, the compiler seems to have a bug! Or does it? We are really
    testing for much more; for results to be consistent:
    - The semantics of the source language, i.e. the IMP evaluator, 
      should be correct.
    - The semantics of the target language, i.e. the Vellvm evaluator,
      should be correct.
    - The compiler itself should be correct.
    - The Checker should be correct. 
    It is possible to make mistakes in any of these. *)

(** Moreover, this is on top of the many reasons for test failure in the 
    Checker. A good first step is to find out where it's really failing.
    Let us take advantage of QuickChick's Checker class, and add more 
    informative messages. *)

(*
Definition imp_compiler_correct (p:Imp.com) : Checker :=
  let fvs := IDSet.elements (fv p) in
  match compile p with
  | inl e => whenFail "Compilation failed" false
  | inr ll_prog =>
    let m := modul_of_toplevel_entities ll_prog in
    match mcfg_of_modul m with
    | None => whenFail "Compilation failed" false
    | Some mcfg =>
      match init_state mcfg "imp_command" with
      | inl e => whenFail "init failed" false
      | inr initial_state =>
        let semantics := sem mcfg initial_state in
        let llvm_final_state := MemDFin [] semantics 10000 in
        let imp_state := ceval_step empty_state p 100 in
        match (llvm_final_state, imp_state) with
        | (None, None) => whenFail "both out of gas" true
        | (Some llvm_st, None) => whenFail "imp out of gas" true
        | (None, Some imp_st) => whenFail "llvm out of gas" false 
        | (Some llvm_st, Some imp_st) => 
          let ans_state := List.map (fun x => dvalue_of_int64 (imp_st x)) fvs in
          checker
            (whenFail ("not equal: llvm: "
                         ++ (string_of llvm_st)
                         ++ "; imp: "
                         ++ (string_of ans_state)
                         ++ "; free vars: "
                         ++ (string_of fvs) (* (elems_to_string fvs) *)
                         ++ "; compiled code: "
                         ++ (string_of ll_prog))
                      (imp_memory_eqb (**!*) (List.rev llvm_st)
                                      (**! llvm_st *) ans_state))
        end        
      end
    end
  end.
 *)

(** Alas, there seems to be a real bug somewhere, and thanks to QuickChick, we 
    have a counterexample to try running the compiler on. Let's try to put the
    Shrinker to good use, and obtain a minimal counterexample. *)

(* Insert counterexample, run compile, and look at the results. *)

(** EX: Another way to quickly zoom in on a test failure, or to just gain more 
    confidence in a particular aspect of the compiler, is to control the 
    generation process. Write a Checker that uses the generator for only
    assignment statements. *)

(** EX: Write a Checker that uses the generator for only IF-THEN-ELSE, 
    assignments, and SKIP, and where boolean expressions within are small, 
    using the generator defined in the earlier exercise. *)


(** Sidenote: As the number of generators at each "level" increases, managing
    how they compose can become a difficult affair. One way to manage this is
    to define a new typeclass instance that wraps a generator, and supply the
    concrete choices within.

    Another way is to manage choices by de-registering generators after they 
    are defined. Then have testing broken up into QuickChick sections whose 
    preamble chooses a "package" of generators that compose implicitly, and 
    whose epilogue de-registers them. However, this is clearly prone to error.
 *)



There are other ways of composing these generators 


(** Let's fix the bug, and test again. *)



(* EX: *)



(** EX: Another way to *)

