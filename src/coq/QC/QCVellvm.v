 (** Framework for running QC vellvm tests.

    This sets up a step function which mimics the step function in
    interpreter.ml in Coq. This function may not terminate (e.g., when
    given an LLVM program that loops forever), and as such we need to
    disable the Coq termination checker to define it.
 *)
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

From QuickChick Require Import QuickChick.
From Vellvm Require Import ShowAST ReprAST GenAST TopLevel LLVMAst DynamicValues.

Extraction Blacklist String List Char Core Z Format.

(* TODO: Use the existing vellvm version of this? Might actually just be ocaml result type. *)
Inductive MlResult a e :=
| MlOk : a -> MlResult a e
| MlError : e -> MlResult a e.

Extract Inductive MlResult => "result" [ "Ok" "Error" ].

Import TopLevel64BitIntptr.
(* Import TopLevelBigIntptr. *)
Import DV.
Import MemoryModelImplementation.LLVMParams64BitIntptr.Events.
(* Import MemoryModelImplementation.LLVMParamsBigIntptr.Events. *)

Unset Guard Checking.
Fixpoint step (t : ITreeDefinition.itree L4 res_L4) : MlResult dvalue string
  := match observe t with
     | RetF (_,(_,(_,(_,x)))) => MlOk _ string x
     | TauF t => step t
     | VisF e k => MlError _ string "Uninterpreted event"
     end.
Set Guard Checking.

(** Top level interpreter to run LLVM programs. Yields either a uvalue, or an error string. *)
Definition interpret (prog : list (toplevel_entity typ (block typ * list (block typ)))) : MlResult dvalue string
  := step (interpreter prog).

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
Extract Constant llc_command =>
          "fun prog ->
              let llvm_file_name = Filename.(concat (get_temp_dir_name ()) ""temporary_vellvm.ll"") in
              let test_binary = Filename.(concat (get_temp_dir_name ()) ""vellvmqc"") in
              let f = open_out llvm_file_name in
                Printf.fprintf f ""%s"" prog;
                close_out f;
                Big_int_Z.big_int_of_int (Sys.command (""clang -lm -Wno-everything "" ^ llvm_file_name ^ "" -o "" ^ test_binary ^ "" && "" ^ test_binary))".

Axiom vellvm_print_ll : list (toplevel_entity typ (block typ * list (block typ))) -> string.
Extract Constant vellvm_print_ll => "fun prog -> Llvm_printer.toplevel_entities Format.str_formatter prog; Format.flush_str_formatter".

(** Use the *llc_command* Axiom to run a Vellvm program with clang,
    and wrap up the exit code as a uvalue. *)
Definition run_llc (prog : list (toplevel_entity typ (block typ * list (block typ)))) : dvalue
  := DVALUE_I8 (repr (llc_command (to_caml_str (show prog)))).

(** Basic property to make sure that Vellvm and Clang agree when they
    both produce values *)
Definition vellvm_agrees_with_clang (prog : list (toplevel_entity typ (block typ * list (block typ)))) : Checker
  := 
    (* collect (show prog) *)
            match run_llc prog, interpret prog with
            | DVALUE_I8 y, MlOk _ _ (DVALUE_I8 x) =>
              whenFail ("Vellvm: " ++ show (unsigned x) ++ " | Clang: " ++ show (unsigned y) ++ " | Ast: " ++ ReprAST.repr prog) (equ x y)
            | _, _ => checker true
            end.

Definition agrees := (forAll (run_GenLLVM gen_llvm) vellvm_agrees_with_clang).

Extract Constant defNumTests    => "10000".
QCInclude "../../ml/*".
QCInclude "../../ml/libvellvm/*".


(* QCInclude "../../ml/libvellvm/llvm_printer.ml". *)
(* QCInclude "../../ml/libvellvm/Camlcoq.ml". *)
(* QCInclude "../../ml/extracted/*ml". *)
Extract Inlined Constant Error.failwith => "(fun _ -> raise)".
QuickChick (forAll (run_GenLLVM gen_llvm) vellvm_agrees_with_clang).
(*! QuickChick agrees. *)


