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

#[global] Instance MlResultShow {a e} `{Show a} `{Show e} : Show (MlResult a e).
Proof.
  split.
  exact
    (fun res =>
       match res with
       | MlOk _ _ a => ("Ok " ++ show a)%string
       | MlError _ _ e => ("Error " ++ show e)%string
       end).
Defined.

Import TopLevel64BitIntptr.
(* Import TopLevelBigIntptr. *)
Import DV.
Import MemoryModelImplementation.LLVMParams64BitIntptr.Events.
(* Import MemoryModelImplementation.LLVMParamsBigIntptr.Events. *)

#[global] Instance showdv : Show dvalue.
Proof.
  split.
  apply show_dvalue.
Defined.

Unset Guard Checking.
Fixpoint step (t : ITreeDefinition.itree L4 res_L4) : MlResult dvalue string
  := match observe t with
     | RetF (_,(_,(_,(_,x)))) => MlOk _ string x
     | TauF t => step t
     | VisF (inl1 e) k =>
         MlError _ string "Uninterpreted external call"
     | VisF (inr1 (inl1 (ThrowOOM msg))) k =>
         MlError _ string ("OOM: " ++ msg)%string
     | VisF (inr1 (inr1 (inl1 (ThrowUB msg)))) k =>
         MlError _ string ("UB: " ++ msg)%string
     | VisF (inr1 (inr1 (inr1 (inl1 (Debug msg))))) k =>
         MlError _ string ("Debug: " ++ msg)%string
     | VisF (inr1 (inr1 (inr1 (inr1 (LLVMEvents.Throw msg))))) k =>
         MlError _ string ("Failure: " ++ msg)%string
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

(** Ocaml integers *)
Axiom oint : Type. (* ocaml int type *)
Extract Inlined Constant oint => "int".

Axiom oint_to_Z : oint -> Z.
Extract Inlined Constant oint_to_Z => "Big_int_Z.big_int_of_int".

Axiom oneq : oint -> oint -> bool.
Extract Inlined Constant oneq => "(<>)".

Axiom oeq : oint -> oint -> bool.
Extract Inlined Constant oeq => "(=)".

Axiom ozero : oint.
Extract Inlined Constant ozero => "0".

(** Processes *)
Inductive process_status : Type :=
| WEXITED   : oint -> process_status
| WSIGNALED : oint -> process_status
| WSTOPPED  : oint -> process_status
.
Extract Inductive process_status => "process_status" [ "WEXITED" "WSIGNALED" "WSTOPPED" ].

#[global] Instance Show_process_status : Show process_status.
Proof.
  split.
  intros STATUS. destruct STATUS as [EXIT | SIGNAL | STOPPED].
  - exact ("Exited with " ++ show (oint_to_Z EXIT))%string.
  - exact ("Signaled with " ++ show (oint_to_Z SIGNAL))%string.
  - exact ("Stopped with " ++ show (oint_to_Z STOPPED))%string.
Qed.

Axiom fork : unit -> oint.
Extract Inlined Constant fork => "Unix.fork".

Axiom wait : unit -> (oint * process_status)%type.
Extract Inlined Constant wait => "Unix.wait".

Axiom wait_flag : Type.
Extract Inlined Constant wait_flag => "Unix.wait_flag".

Axiom waitpid : list wait_flag -> oint -> (oint * process_status)%type.
Extract Inlined Constant waitpid => "Unix.waitpid".

Axiom exit : forall {A}, oint -> A.
Extract Inlined Constant exit => "exit".

(** Write our LLVM program to a file ("temporary_vellvm.ll"), and then
    use clang to compile this file to an executable, which we then run in
    order to get the return code. *)
Axiom llc_command_ocaml : string -> oint.
Extract Constant llc_command_ocaml =>
          "fun prog ->
              let llvm_file_name = Filename.(concat (get_temp_dir_name ()) ""temporary_vellvm.ll"") in
              let test_binary = Filename.(concat (get_temp_dir_name ()) ""vellvmqc"") in
              let f = open_out llvm_file_name in
                Printf.fprintf f ""%s"" prog;
                close_out f;
                Sys.command (""clang -lm -Wno-everything "" ^ llvm_file_name ^ "" -o "" ^ test_binary ^ "" && "" ^ test_binary)".


Definition llc_command (prog : string) : int
  := oint_to_Z (llc_command_ocaml prog).

Axiom vellvm_print_ll : list (toplevel_entity typ (block typ * list (block typ))) -> string.
Extract Constant vellvm_print_ll => "fun prog -> Llvm_printer.toplevel_entities Format.str_formatter prog; Format.flush_str_formatter".

(** Use the *llc_command* Axiom to run a Vellvm program with clang,
    and wrap up the exit code as a uvalue. *)
Definition run_llc (prog : list (toplevel_entity typ (block typ * list (block typ)))) : dvalue
  := DVALUE_I8 (repr (llc_command (to_caml_str (show prog)))).

(* Hide show instance... *)
Inductive PROG :=
| Prog : list (toplevel_entity typ (block typ * list (block typ))) -> PROG
.

#[global] Instance Show_PROG : Show PROG :=
  { show p := "" (* PROG: avoiding inefficient printing in QC, see #253 *) }.

Definition gen_PROG : GenLLVM PROG
  := fmap Prog gen_llvm.

(** Basic property to make sure that Vellvm and Clang agree when they
    both produce values *)
Definition vellvm_agrees_with_clang_parallel (p : PROG) : Checker
  :=
  (* collect (show prog) *)
  let '(Prog prog) := p in
  let pid := fork tt in
  if oeq pid ozero
  then (* Child *)
    exit (llc_command_ocaml (to_caml_str (show prog)))
  else (* Parent *)
    let vellvm_res := interpret prog in
    let clang_res := snd (waitpid nil pid) in
    match vellvm_res, clang_res with
    | MlOk _ _ (DVALUE_I8 x), (WEXITED ocaml_y) =>
        let y := repr (oint_to_Z ocaml_y) in
        if equ x y
        then checker true
        else whenFail ("Vellvm: " ++ show (unsigned x) ++ " | Clang: " ++ show (unsigned y) ++ " | Ast: " ++ ReprAST.repr prog) false
    | _, (WSIGNALED ocaml_y) =>
        whenFail ("clang process signaled") false
    | _, (WSTOPPED ocaml_y) =>
        whenFail ("clang process stopped") false
    | _, _ =>
        whenFail ("Something else went wrong... Vellvm: " ++ show vellvm_res ++ " | Clang: " ++ show clang_res) false
    end.

(** Basic property to make sure that Vellvm and Clang agree when they
    both produce values *)
Definition vellvm_agrees_with_clang (p : PROG) : Checker
  :=
  (* collect (show prog) *)
  let '(Prog prog) := p in
  let clang_res := run_llc prog in
  let vellvm_res := interpret prog in
  match clang_res, vellvm_res with
  | DVALUE_I8 y, MlOk _ _ (DVALUE_I8 x) =>
      if equ x y
      then checker true
      else whenFail ("Vellvm: " ++ show (unsigned x) ++ " | Clang: " ++ show (unsigned y) ++ " | Ast: " ++ ReprAST.repr prog) false
  | _, _ =>
      whenFail ("Something else went wrong... Vellvm: " ++ show vellvm_res ++ " | Clang: " ++ show clang_res) false
  end.

(* Definition agrees := (forAll (run_GenLLVM gen_llvm) vellvm_agrees_with_clang). *)

Extract Constant defNumTests    => "5000".
QCInclude "../../ml/*".
QCInclude "../../ml/libvellvm/*".


(* QCInclude "../../ml/libvellvm/llvm_printer.ml". *)
(* QCInclude "../../ml/libvellvm/Camlcoq.ml". *)
(* QCInclude "../../ml/extracted/*ml". *)
Extract Inlined Constant Error.failwith => "(fun _ -> raise)".
QuickChick (forAll (run_GenLLVM gen_PROG) vellvm_agrees_with_clang).
(*! QuickChick agrees. *)
