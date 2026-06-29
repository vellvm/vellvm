(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

open VellvmLib
open Assert

module DV = DynamicValues

let default_cl_test_args = []

let of_str = Camlcoq.camlstring_of_coqstring

let string_of_dvalue (d : DV.dvalue) =
  of_str (DV.show_dvalue Interpreter.params d)

let string_of_function_id id : string =
  LLVMAst.( match id with
  | Name n -> "@" ^ (Camlcoq.camlstring_of_coqstring n)
  | Anon z -> "@" ^ (Camlcoq.Z.to_string z)
  | Raw z ->  "_RAW_" ^  (Camlcoq.Z.to_string z)
  )


(* test harness ------------------------------------------------------------- *)
(* Todo add line count information *)
let parse_tests filename =
  let assertions = ref [] in
  let channel = open_in filename in
  try
    while true do
      let line = input_line channel in
      assertions := Assertion.parse_assertion line @ !assertions
    done ;
    []
  with End_of_file -> close_in channel ; List.rev !assertions


(* Semantics of ASSERT EQ ty expected = call @f(args):

   If expected is `poison` then the call should result in poison.

   If ty is an integral type, then use LLVM's `icmp eq` as the comparison.

   If ty is a floating point type, then use LLVM's `fcmp ueq` as the comparison.
 *)


(* "Syntactic comparison" of dynamic values -- does not take
   the semantic content into account.  *)
let compare_dvalues_exn expected got msg : unit =
  if TopLevel.dvalue_eqb expected got then ()
  else
    failwith msg

let dvalue_i1_to_bool (dv : DV.dvalue) : bool =
  match dv with 
  | DV.DVALUE_I (sz,bitint) ->  Integers.eq sz bitint (Integers.one sz)
  | _ -> failwith "non-i1 value"



let dvalue_eq_assertion name ty (expected : DV.dvalue) (got : unit -> DV.dvalue) () =
  let open DynamicTypes in
  Platform.verb (Printf.sprintf "running ASSERT in %s\n" name) ;  
  let result = got () in
  let msg =
    Printf.sprintf "ASSERT EQ failed: \ngot:\n\t%s\nasserted:\n\t%s"
         (string_of_dvalue result) (string_of_dvalue expected) 
  in
  begin match expected with
  | DV.DVALUE_Poison _ -> compare_dvalues_exn expected result msg
  | _ ->
     begin match ty with
     | DTYPE_I _ 
     | DTYPE_IPTR
     | DTYPE_Pointer ->
        (* integral comparison *)
        let v = Assertion.ocaml_of_EOU @@ Compare.eval_icmp Interpreter.params false Eq expected result in
        if dvalue_i1_to_bool v then () else
          failwith msg
     (* | DTYPE_FP _ -> (\* floating point comparison *\) *)
     (*    (\* compare_dvalues_exn expected result msg         *\) *)
     (*    let v = Assertion.ocaml_of_EOU @@ DV.eval_fcmp Interpreter.params FOeq expected result in *)
     (*    if dvalue_i1_to_bool v then () else *)
     (*      failwith msg *)
     (* | DTYPE_Vector _  -> failwith "TODO: comparison on vectors" *)
     | _ -> (* Best effort comparison of other types *)
        compare_dvalues_exn expected result msg
     end
  end


let make_test_h run name ll_ast t : (string * assertion) option =
  let open Format in
  (* TODO: ll_ast is of type list (toplevel_entity typ (block typ * list (block typ))) *)
  (* Can just replace this with the newer ones? *)
  let run_to_value dtyp entry args ll_ast () : DV.dvalue =
    match run dtyp entry args ll_ast with
    | Ok dv -> dv
    | Error e -> failwith (Result.string_of_exit_condition e)
  in
  let args_str args =
    pp_print_list
      ~pp_sep:(fun f () -> pp_print_string f ", ")
      Interpreter.pp_dvalue str_formatter args ;
    flush_str_formatter ()
  in
  (* let _ = Printf.printf "I can get here\n" in *)
  match t with
  | Assertion.EQTest (expected, dtyp, entry, args) ->
      let str =
        let expected_str = string_of_dvalue expected in
        let args_str = args_str args in
        Printf.sprintf "%s = %s(%s)" expected_str (string_of_function_id entry) args_str
      in
      let result = run_to_value dtyp entry args ll_ast in
      Some (str, dvalue_eq_assertion name dtyp expected result)

  | Assertion.SuccessTest ( entry, args) ->
     let str =
       let args_str  =
         pp_print_list
           ~pp_sep:(fun f () -> pp_print_string f ", ")
           Interpreter.pp_dvalue str_formatter args ;
         flush_str_formatter ()
       in
       Printf.sprintf "%s(%s)" (string_of_function_id entry) args_str
     in
     let t_void = Assertion.typ_to_dtyp (LLVMAst.TYPE_Void) in
     Some (str, (fun () -> ignore (run_to_value t_void entry args ll_ast ())))

let make_test name link_files ll_ast t : (string * assertion) option =
  let run dtyp entry args ll_ast =
    let linked_ast = TopLevel.link_all link_files ll_ast in
    Interpreter.step
      (TopLevel.interpreter_gen Interpreter.params dtyp
         entry
         (Monad.ret (Obj.magic ITreeDefinition.coq_Monad_itree) args) linked_ast )
  in
  make_test_h run name ll_ast t


let test_file_h make_test link_files path =
  Platform.configure () ;
  let _ = Platform.verb @@ Printf.sprintf "* processing file: %s\n" path in
  let _file, ext = Platform.path_to_basename_ext path in
  match ext with
  | "ll" ->
      let tests = parse_tests path in
      let _ = Printf.printf "Parsed successfully\n" in
      let ll_ast = IO.parse_file path in
      let _ = Printf.printf "AST retrieved successfully\n" in
      let suite = Test (path, List.filter_map (make_test path link_files ll_ast) tests) in
      let outcome = run_suite [suite] in
      Printf.printf "%s\n" (outcome_to_string outcome) ;
      raise (Ran_tests (successful outcome))
  | _ -> failwith @@ Printf.sprintf "found unsupported file type: %s" path

let test_file link_files path = test_file_h make_test link_files path

let test_dir link_files dir =
  Printf.printf "===> TESTING ASSERTIONS IN: %s\n" dir ;
  let pathlist = Platform.ll_files_of_dir dir in
  let files =
    List.filter_map
      (fun path ->
        let _file, ext = Platform.path_to_basename_ext path in
        try
          match ext with
          | "ll" -> Some (path, IO.parse_file path, parse_tests path)
          | _ -> None
        with
        | Failure s | Parse_util.InvalidAnonymousId s ->
            let _ = Printf.printf "FAILURE %s\n\t%s\n%!" path s in
            None
        | _ ->
            let _ = Printf.printf "FAILURE %s\n%!" path in
            None )
      pathlist
  in
  let suite =
    List.map
      (fun (file, ast, tests) ->
        Test (file, List.filter_map (make_test file link_files ast) tests) )
      files
  in
  let outcome = run_suite suite in
  Printf.printf "%s\n" (outcome_to_string outcome) ;
  raise (Ran_tests (successful outcome))

let test_all link_files =
  let test_directory = "../tests" in
  let _ =
    Printf.printf "============== RUNNING TEST SUITE ==============\n"
  in
  let b1 = try FrontendTest.test_pp_dir test_directory with Ran_tests b -> b in
  let b2 = try test_dir link_files test_directory with Ran_tests b -> b in
  raise (Ran_tests (b1 && b2))

