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


(* https://www.rosettacode.org/wiki/String_matching#OCaml *)
let string_begins_with s1 s2 =
  let len1 = String.length s1 and len2 = String.length s2 in
  if len1 < len2 then false
  else
    let sub = String.sub s1 0 len2 in
    sub = s2

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
  (* Put the parser into "NormalMode" *)
  try
    while true do
      let line = input_line channel in
      assertions := Assertion.parse_assertion line @ !assertions
    done ;
    []
  with End_of_file -> close_in channel ; List.rev !assertions


let srctgt_test_flag = ref false

let compare_dvalues_exn dv1 dv2 ans : unit =
  if TopLevel.dvalue_eqb dv1 dv2 = ans then ()
  else
    failwith
      (Printf.sprintf
         "dvalue comparison for %s failed: \ngot:\n\t%s\nasserted:\n\t%s"
         (if ans then "equality" else "inequality")
         (string_of_dvalue dv1) (string_of_dvalue dv2) )

let dvalue_eq_assertion name (got : unit -> DV.dvalue)
    (expected : unit -> DV.dvalue) () =
  Platform.verb (Printf.sprintf "running ASSERT in %s\n" name) ;
  let dv1 = got () in
  let dv2 = expected () in
  compare_dvalues_exn dv1 dv2 true

let compare_tgt_for_poison src tgt : unit =
  match tgt with
  | DV.DVALUE_Poison _ -> (
    match src with
    | DV.DVALUE_Poison _ ->
        failwith
          "TargetMorePoisonous: expected src to be non-poison value, but \
           got poison"
    | _ -> () )
  | _ ->
      failwith
        (Printf.sprintf
           "TargetMorePoisonous: expected tgt to be poison but got %s"
           (string_of_dvalue tgt) )

(* TODO: This could be reformated to make it cleaner - move some of it to
   assertion.ml?. *)
(* SAZ: why does this duplicate a lot of code in tester.ml? *)
let make_test_h run name ll_ast t : (string * assertion) option =
  let open Format in
  (* TODO: ll_ast is of type list (toplevel_entity typ (block typ * list
     (block typ))) *)
  (* Can just replace this with the newer ones? *)
  let run_to_value dtyp entry args ll_ast () : DV.dvalue =
    match run dtyp entry args ll_ast with
    | Ok dv -> dv
    | Error e -> failwith (Result.string_of_exit_condition e)
  in
  (* let _ = Printf.printf "I can get here\n" in *)
  match t with
  | Assertion.EQTest (expected, dtyp, entry, args) ->
      let str =
        let expected_str = string_of_dvalue expected in
        let args_str : string =
          pp_print_list
            ~pp_sep:(fun f () -> pp_print_string f ", ")
            Interpreter.pp_dvalue str_formatter args ;
          flush_str_formatter ()
        in
        Printf.sprintf "%s = %s(%s)" expected_str (string_of_function_id entry) args_str
      in
      let result = run_to_value dtyp entry args ll_ast in
      Some (str, dvalue_eq_assertion name result (fun () -> expected))
  | Assertion.POISONTest (dtyp, entry, args) ->
       let expected =
           DV.DVALUE_Poison
           dtyp
       in
       let str =
         let expected_str = string_of_dvalue expected in
         let args_str =
           pp_print_list
             ~pp_sep:(fun f () -> pp_print_string f ", ")
             Interpreter.pp_dvalue str_formatter args ;
           flush_str_formatter ()
         in
         Printf.sprintf "%s = %s(%s)" expected_str (string_of_function_id entry) args_str
       in
       let result = run_to_value dtyp entry args ll_ast in
       Some (str, dvalue_eq_assertion name result (fun () -> expected))


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
  Platform.configure () ;
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

