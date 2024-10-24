type ast =
  (LLVMAst.typ, Generate.GA.runnable_blocks) LLVMAst.toplevel_entity list

type 'a test = Test of string * (string * 'a) list


type src_tgt_error_side = Src | Tgt

let string_of_src_tgt_error_side = function Src -> "Src" | Tgt -> "Tgt"

(* enum function for the OrdType*)
let int_of_src_tgt_error_side = function Src -> 1 | Tgt -> 2

(* Move test_error from Assertion.ml to here *)
type exit_condition =
  | UninterpretedCall of string
  | OutOfMemory of string
  | UndefinedBehavior of string
  | Failed of string

let string_of_exit_condition e =
  match e with
  | UninterpretedCall s -> "Uninterpreted Call: " ^ s
  | OutOfMemory s -> "Out Of Memory: " ^ s
  | UndefinedBehavior s -> "Undefined Behavior: " ^ s
  | Failed s -> "Failed: " ^ s

(* Serve as the key for the mapping *)
type test_result =
  | STOk : Assertion.src_tgt_mode -> test_result
  | STNOk : Assertion.src_tgt_mode -> test_result
  | STErr : src_tgt_error_side -> test_result
  | EQOk
  | EQNOk
  | POIOk
  | POINOk
  | UNSOLVED
  | NOASSERT

let string_of_test_result = function
  | STOk mode ->
      Printf.sprintf "Src Tgt Correct (%s)"
        (Assertion.show_src_tgt_mode mode)
  | STNOk mode ->
      Printf.sprintf "Src Tgt Incorrect (%s)"
        (Assertion.show_src_tgt_mode mode)
  | STErr side ->
      Printf.sprintf "%s Error" (string_of_src_tgt_error_side side)
  | EQOk -> "Equality Correct"
  | EQNOk -> "Equality Incorrect"
  | POIOk -> "Poison Correct"
  | POINOk -> "Poison Incorrect"
  | UNSOLVED -> "Not Runnable"
  | NOASSERT -> "NO ASSERT"

(* enum function for the OrdType*)
let int_of_test_result = function
  | STOk _ -> 1
  | STNOk _ -> 2
  | STErr _ -> 3
  | EQOk -> 4
  | EQNOk -> 5
  | POIOk -> 6
  | POINOk -> 7
  | UNSOLVED -> 8
  | NOASSERT -> 9
(* The first string is always file name *)

module Test_Result_Key = struct
  type t = test_result

  let compare tr1 tr2 =
    match (tr1, tr2) with
    | STOk mode1, STOk mode2 ->
        Assertion.int_of_src_tgt_mode mode1
        - Assertion.int_of_src_tgt_mode mode2
    | STNOk mode1, STNOk mode2 ->
        Assertion.int_of_src_tgt_mode mode1
        - Assertion.int_of_src_tgt_mode mode2
    | STErr side1, STErr side2 ->
        int_of_src_tgt_error_side side1 - int_of_src_tgt_error_side side2
    | _, _ -> int_of_test_result tr1 - int_of_test_result tr2
end

(* The value that is stored in the map *)
type test_outcome =
  | AST_ERR_MSG : ast * string -> test_outcome
  | AST_TEST_ERR : ast * exit_condition -> test_outcome
  | AST_CORRECT : ast -> test_outcome
  | ERR_MSG : string -> test_outcome
  | RAW_STR : Assertion.raw_assertion_string -> test_outcome
  | NO_ASSERT : test_outcome

type test_sum = TEST_SUM : string * test_outcome -> test_sum

module ResultMap = Map.Make (Test_Result_Key)

(* Annotated the key (test_result) value (test_outcome list) pair for the
   map *)
type value = test_sum list

type result_sum = value ResultMap.t

let merge_result_outcome_aux (_k : ResultMap.key) (op1 : value option)
    (op2 : value option) : value option =
  match (op1, op2) with
  | None, None -> None
  | None, Some l -> Some l
  | Some l, None -> Some l
  | Some l1, Some l2 -> Some (List.append l1 l2)

let merge_result_outcome : result_sum -> result_sum -> result_sum =
  ResultMap.merge merge_result_outcome_aux

let empty : result_sum = ResultMap.empty

let make_singleton (key : ResultMap.key) (name : string)
    (outcome : test_outcome) =
  ResultMap.singleton key [TEST_SUM (name, outcome)]

(* Need a function to dump the map... *)

let string_of_chars chars : string =
  let buf = Buffer.create 16 in
  List.iter (Buffer.add_char buf) chars ;
  Buffer.contents buf

let string_of_test_outcome (with_ast : bool) (outcome : test_outcome) :
    string =
  let show_ast (sum_ast : ast) =
    if with_ast then
      Printf.sprintf "\nAST: \n%s\n"
        (string_of_chars (ShowAST.showProg sum_ast))
    else ""
  in
  match outcome with
  | AST_ERR_MSG (sum_ast, msg) ->
      Printf.sprintf "Error Message: %s%s" msg (show_ast sum_ast)
  | AST_TEST_ERR (sum_ast, exit_cond) ->
      Printf.sprintf "Fail Test: %s%s"
        (string_of_exit_condition exit_cond)
        (show_ast sum_ast)
  | AST_CORRECT sum_ast ->
      if with_ast then Printf.sprintf "Correct: %s" (show_ast sum_ast)
      else "Correct"
  | ERR_MSG msg -> Printf.sprintf "Error Message: %s" msg
  | RAW_STR rs ->
      Printf.sprintf "Raw Assertion String: %s"
        (Assertion.string_of_raw_assertion_string rs)
  | NO_ASSERT -> "NO ASSERT"

(* TODO: Need helper function for printing out the map ? *)
(* TODO: Add function in assert.ml to output the map in specific location *)
(* TODO: Call it from main.ml*)
(* Then DONE!!*)

let string_of_test_sum (with_ast : bool) (ts : test_sum) : string =
  let msg outcome =
    string_of_test_outcome with_ast outcome
    (* String.concat "\n" (List.map (string_of_test_outcome with_ast)
       outcome) *)
  in
  match ts with
  | TEST_SUM (filename, outcome) ->
      Printf.sprintf "%s ==> %s" filename (msg outcome)

let string_of_value (with_ast : bool) (v : value) : string =
  let string_space = if with_ast then "\n" else "" in
  String.concat string_space
    (List.map (fun x -> string_of_test_sum with_ast x ^ "\n") v)

let string_of_key_value_pair (with_ast : bool) (rs : ResultMap.key * value) :
    string =
  let k, v = rs in
  Printf.sprintf "<<<<<<< %s >>>>>>>\n%s\n" (string_of_test_result k)
    (string_of_value with_ast v)

let bindings = ResultMap.bindings

let filter_map = ResultMap.filter

let get_stats (rs : result_sum) =
  let res : (ResultMap.key * value) list = ResultMap.bindings rs in
  List.map
    (fun elem -> (string_of_test_result (fst elem), List.length (snd elem)))
    res

(* Another version of result, which contains more information for
   statistics*)

type outcome' = result_sum

type assertion' = unit -> outcome'

type suite' = assertion' test list

(* This function will process the assertion and output a singleton map
   object *)
let run_assertion' (name : string) (test_case : string) (f : assertion') :
    result_sum =
  try f () with
  | Failure m ->
      let msg = Printf.sprintf "%s\n\t%s" test_case m in
      make_singleton UNSOLVED name (ERR_MSG msg)
  | e ->
      let msg =
        Printf.sprintf "%s\n\t%s" test_case
          ("test threw\n   exception: " ^ Printexc.to_string e)
      in
      make_singleton UNSOLVED name (ERR_MSG msg)

(* Test is file name * string (test case) * assertion *)
let run_test' (t : assertion' test) : outcome' =
  let run_case name (cn, f) = run_assertion' name cn f in
  match t with
  | Test (name, cases) ->
      if List.length cases == 0 then
        make_singleton NOASSERT name NO_ASSERT
      else
        List.fold_right
          (fun case acc -> merge_result_outcome (run_case name case) acc)
          cases empty

let run_suite' (s : suite') : outcome' =
  List.fold_right
    (fun x acc -> merge_result_outcome (run_test' x) acc)
    s empty


(* let string_of_result_sum (rs : result_sum) : string = let ls =
   ResultMap.bindings rs in failwith "TODO: unimplemented" *)
(* String.concat (List.map ()) *)
