open LLVMAst
open Generate

type ast =
  (LLVMAst.typ, Generate.GA.runnable_blocks) LLVMAst.toplevel_entity list

type 'a test = Test of string * (string * 'a) list

type src_tgt_error_side = Src | Tgt

(* enum function for the OrdType*)
let int_of_src_tgt_error_side = function Src -> 1 | Tgt -> 2

(* Move test_error from Assertion.ml to here *)
type test_error =
  | UninterpretedCall : string -> test_error
  | OutOfMemory : string -> test_error
  | UndefinedBehavior : string -> test_error
  | Failed : string -> test_error

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
  | AST_TEST_ERR : ast * test_error -> test_outcome
  | AST_CORRECT : ast -> test_outcome
  | ERR_MSG : string -> test_outcome
  | RAW_STR : Assertion.raw_assertion_string -> test_outcome

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
