(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)
(* An assertion is just a unit->unit function that either *)
(* succeeds silently or throws an Failure exception.       *)

type src_tgt_error_side = Src | Tgt

type test_error =
  | UninterpretedCall : string -> test_error
  | OutOfMemory : string -> test_error
  | UndefinedBehavior : string -> test_error
  | Failed : string -> test_error

type assertion = unit -> unit

type 'a test = Test of string * (string * 'a) list

type suite = assertion test list

(* Assertions *)

(* let assert_eq v1 v2 : assertion = fun () -> if v1 <> v2 then failwith "not
   equal" else ()

   let assert_eqf f v2 : assertion = fun () -> if f () <> v2 then failwith
   "not equal" else ()

   let assert_eqfs f v2 : assertion = fun () -> let s1 = f () in if s1 <> v2
   then failwith @@ Printf.sprintf "not equal\n\texpected:%s\n\tgot:%s\n" v2
   s1 else ()

   let assert_fail : assertion = fun () -> failwith "assert fail" *)

(* Generating Test Results *)

type result = Pass | Fail of string

type outcome = result test list

let run_assertion (f : assertion) : result =
  try f () ; Pass with
  | Failure m -> Fail m
  | e -> Fail ("test threw exception: " ^ Printexc.to_string e)

let run_test (t : assertion test) : result test =
  let run_case (cn, f) = (cn, run_assertion f) in
  match t with Test (n, cases) -> Test (n, List.map run_case cases)

let run_suite (s : suite) : outcome = List.map run_test s

let successful (o : outcome) : bool =
  List.for_all
    (fun (Test (_, cases)) -> List.for_all (fun (_, r) -> r = Pass) cases)
    o

(* Another version of result, which contains more information for
   statistics*)
type test_result =
  | STOk : string * Assertion.src_tgt_mode -> test_result
  | STNOk : string * Assertion.src_tgt_mode * string -> test_result
  | STErr : string * src_tgt_error_side * test_error -> test_result
  | EQOk : string * Assertion.raw_assertion_string -> test_result
  | EQFal : string * Assertion.raw_assertion_string -> test_result
  | POIOk : string * Assertion.raw_assertion_string -> test_result
  | POIFal : string * Assertion.raw_assertion_string -> test_result
  | UNSOLVED : string -> test_result

type assertion1 = unit -> test_result

type suite1 = assertion1 test list

type outcome1 = test_result test list

let run_assertion1 (f : assertion1) : test_result =
  try f () with
  | Failure m -> UNSOLVED m
  | e -> UNSOLVED ("test threw exception: " ^ Printexc.to_string e)

let run_test1 (t : assertion1 test) : test_result test =
  let run_case (cn, f) = (cn, run_assertion1 f) in
  match t with Test (n, cases) -> Test (n, List.map run_case cases)

let run_suite1 (s : suite1) : outcome1 = List.map run_test1 s
(***********************)
(* Reporting functions *)

let result_test_to_string (name_pts : string) (r : result test) : string =
  let string_of_case (name, res) =
    let p, m =
      match res with
      | Pass -> ("PASSED", "")
      | Fail msg -> ("FAILED", "\n\t   ERROR: " ^ msg)
    in
    Printf.sprintf "  %s - %s%s%!" p name m
  in
  match r with
  | Test (_, cases) ->
      name_pts ^ ":"
      ^ List.fold_left
          (fun rest case -> rest ^ "\n" ^ string_of_case case)
          "" cases

(* returns (name_pts, passed, failed, total, points_earned, max_given,
   max_hidden) *)
let get_results (t : result test) =
  let num_passed cases =
    List.fold_left
      (fun cnt (_, r) -> match r with Pass -> cnt + 1 | _ -> cnt)
      0 cases
  in
  let num_failed cases =
    List.fold_left
      (fun cnt (_, r) -> match r with Fail _ -> cnt + 1 | _ -> cnt)
      0 cases
  in
  match t with
  | Test (name, cases) ->
      let total = List.length cases in
      let passed = num_passed cases in
      let failed = num_failed cases in
      (name, passed, failed, total, 0.0, 0, 0)

let outcome_to_string (o : outcome) : string =
  let sep = "\n(*-------------------------------------- *)\n" in
  let helper (passed, failed, total, str) (t : result test) =
    let name_pts, p, f, tot, _, _, _ = get_results t in
    ( passed + p
    , failed + f
    , total + tot
    , str ^ "\n"
      ^
      if f > 0 then result_test_to_string name_pts t
      else if tot > 0 then Printf.sprintf "%s: PASSED" name_pts
      else Printf.sprintf "%s: NO ASSERT" name_pts )
  in
  let p, f, tot, str = List.fold_left helper (0, 0, 0, "") o in
  str ^ sep ^ Printf.sprintf "Passed: %d/%d\nFailed: %d/%d\n" p tot f tot
