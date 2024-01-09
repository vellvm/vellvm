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

open Result

type assertion = unit -> unit

type 'a test = 'a Result.test

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

type outcome' = result_sum

type assertion' = unit -> outcome'

type suite' = assertion' test list

module ResultMap = Result.ResultMap

(* This function will process the assertion and output a singleton map
   object *)
let run_assertion' (name : string) (test_case : string) (f : assertion') :
    result_sum =
  try f () with
  | Failure m ->
      let msg = Printf.sprintf "%s\n\t%s" test_case m in
      Result.make_singleton UNSOLVED name (ERR_MSG msg)
  | e ->
      let msg =
        Printf.sprintf "%s\n\t%s" test_case
          ("test threw\n   exception: " ^ Printexc.to_string e)
      in
      Result.make_singleton UNSOLVED name (ERR_MSG msg)

(* Test is file name * string (test case) * assertion *)
let run_test' (t : assertion' test) : outcome' =
  let run_case name (cn, f) = run_assertion' name cn f in
  match t with
  | Test (name, cases) ->
      if List.length cases == 0 then
        Result.make_singleton NOASSERT name NO_ASSERT
      else
        List.fold_right
          (fun case acc -> merge_result_outcome (run_case name case) acc)
          cases Result.empty

let run_suite' (s : suite') : outcome' =
  List.fold_right
    (fun x acc -> merge_result_outcome (run_test' x) acc)
    s Result.empty

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

let outcome'2outcome (_ : outcome') : outcome = failwith "unimplemented"
