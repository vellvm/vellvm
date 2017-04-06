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
type assertion = (unit -> unit)

type 'a test = 
  | Test of string * (string * 'a) list

type suite = (assertion test) list

(* Assertions *)

let assert_eq v1 v2 : assertion =
  fun () -> if v1 <> v2 then failwith "not equal" else ()

let assert_eqf f v2 : assertion =
  fun () -> if (f ()) <> v2 then failwith "not equal" else ()

let assert_eqfs f v2 : assertion =
  fun () ->
    let s1 = f () in
    if s1 <> v2 then failwith @@ Printf.sprintf "not equal\n\texpected:%s\n\tgot:%s\n" v2 s1
    else ()

let assert_fail : assertion = fun () -> failwith "assert fail"



(* Generating Test Results *)

type result = 
  | Pass 
  | Fail of string

type outcome = (result test) list

let run_assertion (f:assertion) : result =
  try 
    f ();
    Pass
  with
    | Failure m -> Fail m
    | e -> Fail ("test threw exception: " ^ (Printexc.to_string e))

let run_test (t:assertion test) : result test =
  let run_case (cn, f) = (cn, run_assertion f) in
  begin match t with
    | Test (n, cases) -> Test(n, List.map run_case cases)
  end
  
let run_suite (s:suite):outcome =
  List.map run_test s


(***********************)
(* Reporting functions *)

let result_test_to_string (name_pts:string) (r:result test): string =
  let string_of_case (name, res) =
    let (p, m) =
      begin match res with
      | Pass     -> "passed", ""
      | Fail msg -> "failed", ("\n\t   ERROR: " ^ msg)
      end
    in
    Printf.sprintf "  %s - %s%s%!" p name m
  in
  begin match r with
    | Test (_, cases) ->
      name_pts ^ ":" ^ 
      (List.fold_left (fun rest -> fun case -> rest ^ "\n" ^ (string_of_case case)) "" cases)
  end

(* returns (name_pts, passed, failed, total, points_earned, max_given, max_hidden) *)
let get_results (t:result test) =
  let num_passed cases = 
    List.fold_left (fun cnt (_,r) -> match r with Pass -> cnt + 1 | _ -> cnt) 0 cases in
  let num_failed cases = 
    List.fold_left (fun cnt (_,r) -> match r with Fail _ -> cnt + 1 | _ -> cnt) 0 cases in
  begin match t with
    | Test(name, cases) ->
      let total = List.length cases in
      let passed = num_passed cases in
      let failed = num_failed cases in
      (name, passed, failed, total, 0.0, 0, 0)
  end

let outcome_to_string (o:outcome):string =
  let sep = "\n(*-------------------------------------- *)\n" in
  let helper  (passed, failed, total, str) (t:result test) =
    let (name_pts, p, f, tot, s, mg, mh) = get_results t in
    (passed + p, failed + f, total + tot, 
    str ^ "\n" ^ (
      if f > 0 then (result_test_to_string name_pts t) else 
      if tot > 0 then (name_pts ^ ":\n  OK") else
        (name_pts ^ ":\n  Hidden") 
      )
    ) in
  let (p,f,tot,str) = List.fold_left helper (0,0,0,"") o in
  str ^ sep ^ (Printf.sprintf "Passed: %d/%d\nFailed: %d/%d\n" p tot f tot)
  



