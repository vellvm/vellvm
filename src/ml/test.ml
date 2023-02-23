(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

;; open Platform
;; open Driver
;; open Assert
;; open DynamicValues
;; open Handlers.LLVMEvents

(* Vellvm test cases -------------------------------------------------------- *)


let parse_pp_test path =
  let _ = Platform.verb @@ Printf.sprintf "* processing file: %s\n" path in
  let filename, _ = Platform.path_to_basename_ext path in
  let vll_file = Platform.gen_name !Platform.output_path filename ".v.ll" in
  let dot_s = Platform.gen_name !Platform.output_path filename ".s" in
  let _ = Printf.fprintf stderr "Running llc on: %s\n%!" path in
  try
    (* VV: Re-enabled llc *)
    let _ = llc_parse path dot_s in
    let prog = parse_file path in
    let _ = output_file vll_file prog in
    try
      let _ = llc_parse vll_file dot_s in
      ()
    with
    PlatformError _ -> failwith (Printf.sprintf "vellvm output bad file: %s" vll_file)
  with
    PlatformError _ -> ()



let files_of_dir path : string list =
  let tmp_file = gen_name "." ".ll_files" ".tmp" in
  let cmd = Printf.sprintf "find %s -name \"*.ll\" -print > %s" path tmp_file in
  let () = sh cmd raise_error in 
  let fhandle = open_in tmp_file in
  let rec loop paths =
    try
      loop ((input_line fhandle)::paths)
    with
    | End_of_file -> paths
  in
  let ans = loop [] in
  close_in fhandle;
  let rm_cmd = Printf.sprintf "rm %s" tmp_file in
  let () = sh rm_cmd raise_error in
  ans

let pp_test_of_dir dir =
  Test ("Parsing files in: " ^ dir,
        List.map (fun f -> (f, fun () -> parse_pp_test f)) (files_of_dir dir))

let run_uvalue_test (test:DV.uvalue -> bool) path =
  let (res, msg) =
    match run_ll_file path with
    | Error msg -> (false, msg)
    | Ok dv -> (test dv, "")
  in
  if not res then failwith (path ^ " test failed: " ^ msg); ()

(* https://www.rosettacode.org/wiki/String_matching#OCaml *)
let sting_begins_with s1 s2 =
  let len1 = String.length s1
  and len2 = String.length s2 in
  if len1 < len2 then false else
    let sub = String.sub s1 0 len2 in
    (sub = s2)

let run_parsefail_test path prefix =
  let (failed,msg) =
    try
      ignore (run_ll_file path);
      (false,"")
    with
      Failure msg -> (sting_begins_with msg prefix, msg)
  in
  if not failed then failwith (path ^ " test failed to produce expected parsing error. Got ubstead: " ^ msg); ()

let must_fail_tests =
  [("../tests/must-fail/float-literal-size.ll", "Illegal 32-bit floating point literal");
  ]

let poison_tests =
  ["../tests/llvm-arith/i1/add_nsw.ll";
   "../tests/llvm-arith/i1/add_nuw.ll";
   "../tests/llvm-arith/i1/sub_nsw.ll";
   "../tests/llvm-arith/i1/sub_nuw.ll";
   "../tests/llvm-arith/i32/add_nsw.ll";
   "../tests/llvm-arith/i32/add_nuw.ll";
   "../tests/llvm-arith/i32/ashr_ex.ll";
   "../tests/llvm-arith/i32/lshr_ex.ll";
   "../tests/llvm-arith/i32/mul_nsw.ll";
   "../tests/llvm-arith/i32/mul_nuw.ll";
   "../tests/llvm-arith/i32/sdiv_ex.ll";
   "../tests/llvm-arith/i32/shl_nsw.ll";
   "../tests/llvm-arith/i32/shl_nuw.ll";
   "../tests/llvm-arith/i32/sub_nsw.ll";
   "../tests/llvm-arith/i32/sub_nuw.ll";
   "../tests/llvm-arith/i32/udiv_ex.ll";
   "../tests/llvm-arith/i8/add_nsw.ll";
   "../tests/llvm-arith/i8/add_nuw.ll";
   "../tests/llvm-arith/i8/ashr_ex.ll";
   "../tests/llvm-arith/i8/lshr_ex.ll";
   "../tests/llvm-arith/i8/mul_nsw.ll";
   "../tests/llvm-arith/i8/mul_nuw.ll";
   "../tests/llvm-arith/i8/sdiv_ex.ll";
   "../tests/llvm-arith/i8/shl_nsw.ll";
   "../tests/llvm-arith/i8/shl_nuw.ll";
   "../tests/llvm-arith/i8/sub_nsw.ll";
   "../tests/llvm-arith/i8/sub_nuw.ll";
   "../tests/llvm-arith/i8/udiv_ex.ll";
   "../tests/llvm-arith/i64/add_nsw.ll";
   "../tests/llvm-arith/i64/add_nuw.ll";
   "../tests/llvm-arith/i64/ashr_ex.ll";
   "../tests/llvm-arith/i64/lshr_ex.ll";
   "../tests/llvm-arith/i64/mul_nsw.ll";
   "../tests/llvm-arith/i64/mul_nuw.ll";
   "../tests/llvm-arith/i64/sdiv_ex.ll";
   "../tests/llvm-arith/i64/shl_nsw.ll";
   "../tests/llvm-arith/i64/shl_nuw.ll";
   "../tests/llvm-arith/i64/sub_nsw.ll";
   "../tests/llvm-arith/i64/sub_nuw.ll";
   "../tests/llvm-arith/i64/udiv_ex.ll";]

let i1_tests : (string * int) list =
  [("../tests/llvm-arith/i1/xor.ll", 0);
   ("../tests/llvm-arith/i1/udiv.ll", 1);
   ("../tests/llvm-arith/i1/srem.ll", 0);
   ("../tests/llvm-arith/i1/or.ll", 1);
   ("../tests/llvm-arith/i1/mul.ll", 0);
   ("../tests/llvm-arith/i1/and.ll", 0);
   ("../tests/llvm-arith/i1/add_twice.ll", 1);
   ("../tests/llvm-arith/i1/urem.ll", 0);
   ("../tests/llvm-arith/i1/sub.ll", 0);
   ("../tests/llvm-arith/i1/sdiv.ll", 1);
   ("../tests/llvm-arith/i1/mul_safe.ll", 0);
   ("../tests/llvm-arith/i1/arith_combo.ll", 0);
   ("../tests/llvm-arith/i1/add_twice_named.ll", 1);
   ("../tests/llvm-arith/i1/add_safe.ll", 1)  
  ]

let i32_tests : (string * int) list =
  [  ]

let i64_tests : (string * int) list =
  [
    (* ("../tests/ll/gep1.ll", 6); (* need CString support for this *)*)
    ("../tests/ll/gep2.ll", 4);
    ("../tests/ll/gep3.ll", 1);
    ("../tests/ll/gep4.ll", 2);
    ("../tests/ll/gep5.ll", 4);
    ("../tests/ll/gep6.ll", 7);
    ("../tests/ll/gep7.ll", 7);
    ("../tests/ll/gep8.ll", 2);
    ("../tests/ll/gep9.ll", 5);
  ]

let float_tests : (string * float ) list =
  [
    ("../tests/llvm-arith/float/float_literal.ll", 125.31999969482421875);
    ("../tests/llvm-arith/float/hex_float_literal.ll", 468655825485824.);
    ("../tests/llvm-arith/float/i8_uitofp_float.ll", 10.0);
  ]
let snan = Stdlib.Int64.float_of_bits (Stdlib.Int64.of_string "0x7FF0000000000001")
let qnan = Stdlib.Int64.float_of_bits (Stdlib.Int64.of_string "0x7FF8000000000000")

let double_tests : (string * float ) list =
  [
    ("../tests/llvm-arith/double/double_literal.ll", 125.31999999999999317878973670303821563720703125);
    ("../tests/llvm-arith/double/i8_uitofp_double.ll", 255.0);
    ("../tests/llvm-arith/double/snan.ll", snan) ;
    ("../tests/llvm-arith/double/qnan.ll", qnan) ;
    ("../tests/llvm-arith/double/max.ll" , 2.0 ) ;
    ("../tests/llvm-arith/double/max1.ll", qnan) ;
    ("../tests/llvm-arith/double/max2.ll", qnan) ;
    ("../tests/llvm-arith/double/max3.ll", qnan) ;
    ("../tests/llvm-arith/double/max4.ll", qnan) ;
    ("../tests/llvm-arith/double/min.ll" , 1.0 ) ;
    ("../tests/llvm-arith/double/min4.ll", qnan)
  ]

let arith_tests : (string * int) list =
  [ "../tests/ll/add.ll", 14
  ; "../tests/ll/sub.ll", 1
  ; "../tests/ll/mul.ll", 45
  ; "../tests/ll/and.ll", 0
  ; "../tests/ll/or.ll",  1
  ; "../tests/ll/xor.ll", 0
  ; "../tests/ll/shl.ll", 168
  ; "../tests/ll/lshr.ll", 10
  ; "../tests/ll/ashr.ll", 5 ]
  @
  [ "../tests/ll/add_twice.ll", 29
  ; "../tests/ll/sub_neg.ll", -1 (* Why, oh why, does the termianl only report the last byte? *)
  ; "../tests/ll/arith_combo.ll", 4
  ; "../tests/ll/return_intermediate.ll", 18 ]

  
let calling_convention_tests =
  [ "../tests/ll/call.ll", 42
  ; "../tests/ll/call1.ll", 17
  ; "../tests/ll/call2.ll", 19
  ; "../tests/ll/call3.ll", 34
  ; "../tests/ll/call4.ll", 34
  ; "../tests/ll/call5.ll", 24
  ; "../tests/ll/call6.ll", 26
  ]

let memory_tests =
  [ "../tests/ll/alloca1.ll", 17
  ; "../tests/ll/alloca2.ll", 17
  ; "../tests/ll/global1.ll", 12
  ]

let phi_tests =
  [ "../tests/ll/phi0.ll", 0
  ; "../tests/ll/phi1.ll", 1
  ; "../tests/ll/phi2.ll", 0
  ; "../tests/ll/phi3.ll", 1
  ]

let terminator_tests =
  [ "../tests/ll/return.ll", 0
  ; "../tests/ll/return42.ll", 42
  ; "../tests/ll/br1.ll", 9
  ; "../tests/ll/br2.ll", 17
  ; "../tests/ll/cbr1.ll", 7
  ; "../tests/ll/cbr2.ll", 9
  ; "../tests/ll/duplicate_lbl.ll", 1
  ; "../tests/ll/switch1.ll", 0
  ; "../tests/ll/switch2.ll", 0
  ; "../tests/ll/switch3.ll", 0
  ]

let bitcast_tests =
  [ "../tests/ll/bitcast1.ll", 3
  ]

let c_tests =
  [ "../tests/c/average.ll", 2 ]

let other_tests =
  arith_tests @ calling_convention_tests @ memory_tests @ phi_tests @ terminator_tests @ bitcast_tests



let sum_tree_tests = ["../tests/ll/sum_tree.ll", 116]
let gcd_euclidian_tests = [ "../tests/ll/gcd_euclidian.ll", 2]
let binary_search_tests = ["../tests/ll/binarysearch.ll", 8]
let gep_5_deep_tests = ["../tests/ll/qtree.ll", 3]
let binary_gcd_tests = ["../tests/ll/binary_gcd.ll", 3]
let linear_search_tests = ["../tests/ll/linear_search.ll", 1]
let lfsr_tests = ["../tests/ll/lfsr.ll", 108]
let naive_factor_tests =
  [ "../tests/ll/naive_factor_prime.ll", 1
  ; "../tests/ll/naive_factor_nonprime.ll", 0
  ]
let euclid_recursive_test = ["../tests/ll/euclid.ll", 2]
let matmul_tests = ["../tests/ll/matmul.ll", 0]

(* STUBWITH *)

let larger_tests =
  sum_tree_tests
  @ gcd_euclidian_tests
  @ binary_search_tests
  @ gep_5_deep_tests
  @ binary_gcd_tests
  @ linear_search_tests
  @ lfsr_tests
  @ naive_factor_tests
  @ euclid_recursive_test
  @ matmul_tests

let large_tests = [ "../tests/ll/list1.ll", 3
                  ; "../tests/ll/cbr.ll", 42
                  ; "../tests/ll/factorial.ll", 120
                  ; "../tests/ll/factrect.ll", 120
                  ; "../tests/ll/duplicate_factorial.ll", 240
                  ]



let intrinsics_tests : (string * float) list =
  [
    ("../tests/intrinsics/llvm_fabs_f64.ll", 1.0)
  ]

let parse_files =
  [  ]

let test_dirs =
  ["../tests/ll/";
   "../tests/llvm-arith/i1/";
   "../tests/llvm-arith/i8/";
   "../tests/llvm-arith/i32/";
   "../tests/llvm-arith/i64/";
   "../tests/llvm-arith/float/";
   "../tests/llvm-arith/double/";
  ]

let poison_test = function
  | DV.UVALUE_Poison -> true
  | _ -> false

let i1_test (i1:int1) = function
  | DV.UVALUE_I1 i2 ->
     Int1.eq i1 i2
  | _ -> false

let i8_test (i1:int8) = function
  | DV.UVALUE_I1 i2 ->
     Int8.eq i1 i2
  | _ -> false

let i32_test (i1:int32) = function
  | DV.UVALUE_I32 i2 ->
     Int32.eq i1 i2
  | _ -> false

let i64_test (i1:int64) = function
  | DV.UVALUE_I64 i2 ->
     Int64.eq i1 i2
  | _ -> false

(* NOTE: OCaml's floats are actually 64-bit doubles, but contain 32-bit floats as a subset *)
let float_test (i1:float) = function
  | DV.UVALUE_Float i2 ->
    compare i1 (Camlcoq.camlfloat_of_coqfloat32 i2) = 0
  | _ -> false

let double_test (i1:float) = function
  | DV.UVALUE_Double i2 ->
    compare i1 (Camlcoq.camlfloat_of_coqfloat i2) = 0
  | _ -> false



let i1_of_int i = Int1.repr (Camlcoq.Z.of_sint i)

let i8_of_int i = Int8.repr (Camlcoq.Z.of_sint i)

let i32_of_int i = Int32.repr (Camlcoq.Z.of_sint i)

let i64_of_int i = Int64.repr (Camlcoq.Z.of_sint i)

let suite = [Test ("Poison",
                   List.map (fun f ->
                       (f, fun () -> run_uvalue_test poison_test f))
                     poison_tests);

             Test ("I1-arith",
                   List.map (fun (f, i) ->
                       (f, fun () -> run_uvalue_test (i1_test (i1_of_int i)) f))
                     i1_tests);

             Test ("I8-arith",
                   List.map (fun (f, i) ->
                       (f, fun () -> run_uvalue_test (i8_test (i8_of_int i)) f))
                     i1_tests);

             Test ("I32-arith",
                   List.map (fun (f, i) ->
                       (f, fun () -> run_uvalue_test (i32_test (i32_of_int i)) f))
                     i32_tests);

             Test ("I64-arith",
                   List.map (fun (f, i) ->
                       (f, fun () -> run_uvalue_test (i64_test (i64_of_int i)) f))
                     i64_tests);

             Test ("Float-arith",
                   List.map (fun (f, i) ->
                       (f, (fun () -> run_uvalue_test (float_test i) f)))
                       float_tests);

             Test ("Double-arith",
                   List.map (fun (f, i) ->
                       (f, (fun () -> run_uvalue_test (double_test i) f)))
                       double_tests);

             Test ("Other Tests",
                   List.map (fun (f, i) ->
                       (f, fun () -> run_uvalue_test (i64_test (i64_of_int i)) f))
                     other_tests);

             Test ("Larger Tests",
                   List.map (fun (f, i) ->
                       (f, fun () -> run_uvalue_test (i64_test (i64_of_int i)) f))
                     (larger_tests @ large_tests));

             Test ("C Tests",
                   List.map (fun (f, i) ->
                       (f, fun () -> run_uvalue_test (i32_test (i32_of_int i)) f))
                     (c_tests));

             
             (* Test ("Parsing-Must-fail",
              *       List.map (fun (f, p) ->
              *           (f, (fun () -> run_parsefail_test f p)))
              *         must_fail_tests); *)

             Test ("Intrinsics",
                   List.map (fun (f, i) ->
                       (f, (fun () -> run_uvalue_test (double_test i) f)))
                     intrinsics_tests);


            ]


            (* @
             *   (List.map pp_test_of_dir test_dirs) *)

