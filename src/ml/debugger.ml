module DV = DynamicValues
open LLVMEvents

open ITreeDefinition
open Result
open Interpreter

(* Vellvm debugger ---------------------------------------------------------- *)

type __ = Obj.t

let string_of_dvalue (d : DV.dvalue) =
  Camlcoq.camlstring_of_coqstring (DV.show_dvalue Interpreter.params d)

type file_location =
  { file : string;
    line_start : int option;
    column_start : int option;
    line_end : int option;
    column_end : int option;
  }

let show_int_option lo =
  match lo with
  | None -> ""
  | Some x -> string_of_int x

let show_file_location fl =
  match fl with
  | { file; line_start; column_start; line_end; column_end } ->
      file ^ ":" ^ show_int_option line_start ^ "." ^ show_int_option column_start ^ "-" ^ show_int_option line_end ^ "." ^ show_int_option column_end

type breakpoint = BreakpointLoc of file_location

let show_breakpoint bp =
  match bp with
  | BreakpointLoc fl -> show_file_location fl

type debug_state =
  { breakpoints : (int, breakpoint) Hashtbl.t;
    mutable max_breakpoint : int;
  }

let last_line = ref (Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()))
let current_line = ref (Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()))
let state = ref { breakpoints = Hashtbl.create 0; max_breakpoint = 0; }

let debug_raw_step m =
  (match single_step m with
  | Either.Left x ->
     let loc_str = Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()) in
     last_line := !current_line;
     current_line := loc_str;
     Either.Left x
  | res -> res)

(**
Takes in two lists, and returns a triple:
- pairs of elements with matching indices from l1 and l2
- either
  - elements of l1 that have no matching index in l2 (when l1 is longer than l2)
  - elements of l2 that have no matching index in l1 (when l2 is longer than l1)
  - or None if the lists had the same length
*)
let group_matching_indices l1 l2 =
  let rec aux l1 l2 acc =
    match (l1, l2) with
    | ([], []) -> (acc, None)
    | ([], _) -> (acc, Some (Either.Right l2))
    | (_, []) -> (acc, Some (Either.Left l1))
    | (h1::t1, h2::t2) -> aux t1 t2 ((h1, h2)::acc)
  in aux l1 l2 []

let new_stack_vars s1 s2 =
  let (common, rest) = group_matching_indices s1 s2 in
  let vars_from_new_frames =
    match rest with
    | None -> []
    | Some (Either.Left _) -> []
    | Some (Either.Right r) -> List.concat (List.map (fun c -> List.rev (RawIdMaps.RM.elements (c : Stack.stack_frame).stack_vars)) r)
  in
  let vars_from_last_common_frame =
    match List.rev common with
    | [] -> []
    | (c1, c2)::_ ->
      let sv1 = RawIdMaps.RM.elements (c1 : Stack.stack_frame).stack_vars in
      let sv2 = RawIdMaps.RM.elements (c2 : Stack.stack_frame).stack_vars in
      List.filter
        (fun (k, v) ->
          match List.find_opt (fun (k', _) -> k == k') sv1 with
          | None -> true (* new key*)
          | Some (_, v') -> v != v' (* updated value *))
        sv2
  in List.append vars_from_last_common_frame vars_from_new_frames

(* Step will step into function calls *)
let rec step m =
  let before_stack = (Stack.local_stack_object Interpreter.params).local_stack_get () in
  (match debug_raw_step m with
  | Either.Left x ->
     if !current_line = "" || !current_line = !last_line
     then step x
     else 
      let after_stack = (Stack.local_stack_object Interpreter.params).local_stack_get () in
      List.iter
        (fun (k, v) -> Printf.printf "%s -> %s\n" (Camlcoq.camlstring_of_coqstring (ShowAST.show_raw_id k)) (string_of_dvalue v))
        (new_stack_vars before_stack after_stack);
      Either.Left x
  | res -> res)

(* Next will skip over function calls *)
let rec next_helper level m =
  match step m with
  | Either.Left x ->
     let new_stack_level = List.length ((Stack.local_stack_object Interpreter.params).local_stack_get ()) in
     if new_stack_level = level
     then Either.Left x
     else next_helper level x
  | res -> res

let next m =
  let stack_level = List.length ((Stack.local_stack_object Interpreter.params).local_stack_get ()) in
  next_helper stack_level m

let location_parse loc =
  let r = Str.regexp {|^\[\([^:]*\):\([0-9]+\)\.\([0-9]+\)-\([0-9]+\)\.\([0-9]+\)\]$|} in
  if Str.string_match r loc 0
  then
    (* Successful parse *)
    Some { file = Str.matched_group 1 loc
         ; line_start = Some (int_of_string (Str.matched_group 2 loc))
         ; column_start = Some (int_of_string (Str.matched_group 3 loc))
         ; line_end = Some (int_of_string (Str.matched_group 4 loc))
         ; column_end = Some (int_of_string (Str.matched_group 5 loc))
      }
  else None

let option_wild_match x y =
  match x with
  | Some _ -> x = y
  | None -> true

let file_location_match bp l =
  bp.file = l.file &&
    option_wild_match bp.line_start l.line_start &&
    option_wild_match bp.column_start l.column_start &&
    option_wild_match bp.line_end l.line_end &&
    option_wild_match bp.column_end l.column_end

(* Check if the current line matches any active breakpoints *)
let breakpoint_match loc =
  match location_parse loc with
  | Some l ->
     let bps = Hashtbl.to_seq_values !state.breakpoints in
     Stdlib.Seq.exists
       (fun x ->
         match x with
         | BreakpointLoc bp ->
            file_location_match bp l) bps
  | None -> false

let rec continue m =
  (* Use next to skip past any current breakpoints *)
  (match next m with
  | Either.Left x ->
     if breakpoint_match !current_line
     then Either.Left x
     else continue x
  | res -> res)

type debug_command =
  Next | Step | Continue | Quit | AddBreakpoint of (string * int) |
  PrintGlobals | PrintLocals | PrintBreakpoints | RemoveBreakpoint of int |
  StackTrace | Help

let rec read_command () =
  Printf.printf ("(vellvm)> ");
  let str = read_line () in
  match str with
  | "n" -> Next
  | "s" -> Step
  | "c" -> Continue
  | "q" -> Quit
  | "pg" -> PrintGlobals
  | "pl" -> PrintLocals
  | "pb" -> PrintBreakpoints
  | "bt" -> StackTrace
  | "st" -> StackTrace
  | "rb" ->
     let bp = read_int () in
     RemoveBreakpoint bp
  | "b" ->
     let file = read_line () in
     let line = read_int () in
     AddBreakpoint (file, line)
  | "h" -> Help
  | _ -> Printf.printf "Invalid command.\n"; read_command ()

let print_stack_frame_vars (sf : Stack.stack_frame) =
  List.iter (fun (k, v) ->
      Printf.printf "%s -> %s\n" (Camlcoq.camlstring_of_coqstring (ShowAST.show_raw_id k)) (string_of_dvalue v)) (RawIdMaps.RM.elements sf.stack_vars)

let print_stack_vars (s : Stack.stack_frame list) =
  List.iteri (fun n (sf : Stack.stack_frame) ->
      Printf.printf "Stack frame #%d (%s):\n" n (match sf.stack_loc with None -> "_" | Some l -> Camlcoq.camlstring_of_coqstring l);
      print_stack_frame_vars sf) s

let print_stack_frames (s : Stack.stack_frame list) =
  List.iteri (fun n (sf : Stack.stack_frame) ->
      Printf.printf "#%d: %s\n" n (match sf.stack_loc with None -> "_" | Some l -> Camlcoq.camlstring_of_coqstring l)) s

let print_globals g =
  List.iter  (fun (k, v) ->
      Printf.printf "%s -> %s\n" (Camlcoq.camlstring_of_coqstring (ShowAST.show_raw_id k)) (string_of_dvalue v)) (RawIdMaps.RM.elements g)


let help_msg : string =
  "Vellvm Debugger Commands:  \n" ^
    "\t n : run until next breakpoint\n" ^
    "\t s : step\n" ^
    "\t c : continue\n" ^
    "\t q : quit\n" ^
    "\t pg : print global values\n" ^                
    "\t pl : print local values\n" ^
    "\t pb : print breakpoints\n" ^
    "\t bt : print stack trace\n" ^
    "\t st : print stack trace\n" ^
    "\t rb n: remove breakpoint number n\n" ^
    "\t b n : add breakpoint with number n\n" ^
    "\t h : display this help message\n"

let rec debugger
    (m : (__ coq_MCFGEbot, Interpreter.interp_state) itree)
    : (DV.dvalue, exit_condition) result =
  let command = read_command () in
  match command with
  | Next ->
     (match next m with
     | Either.Left x -> debugger x
     | Either.Right res -> res)
  | Step ->
     (match step m with
     | Either.Left x -> debugger x
     | Either.Right res -> res)
  | Continue ->
     (match continue m with
     | Either.Left x -> debugger x
     | Either.Right res -> res)
  | PrintGlobals ->
     let globals = ((Global.globals_object Interpreter.params).globals_get ()) in
     print_globals globals;
     debugger m
  | PrintLocals ->
     let stack = (Stack.local_stack_object Interpreter.params).local_stack_get () in
     print_stack_vars stack;
     debugger m
  | StackTrace ->
     let stack = (Stack.local_stack_object Interpreter.params).local_stack_get () in
     print_stack_frames stack;
     debugger m
  | AddBreakpoint (file, line) ->
     Hashtbl.add !state.breakpoints !state.max_breakpoint (BreakpointLoc { file = file; line_start = Some line; column_start = None; line_end = None; column_end = None });
     Printf.printf "Added breakpoint %d\n" !state.max_breakpoint;
     !state.max_breakpoint <- !state.max_breakpoint + 1;
     debugger m
  | RemoveBreakpoint bp ->
     Hashtbl.remove !state.breakpoints bp;
     debugger m
  | PrintBreakpoints ->
     let bps = Hashtbl.to_seq !state.breakpoints in
     Stdlib.Seq.iter (fun (k, v) -> Printf.printf "%s -> %s\n" (string_of_int k) (show_breakpoint v)) bps;
     debugger m
  | Help ->
     Printf.printf "%s\n" help_msg;
     debugger m
  | Quit -> Error (Failed "Quitting")

let vellvm_debugger
      (args : string list)
      (prog :
         ( LLVMAst.typ
         , LLVMAst.typ LLVMAst.block * LLVMAst.typ LLVMAst.block list )
           LLVMAst.toplevel_entity
           list )
    : (DV.dvalue, exit_condition) result =
  Out_channel.set_buffered stdout false;
  Out_channel.set_buffered stderr false;
  let prog = (TopLevel.interpreter (List.map Camlcoq.coqstring_of_camlstring args) prog) in
  debugger prog
