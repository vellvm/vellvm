let str = Camlcoq.coqstring_of_camlstring
let of_str = Camlcoq.camlstring_of_coqstring


let coq_of_int = Camlcoq.Z.of_sint
let to_int = Camlcoq.Z.to_int
let n_to_int = Camlcoq.N.to_int
let pos_to_int = Camlcoq.P.to_int

let n_of_z z = Camlcoq.N.of_int64 (Camlcoq.Z.to_int64 z)
let pos_of_z z = Camlcoq.P.of_int64 (Camlcoq.Z.to_int64 z)

(* fails if the represenation isn't a positive decimal integer *)
let n_of_int_syntax (z:Number.signed_int) =
  match z with
  | Number.IntDecimal (Decimal.Pos u) -> ParserHelper.coq_N_of_uint u
  | Number.IntHexadecimal (Hexadecimal.Pos u) -> ParserHelper.coq_N_of_hex_uint u
  | _ -> failwith "n_of_int_syntax got invalid syntax"


let append_hexdigit (h:int64) (acc:Hexadecimal.uint) : Hexadecimal.uint =
  let open Hexadecimal in 
  begin match h with
  | 0x0L -> D0 acc
  | 0x1L -> D1 acc
  | 0x2L -> D2 acc
  | 0x3L -> D3 acc
  | 0x4L -> D4 acc
  | 0x5L -> D5 acc
  | 0x6L -> D6 acc
  | 0x7L -> D7 acc
  | 0x8L -> D8 acc
  | 0x9L -> D9 acc
  | 0xaL -> Da acc
  | 0xbL -> Db acc
  | 0xcL -> Dc acc
  | 0xdL -> Dd acc
  | 0xeL -> De acc
  | 0xfL -> Df acc
  | _ -> failwith "append_hexdigit got non-hex int value"
  end


let hexadecimal_uint_to_int64 (h:Hexadecimal.uint) : int64 =
  let open Hexadecimal in
  let open Int64 in

  let rec helper (h:Hexadecimal.uint) (acc:int64) : int64 =
    let acc' = shift_left acc 4 in 
    match h with
    | Nil -> acc
    | D0 u -> helper u (add acc' 0x0L)
    | D1 u -> helper u (add acc' 0x1L)
    | D2 u -> helper u (add acc' 0x2L)
    | D3 u -> helper u (add acc' 0x3L)
    | D4 u -> helper u (add acc' 0x4L)
    | D5 u -> helper u (add acc' 0x5L)
    | D6 u -> helper u (add acc' 0x6L)
    | D7 u -> helper u (add acc' 0x7L)
    | D8 u -> helper u (add acc' 0x8L)
    | D9 u -> helper u (add acc' 0x9L)
    | Da u -> helper u (add acc' 0xaL)
    | Db u -> helper u (add acc' 0xbL)
    | Dc u -> helper u (add acc' 0xcL)
    | Dd u -> helper u (add acc' 0xdL)
    | De u -> helper u (add acc' 0xeL)
    | Df u -> helper u (add acc' 0xfL)
  in
  helper h 0x0L

(* Prepends the [d]th hexadecimal digit of the int64 [x] onto [acc].  
   0 <= d < 16  digits are numbered so that digit 0 is the least signicant
   bits and digit 16 is the most significant.

 *)
let int_to_coq_hexadecimal_uint (x:int64) (d:int) (acc:Hexadecimal.uint) : Hexadecimal.uint =
  if d < 0 || d >= 16 then failwith (Printf.sprintf "int_to_coq_hexadecimal got bad digit: %d" d)
  else
    let open Int64 in
    (* right-shift x by 4 * d bits *)
    let x_shifted = shift_right_logical x (4*d) in
    let x_masked = logand x_shifted 0xfL in
    append_hexdigit x_masked acc 
    

(* byte to hexadecimal *)
let byte_to_coq_hexadecimal_uint (b:char) : Hexadecimal.uint =
  let b_int64 = Int64.of_int (Char.code b) in
  int_to_coq_hexadecimal_uint b_int64 1 (
      int_to_coq_hexadecimal_uint b_int64 0
        Hexadecimal.Nil)


(* SAZ: Need to audit the string handling.*)
let byte_to_i8 (b:char) =
  (LLVMAst.TYPE_I (pos_of_z (coq_of_int 8)), LLVMAst.EXP_Integer (Number.IntHexadecimal (Hexadecimal.Pos (byte_to_coq_hexadecimal_uint b))))

let i8_to_byte (typ, exp) =
  begin match (typ, exp) with
  | LLVMAst.TYPE_I sz, LLVMAst.EXP_Integer (Number.IntHexadecimal (Hexadecimal.Pos u)) ->
     if (pos_to_int sz) <> 8 then failwith "i8_to_byte failed with non-byte type annotation"
     else Char.chr (Int64.to_int (hexadecimal_uint_to_int64 u))
  | _ -> failwith "i8_to_byte failed with incorrect type/value"
  end


(* Dealing with C escape sequences: 
    escape   : bytes -> bytes
    unescape : bytes -> bytes

*)

(* 
   c :: tail
 *)

let octal_digit (c : char) : int option  =
  let c = Char.code c in
  if c < 48 || c > 55
  then None
  else Some (c - 48)

let hex_digit (c : char) : int option  =
  let c = Char.code c in
  if 48 <= c && c <= 57 then Some (c - 48)            (* 0 .. 9 *)
  else if 65 <= c && c <= 70 then Some (c - 65 + 10)  (* A .. F *)
  else if 97 <= c && c <= 102 then Some (c - 97 + 10) (* a .. f *)
  else None


(* 
   SAZ: Despite their name, the so called "c string" literals in LLVM IR
   really don't have anything to do with C strings.  They don't use any of
   the same syntactic conventions for escape characters.

   In LLVM the only form of escaped characters are \\ (slash) or
   \hh where h is a hex number.
 *)


(* Parses a sequence of characters following a \ to see if it is a legal LLVM IR
   escape sequence (excluding the leading \). 
   returns 
      None if the sequence isn't legal
      Some (c, rest), where c is the decoded byte and rest is the remainder of the list.
*)
let interpret_escaped str : (char * char list) option =
  begin match str with
  | [] ->
     None

  | '\\' :: rest ->
     (* found second \, so it is valid *)
     Some ('\\', rest)
     
  | c1 :: c2 :: rest ->
     begin match (hex_digit c1, hex_digit c2) with
     | Some d1, Some d2  ->
        Some (Char.chr (16 * d1 + d2), rest)
     | _ ->
        None
     end

  | _ ->
     None
  end

let unescape (str : char list) : char list =
  let rec go str acc =
    begin match str with
    | [] ->
       List.rev acc 

    | '\\' :: esc ->
       begin match interpret_escaped esc with
       | None -> go esc ('\\'::acc)
       | Some (c, rest) -> go rest (c::acc)
       end
          
    | x :: rest ->
       go rest (x::acc)
    end
  in
  go str []

let int_to_hex_digit (h : int) : char =
  if h < 10
  then Char.chr (h+48)
  else Char.chr (h-10 + 65)

let to_hex_digits (c : char) : char * char =
  let u = (Char.code c) / 16 in
  let l = (Char.code c) mod 16 in
  (int_to_hex_digit u, int_to_hex_digit l)

(* Characters that _must_ be escaped inside of strings are the "unprintable" characters:
   (Char.code c) < 32 || (Char.code c) >= 127
 *)
let escape_char (c:char) : char list =
  let code = Char.code c in 
  if (code < 32) || (code >= 127) || code = 34 then
    let (u,l) = to_hex_digits c in ['\\';u;l]
  else if code = 92 then ['\\';'\\']
  else [c]

let escape (str : char list) : char list =
  List.concat_map escape_char str

let cstring_bytes_to_LLVM_i8_array bytes =
  List.map byte_to_i8 bytes

let llvm_i8_array_to_cstring_bytes arr =
  List.map i8_to_byte arr


let coqfloat_of_string d =
  Floats.Float.of_bits(Camlcoq.coqint_of_camlint64(Int64.bits_of_float (float_of_string d)))

let coqfloat32_of_string d =
  Floats.Float32.of_bits(Camlcoq.coqint_of_camlint(Int32.bits_of_float (float_of_string d)))

let rec string_of_positive =
  let open BinNums in
  function 
    | Coq_xI p -> string_of_positive p ^ "1"
    | Coq_xO p -> string_of_positive p ^ "0"
    | Coq_xH -> "1"

let string_of_Z =
  let open BinNums in
  function
    | Z0 -> "0"
    | Zpos v -> string_of_positive v
    | Zneg v -> "-" ^ (string_of_positive v)


let float_of_coqfloat = Camlcoq.camlfloat_of_coqfloat


(*  ------------------------------------------------------------------------- *)
(* Dealing with anonymous LLVM locals / block identifiers *)

type lexed_id =
  | Anonymous of int
  | Named of string

exception InvalidAnonymousId of string

type ctr = {peek : unit -> int ; get : unit -> int; set : int -> unit; reset : unit -> unit}
let mk_counter () =
  let c = ref 0 in
  { peek = (fun () -> !c);
    get = (fun () -> let cnt = !c in incr c; cnt);
    set = (fun cnt -> c := cnt);
    reset = (fun () -> c := 0);
  }

let anon_ctr = mk_counter ()
let void_ctr = mk_counter ()             

let generate_anon_raw_id () : LLVMAst.raw_id =
  (* (Printf.fprintf stderr "gnerate_anon_raw_id = %d" (anon_ctr.peek ())); *)
  LLVMAst.Anon (coq_of_int (anon_ctr.get ()))

let generate_void_instr_id () : LLVMAst.instr_id =
  LLVMAst.IVoid (coq_of_int (void_ctr.get ()))

let validate_declared_int n =
  let expected = anon_ctr.get () in
  if expected <= n
  then begin
      anon_ctr.set (n + 1);
      (LLVMAst.Anon (coq_of_int n))
    end
  else
    let msg = Printf.sprintf "Unexpected sequential id: expected >= %n but found %n" expected n in
    raise (InvalidAnonymousId msg)

let validate_bound_lexed_id (r : lexed_id) : LLVMAst.raw_id =
  match r with
  | Anonymous n -> validate_declared_int n
  | Named s     -> LLVMAst.Name (str s)  (* named identifiers are always OK *)

let validate_label (l : string) : LLVMAst.raw_id =
  try
    let n = int_of_string l in
    validate_declared_int n
  with
  | Failure _ -> LLVMAst.Name (str l)

let check_or_generate_label (lo : string option) : LLVMAst.raw_id =
  match lo with
  | None   -> generate_anon_raw_id ()
  | Some l -> validate_label l

let check_or_generate_id (lo : lexed_id option) : LLVMAst.raw_id =
  match lo with
  | None   -> generate_anon_raw_id ()
  | Some l -> validate_bound_lexed_id l

let lexed_id_to_raw_id (r : lexed_id) : LLVMAst.raw_id =
  match r with
  | Anonymous n -> LLVMAst.Anon (coq_of_int n)
  | Named s -> LLVMAst.Name (str s)  (* named identifiers are always OK *)

