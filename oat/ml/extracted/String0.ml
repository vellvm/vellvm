open Ascii
open Bool
open Datatypes
open List0

(** val string_rect :
    'a1 -> (char -> char list -> 'a1 -> 'a1) -> char list -> 'a1 **)

let rec string_rect f f0 = function
| [] -> f
| a::s0 -> f0 a s0 (string_rect f f0 s0)

(** val string_rec :
    'a1 -> (char -> char list -> 'a1 -> 'a1) -> char list -> 'a1 **)

let rec string_rec f f0 = function
| [] -> f
| a::s0 -> f0 a s0 (string_rec f f0 s0)

(** val string_dec : char list -> char list -> bool **)

let rec string_dec s x =
  match s with
  | [] -> (match x with
           | [] -> true
           | _::_ -> false)
  | a::s0 ->
    (match x with
     | [] -> false
     | a0::s1 -> if (=) a a0 then string_dec s0 s1 else false)

(** val eqb : char list -> char list -> bool **)

let rec eqb s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _::_ -> false)
  | c1::s1' ->
    (match s2 with
     | [] -> false
     | c2::s2' -> if (=) c1 c2 then eqb s1' s2' else false)

(** val eqb_spec : char list -> char list -> reflect **)

let rec eqb_spec s s2 =
  match s with
  | [] -> (match s2 with
           | [] -> ReflectT
           | _::_ -> ReflectF)
  | a::s0 ->
    (match s2 with
     | [] -> ReflectF
     | a0::s3 ->
       (match Ascii.eqb_spec a a0 with
        | ReflectT -> eqb_spec s0 s3
        | ReflectF -> ReflectF))

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

(** val length : char list -> nat **)

let rec length = function
| [] -> O
| _::s' -> S (length s')

(** val get : nat -> char list -> char option **)

let rec get n = function
| [] -> None
| c::s' -> (match n with
            | O -> Some c
            | S n' -> get n' s')

(** val substring : nat -> nat -> char list -> char list **)

let rec substring n m s =
  match n with
  | O ->
    (match m with
     | O -> []
     | S m' -> (match s with
                | [] -> s
                | c::s' -> c::(substring O m' s')))
  | S n' -> (match s with
             | [] -> s
             | _::s' -> substring n' m s')

(** val concat : char list -> char list list -> char list **)

let rec concat sep = function
| [] -> []
| x :: xs ->
  (match xs with
   | [] -> x
   | _ :: _ -> append x (append sep (concat sep xs)))

(** val prefix : char list -> char list -> bool **)

let rec prefix s1 s2 =
  match s1 with
  | [] -> true
  | a::s1' ->
    (match s2 with
     | [] -> false
     | b::s2' -> if (=) a b then prefix s1' s2' else false)

(** val index : nat -> char list -> char list -> nat option **)

let rec index n s1 s2 = match s2 with
| [] ->
  (match n with
   | O -> (match s1 with
           | [] -> Some O
           | _::_ -> None)
   | S _ -> None)
| _::s2' ->
  (match n with
   | O ->
     if prefix s1 s2
     then Some O
     else (match index O s1 s2' with
           | Some n0 -> Some (S n0)
           | None -> None)
   | S n' ->
     (match index n' s1 s2' with
      | Some n0 -> Some (S n0)
      | None -> None))

(** val findex : nat -> char list -> char list -> nat **)

let findex n s1 s2 =
  match index n s1 s2 with
  | Some n0 -> n0
  | None -> O

(** val string_of_list_ascii : char list -> char list **)

let rec string_of_list_ascii = function
| [] -> []
| ch :: s0 -> ch::(string_of_list_ascii s0)

(** val list_ascii_of_string : char list -> char list **)

let rec list_ascii_of_string = function
| [] -> []
| ch::s0 -> ch :: (list_ascii_of_string s0)

(** val string_of_list_byte : char list -> char list **)

let string_of_list_byte s =
  string_of_list_ascii (map (fun x -> x) s)

(** val list_byte_of_string : char list -> char list **)

let list_byte_of_string s =
  map (fun x -> x) (list_ascii_of_string s)

module StringSyntax =
 struct
 end

(** val coq_HelloWorld : char list **)

let coq_HelloWorld =
  '\t'::('"'::('H'::('e'::('l'::('l'::('o'::(' '::('w'::('o'::('r'::('l'::('d'::('!'::('"'::('\007'::('\n'::[]))))))))))))))))
