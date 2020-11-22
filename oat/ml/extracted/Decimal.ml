open Datatypes

type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

(** val uint_rect :
    'a1 -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 ->
    'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 ->
    'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 ->
    'a1) -> (uint -> 'a1 -> 'a1) -> uint -> 'a1 **)

let rec uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 = function
| Nil -> f
| D0 u0 -> f0 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0)
| D1 u0 -> f1 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0)
| D2 u0 -> f2 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0)
| D3 u0 -> f3 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0)
| D4 u0 -> f4 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0)
| D5 u0 -> f5 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0)
| D6 u0 -> f6 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0)
| D7 u0 -> f7 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0)
| D8 u0 -> f8 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0)
| D9 u0 -> f9 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0)

(** val uint_rec :
    'a1 -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 ->
    'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 ->
    'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 ->
    'a1) -> (uint -> 'a1 -> 'a1) -> uint -> 'a1 **)

let rec uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 = function
| Nil -> f
| D0 u0 -> f0 u0 (uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0)
| D1 u0 -> f1 u0 (uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0)
| D2 u0 -> f2 u0 (uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0)
| D3 u0 -> f3 u0 (uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0)
| D4 u0 -> f4 u0 (uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0)
| D5 u0 -> f5 u0 (uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0)
| D6 u0 -> f6 u0 (uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0)
| D7 u0 -> f7 u0 (uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0)
| D8 u0 -> f8 u0 (uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0)
| D9 u0 -> f9 u0 (uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 u0)

type int =
| Pos of uint
| Neg of uint

type decimal =
| Decimal of int * uint
| DecimalExp of int * uint * int

(** val uint_beq : uint -> uint -> bool **)

let rec uint_beq x y =
  match x with
  | Nil -> (match y with
            | Nil -> true
            | _ -> false)
  | D0 x0 -> (match y with
              | D0 x1 -> uint_beq x0 x1
              | _ -> false)
  | D1 x0 -> (match y with
              | D1 x1 -> uint_beq x0 x1
              | _ -> false)
  | D2 x0 -> (match y with
              | D2 x1 -> uint_beq x0 x1
              | _ -> false)
  | D3 x0 -> (match y with
              | D3 x1 -> uint_beq x0 x1
              | _ -> false)
  | D4 x0 -> (match y with
              | D4 x1 -> uint_beq x0 x1
              | _ -> false)
  | D5 x0 -> (match y with
              | D5 x1 -> uint_beq x0 x1
              | _ -> false)
  | D6 x0 -> (match y with
              | D6 x1 -> uint_beq x0 x1
              | _ -> false)
  | D7 x0 -> (match y with
              | D7 x1 -> uint_beq x0 x1
              | _ -> false)
  | D8 x0 -> (match y with
              | D8 x1 -> uint_beq x0 x1
              | _ -> false)
  | D9 x0 -> (match y with
              | D9 x1 -> uint_beq x0 x1
              | _ -> false)

(** val uint_eq_dec : uint -> uint -> bool **)

let uint_eq_dec x y =
  let b = uint_beq x y in if b then true else false

(** val int_beq : int -> int -> bool **)

let int_beq x y =
  match x with
  | Pos d -> (match y with
              | Pos d0 -> uint_beq d d0
              | Neg _ -> false)
  | Neg d -> (match y with
              | Pos _ -> false
              | Neg d0 -> uint_beq d d0)

(** val int_eq_dec : int -> int -> bool **)

let int_eq_dec x y =
  let b = int_beq x y in if b then true else false

(** val decimal_beq : decimal -> decimal -> bool **)

let decimal_beq x y =
  match x with
  | Decimal (i, f) ->
    (match y with
     | Decimal (i0, f0) -> (&&) (int_beq i i0) (uint_beq f f0)
     | DecimalExp (_, _, _) -> false)
  | DecimalExp (i, f, e) ->
    (match y with
     | Decimal (_, _) -> false
     | DecimalExp (i0, f0, e0) ->
       (&&) (int_beq i i0) ((&&) (uint_beq f f0) (int_beq e e0)))

(** val decimal_eq_dec : decimal -> decimal -> bool **)

let decimal_eq_dec x y =
  let b = decimal_beq x y in if b then true else false

(** val nb_digits : uint -> nat **)

let rec nb_digits = function
| Nil -> O
| D0 d0 -> S (nb_digits d0)
| D1 d0 -> S (nb_digits d0)
| D2 d0 -> S (nb_digits d0)
| D3 d0 -> S (nb_digits d0)
| D4 d0 -> S (nb_digits d0)
| D5 d0 -> S (nb_digits d0)
| D6 d0 -> S (nb_digits d0)
| D7 d0 -> S (nb_digits d0)
| D8 d0 -> S (nb_digits d0)
| D9 d0 -> S (nb_digits d0)

(** val nzhead : uint -> uint **)

let rec nzhead d = match d with
| D0 d0 -> nzhead d0
| _ -> d

(** val unorm : uint -> uint **)

let unorm d =
  match nzhead d with
  | Nil -> D0 Nil
  | x -> x

(** val norm : int -> int **)

let norm = function
| Pos d0 -> Pos (unorm d0)
| Neg d0 -> (match nzhead d0 with
             | Nil -> Pos (D0 Nil)
             | x -> Neg x)

(** val opp : int -> int **)

let opp = function
| Pos d0 -> Neg d0
| Neg d0 -> Pos d0

(** val revapp : uint -> uint -> uint **)

let rec revapp d d' =
  match d with
  | Nil -> d'
  | D0 d0 -> revapp d0 (D0 d')
  | D1 d0 -> revapp d0 (D1 d')
  | D2 d0 -> revapp d0 (D2 d')
  | D3 d0 -> revapp d0 (D3 d')
  | D4 d0 -> revapp d0 (D4 d')
  | D5 d0 -> revapp d0 (D5 d')
  | D6 d0 -> revapp d0 (D6 d')
  | D7 d0 -> revapp d0 (D7 d')
  | D8 d0 -> revapp d0 (D8 d')
  | D9 d0 -> revapp d0 (D9 d')

(** val rev : uint -> uint **)

let rev d =
  revapp d Nil

(** val app : uint -> uint -> uint **)

let app d d' =
  revapp (rev d) d'

(** val app_int : int -> uint -> int **)

let app_int d1 d2 =
  match d1 with
  | Pos d3 -> Pos (app d3 d2)
  | Neg d3 -> Neg (app d3 d2)

(** val nztail : uint -> uint * nat **)

let nztail d =
  let aux =
    let rec aux d_rev = match d_rev with
    | D0 d_rev0 -> let (r, n) = aux d_rev0 in (r, (S n))
    | _ -> (d_rev, O)
    in aux
  in
  let (r, n) = aux (rev d) in ((rev r), n)

(** val nztail_int : int -> int * nat **)

let nztail_int = function
| Pos d0 -> let (r, n) = nztail d0 in ((Pos r), n)
| Neg d0 -> let (r, n) = nztail d0 in ((Neg r), n)

(** val del_head : nat -> uint -> uint **)

let rec del_head n d =
  match n with
  | O -> d
  | S n0 ->
    (match d with
     | Nil -> D0 Nil
     | D0 d0 -> del_head n0 d0
     | D1 d0 -> del_head n0 d0
     | D2 d0 -> del_head n0 d0
     | D3 d0 -> del_head n0 d0
     | D4 d0 -> del_head n0 d0
     | D5 d0 -> del_head n0 d0
     | D6 d0 -> del_head n0 d0
     | D7 d0 -> del_head n0 d0
     | D8 d0 -> del_head n0 d0
     | D9 d0 -> del_head n0 d0)

(** val del_head_int : nat -> int -> uint **)

let del_head_int n = function
| Pos d0 -> del_head n d0
| Neg d0 -> del_head n d0

(** val del_tail : nat -> uint -> uint **)

let del_tail n d =
  rev (del_head n (rev d))

(** val del_tail_int : nat -> int -> int **)

let del_tail_int n = function
| Pos d0 -> Pos (del_tail n d0)
| Neg d0 -> Neg (del_tail n d0)

module Little =
 struct
  (** val succ : uint -> uint **)

  let rec succ = function
  | Nil -> D1 Nil
  | D0 d0 -> D1 d0
  | D1 d0 -> D2 d0
  | D2 d0 -> D3 d0
  | D3 d0 -> D4 d0
  | D4 d0 -> D5 d0
  | D5 d0 -> D6 d0
  | D6 d0 -> D7 d0
  | D7 d0 -> D8 d0
  | D8 d0 -> D9 d0
  | D9 d0 -> D0 (succ d0)

  (** val double : uint -> uint **)

  let rec double = function
  | Nil -> Nil
  | D0 d0 -> D0 (double d0)
  | D1 d0 -> D2 (double d0)
  | D2 d0 -> D4 (double d0)
  | D3 d0 -> D6 (double d0)
  | D4 d0 -> D8 (double d0)
  | D5 d0 -> D0 (succ_double d0)
  | D6 d0 -> D2 (succ_double d0)
  | D7 d0 -> D4 (succ_double d0)
  | D8 d0 -> D6 (succ_double d0)
  | D9 d0 -> D8 (succ_double d0)

  (** val succ_double : uint -> uint **)

  and succ_double = function
  | Nil -> D1 Nil
  | D0 d0 -> D1 (double d0)
  | D1 d0 -> D3 (double d0)
  | D2 d0 -> D5 (double d0)
  | D3 d0 -> D7 (double d0)
  | D4 d0 -> D9 (double d0)
  | D5 d0 -> D1 (succ_double d0)
  | D6 d0 -> D3 (succ_double d0)
  | D7 d0 -> D5 (succ_double d0)
  | D8 d0 -> D7 (succ_double d0)
  | D9 d0 -> D9 (succ_double d0)
 end

(** val uint_of_uint : uint -> uint **)

let uint_of_uint i =
  i

(** val int_of_int : int -> int **)

let int_of_int i =
  i
