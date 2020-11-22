open Datatypes
open Decimal
open Hexadecimal
open Numeral

type t = nat

(** val zero : nat **)

let zero =
  O

(** val one : nat **)

let one =
  S O

(** val two : nat **)

let two =
  S (S O)

(** val succ : nat -> nat **)

let succ x =
  S x

(** val pred : nat -> nat **)

let pred n = match n with
| O -> n
| S u -> u

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val double : nat -> nat **)

let double n =
  add n n

(** val mul : nat -> nat -> nat **)

let rec mul n m =
  match n with
  | O -> O
  | S p -> add m (mul p m)

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

(** val eqb : nat -> nat -> bool **)

let rec eqb n m =
  match n with
  | O -> (match m with
          | O -> true
          | S _ -> false)
  | S n' -> (match m with
             | O -> false
             | S m' -> eqb n' m')

(** val leb : nat -> nat -> bool **)

let rec leb n m =
  match n with
  | O -> true
  | S n' -> (match m with
             | O -> false
             | S m' -> leb n' m')

(** val ltb : nat -> nat -> bool **)

let ltb n m =
  leb (S n) m

(** val compare : nat -> nat -> comparison **)

let rec compare n m =
  match n with
  | O -> (match m with
          | O -> Eq
          | S _ -> Lt)
  | S n' -> (match m with
             | O -> Gt
             | S m' -> compare n' m')

(** val max : nat -> nat -> nat **)

let rec max n m =
  match n with
  | O -> m
  | S n' -> (match m with
             | O -> n
             | S m' -> S (max n' m'))

(** val min : nat -> nat -> nat **)

let rec min n m =
  match n with
  | O -> O
  | S n' -> (match m with
             | O -> O
             | S m' -> S (min n' m'))

(** val even : nat -> bool **)

let rec even = function
| O -> true
| S n0 -> (match n0 with
           | O -> false
           | S n' -> even n')

(** val odd : nat -> bool **)

let odd n =
  negb (even n)

(** val pow : nat -> nat -> nat **)

let rec pow n = function
| O -> S O
| S m0 -> mul n (pow n m0)

(** val tail_add : nat -> nat -> nat **)

let rec tail_add n m =
  match n with
  | O -> m
  | S n0 -> tail_add n0 (S m)

(** val tail_addmul : nat -> nat -> nat -> nat **)

let rec tail_addmul r n m =
  match n with
  | O -> r
  | S n0 -> tail_addmul (tail_add m r) n0 m

(** val tail_mul : nat -> nat -> nat **)

let tail_mul n m =
  tail_addmul O n m

(** val of_uint_acc : Decimal.uint -> nat -> nat **)

let rec of_uint_acc d acc =
  match d with
  | Decimal.Nil -> acc
  | Decimal.D0 d0 ->
    of_uint_acc d0 (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc)
  | Decimal.D1 d0 ->
    of_uint_acc d0 (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc))
  | Decimal.D2 d0 ->
    of_uint_acc d0 (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc)))
  | Decimal.D3 d0 ->
    of_uint_acc d0 (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc))))
  | Decimal.D4 d0 ->
    of_uint_acc d0 (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc)))))
  | Decimal.D5 d0 ->
    of_uint_acc d0 (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc))))))
  | Decimal.D6 d0 ->
    of_uint_acc d0 (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc)))))))
  | Decimal.D7 d0 ->
    of_uint_acc d0 (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc))))))))
  | Decimal.D8 d0 ->
    of_uint_acc d0 (S (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc)))))))))
  | Decimal.D9 d0 ->
    of_uint_acc d0 (S (S (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc))))))))))

(** val of_uint : Decimal.uint -> nat **)

let of_uint d =
  of_uint_acc d O

(** val of_hex_uint_acc : Hexadecimal.uint -> nat -> nat **)

let rec of_hex_uint_acc d acc =
  match d with
  | Nil -> acc
  | D0 d0 ->
    of_hex_uint_acc d0
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc)
  | D1 d0 ->
    of_hex_uint_acc d0 (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc))
  | D2 d0 ->
    of_hex_uint_acc d0 (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc)))
  | D3 d0 ->
    of_hex_uint_acc d0 (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc))))
  | D4 d0 ->
    of_hex_uint_acc d0 (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc)))))
  | D5 d0 ->
    of_hex_uint_acc d0 (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc))))))
  | D6 d0 ->
    of_hex_uint_acc d0 (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc)))))))
  | D7 d0 ->
    of_hex_uint_acc d0 (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc))))))))
  | D8 d0 ->
    of_hex_uint_acc d0 (S (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc)))))))))
  | D9 d0 ->
    of_hex_uint_acc d0 (S (S (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc))))))))))
  | Da d0 ->
    of_hex_uint_acc d0 (S (S (S (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc)))))))))))
  | Db d0 ->
    of_hex_uint_acc d0 (S (S (S (S (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc))))))))))))
  | Dc d0 ->
    of_hex_uint_acc d0 (S (S (S (S (S (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc)))))))))))))
  | Dd d0 ->
    of_hex_uint_acc d0 (S (S (S (S (S (S (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc))))))))))))))
  | De d0 ->
    of_hex_uint_acc d0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc)))))))))))))))
  | Df d0 ->
    of_hex_uint_acc d0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc))))))))))))))))

(** val of_hex_uint : Hexadecimal.uint -> nat **)

let of_hex_uint d =
  of_hex_uint_acc d O

(** val of_num_uint : uint -> nat **)

let of_num_uint = function
| UIntDec d0 -> of_uint d0
| UIntHex d0 -> of_hex_uint d0

(** val to_little_uint : nat -> Decimal.uint -> Decimal.uint **)

let rec to_little_uint n acc =
  match n with
  | O -> acc
  | S n0 -> to_little_uint n0 (Decimal.Little.succ acc)

(** val to_uint : nat -> Decimal.uint **)

let to_uint n =
  Decimal.rev (to_little_uint n (Decimal.D0 Decimal.Nil))

(** val to_little_hex_uint : nat -> Hexadecimal.uint -> Hexadecimal.uint **)

let rec to_little_hex_uint n acc =
  match n with
  | O -> acc
  | S n0 -> to_little_hex_uint n0 (Little.succ acc)

(** val to_hex_uint : nat -> Hexadecimal.uint **)

let to_hex_uint n =
  rev (to_little_hex_uint n (D0 Nil))

(** val to_num_uint : nat -> uint **)

let to_num_uint n =
  UIntDec (to_uint n)

(** val to_num_hex_uint : nat -> uint **)

let to_num_hex_uint n =
  UIntHex (to_hex_uint n)

(** val of_int : Decimal.int -> nat option **)

let of_int d =
  match Decimal.norm d with
  | Decimal.Pos u -> Some (of_uint u)
  | Decimal.Neg _ -> None

(** val of_hex_int : Hexadecimal.int -> nat option **)

let of_hex_int d =
  match norm d with
  | Pos u -> Some (of_hex_uint u)
  | Neg _ -> None

(** val of_num_int : int -> nat option **)

let of_num_int = function
| IntDec d0 -> of_int d0
| IntHex d0 -> of_hex_int d0

(** val to_int : nat -> Decimal.int **)

let to_int n =
  Decimal.Pos (to_uint n)

(** val to_hex_int : nat -> Hexadecimal.int **)

let to_hex_int n =
  Pos (to_hex_uint n)

(** val to_num_int : nat -> int **)

let to_num_int n =
  IntDec (to_int n)

(** val divmod : nat -> nat -> nat -> nat -> nat * nat **)

let rec divmod x y q u =
  match x with
  | O -> (q, u)
  | S x' -> (match u with
             | O -> divmod x' y (S q) y
             | S u' -> divmod x' y q u')

(** val div : nat -> nat -> nat **)

let div x y = match y with
| O -> y
| S y' -> fst (divmod x y' O y')

(** val modulo : nat -> nat -> nat **)

let modulo x y = match y with
| O -> y
| S y' -> sub y' (snd (divmod x y' O y'))

(** val gcd : nat -> nat -> nat **)

let rec gcd a b =
  match a with
  | O -> b
  | S a' -> gcd (modulo b (S a')) (S a')

(** val square : nat -> nat **)

let square n =
  mul n n

(** val sqrt_iter : nat -> nat -> nat -> nat -> nat **)

let rec sqrt_iter k p q r =
  match k with
  | O -> p
  | S k' ->
    (match r with
     | O -> sqrt_iter k' (S p) (S (S q)) (S (S q))
     | S r' -> sqrt_iter k' p q r')

(** val sqrt : nat -> nat **)

let sqrt n =
  sqrt_iter n O O O

(** val log2_iter : nat -> nat -> nat -> nat -> nat **)

let rec log2_iter k p q r =
  match k with
  | O -> p
  | S k' ->
    (match r with
     | O -> log2_iter k' (S p) (S q) q
     | S r' -> log2_iter k' p (S q) r')

(** val log2 : nat -> nat **)

let log2 n =
  log2_iter (pred n) O (S O) O

(** val iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec iter n f x =
  match n with
  | O -> x
  | S n0 -> f (iter n0 f x)

(** val div2 : nat -> nat **)

let rec div2 = function
| O -> O
| S n0 -> (match n0 with
           | O -> O
           | S n' -> S (div2 n'))

(** val testbit : nat -> nat -> bool **)

let rec testbit a = function
| O -> odd a
| S n0 -> testbit (div2 a) n0

(** val shiftl : nat -> nat -> nat **)

let rec shiftl a = function
| O -> a
| S n0 -> double (shiftl a n0)

(** val shiftr : nat -> nat -> nat **)

let rec shiftr a = function
| O -> a
| S n0 -> div2 (shiftr a n0)

(** val bitwise : (bool -> bool -> bool) -> nat -> nat -> nat -> nat **)

let rec bitwise op n a b =
  match n with
  | O -> O
  | S n' ->
    add (if op (odd a) (odd b) then S O else O)
      (mul (S (S O)) (bitwise op n' (div2 a) (div2 b)))

(** val coq_land : nat -> nat -> nat **)

let coq_land a b =
  bitwise (&&) a a b

(** val coq_lor : nat -> nat -> nat **)

let coq_lor a b =
  bitwise (||) (max a b) a b

(** val ldiff : nat -> nat -> nat **)

let ldiff a b =
  bitwise (fun b0 b' -> (&&) b0 (negb b')) a a b

(** val coq_lxor : nat -> nat -> nat **)

let coq_lxor a b =
  bitwise xorb (max a b) a b
