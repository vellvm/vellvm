open BinNums
open BinPos
open Bool
open Datatypes
open Decimal
open Hexadecimal
open Numeral

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module N =
 struct
  type t = coq_N

  (** val zero : coq_N **)

  let zero =
    N0

  (** val one : coq_N **)

  let one =
    Npos Coq_xH

  (** val two : coq_N **)

  let two =
    Npos (Coq_xO Coq_xH)

  (** val succ_double : coq_N -> coq_N **)

  let succ_double = function
  | N0 -> Npos Coq_xH
  | Npos p -> Npos (Coq_xI p)

  (** val double : coq_N -> coq_N **)

  let double = function
  | N0 -> N0
  | Npos p -> Npos (Coq_xO p)

  (** val succ : coq_N -> coq_N **)

  let succ = function
  | N0 -> Npos Coq_xH
  | Npos p -> Npos (Pos.succ p)

  (** val pred : coq_N -> coq_N **)

  let pred = function
  | N0 -> N0
  | Npos p -> Pos.pred_N p

  (** val succ_pos : coq_N -> positive **)

  let succ_pos = function
  | N0 -> Coq_xH
  | Npos p -> Pos.succ p

  (** val add : coq_N -> coq_N -> coq_N **)

  let add n m =
    match n with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n
                 | Npos q -> Npos (Pos.add p q))

  (** val sub : coq_N -> coq_N -> coq_N **)

  let sub n m =
    match n with
    | N0 -> N0
    | Npos n' ->
      (match m with
       | N0 -> n
       | Npos m' ->
         (match Pos.sub_mask n' m' with
          | Pos.IsPos p -> Npos p
          | _ -> N0))

  (** val mul : coq_N -> coq_N -> coq_N **)

  let mul n m =
    match n with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Npos (Pos.mul p q))

  (** val compare : coq_N -> coq_N -> comparison **)

  let compare n m =
    match n with
    | N0 -> (match m with
             | N0 -> Eq
             | Npos _ -> Lt)
    | Npos n' -> (match m with
                  | N0 -> Gt
                  | Npos m' -> Pos.compare n' m')

  (** val eqb : coq_N -> coq_N -> bool **)

  let eqb n m =
    match n with
    | N0 -> (match m with
             | N0 -> true
             | Npos _ -> false)
    | Npos p -> (match m with
                 | N0 -> false
                 | Npos q -> Pos.eqb p q)

  (** val leb : coq_N -> coq_N -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : coq_N -> coq_N -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val min : coq_N -> coq_N -> coq_N **)

  let min n n' =
    match compare n n' with
    | Gt -> n'
    | _ -> n

  (** val max : coq_N -> coq_N -> coq_N **)

  let max n n' =
    match compare n n' with
    | Gt -> n
    | _ -> n'

  (** val div2 : coq_N -> coq_N **)

  let div2 = function
  | N0 -> N0
  | Npos p0 ->
    (match p0 with
     | Coq_xI p -> Npos p
     | Coq_xO p -> Npos p
     | Coq_xH -> N0)

  (** val even : coq_N -> bool **)

  let even = function
  | N0 -> true
  | Npos p -> (match p with
               | Coq_xO _ -> true
               | _ -> false)

  (** val odd : coq_N -> bool **)

  let odd n =
    negb (even n)

  (** val pow : coq_N -> coq_N -> coq_N **)

  let pow n = function
  | N0 -> Npos Coq_xH
  | Npos p0 -> (match n with
                | N0 -> N0
                | Npos q -> Npos (Pos.pow q p0))

  (** val square : coq_N -> coq_N **)

  let square = function
  | N0 -> N0
  | Npos p -> Npos (Pos.square p)

  (** val log2 : coq_N -> coq_N **)

  let log2 = function
  | N0 -> N0
  | Npos p0 ->
    (match p0 with
     | Coq_xI p -> Npos (Pos.size p)
     | Coq_xO p -> Npos (Pos.size p)
     | Coq_xH -> N0)

  (** val size : coq_N -> coq_N **)

  let size = function
  | N0 -> N0
  | Npos p -> Npos (Pos.size p)

  (** val size_nat : coq_N -> nat **)

  let size_nat = function
  | N0 -> O
  | Npos p -> Pos.size_nat p

  (** val pos_div_eucl : positive -> coq_N -> coq_N * coq_N **)

  let rec pos_div_eucl a b =
    match a with
    | Coq_xI a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r')
    | Coq_xO a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r')
    | Coq_xH ->
      (match b with
       | N0 -> (N0, (Npos Coq_xH))
       | Npos p ->
         (match p with
          | Coq_xH -> ((Npos Coq_xH), N0)
          | _ -> (N0, (Npos Coq_xH))))

  (** val div_eucl : coq_N -> coq_N -> coq_N * coq_N **)

  let div_eucl a b =
    match a with
    | N0 -> (N0, N0)
    | Npos na -> (match b with
                  | N0 -> (N0, a)
                  | Npos _ -> pos_div_eucl na b)

  (** val div : coq_N -> coq_N -> coq_N **)

  let div a b =
    fst (div_eucl a b)

  (** val modulo : coq_N -> coq_N -> coq_N **)

  let modulo a b =
    snd (div_eucl a b)

  (** val gcd : coq_N -> coq_N -> coq_N **)

  let gcd a b =
    match a with
    | N0 -> b
    | Npos p -> (match b with
                 | N0 -> a
                 | Npos q -> Npos (Pos.gcd p q))

  (** val ggcd : coq_N -> coq_N -> coq_N * (coq_N * coq_N) **)

  let ggcd a b =
    match a with
    | N0 -> (b, (N0, (Npos Coq_xH)))
    | Npos p ->
      (match b with
       | N0 -> (a, ((Npos Coq_xH), N0))
       | Npos q ->
         let (g, p0) = Pos.ggcd p q in
         let (aa, bb) = p0 in ((Npos g), ((Npos aa), (Npos bb))))

  (** val sqrtrem : coq_N -> coq_N * coq_N **)

  let sqrtrem = function
  | N0 -> (N0, N0)
  | Npos p ->
    let (s, m) = Pos.sqrtrem p in
    (match m with
     | Pos.IsPos r -> ((Npos s), (Npos r))
     | _ -> ((Npos s), N0))

  (** val sqrt : coq_N -> coq_N **)

  let sqrt = function
  | N0 -> N0
  | Npos p -> Npos (Pos.sqrt p)

  (** val coq_lor : coq_N -> coq_N -> coq_N **)

  let coq_lor n m =
    match n with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n
                 | Npos q -> Npos (Pos.coq_lor p q))

  (** val coq_land : coq_N -> coq_N -> coq_N **)

  let coq_land n m =
    match n with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Pos.coq_land p q)

  (** val ldiff : coq_N -> coq_N -> coq_N **)

  let ldiff n m =
    match n with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> n
                 | Npos q -> Pos.ldiff p q)

  (** val coq_lxor : coq_N -> coq_N -> coq_N **)

  let coq_lxor n m =
    match n with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n
                 | Npos q -> Pos.coq_lxor p q)

  (** val shiftl_nat : coq_N -> nat -> coq_N **)

  let rec shiftl_nat a = function
  | O -> a
  | S n0 -> double (shiftl_nat a n0)

  (** val shiftr_nat : coq_N -> nat -> coq_N **)

  let rec shiftr_nat a = function
  | O -> a
  | S n0 -> div2 (shiftr_nat a n0)

  (** val shiftl : coq_N -> coq_N -> coq_N **)

  let shiftl a n =
    match a with
    | N0 -> N0
    | Npos a0 -> Npos (Pos.shiftl a0 n)

  (** val shiftr : coq_N -> coq_N -> coq_N **)

  let shiftr a = function
  | N0 -> a
  | Npos p -> Pos.iter div2 a p

  (** val testbit_nat : coq_N -> nat -> bool **)

  let testbit_nat = function
  | N0 -> (fun _ -> false)
  | Npos p -> Pos.testbit_nat p

  (** val testbit : coq_N -> coq_N -> bool **)

  let testbit a n =
    match a with
    | N0 -> false
    | Npos p -> Pos.testbit p n

  (** val to_nat : coq_N -> nat **)

  let to_nat = function
  | N0 -> O
  | Npos p -> Pos.to_nat p

  (** val of_nat : nat -> coq_N **)

  let of_nat = function
  | O -> N0
  | S n' -> Npos (Pos.of_succ_nat n')

  (** val iter : coq_N -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let iter n f x =
    match n with
    | N0 -> x
    | Npos p -> Pos.iter f x p

  (** val of_uint : Decimal.uint -> coq_N **)

  let of_uint =
    Pos.of_uint

  (** val of_hex_uint : Hexadecimal.uint -> coq_N **)

  let of_hex_uint =
    Pos.of_hex_uint

  (** val of_num_uint : uint -> coq_N **)

  let of_num_uint = function
  | UIntDec d0 -> of_uint d0
  | UIntHex d0 -> of_hex_uint d0

  (** val of_int : Decimal.int -> coq_N option **)

  let of_int d =
    match Decimal.norm d with
    | Decimal.Pos d0 -> Some (Pos.of_uint d0)
    | Decimal.Neg _ -> None

  (** val of_hex_int : Hexadecimal.int -> coq_N option **)

  let of_hex_int d =
    match norm d with
    | Pos d0 -> Some (Pos.of_hex_uint d0)
    | Neg _ -> None

  (** val of_num_int : int -> coq_N option **)

  let of_num_int = function
  | IntDec d0 -> of_int d0
  | IntHex d0 -> of_hex_int d0

  (** val to_uint : coq_N -> Decimal.uint **)

  let to_uint = function
  | N0 -> Decimal.D0 Decimal.Nil
  | Npos p -> Pos.to_uint p

  (** val to_hex_uint : coq_N -> Hexadecimal.uint **)

  let to_hex_uint = function
  | N0 -> D0 Nil
  | Npos p -> Pos.to_hex_uint p

  (** val to_num_uint : coq_N -> uint **)

  let to_num_uint n =
    UIntDec (to_uint n)

  (** val to_int : coq_N -> Decimal.int **)

  let to_int n =
    Decimal.Pos (to_uint n)

  (** val to_hex_int : coq_N -> Hexadecimal.int **)

  let to_hex_int n =
    Pos (to_hex_uint n)

  (** val to_num_int : coq_N -> int **)

  let to_num_int n =
    IntDec (to_int n)

  (** val eq_dec : coq_N -> coq_N -> bool **)

  let eq_dec n m =
    match n with
    | N0 -> (match m with
             | N0 -> true
             | Npos _ -> false)
    | Npos x -> (match m with
                 | N0 -> false
                 | Npos p0 -> Pos.eq_dec x p0)

  (** val discr : coq_N -> positive option **)

  let discr = function
  | N0 -> None
  | Npos p -> Some p

  (** val binary_rect :
      'a1 -> (coq_N -> 'a1 -> 'a1) -> (coq_N -> 'a1 -> 'a1) -> coq_N -> 'a1 **)

  let binary_rect f0 f2 fS2 n =
    let f2' = fun p -> f2 (Npos p) in
    let fS2' = fun p -> fS2 (Npos p) in
    (match n with
     | N0 -> f0
     | Npos p ->
       let rec f = function
       | Coq_xI p1 -> fS2' p1 (f p1)
       | Coq_xO p1 -> f2' p1 (f p1)
       | Coq_xH -> fS2 N0 f0
       in f p)

  (** val binary_rec :
      'a1 -> (coq_N -> 'a1 -> 'a1) -> (coq_N -> 'a1 -> 'a1) -> coq_N -> 'a1 **)

  let binary_rec =
    binary_rect

  (** val peano_rect : 'a1 -> (coq_N -> 'a1 -> 'a1) -> coq_N -> 'a1 **)

  let peano_rect f0 f n =
    let f' = fun p -> f (Npos p) in
    (match n with
     | N0 -> f0
     | Npos p -> Pos.peano_rect (f N0 f0) f' p)

  (** val peano_rec : 'a1 -> (coq_N -> 'a1 -> 'a1) -> coq_N -> 'a1 **)

  let peano_rec =
    peano_rect

  (** val recursion : 'a1 -> (coq_N -> 'a1 -> 'a1) -> coq_N -> 'a1 **)

  let recursion =
    peano_rect

  (** val leb_spec0 : coq_N -> coq_N -> reflect **)

  let leb_spec0 x y =
    iff_reflect (leb x y)

  (** val ltb_spec0 : coq_N -> coq_N -> reflect **)

  let ltb_spec0 x y =
    iff_reflect (ltb x y)

  module Private_OrderTac =
   struct
    module IsTotal =
     struct
     end

    module Tac =
     struct
     end
   end

  module Private_Tac =
   struct
   end

  module Private_Dec =
   struct
    (** val max_case_strong :
        coq_N -> coq_N -> (coq_N -> coq_N -> __ -> 'a1 -> 'a1) -> (__ -> 'a1)
        -> (__ -> 'a1) -> 'a1 **)

    let max_case_strong n m compat hl hr =
      let c = coq_CompSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat n (max n m) __ (hl __)
       | _ -> compat m (max n m) __ (hr __))

    (** val max_case :
        coq_N -> coq_N -> (coq_N -> coq_N -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1
        -> 'a1 **)

    let max_case n m x x0 x1 =
      max_case_strong n m x (fun _ -> x0) (fun _ -> x1)

    (** val max_dec : coq_N -> coq_N -> bool **)

    let max_dec n m =
      max_case n m (fun _ _ _ h0 -> h0) true false

    (** val min_case_strong :
        coq_N -> coq_N -> (coq_N -> coq_N -> __ -> 'a1 -> 'a1) -> (__ -> 'a1)
        -> (__ -> 'a1) -> 'a1 **)

    let min_case_strong n m compat hl hr =
      let c = coq_CompSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat m (min n m) __ (hr __)
       | _ -> compat n (min n m) __ (hl __))

    (** val min_case :
        coq_N -> coq_N -> (coq_N -> coq_N -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1
        -> 'a1 **)

    let min_case n m x x0 x1 =
      min_case_strong n m x (fun _ -> x0) (fun _ -> x1)

    (** val min_dec : coq_N -> coq_N -> bool **)

    let min_dec n m =
      min_case n m (fun _ _ _ h0 -> h0) true false
   end

  (** val max_case_strong :
      coq_N -> coq_N -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let max_case_strong n m x x0 =
    Private_Dec.max_case_strong n m (fun _ _ _ x1 -> x1) x x0

  (** val max_case : coq_N -> coq_N -> 'a1 -> 'a1 -> 'a1 **)

  let max_case n m x x0 =
    max_case_strong n m (fun _ -> x) (fun _ -> x0)

  (** val max_dec : coq_N -> coq_N -> bool **)

  let max_dec =
    Private_Dec.max_dec

  (** val min_case_strong :
      coq_N -> coq_N -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let min_case_strong n m x x0 =
    Private_Dec.min_case_strong n m (fun _ _ _ x1 -> x1) x x0

  (** val min_case : coq_N -> coq_N -> 'a1 -> 'a1 -> 'a1 **)

  let min_case n m x x0 =
    min_case_strong n m (fun _ -> x) (fun _ -> x0)

  (** val min_dec : coq_N -> coq_N -> bool **)

  let min_dec =
    Private_Dec.min_dec

  module Private_NZPow =
   struct
   end

  module Private_NZSqrt =
   struct
   end

  (** val sqrt_up : coq_N -> coq_N **)

  let sqrt_up a =
    match compare N0 a with
    | Lt -> succ (sqrt (pred a))
    | _ -> N0

  (** val log2_up : coq_N -> coq_N **)

  let log2_up a =
    match compare (Npos Coq_xH) a with
    | Lt -> succ (log2 (pred a))
    | _ -> N0

  module Private_NZDiv =
   struct
   end

  (** val lcm : coq_N -> coq_N -> coq_N **)

  let lcm a b =
    mul a (div b (gcd a b))

  (** val eqb_spec : coq_N -> coq_N -> reflect **)

  let eqb_spec x y =
    iff_reflect (eqb x y)

  (** val b2n : bool -> coq_N **)

  let b2n = function
  | true -> Npos Coq_xH
  | false -> N0

  (** val setbit : coq_N -> coq_N -> coq_N **)

  let setbit a n =
    coq_lor a (shiftl (Npos Coq_xH) n)

  (** val clearbit : coq_N -> coq_N -> coq_N **)

  let clearbit a n =
    ldiff a (shiftl (Npos Coq_xH) n)

  (** val ones : coq_N -> coq_N **)

  let ones n =
    pred (shiftl (Npos Coq_xH) n)

  (** val lnot : coq_N -> coq_N -> coq_N **)

  let lnot a n =
    coq_lxor a (ones n)
 end

(** val coq_N_rec_double :
    coq_N -> 'a1 -> (coq_N -> 'a1 -> 'a1) -> (coq_N -> 'a1 -> 'a1) -> 'a1 **)

let coq_N_rec_double a f0 f2 fS2 =
  N.binary_rec f0 f2 fS2 a
