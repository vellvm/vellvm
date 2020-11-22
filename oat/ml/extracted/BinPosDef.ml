open BinNums
open Datatypes
open Decimal
open Hexadecimal
open Nat
open Numeral

module Pos =
 struct
  type t = positive

  (** val succ : positive -> positive **)

  let rec succ = function
  | Coq_xI p -> Coq_xO (succ p)
  | Coq_xO p -> Coq_xI p
  | Coq_xH -> Coq_xO Coq_xH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | Coq_xI p ->
      (match y with
       | Coq_xI q -> Coq_xO (add_carry p q)
       | Coq_xO q -> Coq_xI (add p q)
       | Coq_xH -> Coq_xO (succ p))
    | Coq_xO p ->
      (match y with
       | Coq_xI q -> Coq_xI (add p q)
       | Coq_xO q -> Coq_xO (add p q)
       | Coq_xH -> Coq_xI p)
    | Coq_xH ->
      (match y with
       | Coq_xI q -> Coq_xO (succ q)
       | Coq_xO q -> Coq_xI q
       | Coq_xH -> Coq_xO Coq_xH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | Coq_xI p ->
      (match y with
       | Coq_xI q -> Coq_xI (add_carry p q)
       | Coq_xO q -> Coq_xO (add_carry p q)
       | Coq_xH -> Coq_xI (succ p))
    | Coq_xO p ->
      (match y with
       | Coq_xI q -> Coq_xO (add_carry p q)
       | Coq_xO q -> Coq_xI (add p q)
       | Coq_xH -> Coq_xO (succ p))
    | Coq_xH ->
      (match y with
       | Coq_xI q -> Coq_xI (succ q)
       | Coq_xO q -> Coq_xO (succ q)
       | Coq_xH -> Coq_xI Coq_xH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | Coq_xI p -> Coq_xI (Coq_xO p)
  | Coq_xO p -> Coq_xI (pred_double p)
  | Coq_xH -> Coq_xH

  (** val pred : positive -> positive **)

  let pred = function
  | Coq_xI p -> Coq_xO p
  | Coq_xO p -> pred_double p
  | Coq_xH -> Coq_xH

  (** val pred_N : positive -> coq_N **)

  let pred_N = function
  | Coq_xI p -> Npos (Coq_xO p)
  | Coq_xO p -> Npos (pred_double p)
  | Coq_xH -> N0

  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)

  let mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1

  (** val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)

  let mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos Coq_xH
  | IsPos p -> IsPos (Coq_xI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (Coq_xO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | Coq_xI p -> IsPos (Coq_xO (Coq_xO p))
  | Coq_xO p -> IsPos (Coq_xO (pred_double p))
  | Coq_xH -> IsNul

  (** val pred_mask : mask -> mask **)

  let pred_mask = function
  | IsPos q -> (match q with
                | Coq_xH -> IsNul
                | _ -> IsPos (pred q))
  | _ -> IsNeg

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | Coq_xI p ->
      (match y with
       | Coq_xI q -> double_mask (sub_mask p q)
       | Coq_xO q -> succ_double_mask (sub_mask p q)
       | Coq_xH -> IsPos (Coq_xO p))
    | Coq_xO p ->
      (match y with
       | Coq_xI q -> succ_double_mask (sub_mask_carry p q)
       | Coq_xO q -> double_mask (sub_mask p q)
       | Coq_xH -> IsPos (pred_double p))
    | Coq_xH -> (match y with
                 | Coq_xH -> IsNul
                 | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | Coq_xI p ->
      (match y with
       | Coq_xI q -> succ_double_mask (sub_mask_carry p q)
       | Coq_xO q -> double_mask (sub_mask p q)
       | Coq_xH -> IsPos (pred_double p))
    | Coq_xO p ->
      (match y with
       | Coq_xI q -> double_mask (sub_mask_carry p q)
       | Coq_xO q -> succ_double_mask (sub_mask_carry p q)
       | Coq_xH -> double_pred_mask p)
    | Coq_xH -> IsNeg

  (** val sub : positive -> positive -> positive **)

  let sub x y =
    match sub_mask x y with
    | IsPos z -> z
    | _ -> Coq_xH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | Coq_xI p -> add y (Coq_xO (mul p y))
    | Coq_xO p -> Coq_xO (mul p y)
    | Coq_xH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | Coq_xI n' -> f (iter f (iter f x n') n')
  | Coq_xO n' -> iter f (iter f x n') n'
  | Coq_xH -> f x

  (** val pow : positive -> positive -> positive **)

  let pow x =
    iter (mul x) Coq_xH

  (** val square : positive -> positive **)

  let rec square = function
  | Coq_xI p0 -> Coq_xI (Coq_xO (add (square p0) p0))
  | Coq_xO p0 -> Coq_xO (Coq_xO (square p0))
  | Coq_xH -> Coq_xH

  (** val div2 : positive -> positive **)

  let div2 = function
  | Coq_xI p0 -> p0
  | Coq_xO p0 -> p0
  | Coq_xH -> Coq_xH

  (** val div2_up : positive -> positive **)

  let div2_up = function
  | Coq_xI p0 -> succ p0
  | Coq_xO p0 -> p0
  | Coq_xH -> Coq_xH

  (** val size_nat : positive -> nat **)

  let rec size_nat = function
  | Coq_xI p0 -> S (size_nat p0)
  | Coq_xO p0 -> S (size_nat p0)
  | Coq_xH -> S O

  (** val size : positive -> positive **)

  let rec size = function
  | Coq_xI p0 -> succ (size p0)
  | Coq_xO p0 -> succ (size p0)
  | Coq_xH -> Coq_xH

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | Coq_xI p ->
      (match y with
       | Coq_xI q -> compare_cont r p q
       | Coq_xO q -> compare_cont Gt p q
       | Coq_xH -> Gt)
    | Coq_xO p ->
      (match y with
       | Coq_xI q -> compare_cont Lt p q
       | Coq_xO q -> compare_cont r p q
       | Coq_xH -> Gt)
    | Coq_xH -> (match y with
                 | Coq_xH -> r
                 | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val min : positive -> positive -> positive **)

  let min p p' =
    match compare p p' with
    | Gt -> p'
    | _ -> p

  (** val max : positive -> positive -> positive **)

  let max p p' =
    match compare p p' with
    | Gt -> p
    | _ -> p'

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | Coq_xI p0 -> (match q with
                    | Coq_xI q0 -> eqb p0 q0
                    | _ -> false)
    | Coq_xO p0 -> (match q with
                    | Coq_xO q0 -> eqb p0 q0
                    | _ -> false)
    | Coq_xH -> (match q with
                 | Coq_xH -> true
                 | _ -> false)

  (** val leb : positive -> positive -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : positive -> positive -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val sqrtrem_step :
      (positive -> positive) -> (positive -> positive) -> (positive * mask)
      -> positive * mask **)

  let sqrtrem_step f g = function
  | (s, y) ->
    (match y with
     | IsPos r ->
       let s' = Coq_xI (Coq_xO s) in
       let r' = g (f r) in
       if leb s' r'
       then ((Coq_xI s), (sub_mask r' s'))
       else ((Coq_xO s), (IsPos r'))
     | _ -> ((Coq_xO s), (sub_mask (g (f Coq_xH)) (Coq_xO (Coq_xO Coq_xH)))))

  (** val sqrtrem : positive -> positive * mask **)

  let rec sqrtrem = function
  | Coq_xI p0 ->
    (match p0 with
     | Coq_xI p1 ->
       sqrtrem_step (fun x -> Coq_xI x) (fun x -> Coq_xI x) (sqrtrem p1)
     | Coq_xO p1 ->
       sqrtrem_step (fun x -> Coq_xO x) (fun x -> Coq_xI x) (sqrtrem p1)
     | Coq_xH -> (Coq_xH, (IsPos (Coq_xO Coq_xH))))
  | Coq_xO p0 ->
    (match p0 with
     | Coq_xI p1 ->
       sqrtrem_step (fun x -> Coq_xI x) (fun x -> Coq_xO x) (sqrtrem p1)
     | Coq_xO p1 ->
       sqrtrem_step (fun x -> Coq_xO x) (fun x -> Coq_xO x) (sqrtrem p1)
     | Coq_xH -> (Coq_xH, (IsPos Coq_xH)))
  | Coq_xH -> (Coq_xH, IsNul)

  (** val sqrt : positive -> positive **)

  let sqrt p =
    fst (sqrtrem p)

  (** val gcdn : nat -> positive -> positive -> positive **)

  let rec gcdn n a b =
    match n with
    | O -> Coq_xH
    | S n0 ->
      (match a with
       | Coq_xI a' ->
         (match b with
          | Coq_xI b' ->
            (match compare a' b' with
             | Eq -> a
             | Lt -> gcdn n0 (sub b' a') a
             | Gt -> gcdn n0 (sub a' b') b)
          | Coq_xO b0 -> gcdn n0 a b0
          | Coq_xH -> Coq_xH)
       | Coq_xO a0 ->
         (match b with
          | Coq_xI _ -> gcdn n0 a0 b
          | Coq_xO b0 -> Coq_xO (gcdn n0 a0 b0)
          | Coq_xH -> Coq_xH)
       | Coq_xH -> Coq_xH)

  (** val gcd : positive -> positive -> positive **)

  let gcd a b =
    gcdn (Nat.add (size_nat a) (size_nat b)) a b

  (** val ggcdn :
      nat -> positive -> positive -> positive * (positive * positive) **)

  let rec ggcdn n a b =
    match n with
    | O -> (Coq_xH, (a, b))
    | S n0 ->
      (match a with
       | Coq_xI a' ->
         (match b with
          | Coq_xI b' ->
            (match compare a' b' with
             | Eq -> (a, (Coq_xH, Coq_xH))
             | Lt ->
               let (g, p) = ggcdn n0 (sub b' a') a in
               let (ba, aa) = p in (g, (aa, (add aa (Coq_xO ba))))
             | Gt ->
               let (g, p) = ggcdn n0 (sub a' b') b in
               let (ab, bb) = p in (g, ((add bb (Coq_xO ab)), bb)))
          | Coq_xO b0 ->
            let (g, p) = ggcdn n0 a b0 in
            let (aa, bb) = p in (g, (aa, (Coq_xO bb)))
          | Coq_xH -> (Coq_xH, (a, Coq_xH)))
       | Coq_xO a0 ->
         (match b with
          | Coq_xI _ ->
            let (g, p) = ggcdn n0 a0 b in
            let (aa, bb) = p in (g, ((Coq_xO aa), bb))
          | Coq_xO b0 -> let (g, p) = ggcdn n0 a0 b0 in ((Coq_xO g), p)
          | Coq_xH -> (Coq_xH, (a, Coq_xH)))
       | Coq_xH -> (Coq_xH, (Coq_xH, b)))

  (** val ggcd : positive -> positive -> positive * (positive * positive) **)

  let ggcd a b =
    ggcdn (Nat.add (size_nat a) (size_nat b)) a b

  (** val coq_Nsucc_double : coq_N -> coq_N **)

  let coq_Nsucc_double = function
  | N0 -> Npos Coq_xH
  | Npos p -> Npos (Coq_xI p)

  (** val coq_Ndouble : coq_N -> coq_N **)

  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (Coq_xO p)

  (** val coq_lor : positive -> positive -> positive **)

  let rec coq_lor p q =
    match p with
    | Coq_xI p0 ->
      (match q with
       | Coq_xI q0 -> Coq_xI (coq_lor p0 q0)
       | Coq_xO q0 -> Coq_xI (coq_lor p0 q0)
       | Coq_xH -> p)
    | Coq_xO p0 ->
      (match q with
       | Coq_xI q0 -> Coq_xI (coq_lor p0 q0)
       | Coq_xO q0 -> Coq_xO (coq_lor p0 q0)
       | Coq_xH -> Coq_xI p0)
    | Coq_xH -> (match q with
                 | Coq_xO q0 -> Coq_xI q0
                 | _ -> q)

  (** val coq_land : positive -> positive -> coq_N **)

  let rec coq_land p q =
    match p with
    | Coq_xI p0 ->
      (match q with
       | Coq_xI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | Coq_xO q0 -> coq_Ndouble (coq_land p0 q0)
       | Coq_xH -> Npos Coq_xH)
    | Coq_xO p0 ->
      (match q with
       | Coq_xI q0 -> coq_Ndouble (coq_land p0 q0)
       | Coq_xO q0 -> coq_Ndouble (coq_land p0 q0)
       | Coq_xH -> N0)
    | Coq_xH -> (match q with
                 | Coq_xO _ -> N0
                 | _ -> Npos Coq_xH)

  (** val ldiff : positive -> positive -> coq_N **)

  let rec ldiff p q =
    match p with
    | Coq_xI p0 ->
      (match q with
       | Coq_xI q0 -> coq_Ndouble (ldiff p0 q0)
       | Coq_xO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | Coq_xH -> Npos (Coq_xO p0))
    | Coq_xO p0 ->
      (match q with
       | Coq_xI q0 -> coq_Ndouble (ldiff p0 q0)
       | Coq_xO q0 -> coq_Ndouble (ldiff p0 q0)
       | Coq_xH -> Npos p)
    | Coq_xH -> (match q with
                 | Coq_xO _ -> Npos Coq_xH
                 | _ -> N0)

  (** val coq_lxor : positive -> positive -> coq_N **)

  let rec coq_lxor p q =
    match p with
    | Coq_xI p0 ->
      (match q with
       | Coq_xI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | Coq_xO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | Coq_xH -> Npos (Coq_xO p0))
    | Coq_xO p0 ->
      (match q with
       | Coq_xI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | Coq_xO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | Coq_xH -> Npos (Coq_xI p0))
    | Coq_xH ->
      (match q with
       | Coq_xI q0 -> Npos (Coq_xO q0)
       | Coq_xO q0 -> Npos (Coq_xI q0)
       | Coq_xH -> N0)

  (** val shiftl_nat : positive -> nat -> positive **)

  let rec shiftl_nat p = function
  | O -> p
  | S n0 -> Coq_xO (shiftl_nat p n0)

  (** val shiftr_nat : positive -> nat -> positive **)

  let rec shiftr_nat p = function
  | O -> p
  | S n0 -> div2 (shiftr_nat p n0)

  (** val shiftl : positive -> coq_N -> positive **)

  let shiftl p = function
  | N0 -> p
  | Npos n0 -> iter (fun x -> Coq_xO x) p n0

  (** val shiftr : positive -> coq_N -> positive **)

  let shiftr p = function
  | N0 -> p
  | Npos n0 -> iter div2 p n0

  (** val testbit_nat : positive -> nat -> bool **)

  let rec testbit_nat p n =
    match p with
    | Coq_xI p0 -> (match n with
                    | O -> true
                    | S n' -> testbit_nat p0 n')
    | Coq_xO p0 -> (match n with
                    | O -> false
                    | S n' -> testbit_nat p0 n')
    | Coq_xH -> (match n with
                 | O -> true
                 | S _ -> false)

  (** val testbit : positive -> coq_N -> bool **)

  let rec testbit p n =
    match p with
    | Coq_xI p0 ->
      (match n with
       | N0 -> true
       | Npos n0 -> testbit p0 (pred_N n0))
    | Coq_xO p0 ->
      (match n with
       | N0 -> false
       | Npos n0 -> testbit p0 (pred_N n0))
    | Coq_xH -> (match n with
                 | N0 -> true
                 | Npos _ -> false)

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | Coq_xI p0 -> op a (iter_op op p0 (op a a))
    | Coq_xO p0 -> iter_op op p0 (op a a)
    | Coq_xH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Nat.add x (S O)

  (** val of_nat : nat -> positive **)

  let rec of_nat = function
  | O -> Coq_xH
  | S x -> (match x with
            | O -> Coq_xH
            | S _ -> succ (of_nat x))

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> Coq_xH
  | S x -> succ (of_succ_nat x)

  (** val of_uint_acc : Decimal.uint -> positive -> positive **)

  let rec of_uint_acc d acc =
    match d with
    | Decimal.Nil -> acc
    | Decimal.D0 l ->
      of_uint_acc l (mul (Coq_xO (Coq_xI (Coq_xO Coq_xH))) acc)
    | Decimal.D1 l ->
      of_uint_acc l (add Coq_xH (mul (Coq_xO (Coq_xI (Coq_xO Coq_xH))) acc))
    | Decimal.D2 l ->
      of_uint_acc l
        (add (Coq_xO Coq_xH) (mul (Coq_xO (Coq_xI (Coq_xO Coq_xH))) acc))
    | Decimal.D3 l ->
      of_uint_acc l
        (add (Coq_xI Coq_xH) (mul (Coq_xO (Coq_xI (Coq_xO Coq_xH))) acc))
    | Decimal.D4 l ->
      of_uint_acc l
        (add (Coq_xO (Coq_xO Coq_xH))
          (mul (Coq_xO (Coq_xI (Coq_xO Coq_xH))) acc))
    | Decimal.D5 l ->
      of_uint_acc l
        (add (Coq_xI (Coq_xO Coq_xH))
          (mul (Coq_xO (Coq_xI (Coq_xO Coq_xH))) acc))
    | Decimal.D6 l ->
      of_uint_acc l
        (add (Coq_xO (Coq_xI Coq_xH))
          (mul (Coq_xO (Coq_xI (Coq_xO Coq_xH))) acc))
    | Decimal.D7 l ->
      of_uint_acc l
        (add (Coq_xI (Coq_xI Coq_xH))
          (mul (Coq_xO (Coq_xI (Coq_xO Coq_xH))) acc))
    | Decimal.D8 l ->
      of_uint_acc l
        (add (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
          (mul (Coq_xO (Coq_xI (Coq_xO Coq_xH))) acc))
    | Decimal.D9 l ->
      of_uint_acc l
        (add (Coq_xI (Coq_xO (Coq_xO Coq_xH)))
          (mul (Coq_xO (Coq_xI (Coq_xO Coq_xH))) acc))

  (** val of_uint : Decimal.uint -> coq_N **)

  let rec of_uint = function
  | Decimal.Nil -> N0
  | Decimal.D0 l -> of_uint l
  | Decimal.D1 l -> Npos (of_uint_acc l Coq_xH)
  | Decimal.D2 l -> Npos (of_uint_acc l (Coq_xO Coq_xH))
  | Decimal.D3 l -> Npos (of_uint_acc l (Coq_xI Coq_xH))
  | Decimal.D4 l -> Npos (of_uint_acc l (Coq_xO (Coq_xO Coq_xH)))
  | Decimal.D5 l -> Npos (of_uint_acc l (Coq_xI (Coq_xO Coq_xH)))
  | Decimal.D6 l -> Npos (of_uint_acc l (Coq_xO (Coq_xI Coq_xH)))
  | Decimal.D7 l -> Npos (of_uint_acc l (Coq_xI (Coq_xI Coq_xH)))
  | Decimal.D8 l -> Npos (of_uint_acc l (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
  | Decimal.D9 l -> Npos (of_uint_acc l (Coq_xI (Coq_xO (Coq_xO Coq_xH))))

  (** val of_hex_uint_acc : Hexadecimal.uint -> positive -> positive **)

  let rec of_hex_uint_acc d acc =
    match d with
    | Nil -> acc
    | D0 l ->
      of_hex_uint_acc l (mul (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) acc)
    | D1 l ->
      of_hex_uint_acc l
        (add Coq_xH (mul (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) acc))
    | D2 l ->
      of_hex_uint_acc l
        (add (Coq_xO Coq_xH)
          (mul (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) acc))
    | D3 l ->
      of_hex_uint_acc l
        (add (Coq_xI Coq_xH)
          (mul (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) acc))
    | D4 l ->
      of_hex_uint_acc l
        (add (Coq_xO (Coq_xO Coq_xH))
          (mul (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) acc))
    | D5 l ->
      of_hex_uint_acc l
        (add (Coq_xI (Coq_xO Coq_xH))
          (mul (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) acc))
    | D6 l ->
      of_hex_uint_acc l
        (add (Coq_xO (Coq_xI Coq_xH))
          (mul (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) acc))
    | D7 l ->
      of_hex_uint_acc l
        (add (Coq_xI (Coq_xI Coq_xH))
          (mul (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) acc))
    | D8 l ->
      of_hex_uint_acc l
        (add (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
          (mul (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) acc))
    | D9 l ->
      of_hex_uint_acc l
        (add (Coq_xI (Coq_xO (Coq_xO Coq_xH)))
          (mul (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) acc))
    | Da l ->
      of_hex_uint_acc l
        (add (Coq_xO (Coq_xI (Coq_xO Coq_xH)))
          (mul (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) acc))
    | Db l ->
      of_hex_uint_acc l
        (add (Coq_xI (Coq_xI (Coq_xO Coq_xH)))
          (mul (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) acc))
    | Dc l ->
      of_hex_uint_acc l
        (add (Coq_xO (Coq_xO (Coq_xI Coq_xH)))
          (mul (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) acc))
    | Dd l ->
      of_hex_uint_acc l
        (add (Coq_xI (Coq_xO (Coq_xI Coq_xH)))
          (mul (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) acc))
    | De l ->
      of_hex_uint_acc l
        (add (Coq_xO (Coq_xI (Coq_xI Coq_xH)))
          (mul (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) acc))
    | Df l ->
      of_hex_uint_acc l
        (add (Coq_xI (Coq_xI (Coq_xI Coq_xH)))
          (mul (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))) acc))

  (** val of_hex_uint : Hexadecimal.uint -> coq_N **)

  let rec of_hex_uint = function
  | Nil -> N0
  | D0 l -> of_hex_uint l
  | D1 l -> Npos (of_hex_uint_acc l Coq_xH)
  | D2 l -> Npos (of_hex_uint_acc l (Coq_xO Coq_xH))
  | D3 l -> Npos (of_hex_uint_acc l (Coq_xI Coq_xH))
  | D4 l -> Npos (of_hex_uint_acc l (Coq_xO (Coq_xO Coq_xH)))
  | D5 l -> Npos (of_hex_uint_acc l (Coq_xI (Coq_xO Coq_xH)))
  | D6 l -> Npos (of_hex_uint_acc l (Coq_xO (Coq_xI Coq_xH)))
  | D7 l -> Npos (of_hex_uint_acc l (Coq_xI (Coq_xI Coq_xH)))
  | D8 l -> Npos (of_hex_uint_acc l (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
  | D9 l -> Npos (of_hex_uint_acc l (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
  | Da l -> Npos (of_hex_uint_acc l (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
  | Db l -> Npos (of_hex_uint_acc l (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
  | Dc l -> Npos (of_hex_uint_acc l (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
  | Dd l -> Npos (of_hex_uint_acc l (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
  | De l -> Npos (of_hex_uint_acc l (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
  | Df l -> Npos (of_hex_uint_acc l (Coq_xI (Coq_xI (Coq_xI Coq_xH))))

  (** val of_num_uint : uint -> coq_N **)

  let of_num_uint = function
  | UIntDec d0 -> of_uint d0
  | UIntHex d0 -> of_hex_uint d0

  (** val of_int : Decimal.int -> positive option **)

  let of_int = function
  | Decimal.Pos d0 -> (match of_uint d0 with
                       | N0 -> None
                       | Npos p -> Some p)
  | Decimal.Neg _ -> None

  (** val of_hex_int : Hexadecimal.int -> positive option **)

  let of_hex_int = function
  | Pos d0 -> (match of_hex_uint d0 with
               | N0 -> None
               | Npos p -> Some p)
  | Neg _ -> None

  (** val of_num_int : int -> positive option **)

  let of_num_int = function
  | IntDec d0 -> of_int d0
  | IntHex d0 -> of_hex_int d0

  (** val to_little_uint : positive -> Decimal.uint **)

  let rec to_little_uint = function
  | Coq_xI p0 -> Decimal.Little.succ_double (to_little_uint p0)
  | Coq_xO p0 -> Decimal.Little.double (to_little_uint p0)
  | Coq_xH -> Decimal.D1 Decimal.Nil

  (** val to_uint : positive -> Decimal.uint **)

  let to_uint p =
    Decimal.rev (to_little_uint p)

  (** val to_little_hex_uint : positive -> Hexadecimal.uint **)

  let rec to_little_hex_uint = function
  | Coq_xI p0 -> Little.succ_double (to_little_hex_uint p0)
  | Coq_xO p0 -> Little.double (to_little_hex_uint p0)
  | Coq_xH -> D1 Nil

  (** val to_hex_uint : positive -> Hexadecimal.uint **)

  let to_hex_uint p =
    rev (to_little_hex_uint p)

  (** val to_num_uint : positive -> uint **)

  let to_num_uint p =
    UIntDec (to_uint p)

  (** val to_int : positive -> Decimal.int **)

  let to_int n =
    Decimal.Pos (to_uint n)

  (** val to_hex_int : positive -> Hexadecimal.int **)

  let to_hex_int p =
    Pos (to_hex_uint p)

  (** val to_num_int : positive -> int **)

  let to_num_int n =
    IntDec (to_int n)
 end
