open Ascii
open Basics
open BinNums
open BinPos
open Compare_dec
open Datatypes
open List0
open Monad
open PeanoNat
open RelDec
open String0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val get_last_digit : nat -> char list **)

let get_last_digit n =
  match Nat.modulo n (S (S (S (S (S (S (S (S (S (S O)))))))))) with
  | O -> '0'::[]
  | S n0 ->
    (match n0 with
     | O -> '1'::[]
     | S n1 ->
       (match n1 with
        | O -> '2'::[]
        | S n2 ->
          (match n2 with
           | O -> '3'::[]
           | S n3 ->
             (match n3 with
              | O -> '4'::[]
              | S n4 ->
                (match n4 with
                 | O -> '5'::[]
                 | S n5 ->
                   (match n5 with
                    | O -> '6'::[]
                    | S n6 ->
                      (match n6 with
                       | O -> '7'::[]
                       | S n7 -> (match n7 with
                                  | O -> '8'::[]
                                  | S _ -> '9'::[]))))))))

(** val string_of_nat_aux_F :
    (char list -> nat -> char list) -> char list -> nat -> char list **)

let string_of_nat_aux_F string_of_nat_aux0 acc n =
  match Nat.div n (S (S (S (S (S (S (S (S (S (S O)))))))))) with
  | O -> append (get_last_digit n) acc
  | S n0 -> string_of_nat_aux0 (append (get_last_digit n) acc) (S n0)

(** val string_of_nat_aux_terminate : char list -> nat -> char list **)

let rec string_of_nat_aux_terminate acc n =
  match Nat.div n (S (S (S (S (S (S (S (S (S (S O)))))))))) with
  | O -> append (get_last_digit n) acc
  | S n0 -> string_of_nat_aux_terminate (append (get_last_digit n) acc) (S n0)

(** val string_of_nat_aux : char list -> nat -> char list **)

let rec string_of_nat_aux acc n =
  match Nat.div n (S (S (S (S (S (S (S (S (S (S O)))))))))) with
  | O -> append (get_last_digit n) acc
  | S n0 -> string_of_nat_aux (append (get_last_digit n) acc) (S n0)

type coq_R_string_of_nat_aux =
| R_string_of_nat_aux_0 of char list * nat
| R_string_of_nat_aux_1 of char list * nat * nat * char list
   * coq_R_string_of_nat_aux

(** val coq_R_string_of_nat_aux_rect :
    (char list -> nat -> __ -> 'a1) -> (char list -> nat -> nat -> __ -> __
    -> char list -> coq_R_string_of_nat_aux -> 'a1 -> 'a1) -> char list ->
    nat -> char list -> coq_R_string_of_nat_aux -> 'a1 **)

let rec coq_R_string_of_nat_aux_rect f f0 _ _ _ = function
| R_string_of_nat_aux_0 (acc, n) -> f acc n __
| R_string_of_nat_aux_1 (acc, n, x, x0, x1) ->
  let acc' = append (get_last_digit n) acc in
  f0 acc n x __ __ x0 x1 (coq_R_string_of_nat_aux_rect f f0 acc' x x0 x1)

(** val coq_R_string_of_nat_aux_rec :
    (char list -> nat -> __ -> 'a1) -> (char list -> nat -> nat -> __ -> __
    -> char list -> coq_R_string_of_nat_aux -> 'a1 -> 'a1) -> char list ->
    nat -> char list -> coq_R_string_of_nat_aux -> 'a1 **)

let rec coq_R_string_of_nat_aux_rec f f0 _ _ _ = function
| R_string_of_nat_aux_0 (acc, n) -> f acc n __
| R_string_of_nat_aux_1 (acc, n, x, x0, x1) ->
  let acc' = append (get_last_digit n) acc in
  f0 acc n x __ __ x0 x1 (coq_R_string_of_nat_aux_rec f f0 acc' x x0 x1)

(** val string_of_nat_aux_rect :
    (char list -> nat -> __ -> 'a1) -> (char list -> nat -> nat -> __ -> __
    -> 'a1 -> 'a1) -> char list -> nat -> 'a1 **)

let rec string_of_nat_aux_rect f f0 acc n =
  let f1 = f0 acc n in
  let f2 = f acc n in
  (match Nat.div n (S (S (S (S (S (S (S (S (S (S O)))))))))) with
   | O -> f2 __
   | S n0 ->
     let f3 = let n' = S n0 in f1 n' __ in
     let f4 = f3 __ in
     let hrec =
       string_of_nat_aux_rect f f0 (append (get_last_digit n) acc) (S n0)
     in
     f4 hrec)

(** val string_of_nat_aux_rec :
    (char list -> nat -> __ -> 'a1) -> (char list -> nat -> nat -> __ -> __
    -> 'a1 -> 'a1) -> char list -> nat -> 'a1 **)

let string_of_nat_aux_rec =
  string_of_nat_aux_rect

(** val coq_R_string_of_nat_aux_correct :
    char list -> nat -> char list -> coq_R_string_of_nat_aux **)

let coq_R_string_of_nat_aux_correct acc n _res =
  string_of_nat_aux_rect (fun y y0 _ _ _ -> R_string_of_nat_aux_0 (y, y0))
    (fun y y0 y1 _ _ y4 _ _ -> R_string_of_nat_aux_1 (y, y0, y1,
    (string_of_nat_aux (append (get_last_digit y0) y) y1),
    (y4 (string_of_nat_aux (append (get_last_digit y0) y) y1) __))) acc n
    _res __

(** val string_of_nat : nat -> char list **)

let string_of_nat =
  string_of_nat_aux []

(** val string_of_Z : coq_Z -> char list **)

let string_of_Z = function
| Z0 -> '0'::[]
| Zpos p -> string_of_nat (Pos.to_nat p)
| Zneg p -> append ('-'::[]) (string_of_nat (Pos.to_nat p))

(** val string_of_nat_bin : nat -> char list **)

let rec string_of_nat_bin = function
| O -> []
| S n0 ->
  (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))))))))))::
    (string_of_nat_bin n0)

(** val monad_fold_right :
    'a1 coq_Monad -> ('a3 -> 'a2 -> 'a1) -> 'a2 list -> 'a3 -> 'a1 **)

let rec monad_fold_right m f l b =
  match l with
  | [] -> ret m b
  | x :: xs -> bind m (monad_fold_right m f xs b) (fun r -> f r x)

(** val monad_app_fst :
    'a1 coq_Monad -> ('a2 -> 'a1) -> ('a2 * 'a3) -> 'a1 **)

let monad_app_fst m f = function
| (x, y) -> bind m (f x) (fun z -> ret m (z, y))

(** val monad_app_snd :
    'a1 coq_Monad -> ('a3 -> 'a1) -> ('a2 * 'a3) -> 'a1 **)

let monad_app_snd m f = function
| (x, y) -> bind m (f y) (fun z -> ret m (x, z))

(** val map_monad : 'a1 coq_Monad -> ('a2 -> 'a1) -> 'a2 list -> 'a1 **)

let rec map_monad m f = function
| [] -> ret m []
| a :: l' ->
  bind m (f a) (fun b ->
    bind m (map_monad m f l') (fun bs -> ret m (b :: bs)))

(** val map_monad_ : 'a1 coq_Monad -> ('a2 -> 'a1) -> 'a2 list -> 'a1 **)

let map_monad_ m f l =
  bind m (map_monad m f l) (fun _ -> ret m ())

(** val map2 : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list **)

let rec map2 f la lb =
  match la with
  | [] -> []
  | a :: la' ->
    (match lb with
     | [] -> []
     | b :: lb' -> (f a b) :: (map2 f la' lb'))

(** val forall2b : ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> bool **)

let rec forall2b f l m =
  match l with
  | [] -> (match m with
           | [] -> true
           | _ :: _ -> false)
  | a :: l' ->
    (match m with
     | [] -> false
     | b :: m' -> (&&) (f a b) (forall2b f l' m'))

(** val coq_Forall_dec : ('a1 -> bool) -> 'a1 list -> bool **)

let rec coq_Forall_dec p_dec = function
| [] -> true
| a :: l' -> if p_dec a then coq_Forall_dec p_dec l' else false

(** val replace : 'a1 list -> nat -> 'a1 -> 'a1 list **)

let rec replace l n a =
  match n with
  | O -> (match l with
          | [] -> []
          | _ :: l' -> a :: l')
  | S n' -> (match l with
             | [] -> []
             | a' :: l' -> a' :: (replace l' n' a))

(** val replicate : 'a1 -> nat -> 'a1 list **)

let rec replicate a = function
| O -> []
| S n' -> a :: (replicate a n')

(** val interval : nat -> nat -> nat list **)

let rec interval n = function
| O -> []
| S j -> if le_lt_dec n j then app (interval n j) (j :: []) else []

(** val trim : 'a1 option list -> 'a1 list **)

let rec trim = function
| [] -> []
| o :: lo' -> (match o with
               | Some a -> a :: (trim lo')
               | None -> [])

(** val nth_f : 'a2 -> ('a1 -> 'a2) -> nat -> 'a1 list -> 'a2 **)

let rec nth_f d f n l =
  match n with
  | O -> (match l with
          | [] -> d
          | a :: _ -> f a)
  | S n' -> (match l with
             | [] -> d
             | _ :: l' -> nth_f d f n' l')

(** val assoc : 'a1 coq_RelDec -> 'a1 -> ('a1 * 'a2) list -> 'a2 option **)

let rec assoc rD a = function
| [] -> None
| p :: l' ->
  let (a', b) = p in if rel_dec rD a a' then Some b else assoc rD a l'

(** val snoc : 'a1 -> 'a1 list -> 'a1 list **)

let snoc a l =
  app l (a :: [])

(** val map_option : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list option **)

let rec map_option f = function
| [] -> Some []
| a :: l' ->
  (match f a with
   | Some b ->
     (match map_option f l' with
      | Some bl -> Some (b :: bl)
      | None -> None)
   | None -> None)

(** val find_map : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 option **)

let rec find_map f = function
| [] -> None
| x :: xs -> (match f x with
              | Some ans -> Some ans
              | None -> find_map f xs)

(** val opt_compose :
    ('a2 -> 'a3) -> ('a1 -> 'a2 option) -> 'a1 -> 'a3 option **)

let opt_compose g f a =
  option_map g (f a)

(** val option_iter : ('a1 -> 'a1 option) -> 'a1 -> nat -> 'a1 option **)

let rec option_iter f a = function
| O -> Some a
| S n' -> (match f a with
           | Some a' -> option_iter f a' n'
           | None -> None)

(** val option_bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option **)

let option_bind m f =
  match m with
  | Some a -> f a
  | None -> None

(** val option_bind2 :
    ('a1 * 'a2) option -> ('a1 -> 'a2 -> 'a3 option) -> 'a3 option **)

let option_bind2 m f =
  match m with
  | Some p -> let (a, b) = p in f a b
  | None -> None

module OptionNotations =
 struct
 end

(** val map_prod :
    ('a1 * 'a2) -> ('a1 -> 'a3) -> ('a2 -> 'a4) -> 'a3 * 'a4 **)

let map_prod p f g =
  ((f (fst p)), (g (snd p)))

(** val flip : ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 -> 'a3 **)

let flip =
  flip

(** val comp : ('a2 -> 'a3) -> ('a1 -> 'a2) -> 'a1 -> 'a3 **)

let comp =
  compose

(** val map_snd : ('a2 -> 'a3) -> ('a1 * 'a2) list -> ('a1 * 'a3) list **)

let map_snd f =
  map (fun ab -> let (a, b) = ab in (a, (f b)))
