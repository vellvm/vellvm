open Datatypes
open Nat
open Specif

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module ListNotations =
 struct
 end

(** val hd : 'a1 -> 'a1 list -> 'a1 **)

let hd default = function
| [] -> default
| x :: _ -> x

(** val hd_error : 'a1 list -> 'a1 option **)

let hd_error = function
| [] -> None
| x :: _ -> Some x

(** val tl : 'a1 list -> 'a1 list **)

let tl = function
| [] -> []
| _ :: m -> m

(** val destruct_list : 'a1 list -> ('a1, 'a1 list) sigT option **)

let destruct_list = function
| [] -> None
| y :: l0 -> Some (Coq_existT (y, l0))

(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec h a = function
| [] -> false
| y :: l0 -> let s = h y a in if s then true else in_dec h a l0

(** val nth : nat -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default =
  match n with
  | O -> (match l with
          | [] -> default
          | x :: _ -> x)
  | S m -> (match l with
            | [] -> default
            | _ :: t -> nth m t default)

(** val nth_ok : nat -> 'a1 list -> 'a1 -> bool **)

let rec nth_ok n l default =
  match n with
  | O -> (match l with
          | [] -> false
          | _ :: _ -> true)
  | S m -> (match l with
            | [] -> false
            | _ :: t -> nth_ok m t default)

(** val nth_in_or_default : nat -> 'a1 list -> 'a1 -> bool **)

let rec nth_in_or_default n l d =
  match l with
  | [] -> false
  | _ :: l0 -> (match n with
                | O -> true
                | S n0 -> nth_in_or_default n0 l0 d)

(** val nth_error : 'a1 list -> nat -> 'a1 option **)

let rec nth_error l = function
| O -> (match l with
        | [] -> None
        | x :: _ -> Some x)
| S n0 -> (match l with
           | [] -> None
           | _ :: l0 -> nth_error l0 n0)

(** val nth_default : 'a1 -> 'a1 list -> nat -> 'a1 **)

let nth_default default l n =
  match nth_error l n with
  | Some x -> x
  | None -> default

(** val last : 'a1 list -> 'a1 -> 'a1 **)

let rec last l d =
  match l with
  | [] -> d
  | a :: l0 -> (match l0 with
                | [] -> a
                | _ :: _ -> last l0 d)

(** val removelast : 'a1 list -> 'a1 list **)

let rec removelast = function
| [] -> []
| a :: l0 -> (match l0 with
              | [] -> []
              | _ :: _ -> a :: (removelast l0))

(** val exists_last : 'a1 list -> ('a1 list, 'a1) sigT **)

let rec exists_last = function
| [] -> assert false (* absurd case *)
| y :: l0 ->
  (match l0 with
   | [] -> Coq_existT ([], y)
   | _ :: _ ->
     let s = exists_last l0 in
     let Coq_existT (l', s0) = s in Coq_existT ((y :: l'), s0))

(** val remove : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list **)

let rec remove eq_dec x = function
| [] -> []
| y :: tl0 ->
  if eq_dec x y then remove eq_dec x tl0 else y :: (remove eq_dec x tl0)

(** val count_occ : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 -> nat **)

let rec count_occ eq_dec l x =
  match l with
  | [] -> O
  | y :: tl0 ->
    let n = count_occ eq_dec tl0 x in if eq_dec y x then S n else n

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x :: l' -> app (rev l') (x :: [])

(** val rev_append : 'a1 list -> 'a1 list -> 'a1 list **)

let rec rev_append l l' =
  match l with
  | [] -> l'
  | a :: l0 -> rev_append l0 (a :: l')

(** val rev' : 'a1 list -> 'a1 list **)

let rev' l =
  rev_append l []

(** val concat : 'a1 list list -> 'a1 list **)

let rec concat = function
| [] -> []
| x :: l0 -> app x (concat l0)

(** val list_eq_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_eq_dec eq_dec l l' =
  match l with
  | [] -> (match l' with
           | [] -> true
           | _ :: _ -> false)
  | y :: l0 ->
    (match l' with
     | [] -> false
     | a0 :: l1 -> if eq_dec y a0 then list_eq_dec eq_dec l0 l1 else false)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| [] -> []
| x :: t -> app (f x) (flat_map f t)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: t -> fold_left f t (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t -> f b (fold_right f a0 t)

(** val list_power : 'a1 list -> 'a2 list -> ('a1 * 'a2) list list **)

let rec list_power l l' =
  match l with
  | [] -> [] :: []
  | x :: t ->
    flat_map (fun f -> map (fun y -> (x, y) :: f) l') (list_power t l')

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a :: l0 -> (||) (f a) (existsb f l0)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a :: l0 -> (&&) (f a) (forallb f l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

(** val find : ('a1 -> bool) -> 'a1 list -> 'a1 option **)

let rec find f = function
| [] -> None
| x :: tl0 -> if f x then Some x else find f tl0

(** val partition : ('a1 -> bool) -> 'a1 list -> 'a1 list * 'a1 list **)

let rec partition f = function
| [] -> ([], [])
| x :: tl0 ->
  let (g, d) = partition f tl0 in if f x then ((x :: g), d) else (g, (x :: d))

(** val remove' : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list **)

let remove' eq_dec x =
  filter (fun y -> if eq_dec x y then false else true)

(** val count_occ' : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 -> nat **)

let count_occ' eq_dec l x =
  length (filter (fun y -> if eq_dec y x then true else false) l)

(** val split : ('a1 * 'a2) list -> 'a1 list * 'a2 list **)

let rec split = function
| [] -> ([], [])
| p :: tl0 ->
  let (x, y) = p in
  let (left, right) = split tl0 in ((x :: left), (y :: right))

(** val combine : 'a1 list -> 'a2 list -> ('a1 * 'a2) list **)

let rec combine l l' =
  match l with
  | [] -> []
  | x :: tl0 ->
    (match l' with
     | [] -> []
     | y :: tl' -> (x, y) :: (combine tl0 tl'))

(** val list_prod : 'a1 list -> 'a2 list -> ('a1 * 'a2) list **)

let rec list_prod l l' =
  match l with
  | [] -> []
  | x :: t -> app (map (fun y -> (x, y)) l') (list_prod t l')

(** val firstn : nat -> 'a1 list -> 'a1 list **)

let rec firstn n l =
  match n with
  | O -> []
  | S n0 -> (match l with
             | [] -> []
             | a :: l0 -> a :: (firstn n0 l0))

(** val skipn : nat -> 'a1 list -> 'a1 list **)

let rec skipn n l =
  match n with
  | O -> l
  | S n0 -> (match l with
             | [] -> []
             | _ :: l0 -> skipn n0 l0)

(** val nodup : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec nodup decA = function
| [] -> []
| x :: xs -> if in_dec decA x xs then nodup decA xs else x :: (nodup decA xs)

(** val seq : nat -> nat -> nat list **)

let rec seq start = function
| O -> []
| S len0 -> start :: (seq (S start) len0)

(** val coq_Exists_dec : 'a1 list -> ('a1 -> bool) -> bool **)

let rec coq_Exists_dec l pdec =
  match l with
  | [] -> false
  | y :: l0 -> if coq_Exists_dec l0 pdec then true else pdec y

(** val coq_Forall_rect :
    'a2 -> ('a1 -> 'a1 list -> __ -> 'a2) -> 'a1 list -> 'a2 **)

let coq_Forall_rect h h' = function
| [] -> h
| y :: l0 -> h' y l0 __

(** val coq_Forall_dec : ('a1 -> bool) -> 'a1 list -> bool **)

let rec coq_Forall_dec pdec = function
| [] -> true
| y :: l0 -> if coq_Forall_dec pdec l0 then pdec y else false

(** val coq_Forall_Exists_dec : ('a1 -> bool) -> 'a1 list -> bool **)

let coq_Forall_Exists_dec =
  coq_Forall_dec

(** val repeat : 'a1 -> nat -> 'a1 list **)

let rec repeat x = function
| O -> []
| S k -> x :: (repeat x k)

(** val list_sum : nat list -> nat **)

let list_sum l =
  fold_right add O l

(** val list_max : nat list -> nat **)

let list_max l =
  fold_right max O l
