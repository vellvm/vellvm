
(** val compose : ('a2 -> 'a3) -> ('a1 -> 'a2) -> 'a1 -> 'a3 **)

let compose g f x =
  g (f x)

type ('a, 'b) arrow = 'a -> 'b

(** val const : 'a1 -> 'a2 -> 'a1 **)

let const a _ =
  a

(** val flip : ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 -> 'a3 **)

let flip f x y =
  f y x

(** val apply : ('a1 -> 'a2) -> 'a1 -> 'a2 **)

let apply f =
  f
