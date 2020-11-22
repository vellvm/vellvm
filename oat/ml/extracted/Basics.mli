
val compose : ('a2 -> 'a3) -> ('a1 -> 'a2) -> 'a1 -> 'a3

type ('a, 'b) arrow = 'a -> 'b

val const : 'a1 -> 'a2 -> 'a1

val flip : ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 -> 'a3

val apply : ('a1 -> 'a2) -> 'a1 -> 'a2
