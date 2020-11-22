open Datatypes

type __ = Obj.t

val bool_dec : bool -> bool -> bool

val compare : bool -> bool -> comparison

val eqb : bool -> bool -> bool

val ifb : bool -> bool -> bool -> bool

val orb_true_elim : bool -> bool -> bool

val andb_false_elim : bool -> bool -> bool

type reflect =
| ReflectT
| ReflectF

val reflect_rect : (__ -> 'a1) -> (__ -> 'a1) -> bool -> reflect -> 'a1

val reflect_rec : (__ -> 'a1) -> (__ -> 'a1) -> bool -> reflect -> 'a1

val iff_reflect : bool -> reflect

val reflect_dec : bool -> reflect -> bool

val eqb_spec : bool -> bool -> reflect

module BoolNotations :
 sig
 end
