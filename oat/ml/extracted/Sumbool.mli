
type __ = Obj.t

val sumbool_of_bool : bool -> bool

val bool_eq_rec : bool -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

val sumbool_and : bool -> bool -> bool

val sumbool_or : bool -> bool -> bool

val sumbool_not : bool -> bool

val bool_of_sumbool : bool -> bool
