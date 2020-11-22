
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val sumbool_of_bool : bool -> bool **)

let sumbool_of_bool = function
| true -> true
| false -> false

(** val bool_eq_rec : bool -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

let bool_eq_rec b x x0 =
  if b then x __ else x0 __

(** val sumbool_and : bool -> bool -> bool **)

let sumbool_and h1 h2 =
  if h1 then h2 else false

(** val sumbool_or : bool -> bool -> bool **)

let sumbool_or h1 h2 =
  if h1 then true else h2

(** val sumbool_not : bool -> bool **)

let sumbool_not = function
| true -> false
| false -> true

(** val bool_of_sumbool : bool -> bool **)

let bool_of_sumbool = function
| true -> true
| false -> false
