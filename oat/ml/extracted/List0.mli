open Datatypes
open Nat
open Specif

type __ = Obj.t

module ListNotations :
 sig
 end

val hd : 'a1 -> 'a1 list -> 'a1

val hd_error : 'a1 list -> 'a1 option

val tl : 'a1 list -> 'a1 list

val destruct_list : 'a1 list -> ('a1, 'a1 list) sigT option

val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool

val nth : nat -> 'a1 list -> 'a1 -> 'a1

val nth_ok : nat -> 'a1 list -> 'a1 -> bool

val nth_in_or_default : nat -> 'a1 list -> 'a1 -> bool

val nth_error : 'a1 list -> nat -> 'a1 option

val nth_default : 'a1 -> 'a1 list -> nat -> 'a1

val last : 'a1 list -> 'a1 -> 'a1

val removelast : 'a1 list -> 'a1 list

val exists_last : 'a1 list -> ('a1 list, 'a1) sigT

val remove : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list

val count_occ : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 -> nat

val rev : 'a1 list -> 'a1 list

val rev_append : 'a1 list -> 'a1 list -> 'a1 list

val rev' : 'a1 list -> 'a1 list

val concat : 'a1 list list -> 'a1 list

val list_eq_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val list_power : 'a1 list -> 'a2 list -> ('a1 * 'a2) list list

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val forallb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val find : ('a1 -> bool) -> 'a1 list -> 'a1 option

val partition : ('a1 -> bool) -> 'a1 list -> 'a1 list * 'a1 list

val remove' : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list

val count_occ' : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 -> nat

val split : ('a1 * 'a2) list -> 'a1 list * 'a2 list

val combine : 'a1 list -> 'a2 list -> ('a1 * 'a2) list

val list_prod : 'a1 list -> 'a2 list -> ('a1 * 'a2) list

val firstn : nat -> 'a1 list -> 'a1 list

val skipn : nat -> 'a1 list -> 'a1 list

val nodup : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list

val seq : nat -> nat -> nat list

val coq_Exists_dec : 'a1 list -> ('a1 -> bool) -> bool

val coq_Forall_rect : 'a2 -> ('a1 -> 'a1 list -> __ -> 'a2) -> 'a1 list -> 'a2

val coq_Forall_dec : ('a1 -> bool) -> 'a1 list -> bool

val coq_Forall_Exists_dec : ('a1 -> bool) -> 'a1 list -> bool

val repeat : 'a1 -> nat -> 'a1 list

val list_sum : nat list -> nat

val list_max : nat list -> nat
