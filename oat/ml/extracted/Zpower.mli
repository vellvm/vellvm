open BinInt
open BinNums
open BinPos
open Datatypes

type __ = Obj.t

val coq_Zpower_nat : coq_Z -> nat -> coq_Z

val shift_nat : nat -> positive -> positive

val shift_pos : positive -> positive -> positive

val shift : coq_Z -> positive -> positive

val two_power_nat : nat -> coq_Z

val two_power_pos : positive -> coq_Z

val two_p : coq_Z -> coq_Z

val coq_Zdiv_rest_aux : ((coq_Z * coq_Z) * coq_Z) -> (coq_Z * coq_Z) * coq_Z

val coq_Zdiv_rest : coq_Z -> positive -> coq_Z * coq_Z

type coq_Zdiv_rest_proofs =
| Zdiv_rest_proof of coq_Z * coq_Z

val coq_Zdiv_rest_proofs_rect :
  coq_Z -> positive -> (coq_Z -> coq_Z -> __ -> __ -> __ -> 'a1) ->
  coq_Zdiv_rest_proofs -> 'a1

val coq_Zdiv_rest_proofs_rec :
  coq_Z -> positive -> (coq_Z -> coq_Z -> __ -> __ -> __ -> 'a1) ->
  coq_Zdiv_rest_proofs -> 'a1

val coq_Zdiv_rest_correct : coq_Z -> positive -> coq_Zdiv_rest_proofs
