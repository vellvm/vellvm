open CategoryOps
open Function0
open ITreeDefinition

val subevent : ('a1, 'a2) coq_IFun -> 'a1 -> 'a2

module SumNotations :
 sig
 end

type ('u, 'v) coq_Embeddable = 'u -> 'v

val embed : ('a1, 'a2) coq_Embeddable -> 'a1 -> 'a2

val coq_Embeddable_forall :
  ('a1 -> ('a2, 'a3) coq_Embeddable) -> ('a1 -> 'a2, 'a1 -> 'a3)
  coq_Embeddable

val coq_Embeddable_itree :
  ('a1, 'a2) coq_IFun -> ('a1, ('a2, 'a3) itree) coq_Embeddable
