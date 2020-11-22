open CategoryOps
open Function0
open ITreeDefinition

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val subevent : ('a1, 'a2) coq_IFun -> 'a1 -> 'a2 **)

let subevent h x =
  resum __ __ h __ x

module SumNotations =
 struct
 end

type ('u, 'v) coq_Embeddable = 'u -> 'v

(** val embed : ('a1, 'a2) coq_Embeddable -> 'a1 -> 'a2 **)

let embed embeddable =
  embeddable

(** val coq_Embeddable_forall :
    ('a1 -> ('a2, 'a3) coq_Embeddable) -> ('a1 -> 'a2, 'a1 -> 'a3)
    coq_Embeddable **)

let coq_Embeddable_forall h u a =
  embed (h a) (u a)

(** val coq_Embeddable_itree :
    ('a1, 'a2) coq_IFun -> ('a1, ('a2, 'a3) itree) coq_Embeddable **)

let coq_Embeddable_itree h e =
  ITree.trigger (subevent h e)
