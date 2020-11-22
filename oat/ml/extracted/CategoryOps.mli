
type __ = Obj.t

module Carrier :
 sig
 end

type ('obj, 'c) coq_Eq2 = __

type ('obj, 'c) coq_Id_ = 'obj -> 'c

val id_ : ('a1, 'a2) coq_Id_ -> 'a1 -> 'a2

type ('obj, 'c) coq_Cat = 'obj -> 'obj -> 'obj -> 'c -> 'c -> 'c

val cat : ('a1, 'a2) coq_Cat -> 'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2

type ('obj, 'c) coq_Initial = 'obj -> 'c

val empty : 'a1 -> ('a1, 'a2) coq_Initial -> 'a1 -> 'a2

type ('obj, 'c) coq_Terminal = 'obj -> 'c

val one : 'a1 -> ('a1, 'a2) coq_Terminal -> 'a1 -> 'a2

type ('obj, 'c) op = 'c

type ('obj, 'c) coq_Bimap = 'obj -> 'obj -> 'obj -> 'obj -> 'c -> 'c -> 'c

val bimap :
  ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Bimap -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a2 -> 'a2 -> 'a2

type ('obj, 'c) coq_Case = 'obj -> 'obj -> 'obj -> 'c -> 'c -> 'c

val case_ :
  ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Case -> 'a1 -> 'a1 -> 'a1 -> 'a2 ->
  'a2 -> 'a2

type ('obj, 'c) coq_Inl = 'obj -> 'obj -> 'c

val inl_ : ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Inl -> 'a1 -> 'a1 -> 'a2

type ('obj, 'c) coq_Inr = 'obj -> 'obj -> 'c

val inr_ : ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Inr -> 'a1 -> 'a1 -> 'a2

type ('obj, 'c) coq_AssocR = 'obj -> 'obj -> 'obj -> 'c

val assoc_r :
  ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_AssocR -> 'a1 -> 'a1 -> 'a1 -> 'a2

type ('obj, 'c) coq_AssocL = 'obj -> 'obj -> 'obj -> 'c

val assoc_l :
  ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_AssocL -> 'a1 -> 'a1 -> 'a1 -> 'a2

type ('obj, 'c) coq_UnitL = 'obj -> 'c

val unit_l : ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1, 'a2) coq_UnitL -> 'a1 -> 'a2

type ('obj, 'c) coq_UnitL' = 'obj -> 'c

val unit_l' :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1, 'a2) coq_UnitL' -> 'a1 -> 'a2

type ('obj, 'c) coq_UnitR = 'obj -> 'c

val unit_r : ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1, 'a2) coq_UnitR -> 'a1 -> 'a2

type ('obj, 'c) coq_UnitR' = 'obj -> 'c

val unit_r' :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1, 'a2) coq_UnitR' -> 'a1 -> 'a2

type ('obj, 'c) coq_Pair = 'obj -> 'obj -> 'obj -> 'c -> 'c -> 'c

val pair_ :
  ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Pair -> 'a1 -> 'a1 -> 'a1 -> 'a2 ->
  'a2 -> 'a2

type ('obj, 'c) coq_Fst = 'obj -> 'obj -> 'c

val fst_ : ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Fst -> 'a1 -> 'a1 -> 'a2

type ('obj, 'c) coq_Snd = 'obj -> 'obj -> 'c

val snd_ : ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Snd -> 'a1 -> 'a1 -> 'a2

type ('obj, 'c) coq_Swap = 'obj -> 'obj -> 'c

val swap : ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Swap -> 'a1 -> 'a1 -> 'a2

module CatNotations :
 sig
 end

val merge :
  ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Id_ -> ('a1, 'a2) coq_Case -> 'a1 ->
  'a2

val coq_Bimap_Coproduct :
  ('a1, 'a2) coq_Cat -> ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Case -> ('a1,
  'a2) coq_Inl -> ('a1, 'a2) coq_Inr -> ('a1, 'a2) coq_Bimap

val coq_Swap_Coproduct :
  ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Case -> ('a1, 'a2) coq_Inl -> ('a1,
  'a2) coq_Inr -> ('a1, 'a2) coq_Swap

val coq_AssocR_Coproduct :
  ('a1, 'a2) coq_Cat -> ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Case -> ('a1,
  'a2) coq_Inl -> ('a1, 'a2) coq_Inr -> ('a1, 'a2) coq_AssocR

val coq_AssocL_Coproduct :
  ('a1, 'a2) coq_Cat -> ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Case -> ('a1,
  'a2) coq_Inl -> ('a1, 'a2) coq_Inr -> ('a1, 'a2) coq_AssocL

val coq_UnitL_Coproduct :
  ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Case -> ('a1, 'a2) coq_Id_ -> 'a1 ->
  ('a1, 'a2) coq_Initial -> ('a1, 'a2) coq_UnitL

val coq_UnitL'_Coproduct :
  ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Inr -> 'a1 -> ('a1, 'a2) coq_UnitL'

val coq_UnitR_Coproduct :
  ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Case -> ('a1, 'a2) coq_Id_ -> 'a1 ->
  ('a1, 'a2) coq_Initial -> ('a1, 'a2) coq_UnitR

val coq_UnitR'_Coproduct :
  ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Inl -> 'a1 -> ('a1, 'a2) coq_UnitR'

val coq_Bimap_Product :
  ('a1, 'a2) coq_Cat -> ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Pair -> ('a1,
  'a2) coq_Fst -> ('a1, 'a2) coq_Snd -> ('a1, 'a2) coq_Bimap

val coq_Swap_Product :
  ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Pair -> ('a1, 'a2) coq_Fst -> ('a1,
  'a2) coq_Snd -> ('a1, 'a2) coq_Swap

val coq_AssocR_Product :
  ('a1, 'a2) coq_Cat -> ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Pair -> ('a1,
  'a2) coq_Fst -> ('a1, 'a2) coq_Snd -> ('a1, 'a2) coq_AssocR

val coq_AssocL_Product :
  ('a1, 'a2) coq_Cat -> ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Pair -> ('a1,
  'a2) coq_Fst -> ('a1, 'a2) coq_Snd -> ('a1, 'a2) coq_AssocL

val coq_UnitL_Product :
  ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Snd -> 'a1 -> ('a1, 'a2) coq_UnitL

val coq_UnitL'_Product :
  ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Pair -> ('a1, 'a2) coq_Id_ -> 'a1 ->
  ('a1, 'a2) coq_Terminal -> ('a1, 'a2) coq_UnitL'

val coq_UnitR_Product :
  ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Fst -> 'a1 -> ('a1, 'a2) coq_UnitR

val coq_UnitR'_Product :
  ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Pair -> ('a1, 'a2) coq_Id_ -> 'a1 ->
  ('a1, 'a2) coq_Terminal -> ('a1, 'a2) coq_UnitR'

type ('obj, 'c) coq_Dagger = 'obj -> 'obj -> ('obj, 'c) op -> 'c

val dagger : ('a1, 'a2) coq_Dagger -> 'a1 -> 'a1 -> ('a1, 'a2) op -> 'a2

type ('obj, 'c) coq_Iter = 'obj -> 'obj -> 'c -> 'c

val iter :
  ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Iter -> 'a1 -> 'a1 -> 'a2 -> 'a2

val loop :
  ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Id_ -> ('a1, 'a2) coq_Cat -> ('a1,
  'a2) coq_Case -> ('a1, 'a2) coq_Inl -> ('a1, 'a2) coq_Inr -> ('a1, 'a2)
  coq_Iter -> 'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a2

type ('obj, 'c) coq_ReSum = 'c

val resum : 'a1 -> 'a1 -> ('a1, 'a2) coq_ReSum -> 'a2

val coq_ReSum_id : ('a1, 'a2) coq_Id_ -> 'a1 -> ('a1, 'a2) coq_ReSum

val coq_ReSum_sum :
  ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Case -> 'a1 -> 'a1 -> 'a1 -> ('a1,
  'a2) coq_ReSum -> ('a1, 'a2) coq_ReSum -> ('a1, 'a2) coq_ReSum

val coq_ReSum_inl :
  ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Cat -> ('a1, 'a2) coq_Inl -> 'a1 ->
  'a1 -> 'a1 -> ('a1, 'a2) coq_ReSum -> ('a1, 'a2) coq_ReSum

val coq_ReSum_inr :
  ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Cat -> ('a1, 'a2) coq_Inr -> 'a1 ->
  'a1 -> 'a1 -> ('a1, 'a2) coq_ReSum -> ('a1, 'a2) coq_ReSum

val coq_ReSum_empty :
  'a1 -> ('a1, 'a2) coq_Initial -> 'a1 -> ('a1, 'a2) coq_ReSum
