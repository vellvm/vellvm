
type __ = Obj.t

module Carrier =
 struct
 end

type ('obj, 'c) coq_Eq2 = __

type ('obj, 'c) coq_Id_ = 'obj -> 'c

(** val id_ : ('a1, 'a2) coq_Id_ -> 'a1 -> 'a2 **)

let id_ id_0 =
  id_0

type ('obj, 'c) coq_Cat = 'obj -> 'obj -> 'obj -> 'c -> 'c -> 'c

(** val cat : ('a1, 'a2) coq_Cat -> 'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 **)

let cat cat0 =
  cat0

type ('obj, 'c) coq_Initial = 'obj -> 'c

(** val empty : 'a1 -> ('a1, 'a2) coq_Initial -> 'a1 -> 'a2 **)

let empty _ initial =
  initial

type ('obj, 'c) coq_Terminal = 'obj -> 'c

(** val one : 'a1 -> ('a1, 'a2) coq_Terminal -> 'a1 -> 'a2 **)

let one _ terminal =
  terminal

type ('obj, 'c) op = 'c

type ('obj, 'c) coq_Bimap = 'obj -> 'obj -> 'obj -> 'obj -> 'c -> 'c -> 'c

(** val bimap :
    ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Bimap -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a2 -> 'a2 -> 'a2 **)

let bimap _ bimap0 =
  bimap0

type ('obj, 'c) coq_Case = 'obj -> 'obj -> 'obj -> 'c -> 'c -> 'c

(** val case_ :
    ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Case -> 'a1 -> 'a1 -> 'a1 -> 'a2 ->
    'a2 -> 'a2 **)

let case_ _ case =
  case

type ('obj, 'c) coq_Inl = 'obj -> 'obj -> 'c

(** val inl_ :
    ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Inl -> 'a1 -> 'a1 -> 'a2 **)

let inl_ _ inl =
  inl

type ('obj, 'c) coq_Inr = 'obj -> 'obj -> 'c

(** val inr_ :
    ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Inr -> 'a1 -> 'a1 -> 'a2 **)

let inr_ _ inr =
  inr

type ('obj, 'c) coq_AssocR = 'obj -> 'obj -> 'obj -> 'c

(** val assoc_r :
    ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_AssocR -> 'a1 -> 'a1 -> 'a1 -> 'a2 **)

let assoc_r _ assocR =
  assocR

type ('obj, 'c) coq_AssocL = 'obj -> 'obj -> 'obj -> 'c

(** val assoc_l :
    ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_AssocL -> 'a1 -> 'a1 -> 'a1 -> 'a2 **)

let assoc_l _ assocL =
  assocL

type ('obj, 'c) coq_UnitL = 'obj -> 'c

(** val unit_l :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1, 'a2) coq_UnitL -> 'a1 -> 'a2 **)

let unit_l _ _ unitL =
  unitL

type ('obj, 'c) coq_UnitL' = 'obj -> 'c

(** val unit_l' :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1, 'a2) coq_UnitL' -> 'a1 -> 'a2 **)

let unit_l' _ _ unitL' =
  unitL'

type ('obj, 'c) coq_UnitR = 'obj -> 'c

(** val unit_r :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1, 'a2) coq_UnitR -> 'a1 -> 'a2 **)

let unit_r _ _ unitR =
  unitR

type ('obj, 'c) coq_UnitR' = 'obj -> 'c

(** val unit_r' :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1, 'a2) coq_UnitR' -> 'a1 -> 'a2 **)

let unit_r' _ _ unitR' =
  unitR'

type ('obj, 'c) coq_Pair = 'obj -> 'obj -> 'obj -> 'c -> 'c -> 'c

(** val pair_ :
    ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Pair -> 'a1 -> 'a1 -> 'a1 -> 'a2 ->
    'a2 -> 'a2 **)

let pair_ _ pair =
  pair

type ('obj, 'c) coq_Fst = 'obj -> 'obj -> 'c

(** val fst_ :
    ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Fst -> 'a1 -> 'a1 -> 'a2 **)

let fst_ _ fst =
  fst

type ('obj, 'c) coq_Snd = 'obj -> 'obj -> 'c

(** val snd_ :
    ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Snd -> 'a1 -> 'a1 -> 'a2 **)

let snd_ _ snd =
  snd

type ('obj, 'c) coq_Swap = 'obj -> 'obj -> 'c

(** val swap :
    ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Swap -> 'a1 -> 'a1 -> 'a2 **)

let swap _ swap0 =
  swap0

module CatNotations =
 struct
 end

(** val merge :
    ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Id_ -> ('a1, 'a2) coq_Case -> 'a1
    -> 'a2 **)

let merge bif id_C coproduct_C a =
  case_ bif coproduct_C a a a (id_ id_C a) (id_ id_C a)

(** val coq_Bimap_Coproduct :
    ('a1, 'a2) coq_Cat -> ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Case -> ('a1,
    'a2) coq_Inl -> ('a1, 'a2) coq_Inr -> ('a1, 'a2) coq_Bimap **)

let coq_Bimap_Coproduct cat_C sUM coprod_SUM inl_SUM inr_SUM a b c d f g =
  case_ sUM coprod_SUM a b (sUM c d)
    (cat cat_C a c (sUM c d) f (inl_ sUM inl_SUM c d))
    (cat cat_C b d (sUM c d) g (inr_ sUM inr_SUM c d))

(** val coq_Swap_Coproduct :
    ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Case -> ('a1, 'a2) coq_Inl -> ('a1,
    'a2) coq_Inr -> ('a1, 'a2) coq_Swap **)

let coq_Swap_Coproduct sUM coprod_SUM inl_SUM inr_SUM a b =
  case_ sUM coprod_SUM a b (sUM b a) (inr_ sUM inr_SUM b a)
    (inl_ sUM inl_SUM b a)

(** val coq_AssocR_Coproduct :
    ('a1, 'a2) coq_Cat -> ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Case -> ('a1,
    'a2) coq_Inl -> ('a1, 'a2) coq_Inr -> ('a1, 'a2) coq_AssocR **)

let coq_AssocR_Coproduct cat_C sUM coprod_SUM inl_SUM inr_SUM a b c =
  case_ sUM coprod_SUM (sUM a b) c (sUM a (sUM b c))
    (case_ sUM coprod_SUM a b (sUM a (sUM b c))
      (inl_ sUM inl_SUM a (sUM b c))
      (cat cat_C b (sUM b c) (sUM a (sUM b c)) (inl_ sUM inl_SUM b c)
        (inr_ sUM inr_SUM a (sUM b c))))
    (cat cat_C c (sUM b c) (sUM a (sUM b c)) (inr_ sUM inr_SUM b c)
      (inr_ sUM inr_SUM a (sUM b c)))

(** val coq_AssocL_Coproduct :
    ('a1, 'a2) coq_Cat -> ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Case -> ('a1,
    'a2) coq_Inl -> ('a1, 'a2) coq_Inr -> ('a1, 'a2) coq_AssocL **)

let coq_AssocL_Coproduct cat_C sUM coprod_SUM inl_SUM inr_SUM a b c =
  case_ sUM coprod_SUM a (sUM b c) (sUM (sUM a b) c)
    (cat cat_C a (sUM a b) (sUM (sUM a b) c) (inl_ sUM inl_SUM a b)
      (inl_ sUM inl_SUM (sUM a b) c))
    (case_ sUM coprod_SUM b c (sUM (sUM a b) c)
      (cat cat_C b (sUM a b) (sUM (sUM a b) c) (inr_ sUM inr_SUM a b)
        (inl_ sUM inl_SUM (sUM a b) c)) (inr_ sUM inr_SUM (sUM a b) c))

(** val coq_UnitL_Coproduct :
    ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Case -> ('a1, 'a2) coq_Id_ -> 'a1
    -> ('a1, 'a2) coq_Initial -> ('a1, 'a2) coq_UnitL **)

let coq_UnitL_Coproduct sUM coprod_SUM id_C i initial_I a =
  case_ sUM coprod_SUM i a a (empty i initial_I a) (id_ id_C a)

(** val coq_UnitL'_Coproduct :
    ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Inr -> 'a1 -> ('a1, 'a2) coq_UnitL' **)

let coq_UnitL'_Coproduct =
  inr_

(** val coq_UnitR_Coproduct :
    ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Case -> ('a1, 'a2) coq_Id_ -> 'a1
    -> ('a1, 'a2) coq_Initial -> ('a1, 'a2) coq_UnitR **)

let coq_UnitR_Coproduct sUM coprod_SUM id_C i initial_I a =
  case_ sUM coprod_SUM a i a (id_ id_C a) (empty i initial_I a)

(** val coq_UnitR'_Coproduct :
    ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Inl -> 'a1 -> ('a1, 'a2) coq_UnitR' **)

let coq_UnitR'_Coproduct sUM inl_SUM i a =
  inl_ sUM inl_SUM a i

(** val coq_Bimap_Product :
    ('a1, 'a2) coq_Cat -> ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Pair -> ('a1,
    'a2) coq_Fst -> ('a1, 'a2) coq_Snd -> ('a1, 'a2) coq_Bimap **)

let coq_Bimap_Product cat_C pROD prod_PROD fst_PROD snd_PROD a b c d f g =
  pair_ pROD prod_PROD c d (pROD a b)
    (cat cat_C (pROD a b) a c (fst_ pROD fst_PROD a b) f)
    (cat cat_C (pROD a b) b d (snd_ pROD snd_PROD a b) g)

(** val coq_Swap_Product :
    ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Pair -> ('a1, 'a2) coq_Fst -> ('a1,
    'a2) coq_Snd -> ('a1, 'a2) coq_Swap **)

let coq_Swap_Product pROD prod_PROD fst_PROD snd_PROD a b =
  pair_ pROD prod_PROD b a (pROD a b) (snd_ pROD snd_PROD a b)
    (fst_ pROD fst_PROD a b)

(** val coq_AssocR_Product :
    ('a1, 'a2) coq_Cat -> ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Pair -> ('a1,
    'a2) coq_Fst -> ('a1, 'a2) coq_Snd -> ('a1, 'a2) coq_AssocR **)

let coq_AssocR_Product cat_C pROD prod_PROD fst_PROD snd_PROD a b c =
  pair_ pROD prod_PROD a (pROD b c) (pROD (pROD a b) c)
    (cat cat_C (pROD (pROD a b) c) (pROD a b) a
      (fst_ pROD fst_PROD (pROD a b) c) (fst_ pROD fst_PROD a b))
    (pair_ pROD prod_PROD b c (pROD (pROD a b) c)
      (cat cat_C (pROD (pROD a b) c) (pROD a b) b
        (fst_ pROD fst_PROD (pROD a b) c) (snd_ pROD snd_PROD a b))
      (snd_ pROD snd_PROD (pROD a b) c))

(** val coq_AssocL_Product :
    ('a1, 'a2) coq_Cat -> ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Pair -> ('a1,
    'a2) coq_Fst -> ('a1, 'a2) coq_Snd -> ('a1, 'a2) coq_AssocL **)

let coq_AssocL_Product cat_C pROD prod_PROD fst_PROD snd_PROD a b c =
  pair_ pROD prod_PROD (pROD a b) c (pROD a (pROD b c))
    (pair_ pROD prod_PROD a b (pROD a (pROD b c))
      (fst_ pROD fst_PROD a (pROD b c))
      (cat cat_C (pROD a (pROD b c)) (pROD b c) b
        (snd_ pROD snd_PROD a (pROD b c)) (fst_ pROD fst_PROD b c)))
    (cat cat_C (pROD a (pROD b c)) (pROD b c) c
      (snd_ pROD snd_PROD a (pROD b c)) (snd_ pROD snd_PROD b c))

(** val coq_UnitL_Product :
    ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Snd -> 'a1 -> ('a1, 'a2) coq_UnitL **)

let coq_UnitL_Product =
  snd_

(** val coq_UnitL'_Product :
    ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Pair -> ('a1, 'a2) coq_Id_ -> 'a1
    -> ('a1, 'a2) coq_Terminal -> ('a1, 'a2) coq_UnitL' **)

let coq_UnitL'_Product pROD prod_PROD id_C t terminal_T a =
  pair_ pROD prod_PROD t a a (one t terminal_T a) (id_ id_C a)

(** val coq_UnitR_Product :
    ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Fst -> 'a1 -> ('a1, 'a2) coq_UnitR **)

let coq_UnitR_Product pROD fst_PROD t a =
  fst_ pROD fst_PROD a t

(** val coq_UnitR'_Product :
    ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Pair -> ('a1, 'a2) coq_Id_ -> 'a1
    -> ('a1, 'a2) coq_Terminal -> ('a1, 'a2) coq_UnitR' **)

let coq_UnitR'_Product pROD prod_PROD id_C t terminal_T a =
  pair_ pROD prod_PROD a t a (id_ id_C a) (one t terminal_T a)

type ('obj, 'c) coq_Dagger = 'obj -> 'obj -> ('obj, 'c) op -> 'c

(** val dagger :
    ('a1, 'a2) coq_Dagger -> 'a1 -> 'a1 -> ('a1, 'a2) op -> 'a2 **)

let dagger dagger0 =
  dagger0

type ('obj, 'c) coq_Iter = 'obj -> 'obj -> 'c -> 'c

(** val iter :
    ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Iter -> 'a1 -> 'a1 -> 'a2 -> 'a2 **)

let iter _ iter0 =
  iter0

(** val loop :
    ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Id_ -> ('a1, 'a2) coq_Cat -> ('a1,
    'a2) coq_Case -> ('a1, 'a2) coq_Inl -> ('a1, 'a2) coq_Inr -> ('a1, 'a2)
    coq_Iter -> 'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a2 **)

let loop bif id_C cat_C case_bif inl_bif inr_bif iter_bif a b c f =
  cat cat_C a (bif c a) b (inr_ bif inr_bif c a)
    (iter bif iter_bif (bif c a) b
      (cat cat_C (bif c a) (bif c b) (bif (bif c a) b) f
        (bimap bif (coq_Bimap_Coproduct cat_C bif case_bif inl_bif inr_bif) c
          b (bif c a) b (inl_ bif inl_bif c a) (id_ id_C b))))

type ('obj, 'c) coq_ReSum = 'c

(** val resum : 'a1 -> 'a1 -> ('a1, 'a2) coq_ReSum -> 'a2 **)

let resum _ _ reSum =
  reSum

(** val coq_ReSum_id : ('a1, 'a2) coq_Id_ -> 'a1 -> ('a1, 'a2) coq_ReSum **)

let coq_ReSum_id =
  id_

(** val coq_ReSum_sum :
    ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Case -> 'a1 -> 'a1 -> 'a1 -> ('a1,
    'a2) coq_ReSum -> ('a1, 'a2) coq_ReSum -> ('a1, 'a2) coq_ReSum **)

let coq_ReSum_sum bif h1 a b c h4 h5 =
  case_ bif h1 a b c (resum a c h4) (resum b c h5)

(** val coq_ReSum_inl :
    ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Cat -> ('a1, 'a2) coq_Inl -> 'a1 ->
    'a1 -> 'a1 -> ('a1, 'a2) coq_ReSum -> ('a1, 'a2) coq_ReSum **)

let coq_ReSum_inl bif h0 h2 a b c h4 =
  cat h0 a b (bif b c) (resum a b h4) (inl_ bif h2 b c)

(** val coq_ReSum_inr :
    ('a1 -> 'a1 -> 'a1) -> ('a1, 'a2) coq_Cat -> ('a1, 'a2) coq_Inr -> 'a1 ->
    'a1 -> 'a1 -> ('a1, 'a2) coq_ReSum -> ('a1, 'a2) coq_ReSum **)

let coq_ReSum_inr bif h0 h3 a b c h4 =
  cat h0 a b (bif c b) (resum a b h4) (inr_ bif h3 c b)

(** val coq_ReSum_empty :
    'a1 -> ('a1, 'a2) coq_Initial -> 'a1 -> ('a1, 'a2) coq_ReSum **)

let coq_ReSum_empty =
  empty
