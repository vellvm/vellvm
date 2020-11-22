open Sum

type __ = Obj.t

type ('e, 'f) coq_IFun = __ -> 'e -> 'f

val apply_IFun : ('a1, 'a2) coq_IFun -> 'a1 -> 'a2

val apply_IFun' : ('a1, 'a2) coq_IFun -> 'a1 -> 'a2

val as_IFun : (__ -> 'a1 -> 'a2) -> 'a1 -> 'a2

val coq_Id_IFun : 'a1 -> 'a1

val coq_Cat_IFun : ('a1, 'a2) coq_IFun -> ('a2, 'a3) coq_IFun -> 'a1 -> 'a3

val coq_Initial_void1 : __ -> 'a1

val case_sum1 :
  (__ -> 'a1 -> 'a3) -> (__ -> 'a2 -> 'a3) -> ('a1, 'a2, 'a4) sum1 -> 'a3

val coq_Case_sum1 :
  ('a1, 'a3) coq_IFun -> ('a2, 'a3) coq_IFun -> ('a1, 'a2, 'a4) sum1 -> 'a3

val coq_Inl_sum1 : 'a1 -> ('a1, 'a2, 'a3) sum1

val coq_Inr_sum1 : 'a2 -> ('a1, 'a2, 'a3) sum1
