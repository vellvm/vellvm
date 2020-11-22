open Datatypes
open ITreeDefinition
open Sum

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val interp_mrec :
    (__ -> 'a1 -> (('a1, 'a2, __) sum1, __) itree) -> (('a1, 'a2, __) sum1,
    'a3) itree -> ('a2, 'a3) itree **)

let interp_mrec ctx =
  ITree.iter (fun t ->
    match observe t with
    | RetF r -> lazy (Coq_go (RetF (Coq_inr r)))
    | TauF t0 -> lazy (Coq_go (RetF (Coq_inl t0)))
    | VisF (e0, k) ->
      (match e0 with
       | Coq_inl1 d ->
         lazy (Coq_go (RetF (Coq_inl (ITree.bind' k (ctx __ d)))))
       | Coq_inr1 e ->
         lazy (Coq_go (VisF (e, (fun x -> lazy (Coq_go (RetF (Coq_inl
           (k x))))))))))

(** val mrec :
    (__ -> 'a1 -> (('a1, 'a2, __) sum1, __) itree) -> 'a1 -> ('a2, 'a3) itree **)

let mrec ctx d =
  interp_mrec ctx (Obj.magic ctx __ d)

(** val trigger_inl1 : 'a1 -> (('a1, 'a2, __) sum1, 'a3) itree **)

let trigger_inl1 d =
  ITree.trigger (Coq_inl1 d)

(** val mrec_fix :
    ((__ -> 'a1 -> (('a1, 'a2, __) sum1, __) itree) -> __ -> 'a1 -> (('a1,
    'a2, __) sum1, __) itree) -> 'a1 -> ('a2, 'a3) itree **)

let mrec_fix ctx x =
  mrec (ctx (fun _ -> trigger_inl1)) x

type ('a, 'b, 'x) callE =
  'a
  (* singleton inductive, whose constructor was Call *)

(** val callE_rect : ('a1 -> 'a3) -> ('a1, 'a2, 'a4) callE -> 'a3 **)

let callE_rect f =
  f

(** val callE_rec : ('a1 -> 'a3) -> ('a1, 'a2, 'a4) callE -> 'a3 **)

let callE_rec f =
  f

(** val unCall : ('a1, 'a2, 'a3) callE -> 'a1 **)

let unCall e =
  e

(** val calling : ('a1 -> 'a3) -> ('a1, 'a2, 'a4) callE -> 'a3 **)

let calling f =
  f

(** val calling' :
    ('a1 -> ('a3, 'a2) itree) -> ('a1, 'a2, 'a4) callE -> ('a3, 'a4) itree **)

let calling' f e =
  Obj.magic f e

(** val coq_rec :
    ('a2 -> ((('a2, 'a3, __) callE, 'a1, __) sum1, 'a3) itree) -> 'a2 ->
    ('a1, 'a3) itree **)

let coq_rec body a =
  mrec (fun _ -> calling' body) a

(** val call : 'a2 -> ((('a2, 'a3, __) callE, 'a1, __) sum1, 'a3) itree **)

let call a =
  ITree.trigger (Coq_inl1 a)

(** val rec_fix :
    (('a2 -> ((('a2, 'a3, __) callE, 'a1, __) sum1, 'a3) itree) -> 'a2 ->
    ((('a2, 'a3, __) callE, 'a1, __) sum1, 'a3) itree) -> 'a2 -> ('a1, 'a3)
    itree **)

let rec_fix body =
  coq_rec (body call)
