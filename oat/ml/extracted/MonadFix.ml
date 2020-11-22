open Datatypes

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'm coq_MonadFix =
  __ -> __ -> ((__ -> 'm) -> __ -> 'm) -> __ -> 'm
  (* singleton inductive, whose constructor was Build_MonadFix *)

(** val mfix :
    'a1 coq_MonadFix -> (('a2 -> 'a1) -> 'a2 -> 'a1) -> 'a2 -> 'a1 **)

let mfix monadFix x x0 =
  Obj.magic monadFix __ __ x x0

type 'r ftype = __

type tuple = __

(** val wrap : __ list -> (tuple -> 'a1) -> 'a1 ftype **)

let rec wrap ls f =
  match ls with
  | [] -> Obj.magic f ()
  | _ :: ls0 -> Obj.magic (fun x -> wrap ls0 (fun g -> Obj.magic f (x, g)))

(** val apply : __ list -> 'a1 ftype -> tuple -> 'a1 **)

let rec apply ls f x =
  match ls with
  | [] -> Obj.magic f
  | _ :: ls0 ->
    apply ls0 (Obj.magic f (fst (Obj.magic x))) (snd (Obj.magic x))

(** val mfix_multi :
    'a1 coq_MonadFix -> __ list -> ('a1 ftype -> 'a1 ftype) -> 'a1 ftype **)

let mfix_multi mF ls f =
  wrap ls (mfix mF (fun packed -> apply ls (f (wrap ls packed))))

(** val mfix2 :
    'a1 coq_MonadFix -> (('a2 -> 'a3 -> 'a1) -> 'a2 -> 'a3 -> 'a1) -> 'a2 ->
    'a3 -> 'a1 **)

let mfix2 mF ff a b =
  let ff' = fun fabp abp ->
    let (a0, b0) = abp in let fab = fun a1 b1 -> fabp (a1, b1) in ff fab a0 b0
  in
  mfix mF ff' (a, b)

(** val mfix3 :
    'a1 coq_MonadFix -> (('a2 -> 'a3 -> 'a4 -> 'a1) -> 'a2 -> 'a3 -> 'a4 ->
    'a1) -> 'a2 -> 'a3 -> 'a4 -> 'a1 **)

let mfix3 mF ff a b c =
  let ff' = fun fabcp abcp ->
    let (abp, c0) = abcp in
    let (a0, b0) = abp in
    let fabc = fun a1 b1 c1 -> fabcp ((a1, b1), c1) in ff fabc a0 b0 c0
  in
  mfix mF ff' ((a, b), c)
