open Applicative
open Functor

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'm coq_Monad = { ret : (__ -> __ -> 'm);
                      bind : (__ -> __ -> 'm -> (__ -> 'm) -> 'm) }

(** val ret : 'a1 coq_Monad -> 'a2 -> 'a1 **)

let ret monad x =
  Obj.magic monad.ret __ x

(** val bind : 'a1 coq_Monad -> 'a1 -> ('a2 -> 'a1) -> 'a1 **)

let bind monad x x0 =
  Obj.magic monad.bind __ __ x x0

(** val liftM : 'a1 coq_Monad -> ('a2 -> 'a3) -> 'a1 -> 'a1 **)

let liftM m f x =
  bind m x (fun x0 -> ret m (f x0))

(** val liftM2 : 'a1 coq_Monad -> ('a2 -> 'a3 -> 'a4) -> 'a1 -> 'a1 -> 'a1 **)

let liftM2 m f x y =
  bind m x (fun x0 -> bind m y (fun x1 -> ret m (f x0 x1)))

(** val liftM3 :
    'a1 coq_Monad -> ('a2 -> 'a3 -> 'a4 -> 'a5) -> 'a1 -> 'a1 -> 'a1 -> 'a1 **)

let liftM3 m f x y z =
  bind m x (fun x0 ->
    bind m y (fun x1 -> bind m z (fun x2 -> ret m (f x0 x1 x2))))

(** val apM : 'a1 coq_Monad -> 'a1 -> 'a1 -> 'a1 **)

let apM m fM aM =
  bind m fM (fun f -> liftM m f aM)

(** val mcompose :
    'a1 coq_Monad -> ('a2 -> 'a1) -> ('a3 -> 'a1) -> 'a2 -> 'a1 **)

let mcompose m f g x =
  bind m (f x) g

module MonadBaseNotation =
 struct
 end

module MonadNotation =
 struct
 end

module MonadLetNotation =
 struct
 end

(** val coq_Functor_Monad : 'a1 coq_Monad -> 'a1 coq_Functor **)

let coq_Functor_Monad m _ _ =
  liftM m

(** val coq_Applicative_Monad : 'a1 coq_Monad -> 'a1 coq_Applicative **)

let coq_Applicative_Monad m =
  { pure = (fun _ -> ret m); ap = (fun _ _ -> apM m) }
