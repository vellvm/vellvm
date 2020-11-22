open Ast
open BinNums
open CategoryKleisli
open CategoryOps
open Datatypes
open DynamicValues
open Error
open Function0
open ITreeDefinition
open Integers
open List0
open Monad
open OatEvents
open Recursion
open String0
open Subevent
open Util

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module Int64 = Int64

type int64 = Int64.int

type expr = exp

type stmt = Ast.stmt

type unop = Ast.unop

type binop = Ast.binop

type vdecl = Ast.vdecl

(** val neq : int64 -> int64 -> bool **)

let neq x y =
  negb (Int64.eq x y)

(** val lte : int64 -> int64 -> bool **)

let lte x y =
  (||) (Int64.eq x y) (Int64.lt x y)

(** val gt : int64 -> int64 -> bool **)

let gt x y =
  negb (lte x y)

(** val gte : int64 -> int64 -> bool **)

let gte x y =
  negb (Int64.lt x y)

(** val denote_uop : unop -> ovalue -> (__ coq_OatE, ovalue) itree **)

let denote_uop u v =
  match u with
  | Neg ->
    (match v with
     | OVALUE_Int i ->
       ret (Obj.magic coq_Monad_itree) (OVALUE_Int (Int64.neg i))
     | _ ->
       raise
         (coq_ReSum_inr (Obj.magic __)
           (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
           (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
           (coq_ReSum_inr (Obj.magic __)
             (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
             (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
             (coq_ReSum_inr (Obj.magic __)
               (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
               (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
               (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
         ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('u'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[]))))))))))))))))))))))))))))))))))))))))))
  | Lognot ->
    (match v with
     | OVALUE_Bool b -> ret (Obj.magic coq_Monad_itree) (OVALUE_Bool (negb b))
     | _ ->
       raise
         (coq_ReSum_inr (Obj.magic __)
           (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
           (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
           (coq_ReSum_inr (Obj.magic __)
             (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
             (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
             (coq_ReSum_inr (Obj.magic __)
               (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
               (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
               (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
         ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('u'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[]))))))))))))))))))))))))))))))))))))))))))
  | Bitnot ->
    (match v with
     | OVALUE_Int i ->
       ret (Obj.magic coq_Monad_itree) (OVALUE_Int (Int64.not i))
     | _ ->
       raise
         (coq_ReSum_inr (Obj.magic __)
           (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
           (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
           (coq_ReSum_inr (Obj.magic __)
             (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
             (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
             (coq_ReSum_inr (Obj.magic __)
               (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
               (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
               (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
         ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('u'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[]))))))))))))))))))))))))))))))))))))))))))

(** val denote_bop :
    binop -> ovalue -> ovalue -> (__ coq_OatE, ovalue) itree **)

let denote_bop op v1 v2 =
  match op with
  | Add ->
    (match v1 with
     | OVALUE_Int l ->
       (match v2 with
        | OVALUE_Int r ->
          ret (Obj.magic coq_Monad_itree) (OVALUE_Int (Int64.add l r))
        | _ ->
          raise
            (coq_ReSum_inr (Obj.magic __)
              (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
              (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
              (coq_ReSum_inr (Obj.magic __)
                (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                (coq_ReSum_inr (Obj.magic __)
                  (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                  (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                  (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
            ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
     | _ ->
       raise
         (coq_ReSum_inr (Obj.magic __)
           (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
           (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
           (coq_ReSum_inr (Obj.magic __)
             (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
             (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
             (coq_ReSum_inr (Obj.magic __)
               (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
               (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
               (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
         ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
  | Sub ->
    (match v1 with
     | OVALUE_Int l ->
       (match v2 with
        | OVALUE_Int r ->
          ret (Obj.magic coq_Monad_itree) (OVALUE_Int (Int64.sub l r))
        | _ ->
          raise
            (coq_ReSum_inr (Obj.magic __)
              (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
              (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
              (coq_ReSum_inr (Obj.magic __)
                (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                (coq_ReSum_inr (Obj.magic __)
                  (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                  (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                  (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
            ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
     | _ ->
       raise
         (coq_ReSum_inr (Obj.magic __)
           (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
           (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
           (coq_ReSum_inr (Obj.magic __)
             (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
             (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
             (coq_ReSum_inr (Obj.magic __)
               (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
               (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
               (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
         ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
  | Mul ->
    (match v1 with
     | OVALUE_Int l ->
       (match v2 with
        | OVALUE_Int r ->
          ret (Obj.magic coq_Monad_itree) (OVALUE_Int (Int64.mul l r))
        | _ ->
          raise
            (coq_ReSum_inr (Obj.magic __)
              (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
              (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
              (coq_ReSum_inr (Obj.magic __)
                (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                (coq_ReSum_inr (Obj.magic __)
                  (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                  (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                  (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
            ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
     | _ ->
       raise
         (coq_ReSum_inr (Obj.magic __)
           (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
           (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
           (coq_ReSum_inr (Obj.magic __)
             (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
             (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
             (coq_ReSum_inr (Obj.magic __)
               (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
               (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
               (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
         ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
  | Ast.Eq ->
    (match v1 with
     | OVALUE_Int l ->
       (match v2 with
        | OVALUE_Int r ->
          ret (Obj.magic coq_Monad_itree) (OVALUE_Bool (Int64.eq l r))
        | _ ->
          raise
            (coq_ReSum_inr (Obj.magic __)
              (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
              (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
              (coq_ReSum_inr (Obj.magic __)
                (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                (coq_ReSum_inr (Obj.magic __)
                  (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                  (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                  (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
            ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
     | _ ->
       raise
         (coq_ReSum_inr (Obj.magic __)
           (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
           (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
           (coq_ReSum_inr (Obj.magic __)
             (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
             (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
             (coq_ReSum_inr (Obj.magic __)
               (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
               (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
               (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
         ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
  | Neq ->
    (match v1 with
     | OVALUE_Int l ->
       (match v2 with
        | OVALUE_Int r ->
          ret (Obj.magic coq_Monad_itree) (OVALUE_Bool (neq l r))
        | _ ->
          raise
            (coq_ReSum_inr (Obj.magic __)
              (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
              (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
              (coq_ReSum_inr (Obj.magic __)
                (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                (coq_ReSum_inr (Obj.magic __)
                  (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                  (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                  (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
            ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
     | _ ->
       raise
         (coq_ReSum_inr (Obj.magic __)
           (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
           (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
           (coq_ReSum_inr (Obj.magic __)
             (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
             (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
             (coq_ReSum_inr (Obj.magic __)
               (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
               (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
               (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
         ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
  | Ast.Lt ->
    (match v1 with
     | OVALUE_Int l ->
       (match v2 with
        | OVALUE_Int r ->
          ret (Obj.magic coq_Monad_itree) (OVALUE_Bool (Int64.lt l r))
        | _ ->
          raise
            (coq_ReSum_inr (Obj.magic __)
              (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
              (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
              (coq_ReSum_inr (Obj.magic __)
                (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                (coq_ReSum_inr (Obj.magic __)
                  (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                  (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                  (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
            ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
     | _ ->
       raise
         (coq_ReSum_inr (Obj.magic __)
           (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
           (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
           (coq_ReSum_inr (Obj.magic __)
             (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
             (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
             (coq_ReSum_inr (Obj.magic __)
               (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
               (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
               (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
         ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
  | Lte ->
    (match v1 with
     | OVALUE_Int l ->
       (match v2 with
        | OVALUE_Int r ->
          ret (Obj.magic coq_Monad_itree) (OVALUE_Bool (lte l r))
        | _ ->
          raise
            (coq_ReSum_inr (Obj.magic __)
              (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
              (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
              (coq_ReSum_inr (Obj.magic __)
                (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                (coq_ReSum_inr (Obj.magic __)
                  (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                  (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                  (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
            ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
     | _ ->
       raise
         (coq_ReSum_inr (Obj.magic __)
           (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
           (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
           (coq_ReSum_inr (Obj.magic __)
             (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
             (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
             (coq_ReSum_inr (Obj.magic __)
               (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
               (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
               (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
         ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
  | Ast.Gt ->
    (match v1 with
     | OVALUE_Int l ->
       (match v2 with
        | OVALUE_Int r ->
          ret (Obj.magic coq_Monad_itree) (OVALUE_Bool (gt l r))
        | _ ->
          raise
            (coq_ReSum_inr (Obj.magic __)
              (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
              (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
              (coq_ReSum_inr (Obj.magic __)
                (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                (coq_ReSum_inr (Obj.magic __)
                  (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                  (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                  (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
            ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
     | _ ->
       raise
         (coq_ReSum_inr (Obj.magic __)
           (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
           (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
           (coq_ReSum_inr (Obj.magic __)
             (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
             (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
             (coq_ReSum_inr (Obj.magic __)
               (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
               (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
               (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
         ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
  | Gte ->
    (match v1 with
     | OVALUE_Int l ->
       (match v2 with
        | OVALUE_Int r ->
          ret (Obj.magic coq_Monad_itree) (OVALUE_Bool (gte l r))
        | _ ->
          raise
            (coq_ReSum_inr (Obj.magic __)
              (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
              (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
              (coq_ReSum_inr (Obj.magic __)
                (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                (coq_ReSum_inr (Obj.magic __)
                  (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                  (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                  (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
            ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
     | _ ->
       raise
         (coq_ReSum_inr (Obj.magic __)
           (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
           (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
           (coq_ReSum_inr (Obj.magic __)
             (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
             (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
             (coq_ReSum_inr (Obj.magic __)
               (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
               (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
               (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
         ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
  | And ->
    (match v1 with
     | OVALUE_Bool l ->
       (match v2 with
        | OVALUE_Bool r ->
          ret (Obj.magic coq_Monad_itree) (OVALUE_Bool ((&&) l r))
        | _ ->
          raise
            (coq_ReSum_inr (Obj.magic __)
              (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
              (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
              (coq_ReSum_inr (Obj.magic __)
                (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                (coq_ReSum_inr (Obj.magic __)
                  (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                  (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                  (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
            ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
     | _ ->
       raise
         (coq_ReSum_inr (Obj.magic __)
           (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
           (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
           (coq_ReSum_inr (Obj.magic __)
             (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
             (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
             (coq_ReSum_inr (Obj.magic __)
               (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
               (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
               (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
         ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
  | Or ->
    (match v1 with
     | OVALUE_Bool l ->
       (match v2 with
        | OVALUE_Bool r ->
          ret (Obj.magic coq_Monad_itree) (OVALUE_Bool ((||) l r))
        | _ ->
          raise
            (coq_ReSum_inr (Obj.magic __)
              (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
              (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
              (coq_ReSum_inr (Obj.magic __)
                (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                (coq_ReSum_inr (Obj.magic __)
                  (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                  (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                  (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
            ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
     | _ ->
       raise
         (coq_ReSum_inr (Obj.magic __)
           (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
           (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
           (coq_ReSum_inr (Obj.magic __)
             (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
             (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
             (coq_ReSum_inr (Obj.magic __)
               (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
               (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
               (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
         ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
  | IAnd ->
    (match v1 with
     | OVALUE_Int l ->
       (match v2 with
        | OVALUE_Int r ->
          ret (Obj.magic coq_Monad_itree) (OVALUE_Int (Int64.coq_and l r))
        | _ ->
          raise
            (coq_ReSum_inr (Obj.magic __)
              (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
              (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
              (coq_ReSum_inr (Obj.magic __)
                (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                (coq_ReSum_inr (Obj.magic __)
                  (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                  (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                  (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
            ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
     | _ ->
       raise
         (coq_ReSum_inr (Obj.magic __)
           (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
           (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
           (coq_ReSum_inr (Obj.magic __)
             (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
             (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
             (coq_ReSum_inr (Obj.magic __)
               (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
               (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
               (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
         ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
  | IOr ->
    (match v1 with
     | OVALUE_Int l ->
       (match v2 with
        | OVALUE_Int r ->
          ret (Obj.magic coq_Monad_itree) (OVALUE_Int (Int64.coq_or l r))
        | _ ->
          raise
            (coq_ReSum_inr (Obj.magic __)
              (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
              (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
              (coq_ReSum_inr (Obj.magic __)
                (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                (coq_ReSum_inr (Obj.magic __)
                  (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                  (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                  (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
            ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
     | _ ->
       raise
         (coq_ReSum_inr (Obj.magic __)
           (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
           (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
           (coq_ReSum_inr (Obj.magic __)
             (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
             (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
             (coq_ReSum_inr (Obj.magic __)
               (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
               (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
               (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
         ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
  | Shl ->
    (match v1 with
     | OVALUE_Int l ->
       (match v2 with
        | OVALUE_Int r ->
          ret (Obj.magic coq_Monad_itree) (OVALUE_Int (Int64.shl l r))
        | _ ->
          raise
            (coq_ReSum_inr (Obj.magic __)
              (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
              (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
              (coq_ReSum_inr (Obj.magic __)
                (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                (coq_ReSum_inr (Obj.magic __)
                  (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                  (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                  (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
            ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
     | _ ->
       raise
         (coq_ReSum_inr (Obj.magic __)
           (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
           (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
           (coq_ReSum_inr (Obj.magic __)
             (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
             (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
             (coq_ReSum_inr (Obj.magic __)
               (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
               (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
               (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
         ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
  | Shr ->
    (match v1 with
     | OVALUE_Int l ->
       (match v2 with
        | OVALUE_Int r ->
          ret (Obj.magic coq_Monad_itree) (OVALUE_Int (Int64.shru l r))
        | _ ->
          raise
            (coq_ReSum_inr (Obj.magic __)
              (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
              (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
              (coq_ReSum_inr (Obj.magic __)
                (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                (coq_ReSum_inr (Obj.magic __)
                  (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                  (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                  (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
            ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
     | _ ->
       raise
         (coq_ReSum_inr (Obj.magic __)
           (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
           (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
           (coq_ReSum_inr (Obj.magic __)
             (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
             (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
             (coq_ReSum_inr (Obj.magic __)
               (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
               (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
               (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
         ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
  | Sar ->
    (match v1 with
     | OVALUE_Int l ->
       (match v2 with
        | OVALUE_Int r ->
          ret (Obj.magic coq_Monad_itree) (OVALUE_Int (Int64.shr l r))
        | _ ->
          raise
            (coq_ReSum_inr (Obj.magic __)
              (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
              (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
              (coq_ReSum_inr (Obj.magic __)
                (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                (coq_ReSum_inr (Obj.magic __)
                  (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                  (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                  (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
            ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))
     | _ ->
       raise
         (coq_ReSum_inr (Obj.magic __)
           (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
           (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
           (coq_ReSum_inr (Obj.magic __)
             (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
             (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
             (coq_ReSum_inr (Obj.magic __)
               (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
               (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
               (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
         ('e'::('r'::('r'::(':'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('t'::('y'::('p'::('e'::('s'::(' '::('f'::('o'::('r'::(' '::('b'::('i'::('n'::('a'::('r'::('y'::(' '::('o'::('p'::('e'::('r'::('a'::('n'::('d'::[])))))))))))))))))))))))))))))))))))))))))))

(** val fcall_return_or_fail :
    expr -> ovalue list -> (__ coq_OatE, ovalue) itree **)

let fcall_return_or_fail id0 args0 =
  match id0 with
  | Id i ->
    ITree.trigger
      (subevent
        (coq_ReSum_inl (Obj.magic __)
          (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0)) (fun _ _ _ ->
          coq_Inl_sum1) __ __ __
          (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __)) (OCall (i,
        args0)))
  | _ ->
    raise
      (coq_ReSum_inr (Obj.magic __)
        (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
        (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
        (coq_ReSum_inr (Obj.magic __)
          (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
          (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
          (coq_ReSum_inr (Obj.magic __)
            (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
            (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
            (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
      ('e'::('r'::('r'::(':'::(' '::('c'::('a'::('n'::('\''::('t'::(' '::('c'::('a'::('l'::('l'::(' '::('a'::(' '::('t'::('h'::('i'::('n'::('g'::(' '::('t'::('h'::('a'::('t'::('\''::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('f'::('u'::('n'::('c'::('!'::[]))))))))))))))))))))))))))))))))))))))))))

(** val denote_expr : expr -> (__ coq_OatE, ovalue) itree **)

let rec denote_expr = function
| CBool b -> ret (Obj.magic coq_Monad_itree) (OVALUE_Bool b)
| CInt i -> ret (Obj.magic coq_Monad_itree) (OVALUE_Int i)
| CStr s -> ret (Obj.magic coq_Monad_itree) (OVALUE_Str s)
| Bop (op, l_exp, r_exp) ->
  let l = elt_of l_exp in
  let r = elt_of r_exp in
  bind (Obj.magic coq_Monad_itree) (denote_expr l) (fun l' ->
    bind (Obj.magic coq_Monad_itree) (denote_expr r) (fun r' ->
      denote_bop op l' r'))
| Uop (op, n) ->
  let e' = elt_of n in
  bind (Obj.magic coq_Monad_itree) (denote_expr e') (fun v -> denote_uop op v)
| Id i ->
  ITree.trigger
    (subevent
      (coq_ReSum_inr (Obj.magic __)
        (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
        (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
        (coq_ReSum_inl (Obj.magic __)
          (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
          (Obj.magic (fun _ _ _ -> coq_Inl_sum1)) __ __ __
          (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __)))
      (OLocalRead i))
| Call (f, args0) ->
  let f_id = f.elt in
  bind (Obj.magic coq_Monad_itree)
    (map_monad (Obj.magic coq_Monad_itree) (fun e0 -> denote_expr e0.elt)
      args0) (fun args' ->
    bind (Obj.magic coq_Monad_itree) (fcall_return_or_fail f_id args')
      (fun f_ret ->
      match f_ret with
      | OVALUE_Void ->
        raise
          (coq_ReSum_inr (Obj.magic __)
            (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
            (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
            (coq_ReSum_inr (Obj.magic __)
              (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
              (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
              (coq_ReSum_inr (Obj.magic __)
                (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
          ('e'::('r'::('r'::(':'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('v'::('o'::('i'::('d'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::('c'::('a'::('l'::('l'::(' '::('i'::('n'::(' '::('a'::('n'::(' '::('e'::('x'::('p'::('r'::('e'::('s'::('s'::('i'::('o'::('n'::[]))))))))))))))))))))))))))))))))))))))))))))))))
      | _ -> ret (Obj.magic coq_Monad_itree) f_ret))
| _ ->
  raise
    (coq_ReSum_inr (Obj.magic __)
      (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
      (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
      (coq_ReSum_inr (Obj.magic __)
        (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
        (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
        (coq_ReSum_inr (Obj.magic __)
          (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
          (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
          (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
    ('e'::('r'::('r'::(':'::(' '::('u'::('n'::('i'::('m'::('p'::('l'::('e'::('m'::('e'::('n'::('t'::('e'::('d'::[]))))))))))))))))))

(** val seq :
    stmt node list -> (stmt -> (__ coq_OatE, (unit, 'a1) sum) itree) -> (__
    coq_OatE, (unit, 'a1) sum) itree **)

let seq l f =
  let base = ret coq_Monad_itree (Coq_inl ()) in
  let combine = fun acc hd ->
    bind coq_Monad_itree (Obj.magic f hd.elt) (fun v ->
      match v with
      | Coq_inl _ -> acc
      | Coq_inr v0 -> ret coq_Monad_itree (Coq_inr v0))
  in
  fold_left (Obj.magic combine) l (Obj.magic base)

type stmt_t = (unit, ovalue) sum

type cont_stmt = (unit, stmt_t) sum

(** val coq_while :
    (__ coq_OatE, (unit, stmt_t) sum) itree -> (__ coq_OatE, stmt_t) itree **)

let coq_while step =
  iter (Obj.magic __) (fun _ _ ->
    coq_Iter_Kleisli (Obj.magic (fun _ _ -> coq_MonadIter_itree))) __ __
    (fun _ -> Obj.magic step) ()

(** val end_loop : (__ coq_OatE, (unit, stmt_t) sum) itree **)

let end_loop =
  ret (Obj.magic coq_Monad_itree) (Coq_inr (Coq_inl ()))

(** val cont_loop_silent : (__ coq_OatE, (unit, stmt_t) sum) itree **)

let cont_loop_silent =
  ret (Obj.magic coq_Monad_itree) (Coq_inl ())

(** val cont_loop_end : ovalue -> (__ coq_OatE, (unit, stmt_t) sum) itree **)

let cont_loop_end v =
  ret (Obj.magic coq_Monad_itree) (Coq_inr (Coq_inr v))

(** val for_loop_pre : vdecl list -> (__ coq_OatE, unit) itree **)

let for_loop_pre decl =
  bind (Obj.magic coq_Monad_itree)
    (map_monad (Obj.magic coq_Monad_itree) (fun vdec ->
      let e = denote_expr (snd vdec).elt in
      bind (Obj.magic coq_Monad_itree) (Obj.magic e) (fun v ->
        ITree.trigger
          (subevent
            (coq_ReSum_inr (Obj.magic __)
              (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
              (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
              (coq_ReSum_inl (Obj.magic __)
                (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                (Obj.magic (fun _ _ _ -> coq_Inl_sum1)) __ __ __
                (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __)))
            (OLocalWrite ((fst vdec), v))))) decl) (fun _ ->
    ret (Obj.magic coq_Monad_itree) ())

(** val lift_eff :
    (__ coq_OatE, 'a1) itree -> (__ coq_OatE, (unit, 'a1) sum) itree **)

let lift_eff t0 =
  bind (Obj.magic coq_Monad_itree) (Obj.magic t0) (fun t'0 ->
    ret (Obj.magic coq_Monad_itree) (Coq_inr t'0))

(** val denote_stmt : stmt -> (__ coq_OatE, (unit, ovalue) sum) itree **)

let rec denote_stmt = function
| Assn (target, source) ->
  let tgt = elt_of target in
  let src = elt_of source in
  (match tgt with
   | Id i ->
     bind (Obj.magic coq_Monad_itree) (Obj.magic denote_expr src) (fun v ->
       bind (Obj.magic coq_Monad_itree)
         (ITree.trigger
           (subevent
             (coq_ReSum_inr (Obj.magic __)
               (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
               (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
               (coq_ReSum_inl (Obj.magic __)
                 (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                 (Obj.magic (fun _ _ _ -> coq_Inl_sum1)) __ __ __
                 (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __)))
             (OLocalWrite (i, v)))) (fun _ ->
         ret (Obj.magic coq_Monad_itree) (Coq_inl ())))
   | _ ->
     raise
       (coq_ReSum_inr (Obj.magic __)
         (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
         (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
         (coq_ReSum_inr (Obj.magic __)
           (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
           (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
           (coq_ReSum_inr (Obj.magic __)
             (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
             (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
             (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
       ('e'::('r'::('r'::(':'::(' '::('a'::('s'::('s'::('i'::('g'::('n'::('m'::('e'::('n'::('t'::(' '::('t'::('o'::(' '::('a'::(' '::('n'::('o'::('n'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::(' '::('t'::('a'::('r'::('g'::('e'::('t'::[])))))))))))))))))))))))))))))))))))))))))
| Decl v ->
  let (id0, node0) = v in
  let src = elt_of node0 in
  bind (Obj.magic coq_Monad_itree) (Obj.magic denote_expr src) (fun v0 ->
    bind (Obj.magic coq_Monad_itree)
      (ITree.trigger
        (subevent
          (coq_ReSum_inr (Obj.magic __)
            (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
            (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
            (coq_ReSum_inl (Obj.magic __)
              (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
              (Obj.magic (fun _ _ _ -> coq_Inl_sum1)) __ __ __
              (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __)))
          (OLocalWrite (id0, v0)))) (fun _ ->
      ret (Obj.magic coq_Monad_itree) (Coq_inl ())))
| Return e ->
  (match e with
   | Some r ->
     bind (Obj.magic coq_Monad_itree) (Obj.magic denote_expr r.elt)
       (fun rv -> ret (Obj.magic coq_Monad_itree) (Coq_inr rv))
   | None -> ret (Obj.magic coq_Monad_itree) (Coq_inr OVALUE_Void))
| If (cond, p, f) ->
  let e_cond = cond.elt in
  bind (Obj.magic coq_Monad_itree) (Obj.magic denote_expr e_cond)
    (fun exp0 ->
    match exp0 with
    | OVALUE_Bool bv -> if bv then seq p denote_stmt else seq f denote_stmt
    | _ ->
      raise
        (coq_ReSum_inr (Obj.magic __)
          (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
          (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
          (coq_ReSum_inr (Obj.magic __)
            (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
            (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
            (coq_ReSum_inr (Obj.magic __)
              (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
              (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
              (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
        ('e'::('r'::('r'::[]))))
| While (cond, stmts) ->
  coq_while
    (bind (Obj.magic coq_Monad_itree) (Obj.magic denote_expr cond.elt)
      (fun x ->
      match x with
      | OVALUE_Bool bv ->
        if bv then lift_eff (seq stmts denote_stmt) else end_loop
      | _ ->
        raise
          (coq_ReSum_inr (Obj.magic __)
            (Obj.magic (fun _ _ _ x0 x1 _ -> coq_Cat_IFun x0 x1))
            (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
            (coq_ReSum_inr (Obj.magic __)
              (Obj.magic (fun _ _ _ x0 x1 _ -> coq_Cat_IFun x0 x1))
              (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
              (coq_ReSum_inr (Obj.magic __)
                (Obj.magic (fun _ _ _ x0 x1 _ -> coq_Cat_IFun x0 x1))
                (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
          ('e'::('r'::('r'::[])))))
| SCall (invoke, args0) ->
  let f_id = invoke.elt in
  bind (Obj.magic coq_Monad_itree)
    (map_monad (Obj.magic coq_Monad_itree) (fun e ->
      Obj.magic denote_expr e.elt) args0) (fun args' ->
    bind (Obj.magic coq_Monad_itree)
      (Obj.magic fcall_return_or_fail f_id args') (fun _ ->
      ret (Obj.magic coq_Monad_itree) (Coq_inl ())))
| _ ->
  raise
    (coq_ReSum_inr (Obj.magic __)
      (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
      (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
      (coq_ReSum_inr (Obj.magic __)
        (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
        (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
        (coq_ReSum_inr (Obj.magic __)
          (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
          (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
          (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
    ('u'::('n'::('i'::('m'::('p'::('l'::('e'::('m'::('e'::('n'::('t'::('e'::('d'::[])))))))))))))

(** val denote_block_acc :
    (__ coq_OatE, (unit, ovalue) sum) itree -> block -> (__ coq_OatE, ovalue)
    itree **)

let rec denote_block_acc denoted = function
| [] ->
  bind (Obj.magic coq_Monad_itree) (Obj.magic denoted) (fun v ->
    match v with
    | Coq_inl _ -> ret (Obj.magic coq_Monad_itree) OVALUE_Void
    | Coq_inr v0 -> ret (Obj.magic coq_Monad_itree) v0)
| h :: t0 ->
  let denoted_so_far =
    bind (Obj.magic coq_Monad_itree) denoted (fun v ->
      match v with
      | Coq_inl _ -> denote_stmt h.elt
      | Coq_inr _ ->
        raise
          (coq_ReSum_inr (Obj.magic __)
            (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
            (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
            (coq_ReSum_inr (Obj.magic __)
              (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
              (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
              (coq_ReSum_inr (Obj.magic __)
                (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
                (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
                (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
          ('e'::('r'::('r'::('o'::('r'::(':'::(' '::('t'::('e'::('r'::('m'::('i'::('n'::('a'::('t'::('o'::('r'::(' '::('a'::('l'::('r'::('e'::('a'::('d'::('y'::(' '::('s'::('e'::('e'::('n'::(' '::('-'::(' '::('c'::('a'::('n'::('n'::('o'::('t'::(' '::('d'::('e'::('n'::('o'::('t'::('e'::(' '::('a'::('n'::('o'::('t'::('h'::('e'::('r'::(' '::('s'::('t'::('m'::('t'::(' '::('i'::('n'::(' '::('a'::(' '::('b'::('l'::('o'::('c'::('k'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  in
  denote_block_acc denoted_so_far t0

(** val denote_block : block -> (__ coq_OatE, ovalue) itree **)

let denote_block b =
  denote_block_acc (ret (Obj.magic coq_Monad_itree) (Coq_inl ())) b

type fdecl_denotation = ovalue list -> (__ coq_OatE, ovalue) itree

(** val combine_lists_err :
    'a1 list -> 'a2 list -> (char list, ('a1 * 'a2) list) sum **)

let rec combine_lists_err l1 l2 =
  match l1 with
  | [] ->
    (match l2 with
     | [] -> ret (Obj.magic coq_Monad_err) []
     | _ :: _ -> ret (Obj.magic coq_Monad_err) [])
  | x :: xs ->
    (match l2 with
     | [] -> ret (Obj.magic coq_Monad_err) []
     | y :: ys ->
       bind (Obj.magic coq_Monad_err) (combine_lists_err xs ys) (fun l ->
         ret (Obj.magic coq_Monad_err) ((x, y) :: l)))

type function_denotation = ovalue list -> (__ coq_OatE, ovalue) itree

(** val t : (id * ovalue) list -> (__ coq_OStackE, unit) itree **)

let t bs =
  ITree.trigger
    (subevent (coq_ReSum_id (fun _ _ -> coq_Id_IFun) __) (OStackPush bs))

(** val t' : (id * ovalue) list -> block -> (__ coq_OatE, ovalue) itree **)

let t' bs b =
  let basic = denote_block b in
  let t'' =
    ITree.trigger
      (subevent
        (coq_ReSum_inr (Obj.magic __) (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0)
          (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
          (coq_ReSum_inr (Obj.magic __) (fun _ _ _ x x0 _ ->
            coq_Cat_IFun x x0) (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __
            __
            (coq_ReSum_inl (Obj.magic __) (fun _ _ _ x x0 _ ->
              coq_Cat_IFun x x0) (Obj.magic (fun _ _ _ -> coq_Inl_sum1)) __
              __ __ (coq_ReSum_id (fun _ _ -> coq_Id_IFun) __)))) (OStackPush
        bs))
  in
  bind (Obj.magic coq_Monad_itree) (Obj.magic t'') (fun _ -> basic)

(** val denote_fdecl : fdecl -> function_denotation **)

let denote_fdecl df arg =
  let a = combine_lists_err (map snd df.args) arg in
  let b = ret coq_Monad_itree in
  let c =
    lift_err
      (coq_ReSum_inr (Obj.magic __) (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0)
        (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
        (coq_ReSum_inr (Obj.magic __) (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0)
          (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
          (coq_ReSum_inr (Obj.magic __) (fun _ _ _ x x0 _ ->
            coq_Cat_IFun x x0) (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __
            __ (coq_ReSum_id (fun _ _ -> coq_Id_IFun) __)))) b a
  in
  let f = fun bs ->
    ITree.trigger
      (subevent
        (coq_ReSum_inr (Obj.magic __) (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0)
          (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
          (coq_ReSum_inr (Obj.magic __) (fun _ _ _ x x0 _ ->
            coq_Cat_IFun x x0) (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __
            __
            (coq_ReSum_inl (Obj.magic __) (fun _ _ _ x x0 _ ->
              coq_Cat_IFun x x0) (Obj.magic (fun _ _ _ -> coq_Inl_sum1)) __
              __ __ (coq_ReSum_id (fun _ _ -> coq_Id_IFun) __)))) (OStackPush
        bs))
  in
  let f' = fun _ ->
    ITree.trigger
      (subevent
        (coq_ReSum_inr (Obj.magic __) (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0)
          (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
          (coq_ReSum_inr (Obj.magic __) (fun _ _ _ x x0 _ ->
            coq_Cat_IFun x x0) (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __
            __
            (coq_ReSum_inl (Obj.magic __) (fun _ _ _ x x0 _ ->
              coq_Cat_IFun x x0) (Obj.magic (fun _ _ _ -> coq_Inl_sum1)) __
              __ __ (coq_ReSum_id (fun _ _ -> coq_Id_IFun) __)))) OStackPop)
  in
  bind (Obj.magic coq_Monad_itree) (Obj.magic c) (fun bs ->
    bind (Obj.magic coq_Monad_itree) (Obj.magic f bs) (fun _ ->
      bind (Obj.magic coq_Monad_itree) (denote_block df.body) (fun rv ->
        bind (Obj.magic coq_Monad_itree) (Obj.magic f' ()) (fun _ ->
          ret (Obj.magic coq_Monad_itree) rv))))

(** val lookup : id -> (id * 'a1) list -> 'a1 option **)

let rec lookup id0 = function
| [] -> None
| h :: t0 -> if eqb (fst h) id0 then Some (snd h) else lookup id0 t0

(** val interp_away_calls :
    (id * function_denotation) list -> char list -> ovalue list -> (__
    coq_OatE', value) itree **)

let interp_away_calls fdecls id0 args0 =
  mrec (fun _ call ->
    let OCall (id1, args1) = call in
    (match lookup id1 fdecls with
     | Some fdecl0 -> Obj.magic fdecl0 args1
     | None ->
       raise
         (coq_ReSum_inr (Obj.magic __)
           (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
           (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
           (coq_ReSum_inr (Obj.magic __)
             (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
             (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
             (coq_ReSum_inr (Obj.magic __)
               (Obj.magic (fun _ _ _ x x0 _ -> coq_Cat_IFun x x0))
               (Obj.magic (fun _ _ _ -> coq_Inr_sum1)) __ __ __
               (coq_ReSum_id (Obj.magic (fun _ _ -> coq_Id_IFun)) __))))
         ('e'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::('c'::('a'::('l'::('l'::(' '::('n'::('o'::('t'::(' '::('i'::('n'::(' '::('c'::('o'::('n'::('t'::('e'::('x'::('t'::[])))))))))))))))))))))))))))))))))))))
    (OCall (id0, args0))
