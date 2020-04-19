From QuickChick Require Import QuickChick GenLow.
From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".

From ExtLib.Structures Require Export
     Functor Applicative Monads.

From Vellvm Require Import LLVMAst Util.
Require Import Integers Floats.

Require Import List.

Import ListNotations.
Import MonadNotation.
Import ApplicativeNotation.

From Coq Require Import
     ZArith List String Omega Bool.Bool.

Open Scope Z_scope.
Print typ.

Check oneof.
Check arbitrary.
Search G (list _).

(* Generate a type of size 0 *)
Definition gen_typ_0 (ctx : list (ident * typ)) : G typ :=
  oneOf_ failGen
        ((ret TYPE_Identified <*> oneOf_ failGen (map (fun '(i,_) => ret i) ctx)) ::
         (map ret
              [ TYPE_I 1
              ; TYPE_I 8
              ; TYPE_I 32
              ; TYPE_I 64
              ; TYPE_Void
              ; TYPE_Half
              ; TYPE_Double
              ; TYPE_X86_fp80
              ; TYPE_Fp128
              ; TYPE_Ppc_fp128
              ; TYPE_Metadata
              ; TYPE_X86_mmx
              ; TYPE_Opaque
              ])).

Program Fixpoint gen_typ_size (sz : nat) (ctx : list (ident * typ)) {measure sz} : G typ :=
  match sz with
  | 0%nat => gen_typ_0 ctx
  | (S sz') => oneOf_ failGen
                    [ gen_typ_0 ctx
                    (* Might want to restrict the size to something reasonable *)
                    ; ret TYPE_Array <*> arbitrary <*> gen_typ_size sz' ctx
                    ; ret TYPE_Vector <*> arbitrary <*> gen_typ_size sz' ctx
                    ; let n := Nat.div sz 2 in ret TYPE_Function <*> gen_typ_size n ctx <*> listOf (gen_typ_size n ctx)
                    ; ret TYPE_Struct <*> listOf (gen_typ_size sz' ctx)
                    ; ret TYPE_Packed_struct <*> listOf (gen_typ_size sz' ctx)
                    ]
  end.
Next Obligation.
  cbn.
  assert (0 <= 1)%nat by omega.
  pose proof Nat.divmod_spec sz' 1 0 0 H.
  cbn; destruct (Nat.divmod sz' 1 0 0).
  cbn; omega.
Qed.
Next Obligation.
  cbn.
  assert (0 <= 1)%nat by omega.
  pose proof Nat.divmod_spec sz' 1 0 0 H.
  cbn; destruct (Nat.divmod sz' 1 0 0).
  cbn; omega.
Qed.

Definition gen_typ (ctx : list (ident * typ)) : G typ
  := sized (fun sz => gen_typ_size sz ctx).

Fixpoint max_nat_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | x::rest => max x (max_nat_list rest)
  end.

(* TODO: how big should lists be? *)
Fixpoint sizeof_typ (t : typ) : nat :=
  match t with
  | TYPE_Pointer t            => S (sizeof_typ t)
  | TYPE_Array sz t           => S (sizeof_typ t)
  | TYPE_Function ret args    => max (sizeof_typ ret) (max_nat_list (map sizeof_typ args))
  | TYPE_Struct fields        => max_nat_list (map sizeof_typ fields)
  | TYPE_Packed_struct fields => max_nat_list (map sizeof_typ fields)
  | TYPE_Vector sz t          => S (sizeof_typ t)
  | _                         => 0
  end.

Require Import TypeUtil AstLib.
Require Import String.
Open Scope string_scope.

Inductive blah : Type :=
| Foo : blah
| Bar : list blah -> blah.

Check concat.
Fixpoint show_blah (b : blah) : string :=
  match b with
  | Foo => "Foo"
  | Bar bs => concat ", " (map show_blah bs)
  end.

Derive Show for raw_id.
Derive Show for ident.

Fixpoint show_typ (t : typ) : string :=
  match t with
  | TYPE_I sz                 => "TYPE_I " ++ show sz
  | TYPE_Pointer t            => "TYPE_Pointer" ++ show_typ t
  | TYPE_Void                 => "TYPE_Void"
  | TYPE_Half                 => "TYPE_Half"
  | TYPE_Float                => "TYPE_Float"
  | TYPE_Double               => "TYPE_Double"
  | TYPE_X86_fp80             => "TYPE_X86_fp80"
  | TYPE_Fp128                => "TYPE_Fp128"
  | TYPE_Ppc_fp128            => "TYPE_Ppc_fp128"
  | TYPE_Metadata             => "TYPE_Metadata"
  | TYPE_X86_mmx              => "TYPE_X86_mmx"
  | TYPE_Array sz t           => "TYPE_Array " ++ show sz ++ " " ++ show_typ t
  | TYPE_Function ret args    => "TYPE_Function " ++ show_typ ret ++ " (" ++ concat ", " (map show_typ args) ++ ")"
  | TYPE_Struct fields        => "TYPE_Struct {" ++ concat ", " (map show_typ fields) ++ "}"
  | TYPE_Packed_struct fields => "TYPE_Packed_struct {" ++ concat ", " (map show_typ fields) ++ "}"
  | TYPE_Opaque               => "TYPE_Opaque"
  | TYPE_Vector sz t          => "TYPE_Vector " ++ show sz ++ " " ++ show_typ t
  | TYPE_Identified id        => "TYPE_Identified " ++ show id
  end.

Instance showTyp:  Show typ :=
{|
  show := show_typ
|}.
Sample (gen_typ_size 4 []).

Require Import Vellvm.AstLib.

(* Definition gen_global_name : G ident := *)
(*   n <- choose (0, 10000);; *)
(*   ret (ID_Global (Name ("v" ++ show n))). *)

(* Definition gen_typ_ctx_size (sz : nat) (names : nat) : G (list (ident * typ)) *)
(*   := match sz with *)
(*      | O => ret [] *)
(*      | S x => *)
(*        n <- gen_global_name;; *)
(*        ret (n, t) *)
(*      end. *)                                                                    

(* Generate an expression of a given type *)
(* Context should probably not have duplicate ids *)
(* May want to decrease size more for arrays and vectors *)
Print exp.
Check map_monad.

Definition gen_ibinop : G ibinop :=
  oneOf_ failGen
         [ ret LLVMAst.Add <*> arbitrary <*> arbitrary
         ; ret Sub <*> arbitrary <*> arbitrary
         ; ret Mul <*> arbitrary <*> arbitrary
         ; ret Shl <*> arbitrary <*> arbitrary
         ; ret UDiv <*> arbitrary
         ; ret SDiv <*> arbitrary
         ; ret LShr <*> arbitrary
         ; ret AShr <*> arbitrary
         ; ret URem
         ; ret SRem
         ; ret And
         ; ret Or
         ; ret Xor
         ].


(* Need a restricted version of the type generator for this? *)
Program Fixpoint gen_exp_size (sz : nat) (ctx : list (ident * typ)) (t : typ) {measure sz} : G (exp typ) :=
  match sz with
  | 0%nat =>
    match t with
    | TYPE_I sz => ret EXP_Integer <*> arbitrary
    | TYPE_Pointer t => failGen (* Only pointer type expressions might be conversions? Maybe GEP? *)
    | TYPE_Void => failGen  (* There should be no expressions of type void *)
    | TYPE_Function ret args => failGen (* No expressions of function type *)
    | TYPE_Opaque => failGen (* TODO: not sure what these should be... *)
    | TYPE_Vector n t => es <- vectorOf (Z.to_nat n) (gen_exp_size (sz - 1) ctx t);; ret (EXP_Array (map (fun e => (t, e)) es))
    (* Involves lookup *)
    (* | TYPE_Identified id => _ *)
    | _ => failGen
    end

  (* Conversions? *)
  | (S sz') =>
    (* TODO: short-circuit to size 0 *)
    match t with
    | TYPE_I isz =>
      (* If I1 also allow ICmp and FCmp *)
      let n := Nat.div sz 2 in
      ret OP_IBinop <*> gen_ibinop <*> ret t <*> gen_exp_size n ctx t <*> gen_exp_size n ctx t
    | TYPE_Pointer t => _ (* GEP? *)
    | TYPE_Void => failGen (* No void type expressions *)
    | TYPE_Array n t =>
      es <- vectorOf (Z.to_nat n) (gen_exp_size sz' ctx t);;
      ret (EXP_Array (map (fun e => (t, e)) es))
    | TYPE_Vector n t =>
      es <- vectorOf (Z.to_nat n) (gen_exp_size sz' ctx t);;
      ret (EXP_Array (map (fun e => (t, e)) es))
    | TYPE_Function ret args => _
    | TYPE_Struct fields =>
      (* Should we divide size evenly amongst components of struct? *)
      tes <- map_monad (fun t => e <- gen_exp_size (sz - 1) ctx t;; ret (t, e)) fields;;
      ret (EXP_Struct tes)
    | TYPE_Packed_struct fields =>
      (* Should we divide size evenly amongst components of struct? *)
      tes <- map_monad (fun t => e <- gen_exp_size (sz - 1) ctx t;; ret (t, e)) fields;;
      ret (EXP_Packed_struct tes)
    | TYPE_Opaque => _
    | TYPE_Identified id => _
    | _ => failGen
    end
  end.
