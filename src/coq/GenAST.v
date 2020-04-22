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

Section ShowInstances.
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

End ShowInstances.

Section TypGenerators.
  (* TODO: These currently don't generate pointer types either. *)

  (* Not sized in the QuickChick sense, sized in the LLVM sense. *)
  Definition gen_sized_typ_0 (ctx : list (ident * typ)) : G typ :=
    oneOf_ failGen
          (* TODO: add identified here *)
          ( (* (ret TYPE_Identified <*> oneOf_ failGen (map (fun '(i,_) => ret i) ctx)) :: *)
           (map ret
                [ TYPE_I 1
                ; TYPE_I 8
                ; TYPE_I 32
                ; TYPE_I 64
                (* TODO: Generate floats and stuff *)
                (* TODO: Could generate TYPE_Identified if we filter for sized types *)
                (* ; TYPE_Half *)
                (* ; TYPE_Double *)
                (* ; TYPE_X86_fp80 *)
                (* ; TYPE_Fp128 *)
                (* ; TYPE_Ppc_fp128 *)
                (* ; TYPE_Metadata *)
                (* ; TYPE_X86_mmx *)
                (* ; TYPE_Opaque *)
                ])).

  Program Fixpoint gen_sized_typ_size (sz : nat) (ctx : list (ident * typ)) {measure sz} : G typ :=
    match sz with
    | O => gen_sized_typ_0 ctx
    | (S sz') => oneOf_ failGen
                      [ gen_sized_typ_0 ctx
                      (* Might want to restrict the size to something reasonable *)
                      ; ret TYPE_Array <*> arbitrary <*> gen_sized_typ_size sz' ctx
                      ; ret TYPE_Vector <*> arbitrary <*> gen_sized_typ_size sz' ctx
                      ; let n := Nat.div sz 2 in ret TYPE_Function <*> gen_sized_typ_size n ctx <*> listOf (gen_sized_typ_size n ctx)
                      ; ret TYPE_Struct <*> listOf (gen_sized_typ_size sz' ctx)
                      ; ret TYPE_Packed_struct <*> listOf (gen_sized_typ_size sz' ctx)
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

  Definition gen_sized_typ (ctx : list (ident * typ)) : G typ
    := sized (fun sz => gen_sized_typ_size sz ctx).

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
                (* TODO: Generate floats and stuff *)
                (* ; TYPE_Half *)
                (* ; TYPE_Double *)
                (* ; TYPE_X86_fp80 *)
                (* ; TYPE_Fp128 *)
                (* ; TYPE_Ppc_fp128 *)
                (* ; TYPE_Metadata *)
                (* ; TYPE_X86_mmx *)
                (* ; TYPE_Opaque *)
                ])).

  (* TODO: This should probably be mutually recursive with
     gen_sized_typ since pointers of any type are considered sized *)
  Program Fixpoint gen_typ_size (sz : nat) (ctx : list (ident * typ)) {measure sz} : G typ :=
    match sz with
    | 0%nat => gen_typ_0 ctx
    | (S sz') => oneOf_ failGen
                      [ gen_typ_0 ctx
                      (* Might want to restrict the size to something reasonable *)
                      (* TODO: Make sure length of Array >= 0, and length of vector >= 1 *)
                      ; ret TYPE_Array <*> arbitrary <*> gen_sized_typ_size sz' ctx
                      ; ret TYPE_Vector <*> arbitrary <*> gen_sized_typ_size sz' ctx
                      ; let n := Nat.div sz 2 in
                        ret TYPE_Function <*> gen_typ_size n ctx <*> listOf (gen_sized_typ_size n ctx)
                      ; ret TYPE_Struct <*> listOf (gen_sized_typ_size sz' ctx)
                      ; ret TYPE_Packed_struct <*> listOf (gen_sized_typ_size sz' ctx)
                      ]
    end.
  Next Obligation.
    cbn.
    assert (0 <= 1)%nat by omega.
    pose proof Nat.divmod_spec sz' 1 0 0 H.
    cbn; destruct (Nat.divmod sz' 1 0 0).
    cbn; omega.
  Qed.

  Definition gen_typ (ctx : list (ident * typ)) : G typ
    := sized (fun sz => gen_typ_size sz ctx).

  (* TODO: look up identifiers *)
  (* Types for operation expressions *)
  Definition gen_op_typ : G typ :=
    oneOf_ failGen
           (map ret
                [ TYPE_I 1
                ; TYPE_I 8
                ; TYPE_I 32
                ; TYPE_I 64
                (* TODO: Generate floats and stuff *)
                (* ; TYPE_Half *)
                (* ; TYPE_Double *)
                (* ; TYPE_X86_fp80 *)
                (* ; TYPE_Fp128 *)
                (* ; TYPE_Ppc_fp128 *)
                (* ; TYPE_Metadata *)
                (* ; TYPE_X86_mmx *)
                (* ; TYPE_Opaque *)
                ]).

  (* TODO: look up identifiers *)
  Definition gen_int_typ : G typ :=
    oneOf_ failGen
           (map ret
                [ TYPE_I 1
                ; TYPE_I 8
                ; TYPE_I 32
                ; TYPE_I 64
                ]).

End TypGenerators.

Section ExpGenerators.
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

  Definition gen_icmp : G icmp :=
    oneOf_ failGen
           (map ret
                [ Eq; Ne; Ugt; Uge; Ult; Ule; Sgt; Sge; Slt; Sle]).

  (* Generate an expression of a given type *)
  (* Context should probably not have duplicate ids *)
  (* May want to decrease size more for arrays and vectors *)
  (* TODO: Need a restricted version of the type generator for this? *)
  (* TODO: look up named types from the context *)
  (* TODO: generate conversions? *)
  Program Fixpoint gen_exp_size (sz : nat) (ctx : list (ident * typ)) (t : typ) {measure sz} : G (exp typ) :=
    match sz with
    | 0%nat =>
      match t with
      | TYPE_I n                  => ret EXP_Integer <*> arbitrary
      | TYPE_Pointer t            => failGen (* Only pointer type expressions might be conversions? Maybe GEP? *)
      | TYPE_Void                 => failGen (* There should be no expressions of type void *)
      | TYPE_Function ret args    => failGen (* No expressions of function type *)
      | TYPE_Opaque               => failGen (* TODO: not sure what these should be... *)
      | TYPE_Half                 => failGen
      | TYPE_Float                => failGen
      | TYPE_Double               => failGen
      | TYPE_X86_fp80             => failGen
      | TYPE_Fp128                => failGen
      | TYPE_Ppc_fp128            => failGen
      | TYPE_Metadata             => failGen
      | TYPE_X86_mmx              => failGen
      | TYPE_Array sz t           => failGen
      | TYPE_Struct fields        => failGen
      | TYPE_Packed_struct fields => failGen
      | TYPE_Vector sz t          => failGen
      | TYPE_Identified id        => failGen
      end
    | (S sz') =>
      let gens :=
          match t with
          | TYPE_I isz =>
            (* TODO: If I1 also allow ICmp and FCmp *)
            [let n := Nat.div sz 2 in
             ret OP_IBinop <*> gen_ibinop <*> ret t <*> gen_exp_size n ctx t <*> gen_exp_size n ctx t]
          | TYPE_Array n t =>
            [es <- vectorOf (Z.to_nat n) (gen_exp_size sz' ctx t);;
             ret (EXP_Array (map (fun e => (t, e)) es))]
          | TYPE_Vector n t =>
            [es <- vectorOf (Z.to_nat n) (gen_exp_size sz' ctx t);;
             ret (EXP_Array (map (fun e => (t, e)) es))]
          | TYPE_Struct fields =>
            (* Should we divide size evenly amongst components of struct? *)
            [tes <- map_monad (fun t => e <- gen_exp_size sz' ctx t;; ret (t, e)) fields;;
             ret (EXP_Struct tes)]
          | TYPE_Packed_struct fields =>
            (* Should we divide size evenly amongst components of struct? *)
            [tes <- map_monad (fun t => e <- gen_exp_size sz' ctx t;; ret (t, e)) fields;;
             ret (EXP_Packed_struct tes)]
          | TYPE_Pointer t         => [failGen] (* GEP? *)
          | TYPE_Void              => [failGen] (* No void type expressions *)
          | TYPE_Function ret args => [failGen] (* These shouldn't exist, I think *)
          | TYPE_Opaque            => [failGen] (* TODO: not sure what these should be... *)
          | TYPE_Half              => [failGen]
          | TYPE_Float             => [failGen]
          | TYPE_Double            => [failGen]
          | TYPE_X86_fp80          => [failGen]
          | TYPE_Fp128             => [failGen]
          | TYPE_Ppc_fp128         => [failGen]
          | TYPE_Metadata          => [failGen]
          | TYPE_X86_mmx           => [failGen]
          | TYPE_Identified id     => [failGen] (* TODO: Involves lookup *)
          end
      in
      (* short-circuit to size 0 *)
      oneOf_ failGen (gen_exp_size 0 ctx t :: gens)
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
  Next Obligation.
    cbn.
    assert (0 <= 1)%nat by omega.
    pose proof Nat.divmod_spec sz' 1 0 0 H.
    cbn; destruct (Nat.divmod sz' 1 0 0).
    cbn; omega.
  Qed.

  Definition gen_exp (ctx : list (ident * typ)) (t : typ) : G (exp typ)
    := sized (fun sz => gen_exp_size sz ctx t).

  Definition gen_texp (ctx : list (ident * typ)) : G (texp typ)
    := t <- gen_typ ctx;;
       e <- gen_exp ctx t;;
       ret (t, e).

  Definition gen_op (ctx : list (ident * typ)) (t : typ) : G (exp typ)
    := sized (fun sz =>
                match t with
                | TYPE_I isz =>
                  (* TODO: If I1 also allow ICmp and FCmp *)
                  let n := Nat.div sz 2 in
                  ret OP_IBinop <*> gen_ibinop <*> ret t <*> gen_exp_size n ctx t <*> gen_exp_size n ctx t
                | _ => failGen
                end).

  Definition gen_int_texp (ctx : list (ident * typ)) : G (texp typ)
    := t <- gen_int_typ;;
       e <- gen_exp ctx t;;
       ret (t, e).

End ExpGenerators.

Section InstrGenerators.

  (* TODO: move this *)
  Definition genInt : G int
    := fmap Int.repr (arbitrary : G Z).

  Instance GenInt : Gen int
    := Build_Gen int genInt.

  (* TODO: move this. Also give a less confusing name because genOption is a thing? *)
  Definition gen_option {A} (g : G A) : G (option A)
    := freq_ failGen [(1%nat, ret None); (7%nat, liftM Some g)].

  Definition gen_instr_size (ctx : list (ident * typ)) : G (instr typ) :=
    oneOf_ failGen
           [ ret (INSTR_Comment "test")
           ; t <- gen_op_typ;; ret INSTR_Op <*> gen_op ctx t
           ; ret INSTR_Alloca <*> gen_sized_typ ctx <*> gen_option (gen_int_texp ctx) <*> arbitrary
           (* TODO: Generate calls *)
           ; ret INSTR_Load <*> arbitrary <*> gen_
           ].

  (* TODO: Generate instructions with ids *)
  (* Make sure we can add these new ids to the context! *)

  Inductive instr : Set :=
| INSTR_Comment (msg:string)
| INSTR_Op   (op:exp)                        (* INVARIANT: op must be of the form SV (OP_ ...) *)
| INSTR_Call (fn:texp) (args:list texp)      (* CORNER CASE: return type is void treated specially *)
| INSTR_Alloca (t:T) (nb: option texp) (align:option int)
| INSTR_Load  (volatile:bool) (t:T) (ptr:texp) (align:option int)
| INSTR_Store (volatile:bool) (val:texp) (ptr:texp) (align:option int)
| INSTR_Fence
| INSTR_AtomicCmpXchg
| INSTR_AtomicRMW
| INSTR_Unreachable
| INSTR_VAArg
| INSTR_LandingPad
End InstrGenerators.

Section Helpers.
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

  (* TODO: incomplete. Should typecheck *)
  Fixpoint well_formed_op (ctx : list (ident * typ)) (op : exp typ) : bool :=
    match op with
    | OP_IBinop iop t v1 v2              => true 
    | OP_ICmp cmp t v1 v2                => true
    | OP_FBinop fop fm t v1 v2           => true
    | OP_FCmp cmp t v1 v2                => true
    | OP_Conversion conv t_from v t_to   => true
    | OP_GetElementPtr t ptrval idxs     => true
    | OP_ExtractElement vec idx          => true
    | OP_InsertElement vec elt idx       => true
    | OP_ShuffleVector vec1 vec2 idxmask => true
    | OP_ExtractValue vec idxs           => true
    | OP_InsertValue vec elt idxs        => true
    | OP_Select cnd v1 v2                => true
    | OP_Freeze v                        => true
    | _                                  => false
    end.
  
  Fixpoint well_formed_instr (ctx : list (ident * typ)) (i : instr typ) : bool :=
    match i with
    | INSTR_Comment msg => true
    | INSTR_Op op => well_formed_op ctx op
    | INSTR_Call fn args => _
    | INSTR_Alloca t nb align => is_sized_typ ctx t (* The alignment may not be greater than 1 << 29. *)
    | INSTR_Load volatile t ptr align => _
    | INSTR_Store volatile val ptr align => _
    | INSTR_Fence => _
    | INSTR_AtomicCmpXchg => _
    | INSTR_AtomicRMW => _
    | INSTR_Unreachable => _
    | INSTR_VAArg => _
    | INSTR_LandingPad => _
    end.
End Helpers.

(* Graveyard *)

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
