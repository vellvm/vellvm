From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

From ExtLib.Structures Require Export
     Functor Applicative Monads.

Require Import ExtLib.Data.Monads.StateMonad.

From Vellvm Require Import LLVMAst Util AstLib TypeUtil CFG.
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

  Global Instance showTyp:  Show typ :=
    {|
    show := show_typ
    |}.

  Global Instance showBlock: Show (block typ) :=
    {|
    show := CeresSerialize.to_string 
    |}.

  Global Instance showCode: Show (code typ) :=
    {|
    show := CeresSerialize.to_string 
    |}.

  Global Instance showInstr: Show (instr typ) :=
    {|
    show := CeresSerialize.to_string
    |}.

End ShowInstances.

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

  (* TODO: Move these *)
  Fixpoint find_pred {A} (p : A -> bool) (l : list A) : option A
    := match l with
       | []   => None
       | x::xs =>
         if p x
         then Some x
         else find_pred p xs
       end.

  Fixpoint is_sized_type_h (t : typ) : bool
    := match t with
       | TYPE_I sz                 => true
       | TYPE_Pointer t            => true
       | TYPE_Void                 => false
       | TYPE_Half                 => true
       | TYPE_Float                => true
       | TYPE_Double               => true
       | TYPE_X86_fp80             => true
       | TYPE_Fp128                => true
       | TYPE_Ppc_fp128            => true
       | TYPE_Metadata             => true (* Is this right? *)
       | TYPE_X86_mmx              => true
       | TYPE_Array sz t           => is_sized_type_h t
       | TYPE_Function ret args    => false
       | TYPE_Struct fields        => true
       | TYPE_Packed_struct fields => true
       | TYPE_Opaque               => false
       | TYPE_Vector sz t          => is_sized_type_h t
       | TYPE_Identified id        => false (* Shouldn't happen *)
       end.

  (* Only works correctly if the type is well formed *)
  Definition is_sized_type (ctx : list (ident * typ)) (t : typ) : bool
    := is_sized_type_h (normalize_type ctx t).

  Definition is_int_type_h (t : typ) : bool
    := match t with
       | TYPE_I sz => true
       | _ => false
       end.

  (* Only works correctly if the type is well formed *)
  Definition is_int_type (ctx : list (ident * typ)) (t : typ) : bool
    := is_int_type_h (normalize_type ctx t).

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

  (*
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
   *)
End Helpers.

Section GenerationState.
  Record GenState :=
    mkGenState
    { num_void : nat
    ; num_raw  : nat
    ; num_blocks : nat
    ; gen_ctx : list (ident * typ)
    }.

  Definition init_GenState : GenState
    := {| num_void   := 0
        ; num_raw    := 0
        ; num_blocks := 0
        ; gen_ctx    := []
       |}.

  Definition increment_raw (gs : GenState) : GenState
    := {| num_void   := gs.(num_void)
        ; num_raw    := S gs.(num_raw)
        ; num_blocks := gs.(num_blocks)
        ; gen_ctx    := gs.(gen_ctx)
       |}.

  Definition increment_void (gs : GenState) : GenState
    := {| num_void   := S gs.(num_void)
        ; num_raw    := gs.(num_raw)
        ; num_blocks := gs.(num_blocks)
        ; gen_ctx    := gs.(gen_ctx)
       |}.

  Definition increment_blocks (gs : GenState) : GenState
    := {| num_void   := gs.(num_void)
        ; num_raw    := gs.(num_raw)
        ; num_blocks := S gs.(num_blocks)
        ; gen_ctx    := gs.(gen_ctx)
       |}.

  Definition replace_ctx (ctx : list (ident * typ)) (gs : GenState) : GenState
    := {| num_void   := gs.(num_void)
        ; num_raw    := gs.(num_raw)
        ; num_blocks := gs.(num_blocks)
        ; gen_ctx    := ctx
       |}.

  Definition GenLLVM := stateT GenState G.

  Definition get_raw (gs : GenState) : nat
    := gs.(num_raw).

  Definition get_void (gs : GenState) : nat
    := gs.(num_void).

  Definition get_blocks (gs : GenState) : nat
    := gs.(num_blocks).

  Definition new_raw_id : GenLLVM raw_id
    := n <- gets get_raw;;
       modify increment_raw;;
       ret (Name ("v" ++ show n)).

  Definition new_void_id : GenLLVM instr_id
    := n <- gets get_void;;
       modify increment_void;;
       ret (IVoid (Z.of_nat n)).

  Definition new_block_id : GenLLVM block_id
    := n <- gets get_blocks;;
       modify increment_blocks;;
       ret (Name ("b" ++ show n)).

  Definition get_ctx : GenLLVM (list (ident * typ))
    := gets (fun gs => gs.(gen_ctx)).

  Definition add_to_ctx (x : (ident * typ)) : GenLLVM  unit
    := ctx <- get_ctx;;
       let new_ctx := x :: ctx in
       modify (replace_ctx new_ctx);;
       ret tt.

  Definition append_to_ctx (vars : list (ident * typ)) : GenLLVM unit
    := ctx <- get_ctx;;
       let new_ctx := vars ++ ctx in
       modify (replace_ctx new_ctx);;
       ret tt.

  Definition reset_ctx : GenLLVM unit
    := modify (replace_ctx []);; ret tt.

  Definition oneOf_LLVM {A} (gs : list (GenLLVM A)) : GenLLVM A
    := n <- lift (choose (0, List.length gs - 1)%nat);;
       nth n gs (lift failGen).
End GenerationState.

Section TypGenerators.
  (* TODO: These currently don't generate pointer types either. *)

  (* Not sized in the QuickChick sense, sized in the LLVM sense. *)
  Definition gen_sized_typ_0 (ctx : list (ident * typ)) : G typ :=
    let sized_ctx := filter (fun '(i,t) => is_sized_type ctx t) ctx in
    let ident_gen :=
        (* Don't want to fail if there are no identifiers *)
        if (List.length sized_ctx =? 0)%nat
        then []
        else [ret TYPE_Identified <*> oneOf_ failGen (map (fun '(i,_) => ret i) sized_ctx)] in
    oneOf_ failGen
           (ident_gen ++
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
                      ; ret TYPE_Pointer <*> gen_sized_typ_size sz' ctx
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

  Definition gen_typ_non_void_0 (ctx : list (ident * typ)) : G typ :=
    oneOf_ failGen
          ((ret TYPE_Identified <*> oneOf_ failGen (map (fun '(i,_) => ret i) ctx)) ::
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
                ])).

  Program Fixpoint gen_typ_non_void_size (sz : nat) (ctx : list (ident * typ)) {measure sz} : G typ :=
    match sz with
    | 0%nat => gen_typ_non_void_0 ctx
    | (S sz') => oneOf_ failGen
                      [ gen_typ_non_void_0 ctx
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


  (* TODO: Move. Also, do I really have to define this? *)
  Fixpoint zipWith {A B C} (f : A -> B -> C) (xs : list A) (ys : list B) : list C
    := match xs, ys with
       | [], _        => []
       | _, []        => []
       | a::xs', b::ys' => f a b :: zipWith f xs' ys'
       end.

  (* TODO: Move this*)
  (* This only returns what you expect on normalized typs *)
  (* TODO: I don't think this does the right thing for pointers to
           identified types... It should be conservative and say that
           the types are *not* equal always, though.
   *)
  Program Fixpoint normalized_typ_eq (a : typ) (b : typ) {measure (sizeof_typ a)} : bool
    := match a with
       | TYPE_I sz =>
         match b with
         | TYPE_I sz' => if Z.eq_dec sz sz' then true else false
         | _ => false
         end
       | TYPE_Pointer t =>
         match b with
         | TYPE_Pointer t' => normalized_typ_eq t t'
         | _ => false
         end
       | TYPE_Void =>
         match b with
         | TYPE_Void => true
         | _ => false
         end
       | TYPE_Half =>
         match b with
         | TYPE_Half => true
         | _ => false
         end
       | TYPE_Float =>
         match b with
         | TYPE_Float => true
         | _ => false
         end
       | TYPE_Double =>
         match b with
         | TYPE_Double => true
         | _ => false
         end
       | TYPE_X86_fp80 =>
         match b with
         | TYPE_X86_fp80 => true
         | _ => false
         end
       | TYPE_Fp128 =>
         match b with
         | TYPE_Fp128 => true
         | _ => false
         end
       | TYPE_Ppc_fp128 =>
         match b with
         | TYPE_Ppc_fp128 => true
         | _ => false
         end
       | TYPE_Metadata =>
         match b with
         | TYPE_Metadata => true
         | _ => false
         end
       | TYPE_X86_mmx =>
         match b with
         | TYPE_X86_mmx => true
         | _ => false
         end
       | TYPE_Array sz t =>
         match b with
         | TYPE_Array sz' t' =>
           if Z.eq_dec sz sz'
           then normalized_typ_eq t t'
           else false
         | _ => false
         end
       | TYPE_Function ret args =>
         match b with
         | TYPE_Function ret' args' =>
           normalized_typ_eq ret ret' && forallb id (zipWith (fun a b => @normalized_typ_eq a b _) args args')
         | _ => false
         end
       | TYPE_Struct fields =>
         match b with
         | TYPE_Struct fields' => forallb id (zipWith (fun a b => @normalized_typ_eq a b _) fields fields')
         | _ => false
         end
       | TYPE_Packed_struct fields =>
         match b with
         | TYPE_Packed_struct fields' => forallb id (zipWith (fun a b => @normalized_typ_eq a b _) fields fields')
         | _ => false
         end
       | TYPE_Opaque =>
         match b with
         | TYPE_Opaque => false (* TODO: Unsure if this should compare equal *)
         | _ => false
         end
       | TYPE_Vector sz t =>
         match b with
         | TYPE_Vector sz' t' =>
           if Z.eq_dec sz sz'
           then normalized_typ_eq t t'
           else false
         | _ => false
         end
       | TYPE_Identified id => false
       end.
  Admit Obligations.

  (* Generate an expression of a given type *)
  (* Context should probably not have duplicate ids *)
  (* May want to decrease size more for arrays and vectors *)
  (* TODO: Need a restricted version of the type generator for this? *)
  (* TODO: look up named types from the context *)
  (* TODO: generate conversions? *)
  Unset Guard Checking.

  (* TODO: Move this *)
  Fixpoint replicateM {M : Type -> Type} {A} `{Monad M} (n : nat) (ma : M A) : M (list A)
    := match n with
       | O    => a <- ma;; ret [a]
       | S n' => a <- ma;; rest <- replicateM n' ma;; ret (a :: rest)
       end.

  Fixpoint gen_exp_size (sz : nat) (ctx : list (ident * typ)) (t : typ) {struct t} : G (exp typ) :=
    match sz with
    | 0%nat =>
      match t with
      | TYPE_I n                  => ret EXP_Integer <*> arbitrary
      | TYPE_Pointer t            => failGen (* Only pointer type expressions might be conversions? Maybe GEP? *)
      | TYPE_Void                 => failGen (* There should be no expressions of type void *)
      | TYPE_Function ret args    => failGen (* No expressions of function type *)
      | TYPE_Opaque               => failGen (* TODO: not sure what these should be... *)
      | TYPE_Array n t            => failGen
      | TYPE_Vector sz t          => failGen
      | TYPE_Struct fields        => failGen
      | TYPE_Packed_struct fields => failGen
      | TYPE_Identified id        =>
        match find_pred (fun '(i,t) => if Ident.eq_dec id i then true else false) ctx with
        | None => failGen
        | Some (i,t) => gen_exp_size sz ctx t
        end
      (* Not generating these types for now *)
      | TYPE_Half                 => failGen
      | TYPE_Float                => failGen
      | TYPE_Double               => failGen
      | TYPE_X86_fp80             => failGen
      | TYPE_Fp128                => failGen
      | TYPE_Ppc_fp128            => failGen
      | TYPE_Metadata             => failGen
      | TYPE_X86_mmx              => failGen
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
          | TYPE_Identified id     =>
            [match find_pred (fun '(i,t) => if Ident.eq_dec id i then true else false) ctx with
             | None => failGen
             | Some (i,t) => gen_exp_size sz ctx t
             end]
          end
      in
      (* short-circuit to size 0 *)
      oneOf_ failGen (gen_exp_size 0 ctx t :: gens)
    end.

  Definition gen_exp (ctx : list (ident * typ)) (t : typ) : G (exp typ)
    := sized (fun sz => gen_exp_size sz ctx t).

  Definition gen_texp (ctx : list (ident * typ)) : G (texp typ)
    := t <- gen_typ ctx;;
       e <- gen_exp ctx t;;
       ret (t, e).

  Definition gen_sized_texp (ctx : list (ident * typ)) : G (texp typ)
    := t <- gen_sized_typ ctx;;
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

  Definition gen_load (ctx : list (ident * typ)) : G (typ * instr typ)
    := t   <- gen_sized_typ ctx;;
       let pt := TYPE_Pointer t in
       vol <- (arbitrary : G bool);;
       ptr <- gen_exp ctx pt;;
       align <- arbitrary;;
       ret (t, INSTR_Load vol t (pt, ptr) align).

  Definition gen_store (ctx : list (ident * typ)) : G (typ * instr typ)
    := vol <- arbitrary;;
       align <- arbitrary;;

       val <- gen_sized_texp ctx;;
       let '(t, e) := val in

       let pt := TYPE_Pointer t in
       pexp <- gen_exp ctx pt;;
       let ptr := (pt, pexp) in

       ret (TYPE_Void, INSTR_Store vol val ptr align).


  (* Generate an instruction, as well as its type...

     The type is sometimes void for instructions that don't really
     compute a value, like void function calls, stores, etc.
   *)
  Definition gen_instr : GenLLVM (typ * instr typ) :=
    ctx <- get_ctx;;
    lift (oneOf_ failGen
           [ ret (TYPE_Void, INSTR_Comment "test")
           ; t <- gen_op_typ;; i <- ret INSTR_Op <*> gen_op ctx t;; ret (t, i)
           ; t <- gen_sized_typ ctx;;
             num_elems <- gen_option (gen_int_texp ctx);;
             align <- arbitrary;;
             ret (TYPE_Pointer t, INSTR_Alloca t num_elems align)
           (* TODO: Generate calls *)
           ; gen_load ctx
           ; gen_store ctx
           (* TODO: Generate atomic operations and other instructions *)
           ]).

  (* TODO: Generate instructions with ids *)
  (* Make sure we can add these new ids to the context! *)

  (* TODO: want to generate phi nodes, which might be a bit
  complicated because we need to know that an id that occurs in a
  later block is in context *)

  (* Generate a block of code, spitting out a new context. *)
  Definition gen_instr_id : GenLLVM (instr_id * instr typ)
    := '(t, instr) <- gen_instr;;
       match t with
       | TYPE_Void =>
         vid <- new_void_id;;
         ret (vid, instr)
       | _ =>
         i <- new_raw_id;;
         add_to_ctx (ID_Local i, t);;
         ret (IId i, instr)
       end.

  Fixpoint gen_code_length (n : nat) : GenLLVM (code typ)
    := match n with
       | O => ret []
       | S n' =>
         instr <- gen_instr_id;;
         rest  <- gen_code_length n';;
         ret (instr :: rest)
       end.

  Definition gen_code : GenLLVM (code typ)
    := n <- lift arbitrary;;
       gen_code_length n.

  (* Returns a terminator and a list of new blocks that it reaches *)
  (* Need to make returns more likely than branches so we don't get an
     endless tree of blocks *)
  Fixpoint gen_terminator
             (sz : nat) (t : typ) {struct t} : GenLLVM (terminator typ * list (block typ))
    :=
      ctx <- get_ctx;;
      match sz with
       | 0%nat =>
         (* Only returns allowed *)
         match (normalize_type ctx t) with
         | TYPE_Void => ret (TERM_Ret_void, [])
         | _ =>
           e <- lift (gen_exp ctx t);;
           ret (TERM_Ret (t, e), [])
         end
       | S sz' =>
         (* Need to lift oneOf to GenLLVM ...*)
         oneOf_LLVM
           [ gen_terminator 0 t
           ; '(b, bs) <- gen_blocks sz' t;; ret (TERM_Br_1 (blk_id b), bs)
           ]
       end
  with gen_blocks (sz : nat) (t : typ) {struct t} : GenLLVM (block typ * list (block typ))
         :=
           bid <- new_block_id;;
           code <- gen_code;;
           '(term, bs) <- gen_terminator (sz - 1) t;;
           i <- new_raw_id;;
           let b := {| blk_id   := bid
                     ; blk_phis := []
                     ; blk_code := code
                     ; blk_term := (IId i, term)
                     ; blk_comments := None
                    |} in
           ret (b, b :: bs).

  Definition gen_cfg_with_typ (sz : nat) (ret_t : typ) (args : list (ident * typ)) : GenLLVM (cfg typ)
    :=
      reset_ctx;;
      append_to_ctx args;;
      '(b, blocks) <- gen_blocks sz ret_t;;
      let cfg :=
          {| init := b.(blk_id);
             blks := blocks;
             args := map fst args;
          |} in
      ret cfg.

End InstrGenerators.


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
