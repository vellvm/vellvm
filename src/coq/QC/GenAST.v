(** This file contains QuickChick generators for LLVM programs.

    There are many different ways of generating values of different
    types which have different constraints (e.g., positive values,
    sized types, etc). This is necessary to satisfy the invariants of
    LLVM programs.

    Currently programs are rather simple, only generating integer
    types and simple loops, but we hope to expand this soon.

    See vellvm-quickchick-overview.org in the root of the project for
    more details. *)
Require Import Ceres.Ceres.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

From ExtLib.Structures Require Export
     Functor Applicative Monads.

Require Import ExtLib.Data.Monads.StateMonad.

From Vellvm Require Import LLVMAst Utilities AstLib Syntax.CFG Syntax.TypeUtil Syntax.TypToDtyp DynamicTypes Semantics.TopLevel QC.Utils.
Require Import Integers Floats.

Require Import List.

Import ListNotations.
Import MonadNotation.
Import ApplicativeNotation.

From Coq Require Import
     ZArith List String Lia Bool.Bool.

Open Scope Z_scope.


(* Disable guard checking. This file is only used for generating test
    cases. Some of our generation functions terminate in non-trivial
    ways, but since they're only used to generate test cases (and are
    not used in proofs) it's not terribly important to prove that they
    actually terminate.  *)
Unset Guard Checking.

Section Helpers.
  Fixpoint is_sized_type_h (t : dtyp) : bool
    := match t with
       | DTYPE_I sz                 => true
       | DTYPE_Pointer              => true
       | DTYPE_Void                 => false
       | DTYPE_Half                 => true
       | DTYPE_Float                => true
       | DTYPE_Double               => true
       | DTYPE_X86_fp80             => true
       | DTYPE_Fp128                => true
       | DTYPE_Ppc_fp128            => true
       | DTYPE_Metadata             => true (* Is this right? *)
       | DTYPE_X86_mmx              => true
       | DTYPE_Array sz t           => is_sized_type_h t
       | DTYPE_Struct fields        => true
       | DTYPE_Packed_struct fields => true
       | DTYPE_Opaque               => false
       | DTYPE_Vector sz t          => is_sized_type_h t
       end.

  (* Only works correctly if the type is well formed *)
  Definition is_sized_type (typ_ctx : list (ident * typ)) (t : typ) : bool
    := is_sized_type_h (typ_to_dtyp typ_ctx t).

  Definition is_int_type_h (t : dtyp) : bool
    := match t with
       | DTYPE_I sz => true
       | _ => false
       end.

  (* Only works correctly if the type is well formed *)
  Definition is_int_type (typ_ctx : list (ident * typ)) (t : typ) : bool
    := is_int_type_h (typ_to_dtyp typ_ctx t).

  (* TODO: incomplete. Should typecheck *)
  Fixpoint well_formed_op (typ_ctx : list (ident * typ)) (op : exp typ) : bool :=
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

  Definition genNatInt : G int
    := fmap (fun n => Int.repr (Z.of_nat n)) (arbitrary : G nat).

  Definition genPosInt : G int
    := fmap (fun n => Int.repr (Z.of_nat (S n))) (arbitrary : G nat).

  Definition genPosZ : G Z
    :=
      n <- (arbitrary : G nat);;
      ret (Z.of_nat n).
End Helpers.

Section GenerationState.
  Record GenState :=
    mkGenState
    { num_void : nat
    ; num_raw  : nat
    ; num_global : nat
    ; num_blocks : nat
    (* Types of values *)
    ; gen_ctx : list (ident * typ)
    (* Type aliases *)
    ; gen_typ_ctx : list (ident * typ)
    }.

  Definition init_GenState : GenState
    := {| num_void   := 0
        ; num_raw    := 0
        ; num_global := 0
        ; num_blocks := 0
        ; gen_ctx    := []
        ; gen_typ_ctx    := []
       |}.

  Definition increment_raw (gs : GenState) : GenState
    := {| num_void    := gs.(num_void)
        ; num_raw     := S gs.(num_raw)
        ; num_global  := gs.(num_global)
        ; num_blocks  := gs.(num_blocks)
        ; gen_ctx     := gs.(gen_ctx)
        ; gen_typ_ctx := gs.(gen_typ_ctx)
       |}.

  Definition increment_global (gs : GenState) : GenState
    := {| num_void    := gs.(num_void)
        ; num_raw     := gs.(num_raw)
        ; num_global  := S gs.(num_global)
        ; num_blocks  := gs.(num_blocks)
        ; gen_ctx     := gs.(gen_ctx)
        ; gen_typ_ctx := gs.(gen_typ_ctx)
       |}.

  Definition increment_void (gs : GenState) : GenState
    := {| num_void    := S gs.(num_void)
        ; num_raw     := gs.(num_raw)
        ; num_global  := gs.(num_global)
        ; num_blocks  := gs.(num_blocks)
        ; gen_ctx     := gs.(gen_ctx)
        ; gen_typ_ctx := gs.(gen_typ_ctx)
       |}.

  Definition increment_blocks (gs : GenState) : GenState
    := {| num_void    := gs.(num_void)
        ; num_raw     := gs.(num_raw)
        ; num_global  := gs.(num_global)
        ; num_blocks  := S gs.(num_blocks)
        ; gen_ctx     := gs.(gen_ctx)
        ; gen_typ_ctx := gs.(gen_typ_ctx)
       |}.

  Definition replace_ctx (ctx : list (ident * typ)) (gs : GenState) : GenState
    := {| num_void    := gs.(num_void)
        ; num_raw     := gs.(num_raw)
        ; num_global  := gs.(num_global)
        ; num_blocks  := gs.(num_blocks)
        ; gen_ctx     := ctx
        ; gen_typ_ctx := gs.(gen_typ_ctx)
       |}.

  Definition replace_typ_ctx (typ_ctx : list (ident * typ)) (gs : GenState) : GenState
    := {| num_void    := gs.(num_void)
        ; num_raw     := gs.(num_raw)
        ; num_global  := gs.(num_global)
        ; num_blocks  := gs.(num_blocks)
        ; gen_ctx     := gs.(gen_ctx)
        ; gen_typ_ctx := typ_ctx
       |}.

  Definition GenLLVM := stateT GenState G.

  Definition get_raw (gs : GenState) : nat
    := gs.(num_raw).

  Definition get_global (gs : GenState) : nat
    := gs.(num_global).

  Definition get_void (gs : GenState) : nat
    := gs.(num_void).

  Definition get_blocks (gs : GenState) : nat
    := gs.(num_blocks).

  #[global] Instance MGEN : Monad GenLLVM.
  unfold GenLLVM.
  apply Monad_stateT.
  typeclasses eauto.
  Defined.

  Definition new_raw_id : GenLLVM raw_id
    := n <- gets get_raw;;
       modify increment_raw;;
       ret (Name ("v" ++ show n)).

  Definition new_global_id : GenLLVM raw_id
    := n <- gets get_global;;
       modify increment_global;;
       ret (Name ("g" ++ show n)).

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

  Definition get_typ_ctx : GenLLVM (list (ident * typ))
    := gets (fun gs => gs.(gen_typ_ctx)).

  Definition add_to_ctx (x : (ident * typ)) : GenLLVM  unit
    := ctx <- get_ctx;;
       let new_ctx := x :: ctx in
       modify (replace_ctx new_ctx);;
       ret tt.

  Definition add_to_typ_ctx (x : (ident * typ)) : GenLLVM  unit
    := ctx <- get_typ_ctx;;
       let new_ctx := x :: ctx in
       modify (replace_typ_ctx new_ctx);;
       ret tt.

  Definition append_to_ctx (vars : list (ident * typ)) : GenLLVM unit
    := ctx <- get_ctx;;
       let new_ctx := vars ++ ctx in
       modify (replace_ctx new_ctx);;
       ret tt.

  Definition append_to_typ_ctx (aliases : list (ident * typ)) : GenLLVM unit
    := ctx <- get_typ_ctx;;
       let new_ctx := aliases ++ ctx in
       modify (replace_typ_ctx new_ctx);;
       ret tt.

  Definition reset_ctx : GenLLVM unit
    := modify (replace_ctx []);; ret tt.

  Definition reset_typ_ctx : GenLLVM unit
    := modify (replace_typ_ctx []);; ret tt.

  Definition oneOf_LLVM {A} (gs : list (GenLLVM A)) : GenLLVM A
    := n <- lift (choose (0, List.length gs - 1)%nat);;
       nth n gs (lift failGen).

  Definition freq_LLVM {A} (gs : list (nat * GenLLVM A)) : GenLLVM A
    := mkStateT
         (fun st => freq_ failGen (fmap (fun '(n, g) => (n, runStateT g st)) gs)).

  Definition vectorOf_LLVM {A : Type} (k : nat) (g : GenLLVM A)
    : GenLLVM (list A) :=
    fold_right (fun m m' =>
                  x <- m;;
                  xs <- m';;
                  ret (x :: xs)) (ret []) (repeat g k).

  Definition sized_LLVM {A : Type} (gn : nat -> GenLLVM A) : GenLLVM A
    := mkStateT
         (fun st => sized (fun n => runStateT (gn n) st)).

  Definition resize_LLVM {A : Type} (sz : nat) (g : GenLLVM A) : GenLLVM A
    := mkStateT
         (fun st => resize sz (runStateT g st)).

  Definition listOf_LLVM {A : Type} (g : GenLLVM A) : GenLLVM (list A) :=
    sized_LLVM (fun n =>
                  k <- lift (choose (0, n)%nat);;
                  vectorOf_LLVM k g).

  Definition nonemptyListOf_LLVM
             {A : Type} (g : GenLLVM A) : GenLLVM (list A)
    := sized_LLVM (fun n =>
                     k <- lift (choose (1, n)%nat);;
                     vectorOf_LLVM k g).

  Definition run_GenLLVM {A} (g : GenLLVM A) : G A
    := fmap fst (runStateT g init_GenState).

  Definition lift_GenLLVM {A} (g : G A) : GenLLVM A
    := mkStateT (fun st => a <- g;; ret (a, st)).
End GenerationState.

Section TypGenerators.
  (* TODO: These currently don't generate pointer types either. *)

  (* Not sized in the QuickChick sense, sized in the LLVM sense. *)
  Definition gen_sized_typ_0 : GenLLVM typ :=
    aliases <- get_typ_ctx;;
    let sized_aliases := filter (fun '(i,t) => is_sized_type aliases t) aliases in
    let ident_gen :=
        (* Don't want to fail if there are no identifiers *)
        if (List.length sized_aliases =? 0)%nat
        then []
        else [ret TYPE_Identified <*> oneOf_LLVM (map (fun '(i,_) => ret i) sized_aliases)] in
    oneOf_LLVM
           (ident_gen ++
           (map ret
                [ TYPE_I 1
                ; TYPE_I 8
                ; TYPE_I 32
                (* TODO: big ints *)
                (* ; TYPE_I 64 *)
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

  Program Fixpoint gen_sized_typ_size (sz : nat) {measure sz} : GenLLVM typ :=
    match sz with
    | O => gen_sized_typ_0
    | (S sz') =>
      oneOf_LLVM
        [ gen_sized_typ_0
        ; ret TYPE_Pointer <*> gen_sized_typ_size sz'
        (* Might want to restrict the size to something reasonable *)
        (* ; ret TYPE_Array <*> lift genPosZ <*> gen_sized_typ_size sz'
        ; ret TYPE_Vector <*> lift genPosZ <*> gen_sized_typ_size sz'
        ; let n := Nat.div sz 2 in
          ret TYPE_Function <*> gen_sized_typ_size n <*> listOf_LLVM (gen_sized_typ_size n)
        ; ret TYPE_Struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz')
        ; ret TYPE_Packed_struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz') *)
        ]
    end.

  Definition gen_sized_typ : GenLLVM typ
    := sized_LLVM (fun sz => gen_sized_typ_size sz).

  (* Generate a type of size 0 *)
  Definition gen_typ_0 : GenLLVM typ :=
    aliases <- get_typ_ctx;;
    let identified :=
        match aliases with
        | [] => []
        | _  => [(ret TYPE_Identified <*> oneOf_LLVM (map (fun '(i,_) => ret i) aliases))]
        end
    in
    oneOf_LLVM
          ((* identified ++ *)
           (map ret
                [ TYPE_I 1
                ; TYPE_I 8
                ; TYPE_I 32
                (* TODO: big ints*)
               (* ; TYPE_I 64 *)
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

  Definition genN : G N
    := n <- arbitrary;; ret (N.of_nat n).

  (* TODO: This should probably be mutually recursive with
     gen_sized_typ since pointers of any type are considered sized *)
  Program Fixpoint gen_typ_size (sz : nat) {measure sz} : GenLLVM typ :=
    match sz with
    | 0%nat => gen_typ_0
    | (S sz') => oneOf_LLVM
                      [ gen_typ_0
                      (* Might want to restrict the size to something reasonable *)
                      (* TODO: Make sure length of Array >= 0, and length of vector >= 1 *)
                      ; ret TYPE_Array <*> lift genN <*> gen_sized_typ_size sz'
                      ; ret TYPE_Vector <*> lift genN <*> gen_sized_typ_size sz'
                      ; let n := Nat.div sz 2 in
                        ret TYPE_Function <*> gen_typ_size n <*> listOf_LLVM (gen_sized_typ_size n)
                      ; ret TYPE_Struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz')
                      ; ret TYPE_Packed_struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz')
                      ]
    end.
  Next Obligation.
    cbn.
    assert (0 <= 1)%nat by lia.
    pose proof Nat.divmod_spec sz' 1 0 0 H.
    cbn; destruct (Nat.divmod sz' 1 0 0).
    cbn; lia.
  Qed.

  Definition gen_typ : GenLLVM typ
    := sized_LLVM (fun sz => gen_typ_size sz).

  Definition gen_typ_non_void_0 : GenLLVM typ :=
    aliases <- get_typ_ctx;;
    let identified :=
        match aliases with
        | [] => []
        | _  => [(ret TYPE_Identified <*> oneOf_LLVM (map (fun '(i,_) => ret i) aliases))]
        end
    in
    oneOf_LLVM
          (identified ++
           (map ret
                [ TYPE_I 1
                ; TYPE_I 8
                ; TYPE_I 32
                (* TODO: big ints *)
                (* ; TYPE_I 64 *)
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

  Program Fixpoint gen_typ_non_void_size (sz : nat) {measure sz} : GenLLVM typ :=
    match sz with
    | 0%nat => gen_typ_non_void_0
    | (S sz') => oneOf_LLVM
                      [ gen_typ_non_void_0
                      (* Might want to restrict the size to something reasonable *)
                      (* TODO: Make sure length of Array >= 0, and length of vector >= 1 *)
                      ; ret TYPE_Array <*> lift genN <*> gen_sized_typ_size sz'
                      ; ret TYPE_Vector <*> lift genN <*> gen_sized_typ_size sz'
                      ; let n := Nat.div sz 2 in
                        ret TYPE_Function <*> gen_typ_size n <*> listOf_LLVM (gen_sized_typ_size n)
                      ; ret TYPE_Struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz')
                      ; ret TYPE_Packed_struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz')
                      ]
    end.

  (* TODO: look up identifiers *)
  (* Types for operation expressions *)
  Definition gen_op_typ : GenLLVM typ :=
    oneOf_LLVM
           (map ret
                [ TYPE_I 1
                ; TYPE_I 8
                ; TYPE_I 32
                (* TODO: big ints *)
                (* ; TYPE_I 64 *)
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
  Definition gen_int_typ : GenLLVM typ :=
    oneOf_LLVM
           (map ret
                [ TYPE_I 1
                ; TYPE_I 8
                ; TYPE_I 32
                (* TODO: big ints *)
                (* ; TYPE_I 64 *)
                ]).
End TypGenerators.

Section ExpGenerators.
  (* nuw / nsw make poison values likely *)
  Definition gen_ibinop : G ibinop :=
    (* Note: some of these binops are currently commented out due to a
       bug with extraction and QC. *)
    oneOf_ failGen
           [ ret LLVMAst.Add <*> ret false <*> ret false
           ; ret Sub <*> ret false <*> ret false
           ; ret Mul <*> ret false <*> ret false
           ; ret Shl <*> ret false <*> ret false
           ; ret UDiv <*> ret false
           ; ret SDiv <*> ret false
           ; ret LShr <*> ret false
           ; ret AShr <*> ret false
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

  (* TODO: Move this*)
  Fixpoint dtyp_eq (a : dtyp) (b : dtyp) {struct a} : bool
    := match a, b with
       | DTYPE_I sz, DTYPE_I sz' =>
         if N.eq_dec sz sz' then true else false
       | DTYPE_I sz, _ => false
       | DTYPE_Pointer, DTYPE_Pointer => true
       | DTYPE_Pointer, _ => false
       | DTYPE_Void, DTYPE_Void => true
       | DTYPE_Void, _ => false
       | DTYPE_Half, DTYPE_Half => true
       | DTYPE_Half, _ => false
       | DTYPE_Float, DTYPE_Float => true
       | DTYPE_Float, _ => false
       | DTYPE_Double, DTYPE_Double => true
       | DTYPE_Double, _ => false
       | DTYPE_X86_fp80, DTYPE_X86_fp80 => true
       | DTYPE_X86_fp80, _ => false
       | DTYPE_Fp128, DTYPE_Fp128 => true
       | DTYPE_Fp128, _ => false
       | DTYPE_Ppc_fp128, DTYPE_Ppc_fp128 => true
       | DTYPE_Ppc_fp128, _ => false
       | DTYPE_Metadata, DTYPE_Metadata => true
       | DTYPE_Metadata, _ => false
       | DTYPE_X86_mmx, DTYPE_X86_mmx => true
       | DTYPE_X86_mmx, _ => false
       | DTYPE_Array sz t, DTYPE_Array sz' t' =>
           if N.eq_dec sz sz'
           then dtyp_eq t t'
           else false
       | DTYPE_Array sz t, _ => false
       | DTYPE_Struct fields, DTYPE_Struct fields' =>
         if Nat.eqb (Datatypes.length fields) (Datatypes.length fields')
         then forallb id (map_In (zip fields fields') (fun '(a, b) HIn => dtyp_eq a b))
         else false
       | DTYPE_Struct fields, _ => false
       | DTYPE_Packed_struct fields, DTYPE_Packed_struct fields' =>
         if Nat.eqb (Datatypes.length fields) (Datatypes.length fields')
         then forallb id (map_In (zip fields fields') (fun '(a, b) HIn => dtyp_eq a b))
         else false
       | DTYPE_Packed_struct fields, _ => false
       | DTYPE_Opaque, DTYPE_Opaque => false (* TODO: Unsure if this should compare equal *)
       | DTYPE_Opaque, _ => false
       | DTYPE_Vector sz t, DTYPE_Vector sz' t' =>
           if N.eq_dec sz sz'
           then dtyp_eq t t'
           else false
       | DTYPE_Vector sz t, _ => false
       end.

  (* TODO: Move this*)
  (* This only returns what you expect on normalized typs *)
  (* TODO: I don't think this does the right thing for pointers to
           identified types... It should be conservative and say that
           the types are *not* equal always, though.
   *)
  Fixpoint normalized_typ_eq (a : typ) (b : typ) {struct a} : bool
    := match a with
       | TYPE_I sz =>
         match b with
         | TYPE_I sz' => if N.eq_dec sz sz' then true else false
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
           if N.eq_dec sz sz'
           then normalized_typ_eq t t'
           else false
         | _ => false
         end
       | TYPE_Function ret args =>
         match b with
         | TYPE_Function ret' args' =>
           normalized_typ_eq ret ret' && forallb id (zipWith (fun a b => normalized_typ_eq a b) args args')
         | _ => false
         end
       | TYPE_Struct fields =>
         match b with
         | TYPE_Struct fields' => forallb id (zipWith (fun a b => normalized_typ_eq a b) fields fields')
         | _ => false
         end
       | TYPE_Packed_struct fields =>
         match b with
         | TYPE_Packed_struct fields' => forallb id (zipWith (fun a b => normalized_typ_eq a b) fields fields')
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
           if N.eq_dec sz sz'
           then normalized_typ_eq t t'
           else false
         | _ => false
         end
       | TYPE_Identified id => false
       end.

  (* TODO: Move this *)
  Fixpoint replicateM {M : Type -> Type} {A} `{Monad M} (n : nat) (ma : M A) : M (list A)
    := match n with
       | O    => a <- ma;; ret [a]
       | S n' => a <- ma;; rest <- replicateM n' ma;; ret (a :: rest)
       end.

  (* This needs to use normalized_typ_eq, instead of dtyp_eq because of pointer types...
     dtyps only tell you that a type is a pointer, the other type
     information about the pointers is erased.
   *)
  Definition filter_type (ty : typ) (ctx : list (ident * typ)) : list (ident * typ)
    := filter (fun '(i, t) => normalized_typ_eq (normalize_type ctx ty) (normalize_type ctx t)) ctx.

  (* TODO: Also generate negative numbers *)
  Definition gen_non_zero : G Z
    := n <- (arbitrary : G nat);;
       ret (Z.of_nat (S n)).

  Definition gen_non_zero_exp_size (sz : nat) (t : typ) : GenLLVM (exp typ)
    := match t with
       | TYPE_I n => ret EXP_Integer <*> lift gen_non_zero (* TODO: should integer be forced to be in bounds? *)
       | _ => lift failGen
       end.

  (* TODO: should make it much more likely to pick an identifier for
           better test cases *)
  Fixpoint gen_exp_size (sz : nat) (t : typ) {struct t} : GenLLVM (exp typ) :=
    match sz with
    | 0%nat =>
      ctx <- get_ctx;;
      let ts := filter_type t ctx in
      let gen_idents :=
          match ts with
          | [] => []
          | _ => [(16%nat, fmap (fun '(i,_) => EXP_Ident i) (oneOf_LLVM (fmap ret ts)))]
          end in
      let gen_size_0 :=
          match t with
          | TYPE_I n                  => ret EXP_Integer <*> lift (arbitrary : G Z) (* lift (x <- (arbitrary : G nat);; ret (Z.of_nat x)) (* TODO: should the integer be forced to be in bounds? *) *)
          | TYPE_Pointer t            => lift failGen (* Only pointer type expressions might be conversions? Maybe GEP? *)
          | TYPE_Void                 => lift failGen (* There should be no expressions of type void *)
          | TYPE_Function ret args    => lift failGen (* No expressions of function type *)
          | TYPE_Opaque               => lift failGen (* TODO: not sure what these should be... *)
          | TYPE_Array n t            => lift failGen
          | TYPE_Vector sz t          => lift failGen
          | TYPE_Struct fields        => lift failGen
          | TYPE_Packed_struct fields => lift failGen
          | TYPE_Identified id        =>
            ctx <- get_ctx;;
            match find_pred (fun '(i,t) => if Ident.eq_dec id i then true else false) ctx with
            | None => lift failGen
            | Some (i,t) => gen_exp_size 0 t
            end
          (* Not generating these types for now *)
          | TYPE_Half                 => lift failGen
          | TYPE_Float                => lift failGen
          | TYPE_Double               => lift failGen
          | TYPE_X86_fp80             => lift failGen
          | TYPE_Fp128                => lift failGen
          | TYPE_Ppc_fp128            => lift failGen
          | TYPE_Metadata             => lift failGen
          | TYPE_X86_mmx              => lift failGen
          end in
      (* Hack to avoid failing way too much *)
      match t with
      | TYPE_Pointer t => freq_LLVM gen_idents
      | _ => freq_LLVM
               (gen_idents ++ [(1%nat, gen_size_0)])
      end
    | (S sz') =>
      let gens :=
          match t with
          | TYPE_I isz =>
            (* TODO: If I1 also allow ICmp and FCmp *)
            [gen_ibinop_exp isz]
          | TYPE_Array n t =>
            [es <- vectorOf_LLVM (N.to_nat n) (gen_exp_size 0 t);;
             ret (EXP_Array (map (fun e => (t, e)) es))]
          | TYPE_Vector n t =>
            [es <- vectorOf_LLVM (N.to_nat n) (gen_exp_size 0 t);;
             ret (EXP_Array (map (fun e => (t, e)) es))]
          | TYPE_Struct fields =>
            (* Should we divide size evenly amongst components of struct? *)
            [tes <- map_monad (fun t => e <- gen_exp_size 0 t;; ret (t, e)) fields;;
             ret (EXP_Struct tes)]
          | TYPE_Packed_struct fields =>
            (* Should we divide size evenly amongst components of struct? *)
            [tes <- map_monad (fun t => e <- gen_exp_size 0 t;; ret (t, e)) fields;;
             ret (EXP_Packed_struct tes)]
          | TYPE_Pointer t         => [] (* GEP? *)
          | TYPE_Void              => [lift failGen] (* No void type expressions *)
          | TYPE_Function ret args => [lift failGen] (* These shouldn't exist, I think *)
          | TYPE_Opaque            => [lift failGen] (* TODO: not sure what these should be... *)
          | TYPE_Half              => [lift failGen]
          | TYPE_Float             => [lift failGen]
          | TYPE_Double            => [lift failGen]
          | TYPE_X86_fp80          => [lift failGen]
          | TYPE_Fp128             => [lift failGen]
          | TYPE_Ppc_fp128         => [lift failGen]
          | TYPE_Metadata          => [lift failGen]
          | TYPE_X86_mmx           => [lift failGen]
          | TYPE_Identified id     =>
            [ctx <- get_ctx;;
             match find_pred (fun '(i,t) => if Ident.eq_dec id i then true else false) ctx with
             | None => lift failGen
             | Some (i,t) => gen_exp_size sz t
             end]
          end
      in
      (* short-circuit to size 0 *)
      oneOf_LLVM (gen_exp_size 0 t :: gens)
    end
  with
  (* TODO: Make sure we don't divide by 0 *)
  gen_ibinop_exp (isz : N) : GenLLVM (exp typ)
    :=
      let t := TYPE_I isz in
      ibinop <- lift gen_ibinop;;
      if Handlers.LLVMEvents.DV.iop_is_div ibinop
      then ret (OP_IBinop ibinop) <*> ret t <*> gen_exp_size 0 t <*> gen_non_zero_exp_size 0 t
      else ret (OP_IBinop ibinop) <*> ret t <*> gen_exp_size 0 t <*> gen_exp_size 0 t.

  Definition gen_exp (t : typ) : GenLLVM (exp typ)
    := sized_LLVM (fun sz => gen_exp_size sz t).

  Definition gen_texp : GenLLVM (texp typ)
    := t <- gen_typ;;
       e <- gen_exp t;;
       ret (t, e).

  Definition gen_sized_texp : GenLLVM (texp typ)
    := t <- gen_sized_typ;;
       e <- gen_exp t;;
       ret (t, e).

  Definition gen_op (t : typ) : GenLLVM (exp typ)
    := sized_LLVM
         (fun sz =>
            match t with
            | TYPE_I isz =>
              (* TODO: If I1 also allow ICmp and FCmp *)
              gen_ibinop_exp isz
            | _ => lift failGen
            end).

  Definition gen_int_texp : GenLLVM (texp typ)
    := t <- gen_int_typ;;
       e <- gen_exp t;;
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

  (* TODO: move these *)
  Definition opt_add_state {A} {ST} (st : ST) (o : option (A * ST)) : (option A * ST)
    := match o with
       | None => (None, st)
       | (Some (a, st')) => (Some a, st')
       end.

  Definition gen_opt_LLVM {A} (g : GenLLVM A) : GenLLVM (option A)
    := mkStateT
         (fun st =>
            opt <- gen_option (runStateT g st);;
            ret (opt_add_state st opt)).

  Definition gen_load : GenLLVM (typ * instr typ)
    := t   <- gen_sized_typ;;
       let pt := TYPE_Pointer t in
       vol <- lift (arbitrary : G bool);;
       ptr <- resize_LLVM 0 (gen_exp pt);;
       align <- ret None;;
       ret (t, INSTR_Load vol t (pt, ptr) align).

  Definition gen_store_to (ptr : texp typ) : GenLLVM (typ * instr typ)
    :=
      match ptr with
      | (TYPE_Pointer t, pexp) =>
        vol   <- lift arbitrary;;
        align <- ret None;;

        e <- resize_LLVM 0 (gen_exp t);;
        let val := (t, e) in

        ret (TYPE_Void, INSTR_Store vol val ptr align)
      | _ => lift failGen
      end.

  Definition gen_store : GenLLVM (typ * instr typ)
    := t <- gen_sized_typ;;
       let pt := TYPE_Pointer t in
       pexp <- gen_exp pt;;
       gen_store_to (pt, pexp).

  (* Generate an instruction, as well as its type...

     The type is sometimes void for instructions that don't really
     compute a value, like void function calls, stores, etc.
   *)
  Definition gen_instr : GenLLVM (typ * instr typ) :=
    oneOf_LLVM
      [ t <- gen_op_typ;; i <- ret INSTR_Op <*> gen_op t;; ret (t, i)
      ; t <- gen_op_typ;; (* gen_sized_typ;; *)
        (* TODO: generate multiple element allocas. Will involve changing initialization *)
        num_elems <- ret None;; (* gen_opt_LLVM (resize_LLVM 0 gen_int_texp);; *)
        align <- ret None;;
        ret (TYPE_Pointer t, INSTR_Alloca t num_elems align)
      (* TODO: Generate calls *)
      ; gen_load
      ; gen_store
      (* TODO: Generate atomic operations and other instructions *)
      ].

  (* TODO: Generate instructions with ids *)
  (* Make sure we can add these new ids to the context! *)

  (* TODO: want to generate phi nodes, which might be a bit
  complicated because we need to know that an id that occurs in a
  later block is in context *)

  Definition add_id_to_instr (t_instr : typ * instr typ) : GenLLVM (instr_id * instr typ)
    :=
      match t_instr with
      | (TYPE_Void, instr) =>
        vid <- new_void_id;;
        ret (vid, instr)
      | (t, instr) =>
        i <- new_raw_id;;
        add_to_ctx (ID_Local i, t);;
        ret (IId i, instr)
      end.

  (* Generate a block of code, spitting out a new context. *)
  Definition gen_instr_id : GenLLVM (instr_id * instr typ)
    := t_instr <- gen_instr;; add_id_to_instr t_instr.

  Definition fix_alloca (iid : instr_id * instr typ) : GenLLVM (list (instr_id * instr typ))
    := match iid with
       | (IId i, INSTR_Alloca t num_elems align) =>
         t_instr <- gen_store_to (TYPE_Pointer t, EXP_Ident (ID_Local i));;
         instr <- add_id_to_instr t_instr;;
         ret [instr]
       | _ => ret []
       end.

  Fixpoint gen_code_length (n : nat) : GenLLVM (code typ)
    := match n with
       | O => ret []
       | S n' =>
         instr <- gen_instr_id;;
         (* Add an initial store if instr is alloca *)
         alloca_store <- fix_alloca instr;;
         rest  <- gen_code_length n';;
         ret (instr :: alloca_store ++ rest)
       end.

  Definition gen_code : GenLLVM (code typ)
    := n <- lift arbitrary;;
       gen_code_length n.


  Definition instr_id_to_raw_id (fail_msg : string) (i : instr_id) : raw_id :=
    match i with
    | IId id => id
    | IVoid n => Name ("fail (instr_id_to_raw_id): " ++ fail_msg)
    end.

  (* Returns a terminator and a list of new blocks that it reaches *)
  (* Need to make returns more likely than branches so we don't get an
     endless tree of blocks *)
  Fixpoint gen_terminator_sz
           (sz : nat)
           (t : typ) (* Return type *)
           (back_blocks : list block_id) (* Blocks that I'm allowed to jump back to *)
           {struct t} : GenLLVM (terminator typ * list (block typ))
    :=
      ctx <- get_ctx;;
      match sz with
       | 0%nat =>
         (* Only returns allowed *)
         match (typ_to_dtyp ctx t) with
         | DTYPE_Void => ret (TERM_Ret_void, [])
         | _ =>
           e <- gen_exp_size 0 t;;
           ret (TERM_Ret (t, e), [])
         end
       | S sz' =>
         (* Need to lift oneOf to GenLLVM ...*)
         freq_LLVM
           ([ (6%nat, gen_terminator_sz 0 t back_blocks)
           (* Simple jump *)
           ; (min sz' 6%nat, '(b, (bh, bs)) <- gen_blocks_sz sz' t back_blocks;; ret (TERM_Br_1 (blk_id b), (bh::bs)))
           (* Conditional branch, with no backloops *)
           ; (min sz' 6%nat,
                   c <- gen_exp_size 0 (TYPE_I 1);;

                   (* Save context *)
                   ctx <- get_ctx;;

                   (* Generate first branch *)
                   '(b1, (bh1, bs1)) <- gen_blocks_sz sz' t back_blocks;;

                   (* Restore context so blocks in second branch don't refer
                      to variables from the first branch. *)
                   modify (replace_ctx ctx);;
                   '(b2, (bh2, bs2)) <- gen_blocks_sz sz' t back_blocks;;

                   ret (TERM_Br (TYPE_I 1, c) (blk_id b1) (blk_id b2), (bh1::bs1) ++ (bh2::bs2)))
            (* Sometimes generate a loop *)
            ; (min sz' 6%nat,
               '(t, (b, bs)) <- gen_loop_sz sz t back_blocks 10;;
               ret (t, (b :: bs)))
           ]
              ++
              (* Loop back sometimes *)
              match back_blocks with
              | (b::bs) =>
                [(min sz' 1%nat,
                bid <- lift_GenLLVM (elems_ b back_blocks);;
                ret (TERM_Br_1 bid, []))]
              | nil => []
              end)
       end
  with gen_blocks_sz
         (sz : nat)
         (t : typ) (* Return type *)
         (back_blocks : list block_id) (* Blocks that I'm allowed to jump back to *)
         {struct t} : GenLLVM (block typ * (block typ * list (block typ)))
         :=
           bid <- new_block_id;;
           code <- gen_code;;
           '(term, bs) <- gen_terminator_sz (sz - 1) t back_blocks;;
           let b := {| blk_id   := bid
                     ; blk_phis := []
                     ; blk_code := code
                     ; blk_term := term
                     ; blk_comments := None
                    |} in
           ret (b, (b, bs))
  with gen_loop_sz
         (sz : nat)
         (t : typ)
         (back_blocks : list block_id) (* Blocks that I'm allowed to jump back to *)
         (bound : LLVMAst.int) {struct t} : GenLLVM (terminator typ * (block typ * list (block typ)))
    :=
      bid_entry <- new_block_id;;
      (* TODO: make it so I can generate constant expressions *)
      loop_init <- ret INSTR_Op <*> gen_op (TYPE_I 32 (* TODO: big ints *));; (* gen_exp_size sz (TYPE_I 64);; *)
      bound' <- lift_GenLLVM (choose (0, bound));;
      '(loop_init_instr_id, loop_init_instr) <- add_id_to_instr (TYPE_I 32 (* TODO: big ints *), loop_init);;
      let loop_init_instr_raw_id := instr_id_to_raw_id "loop init id" loop_init_instr_id in
      '(loop_cmp_id, loop_cmp) <- add_id_to_instr (TYPE_I 1, INSTR_Op (OP_ICmp Ule (TYPE_I 32 (* TODO: big ints *)) (EXP_Ident (ID_Local loop_init_instr_raw_id)) (EXP_Integer bound')));;
      let loop_cmp_raw_id := instr_id_to_raw_id "loop_cmp_id" loop_cmp_id in
      let lower_exp := OP_Select (TYPE_I 1, (EXP_Ident (ID_Local loop_cmp_raw_id)))
                                 (TYPE_I 32 (* TODO: big ints *), (EXP_Ident (ID_Local loop_init_instr_raw_id)))
                                 (TYPE_I 32 (* TODO: big ints *), EXP_Integer bound') in
      '(select_id, select_instr) <- add_id_to_instr (TYPE_I 32 (* TODO: big ints *), INSTR_Op lower_exp);;
      let loop_final_init_id_raw := instr_id_to_raw_id "loop iterator id" select_id in

      let loop_cond_exp := INSTR_Op (OP_ICmp Ugt (TYPE_I 32 (* TODO: big ints *)) (EXP_Ident (ID_Local loop_final_init_id_raw)) (EXP_Integer 0)) in
      '(loop_cond_id, loop_cond) <- add_id_to_instr (TYPE_I 1, loop_cond_exp);;

      let entry_code : list (instr_id * instr typ) := [(loop_init_instr_id, loop_init_instr); (loop_cmp_id, loop_cmp); (select_id, select_instr); (loop_cond_id, loop_cond)] in

      (* Generate end blocks *)
      ctx <- get_ctx;;
      '(_, (end_b, end_bs)) <- gen_blocks_sz (sz / 2) t back_blocks;;
      let end_blocks := end_b :: end_bs in
      let end_bid := blk_id end_b in

      bid_next <- new_block_id;;
      loop_bid <- new_block_id;;
      phi_id <- new_raw_id;;

      (* Block for controlling the next iteration of the loop *)
      let next_exp := OP_IBinop (Sub false false) (TYPE_I 32 (* TODO: big ints *)) (EXP_Ident (ID_Local phi_id)) (EXP_Integer 1) in
      '(next_instr_id, next_instr) <- add_id_to_instr (TYPE_I 32 (* TODO: big ints *), INSTR_Op next_exp);;
      let next_instr_raw_id := instr_id_to_raw_id "next_exp" next_instr_id in
      let next_cond_exp := OP_ICmp Ugt (TYPE_I 32 (* TODO: big ints *)) (EXP_Ident (ID_Local next_instr_raw_id)) (EXP_Integer 0) in
      '(next_cond_id, next_cond) <- add_id_to_instr (TYPE_I 1, INSTR_Op next_cond_exp);;
      let next_cond_raw_id := instr_id_to_raw_id "next_cond_exp" next_cond_id in

      let next_code := [(next_instr_id, next_instr); (next_cond_id, next_cond)] in
      let next_block := {| blk_id   := bid_next
                         ; blk_phis := []
                         ; blk_code := next_code
                         ; blk_term := TERM_Br (TYPE_I 1, (EXP_Ident (ID_Local next_cond_raw_id))) loop_bid end_bid
                         ; blk_comments := None
                         |} in

      (* Generate loop blocks *)
      modify (replace_ctx ctx);;
      '(loop_b, loop_bs) <- gen_loop_entry_sz (sz / 2) t loop_bid phi_id bid_entry bid_next (EXP_Ident (ID_Local loop_final_init_id_raw)) (EXP_Ident (ID_Local next_instr_raw_id)) back_blocks;;
      let loop_blocks := loop_b :: loop_bs in
      let loop_bid := blk_id loop_b in

      let entry_block := {| blk_id   := bid_entry
                          ; blk_phis := []
                          ; blk_code := entry_code
                          ; blk_term := TERM_Br (TYPE_I 1, (EXP_Ident (ID_Local (instr_id_to_raw_id "loop_cond_id" loop_cond_id)))) loop_bid end_bid
                          ; blk_comments := None
                          |} in

      ret (TERM_Br_1 bid_entry, (entry_block, loop_blocks ++ [next_block] ++ end_blocks))
  with gen_loop_entry_sz
         (sz : nat)
         (t : typ)
         (bid_loop : block_id)
         (phi_id : local_id)
         (bid_entry bid_next : block_id)
         (entry_exp next_exp : exp typ)
         (back_blocks : list block_id) (* Blocks that I'm allowed to jump back to *)
         {struct t} : GenLLVM (block typ * list (block typ))
         := (* This should basically be gen_blocks_sz, but the initial block contains loop control and phi nodes *)
           code <- gen_code;;
           '(term, bs) <- gen_terminator_sz (sz - 1) t (bid_next::back_blocks);;
           let b := {| blk_id   := bid_loop
                     ; blk_phis := [(phi_id, Phi (TYPE_I 32 (* TODO: big ints *)) [(bid_entry, entry_exp); (bid_next, next_exp)])]
                     ; blk_code := code
                     ; blk_term := term
                     ; blk_comments := None
                    |} in
           ret (b, bs).

  Definition gen_blocks (t : typ) : GenLLVM (block typ * list (block typ))
    := sized_LLVM (fun n => fmap snd (gen_blocks_sz n t [])).

  (* Don't want to generate CFGs, actually. Want to generated TLEs *)
  Definition gen_definition (name : global_id) (ret_t : typ) (args : list (local_id * typ)) : GenLLVM (definition typ (block typ * list (block typ)))
    :=
      ctx <- get_ctx;;
      (* Add arguments to context *)
      let args_ctx := map (fun '(i, t) => (ID_Local i, t)) args in
      append_to_ctx args_ctx;;

      bs <- gen_blocks ret_t;;

      let args_t := map snd args in
      let f_type := TYPE_Function ret_t args_t in
      let prototype :=
          mk_declaration name f_type
                         ([], [])
                         None None None None
                         []
                         None None None
      in
      (* Reset context *)
      modify (replace_ctx ((ID_Global name, f_type) :: ctx));;
      ret (mk_definition (block typ * list (block typ)) prototype (map fst args) bs).

  Definition gen_new_definition (ret_t : typ) (args : list (local_id * typ)) : GenLLVM (definition typ (block typ * list (block typ)))
    :=
      name <- new_global_id;;
      gen_definition name ret_t args.

  Definition gen_main : GenLLVM (definition typ (block typ * list (block typ)))
    := gen_definition (Name "main") (TYPE_I 8) [].

  Definition gen_main_tle : GenLLVM (toplevel_entity typ (block typ * list (block typ)))
    := ret TLE_Definition <*> gen_main.

  Definition gen_llvm :GenLLVM (list (toplevel_entity typ (block typ * list (block typ))))
    := fmap ret gen_main_tle.

End InstrGenerators.
