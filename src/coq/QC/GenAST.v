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

From ExtLib.Structures Require Export
     Functor Applicative Monads.

Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Structures.Monads.

Require Import List.

Import ListNotations.

From Vellvm Require Import LLVMAst Utilities AstLib Syntax.CFG Syntax.TypeUtil Syntax.TypToDtyp DynamicTypes Semantics.TopLevel QC.Utils.
Require Import Integers Floats.
Require Import List.

Import ListNotations.
Import MonadNotation.
Import ApplicativeNotation.

From Coq Require Import
     ZArith List String Lia Bool.Bool.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

From FlocqQuickChick Require Import Generators.

From ExtLib.Structures Require Export
     Functor.
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
       | DTYPE_IPTR                 => true
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

  Definition genN : G N
    :=
      n <- (arbitrary : G nat);;
      ret (N.of_nat n).
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
    ; gen_ptrtoint_ctx : list (typ * ident * typ)
    }.

  Definition init_GenState : GenState
    := {| num_void   := 0
        ; num_raw    := 0
        ; num_global := 0
        ; num_blocks := 0
        ; gen_ctx    := []
        ; gen_typ_ctx    := []
        ; gen_ptrtoint_ctx := []
       |}.

  Definition increment_raw (gs : GenState) : GenState
    := {| num_void    := gs.(num_void)
        ; num_raw     := S gs.(num_raw)
        ; num_global  := gs.(num_global)
        ; num_blocks  := gs.(num_blocks)
        ; gen_ctx     := gs.(gen_ctx)
        ; gen_typ_ctx := gs.(gen_typ_ctx)
        ; gen_ptrtoint_ctx := gs.(gen_ptrtoint_ctx)
       |}.

  Definition increment_global (gs : GenState) : GenState
    := {| num_void    := gs.(num_void)
        ; num_raw     := gs.(num_raw)
        ; num_global  := S gs.(num_global)
        ; num_blocks  := gs.(num_blocks)
        ; gen_ctx     := gs.(gen_ctx)
        ; gen_typ_ctx := gs.(gen_typ_ctx)
        ; gen_ptrtoint_ctx := gs.(gen_ptrtoint_ctx)
       |}.

  Definition increment_void (gs : GenState) : GenState
    := {| num_void    := S gs.(num_void)
        ; num_raw     := gs.(num_raw)
        ; num_global  := gs.(num_global)
        ; num_blocks  := gs.(num_blocks)
        ; gen_ctx     := gs.(gen_ctx)
        ; gen_typ_ctx := gs.(gen_typ_ctx)
        ; gen_ptrtoint_ctx := gs.(gen_ptrtoint_ctx)
       |}.

  Definition increment_blocks (gs : GenState) : GenState
    := {| num_void    := gs.(num_void)
        ; num_raw     := gs.(num_raw)
        ; num_global  := gs.(num_global)
        ; num_blocks  := S gs.(num_blocks)
        ; gen_ctx     := gs.(gen_ctx)
        ; gen_typ_ctx := gs.(gen_typ_ctx)
        ; gen_ptrtoint_ctx := gs.(gen_ptrtoint_ctx)
       |}.

  Definition replace_ctx (ctx : list (ident * typ)) (gs : GenState) : GenState
    := {| num_void    := gs.(num_void)
        ; num_raw     := gs.(num_raw)
        ; num_global  := gs.(num_global)
        ; num_blocks  := gs.(num_blocks)
        ; gen_ctx     := ctx
        ; gen_typ_ctx := gs.(gen_typ_ctx)
        ; gen_ptrtoint_ctx := gs.(gen_ptrtoint_ctx)
       |}.

  Definition replace_typ_ctx (typ_ctx : list (ident * typ)) (gs : GenState) : GenState
    := {| num_void    := gs.(num_void)
        ; num_raw     := gs.(num_raw)
        ; num_global  := gs.(num_global)
        ; num_blocks  := gs.(num_blocks)
        ; gen_ctx     := gs.(gen_ctx)
        ; gen_typ_ctx := typ_ctx
        ; gen_ptrtoint_ctx := gs.(gen_ptrtoint_ctx)
       |}.

  Definition replace_ptrtoint_ctx (ptrtoint_ctx : list (typ * ident * typ)) (gs: GenState) : GenState
    := {| num_void    := gs.(num_void)
        ; num_raw     := gs.(num_raw)
        ; num_global  := gs.(num_global)
        ; num_blocks  := gs.(num_blocks)
        ; gen_ctx     := gs.(gen_ctx)
        ; gen_typ_ctx := gs.(gen_typ_ctx)
        ; gen_ptrtoint_ctx := ptrtoint_ctx
       |}.
  
  Definition GenLLVM := stateT GenState G.

  (* Need this because extlib doesn't declare this instance as global :|. *)
  #[global] Instance monad_stateT {s m} `{Monad m} : Monad (stateT s m).
  Proof.
    apply Monad_stateT;
      typeclasses eauto.
  Defined.

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

  Definition get_ptrtoint_ctx : GenLLVM (list (typ * ident * typ))
    := gets (fun gs => gs.(gen_ptrtoint_ctx)).
  
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

  Definition add_to_ptrtoint_ctx (x : (typ * ident * typ)) : GenLLVM unit
    := ctx <- get_ptrtoint_ctx;;
       let new_ctx := x :: ctx in
       modify (replace_ptrtoint_ctx new_ctx);;
       ret tt.

  Definition append_to_ctx (vars : list (ident * typ)) : GenLLVM unit
    := ctx <- get_ctx;;
       let new_ctx := vars ++ ctx in
       modify (replace_ctx new_ctx);;
       ret tt.
  
  Definition hide_ctx {A} (g: GenLLVM A) : GenLLVM A
    := saved_ctx <- get_ctx;;
       modify (replace_ctx []);;
       a <- g;;
       append_to_ctx saved_ctx;;
       ret a.
  
  Definition append_to_typ_ctx (aliases : list (ident * typ)) : GenLLVM unit
    := ctx <- get_typ_ctx;;
       let new_ctx := aliases ++ ctx in
       modify (replace_typ_ctx new_ctx);;
       ret tt.

  (* TODO:Not sure when it will be used, if not just delete it *)
  Definition append_to_ptrtoint_ctx (aliases : list (typ * ident * typ)) : GenLLVM unit
    := ctx <- get_ptrtoint_ctx;;
       let new_ctx := aliases ++ ctx in
       modify (replace_ptrtoint_ctx new_ctx);;
       ret tt.
  
  Definition reset_ctx : GenLLVM unit
    := modify (replace_ctx []);; ret tt.

  Definition reset_typ_ctx : GenLLVM unit
    := modify (replace_typ_ctx []);; ret tt.

  Definition reset_ptrtoint_ctx : GenLLVM unit
    := modify (replace_ptrtoint_ctx []);; ret tt.

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

  (*filter all the (ident, typ) in ctx such that typ is a ptr*)
Definition filter_ptr_typs (ctx : list (ident * typ)) : list (ident * typ) :=
  filter (fun '(_, t) => match t with
                        | TYPE_Pointer _ => true
                        | _ => false
                     end) ctx. 

Definition filter_sized_typs (typ_ctx: list (ident * typ)) (ctx : list (ident * typ)) : list (ident * typ) :=
  filter (fun '(_, t) => is_sized_type typ_ctx t) ctx.

Definition filter_non_void_typs (ctx : list (ident * typ)) : list (ident * typ) :=
  filter (fun '(_, t) => match t with
                      | TYPE_Void => false
                      | _ => true
                      end) ctx.

Definition filter_agg_typs (ctx: list (ident * typ)) : list (ident * typ) :=
  filter (fun '(_, t) =>
            match t with
            | TYPE_Array sz _ => N.ltb 0 sz
            | TYPE_Struct l
            | TYPE_Packed_struct l => negb (seq.nilp l)
            | _ => false
            end ) ctx.

Definition filter_vec_typs (ctx: list (ident * typ)) : list (ident * typ) :=
  filter (fun '(_, t) =>
            match t with
            | TYPE_Vector _ _ => true
            | _ => false
            end) ctx.

Definition filter_ptr_vecptr_typ (ctx: list (ident * typ)) : list (ident * typ) :=
  filter (fun '(_, t) =>
            match t with
            | TYPE_Pointer _ => true
            | TYPE_Vector _ (TYPE_Pointer _) => true
            | _ => false
            end) ctx.

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
                ; TYPE_Float
                (* ; TYPE_Double *)
                (* TODO: Could generate TYPE_Identified if we filter for sized types *)
                (* ; TYPE_Half *)
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
        ctx <- get_ctx;;
        aliases <- get_typ_ctx;;
        let typs_in_ctx := map (fun '(_, typ) => (1%nat, ret typ)) (filter_sized_typs aliases ctx) in
       freq_LLVM
        (typs_in_ctx ++[(1%nat, gen_sized_typ_0)
        ; (1%nat, ret TYPE_Pointer <*> gen_sized_typ_size sz')
        (* TODO: Might want to restrict the size to something reasonable *)
        ; (1%nat, ret TYPE_Array <*> lift_GenLLVM genN <*> gen_sized_typ_size sz')
        ; (1%nat, ret TYPE_Vector <*> (n <- lift_GenLLVM genN;; ret (n + 1)%N) <*> gen_sized_typ_size 0)
        (* TODO: I don't think functions are sized types? *)
        (* ; let n := Nat.div sz 2 in *)
        (*   ret TYPE_Function <*> gen_sized_typ_size n <*> listOf_LLVM (gen_sized_typ_size n) *)
        ; (1%nat, ret TYPE_Struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz'))
        ; (1%nat, ret TYPE_Packed_struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz'))
          ])
    end.
  Next Obligation.
  lia.
  Defined.

  Definition gen_sized_typ : GenLLVM typ
    := sized_LLVM (fun sz => gen_sized_typ_size sz).

 Program Fixpoint gen_sized_typ_size_ptrinctx (sz : nat) {measure sz} : GenLLVM typ :=
    match sz with
    | 0%nat => gen_sized_typ_0
    | (S sz') =>
        ctx <- get_ctx;;
        aliases <- get_typ_ctx;;
        let typs_in_ctx := map (fun '(_, typ) => (1%nat, ret typ)) (filter_sized_typs aliases ctx) in
      freq_LLVM
        (typs_in_ctx ++ [(1%nat, gen_sized_typ_0)
        (* TODO: Might want to restrict the size to something reasonable *)
        ; (1%nat, ret TYPE_Array <*> lift_GenLLVM genN <*> gen_sized_typ_size_ptrinctx sz')
        ; (1%nat, ret TYPE_Vector <*> (n <- lift_GenLLVM genN;; ret (n + 1)%N) <*> gen_sized_typ_size_ptrinctx 0)
        (* TODO: I don't think functions are sized types? *)
        (* ; let n := Nat.div sz 2 in *)
        (*   ret TYPE_Function <*> gen_sized_typ_size n <*> listOf_LLVM (gen_sized_typ_size n) *)
        ; (1%nat, ret TYPE_Struct <*> nonemptyListOf_LLVM (gen_sized_typ_size_ptrinctx sz'))
        ; (1%nat, ret TYPE_Packed_struct <*> nonemptyListOf_LLVM (gen_sized_typ_size_ptrinctx sz'))])
    end.
  Next Obligation.
  lia.
  Defined.
    
  Definition gen_sized_typ_ptrinctx : GenLLVM typ
    := sized_LLVM (fun sz => gen_sized_typ_size_ptrinctx sz).
  
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
                ; TYPE_Float
                (*; TYPE_Double*)
                (* ; TYPE_Half *)
                (* ; TYPE_X86_fp80 *)
                (* ; TYPE_Fp128 *)
                (* ; TYPE_Ppc_fp128 *)
                (* ; TYPE_Metadata *)
                (* ; TYPE_X86_mmx *)
                (* ; TYPE_Opaque *)
                ])).

  (* TODO: This should probably be mutually recursive with
     gen_sized_typ since pointers of any type are considered sized *)
  Program Fixpoint gen_typ_size (sz : nat) {measure sz} : GenLLVM typ :=
    match sz with
    | 0%nat => gen_typ_0
    | (S sz') =>
        ctx <- get_ctx;;
        (* not filter sized types for this one *)
        let typs_in_ctx := map (fun '(_, typ) => (1%nat, ret typ)) ctx in
        freq_LLVM
          (typs_in_ctx ++ [ (1%nat, gen_typ_0) (* TODO: Not sure if I need to add it here *)
              (* Might want to restrict the size to something reasonable *)
              (* TODO: Make sure length of Array >= 0, and length of vector >= 1 *)
            ; (1%nat, ret TYPE_Array <*> lift genN <*> gen_sized_typ_size sz')
            ; (1%nat, ret TYPE_Vector <*> (n <- lift_GenLLVM genN;;ret (n + 1)%N) <*> gen_sized_typ_size 0)
            ; let n := Nat.div sz 2 in
              (1%nat, ret TYPE_Function <*> gen_typ_size n <*> listOf_LLVM (gen_sized_typ_size n))
            ; (1%nat, ret TYPE_Struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz'))
            ; (1%nat, ret TYPE_Packed_struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz'))
          ])
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
                ; TYPE_Float
                (* ; TYPE_Double *)
                (* ; TYPE_Half *)
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
    | (S sz') =>
        ctx <- get_ctx;;
        let typs_in_ctx := map (fun '(_, typ) => (1%nat, ret typ)) (filter_non_void_typs ctx) in
        freq_LLVM        
          (typs_in_ctx ++[ (1%nat, gen_typ_non_void_0)
              (* Might want to restrict the size to something reasonable *)
              (* TODO: Make sure length of Array >= 0, and length of vector >= 1 *)
            ; (1%nat, ret TYPE_Array <*> lift genN <*> gen_sized_typ_size sz')
            ; (1%nat, ret TYPE_Vector <*> (n <- lift_GenLLVM genN;;ret (n + 1)%N) <*> gen_sized_typ_size 0)
            ; let n := Nat.div sz 2 in
              (1%nat, ret TYPE_Function <*> gen_typ_size n <*> listOf_LLVM (gen_sized_typ_size n))
            ; (1%nat, ret TYPE_Struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz'))
            ; (1%nat, ret TYPE_Packed_struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz'))
          ])
    end.

  Program Fixpoint gen_typ_non_void_size_wo_fn (sz : nat) {measure sz} : GenLLVM typ :=
  match sz with
  | 0%nat => gen_typ_non_void_0
  | (S sz') =>
      ctx <- get_ctx;;
      aliases <- get_typ_ctx;;
      let typs_in_ctx := map (fun '(_, typ) => (1%nat, ret typ)) (filter_sized_typs aliases ctx) in
      freq_LLVM                
        (typs_in_ctx ++ [ (1%nat, gen_typ_non_void_0)
            (* Might want to restrict the size to something reasonable *)
            (* TODO: Make sure length of Array >= 0, and length of vector >= 1 *)
          ; (1%nat, ret TYPE_Array <*> lift genN <*> gen_sized_typ_size sz')
          ; (1%nat, ret TYPE_Vector <*> (n <- lift_GenLLVM genN;;ret (n + 1)%N) <*> gen_sized_typ_size 0)
          ; (1%nat, ret TYPE_Struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz'))
          ; (1%nat, ret TYPE_Packed_struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz'))
        ])
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
                ; TYPE_Float
                (* ; TYPE_Double *)
                (* ; TYPE_Half *)
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

  (* TODO: IPTR not implemented *)
  Definition gen_int_typ_for_ptr_cast : GenLLVM typ :=
    ret (TYPE_I 64).
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

  (*Float operations*)
  Definition gen_fbinop : G fbinop :=
    oneOf_ failGen
            [ ret LLVMAst.FAdd
            ; ret FSub
            ; ret FMul
            ; ret FDiv
            ; ret FRem
            ].

  Definition gen_icmp : G icmp :=
    oneOf_ failGen
           (map ret
                [ Eq; Ne; Ugt; Uge; Ult; Ule; Sgt; Sge; Slt; Sle]).

  Definition gen_fcmp : G fcmp :=
    oneOf_ failGen
            (map ret
                  [FFalse; FOeq; FOgt; FOge; FOlt; FOle; FOne; FOrd;
                   FUno; FUeq; FUgt; FUge; FUlt; FUle; FUne; FTrue]).

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
       | DTYPE_I _, _ => false
       | DTYPE_IPTR, DTYPE_IPTR => true
       | DTYPE_IPTR, _ => false
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
       | DTYPE_Array _ _, _ => false
       | DTYPE_Struct fields, DTYPE_Struct fields' =>
         if Nat.eqb (Datatypes.length fields) (Datatypes.length fields')
         then forallb id (map_In (zip fields fields') (fun '(a, b) HIn => dtyp_eq a b))
         else false
       | DTYPE_Struct _, _ => false
       | DTYPE_Packed_struct fields, DTYPE_Packed_struct fields' =>
         if Nat.eqb (Datatypes.length fields) (Datatypes.length fields')
         then forallb id (map_In (zip fields fields') (fun '(a, b) HIn => dtyp_eq a b))
         else false
       | DTYPE_Packed_struct _, _ => false
       | DTYPE_Opaque, DTYPE_Opaque => false (* TODO: Unsure if this should compare equal *)
       | DTYPE_Opaque, _ => false
       | DTYPE_Vector sz t, DTYPE_Vector sz' t' =>
           if N.eq_dec sz sz'
           then dtyp_eq t t'
           else false
       | DTYPE_Vector _ _, _ => false
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
       | TYPE_IPTR =>
         match b with
         | TYPE_IPTR => true
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
             Nat.eqb (Datatypes.length args) (Datatypes.length args') &&
               normalized_typ_eq ret ret' &&
               forallb id (zipWith (fun a b => normalized_typ_eq a b) args args')
         | _ => false
         end
       | TYPE_Struct fields =>
         match b with
         | TYPE_Struct fields' =>
             Nat.eqb (Datatypes.length fields) (Datatypes.length fields') &&
             forallb id (zipWith (fun a b => normalized_typ_eq a b) fields fields')
         | _ => false
         end
       | TYPE_Packed_struct fields =>
         match b with
         | TYPE_Packed_struct fields' =>
             Nat.eqb (Datatypes.length fields) (Datatypes.length fields') &&
             forallb id (zipWith (fun a b => normalized_typ_eq a b) fields fields')
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
       | TYPE_IPTR => ret EXP_Integer <*> lift gen_non_zero
       | TYPE_Float => ret EXP_Float <*> lift fing32
       | TYPE_Double => lift failGen(*ret EXP_Double <*> lift fing64*) (*TODO : Fix generator for double*)
       | _ => lift failGen
       end.

(* Generator GEP part *)
(* Get index paths from array or vector*)
Fixpoint get_index_paths_from_AoV (sz: nat) (t: typ) (sub_paths: list (typ * list Z)) (pre_path: list Z): list (typ * list Z) :=
  match sz with
  | 0%nat => []
  | S z =>
      map (fun '(t, p) => (t, pre_path ++ [Z.of_nat z] ++ p)) sub_paths ++ get_index_paths_from_AoV z t sub_paths pre_path
  end.

(* Can work after extracting the pointer inside*)
Fixpoint get_index_paths_aux (t_from : typ) (pre_path : list Z) {struct t_from}: list (typ * list (Z)) :=
  match t_from with
  | TYPE_Array sz t
  | TYPE_Vector sz t =>
      let sub_paths := get_index_paths_aux t [] in (* Get index path from the first element*)
      [(t_from, pre_path)] ++ (* The path to the array *)
      get_index_paths_from_AoV (N.to_nat sz) t sub_paths pre_path (* Assemble them into 1*)
  | TYPE_Struct fields
  | TYPE_Packed_struct fields => [(t_from, pre_path)] ++ get_index_paths_from_struct fields pre_path 0
  | t => [(t, pre_path)]
  end with
  get_index_paths_from_struct (fields: list typ) (pre_path: list Z) (current_index : Z) {struct fields}: list (typ * list Z) :=
  match fields with
  | nil => nil
  | h::t => let head_list := map (fun '(t, p) => (t, pre_path ++ [current_index] ++ p)) (get_index_paths_aux h []) in
  let tail_list := get_index_paths_from_struct t pre_path (current_index + 1%Z) in
  head_list ++ tail_list
  end.

Definition get_index_paths_ptr (t_from: typ) : list (typ * list (Z)) :=
  map (fun '(t, path) => (t, path)) (get_index_paths_aux t_from [0%Z]).


(* Index path without getting into vector *)
Fixpoint get_index_paths_agg_aux (t_from : typ) (pre_path : list Z) {struct t_from}: list (typ * list (Z)) :=
  match t_from with
  | TYPE_Array sz t =>
      let sub_paths := get_index_paths_agg_aux t [] in (* Get index path from the first element*)
      [(t_from, pre_path)] ++ (* The path to the array *)
      get_index_paths_from_AoV (N.to_nat sz) t sub_paths pre_path (* Assemble them into 1*)
  | TYPE_Struct fields
  | TYPE_Packed_struct fields =>
      [(t_from, pre_path)] ++ get_index_paths_agg_from_struct fields pre_path 0
  | t => [(t, pre_path)]
  end with
  get_index_paths_agg_from_struct (fields: list typ) (pre_path: list Z) (current_index : Z) {struct fields}: list (typ * list Z) :=
  match fields with
  | nil => nil
  | h::t =>
      let head_list :=
        map (fun '(t, p) => (t, pre_path ++ [current_index] ++ p)) (get_index_paths_agg_aux h []) in
      let tail_list := get_index_paths_agg_from_struct t pre_path (current_index + 1%Z) in
      head_list ++ tail_list
  end.

(* The method is mainly used by extractvalue and insertvalue, 
   which requires at least one index for getting inside the aggregate type.
   There is a possibility for us to get nil path. The filter below will get rid of that possibility.
   Given that the nilpath will definitely be at the beginning of a list of options, we can essentially get the tail. *)
Definition get_index_paths_agg (t_from: typ) : list (typ * list (Z)) :=
  let agg_paths := get_index_paths_agg_aux t_from nil in
  tl agg_paths.

Definition get_ctx_ptrs  : GenLLVM (list (ident * typ)) :=
  ctx <- get_ctx;;
  ret (filter_ptr_typs ctx).

Definition get_ctx_ptr : GenLLVM (ident * typ) :=
  ptrs_in_context <- get_ctx_ptrs;;
  '(ptr_ident, ptr_typ) <- (oneOf_LLVM (map ret (ptrs_in_context)));;
  match ptr_typ with
  | TYPE_Pointer t => ret (ptr_ident, t)
  | _ => lift failGen (* Should not happen *)
  end.

Definition get_ctx_agg_typs : GenLLVM (list (ident * typ)) :=
  ctx <- get_ctx;;
  ret (filter_agg_typs ctx).

Definition get_ctx_agg_typ : GenLLVM (ident * typ) :=
  aggs_in_context <- get_ctx_agg_typs;;
  oneOf_LLVM (map ret aggs_in_context).

Definition get_ctx_vec_typs : GenLLVM (list (ident * typ)) :=
  ctx <- get_ctx;;
  ret (filter_vec_typs ctx).

Definition get_ctx_vec_typ : GenLLVM (ident * typ) :=
  vecs_in_context <- get_ctx_vec_typs;;
  oneOf_LLVM (map ret vecs_in_context).

Definition gen_gep : GenLLVM (typ * instr typ) :=
  '(id, t_in_ptr) <- get_ctx_ptr;;
  let paths_in_ptr := get_index_paths_ptr t_in_ptr in (* Inner paths: Paths after removing the outer pointer *)
  '(t, path) <- oneOf_LLVM (map ret paths_in_ptr);; (* Select one path from the paths *)
  let path_for_gep := map (fun x => (TYPE_I 32, EXP_Integer (x))) path in (* Turning the path to integer *)
   (* Refer to function get_int_typ *)
  ret (TYPE_Pointer t, INSTR_Op (OP_GetElementPtr t_in_ptr
                    (TYPE_Pointer t_in_ptr, EXP_Ident id) path_for_gep)).

Definition gen_extractvalue : GenLLVM (typ * instr typ) :=
  '(id, tagg) <- get_ctx_agg_typ;;
  let paths_in_agg := get_index_paths_agg tagg in
  '(t, path_for_extractvalue) <- oneOf_LLVM (map ret paths_in_agg);;
  ret (t, INSTR_Op (OP_ExtractValue (tagg, EXP_Ident id) path_for_extractvalue)).


(* ExtractElement *)
Definition gen_extractelement : GenLLVM (typ * instr typ) :=
  ctx <- get_ctx;;
  let vector_in_context := filter_vec_typs ctx in
  '(id, tvec) <- (oneOf_LLVM (map ret vector_in_context));;
  let get_size_ty (vType: typ) :=
    match tvec with
    | TYPE_Vector sz ty => (sz, ty)
    | _ => (0%N, TYPE_Void)
    end in
  let '(sz, t_in_vec) := get_size_ty tvec in
  let index_list := map (fun x => N.of_nat x) (List.seq 0 (N.to_nat sz)) in
  index_for_extractelement <- oneOf_LLVM (map ret index_list);;
  ret (t_in_vec, INSTR_Op (OP_ExtractElement (tvec, EXP_Ident id) (TYPE_I 32%N, EXP_Integer (Z.of_nat (N.to_nat index_for_extractelement))))).

(* Assumes input is a primitive type *)
(* Generate the element to be inserted into vector *)
Definition gen_typ_eq_prim_typ (t: typ): GenLLVM (exp typ) :=
  match t with
  | TYPE_I _ => i <- lift_GenLLVM (genNatInt);;
  ret (EXP_Integer (DynamicValues.Int32.intval i))
  | TYPE_Float => f <- lift_GenLLVM (fing32);;
  ret (EXP_Float f)
  | TYPE_Double => d <- lift_GenLLVM (fing64);;
  ret (EXP_Double d)
  | _ => ret (EXP_Null)
  end.

Definition gen_insertelement : GenLLVM (typ * instr typ) :=
  '(id, tvec) <- get_ctx_vec_typ;;
  let get_size_ty (vType: typ) :=
    match tvec with
    | TYPE_Vector sz ty => (sz, ty)
    | _ => (0%N, TYPE_Void)
    end in
  let '(sz, t_in_vec) := get_size_ty tvec in
  value <- gen_typ_eq_prim_typ t_in_vec;;
  index <- lift_GenLLVM (choose (0,Z.of_N sz));;
  ret (tvec, INSTR_Op (OP_InsertElement (tvec, EXP_Ident id) (t_in_vec, value) (TYPE_I 32, EXP_Integer index))).

Definition gen_ptrtoint : GenLLVM (typ * instr typ) :=
  ctx <- get_ctx;;
  let ptr_in_context := filter_ptr_typs ctx in
  '(id, tptr) <- (oneOf_LLVM (map ret ptr_in_context));;
  let gen_typ_in_ptr :=
    match tptr with
    | TYPE_Pointer t =>
        gen_int_typ_for_ptr_cast (* TODO: Wait till IPTR is implemented *)
    | TYPE_Vector sz ty =>
        x <- gen_int_typ_for_ptr_cast;;
        ret (TYPE_Vector sz x)
    | _ =>
        ret (TYPE_Void) (* Won't get into this case *)
    end in
  typ_from_cast <- gen_typ_in_ptr;;
  ret (typ_from_cast, INSTR_Op (OP_Conversion Ptrtoint tptr (EXP_Ident id) typ_from_cast)).

(* TODO: gen_inttoptr incomplete *)
Fixpoint get_size_from_typ (t: typ) : N :=
  match t with
  | TYPE_I sz => N.max 1 (sz / 8)%N
  | TYPE_Float => 4
  | TYPE_Double => 8
  | TYPE_Array sz t
  | TYPE_Vector sz t => (sz) * (get_size_from_typ t)
  | TYPE_Struct fields
  | TYPE_Packed_struct fields => fold_right (fun x acc => ((get_size_from_typ x) + acc)%N) 0%N fields
  | TYPE_Pointer _ => 8
  | _ => 1
  end.

(* Assuming max_byte_sz for this function is greater than 0 *)
Definition get_prim_typ_le_size (max_byte_sz: N) : list (GenLLVM typ) :=
  (if (1 <=? max_byte_sz)%N then [ret (TYPE_I 1); ret (TYPE_I 8)] else []) ++
  (if (4 <=? max_byte_sz)%N then [ret (TYPE_I 32); ret TYPE_Float] else []) ++
  (if (8 <=? max_byte_sz)%N then [ret (TYPE_I 64); ret TYPE_Double] else []).

(* Main method, it will generate based on the max_byte_sz
  Currently we support, int (1,8,32,64), float, double
  pointer, vector, array, struct, packed struct
  Aggregate structures used the types above. *)
Fixpoint gen_typ_le_size (max_byte_sz : N) : GenLLVM typ :=
  ctx <- get_ctx;;
  oneOf_LLVM
    ( (* Primitive types *)
      get_prim_typ_le_size max_byte_sz ++
      
      (* Vector type *)
      (if (max_byte_sz =? 0)%N then [] else
      [ sz' <- lift_GenLLVM (choose (1, BinIntDef.Z.of_N max_byte_sz ));;
        let sz' := BinIntDef.Z.to_N sz' in
        t <- oneOf_LLVM (get_prim_typ_le_size (max_byte_sz / sz'));;
        ret (TYPE_Vector (sz') t)
      ]) ++

      (* Array type *)
      [ sz' <- lift_GenLLVM (choose (0, BinIntDef.Z.of_N max_byte_sz));;
        let sz' := BinIntDef.Z.to_N sz' in
        if (sz' =? 0)%N (* Catch 0 array*)
        then
          t <- oneOf_LLVM (get_prim_typ_le_size 64);; (* Only primitive type to enhance performance *)
          ret (TYPE_Array (sz') t)
        else
          t <- gen_typ_le_size (max_byte_sz / sz');;
          ret (TYPE_Array (sz') t)
      ] ++

      (* Struct type *)
      [fields <- gen_typ_from_size_struct max_byte_sz;;
       ret (TYPE_Struct fields)
      ] ++

      (* Packed struct type *)
      [fields <- gen_typ_from_size_struct max_byte_sz;;
       ret (TYPE_Packed_struct fields)
      ])
with gen_typ_from_size_struct (max_byte_sz : N) : GenLLVM (list typ) :=
       subtyp <- gen_typ_le_size max_byte_sz;;
       let sz' := (max_byte_sz - (get_size_from_typ subtyp))%N in
       if (sz' =? 0)%N (* If the remaining size available is 0, then it will shrink the test case to not have other subtyp appending at the end *)
       then
         ret [subtyp]
       else
         tl <- gen_typ_from_size_struct sz';;
         ret ([subtyp] ++ tl).

(* A Helper function that will detect if  the type has pointer *)
Fixpoint typ_contains_pointer (old_ptr: typ) : bool :=
  match old_ptr with
  | TYPE_Pointer _ => true
  | TYPE_Array _ t
  | TYPE_Vector _ t =>
      typ_contains_pointer t
  | TYPE_Struct fields
  | TYPE_Packed_struct fields =>
      fold_left (fun acc x => orb acc (typ_contains_pointer x)) fields false
  | _ => false
  end.

Definition gen_inttoptr : GenLLVM (typ * instr typ) :=
  ctx <- get_ptrtoint_ctx;;
  '(old_tptr, id, typ_from_cast) <- oneOf_LLVM (map ret ctx);;
  (* In the following case, we will check whether there are double pointers in the old pointer type, we will not cast if the data structure has double pointer *)
  (* TODO: Better identify the pointer inside and cast without changing their location *)
  new_tptr <-
    match old_tptr with
    | TYPE_Pointer old_typ =>
        if typ_contains_pointer old_typ
        then
          ret old_tptr
        else
          x <- gen_typ_le_size (get_size_from_typ old_typ);;
          ret (TYPE_Pointer x)
    | TYPE_Vector sz (TYPE_Pointer old_typ) =>
        if typ_contains_pointer old_typ
        then
          ret old_tptr
        else
          x <- gen_typ_le_size (get_size_from_typ old_typ);;
          ret (TYPE_Pointer x)
    | _ => ret (TYPE_Void) (* Won't reach here... Hopefully *)
    end;;
  ret (new_tptr, INSTR_Op (OP_Conversion Inttoptr typ_from_cast (EXP_Ident id) new_tptr)).

Definition genTypHelper (n: nat): G (typ) :=
  run_GenLLVM (gen_typ_non_void_size n).

Definition genType: G (typ) :=
  sized genTypHelper.
  
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
      let fix gen_size_0 (t: typ) :=
          match t with
          | TYPE_I n                  => ret EXP_Integer <*> lift (arbitrary : G Z) (* lift (x <- (arbitrary : G nat);; ret (Z.of_nat x)) (* TODO: should the integer be forced to be in bounds? *) *)
          | TYPE_IPTR => ret EXP_Integer <*> lift (arbitrary : G Z)
          | TYPE_Pointer t            => lift failGen (* Only pointer type expressions might be conversions? Maybe GEP? *)
          | TYPE_Void                 => lift failGen (* There should be no expressions of type void *)
          | TYPE_Function ret args    => lift failGen (* No expressions of function type *)
          | TYPE_Opaque               => lift failGen (* TODO: not sure what these should be... *)

          (* Generate literals for aggregate structures *)
          | TYPE_Array n t =>
              es <- vectorOf_LLVM (N.to_nat n) (gen_size_0 t);;
              ret (EXP_Array (map (fun e => (t, e)) es))
          | TYPE_Vector n t =>
              es <- vectorOf_LLVM (N.to_nat n) (gen_size_0 t);;
              ret (EXP_Vector (map (fun e => (t, e)) es))
          | TYPE_Struct fields =>
              (* Should we divide size evenly amongst components of struct? *)
              tes <- map_monad (fun t => e <- gen_size_0 t;; ret (t, e)) fields;;
              ret (EXP_Struct tes)
          | TYPE_Packed_struct fields =>
              (* Should we divide size evenly amongst components of struct? *)
              tes <- map_monad (fun t => e <- gen_size_0 t;; ret (t, e)) fields;;
              ret (EXP_Packed_struct tes)

          | TYPE_Identified id        =>
            ctx <- get_ctx;;
            match find_pred (fun '(i,t) => if Ident.eq_dec id i then true else false) ctx with
            | None => lift failGen
            | Some (i,t) => gen_exp_size 0 t
            end
          (* Not generating these types for now *)
          | TYPE_Half                 => lift failGen
          | TYPE_Float                => ret EXP_Float <*> lift fing32(* referred to genarators in flocq-quickchick*)
          | TYPE_Double               => lift failGen (*ret EXP_Double <*> lift fing64*) (* TODO: Fix generator for double*)
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
               (gen_idents ++ [(1%nat, gen_size_0 t)])
      end
    | (S sz') =>
      let gens :=
          match t with
          | TYPE_I isz =>
            (* TODO: If I1 also allow ICmp and FCmp *)
            [gen_ibinop_exp isz]
          | TYPE_IPTR =>
            (* TODO: If I1 also allow ICmp and FCmp *)
            [gen_ibinop_exp_typ TYPE_IPTR]
          | TYPE_Pointer t         => [] (* GEP? *)

          (* TODO: currently only generate literals for aggregate structures with size 0 exps *)
          | TYPE_Array n t => []
          | TYPE_Vector n t => []
          | TYPE_Struct fields => []
          | TYPE_Packed_struct fields => []

          | TYPE_Void              => [lift failGen] (* No void type expressions *)
          | TYPE_Function ret args => [lift failGen] (* These shouldn't exist, I think *)
          | TYPE_Opaque            => [lift failGen] (* TODO: not sure what these should be... *)
          | TYPE_Half              => [lift failGen]
          | TYPE_Float             => [gen_fbinop_exp TYPE_Float]
          | TYPE_Double            => [(*gen_fbinop_exp TYPE_Double*)lift failGen]
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
  gen_ibinop_exp_typ (t : typ) : GenLLVM (exp typ)
    :=
      ibinop <- lift gen_ibinop;;
      if Handlers.LLVMEvents.DV.iop_is_div ibinop
      then ret (OP_IBinop ibinop) <*> ret t <*> gen_exp_size 0 t <*> gen_non_zero_exp_size 0 t
      else ret (OP_IBinop ibinop) <*> ret t <*> gen_exp_size 0 t <*> gen_exp_size 0 t
  with
  gen_ibinop_exp (isz : N) : GenLLVM (exp typ)
    :=
      let t := TYPE_I isz in
      gen_ibinop_exp_typ t
  with
  gen_fbinop_exp (ty: typ) : GenLLVM (exp typ)
    :=
      match ty with
       | TYPE_Float => fbinop <- lift gen_fbinop;;
       if (Handlers.LLVMEvents.DV.fop_is_div fbinop)
       then ret (OP_FBinop fbinop nil) <*> ret ty <*> gen_exp_size 0 ty <*> gen_exp_size 0 ty
       else ret (OP_FBinop fbinop nil) <*> ret ty <*> gen_exp_size 0 ty <*> gen_exp_size 0 ty
       | TYPE_Double => fbinop <- lift gen_fbinop;;
       if (Handlers.LLVMEvents.DV.fop_is_div fbinop)
       then ret (OP_FBinop fbinop nil) <*> ret ty <*> gen_exp_size 0 ty <*> gen_exp_size 0 ty
       else ret (OP_FBinop fbinop nil) <*> ret ty <*> gen_exp_size 0 ty <*> gen_exp_size 0 ty
       | _ => lift failGen
      end.

  Definition gen_exp (t : typ) : GenLLVM (exp typ)
    := sized_LLVM (fun sz => gen_exp_size sz t).

Definition gen_insertvalue : GenLLVM (typ * instr typ) :=
  '(id, tagg) <- get_ctx_agg_typ;;
  let paths_in_agg := get_index_paths_agg tagg in
  '(tsub, path_for_insertvalue) <- oneOf_LLVM (map ret paths_in_agg);;
  ex <- hide_ctx (gen_exp_size 0 tsub);;
  (* Generate all of the type*)
  ret (tagg, INSTR_Op (OP_InsertValue (tagg, EXP_Ident id) (tsub, ex) path_for_insertvalue)).
  
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
            | TYPE_Float => gen_fbinop_exp TYPE_Float
            | TYPE_Double => gen_fbinop_exp TYPE_Double
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
    := '(ptr_ident, ptr_typ) <- get_ctx_ptr;;
       vol <- lift (arbitrary : G bool);;
       let pt := TYPE_Pointer ptr_typ in
       let ptr := EXP_Ident ptr_ident in
       align <- ret None;;
       ret (ptr_typ, INSTR_Load vol ptr_typ (pt, ptr) align).

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
    := '(ptr_ident, ptr_typ) <- get_ctx_ptr;;
       let pt := TYPE_Pointer ptr_typ in
       let pexp := EXP_Ident ptr_ident in
       gen_store_to (pt, pexp).

  (* Generate an instruction, as well as its type...

     The type is sometimes void for instructions that don't really
     compute a value, like void function calls, stores, etc.
   *)
  Definition gen_instr : GenLLVM (typ * instr typ) :=
    ctx <- get_ctx;;
    ptrtoint_ctx <- get_ptrtoint_ctx;;
    oneOf_LLVM
      ([ t <- gen_op_typ;; i <- ret INSTR_Op <*> gen_op t;; ret (t, i)
         ; t <- gen_sized_typ_ptrinctx;;
           (* TODO: generate multiple element allocas. Will involve changing initialization *)
           num_elems <- ret None;; (* gen_opt_LLVM (resize_LLVM 0 gen_int_texp);; *)
           align <- ret None;;
           ret (TYPE_Pointer t, INSTR_Alloca t num_elems align)
        ] (* TODO: Generate atomic operations and other instructions *)
         ++ (if seq.nilp (filter_ptr_typs ctx) then [] else [gen_gep; gen_load; gen_store; gen_ptrtoint])
         ++ (if seq.nilp ptrtoint_ctx then [] else [gen_inttoptr])
         ++ (if seq.nilp (filter_agg_typs ctx) then [] else [gen_extractvalue; gen_insertvalue])
         ++ (if seq.nilp (filter_vec_typs ctx) then [] else [gen_extractelement; gen_insertelement])).
  
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
          match instr with
          | INSTR_Op (OP_Conversion Ptrtoint t_from v t_to) =>
              add_to_ptrtoint_ctx (t_from, ID_Local i, t_to);; (* Register the local variable to ptrtoint_ctx*)
              ret (IId i, instr)
          | _ =>
              add_to_ctx (ID_Local i, t);;
              ret (IId i, instr)
          end
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
