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

From Vellvm Require Import LLVMAst Utilities AstLib Syntax.CFG Syntax.TypeUtil Syntax.TypToDtyp DynamicTypes Semantics.TopLevel QC.Utils QC.Generators Handlers.Handlers DList.
Require Import Integers.


From ExtLib.Structures Require Export
     Functor Applicative Monads Monoid.

Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Data.Monads.EitherMonad.
Require Import ExtLib.Structures.Monads.

Require Import List.

Import ListNotations.



Import ListNotations.
Import MonadNotation.
Import ApplicativeNotation.

From Coq Require Import
     ZArith Lia Bool.Bool.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

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
  Fixpoint is_sized_type_h (t : typ) : bool
    := match t with
       | TYPE_I sz => true
       | TYPE_IPTR => true
       | TYPE_Pointer t => is_sized_type_h t
       | TYPE_Void => false
       | TYPE_Half => true
       | TYPE_Float => true
       | TYPE_Double => true
       | TYPE_X86_fp80 => true
       | TYPE_Fp128 => true
       | TYPE_Ppc_fp128 => true
       | TYPE_Metadata => true (* Not sure if this is right *)
       | TYPE_X86_mmx => true
       | TYPE_Array sz t => is_sized_type_h t
       | TYPE_Function ret args vararg => false
       | TYPE_Struct fields => true
       | TYPE_Packed_struct fields => true
       | TYPE_Opaque => false
       | TYPE_Vector sz t => is_sized_type_h t
       | TYPE_Identified id => false
       end.

  (* Only works correctly if the type is well formed *)
  Definition is_sized_type (typ_ctx : list (ident * typ)) (t : typ) : bool
    := is_sized_type_h (normalize_type typ_ctx t).

  Definition is_int_type_h (t : typ) : bool
    := match t with
       | TYPE_I sz => true
       | _ => false
       end.

  (* Only works correctly if the type is well formed *)
  Definition is_int_type (typ_ctx : list (ident * typ)) (t : typ) : bool
    := is_int_type_h (normalize_type typ_ctx t).

  Definition is_function_type_h (t : typ) : bool
    := match t with
       | TYPE_Function _ _ _ => true
       | _ => false
       end.

  Definition is_function_type (typ_ctx : list (ident * typ)) (t : typ) : bool
    := is_function_type_h (normalize_type typ_ctx t).

  Definition is_function_pointer_h (t : typ) : bool
    := match t with
       | TYPE_Pointer (TYPE_Function _ _ _) => true
       | _ => false
       end.

  Definition is_function_pointer (typ_ctx : list (ident * typ)) (t : typ) : bool
    := is_function_pointer_h (normalize_type typ_ctx t).

  (* TODO: incomplete. Should typecheck *)
  Definition well_formed_op (typ_ctx : list (ident * typ)) (op : exp typ) : bool :=
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

  Definition type_context := list (ident * typ).
  Definition var_context := list (ident * typ).
  Definition ptr_to_int_context := list (typ * ident * typ).
  Definition all_var_contexts := (var_context * ptr_to_int_context)%type.

  Record GenState :=
    mkGenState
    { num_void : N
    ; num_raw  : N
    ; num_global : N
    ; num_blocks : N
    (* Types of values *)
    ; gen_ctx : var_context
    (* Type aliases *)
    ; gen_typ_ctx : type_context
    ; gen_ptrtoint_ctx : ptr_to_int_context
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
        ; num_raw     := N.succ gs.(num_raw)
        ; num_global  := gs.(num_global)
        ; num_blocks  := gs.(num_blocks)
        ; gen_ctx     := gs.(gen_ctx)
        ; gen_typ_ctx := gs.(gen_typ_ctx)
        ; gen_ptrtoint_ctx := gs.(gen_ptrtoint_ctx)
       |}.

  Definition increment_global (gs : GenState) : GenState
    := {| num_void    := gs.(num_void)
        ; num_raw     := gs.(num_raw)
        ; num_global  := N.succ gs.(num_global)
        ; num_blocks  := gs.(num_blocks)
        ; gen_ctx     := gs.(gen_ctx)
        ; gen_typ_ctx := gs.(gen_typ_ctx)
        ; gen_ptrtoint_ctx := gs.(gen_ptrtoint_ctx)
       |}.

  Definition increment_void (gs : GenState) : GenState
    := {| num_void    := N.succ gs.(num_void)
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
        ; num_blocks  := N.succ gs.(num_blocks)
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

  Definition GenLLVM := eitherT string (stateT GenState G).

  
  (* Need this because extlib doesn't declare this instance as global :|. *)
  #[global] Instance monad_stateT {s m} `{Monad m} : Monad (stateT s m).
  Proof.
    apply Monad_stateT;
      typeclasses eauto.
  Defined.

  Definition get_raw (gs : GenState) : N
    := gs.(num_raw).

  Definition get_global (gs : GenState) : N
    := gs.(num_global).

  Definition get_void (gs : GenState) : N
    := gs.(num_void).

  Definition get_blocks (gs : GenState) : N
    := gs.(num_blocks).

  #[global] Instance STGST : Monad (stateT GenState G).
  apply Monad_stateT.
  typeclasses eauto.
  Defined.

  #[global] Instance MGEN : Monad GenLLVM.
  unfold GenLLVM.
  apply Monad_eitherT.
  typeclasses eauto.
  Defined.

  Definition lift_GenLLVM {A} (g : G A) : GenLLVM A
    := mkEitherT (mkStateT (fun st => a <- g;; ret (inr a, st))).
  
  #[global] Instance MGENT: MonadT GenLLVM G.
  unfold GenLLVM.
  constructor.
  exact @lift_GenLLVM.
  Defined.
  
  (* SAZ: 
     [failGen] was the one piece of the backtracking variant of QuickChick we
     needed.  
   *)
  Definition failGen {A:Type} (s:string) : GenLLVM A :=
    mkEitherT (ret (inl s)).
  
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
       ret (IVoid (Z.of_N n)).

  Definition new_block_id : GenLLVM block_id
    := n <- gets get_blocks;;
       modify increment_blocks;;
       ret (Name ("b" ++ show n)).

  Definition get_ctx : GenLLVM var_context
    := gets (fun gs => gs.(gen_ctx)).

  Definition get_typ_ctx : GenLLVM type_context
    := gets (fun gs => gs.(gen_typ_ctx)).

  Definition get_ptrtoint_ctx : GenLLVM ptr_to_int_context
    := gets (fun gs => gs.(gen_ptrtoint_ctx)).

  (* Get all variable contexts that might need to be saved *)
  Definition get_variable_ctxs : GenLLVM all_var_contexts
    := ctx <- get_ctx;;
       ptoi_ctx <- get_ptrtoint_ctx;;
       ret (ctx, ptoi_ctx).

  Definition set_ctx (ctx : var_context) : GenLLVM unit
    := modify (replace_ctx ctx);;
       ret tt.

  Definition set_ptrtoint_ctx (ptoi_ctx : ptr_to_int_context) : GenLLVM unit
    := modify (replace_ptrtoint_ctx ptoi_ctx);;
       ret tt.

  Definition restore_variable_ctxs (ctxs : all_var_contexts) : GenLLVM unit
    := match ctxs with
       | (ctx, ptoi_ctx) =>
           set_ctx ctx;;
           set_ptrtoint_ctx ptoi_ctx
       end.

  (* TODO: Do we need this? *)
  Definition filter_global_from_variable_ctxs (ctxs : all_var_contexts) : all_var_contexts
    := let is_global_id (id: ident) :=
         match id with
         | ID_Global _ => true
         | ID_Local _ => false
         end in
       match ctxs with
       | (ctx, ptoi_ctx) =>
           let globals_in_ctx := filter (fun '(id, _) => is_global_id id) ctx in
           let globals_in_ptoi_ctx := filter (fun '(_, id, _) => is_global_id id) ptoi_ctx in
           (globals_in_ctx, globals_in_ptoi_ctx)
       end.

  Definition add_to_ctx (x : (ident * typ)) : GenLLVM unit
    := ctx <- get_ctx;;
       let new_ctx := x :: ctx in
       modify (replace_ctx new_ctx);;
       ret tt.

  Definition add_to_typ_ctx (x : (ident * typ)) : GenLLVM unit
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
       let new_ctx := (vars ++ ctx)%list in
       modify (replace_ctx new_ctx);;
       ret tt.

  Definition append_to_typ_ctx (aliases : list (ident * typ)) : GenLLVM unit
    := ctx <- get_typ_ctx;;
       let new_ctx := (aliases ++ ctx)%list in
       modify (replace_typ_ctx new_ctx);;
       ret tt.

  Definition append_to_ptrtoint_ctx (aliases : list (typ * ident * typ)) : GenLLVM unit
    := ctx <- get_ptrtoint_ctx;;
       let new_ctx := (aliases ++ ctx)%list in
       modify (replace_ptrtoint_ctx new_ctx);;
       ret tt.

  Definition reset_ctx : GenLLVM unit
    := modify (replace_ctx []);; ret tt.

  Definition reset_typ_ctx : GenLLVM unit
    := modify (replace_typ_ctx []);; ret tt.

  Definition reset_ptrtoint_ctx : GenLLVM unit
    := modify (replace_ptrtoint_ctx []);; ret tt.

  Definition hide_ctx {A} (g: GenLLVM A) : GenLLVM A
    := saved_ctx <- get_ctx;;
       reset_ctx;;
       a <- g;;
       append_to_ctx saved_ctx;;
       ret a.

  Definition hide_ptrtoint_ctx {A} (g: GenLLVM A) : GenLLVM A
    := saved_ctx <- get_ptrtoint_ctx;;
       reset_ptrtoint_ctx;;
       a <- g;;
       append_to_ptrtoint_ctx saved_ctx;;
       ret a.

  Definition hide_variable_ctxs {A} (g: GenLLVM A) : GenLLVM A
    := hide_ctx (hide_ptrtoint_ctx g).

  (** Restore context after running a generator. *)
  Definition backtrack_ctx {A} (g: GenLLVM A) : GenLLVM A
    := saved_ctx <- get_ctx;;
       a <- g;;
       set_ctx saved_ctx;;
       ret a.

  (** Restore ptrtoint context after running a generator. *)
  Definition backtrack_ptrtoint_ctx {A} (g: GenLLVM A) : GenLLVM A
    := saved_ctx <- get_ptrtoint_ctx;;
       a <- g;;
       set_ptrtoint_ctx saved_ctx;;
       ret a.

  (** Restore all variable contexts after running a generator. *)
  Definition backtrack_variable_ctxs {A} (g: GenLLVM A) : GenLLVM A
    := backtrack_ctx (backtrack_ptrtoint_ctx g).

  (* Elems implemented with reservoir sampling *)
  Definition elems_res {A} (def : G A) (l : list A) : G A
    := fst
         (fold_left
            (fun '(gacc, k) a =>
               let gen' :=
                 swap <- fmap (N.eqb 0) (choose (0%N, k));;
                 if swap
                 then (* swap *)
                   ret a
                 else (* No swap *)
                   gacc
               in (gen', (k+1)%N))
            l (def, 0%N)).
  
  Definition oneOf_LLVM {A} (gs : list (GenLLVM A)) : GenLLVM A
    := fst
         (fold_left
            (fun '(gacc, k) a =>
               let gen' :=
                 swap <- lift (fmap (N.eqb 0) (choose (0%N, k)));;
                 if swap
                 then (* swap *)
                   a
                 else (* No swap *)
                   gacc
               in (gen', (k+1)%N))
            gs (failGen "oneOf_LLVM", 0%N)).

  Definition oneOf_res {A} (def : G A) (gs : list (G A)) : G A
    := fst
         (fold_left
            (fun '(gacc, k) a =>
               let gen' :=
                 swap <- fmap (N.eqb 0) (choose (0%N, k));;
                 if swap
                 then (* swap *)
                   a
                 else (* No swap *)
                   gacc
               in (gen', (k+1)%N))
            gs (def, 0%N)).

  Definition freq_res {A} (def : G A) (gs : list (N * G A)) : G A
    := fst
         (fold_left
            (fun '(gacc, k) '(fk, a) =>
               let k' := (k + fk)%N in
               let gen' :=
                 swap <- fmap (fun x => N.leb x fk) (choose (0%N, k'));;
                 if swap
                 then (* swap *)
                   a
                 else (* No swap *)
                   gacc
               in (gen', k'))
            gs (def, 0%N)).

  Definition freq_LLVM_N {A} (gs : list (N * GenLLVM A)) : GenLLVM A
    := fst
         (fold_left
            (fun '(gacc, k) '(fk, a) =>
               let k' := (k + fk)%N in
               let gen' :=
                 swap <- lift (fmap (fun x => N.leb x fk) (choose (0%N, k')));;
                 if swap
                 then (* swap *)
                   a
                 else (* No swap *)
                   gacc
               in (gen', k'))
            gs (failGen "freq_LLVM_N", 0%N)).

  Definition freq_LLVM {A} (gs : list (nat * GenLLVM A)) : GenLLVM A
    := fst
         (fold_left
            (fun '(gacc, k) '(fk, a) =>
               let fkn := N.of_nat fk in
               let k' := (k + fkn)%N in
               let gen' :=
                 swap <- lift (fmap (fun x => N.leb x fkn) (choose (0%N, k')));;
                 if swap
                 then (* swap *)
                   a
                 else (* No swap *)
                   gacc
               in (gen', k'))
            gs (failGen "freq_LLVM", 0%N)).

  (* SAZ: Where do we need this? *)
  (*
  Definition freq_LLVM' {A} (gs : list (nat * GenLLVM A)) : GenLLVM A
    :=
        mkStateT
          (fun st => freq_ failGen (fmap (fun '(n, g) => (n, runStateT g st)) gs)).
   *)
    

  Definition thunkGen_LLVM {A} (thunk : unit -> GenLLVM A) : GenLLVM A
    := u <- ret tt;;
       thunk tt.

  Definition oneOf_LLVM_thunked {A} (gs : list (unit -> GenLLVM A)) : GenLLVM A
    := thunkGen_LLVM
         (fst
            (fold_left
               (fun '(gacc, k) a =>
                  let gen' := fun x =>
                    swap <- lift (fmap (N.eqb 0) (choose (0%N, k)));;
                    if swap
                    then (* swap *)
                      a x
                    else (* No swap *)
                      gacc x
                  in (gen', (k+1)%N))
               gs (fun _ => failGen "oneOF_LLVM_thunked", 0%N))).

  Definition oneOf_LLVM_thunked' {A} (gs : list (unit -> GenLLVM A)) : GenLLVM A
    := n <- lift (choose (0, List.length gs - 1)%nat);;
       thunkGen_LLVM (nth n gs (fun _ => failGen "oneOf_LLVM_thunked'")).

  Definition freq_LLVM_thunked_N {A} (gs : list (N * (unit -> GenLLVM A))) : GenLLVM A
    := thunkGen_LLVM
         (fst
            (fold_left
               (fun '(gacc, k) '(fk, a) =>
                  let k' := (k + fk)%N in
                  let gen' := fun x =>
                    swap <- lift (fmap (fun x => N.leb x fk) (choose (0%N, k')));;
                    if swap
                    then (* swap *)
                      a x
                    else (* No swap *)
                      gacc x
                  in (gen', k'))
               gs (fun _ => failGen "freq_LLVM_thunked_N'", 0%N))).

  Definition freq_LLVM_thunked {A} (gs : list (nat * (unit -> GenLLVM A))) : GenLLVM A
    := thunkGen_LLVM
         (fst
            (fold_left
               (fun '(gacc, k) '(fk, a) =>
                  let fkn := N.of_nat fk in
                  let k' := (k + fkn)%N in
                  let gen' := fun x =>
                    swap <- lift (fmap (fun x => N.leb x fkn) (choose (0%N, k')));;
                    if swap
                    then (* swap *)
                      a x
                    else (* No swap *)
                      gacc x
                  in (gen', k'))
               gs (fun _ => failGen "freq_LLVM_thunked", 0%N))).

  (* SAZ: do we need this? *)
  (*
  Definition freq_LLVM_thunked' {A} (gs : list (nat * (unit -> GenLLVM A))) : GenLLVM A
    := mkStateT
         (fun st => freq_ failGen (fmap (fun '(n, g) => (n, runStateT (thunkGen_LLVM g) st)) gs)).
   *)

  Definition elems_LLVM {A : Type} (l: list A) : GenLLVM A
    := fst
         (fold_left
            (fun '(gacc, k) a =>
               let gen' :=
                 swap <- lift (fmap (N.eqb 0) (choose (0%N, k)));;
                 if swap
                 then (* swap *)
                   ret a
                 else (* No swap *)
                   gacc
               in (gen', (k+1)%N))
            l (failGen "elems_LLVM", 0%N)).

  Definition vectorOf_LLVM {A : Type} (k : nat) (g : GenLLVM A)
    : GenLLVM (list A) :=
    fold_left (fun m' m =>
                 x <- m;;
                 xs <- m';;
                 ret (x :: xs)) (repeat g k) (ret []).

  Definition sized_LLVM {A : Type} (gn : nat -> GenLLVM A) : GenLLVM A
    := mkEitherT (mkStateT
                    (fun st => sized (fun n => runStateT (unEitherT (gn n)) st))).

  Definition resize_LLVM {A : Type} (sz : nat) (g : GenLLVM A) : GenLLVM A
    := mkEitherT (mkStateT
                    (fun st => resize sz (runStateT (unEitherT g) st))).

  Definition listOf_LLVM {A : Type} (g : GenLLVM A) : GenLLVM (list A) :=
    sized_LLVM (fun n =>
                  k <- lift (choose (0, n)%nat);;
                  vectorOf_LLVM k g).

  Definition nonemptyListOf_LLVM
             {A : Type} (g : GenLLVM A) : GenLLVM (list A)
    := sized_LLVM (fun n =>
                     k <- lift (choose (1, n)%nat);;
                     vectorOf_LLVM k g).

  Definition run_GenLLVM {A} (g : GenLLVM A) : G (string + A)
    := fmap fst (runStateT (unEitherT g) init_GenState).

End GenerationState.

Section TypGenerators.
  (*filter all the (ident, typ) in ctx such that typ is a ptr*)
  Definition filter_ptr_typs (typ_ctx : type_context) (ctx : var_context) : var_context :=
    filter (fun '(_, t) => match normalize_type typ_ctx t with
                        | TYPE_Pointer _ => true
                        | _ => false
                        end) ctx.

  Definition filter_sized_ptr_typs (typ_ctx : type_context) (ctx : var_context) : var_context :=
    filter (fun '(_, t) => match normalize_type typ_ctx t with
                        | TYPE_Pointer t => is_sized_type typ_ctx t
                        | _ => false
                        end) ctx.

  Definition filter_sized_typs (typ_ctx: type_context) (ctx : var_context) : var_context :=
    filter (fun '(_, t) => is_sized_type typ_ctx t) ctx.

  Definition filter_non_void_typs (typ_ctx : type_context) (ctx : var_context) : var_context :=
    filter (fun '(_, t) => match normalize_type typ_ctx t with
                        | TYPE_Void => false
                        | _ => true
                        end) ctx.

  Definition filter_agg_typs (typ_ctx : type_context) (ctx: var_context) : var_context :=
    filter (fun '(_, t) =>
              match normalize_type typ_ctx t with
              | TYPE_Array sz _ => N.ltb 0 sz
              | TYPE_Struct l
              | TYPE_Packed_struct l => negb (seq.nilp l)
              | _ => false
              end ) ctx.

  Definition filter_vec_typs (typ_ctx : type_context) (ctx: var_context) : var_context :=
    filter (fun '(_, t) =>
              match normalize_type typ_ctx t with
              | TYPE_Vector _ _ => true
              | _ => false
              end) ctx.

  Definition filter_ptr_vecptr_typs (typ_ctx : type_context) (ctx: var_context) : var_context :=
    filter (fun '(_, t) =>
              match normalize_type typ_ctx t with
              | TYPE_Pointer _ => true
              | TYPE_Vector _ (TYPE_Pointer _) => true
              | _ => false
              end) ctx.

  Definition filter_sized_ptr_vecptr_typs (typ_ctx : type_context) (ctx: var_context) : var_context :=
    filter (fun '(_, t) =>
              match normalize_type typ_ctx t with
              | TYPE_Pointer t => is_sized_type typ_ctx t
              | TYPE_Vector _ (TYPE_Pointer t) => is_sized_type typ_ctx t
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
        else [ret TYPE_Identified <*> fmap (fun '(i, _) => i) (elems_LLVM sized_aliases)] in
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

  (* TODO: Move this *)
  Definition lengthN {X} (xs : list X) : N :=
    fold_left (fun acc x => (acc + 1)%N) xs 0%N.

  Definition gen_typ_from_ctx (ctx : var_context) : GenLLVM typ
    := fmap snd (elems_LLVM ctx).

  Definition gen_ident_from_ctx (ctx : var_context) : GenLLVM ident
    := fmap fst (elems_LLVM ctx).

  Program Fixpoint gen_sized_typ_size (sz : nat) {measure sz} : GenLLVM typ :=
    match sz with
    | O => gen_sized_typ_0
    | (S sz') =>
        ctx <- get_ctx;;
        aliases <- get_typ_ctx;;
        let typs_in_ctx := filter_sized_typs aliases ctx in
        freq_LLVM_thunked_N
        ([(N.min (lengthN typs_in_ctx) 10, (fun _ => gen_typ_from_ctx typs_in_ctx))] ++
         [(1%N, (fun _ => gen_sized_typ_0))
        ; (1%N, (fun _ => ret TYPE_Pointer <*> gen_sized_typ_size sz'))
        (* TODO: Might want to restrict the size to something reasonable *)
        ; (1%N, (fun _ => ret TYPE_Array <*> lift_GenLLVM genN <*> gen_sized_typ_size sz'))
        ; (1%N, (fun _ => ret TYPE_Vector <*> (n <- lift_GenLLVM genN;; ret (n + 1)%N) <*> gen_sized_typ_size 0))
        (* TODO: I don't think functions are sized types? *)
        (* ; let n := Nat.div sz 2 in *)
        (*   ret TYPE_Function <*> gen_sized_typ_size n <*> listOf_LLVM (gen_sized_typ_size n) *)
        ; (1%N, (fun _ => ret TYPE_Struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz')))
        ; (1%N, (fun _ => ret TYPE_Packed_struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz')))
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
        let typs_in_ctx := filter_sized_typs aliases ctx in
        freq_LLVM_thunked_N
        ([(N.min (lengthN typs_in_ctx) 10, (fun _ => gen_typ_from_ctx typs_in_ctx))] ++
        [(1%N, (fun _ => gen_sized_typ_0))
        (* TODO: Might want to restrict the size to something reasonable *)
        ; (1%N, (fun _ => ret TYPE_Array <*> lift_GenLLVM genN <*> gen_sized_typ_size_ptrinctx sz'))
        ; (1%N, (fun _ => ret TYPE_Vector <*> (n <- lift_GenLLVM genN;; ret (n + 1)%N) <*> gen_sized_typ_size_ptrinctx 0))
        (* TODO: I don't think functions are sized types? *)
        (* ; let n := Nat.div sz 2 in *)
        (*   ret TYPE_Function <*> gen_sized_typ_size n <*> listOf_LLVM (gen_sized_typ_size n) *)
        ; (1%N, (fun _ => ret TYPE_Struct <*> nonemptyListOf_LLVM (gen_sized_typ_size_ptrinctx sz')))
        ; (1%N, (fun _ => ret TYPE_Packed_struct <*> nonemptyListOf_LLVM (gen_sized_typ_size_ptrinctx sz')))])
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
        | _  => [(ret TYPE_Identified <*> gen_ident_from_ctx aliases)]
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
        freq_LLVM_thunked_N
        ([(N.min (lengthN ctx) 10, (fun _ => gen_typ_from_ctx ctx))] ++
        [ (1%N, (fun _ => gen_typ_0)) (* TODO: Not sure if I need to add it here *)
        (* Might want to restrict the size to something reasonable *)
        (* TODO: Make sure length of Array >= 0, and length of vector >= 1 *)
        ; (1%N, (fun _ => ret TYPE_Array <*> lift genN <*> gen_sized_typ_size sz'))
        ; (1%N, (fun _ => ret TYPE_Vector <*> (n <- lift_GenLLVM genN;;ret (n + 1)%N) <*> gen_sized_typ_size 0))
        ; let n := Nat.div sz 2 in
        (1%N, (fun _ => ret TYPE_Function <*> gen_typ_size n <*> listOf_LLVM (gen_sized_typ_size n) <*> ret false))
        ; (1%N, (fun _ => ret TYPE_Struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz')))
        ; (1%N, (fun _ => ret TYPE_Packed_struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz')))
        ])
    end.
  Next Obligation.
    cbn.
    assert (0 <= 1)%nat by lia.
    pose proof Nat.divmod_spec sz' 1 0 0 H0.
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
        | _  => [(ret TYPE_Identified <*> gen_ident_from_ctx aliases)]
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
        typ_ctx <- get_typ_ctx;;
        ctx <- get_ctx;;
        let ctx := filter_non_void_typs typ_ctx ctx in
        freq_LLVM_thunked_N
        ([(N.min (lengthN ctx) 10, fun _ => gen_typ_from_ctx ctx)] ++
        [ (1%N, fun _ => gen_typ_non_void_0)
        (* Might want to restrict the size to something reasonable *)
        (* TODO: Make sure length of Array >= 0, and length of vector >= 1 *)
        ; (1%N, fun _ => ret TYPE_Array <*> lift genN <*> gen_sized_typ_size sz')
        ; (1%N, fun _ => ret TYPE_Vector <*> (n <- lift_GenLLVM genN;;ret (n + 1)%N) <*> gen_sized_typ_size 0)
        ; let n := Nat.div sz 2 in
        (1%N, fun _ => ret TYPE_Function <*> gen_typ_size n <*> listOf_LLVM (gen_sized_typ_size n) <*> ret false)
        ; (1%N, fun _ => ret TYPE_Struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz'))
        ; (1%N, fun _ => ret TYPE_Packed_struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz'))
          ])
    end.

  Program Fixpoint gen_typ_non_void_size_wo_fn (sz : nat) {measure sz} : GenLLVM typ :=
  match sz with
  | 0%nat => gen_typ_non_void_0
  | (S sz') =>
      ctx <- get_ctx;;
      aliases <- get_typ_ctx;;
      let ctx := filter_sized_typs aliases ctx in
      freq_LLVM_thunked_N
      ([(N.min (lengthN ctx) 10, fun _ => gen_typ_from_ctx ctx)] ++
      [ (1%N, fun _ => gen_typ_non_void_0)
      (* Might want to restrict the size to something reasonable *)
      (* TODO: Make sure length of Array >= 0, and length of vector >= 1 *)
      ; (1%N, fun _ => ret TYPE_Array <*> lift genN <*> gen_sized_typ_size sz')
      ; (1%N, fun _ => ret TYPE_Vector <*> (n <- lift_GenLLVM genN;;ret (n + 1)%N) <*> gen_sized_typ_size 0)
      ; (1%N, fun _ => ret TYPE_Struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz'))
      ; (1%N, fun _ => ret TYPE_Packed_struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz'))
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
    elems_LLVM
      [ TYPE_I 1
        ; TYPE_I 8
        ; TYPE_I 32
      (* TODO: big ints *)
      (* ; TYPE_I 64 *)
      ].

  (* TODO: IPTR not implemented *)
  Definition gen_int_typ_for_ptr_cast : GenLLVM typ :=
    ret (TYPE_I 64).
End TypGenerators.

Section ExpGenerators.

  (* SAZ: Here there were old uses of [failGen] that I replaced (arbitrarily) with the 
     last element of the non-empty list. *)
  
  Definition gen_ibinop : G ibinop :=
     oneOf_ (ret Xor) (* SAZ: This default case is a hack *)
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
    oneOf_ (ret FRem) (* SAZ: This default case is a hack *)
            [ ret LLVMAst.FAdd
            ; ret FSub
            ; ret FMul
            ; ret FDiv
            ; ret FRem
            ].

  Definition gen_icmp : G icmp :=
    oneOf_ (ret Sle) (* SAZ: This default case is a hack *)
           (map ret
                [ Eq; Ne; Ugt; Uge; Ult; Ule; Sgt; Sge; Slt; Sle]).

  Definition gen_fcmp : G fcmp :=
    oneOf_ (ret FTrue) (* SAZ: This default case is a hack *)
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
       | TYPE_Function ret args varargs=>
         match b with
         | TYPE_Function ret' args' varargs' =>
             Nat.eqb (Datatypes.length args) (Datatypes.length args') &&
               normalized_typ_eq ret ret' &&
               forallb id (zipWith (fun a b => normalized_typ_eq a b) args args')
             && Bool.eqb varargs varargs'
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

  (* This needs to use normalized_typ_eq, instead of dtyp_eq because of pointer types...
     dtyps only tell you that a type is a pointer, the other type
     information about the pointers is erased.
   *)
  Definition filter_type (ty : typ) (ctx : list (ident * typ)) : list (ident * typ)
    := filter (fun '(i, t) => normalized_typ_eq (normalize_type ctx ty) (normalize_type ctx t)) ctx.

  Variant contains_flag :=
  | soft
  | hard.

  (* This is a part of the easy fix for Issue 260. It can also potentially help other generators in filtering
     If there exists a subtyp of certain tribute *)
  Fixpoint contains_typ (t_from : typ) (t : typ) (flag : contains_flag): bool :=
    match t_from with
    | TYPE_I _ =>
        match t with
        | TYPE_I _ =>
            match flag with
            | soft => true
            | hard => normalized_typ_eq t_from t
            end
        | _ => false
        end
    | TYPE_IPTR
    | TYPE_Half
    | TYPE_Float
    | TYPE_Double
    | TYPE_X86_fp80
    | TYPE_Fp128
    | TYPE_Ppc_fp128
    | TYPE_Metadata
    | TYPE_X86_mmx => normalized_typ_eq t_from t
    | TYPE_Pointer subtyp =>
        match t with
        | TYPE_Pointer subtyp' =>
            match flag with
            | soft => true
            | hard => normalized_typ_eq subtyp subtyp' || contains_typ subtyp t flag
            end
        | _ => contains_typ subtyp t flag
        end
    | TYPE_Array sz subtyp =>
        match t with
        | TYPE_Array sz' subtyp' =>
            match flag with
            | soft => true
            | hard =>  (sz =? sz')%N && ((normalized_typ_eq subtyp subtyp') || (contains_typ subtyp t flag))
            end
        | _ => contains_typ subtyp t flag
        end
    | TYPE_Vector sz subtyp =>
        match t with
        | TYPE_Vector sz' subtyp' =>
            match flag with
            | soft => true
            | hard =>  (sz =? sz')%N && ((normalized_typ_eq subtyp subtyp') || (contains_typ subtyp t flag))
            end
        | _ => contains_typ subtyp t flag
        end
    | TYPE_Struct fields =>
        match t with
        | TYPE_Struct fields' =>
            match flag with
            | soft => true
            | hard => normalized_typ_eq t_from t || fold_left (fun acc x => acc || x) (map (fun y => contains_typ y t flag) fields) false
            end
        | _ => fold_left (fun acc x => acc || contains_typ x t flag) fields false
        end
    | TYPE_Packed_struct fields =>
        match t with
        | TYPE_Packed_struct fields' =>
            match flag with
            | soft => true
            | hard =>  normalized_typ_eq t_from t || fold_left (fun acc x => acc || x) (map (fun y => contains_typ y t flag) fields) false
            end
        | _ => fold_left (fun acc x => acc || contains_typ x t flag) fields false
        end
    | TYPE_Function ret_t args vararg =>
        match t with
        | TYPE_Function ret_t args vararg =>
            match flag with
            | soft => true
            | hard => normalized_typ_eq t_from t
            end
        | _ => false
        end
    | _ => false
    end.

  Definition filter_function_pointers (typ_ctx : type_context) (ctx : var_context) : var_context :=
    filter (fun '(_, t) => is_function_pointer typ_ctx t) ctx.

  (* Can't use choose for these functions because it gets extracted to
     ocaml's Random.State.int function which has small bounds. *)

  Definition gen_unsigned_bitwidth (bitwidth : N) : G Z :=
    z <- (arbitrary : G Z);;
    ret (Z.modulo z (2^(Z.of_N bitwidth))).

  Definition gen_signed_bitwidth (bitwidth : N) : G Z :=
    let zbitwidth := Z.of_N bitwidth in
    let zhalf := zbitwidth - 1 in

    z <- (arbitrary : G Z);;
    negative <- (arbitrary : G bool);;
    if negative : bool
    then
      ret (-((Z.modulo z (2^zhalf)) + 1))
    else
      ret (Z.modulo z (2^zhalf)).

  Definition gen_gt_zero (bitwidth : option N) : G Z
    := match bitwidth with
       | None =>
           (* Unbounded *)
           n <- (arbitrary : G N);;
           ret (Z.of_N (N.succ n))
       | Some bitwidth =>
           n <- (arbitrary : G N);;
           ret (1 + Z.modulo (Z.of_N n) (2^(Z.of_N bitwidth) - 1))
       end.

  Definition gen_non_zero (bitwidth : option N) : G Z
    := match bitwidth with
       | None =>
           (* Unbounded *)
           x <- gen_gt_zero None;;
           elems_ x [x; -x]
       | Some bitwidth =>
           let zbitwidth := Z.of_N bitwidth in
           let zhalf := zbitwidth - 1 in
           if Z.eqb zhalf 0
           then ret (-1)
           else
             negative <- (arbitrary : G bool);;
             if (negative : bool)
             then
               n <- (arbitrary : G N);;
               ret (-(1 + Z.modulo (Z.of_N n) (2^zhalf)))
             else
               n <- (arbitrary : G N);;
               ret (1 + Z.modulo (Z.of_N n) (2^zhalf - 1))
       end.

  Definition gen_non_zero_exp_size (sz : nat) (t : typ) : GenLLVM (exp typ)
    := match t with
       | TYPE_I n => ret EXP_Integer <*> lift (gen_non_zero (Some n))
       | TYPE_IPTR => ret EXP_Integer <*> lift (gen_non_zero None)
       | TYPE_Float => ret EXP_Float <*> lift fing32 (* TODO: is this actually non-zero...? *)
       | TYPE_Double => failGen "gen_non_zero_exp_size TYPE_Double"(*ret EXP_Double <*> lift fing64*) (*TODO : Fix generator for double*)
       | _ => failGen "gen_non_zero_exp_size"
       end.

  Definition gen_gt_zero_exp_size (sz : nat) (t : typ) : GenLLVM (exp typ)
    := match t with
       | TYPE_I n => ret EXP_Integer <*> lift (gen_gt_zero (Some n))
       | TYPE_IPTR => ret EXP_Integer <*> lift (gen_gt_zero None)
       | TYPE_Float => failGen "gen_gt_zero_exp_size TYPE_Float"
       | TYPE_Double => failGen "gen_gt_zero_exp_size TYPE_Double"(*ret EXP_Double <*> lift fing64*) (*TODO : Fix generator for double*)
       | _ => failGen "gen_gt_zero_exp_size"
       end.

Definition genTypHelper (n: nat): G (string + typ) :=
  run_GenLLVM (gen_typ_non_void_size n).

Definition genType: G (string + typ) :=
  sized genTypHelper.

  Fixpoint gen_exp_size (sz : nat) (t : typ) {struct t} : GenLLVM (exp typ) :=
    match sz with
    | 0%nat =>
      ctx <- get_ctx;;
      let ts := filter_type t ctx in
      let gen_idents :=
          match ts with
          | [] => []
          | _ => [(16%nat, fmap (fun '(i,_) => EXP_Ident i) (elems_LLVM ts))]
          end in
      let fix gen_size_0 (t: typ) :=
          match t with
          | TYPE_I n                  =>
              z <- lift (gen_unsigned_bitwidth n);;
              ret (EXP_Integer z)
          (* lift (x <- (arbitrary : G nat);; ret (Z.of_nat x))
           (* TODO: should the integer be forced to be in bounds? *) *)
          | TYPE_IPTR => ret EXP_Integer <*> lift (arbitrary : G Z)
          | TYPE_Pointer subtyp       => failGen "gen_exp_size TYPE_Pointer"
          (* Only pointer type expressions might be conversions? Maybe GEP? *)
          | TYPE_Void                 => failGen "gen_exp_size TYPE_Void" (* There should be no expressions of type void *)
          | TYPE_Function ret args _   => failGen "gen_exp_size TYPE_Function"(* No expressions of function type *)
          | TYPE_Opaque               => failGen "gen_exp_size TYPE_Opaque" (* TODO: not sure what these should be... *)

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
            | None => failGen "gen_exp_size TYPE_Identified"
            | Some (i,t) => gen_exp_size 0 t
            end
          (* Not generating these types for now *)
          | TYPE_Half                 => failGen "gen_exp_size TYPE_Half"
          | TYPE_Float                => ret EXP_Float <*> lift fing32(* referred to genarators in flocq-quickchick*)
          | TYPE_Double               => failGen "gen_exp_size TYPE_Double" (*ret EXP_Double <*> lift fing64*) (* TODO: Fix generator for double*)
          | TYPE_X86_fp80             => failGen "gen_exp_size TYPE_X86_fp80"
          | TYPE_Fp128                => failGen "gen_exp_size TYPE_Fp128"
          | TYPE_Ppc_fp128            => failGen "gen_exp_size TYPE_Ppc_fp128"
          | TYPE_Metadata             => failGen "gen_exp_size TYPE_Metadata"
          | TYPE_X86_mmx              => failGen "gen_exp_size TYPE_X86_mmx"
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

          | TYPE_Void              => [failGen "gen_exp_size TYPE_VOID list"] (* No void type expressions *)
          | TYPE_Function ret args _ => [failGen "gen_exp_size TYPE_Function list"] (* These shouldn't exist, I think *)
          | TYPE_Opaque            => [failGen "gen_exp_size TYPE_Opaque list"] (* TODO: not sure what these should be... *)
          | TYPE_Half              => [failGen "gen_exp_size TYPE_Half list" ]
          | TYPE_Float             => [gen_fbinop_exp TYPE_Float]
          | TYPE_Double            => [(*gen_fbinop_exp TYPE_Double*)failGen "gen_exp_size TYPE_Double list"]
          | TYPE_X86_fp80          => [failGen "gen_exp_size TYPE_X86_fp80 list"]
          | TYPE_Fp128             => [failGen "gen_exp_size TYPE_Fp128 list"]
          | TYPE_Ppc_fp128         => [failGen "gen_exp_size TYPE_Ppc_fp128 list"]
          | TYPE_Metadata          => [failGen "gen_exp_size TYPE_Metadata list"]
          | TYPE_X86_mmx           => [failGen "gen_exp_size TYPE_X86_mmx list"]
          | TYPE_Identified id     =>
            [ctx <- get_ctx;;
             match find_pred (fun '(i,t) => if Ident.eq_dec id i then true else false) ctx with
             | None => failGen "gen_exp_size TYPE_Identified list"
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

    if Handlers.LLVMEvents.DV.iop_is_div ibinop && Handlers.LLVMEvents.DV.iop_is_signed ibinop
    then
      ret (OP_IBinop ibinop) <*> ret t <*> gen_exp_size 0 t <*> gen_non_zero_exp_size 0 t
    else
      if Handlers.LLVMEvents.DV.iop_is_div ibinop
      then
        ret (OP_IBinop ibinop) <*> ret t <*> gen_exp_size 0 t <*> gen_gt_zero_exp_size 0 t
      else
        exp_value <- gen_exp_size 0 t;;
        if Handlers.LLVMEvents.DV.iop_is_shift ibinop
        then
          let max_shift_size :=
            match t with
            | TYPE_I i => BinIntDef.Z.of_N (i - 1)
            | _ => 0
            end in
          x <- lift (choose (0, max_shift_size));;
          let exp_value2 : exp typ := EXP_Integer x in
          ret (OP_IBinop ibinop t exp_value exp_value2)
        else ret (OP_IBinop ibinop t exp_value) <*> gen_exp_size 0 t
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
       | _ => failGen "gen_fbinop_exp"
      end.

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
            | TYPE_Float => gen_fbinop_exp TYPE_Float
            | TYPE_Double => gen_fbinop_exp TYPE_Double
            | _ => failGen "gen_op"
            end).

  Definition gen_int_texp : GenLLVM (texp typ)
    := t <- gen_int_typ;;
       e <- gen_exp t;;
       ret (t, e).

End ExpGenerators.

Section InstrGenerators.

  (* Generator GEP part *)
  (* Get index paths from array or vector*)
  Definition get_index_paths_from_AoV (sz: N) (t: typ) (pre_path: DList Z) (sub_paths: DList (typ * DList Z)) : DList (typ * DList Z) :=
    N.recursion DList_empty
                (fun ix acc =>
                   let ix_sub_paths := DList_map (fun '(t, sub_path) => (t, DList_append pre_path (DList_cons (Z.of_N ix) sub_path))) sub_paths in
                   DList_append acc ix_sub_paths)
                sz.

  (* Can work after extracting the pointer inside*)
  Fixpoint get_index_paths_aux (t_from : typ) (pre_path : DList Z) {struct t_from}: DList (typ * DList (Z)) :=
    match t_from with
    | TYPE_Array sz t =>
        let sub_paths := get_index_paths_aux t DList_empty in (* Get index path from the first element*)
        DList_cons (t_from, pre_path) (get_index_paths_from_AoV sz t pre_path sub_paths)
    | TYPE_Struct fields
    | TYPE_Packed_struct fields =>
        DList_cons (t_from, pre_path) (get_index_paths_from_struct pre_path fields)
    | _ => DList_singleton (t_from, pre_path)
    end with
  get_index_paths_from_struct (pre_path: DList Z) (fields: list typ) {struct fields}: DList (typ * DList Z) :=
    snd (fold_left
           (fun '(ix, paths) (fld_typ : typ) =>
              (ix + 1,
                (DList_append (get_index_paths_aux fld_typ (DList_append pre_path (DList_singleton ix)))
                              paths)))
           fields (0%Z, DList_empty : DList (typ * DList Z))).

  Definition DList_paths_to_list_paths (paths : DList (typ * DList (Z))) : list (typ * list (Z))
    := map (fun '(x, paths) => (x, DList_to_list paths)) (DList_to_list paths).

  Definition get_index_paths_ptr (t_from: typ) : list (typ * list (Z)) :=
    DList_paths_to_list_paths (get_index_paths_aux t_from (DList_singleton 0%Z)).

  (* Index path without getting into vector *)
  Fixpoint get_index_paths_agg_aux (t_from : typ) (pre_path : DList Z) {struct t_from}: DList (typ * DList (Z)) :=
    match t_from with
    | TYPE_Array sz t =>
        let sub_paths := get_index_paths_agg_aux t DList_empty in (* Get index path from the first element*)
        DList_cons (t_from, pre_path) (get_index_paths_from_AoV sz t pre_path sub_paths)
    | TYPE_Struct fields
    | TYPE_Packed_struct fields =>
        DList_cons (t_from, pre_path) (get_index_paths_agg_from_struct pre_path fields)
    | _ => DList_singleton (t_from, pre_path)
    end with
  get_index_paths_agg_from_struct (pre_path: DList Z) (fields: list typ) {struct fields}: DList (typ * DList Z) :=
    snd (fold_left
           (fun '(ix, paths) (fld_typ : typ) =>
              (ix + 1,
                (DList_append (get_index_paths_agg_aux fld_typ (DList_append pre_path (DList_singleton ix)))
                              paths)))
           fields (0%Z, DList_empty : DList (typ * DList Z))).

  (* The method is mainly used by extractvalue and insertvalue,
     which requires at least one index for getting inside the aggregate type.
     There is a possibility for us to get nil path. The filter below will get rid of that possibility.
     Given that the nilpath will definitely be at the beginning of a list of options, we can essentially get the tail. *)
  Definition get_index_paths_agg (t_from: typ) : list (typ * list (Z)) :=
    tl (DList_paths_to_list_paths (get_index_paths_agg_aux t_from DList_empty)).

  Definition get_ctx_ptrs  : GenLLVM (list (ident * typ)) :=
    typ_ctx <- get_typ_ctx;;
    ctx <- get_ctx;;
    ret (filter_ptr_typs typ_ctx ctx).

  Definition get_ctx_sized_ptrs  : GenLLVM (list (ident * typ)) :=
    typ_ctx <- get_typ_ctx;;
    ctx <- get_ctx;;
    ret (filter_sized_ptr_typs typ_ctx ctx).

  (* Index path without getting into vector *)
  Fixpoint get_index_paths_insertvalue_aux (t_from : typ) (pre_path : DList Z) (ctx : list (ident * typ)) {struct t_from}: bool * DList (typ * DList (Z)) :=
    match t_from with
    | TYPE_Array sz t =>
        let '(has_subpaths, sub_paths) := get_index_paths_insertvalue_aux t DList_empty ctx in (* Get index path from the first element*)
        if has_subpaths
        then (true, DList_cons (t_from, pre_path) (get_index_paths_from_AoV sz t pre_path sub_paths))
        else (false, DList_empty)
    | TYPE_Struct fields
    | TYPE_Packed_struct fields =>
        let '(has_reach, reaches) := (get_index_paths_insertvalue_from_struct pre_path fields ctx) in
        if has_reach
        then (true, DList_cons (t_from, pre_path) reaches)
        else (false, DList_empty)
    | TYPE_Pointer t => if seq.nilp (filter_type t_from ctx) then (false, DList_empty) else (true, DList_singleton (t_from, pre_path))
    | TYPE_Vector _ t =>
        let '(has_subpaths, sub_paths) := get_index_paths_insertvalue_aux t DList_empty ctx in (* Get index path from the first element*)
        if has_subpaths then (true, DList_singleton (t_from, pre_path)) else (false, DList_empty)
    | _ => (true, DList_singleton (t_from, pre_path))
    end with
  get_index_paths_insertvalue_from_struct (pre_path: DList Z) (fields: list typ) (ctx: list (ident * typ)) {struct fields}: bool * DList (typ * DList Z) :=
    snd (fold_left
           (fun '(ix, (b, paths)) (fld_typ : typ) =>
              (ix + 1,
                (let '(has_reach, reach) := get_index_paths_insertvalue_aux fld_typ (DList_append pre_path (DList_singleton ix)) ctx in
                 (orb has_reach b, DList_append reach paths))))
           fields (0%Z, (false, DList_empty : DList (typ * DList Z)))).

  Definition get_index_paths_insertvalue (t_from : typ) (ctx : list (ident * typ)): list (typ * list (Z)) :=
    tl (DList_paths_to_list_paths (snd (get_index_paths_insertvalue_aux t_from DList_empty ctx))).

  Fixpoint has_paths_insertvalue_aux (t_from : typ) (ctx : list (ident * typ)) {struct t_from}: bool :=
    match t_from with
    | TYPE_Array _ t
    | TYPE_Vector _ t => has_paths_insertvalue_aux t ctx
    | TYPE_Struct fields
    | TYPE_Packed_struct fields => fold_left (fun acc x => orb acc (has_paths_insertvalue_aux x ctx)) fields false
    | TYPE_Pointer _ => seq.nilp (filter (fun '(_, x) => normalized_typ_eq x t_from) ctx)
    | _ => true
    end.

  Definition filter_insertvalue_typs (agg_typs : list (ident * typ)) (ctx : list (ident * typ)) : list (ident * typ) :=
    filter (fun '(_, x) => has_paths_insertvalue_aux x ctx) agg_typs.

  Definition get_ctx_ptr : GenLLVM (ident * typ) :=
    ptrs_in_context <- get_ctx_ptrs;;
    '(ptr_ident, ptr_typ) <- elems_LLVM ptrs_in_context;;
    match ptr_typ with
    | TYPE_Pointer t => ret (ptr_ident, t)
    | _ => failGen "get_ctx_ptr" (* Should not happen *)
    end.

  Definition get_ctx_sized_ptr : GenLLVM (ident * typ) :=
    ptrs_in_context <- get_ctx_sized_ptrs;;
    '(ptr_ident, ptr_typ) <- elems_LLVM ptrs_in_context;;
    match ptr_typ with
    | TYPE_Pointer t => ret (ptr_ident, t)
    | _ => failGen "get_ctx_sized_ptr" (* Should not happen *)
    end.

  Definition get_ctx_agg_typs : GenLLVM (list (ident * typ)) :=
    typ_ctx <- get_typ_ctx;;
    ctx <- get_ctx;;
    ret (filter_agg_typs typ_ctx ctx).

  Definition get_ctx_agg_typ : GenLLVM (ident * typ) :=
    aggs_in_context <- get_ctx_agg_typs;;
    elems_LLVM aggs_in_context.

  Definition get_ctx_vec_typs : GenLLVM (list (ident * typ)) :=
    typ_ctx <- get_typ_ctx;;
    ctx <- get_ctx;;
    ret (filter_vec_typs typ_ctx ctx).

  Definition get_ctx_vec_typ : GenLLVM (ident * typ) :=
    vecs_in_context <- get_ctx_vec_typs;;
    elems_LLVM vecs_in_context.

  Definition gen_gep (tptr : typ) : GenLLVM (typ * instr typ) :=
    let get_typ_in_ptr (tptr : typ) :=
      match tptr with
      | TYPE_Pointer t => ret t
      | _ => failGen "gen_gep"
      end in
    t_in_ptr <- get_typ_in_ptr tptr;;
    eptr <- gen_exp_size 0 tptr;;
    let paths_in_ptr := get_index_paths_ptr t_in_ptr in (* Inner paths: Paths after removing the outer pointer *)
    '(ret_t, path) <- elems_LLVM paths_in_ptr;; (* Select one path from the paths *)
    let path_for_gep := map (fun x => (TYPE_I 32, EXP_Integer (x))) path in (* Turning the path to integer *)
    ret (TYPE_Pointer ret_t, INSTR_Op (OP_GetElementPtr t_in_ptr (TYPE_Pointer t_in_ptr, eptr) path_for_gep)).

  Definition gen_extractvalue (tagg : typ): GenLLVM (typ * instr typ) :=
    eagg <- gen_exp_size 0 tagg;;
    let paths_in_agg := get_index_paths_agg tagg in
    '(t, path_for_extractvalue) <- elems_LLVM paths_in_agg;;
    ret (t, INSTR_Op (OP_ExtractValue (tagg, eagg) path_for_extractvalue)).

  Definition gen_insertvalue (tagg: typ): GenLLVM (typ * instr typ) :=
    eagg <- gen_exp_size 0 tagg;;
    ctx <- get_ctx;;
    let paths_in_agg := get_index_paths_insertvalue tagg ctx in
    '(tsub, path_for_insertvalue) <- elems_LLVM paths_in_agg;;
    esub <- hide_ctx (gen_exp_size 0 tsub);;
    (* Generate all of the type*)
    ret (tagg, INSTR_Op (OP_InsertValue (tagg, eagg) (tsub, esub) path_for_insertvalue)).


  (* ExtractElement *)
  Definition gen_extractelement (tvec : typ): GenLLVM (typ * instr typ) :=
    evec <- gen_exp_size 0 tvec;;
    let get_size_ty (vType: typ) :=
      match tvec with
      | TYPE_Vector sz ty => (sz, ty)
      | _ => (0%N, TYPE_Void)
      end in
    let '(sz, t_in_vec) := get_size_ty tvec in
    index_for_extractelement <- lift_GenLLVM (choose (0, Z.of_N sz - 1)%Z);;
    ret (t_in_vec, INSTR_Op (OP_ExtractElement (tvec, evec) (TYPE_I 32%N, EXP_Integer index_for_extractelement))).

  Definition gen_insertelement (tvec : typ) : GenLLVM (typ * instr typ) :=
    evec <- gen_exp_size 0 tvec;;
    let get_size_ty (vType: typ) :=
      match tvec with
      | TYPE_Vector sz ty => (sz, ty)
      | _ => (0%N, TYPE_Void)
      end in
    let '(sz, t_in_vec) := get_size_ty tvec in
    value <- gen_exp_size 0 t_in_vec;;
    index <- lift_GenLLVM (choose (0, Z.of_N (sz - 1)));;
    ret (tvec, INSTR_Op (OP_InsertElement (tvec, evec) (t_in_vec, value) (TYPE_I 32, EXP_Integer index))).

  Definition gen_ptrtoint (tptr : typ): GenLLVM (typ * instr typ) :=
    eptr <- gen_exp_size 0 tptr;;
    let gen_typ_in_ptr (tptr : typ) :=
      match tptr with
      | TYPE_Pointer t =>
          gen_int_typ_for_ptr_cast (* TODO: Wait till IPTR is implemented *)
      | TYPE_Vector sz ty =>
          x <- gen_int_typ_for_ptr_cast;;
          ret (TYPE_Vector sz x)
      | _ =>
          ret (TYPE_Void) (* Won't get into this case *)
      end in
    typ_from_cast <- gen_typ_in_ptr tptr;;
    ret (typ_from_cast, INSTR_Op (OP_Conversion Ptrtoint tptr eptr typ_from_cast)).

  Definition round_up_to_eight (n : N) : N :=
    if N.eqb 0 n
    then 0
    else (((n - 1) / 8) + 1) * 8.

  Fixpoint get_bit_size_from_typ (t : typ) : N :=
    match t with
    | TYPE_I sz => N.max 1 sz
    | TYPE_IPTR => 64 (* TODO: probably kind of a lie... *)
    | TYPE_Pointer t => 64
    | TYPE_Void => 0
    | TYPE_Half => 16
    | TYPE_Float => 32
    | TYPE_Double => 64
    | TYPE_X86_fp80 => 80
    | TYPE_Fp128 => 128
    | TYPE_Ppc_fp128 => 128
    | TYPE_Metadata => 0
    | TYPE_X86_mmx => 64
    | TYPE_Array sz t => sz * (round_up_to_eight (get_bit_size_from_typ t))
    | TYPE_Function ret args vararg => 0
    | TYPE_Struct fields
    | TYPE_Packed_struct fields =>
        fold_right (fun x acc => (round_up_to_eight (get_bit_size_from_typ x) + acc)%N) 0%N fields
    | TYPE_Opaque => 0
    | TYPE_Vector sz t => sz * get_bit_size_from_typ t
    | TYPE_Identified id => 0
    end.

  Fixpoint get_size_from_typ (t: typ) : N :=
    round_up_to_eight (get_bit_size_from_typ t) / 8.

  (* Assuming max_byte_sz for this function is greater than 0 *)
  Definition get_prim_typ_le_size (max_byte_sz: N) : list (GenLLVM typ) :=
    (if (1 <=? max_byte_sz)%N then [ret (TYPE_I 1); ret (TYPE_I 8)] else []) ++
      (if (4 <=? max_byte_sz)%N then [ret (TYPE_I 32); ret TYPE_Float] else []) ++
      (if (8 <=? max_byte_sz)%N then [ret (TYPE_I 64); ret TYPE_Double] else []).

  (* Version without problematic i1 type *)
  Definition get_prim_vector_typ_le_size (max_byte_sz: N) : list (GenLLVM typ) :=
    (if (1 <=? max_byte_sz)%N then [ret (TYPE_I 8)] else []) ++
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
               t <- oneOf_LLVM (get_prim_vector_typ_le_size (max_byte_sz / sz'));;
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
          (* [fields <- gen_typ_from_size_struct max_byte_sz;;
       ret (TYPE_Struct fields)
      ] ++ *) (* Issue #260 *)

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
           ret ([subtyp] ++ tl)%list.

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
    typ_ctx <- get_typ_ctx;;
    '(old_tptr, id, typ_from_cast) <- elems_LLVM ctx;;
    (* In the following case, we will check whether there are double pointers in the old pointer type, we will not cast if the data structure has double pointer *)
    (* TODO: Better identify the pointer inside and cast without changing their location *)
    new_tptr <-
      match old_tptr with
      | TYPE_Pointer old_typ =>
          if typ_contains_pointer old_typ || is_function_type typ_ctx old_typ
          then
            ret old_tptr
          else
            x <- gen_typ_le_size (get_size_from_typ old_typ);;
            ret (TYPE_Pointer x)
      | TYPE_Vector sz (TYPE_Pointer old_typ) =>
          if typ_contains_pointer old_typ || is_function_type typ_ctx old_typ
          then
            ret old_tptr
          else
            x <- gen_typ_le_size (get_size_from_typ old_typ);;
            ret (TYPE_Pointer x)
      | _ => ret (TYPE_Void) (* Won't reach here... Hopefully *)
      end;;
    ret (new_tptr, INSTR_Op (OP_Conversion Inttoptr typ_from_cast (EXP_Ident id) new_tptr)).

  Definition filter_first_class_typs (ctx : var_context) : var_context :=
    filter (fun '(_, t) =>
              match t with
              | TYPE_Struct _
              | TYPE_Packed_struct _ => false
              | TYPE_Array _ _ => false
              | TYPE_Pointer (TYPE_Function _ _ _) => false
              | _ => true
              end) ctx.

  Fixpoint gen_bitcast_typ (t_from : typ) : GenLLVM typ :=
    let gen_typ_list :=
      match t_from with
      | TYPE_I 1 =>
          ret [TYPE_I 1]
      | TYPE_I 8 =>
          ret [TYPE_I 8; TYPE_Vector 8 (TYPE_I 1)]
      | TYPE_I 32
      | TYPE_Float =>
          ret [TYPE_I 32; TYPE_Float; TYPE_Vector 4 (TYPE_I 8); TYPE_Vector 32 (TYPE_I 1)]
      | TYPE_I 64
      | TYPE_Double =>
          ret [TYPE_I 64; TYPE_Double; TYPE_Vector 2 (TYPE_I 32); TYPE_Vector 2 (TYPE_Float); TYPE_Vector 8 (TYPE_I 8); TYPE_Vector 64 (TYPE_I 1)]
      | TYPE_Vector sz subtyp =>
          match subtyp with
          | TYPE_Pointer _ =>
              (* TODO: Clean up. Figure out what can subtyp of pointer be *)
              (* new_subtyp <- gen_bitcast_typ subtyp;; *)
              ret [TYPE_Vector sz subtyp]
          | subtyp =>
              let trivial_typs := [(1%N, TYPE_I 1); (8%N, TYPE_I 8); (32%N, TYPE_I 32); (32%N, TYPE_Float); (64%N, TYPE_I 64); (64%N, TYPE_Double)] in
              let size_of_vec := get_bit_size_from_typ t_from in
              let choices := fold_left (fun acc '(s,t) => let sz' := (size_of_vec / s)%N in
                                                       if (sz' =? 0)%N then acc else (acc ++ [TYPE_Vector sz' t])%list) trivial_typs [] in
              ret choices
          end
      | TYPE_Pointer subtyp =>
          (* TODO: Clean up. Figure out what can subtyp of pointer be *)
          (* new_subtyp <- gen_bitcast_typ subtyp;; *)
          new_subtyp <- gen_sized_typ;;
          ret [TYPE_Pointer new_subtyp]
      | _ => ret [t_from] (* TODO: Add more types *) (* This currently is to prevent types like pointer of struct from failing *)
      end in
    typ_list <- gen_typ_list;;
    elems_LLVM typ_list.

  (* TODO: Another approach to form all first class types for bitcast
   If use this will get O(n^2) runtime where n is the length of the context
   but may make generating trivial types less likely to happen *)
  Fixpoint set_add_h {A} (dec : A -> A -> bool) (t : A) (prev next : list A) :=
    match next with
    | nil => (prev ++ [t])%list
    | hd::tl =>
        if dec hd t
        then (prev ++ next)%list
        else set_add_h dec t (prev ++ [hd]) tl
    end.

  Definition gen_bitcast : GenLLVM (typ * instr typ) :=
    ctx <- get_ctx;;
    let first_class_typs_in_ctx := filter_first_class_typs ctx in
    trivial_typ <- oneOf_LLVM [ret (TYPE_I 1); ret (TYPE_I 8); ret (TYPE_I 32); ret (TYPE_I 64); ret (TYPE_Float); ret (TYPE_Double); ret TYPE_Vector <*> lift_GenLLVM genN <*> gen_typ_non_void_0];;
    let gen_first_class_typs := (ret trivial_typ)::(map (fun '(_, t) => ret t) first_class_typs_in_ctx) in
    tfc <- oneOf_LLVM gen_first_class_typs;;
    efc <- gen_exp_size 0 tfc;;
    new_typ <- gen_bitcast_typ tfc;;
    ret (new_typ, INSTR_Op (OP_Conversion Bitcast tfc efc new_typ)).

  Definition gen_call (tfun : typ) : GenLLVM (typ * instr typ) :=
    efun <- gen_exp_size 0 tfun;;
    match tfun with
    | TYPE_Pointer (TYPE_Function ret_t args varargs) =>
        args_texp <- map_monad
                      (fun (arg_typ:typ) =>
                         arg_exp <- gen_exp_size 0 arg_typ;;
                         ret (arg_typ, arg_exp))
                      args;;
        let args_with_params := map (fun arg => (arg, [])) args_texp in
        ret (ret_t, INSTR_Call (TYPE_Function ret_t args varargs, efun) args_with_params [])
    | _ => failGen "gen_call"
    end.

  (* TODO: move this *)
  Definition genInt : G int
    := fmap Int.repr (arbitrary : G Z).

  Instance GenInt : Gen int
    := Build_Gen int genInt.

  (* TODO: move this. Also give a less confusing name because genOption is a thing? *)
  Definition gen_option {A} (g : G A) : G (option A)
    := freq_ (ret None) [(1%nat, ret None); (7%nat, liftM Some g)].

  (* TODO: move these *)
  Definition opt_add_state {A} {ST} (st : ST) (o : option (A * ST)) : (option A * ST)
    := match o with
       | None => (None, st)
       | (Some (a, st')) => (Some a, st')
       end.

  (* (* TODO: move these *) *)
  Definition either_add_state {A X} {ST} (st : ST) (o : X + (A * ST)) : ((X + A) * ST)
    := match o with
       | inl x => (inl x, st)
       | inr (a, st') => (inr a, st')
       end.

  Definition opt_err_add_state {A} {ST} (st:ST) (o : option (err A * ST)) : err (option A) * ST :=
    match o with
    | None => (inr None, st)
    | Some (inl msg, st) => (inl msg, st)
    | Some (inr a, st)  => (inr (Some a), st)
    end.
  
  Definition gen_opt_LLVM {A} (g : GenLLVM A) : GenLLVM (option A)
    := mkEitherT (mkStateT
         (fun st =>
            opt <- gen_option (runStateT (unEitherT g) st);;
            ret (opt_err_add_state st opt)
            )).

  Definition get_typ_in_ptr (pt : typ) : GenLLVM typ :=
    match pt with
    | TYPE_Pointer t => ret t
    | _ => failGen "get_typ_in_ptr"
    end.

  Definition gen_load (tptr : typ) : GenLLVM (typ * instr typ)
    := eptr <- gen_exp_size 0 tptr;;
       vol <- lift (arbitrary : G bool);;
       ptr_typ <- get_typ_in_ptr tptr;;
       align <- ret (Some 1);;
       (* TODO: Fix parameters / generate more of them *)
       ret (ptr_typ, INSTR_Load ptr_typ (tptr, eptr) []).

  Definition gen_store_to (ptr : texp typ) : GenLLVM (typ * instr typ)
    :=
    match ptr with
    | (TYPE_Pointer t, pexp) =>
        e <- resize_LLVM 0 (gen_exp t);;
        let val := (t, e) in

        ret (TYPE_Void, INSTR_Store val ptr [ANN_align 1])
    | _ => failGen "gen_store_to"
    end.

  Definition gen_store (tptr : typ) : GenLLVM (typ * instr typ)
    :=
    eptr <- gen_exp_size 0 tptr;;
    ptr_typ <- get_typ_in_ptr tptr;;
    gen_store_to(tptr, eptr).

  (* Generate an instruction, as well as its type...

     The type is sometimes void for instructions that don't really
     compute a value, like void function calls, stores, etc.
   *)
  Definition gen_instr : GenLLVM (typ * instr typ) :=
    typ_ctx <- get_typ_ctx;;
    ctx <- get_ctx;;
    ptrtoint_ctx <- get_ptrtoint_ctx;;
    let agg_typs_in_ctx := filter_agg_typs typ_ctx ctx in
    let ptr_vecptr_in_ctx := filter_sized_ptr_vecptr_typs typ_ctx ctx in
    let valid_ptr_vecptr_in_ctx := filter (fun '(_, x) => negb (contains_typ x (TYPE_Struct []) soft)) ptr_vecptr_in_ctx in
    let sized_ptr_typs_in_ctx := filter_sized_ptr_typs typ_ctx ctx in
    let vec_typs_in_ctx := filter_vec_typs typ_ctx ctx in
    let fun_ptrs_in_ctx := filter_function_pointers typ_ctx ctx in
    let insertvalue_typs_in_ctx := filter_insertvalue_typs agg_typs_in_ctx ctx in
    let get_typ_l (ctx : var_context) : GenLLVM typ :=
      var <- elems_LLVM ctx;;
      ret (snd var) in
    oneOf_LLVM
      ([ t <- gen_op_typ;; i <- ret INSTR_Op <*> gen_op t;; ret (t, i)
         ; t <- gen_sized_typ_ptrinctx;;
           (* TODO: generate multiple element allocas. Will involve changing initialization *)
           (* num_elems <- ret None;; (* gen_opt_LLVM (resize_LLVM 0 gen_int_texp);; *) *)
           (* align <- ret None;; *)
           ret (TYPE_Pointer t, INSTR_Alloca t [])
        ] (* TODO: Generate atomic operations and other instructions *)
         ++ (if seq.nilp sized_ptr_typs_in_ctx then [] else [
                 (bind (get_typ_l sized_ptr_typs_in_ctx) gen_gep )
                 ; bind (get_typ_l sized_ptr_typs_in_ctx) gen_load
                 ; bind (get_typ_l sized_ptr_typs_in_ctx) gen_store])
         ++ (if seq.nilp valid_ptr_vecptr_in_ctx then [] else [
                 bind (get_typ_l valid_ptr_vecptr_in_ctx) gen_ptrtoint])
         ++ (if seq.nilp ptrtoint_ctx then [] else [gen_inttoptr])
         ++ (if seq.nilp agg_typs_in_ctx then [] else [
                 bind (get_typ_l agg_typs_in_ctx) gen_extractvalue])
         ++ (if seq.nilp insertvalue_typs_in_ctx then [] else [
                 bind (get_typ_l insertvalue_typs_in_ctx) gen_insertvalue])
         ++ (if seq.nilp vec_typs_in_ctx then [] else [
                 bind (get_typ_l vec_typs_in_ctx) gen_extractelement
                 ; bind (get_typ_l vec_typs_in_ctx) gen_insertelement])
         ++ (if seq.nilp fun_ptrs_in_ctx then [] else [
                 bind (get_typ_l fun_ptrs_in_ctx) gen_call])).

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
       | (IId i, INSTR_Alloca t _) =>
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
         freq_LLVM_thunked
           ([ (6%nat, fun _ => gen_terminator_sz 0 t back_blocks)
           (* Simple jump *)
           ; (min sz' 6%nat, fun _ => '(b, (bh, bs)) <- gen_blocks_sz sz' t back_blocks;; ret (TERM_Br_1 (blk_id b), (bh::bs)))
           (* Conditional branch, with no backloops *)
           ; (min sz' 6%nat,
               fun _ =>
                 c <- gen_exp_size 0 (TYPE_I 1);;

                 (* Generate first branch *)
                 (* We backtrack contexts so blocks in second branch
                      don't refer to variables from the first
                      branch. *)
                 '(b1, (bh1, bs1)) <- backtrack_variable_ctxs (gen_blocks_sz (sz / 2) t back_blocks);;

                 '(b2, (bh2, bs2)) <- gen_blocks_sz (sz / 2) t back_blocks;;

                 ret (TERM_Br (TYPE_I 1, c) (blk_id b1) (blk_id b2), ((bh1::bs1) ++ (bh2::bs2))%list))
            (* Sometimes generate a loop *)
            ; (min sz' 6%nat,
                fun _ =>
                  '(t, (b, bs)) <- gen_loop_sz sz' t back_blocks 10;; (* TODO: Should I replace sz with sz' here*)
                  ret (t, (b :: bs)))
           ]
              ++
              (* Loop back sometimes *)
              match back_blocks with
              | (b::bs) =>
                  [(min sz' 1%nat,
                     fun _ =>
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
      ctxs <- get_variable_ctxs;;
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
      restore_variable_ctxs ctxs;;
      '(loop_b, loop_bs) <- gen_loop_entry_sz (sz / 2) t loop_bid phi_id bid_entry bid_next (EXP_Ident (ID_Local loop_final_init_id_raw)) (EXP_Ident (ID_Local next_instr_raw_id)) back_blocks;;
      let loop_blocks := loop_b :: loop_bs in
      let loop_bid := blk_id loop_b in

      let entry_block := {| blk_id   := bid_entry
                          ; blk_phis := []
                          ; blk_code := entry_code
                          ; blk_term := TERM_Br (TYPE_I 1, (EXP_Ident (ID_Local (instr_id_to_raw_id "loop_cond_id" loop_cond_id)))) loop_bid end_bid
                          ; blk_comments := None
                          |} in

      ret (TERM_Br_1 bid_entry, (entry_block, loop_blocks ++ [next_block] ++ end_blocks))%list
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

  Definition is_main (name : global_id)
    := match name with
       | Name sname => String.string_dec sname "main"%string
       | Anon _
       | Raw _ => false
       end.
  (* Don't want to generate CFGs, actually. Want to generated TLEs *)

  Definition gen_definition (name : global_id) (ret_t : typ) (args : list typ) : GenLLVM (definition typ (block typ * list (block typ)))
    :=
      ctxs <- get_variable_ctxs;;

      (* Add arguments to context *)
      args <- map_monad
               (fun t =>
                  i <- new_raw_id;;
                  ret (i, t))
               args;;
      let args_ctx := map (fun '(i, t) => (ID_Local i, t)) args in
      append_to_ctx args_ctx;;

      bs <- gen_blocks ret_t;;

      let args_t := map snd args in
      let f_type := TYPE_Function ret_t args_t false in
      let param_attr_slots := map (fun t => []) args in
      let prototype :=
          mk_declaration name f_type
                         ([], param_attr_slots)
                         []
                         []
      in
      (* Reset context *)
      let '(ctx, ptoi_ctx) := ctxs in
      restore_variable_ctxs ((ID_Global name, TYPE_Pointer f_type)::ctx, ptoi_ctx);;
      ret (mk_definition (block typ * list (block typ)) prototype (map fst args) bs).

  Definition gen_new_definition (ret_t : typ) (args : list typ) : GenLLVM (definition typ (block typ * list (block typ)))
    :=
      name <- new_global_id;;
      gen_definition name ret_t args.

  Definition gen_helper_function: GenLLVM (definition typ (block typ * list (block typ)))
    :=
    ret_t <- hide_ctx gen_sized_typ_ptrinctx;;
    args  <- listOf_LLVM (hide_ctx gen_sized_typ_ptrinctx);;
    gen_new_definition ret_t args.

  Definition gen_helper_function_tle : GenLLVM (toplevel_entity typ (block typ * list (block typ)))
    := ret TLE_Definition <*> gen_helper_function.

  Definition gen_helper_function_tle_multiple : GenLLVM (list (toplevel_entity typ (block typ * list (block typ))))
    := listOf_LLVM gen_helper_function_tle.

  Definition gen_main : GenLLVM (definition typ (block typ * list (block typ)))
    := gen_definition (Name "main") (TYPE_I 8) [].

  Definition gen_main_tle : GenLLVM (toplevel_entity typ (block typ * list (block typ)))
    := ret TLE_Definition <*> gen_main.

  Definition gen_global_var : GenLLVM (global typ)
    :=
      name <- new_global_id;;
      t <- hide_ctx gen_sized_typ_ptrinctx;;
      opt_exp <- fmap Some (hide_ctx (gen_exp_size 0 t));;
      add_to_ctx (ID_Global name, TYPE_Pointer t);;
      let ann_linkage : list (annotation typ) :=
        match opt_exp with
        | None => [ANN_linkage (LINKAGE_External)]
        | Some _ => []
        end in
      let annotations := ann_linkage in (* TODO: Add more flags *)
      ret (mk_global name t false opt_exp false annotations).

  Definition gen_global_tle : GenLLVM (toplevel_entity typ (block typ * list (block typ)))
    := ret TLE_Global <*> gen_global_var.

  Definition gen_global_tle_multiple : GenLLVM (list (toplevel_entity typ (block typ * list (block typ))))
    := listOf_LLVM  gen_global_tle.

  Definition gen_llvm : GenLLVM (list (toplevel_entity typ (block typ * list (block typ))))
    :=
    globals <- gen_global_tle_multiple;;
    functions <- gen_helper_function_tle_multiple;;
    main <- gen_main_tle;;
    ret (globals ++ functions ++ [main])%list.

End InstrGenerators.
