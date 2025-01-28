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

From Vellvm.Syntax Require Import
  CFG
  TypeUtil
  TypToDtyp.

From Vellvm.Handlers Require Import
  Handlers.

From Vellvm.Semantics Require Import
  TopLevel.

From Vellvm Require Import
  LLVMAst
  Utilities
  AstLib
  DynamicTypes
  DList
  IntMaps
  Utils.Default.

From Vellvm.QC Require Import
  Utils
  Generators
  ECS
  Lens
  GenMetadata.

Require Import Integers.


From ExtLib.Structures Require Export
     Functor Applicative Monads Monoid.

Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Data.Monads.EitherMonad.
Require Import ExtLib.Structures.Foldable.
Require Import ExtLib.Structures.Monads.

Require Import List.

Import ListNotations.

Import ListNotations.
Import MonadNotation.
Import FunctorNotation.
Import LensNotations.
Import ApplicativeNotation.

From Coq Require Import
     ZArith Lia Bool.Bool.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

From ExtLib.Structures Require Export
     Functor.
Open Scope Z_scope.
Open Scope lens.
Open Scope string.

(* Disable guard checking. This file is only used for generating test
    cases. Some of our generation functions terminate in non-trivial
    ways, but since they're only used to generate test cases (and are
    not used in proofs) it's not terribly important to prove that they
    actually terminate.  *)
Unset Guard Checking.

(* Controls whether or not we generate floats... The float generators
often break with updates, so this may be convenient *)
Definition enable_float_generation : bool := true.

Section Helpers.
  Definition l_is_empty {A : Type} (l : list A) : bool :=
    match l with
    | [] => true
    | _ => false
    end.


  Fixpoint is_sized_type_h (t : typ) : bool
    := match t with
       | TYPE_I sz => true
       | TYPE_IPTR => true
       | TYPE_Pointer (Some t) => is_sized_type_h t
       | TYPE_Pointer None => true
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
       | TYPE_Struct fields
       | TYPE_Packed_struct fields =>
           forallb is_sized_type_h fields
       | TYPE_Opaque => false
       | TYPE_Vector sz t => is_sized_type_h t
       | TYPE_Identified id => false
       end.

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
       | TYPE_Pointer (Some (TYPE_Function _ _ _)) => true
       (* TODO: What about opaque pointers?  *)
       | _ => false
       end.

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

  Definition genPosZ : G Z
    :=
      n <- (arbitrary : G nat);;
      ret (Z.of_nat (S n)).
  (* ret (Z.of_nat n). *)
  (* TODO: ^This is the original code. Is this correct??? *)

  Definition genN : G N
    :=
      n <- (arbitrary : G nat);;
      ret (N.of_nat n).

  Definition genPosN : G N
    :=
      n <- (arbitrary : G nat);;
      ret (N.of_nat (S n)).
End Helpers.

Section GenerationState.

  Definition VariableMetadata := Metadata FieldOf.
  Definition VariableMetadataMap := IM.Raw.t VariableMetadata.
  Definition type_context := VariableMetadataMap.
  Definition var_context := VariableMetadataMap.
  Definition ptr_to_int_context := VariableMetadataMap.
  Definition all_local_var_contexts := (var_context * ptr_to_int_context)%type.
  Definition all_var_contexts := (var_context * var_context * ptr_to_int_context)%type.
  Definition ContextMetadata s := Metadata s.

  Record GenState s :=
    mkGenState
    { num_void : N
    ; num_raw  : N
    ; num_global : N
    ; num_blocks : N
    ; context : ContextMetadata s
    ; global_memo : list (global typ)
    ; debug_stack : list string
    }.

  Instance Default_GenState {s} : Default (GenState s)
    :=
    { def := {| num_void   := 0
             ; num_raw    := 0
             ; num_global := 0
             ; num_blocks := 0
             ; context := def
             ; global_memo := []
             ; debug_stack := []
             |}
    }.

  Definition num_void' {s} : Lens' (GenState s) N.
    red.
    intros f F afa gs.
    refine ((fun x => _) <$> afa (_ gs)); try typeclasses eauto.
    - apply mkGenState;
        [ apply x
        | apply (num_raw s)
        | apply (num_global s)
        | apply (num_blocks s)
        | apply (context s)
        | apply (global_memo s)
        | apply (debug_stack s)
        ]; apply gs.
    - apply num_void.
  Defined.

  Definition num_raw' {s} : Lens' (GenState s) N.
    red.
    intros f F afa gs.
    refine ((fun x => _) <$> afa (_ gs)); try typeclasses eauto.
    - apply mkGenState;
        [ apply (num_void s)
        | apply x
        | apply (num_global s)
        | apply (num_blocks s)
        | apply (context s)
        | apply (global_memo s)
        | apply (debug_stack s)
        ]; apply gs.
    - apply num_raw.
  Defined.

  Definition num_global' {s} : Lens' (GenState s) N.
    red.
    intros f F afa gs.
    refine ((fun x => _) <$> afa (_ gs)); try typeclasses eauto.
    - apply mkGenState;
        [ apply (num_void s)
        | apply (num_raw s)
        | apply x
        | apply (num_blocks s)
        | apply (context s)
        | apply (global_memo s)
        | apply (debug_stack s)
        ]; apply gs.
    - apply num_global.
  Defined.

  Definition num_blocks' {s} : Lens' (GenState s) N.
    red.
    intros f F afa gs.
    refine ((fun x => _) <$> afa (_ gs)); try typeclasses eauto.
    - apply mkGenState;
        [ apply (num_void s)
        | apply (num_raw s)
        | apply (num_global s)
        | apply x
        | apply (context s)
        | apply (global_memo s)
        | apply (debug_stack s)
        ]; apply gs.
    - apply num_blocks.
  Defined.

  Definition context' {s} : Lens' (GenState s) (ContextMetadata s).
    red.
    intros f F afa gs.
    refine ((fun x => _) <$> afa (_ gs)); try typeclasses eauto.
    - apply mkGenState;
        [ apply (num_void s)
        | apply (num_raw s)
        | apply (num_global s)
        | apply (num_blocks s)
        | apply x
        | apply (global_memo s)
        | apply (debug_stack s)
        ]; apply gs.
    - apply context.
  Defined.

  Definition global_memo' {s} : Lens' (GenState s) (list (global typ)).
    red.
    intros f F afa gs.
    refine ((fun x => _) <$> afa (_ gs)); try typeclasses eauto.
    - apply mkGenState;
        [ apply (num_void s)
        | apply (num_raw s)
        | apply (num_global s)
        | apply (num_blocks s)
        | apply (context s)
        | apply x
        | apply (debug_stack s)
        ]; apply gs.
    - apply global_memo.
  Defined.

  Definition debug_stack' {s} : Lens' (GenState s) (list string).
    red.
    intros f F afa gs.
    refine ((fun x => _) <$> afa (_ gs)); try typeclasses eauto.
    - apply mkGenState;
        [ apply (num_void s)
        | apply (num_raw s)
        | apply (num_global s)
        | apply (num_blocks s)
        | apply (context s)
        | apply (global_memo s)
        | apply x
        ]; apply gs.
    - apply debug_stack.
  Defined.


  Definition increment_raw {s} (gs : GenState s) : GenState s
    := gs & num_raw' %~ N.succ.

  Definition increment_global {s} (gs : GenState s) : GenState s
    := gs & num_global' %~ N.succ.

  Definition increment_void {s} (gs : GenState s) : GenState s
    := gs & num_void' %~ N.succ.

  Definition increment_blocks {s} (gs : GenState s) : GenState s
    := gs & num_blocks' %~ N.succ.

  Definition replace_local_ctx {s} (ctx : Component s Field unit) (gs : GenState s) : GenState s
    := gs & (context' .@  is_local') .~ ctx.

  Definition replace_global_ctx {s} (ctx : Component s Field unit) (gs : GenState s) : GenState s
    := gs & (context' .@  is_global') .~ ctx.

  Definition replace_typ_ctx {s} (typ_ctx : Component s Field typ) (gs : GenState s) : GenState s
    := gs & (context' .@ type_alias') .~ typ_ctx.

  Definition replace_ptrtoint_ctx {s} (ptrtoint_ctx : Component s Field Ent) (gs: GenState s) : GenState s
    := gs & (context' .@ from_pointer') .~ ptrtoint_ctx.

  Definition replace_global_memo {s} (global_memo : list (global typ)) (gs : GenState s) : GenState s
    := gs & global_memo' .~ global_memo.

  Definition GenLLVM := (eitherT string (SystemT GenState G)).

  (* Need this because extlib doesn't declare this instance as global :|. *)
  #[global] Instance monad_stateT {s m} `{Monad m} : Monad (stateT s m).
  Proof.
    apply Monad_stateT;
      typeclasses eauto.
  Defined.

  #[global] Instance MonadState_GenLLVM : MonadState (SystemState GenState G) GenLLVM.
  unfold SystemT.
  try typeclasses eauto.
  Defined.

  Definition gen_context' : Lens' (SystemState GenState G) (ContextMetadata _)
    := (metadata .@ context').

  Definition get_raw {s} (gs : GenState s) : N
    := gs .^ num_raw'.

  Definition get_global {s} (gs : GenState s) : N
    := gs .^ num_global'.

  Definition get_void {s} (gs : GenState s) : N
    := gs .^ num_void'.

  Definition get_blocks {s} (gs : GenState s) : N
    := gs .^ num_blocks'.

  Definition new_id {ID} (id_lens : forall {s : StorageType}, Lens' (GenState s) N) (id_gen : N -> ID) : GenLLVM ID
    := n <- use (metadata .@ num_raw');;
       metadata .@ num_raw' %= N.succ;;
       ret (id_gen n).

  Definition new_local_id : GenLLVM local_id
    := new_id (@num_raw') (fun n => Name ("v" ++ show n)).

  Definition new_global_id : GenLLVM global_id
    := new_id (@num_raw') (fun n => Name ("g" ++ show n)).

  Definition new_void_id : GenLLVM instr_id
    := new_id (@num_void') (fun n => IVoid (Z.of_N n)).

  Definition new_block_id : GenLLVM block_id
    := new_id (@num_blocks') (fun n => Name ("b" ++ show n)).

  (* #[global] Instance STGST : Monad (stateT GenState G). *)
  (* apply Monad_stateT. *)
  (* typeclasses eauto. *)
  (* Defined. *)

  #[global] Instance MGEN : Monad GenLLVM.
  unfold GenLLVM.
  apply Monad_eitherT.
  typeclasses eauto.
  Defined.

  (* GC: For following, I will leave pieces defined in another way so I can learn more about how to use monad *)
  (* Definition lift_GenLLVM {A} (g : G A) : GenLLVM A := *)
  (* mkEitherT (mkStateT (fun stack => mkStateT (fun st => a <- g;; ret (inr a, stack, st)))). *)

  Definition lift_GenLLVM {A} (g : G A) : GenLLVM A.
    unfold GenLLVM.
    apply mkEitherT.
    apply mkStateT.
    (* intros. *)
    refine (fun st => _).
    refine (a <- g ;; ret _).
    exact (inr a, st).
  Defined.

  #[global] Instance MGENT: MonadT GenLLVM G.
  unfold GenLLVM.
  constructor.
  exact @lift_GenLLVM.
  Defined.

  Definition lift_system_GenLLVM {A} (system : SystemT GenState G A) : GenLLVM A.
    unfold GenLLVM.
    apply mkEitherT.
    apply (fmap ret system).
  Defined.

  #[global] Instance MGENTSYSTEM: MonadT GenLLVM (SystemT GenState G).
  unfold GenLLVM.
  constructor.
  exact @lift_system_GenLLVM.
  Defined.

  (* SAZ:
     [failGen] was the one piece of the backtracking variant of QuickChick we
     needed.
   *)
  (* Definition failGen {A:Type} (s:string) : GenLLVM A := *)
  (* mkEitherT (mkStateT (fun stack => ret (inl s, stack))). *)

  Definition failGen {A:Type} (s:string) : GenLLVM A.
    apply mkEitherT.
    apply mkStateT.
    refine (fun stack => _).
    exact (ret (inl (s), stack)).
  Defined.

  Definition annotate {A:Type} (s:string) (g : GenLLVM A) : GenLLVM A
    := old_stack <- use (metadata .@ debug_stack');;
       metadata .@ debug_stack' %= (fun stack => s :: stack);;
       a <- g;;
       metadata .@ debug_stack' .= old_stack;;
       ret a.

  Definition annotate_debug (s : string) : GenLLVM unit :=
    annotate s (ret tt).

  Definition dup_string_wrt_nat (s : string) (n : nat) :=
    let fix dup_string_wrt_nat_tail_recur (acc : string) (n : nat):=
      match n with
      | 0%nat => acc
      | S z => dup_string_wrt_nat_tail_recur (s ++ acc)%string z
      end in dup_string_wrt_nat_tail_recur "" n.

  #[global] Instance MetadataStore_GenState : @MetadataStore G Metadata (SystemState GenState G).
  split.
  apply gen_context'.
  Defined.

  Definition contextFromMap {a} (m : IM.Raw.t a) : GenLLVM var_context
    := IM.Raw.fold
         (fun (k : Z) _ (acc : GenLLVM var_context) =>
            e <- lift_system_GenLLVM (getEntity (mkEnt k));;
            ctx <- acc;;
            ret (IM.Raw.add k e ctx)
         ) m (ret (IM.Raw.empty _)).

  Definition get_local_ctx : GenLLVM var_context
    := locals <- use (gen_context' .@ is_local');;
       contextFromMap locals.

  Definition get_global_ctx : GenLLVM var_context
    := globals <- use (gen_context' .@ is_global');;
       contextFromMap globals.

  Definition merge_var_context (c1 : var_context) (c2 : var_context) : var_context
    := IM.Raw.merge c1 c2.

  Definition get_ctx : GenLLVM var_context
    := locals <- use (gen_context' .@ is_local');;
       globals <- use (gen_context' .@ is_global');;
       contextFromMap (IM.Raw.merge globals locals).

  Definition get_typ_ctx : GenLLVM type_context
    := types <- use (gen_context' .@ type_alias');;
       contextFromMap types.

  Definition get_ptrtoint_ctx : GenLLVM ptr_to_int_context
    := ptois <- use (gen_context' .@ from_pointer');;
       contextFromMap ptois.

  (* Get all variable contexts that might need to be saved *)
  Definition get_variable_ctxs : GenLLVM all_var_contexts
    := local_ctx <- get_local_ctx;;
       global_ctx <- get_global_ctx;;
       ptoi_ctx <- get_ptrtoint_ctx;;
       ret (local_ctx, global_ctx, ptoi_ctx).

  Definition get_global_memo : GenLLVM (list (global typ))
    := use (metadata .@ global_memo').

  Definition set_local_ctx (ctx : var_context) : GenLLVM unit
    := lift (setEntities ctx).

  Definition set_global_ctx (ctx : var_context) : GenLLVM unit
    := lift (setEntities ctx).

  Definition set_ptrtoint_ctx (ptoi_ctx : ptr_to_int_context) : GenLLVM unit
    := lift (setEntities ptoi_ctx).

  Definition set_global_memo (memo : list (global typ)) : GenLLVM unit
    := (metadata .@ global_memo') .= memo;;
       ret tt.

  Definition add_to_global_memo (x : (global typ)) : GenLLVM unit
    := (metadata .@ global_memo') %= (fun memo => x :: memo);;
       ret tt.

  Definition restore_variable_ctxs (ctxs : all_var_contexts) : GenLLVM unit
    := match ctxs with
       | (local_ctx, global_ctx, ptoi_ctx) =>
           set_local_ctx local_ctx;;
           set_global_ctx global_ctx;;
           set_ptrtoint_ctx ptoi_ctx
       end.

  Definition restore_local_variable_ctxs (ctxs : all_local_var_contexts) : GenLLVM unit
    := match ctxs with
       | (local_ctx, ptoi_ctx) =>
           set_local_ctx local_ctx;;
           set_ptrtoint_ctx ptoi_ctx
       end.

  Definition append_ctx (vars :var_context) : GenLLVM unit
    := lift (setEntities vars).

  (* This is very aggressive and will reset entities / entity counter *)
  Definition backtrackMetadata {A} (g : GenLLVM A) : GenLLVM A
    := m <- use gen_context';;
       a <- g;;
       gen_context' .= m;;
       ret a.

  Definition reset_local_ctx : GenLLVM unit
    := locals <- use (gen_context' .@ is_local');;
       lift (deleteEntities locals).

  Definition reset_global_ctx : GenLLVM unit
    := globals <- use (gen_context' .@ is_global');;
       lift (deleteEntities globals).

  Definition reset_ctx : GenLLVM unit
    := reset_local_ctx;;
       reset_global_ctx.

  Definition reset_typ_ctx : GenLLVM unit
    := types <- use (gen_context' .@ type_alias');;
       lift (deleteEntities types).

  Definition reset_ptrtoint_ctx : GenLLVM unit
    := ptrs <- use (gen_context' .@ from_pointer');;
       lift (deleteEntities ptrs).

  Definition reset_global_memo : GenLLVM unit
    := metadata .@ global_memo' .= def;;
       ret tt.

  Definition hide_local_ctx {A} (g : GenLLVM A) : GenLLVM A
    := saved_local_ctx <- get_local_ctx;;
       reset_local_ctx;;
       a <- g;;
       set_local_ctx saved_local_ctx;;
       ret a.

  Definition hide_global_ctx {A} (g : GenLLVM A) : GenLLVM A
    := saved_global_ctx <- get_global_ctx;;
       reset_global_ctx;;
       a <- g;;
       set_global_ctx saved_global_ctx;;
       ret a.

  Definition hide_ctx {A} (g: GenLLVM A) : GenLLVM A
    := hide_global_ctx (hide_local_ctx g).

  Definition hide_ptrtoint_ctx {A} (g: GenLLVM A) : GenLLVM A
    := saved_ctx <- get_ptrtoint_ctx;;
       reset_ptrtoint_ctx;;
       a <- g;;
       append_ctx saved_ctx;;
       ret a.

  Definition hide_variable_ctxs {A} (g: GenLLVM A) : GenLLVM A
    := hide_ctx (hide_ptrtoint_ctx g).

  (** Restore context after running a generator. *)
  Definition backtrack_local_ctx {A} (g: GenLLVM A) : GenLLVM A
    := saved_local_ctx <- get_local_ctx;;
       a <- g;;
       reset_local_ctx;;
       set_local_ctx saved_local_ctx;;
       ret a.

  Definition backtrack_global_ctx {A} (g: GenLLVM A) : GenLLVM A
    := saved_global_ctx <- get_global_ctx;;
       a <- g;;
       reset_global_ctx;;
       set_global_ctx saved_global_ctx;;
       ret a.

  Definition backtrack_ctx {A} (g : GenLLVM A) : GenLLVM A
    := backtrack_global_ctx (backtrack_local_ctx g).

  (** Restore ptrtoint context after running a generator. *)
  Definition backtrack_ptrtoint_ctx {A} (g: GenLLVM A) : GenLLVM A
    := saved_ctx <- get_ptrtoint_ctx;;
       a <- g;;
       reset_global_ctx;;
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
    :=
    (* ctx <- get_ctx;; *)
    (* let is_empty := l_is_empty ctx in *)
    fst
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
            gs (failGen ("freq_LLVM" (* ++ newline ++ if (is_empty) then "Current context is empty" else "Current context: " ++ show ctx *)), 0%N)).

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

  Definition sized_LLVM {A : Type} (gn : nat -> GenLLVM A) : GenLLVM A.
    apply mkEitherT.
    apply mkStateT.
    refine (fun st => sized _).
    refine (fun n => _).
    refine (let opt := unEitherT (gn n) in _).
    refine (let ann := runStateT opt st in ann).
    Defined.

  (* Definition sized_LLVM {A : Type} (gn : nat -> GenLLVM A) : GenLLVM A *)
  (*   := mkEitherT (mkStateT *)
  (*                   (fun st => sized (fun n => runStateT (unEitherT (gn n)) st))). *)

  Definition resize_LLVM {A : Type} (sz : nat) (g : GenLLVM A) : GenLLVM A.
    apply mkEitherT.
    apply mkStateT.
    refine (fun st => _).
    refine (let opt := unEitherT g in _).
    refine (let ans := runStateT opt st in _).
    refine (resize sz ans).
    Defined.

  (* Definition resize_LLVM {A : Type} (sz : nat) (g : GenLLVM A) : GenLLVM A *)
  (*   := mkEitherT (mkStateT *)
  (*                   (fun st => resize sz (runStateT (unEitherT g) st))). *)

  Definition listOf_LLVM {A : Type} (g : GenLLVM A) : GenLLVM (list A) :=
    sized_LLVM (fun n =>
                  k <- lift (choose (0, n)%nat);;
                  vectorOf_LLVM k g).

  Definition nonemptyListOf_LLVM
             {A : Type} (g : GenLLVM A) : GenLLVM (list A)
    := sized_LLVM (fun n =>
                     k <- lift (choose (1, n)%nat);;
                     vectorOf_LLVM k g).

  Definition run_GenLLVM {A} (g: GenLLVM A) : G (string + A) :=
    let ran := runStateT (unEitherT g) def in
    '(err_a,st) <- ran;;
    let stack := st .^ metadata .@ debug_stack' in
    let debug : string := fold_right (fun d1 drest => (d1 ++ newline ++ drest)%string) "" (rev stack) in
    let flushed_err :=
      match err_a with
      | inl err_str => inl (err_str ++ newline ++ "DEBUG SECTION: " ++ newline ++ debug)%string
      | inr _ => err_a
      end in
    ret flushed_err.

End GenerationState.

Section TypGenerators.
  Definition assign_if {m : Type -> Type} {s a b : Type} `{HM : Monad m} `{ST : @MonadState s m}
    (cnd : bool) (l : ASetter s s a b) (v : b) : m unit
    := if cnd then l .= v;; ret tt else ret tt.

  Definition bool_setter (cnd : bool) : Update unit
    := if cnd then SetValue _ tt else Unset _.

  Definition GenQuery' m := QueryT Metadata m.
  Definition runGenQuery {m A E}
    `{TE : ToEnt E}
    `{Monad m}
    `{MS: MetadataStore m Metadata (SystemState GenState m)}
    `{MT: MonadT (SystemT GenState m) m}
    (q : GenQuery' m A) (k : E) : SystemT GenState m (option A):=
    let e := toEnt k in
    meta <- getEntity e;;
    lift (unQueryT q e meta).
  Definition GenQuery := GenQuery' G.

  Definition runGenQueryLLVM {A E} `{TE : ToEnt E}
    (q : GenQuery A) (k : E) : GenLLVM (option A):=
    lift (runGenQuery q k).

  (* Attempt to find a matching entity in the context...
     Note: this is not a random selection, the first thing found is returned.
   *)
  Definition genFind {a es E}
    `{ToEnt E} `{Foldable es E}
    (focus : @EntTarget es E _ _ GenState G)
    (filter : GenQuery a)
    : GenLLVM (option a)
    := lift (efind focus filter).

  (* Normalize a type using the GenState to look up type aliases *)
  Program Fixpoint normalize_type_GenLLVM (t : typ) : GenLLVM typ :=
    match t with
    | TYPE_Array sz t =>
        nt <- normalize_type_GenLLVM t;;
        ret (TYPE_Array sz nt)

    | TYPE_Function ret_t args varargs =>
        nret <- normalize_type_GenLLVM ret_t;;
        nargs <- map_monad normalize_type_GenLLVM args;;
        ret (TYPE_Function nret nargs varargs)

    | TYPE_Struct fields =>
        nfields <- map_monad normalize_type_GenLLVM fields;;
        ret (TYPE_Struct nfields)

    | TYPE_Packed_struct fields =>
        nfields <- map_monad normalize_type_GenLLVM fields;;
        ret (TYPE_Packed_struct nfields)

    | TYPE_Vector sz t =>
        nt <- normalize_type_GenLLVM t;;
        ret (TYPE_Vector sz nt)

    | TYPE_Identified id =>
        ot <- genFind
               (use (gen_context' .@ type_alias'))
               (n <- queryl name';;
                if Ident.eq_dec id n
                then queryl type_alias'
                else mzero);;
        match ot with
        | Some t' =>
            normalize_type_GenLLVM t'
        | None =>
            ret (TYPE_Identified id)
        end
    | TYPE_I sz => ret t
    | TYPE_IPTR => ret t
    | TYPE_Pointer (Some t') =>
        pt <- normalize_type_GenLLVM t';;
        ret (TYPE_Pointer (Some pt))
    | TYPE_Pointer None => ret t
    | TYPE_Void => ret t
    | TYPE_Half => ret t
    | TYPE_Float => ret t
    | TYPE_Double => ret t
    | TYPE_X86_fp80 => ret t
    | TYPE_Fp128 => ret t
    | TYPE_Ppc_fp128 => ret t
    | TYPE_Metadata => ret t
    | TYPE_X86_mmx => ret t
    | TYPE_Opaque => ret t
    end.

  (* Only works correctly if the type is well formed *)
  Definition is_sized_type (t : typ) : GenLLVM bool
    := t' <- normalize_type_GenLLVM t;;
       ret (is_sized_type_h t').

  (* TODO: handle opaque PTR *)
  Definition typ_metadata_setter (τ : typ) : GenLLVM (Metadata SetterOf) :=
    normalized <- normalize_type_GenLLVM τ;;
    let st := is_sized_type_h normalized in
    ret (def
         & (@normalized_type' SetterOf .~ SetValue _ normalized)
         & (@is_sized' SetterOf .~ bool_setter st)
         & (@is_pointer' SetterOf .~ bool_setter (match τ with | TYPE_Pointer _ => true | _ => false end))
         & (@is_sized_pointer' SetterOf .~
              bool_setter
              (match τ with
               | TYPE_Pointer τ' => st
               | _ => false
               end))
         & (@is_aggregate' SetterOf .~
              bool_setter
              (match normalized with
               | TYPE_Array _ _
               | TYPE_Struct _
               | TYPE_Packed_struct _ => true
               | _ => false
               end))
         & (@is_indexable' SetterOf .~
              bool_setter
              (match normalized with
               | TYPE_Array sz _ => N.ltb 0 sz
               | TYPE_Struct l
               | TYPE_Packed_struct l => negb (l_is_empty l)
               | _ => false
               end))
         & (@is_non_void' SetterOf .~
              bool_setter
              (match normalized with
               | TYPE_Void => false
               | _ => true
               end))
         & (@is_vector' SetterOf .~
              bool_setter
              (match normalized with
               | TYPE_Vector _ _ => true
               | _ => false
               end))
         & (@is_ptr_vector' SetterOf .~
              bool_setter
              (match normalized with
               | TYPE_Pointer _ => true
               | TYPE_Vector _ (TYPE_Pointer _) => true
               | _ => false
               end))
         & (@is_sized_ptr_vector' SetterOf .~
              bool_setter
              (match normalized with
               | TYPE_Pointer t => st
               | TYPE_Vector _ (TYPE_Pointer t) => st
               | _ => false
               end))
         & (@is_first_class_type' SetterOf .~
              bool_setter
              (match normalized with
               | TYPE_Struct _
               | TYPE_Packed_struct _ => false
               | TYPE_Array _ _ => false
               | TYPE_Pointer (Some (TYPE_Function _ _ _)) => false
               | _ => true
               end))
         & (@is_function_pointer' SetterOf .~
              bool_setter (is_function_pointer_h normalized))).

  Definition set_typ_metadata (e : Ent) (τ : typ) : GenLLVM unit
    := setter <- typ_metadata_setter τ;;
       lift (setEntity e setter).

  Definition add_to_local_ctx (x : (ident * typ)) : GenLLVM Ent
    := let '(n, t) := x in
       e <- lift newEntity;;
       (gen_context' .@ entl e .@ is_local') .= ret tt;;
       (gen_context' .@ entl e .@ name') .= ret n;;
       (gen_context' .@ entl e .@ variable_type') .= ret t;;
       (* Default to deterministic *)
       (gen_context' .@ entl e .@ deterministic') .= true;;
       set_typ_metadata e t;;
       ret e.

  Definition genLocalEnt (τ : typ) : GenLLVM (ident * Ent)
    :=  n <- ID_Local <$> new_local_id;;
        e <- add_to_local_ctx (n, τ);;
        ret (n, e).

  Definition genLocal (τ : typ) : GenLLVM ident
    :=  fst <$> genLocalEnt τ.

  Definition add_to_global_ctx (x : (ident * typ)) : GenLLVM Ent
    := let '(n, t) := x in
       e <- lift newEntity;;
       (gen_context' .@ entl e .@ is_global') .= ret tt;;
       (gen_context' .@ entl e .@ name') .= ret n;;
       (gen_context' .@ entl e .@ variable_type') .= ret t;;
       (* Default to deterministic *)
       (gen_context' .@ entl e .@ deterministic') .= true;;
       set_typ_metadata e t;;
       ret e.

  Definition genGlobalEnt (τ : typ) : GenLLVM (ident * Ent)
    :=  n <- ID_Global <$> new_global_id;;
        e <- add_to_global_ctx (n, τ);;
        ret (n, e).

  Definition genGlobal (τ : typ) : GenLLVM ident
    := fst <$> genGlobalEnt τ.

  (* A little uncertain about this. Should void instructions have
  names? Cannot refer to their results anyway, so maybe not? *)
  Definition genVoidEnt : GenLLVM (instr_id * Ent)
    :=  e <- lift newEntity;;
        n <- new_void_id;;
       set_typ_metadata e TYPE_Void;;
       ret (n, e).

  Definition genVoid : GenLLVM instr_id
    :=  fmap fst genVoidEnt.

  (* Generate an id for the instruction given the return type *)
  Definition genInstrIdEnt (τ : typ) : GenLLVM (instr_id * Ent)
    := match τ with
       | TYPE_Void => genVoidEnt
       | _ => (fun '(n, e) => (IId (ident_to_raw_id n), e)) <$> genLocalEnt τ
       end.

  (* Generate an id for the instruction given the return type *)
  Definition genInstrId (τ : typ) : GenLLVM instr_id
    := match τ with
       | TYPE_Void => genVoid
       | _ => (fun (n : ident) => IId (ident_to_raw_id n)) <$> genLocal τ
       end.

  Definition add_to_typ_ctx (x : (ident * typ)) : GenLLVM unit
    := let '(n, t) := x in
       e <- lift newEntity;;
       (gen_context' .@ entl e .@ name') .= ret n;;
       (gen_context' .@ entl e .@ type_alias') .= ret t;;
       set_typ_metadata e t;;
       st <- use (gen_context' .@ entl e .@ is_sized');;
       (gen_context' .@ entl e .@ is_sized_type_alias') .= st;;
       (gen_context' .@ entl e .@ is_sized') .= None;;
       (* Disable type alias usage for now. See https://github.com/vellvm/vellvm/issues/361 *)
       (gen_context' .@ entl e .@ type_alias') .= None;;
       (gen_context' .@ entl e .@ is_sized_type_alias') .= None;;
       ret tt.

  (* Should this be a local? *)
  Definition add_to_ptrtoint_ctx (x : (typ * ident * Ent)) : GenLLVM unit
    := let '(t, name, ptr) := x in
       e <- lift newEntity;;
       (gen_context' .@ entl e .@ name') .= ret name;;
       (gen_context' .@ entl e .@ is_local') .= ret tt;;
       (gen_context' .@ entl e .@ from_pointer') .= ret ptr;;
       (* non-deterministic if the pointer is (could have
          deterministic pointers like null) *)
       d <- use (gen_context' .@ entl ptr .@ deterministic');;
       (gen_context' .@ entl e .@ deterministic') .= d;;
       set_typ_metadata e t;;
       ret tt.


  (* (*filter all the (ident, typ) in ctx such that typ is a ptr*) *)
  (* Definition filter_ptr_typs (typ_ctx : type_context) (ctx : var_context) : var_context := *)
  (*   filter (fun '(_, t) => match normalize_type typ_ctx t with *)
  (*                       | TYPE_Pointer _ => true *)
  (*                       | _ => false *)
  (*                       end) ctx. *)

  (* Definition filter_sized_ptr_typs (typ_ctx : type_context) (ctx : var_context) : var_context := *)
  (*   filter (fun '(_, t) => match normalize_type typ_ctx t with *)
  (*                       | TYPE_Pointer t => is_sized_type typ_ctx t *)
  (*                       | _ => false *)
  (*                       end) ctx. *)

  (* Definition filter_sized_typs (typ_ctx: type_context) (ctx : var_context) : var_context := *)
  (*   filter (fun '(_, t) => is_sized_type typ_ctx t) ctx. *)

  (* Definition filter_non_void_typs (typ_ctx : type_context) (ctx : var_context) : var_context := *)
  (*   filter (fun '(_, t) => match normalize_type typ_ctx t with *)
  (*                       | TYPE_Void => false *)
  (*                       | _ => true *)
  (*                       end) ctx. *)

  (* Definition filter_agg_typs (typ_ctx : type_context) (ctx: var_context) : var_context := *)
  (*   filter (fun '(_, t) => *)
  (*             match normalize_type typ_ctx t with *)
  (*             | TYPE_Array sz _ => N.ltb 0 sz *)
  (*             | TYPE_Struct l *)
  (*             | TYPE_Packed_struct l => negb (l_is_empty l) *)
  (*             | _ => false *)
  (*             end ) ctx. *)

  (* Definition filter_vec_typs (typ_ctx : type_context) (ctx: var_context) : var_context := *)
  (*   filter (fun '(_, t) => *)
  (*             match normalize_type typ_ctx t with *)
  (*             | TYPE_Vector _ _ => true *)
  (*             | _ => false *)
  (*             end) ctx. *)

  (* Definition filter_ptr_vecptr_typs (typ_ctx : type_context) (ctx: var_context) : var_context := *)
  (*   filter (fun '(_, t) => *)
  (*             match normalize_type typ_ctx t with *)
  (*             | TYPE_Pointer _ => true *)
  (*             | TYPE_Vector _ (TYPE_Pointer _) => true *)
  (*             | _ => false *)
  (*             end) ctx. *)

  (* Definition filter_sized_ptr_vecptr_typs (typ_ctx : type_context) (ctx: var_context) : var_context := *)
  (*   filter (fun '(_, t) => *)
  (*             match normalize_type typ_ctx t with *)
  (*             | TYPE_Pointer t => is_sized_type typ_ctx t *)
  (*             | TYPE_Vector _ (TYPE_Pointer t) => is_sized_type typ_ctx t *)
  (*             | _ => false *)
  (*             end) ctx. *)

  Definition gen_IntMapRaw_key_filter {a b} (m : IM.Raw.t a) (filter : GenQuery b) : GenLLVM (option Z)
    := '(g, _) <- (IM.Raw.fold
                    (fun key _ (grest : GenLLVM (option Z * N)) =>
                       cnd <- is_some <$> runGenQueryLLVM filter key;;
                       '(gacc, k) <- grest;;
                       swap <- lift (fmap (N.eqb 0) (choose (0%N, k)));;
                       let k' := if cnd then (k+1)%N else k in
                       if swap && cnd
                       then (* swap *)
                         ret (Some key, k')
                       else (* No swap *)
                         ret (gacc, k'))
                    m (ret (@None Z, 0%N)));;
       ret g.

  Definition gen_IntMapRaw_filter {a b} (m : IM.Raw.t a) (filter : GenQuery b) : GenLLVM (option b)
    := '(g, _) <- (IM.Raw.fold
                    (fun key _ (grest : GenLLVM (option b * N)) =>
                       qres <- runGenQueryLLVM filter key;;
                       let cnd := is_some qres in
                       '(gacc, k) <- grest;;
                       swap <- lift (fmap (N.eqb 0) (choose (0%N, k)));;
                       let k' := if cnd then (k+1)%N else k in
                       if swap && cnd
                       then (* swap *)
                         ret (qres, k')
                       else (* No swap *)
                         ret (gacc, k'))
                    m (ret (@None b, 0%N)));;
       ret g.

  Definition gen_IntMapRaw_key {a} (m : IM.Raw.t a) : GenLLVM (option Z)
    := gen_IntMapRaw_key_filter m (ret tt).

  Definition gen_IntMapRaw_ent {a} (m : IM.Raw.t a) : GenLLVM (option Ent)
    := fmap (fmap mkEnt) (gen_IntMapRaw_key m).

  Definition gen_IntMapRaw_ent_filter {a b} (m : IM.Raw.t a) (filter : GenQuery b) : GenLLVM (option Ent)
    := fmap (fmap mkEnt) (gen_IntMapRaw_key_filter m filter).

  Definition gen_sized_type_alias : GenLLVM (option ident)
    := es <- use (gen_context' .@ is_sized_type_alias');;
       var <- gen_IntMapRaw_ent_filter es (withoutl is_function_pointer');;
       match var with
       | Some var =>
           id <- use (gen_context' .@ entl var .@ name');;
           ret id
       | None => ret None
       end.

  Definition gen_entity_with {a} (focus : Lens' (SystemState GenState G) (IM.Raw.t a)): GenLLVM (option Ent)
    := es <- use focus;;
       gen_IntMapRaw_ent es.

  Definition gen_entity_with_filter {a b}
    (focus : Lens' (SystemState GenState G) (IM.Raw.t a))
    (filter : GenQuery b)
    : GenLLVM (option Ent)
    := es <- use focus;;
       gen_IntMapRaw_ent_filter es filter.

  (* Randomly select from all matching entities in the context *)
  Definition gen_foldable_filter_ent {b es E} `{ToEnt E} `{Foldable es E}
    (m : es) (filter : GenQuery b) : GenLLVM (option (Ent * b))
    := '(g, _) <- (fold _
                    (fun key (grest : GenLLVM (option (Ent * b) * N)) =>
                       qres <- runGenQueryLLVM filter key;;
                       let cnd := is_some qres in
                       '(gacc, k) <- grest;;
                       swap <- lift (fmap (N.eqb 0) (choose (0%N, k)));;
                       let k' := if cnd then (k+1)%N else k in
                       if swap && cnd
                       then (* swap *)
                         ret (fmap (fun x => (toEnt key, x)) qres, k')
                       else (* No swap *)
                         ret (gacc, k'))
                    (ret (@None (Ent * b), 0%N))) m;;
       ret g.

  Definition gen_foldable_filter {b es E} `{ToEnt E} `{Foldable es E}
    (m : es) (filter : GenQuery b) : GenLLVM (option b)
    := fmap snd <$> gen_foldable_filter_ent m filter.

  Definition genMatchEnt {a es E}
    `{ToEnt E} `{Foldable es E}
    (focus : @EntTarget es E _ _ GenState G)
    (filter : GenQuery a)
    : GenLLVM (option (Ent * a))
    := es <- lift focus;;
       gen_foldable_filter_ent es filter.

  Definition genMatch {a es E}
    `{ToEnt E} `{Foldable es E}
    (focus : @EntTarget es E _ _ GenState G)
    (filter : GenQuery a)
    : GenLLVM (option a)
    := es <- lift focus;;
       gen_foldable_filter es filter.

  Definition get_type_from_alias (var : Ent) : GenLLVM typ
    := mident <- use (gen_context' .@ entl var .@ type_alias');;
       match mident with
       | Some id => ret id
       | None => failGen "gen_sized_type_alias, couldn't find entity... Shouldn't happen"
       end.

  Definition get_type_of_variable (var : Ent) : GenLLVM typ
    := mident <- use (gen_context' .@ entl var .@ variable_type');;
       match mident with
       | Some id => ret id
       | None => failGen "gen_sized_type_alias, couldn't find entity... Shouldn't happen"
       end.

  (* Generate a type that matches one of the type aliases *)
  Definition gen_sized_type_of_alias {a} (focus : Lens' (SystemState GenState G) (IM.Raw.t a)) : GenLLVM typ
    := var <- gen_entity_with focus;;
       match var with
       | Some var =>
           get_type_from_alias var
       | None => failGen "gen_sized_type_of_alias, couldn't find entity... Shouldn't happen"
       end.

  Definition gen_sized_type_of_alias_filter {a b}
    (focus : Lens' (SystemState GenState G) (IM.Raw.t a))
    (filter : GenQuery b)
    : GenLLVM (option typ)
    := var <- gen_entity_with_filter focus filter;;
       match var with
       | Some var => fmap Some (get_type_from_alias var)
       | None => ret None
       end.

  (* Generate a type that matches one of the variables *)
  Definition gen_type_of_variable_filter {a b}
    (focus : Lens' (SystemState GenState G) (IM.Raw.t a))
    (filter : GenQuery b)
    : GenLLVM (option typ)
    := var <- gen_entity_with_filter focus filter;;
       match var with
       | Some var => fmap Some (get_type_of_variable var)
       | None => ret None
       end.

  (* Not sized in the QuickChick sense, sized in the LLVM sense. *)
  Definition gen_sized_typ_0 : GenLLVM typ :=
    oid <- gen_sized_type_alias;;
    let ident_gen :=
      match oid with
      | None => []
      | Some id => [ret (TYPE_Identified id)]
      end
    in
    oneOf_LLVM
      (ident_gen ++
         (map ret
            ([ TYPE_I 1
               ; TYPE_I 8
               ; TYPE_I 16
               ; TYPE_I 32
               ; TYPE_I 64
                        (* TODO: Could generate TYPE_Identified if we filter for sized types *)
                        (* ; TYPE_Half *)
                        (* ; TYPE_X86_fp80 *)
                        (* ; TYPE_Fp128 *)
                        (* ; TYPE_Ppc_fp128 *)
                        (* ; TYPE_Metadata *)
                        (* ; TYPE_X86_mmx *)
                        (* ; TYPE_Opaque *)
              ] ++
               (if enable_float_generation
                then
                 [ (* TODO: Generate floats and stuff *)
                   TYPE_Float
                   (* ; TYPE_Double *)
                 ]
               else
                 [])
         ))).

  (* TODO: Move this *)
  Definition lengthN {X} (xs : list X) : N :=
    fold_left (fun acc x => (acc + 1)%N) xs 0%N.

  (* Definition gen_typ_from_ctx (ctx : var_context) : GenLLVM typ *)
  (*   := fmap snd (elems_LLVM ctx). *)

  (* Definition gen_ident_from_ctx (ctx : var_context) : GenLLVM ident *)
  (*   := fmap fst (elems_LLVM ctx). *)

  Definition def_option_GenLLVM {a} (def : GenLLVM a) (gopt : GenLLVM (option a)) : GenLLVM a
    := o <- gopt;;
       match o with
       | Some a => ret a
       | None => def
       end.

  Definition gen_type_matching_alias_focus {a b}
    (focus : Lens' (SystemState GenState G) (IM.Raw.t a)) (filter : GenQuery b)
    : GenLLVM (option typ)
    := gen_sized_type_of_alias_filter focus filter.

  Definition gen_type_matching_variable_focus {a b}
    (focus : Lens' (SystemState GenState G) (IM.Raw.t a)) (filter : GenQuery b)
    : GenLLVM (option typ)
    := gen_type_of_variable_filter focus filter.

  Definition gen_type_matching_alias {b} (filter : GenQuery b) : GenLLVM (option typ)
    := gen_type_matching_alias_focus (gen_context' .@ is_sized_type_alias') filter.

  Definition gen_type_matching_local {b} (filter : GenQuery b) : GenLLVM (option typ)
    := gen_type_matching_variable_focus (gen_context' .@ is_local') filter.

  Definition gen_type_matching_global {b} (filter : GenQuery b) : GenLLVM (option typ)
    := gen_type_matching_variable_focus (gen_context' .@ is_global') filter.

  Definition gen_type_matching_variable {b} (filter : GenQuery b) : GenLLVM (option typ)
    := gen_type_matching_variable_focus (gen_context' .@ variable_type') filter.

  Definition gen_primitive_typ : GenLLVM typ :=
    oneOf_LLVM
      ([ret (TYPE_I 1)
        ; ret (TYPE_I 8)
        ; ret (TYPE_I 16)
        ; ret (TYPE_I 32)
        ; ret (TYPE_I 64)
        ] ++ if enable_float_generation then [ret (TYPE_Float) (* ; ret TYPE_DOUBLE *)] else []).

  Definition sized_aggregate_typ_gens (subg : nat -> GenLLVM typ) (sz : nat) :  list (unit -> GenLLVM typ)
    := [ (fun _ => gen_sized_typ_0)
       ; (fun _ => ret (fun t => TYPE_Pointer (Some t)) <*> subg sz)
       (* TODO: Might want to restrict the size to something reasonable *)
       ; (fun _ => ret TYPE_Array <*> lift_GenLLVM genN <*> subg sz)
       ; (fun _ => ret TYPE_Vector <*> (n <- lift_GenLLVM genN;; ret (n + 1)%N) <*> gen_primitive_typ)
       ; (fun _ => ret TYPE_Struct <*> nonemptyListOf_LLVM (subg sz))
       ; (fun _ => ret TYPE_Packed_struct <*> nonemptyListOf_LLVM (subg sz))
    ].

  Fixpoint gen_typ_size'
    (baseGen : GenLLVM typ)
    (aggregate_gens : (nat -> GenLLVM typ) -> nat -> list (unit -> GenLLVM typ))
    (from_context : GenLLVM (option typ)) (sz : nat)
    {struct sz} : GenLLVM typ :=
    match sz with
    | O => baseGen
    | (S sz') =>
        ofc <- from_context;;
        let fc : list (N * (unit -> GenLLVM typ)) :=
          match ofc with
          | None => []
          | Some fc =>
              [(10%N, fun _ : unit => ret fc)]
          end
        in
        let aggregates := (sized_aggregate_typ_gens (fun sz => @gen_typ_size' baseGen aggregate_gens from_context sz) sz') in
        freq_LLVM_thunked_N (fc ++ fmap (fun x => (1%N, x)) aggregates)
    end.

  Definition gen_sized_typ_size :=
    gen_typ_size' gen_sized_typ_0 sized_aggregate_typ_gens (gen_type_matching_variable (withl is_sized')).

  Definition max_typ_size : nat := 4.

  Definition gen_sized_typ  : GenLLVM typ
    := sized_LLVM (fun sz => gen_sized_typ_size (min sz max_typ_size)).

(*   (* Want to be able to use gen_sized_typ' to do this... *)
(*      But I did not notice this wants only sized types from the contexts. *)
(*      Need to be able to filter focused entities to only the ones with the sized type tags... Should be doable. *)
(*    *) *)
(*   Definition gen_sized_typ_ptrin_fctx : GenLLVM typ *)
(*     := gen_typ_size' ( *)
(*     ctx <- get_ctx;; *)
(*     aliases <- get_typ_ctx;; *)
(*     let typs_in_ctx := filter_sized_typs aliases ctx in *)
(*     sized_LLVM (fun sz => gen_sized_typ_size_ptrinctx sz typs_in_ctx). *)

(* gen_sized_typ_ptrin_fctx seems to grab a  *)

(*   Definition gen_sized_typ_ptrin_gctx : GenLLVM typ *)
(*     := *)
(*     gctx <- get_global_ctx;; *)
(*     aliases <- get_typ_ctx;; *)
(*     let typs_in_ctx := filter_sized_typs aliases gctx in *)
(*     sized_LLVM (fun sz => gen_sized_typ_size_ptrinctx sz typs_in_ctx). *)

  Definition gen_type_alias_ident : GenLLVM (option ident)
    := es <- use (gen_context' .@ type_alias');;
       var <- gen_IntMapRaw_ent es;;
       match var with
       | Some var =>
           id <- use (gen_context' .@ entl var .@ name');;
           ret id
       | None => ret None
       end.

  (* Generate a type of size 0 *)
  Definition gen_typ_0 : GenLLVM typ :=
    oid <- gen_sized_type_alias;;
    (* let ident_gen := *)
    (*   match oid with *)
    (*   | None => [] *)
    (*   | Some id => [ret (TYPE_Identified id)] *)
    (*   end *)
    (* in *)
    oneOf_LLVM
          ((* identified ++ *)
           (map ret
                ([ TYPE_I 1
                ; TYPE_I 8
                ; TYPE_I 16
                ; TYPE_I 32
                ; TYPE_I 64
                ; TYPE_Void
                (* ; TYPE_Metadata *)
                (* ; TYPE_X86_mmx *)
                (* ; TYPE_Opaque *)
                ] ++
                   (if enable_float_generation
                    then
                      [ (* TODO: Generate floats and stuff *)
                        TYPE_Float
                          (* ; TYPE_Double *)
                          (* ; TYPE_Half *)
                          (* ; TYPE_X86_fp80 *)
                          (* ; TYPE_Fp128 *)
                          (* ; TYPE_Ppc_fp128 *)
                      ]
                    else
                      [])))).


  Definition aggregate_typ_gens (subg : nat -> GenLLVM typ) (sz : nat) :  list (unit -> GenLLVM typ)
    := [ (fun _ => subg 0%nat)
       ; (fun _ => ret (fun t => TYPE_Pointer (Some t)) <*> subg sz)
       (* TODO: Might want to restrict the size to something reasonable *)
       ; (fun _ => ret TYPE_Array <*> lift_GenLLVM genN <*> subg sz)
       ; (fun _ => ret TYPE_Vector <*> (n <- lift_GenLLVM genN;; ret (n + 1)%N) <*> gen_primitive_typ)
       ; (fun _ =>
          let n := Nat.div (S sz) 2 in
          ret TYPE_Function <*> subg n <*> listOf_LLVM (gen_sized_typ_size n) <*> ret false)
       ; (fun _ => ret TYPE_Struct <*> nonemptyListOf_LLVM (subg sz))
       ; (fun _ => ret TYPE_Packed_struct <*> nonemptyListOf_LLVM (subg sz))
    ].

  (* TODO: This should probably be mutually recursive with
     gen_sized_typ since pointers of any type are considered sized *)
  Definition gen_typ_size : nat -> GenLLVM typ :=
    gen_typ_size' gen_typ_0 aggregate_typ_gens (gen_type_matching_variable (ret tt)).

  Definition gen_typ : GenLLVM typ
    := sized_LLVM (fun sz => gen_typ_size (min sz max_typ_size)).

  Definition gen_typ_non_void_0 : GenLLVM typ :=
    oid <- gen_sized_type_alias;;
    let ident_gen :=
      match oid with
      | None => []
      | Some id => [ret (TYPE_Identified id)]
      end
    in
    oneOf_LLVM
      (ident_gen ++
         (map ret
            ([ TYPE_I 1
               ; TYPE_I 8
               ; TYPE_I 16
               ; TYPE_I 32
               ; TYPE_I 64
                        (* ; TYPE_Metadata *)
                        (* ; TYPE_X86_mmx *)
                        (* ; TYPE_Opaque *)
              ] ++ (if enable_float_generation
                    then
                      [ (* TODO: Generate floats and stuff *)
                        TYPE_Float
                          (* ; TYPE_Double *)
                          (* ; TYPE_Half *)
                          (* ; TYPE_X86_fp80 *)
                          (* ; TYPE_Fp128 *)
                          (* ; TYPE_Ppc_fp128 *)
                      ]
                    else
                      [])))).

  Definition gen_typ_non_void_size : nat -> GenLLVM typ :=
    gen_typ_size' gen_typ_non_void_0 aggregate_typ_gens (gen_type_matching_variable (withl is_non_void')).

  Definition gen_typ_non_void : GenLLVM typ :=
    sized_LLVM (fun sz => gen_typ_non_void_size (min sz max_typ_size)).

  (* Non-void, non-function types *)
  Definition gen_typ_non_void_size_wo_fn : nat -> GenLLVM typ :=
    gen_typ_size' gen_typ_non_void_0 sized_aggregate_typ_gens (gen_type_matching_variable (withl is_non_void')).

  Definition gen_typ_non_void_wo_fn : GenLLVM typ :=
    sized_LLVM (fun sz => gen_typ_non_void_size_wo_fn (min sz max_typ_size)).

  (* TODO: look up identifiers *)
  (* Types for operation expressions *)
  Definition gen_op_typ : GenLLVM typ :=
    oneOf_LLVM
      (map ret
         ([ TYPE_I 1
            ; TYPE_I 8
            ; TYPE_I 16
            ; TYPE_I 32
            ; TYPE_I 64
                     (* ; TYPE_Metadata *)
                     (* ; TYPE_X86_mmx *)
                     (* ; TYPE_Opaque *)
           ] ++ (if enable_float_generation
                 then
                   [ (* TODO: Generate floats and stuff *)
                     TYPE_Float
                       (* ; TYPE_Double *)
                       (* ; TYPE_Half *)
                       (* ; TYPE_X86_fp80 *)
                       (* ; TYPE_Fp128 *)
                       (* ; TYPE_Ppc_fp128 *)
                   ]
                 else
                   []))).

  (* TODO: look up identifiers *)
  Definition gen_int_typ : GenLLVM typ :=
    elems_LLVM
      [ TYPE_I 1
        ; TYPE_I 8
        ; TYPE_I 16
        ; TYPE_I 32
        ; TYPE_I 64
      ].

  (* TODO: look up identifiers *)
  Definition gen_float_typ : GenLLVM typ :=
    elems_LLVM
      [ TYPE_Float
        (* ; TYPE_Double *)
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
            (* ; ret FRem *) (* Disable FRem because vellvm doesn't support it yet *)
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
         if Pos.eq_dec sz sz' then true else false
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
         | TYPE_I sz' => if Pos.eq_dec sz sz' then true else false
         | _ => false
         end
       | TYPE_IPTR =>
         match b with
         | TYPE_IPTR => true
         | _ => false
         end
       | TYPE_Pointer t =>
         match b with
         | TYPE_Pointer t' =>
             match (t, t') with
             | (Some t, Some t') => normalized_typ_eq t t'
             | (None, None) => true
             | _ => false
             end
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
       | TYPE_Identified id =>
           match b with
           | TYPE_Identified id' =>
               if Ident.eq_dec id id'
               then true
               else false
           | _ => false
           end
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
    | TYPE_Pointer None
    | TYPE_Half
    | TYPE_Float
    | TYPE_Double
    | TYPE_X86_fp80
    | TYPE_Fp128
    | TYPE_Ppc_fp128
    | TYPE_Metadata
    | TYPE_X86_mmx => normalized_typ_eq t_from t
    | TYPE_Pointer (Some subtyp) =>
        match t with
        | TYPE_Pointer (Some subtyp') =>
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

  (* TODO: remove this *)
  (* Definition filter_function_pointers (typ_ctx : type_context) (ctx : var_context) : var_context := *)
  (*   filter (fun '(_, t) => is_function_pointer typ_ctx t) ctx. *)

  (* Can't use choose for these functions because it gets extracted to
     ocaml's Random.State.int function which has small bounds. *)

  Definition gen_bitZ : G Z :=
    b <- (arbitrary : G bool);;
    if b then ret 1 else ret 0.

  Fixpoint gen_unsigned_bitwidth_h (acc : Z) (bitwidth : positive) {struct bitwidth} : G Z :=
    if Pos.eqb bitwidth 1
    then gen_bitZ
    else
      bit <- gen_bitZ;;
      gen_unsigned_bitwidth_h (2 * acc + bit)%Z (bitwidth-1).

  Definition gen_unsigned_bitwidth (bitwidth : positive) : G Z :=
    gen_unsigned_bitwidth_h 0 bitwidth.

  Definition gen_signed_bitwidth (bitwidth : positive) : G Z :=
    let zbitwidth := Zpos bitwidth in
    let zhalf := zbitwidth - 1 in

    z <- (arbitrary : G Z);;
    negative <- (arbitrary : G bool);;
    if negative : bool
    then
      ret (-((Z.modulo z (2^zhalf)) + 1))
    else
      ret (Z.modulo z (2^zhalf)).

  Definition gen_gt_zero (bitwidth : option positive) : G Z
    := match bitwidth with
       | None =>
           (* Unbounded *)
           n <- gen_unsigned_bitwidth 64;;
           ret (1 + Z.modulo n (2^64 - 1))
       | Some bitwidth =>
           n <- gen_unsigned_bitwidth bitwidth;;
           ret (1 + Z.modulo n (2^(Zpos bitwidth) - 1))
       end.

  Definition gen_non_zero (bitwidth : option positive) : G Z
    := match bitwidth with
       | None =>
           (* Unbounded *)
           x <- gen_gt_zero None;;
           elems_ x [x; -x]
       | Some bitwidth =>
           let zbitwidth := Zpos bitwidth in
           let half := (bitwidth - 1)%positive in
           let zhalf := zbitwidth - 1 in
           if Z.eqb zhalf 0
           then ret (-1)
           else
             negative <- (arbitrary : G bool);;
             if (negative : bool)
             then
               n <- gen_unsigned_bitwidth half;;
               ret (-(1 + Z.modulo n (2^zhalf)))
             else
               n <- gen_unsigned_bitwidth half;;
               ret (1 + Z.modulo n (2^zhalf - 1))
       end.

  (* TODO: make this more complex using metadata *)
  Definition gen_non_zero_exp_size (sz : nat) (t : typ) : GenLLVM (exp typ)
    := match t with
       | TYPE_I n => ret EXP_Integer <*> lift (gen_non_zero (Some n))
       | TYPE_IPTR => ret EXP_Integer <*> lift (gen_non_zero None)
       | TYPE_Float => ret EXP_Float <*> lift fing32 (* TODO: is this actually non-zero...? *)
       | TYPE_Double => ret EXP_Double <*> lift fing64 (*TODO : Fix generator for double*)
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

  Variant exp_source :=
    | FULL_CTX
    | GLOBAL_CTX.

  (* Generate an entity to a variable *)
  Definition gen_var_ent {a b}
    (focus : Lens' (SystemState GenState G) (IM.Raw.t a)) (filter : GenQuery b) : GenLLVM (option Ent)
    := focused <- use focus;;
       gen_IntMapRaw_ent_filter focused filter.

  Definition gen_var_ident {a b}
    (focus : Lens' (SystemState GenState G) (IM.Raw.t a)) (filter : GenQuery b) : GenLLVM (option ident)
    := oe <- gen_var_ent focus filter;;
       match oe with
       | None => ret None
       | Some e => use (gen_context' .@ entl e .@ name')
       end.

  (* Generate an entity for a variable of a given typ *)
  (* t should already be normalized *)
  Definition gen_var_of_typ_ent {a b}
    (focus : Lens' (SystemState GenState G) (IM.Raw.t a))
    (filter : GenQuery b)
    (t : typ) : GenLLVM (option Ent)
    := gen_var_ent focus
         (vt <- queryl variable_type';;
          if (normalized_typ_eq t vt)
          then filter
          else mzero).

  (* Generate an ident for a variable of a given typ *)
  (* t should already be normalized *)
  Definition gen_var_of_typ_ident {a b}
    (focus : Lens' (SystemState GenState G) (IM.Raw.t a))
    (filter : GenQuery b)
    (t : typ) : GenLLVM (option ident)
    := gen_var_ident focus
         (vt <- queryl variable_type';;
          if (normalized_typ_eq t vt)
          then filter
          else mzero).

  Fixpoint gen_exp_size' (gen_global_of_typ : typ -> GenLLVM (option ident)) (gen_ident_of_typ : typ -> GenLLVM (option ident)) (sz : nat) (t : typ) {struct t} : GenLLVM (exp typ) :=
    match sz with
    | 0%nat =>
        (* annotate_debug ("++++++++GenExpOT: " ++ show t);; *)
        i <- gen_ident_of_typ t;;
        let gen_idents : list (nat * GenLLVM (exp typ)) :=
          match i with
          | None => []
          | Some ident => [(320%nat, fmap (fun i => EXP_Ident i) (@ret GenLLVM _ _ ident))]
          end in
        let fix gen_size_0 (t: typ) :=
          match t with
          | TYPE_I n                  =>
              z <- lift (gen_unsigned_bitwidth n);;
              ret (EXP_Integer z)
          (* lift (x <- (arbitrary : G nat);; ret (Z.of_nat x)) *)
          (*  (* TODO: should the integer be forced to be in bounds? *) *)
          | TYPE_IPTR => ret EXP_Integer <*> lift (arbitrary : G Z)
          | TYPE_Pointer _       => failGen "gen_exp_size TYPE_Pointer"
          (* Only pointer type expressions might be conversions? Maybe GEP? *)
          | TYPE_Void                 => failGen "gen_exp_size TYPE_Void" (* There should be no expressions of type void *)
          | TYPE_Function ret args _   => failGen "gen_exp_size TYPE_Function"(* No expressions of function type *)
          | TYPE_Opaque               => failGen "gen_exp_size TYPE_Opaque" (* TODO: not sure what these should be... *)

          (* Generate literals for aggregate structures *)
          | TYPE_Array n t =>
              es <- (vectorOf_LLVM (N.to_nat n) (gen_exp_size' gen_global_of_typ gen_global_of_typ 0%nat t));;
              ret (EXP_Array (TYPE_Array n t) (map (fun e => (t, e)) es))
          | TYPE_Vector n t =>
              es <- (vectorOf_LLVM (N.to_nat n) (gen_exp_size' gen_global_of_typ gen_global_of_typ 0%nat t));;
              ret (EXP_Vector (TYPE_Vector n t) (map (fun e => (t, e)) es))
          | TYPE_Struct fields =>
              (* Should we divide size evenly amongst components of struct? *)
              tes <- map_monad (fun t => e <- (gen_exp_size' gen_global_of_typ gen_global_of_typ 0%nat t);; ret (t, e)) fields;;
              ret (EXP_Struct tes)
          | TYPE_Packed_struct fields =>
              (* Should we divide size evenly amongst components of struct? *)
              tes <- map_monad (fun t => e <- (gen_exp_size' gen_global_of_typ gen_global_of_typ 0%nat t);; ret (t, e)) fields;;
              ret (EXP_Packed_struct tes)

          | TYPE_Identified id        =>
              t <- def_option_GenLLVM (failGen "gen_exp_size TYPE_Identified")
                    (genFind
                       (use (gen_context' .@ type_alias'))
                       (n <- queryl name';;
                        if Ident.eq_dec id n
                        then queryl type_alias'
                        else mzero));;
              gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat t
          (* Not generating these types for now *)
          | TYPE_Half                 => failGen "gen_exp_size TYPE_Half"
          | TYPE_Float                => ret EXP_Float <*> lift fing32(* referred to genarators in flocq-quickchick*)
          | TYPE_Double               => ret EXP_Double <*> lift fing64 (* TODO: Fix generator for double*)
          | TYPE_X86_fp80             => failGen "gen_exp_size TYPE_X86_fp80"
          | TYPE_Fp128                => failGen "gen_exp_size TYPE_Fp128"
          | TYPE_Ppc_fp128            => failGen "gen_exp_size TYPE_Ppc_fp128"
          | TYPE_Metadata             => failGen "gen_exp_size TYPE_Metadata"
          | TYPE_X86_mmx              => failGen "gen_exp_size TYPE_X86_mmx"
          end in
        (* Hack to avoid failing way too much *)
        match t with
        | TYPE_Pointer (Some t) =>
            if (seq.nilp gen_idents)
            then
              (* Generate Global Pointer retroactively *)
              (* 0. Flip the global context if we are at the first level *)
              (* 1. Generate a global id, *)
              (* 2. recursively define the receiving types *)
              annotate "retroactive global pointer"
                (in_exp <- gen_exp_size' gen_global_of_typ gen_global_of_typ 0%nat t;;
                 name <- new_global_id;;
                 add_to_global_memo (mk_global name t false (Some in_exp) false []);;
                 e <- add_to_global_ctx (ID_Global name, TYPE_Pointer (Some t));;
                 (gen_context' .@ entl e .@ deterministic') .= false;;
                 ret (EXP_Ident (ID_Global name)))
            else freq_LLVM (gen_idents)
        (* TODO: handle opaque ptrs *)

        (* freq_LLVM ((* (1%nat, ret EXP_Undef) :: *) gen_idents) *)
        (* TODO: Add some retroactive global generation *)
        | _ => freq_LLVM
                ((10%nat, gen_size_0 t) :: (* (1%nat, ret EXP_Zero_initializer) :: *) gen_idents)
        end
    | (S sz') =>
        let gens :=
          match t with
          | TYPE_I isz =>
              if Pos.eqb isz 1
              then
                ([ gen_ibinop_exp gen_global_of_typ gen_ident_of_typ isz
                  ; τ <- gen_int_typ;;
                    gen_icmp_exp_typ gen_global_of_typ gen_ident_of_typ τ
                ] ++
                  if enable_float_generation
                  then
                    [τ <- gen_float_typ;;
                     gen_fcmp_exp_typ gen_global_of_typ gen_ident_of_typ τ
                    ]
                  else [])%list
              else
                [ gen_ibinop_exp gen_global_of_typ gen_ident_of_typ isz ]
          | TYPE_IPTR =>
              [gen_ibinop_exp_typ gen_global_of_typ gen_ident_of_typ TYPE_IPTR]
          | TYPE_Pointer _         => [] (* GEP? *)

          (* TODO: currently only generate literals for aggregate structures with size 0 exps *)
          | TYPE_Array n t => []
          | TYPE_Vector n t => []
          | TYPE_Struct fields => []
          | TYPE_Packed_struct fields => []

          | TYPE_Void              => [failGen "gen_exp_size TYPE_VOID list"] (* No void type expressions *)
          | TYPE_Function ret args _ => [failGen "gen_exp_size TYPE_Function list"] (* These shouldn't exist, I think *)
          | TYPE_Opaque            => [failGen "gen_exp_size TYPE_Opaque list"] (* TODO: not sure what these should be... *)
          | TYPE_Half              => [failGen "gen_exp_size TYPE_Half list" ]
          | TYPE_Float             => [gen_fbinop_exp gen_global_of_typ gen_ident_of_typ TYPE_Float]
          | TYPE_Double            => [gen_fbinop_exp gen_global_of_typ gen_ident_of_typ TYPE_Double]
          | TYPE_X86_fp80          => [failGen "gen_exp_size TYPE_X86_fp80 list"]
          | TYPE_Fp128             => [failGen "gen_exp_size TYPE_Fp128 list"]
          | TYPE_Ppc_fp128         => [failGen "gen_exp_size TYPE_Ppc_fp128 list"]
          | TYPE_Metadata          => [failGen "gen_exp_size TYPE_Metadata list"]
          | TYPE_X86_mmx           => [failGen "gen_exp_size TYPE_X86_mmx list"]
          | TYPE_Identified id     =>
              [ t <- def_option_GenLLVM (failGen "gen_exp_size TYPE_Identified")
                      (genFind
                         (use (gen_context' .@ type_alias'))
                         (n <- queryl name';;
                          if Ident.eq_dec id n
                          then queryl type_alias'
                          else mzero));;
                gen_exp_size' gen_global_of_typ gen_ident_of_typ sz t
              ]
          end
        in
        (* short-circuit to size 0 *)
        oneOf_LLVM (gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat t :: gens)
    end
  with
  (* TODO: Make sure we don't divide by 0 *)
  gen_ibinop_exp_typ (gen_global_of_typ : typ -> GenLLVM (option ident)) (gen_ident_of_typ : typ -> GenLLVM (option ident)) (t : typ) {struct t} : GenLLVM (exp typ)
  := ibinop <- lift gen_ibinop;;

    if Handlers.LLVMEvents.DV.iop_is_div ibinop && Handlers.LLVMEvents.DV.iop_is_signed ibinop
    then
      ret (OP_IBinop ibinop) <*> ret t <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat t <*> gen_non_zero_exp_size 0%nat t
    else
      if Handlers.LLVMEvents.DV.iop_is_div ibinop
      then
        ret (OP_IBinop ibinop) <*> ret t <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat t <*> gen_gt_zero_exp_size 0%nat t
      else
        exp_value <- gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat t;;
        if Handlers.LLVMEvents.DV.iop_is_shift ibinop
        then
          let max_shift_size :=
            match t with
            | TYPE_I i => BinIntDef.Z.of_N (Npos i - 1)%N
            | _ => 0%Z
            end in
          x <- lift (choose (0%Z, max_shift_size));;
          let exp_value2 : exp typ := EXP_Integer x in
          ret (OP_IBinop ibinop t exp_value exp_value2)
        else ret (OP_IBinop ibinop t exp_value) <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat t
  with
  gen_ibinop_exp (gen_global_of_typ : typ -> GenLLVM (option ident)) (gen_ident_of_typ : typ -> GenLLVM (option ident)) (isz : positive) {struct isz} : GenLLVM (exp typ)
  :=
    let t := TYPE_I isz in
    gen_ibinop_exp_typ gen_global_of_typ gen_ident_of_typ t
  with
  gen_fbinop_exp (gen_global_of_typ : typ -> GenLLVM (option ident)) (gen_ident_of_typ : typ -> GenLLVM (option ident)) (ty: typ) {struct ty} : GenLLVM (exp typ)
  :=
    match ty with
    | TYPE_Float => fbinop <- lift gen_fbinop;;
                   if (Handlers.LLVMEvents.DV.fop_is_div fbinop)
                   then ret (OP_FBinop fbinop nil) <*> ret ty <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat ty <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat ty
                   else ret (OP_FBinop fbinop nil) <*> ret ty <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat ty <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat ty
    | TYPE_Double => fbinop <- lift gen_fbinop;;
                    if (Handlers.LLVMEvents.DV.fop_is_div fbinop)
                    then ret (OP_FBinop fbinop nil) <*> ret ty <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat ty <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat ty
                    else ret (OP_FBinop fbinop nil) <*> ret ty <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat ty <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat ty
    | _ => failGen "gen_fbinop_exp"
    end
  with
  gen_icmp_exp_typ (gen_global_of_typ : typ -> GenLLVM (option ident)) (gen_ident_of_typ : typ -> GenLLVM (option ident)) (t : typ) {struct t} : GenLLVM (exp typ)
  := cmp <- lift gen_icmp;;
     ret (OP_ICmp cmp) <*> ret t <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat t <*> gen_non_zero_exp_size 0%nat t
  with
  gen_fcmp_exp_typ (gen_global_of_typ : typ -> GenLLVM (option ident)) (gen_ident_of_typ : typ -> GenLLVM (option ident)) (t : typ) {struct t} : GenLLVM (exp typ)
  := cmp <- lift gen_fcmp;;
     ret (OP_FCmp cmp) <*> ret t <*> gen_exp_size' gen_global_of_typ gen_ident_of_typ 0%nat t <*> gen_non_zero_exp_size 0%nat t.

  Definition gen_icmp_exp (gen_global_of_typ : typ -> GenLLVM (option ident)) (gen_ident_of_typ : typ -> GenLLVM (option ident)) : GenLLVM (exp typ)
    := τ <- gen_int_typ;;
       gen_icmp_exp_typ gen_global_of_typ gen_ident_of_typ τ.

  Definition gen_fcmp_exp (gen_global_of_typ : typ -> GenLLVM (option ident)) (gen_ident_of_typ : typ -> GenLLVM (option ident)) : GenLLVM (exp typ)
    := τ <- gen_float_typ;;
       gen_fcmp_exp_typ gen_global_of_typ gen_ident_of_typ τ.

  Definition gen_deterministic_global_ident :=
    gen_var_of_typ_ident (gen_context' .@ is_global') (withl is_deterministic').

  Definition gen_global_ident :=
    gen_var_of_typ_ident (gen_context' .@ is_global') (ret tt).

  Definition gen_deterministic_ident :=
    gen_var_of_typ_ident (gen_context' .@ variable_type') (withl is_deterministic').

  Definition gen_ident :=
    gen_var_of_typ_ident (gen_context' .@ variable_type') (ret tt).

  Definition gen_exp_size :=
    gen_exp_size' gen_deterministic_global_ident.

  Definition gen_exp_possibly_non_deterministic_size :=
    gen_exp_size' gen_global_ident.

  Definition gen_exp (t : typ) : GenLLVM (exp typ)
    := annotate ("gen_exp: " ++ show t)
         (sized_LLVM (fun sz => gen_exp_size gen_deterministic_ident sz t)).

  Definition gen_exp_possibly_non_deterministic (t : typ) : GenLLVM (exp typ)
    := annotate ("gen_exp_possibly_non_deterministic: " ++ show t)
         (sized_LLVM (fun sz => gen_exp_possibly_non_deterministic_size gen_ident sz t)).

  Definition gen_exp_sz0 (t : typ) : GenLLVM (exp typ)
    := annotate "gen_exp_sz0" (resize_LLVM 0 (gen_exp t)).

  Definition gen_exp_possibly_non_deterministic_sz0 (t : typ) : GenLLVM (exp typ)
    := annotate "gen_exp_possibly_non_deterministic_sz0" (resize_LLVM 0 (gen_exp_possibly_non_deterministic t)).

  Definition gen_texp : GenLLVM (texp typ)
    := annotate "gen_texp"
         (t <- gen_typ;;
          e <- gen_exp t;;
          ret (t, e)).

  Definition gen_sized_texp : GenLLVM (texp typ)
    := annotate "gen_sized_texp"
         (t <- gen_sized_typ;;
          e <- gen_exp t;;
          ret (t, e)).

  Definition gen_op (t : typ) : GenLLVM (exp typ)
    := sized_LLVM
         (fun sz =>
            match t with
            | TYPE_I isz =>
                if Pos.eqb isz 1
                then
                  (* If I1 also allow ICmp and FCmp *)
                  oneOf_LLVM
                    [ gen_ibinop_exp gen_deterministic_global_ident gen_deterministic_ident isz
                      ; gen_icmp_exp gen_deterministic_global_ident gen_deterministic_ident
                      ; gen_fcmp_exp gen_deterministic_global_ident gen_deterministic_ident
                    ]
                else
                  gen_ibinop_exp gen_deterministic_global_ident gen_deterministic_ident isz
            | TYPE_Float => gen_fbinop_exp gen_deterministic_global_ident gen_deterministic_ident TYPE_Float
            | TYPE_Double => gen_fbinop_exp gen_deterministic_global_ident gen_deterministic_ident TYPE_Double
            | _ => failGen "gen_op"
            end).

  Definition gen_int_texp : GenLLVM (texp typ)
    := t <- gen_int_typ;;
       e <- gen_exp t;;
       ret (t, e).

End ExpGenerators.

Require Import Semantics.LLVMEvents.
Require Import Semantics.InterpretationStack.
Require Import Handlers.Handlers.
From ITree Require Import
  ITree
  Interp.Recursion
  Events.Exception.

Import TopLevel64BitIntptr.
Import DV.
Import MemoryModelImplementation.LLVMParams64BitIntptr.Events.


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

  (* Index path without getting into vector *)
  (* t_from should already be normalized *)
  Fixpoint get_index_paths_insertvalue_aux (t_from : typ) (pre_path : DList Z) {struct t_from}: GenLLVM (bool * DList (typ * DList (Z))) :=
    match t_from with
    | TYPE_Array sz t =>
        '(has_subpaths, sub_paths) <- get_index_paths_insertvalue_aux t DList_empty;; (* Get index path from the first element*)
        if has_subpaths
        then ret (true, DList_cons (t_from, pre_path) (get_index_paths_from_AoV sz t pre_path sub_paths))
        else ret (false, DList_empty)
    | TYPE_Struct fields
    | TYPE_Packed_struct fields =>
        '(has_reach, reaches) <- get_index_paths_insertvalue_from_struct pre_path fields;;
        if has_reach
        then ret (true, DList_cons (t_from, pre_path) reaches)
        else ret (false, DList_empty)
    | TYPE_Pointer t =>
        in_ctx <- fmap is_some (genFind
                                 (use (gen_context' .@ variable_type'))
                                 (nt <- queryl normalized_type';;
                                  if (normalized_typ_eq t_from nt)
                                  then ret tt
                                  else mzero));;
        if in_ctx
        then ret (true, DList_singleton (t_from, pre_path))
        else ret (false, DList_empty)
    | TYPE_Vector _ t =>
        '(has_subpaths, sub_paths) <- get_index_paths_insertvalue_aux t DList_empty;; (* Get index path from the first element*)
        if has_subpaths
        then ret (true, DList_singleton (t_from, pre_path))
        else ret (false, DList_empty)
    | _ => ret (true, DList_singleton (t_from, pre_path))
    end with
  get_index_paths_insertvalue_from_struct (pre_path: DList Z) (fields: list typ) {struct fields}: GenLLVM (bool * DList (typ * DList Z)) :=
    fmap snd (fold_left
           (fun acc (fld_typ : typ) =>
              '(ix, (b, paths)) <- acc;;
              '(has_reach, reach) <- get_index_paths_insertvalue_aux fld_typ (DList_append pre_path (DList_singleton ix));;
              ret (ix + 1, (orb has_reach b, DList_append reach paths)))
           fields (ret (0%Z, (false, DList_empty : DList (typ * DList Z))))).

  Definition get_index_paths_insertvalue
    (t_from : typ)
    : GenLLVM (list (typ * list (Z)))
    :=
    paths <- get_index_paths_insertvalue_aux t_from DList_empty;;
    ret (tl (DList_paths_to_list_paths (snd paths))).

  Fixpoint has_paths_insertvalue_aux (t_from : typ) {struct t_from}: GenQuery bool :=
    match t_from with
    | TYPE_Array _ t
    | TYPE_Vector _ t => has_paths_insertvalue_aux t
    | TYPE_Struct fields
    | TYPE_Packed_struct fields =>
        fold_left (fun acc x =>
                     cnd_rest <- acc;;
                     cnd <- has_paths_insertvalue_aux x;;
                     ret (orb cnd_rest cnd)) fields (ret false)
    | TYPE_Pointer _ =>
        (* Check for the pointer type in the context *)
        nt <- queryl normalized_type';;
        ret (normalized_typ_eq nt t_from)
    | _ => ret true
    end.

  Definition gen_gep (tptr : typ) : GenLLVM (instr_id * instr typ) :=
    let get_typ_in_ptr (tptr : typ) :=
      match tptr with
      | TYPE_Pointer (Some t) => ret t
      (* TODO: What about opaque pointers? *)
      | _ => failGen "gen_gep"
      end in
    annotate "gen_gep"
      (t_in_ptr <- get_typ_in_ptr tptr;;
       eptr <- gen_exp_sz0 tptr;;
       let paths_in_ptr := get_index_paths_ptr t_in_ptr in (* Inner paths: Paths after removing the outer pointer *)
       '(ret_t, path) <- elems_LLVM paths_in_ptr;; (* Select one path from the paths *)
       let path_for_gep := map (fun x => (TYPE_I 32, EXP_Integer (x))) path in (* Turning the path to integer *)
       '(id, e) <- genInstrIdEnt (TYPE_Pointer (Some ret_t));;
       (* Default to non-deterministic for now. Need a way to look up whether the base pointer was deterministic *)
       (gen_context' .@ entl e .@ deterministic') .= false;;
       ret (id, INSTR_Op (OP_GetElementPtr t_in_ptr (TYPE_Pointer (Some t_in_ptr), eptr) path_for_gep))).

  Definition gen_extractvalue (tagg : typ): GenLLVM (instr_id * instr typ) :=
    annotate ("gen_extractvalue: " ++ show tagg)
      (eagg <- gen_exp_sz0 tagg;;
       ntagg <- normalize_type_GenLLVM tagg;;
       let paths_in_agg := get_index_paths_agg ntagg in
       '(t, path_for_extractvalue) <- elems_LLVM paths_in_agg;;
       id <- genInstrId t;;
       ret (id, INSTR_Op (OP_ExtractValue (tagg, eagg) path_for_extractvalue))).

  Definition gen_insertvalue (tagg: typ): GenLLVM (instr_id * instr typ) :=
    annotate "gen_insertvalue"
      (eagg <- gen_exp_sz0 tagg;;
       ctx <- get_ctx;;
       ntagg <- normalize_type_GenLLVM tagg;;
       paths_in_agg <- get_index_paths_insertvalue ntagg;;
       '(tsub, path_for_insertvalue) <- elems_LLVM paths_in_agg;;
       (* GC: THIS IS FALSE and will cause trouble because maybe the type we want is not in the context!!! NEED TO CHANGE TO SOMETHING ELSE*)
       esub <- hide_ctx (gen_exp_sz0 tsub);;
       (* Generate all of the type*)
       id <- genInstrId tagg;;
       ret (id, INSTR_Op (OP_InsertValue (tagg, eagg) (tsub, esub) path_for_insertvalue))).

  (* ExtractElement *)
  Definition gen_extractelement (tvec : typ): GenLLVM (instr_id * instr typ) :=
    annotate "gen_extractelement"
      (evec <- gen_exp_sz0 tvec;;
       let get_size_ty (vType: typ) :=
         match tvec with
         | TYPE_Vector sz ty => (sz, ty)
         | _ => (0%N, TYPE_Void)
         end in
       let '(sz, t_in_vec) := get_size_ty tvec in
       index_for_extractelement <- lift_GenLLVM (choose (0, Z.of_N sz - 1)%Z);;
       id <- genInstrId t_in_vec;;
       ret (id, INSTR_Op (OP_ExtractElement (tvec, evec) (TYPE_I 32, EXP_Integer index_for_extractelement)))).

  Definition gen_insertelement (tvec : typ) : GenLLVM (instr_id * instr typ) :=
    annotate "gen_insertelement"
      (evec <- gen_exp_sz0 tvec;;
       let get_size_ty (vType: typ) :=
         match tvec with
         | TYPE_Vector sz ty => (sz, ty)
         | _ => (0%N, TYPE_Void)
         end in
       let '(sz, t_in_vec) := get_size_ty tvec in
       value <- gen_exp_sz0 t_in_vec;;
       index <- lift_GenLLVM (choose (0, Z.of_N (sz - 1)));;
       id <- genInstrId tvec;;
       ret (id, INSTR_Op (OP_InsertElement (tvec, evec) (t_in_vec, value) (TYPE_I 32, EXP_Integer index)))).

  Definition round_up_to_eight (n : N) : N :=
    if N.eqb 0 n
    then 0
    else (((n - 1) / 8) + 1) * 8.

  Fixpoint get_bit_size_from_typ (t : typ) : N :=
    match t with
    | TYPE_I sz => Npos sz
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

  Definition get_size_from_typ (t: typ) : N :=
    round_up_to_eight (get_bit_size_from_typ t) / 8.

  (* Assuming max_byte_sz for this function is greater than 0 *)
  Definition get_prim_typ_le_size (max_byte_sz: N) : list (GenLLVM typ) :=
    (if (1 <=? max_byte_sz)%N then [ret (TYPE_I 1); ret (TYPE_I 8)] else []) ++
      (if (4 <=? max_byte_sz)%N then [ret (TYPE_I 32); ret TYPE_Float] else []) ++
      (if (8 <=? max_byte_sz)%N then [ret (TYPE_I 64) (* ; ret TYPE_Double *)] else []).

  (* Version without problematic i1 type *)
  Definition get_prim_vector_typ_le_size (max_byte_sz: N) : list (GenLLVM typ) :=
    (if (1 <=? max_byte_sz)%N then [ret (TYPE_I 8)] else []) ++
      (if (4 <=? max_byte_sz)%N then [ret (TYPE_I 32); ret TYPE_Float] else []) ++
      (if (8 <=? max_byte_sz)%N then [ret (TYPE_I 64) (* ; ret TYPE_Double *)] else []).

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

  (* Try to find a variable that's the result of a cast from a pointer *)
  Definition gen_ptr_casted_var : GenLLVM (option Ent)
    := gen_entity_with (gen_context' .@ from_pointer').

  (* Generate an identity and type for a variable that was cast from a pointer, also grab the pointer entity *)
  Definition gen_inttoptr_info : GenLLVM (option (Ent * ident * typ))
    := genMatch
         (use (gen_context' .@ from_pointer'))
         (ptr <- queryl from_pointer';;
          t <- queryl variable_type';;
          n <- queryl name';;
          ret (ptr, n, t)).

  (* TODO: old_tptr checks for vectors of pointers...
     I don't think we will find those with the new generator queries?
   *)
  (* TODO: handle opaque pointers. *)
  Definition gen_inttoptr (ptrEnt : Ent) (id : ident) (typ_from_cast : typ) : GenLLVM (instr_id * instr typ) :=
    annotate "gen_inttoptr"
      (opt <- use (gen_context' .@ entl ptrEnt .@ normalized_type');;
       match opt with
       | None => failGen "gen_inttoptr: Pointer entity missing normalized type."
       | Some old_tptr =>
           (* In the following case, we will check whether there are double pointers in the old pointer type, we will not cast if the data structure has double pointer *)
           (* TODO: Better identify the pointer inside and cast without changing their location *)
           new_tptr <-
             match old_tptr with
             | TYPE_Pointer (Some old_typ) =>
                 if typ_contains_pointer old_typ || is_function_type_h old_typ
                 then
                   ret old_tptr
                 else
                   x <- gen_typ_le_size (get_size_from_typ old_typ);;
                   ret (TYPE_Pointer (Some x))
             | TYPE_Vector sz (TYPE_Pointer (Some old_typ)) =>
                 if typ_contains_pointer old_typ || is_function_type_h old_typ
                 then
                   ret old_tptr
                 else
                   x <- gen_typ_le_size (get_size_from_typ old_typ);;
                   ret (TYPE_Pointer (Some x))
             | _ => ret (TYPE_Void) (* Won't reach here... Hopefully *)
             end;;
           '(iid, e) <- genInstrIdEnt new_tptr;;
           d <- use (gen_context' .@ entl ptrEnt .@ deterministic');;
           (* TODO: for now consider all pointers nondeterministic *)
           (gen_context' .@ entl e .@ deterministic') .= false;;
           ret (iid, INSTR_Op (OP_Conversion Inttoptr typ_from_cast (EXP_Ident id) new_tptr))
       end).

  (* TODO: handle opaque pointers. *)
  Definition gen_bitcast_typ (t_from : typ) : GenLLVM typ :=
    let gen_typ_list :=
      match t_from with
      | TYPE_I 1 =>
          ret [TYPE_I 1]
      | TYPE_I 8 =>
          ret [TYPE_I 8 (* ; TYPE_Vector 8 (TYPE_I 1) *)]
      | TYPE_I 16 =>
          ret [TYPE_I 16; TYPE_Vector 2 (TYPE_I 8) (* ; TYPE_Vector 8 (TYPE_I 1) *)]
      | TYPE_I 32
      | TYPE_Float =>
          ret [TYPE_I 32; TYPE_Float; TYPE_Vector 4 (TYPE_I 8); TYPE_Vector 2 (TYPE_I 16); TYPE_Vector 1 (TYPE_I 32); TYPE_Vector 1 TYPE_Float (* ; TYPE_Vector 32 (TYPE_I 1) *)]
      | TYPE_I 64
      | TYPE_Double =>
          ret [TYPE_I 64; (* TYPE_Double; *) TYPE_Vector 8 (TYPE_I 8); TYPE_Vector 4 (TYPE_I 16); TYPE_Vector 2 (TYPE_I 32); TYPE_Vector 2 (TYPE_Float) (* ; TYPE_Vector 64 (TYPE_I 1) *)]
      | TYPE_Vector sz subtyp =>
          match subtyp with
          | TYPE_Pointer _ =>
              (* TODO: Clean up. Figure out what can subtyp of pointer be *)
              (* new_subtyp <- gen_bitcast_typ subtyp;; *)
              ret [TYPE_Vector sz subtyp]
          | subtyp =>
              let trivial_typs := [(* (1%N, TYPE_I 1); *) (8%N, TYPE_I 8); (32%N, TYPE_I 32); (32%N, TYPE_Float); (64%N, TYPE_I 64) (* ; (64%N, TYPE_Double) *)] in
              let size_of_vec := get_bit_size_from_typ t_from in
              let choices := fold_left (fun acc '(s,t) => let sz' := (size_of_vec / s)%N in
                                                       let rem := (size_of_vec mod s)%N in
                                                       if ((sz' =? 0) || negb (rem =? 0))%N then acc else ((TYPE_Vector sz' t) :: acc)%list) trivial_typs [] in
              ret (t_from :: choices) (* I think adding t_from here slightly biases the generator sometimes *)
          end
      | TYPE_Pointer (Some subtyp) =>
          (* TODO: Clean up. Figure out what can subtyp of pointer be *)
          (* new_subtyp <- gen_bitcast_typ subtyp;; *)
          new_subtyp <- gen_sized_typ;;
          ret [TYPE_Pointer (Some new_subtyp)]
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
    end%list.

  Definition gen_trivial_typ : GenLLVM typ :=
    oneOf_LLVM [ret (TYPE_I 1)
                ; ret (TYPE_I 8)
                ; ret (TYPE_I 16)
                ; ret (TYPE_I 32)
                ; ret (TYPE_I 64)
                ; ret (TYPE_Float)
                (* ; ret (TYPE_Double) *)
                ; ret TYPE_Vector <*> lift_GenLLVM genPosN <*> gen_primitive_typ].

  Definition gen_first_class_typ_from_context : GenLLVM (option typ)
    := gen_type_matching_variable (withl is_first_class_type').

  Definition gen_non_aggregate_first_class_typ_from_context : GenLLVM (option typ)
    := gen_type_matching_variable (withl is_first_class_type';; withoutl is_aggregate').

  Definition gen_first_class_type_size : nat -> GenLLVM typ
    := gen_typ_size' gen_trivial_typ (fun subg sz => [fun _ => subg sz]) gen_first_class_typ_from_context.

  Definition gen_non_aggregate_first_class_type_size : nat -> GenLLVM typ
    := gen_typ_size' gen_trivial_typ (fun subg sz => [fun _ => subg sz]) gen_non_aggregate_first_class_typ_from_context.

  Definition gen_first_class_type : GenLLVM typ
    := sized_LLVM (fun sz => gen_first_class_type_size (min sz max_typ_size)).

  Definition gen_non_aggregate_first_class_type : GenLLVM typ
    := sized_LLVM (fun sz => gen_non_aggregate_first_class_type_size (min sz max_typ_size)).

  Definition gen_bitcast : GenLLVM (instr_id * instr typ) :=
    annotate "gen_bitcast"
      (tfc <- gen_trivial_typ;;
       efc <- gen_exp_sz0 tfc;;
       new_typ <- gen_bitcast_typ tfc;;
       id <- genInstrId new_typ;;
       ret (id, INSTR_Op (OP_Conversion Bitcast tfc efc new_typ))).

  Definition gen_call (tfun : typ) : GenLLVM (instr_id * instr typ) :=
    ctx <- use (gen_context' .@ @variable_type' (WorldOf _));;
    let blah := IM.Raw.elements ctx in
    annotate ("gen_call: " ++ show blah)
      match tfun with
      | TYPE_Pointer (Some (TYPE_Function ret_t args varargs)) =>
          args_texp <- map_monad
                        (fun (arg_typ:typ) =>
                           arg_exp <- gen_exp_sz0 arg_typ;;
                           ret (arg_typ, arg_exp))
                        args;;
          let args_with_params := map (fun arg => (arg, [])) args_texp in
          (* Otherwise we won't find function pointers *)
          efun <- gen_exp_possibly_non_deterministic_sz0 tfun;;
          id <- genInstrId ret_t;;
          ret (id, INSTR_Call (TYPE_Function ret_t args varargs, efun) args_with_params [])
      | _ => failGen "gen_call"
      end.

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

  Definition opt_err_add_state {A} {ST} (st:ST) (o : option (err A * list string * ST)) : err (option A) * list string * ST :=
    match o with
    | None => (inr None, [], st)
    | Some (inl msg, stack, st) => (inl msg, stack, st)
    | Some (inr a, stack, st) => (inr (Some a), stack, st)
    end.

  Definition get_typ_in_ptr (pt : typ) : GenLLVM typ :=
    match pt with
    | TYPE_Pointer (Some t) => ret t
    | _ => failGen "get_typ_in_ptr"
    end.

  Definition gen_load (tptr : typ) : GenLLVM (instr_id * instr typ)
    := eptr <- gen_exp_sz0 tptr;;
       vol <- lift (arbitrary : G bool);;
       ptr_typ <- get_typ_in_ptr tptr;;
       align <- ret (Some 1);;
       id <- genInstrId ptr_typ;;
       (* TODO: Fix parameters / generate more of them *)
       ret (id, INSTR_Load ptr_typ (tptr, eptr) []).

  (* TODO: handle opaque pointers?  *)
  Definition gen_store_to (ptr : texp typ) : GenLLVM (instr_id * instr typ)
    :=
    annotate "gen_store_to"
      match ptr with
      | (TYPE_Pointer (Some t), pexp) =>
          ctx <- get_ctx;;
          e <- (gen_exp_sz0 t);;
          let val := (t, e) in
          id <- genVoid;;
          ret (id, INSTR_Store val ptr [ANN_align 1])
      | _ => failGen "gen_store_to"
      end.

  Definition gen_store (tptr : typ) : GenLLVM (instr_id * instr typ)
    :=
    annotate "gen_store"
      (eptr <- gen_exp_sz0 tptr;;
       ptr_typ <- get_typ_in_ptr tptr;;
       gen_store_to(tptr, eptr)).

  (* Generate an instruction, as well as its type...

     The type is sometimes void for instructions that don't really
     compute a value, like void function calls, stores, etc.
   *)

  Definition gen_sized_ptr_type : GenLLVM (option typ)
    := genMatch
         (use (gen_context' .@ is_sized_pointer'))
         (queryl variable_type').

  Definition gen_aggregate_type : GenLLVM (option typ)
    := genMatch
         (use (gen_context' .@ is_aggregate'))
         (queryl variable_type').

  Definition gen_indexable_type : GenLLVM (option typ)
    := genMatch
         (use (gen_context' .@ is_indexable'))
         (queryl variable_type').

  Definition gen_ptr_vecptr_type : GenLLVM (option typ)
    := genMatch
         (use (gen_context' .@ is_ptr_vector'))
         (queryl variable_type').

  Definition gen_valid_ptr_vecptr_type : GenLLVM (option typ)
    := genMatch
         (use (gen_context' .@ is_ptr_vector'))
         (t <- queryl variable_type';;
          nt <- queryl normalized_type';;
          if negb (contains_typ nt (TYPE_Struct []) soft)
          then ret t
          else mzero).

  Definition gen_valid_ptr_vecptr_ent : GenLLVM (option (Ent * typ))
    := genMatchEnt
         (use (gen_context' .@ is_ptr_vector'))
         (t <- queryl variable_type';;
          nt <- queryl normalized_type';;
          if negb (contains_typ nt (TYPE_Struct []) soft)
          then ret t
          else mzero).

  Definition gen_vec_type : GenLLVM (option typ)
    := genMatch
         (use (gen_context' .@ is_vector'))
         (queryl variable_type').

  Definition gen_function_pointer_type : GenLLVM (option typ)
    := genMatch
         (use (gen_context' .@ is_function_pointer'))
         (queryl variable_type').

  Definition gen_insertvalue_type : GenLLVM (option typ)
    := genMatch
         (use (gen_context' .@ is_indexable'))
         (t <- queryl variable_type';;
          nt <- queryl normalized_type';;
          cnd <- has_paths_insertvalue_aux nt;;
          if cnd
          then ret t
          else mzero).

  (* Generate a pointer to a sized type (which some variable that exists in the context already has) *)
  Definition gen_sized_typ_in_context : GenLLVM (option typ)
    := genMatch
         (use (gen_context' .@ is_sized'))
         (queryl variable_type').

  Definition gen_op_instr_of_typ (τ : typ) : GenLLVM (instr_id * instr typ)
    := i <- ret INSTR_Op <*> gen_op τ;;
       id <- genInstrId τ;;
       ret (id, i).

  Definition gen_op_instr : GenLLVM (instr_id * instr typ)
    := τ <- gen_op_typ;;
       gen_op_instr_of_typ τ.

  Definition gen_ptr_or_vector_ptr (τ : typ) : GenLLVM (option Ent) :=
    gen_var_of_typ_ent (gen_context' .@ is_ptr_vector') (ret true) τ.

  Definition gen_ptrtoint (ptr_ent : Ent) (tptr : typ) : GenLLVM (instr_id * instr typ) :=
    annotate "gen_ptrtoint"
      (let gen_typ_in_ptr (tptr : typ) :=
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
       '(id, e) <- genInstrIdEnt typ_from_cast;;
       ptr_name <- use (gen_context' .@ entl ptr_ent .@ name');;
       match ptr_name with
       | None => failGen "gen_ptrtoint: unnamed pointer, shouldn't happen."
       | Some ptr_name =>
           let ptr_exp := EXP_Ident ptr_name in
           (* TODO: Copy whether the pointer is deterministic *)
           d <- use (gen_context' .@ entl ptr_ent .@ deterministic');;
           (* Consider pointers nondeterministic for now. Currently
              causes problems. E.g., a pointer returned from a function
              defaults to deterministic *)
           (gen_context' .@ entl e .@ deterministic') .= false;;
           (gen_context' .@ entl e .@ from_pointer') .= ret ptr_ent;;
           ret (id, INSTR_Op (OP_Conversion Ptrtoint tptr ptr_exp typ_from_cast))
       end).

  (* Generate basic instructions.
     Note: this function returns a list because when we generate an alloca we must initialize it...

     TODO: don't initialize alloca and flag it as non-deterministic?
   *)
  Definition gen_instr : GenLLVM (list (instr_id * instr typ)) :=
    annotate "gen_instr"
      (ointtoptr_info <- gen_inttoptr_info;;
       osized_ptr_typ <- gen_sized_ptr_type;;
       ovalid_ptr_vecptr <- gen_valid_ptr_vecptr_ent;;
       oagg_typ <- gen_indexable_type;;
       ovec_typ <- gen_vec_type;;
       oinsertvalue_typ <- gen_insertvalue_type;;
       ofun_ptr_typ <- gen_function_pointer_type;;
       osized_typ <- gen_sized_typ_in_context;;
       oneOf_LLVM
         ([ op <- gen_op_instr;; t <- gen_op_typ;;
            ret [op]
            ; fmap ret gen_bitcast
           ]
            ++ (* TODO: generate multiple element allocas. Will involve changing initialization *)
            (* num_elems <- ret None;; (* gen_opt_LLVM (resize_LLVM 0 gen_int_texp);; *) *)
            (* align <- ret None;; *)
            maybe [] (fun t => ['(id, e) <- genLocalEnt (TYPE_Pointer (Some t));;
                             (* Allocas are non-deterministic *)
                             gen_context' .@ entl e .@ deterministic' .= false;;
                             store <- gen_store_to (TYPE_Pointer (Some t), EXP_Ident id);;
                             ret [(IId (ident_to_raw_id id), INSTR_Alloca t []); store]]) osized_typ
            ++ maybe [] (fun t => fmap (fun x => [x]) <$> [gen_load t; gen_store t; gen_gep t]) osized_ptr_typ
            ++ maybe [] (fun '(e, t) => [(fun x => [x]) <$> gen_ptrtoint e t]) ovalid_ptr_vecptr
            ++ maybe [] (fun '(e, id, t) => [(fun x => [x]) <$> gen_inttoptr e id t]) ointtoptr_info
            ++ maybe [] (fun t => [(fun x => [x]) <$> gen_extractvalue t]) oagg_typ
            ++ maybe [] (fun t => [(fun x => [x]) <$> gen_insertvalue t]) oinsertvalue_typ
            ++ maybe [] (fun t => fmap (fun x => [x]) <$> [gen_extractelement t; gen_insertelement t]) ovec_typ
            ++ maybe [] (fun t => [(fun x => [x]) <$> gen_call t]) ofun_ptr_typ
         )).

  Fixpoint gen_code_length (n : nat) : GenLLVM (code typ)
    := match n with
       | O => ret []
       | S n' =>
           instr <- gen_instr;;
           rest  <- gen_code_length n';;
           ret (instr ++ rest)%list
       end.

  Definition block_size : nat := 20.

  Definition gen_code : GenLLVM (code typ)
    := annotate "gen_code"
         (n <- lift (resize block_size arbitrary);;
          gen_code_length n).

  Definition instr_id_to_raw_id (fail_msg : string) (i : instr_id) : raw_id :=
    match i with
    | IId id => id
    | IVoid n => Name ("fail (instr_id_to_raw_id): " ++ fail_msg)
    end.

  (* Returns a terminator and a list of new blocks that it reaches *)
  (* Need to make returns more likely than branches so we don't get an
     endless tree of blocks *)

  Definition gen_ret (τ : typ) : GenLLVM (terminator typ)
    := nt <- normalize_type_GenLLVM τ;;
       match nt with
       | TYPE_Void => ret TERM_Ret_void
       | _ =>
           e <- gen_exp_sz0%nat τ;;
           ret (TERM_Ret (τ, e))
       end.

  Fixpoint gen_terminator_sz
    (sz : nat)
    (t : typ) (* Return type *)
    (back_blocks : list block_id) (* Blocks that I'm allowed to jump back to *)
    {struct t} : GenLLVM (terminator typ * list (block typ))
    :=
    match sz with
    | 0%nat =>
        term <- gen_ret t;;
        ret (term, [])
    | S sz' =>
        (* Need to lift oneOf to GenLLVM ...*)
        freq_LLVM_thunked
          ([ (6%nat, fun _ => gen_terminator_sz 0 t back_blocks)
               (* Simple jump *)
             ; (min sz' 6%nat, fun _ => '(b, (bh, bs)) <- gen_blocks_sz sz' t back_blocks;; ret (TERM_Br_1 (blk_id b), (bh::bs)))
                 (* Conditional branch, with no backloops *)
             ; (min sz' 6%nat,
                 fun _ =>
                   c <- gen_exp_sz0 (TYPE_I 1);;

                   (* Generate first branch *)
                   (* We backtrack contexts so blocks in second branch *)
                   (* don't refer to variables from the first *)
                   (* branch. *)
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
       := bid <- new_block_id;;
          (* annotate_debug ("----Genblock: " ++ show bid);; *)
          code <- gen_code;;
          '(term, bs) <- gen_terminator_sz (sz - 1) t back_blocks;;
          let b := {| blk_id   := bid
                   ;  blk_phis := []
                   ;  blk_code := code
                   ;  blk_term := term
                   ;  blk_comments := None
                   |} in
          ret (b, (b, bs))
  with gen_loop_sz
         (sz : nat)
         (t : typ)
         (back_blocks : list block_id) (* Blocks that I'm allowed to jump back to *)
         (bound : LLVMAst.int_ast) {struct t} : GenLLVM (terminator typ * (block typ * list (block typ)))
       :=
         bid_entry <- new_block_id;;
         (* TODO: make it so I can generate constant expressions *)
         '(loop_init_instr_id, loop_init_instr) <- gen_op_instr_of_typ (TYPE_I 32) (* TODO: big ints *);;
         let loop_init_instr_raw_id := instr_id_to_raw_id "loop init id" loop_init_instr_id in
         bound' <- lift_GenLLVM (choose (0, bound));;
         let gen_icmp (τ : typ) : GenLLVM (instr_id * instr typ) :=
           iid <- genInstrId (TYPE_I 1);;
           ret (iid, INSTR_Op (OP_ICmp Ule τ (EXP_Ident (ID_Local loop_init_instr_raw_id)) (EXP_Integer bound')))
         in
         '(loop_cmp_id, loop_cmp) <- gen_icmp (TYPE_I 32);; (* TODO: big ints *)
         let loop_cmp_raw_id := instr_id_to_raw_id "loop_cmp_id" loop_cmp_id in
         let gen_select (τ : typ) : GenLLVM (instr_id * instr typ) :=
           let lower_exp := OP_Select (TYPE_I 1, (EXP_Ident (ID_Local loop_cmp_raw_id)))
                              (τ, (EXP_Ident (ID_Local loop_init_instr_raw_id)))
                              (τ, EXP_Integer bound') in
           iid <- genInstrId τ;;
           ret (iid, INSTR_Op lower_exp)
         in
         '(select_id, select_instr) <- gen_select (TYPE_I 32);;
         let loop_final_init_id_raw := instr_id_to_raw_id "loop iterator id" select_id in
         '(loop_cond_id, loop_cond) <-
           (let loop_cond_exp := INSTR_Op (OP_ICmp Ugt (TYPE_I 32 (* TODO: big ints *)) (EXP_Ident (ID_Local loop_final_init_id_raw)) (EXP_Integer 0)) in
           iid <- genInstrId (TYPE_I 1);;
           ret (iid, loop_cond_exp));;

         let entry_code : list (instr_id * instr typ) := [(loop_init_instr_id, loop_init_instr); (loop_cmp_id, loop_cmp); (select_id, select_instr); (loop_cond_id, loop_cond)] in

         (* Generate end blocks *)
         '(loop_bid, phi_id, bid_entry, bid_next, next_instr_raw_id, next_block, end_bid, end_blocks) <- backtrack_variable_ctxs
                  ('(_, (end_b, end_bs)) <- gen_blocks_sz (sz / 2) t back_blocks;;
                   let end_blocks := end_b :: end_bs in
                   let end_bid := blk_id end_b in

                   bid_next <- new_block_id;;
                   loop_bid <- new_block_id;;
                   phi_id <- new_local_id;;

                   (* Block for controlling the next iteration of the loop *)
                   '(next_instr_id, next_instr) <-
                     (iid <- genLocal (TYPE_I 32);;
                      let next_exp := OP_IBinop (Sub false false) (TYPE_I 32 (* TODO: big ints *)) (EXP_Ident (ID_Local phi_id)) (EXP_Integer 1) in
                      ret (IId (ident_to_raw_id iid), INSTR_Op next_exp));;
                   let next_instr_raw_id := instr_id_to_raw_id "next_exp" next_instr_id in

                   '(next_cond_id, next_cond) <-
                     (let next_cond_exp := OP_ICmp Ugt (TYPE_I 32 (* TODO: big ints *)) (EXP_Ident (ID_Local next_instr_raw_id)) (EXP_Integer 0) in
                      iid <- genInstrId (TYPE_I 1);;
                      ret (iid, INSTR_Op next_cond_exp));;
                   let next_cond_raw_id := instr_id_to_raw_id "next_cond_exp" next_cond_id in

                   let next_code := [(next_instr_id, next_instr); (next_cond_id, next_cond)] in
                   let next_block := {| blk_id   := bid_next
                                     ; blk_phis := []
                                     ; blk_code := next_code
                                     ; blk_term := TERM_Br (TYPE_I 1, (EXP_Ident (ID_Local next_cond_raw_id))) loop_bid end_bid
                                     ; blk_comments := None
                                     |} in
                   ret (loop_bid, phi_id, bid_entry, bid_next, next_instr_raw_id, next_block, end_bid, end_blocks));;

         (* Generate loop blocks *)
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
       | Name sname => String.eqb sname "main"%string
       | Anon _
       | Raw _ => false
       end.
  (* Don't want to generate CFGs, actually. Want to generated TLEs *)

  Definition gen_definition_h (name : global_id) (ret_t : typ) (args_t : list typ) : GenLLVM (definition typ (block typ * list (block typ)))
    :=
    (* Generate argument variables *)
    args <- map_monad genLocal args_t;;
    let f_type := TYPE_Function ret_t args_t false in
    let param_attr_slots := map (fun t => []) args in
    let prototype :=
      mk_declaration name f_type
        ([], param_attr_slots)
        []
        []
    in

    bs <- gen_blocks ret_t;;
    ret (mk_definition (block typ * list (block typ)) prototype (map ident_to_raw_id args) bs).


  Definition gen_definition (name : global_id) (ret_t : typ) (args : list typ) : GenLLVM (definition typ (block typ * list (block typ)))
    :=
    annotate "gen_definition"
      (dfn <- backtrackMetadata (gen_definition_h name ret_t args);;
       e <- add_to_global_ctx (ID_Global name, TYPE_Pointer (Some dfn.(df_prototype).(dc_type)));;
       (gen_context' .@ entl e .@ deterministic') .= false;;
       ret dfn).

  Definition gen_new_definition (ret_t : typ) (args : list typ) : GenLLVM (definition typ (block typ * list (block typ)))
    :=
    name <- new_global_id;;
    gen_definition name ret_t args.

  Definition gen_helper_function: GenLLVM (definition typ (block typ * list (block typ)))
    :=
    ret_t <- hide_ctx gen_sized_typ;;
    args  <- listOf_LLVM (hide_ctx gen_sized_typ);;
    gen_new_definition ret_t args.

  Definition gen_helper_function_tle : GenLLVM (toplevel_entity typ (block typ * list (block typ)))
    := ret TLE_Definition <*> gen_helper_function.

  Definition gen_helper_function_tle_multiple : GenLLVM (list (toplevel_entity typ (block typ * list (block typ))))
    := listOf_LLVM gen_helper_function_tle.

  Definition gen_main : GenLLVM (definition typ (block typ * list (block typ)))
    := gen_definition (Name "main") (TYPE_I 8) [].

  Definition gen_main_tle : GenLLVM (toplevel_entity typ (block typ * list (block typ)))
    := ret TLE_Definition <*> gen_main.

  Definition gen_typ_tle : GenLLVM (toplevel_entity typ (block typ * list (block typ)))
    :=
    name <- new_local_id;;
    let id := ID_Local name in
    τ <- oneOf_LLVM_thunked
          [ (fun _ => ret TYPE_Struct <*> (k <- lift (choose (0, 5)%nat);;
                                        vectorOf_LLVM k gen_typ_non_void_wo_fn))
            ; (fun _ => ret TYPE_Packed_struct <*> (k <- lift (choose (0, 5)%nat);;
                                        vectorOf_LLVM k gen_typ_non_void_wo_fn))
          ];;
    add_to_typ_ctx (id, τ);;
    ret (TLE_Type_decl id τ).

  Definition gen_typ_tle_multiple : GenLLVM (list (toplevel_entity typ (block typ * list (block typ))))
    := listOf_LLVM gen_typ_tle.

  Definition gen_global_var : GenLLVM (global typ)
    :=
    name <- new_global_id;;
    t <- hide_ctx gen_sized_typ;;
    (* annotate_debug ("--Generate: Global: @" ++ show name ++ " " ++ show t);; *)
    opt_exp <- fmap Some (hide_ctx (gen_exp_sz0 t));;
    e <- add_to_global_ctx (ID_Global name, TYPE_Pointer (Some t));;
    (gen_context' .@ entl e .@ deterministic') .= false;;
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

  Definition list_high_level_dec : list (declaration typ) :=
    [
      let puts_id := Name "puts" in
      let puts_typ := TYPE_Function (TYPE_I 32) [(TYPE_Pointer (Some (TYPE_I 8)))] false in
      mk_declaration puts_id puts_typ ([], []) [] []
    ].

  Definition gen_list_high_level_tle : GenLLVM (list (toplevel_entity typ (block typ * list (block typ)))) :=
    ret (map TLE_Declaration list_high_level_dec).

  Definition gen_llvm : GenLLVM (list (toplevel_entity typ (block typ * list (block typ))))
    :=
    high_levels <- gen_list_high_level_tle;;
    defined_typs <- gen_typ_tle_multiple;;
    globals <- gen_global_tle_multiple;;
    functions <- gen_helper_function_tle_multiple;;
    main <- gen_main_tle;;
    res_globals <- get_global_memo;;
    let new_globals := (globals ++ map TLE_Global res_globals)%list in
    ret (high_levels ++ defined_typs ++ new_globals ++ functions ++ [main])%list.

End InstrGenerators.
