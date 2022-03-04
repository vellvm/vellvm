(** * Plugging the pieces together: executable and propositional semantics for Vellvm *)

(* begin hide *)
From Coq Require Import
     Ensembles List String ZArith
     Lists.ListSet.

From ITree Require Import
     ITree
     Events.State.

From ExtLib Require Import
     Structures.Monads
     Data.Map.FMapAList.

From Vellvm Require Import
     Utilities
     Syntax
     Semantics.LLVMEvents
     Semantics.Denotation
     Semantics.IntrinsicsDefinitions
     Handlers.Handlers
     Semantics.InterpretationStack.

Import MonadNotation.
Import ListNotations.
Import Monads.
Import SemNotations.
Open Scope string_scope.

(* end hide *)

(** * Top Level
   This file ties things together to concretely defines the semantics of a [Vellvm]
   program. It covers two main tasks to do so: to initialize the memory, and to
   chain together the successive interpreters.
   As such, the raw denotation of a [Vellvm] program in terms of an [itree] is
   progressively stripped out of its events.
   We provide two such chains of interpretations: a model, that handles the
   internal non-determinism due to under-defined values into the non-determinism
   monad; and an executable one, that arbitrarily interpret under-defined values
   by setting its bits to 0.
 *)

(** * Initialization
    The initialization phase allocates and initializes globals,
    and allocates function pointers. This initialization phase is internalized
    in [Vellvm], it is an [itree] as any other.
 *)

Definition allocate_global (g:global dtyp) : itree L0 unit :=
  'v <- trigger (Alloca (g_typ g));;
  trigger (GlobalWrite (g_ident g) v).

Definition allocate_globals (gs:list (global dtyp)) : itree L0 unit :=
  map_monad_ allocate_global gs.

(* Returns `true` only if both function are named and have
     the same name.
 *)
Definition function_name_eq (a b:function_id) : bool :=
  match a, b with
  | Name aname, Name bname => eqb aname bname
  | _, _ => false
  end.

Definition allocate_declaration (d:declaration dtyp) : itree L0 unit :=
  match List.find (fun x => function_name_eq (dc_name d) (dc_name x)) defined_intrinsics_decls with
  | Some _ => Ret tt (* Don't allocate pointers for LLVM intrinsics declarations *)
  | None =>
    'v <- trigger (Alloca DTYPE_Pointer);;
    trigger (GlobalWrite (dc_name d) v)
  end.

Definition allocate_declarations (ds:list (declaration dtyp)) : itree L0 unit :=
  map_monad_ allocate_declaration ds.

Definition initialize_global (g:global dtyp) : itree exp_E unit :=
  let dt := (g_typ g) in
  a <- trigger (GlobalRead (g_ident g));;
  uv <- match (g_exp g) with
       | None => ret (UVALUE_Undef dt)
       | Some e =>  ⟦ e at dt ⟧e
       end ;;
  dv <- concretize_or_pick uv True ;;
  trigger (Store a dv).

Definition initialize_globals (gs:list (global dtyp)): itree exp_E unit :=
  map_monad_ initialize_global gs.

Definition build_global_environment (CFG : CFG.mcfg dtyp) : itree L0 unit :=
  allocate_declarations ((m_declarations CFG) ++ (List.map (df_prototype) (m_definitions CFG)));;
  allocate_globals (m_globals CFG) ;;
  translate exp_to_L0 (initialize_globals (m_globals CFG)).

(** Local environment implementation
    The map-based handlers are defined parameterized over a domain of key and value.
    We now pick concrete such domain.
    Note that while local environments may store under-defined values,
    global environments are statically guaranteed to store [dvalue]s.
 *)
Definition function_env := FMapAList.alist dvalue D.function_denotation.

(**
   Denotes a function and returns its pointer.
 *)

Definition address_one_function (df : definition dtyp (CFG.cfg dtyp)) : itree L0 (dvalue * D.function_denotation) :=
  let fid := (dc_name (df_prototype df)) in
  fv <- trigger (GlobalRead fid) ;;
  ret (fv, ⟦ df ⟧f).

(**
   We are now ready to define our semantics. Guided by the events and handlers,
   we work in layers: the first layer is defined as the uninterpreted [itree]
   resulting from the denotation of the LLVM program. Each successive handler
   then transform a tree at layer n to a tree at layer (n+1).
 *)
(**
   In order to limit bloated type signature, we name the successive return types.
 *)

Notation res_L1 := (global_env * uvalue)%type.
Notation res_L2 := (local_env * lstack * res_L1)%type.
Notation res_L3 := (memory_stack * res_L2)%type.
Notation res_L4 := (memory_stack * (local_env * lstack * (global_env * uvalue)))%type.

(**
     Full denotation of a Vellvm program as an interaction tree:
     * initialize the global environment;
     * point wise denote each function;
     * retrieve the address of the entry point function;
     * tie the mutually recursive know and run it starting from the 
     * entry point
     *
     * This code should be semantically equivalent to running the following
     * LLVM snippet after initializing the global configuration:
     *
     *  %ans = call ret_typ entry (args)
     *  ret ret_typ %ans
     *)
Definition denote_vellvm
           (ret_typ : dtyp)
           (entry : string)
           (args : list uvalue)
           (mcfg : CFG.mcfg dtyp) : itree L0 uvalue :=
  build_global_environment mcfg ;;
  'defns <- map_monad address_one_function (m_definitions mcfg) ;;
  'addr <- trigger (GlobalRead (Name entry)) ;;
  denote_mcfg defns ret_typ (dvalue_to_uvalue addr) args.


(* main_args and denote_vellvm_main may not be needed anymore, but I'm keeping them 
     For backwards compatibility.
 *)
(* (for now) assume that [main (i64 argc, i8** argv)]
    pass in 0 and null as the arguments to main
    Note: this isn't compliant with standard C semantics
 *)
Definition main_args := [DV.UVALUE_I64 (DynamicValues.Int64.zero);
                        DV.UVALUE_Addr (Addr.null)
                        ].

Definition denote_vellvm_main (mcfg : CFG.mcfg dtyp) : itree L0 uvalue :=
  denote_vellvm (DTYPE_I (32)%N) "main" main_args mcfg.

(**
     Now that we know how to denote a whole llvm program, we can _interpret_
     the resulting [itree].
 *)
Definition interpreter_gen
           (ret_typ : dtyp)
           (entry : string)
           (args : list uvalue)
           (prog: list (toplevel_entity typ (block typ * list (block typ))))
  : itree L4 res_L4 :=
  let t := denote_vellvm ret_typ entry args (convert_types (mcfg_of_tle prog)) in
  interp_mcfg4_exec t [] ([],[]) empty_memory_stack.

(**
     Finally, the reference interpreter assumes no user-defined intrinsics and starts 
     from "main" using bogus initial inputs.
 *)
Definition interpreter := interpreter_gen (DTYPE_I 32%N) "main" main_args.

(**
     We now turn to the definition of our _model_ of vellvm's semantics. The
     process is extremely similar to the one for defining the executable
     semantics, except that we use, where relevant, the handlers capturing
     all allowed behaviors into the [Prop] monad.
 *)
(**
     The model simply performs the syntactic conversion from [toplevel_entity]
     to [mcfg], normalizes the types, denotes the [mcfg] and finally interprets the tree
     starting from empty environments.
 *)
Definition model_gen
           (ret_typ : dtyp)
           (entry : string)
           (args : list uvalue)
           (prog: list (toplevel_entity typ (block typ * list (block typ))))
  : PropT L4 (memory_stack * (local_env * lstack * (global_env * uvalue))) :=
  let t := denote_vellvm ret_typ entry args (convert_types (mcfg_of_tle prog)) in
  ℑs eq t [] ([],[]) empty_memory_stack. 

(**
     Finally, the official model assumes no user-defined intrinsics.
 *)
Definition model := model_gen (DTYPE_I 32%N) "main" main_args.

