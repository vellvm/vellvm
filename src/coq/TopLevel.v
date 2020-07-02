(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

(** * Plugging the pieces together: executable and propositional semantics for Vellvm *)

(* begin hide *)
From Coq Require Import
     Ensembles List String ZArith.

From ITree Require Import
     ITree
     Events.State.

From ExtLib Require Import
     Structures.Monads
     Data.Map.FMapAList.

From Vellvm Require Import
     LLVMAst
     AstLib
     DynamicTypes
     LLVMEvents
     Denotation
     IntrinsicsDefinitions
     Handlers.Handlers
     TypToDtyp
     Util
     Error
     PropT
     InterpreterMCFG.

Import MonadNotation.
Import ListNotations.
Import Monads.

Module D   := Denotation Addr LLVMEvents.
Module IS  := IntrinsicsDefinitions.Make Addr LLVMEvents.
Export DV.
Import D IS.

(* Module TopLevelEnv. *)

  Open Scope string_scope.

  (* end hide *)

  (**
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

  (** Initialization
    The initialization phase allocates and initializes globals,
    and allocates function pointers.
    This initialization phase is internalized in [Vellvm], it is
    an [itree] as any other.
   *)

  Definition allocate_global (g:global dtyp) : itree L0 unit :=
    'v <- trigger (Alloca (g_typ g));;
    trigger (GlobalWrite (g_ident g) v).

  Definition allocate_globals (gs:list (global dtyp)) : itree L0 unit :=
    map_monad_ allocate_global gs.

  (* Who is in charge of allocating the addresses for external functions declared in this mcfg? *)
  Definition allocate_declaration (d:declaration dtyp) : itree L0 unit :=
    (* SAZ TODO:  Don't allocate pointers for LLVM intrinsics declarations *)
    'v <- trigger (Alloca DTYPE_Pointer);;
    trigger (GlobalWrite (dc_name d) v).

  Definition allocate_declarations (ds:list (declaration dtyp)) : itree L0 unit :=
    map_monad_ allocate_declaration ds.

  Definition initialize_global (g:global dtyp) : itree exp_E unit :=
    let dt := (g_typ g) in
    a <- trigger (GlobalRead (g_ident g));;
    uv <- match (g_exp g) with
         | None => ret (UVALUE_Undef dt)
         | Some e => D.denote_exp (Some dt) e
         end ;;
    dv <- concretize_or_pick uv True ;;
    trigger (Store a dv).

  Definition initialize_globals (gs:list (global dtyp)): itree exp_E unit :=
    map_monad_ initialize_global gs.

  Definition build_global_environment (CFG : CFG.mcfg dtyp) : itree L0 unit :=
    allocate_globals (m_globals CFG) ;;
    allocate_declarations ((m_declarations CFG) ++ (List.map (df_prototype) (m_definitions CFG)));;
    translate _exp_E_to_L0 (initialize_globals (m_globals CFG)).

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
    ret (fv, D.denote_function df).

  (**
     Conversion to dynamic types
   *)

  Definition convert_types (CFG:(CFG.mcfg typ)) : (CFG.mcfg dtyp) :=
    convert_typ (m_type_defs CFG) CFG.

  (**
   We are now ready to define our semantics. Guided by the events and handlers,
   we work in layers: the first layer is defined as the uninterpreted [itree]
   resulting from the denotation of the LLVM program. Each successive handler
   then transform a tree at layer n to a tree at layer (n+1).
   *)
  (**
   In order to limit bloated type signature, we name the successive return types.
   *)

  Notation res_L1 := (global_env * uvalue)%type (* (only parsing) *).
  Notation res_L2 := (local_env * lstack * res_L1)%type (* (only parsing) *).
  Notation res_L3 := (memory_stack * res_L2)%type (* (only parsing) *).
  Notation res_L4 := (memory_stack * (local_env * lstack * (global_env * uvalue)))%type (* (only parsing) *).

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
    D.denote_mcfg defns ret_typ (dvalue_to_uvalue addr) args.


  (* SAZ: main_args and denote_vellvm_main may not be needed anymore, but I'm keeping them 
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
    denote_vellvm (DTYPE_I (32)%Z) "main" main_args mcfg.
    
  (**
     Now that we know how to denote a whole llvm program, we can _interpret_
     the resulting [itree].
   *)

  (**
     The interpreter now simply performs the syntactic conversion from [toplevel_entity]
     to [mcfg], normalizes the types, denotes the [mcfg] and finally interprets the tree
     starting from empty environments.
   *)
  Definition mcfg_of_tle (p: list (toplevel_entity typ (block typ * list (block typ)))) :=
    convert_types (CFG.mcfg_of_modul _ (modul_of_toplevel_entities _ p)).

  (* YZ TODO : We overload the term interpreter for the general notion of lifting handlers and
     for the executable version of the semantics *)
  Definition interpreter_user
             (ret_typ : dtyp)
             (entry : string)
             (args : list uvalue)
             (user_intrinsics: intrinsic_definitions)
             (prog: list (toplevel_entity typ (block typ * list (block typ))))
    : itree L5 res_L4 :=
    let t := denote_vellvm ret_typ entry args (mcfg_of_tle prog) in
    interp_to_L5_exec user_intrinsics t [] ([],[]) empty_memory_stack.

  (**
     Finally, the reference interpreter assumes no user-defined intrinsics and starts 
     from "main" using bogus initial inputs.
   *)
  Definition interpreter := interpreter_user (DTYPE_I 32%Z) "main" main_args [].

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
  Definition model_user
             (ret_typ : dtyp)
             (entry : string)
             (args : list uvalue)
             (user_intrinsics: IS.intrinsic_definitions)
             (prog: list (toplevel_entity typ (block typ * list (block typ))))
    : PropT L5 (memory_stack * (local_env * lstack * (global_env * uvalue))) :=
    let t := denote_vellvm ret_typ entry args (mcfg_of_tle prog) in
    interp_to_L5 Logic.eq user_intrinsics t [] ([],[]) empty_memory_stack. 

  (**
     Finally, the reference interpreter assumes no user-defined intrinsics.
   *)
  Definition model := model_user (DTYPE_I 32%Z) "main" main_args [].

(* End TopLevelEnv. *)
