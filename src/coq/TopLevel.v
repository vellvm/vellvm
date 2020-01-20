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
     Ensembles List String.

From ITree Require Import
     ITree
     Events.State.

From ExtLib Require Import
     Structures.Monads
     Data.Map.FMapAList.

From Vellvm Require Import
     AstLib
     TransformTypes
     DynamicTypes
     LLVMEvents
     Denotation
     Environment
     IntrinsicsDefinitions
     Handlers.Global
     Handlers.Local
     Handlers.Stack
     Handlers.Memory
     Handlers.Intrinsics
     Handlers.UndefinedBehaviour
     LLVMAst
     Util
     Error
     Handlers.Pick
     PropT.

Import MonadNotation.
Import ListNotations.
Import Monads.

Module IO := LLVMEvents.Make(Memory.A).
Module M := Memory.Make(IO).
Module D := Denotation(Memory.A)(IO).
Module IS := IntrinsicsDefinitions.Make(A)(IO).
Module INT := Intrinsics.Make(Memory.A)(IO).
Module P := Pick.Make(Memory.A)(IO).
Import IO.
Export IO.DV.

Module TopLevelEnv <: Environment.
  Definition local_env  := FMapAList.alist raw_id uvalue.
  Definition global_env := FMapAList.alist raw_id dvalue.
  Definition memory     := M.memory_stack.
  Definition stack      := @stack (list (raw_id * uvalue)).

  Open Scope string_scope.

  Notation res_L0 := uvalue (* (only parsing) *).
  Notation res_L1 := (global_env * res_L0)%type (* (only parsing) *).
  Notation res_L2 := (local_env * stack * res_L1)%type (* (only parsing) *).
  Notation res_L3 := (memory * res_L2)%type (* (only parsing) *).
  Notation res_L4 := (memory * (local_env * stack * (global_env * uvalue)))%type (* (only parsing) *).

  
  Section WithContext.


    (* Context E is the "general ambient context of non-call related events." *)
    Context {E X1 X2 X3 X4 X5 X6 X7 X8}
            `{LLVMGEnvE +? X1 -< E}
            `{LLVMEnvE +? X2 -< E}
            `{FailureE +? X3 -< E}
            `{UBE +? X4 -< E}
            `{PickE +? X5 -< E}
            `{MemoryE +? X6 -< E}
            `{IntrinsicE +? X7 -< E}
            `{ExternalCallE +? X8 -< E}.

    Context {E2 X9}
            `{CallE +? E -< E2}
            `{LLVMStackE +? X9 -< E2}.

(* end hide *)

  (** This file ties things together to concretely defines the semantics of a
   [Vellvm] program. It covers two main tasks to do so: to initialize the
   memory, and to chain together the successive interpreters.  As such, the raw
   denotation of a [Vellvm] program in terms of an [itree] is progressively
   stripped out of its events.  We provide two such chains of interpretations: a
   model, that handles the internal non-determinism due to under-defined values
   into the non-determinism monad; and an executable one, that arbitrarily
   interpret under-defined values by setting its bits to 0.  *)

  (** Initialization

    The initialization phase allocates and initializes globals, and allocates
    function pointers.  This initialization phase is internalized in [Vellvm],
    it is an [itree] as any other.  *)

    Definition allocate_global (g:global dtyp) : itree E unit :=
      'v <- trigger (Alloca (g_typ g));;
       trigger (GlobalWrite (g_ident g) v).

    Definition allocate_globals (gs:list (global dtyp)) : itree E unit :=
      map_monad_ allocate_global gs.

    (* Who is in charge of allocating the addresses for external functions declared in this mcfg? *)
    Definition allocate_declaration (d:declaration dtyp) : itree E unit :=
      (* SAZ TODO:  Don't allocate pointers for LLVM intrinsics declarations *)
      vis (Alloca DTYPE_Pointer) (fun v => trigger (GlobalWrite (dc_name d) v)).

    Definition allocate_declarations (ds:list (declaration dtyp)) : itree E unit :=
      map_monad_ allocate_declaration ds.

    Definition initialize_global (g:global dtyp) : itree E unit :=
      let dt := (g_typ g) in
      a <- trigger (GlobalRead (g_ident g));;
        uv <- match (g_exp g) with
             | None => ret (UVALUE_Undef dt)
             | Some e => D.denote_exp (Some dt) e
             end ;;
        (* CB TODO: Do we need pick here? *)
        dv <- trigger (pick uv True) ;;
        trigger (Store a dv).

    Definition initialize_globals (gs:list (global dtyp)): itree E unit :=
      map_monad_ initialize_global gs.

    Definition build_global_environment (CFG : CFG.mcfg dtyp) : itree E unit :=
      allocate_globals (m_globals CFG) ;;
      allocate_declarations ((m_declarations CFG) ++ (List.map (df_prototype) (m_definitions CFG)));;
      initialize_globals (m_globals CFG).

    (** Local environment implementation

    The map-based handlers are defined parameterized over a domain of key and
    value.  We now pick concrete such domain.  Note that while local
    environments may store under-defined values, global environments are
    statically guaranteed to store [dvalue]s.  *)
    Definition function_env := FMapAList.alist dvalue (@D.function_denotation E2).

    (** Denotes a function and returns its pointer.  *)

    Definition address_one_function (df : definition dtyp (CFG.cfg dtyp)):
      itree E (dvalue * @D.function_denotation E2) :=
      let fid := (dc_name (df_prototype df)) in
      fv <- trigger (GlobalRead fid) ;;
      ret (fv, D.denote_function df).

    (* (for now) assume that [main (i64 argc, i8** argv)]

       - pass in 0 and null as the arguments to main 
       - Note: this isn't compliant with standard C semantics 

      TODO: implement command-line arguments
     *)
    Definition main_args := [DV.DVALUE_I64 (DynamicValues.Int64.zero);
                               DV.DVALUE_Addr (Memory.A.null)
                            ].

    (** Transformation and normalization of types. *)
    Definition eval_typ (CFG:CFG.mcfg typ) (t:typ) : dtyp :=
      TypeUtil.normalize_type_dtyp (m_type_defs CFG) t.

    Definition normalize_types (CFG:(CFG.mcfg typ)) : (CFG.mcfg dtyp) :=
      TransformTypes.fmap_mcfg _ _ (eval_typ CFG) CFG.

  (**
   We are now ready to define our semantics. Guided by the events and handlers,
   we work in layers: the first layer is defined as the uninterpreted [itree]
   resulting from the denotation of the LLVM program. Each successive handler
   then transform a tree at layer n to a tree at layer (n+1).
   *)
  (**
   In order to limit bloated type signature, we name the successive return types.
   *)

    
  (**
l     Full denotation of a Vellvm program as an interaction tree:
     * initialize the global environment;
     * point wise denote each function;
     * retrieve the address of the main function;
     * tie the mutually recursive know and run it starting from the main.
     *)

  (*
    denoting a CFG: no ExtCall.
    The function_denotation should not expose Calls.
    It should be a function from (list dvalue) to  t d

   *)
  Definition denote_vellvm (mcfg : CFG.mcfg dtyp) : itree _ res_L0 :=
    build_global_environment mcfg ;;
    'defns <- map_monad address_one_function (m_definitions mcfg);;
    'addr <- trigger (GlobalRead (Name "main")) ;;
    D.denote_mcfg defns DTYPE_Void addr main_args.

  (**
     Now that we know how to denote a whole llvm program, we can _interpret_
     the resulting [itree].
   *)

  (* Explicit application of a state to a [stateT] computation: convenient to ease some rewriting,
     but semantically equivalent to simply applying the state. *)
  Definition run_state {E A env} (R : Monads.stateT env (itree E) A) (st: env) : itree E (env * A) := R st.


  End WithContext.

  (* This is basically the same definition as IO.L0 *)
  Definition IOE := FailureE +' ExternalCallE +' IntrinsicE +' LLVMGEnvE +' LLVMEnvE +' LLVMStackE +' MemoryE +' PickE +' UBE +' DebugE.

  Typeclasses eauto := 5.
  Definition interp_vellvm_exec_user {R: Type} (user_intrinsics: INT.intrinsic_definitions)
             (trace: itree IOE R)
             (g: global_env)
             (l: local_env * @Stack.stack local_env)
             (m: M.memory_stack)
 :=
    let L0_trace       := INT.interpret_intrinsics user_intrinsics trace in
    let L1_trace       := run_state (interp_global L0_trace) g in
    let L2_trace       := run_state (interp_local_stack (handle_local (v:=res_L0)) L1_trace) l in
    let L3_trace       := run_state (M.interp_memory L2_trace) m in
    let L4_trace       := P.interp_undef L3_trace in
    let L5_trace       := interp_UB L4_trace in
    L5_trace.
  Typeclasses eauto := .

  (**
     The interpreter now simply performs the syntactic conversion from [toplevel_entity]
     to [mcfg], normalizes the types, denotes the [mcfg] and finally interprets the tree
     starting from empty environments.
   *)
  Definition interpreter_user
             (user_intrinsics: IS.intrinsic_definitions)
             (prog: list (toplevel_entity typ (list (block typ))))
    : itree (FailureE +' ExternalCallE +' IntrinsicE +' DebugE)
            (M.memory_stack * (local_env * Stack.stack * (global_env * _)))             
    :=
    let scfg := Vellvm.AstLib.modul_of_toplevel_entities _ prog in

    match CFG.mcfg_of_modul _ scfg with
    | Some ucfg =>
      let mcfg := normalize_types ucfg in

      let t := denote_vellvm mcfg in

      interp_vellvm_exec_user user_intrinsics t [] ([],[]) (M.empty, [[]])

    | None => raise "Ill-formed program: mcfg_of_modul failed."
    end.

  (**
     Finally, the reference interpreter assumes no user-defined intrinsics.
   *)
  Definition interpreter := interpreter_user [].

  (**
     We now turn to the definition of our _model_ of vellvm's semantics. The
     process is extremely similar to the one for defining the executable
     semantics, except that we use, where relevant, the handlers capturing
     all allowed behaviors into the [Prop] monad.
   *)
  
  Typeclasses eauto := 5.
  Definition interp_vellvm_model_user {R: Type} user_intrinsics (trace: itree IOE R) g l m :=
    let L0_trace       := INT.interpret_intrinsics user_intrinsics trace in
    let L1_trace       := run_state (interp_global L0_trace) g in
    let L2_trace       := run_state (interp_local_stack (handle_local (v:=res_L0)) L1_trace) l in
    let L3_trace       := run_state (M.interp_memory L2_trace) m in
    let L4_trace       := P.model_undef L3_trace in 
    let L5_trace       := model_UB L4_trace in
    L5_trace.
  Typeclasses eauto := .
  
  (**
     The model now simply performs the syntactic conversion from [toplevel_entity]
     to [mcfg], normalizes the types, denotes the [mcfg] and finally interprets the tree
     starting from empty environments.
   *)
  Definition model_user (user_intrinsics: IS.intrinsic_definitions) (prog: list (toplevel_entity typ (list (block typ)))) :=
    let scfg := Vellvm.AstLib.modul_of_toplevel_entities _ prog in

    match CFG.mcfg_of_modul _ scfg with
    | Some ucfg =>
      let mcfg := normalize_types ucfg in

      let t := denote_vellvm mcfg in

      interp_vellvm_model_user user_intrinsics t [] ([],[]) (M.empty, [[]])

    | None => lift (raise "Ill-formed program: mcfg_of_modul failed.")
    end.

  (**
     Finally, the reference interpreter assumes no user-defined intrinsics.
   *)
  Definition model := model_user [].

End TopLevelEnv.
