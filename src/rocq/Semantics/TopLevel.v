(** * Plugging the pieces together: executable and propositional semantics for Vellvm *)

(* begin hide *)
From Stdlib Require Import Program.
From ExtLib Require Import Structures.Maps.
From ITree Require Import
  ITree
  Events.State.

From Vellvm Require Import Handlers.
From Vellvm Require Import
  Utils
  Syntax
  Params
  Interfaces.Memory
  Semantics.DynamicValues
  Semantics.LLVMEvents
  Semantics.Denotation
  Semantics.Operations
  Semantics.IntrinsicsDefinitions
  Semantics.InterpretationStack
  Semantics.VellvmIntegers
  Semantics.Libraries.
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

Section withParams.
  Context {Pa : Params}.


  (* SAZ: commenting this out for now, since it's trickier than we wanted *)
  (* Command-line arguments----------------------------------------------------------------------- *)

  (* To support command-line arguments we convert a list of Rocq strings into a preamble of
     global declarations with a form illustrated in tests/io/args_vellvm.ll.  Given N strings
     s_arg0, s_arg1, ..., s_argN.

     Arguments are parsed from the command line as (list (list Z)) where each Z is an i8.

     Note:
     - following C-style conventions, s_arg0 is the _name_ of the executable, so the
       (list (list Z)) should never be non-empty
     - we name the array of arguments argv itself [arg_gid (N+1)]
     Therefore, after initializing everything, we call main with
        UValue_r N) and whatever pointer we get from doing [u <- Load argv]
   *)
  (* TOPLEVEL Semantics  ------------------------------------------------------------------------- *)


  (** * Linking

    We first need to link external definitions. Currently, these definitions are
    only functions we hard-code into the environment for their usefulness.
    Linking occurs at the `toplevel_definition` level.

    NOTE: If we do not need to reason about these functions, linking can be done
    directly against the source .ll file via the `-L` flag of the interpreter.
   *)

  Definition ll_toplevel_entity := (toplevel_entity typ (block typ * list (block typ))).

  Definition ll_toplevel_entities := toplevel_entities typ (block typ * list (block typ)).

  Definition PREDEFINED_FUNCTIONS : ll_toplevel_entities := List.concat [].

  (* Example ensure_functions_defined : negb (Nat.eqb (List.length PREDEFINED_FUNCTIONS) O) .  *)
  (* Proof. reflexivity. Qed.   *)

  (* checks if `userdecl_n` is a name of a definition in `predefs`. *)
  Definition userdecl_defined_in (userdecl_n : string)
                                 (predefs    : ll_toplevel_entities) : bool :=
    existsb (fun predef =>
    match predef with
          TLE_Definition  {| df_prototype := {| dc_name := Name predef_n |}|}
             => String.eqb userdecl_n predef_n
      | _    => false
    end) predefs.

  Definition decl_defined_in (user_tle : ll_toplevel_entity)
                             (predefs  : ll_toplevel_entities) : bool :=
    match user_tle with
      | TLE_Declaration {| dc_name := Name n |} => userdecl_defined_in n predefs
      | _ => false
    end.

  Definition defines_decl :
    ll_toplevel_entities -> ll_toplevel_entity -> bool :=
    (Basics.flip decl_defined_in).

  (** Importantly, the linker _removes any declaration_ from the user's
     program that shares a name with a definition in `predefs`
     before joining the two programs.
     This is so that we can enforce our handcrafted declaration
     is the one referenced by their program.
  *)
  Definition link  (predefs  : ll_toplevel_entities)
                   (userprog : ll_toplevel_entities) : ll_toplevel_entities :=
      let predefined     := (defines_decl predefs) in
      let userprog'      := filter (negb ∘ predefined) userprog
        in List.app predefs userprog'.

  Definition link_all
    (linked_files  : list ll_toplevel_entities)
    (userprog : ll_toplevel_entities) : ll_toplevel_entities :=
    fold_left (fun prog linked => link linked prog) linked_files userprog.

  (** * Initialization

    The initialization phase allocates and initializes globals, and allocates
   function pointers. This initialization phase is internalized in [Vellvm], it
   is an [itree] as any other.  *)

  (** Allocate space for a global *)
  Definition allocate_global (g:global dtyp) : MCFGtop unit :=
    if (g_alias g) then
      (* Aliases don't allocate new storage space. *)
      ret tt 
    else
      v <- alloca (g_typ g) 1%N None;;
      gwrite (g_ident g) v.

  Definition allocate_globals (gs:list (global dtyp)) : MCFGtop unit :=
    loop_monad allocate_global gs.

  Definition i8 : dtyp := DTYPE_I 8%positive.

  Definition i8_array_of_string (s : string) : dvalue :=
    let len := N.of_nat (String.length s) + 1%N in
      DVALUE_Array false
          (DTYPE_Array false len i8)
          (List.app
            (map (DVALUE_Base ∘ (DVALUE_I 8%positive) ∘
            @Integers.repr 8%positive ∘
            Z.of_N ∘
            Stdlib.Strings.Ascii.N_of_ascii ) (Stdlib.Strings.String.list_ascii_of_string s))
            [DVALUE_Base (DVALUE_I 8%positive (@Integers.zero 8%positive))]).

  Definition allocate_arg (arg : string) : MCFGtop dvalue :=
    let len := N.of_nat (String.length arg) + 1%N in
    (* tl;dr allocating the string in a C-like manner; + 1 for null terminator *)
    v <- alloca i8 len None;;
    store (DTYPE_Array false len i8) v (i8_array_of_string arg);;
    ret v.

  Definition allocate_args (args : list string) : MCFGtop dvalue :=
    let len := N.of_nat (Datatypes.length args) in
      v <- alloca DTYPE_Pointer len None;;
      arg_addrs <- map_monad allocate_arg args;;
      store (DTYPE_Array false len DTYPE_Pointer) v
            (DVALUE_Array false (DTYPE_Array false len DTYPE_Pointer) arg_addrs);;
      ret v.

  Definition build_main_args (args : list string) : MCFGtop (list dvalue) :=
    v <- allocate_args args;;
    let main_args :=
      [DVALUE_Base (DVALUE_I 32 ((@Integers.repr 32%positive ∘ Z.of_nat) (List.length args))); v]
    in
    ret main_args.

  (* Who is in charge of allocating the addresses for external functions declared in this mcfg?
     - For now we assume that there is only one mcfg, so we allocate addresses for all declared
       and defined functions.
     - If we ever do some kind of "linking" we may need to revisit this, but it presumably
       would be resolved by an operation of type [link : mcfg -> mcfg -> mcfg] that
       combines two mcfgs coherently
   *)

  Definition allocate_declaration (d:declaration dtyp) : MCFGtop unit :=
    match lookup_intrinsic_declaration (dc_name d) with
    | Some _ => Ret tt (* Don't allocate pointers for LLVM intrinsics declarations *)
    | None =>
        'v <- alloca DTYPE_Pointer 1%N None;;
        gwrite (dc_name d) v
    end.

  Definition allocate_declarations (ds:list (declaration dtyp)) : MCFGtop unit :=
    loop_monad allocate_declaration ds.

  (* We have to initialize the global definitions after allocating them because they
     might be mutually recursive.  It is possible to declare cyclic data structures
     statically at the global level in LLVM.
   *)
  Definition initialize_global (g:global dtyp) : MCFGtop unit :=
    if (g_alias g) then
      (* aliases simply populate the global ID map *)
      match (g_exp g) with
      | Some (EXP_Ident (ID_Global g_source)) =>
          p <- gread g_source;;
          gwrite (g_ident g) p
      | Some _ => raiseUB ("alias " ++ (show_raw_id (g_ident g)) ++ " has bad initializer expression")
      | None => raiseUB ("alias " ++ (show_raw_id (g_ident g)) ++ " not initialized")
      end
    else
      (* non-aliases are intialized by storing values *)
    let dt := (g_typ g) in
    a <- gread (g_ident g);;
    uv <- match (g_exp g) with
         | None => ret (DVALUE_Base (DVALUE_Poison dt))
         | Some e => denote_exp (Some dt) e
         end ;;
    store dt a uv.

  Definition initialize_globals (gs:list (global dtyp)): MCFGtop unit :=
    loop_monad initialize_global gs.

  Definition build_global_environment (CFGtop : CFG.mcfg dtyp) : MCFGtop unit :=
    allocate_declarations ((m_declarations CFGtop) ++ (List.map (df_prototype) (m_definitions CFGtop)));;
    allocate_globals (m_globals CFGtop) ;;
    initialize_globals (m_globals CFGtop).

  (**
   Denotes a function and returns its pointer.
   *)

  Definition address_one_function (df : definition dtyp (CFG.cfg dtyp))
    : MCFGtop (Z * function_denotation) :=
    let fid := (dc_name (df_prototype df)) in
    fv <- gread fid ;;
    match fv with
    | DVALUE_Base (DVALUE_Pointer p) =>
        ret (ptr_to_int p, denote_function df)
    | _ => raise "address_one_function: invalid address, should not happen."
    end.

  (**
   Denotes a library function
   *)
  Definition address_one_library_function (libfun : function_id * function_denotation)
    : MCFGtop (Z * function_denotation) :=
    let (fid, den) := libfun in
    fv <- gread fid ;;
    match fv with
    | DVALUE_Base (DVALUE_Pointer p) =>
        ret (ptr_to_int p, den)
    | _ => raise "address_one_library_function: invalid address, should not happen."
    end.

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
     Full denotation of a Vellvm program as an interaction tree:
     * initialize the global environment;
     * pointwise denote each function (and libraries)
     * retrieve the address of the entry point function;
     * tie the mutually recursive knot and run it starting from the
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
             (entry : function_id)
             (args : list dvalue)
             (mcfg : CFG.mcfg dtyp) : MCFGtop dvalue :=
    build_global_environment mcfg ;;
    'defns <- map_monad address_one_function (m_definitions mcfg) ;;
    'libraries <- map_monad address_one_library_function (library_functions (m_declarations mcfg));;
    'addr <- gread entry ;;
    'rv <- denote_mcfg (IP.of_list (defns ++ libraries)) ret_typ addr args;;
    match rv with
    | inl exc => raiseLLVM exc
    | inr rv => ret rv
    end.

  (**
     Now that we know how to denote a whole llvm program, we can _interpret_
     the resulting [itree].

     arg_gen is an itree so that main args can be allocated prior to
     interpretation (on the correct interpretation level).
   *)
  Definition interpreter_gen
    (ret_typ : dtyp)
    (entry : function_id)
    (arg_gen : MCFGtop (list dvalue))
    (prog: ll_toplevel_entities) : MCFGbot (Res dvalue) :=
    let t :=
      args <- arg_gen;;
      denote_vellvm ret_typ entry args
        (convert_types (mcfg_of_tle (link PREDEFINED_FUNCTIONS prog)))
    in interp_mcfg t Maps.empty (Build_stack_frame Maps.empty None None,[]) initial_state.

  (**
     Finally, the reference interpreter assumes no user-defined intrinsics and starts
     from "main" using bogus initial inputs.
   *)
  Definition interpreter_param
             (args : list string)
             (prog : ll_toplevel_entities)
              : MCFGbot _ 
    := interpreter_gen (DTYPE_I 32%positive) (Name "main") (build_main_args args) prog.

End withParams.

From Vellvm Require Import ParamsV IPtrInfinite.
Definition interpreter := interpreter_param (Pa := @ParamsV IPZ IPZTheory).
Definition dvalue_eqb := @DynamicValues.dvalue_eqb (@ParamsV IPZ IPZTheory).
