(** * Plugging the pieces together: executable and propositional semantics for Vellvm *)

(* begin hide *)
From Stdlib Require Import Program.
From ITree Require Import
  ITree
  Events.State.

From Vellvm Require Import Handlers.
From Vellvm Require Import
  Utilities
  Syntax
  Semantics.Params
  Semantics.Params.Memory
  Semantics.DynamicValues
  Semantics.LLVMEvents
  Semantics.Denotation
  Semantics.Operations
  Semantics.IntrinsicsDefinitions
  Semantics.InterpretationStack
  Semantics.VellvmIntegers
  QC.ShowAST.
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

  (* IO & built-in functions -------------------------------------------------------------------- *)
  (* SAZ: Is there a better location to put this information? It depends on many of the
     modules that are in scope at this point.
  *)
  (** * puts
        [int  puts(const char *s);]
        The function puts() writes the string s, and a terminating newline character, to the stream stdout.
        The functions fputs() and puts() return a nonnegative integer on success and EOF on error.

      * putchar
      [int putchar (int c);]
      The function putchar() writes the character c to the stream stdout.
      The functions fputc() and putc() return the value written on success and EOF on error.

      SAZ/RAB: it isn't clear what kinds of errors count as "errors" for puts and
      putchar. Our implementation will never explicitly return EOF (since that
      seems to be a stdout stream error.  It will only ever raise "semantic"
      errors.
   *)

(** Semantic function that triggers a single IO_stdout event to print
    the passed-in character.
    the character comes in as an i32, so the function truncates to an i8
    to match types with IO_stdout. *)
  
  Definition putchar_denotation : function_denotation.
    refine
      (let putchar_body (u_char:dvalue) : itree L0' dvalue :=
         match u_char with
         | DVALUE_I sz x32 =>
             if Pos.eq_dec 32 sz
             then
               match get_conv_case (Trunc false false) (DTYPE_I 32) u_char (DTYPE_I 8) with
               | Conv_Pure (DVALUE_I sz x8) =>
                   if Pos.eq_dec 8 sz
                   then _
                   else raise "conversion from i32 to i8 in putchar gave unexpected conversion type"
               | _ => raise "conversion from i32 to i8 in putchar gave unexpected conversion type"
               end ;;
               ret u_char
             else
               raiseUB ("putc got non-i32 integer argument")
         | bad => raiseUB ("putc got non-i32 argument " ++ show_dvalue bad)
         end
       in

       fun (args : list dvalue) =>
         match args with
         | char::[] => putchar_body char
         | _ => raise "putc called with zero or more than one arguments"
         end).
    subst.
    exact (io_stdout [x8]).
  Defined.

  (** A semantic function to read an i8 value at [strptr + index] from the memory.
      Propagates all memory failures and raises a Vellvm "Failure" if the
      value read does not concretize to a DVALUE_I8.
   *)
  Definition i8_str_index (strptr : addr) (index : Z) : itree L0' (@Integers.bit_int 8) :=
    iptr <- EOB_to_itree (from_Z index) ;;
    addr <- EOB_to_itree (handle_gep_addr (DTYPE_I 8) strptr [DVALUE_IPTR iptr]) ;;
    d_byte <- load (DTYPE_I 8) (DVALUE_Addr addr) ;;
    match d_byte with
    | DVALUE_I 8 b => ret b
    | bad => raise ("i8_str_index failed with non-DVALUE_I8 " ++ show_dvalue bad)
    end.

  (** Semantic function that treats [u_strptr] as a C-style string pointer:
      - reads i8 values from memory until it encounters a null-terminator (i8 0)
      - triggers an IO_stdout event with the bytes plus a newline
   *)
  Definition puts_denotation : function_denotation :=
    let puts_body (u_strptr : dvalue) : itree L0' dvalue :=
      match u_strptr with
      | DVALUE_Addr strptr =>
          char <- i8_str_index strptr 0%Z ;;
          bytes <-
            ITree.iter
              (fun '(c, bytes, offset) =>
                 if @Integers.eq 8 c (@Integers.zero 8) then
                   (* null terminated string so end the iteration, add the newline *)
                   ret (inr ((@Integers.repr 8 10) :: bytes))
                 else
                   next_char <- i8_str_index strptr offset ;;
                   ret (inl (next_char, c::bytes, (offset + 1)%Z))
              )
              (char, [], 1%Z) ;;
          v <- io_stdout (DList.rev_tail_rec bytes) ;;
          ret (DVALUE_I 8 (@Integers.zero 8))
      | bad => raiseUB ("puts got non-address argument " ++ show_dvalue bad)
      end
    in

    fun (args : list dvalue) =>
      match args with
      | strptr::[] => puts_body strptr
      | _ => raise "puts called with zero or more than one arguments"
      end.

  (* *********DO NOT USE DIRECTLY*********
  Program should ONLY use `built_in_functions`, defined below, which filters
  out unused functions from _BUILTINS.

  Lists all functions built-in by default. As vellvm gains more, they should
  go into this list.
*)

  Definition _BUILTINS : list (function_id * function_denotation) :=
    [(Name "puts", puts_denotation);
     (Name "putchar", putchar_denotation)].

  (** * [built_in_functions]

      This is a list of standard library functions whose semantics can/must be
      expressed directly in the semantic model.  They are not LLVM intrinsics, so
      they _do_ get addresses.

      These definitions assume that the built-in functions are declared in the .ll file
      but that their semantics as itrees are defined here.  Note that the type at which
      the function is declared in the ll file should match that used for the semantics,
      but there is no check about that.

      For example, to use the C [<stdio.h> puts] function, one would include the
      following declaration as part of the ll file:
      [declare i32 puts(i8* %str)]
      See /tests/io for some examples.
   *)

  Definition built_in_functions (decls : list (declaration dtyp)) :
    list (function_id * function_denotation) :=
    filter (fun '(n, d) =>
              existsb (fun s => Rocqlib.proj_sumbool (Syntax.AstLib.RawIDOrd.eq_dec s n))
                (List.map (@dc_name dtyp) decls))
      (* if we have many builtins, pull out this List.map to a let-bind for explicit optimization *)
      _BUILTINS.


  (* SAZ: commenting this out for now, since it's trickier than we wanted *)
  (* Command-line arguments----------------------------------------------------------------------- *)

  (* To support command-line arguments we convert a list of Coq strings into a preamble of
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
   only functions we hard-code into the environment for their usefulness--
   most notably `printf`. Linking occurs at the `toplevel_definition` level. *)

  Definition ll_toplevel_entity := (toplevel_entity typ (block typ * list (block typ))).

  Definition ll_toplevel_entities := toplevel_entities typ (block typ * list (block typ)).

  (* TODO: link against printf's llvm ir code directly. If impossible, revive
     the printf_definition hack
   *)
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
  Definition allocate_global (g:global dtyp) : itree L0 unit :=
    if (g_alias g) then
      (* Aliases don't allocate new storage space. *)
      ret tt 
    else
      v <- alloca (g_typ g) 1%N None;;
      gwrite (g_ident g) v.

  Definition allocate_globals (gs:list (global dtyp)) : itree L0 unit :=
    map_monad_ allocate_global gs.

  Definition i8 : dtyp := DTYPE_I 8%positive.


  Definition i8_array_of_string (s : string) : dvalue :=
    let len := N.of_nat (String.length s) + 1%N in
      DVALUE_Array
          (DTYPE_Array len i8)
          (List.app
            (map ((DVALUE_I 8%positive) ∘
            @Integers.repr 8%positive ∘
            Z.of_N ∘
            Stdlib.Strings.Ascii.N_of_ascii ) (Stdlib.Strings.String.list_ascii_of_string s))
            [DVALUE_I 8%positive (@Integers.zero 8%positive)]).

  Definition allocate_arg (arg : string) : itree L0 dvalue :=
    let len := N.of_nat (String.length arg) + 1%N in
    (* tl;dr allocating the string in a C-like manner; + 1 for null terminator *)
    v <- alloca i8 len None;;
    store (DTYPE_Array len i8) v (i8_array_of_string arg);;
    ret v.

  Definition allocate_args (args : list string) : itree L0 dvalue :=
    let len := N.of_nat (Datatypes.length args) in
      v <- alloca DTYPE_Pointer len None;;
      arg_addrs <- map_monad allocate_arg args;;
      store (DTYPE_Array len DTYPE_Pointer) v
            (DVALUE_Array (DTYPE_Array len DTYPE_Pointer) arg_addrs);;
      ret v.

  Definition build_main_args (args : list string) : itree L0 (list dvalue) :=
    v <- allocate_args args;;
    let main_args :=
      [DVALUE_I 32 ((@Integers.repr 32%positive ∘ Z.of_nat) (List.length args)); v]
    in
    ret main_args.

  (* Who is in charge of allocating the addresses for external functions declared in this mcfg?
     - For now we assume that there is only one mcfg, so we allocate addresses for all declared
       and defined functions.
     - If we ever do some kind of "linking" we may need to revisit this, but it presumably
       would be resolved by an operation of type [link : mcfg -> mcfg -> mcfg] that
       combines two mcfgs coherently
   *)

  Definition allocate_declaration (d:declaration dtyp) : itree L0 unit :=
    match lookup_intrinsic_declaration (dc_name d) with
    | Some _ => Ret tt (* Don't allocate pointers for LLVM intrinsics declarations *)
    | None =>
        'v <- alloca DTYPE_Pointer 1%N None;;
        gwrite (dc_name d) v
    end.

  Definition allocate_declarations (ds:list (declaration dtyp)) : itree L0 unit :=
    map_monad_ allocate_declaration ds.

  (* We have to initialize the global definitions after allocating them because they
     might be mutually recursive.  It is possible to declare cyclic data structures
     statically at the global level in LLVM.
   *)
  Definition initialize_global (g:global dtyp) : itree L0 unit :=
    if (g_alias g) then
      (* aliases simply populate the global ID map *)
      match (g_exp g) with
      | Some (EXP_Ident (ID_Global g_source)) =>
          addr <- gread g_source;;
          gwrite (g_ident g) addr
      | Some _ => raiseUB ("alias " ++ (show_raw_id (g_ident g)) ++ " has bad initializer expression")
      | None => raiseUB ("alias " ++ (show_raw_id (g_ident g)) ++ " not initialized")
      end
    else
      (* non-aliases are intialized by storing values *)
    let dt := (g_typ g) in
    a <- gread (g_ident g);;
    uv <- match (g_exp g) with
         | None => ret (DVALUE_Poison dt)
         | Some e => denote_exp (Some dt) e
         end ;;
    store dt a uv.

  Definition initialize_globals (gs:list (global dtyp)): itree L0 unit :=
    map_monad_ initialize_global gs.

  Definition build_global_environment (CFG : CFG.mcfg dtyp) : itree L0 unit :=
    allocate_declarations ((m_declarations CFG) ++ (List.map (df_prototype) (m_definitions CFG)));;
    allocate_globals (m_globals CFG) ;;
    initialize_globals (m_globals CFG).

  (** Local environment implementation
    The map-based handlers are defined parameterized over a domain of key and value.
    We now pick concrete such domain.
    Note that while local environments may store under-defined values,
    global environments are statically guaranteed to store [dvalue]s.
   *)
  Definition function_env := FMapAList.alist dvalue function_denotation.

  (**
   Denotes a function and returns its pointer.
   *)

  Definition address_one_function (df : definition dtyp (CFG.cfg dtyp))
    : itree L0 (Z * function_denotation) :=
    let fid := (dc_name (df_prototype df)) in
    fv <- gread fid ;;
    match fv with
    | DVALUE_Addr addr =>
        ret (ptr_to_int addr, denote_function df)
    | _ => raise "address_one_function: invalid address, should not happen."
    end.

  (**
   Denotes a builtin function
   *)
  Definition address_one_builtin_function (builtin : function_id * function_denotation)
    : itree L0 (Z * function_denotation) :=
    let (fid, den) := builtin in
    fv <- gread fid ;;
    match fv with
    | DVALUE_Addr addr =>
        ret (ptr_to_int addr, den)
    | _ => raise "address_one_builtin_function: invalid address, should not happen."
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

  (* TODO MOVE? *)
  Notation res_L1 := (global_env * dvalue)%type.
  Notation res_L2 := (stack_frame * stack * res_L1)%type.
  Notation res_L3 := (state * res_L2)%type.
  Notation res_L4 := (state * (stack_frame * stack * (global_env * dvalue)))%type.
  Notation res_L5 := (state * (stack_frame * stack * (global_env * dvalue)))%type.
  Notation res_L6 := (state * (stack_frame * stack * (global_env * dvalue)))%type.

  (**
     Full denotation of a Vellvm program as an interaction tree:
     * initialize the global environment;
     * pointwise denote each function (and builtin)
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
             (mcfg : CFG.mcfg dtyp) : itree L0 dvalue :=
    build_global_environment mcfg ;;
    'defns <- map_monad address_one_function (m_definitions mcfg) ;;
    'builtins <- map_monad address_one_builtin_function (built_in_functions (m_declarations mcfg));;
    'addr <- gread entry ;;
    'rv <- denote_mcfg (IP.of_list (defns ++ builtins)) ret_typ addr args;;
    match rv with
    | inl exc => raiseLLVM exc
    | inr rv => ret rv
    end.

  (* default_main_args and denote_vellvm_main may not be needed anymore, but I'm keeping them
     For backwards compatibility.
   *)
  (* (for now) assume that [main (i64 argc, i8** argv)]
    pass in 0 and null as the arguments to main
    Note: this isn't compliant with standard C semantics, but integrating the actual
    inputs from the command line is nontrivial since we have to martial C-level strings
    into the Vellvm memory.
   *)
  Definition default_main_args : list string := [].

  (**
     Now that we know how to denote a whole llvm program, we can _interpret_
     the resulting [itree].

     arg_gen is an itree so that main args can be allocated prior to
     interpretation (on the correct interpretation level).
   *)
  Definition interpreter_gen
    (ret_typ : dtyp)
    (entry : function_id)
    (arg_gen : itree L0 (list dvalue))
    (prog: ll_toplevel_entities)
    : itree _ _ :=
    let t :=
      args <- arg_gen;;
      denote_vellvm ret_typ entry args
        (convert_types (mcfg_of_tle (link PREDEFINED_FUNCTIONS prog)))
    in interp_mcfg t [] (Build_stack_frame [] None None None,[]) initial_state.

  (**
     Finally, the reference interpreter assumes no user-defined intrinsics and starts
     from "main" using bogus initial inputs.
   *)
  Definition interpreter_param
             (args : list string)
             (prog : ll_toplevel_entities)
              : itree _ _ 
    := interpreter_gen (DTYPE_I 32%positive) (Name "main") (build_main_args args) prog.

End withParams.

From Vellvm Require Import ParamsV IPtrInfinite.
Definition interpreter := interpreter_param (Pa := @ParamsV IPZ IPZTheory).
Definition dvalue_eqb := @DynamicValues.dvalue_eqb (@ParamsV IPZ IPZTheory).
