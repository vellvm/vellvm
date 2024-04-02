(** * Plugging the pieces together: executable and propositional semantics for Vellvm *)

(* begin hide *)
From Coq Require Import
     Ensembles List String ZArith
     Lists.ListSet
     Relations.

From ITree Require Import
     ITree
     Events.State.

From ExtLib Require Import
     Structures.Functor
     Structures.Monads
     Data.Map.FMapAList.

From Vellvm Require Import
  Utilities
  Utils.IntMaps
  Syntax
  Syntax.LLVMAst
  Syntax.AstLib
  Semantics.LLVMEvents
  Semantics.Denotation
  Semantics.IntrinsicsDefinitions
  Semantics.InterpretationStack
  Semantics.VellvmIntegers
  Semantics.StoreId.

Import MonadNotation.
Import ListNotations.
Import Monads.
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
Module Type LLVMTopLevel (IS : InterpreterStack).
  Export IS.
  Export IS.LP.Events.
  Export IS.LLVM.D.
  Export IS.LLVM.MEM.
  Export IS.LLVM.MEM.MEM_MODEL.
  Import IS.LLVM.MEM.CP.CONC.
  Import MMEP.MMSP.
  Import MMEP.
  Import MEM_EXEC_INTERP.
  Import MEM_SPEC_INTERP.
  Export GEP.
  Export IS.LLVM.Local.
  Export IS.LLVM.Global.
  Export IS.LLVM.Stack.
  Export IS.LP.ADDR.

  Import SemNotations.

  (* IO & built-in functions -------------------------------------------------------------------- *)
  (* SAZ: Is there a better location to put this information? It depends on many of the
     modules that are in scope at this point.
  *)
  (** * puts 
      [int  puts(const char *s);]
      The function puts() writes the string s, and a terminating newline character, to the stream stdout.
      The functions fputs() and puts() return a nonnegative integer on success and EOF on error.

      SAZ: it isn't clear what kinds of errors count as "errors" for puts. Our implementation 
      will never explicitly return EOF (since that seems to be a stdout stream error.  It will
      only ever raise "semantic" errors.
   *)

  (** A semantic function to read an i8 value at [strptr + index] from the memory. 
      Propagates all memory failures and raises a Vellvm "Failure" if the 
      value read does not concretize to a DVALUE_I8.
   *)
  Definition i8_str_index (strptr : addr) (index : Z) : itree L0' Int8.int :=
    iptr <- (@lift_OOM (itree L0') _ _ _ (LP.IP.from_Z index)) ;;
    addr <-
      match handle_gep_addr (DTYPE_I 8) strptr [DVALUE_IPTR iptr] with
            | inl msg => raise msg 
            | inr c => @lift_OOM (itree L0') _ _ _ c
            end ;;
    u_byte <- trigger (Load (DTYPE_I 8) (DVALUE_Addr addr)) ;;
    d_byte <- concretize_or_pick u_byte;;
    match d_byte with
    | DVALUE_I8 b => ret b
    | _ => raise "i8_str_index failed with non-DVALUE_I8"
    end.

  
  (** Semantic function that treats [u_strptr] as a C-style string pointer:
      - reads i8 values from memory until it encounters a null-terminator (i8 0)
      - triggers an IO_stdout event with the bytes plus a newline
   *)
  Definition puts_denotation : function_denotation :=
    let puts_body (u_strptr:uvalue) : itree L0' uvalue :=
      dv <- concretize_or_pick u_strptr;;
      match dv with
      | DVALUE_Addr strptr =>
          char <- i8_str_index strptr 0%Z ;;
          bytes <- 
            ITree.iter
              (fun '(c, bytes, offset) =>
                 if Int8.eq c (Int8.zero) then
                   (* null terminated string so end the iteration, add the newline *)
                   ret (inr ((Int8.repr 10) :: bytes))
                 else 
                   next_char <- i8_str_index strptr offset ;;
                   ret (inl (next_char, c::bytes, (offset + 1)%Z))
              )
              (char, [], 1%Z) ;;
          v <- trigger (IO_stdout (DList.rev_tail_rec bytes)) ;;
          ret (UVALUE_I8 (Int8.zero))
      | _ => raiseUB "puts got non-address argument"
      end
    in
    
    fun (args : list uvalue) =>
      match args with
      | strptr::[] => puts_body strptr
      | _ => raise "puts called with zero or more than one arguments"
      end.

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

  Definition built_in_functions (decls : list (declaration dtyp)) : list (function_id * function_denotation) :=
    match List.find (fun s => (Coqlib.proj_sumbool (Syntax.AstLib.RawIDOrd.eq_dec s (Name "puts"))))
            (List.map (@dc_name dtyp) decls) with
    | Some _ => [(Name "puts", puts_denotation)]
    | None => []
    end.

  
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
(*
  Definition zi8_to_exp (z_i8 : Z) := @LLVMAst.EXP_Integer dtyp z_i8.
  Definition zi8s_to_EXP_Cstring (zi8s:list Z) :=
    EXP_Cstring (List.map (fun z => (DTYPE_I 8, zi8_to_exp z)) zi8s).

  (* These assume that [arg] is a list _including_ the 0 null terminator. *) 
  Definition cstring_typ (arg:list Z) := DTYPE_Array (N.of_nat(List.length arg)) (DTYPE_I 8).               
  Definition arg_global gid (arg:list Z) :=
      mk_global gid (cstring_typ arg) true (Some (zi8s_to_EXP_Cstring arg)) false [].

  Definition mapi {A B} (f : N -> A -> B) (l:list A ) : list B :=
    (fix h (n:N) l :=
      match l with
      | [] => []
      | x::xs => (f n x)::h (1+n)%N xs
      end) 0%N l.

  (* SAZ: TODO: do we use "Raw" anywhere else in the semantics?  I chose to use them here
     because the global declarations associated with these identifiers aren't really present
     statically; they are allocated by the "runtime".  We need to be able to generate 
     N+1 fresh global identifiers to hold the storage space for command-line arugments. 
   *)
  Definition arg_raw_id (n:N) := (Raw (Z.of_N n)).
  Definition arg_gid (n:N) := ID_Global (arg_raw_id n).
  Definition arg_tle (n:N) (arg:list Z) : toplevel_entity dtyp (CFG.cfg dtyp) :=
    TLE_Global (arg_global (arg_raw_id n) arg).

  Definition arg_gep_ref (n:N) (arg:list Z) : (dtyp * exp dtyp) :=
    (DTYPE_Pointer,
      OP_GetElementPtr (cstring_typ arg) (DTYPE_Pointer, EXP_Ident (arg_gid n))
        [(DTYPE_I 64, EXP_Integer 0%Z); (DTYPE_I 64, EXP_Integer 0%Z)]).

  Definition argv_type (argc:N) := DTYPE_Array argc DTYPE_Pointer.
  
  Definition argv_array_global (args : list (list Z)) :=
    let argc : N := N.of_nat (List.length args) in
    mk_global
      (arg_raw_id (1+argc))
      (argv_type argc)
      false
      (Some (EXP_Array (mapi arg_gep_ref args)))
      false
      [].
      
    
  Definition argc_array_tle (args : list (list Z)) : toplevel_entity dtyp (CFG.cfg dtyp) :=
    TLE_Global (argv_array_global args).

  (* TODO: 
      The staging of these arguments is a bit tricky.  We want to inject these new TLEs into
      the semantics, but we also need to "call" the main function with some arguments that
      depend on them: i.e. 
          argc = EXP_Integer N and 
          argv = [bitcast ([3 x i8*]* @_RAW_argv to i8** )])

     It is probably cleaner to maintain the syntactic/semantic phase distinction and 
     just "close" the program at the syntax level and then treat the argv strings as
     part of the global environment where we want to interpret main_args like:

     main args (initialize_globals : itree) : itree :=
         initialize_globals ;;
         initialize_args args ;;
         argv <- trigger (GlobalRead (g_ident (arg_raw_id (1+argc)))) ;;
         trigger (Call "main" [UVALUE_I32 N; argv])
   *)
   *)  
  
  (* TOPLEVEL Semantics  ------------------------------------------------------------------------- *)
  
  (** * Initialization

    The initialization phase allocates and initializes globals, and allocates
   function pointers. This initialization phase is internalizedin [Vellvm], it
   is an [itree] as any other.  *)

  (** Allocate space for a global *)
  Definition allocate_global (g:global dtyp) : itree L0 unit :=
    'v <- trigger (Alloca (g_typ g) 1%N None);;
    trigger (GlobalWrite (g_ident g) v).

  Definition allocate_globals (gs:list (global dtyp)) : itree L0 unit :=
    map_monad_ allocate_global gs.

  (* Who is in charge of allocating the addresses for external functions declared in this mcfg? 
     - For now we assume that there is only one mcfg, so we allocate addresses for all declared 
       and defined functions.
     - If we ever do some kind of "linking" we may need to revisit this, but it presumably
       would be resolved by an operation of type [link : mcfg -> mcfg -> mcfg] that 
       combines two mcfgs coherently
   *)

  (* Returns `true` only if both function are named and have the same name.  *)
  (* TODO: move to AstLib? *)
  Definition function_name_eq (a b:function_id) : bool :=
    match a, b with
    | Name aname, Name bname => eqb aname bname
    | _, _ => false
    end.

  Definition allocate_declaration (d:declaration dtyp) : itree L0 unit :=
    match List.find (fun x => function_name_eq (dc_name d) (dc_name x)) defined_intrinsics_decls with
    | Some _ => Ret tt (* Don't allocate pointers for LLVM intrinsics declarations *)
    | None =>
        'v <- trigger (Alloca DTYPE_Pointer 1%N None);;
        trigger (GlobalWrite (dc_name d) v)
    end.

  Definition allocate_declarations (ds:list (declaration dtyp)) : itree L0 unit :=
    map_monad_ allocate_declaration ds.

  (* We have to initialize the global definitions after allocating them because they
     might be mutually recursive.  It is possible to declare cyclic data structures 
     statically at the global level in LLVM.
   *)
  Definition initialize_global (g:global dtyp) : itree exp_E unit :=
    let dt := (g_typ g) in
    a <- trigger (GlobalRead (g_ident g));;
    uv <- match (g_exp g) with
         | None => ret (UVALUE_Undef dt)
         | Some e =>  ⟦ e at dt ⟧e
         end ;;
    trigger (Store dt a uv).

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
  Definition function_env := FMapAList.alist dvalue function_denotation.

  (**
   Denotes a function and returns its pointer.
   *)

  Definition address_one_function (df : definition dtyp (CFG.cfg dtyp))
    : itree L0 (Z * function_denotation) :=
    let fid := (dc_name (df_prototype df)) in
    fv <- trigger (GlobalRead fid) ;;
    match fv with
    | DVALUE_Addr addr =>        
        ret (LP.PTOI.ptr_to_int addr, ⟦ df ⟧f)
    | _ => raise "address_one_function: invalid address, should not happen."
    end.

  (**
   Denotes a builtin function 
   *)
  Definition address_one_builtin_function (builtin : function_id * function_denotation) 
    : itree L0 (Z * function_denotation) :=
    let (fid, den) := builtin in 
    fv <- trigger (GlobalRead fid) ;;
    match fv with
    | DVALUE_Addr addr =>        
        ret (LP.PTOI.ptr_to_int addr, den)
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

  Notation res_L1 := (global_env * dvalue)%type.
  Notation res_L2 := (local_env * lstack * res_L1)%type.
  Notation res_L3 := (MemState * (store_id * res_L2))%type.
  Notation res_L4 := (MemState * (store_id * (local_env * lstack * (global_env * dvalue))))%type.
  Notation res_L5 := (MemState * (store_id * (local_env * lstack * (global_env * dvalue))))%type.
  Notation res_L6 := (MemState * (store_id * (local_env * lstack * (global_env * dvalue))))%type.

  (**
     Full denotation of a Vellvm program as an interaction tree:
     * initialize the global environment;
     * pointwise denote each function (and builtin)
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
             (mcfg : CFG.mcfg dtyp) : itree L0 dvalue :=
    build_global_environment mcfg ;;
    'defns <- map_monad address_one_function (m_definitions mcfg) ;;
    'builtins <- map_monad address_one_builtin_function (built_in_functions (m_declarations mcfg));;
    'addr <- trigger (GlobalRead (Name entry)) ;;
    'rv <- denote_mcfg (IP.of_list (defns ++ builtins)) ret_typ (dvalue_to_uvalue addr) args ;;
    dv_pred <- trigger (pickNonPoison rv);;
    ret (proj1_sig dv_pred).

  (* main_args and denote_vellvm_main may not be needed anymore, but I'm keeping them
     For backwards compatibility.
   *)
  (* (for now) assume that [main (i64 argc, i8** argv)]
    pass in 0 and null as the arguments to main
    Note: this isn't compliant with standard C semantics, but integrating the actual
    inputs from the command line is nontrivial since we have martial C-level strings
    into the Vellvm memory.  
   *)
  Definition main_args := [DV.UVALUE_I32 (Int32.zero);
                           DV.UVALUE_Addr null
    ].

  Definition denote_vellvm_main (mcfg : CFG.mcfg dtyp) : itree L0 dvalue :=
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
    interp_mcfg4_exec t [] ([],[]) 0 initial_memory_state.

  (**
     Finally, the reference interpreter assumes no user-defined intrinsics and starts
     from "main" using bogus initial inputs.
   *)
  Definition interpreter
             (prog : list (toplevel_entity typ (block typ * list (block typ)))) : itree L4 res_L4
    := interpreter_gen (DTYPE_I 32%N) "main" main_args prog.

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
    : PropT L4 res_L4 :=
    let t := denote_vellvm ret_typ entry args (convert_types (mcfg_of_tle prog)) in
    ℑs eq eq t [] ([],[]) 0 initial_memory_state.

  Definition model_gen_oom
             (ret_typ : dtyp)
             (entry : string)
             (args : list uvalue)
             (prog: list (toplevel_entity typ (block typ * list (block typ))))
    : PropT L4 res_L4 :=
    let t := denote_vellvm ret_typ entry args (convert_types (mcfg_of_tle prog)) in
    ℑs6 eq eq eq t [] ([],[]) 0 initial_memory_state.

  Definition model_gen_oom_L1
             (ret_typ : dtyp)
             (entry : string)
             (args : list uvalue)
             (prog: list (toplevel_entity typ (block typ * list (block typ))))
    : itree L1 res_L1 :=
    let t := denote_vellvm ret_typ entry args (convert_types (mcfg_of_tle prog)) in
    ℑs1 t [].

  Definition model_gen_oom_L2
             (ret_typ : dtyp)
             (entry : string)
             (args : list uvalue)
             (prog: list (toplevel_entity typ (block typ * list (block typ))))
    : itree L2 res_L2 :=
    let t := denote_vellvm ret_typ entry args (convert_types (mcfg_of_tle prog)) in
    ℑs2 t [] ([], []).

  Definition model_gen_oom_L3
    (RR : relation res_L2)
    (ret_typ : dtyp)
    (entry : string)
    (args : list uvalue)
    (prog: list (toplevel_entity typ (block typ * list (block typ))))
    : PropT L3 res_L3 :=
    let t := denote_vellvm ret_typ entry args (convert_types (mcfg_of_tle prog)) in
    ℑs3 RR t [] ([], []) 0 initial_memory_state.

  Definition model_gen_oom_L4
    RR_mem
    RR_pick
    (ret_typ : dtyp)
    (entry : string)
    (args : list uvalue)
    (prog: list (toplevel_entity typ (block typ * list (block typ))))
    : PropT L4 res_L4 :=
    let t := denote_vellvm ret_typ entry args (convert_types (mcfg_of_tle prog)) in
    ℑs4 RR_mem RR_pick t [] ([], []) 0 initial_memory_state.

  Definition model_gen_oom_L5
    RR_mem
    RR_pick
    (ret_typ : dtyp)
    (entry : string)
    (args : list uvalue)
    (prog: list (toplevel_entity typ (block typ * list (block typ))))
    : PropT L5 res_L5 :=
    let t := denote_vellvm ret_typ entry args (convert_types (mcfg_of_tle prog)) in
    ℑs5 RR_mem RR_pick t [] ([], []) 0 initial_memory_state.

  Definition model_gen_oom_L6
    RR_mem
    RR_pick
    RR_oom
    (ret_typ : dtyp)
    (entry : string)
    (args : list uvalue)
    (prog: list (toplevel_entity typ (block typ * list (block typ))))
    : PropT L6 res_L6 :=
    let t := denote_vellvm ret_typ entry args (convert_types (mcfg_of_tle prog)) in
    ℑs6 RR_mem RR_pick RR_oom t [] ([], []) 0 initial_memory_state.

  (**
     Finally, the official model assumes no user-defined intrinsics.
   *)
  Definition model := model_gen (DTYPE_I 32%N) "main" main_args.
  Definition model_oom := model_gen_oom (DTYPE_I 32%N) "main" main_args.
  Definition model_oom_L1 := model_gen_oom_L1 (DTYPE_I 32%N) "main" main_args.
  Definition model_oom_L2 := model_gen_oom_L2 (DTYPE_I 32%N) "main" main_args.
  Definition model_oom_L3 RR_mem := model_gen_oom_L3 RR_mem (DTYPE_I 32%N) "main" main_args.
  Definition model_oom_L4 RR_mem RR_pick := model_gen_oom_L4 RR_mem RR_pick (DTYPE_I 32%N) "main" main_args.
  Definition model_oom_L5 RR_mem RR_pick := model_gen_oom_L5 RR_mem RR_pick (DTYPE_I 32%N) "main" main_args.
  Definition model_oom_L6 RR_mem RR_pick RR_oom := model_gen_oom_L6 RR_mem RR_pick RR_oom (DTYPE_I 32%N) "main" main_args.
End LLVMTopLevel.

Module Make (IS : InterpreterStack) : LLVMTopLevel IS.
  Include LLVMTopLevel IS.
End Make.

Module TopLevelBigIntptr := Make InterpreterStackBigIntptr.
Module TopLevel64BitIntptr := Make InterpreterStack64BitIntptr.
