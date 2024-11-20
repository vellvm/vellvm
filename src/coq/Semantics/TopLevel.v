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
  Numeric.Coqlib
  Syntax.LLVMAst
  Syntax.AstLib
  Semantics.LLVMEvents
  Semantics.Denotation
  Semantics.IntrinsicsDefinitions
  Semantics.InterpretationStack
  Semantics.VellvmIntegers
  Semantics.StoreId
  Semantics.Printfdefn. 
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
      (let putchar_body (u_char:uvalue) : itree L0' uvalue :=
         dv <- concretize_or_pick u_char ;; 
         match dv with
         | @DVALUE_I sz x32 =>
             if Pos.eq_dec 32 sz
             then
               match get_conv_case Trunc (DTYPE_I 32) dv (DTYPE_I 8) with 
               | Conv_Pure (@DVALUE_I sz x8) =>
                   if Pos.eq_dec 8 sz
                   then _
                   else raise "conversion from i32 to i8 in putchar gave unexpected conversion type"
               | _ => raise "conversion from i32 to i8 in putchar gave unexpected conversion type"
               end ;;
               ret (dvalue_to_uvalue dv)
             else
               raiseUB ("putc got non-i32 integer argument")
         | bad => raiseUB ("putc got non-i32 argument " ++ show_dvalue bad)
         end
       in 

       fun (args : list uvalue) =>
         match args with
         | char::[] => putchar_body char
         | _ => raise "putc called with zero or more than one arguments"
         end).

    subst.
    exact (trigger (IO_stdout [x8])).
  Defined.
 

  (** A semantic function to read an i8 value at [strptr + index] from the memory. 
      Propagates all memory failures and raises a Vellvm "Failure" if the 
      value read does not concretize to a DVALUE_I8.
   *)
  Definition i8_str_index (strptr : addr) (index : Z) : itree L0' (@Integers.bit_int 8) :=
    iptr <- (@lift_OOM (itree L0') _ _ _ (LP.IP.from_Z index)) ;;
    addr <-
      match handle_gep_addr (DTYPE_I 8) strptr [DVALUE_IPTR iptr] with
            | inl msg => raise msg 
            | inr c => @lift_OOM (itree L0') _ _ _ c
            end ;;
    u_byte <- trigger (Load (DTYPE_I 8) (DVALUE_Addr addr)) ;;
    d_byte <- concretize_or_pick u_byte;;
    match d_byte with
    | @DVALUE_I 8 b => ret b
    | bad => raise ("i8_str_index failed with non-DVALUE_I8 " ++ show_dvalue bad)
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
                 if @Integers.eq 8 c (@Integers.zero 8) then
                   (* null terminated string so end the iteration, add the newline *)
                   ret (inr ((@Integers.repr 8 10) :: bytes))
                 else 
                   next_char <- i8_str_index strptr offset ;;
                   ret (inl (next_char, c::bytes, (offset + 1)%Z))
              )
              (char, [], 1%Z) ;;
          v <- trigger (IO_stdout (DList.rev_tail_rec bytes)) ;;
          ret (@UVALUE_I 8 (@Integers.zero 8))
      | bad => raiseUB ("puts got non-address argument " ++ show_dvalue bad)
      end
    in
    
    fun (args : list uvalue) =>
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

  Definition built_in_functions (decls : list (declaration dtyp)) : list (function_id * function_denotation) :=
  filter  (fun '(n, d) => existsb (fun s => Coqlib.proj_sumbool (Syntax.AstLib.RawIDOrd.eq_dec s n)) 
                                  (List.map (@dc_name dtyp) decls))
                                  (* if we have many builtins, 
                                     pull out this List.map to a let-bind
                                     for explicit optimization *)
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
  
  (** * Linking 

    We first need to link_predefs external definitions. Currently, these definitions are
   only functions we hard-code into the environment for their usefulness-- 
   most notably `printf`. Linking occurs at the `toplevel_definition` level. *)

  Definition ll_toplevel_entity := (toplevel_entity typ (block typ * list (block typ))).

  Definition ll_toplevel_entities := toplevel_entities typ 
                                                 (block typ * list (block typ)). 

  Definition PREDEFINED_FUNCTIONS : ll_toplevel_entities := List.concat [printf_definition]. 

  Example ensure_functions_defined : negb (Nat.eqb (List.length PREDEFINED_FUNCTIONS) O) . 
  Proof. reflexivity. Qed. 

   (* Get list of predef definitions 
      Check each userdefined definition 
      If it's in the list of predefs, remove it *)

  Definition defined_in_predefs (userdef : ll_toplevel_entity) : bool := 
    existsb (fun predef =>
    match predef, userdef with 
          TLE_Definition  {| df_prototype := {| dc_name := Name predef_n |}|}, 
          TLE_Definition  {| df_prototype := {| dc_name := Name userdef_n |}|}
             => String.eqb predef_n userdef_n
      | _, _    => false
    end) PREDEFINED_FUNCTIONS. 
  

  (* checks if `userdecl_n` is a name of a definition in `predefs`. *)
  Definition userdecl_defined_in_predefs (userdecl : declaration dtyp) : bool := 
    existsb (fun predef =>
    match predef, userdecl with 
          TLE_Definition  {| df_prototype := {| dc_name := Name predef_n |}|}, 
                          {| dc_name := Name userdecl_n |}          
             => String.eqb userdecl_n predef_n
      | _, _    => false
    end) PREDEFINED_FUNCTIONS. 
    
  Definition pairapp {A  B: Type} (p1 p2: list A * list B) :=
    match (p1, p2) with 
    ((l1, l2), (l1', l2')) => (List.app l1 l1', List.app l2 l2')
    end.

  Definition tripleapp {A B C: Type} (p1 p2: list A * list B * list C) :=
    match (p1, p2) with 
    ((l1, l2, l3), (l1', l2', l3')) => 
      (List.app l1 l1', List.app l2 l2', List.app l3 l3')
    end.

  Definition tle_defs_eq (d1 d2 : ll_toplevel_entity) :=
    match d1, d2 with 
    | TLE_Definition  {| df_prototype := {| dc_name := Name n1 |}|}, 
      TLE_Definition  {| df_prototype := {| dc_name := Name n2 |}|} => String.eqb n1 n2
    | _, _ => false 
    end. 
  
  Definition defs_eq (d1 d2 : definition dtyp (CFG.cfg dtyp)) :=
    match d1, d2 with 
    | {| df_prototype := {| dc_name := Name n1 |}|}, 
      {| df_prototype := {| dc_name := Name n2 |}|} => String.eqb n1 n2
    | _, _ => false 
    end. 

  Definition tle_decls_eq (d1 d2 : ll_toplevel_entity) 
  :=
    match d1, d2 with 
    | TLE_Declaration  {| dc_name := Name n1 |}, 
      TLE_Declaration  {| dc_name := Name n2 |} => String.eqb n1 n2 
    | _, _ => false 
    end. 

  Definition decls_eq (d1 d2 : declaration dtyp) 
  :=
    match d1, d2 with 
    | {| dc_name := Name n1 |}, 
      {| dc_name := Name n2 |} => String.eqb n1 n2 
    | _, _ => false 
    end. 

  Fixpoint uniq_b {A : Type} (eqfn : A -> A -> bool) (l : list A) : bool :=
    match l with 
      | [] => true 
      | (x::xs) => andb (negb (existsb (eqfn x) xs)) (uniq_b eqfn xs)
    end. 

  Fixpoint remove_duplicates_aux {A : Type} (p : A -> A -> bool) (new old : list A) : list A :=
    match old with
    | [] => new
    | x :: xs =>
      if existsb (fun n => p x n) new then
        remove_duplicates_aux p new xs
      else
        remove_duplicates_aux p (x :: new) xs
    end.

  Definition remove_duplicates {A : Type} (p : A -> A -> bool) (l : list A) : list A :=
    remove_duplicates_aux p [] l.


(* nodup does not work because it needs decidable propositional equality- 
   TOTAL definition of equality on the ll_toplevel_entity type. 
   There is one decision procedure that does this. *)

  (** Importantly, the linker _removes any declaration_ from the user's
     program that shares a name with a definition in `predefs` 
     before joining the two programs. 
     This is so that we can enforce our handcrafted declaration 
     is the one referenced by their program. 
  *)

  Definition tle_decl_def_match (defs : ll_toplevel_entities) (decl : ll_toplevel_entity) : bool :=
    existsb (fun def => 
      match decl, def with 
    | TLE_Declaration   {| dc_name := Name n1 ; dc_type := t1 |}, 
      TLE_Definition    {| df_prototype := {| dc_name := Name n2 ; dc_type := t2 |}|} =>
        andb (String.eqb n1 n2) true
        (* (t1 = t2 ) NEED DECIDABLE EQUALITY ON typ  *)
    | _, _ => false 
      end
    ) defs. 


  Definition decl_def_match (defs : list (definition dtyp (CFG.cfg dtyp))) (decl : declaration dtyp) : bool :=
    existsb (fun def => 
      match decl, def with 
    | {| dc_name := Name n1 ; dc_type := t1 |}, 
      {| df_prototype := {| dc_name := Name n2 ; dc_type := t2 |}|} =>
        andb (String.eqb n1 n2) (if dtyp_eq_dec t1 t2 then true else false) 
    | _, _ => false 
      end
    ) defs. 

  Definition link_tles 
  (* {M} `{Monad M} `{RAISE_ERROR M} *)
   (asts : list ll_toplevel_entities) : ll_toplevel_entities :=
    (* 
      If we want to do checks, we can put them back in. 
    
    Pulling out relevant information helps here. folds
    are preferred over filter to minimize passes over linked programs, which can
    hundreds of thousands to millions of elements long. 
    *)
    (* let decls_defs_rest_of_ast ast := 
      let '(decls, defs, rest) :=
        List.fold_left (fun ds tle => match (ds, tle) with 
        | ((decls, defs, rest), TLE_Declaration _ as decl) => (decl::decls, defs, rest)
        | ((decls, defs, rest), TLE_Definition  _ as def)  => (decls, def::defs, rest)
        | ((decls, defs, rest), other) => (decls, defs, other::rest)
        end) ast ([], [], []) in 
        (List.rev decls, List.rev defs, List.rev rest) in 
    (* one pass over the program *)
    let '(decls, defs, rest) := 
      List.fold_left (fun ds ast => tripleapp (decls_defs_rest_of_ast ast) ds) asts ([], [], []) 
       in 
    (* prune duplicate declarations *)
    let unique_decls := remove_duplicates tle_decls_eq decls in  *)
    List.concat asts. 

(* Do this in 
  linking goes before. happens in ocaml in driver.ml
 *)
  (* Important when linking with predefs: we want our definition of printf,
  putc, puts, etc-- not stdio's. so, we need to REMOVE all definitions from the
  user source that match definitions in our predefs/builtins. *)
  Definition link_predefs (userprog : ll_toplevel_entities) := 
      let filtered       := (filter (negb ∘ defined_in_predefs)) userprog
        in List.app PREDEFINED_FUNCTIONS filtered. 

   (* 
    Potential lemma for linking-- 

   Lemma linking_postcondition :  
    forall (p1 p2 : ll_toplevel_entities), 
      not exists tl in (link_predefs p1 p2), tl' in p1 s.t. 
      (tl is a Definition with name n /\ tl' is a Declaration with name n)   
   *)


  Import CFGNotations. 

(* ms needs to be non-empty. enforce structurally, with a check, or not at all? *)
  Definition link_mcfgs (ms : nlist (CFG.mcfg dtyp)) :=
  (* merge ms, run transformations: enforce decl uniqueness,
     and perform checks on linked program with the error monad.
     either ret linked program or fail. *)
    let wf_cfg_or_fail {M} `{Monad M} `{RAISE_ERROR M} (m : CFG.mcfg dtyp) 
    (* : M (CFG.mcfg dtyp)  *)
    := 
    match m with 
      {| 
        m_name         := name;
        m_target       := target;
        m_datalayout   := d;
        m_type_defs    := tds;
        m_globals      := globals;
        m_declarations := decls;
        m_definitions  := defs;
      |} => 
    let unique_decls := remove_duplicates decls_eq decls in  
    (*  Laws: 
        Declarational Uniqueness: 
          Each declaration in a program has a unique name (manually enforced). 
        Declarations -> Definitions is Injective over names and types:
          For each definition, there is at most one declaration that shares
          its name and type (checked).
       Jump Closure:
          The set of terminator-mentioned labels in a CFG is a subset of 
          the set of block labels in that CFG (checked).
       *)
    let declarational_uniqueness := andb (uniq_b decls_eq decls) (uniq_b defs_eq defs) in 
    if negb declarational_uniqueness 
    then raise_error "non-unique definitions in linked program"
    else 
    let decls_defs_injective : bool := 
       (forallb (decl_def_match defs) decls) in 
    if negb decls_defs_injective
    then raise_error "decls/defs non-injective"
    else 
       ret {| 
        m_name         := name;
        m_target       := target;
        m_datalayout   := d;
        m_type_defs    := tds;
        m_globals      := globals;
        m_declarations := unique_decls;
        m_definitions  := defs;
      |}
    end
    in wf_cfg_or_fail (njoin_with modul_app ms).

    (* let jump_closure : bool :=
      let ocfgs : list (ocfg dtyp) := map (blks ∘ df_instrs) defs in 
      let block_ids : FS.t := fs_of_list (flat_map Scope.inputs ocfgs) in 
      let terminator_ids : FS.t := fs_of_list (flat_map (Scope.outputs) ocfgs)
      in FS.subset terminator_ids block_ids
    in  *)



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
       would be resolved by an operation of type [link_predefs : mcfg -> mcfg -> mcfg] that 
       combines two mcfgs coherently
   *)

  (* Returns `true` only if both function are named and have the same name.  *)
  (* TODO: move to AstLib? *)
  Definition function_name_eq (a b:function_id) : bool :=
    match a, b with
    | Name aname, Name bname => String.eqb aname bname
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
    inputs from the command line is nontrivial since we have to martial C-level strings
    into the Vellvm memory.  
   *)
  Definition main_args := [@DV.UVALUE_I 32 (@Integers.zero 32);
                           DV.UVALUE_Addr null
    ].

  Definition denote_vellvm_main (mcfg : CFG.mcfg dtyp) : itree L0 dvalue :=
    denote_vellvm (DTYPE_I (32)%positive) "main" main_args mcfg.

(* should change link_predefs to be over mcfg. 
   it should happen after main linking happens. *)

  Definition name_me progs :=
    let linked_with_predefs := convert_types (mcfg_of_tle (link_predefs progs)) in
    link_mcfgs (nbase linked_with_predefs).

  (**
     Now that we know how to denote a whole llvm program, we can _interpret_
     the resulting [itree].
   *)
  Definition interpreter_gen
             (ret_typ : dtyp)
             (entry : string)
             (args : list uvalue)
             (prog: ll_toplevel_entities)
    : itree L4 res_L4 :=
    let t := denote_vellvm ret_typ entry args 
              (convert_types (mcfg_of_tle (link_predefs prog))) in
    interp_mcfg4_exec t [] ([],[]) 0 initial_memory_state.

  (**
     Finally, the reference interpreter assumes no user-defined intrinsics and starts
     from "main" using bogus initial inputs.
   *)
  Definition interpreter
             (prog : ll_toplevel_entities) : itree L4 res_L4
    := interpreter_gen (DTYPE_I 32%positive) "main" main_args prog.

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
             (prog: ll_toplevel_entities)
    : PropT L4 res_L4 :=
    let t := denote_vellvm ret_typ entry args 
              (convert_types (mcfg_of_tle (link_predefs prog))) in
    ℑs eq eq t [] ([],[]) 0 initial_memory_state.

  Definition model_gen_oom
             (ret_typ : dtyp)
             (entry : string)
             (args : list uvalue)
             (prog: ll_toplevel_entities)
    : PropT L4 res_L4 :=
    let t := denote_vellvm ret_typ entry args 
              (convert_types (mcfg_of_tle (link_predefs prog))) in
    ℑs6 eq eq eq t [] ([],[]) 0 initial_memory_state.

  Definition model_gen_oom_L1
             (ret_typ : dtyp)
             (entry : string)
             (args : list uvalue)
             (prog: ll_toplevel_entities)
    : itree L1 res_L1 :=
    let t := denote_vellvm ret_typ entry args 
              (convert_types (mcfg_of_tle (link_predefs prog))) in
    ℑs1 t [].

  Definition model_gen_oom_L2
             (ret_typ : dtyp)
             (entry : string)
             (args : list uvalue)
             (prog: ll_toplevel_entities)
    : itree L2 res_L2 :=
    let t := denote_vellvm ret_typ entry args 
              (convert_types (mcfg_of_tle (link_predefs prog))) in
    ℑs2 t [] ([], []).

  Definition model_gen_oom_L3
    (RR : relation res_L2)
    (ret_typ : dtyp)
    (entry : string)
    (args : list uvalue)
    (prog: ll_toplevel_entities)
    : PropT L3 res_L3 :=
    let t := denote_vellvm ret_typ entry args 
              (convert_types (mcfg_of_tle (link_predefs prog))) in
    ℑs3 RR t [] ([], []) 0 initial_memory_state.

  Definition model_gen_oom_L4
    RR_mem
    RR_pick
    (ret_typ : dtyp)
    (entry : string)
    (args : list uvalue)
    (prog: ll_toplevel_entities)
    : PropT L4 res_L4 :=
    let t := denote_vellvm ret_typ entry args 
              (convert_types (mcfg_of_tle (link_predefs prog))) in
    ℑs4 RR_mem RR_pick t [] ([], []) 0 initial_memory_state.

  Definition model_gen_oom_L5
    RR_mem
    RR_pick
    (ret_typ : dtyp)
    (entry : string)
    (args : list uvalue)
    (prog: ll_toplevel_entities)
    : PropT L5 res_L5 :=
    let t := denote_vellvm ret_typ entry args 
              (convert_types (mcfg_of_tle (link_predefs prog))) in
    ℑs5 RR_mem RR_pick t [] ([], []) 0 initial_memory_state.

  Definition model_gen_oom_L6
    RR_mem
    RR_pick
    RR_oom
    (ret_typ : dtyp)
    (entry : string)
    (args : list uvalue)
    (prog: ll_toplevel_entities)
    : PropT L6 res_L6 :=
    let t := denote_vellvm ret_typ entry args 
              (convert_types (mcfg_of_tle (link_predefs prog))) in
    ℑs6 RR_mem RR_pick RR_oom t [] ([], []) 0 initial_memory_state.

  (**
     Finally, the official model assumes no user-defined intrinsics.
   *)
  Definition model := model_gen (DTYPE_I 32%positive) "main" main_args.
  Definition model_oom := model_gen_oom (DTYPE_I 32%positive) "main" main_args.
  Definition model_oom_L1 := model_gen_oom_L1 (DTYPE_I 32%positive) "main" main_args.
  Definition model_oom_L2 := model_gen_oom_L2 (DTYPE_I 32%positive) "main" main_args.
  Definition model_oom_L3 RR_mem := model_gen_oom_L3 RR_mem (DTYPE_I 32%positive) "main" main_args.
  Definition model_oom_L4 RR_mem RR_pick := model_gen_oom_L4 RR_mem RR_pick (DTYPE_I 32%positive) "main" main_args.
  Definition model_oom_L5 RR_mem RR_pick := model_gen_oom_L5 RR_mem RR_pick (DTYPE_I 32%positive) "main" main_args.
  Definition model_oom_L6 RR_mem RR_pick RR_oom := model_gen_oom_L6 RR_mem RR_pick RR_oom (DTYPE_I 32%positive) "main" main_args.
End LLVMTopLevel.

Module Make (IS : InterpreterStack) : LLVMTopLevel IS.
  Include LLVMTopLevel IS.
End Make.

Module TopLevelBigIntptr := Make InterpreterStackBigIntptr.
Module TopLevel64BitIntptr := Make InterpreterStack64BitIntptr.
