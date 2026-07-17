(* begin hide *)
From Stdlib Require Import Program.
From ITree Require Import
  ITree
  Events.State.

From Vellvm Require Import Handlers.
From Vellvm Require Import
  Utils
  Syntax
  Params
  Implementations.Memory
  DynamicValues
  LLVMEvents
  Denotation
  Operations
  Semantics.IntrinsicsDefinitions
  Semantics.InterpretationStack
  Semantics.VellvmIntegers.
(* end hide *)

Section withParams.
  Context {Pa : Params}.

  (* IO & library functions -------------------------------------------------------------------- *)
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
  (** A semantic function to read an i8 value at [strptr + index] from the memory.
      Propagates all memory failures and raises a Vellvm "Failure" if the
      value read does not concretize to a DVALUE_I8.
   *)
  Definition i8_str_index (strptr : ptr) (index : Z) : CFGtop (@Integers.bit_int 8) :=
    iptr <- EOU_to_itree (from_Z index) ;;
    addr <- EOU_to_itree (handle_gep_ptr (DTYPE_I 8) strptr [DVALUE_Base (DVALUE_Iptr iptr)]) ;;
    d_byte <- load (DTYPE_I 8) (DVALUE_Pointer addr) ;;
    match d_byte with
    | DVALUE_Base (DVALUE_I 8 b) => ret b
    | bad => raise ("i8_str_index failed with non-DVALUE_I8 " ++ show_dvalue bad)
    end.

  (** Semantic function that triggers a single IO_stdout event to print
    the passed-in character.
    the character comes in as an i32, so the function truncates to an i8
    to match types with IO_stdout.
   *)
  Definition putchar_denotation : function_denotation :=
      let putchar_body (u_char:dvalue) : CFGtop dvalue :=
         match u_char with
         | DVALUE_Base (DVALUE_I sz x32)  =>
             if Pos.eq_dec 32 sz
             then
               let x8 : int8 := repr (unsigned x32) in
               io_stdout [x8] ;;
               ret (DVALUE_Base (DVALUE_I 8 x8))
             else
               raiseUB ("putc got non-i32 integer argument")
         | bad => raiseUB ("putc got non-i32 argument " ++ show_dvalue bad)
         end
       in
       fun (args : list dvalue) =>
         match args with
         | char::[] => inr <$> putchar_body char
         | _ => raise "putc called with zero or more than one arguments"
         end.

  (** Semantic function that treats [u_strptr] as a C-style string pointer:
      - reads i8 values from memory until it encounters a null-terminator (i8 0)
      - triggers an IO_stdout event with the bytes plus a newline
   *)
  Definition puts_denotation : function_denotation :=
    let puts_body (u_strptr : dvalue) : CFGtop dvalue :=
      match u_strptr with
      | DVALUE_Base (DVALUE_Pointer strptr) =>
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
          ret (DVALUE_Base (DVALUE_I 8 (@Integers.zero 8)))
      | bad => raiseUB ("puts got non-address argument " ++ show_dvalue bad)
      end
    in

    fun (args : list dvalue) =>
      match args with
      | strptr::[] => inr <$> puts_body strptr
      | _ => raise "puts called with zero or more than one arguments"
      end.

    (* *********DO NOT USE DIRECTLY*********
  Program should ONLY use `built_in_functions`, defined below, which filters
  out unused functions from _BUILTINS.

  Lists all functions built-in by default. As vellvm gains more, they should
  go into this list.
*)

  Definition _LIBRARIES : list (function_id * function_denotation) :=
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
  Definition library_functions (decls : list (declaration dtyp)) :
    list (function_id * function_denotation) :=
    filter (fun '(n, d) =>
              existsb (fun s => Rocqlib.proj_sumbool (Syntax.AstLib.RawIDOrd.eq_dec s n))
                (List.map (@dc_name dtyp) decls))
      (* if we have many builtins, pull out this List.map to a let-bind for explicit optimization *)
      _LIBRARIES.

End withParams.
