(* begin hide *)
From Stdlib Require Import
  Ascii
  String.

From ExtLib Require Import
  Programming.Eqv
  Data.String.

From ITree Require Import ITree.

From Vellvm Require Import
  Utils
  Syntax
  Params
  Semantics.DynamicValues
  VellvmIntegers
  Numeric
  LLVMEvents
  Conversion
  EOU.

From Flocq.IEEE754 Require Import
  Binary
  Bits.

Import EqvNotation.
(* end hide *)

(** * Intrinsics VIR provides an easily extensible support for instrinsics.
    
    There are several ways to define the semantics of intrinsics:

    1. As LLVM IR "library" code.

       This is the most easily extensible way to extend VIR with semantics for
       intrinsics. It works by providing a `.ll` file that defines the meaning
       of the intrinsic using standard LLVM instructions.  There are a few
       potential semantic implications that may impact reasoning about such
       intrinsics.  In particular, because such an intrinsic is just an
       "ordinary" LLVM function:

       - calling it will create a stack frame, and do a function call it will
       - have global address address in the heap

       Neither of which would be true of "real" intrinsics.

    2. As a Rocq function that directly manipulates [VIR] [dvalue].
       These are either defined below in this file _or_, like some memory
       intrinsics and varargs that interact with LLVM IR's effects, defined
       elsewhere.

       Each such intrinsic must be:

        - given a constructor of [intrinsic_family] and a row of
          [intrinsic_table], which maps its name to that constructor

        - _if_ the intrinsic is a pure computation, it must be implemented as a
          pure Gallina function of type [semantic_function] and added to
          [intrinsic_semantics]

        - _if_ it is impure, i.e. depends on the memory, as is the case for
          [memcpy], its implementation must be provided in [src/rocq/Semantics/Implementations/Memory.v]
          and a case for its family added to [handle_intrinsicM].
 *)

(** The intrinsics with a built-in semantics.  An overloaded intrinsic is one
    family, whatever its type mangling: [llvm.ushl.sat.i8] and
    [llvm.ushl.sat.i64] are both [Intr_ushl_sat]. *)
Variant intrinsic_family : Set :=
| Intr_fabs
| Intr_maxnum
| Intr_minimum
| Intr_ushl_sat
| Intr_throw
| Intr_assume
| Intr_va_start
| Intr_va_end
| Intr_va_copy
| Intr_memcpy
| Intr_memmove
| Intr_memset
| Intr_malloc
| Intr_free.

(** Each family's name, and whether it is overloaded: an overloaded name is
    followed by the mangling of its type parameters ([.f32], [.p0.p0.i64]),
    any other name must match exactly.  The semantic functions take the types
    from their arguments, so the mangling itself is not interpreted. *)
Definition intrinsic_table : list (string * bool * intrinsic_family) :=
  [ ("llvm.fabs", true, Intr_fabs);
    ("llvm.maxnum", true, Intr_maxnum);
    ("llvm.minimum", true, Intr_minimum);
    ("llvm.ushl.sat", true, Intr_ushl_sat);
    ("llvm.memcpy", true, Intr_memcpy);
    ("llvm.memmove", true, Intr_memmove);
    ("llvm.memset", true, Intr_memset);
    ("malloc", false, Intr_malloc);
    ("free", false, Intr_free);
    ("llvm.vellvm.internal.throw", false, Intr_throw);
    ("llvm.assume", false, Intr_assume);
    ("llvm.va_start", false, Intr_va_start);
    ("llvm.va_end", false, Intr_va_end);
    ("llvm.va_copy", false, Intr_va_copy)
  ]%string.

Definition is_digit (c : ascii) : bool :=
  match c with
  | "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" => true
  | _ => false
  end%char.

(** Does [s] start a type mangling: [i32], [f64], [p0], [v4i1]? *)
Definition starts_mangling (s : string) : bool :=
  match s with
  | String c (String d _) =>
      if (Ascii.eqb c "i" || Ascii.eqb c "f" || Ascii.eqb c "p" || Ascii.eqb c "v")%char%bool
      then is_digit d else false
  | _ => false
  end.

(** Is [name] the family name [fam], followed by a mangling if the family is
    [overloaded]? *)
Fixpoint names_intrinsic (overloaded : bool) (fam name : string) : bool :=
  match fam, name with
  | EmptyString, EmptyString => true
  | EmptyString, String c rest =>
      if overloaded then if Ascii.eqb c "."%char then starts_mangling rest else false
      else false
  | String a fam', String b name' =>
      if Ascii.eqb a b then names_intrinsic overloaded fam' name' else false
  | String _ _, EmptyString => false
  end.

Definition lookup_intrinsic (name : string) : option intrinsic_family :=
  option_map snd
    (List.find (fun '(fam, overloaded, _) => names_intrinsic overloaded fam name) intrinsic_table).

Definition is_intrinsic (id : function_id) : bool :=
  match id with
  | Name s => match lookup_intrinsic s with Some _ => true | None => false end
  | _ => false
  end.

Definition intrinsic_exp {T} (e:exp T) : option string :=
  match e with
  | EXP_Ident (ID_Global (Name s)) =>
      match lookup_intrinsic s with
      | Some _ => Some s
      | None => None
      end
  | _ => None
  end.



(* This functor module provides a way to (extensibly) add the semantic behavior
   for intrinsics defined outside of the core Vellvm operational semantics.

   Internally, invocation of an intrinsic looks no different than that of an
   external function call, so each LLVM intrinsic instruction should produce
   a Call effect.

   Each intrinsic is identified by its name (a string) and its denotation is
   given by a function from a list of dynamic values to a dynamic value (or
   possibly an error).

   NOTE: The intrinsics that can be defined at this layer of the semantics
   cannot affect the core interpreter state or the memory model.  This layer is
   useful for implementing "pure value" intrinsics like floating point
   operations, etc.  Also note that such intrinsics cannot themselves generate
   any other effects.

*)
Section Intrinsics.
  Context {Pa : Params}.
 
  Open Scope string_scope.

  Context {E} `{FailureE -< E} `{UBE -< E} `{OOME -< E} `{ExternalCallE -< E} `{MemoryE -< E}.
    
  (* Each (pure) intrinsic is defined by a function of the following type.

   - each intrinsic should "morally" be a total function: assuming the LLVM program
     is well formed, the intrisnic should always produce an LLVM value (which itself
     might be poison)

   - error should be returned only in the case that the LLVM program is ill-formed
     (e.g. if the wrong number and/or type of arguments is given to the intrinsic)

   - The right-hand [dvalue] of the [+] result is used to throw an exception.
   *)
  Definition pure_base_function := list dvalue_base -> EOU (dvalue_base + dvalue_base).
  Definition pure_function      := list dvalue -> EOU (dvalue + dvalue).
  Definition semantic_function  := list dvalue -> option ptr -> itree E (dvalue + dvalue).


  (* Intrinsics semantic functions -------------------------------------------- *)

  #[local] Notation retr x := (ret (inr x)).
  (* LANGREF: [llvm.fabs] is explicitly *not* a "floating-point math
     operation": it "acts directly on the underlying bit representation and
     never changes anything except possibly for the sign bit".  So its result
     on a NaN is fully determined -- the payload and quiet bit are preserved
     and the sign is cleared -- with none of the non-determinism that applies
     to NaN results of genuine math operations.

     [Float.abs] / [Float32.abs] are [Babs] instantiated with [abs_nan], which
     clears the sign.  Flocq's [b64_abs] / [b32_abs] instead use [unop_nan_pl],
     which returns the NaN completely unchanged, sign included -- so
     [llvm.fabs(-NaN)] used to come back negative. *)

  Definition llvm_fabs : pure_base_function :=
    fun args =>
      match args with
      | [DVALUE_Float d] => retr (DVALUE_Float (Float32.abs d))
      | [DVALUE_Double d] => retr (DVALUE_Double (Float.abs d))
      | _ => raise_error "llvm.fabs got incorrect / ill-typed inputs"
      end.

  (* Is a NaN payload quiet?  The quiet bit is the top bit of the significand:
     bit 51 for binary64, bit 22 for binary32. *)
  Definition quiet_nan_pl64 (pl : positive) : bool := Pos.testbit pl 51%N.
  Definition quiet_nan_pl32 (pl : positive) : bool := Pos.testbit pl 22%N.

  (* LANGREF (llvm.maxnum): "If both operands are qNaNs, returns a NaN. If one
     operand is qNaN and another operand is a number, returns the number. If
     both operands are numbers, returns the greater of the two arguments. -0.0
     is considered to be less than +0.0 for this intrinsic."

     Note that a qNaN operand does *not* propagate -- returning the qNaN, as we
     used to, is simply wrong, not a permitted resolution of NaN
     non-determinism.

     For a *signaling* NaN operand the LangRef does leave the result
     non-deterministic: the intrinsic may "return a NaN" or "treat the
     signaling NaN as a quiet NaN".  We resolve that by returning a NaN, which
     keeps the sNaN behaviour the tests in tests/llvm-arith/double already pin
     down.  Once NaN choices become draw events this is the branch point.

     The [Ceq] case is what implements "-0.0 is less than +0.0": for equal
     non-zero operands either answer is the same value, and for the +0.0/-0.0
     pair it picks the positive one regardless of argument order. *)
  Definition Float_maxnum (a b: float): float :=
    match a, b with
    | B754_nan _ _ _, B754_nan _ _ _ => build_nan _ _ (binop_nan_pl64 a b)
    | B754_nan _ pl _, _ =>
        if quiet_nan_pl64 pl then b else build_nan _ _ (binop_nan_pl64 a b)
    | _, B754_nan _ pl _ =>
        if quiet_nan_pl64 pl then a else build_nan _ _ (binop_nan_pl64 a b)
    | _, _ =>
      if Float.cmp Ceq a b
      then (if Bsign _ _ a then b else a)
      else (if Float.cmp Clt a b then b else a)
    end.

  Definition Float32_maxnum (a b: float32): float32 :=
    match a, b with
    | B754_nan _ _ _, B754_nan _ _ _ => build_nan _ _ (binop_nan_pl32 a b)
    | B754_nan _ pl _, _ =>
        if quiet_nan_pl32 pl then b else build_nan _ _ (binop_nan_pl32 a b)
    | _, B754_nan _ pl _ =>
        if quiet_nan_pl32 pl then a else build_nan _ _ (binop_nan_pl32 a b)
    | _, _ =>
      if Float32.cmp Ceq a b
      then (if Bsign _ _ a then b else a)
      else (if Float32.cmp Clt a b then b else a)
    end.

  Definition llvm_maxnum : pure_base_function :=
    fun args =>
      match args with
      | [DVALUE_Float a; DVALUE_Float b] => retr (DVALUE_Float (Float32_maxnum a b))
      | [DVALUE_Double a; DVALUE_Double b] => retr (DVALUE_Double (Float_maxnum a b))
      | _ => raise_error "llvm.maxnum got incorrect / ill-typed inputs"
      end.

  (* LANGREF (llvm.minimum): "If either operand is a NaN, returns a NaN.
     Otherwise returns the lesser of the two arguments. -0.0 is considered to
     be less than +0.0 for this intrinsic."

     Unlike [llvm.maxnum], propagating a NaN operand is the specified
     behaviour, so only the signed-zero case needed fixing here. *)
  Definition Float_minimum (a b: float): float :=
    match a, b with
    | B754_nan _ _ _, _ | _, B754_nan _ _ _ => build_nan _ _ (binop_nan_pl64 a b)
    | _, _ =>
      if Float.cmp Ceq a b
      then (if Bsign _ _ a then a else b)
      else (if Float.cmp Clt a b then a else b)
    end.

  Definition Float32_minimum (a b: float32): float32 :=
    match a, b with
    | B754_nan _ _ _, _ | _, B754_nan _ _ _ => build_nan _ _ (binop_nan_pl32 a b)
    | _, _ =>
      if Float32.cmp Ceq a b
      then (if Bsign _ _ a then a else b)
      else (if Float32.cmp Clt a b then a else b)
    end.

  Definition llvm_minimum : pure_base_function :=
    fun args =>
      match args with
      | [DVALUE_Float a; DVALUE_Float b] => retr (DVALUE_Float (Float32_minimum a b))
      | [DVALUE_Double a; DVALUE_Double b] => retr (DVALUE_Double (Float_minimum a b))
      | _ => raise_error "llvm.minimum got incorrect / ill-typed inputs"
      end.

  (* Saturated arithmetic: https://llvm.org/docs/LangRef.html#saturation-arithmetic-intrinsics *)
  Definition ushl_sat {I : Type} `{TDI : ToDvalueBase I} `{VMI : VMemInt I} (x y : I) : EOU dvalue_base :=
    res <- mshl x y;;
    let res_u := munsigned res in
    let res_u' := Z.shiftl (munsigned x) (munsigned y) in
    if option_pred (fun bw => munsigned y >=? Zpos bw) (@mbitwidth I VMI)
    then ret DVALUE_Poison
    else
      if (res_u' >? res_u)
      then 
        match (@mmax_unsigned I VMI) with
        | None =>
            raise_error "ushl_sat issue with unbounded integer type."
        | Some m =>
            match mrepr m with
            | raise_oom _ =>
                raise_error "ushl_sat: cannot represent maximum value in type... Should not happen."
            (* Note: we have enlarged the monad, so that statically we don't rule out new absurd cases such as failure or ub *)
            | m => tdb <$> m
            end
        end
      else ret (tdb res).

  Definition llvm_ushl_sat : pure_base_function :=
    fun args =>
      match args with
      | [DVALUE_I sz a; DVALUE_I sz' b] =>
          match Pos.eq_dec sz' sz with
          | left e => inr <$> ushl_sat a (eq_rect sz' (@bit_int) b sz e)
          | right _ => raise_error "llvm.ushl.sat got operands of different widths"
          end
      | _ => raise_error "llvm.ushl.sat got incorrect / ill-typed inputs"
      end.

  Definition llvm_vellvm_internal_throw : pure_base_function :=
    fun args =>
      match args with
      (* Raise: the [inl] branch of the intrinsic's [exc + dvalue] result is
         turned into an abortive [LLVMExc] by [denote_instr]. The payload is a
         placeholder panic object, treated opaquely by the unwind machinery. *)
      | [] => ret (inl DVALUE_None)
      | _ => raise_error "llvm_vellvm_internal_throw got incorrect / ill-typed inputs"
      end.

  (* LangRef (llvm.assume): "If the condition is violated during execution,
     the behavior is undefined."  Its operand bundles belong to the call, not
     to the intrinsic: [denote_operand_bundles] (Denotation.v) checks them. *)
  Definition llvm_assume : pure_base_function :=
    fun args =>
      match args with
      | [DVALUE_I 1 c] =>
          if equ c one then ret (inr DVALUE_None)
          else raise_ub "llvm.assume: the condition is false."
      | [DVALUE_Poison] => raise_ub "llvm.assume: the condition is poison."
      | _ => raise_error "llvm.assume got incorrect / ill-typed inputs"
      end.

  Definition llvm_va_start : semantic_function :=
    fun args varargs =>
      match args, varargs with
    | [ a ], Some varargs =>
        match a with
        | DVALUE_Base DVALUE_Poison => raiseUB ("Store to poisoned address in va_start.")
        | _ => store DTYPE_Pointer a (DVALUE_Pointer varargs);;
              retr (DVALUE_Base DVALUE_None)
        end
    | _, _ => raise "va_start: invalid arguments."
    end.
  
  Definition llvm_va_copy : semantic_function :=
    fun args varargs =>
      match args with
      | [dest; src] =>
          vargs <- load DTYPE_Pointer src;;
          store DTYPE_Pointer dest vargs;;
          retr (DVALUE_Base DVALUE_None)
      | _ => raise ": va_copy invalid arguments"
      end.

  Definition llvm_va_end  : semantic_function :=
    fun args varargs =>
      retr (DVALUE_Base DVALUE_None).

  Definition pure_base_to_pure : pure_base_function -> pure_function :=
    fun f args =>
      args' <- map_monad dvalue_to_dvalue_base args ;;
      ans <- f args' ;;
      match ans with
      | inr x => retr (DVALUE_Base x)
      | inl x => ret (inl (DVALUE_Base x))
      end.
  
  Definition pure_to_semantic : pure_function -> semantic_function :=
    fun f args _ => EOU_to_itree (f args).

  Definition pure_base_to_semantic : pure_base_function -> semantic_function :=
    fun f => pure_to_semantic (pure_base_to_pure f).
  
  (* The semantics of each family, except for the memory intrinsics, which
     [handle_intrinsicM] interprets. *)
  Definition intrinsic_semantics (fam : intrinsic_family) : option semantic_function :=
    match fam with
    | Intr_fabs => Some (pure_base_to_semantic llvm_fabs)
    | Intr_maxnum => Some (pure_base_to_semantic llvm_maxnum)
    | Intr_minimum => Some (pure_base_to_semantic llvm_minimum)
    | Intr_ushl_sat => Some (pure_base_to_semantic llvm_ushl_sat)
    | Intr_throw => Some (pure_base_to_semantic llvm_vellvm_internal_throw)
    | Intr_assume => Some (pure_base_to_semantic llvm_assume)
    | Intr_va_start => Some llvm_va_start
    | Intr_va_end => Some llvm_va_end
    | Intr_va_copy => Some llvm_va_copy
    | Intr_memcpy | Intr_memmove | Intr_memset | Intr_malloc | Intr_free => None
    end.

  Definition named_intrinsic_semantics (name : string) : option semantic_function :=
    match lookup_intrinsic name with
    | Some fam => intrinsic_semantics fam
    | None => None
    end.

End Intrinsics.
