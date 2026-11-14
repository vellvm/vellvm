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

(** * Integer intrinsics

    The intrinsics on integers ([llvm.smax], [llvm.uadd.with.overflow],
    [llvm.ctlz], [llvm.vector.reduce.add], ...) are overloaded at every
    width and involve no pointers, so they are defined once, on mathematical
    integers, independently of [Params]: an [int_intrinsic] sees its
    arguments as [ival]s and answers with an [ires].  A poison argument makes
    the result poison before the intrinsic is consulted
    ([llvm_int_intrinsic]). *)

Variant ival : Set :=
| IV_Int (sz : positive) (u : Z)             (* [u] is the unsigned value *)
| IV_Vector (elts : list (positive * Z))
| IV_Poison.                                 (* or a vector with a poison element *)

Variant ires : Set :=
| IR_Int (sz : positive) (z : Z)             (* [z] modulo [2^sz] *)
| IR_Overflow (sz : positive) (z : Z) (overflow : bool)   (* [{ iN, i1 }] *)
| IR_Poison.

(** From the return type and the arguments; [None] if they are ill-typed. *)
Definition int_intrinsic : Set := dtyp -> list ival -> option ires.

Section IntegerIntrinsics.
  #[local] Open Scope Z_scope.

  Definition imodulus (sz : positive) : Z := 2 ^ Zpos sz.

  Definition isigned (sz : positive) (u : Z) : Z :=
    if 2 * u <? imodulus sz then u else u - imodulus sz.

  Definition imin_signed (sz : positive) : Z := - 2 ^ (Zpos sz - 1).
  Definition imax_signed (sz : positive) : Z := 2 ^ (Zpos sz - 1) - 1.
  Definition imax_unsigned (sz : positive) : Z := imodulus sz - 1.

  Definition sclamp (sz : positive) (z : Z) : Z :=
    Z.max (imin_signed sz) (Z.min z (imax_signed sz)).

  Definition uclamp (sz : positive) (z : Z) : Z :=
    Z.max 0 (Z.min z (imax_unsigned sz)).

  (** Lift an operation on the signed values. *)
  Definition on_signed {A} (f : Z -> Z -> A) (sz : positive) (a b : Z) : A :=
    f (isigned sz a) (isigned sz b).

  Definition int_binary (f : positive -> Z -> Z -> ires) : int_intrinsic :=
    fun _ args =>
      match args with
      | [IV_Int sz a; IV_Int sz' b] => if Pos.eqb sz sz' then Some (f sz a b) else None
      | _ => None
      end.

  (** [f] returns the exact result; the intrinsic returns it at the operand
      width. *)
  Definition int_arith (f : positive -> Z -> Z -> Z) : int_intrinsic :=
    int_binary (fun sz a b => IR_Int sz (f sz a b)).

  (* https://llvm.org/docs/LangRef.html#standard-c-c-library-intrinsics *)
  Definition llvm_smax := int_arith (on_signed Z.max).
  Definition llvm_smin := int_arith (on_signed Z.min).
  Definition llvm_umax := int_arith (fun _ => Z.max).
  Definition llvm_umin := int_arith (fun _ => Z.min).

  (* https://llvm.org/docs/LangRef.html#arithmetic-with-overflow-intrinsics *)
  Definition signed_overflow (f : Z -> Z -> Z) : int_intrinsic :=
    int_binary (fun sz a b =>
      let z := on_signed f sz a b in
      IR_Overflow sz z (negb (Z.eqb z (sclamp sz z)))).

  Definition unsigned_overflow (f : Z -> Z -> Z) : int_intrinsic :=
    int_binary (fun sz a b =>
      let z := f a b in
      IR_Overflow sz z (negb (Z.eqb z (uclamp sz z)))).

  Definition llvm_sadd_with_overflow := signed_overflow Z.add.
  Definition llvm_ssub_with_overflow := signed_overflow Z.sub.
  Definition llvm_smul_with_overflow := signed_overflow Z.mul.
  Definition llvm_uadd_with_overflow := unsigned_overflow Z.add.
  Definition llvm_usub_with_overflow := unsigned_overflow Z.sub.
  Definition llvm_umul_with_overflow := unsigned_overflow Z.mul.

  (* https://llvm.org/docs/LangRef.html#saturation-arithmetic-intrinsics *)
  Definition llvm_sadd_sat := int_arith (fun sz a b => sclamp sz (on_signed Z.add sz a b)).
  Definition llvm_ssub_sat := int_arith (fun sz a b => sclamp sz (on_signed Z.sub sz a b)).
  Definition llvm_uadd_sat := int_arith (fun sz a b => uclamp sz (a + b)).
  Definition llvm_usub_sat := int_arith (fun sz a b => uclamp sz (a - b)).

  (* A shift by the bit width or more is poison. *)
  Definition shl_sat (f : positive -> Z -> Z -> Z) : int_intrinsic :=
    int_binary (fun sz a b => if Zpos sz <=? b then IR_Poison else IR_Int sz (f sz a b)).

  Definition llvm_sshl_sat := shl_sat (fun sz a b => sclamp sz (Z.shiftl (isigned sz a) b)).
  Definition llvm_ushl_sat := shl_sat (fun sz a b => uclamp sz (Z.shiftl a b)).

  (** The intrinsics taking a value and an [i1] immediate. *)
  Definition int_flagged (f : positive -> Z -> bool -> ires) : int_intrinsic :=
    fun _ args =>
      match args with
      | [IV_Int sz a; IV_Int 1 flag] => Some (f sz a (negb (Z.eqb flag 0)))
      | _ => None
      end.

  (* [abs] of the minimum signed value is that value, or poison if
     [is_int_min_poison]. *)
  Definition llvm_abs :=
    int_flagged (fun sz a is_int_min_poison =>
      let s := isigned sz a in
      if andb is_int_min_poison (Z.eqb s (imin_signed sz)) then IR_Poison
      else IR_Int sz (Z.abs s)).

  (* [ctlz] and [cttz] of zero are the bit width, or poison if
     [is_zero_poison]. *)
  Definition count_zeros (f : positive -> Z -> Z) : int_intrinsic :=
    int_flagged (fun sz a is_zero_poison =>
      if Z.eqb a 0
      then if is_zero_poison then IR_Poison else IR_Int sz (Zpos sz)
      else IR_Int sz (f sz a)).

  Definition llvm_ctlz := count_zeros (fun sz a => Zpos sz - 1 - Z.log2 a).
  Definition llvm_cttz := count_zeros (fun _ a => Z.log2 (Z.land a (- a))).

  Definition int_unary (f : positive -> Z -> Z) : int_intrinsic :=
    fun _ args =>
      match args with
      | [IV_Int sz a] => Some (IR_Int sz (f sz a))
      | _ => None
      end.

  Fixpoint pos_popcount (p : positive) : Z :=
    match p with
    | xH => 1
    | xO p => pos_popcount p
    | xI p => 1 + pos_popcount p
    end.

  Definition llvm_ctpop :=
    int_unary (fun _ a => match a with Zpos p => pos_popcount p | _ => 0 end).

  Definition llvm_bitreverse :=
    int_unary (fun sz a =>
      snd (Pos.iter (fun '(a, r) => (Z.div2 a, 2 * r + Z.b2z (Z.odd a))) (a, 0) sz)).

  (* Funnel shifts of the concatenation [a:b] by [c] modulo the bit width:
     [fshl] returns the high word of the left shift, [fshr] the low word of
     the right shift. *)
  Definition funnel_shift (f : positive -> Z -> Z -> Z) : int_intrinsic :=
    fun _ args =>
      match args with
      | [IV_Int sz a; IV_Int sz' b; IV_Int sz'' c] =>
          if andb (Pos.eqb sz sz') (Pos.eqb sz sz'')
          then Some (IR_Int sz (f sz (a * imodulus sz + b) (c mod Zpos sz)))
          else None
      | _ => None
      end.

  Definition llvm_fshl := funnel_shift (fun sz ab c => Z.shiftr (Z.shiftl ab c) (Zpos sz)).
  Definition llvm_fshr := funnel_shift (fun _ ab c => Z.shiftr ab c).

  (* Three-way comparison: -1, 0 or 1 at the return type. *)
  Definition three_way (f : positive -> Z -> Z -> Datatypes.comparison) : int_intrinsic :=
    fun t args =>
      match t, args with
      | DTYPE_Base (DTYPE_I r), [IV_Int sz a; IV_Int sz' b] =>
          if Pos.eqb sz sz'
          then Some (IR_Int r (match f sz a b with Datatypes.Lt => -1 | Datatypes.Eq => 0 | Datatypes.Gt => 1 end))
          else None
      | _, _ => None
      end.

  Definition llvm_scmp := three_way (on_signed Z.compare).
  Definition llvm_ucmp := three_way (fun _ => Z.compare).

  (* https://llvm.org/docs/LangRef.html#vector-reduction-intrinsics *)
  Definition vector_reduce (f : positive -> Z -> Z -> Z) : int_intrinsic :=
    fun _ args =>
      match args with
      | [IV_Vector ((sz, a) :: elts)] =>
          Some (IR_Int sz (fold_left (fun acc '(_, b) => f sz acc b mod imodulus sz) elts a))
      | _ => None
      end.

  Definition llvm_vector_reduce_add := vector_reduce (fun _ => Z.add).
  Definition llvm_vector_reduce_mul := vector_reduce (fun _ => Z.mul).
  Definition llvm_vector_reduce_and := vector_reduce (fun _ => Z.land).
  Definition llvm_vector_reduce_or := vector_reduce (fun _ => Z.lor).
  Definition llvm_vector_reduce_xor := vector_reduce (fun _ => Z.lxor).
  Definition llvm_vector_reduce_smax := vector_reduce (on_signed Z.max).
  Definition llvm_vector_reduce_smin := vector_reduce (on_signed Z.min).
  Definition llvm_vector_reduce_umax := vector_reduce (fun _ => Z.max).
  Definition llvm_vector_reduce_umin := vector_reduce (fun _ => Z.min).

End IntegerIntrinsics.

(** The intrinsics with a built-in semantics.  An overloaded intrinsic is one
    family, whatever its type mangling: [llvm.fabs.f32] and [llvm.fabs.f64]
    are both [Intr_fabs]. *)
Variant intrinsic_family : Set :=
| Intr_int (f : int_intrinsic)
| Intr_fabs
| Intr_maxnum
| Intr_minimum
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

(** The families named [llvm.<name>], and whether each is overloaded: an
    overloaded name is followed by the mangling of its type parameters
    ([.f32], [.p0.p0.i64]), any other name must match exactly.  The semantic
    functions take the types from their arguments, so the mangling itself is
    not interpreted. *)
Definition intrinsic_table : list (string * bool * intrinsic_family) :=
  [ ("fabs", true, Intr_fabs);
    ("maxnum", true, Intr_maxnum);
    ("minimum", true, Intr_minimum);
    ("memcpy", true, Intr_memcpy);
    ("memmove", true, Intr_memmove);
    ("memset", true, Intr_memset);
    ("vellvm.internal.throw", false, Intr_throw);
    ("assume", false, Intr_assume);
    ("va_start", false, Intr_va_start);
    ("va_end", false, Intr_va_end);
    ("va_copy", false, Intr_va_copy);
    ("smax", true, Intr_int llvm_smax);
    ("smin", true, Intr_int llvm_smin);
    ("umax", true, Intr_int llvm_umax);
    ("umin", true, Intr_int llvm_umin);
    ("sadd.with.overflow", true, Intr_int llvm_sadd_with_overflow);
    ("ssub.with.overflow", true, Intr_int llvm_ssub_with_overflow);
    ("smul.with.overflow", true, Intr_int llvm_smul_with_overflow);
    ("uadd.with.overflow", true, Intr_int llvm_uadd_with_overflow);
    ("usub.with.overflow", true, Intr_int llvm_usub_with_overflow);
    ("umul.with.overflow", true, Intr_int llvm_umul_with_overflow);
    ("sadd.sat", true, Intr_int llvm_sadd_sat);
    ("ssub.sat", true, Intr_int llvm_ssub_sat);
    ("uadd.sat", true, Intr_int llvm_uadd_sat);
    ("usub.sat", true, Intr_int llvm_usub_sat);
    ("sshl.sat", true, Intr_int llvm_sshl_sat);
    ("ushl.sat", true, Intr_int llvm_ushl_sat);
    ("abs", true, Intr_int llvm_abs);
    ("ctlz", true, Intr_int llvm_ctlz);
    ("cttz", true, Intr_int llvm_cttz);
    ("ctpop", true, Intr_int llvm_ctpop);
    ("bitreverse", true, Intr_int llvm_bitreverse);
    ("fshl", true, Intr_int llvm_fshl);
    ("fshr", true, Intr_int llvm_fshr);
    ("scmp", true, Intr_int llvm_scmp);
    ("ucmp", true, Intr_int llvm_ucmp);
    ("vector.reduce.add", true, Intr_int llvm_vector_reduce_add);
    ("vector.reduce.mul", true, Intr_int llvm_vector_reduce_mul);
    ("vector.reduce.and", true, Intr_int llvm_vector_reduce_and);
    ("vector.reduce.or", true, Intr_int llvm_vector_reduce_or);
    ("vector.reduce.xor", true, Intr_int llvm_vector_reduce_xor);
    ("vector.reduce.smax", true, Intr_int llvm_vector_reduce_smax);
    ("vector.reduce.smin", true, Intr_int llvm_vector_reduce_smin);
    ("vector.reduce.umax", true, Intr_int llvm_vector_reduce_umax);
    ("vector.reduce.umin", true, Intr_int llvm_vector_reduce_umin)
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

(** [s] without the prefix [pre], if it has it. *)
Fixpoint strip_prefix (pre s : string) : option string :=
  match pre, s with
  | EmptyString, _ => Some s
  | String a pre', String b s' => if Ascii.eqb a b then strip_prefix pre' s' else None
  | String _ _, EmptyString => None
  end.

Definition lookup_intrinsic (name : string) : option intrinsic_family :=
  match strip_prefix "llvm." name with
  | Some name' =>
      option_map snd
        (List.find (fun '(fam, overloaded, _) => names_intrinsic overloaded fam name') intrinsic_table)
  | None =>
      if String.eqb name "malloc" then Some Intr_malloc
      else if String.eqb name "free" then Some Intr_free
      else None
  end.

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

  Definition dvalue_to_ival (v : dvalue) : option ival :=
    match v with
    | DVALUE_Base (DVALUE_I sz x) => Some (IV_Int sz (unsigned x))
    | DVALUE_Base DVALUE_Poison => Some IV_Poison
    | DVALUE_Array true elts =>
        fold_right (fun elt acc =>
                      match elt, acc with
                      | DVALUE_Base (DVALUE_I sz x), Some (IV_Vector l) =>
                          Some (IV_Vector ((sz, unsigned x) :: l))
                      | DVALUE_Base (DVALUE_I _ _), Some IV_Poison
                      | DVALUE_Base DVALUE_Poison, Some _ => Some IV_Poison
                      | _, _ => None
                      end)
          (Some (IV_Vector [])) elts
    | _ => None
    end.

  Fixpoint dvalues_to_ivals (vs : list dvalue) : option (list ival) :=
    match vs with
    | [] => Some []
    | v :: vs =>
        match dvalue_to_ival v, dvalues_to_ivals vs with
        | Some i, Some is => Some (i :: is)
        | _, _ => None
        end
    end.

  Definition ires_to_dvalue (r : ires) : dvalue :=
    match r with
    | IR_Int sz z => DVALUE_Base (DVALUE_I sz (repr z))
    | IR_Overflow sz z overflow =>
        DVALUE_Struct false [DVALUE_Base (DVALUE_I sz (repr z));
                             DVALUE_Base (DVALUE_I 1 (if overflow then one else zero))]
    | IR_Poison => DVALUE_Base DVALUE_Poison
    end.

  Definition is_iv_poison (i : ival) : bool :=
    match i with IV_Poison => true | _ => false end.

  Definition llvm_int_intrinsic (f : int_intrinsic) (t : dtyp) : pure_function :=
    fun args =>
      match dvalues_to_ivals args with
      | Some args' =>
          if existsb is_iv_poison args' then retr (DVALUE_Base DVALUE_Poison)
          else
            match f t args' with
            | Some r => retr (ires_to_dvalue r)
            | None => raise_error "integer intrinsic got incorrect / ill-typed inputs"
            end
      | None => raise_error "integer intrinsic got incorrect / ill-typed inputs"
      end.

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
  Definition intrinsic_semantics (t : dtyp) (fam : intrinsic_family) : option semantic_function :=
    match fam with
    | Intr_int f => Some (pure_to_semantic (llvm_int_intrinsic f t))
    | Intr_fabs => Some (pure_base_to_semantic llvm_fabs)
    | Intr_maxnum => Some (pure_base_to_semantic llvm_maxnum)
    | Intr_minimum => Some (pure_base_to_semantic llvm_minimum)
    | Intr_throw => Some (pure_base_to_semantic llvm_vellvm_internal_throw)
    | Intr_assume => Some (pure_base_to_semantic llvm_assume)
    | Intr_va_start => Some llvm_va_start
    | Intr_va_end => Some llvm_va_end
    | Intr_va_copy => Some llvm_va_copy
    | Intr_memcpy | Intr_memmove | Intr_memset | Intr_malloc | Intr_free => None
    end.

  (* [t] is the call's return type. *)
  Definition named_intrinsic_semantics (t : dtyp) (name : string) : option semantic_function :=
    match lookup_intrinsic name with
    | Some fam => intrinsic_semantics t fam
    | None => None
    end.

End Intrinsics.
