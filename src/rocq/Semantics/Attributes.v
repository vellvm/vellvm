(* begin hide *)

From Stdlib Require Import
  Bool.Bool.

From ITree Require Import
  ITree.

From Vellvm Require Import
  Numeric
  Utils
  Syntax
  Params
  EOU
  VellvmIntegers
  LLVMEvents
  DynamicValues
  IntrinsicsDefinitions.

Open Scope string_scope.

(* end hide *)

(** * Value-level checks imposed by LLVM annotations

    The checks that annotations on instructions, functions, and call sites
    impose on the values flowing through them: explicit alignments, the
    value attributes of parameters and return values (and the load metadata
    that acts like them), the function attributes that constrain how a call
    ends, calling conventions, what may be called as a function, and the
    operand bundles of [llvm.assume].  [Denotation.v] applies them at the
    points where LangRef does.

    Most of them are pure ([EOU]).  The ones that must read memory (the
    bytes promised by [dereferenceable]) and the ones built on them are
    itrees, written generically over any event signature with memory, UB,
    out-of-memory, and failure events (section [MemoryChecks]).
 *)

(** The integer a syntactic integer literal denotes. *)
Definition denote_int_syntax (x:int_syntax) : Z :=
  BinIntDef.Z.of_num_int x.

(** The explicit [align N] among an instruction's annotations, in bytes. *)
Definition explicit_alignment (anns : list (annotation dtyp)) : option N :=
  option_map (fun a => Z.to_N (denote_int_syntax a)) (find_option ann_align anns).

(** ** Parameter and return-value attributes, as LangRef reads them

    [dereferenceable(n)] counts as [nonnull] and [noundef], which LangRef
    says it implies (in addrspace 0). *)
Definition attr_is_nonnull (a : param_attr) : bool :=
  match a with
  | PARAMATTR_Nonnull | PARAMATTR_Dereferenceable _ => true
  | _ => false
  end.

Definition attr_is_noundef (a : param_attr) : bool :=
  match a with
  | PARAMATTR_Noundef | PARAMATTR_Dereferenceable _ => true
  | _ => false
  end.

(** Is the [sz]-bit integer [x] in the (possibly wrapping) range [[lo, hi)]?
    LangRef (range): "The pair a,b represents the range [a,b) ... The range
    is allowed to wrap.  The empty range is represented using 0,0." *)
Definition in_wrapping_range (sz : positive) (x lo hi : Z) : bool :=
  let m := (2 ^ Z.pos sz)%Z in
  let x := (x mod m)%Z in
  let lo := (lo mod m)%Z in
  let hi := (hi mod m)%Z in
  if (lo =? hi)%Z then false                     (* the empty range *)
  else if (lo <? hi)%Z then (lo <=? x)%Z && (x <? hi)%Z
  else (lo <=? x)%Z || (x <? hi)%Z.              (* wraps around *)

(** The floating-point class of a value, as its bit in a [nofpclass] mask
    (LangRef llvm.is.fpclass: snan 1, qnan 2, ninf 4, nnorm 8, nsub 16,
    nzero 32, pzero 64, psub 128, pnorm 256, pinf 512), read off the IEEE
    representation with [e] exponent and [m] mantissa bits. *)
Definition fp_class_of_bits (e m : Z) (bits : Z) : Z :=
  let neg := Z.testbit bits (e + m) in
  let exp := Z.land (Z.shiftr bits m) (Z.ones e) in
  let mant := Z.land bits (Z.ones m) in
  if (exp =? Z.ones e)%Z then
    if (mant =? 0)%Z then (if neg then 4 else 512)               (* infinities *)
    else if Z.testbit mant (m - 1) then 2 else 1                 (* quiet / signaling NaN *)
  else if (exp =? 0)%Z then
    if (mant =? 0)%Z then (if neg then 32 else 64)               (* zeros *)
    else (if neg then 16 else 128)                               (* subnormals *)
  else (if neg then 8 else 256).                                 (* normals *)

(** The integer operands of [llvm.assume] bundles: an alignment or size
    (unsigned), or an offset (signed). *)
Definition is_power_of_two (n : Z) : bool :=
  (0 <? n)%Z && (Z.land n (n - 1) =? 0)%Z.

Section Attributes.
  Context {Pa : Params}.

  (** ** Alignment checks

      LangRef (load/store): "Overestimating the alignment results in
      undefined behavior."  [assert_aligned_to a align msg] raises UB
      (reported with [msg]) if [a] is a pointer that is not aligned to the
      explicit alignment [align].  Without an explicit alignment, or when [a]
      is not a pointer (e.g. poison, which the access itself rejects), it
      does nothing.  [assert_alignment] reads the alignment from an
      instruction's annotations ([align N] on load/store). *)
  Definition assert_aligned_to (a : dvalue) (align : option int_syntax) (msg : string)
    : EOU unit :=
    match a, align with
    | DVALUE_Base (DVALUE_Pointer p), Some al =>
        if ptr_aligned_to p (Z.to_N (denote_int_syntax al)) then ret tt
        else raise_ub msg
    | _, _ => ret tt
    end.

  Definition assert_alignment (a : dvalue) (anns : list (annotation dtyp)) (msg : string)
    : EOU unit :=
    assert_aligned_to a (find_option ann_align anns) msg.

  (** ** Value attributes on parameters and return values

      LangRef: [nonnull], [align N], [range(a, b)], and [nofpclass] turn a
      violating value into poison ("poison value is returned or passed
      instead"); [noundef] makes a value that is not well defined immediate
      UB.  So [nonnull] without [noundef] passes poison on, while [nonnull
      noundef] on null is UB.  [dereferenceable(n)] "implies nonnull in
      addrspace(0)" and "implies noundef"; that its [n] bytes are accessible
      is checked by [assert_attrs_dereferenceable] in [apply_attrs].

      Vectors of pointers ([align]/[nonnull] per lane) are not yet
      covered. *)

  (** The poison-producing attributes, one at a time. *)
  Definition value_attr_nonnull (attrs : list param_attr) (v : dvalue) : dvalue :=
    match v with
    | DVALUE_Base (DVALUE_Pointer p) =>
        if existsb attr_is_nonnull attrs && (ptr_to_int p =? ptr_to_int null)%Z
        then DVALUE_Base DVALUE_Poison else v
    | _ => v
    end.

  Definition value_attr_align (attrs : list param_attr) (v : dvalue) : dvalue :=
    match v, find_option attr_align attrs with
    | DVALUE_Base (DVALUE_Pointer p), Some al =>
        if ptr_aligned_to p (Z.to_N (denote_int_syntax al)) then v
        else DVALUE_Base DVALUE_Poison
    | _, _ => v
    end.

  Definition value_attr_range (attrs : list param_attr) (v : dvalue) : dvalue :=
    match v, find_option attr_range attrs with
    | DVALUE_Base (DVALUE_I sz x), Some (lo, hi) =>
        if in_wrapping_range sz (unsigned x) (denote_int_syntax lo) (denote_int_syntax hi)
        then v else DVALUE_Base DVALUE_Poison
    | _, _ => v
    end.

  Definition fp_class (v : dvalue_base) : option Z :=
    match v with
    | DVALUE_Double d => Some (fp_class_of_bits 11 52 (unsigned (Floats.Float.to_bits d)))
    | DVALUE_Float f => Some (fp_class_of_bits 8 23 (unsigned (Floats.Float32.to_bits f)))
    | _ => None
    end.

  (** LangRef (nofpclass): "If the value is a floating-point class indicated
      by the nofpclass test mask, a poison value is passed or returned
      instead."  It applies to floating-point values, vectors of them, and
      aggregates of those, element by element. *)
  Fixpoint value_nofpclass (mask : Z) (v : dvalue) : dvalue :=
    match v with
    | DVALUE_Base b =>
        match fp_class b with
        | Some c => if (Z.land mask c =? 0)%Z then v else DVALUE_Base DVALUE_Poison
        | None => v
        end
    | DVALUE_Array vec elts => DVALUE_Array vec (List.map (value_nofpclass mask) elts)
    | DVALUE_Struct p fields => DVALUE_Struct p (List.map (value_nofpclass mask) fields)
    end.

  Definition value_attr_nofpclass (attrs : list param_attr) (v : dvalue) : dvalue :=
    match find_option attr_nofpclass attrs with
    | Some mask => value_nofpclass mask v
    | None => v
    end.

  (** The value passed on after the poison-producing attributes. *)
  Definition value_attrs_poison (attrs : list param_attr) (v : dvalue) : dvalue :=
    value_attr_nofpclass attrs
      (value_attr_range attrs (value_attr_align attrs (value_attr_nonnull attrs v))).

  (** Apply a parameter's or return value's attributes to [v], except for
      the memory part of [dereferenceable] (see [apply_attrs]): the value to
      pass on, or UB (reported with [msg]) if [noundef] is violated. *)
  Definition apply_value_attrs (attrs : list param_attr) (msg : string) (v : dvalue)
    : EOU dvalue :=
    let v := value_attrs_poison attrs v in
    if existsb attr_is_noundef attrs && negb (dvalue_well_defined v)
    then raise_ub msg
    else ret v.

  (** ** Metadata without an attribute counterpart

      [!range] on a load, call, or invoke: LangRef "If the loaded or returned
      value is not in the specified range, a poison value is returned
      instead. ... The loaded value or the value returned is known to be in
      the union of the ranges defined by each consecutive pair. ... For
      vector-typed instructions, the range is applied element-wise." *)
  Definition in_metadata_ranges (sz : positive) (x : Z) (ranges : list (int_syntax * int_syntax)) : bool :=
    existsb (fun '(lo, hi) => in_wrapping_range sz x (denote_int_syntax lo) (denote_int_syntax hi)) ranges.

  Definition value_metadata_range_base (ranges : list (int_syntax * int_syntax)) (v : dvalue) : dvalue :=
    match v with
    | DVALUE_Base (DVALUE_I sz x) =>
        if in_metadata_ranges sz (unsigned x) ranges then v else DVALUE_Base DVALUE_Poison
    | _ => v
    end.

  Definition value_metadata_range (ranges : option (list (int_syntax * int_syntax))) (v : dvalue) : dvalue :=
    match ranges, v with
    | None, _ => v
    | Some rs, DVALUE_Array true elts => DVALUE_Array true (List.map (value_metadata_range_base rs) elts)
    | Some rs, _ => value_metadata_range_base rs v
    end.

  (** ** How a call ends

      Check how a call with arguments [args] ended against the function
      attributes [fattrs] (of the callee's definition or of the call site).
      LangRef (noreturn): "This produces undefined behavior at runtime if the
      function ever does dynamically return."  (nounwind): "If the function
      does raise an exception, its runtime behavior is undefined."
      (nocreateundeforpoison): "the result of the function (prior to
      application of return attributes/metadata) will not be undef or poison
      if all arguments are not undef and not poison. Otherwise, it is
      undefined behavior."  So this runs before the return attributes (see
      [check_call_return]). *)
  Definition check_call_result (fattrs : list fn_attr) (msg : string) (args : list dvalue)
             (res : exc + dvalue) : EOU unit :=
    match res with
    | inl _ =>
        if existsb fn_attr_is_nounwind fattrs
        then raise_ub (msg ++ ": unwinding out of a nounwind function.")
        else ret tt
    | inr v =>
        if existsb fn_attr_is_noreturn fattrs
        then raise_ub (msg ++ ": returning from a noreturn function.")
        else if existsb fn_attr_is_nocreateundeforpoison fattrs
                && forallb dvalue_well_defined args && negb (dvalue_well_defined v)
        then raise_ub (msg ++ ": a nocreateundeforpoison function returned undef or poison for well-defined arguments.")
        else ret tt
    end.

  (** ** Calling conventions

      LangRef (Calling Conventions): "The calling convention of any pair of
      dynamic caller/callee must match, or the behavior of the program is
      undefined."  [check_cconv fcc cc fname] compares the convention [fcc]
      of the definition of [fname] with the convention [cc] of a call. *)
  Definition check_cconv (fcc cc : cconv) (fname : string) : EOU unit :=
    if cconv_eqb cc fcc then ret tt
    else raise_ub ("Call to " ++ fname ++ " with a calling convention that does not match its definition.").

  (** ** What may be called

      A call through poison is UB, and so is a call through null: null is
      associated with no object, so it is not a function.  Compare addresses
      only, as for [free(null)].  Any other pointer may be called; whether it
      names a defined function is up to the caller. *)
  Definition check_callee (fv : dvalue) : EOU unit :=
    match fv with
    | DVALUE_Base DVALUE_Poison => raise_ub "call via poison function pointer"
    | DVALUE_Base (DVALUE_Pointer addr) =>
        if (ptr_to_int addr =? ptr_to_int null)%Z
        then raise_ub "call via null function pointer"
        else ret tt
    | _ => raise_error "function call to non-pointer value"
    end.

  (** The integer operands of [llvm.assume] bundles; [None] for poison or a
      non-integer. *)
  Definition bundle_uint (v : dvalue) : option Z :=
    match v with
    | DVALUE_Base (DVALUE_I _ x) => Some (unsigned x)
    | _ => None
    end.

  Definition bundle_sint (v : dvalue) : option Z :=
    match v with
    | DVALUE_Base (DVALUE_I _ x) => Some (signed x)
    | _ => None
    end.

End Attributes.

Section MemoryChecks.
  Context {Pa : Params} {E : Type -> Type}
    `{FailureE -< E} `{UBE -< E} `{OOME -< E} `{MemoryE -< E}.
  #[local] Notation lift := EOU_to_itree.

  (** ** Dereferenceable memory

      [dereferenceable(n)] / [dereferenceable_or_null(n)] and the
      [!dereferenceable] / [!dereferenceable_or_null] load metadata: LangRef
      "the value loaded is known to be dereferenceable at the current program
      point [or null], otherwise the behavior is undefined. The number of
      bytes known to be dereferenceable is specified by the integer value in
      the metadata node."  The [n] bytes are checked by reading them at the
      byte type, which accepts any content: the read raises UB exactly when
      they are not accessible through the pointer (unallocated, freed, out
      of bounds, or another object's provenance). *)
  Definition assert_dereferenceable (or_null : bool) (n : N) (v : dvalue) (msg : string)
    : itree E unit :=
    match v with
    | DVALUE_Base (DVALUE_Pointer p) =>
        if (or_null && (ptr_to_int p =? ptr_to_int null)%Z) || (n =? 0)%N
        then ret tt
        else _ <- load (DTYPE_Array false n (DTYPE_B 8)) v ;; ret tt
    | DVALUE_Base DVALUE_Poison => raiseUB msg
    | _ => raise (msg ++ " (not a pointer)")
    end.

  (** The memory part of the [dereferenceable(n)] and
      [dereferenceable_or_null(n)] attributes, on a pointer.  (A poison value
      under [dereferenceable] is already UB through the [noundef] it
      implies.) *)
  Definition assert_attrs_dereferenceable (attrs : list param_attr) (v : dvalue) (msg : string)
    : itree E unit :=
    match find_option attr_dereferenceable attrs, v with
    | Some (or_null, n), DVALUE_Base (DVALUE_Pointer _) =>
        assert_dereferenceable or_null (Z.to_N (denote_int_syntax n)) v msg
    | _, _ => ret tt
    end.

  (** A load's [!dereferenceable] / [!dereferenceable_or_null] metadata, on
      the loaded value. *)
  Definition assert_load_dereferenceable (md : list (metadata dtyp)) (v : dvalue) (msg : string)
    : itree E unit :=
    match load_metadata_dereferenceable md with
    | Some (or_null, n) => assert_dereferenceable or_null (Z.to_N (denote_int_syntax n)) v msg
    | None => ret tt
    end.

  (** ** Applying attributes

      All of a parameter's or return value's attributes: [apply_value_attrs],
      then the memory part of [dereferenceable]. *)
  Definition apply_attrs (attrs : list param_attr) (msg : string) (v : dvalue)
    : itree E dvalue :=
    v <- lift (apply_value_attrs attrs msg v);;
    assert_attrs_dereferenceable attrs v msg;;
    ret v.

  (** Apply per-argument attribute lists to a list of arguments.  Arguments
      past the end of [attrss] (e.g. variadic ones) have no attributes. *)
  Fixpoint apply_args_attrs (attrss : list (list param_attr)) (msg : string)
    (args : list dvalue) : itree E (list dvalue) :=
    match args with
    | [] => ret []
    | v :: vs =>
        let '(attrs, rest) :=
          match attrss with
          | [] => ([], [])
          | a :: r => (a, r)
          end in
        v' <- apply_attrs attrs msg v;;
        vs' <- apply_args_attrs rest msg vs;;
        ret (v' :: vs')
    end.

  (** The result of a call with arguments [args], after the function
      attributes [fattrs], the [!range] metadata [ranges], and the
      return-value attributes [ret_attrs] (of the callee's definition or of
      the call site): UB if [check_call_result] fails, otherwise the unwind
      unchanged or the returned value passed through [value_metadata_range]
      and [apply_attrs].  [loc] (a location or a function name) prefixes the
      UB messages. *)
  Definition check_call_return (fattrs : list fn_attr) (ret_attrs : list param_attr)
    (ranges : option (list (int_syntax * int_syntax))) (loc : string)
    (args : list dvalue) (res : exc + dvalue) : itree E (exc + dvalue) :=
    lift (check_call_result fattrs loc args res);;
    match res with
    | inl _ => ret res
    | inr v =>
        v' <- apply_attrs ret_attrs (loc ++ " return value violates noundef.")
                (value_metadata_range ranges v);;
        ret (inr v')
    end.

  (** ** Operand bundles of [llvm.assume]

      LangRef (Assume Operand Bundles): "if any of the provided guarantees
      are violated at runtime the behavior is undefined."  An
      [assume_bundle_check] checks the guarantee a bundle states about its
      (already evaluated) operands; the string locates its error messages.
      [denote_operand_bundles] (Denotation.v) evaluates the operands and
      runs the check that [bundle_check] picks. *)
  Definition assume_bundle_check : Type := string -> list dvalue -> itree E unit.

  Definition assume_violated {A} (loc tag : string) : itree E A :=
    raiseUB (loc ++ ": llvm.assume operand bundle """ ++ tag ++ """ is violated.").

  Definition assume_malformed {A} (loc tag : string) : itree E A :=
    raise (loc ++ ": malformed llvm.assume operand bundle """ ++ tag ++ """.").

  (* ["nonnull"(ptr %p)]: "Equivalent to nonnull on %p". *)
  Definition assume_nonnull : assume_bundle_check :=
    fun loc vs =>
      match vs with
      | [p] =>
          match dvalue_ptr_address p with
          | Some a => if (a =? 0)%Z then assume_violated loc "nonnull" else ret tt
          | None => assume_violated loc "nonnull"
          end
      | _ => assume_malformed loc "nonnull"
      end.

  (* ["noundef"(%v)]: "Equivalent to noundef on %v". *)
  Definition assume_noundef : assume_bundle_check :=
    fun loc vs =>
      match vs with
      | [v] => if dvalue_well_defined v then ret tt else assume_violated loc "noundef"
      | _ => assume_malformed loc "noundef"
      end.

  (* ["align"(ptr %p, i64 %align[, i64 %offset])]: "Equivalent to align(%align)
     on %p, or %p - %offset if the %offset argument exists, except that %align
     may be a non-power-of-two alignment (including a zero alignment). If
     %align is not a power of two, the pointer value must be all-zero." *)
  Definition assume_align : assume_bundle_check :=
    fun loc vs =>
      match vs with
      | p :: al :: off =>
          let offset := match off with
                        | [] => Some 0%Z
                        | [o] => bundle_sint o
                        | _ => None
                        end in
          match dvalue_ptr_address p, bundle_uint al, offset with
          | Some a, Some n, Some o =>
              if (if is_power_of_two n then ((a - o) mod n) =? 0 else a =? 0)%Z
              then ret tt else assume_violated loc "align"
          | _, _, _ => assume_violated loc "align"
          end
      | _ => assume_malformed loc "align"
      end.

  (* ["dereferenceable"(ptr %p, i64 %size)]: "Equivalent to
     dereferenceable(%size) on %p, except that %size may also be zero, in
     which case the bundle doesn't imply nonnull"; and likewise
     ["dereferenceable_or_null"]. *)
  Definition assume_dereferenceable (or_null : bool) : assume_bundle_check :=
    fun loc vs =>
      let tag := if or_null then "dereferenceable_or_null" else "dereferenceable" in
      match vs with
      | [p; sz] =>
          match dvalue_ptr_address p, bundle_uint sz with
          | Some _, Some n =>
              if (n =? 0)%Z then ret tt
              else assert_dereferenceable or_null (Z.to_N n) p
                     (loc ++ ": llvm.assume operand bundle """ ++ tag ++ """ is violated.")
          | _, _ => assume_violated loc tag
          end
      | _ => assume_malformed loc tag
      end.

  (** The guarantees an [llvm.assume] bundle can state, by tag.  To support
      another kind of assumption, add its check here and its case to
      [I2F_assume_bundle_checks] (Theory/I2F/I2F_denotation.v).  Tags not
      listed, such as ["separate_storage"] (an aliasing guarantee, left to
      the provenance model), ["cold"], and ["ignore"], are not checked. *)
  Definition assume_bundle_checks : list (string * assume_bundle_check) :=
    [ ("nonnull", assume_nonnull);
      ("noundef", assume_noundef);
      ("align", assume_align);
      ("dereferenceable", assume_dereferenceable false);
      ("dereferenceable_or_null", assume_dereferenceable true) ].

  Definition is_llvm_assume (f : exp dtyp) : bool :=
    match intrinsic_exp f with
    | Some s => String.eqb s "llvm.assume"
    | None => false
    end.

  (* The check a bundle of a call to [f] gets, if any. *)
  Definition bundle_check (f : exp dtyp) (tag : string) : option assume_bundle_check :=
    if is_llvm_assume f
    then option_map snd (find (fun '(t, _) => String.eqb t tag) assume_bundle_checks)
    else None.

End MemoryChecks.
