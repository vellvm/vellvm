(* begin hide *)

From Stdlib Require Import
  Bool.Bool.

From Vellvm Require Import
  Numeric
  Utils
  Syntax
  Params
  EOU
  VellvmIntegers
  LLVMEvents
  DynamicValues.

Open Scope string_scope.

(* end hide *)

(** * Value-level checks imposed by LLVM annotations

    The pure (EOU) checks that annotations on instructions and functions
    impose on the values flowing through them: explicit alignments, the
    value attributes of parameters and return values (and the load metadata
    that acts like them), the [noreturn] / [nounwind] function attributes,
    and what may be called as a function.  [Denotation.v] lifts them into
    the itree semantics at the points where LangRef applies them.
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

      LangRef: [nonnull], [align N], and [range(a, b)] turn a violating value
      into poison ("poison value is returned or passed instead"); [noundef]
      makes a value that is not well defined immediate UB.  So [nonnull]
      without [noundef] passes poison on, while [nonnull noundef] on null is
      UB.  [dereferenceable(n)] "implies nonnull in addrspace(0)" and "implies
      noundef"; only those two consequences are checked here (that [n] bytes
      are accessible needs the memory model).

      Only attributes that can be checked from the value itself are handled.
      Vectors of pointers ([align]/[nonnull] per lane) and [nofpclass] (not
      parsed) are not yet covered. *)

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

  (** The value passed on after the poison-producing attributes. *)
  Definition value_attrs_poison (attrs : list param_attr) (v : dvalue) : dvalue :=
    value_attr_range attrs (value_attr_align attrs (value_attr_nonnull attrs v)).

  (** Apply a parameter's or return value's attributes to [v]: the value to
      pass on, or UB (reported with [msg]) if [noundef] is violated. *)
  Definition apply_value_attrs (attrs : list param_attr) (msg : string) (v : dvalue)
    : EOU dvalue :=
    let v := value_attrs_poison attrs v in
    if existsb attr_is_noundef attrs && negb (dvalue_well_defined v)
    then raise_ub msg
    else ret v.

  (** Apply per-argument attribute lists to a list of arguments.  Arguments
      past the end of [attrss] (e.g. variadic ones) have no attributes. *)
  Fixpoint apply_args_attrs (attrss : list (list param_attr)) (msg : string)
    (args : list dvalue) : EOU (list dvalue) :=
    match args with
    | [] => ret []
    | v :: vs =>
        let '(attrs, rest) :=
          match attrss with
          | [] => ([], [])
          | a :: r => (a, r)
          end in
        v' <- apply_value_attrs attrs msg v;;
        vs' <- apply_args_attrs rest msg vs;;
        ret (v' :: vs')
    end.

  (** ** How a call ends

      Check how a call ended against the [noreturn] / [nounwind] function
      attributes [fattrs] (of the callee's definition or of the call site).
      LangRef (noreturn): "This produces undefined behavior at runtime if the
      function ever does dynamically return."  (nounwind): "If the function
      does raise an exception, its runtime behavior is undefined." *)
  Definition check_call_result (fattrs : list fn_attr) (msg : string) (res : exc + dvalue)
    : EOU unit :=
    match res with
    | inl _ =>
        if existsb fn_attr_is_nounwind fattrs
        then raise_ub (msg ++ ": unwinding out of a nounwind function.")
        else ret tt
    | inr _ =>
        if existsb fn_attr_is_noreturn fattrs
        then raise_ub (msg ++ ": returning from a noreturn function.")
        else ret tt
    end.

  (** The result of a call after the function attributes [fattrs] and the
      return-value attributes [ret_attrs] (of the callee's definition or of
      the call site): UB if [check_call_result] fails, otherwise the unwind
      unchanged or the returned value passed through [apply_value_attrs].
      [loc] (a location or a function name) prefixes the UB messages. *)
  Definition check_call_return (fattrs : list fn_attr) (ret_attrs : list param_attr)
    (loc : string) (res : exc + dvalue) : EOU (exc + dvalue) :=
    check_call_result fattrs loc res;;
    match res with
    | inl _ => ret res
    | inr v =>
        v' <- apply_value_attrs ret_attrs (loc ++ " return value violates noundef.") v;;
        ret (inr v')
    end.

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

End Attributes.
