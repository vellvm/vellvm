(* begin hide *)
From Vellvm Require Import
  Utilities
  Syntax.
Open Scope Z.

(* The block printers below are defined in three variants sharing the
   prefix [label ':' ...] (full / no-phis / no-phis-no-code). The
   prefix overlap is benign because all three are [only printing] and
   the printer dispatches via RHS specificity. Rocq's prefix-conflict
   warning is parse-direction-only and re-fires at every [Import
   VIR_Notations] site, so we suppress it file-wide. *)
Set Warnings "-notation-incompatible-prefix".
(* end hide *)

(** * Surface syntax for VIR
    A VIR program, even a trivial one, is quite a lousy piece of syntax.
    We define here a series of notations allowing us to recover a LLVM-like surface syntax.
    The purpose is to ease readability of proof goals while reasoning interactively.
    As such, the notation are display-only, and hence can be very liberal.
    Note that we currently completely hide some of the type annotations. That might be
    a bit too audacious.
    This file is quite experimental.
 *)

Module VIR_Notations.

  (* Step 2: the bulk of the notations now live in custom entries
     (vir_typ, vir_exp, vir_instr, vir_term, vir_code, vir_phi, vir_phis).
     Custom entries have their own parser namespace, so the keywords
     reused by LLVM (true/false, eq/ugt/ult, op/load/store/...) no
     longer collide with constr — no notation-override warnings remain.

     To inspect a subterm in surface syntax, wrap it with the matching
     bracket:
         [[ty t]]    — typ or dtyp
         [[exp e]]   — expression
         [[instr i]] — instruction
         [[term t]]  — terminator
         [[code c]]  — list of instructions (one per line)
         [[phi p]]   — single phi-node entry
         [[phis ps]] — list of phi-nodes (one per line)
     Auto-dispatch (so terms of those types print in surface syntax
     without a bracket) is deferred to a later step.

     Block and definition printers ([func ... :=], [label : phis code
     term]) remain at constr level: their LHS shapes are unique enough
     that they don't conflict with stdlib. *)

  Declare Custom Entry vir_typ.
  Declare Custom Entry vir_exp.
  Declare Custom Entry vir_instr.
  Declare Custom Entry vir_term.
  Declare Custom Entry vir_code.
  Declare Custom Entry vir_phi.
  Declare Custom Entry vir_phis.
  Declare Custom Entry vir_idx_list.    (* GEP indices: list (T * exp) *)
  Declare Custom Entry vir_phi_args.    (* phi incoming: list (block_id * exp) *)
  Declare Custom Entry vir_arm_list.    (* switch arms: list (tint_literal * block_id) *)
  Declare Custom Entry vir_label_list.  (* indirectbr targets: list block_id *)
  Declare Custom Entry vir_anns.        (* annotation list: list annotation *)
  Declare Custom Entry vir_fmf.         (* fast-math flag list: list fast_math *)
  Declare Custom Entry vir_typ_list.    (* list of types: function args, struct fields *)
  Declare Custom Entry vir_def_list.    (* list of definitions: m_definitions *)
  Declare Custom Entry vir_decl_list.   (* list of declarations: m_declarations *)
  Declare Custom Entry vir_global_list. (* list of globals: m_globals *)
  Declare Custom Entry vir_tle_list.    (* list of toplevel entries *)
  Declare Custom Entry vir_block_list.  (* list of blocks: ocfg / cfg.blks *)

  (** * Display prefixes — entry into surface-syntax sublanguages.

      Auto-firing display brackets keyed by the inner constructor: when
      Rocq prints a term, it enters the matching custom entry through
      one of these prefixes. The inner entry's rules pattern-match on
      specific constructors (EXP_*, INSTR_*, TERM_*, ...) so a [Z]-typed
      [5] still prints as [5], not as [%e 5].

        %t  typ / dtyp        %e  exp
        %i  instr-triple      %T  term-triple
        %p  phi-triple

      No prefix for code lists or phi lists: their inner notations only
      pattern-match on bare [cons], which would over-fire on every list
      in scope (definitions, function args, …). The list entries
      [vir_code] and [vir_phis] are still useful — they fire from inside
      the [block] notation, which dispatches its [code] / [phis] fields
      explicitly. They just don't get a top-level shortcut.

      Display-only; users do not type [%e ...]. To opt out, use
      [Set Printing All]. *)
  Notation "'%t' t" := t (t custom vir_typ   at level 99, only printing, at level 0).
  Notation "'%e' e" := e (e custom vir_exp   at level 99, only printing, at level 0).
  Notation "'%i' i" := i (i custom vir_instr at level 99, only printing, at level 0).
  Notation "'%T' t" := t (t custom vir_term  at level 99, only printing, at level 0).
  Notation "'%p' p" := p (p custom vir_phi   at level 99, only printing, at level 0).

  (** * Coercions (still useful at constr level) *)
  Coercion Name : string >-> raw_id.
  Coercion Anon : int_ast >-> raw_id.

  (** * vir_typ — types (typ and dtyp) *)
  Notation "( t )" := t
    (in custom vir_typ at level 0, t custom vir_typ at level 99, only printing).
  Notation "{ t }" := t
    (in custom vir_typ at level 0, t constr, only printing).
  Notation "x" := x
    (in custom vir_typ at level 0, x ident, only printing).

  Notation "'i' n" := (DTYPE_I n)
    (in custom vir_typ at level 5, n constr at level 0, only printing,
     format "'i' n").
  Notation "'i' n" := (TYPE_I n)
    (in custom vir_typ at level 5, n constr at level 0, only printing,
     format "'i' n").
  (** Pointer types. [DTYPE_Pointer] is nullary (post-opaque dynamic
      types); [TYPE_Pointer] carries an [option typ] — [Some t] is a
      typed pointer ([t *]), [None] is opaque ([ptr]). The previous
      [Notation "'*'" := TYPE_Pointer] only matched the bare
      constructor and rendered typed pointers as ugly [* (Some inner)]. *)
  Notation "'ptr'" := DTYPE_Pointer       (in custom vir_typ at level 5, only printing).
  Notation "'ptr'" := (TYPE_Pointer None) (in custom vir_typ at level 5, only printing).
  Notation "t '*'" := (TYPE_Pointer (Some t))
    (in custom vir_typ at level 5, t custom vir_typ at level 5, only printing,
     format "t '*'").
  Notation "'void'" := DTYPE_Void    (in custom vir_typ at level 5, only printing).
  Notation "'void'" := TYPE_Void     (in custom vir_typ at level 5, only printing).

  (** Floating-point variants. Each surface keyword maps to both the
      [TYPE_FP] (static) and [DTYPE_FP] (dynamic) wrapping of the
      corresponding [floating_point_variant]. *)
  Notation "'half'"      := (TYPE_FP  FP_half)      (in custom vir_typ at level 5, only printing).
  Notation "'half'"      := (DTYPE_FP FP_half)      (in custom vir_typ at level 5, only printing).
  Notation "'bfloat'"    := (TYPE_FP  FP_bfloat)    (in custom vir_typ at level 5, only printing).
  Notation "'bfloat'"    := (DTYPE_FP FP_bfloat)    (in custom vir_typ at level 5, only printing).
  Notation "'float'"     := (TYPE_FP  FP_float)     (in custom vir_typ at level 5, only printing).
  Notation "'float'"     := (DTYPE_FP FP_float)     (in custom vir_typ at level 5, only printing).
  Notation "'double'"    := (TYPE_FP  FP_double)    (in custom vir_typ at level 5, only printing).
  Notation "'double'"    := (DTYPE_FP FP_double)    (in custom vir_typ at level 5, only printing).
  Notation "'fp128'"     := (TYPE_FP  FP_fp128)     (in custom vir_typ at level 5, only printing).
  Notation "'fp128'"     := (DTYPE_FP FP_fp128)     (in custom vir_typ at level 5, only printing).
  Notation "'x86_fp80'"  := (TYPE_FP  FP_x86_fp80)  (in custom vir_typ at level 5, only printing).
  Notation "'x86_fp80'"  := (DTYPE_FP FP_x86_fp80)  (in custom vir_typ at level 5, only printing).
  Notation "'ppc_fp128'" := (TYPE_FP  FP_ppc_fp128) (in custom vir_typ at level 5, only printing).
  Notation "'ppc_fp128'" := (DTYPE_FP FP_ppc_fp128) (in custom vir_typ at level 5, only printing).

  (** Other simple atomic types. *)
  Notation "'iptr'"     := TYPE_IPTR     (in custom vir_typ at level 5, only printing).
  Notation "'label'"    := TYPE_Label    (in custom vir_typ at level 5, only printing).
  Notation "'label'"    := DTYPE_Label   (in custom vir_typ at level 5, only printing).
  Notation "'token'"    := TYPE_Token    (in custom vir_typ at level 5, only printing).
  Notation "'metadata'" := TYPE_Metadata (in custom vir_typ at level 5, only printing).
  Notation "'opaque'"   := TYPE_Opaque   (in custom vir_typ at level 5, only printing).

  (** Array, vector. LLVM IR uses [[N x T]] for arrays and [<N x T>]
      for vectors. *)
  Notation "'[' sz 'x' t ']'" := (TYPE_Array sz t)
    (in custom vir_typ at level 5,
     sz constr at level 0, t custom vir_typ at level 99,
     only printing).
  Notation "'[' sz 'x' t ']'" := (DTYPE_Array sz t)
    (in custom vir_typ at level 5,
     sz constr at level 0, t custom vir_typ at level 99,
     only printing).
  Notation "'<' sz 'x' t '>'" := (TYPE_Vector sz t)
    (in custom vir_typ at level 5,
     sz constr at level 0, t custom vir_typ at level 99,
     only printing).
  Notation "'<' sz 'x' t '>'" := (DTYPE_Vector sz t)
    (in custom vir_typ at level 5,
     sz constr at level 0, t custom vir_typ at level 99,
     only printing).

  (** Struct, packed struct. Use [{| ... |}] for plain struct (we cannot
      reuse plain [{ ... }] without colliding with the constr-escape) and
      [<{ ... }>] for packed (matching LLVM IR). *)
  Notation "'{|' '|}'" := (TYPE_Struct nil)
    (in custom vir_typ at level 5, only printing).
  Notation "'{|' '|}'" := (DTYPE_Struct nil)
    (in custom vir_typ at level 5, only printing).
  Notation "'{|' fields '|}'" := (TYPE_Struct fields)
    (in custom vir_typ at level 5,
     fields custom vir_typ_list at level 99,
     only printing).
  Notation "'{|' fields '|}'" := (DTYPE_Struct fields)
    (in custom vir_typ at level 5,
     fields custom vir_typ_list at level 99,
     only printing).
  Notation "'<{' '}>'" := (TYPE_Packed_struct nil)
    (in custom vir_typ at level 5, only printing).
  Notation "'<{' '}>'" := (DTYPE_Packed_struct nil)
    (in custom vir_typ at level 5, only printing).
  Notation "'<{' fields '}>'" := (TYPE_Packed_struct fields)
    (in custom vir_typ at level 5,
     fields custom vir_typ_list at level 99,
     only printing).
  Notation "'<{' fields '}>'" := (DTYPE_Packed_struct fields)
    (in custom vir_typ at level 5,
     fields custom vir_typ_list at level 99,
     only printing).

  (** Function types. LLVM IR: [ret (arg, ..., arg)] (vararg adds [, ...]).
      Empty-args specific shape avoids dispatching [nil] through
      [vir_typ_list], which would render as [{ [] }]. *)
  Notation "ret '(' ')'" := (TYPE_Function ret nil false)
    (in custom vir_typ at level 30,
     ret custom vir_typ at level 99,
     only printing).
  Notation "ret '(' args ')'" := (TYPE_Function ret args false)
    (in custom vir_typ at level 30,
     ret custom vir_typ at level 99,
     args custom vir_typ_list at level 99,
     only printing).
  Notation "ret '(' '...' ')'" := (TYPE_Function ret nil true)
    (in custom vir_typ at level 30,
     ret custom vir_typ at level 99,
     only printing).
  Notation "ret '(' args ',' '...' ')'" := (TYPE_Function ret args true)
    (in custom vir_typ at level 30,
     ret custom vir_typ at level 99,
     args custom vir_typ_list at level 99,
     only printing).

  (** Identified (named) types. *)
  Notation "'%' x" := (TYPE_Identified (ID_Local x))
    (in custom vir_typ at level 5, x constr at level 0, only printing,
     format "'%' x").
  Notation "'@' x" := (TYPE_Identified (ID_Global x))
    (in custom vir_typ at level 5, x constr at level 0, only printing,
     format "'@' x").

  (** vir_typ_list — recursive printer for [list typ] / [list dtyp].
      Used by struct fields and function arg lists. Comma-separated,
      one line. *)
  Notation "( l )" := l
    (in custom vir_typ_list at level 0, l custom vir_typ_list at level 99, only printing).
  Notation "{ l }" := l
    (in custom vir_typ_list at level 0, l constr, only printing).
  Notation "t ',' .. ',' u" :=
    (cons t .. (cons u nil) ..)
    (in custom vir_typ_list at level 99,
     t custom vir_typ at level 99,
     u custom vir_typ at level 99,
     only printing,
     format "t ',' .. ',' u").

  (** * vir_exp — expressions *)
  Notation "( e )" := e
    (in custom vir_exp at level 0, e custom vir_exp at level 99, only printing).
  Notation "{ e }" := e
    (in custom vir_exp at level 0, e constr, only printing).

  (** ** Identifiers. We fold [EXP_Ident] into the keyed rules directly,
        so a free [EXP_Ident i] in a goal prints as [% x] / [@ x] without
        an intermediate wrapper. Custom entries forbid two bare-LHS rules
        at the same level with different arg specs; one constructor must
        win, and the [ident] rule is the natural one for free variables. *)
  Notation "'%' x" := (EXP_Ident (ID_Local x))
    (in custom vir_exp at level 0, x constr at level 0, only printing,
     format "'%' x").
  Notation "'@' x" := (EXP_Ident (ID_Global x))
    (in custom vir_exp at level 0, x constr at level 0, only printing,
     format "'@' x").

  (** ** Constants. Only one bare-LHS rule survives per (entry, level);
        we keep [EXP_Integer] since integer literals dominate goals.
        Other constants (bool, float, cstring, identifiers) fall back to
        the constr-escape [{ ... }] when they appear unwrapped.

        Two flavours of [EXP_Integer] appear in real terms: the bare
        [int_syntax] one (constructed in Rocq) and the wrapped form
        [EXP_Integer (Z.to_num_int n)] (produced by the parser frontend
        and pervasive after [cbn]). Adding the wrapped variant first
        lets Rocq pick the more-specific RHS for parser-built terms,
        falling back to the bare rule otherwise. *)
  Notation "n" := (EXP_Integer (Z.to_num_int n))
    (in custom vir_exp at level 0, n constr at level 0, only printing).
  Notation "n" := (EXP_Integer n)
    (in custom vir_exp at level 0, n constr at level 0, only printing).
  Notation "'null'"            := EXP_Null             (in custom vir_exp at level 0, only printing).
  Notation "'zeroinitializer'" := EXP_Zero_initializer (in custom vir_exp at level 0, only printing).
  (** Booleans: each maps to the literal value-keyed [EXP_Bool] case.
      No bare-LHS conflict because the LHS is a literal, not a metavar. *)
  Notation "'true'"  := (EXP_Bool true)  (in custom vir_exp at level 0, only printing).
  Notation "'false'" := (EXP_Bool false) (in custom vir_exp at level 0, only printing).
  (** C-string literals. LLVM IR writes [c"hello"]; we space the [c]. *)
  Notation "'c' s" := (EXP_Cstring s)
    (in custom vir_exp at level 0, s constr at level 0, only printing).

  (** ** Integer arithmetic.
        Parametric-flag forms have been dropped (they only fire when the
        nuw/nsw booleans are bound variables, which never happens in
        concrete goals). Each constructor gets one notation per
        nuw/nsw combination it actually permits. *)

  Notation "'add' e ',' f" :=
    (OP_IBinop (Add false false) _ e f) (in custom vir_exp at level 20, only printing).
  Notation "'add' 'nuw' e ',' f" :=
    (OP_IBinop (Add true false) _ e f)  (in custom vir_exp at level 20, only printing).
  Notation "'add' 'nsw' e ',' f" :=
    (OP_IBinop (Add false true) _ e f)  (in custom vir_exp at level 20, only printing).
  Notation "'add' 'nuw' 'nsw' e ',' f" :=
    (OP_IBinop (Add true true) _ e f)   (in custom vir_exp at level 20, only printing).

  Notation "'sub' e ',' f" :=
    (OP_IBinop (Sub false false) _ e f) (in custom vir_exp at level 20, only printing).
  Notation "'sub' 'nuw' e ',' f" :=
    (OP_IBinop (Sub true false) _ e f)  (in custom vir_exp at level 20, only printing).
  Notation "'sub' 'nsw' e ',' f" :=
    (OP_IBinop (Sub false true) _ e f)  (in custom vir_exp at level 20, only printing).
  Notation "'sub' 'nuw' 'nsw' e ',' f" :=
    (OP_IBinop (Sub true true) _ e f)   (in custom vir_exp at level 20, only printing).

  Notation "'mul' e ',' f" :=
    (OP_IBinop (Mul false false) _ e f) (in custom vir_exp at level 20, only printing).
  Notation "'mul' 'nuw' e ',' f" :=
    (OP_IBinop (Mul true false) _ e f)  (in custom vir_exp at level 20, only printing).
  Notation "'mul' 'nsw' e ',' f" :=
    (OP_IBinop (Mul false true) _ e f)  (in custom vir_exp at level 20, only printing).
  Notation "'mul' 'nuw' 'nsw' e ',' f" :=
    (OP_IBinop (Mul true true) _ e f)   (in custom vir_exp at level 20, only printing).

  Notation "'shl' e ',' f" :=
    (OP_IBinop (Shl false false) _ e f) (in custom vir_exp at level 20, only printing).
  Notation "'shl' 'nuw' e ',' f" :=
    (OP_IBinop (Shl true false) _ e f)  (in custom vir_exp at level 20, only printing).
  Notation "'shl' 'nsw' e ',' f" :=
    (OP_IBinop (Shl false true) _ e f)  (in custom vir_exp at level 20, only printing).
  Notation "'shl' 'nuw' 'nsw' e ',' f" :=
    (OP_IBinop (Shl true true) _ e f)   (in custom vir_exp at level 20, only printing).

  Notation "'udiv' e ',' f" :=
    (OP_IBinop (UDiv false) _ e f)       (in custom vir_exp at level 20, only printing).
  Notation "'udiv' 'exact' e ',' f" :=
    (OP_IBinop (UDiv true) _ e f)        (in custom vir_exp at level 20, only printing).

  Notation "'sdiv' e ',' f" :=
    (OP_IBinop (SDiv false) _ e f)       (in custom vir_exp at level 20, only printing).
  Notation "'sdiv' 'exact' e ',' f" :=
    (OP_IBinop (SDiv true) _ e f)        (in custom vir_exp at level 20, only printing).

  Notation "'lshr' e ',' f" :=
    (OP_IBinop (LShr false) _ e f)       (in custom vir_exp at level 20, only printing).
  Notation "'lshr' 'exact' e ',' f" :=
    (OP_IBinop (LShr true) _ e f)        (in custom vir_exp at level 20, only printing).

  Notation "'ashr' e ',' f" :=
    (OP_IBinop (AShr false) _ e f)       (in custom vir_exp at level 20, only printing).
  Notation "'ashr' 'exact' e ',' f" :=
    (OP_IBinop (AShr true) _ e f)        (in custom vir_exp at level 20, only printing).

  Notation "'urem' e ',' f" := (OP_IBinop URem _ e f) (in custom vir_exp at level 20, only printing).
  Notation "'srem' e ',' f" := (OP_IBinop SRem _ e f) (in custom vir_exp at level 20, only printing).
  Notation "'and' e ',' f"  := (OP_IBinop And _ e f)  (in custom vir_exp at level 20, only printing).
  Notation "'or' e ',' f"   := (OP_IBinop Or _ e f)   (in custom vir_exp at level 20, only printing).
  Notation "'xor' e ',' f"  := (OP_IBinop Xor _ e f)  (in custom vir_exp at level 20, only printing).

  (** ** Integer comparison. [OP_ICmp] takes 5 args: [(samesign:bool)
        (cmp:icmp) (t:T) (v1:exp) (v2:exp)]. The [samesign] flag is
        wildcarded — flagged variants ([icmp samesign eq …]) can be
        added later when needed. The previous notations had only 4
        args and never fired. *)
  Notation "'icmp' 'eq'  e ',' f" := (OP_ICmp _ Eq  _ e f) (in custom vir_exp at level 20, only printing).
  Notation "'icmp' 'ne'  e ',' f" := (OP_ICmp _ Ne  _ e f) (in custom vir_exp at level 20, only printing).
  Notation "'icmp' 'ugt' e ',' f" := (OP_ICmp _ Ugt _ e f) (in custom vir_exp at level 20, only printing).
  Notation "'icmp' 'uge' e ',' f" := (OP_ICmp _ Uge _ e f) (in custom vir_exp at level 20, only printing).
  Notation "'icmp' 'ult' e ',' f" := (OP_ICmp _ Ult _ e f) (in custom vir_exp at level 20, only printing).
  Notation "'icmp' 'ule' e ',' f" := (OP_ICmp _ Ule _ e f) (in custom vir_exp at level 20, only printing).
  Notation "'icmp' 'sgt' e ',' f" := (OP_ICmp _ Sgt _ e f) (in custom vir_exp at level 20, only printing).
  Notation "'icmp' 'sge' e ',' f" := (OP_ICmp _ Sge _ e f) (in custom vir_exp at level 20, only printing).
  Notation "'icmp' 'slt' e ',' f" := (OP_ICmp _ Slt _ e f) (in custom vir_exp at level 20, only printing).
  Notation "'icmp' 'sle' e ',' f" := (OP_ICmp _ Sle _ e f) (in custom vir_exp at level 20, only printing).

  (** ** Float arithmetic. [OP_FBinop] takes [(fop, fm:list fast_math,
        t, v1, v2)] — five args. The previous notations had only four,
        so they never fired. The [fm] flag list is wildcarded here;
        flagged fp-binops can be added later via [vir_fmf]. *)
  Notation "'fadd' e ',' f" := (OP_FBinop FAdd _ _ e f) (in custom vir_exp at level 20, only printing).
  Notation "'fsub' e ',' f" := (OP_FBinop FSub _ _ e f) (in custom vir_exp at level 20, only printing).
  Notation "'fmul' e ',' f" := (OP_FBinop FMul _ _ e f) (in custom vir_exp at level 20, only printing).
  Notation "'fdiv' e ',' f" := (OP_FBinop FDiv _ _ e f) (in custom vir_exp at level 20, only printing).
  Notation "'frem' e ',' f" := (OP_FBinop FRem _ _ e f) (in custom vir_exp at level 20, only printing).

  (** ** Float comparison. Now safe to use [true]/[false] as keywords —
        we're inside a custom entry, not constr. *)
  Notation "'fcmp' 'false'"        := (OP_FCmp FFalse _ _ _) (in custom vir_exp at level 20, only printing).
  Notation "'fcmp' 'true'"         := (OP_FCmp FTrue _ _ _)  (in custom vir_exp at level 20, only printing).
  Notation "'fcmp' 'oeq' e ',' f"  := (OP_FCmp FOeq _ e f)   (in custom vir_exp at level 20, only printing).
  Notation "'fcmp' 'ogt' e ',' f"  := (OP_FCmp FOgt _ e f)   (in custom vir_exp at level 20, only printing).
  Notation "'fcmp' 'oge' e ',' f"  := (OP_FCmp FOge _ e f)   (in custom vir_exp at level 20, only printing).
  Notation "'fcmp' 'olt' e ',' f"  := (OP_FCmp FOlt _ e f)   (in custom vir_exp at level 20, only printing).
  Notation "'fcmp' 'ole' e ',' f"  := (OP_FCmp FOle _ e f)   (in custom vir_exp at level 20, only printing).
  Notation "'fcmp' 'one' e ',' f"  := (OP_FCmp FOne _ e f)   (in custom vir_exp at level 20, only printing).
  Notation "'fcmp' 'ord' e ',' f"  := (OP_FCmp FOrd _ e f)   (in custom vir_exp at level 20, only printing).
  Notation "'fcmp' 'uno' e ',' f"  := (OP_FCmp FUno _ e f)   (in custom vir_exp at level 20, only printing).
  Notation "'fcmp' 'ueq' e ',' f"  := (OP_FCmp FUeq _ e f)   (in custom vir_exp at level 20, only printing).
  Notation "'fcmp' 'ugt' e ',' f"  := (OP_FCmp FUgt _ e f)   (in custom vir_exp at level 20, only printing).
  Notation "'fcmp' 'uge' e ',' f"  := (OP_FCmp FUge _ e f)   (in custom vir_exp at level 20, only printing).
  Notation "'fcmp' 'ult' e ',' f"  := (OP_FCmp FUlt _ e f)   (in custom vir_exp at level 20, only printing).
  Notation "'fcmp' 'ule' e ',' f"  := (OP_FCmp FUle _ e f)   (in custom vir_exp at level 20, only printing).
  Notation "'fcmp' 'une' e ',' f"  := (OP_FCmp FUne _ e f)   (in custom vir_exp at level 20, only printing).

  (** ** Conversions.
        LLVM surface form: [<op> <from-type> <value> to <to-type>]. The
        AST mirrors this with [OP_Conversion conv τfrom v τto]. Variants
        with bool / list flags are enumerated for the boolean cases and
        wildcarded for [Fptrunc]/[Fpext] flag lists (which would
        otherwise multiply rules unbounded). *)
  Notation "'trunc' τfrom v 'to' τto" :=
    (OP_Conversion (Trunc false false) τfrom v τto)
    (in custom vir_exp at level 20,
     τfrom custom vir_typ at level 99, v custom vir_exp at level 99,
     τto   custom vir_typ at level 99, only printing).
  Notation "'trunc' 'nuw' τfrom v 'to' τto" :=
    (OP_Conversion (Trunc true false) τfrom v τto)
    (in custom vir_exp at level 20,
     τfrom custom vir_typ at level 99, v custom vir_exp at level 99,
     τto   custom vir_typ at level 99, only printing).
  Notation "'trunc' 'nsw' τfrom v 'to' τto" :=
    (OP_Conversion (Trunc false true) τfrom v τto)
    (in custom vir_exp at level 20,
     τfrom custom vir_typ at level 99, v custom vir_exp at level 99,
     τto   custom vir_typ at level 99, only printing).
  Notation "'trunc' 'nuw' 'nsw' τfrom v 'to' τto" :=
    (OP_Conversion (Trunc true true) τfrom v τto)
    (in custom vir_exp at level 20,
     τfrom custom vir_typ at level 99, v custom vir_exp at level 99,
     τto   custom vir_typ at level 99, only printing).

  Notation "'zext' τfrom v 'to' τto" :=
    (OP_Conversion (Zext false) τfrom v τto)
    (in custom vir_exp at level 20,
     τfrom custom vir_typ at level 99, v custom vir_exp at level 99,
     τto   custom vir_typ at level 99, only printing).
  Notation "'zext' 'nneg' τfrom v 'to' τto" :=
    (OP_Conversion (Zext true) τfrom v τto)
    (in custom vir_exp at level 20,
     τfrom custom vir_typ at level 99, v custom vir_exp at level 99,
     τto   custom vir_typ at level 99, only printing).

  Notation "'sext' τfrom v 'to' τto" :=
    (OP_Conversion Sext τfrom v τto)
    (in custom vir_exp at level 20,
     τfrom custom vir_typ at level 99, v custom vir_exp at level 99,
     τto   custom vir_typ at level 99, only printing).

  (** Two shapes per fp-conversion: empty flags (LLVM displays no
      modifier) and non-empty flags (in brackets, dispatched through
      [vir_fmf]). The brackets disambiguate the parser — without them,
      the empty-flags and with-flags rules share a prefix [fptrunc],
      and Rocq emits a parse-conflict warning even for [only printing]
      notations. *)
  Notation "'fptrunc' τfrom v 'to' τto" :=
    (OP_Conversion (Fptrunc []) τfrom v τto)
    (in custom vir_exp at level 20,
     τfrom custom vir_typ at level 99, v custom vir_exp at level 99,
     τto   custom vir_typ at level 99, only printing).
  Notation "'fptrunc' '[' fmf ']' τfrom v 'to' τto" :=
    (OP_Conversion (Fptrunc fmf) τfrom v τto)
    (in custom vir_exp at level 20,
     fmf custom vir_fmf at level 99,
     τfrom custom vir_typ at level 99, v custom vir_exp at level 99,
     τto   custom vir_typ at level 99, only printing).
  Notation "'fpext' τfrom v 'to' τto" :=
    (OP_Conversion (Fpext []) τfrom v τto)
    (in custom vir_exp at level 20,
     τfrom custom vir_typ at level 99, v custom vir_exp at level 99,
     τto   custom vir_typ at level 99, only printing).
  Notation "'fpext' '[' fmf ']' τfrom v 'to' τto" :=
    (OP_Conversion (Fpext fmf) τfrom v τto)
    (in custom vir_exp at level 20,
     fmf custom vir_fmf at level 99,
     τfrom custom vir_typ at level 99, v custom vir_exp at level 99,
     τto   custom vir_typ at level 99, only printing).

  Notation "'uitofp' τfrom v 'to' τto" :=
    (OP_Conversion (Uitofp false) τfrom v τto)
    (in custom vir_exp at level 20,
     τfrom custom vir_typ at level 99, v custom vir_exp at level 99,
     τto   custom vir_typ at level 99, only printing).
  Notation "'uitofp' 'nneg' τfrom v 'to' τto" :=
    (OP_Conversion (Uitofp true) τfrom v τto)
    (in custom vir_exp at level 20,
     τfrom custom vir_typ at level 99, v custom vir_exp at level 99,
     τto   custom vir_typ at level 99, only printing).

  Notation "'sitofp'    τfrom v 'to' τto" := (OP_Conversion Sitofp        τfrom v τto)
    (in custom vir_exp at level 20, τfrom custom vir_typ at level 99,
     v custom vir_exp at level 99, τto custom vir_typ at level 99, only printing).
  Notation "'fptoui'    τfrom v 'to' τto" := (OP_Conversion Fptoui        τfrom v τto)
    (in custom vir_exp at level 20, τfrom custom vir_typ at level 99,
     v custom vir_exp at level 99, τto custom vir_typ at level 99, only printing).
  Notation "'fptosi'    τfrom v 'to' τto" := (OP_Conversion Fptosi        τfrom v τto)
    (in custom vir_exp at level 20, τfrom custom vir_typ at level 99,
     v custom vir_exp at level 99, τto custom vir_typ at level 99, only printing).
  Notation "'inttoptr'  τfrom v 'to' τto" := (OP_Conversion Inttoptr      τfrom v τto)
    (in custom vir_exp at level 20, τfrom custom vir_typ at level 99,
     v custom vir_exp at level 99, τto custom vir_typ at level 99, only printing).
  Notation "'ptrtoint'  τfrom v 'to' τto" := (OP_Conversion Ptrtoint      τfrom v τto)
    (in custom vir_exp at level 20, τfrom custom vir_typ at level 99,
     v custom vir_exp at level 99, τto custom vir_typ at level 99, only printing).
  Notation "'bitcast'   τfrom v 'to' τto" := (OP_Conversion Bitcast       τfrom v τto)
    (in custom vir_exp at level 20, τfrom custom vir_typ at level 99,
     v custom vir_exp at level 99, τto custom vir_typ at level 99, only printing).
  Notation "'addrspacecast' τfrom v 'to' τto" := (OP_Conversion Addrspacecast τfrom v τto)
    (in custom vir_exp at level 20, τfrom custom vir_typ at level 99,
     v custom vir_exp at level 99, τto custom vir_typ at level 99, only printing).

  (** ** Select. LLVM surface: [select i1 cond, τ a, τ b]. *)
  Notation "'select' τc c ',' τa a ',' τb b" :=
    (OP_Select (τc, c) (τa, a) (τb, b))
    (in custom vir_exp at level 20,
     τc custom vir_typ at level 99, c custom vir_exp at level 99,
     τa custom vir_typ at level 99, a custom vir_exp at level 99,
     τb custom vir_typ at level 99, b custom vir_exp at level 99,
     only printing).

  (** ** Get-element-pointer. The index list dispatches through
        [vir_idx_list]; in real goals it is non-empty, so the bare-cons
        rule handles it. *)
  Notation "'getelementptr' t ',' τp p ',' idxs" :=
    (OP_GetElementPtr t (τp, p) idxs)
    (in custom vir_exp at level 20,
     t custom vir_typ at level 99,
     τp custom vir_typ at level 99,
     p custom vir_exp at level 99,
     idxs custom vir_idx_list at level 99,
     only printing).

  (** * vir_instr — instructions

      Code entries are triples [(instr_id, instr, list metadata)]
      ([code := list (instr_id * instr * list metadata)] in LLVMAst.v),
      so every printer here matches a triple — the trailing [_] hides the
      metadata list. The previous version of this section used 2-tuples
      and never fired on real goals.

      Alloca/load/store all carry their attributes as a [list annotation]
      now (no [option] fields). We do not pattern on the annotation list:
      a generic [a] catches the empty and non-empty cases alike, and the
      [{ a }] constr-escape will display it. *)
  Notation "( i )" := i
    (in custom vir_instr at level 0, i custom vir_instr at level 99, only printing).
  Notation "{ i }" := i
    (in custom vir_instr at level 0, i constr, only printing).

  Notation "r '=' x" := (IId r, INSTR_Op x, _)
    (in custom vir_instr at level 30,
     r constr at level 0,
     x custom vir_exp at level 99,
     only printing).
  Notation "r '=' 'call' fn args" := (IId r, INSTR_Call fn args _ _, _)
    (in custom vir_instr at level 30, r constr at level 0, only printing).
  Notation "'call' fn args" := (IVoid _, INSTR_Call fn args _ _, _)
    (in custom vir_instr at level 30, only printing).

  (** ** Alloca / load / store.

       Three layers per op, picked by Rocq via specificity:
         - empty-anns rule       (RHS [(... [], _)])     for [[]]
         - specific-shape rules  (RHS [(... [ANN_X _], _)]) for the
           common single-annotation forms
         - general-anns rule     (RHS [(... anns, _)] dispatched to
           [vir_anns]) for any multi-annotation shape

       The general rule's metavariable [anns] also matches [[]], but
       Rocq prefers the more specific empty-anns rule. *)
  Notation "r '=' 'alloca' t" :=
    (IId r, INSTR_Alloca t [], _)
    (in custom vir_instr at level 30,
     r constr at level 0,
     t custom vir_typ at level 99,
     only printing).
  Notation "r '=' 'alloca' t ',' 'align' n" :=
    (IId r, INSTR_Alloca t [ANN_align (Z.to_num_int n)], _)
    (in custom vir_instr at level 30,
     r constr at level 0,
     t custom vir_typ at level 99,
     n constr at level 0,
     only printing).
  Notation "r '=' 'alloca' t ',' 'align' n" :=
    (IId r, INSTR_Alloca t [ANN_align n], _)
    (in custom vir_instr at level 30,
     r constr at level 0,
     t custom vir_typ at level 99,
     n constr at level 0,
     only printing).
  Notation "r '=' 'alloca' t ',' anns" :=
    (IId r, INSTR_Alloca t anns, _)
    (in custom vir_instr at level 30,
     r constr at level 0,
     t custom vir_typ at level 99,
     anns custom vir_anns at level 99,
     only printing).

  (** Comma layout: each typed-value pair [(τ, e)] displays as [τ e]
      (no internal comma). Commas only separate the load's element-type
      from its pointer arg, the pointer pair from align, etc. *)
  Notation "r '=' 'load' t ',' τp ptr" :=
    (IId r, INSTR_Load t (τp, ptr) [], _)
    (in custom vir_instr at level 30,
     r constr at level 0,
     t custom vir_typ at level 99,
     τp custom vir_typ at level 99,
     ptr custom vir_exp at level 99,
     only printing).
  Notation "r '=' 'load' t ',' τp ptr ',' 'align' n" :=
    (IId r, INSTR_Load t (τp, ptr) [ANN_align (Z.to_num_int n)], _)
    (in custom vir_instr at level 30,
     r constr at level 0,
     t custom vir_typ at level 99,
     τp custom vir_typ at level 99,
     ptr custom vir_exp at level 99,
     n constr at level 0,
     only printing).
  Notation "r '=' 'load' t ',' τp ptr ',' 'align' n" :=
    (IId r, INSTR_Load t (τp, ptr) [ANN_align n], _)
    (in custom vir_instr at level 30,
     r constr at level 0,
     t custom vir_typ at level 99,
     τp custom vir_typ at level 99,
     ptr custom vir_exp at level 99,
     n constr at level 0,
     only printing).
  Notation "r '=' 'load' 'volatile' t ',' τp ptr" :=
    (IId r, INSTR_Load t (τp, ptr) [ANN_volatile], _)
    (in custom vir_instr at level 30,
     r constr at level 0,
     t custom vir_typ at level 99,
     τp custom vir_typ at level 99,
     ptr custom vir_exp at level 99,
     only printing).
  Notation "r '=' 'load' t ',' τp ptr ',' anns" :=
    (IId r, INSTR_Load t (τp, ptr) anns, _)
    (in custom vir_instr at level 30,
     r constr at level 0,
     t custom vir_typ at level 99,
     τp custom vir_typ at level 99,
     ptr custom vir_exp at level 99,
     anns custom vir_anns at level 99,
     only printing).

  Notation "'store' τv val ',' τp ptr" :=
    (IVoid _, INSTR_Store (τv, val) (τp, ptr) [], _)
    (in custom vir_instr at level 30,
     τv custom vir_typ at level 99, val custom vir_exp at level 99,
     τp custom vir_typ at level 99, ptr custom vir_exp at level 99,
     only printing).
  Notation "'store' τv val ',' τp ptr ',' 'align' n" :=
    (IVoid _, INSTR_Store (τv, val) (τp, ptr) [ANN_align (Z.to_num_int n)], _)
    (in custom vir_instr at level 30,
     τv custom vir_typ at level 99, val custom vir_exp at level 99,
     τp custom vir_typ at level 99, ptr custom vir_exp at level 99,
     n constr at level 0,
     only printing).
  Notation "'store' τv val ',' τp ptr ',' 'align' n" :=
    (IVoid _, INSTR_Store (τv, val) (τp, ptr) [ANN_align n], _)
    (in custom vir_instr at level 30,
     τv custom vir_typ at level 99, val custom vir_exp at level 99,
     τp custom vir_typ at level 99, ptr custom vir_exp at level 99,
     n constr at level 0,
     only printing).
  Notation "'store' 'volatile' τv val ',' τp ptr" :=
    (IVoid _, INSTR_Store (τv, val) (τp, ptr) [ANN_volatile], _)
    (in custom vir_instr at level 30,
     τv custom vir_typ at level 99, val custom vir_exp at level 99,
     τp custom vir_typ at level 99, ptr custom vir_exp at level 99,
     only printing).
  Notation "'store' τv val ',' τp ptr ',' anns" :=
    (IVoid _, INSTR_Store (τv, val) (τp, ptr) anns, _)
    (in custom vir_instr at level 30,
     τv custom vir_typ at level 99, val custom vir_exp at level 99,
     τp custom vir_typ at level 99, ptr custom vir_exp at level 99,
     anns custom vir_anns at level 99,
     only printing).

  (** * vir_term — terminators

      Like code entries, [blk_term] is a triple [(instr_id, terminator,
      list metadata)] (CFG.blk_term in LLVMAst.v). We match the triple
      directly so [[term blk.(blk_term)]] fires without the user having
      to project. *)
  Notation "( t )" := t
    (in custom vir_term at level 0, t custom vir_term at level 99, only printing).
  Notation "{ t }" := t
    (in custom vir_term at level 0, t constr, only printing).

  Notation "'ret' τ e" := (_, TERM_Ret (τ, e), _)
    (in custom vir_term at level 30,
     τ custom vir_typ at level 99, e custom vir_exp at level 99,
     only printing).
  Notation "'ret' 'void'" := (_, TERM_Ret_void, _)
    (in custom vir_term at level 30, only printing).
  Notation "'br' τ c ',' 'label' e ',' 'label' f" :=
    (_, TERM_Br (τ, c) e f, _)
    (in custom vir_term at level 30,
     τ custom vir_typ at level 99,
     c custom vir_exp at level 99,
     e constr at level 0, f constr at level 0,
     only printing).
  Notation "'br' 'label' e" := (_, TERM_Br_1 e, _)
    (in custom vir_term at level 30,
     e constr at level 0,
     only printing).
  Notation "'unreachable'" := (_, TERM_Unreachable, _)
    (in custom vir_term at level 30, only printing).
  Notation "'resume' τ v" := (_, TERM_Resume (τ, v), _)
    (in custom vir_term at level 30,
     τ custom vir_typ at level 99, v custom vir_exp at level 99,
     only printing).
  Notation "'switch' τ v ',' 'label' d brs" :=
    (_, TERM_Switch (τ, v) d brs, _)
    (in custom vir_term at level 30,
     τ custom vir_typ at level 99, v custom vir_exp at level 99,
     brs custom vir_arm_list at level 99,
     only printing).
  Notation "'indirectbr' τ v ',' brs" :=
    (_, TERM_IndirectBr (τ, v) brs, _)
    (in custom vir_term at level 30,
     τ custom vir_typ at level 99, v custom vir_exp at level 99,
     brs custom vir_label_list at level 99,
     only printing).

  (** * vir_code — recursive printer for code lists.
        Each element is an instr triple printed via vir_instr; the list
        itself is rendered one entry per line via the [//] format break.
        Single-element lists work too (one iteration of the [..] form).
        Empty code lists fall through to the constr-escape. *)
  Notation "( c )" := c
    (in custom vir_code at level 0, c custom vir_code at level 99, only printing).
  Notation "{ c }" := c
    (in custom vir_code at level 0, c constr, only printing).

  Notation "i ; .. ; j" :=
    (cons i .. (cons j nil) ..)
    (in custom vir_code at level 99,
     i custom vir_instr at level 30,
     j custom vir_instr at level 30,
     only printing,
     format "i ';' '//' .. ';' '//' j").

  (** * vir_phi — phi-node entries.
        [blk_phis] is [list (local_id * phi * list metadata)], so each
        entry is a triple — same shape as code. The [Phi t args] body
        carries an incoming list [args : list (block_id * exp)] which we
        do not recursively pretty-print here; it falls through to the
        stdlib list display. *)
  Notation "( p )" := p
    (in custom vir_phi at level 0, p custom vir_phi at level 99, only printing).
  Notation "{ p }" := p
    (in custom vir_phi at level 0, p constr, only printing).

  Notation "x '=' 'phi' t a" := (x, Phi t a, _)
    (in custom vir_phi at level 30,
     x constr at level 0,
     t custom vir_typ at level 99,
     a custom vir_phi_args at level 99,
     only printing).

  (** * vir_phis — recursive printer for phi-node lists. *)
  Notation "( ps )" := ps
    (in custom vir_phis at level 0, ps custom vir_phis at level 99, only printing).
  Notation "{ ps }" := ps
    (in custom vir_phis at level 0, ps constr, only printing).

  Notation "p ; .. ; q" :=
    (cons p .. (cons q nil) ..)
    (in custom vir_phis at level 99,
     p custom vir_phi at level 30,
     q custom vir_phi at level 30,
     only printing,
     format "p ';' '//' .. ';' '//' q").

  (** * vir_idx_list — GEP indices [list (T * exp)].
        Each element is a [texp]; lists are usually short, so we lay
        them out comma-separated on one line. *)
  Notation "( i )" := i
    (in custom vir_idx_list at level 0, i custom vir_idx_list at level 99, only printing).
  Notation "{ i }" := i
    (in custom vir_idx_list at level 0, i constr, only printing).
  Notation "τ v" := (τ, v)
    (in custom vir_idx_list at level 5,
     τ custom vir_typ at level 99,
     v custom vir_exp at level 99,
     only printing).
  Notation "i ',' .. ',' j" :=
    (cons i .. (cons j nil) ..)
    (in custom vir_idx_list at level 99,
     i custom vir_idx_list at level 5,
     j custom vir_idx_list at level 5,
     only printing,
     format "i ',' .. ',' j").

  (** * vir_phi_args — phi incoming pairs [list (block_id * exp)].
        AST stores [(block_id, exp)]; LLVM surface displays value first,
        then label, so we swap in the element rule. *)
  Notation "( a )" := a
    (in custom vir_phi_args at level 0, a custom vir_phi_args at level 99, only printing).
  Notation "{ a }" := a
    (in custom vir_phi_args at level 0, a constr, only printing).
  Notation "'[' v ',' lbl ']'" := (lbl, v)
    (in custom vir_phi_args at level 5,
     v custom vir_exp at level 99,
     lbl constr at level 0,
     only printing).
  Notation "a ',' .. ',' b" :=
    (cons a .. (cons b nil) ..)
    (in custom vir_phi_args at level 99,
     a custom vir_phi_args at level 5,
     b custom vir_phi_args at level 5,
     only printing,
     format "a ',' .. ',' b").

  (** * vir_arm_list — switch arms [list (tint_literal * block_id)].
        Each arm has internal commas, so the cons separator is [;] and
        we lay arms out one per line. *)
  Notation "( a )" := a
    (in custom vir_arm_list at level 0, a custom vir_arm_list at level 99, only printing).
  Notation "{ a }" := a
    (in custom vir_arm_list at level 0, a constr, only printing).
  Notation "'i' sz x ',' 'label' lbl" := (TInt_Literal sz (Z.to_num_int x), lbl)
    (in custom vir_arm_list at level 5,
     sz constr at level 0, x constr at level 0, lbl constr at level 0,
     only printing).
  Notation "'i' sz x ',' 'label' lbl" := (TInt_Literal sz x, lbl)
    (in custom vir_arm_list at level 5,
     sz constr at level 0, x constr at level 0, lbl constr at level 0,
     only printing).
  Notation "a ; .. ; b" :=
    (cons a .. (cons b nil) ..)
    (in custom vir_arm_list at level 99,
     a custom vir_arm_list at level 5,
     b custom vir_arm_list at level 5,
     only printing,
     format "a ';' '//' .. ';' '//' b").

  (** * vir_label_list — indirectbr targets [list block_id]. *)
  Notation "( l )" := l
    (in custom vir_label_list at level 0, l custom vir_label_list at level 99, only printing).
  Notation "{ l }" := l
    (in custom vir_label_list at level 0, l constr, only printing).
  Notation "'label' lbl" := lbl
    (in custom vir_label_list at level 5, lbl constr at level 0, only printing).
  Notation "l ',' .. ',' m" :=
    (cons l .. (cons m nil) ..)
    (in custom vir_label_list at level 99,
     l custom vir_label_list at level 5,
     m custom vir_label_list at level 5,
     only printing,
     format "l ',' .. ',' m").

  (** * vir_anns — annotation list [list annotation].
        Element rules cover the most common attributes on memory ops
        (align / volatile / atomic / inalloca / num_elements). Other
        constructors fall through to the constr-escape. The cons
        separator is [;] because element rules may contain commas.

        Empty annotation lists do not display through this entry — the
        dispatching notations (alloca/load/store) provide a separate
        empty-list shape that simply omits the trailing annotations.
        Singleton lists for [align n] / [volatile] are still matched
        directly by the specific instruction rules; this entry handles
        the multi-annotation case. *)
  Notation "( a )" := a
    (in custom vir_anns at level 0, a custom vir_anns at level 99, only printing).
  Notation "{ a }" := a
    (in custom vir_anns at level 0, a constr, only printing).
  Notation "'align' n" := (ANN_align (Z.to_num_int n))
    (in custom vir_anns at level 5, n constr at level 0, only printing).
  Notation "'align' n" := (ANN_align n)
    (in custom vir_anns at level 5, n constr at level 0, only printing).
  Notation "'volatile'"     := ANN_volatile     (in custom vir_anns at level 5, only printing).
  Notation "'atomic'"       := ANN_atomic       (in custom vir_anns at level 5, only printing).
  Notation "'inalloca'"     := ANN_inalloca     (in custom vir_anns at level 5, only printing).
  Notation "'num_elements' τ v" := (ANN_num_elements (τ, v))
    (in custom vir_anns at level 5,
     τ custom vir_typ at level 99,
     v custom vir_exp at level 99,
     only printing).
  Notation "a ; .. ; b" :=
    (cons a .. (cons b nil) ..)
    (in custom vir_anns at level 99,
     a custom vir_anns at level 5,
     b custom vir_anns at level 5,
     only printing,
     format "a ';' '//' .. ';' '//' b").

  (** * vir_fmf — fast-math flag list [list fast_math].
        Eight nullary variants. Same empty-list caveat as [vir_anns]. *)
  Notation "( f )" := f
    (in custom vir_fmf at level 0, f custom vir_fmf at level 99, only printing).
  Notation "{ f }" := f
    (in custom vir_fmf at level 0, f constr, only printing).
  Notation "'nnan'"     := Nnan     (in custom vir_fmf at level 5, only printing).
  Notation "'ninf'"     := Ninf     (in custom vir_fmf at level 5, only printing).
  Notation "'nsz'"      := Nsz      (in custom vir_fmf at level 5, only printing).
  Notation "'arcp'"     := Arcp     (in custom vir_fmf at level 5, only printing).
  Notation "'contract'" := Contract (in custom vir_fmf at level 5, only printing).
  Notation "'afn'"      := Afn      (in custom vir_fmf at level 5, only printing).
  Notation "'reassoc'"  := Reassoc  (in custom vir_fmf at level 5, only printing).
  Notation "'fast'"     := Fast     (in custom vir_fmf at level 5, only printing).
  Notation "f ',' .. ',' g" :=
    (cons f .. (cons g nil) ..)
    (in custom vir_fmf at level 99,
     f custom vir_fmf at level 5,
     g custom vir_fmf at level 5,
     only printing,
     format "f ',' .. ',' g").

  (** * Definitions and blocks (still constr-level)

      [mk_block] now displays via the per-section custom entries: phis
      through vir_phis, code through vir_code, term through vir_term.
      Block comments are wildcarded. *)
  (** [mk_definition] has three fields ([df_prototype], [df_args],
      [df_instrs]); [mk_declaration] has five (name, type, param_attrs,
      attrs, annotations). The previous version of this notation passed
      4 args to the former and 11 to the latter — both stale w.r.t. the
      current AST and never matched real definitions. *)
  Notation "'func' f args ':=' x" :=
    (mk_definition (mk_declaration (Name f) _ _ _ _) args x)
    (at level 10, only printing,
     format "'func'  f  args  ':=' '//' x").

  (** Block printers. Three shapes share the prefix [label ':'] but
      differ in token count and RHS pattern. The printer picks the
      most specific RHS match (both [nil] / phis [nil] / general).
      Parse-direction prefix-conflict warning is suppressed file-wide.

      We don't add a separate (phis non-empty, code [nil]) shape: it
      would have the same LHS token structure as the empty-phis shape
      ([label ':' X term]) but with a different argument entry, which
      Rocq rejects. Phi-only blocks therefore fall through to the
      general shape, where [code = []] renders as [{ [] }]. *)
  Notation "label ':' term" :=
    (mk_block label nil nil term _)
    (at level 10,
     term custom vir_term at level 99,
     only printing,
     format "'[v' label ':' '//' term ']'").
  Notation "label ':' code term" :=
    (mk_block label nil code term _)
    (at level 10,
     code custom vir_code at level 99,
     term custom vir_term at level 99,
     only printing,
     format "'[v' label ':' '//' code '//' term ']'").
  Notation "label ':' phis code term" :=
    (mk_block label phis code term _)
    (at level 10, phis custom vir_phis at level 99,
     code custom vir_code at level 99,
     term custom vir_term at level 99,
     only printing,
     format "'[v' label ':' '//' phis '//' code '//' term ']'").

  (** * Module-level pretty printers.

      [mcfg = modul cfg] is a 7-field record where, in most goals, all
      fields except [m_definitions] are empty. The compact shapes below
      hide empty fields by pattern-matching on [None]/[nil] in the
      slots that are typically empty, leaving the user with just the
      meaningful content. The full-record fallback is the stdlib
      record-syntax display.

      Definitions and declarations are dispatched through their list
      entries to get one-per-line layout. *)

  (** vir_def_list — list of definitions. *)
  Notation "( l )" := l
    (in custom vir_def_list at level 0, l custom vir_def_list at level 99, only printing).
  Notation "{ l }" := l
    (in custom vir_def_list at level 0, l constr, only printing).
  Notation "d ; .. ; e" :=
    (cons d .. (cons e nil) ..)
    (in custom vir_def_list at level 99,
     d constr at level 10, e constr at level 10,
     only printing,
     format "d ';' '//' .. ';' '//' e").

  (** vir_decl_list — list of declarations. *)
  Notation "( l )" := l
    (in custom vir_decl_list at level 0, l custom vir_decl_list at level 99, only printing).
  Notation "{ l }" := l
    (in custom vir_decl_list at level 0, l constr, only printing).
  Notation "d ; .. ; e" :=
    (cons d .. (cons e nil) ..)
    (in custom vir_decl_list at level 99,
     d constr at level 10, e constr at level 10,
     only printing,
     format "d ';' '//' .. ';' '//' e").

  (** vir_global_list — list of globals. *)
  Notation "( l )" := l
    (in custom vir_global_list at level 0, l custom vir_global_list at level 99, only printing).
  Notation "{ l }" := l
    (in custom vir_global_list at level 0, l constr, only printing).
  Notation "g ; .. ; h" :=
    (cons g .. (cons h nil) ..)
    (in custom vir_global_list at level 99,
     g constr at level 10, h constr at level 10,
     only printing,
     format "g ';' '//' .. ';' '//' h").

  (** vir_block_list — recursive printer for the [blks] field of a
      [cfg]. Without this dispatch, [blks] would render through Rocq's
      default list printer ([a ; b ; c] inline), running adjacent
      blocks together. The double [//] inserts a blank line between
      blocks. *)
  Notation "( bs )" := bs
    (in custom vir_block_list at level 0, bs custom vir_block_list at level 99, only printing).
  Notation "{ bs }" := bs
    (in custom vir_block_list at level 0, bs constr, only printing).
  Notation "b ; .. ; c" :=
    (cons b .. (cons c nil) ..)
    (in custom vir_block_list at level 99,
     b constr at level 10, c constr at level 10,
     only printing,
     format "b ';' '//' '//' .. ';' '//' '//' c").

  (** [cfg] — three-field record [{ init; blks; args }]. *)
  Notation "'cfg' init ',' args '{' blks '}'" :=
    (mkCFG init blks args)
    (at level 10,
     blks custom vir_block_list at level 99,
     only printing,
     format "'[v' 'cfg'  init  ','  args  '{' '//' blks '//' '}' ']'").

  (** [mk_modul] compact shape — all "control" fields empty, only
      [m_definitions] populated (the dominant case in goals). The
      [%vir_def_list] dispatch lays definitions one per line. *)
  Notation "'modul' '{' defs '}'" :=
    (mk_modul None None None nil nil nil defs)
    (at level 10, defs custom vir_def_list at level 99, only printing,
     format "'[v' 'modul'  '{' '//' defs '//' '}' ']'").
  (** With declarations — common when external functions are used. *)
  Notation "'modul' '{' decls '|' defs '}'" :=
    (mk_modul None None None nil nil decls defs)
    (at level 10,
     decls custom vir_decl_list at level 99,
     defs  custom vir_def_list  at level 99,
     only printing,
     format "'[v' 'modul'  '{' '//' decls '//'  '|' '//' defs '//' '}' ']'").

  (** [mk_global] compact shape — most fields default-empty. The
      common case is [g_ident] + [g_typ] + [g_constant] + [g_exp]
      with no annotations. *)
  Notation "'global' x ':' t ':=' e" :=
    (mk_global x t false (Some e) false false nil)
    (at level 10, t custom vir_typ at level 99,
     e custom vir_exp at level 99,
     only printing).
  Notation "'constant' x ':' t ':=' e" :=
    (mk_global x t true (Some e) false false nil)
    (at level 10, t custom vir_typ at level 99,
     e custom vir_exp at level 99,
     only printing).

  (** Top-level entries. These appear in pre-reduction goals (before
      [mcfg_of_tle] is fully unfolded). After reduction the entries are
      folded into [mk_modul]. *)
  Notation "'#decl' d"               := (TLE_Declaration d)
    (at level 10, only printing).
  Notation "'#def' d"                := (TLE_Definition d)
    (at level 10, only printing).
  Notation "'#global' g"             := (TLE_Global g)
    (at level 10, only printing).
  Notation "'#type' id ':=' t"       := (TLE_Type_decl id t)
    (at level 10, t custom vir_typ at level 99, only printing).
  Notation "'#target' s"             := (TLE_Target s)
    (at level 10, only printing).
  Notation "'#datalayout' s"         := (TLE_Datalayout s)
    (at level 10, only printing).
  Notation "'#source' s"             := (TLE_Source_filename s)
    (at level 10, only printing).
  Notation "'#comment' s"            := (TLE_Comment s)
    (at level 10, only printing).

  (** vir_tle_list — list of top-level entries (input to [mcfg_of_tle]). *)
  Notation "( l )" := l
    (in custom vir_tle_list at level 0, l custom vir_tle_list at level 99, only printing).
  Notation "{ l }" := l
    (in custom vir_tle_list at level 0, l constr, only printing).
  Notation "t ; .. ; u" :=
    (cons t .. (cons u nil) ..)
    (in custom vir_tle_list at level 99,
     t constr at level 10, u constr at level 10,
     only printing,
     format "t ';' '//' .. ';' '//' u").

End VIR_Notations.

Section SurfaceSyntaxTest.

  Definition add_twice :=
    mcfg_of_tle
      [TLE_Definition {|
           df_prototype :=
             {|dc_name := (Name "main");
               dc_type := (TYPE_Function (TYPE_I 32%positive) [(TYPE_I 32%positive); (TYPE_Pointer (Some (TYPE_Pointer (Some (TYPE_I 8%positive)))))] false);
               dc_param_attrs := ([], [
                                 ]);
               dc_attrs := [];
               dc_annotations := []
             |};
           df_args := [(Name "argc"); (Name "arcv")];
           df_instrs :=
             (
               {|
                 blk_id := (Anon 0%Z);
                 blk_phis := [];
                 blk_code := [(IId (Anon 1%Z), (INSTR_Op (OP_IBinop (Add false false) (TYPE_I 32%positive) (EXP_Integer (Z.to_num_int (5)%Z)) (EXP_Integer (Z.to_num_int (9)%Z)))), []);
                              (IId (Anon 2%Z), (INSTR_Op (OP_IBinop (Add false false) (TYPE_I 32%positive) (EXP_Ident (ID_Local (Anon 1%Z))) (EXP_Integer (Z.to_num_int (15)%Z)))), [])];
                 blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%positive), (EXP_Ident (ID_Local (Anon 2%Z)))), []);
                 blk_comments := None
               |}
               ,[])
         |}].
  
 Import VIR_Notations .

 Variable P: mcfg typ -> Prop.
 Variable Q: cfg typ -> Prop.
 Goal P add_twice.
   unfold add_twice.
   unfold mcfg_of_tle.
   unfold modul_of_toplevel_entities.
   cbn.
   unfold mcfg_of_modul; cbn.
   unfold cfg_of_definition.
   cbn.
   (* TODO: Can we display one instruction per line in code? *)
   (* TODO: phi-nodes? *)
 Abort.

 (** Ad-hoc surface-syntax probe. Constructed directly at [mcfg typ]
     level (no [cbn] dance needed) to exercise:

       - compact [mk_modul] (only [m_definitions] non-empty)
       - [func] / [cfg] / multi-block [mk_block]
       - alloca/store/load with single-annotation [align] forms
       - integer binop ([add]) and comparison ([icmp slt])
       - conditional [br] and unconditional [br_1]
       - phi node with two incoming edges
       - [Z.to_num_int] wrapper at every numeric literal (must hide)
       - function-type display [i32 ( i32 )]
       - typed pointer display [i32 *] *)
 Definition test_branch : mcfg typ :=
   mk_modul None None None nil nil nil
     [{| df_prototype := {|
           dc_name := Name "test";
           dc_type := TYPE_Function (TYPE_I 32%positive) [TYPE_I 32%positive] false;
           dc_param_attrs := ([], [[]]);
           dc_attrs := [];
           dc_annotations := [];
         |};
         df_args := [Name "x"];
         df_instrs := mkCFG
           (Name "entry")
           [{| blk_id := Name "entry";
               blk_phis := [];
               blk_code := [
                 (IId (Name "a"),
                  INSTR_Alloca (TYPE_I 32%positive) [ANN_align (Z.to_num_int 4%Z)],
                  []);
                 (IVoid 0%Z,
                  INSTR_Store
                    (TYPE_I 32%positive, EXP_Integer (Z.to_num_int 5%Z))
                    (TYPE_Pointer (Some (TYPE_I 32%positive)),
                     EXP_Ident (ID_Local (Name "a")))
                    [ANN_align (Z.to_num_int 4%Z)],
                  []);
                 (IId (Name "b"),
                  INSTR_Load (TYPE_I 32%positive)
                    (TYPE_Pointer (Some (TYPE_I 32%positive)),
                     EXP_Ident (ID_Local (Name "a")))
                    [ANN_align (Z.to_num_int 4%Z)],
                  []);
                 (IId (Name "c"),
                  INSTR_Op (OP_IBinop (Add false false) (TYPE_I 32%positive)
                             (EXP_Ident (ID_Local (Name "b")))
                             (EXP_Ident (ID_Local (Name "x")))),
                  []);
                 (IId (Name "cond"),
                  INSTR_Op (OP_ICmp false Slt (TYPE_I 32%positive)
                             (EXP_Ident (ID_Local (Name "c")))
                             (EXP_Integer (Z.to_num_int 0%Z))),
                  [])
               ];
               blk_term := (IVoid 1%Z,
                 TERM_Br (TYPE_I 1%positive, EXP_Ident (ID_Local (Name "cond")))
                         (Name "neg") (Name "pos"),
                 []);
               blk_comments := None;
            |};
            {| blk_id := Name "neg";
               blk_phis := [];
               blk_code := [];
               blk_term := (IVoid 2%Z, TERM_Br_1 (Name "merge"), []);
               blk_comments := None;
            |};
            {| blk_id := Name "pos";
               blk_phis := [];
               blk_code := [];
               blk_term := (IVoid 3%Z, TERM_Br_1 (Name "merge"), []);
               blk_comments := None;
            |};
            {| blk_id := Name "merge";
               blk_phis := [
                 (Name "r",
                  Phi (TYPE_I 32%positive)
                      [(Name "neg", EXP_Ident (ID_Local (Name "c")));
                       (Name "pos", EXP_Ident (ID_Local (Name "c")))],
                  [])
               ];
               blk_code := [];
               blk_term := (IVoid 4%Z,
                 TERM_Ret (TYPE_I 32%positive,
                           EXP_Ident (ID_Local (Name "r"))),
                 []);
               blk_comments := None;
            |}]
           [Name "x"];
        |}].

 Goal P test_branch.
   unfold test_branch.
   (* Inspect interactively — surface-syntax printers exercised here:
        - compact [modul], [func], [cfg]
        - typed-pointer [i32*], typed-int [i32]
        - alloca/store/load with [, align N]
        - [add], [icmp slt]
        - typed [br i1 c, label l1, label l2] and [br label l]
        - phi-node with multiple incoming edges
        - [Z.to_num_int] wrapper hidden everywhere
        - blocks separated by blank lines via [vir_block_list]
      Known cosmetic limitations:
        - block labels and identifiers display with quotes ([%"a"])
        - phi-only block (merge) shows [{[]}] for the empty code list. *)
 Abort.

 (* TODO: regenerate this example with the new frontend syntax *)
 (*
 Definition binarysearch := mcfg_of_tle
   [TLE_Type_decl (ID_Local (Name "struct.Node")) (TYPE_Struct [(TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))); (TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))); (TYPE_I 64%N)]);
   TLE_Global {|g_ident := (Name "node1");
                g_typ := (TYPE_Identified (ID_Local (Name "struct.Node")));
                g_constant := false;
                g_exp := (Some (EXP_Struct [((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))),(EXP_Ident (ID_Global (Name "node2")))); ((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))),(EXP_Ident (ID_Global (Name "node3")))); ((TYPE_I 64%N),(EXP_Integer (50)%Z))]));
                g_externally_initialized := false;
                g_annotations := []
              |};
   TLE_Global {|g_ident := (Name "node2");
                g_typ := (TYPE_Identified (ID_Local (Name "struct.Node")));
                g_constant := false;
                g_exp := (Some (EXP_Struct [((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))),(EXP_Ident (ID_Global (Name "node4")))); ((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))),(EXP_Ident (ID_Global (Name "node5")))); ((TYPE_I 64%N),(EXP_Integer (25)%Z))]));
                g_externally_initialized := false;
                g_annotations := []
              |};
   TLE_Global {|g_ident := (Name "node3");
                g_typ := (TYPE_Identified (ID_Local (Name "struct.Node")));
                g_constant := false;
                g_exp := (Some (EXP_Struct [((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))),(EXP_Ident (ID_Global (Name "node6")))); ((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))),(EXP_Ident (ID_Global (Name "node7")))); ((TYPE_I 64%N),(EXP_Integer (75)%Z))]));
                g_externally_initialized := false;
                g_annotations := []
              |};
   TLE_Global {|g_ident := (Name "node4");
                g_typ := (TYPE_Identified (ID_Local (Name "struct.Node")));
                g_constant := false;
                g_exp := (Some (EXP_Struct [((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))),(EXP_Ident (ID_Global (Name "node8")))); ((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))),EXP_Null); ((TYPE_I 64%N),(EXP_Integer (10)%Z))]));
                g_externally_initialized := false;
                g_annotations := []
              |};
   TLE_Global {|g_ident := (Name "node5");
                g_typ := (TYPE_Identified (ID_Local (Name "struct.Node")));
                g_constant := false;
                g_exp := (Some (EXP_Struct [((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))),EXP_Null); ((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))),EXP_Null); ((TYPE_I 64%N),(EXP_Integer (30)%Z))]));
                g_externally_initialized := false;
                g_annotations := []
              |};
   TLE_Global {|g_ident := (Name "node6");
                g_typ := (TYPE_Identified (ID_Local (Name "struct.Node")));
                g_constant := false;
                g_exp := (Some (EXP_Struct [((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))),EXP_Null); ((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))),EXP_Null); ((TYPE_I 64%N),(EXP_Integer (60)%Z))]));
                g_externally_initialized := false;
                g_annotations := []
              |};
   TLE_Global {|g_ident := (Name "node7");
                g_typ := (TYPE_Identified (ID_Local (Name "struct.Node")));
                g_constant := false;
                g_exp := (Some (EXP_Struct [((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))),EXP_Null); ((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))),EXP_Null); ((TYPE_I 64%N),(EXP_Integer (80)%Z))]));
                g_externally_initialized := false;
                g_annotations := []
              |};
   TLE_Global {|g_ident := (Name "node8");
                g_typ := (TYPE_Identified (ID_Local (Name "struct.Node")));
                g_constant := false;
                g_exp := (Some (EXP_Struct [((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))),EXP_Null); ((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))),EXP_Null); ((TYPE_I 64%N),(EXP_Integer (1)%Z))]));
                g_externally_initialized := false;
                g_annotations := []
              |};
   TLE_Definition {|
       df_prototype := {|dc_name := (Name "contains");
                         dc_type := (TYPE_Function (TYPE_I 64%N) [(TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))); (TYPE_I 64%N)] false);
                         dc_param_attrs := ([], [
                                           ]);
                         dc_attrs := [];
                         dc_annotations := []
                       |};
       df_args := [(Name "root"); (Name "value")];
       df_instrs := (
                     {|
                       blk_id := (Anon 0%Z);
                       blk_phis := [];
                       blk_code := [(IId (Anon 1%Z), (INSTR_Op (OP_GetElementPtr (TYPE_Identified (ID_Local (Name "struct.Node"))) ((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))),(EXP_Ident (ID_Local (Name "root")))) [((TYPE_I 32%positive),(EXP_Integer (0)%Z)); ((TYPE_I 32%positive),(EXP_Integer (2)%Z))])));
                                   (IId (Anon 2%Z), (INSTR_Load (TYPE_I 64%N) ((TYPE_Pointer (TYPE_I 64%N)), (EXP_Ident (ID_Local (Anon 1%Z)))) []));
                                   (IId (Anon 3%Z), (INSTR_Op (OP_ICmp Eq (TYPE_I 64%N) (EXP_Ident (ID_Local (Anon 2%Z))) (EXP_Ident (ID_Local (Name "value"))))))];
                       blk_term := TERM_Br ((TYPE_I 1%N), (EXP_Ident (ID_Local (Anon 3%Z)))) (Name "equal") (Name "notequal");
                       blk_comments := None
                     |},[
                       {|
                         blk_id := (Name "equal");
                         blk_phis := [];
                         blk_code := [];
                         blk_term := TERM_Ret ((TYPE_I 64%N), (EXP_Integer (1)%Z));
                         blk_comments := None
                       |};
                   {|
                     blk_id := (Name "notequal");
                     blk_phis := [];
                     blk_code := [(IId (Anon 4%Z), (INSTR_Op (OP_ICmp Sgt (TYPE_I 64%N) (EXP_Ident (ID_Local (Anon 2%Z))) (EXP_Ident (ID_Local (Name "value"))))))];
                     blk_term := TERM_Br ((TYPE_I 1%N), (EXP_Ident (ID_Local (Anon 4%Z)))) (Name "left") (Name "right");
                     blk_comments := None
                   |};
                   {|
                     blk_id := (Name "left");
                     blk_phis := [];
                     blk_code := [(IId (Anon 5%Z), (INSTR_Op (OP_GetElementPtr (TYPE_Identified (ID_Local (Name "struct.Node"))) ((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))),(EXP_Ident (ID_Local (Name "root")))) [((TYPE_I 32%positive),(EXP_Integer (0)%Z)); ((TYPE_I 32%positive),(EXP_Integer (0)%Z))])));
                                 (IId (Anon 6%Z), (INSTR_Load (TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))) ((TYPE_Pointer (TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node"))))), (EXP_Ident (ID_Local (Anon 5%Z)))) []));
                                 (IId (Anon 7%Z), (INSTR_Op (OP_ICmp Eq (TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))) (EXP_Ident (ID_Local (Anon 6%Z))) EXP_Null)))];
                     blk_term := TERM_Br ((TYPE_I 1%N), (EXP_Ident (ID_Local (Anon 7%Z)))) (Name "none") (Name "left_next");
                     blk_comments := None
                   |};
                   {|
                     blk_id := (Name "left_next");
                     blk_phis := [];
                     blk_code := [(IId (Anon 8%Z), (INSTR_Call ((TYPE_I 64%N), (EXP_Ident (ID_Global (Name "contains")))) [((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))), (EXP_Ident (ID_Local (Anon 6%Z)))); ((TYPE_I 64%N), (EXP_Ident (ID_Local (Name "value"))))]))];
                     blk_term := TERM_Ret ((TYPE_I 64%N), (EXP_Ident (ID_Local (Anon 8%Z))));
                     blk_comments := None
                   |};
                   {|
                     blk_id := (Name "right");
                     blk_phis := [];
                     blk_code := [(IId (Anon 9%Z), (INSTR_Op (OP_GetElementPtr (TYPE_Identified (ID_Local (Name "struct.Node"))) ((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))),(EXP_Ident (ID_Local (Name "root")))) [((TYPE_I 32%positive),(EXP_Integer (0)%Z)); ((TYPE_I 32%positive),(EXP_Integer (1)%Z))])));
                                 (IId (Anon 10%Z), (INSTR_Load false (TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))) ((TYPE_Pointer (TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node"))))), (EXP_Ident (ID_Local (Anon 9%Z)))) None));
                                 (IId (Anon 11%Z), (INSTR_Op (OP_ICmp Eq (TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))) (EXP_Ident (ID_Local (Anon 10%Z))) EXP_Null)))];
                     blk_term := TERM_Br ((TYPE_I 1%N), (EXP_Ident (ID_Local (Anon 11%Z)))) (Name "none") (Name "right_next");
                     blk_comments := None
                   |};
                   {|
                     blk_id := (Name "right_next");
                     blk_phis := [];
                     blk_code := [(IId (Anon 12%Z), (INSTR_Call ((TYPE_I 64%N), (EXP_Ident (ID_Global (Name "contains")))) [((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))), (EXP_Ident (ID_Local (Anon 10%Z)))); ((TYPE_I 64%N), (EXP_Ident (ID_Local (Name "value"))))]))];
                     blk_term := TERM_Ret ((TYPE_I 64%N), (EXP_Ident (ID_Local (Anon 12%Z))));
                     blk_comments := None
                   |};
                   {|
                     blk_id := (Name "none");
                     blk_phis := [];
                     blk_code := [];
                     blk_term := TERM_Ret ((TYPE_I 64%N), (EXP_Integer (0)%Z));
                     blk_comments := None
                   |}])
     |};
   TLE_Definition {|
       df_prototype := {|dc_name := (Name "main");
                         dc_type := (TYPE_Function (TYPE_I 64%N) [(TYPE_I 64%N); (TYPE_Pointer (TYPE_Pointer (TYPE_I 8%positive)))] false);
                         dc_param_attrs := ([], [
                                           ]);
                         dc_attrs := [];
                         dc_annotations := []
                       |};
       df_args := [(Name "argc"); (Name "argv")];
       df_instrs := (
                     {|
                       blk_id := (Anon 0%Z);
                       blk_phis := [];
                       blk_code := [(IId (Anon 1%Z), (INSTR_Op (OP_IBinop (Add false false) (TYPE_I 64%N) (EXP_Integer (50)%Z) (EXP_Integer (0)%Z))));
                                   (IId (Anon 2%Z), (INSTR_Op (OP_IBinop (Add false false) (TYPE_I 64%N) (EXP_Integer (25)%Z) (EXP_Integer (0)%Z))));
                                   (IId (Anon 3%Z), (INSTR_Op (OP_IBinop (Add false false) (TYPE_I 64%N) (EXP_Integer (75)%Z) (EXP_Integer (0)%Z))));
                                   (IId (Anon 4%Z), (INSTR_Op (OP_IBinop (Add false false) (TYPE_I 64%N) (EXP_Integer (10)%Z) (EXP_Integer (0)%Z))));
                                   (IId (Anon 5%Z), (INSTR_Op (OP_IBinop (Add false false) (TYPE_I 64%N) (EXP_Integer (30)%Z) (EXP_Integer (0)%Z))));
                                   (IId (Anon 6%Z), (INSTR_Op (OP_IBinop (Add false false) (TYPE_I 64%N) (EXP_Integer (60)%Z) (EXP_Integer (0)%Z))));
                                   (IId (Anon 7%Z), (INSTR_Op (OP_IBinop (Add false false) (TYPE_I 64%N) (EXP_Integer (80)%Z) (EXP_Integer (0)%Z))));
                                   (IId (Anon 8%Z), (INSTR_Op (OP_IBinop (Add false false) (TYPE_I 64%N) (EXP_Integer (1)%Z) (EXP_Integer (0)%Z))));
                                   (IId (Anon 9%Z), (INSTR_Op (OP_IBinop (Add false false) (TYPE_I 64%N) (EXP_Integer (100)%Z) (EXP_Integer (0)%Z))));
                                   (IId (Anon 10%Z), (INSTR_Op (OP_IBinop (Add false false) (TYPE_I 64%N) (EXP_Integer (120)%Z) (EXP_Integer (0)%Z))));
                                   (IId (Anon 11%Z), (INSTR_Call ((TYPE_I 64%N), (EXP_Ident (ID_Global (Name "contains")))) [((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))), (EXP_Ident (ID_Global (Name "node1")))); ((TYPE_I 64%N), (EXP_Ident (ID_Local (Anon 1%Z))))]));
                                   (IId (Anon 12%Z), (INSTR_Call ((TYPE_I 64%N), (EXP_Ident (ID_Global (Name "contains")))) [((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))), (EXP_Ident (ID_Global (Name "node1")))); ((TYPE_I 64%N), (EXP_Ident (ID_Local (Anon 2%Z))))]));
                                   (IId (Anon 13%Z), (INSTR_Call ((TYPE_I 64%N), (EXP_Ident (ID_Global (Name "contains")))) [((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))), (EXP_Ident (ID_Global (Name "node1")))); ((TYPE_I 64%N), (EXP_Ident (ID_Local (Anon 3%Z))))]));
                                   (IId (Anon 14%Z), (INSTR_Call ((TYPE_I 64%N), (EXP_Ident (ID_Global (Name "contains")))) [((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))), (EXP_Ident (ID_Global (Name "node1")))); ((TYPE_I 64%N), (EXP_Ident (ID_Local (Anon 4%Z))))]));
                                   (IId (Anon 15%Z), (INSTR_Call ((TYPE_I 64%N), (EXP_Ident (ID_Global (Name "contains")))) [((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))), (EXP_Ident (ID_Global (Name "node1")))); ((TYPE_I 64%N), (EXP_Ident (ID_Local (Anon 5%Z))))]));
                                   (IId (Anon 16%Z), (INSTR_Call ((TYPE_I 64%N), (EXP_Ident (ID_Global (Name "contains")))) [((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))), (EXP_Ident (ID_Global (Name "node1")))); ((TYPE_I 64%N), (EXP_Ident (ID_Local (Anon 6%Z))))]));
                                   (IId (Anon 17%Z), (INSTR_Call ((TYPE_I 64%N), (EXP_Ident (ID_Global (Name "contains")))) [((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))), (EXP_Ident (ID_Global (Name "node1")))); ((TYPE_I 64%N), (EXP_Ident (ID_Local (Anon 7%Z))))]));
                                   (IId (Anon 18%Z), (INSTR_Call ((TYPE_I 64%N), (EXP_Ident (ID_Global (Name "contains")))) [((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))), (EXP_Ident (ID_Global (Name "node1")))); ((TYPE_I 64%N), (EXP_Ident (ID_Local (Anon 8%Z))))]));
                                   (IId (Anon 19%Z), (INSTR_Call ((TYPE_I 64%N), (EXP_Ident (ID_Global (Name "contains")))) [((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))), (EXP_Ident (ID_Global (Name "node1")))); ((TYPE_I 64%N), (EXP_Ident (ID_Local (Anon 9%Z))))]));
                                   (IId (Anon 20%Z), (INSTR_Call ((TYPE_I 64%N), (EXP_Ident (ID_Global (Name "contains")))) [((TYPE_Pointer (TYPE_Identified (ID_Local (Name "struct.Node")))), (EXP_Ident (ID_Global (Name "node1")))); ((TYPE_I 64%N), (EXP_Ident (ID_Local (Anon 10%Z))))]));
                                   (IId (Anon 21%Z), (INSTR_Op (OP_IBinop (Add false false) (TYPE_I 64%N) (EXP_Ident (ID_Local (Anon 11%Z))) (EXP_Ident (ID_Local (Anon 12%Z))))));
                                   (IId (Anon 22%Z), (INSTR_Op (OP_IBinop (Add false false) (TYPE_I 64%N) (EXP_Ident (ID_Local (Anon 13%Z))) (EXP_Ident (ID_Local (Anon 14%Z))))));
                                   (IId (Anon 23%Z), (INSTR_Op (OP_IBinop (Add false false) (TYPE_I 64%N) (EXP_Ident (ID_Local (Anon 15%Z))) (EXP_Ident (ID_Local (Anon 16%Z))))));
                                   (IId (Anon 24%Z), (INSTR_Op (OP_IBinop (Add false false) (TYPE_I 64%N) (EXP_Ident (ID_Local (Anon 17%Z))) (EXP_Ident (ID_Local (Anon 18%Z))))));
                                   (IId (Anon 25%Z), (INSTR_Op (OP_IBinop (Add false false) (TYPE_I 64%N) (EXP_Ident (ID_Local (Anon 19%Z))) (EXP_Ident (ID_Local (Anon 20%Z))))));
                                   (IId (Anon 26%Z), (INSTR_Op (OP_IBinop (Add false false) (TYPE_I 64%N) (EXP_Ident (ID_Local (Anon 21%Z))) (EXP_Ident (ID_Local (Anon 22%Z))))));
                                   (IId (Anon 27%Z), (INSTR_Op (OP_IBinop (Add false false) (TYPE_I 64%N) (EXP_Ident (ID_Local (Anon 23%Z))) (EXP_Ident (ID_Local (Anon 24%Z))))));
                                   (IId (Anon 28%Z), (INSTR_Op (OP_IBinop (Add false false) (TYPE_I 64%N) (EXP_Ident (ID_Local (Anon 26%Z))) (EXP_Ident (ID_Local (Anon 27%Z))))));
                                   (IId (Anon 29%Z), (INSTR_Op (OP_IBinop (Add false false) (TYPE_I 64%N) (EXP_Ident (ID_Local (Anon 28%Z))) (EXP_Ident (ID_Local (Anon 25%Z))))))];
                       blk_term := TERM_Ret ((TYPE_I 64%N), (EXP_Ident (ID_Local (Anon 29%Z))));
                       blk_comments := None
                     |},[
                   ])
     |}].

 Goal P binarysearch.
    unfold binarysearch.
   unfold mcfg_of_tle.
   unfold modul_of_toplevel_entities.
   cbn.
   unfold mcfg_of_modul; cbn.
   unfold cfg_of_definition.
   cbn.
 Abort.
  *)
 
End SurfaceSyntaxTest.
