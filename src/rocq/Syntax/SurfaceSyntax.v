(* begin hide *)
From Vellvm Require Import
  Utils
  Syntax.LLVMAst
  Syntax.CFG
  Syntax.DynamicTypes.
Open Scope Z.

(* The three block printers (label-only / no-phis / full) share the
   LHS prefix [label ':' ...]. Rocq's parser flags this with
   [notation-incompatible-prefix] — but the warning is parse-direction
   only, and our printers are [only printing], so the dispatch happens
   via RHS pattern specificity, not LHS prefix matching. Restructuring
   to distinct prefixes would require non-LLVM-IR keywords for the
   block shapes (e.g. [label ':-'] for empty-phis), so we keep the
   shared prefix and silence the warning. The suppression is at file
   scope because Rocq re-runs the prefix check at every
   [Import VIR_Notations] site, where local suppressions don't reach. *)
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

(** ** Known limitations and future work

    The notations cover most of the AST surface area in current research
    goals. Items below are open and could be picked up in any order; none
    are blockers.

    *** Constructors without a surface notation
    - [EXP_Asm] (six-arg constructor): rare in research goals; falls
      through to constr display.
    - [TLE_Module_asm], [TLE_Comdat]: do not exist in the current AST
      (mentioned in older versions). [TLE_Source_filename] etc. covered.
    - [mk_modul]'s [m_type_defs : list (ident * T)] has no compact
      list-printer dispatch.
    - [mk_global] variants with non-empty annotations or [g_alias = true]
      combined with annotations have no compact shape; fall through to
      record-syntax display.
    - Bodies of opaque records ([cmpxchg], [atomicrmw], [ordering],
      [landingpad_clause]): the surrounding [INSTR_*] constructors have
      tagged shapes ([cmpxchg c], [atomicrmw a], [fence o],
      [landingpad t]) but the inner record fields display via
      constr-escape.

    *** Cosmetic display gaps
    - Identifiers built via [Name "x"] display with the string quotes
      (e.g. [%"a"], ["entry":]). Removing the quotes would require
      overriding Rocq's string display, which is not localized to this
      file.
    - Phi-only blocks (phis non-empty, code [nil]) render the empty code
      list as [{[]}] in the middle of the block. Adding a dedicated
      "phis-only" block shape would conflict with the existing empty-phis
      shape (Rocq forbids two notations with same LHS-token shape but
      different custom-entry argument types).
    - Lists separated by commas have no space after the comma in some
      output (e.g. phi-args, GEP indices). Cosmetic; fixable via
      [format] strings.
    - Multi-annotation patterns like [[ANN_volatile; ANN_align 4]] take
      the [vir_anns] general dispatch path but the format may need
      tuning case-by-case.

    *** Design considerations explored and deferred
    - Bind Scope auto-dispatch to drop the visible [%X] prefix when
      printing typed terms at constr level: Rocq's notation system
      requires at least one literal token in the LHS of a constr-level
      notation, so pure-metavariable bare-LHS rules don't fire. The [%X]
      prefix is the unavoidable visible cost of dispatching into a
      custom entry.
    - The file-scope [Set Warnings "-notation-incompatible-prefix"] is
      needed for the three block-printer shapes that share the
      [label ':' ...] prefix. Restructuring would require non-LLVM-IR
      keywords for the empty-shape variants.

    *** Hygiene / known maintenance traps
    - The wrapped-vs-bare integer literal trick ([Notation "n" :=
      (EXP_Integer (Z.to_num_int n))] before [Notation "n" := (EXP_Integer n)])
      is repeated for every constructor that takes [int_syntax]. Adding
      a new such constructor (e.g. a future [ANN_*] taking [int_syntax])
      requires the same dual-rule pattern.
    - Notations with shared LHS prefix (block printers, fp-conversion
      empty/non-empty fmf, alloca/load/store with multiple annotation
      shapes) rely on RHS specificity for printer dispatch. If the
      printer's specificity heuristic ever changes, these need
      revisiting.
    - Signature drift between the AST and the notations file is a real
      risk: this file accumulated five drift bugs across constructors
      ([OP_FBinop], [OP_ICmp], [func]'s declaration arity, [Or],
      [mk_definition] arity) before being audited. New AST changes
      should be cross-referenced against this file. *)

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
  Declare Custom Entry vir_iidx_list.   (* integer index list: OP_Extract/InsertValue *)

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
  Notation "'iptr'"     := TYPE_Iptr     (in custom vir_typ at level 5, only printing).
  Notation "'label'"    := TYPE_Label    (in custom vir_typ at level 5, only printing).
  Notation "'label'"    := DTYPE_Label   (in custom vir_typ at level 5, only printing).
  Notation "'token'"    := TYPE_Token    (in custom vir_typ at level 5, only printing).
  Notation "'metadata'" := TYPE_Metadata (in custom vir_typ at level 5, only printing).
  Notation "'opaque'"   := TYPE_Opaque   (in custom vir_typ at level 5, only printing).

  (** Array, vector. LLVM IR uses [[N x T]] for arrays and [<N x T>]
      for vectors. *)
  Notation "'[' sz 'x' t ']'" := (TYPE_Array false sz t)
    (in custom vir_typ at level 5,
     sz constr at level 0, t custom vir_typ at level 99,
     only printing).
  Notation "'[' sz 'x' t ']'" := (DTYPE_Array false sz t)
    (in custom vir_typ at level 5,
     sz constr at level 0, t custom vir_typ at level 99,
     only printing).
  Notation "'<' sz 'x' t '>'" := (TYPE_Array true sz t)
    (in custom vir_typ at level 5,
     sz constr at level 0, t custom vir_typ at level 99,
     only printing).
  Notation "'<' sz 'x' t '>'" := (DTYPE_Array true sz t)
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
  Notation "'{|' fields '|}'" := (TYPE_Struct false fields)
    (in custom vir_typ at level 5,
     fields custom vir_typ_list at level 99,
     only printing).
  Notation "'{|' fields '|}'" := (DTYPE_Struct false fields)
    (in custom vir_typ at level 5,
     fields custom vir_typ_list at level 99,
     only printing).
  Notation "'<{' '}>'" := (TYPE_Packed_struct nil)
    (in custom vir_typ at level 5, only printing).
  Notation "'<{' '}>'" := (DTYPE_Struct true nil)
    (in custom vir_typ at level 5, only printing).
  Notation "'<{' fields '}>'" := (TYPE_Packed_struct fields)
    (in custom vir_typ at level 5,
     fields custom vir_typ_list at level 99,
     only printing).
  Notation "'<{' fields '}>'" := (DTYPE_Struct true fields)
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
  Notation "'undef'"           := EXP_Undef            (in custom vir_exp at level 0, only printing).
  Notation "'poison'"          := EXP_Poison           (in custom vir_exp at level 0, only printing).
  (** Floating-point literal. Uses a [fp] tag because the bare-LHS slot
      in [vir_exp] is taken by [EXP_Integer]. The body of the literal
      ([float_syntax]) displays through the constr-escape. *)
  Notation "'fp' f" := (EXP_Float f)
    (in custom vir_exp at level 0, f constr at level 0, only printing).
  (** Metadata expression — opaque, displayed as bare constr. *)
  Notation "'meta' m" := (EXP_Metadata m)
    (in custom vir_exp at level 0, m constr at level 0, only printing).
  (** Splat: replicate a single typed value across a vector. *)
  Notation "'splat' τ v" := (EXP_Splat (τ, v))
    (in custom vir_exp at level 5,
     τ custom vir_typ at level 99,
     v custom vir_exp at level 99,
     only printing).
  (** [EXP_Asm] (6 args, very rare in research goals) intentionally
      not given a notation — falls through to constr display. *)
  (** Booleans: each maps to the literal value-keyed [EXP_Bool] case.
      No bare-LHS conflict because the LHS is a literal, not a metavar. *)
  Notation "'true'"  := (EXP_Bool true)  (in custom vir_exp at level 0, only printing).
  Notation "'false'" := (EXP_Bool false) (in custom vir_exp at level 0, only printing).
  (** C-string literals. The AST stores them as a [list (T * exp)] of
      typed byte-values, so we dispatch the elements through
      [vir_idx_list] (the [τ v] element rule shared with GEP indices). *)
  Notation "'c' '[' elts ']'" := (EXP_Cstring elts)
    (in custom vir_exp at level 0,
     elts custom vir_idx_list at level 99,
     only printing).

  (** Composite literals. Same [vir_idx_list] dispatch for element
      lists. Brackets follow LLVM IR conventions where they don't
      collide with constr-level escape:
        - struct        [{| f1, f2 |}]   (cannot reuse plain [{ }])
        - packed struct [<{ f1, f2 }>]
        - array         [[ e1, e2 ]]     ([t] is wildcarded; each elt
                                          carries its own type)
        - vector        [< e1, e2 >]     (same)
   *)
  Notation "'{|' fields '|}'" := (EXP_Struct fields)
    (in custom vir_exp at level 0,
     fields custom vir_idx_list at level 99, only printing).
  Notation "'<{' fields '}>'" := (EXP_Packed_struct fields)
    (in custom vir_exp at level 0,
     fields custom vir_idx_list at level 99, only printing).
  Notation "'[' elts ']'" := (EXP_Array _ elts)
    (in custom vir_exp at level 0,
     elts custom vir_idx_list at level 99, only printing).
  Notation "'<' elts '>'" := (EXP_Vector _ elts)
    (in custom vir_exp at level 0,
     elts custom vir_idx_list at level 99, only printing).

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
  (** [Or] takes a [disjoint:bool] flag now (was nullary). *)
  Notation "'or' e ',' f"            := (OP_IBinop (Or false) _ e f) (in custom vir_exp at level 20, only printing).
  Notation "'or' 'disjoint' e ',' f" := (OP_IBinop (Or true)  _ e f) (in custom vir_exp at level 20, only printing).
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
    (OP_Conversion (CONV_Pure (Trunc false false)) τfrom v τto)
    (in custom vir_exp at level 20,
     τfrom custom vir_typ at level 99, v custom vir_exp at level 99,
     τto   custom vir_typ at level 99, only printing).
  Notation "'trunc' 'nuw' τfrom v 'to' τto" :=
    (OP_Conversion (CONV_Pure (Trunc true false)) τfrom v τto)
    (in custom vir_exp at level 20,
     τfrom custom vir_typ at level 99, v custom vir_exp at level 99,
     τto   custom vir_typ at level 99, only printing).
  Notation "'trunc' 'nsw' τfrom v 'to' τto" :=
    (OP_Conversion (CONV_Pure (Trunc false true)) τfrom v τto)
    (in custom vir_exp at level 20,
     τfrom custom vir_typ at level 99, v custom vir_exp at level 99,
     τto   custom vir_typ at level 99, only printing).
  Notation "'trunc' 'nuw' 'nsw' τfrom v 'to' τto" :=
    (OP_Conversion (CONV_Pure (Trunc true true)) τfrom v τto)
    (in custom vir_exp at level 20,
     τfrom custom vir_typ at level 99, v custom vir_exp at level 99,
     τto   custom vir_typ at level 99, only printing).

  Notation "'zext' τfrom v 'to' τto" :=
    (OP_Conversion (CONV_Pure (Zext false)) τfrom v τto)
    (in custom vir_exp at level 20,
     τfrom custom vir_typ at level 99, v custom vir_exp at level 99,
     τto   custom vir_typ at level 99, only printing).
  Notation "'zext' 'nneg' τfrom v 'to' τto" :=
    (OP_Conversion (CONV_Pure (Zext true)) τfrom v τto)
    (in custom vir_exp at level 20,
     τfrom custom vir_typ at level 99, v custom vir_exp at level 99,
     τto   custom vir_typ at level 99, only printing).

  Notation "'sext' τfrom v 'to' τto" :=
    (OP_Conversion (CONV_Pure Sext) τfrom v τto)
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
    (OP_Conversion (CONV_Pure (Fptrunc [])) τfrom v τto)
    (in custom vir_exp at level 20,
     τfrom custom vir_typ at level 99, v custom vir_exp at level 99,
     τto   custom vir_typ at level 99, only printing).
  Notation "'fptrunc' '[' fmf ']' τfrom v 'to' τto" :=
    (OP_Conversion (CONV_Pure (Fptrunc fmf)) τfrom v τto)
    (in custom vir_exp at level 20,
     fmf custom vir_fmf at level 99,
     τfrom custom vir_typ at level 99, v custom vir_exp at level 99,
     τto   custom vir_typ at level 99, only printing).
  Notation "'fpext' τfrom v 'to' τto" :=
    (OP_Conversion (CONV_Pure (Fpext [])) τfrom v τto)
    (in custom vir_exp at level 20,
     τfrom custom vir_typ at level 99, v custom vir_exp at level 99,
     τto   custom vir_typ at level 99, only printing).
  Notation "'fpext' '[' fmf ']' τfrom v 'to' τto" :=
    (OP_Conversion (CONV_Pure (Fpext fmf)) τfrom v τto)
    (in custom vir_exp at level 20,
     fmf custom vir_fmf at level 99,
     τfrom custom vir_typ at level 99, v custom vir_exp at level 99,
     τto   custom vir_typ at level 99, only printing).

  Notation "'uitofp' τfrom v 'to' τto" :=
    (OP_Conversion (CONV_Pure (Uitofp false)) τfrom v τto)
    (in custom vir_exp at level 20,
     τfrom custom vir_typ at level 99, v custom vir_exp at level 99,
     τto   custom vir_typ at level 99, only printing).
  Notation "'uitofp' 'nneg' τfrom v 'to' τto" :=
    (OP_Conversion (CONV_Pure (Uitofp true)) τfrom v τto)
    (in custom vir_exp at level 20,
     τfrom custom vir_typ at level 99, v custom vir_exp at level 99,
     τto   custom vir_typ at level 99, only printing).

  Notation "'sitofp'    τfrom v 'to' τto" := (OP_Conversion (CONV_Pure Sitofp)        τfrom v τto)
    (in custom vir_exp at level 20, τfrom custom vir_typ at level 99,
     v custom vir_exp at level 99, τto custom vir_typ at level 99, only printing).
  Notation "'fptoui'    τfrom v 'to' τto" := (OP_Conversion (CONV_Pure Fptoui)        τfrom v τto)
    (in custom vir_exp at level 20, τfrom custom vir_typ at level 99,
     v custom vir_exp at level 99, τto custom vir_typ at level 99, only printing).
  Notation "'fptosi'    τfrom v 'to' τto" := (OP_Conversion (CONV_Pure Fptosi)        τfrom v τto)
    (in custom vir_exp at level 20, τfrom custom vir_typ at level 99,
     v custom vir_exp at level 99, τto custom vir_typ at level 99, only printing).
  Notation "'inttoptr'  τfrom v 'to' τto" := (OP_Conversion (CONV_Impure Inttoptr)      τfrom v τto)
    (in custom vir_exp at level 20, τfrom custom vir_typ at level 99,
     v custom vir_exp at level 99, τto custom vir_typ at level 99, only printing).
  Notation "'ptrtoint'  τfrom v 'to' τto" := (OP_Conversion (CONV_Impure Ptrtoint)      τfrom v τto)
    (in custom vir_exp at level 20, τfrom custom vir_typ at level 99,
     v custom vir_exp at level 99, τto custom vir_typ at level 99, only printing).
  Notation "'ptrtoaddr'  τfrom v 'to' τto" := (OP_Conversion (CONV_Impure Ptrtoaddr)      τfrom v τto)
    (in custom vir_exp at level 20, τfrom custom vir_typ at level 99,
     v custom vir_exp at level 99, τto custom vir_typ at level 99, only printing).
  Notation "'bitcast'   τfrom v 'to' τto" := (OP_Conversion CONV_Bitcast       τfrom v τto)
    (in custom vir_exp at level 20, τfrom custom vir_typ at level 99,
     v custom vir_exp at level 99, τto custom vir_typ at level 99, only printing).
  Notation "'addrspacecast' τfrom v 'to' τto" := (OP_Conversion (CONV_Impure Addrspacecast) τfrom v τto)
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

  (** ** Aggregate / vector ops. *)
  Notation "'extractelement' τv vec ',' τi idx" :=
    (OP_ExtractElement (τv, vec) (τi, idx))
    (in custom vir_exp at level 20,
     τv custom vir_typ at level 99, vec custom vir_exp at level 99,
     τi custom vir_typ at level 99, idx custom vir_exp at level 99,
     only printing).
  Notation "'insertelement' τv vec ',' τe elt ',' τi idx" :=
    (OP_InsertElement (τv, vec) (τe, elt) (τi, idx))
    (in custom vir_exp at level 20,
     τv custom vir_typ at level 99, vec custom vir_exp at level 99,
     τe custom vir_typ at level 99, elt custom vir_exp at level 99,
     τi custom vir_typ at level 99, idx custom vir_exp at level 99,
     only printing).
  Notation "'shufflevector' τ1 v1 ',' τ2 v2 ',' τm m" :=
    (OP_ShuffleVector (τ1, v1) (τ2, v2) (τm, m))
    (in custom vir_exp at level 20,
     τ1 custom vir_typ at level 99, v1 custom vir_exp at level 99,
     τ2 custom vir_typ at level 99, v2 custom vir_exp at level 99,
     τm custom vir_typ at level 99, m  custom vir_exp at level 99,
     only printing).

  (** [extractvalue] / [insertvalue] take an [int_syntax] index list
      (not typed). Dispatched through [vir_iidx_list]. *)
  Notation "'extractvalue' τv vec ',' idxs" :=
    (OP_ExtractValue (τv, vec) idxs)
    (in custom vir_exp at level 20,
     τv custom vir_typ at level 99, vec custom vir_exp at level 99,
     idxs custom vir_iidx_list at level 99,
     only printing).
  Notation "'insertvalue' τv vec ',' τe elt ',' idxs" :=
    (OP_InsertValue (τv, vec) (τe, elt) idxs)
    (in custom vir_exp at level 20,
     τv custom vir_typ at level 99, vec custom vir_exp at level 99,
     τe custom vir_typ at level 99, elt custom vir_exp at level 99,
     idxs custom vir_iidx_list at level 99,
     only printing).

  (** Float negation. Two shapes for empty / non-empty fast-math flags
      (same recipe as [fptrunc]/[fpext]). *)
  Notation "'fneg' τ v" := (OP_Fneg [] (τ, v))
    (in custom vir_exp at level 20,
     τ custom vir_typ at level 99, v custom vir_exp at level 99,
     only printing).
  Notation "'fneg' '[' fmf ']' τ v" := (OP_Fneg fmf (τ, v))
    (in custom vir_exp at level 20,
     fmf custom vir_fmf at level 99,
     τ custom vir_typ at level 99, v custom vir_exp at level 99,
     only printing).

  (** Freeze. *)
  Notation "'freeze' τ v" := (OP_Freeze (τ, v))
    (in custom vir_exp at level 20,
     τ custom vir_typ at level 99, v custom vir_exp at level 99,
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

  (** ** Less common instructions: comments, fences, atomics, varargs,
        landing pads. Bodies of opaque records ([cmpxchg], [atomicrmw],
        [ordering]) display via constr-escape. *)
  Notation "'#comment' msg" :=
    (_, INSTR_Comment msg, _)
    (in custom vir_instr at level 30, msg constr at level 0, only printing).
  Notation "'fence' o" :=
    (_, INSTR_Fence _ o, _)
    (in custom vir_instr at level 30, o constr at level 0, only printing).
  Notation "r '=' 'cmpxchg' c" :=
    (IId r, INSTR_AtomicCmpXchg c, _)
    (in custom vir_instr at level 30,
     r constr at level 0, c constr at level 0, only printing).
  Notation "r '=' 'atomicrmw' a" :=
    (IId r, INSTR_AtomicRMW a, _)
    (in custom vir_instr at level 30,
     r constr at level 0, a constr at level 0, only printing).
  Notation "r '=' 'va_arg' τv v ',' τ" :=
    (IId r, INSTR_VAArg (τv, v) τ, _)
    (in custom vir_instr at level 30,
     r constr at level 0,
     τv custom vir_typ at level 99, v custom vir_exp at level 99,
     τ custom vir_typ at level 99,
     only printing).
  Notation "r '=' 'landingpad' t" :=
    (IId r, INSTR_LandingPad t _ _, _)
    (in custom vir_instr at level 30,
     r constr at level 0,
     t custom vir_typ at level 99,
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
  (** [TERM_Invoke] — six args; we wildcard the param-attr-laden args
      list, the annotations, and the operand bundles. The function
      pointer's type and value display through their respective custom
      entries. *)
  Notation "'invoke' τfn fn 'to' 'label' to_lbl 'unwind' 'label' unwind_lbl" :=
    (_, TERM_Invoke (τfn, fn) _ to_lbl unwind_lbl _ _, _)
    (in custom vir_term at level 30,
     τfn custom vir_typ at level 99, fn custom vir_exp at level 99,
     to_lbl constr at level 0, unwind_lbl constr at level 0,
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

  (** vir_iidx_list — integer index list [list int_syntax] for
      [extractvalue] / [insertvalue]. Each element is a bare integer;
      the wrapped variant strips [Z.to_num_int] (same trick as
      [EXP_Integer]). *)
  Notation "( l )" := l
    (in custom vir_iidx_list at level 0, l custom vir_iidx_list at level 99, only printing).
  Notation "{ l }" := l
    (in custom vir_iidx_list at level 0, l constr, only printing).
  Notation "n" := (Z.to_num_int n)
    (in custom vir_iidx_list at level 5, n constr at level 0, only printing).
  Notation "n" := n
    (in custom vir_iidx_list at level 5, n constr at level 0, only printing).
  Notation "i ',' .. ',' j" :=
    (cons i .. (cons j nil) ..)
    (in custom vir_iidx_list at level 99,
     i custom vir_iidx_list at level 5,
     j custom vir_iidx_list at level 5,
     only printing,
     format "i ',' .. ',' j").

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

  (** [mk_global] compact shapes. The common cases:
        - non-constant global with initializer: [global x : t := e]
        - constant global with initializer:     [constant x : t := e]
        - external (no initializer):            [extern x : t]
        - global alias:                         [alias x : t := e]
      Each variant assumes empty annotations and the relevant default
      flags. Anything outside these shapes falls through to record
      display. *)
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
  Notation "'extern' x ':' t" :=
    (mk_global x t false None true false nil)
    (at level 10, t custom vir_typ at level 99,
     only printing).
  Notation "'alias' x ':' t ':=' e" :=
    (mk_global x t false (Some e) false true nil)
    (at level 10, t custom vir_typ at level 99,
     e custom vir_exp at level 99,
     only printing).

  (** [mk_declaration] compact shape. Used for external function
      declarations in [m_declarations]. Param attrs / fn attrs /
      annotations all wildcarded — the common case is just name+type. *)
  Notation "'declare' x ':' t" :=
    (mk_declaration x t _ _ _)
    (at level 10,
     x constr at level 0,
     t custom vir_typ at level 99,
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
  Notation "'#metadata' id ',' distinct ',' md" := (TLE_Metadata id distinct md)
    (at level 10,
     id constr at level 0, distinct constr at level 0, md constr at level 0,
     only printing).
  Notation "'#attrgroup' i attrs" := (TLE_Attribute_group i attrs)
    (at level 10,
     i constr at level 0, attrs constr at level 0,
     only printing).

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

 
End SurfaceSyntaxTest.
