(* begin hide *)
From Coq Require Import List ZArith String.
Import ListNotations.
Open Scope Z.
From Vellvm Require Import
     Syntax.LLVMAst
     Syntax.CFG
     Syntax.DynamicTypes.
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

  (** * Identifiers *)
  Notation "'%' x" := (ID_Local x)  (only printing, at level 5, format "'%' x").
  Notation "'@' x" := (ID_Global x) (only printing, at level 5, format "'@' x").
  Coercion Name : string >-> raw_id.
  Coercion Anon : int >-> raw_id.

  (** * Expressions *)

  (* Unfortunately, simply ignoring the constructor does not get
     rid of the surrounding parentheses.
     I am not aware of any way to circumvent this.
   *)
  (* Coercion EXP_Ident : ident >-> exp. *)
  (* Coercion EXP_Integer : int >-> exp. *)
  (* Coercion EXP_Float : float32 >-> exp. *)
  (* Coercion EXP_Double : float >-> exp. *)
  (* Coercion EXP_Hex : float >-> exp. *)
  (* Coercion EXP_Bool : bool >-> exp. *)
  Notation "i" := (EXP_Ident i)   (at level 10,only printing).
  Notation "e" := (EXP_Integer e) (at level 10,only printing).
  Notation "f" := (EXP_Float f)   (at level 10,only printing).
  Notation "d" := (EXP_Double d)   (at level 10,only printing).
  Notation "h" := (EXP_Hex h)   (at level 10,only printing).
  Notation "b" := (EXP_Bool b)   (at level 10,only printing).
  Notation "'null'" := (EXP_Null)   (at level 10,only printing). 
  Notation "'zeroinitializer'" := (EXP_Zero_initializer)   (at level 10,only printing). 
  (* Coercion EXP_Cstring : string >-> exp. *)
  Notation "s" := (EXP_Cstring s)   (at level 10,only printing).
  Notation "'undef'" := (EXP_Undef)   (at level 10,only printing). 
  
  (* ibinop *)

  (* We only display the wrapping flags that are either true, or parametric.
     Be wary that the parametric case must be declared first for the particular
     cases to take precedence.
   *)
  Notation "'add' nuw nsw e f"     :=
    (OP_IBinop (Add nuw nsw) _ e f)     (at level 20, only printing).
  Notation "'add' e f"             :=
    (OP_IBinop (Add false false) _ e f) (at level 20, only printing).
  Notation "'add' 'nuw' e f"       :=
    (OP_IBinop (Add true false) _ e f)  (at level 20, only printing).
  Notation "'add' 'nsw' e f"       :=
    (OP_IBinop (Add false true) _ e f)  (at level 20, only printing).
  Notation "'add' 'nuw' 'nsw' e f" :=
    (OP_IBinop (Add true true) _ e f)   (at level 20, only printing).

  Notation "'sub' nuw nsw e f"     :=
    (OP_IBinop (Sub nuw nsw) _ e f)     (at level 20, only printing).
  Notation "'sub' e f"             :=
    (OP_IBinop (Sub false false) _ e f) (at level 20, only printing).
  Notation "'sub' 'nuw' e f"       :=
    (OP_IBinop (Sub true false) _ e f)  (at level 20, only printing).
  Notation "'sub' 'nsw' e f"       :=
    (OP_IBinop (Sub false true) _ e f)  (at level 20, only printing).
  Notation "'sub' 'nuw' 'nsw' e f" :=
    (OP_IBinop (Sub true true) _ e f)   (at level 20, only printing).

  Notation "'mul' nuw nsw e f"     :=
    (OP_IBinop (Mul nuw nsw) _ e f)     (at level 20, only printing).
  Notation "'mul' e f"             :=
    (OP_IBinop (Mul false false) _ e f) (at level 20, only printing).
  Notation "'mul' 'nuw' e f"       :=
    (OP_IBinop (Mul true false) _ e f)  (at level 20, only printing).
  Notation "'mul' 'nsw' e f"       :=
    (OP_IBinop (Mul false true) _ e f)  (at level 20, only printing).
  Notation "'mul' 'nuw' 'nsw' e f" :=
    (OP_IBinop (Mul true true) _ e f)   (at level 20, only printing).

  Notation "'shl' nuw nsw e f"     :=
    (OP_IBinop (Shl nuw nsw) _ e f)     (at level 20, only printing).
  Notation "'shl' e f"             :=
    (OP_IBinop (Shl false false) _ e f) (at level 20, only printing).
  Notation "'shl' 'nuw' e f"       :=
    (OP_IBinop (Shl true false) _ e f)  (at level 20, only printing).
  Notation "'shl' 'nsw' e f"       :=
    (OP_IBinop (Shl false true) _ e f)  (at level 20, only printing).
  Notation "'shl' 'nuw' 'nsw' e f" :=
    (OP_IBinop (Shl true true) _ e f)   (at level 20, only printing).

  Notation "'udiv' exact e f" :=
    (OP_IBinop (UDiv exact) _ e f) (at level 20, only printing).
  Notation "'udiv' e f" :=
    (OP_IBinop (UDiv false) _ e f) (at level 20, only printing).
  Notation "'udiv' 'exact' e f" :=
    (OP_IBinop (UDiv true) _ e f)  (at level 20, only printing).

  Notation "'sdiv' exact e f" :=
    (OP_IBinop (SDiv exact) _ e f) (at level 20, only printing).
  Notation "'sdiv' e f" :=
    (OP_IBinop (SDiv false) _ e f) (at level 20, only printing).
  Notation "'sdiv' 'exact' e f" :=
    (OP_IBinop (SDiv true) _ e f)  (at level 20, only printing).

  Notation "'lshr' exact e f" :=
    (OP_IBinop (LShr exact) _ e f) (at level 20, only printing).
  Notation "'lshr' e f" :=
    (OP_IBinop (LShr false) _ e f) (at level 20, only printing).
  Notation "'lshr' 'exact' e f" :=
    (OP_IBinop (LShr true) _ e f)  (at level 20, only printing).

  Notation "'ashr' exact e f" :=
    (OP_IBinop (AShr exact) _ e f) (at level 20, only printing).
  Notation "'ashr' e f" :=
    (OP_IBinop (AShr false) _ e f) (at level 20, only printing).
  Notation "'ashr' 'exact' e f" :=
    (OP_IBinop (AShr true) _ e f)  (at level 20, only printing).

  Notation "'urem' e f" := (OP_IBinop URem _ e f) (at level 20, only printing).
  Notation "'srem' e f" := (OP_IBinop SRem _ e f) (at level 20, only printing).
  Notation "'and' e f"  := (OP_IBinop And _ e f)  (at level 20, only printing).
  Notation "'or' e f"   := (OP_IBinop Or _ e f)   (at level 20, only printing).
  Notation "'xor' e f"  := (OP_IBinop Xor _ e f)  (at level 20, only printing).

  (* icmp *)
  Notation "'eq' e f"   := (OP_ICmp Eq _ e f)                  (at level 20, only printing).
  Notation "'ne' e f"   := (OP_ICmp Ne _ e f)                  (at level 20, only printing).
  Notation "'ugt' e f"  := (OP_ICmp Ugt _ e f)                 (at level 20, only printing).
  Notation "'uge' e f"  := (OP_ICmp Uge _ e f)                 (at level 20, only printing).
  Notation "'ult' e f"  := (OP_ICmp Ult _ e f)                 (at level 20, only printing).
  Notation "'ule' e f"  := (OP_ICmp Ule _ e f)                 (at level 20, only printing).
  Notation "'sgt' e f"  := (OP_ICmp Sgt _ e f)                 (at level 20, only printing).
  Notation "'sge' e f"  := (OP_ICmp Sge _ e f)                 (at level 20, only printing).
  Notation "'slt' e f"  := (OP_ICmp Slt _ e f)                 (at level 20, only printing).
  Notation "'sle' e f"  := (OP_ICmp Sle _ e f)                 (at level 20, only printing).


  (** * Instructions *)

  Notation "r '=' 'op' x" := ((IId r, INSTR_Op x)) (at level 30, only printing).

  Notation "r '=' 'call' x args" := ((IId r, INSTR_Call x args)) (at level 30, only printing).
  Notation "'call' x args" := ((IVoid, INSTR_Call x args)) (at level 30, only printing).

  Notation "r '=' 'alloca' t ',' size ',' 'align' align" :=
    ((IId r, INSTR_Alloca t size align)) (at level 30, only printing).
  Notation "r '=' 'alloca' t ',' size" :=
    ((IId r, INSTR_Alloca t size None)) (at level 30, only printing).
  Notation "r '=' 'alloca' t ',' size" :=
    ((IId r, INSTR_Alloca t (Some size) None)) (at level 30, only printing).
  Notation "r '=' 'alloca' t ',' 'align' align" :=
    ((IId r, INSTR_Alloca t None align)) (at level 30, only printing).
  Notation "r '=' 'alloca' t ',' 'align' align" :=
    ((IId r, INSTR_Alloca t None (Some align))) (at level 30, only printing).
  Notation "r '=' 'alloca' t ',' size ',' 'align' align" :=
    ((IId r, INSTR_Alloca t (Some size) (Some align))) (at level 30, only printing).
  Notation "r '=' 'alloca' t" :=
    ((IId r, INSTR_Alloca t None None)) (at level 30, only printing).

  Notation "r '=' 'load' v t ',' e ',' 'align' align" :=
    ((IId r, INSTR_Load v t e align)) (at level 30, only printing).
  Notation "r '=' 'load' v t ',' e ',' 'align' align" :=
    ((IId r, INSTR_Load v t e (Some align))) (at level 30, only printing).
  Notation "r '=' 'load' v t ',' e" :=
    ((IId r, INSTR_Load v t e None)) (at level 30, only printing).
   Notation "r '=' 'load' v t ',' e" :=
    ((IId r, INSTR_Load v t e None)) (at level 30, only printing).
  Notation "r '=' 'load' t ',' e" := ((IId r, INSTR_Load _ t e _)) (at level 30, only printing).
  Notation "r '=' 'load' t ',' e" := ((IId r, INSTR_Load _ t e _)) (at level 30, only printing).
  Notation "r '=' 'load' t ',' e" := ((IId r, INSTR_Load _ t e _)) (at level 30, only printing).

  Notation "r '=' 'store' e ',' f" := ((IId r, INSTR_Store _ e f _)) (at level 30, only printing).

  (** * Terminators *)
  Notation "'ret' τ e" := (TERM_Ret (τ, e)) (at level 30, only printing).
  Notation "'ret' 'void'" := (TERM_Ret_void) (at level 30, only printing).
  Notation "'br' c ',' 'label' e ',' 'label' f" := (TERM_Br c e f) (at level 30, only printing).
  Notation "'br' 'label' e" := (TERM_Br_1 e) (at level 30, only printing).

  (** * Phi-nodes *)
  Notation "x ← 'Φ' xs" := (x,Phi _ xs) (at level 30,only printing).

  (** * Types *)
  Notation "'ι' x" := (DTYPE_I x) (at level 10,only printing, format "'ι' x").
  Notation "⋆" := (DTYPE_Pointer) (at level 10,only printing).
  Notation "'ι' x" := (TYPE_I x) (at level 10,only printing, format "'ι' x").
  Notation "⋆" := (TYPE_Pointer) (at level 10,only printing).

  (* Notation "x" := (convert_typ _ x) (at level 10, only printing). *)
  (* Notation "x" := (typ_to_dtyp _ x) (at level 10, only printing). *)
  (* Notation "x" := (fmap (typ_to_dtyp _) x) (at level 10, only printing). *)

  (** * Modul  *)
  Notation "x" := (mk_modul _ _ _ _ _ _ x) (at level 10, only printing).

  (** * Definitions  *)
  Notation "'func' f args ':=' x" :=
    (mk_definition _ (mk_declaration (Name f) _ _ _ _ _ _ _ _ _ _)
                   args x) (at level 10, only printing,
                            format "'func'  f  args  ':=' '//' x").
 
  (** * cfg  *)
  Notation "bks" := (mkCFG _ bks _) (at level 10, only printing).

  (** * Blocks  *)
  Notation "label ':' phis code term" :=
    (mk_block label phis code term _)
      (at level 10, only printing,
       format "label ':' '//' phis '//' code '//' term").

End VIR_Notations.

Section SurfaceSyntaxTest.
  
  Definition add_twice := mcfg_of_tle [TLE_Definition {|
                               df_prototype := {|dc_name := (Name "main");
                                                 dc_type := (TYPE_Function (TYPE_I 32%N) [(TYPE_I 32%N); (TYPE_Pointer (TYPE_Pointer (TYPE_I 8%N)))]);
                                                 dc_param_attrs := ([], [
                                                                   ]);
                                                 dc_linkage := None;
                                                 dc_visibility := None;
                                                 dc_dll_storage := None;
                                                 dc_cconv := None;
                                                 dc_attrs := [];
                                                 dc_section := None;
                                                 dc_align := None;
                                                 dc_gc := None|};
                               df_args := [(Name "argc"); (Name "arcv")];
                               df_instrs := (
                                             {|
                                               blk_id := (Anon 0%Z);
                                               blk_phis := [];
                                               blk_code := [(IId (Anon 1%Z), (INSTR_Op (OP_IBinop (Add false false) (TYPE_I 32%N) (EXP_Integer (5)%Z) (EXP_Integer (9)%Z))));
                                                           (IId (Anon 2%Z), (INSTR_Op (OP_IBinop (Add false false) (TYPE_I 32%N) (EXP_Ident (ID_Local (Anon 1%Z))) (EXP_Integer (15)%Z))))];
                                               blk_term := TERM_Ret ((TYPE_I 32%N), (EXP_Ident (ID_Local (Anon 2%Z))));
                                               blk_comments := None
                                             |}
                                           ,[])
                             |}].
  
 Import VIR_Notations .

End SurfaceSyntaxTest.

