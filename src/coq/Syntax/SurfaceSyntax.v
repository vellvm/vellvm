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
  Coercion Anon : int_ast >-> raw_id.

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

  (* fbinop *)
  Notation "'fadd' e f" := (OP_FBinop FAdd _ e f) (at level 20, only printing).
  Notation "'fsub' e f" := (OP_FBinop FSub _ e f) (at level 20, only printing).
  Notation "'fmul' e f" := (OP_FBinop FMul _ e f) (at level 20, only printing).
  Notation "'fdiv' e f" := (OP_FBinop FDiv _ e f) (at level 20, only printing).
  Notation "'frem' e f" := (OP_FBinop FRem _ e f) (at level 20, only printing).

  (* fcmp *)
  Notation "'false'"     := (OP_FCmp FFalse _ _ _) (at level 20, only printing).
  Notation "'true'"      := (OP_FCmp FTrue _ _ _)  (at level 20, only printing).
  Notation "'oeq' e f"   := (OP_FCmp FOeq _ e f)   (at level 20, only printing).
  Notation "'ogt' e f"   := (OP_FCmp FOgt _ e f)   (at level 20, only printing).
  Notation "'oge' e f"   := (OP_FCmp FOge _ e f)   (at level 20, only printing).
  Notation "'olt' e f"   := (OP_FCmp FOlt _ e f)   (at level 20, only printing).
  Notation "'ole' e f"   := (OP_FCmp FOle _ e f)   (at level 20, only printing).
  Notation "'one' e f"   := (OP_FCmp FOne _ e f)   (at level 20, only printing).
  Notation "'ord' e f"   := (OP_FCmp FOrd _ e f)   (at level 20, only printing).
  Notation "'uno' e f"   := (OP_FCmp FUno _ e f)   (at level 20, only printing).
  Notation "'ueq' e f"   := (OP_FCmp FUeq _ e f)   (at level 20, only printing).
  Notation "'ugt' e f"   := (OP_FCmp FUgt _ e f)   (at level 20, only printing).
  Notation "'uge' e f"   := (OP_FCmp FUge _ e f)   (at level 20, only printing).
  Notation "'ult' e f"   := (OP_FCmp FUlt _ e f)   (at level 20, only printing).
  Notation "'ule' e f"   := (OP_FCmp FUle _ e f)   (at level 20, only printing).
  Notation "'une' e f"   := (OP_FCmp FUne _ e f)   (at level 20, only printing).


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
                                                             dc_type := (TYPE_Function (TYPE_I 32%positive) [(TYPE_I 32%positive); (TYPE_Pointer (Some (TYPE_Pointer (Some (TYPE_I 8%positive)))))] false);
                                                             dc_param_attrs := ([], [
                                                                               ]);
                                                             dc_attrs := [];
                                                             dc_annotations := []
                                                           |};
                                           df_args := [(Name "argc"); (Name "arcv")];
                                           df_instrs := (
                                                         {|
                                                           blk_id := (Anon 0%Z);
                                                           blk_phis := [];
                                                           blk_code := [(IId (Anon 1%Z), (INSTR_Op (OP_IBinop (Add false false) (TYPE_I 32%positive) (EXP_Integer (5)%Z) (EXP_Integer (9)%Z))));
                                                                        (IId (Anon 2%Z), (INSTR_Op (OP_IBinop (Add false false) (TYPE_I 32%positive) (EXP_Ident (ID_Local (Anon 1%Z))) (EXP_Integer (15)%Z))))];
                                                           blk_term := TERM_Ret ((TYPE_I 32%positive), (EXP_Ident (ID_Local (Anon 2%Z))));
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
