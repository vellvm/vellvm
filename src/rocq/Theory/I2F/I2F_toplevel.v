From Equations Require Import Equations.

From Stdlib Require Import
  ZArith
  Strings.String
  List.
Import ListNotations.

From ITree Require Import Basics.HeterogeneousRelations ITree.
From ExtLib Require Import Structures.Maps.

From Vellvm Require Import
  Utils
  Syntax
  Semantics
  VellvmIntegers
  Integers
  Interfaces.IPtr
  Interfaces.Params
  Interfaces.Pointer
  Implementations.Pointer
  Implementations.Provenance
  Implementations.IPtrInfinite
  Implementations.IPtrFinite
  Implementations.Memory
  Implementations.ParamsV
  Interfaces.Memory.

From Vellvm Require Import
  Handlers
  Semantics.InterpretationStack
  Semantics.TopLevel
  Semantics.Libraries
  Utils.rutt_cutoff.

From Vellvm Require Import
  Theory.I2F.Refinement
  Theory.I2F.I2F_exp
  Theory.I2F.I2F_denotation
  Theory.I2F.I2F_MemS
  Theory.I2F.I2F_memory
  Theory.I2F.I2F_state.

Existing Instance MemoryModelStateV.
Existing Instance MemoryModelPrimitivesV.

(** * Lifting the interpreter-level result ([I2F_interp_mcfg], [I2F_state.v]) to the top level. *)

(** ** Initial state *)
Lemma I2F_initial_FusedS :
  I2F_FusedS
    (initial_state, ((Build_stack_frame Maps.empty None None, []), Maps.empty))
    (initial_state, ((Build_stack_frame Maps.empty None None, []), Maps.empty)).
Proof.
  constructor; cbn.
  - constructor; cbn.
    + constructor; cbn.
      * apply IM_Refine_empty.
      * constructor; constructor.
      * apply IM_Refine_empty.
    + cbn; reflexivity.
  - constructor; cbn.
    + apply RM_Refine_empty.
    + constructor.
    + reflexivity.
  - constructor.
  - apply RM_Refine_empty.
Qed.

(** ** Global environment construction *)

Lemma I2F_allocate_global : forall (g : global dtyp),
    I2F_refine_MCFG (fun (_ _ : unit) => True)
      (@allocate_global PInf g) (@allocate_global PFin g).
Proof.
  intros g; unfold allocate_global.
  destruct (g_alias g).
  - apply ruttc_ret; auto.
  - rbind I2F_dvalue.
    + unfold alloca; rstep.
    + intros v1 v2 Hv; unfold gwrite; rstep.
Qed.

Lemma I2F_allocate_globals : forall (gs : list (global dtyp)),
    I2F_refine_MCFG (fun (_ _ : unit) => True)
      (@allocate_globals PInf gs) (@allocate_globals PFin gs).
Proof.
  intros gs; unfold allocate_globals, loop_monad.
  induction gs as [| g gs' IH]; cbn.
  - apply ruttc_ret; auto.
  - rbind (fun (_ _ : unit) => True); [apply I2F_allocate_global | intros [] [] _; apply IH].
Qed.

Lemma I2F_allocate_declaration : forall (d : declaration dtyp),
    I2F_refine_MCFG (fun (_ _ : unit) => True)
      (@allocate_declaration PInf d) (@allocate_declaration PFin d).
Proof.
  intros d; unfold allocate_declaration.
  destruct (lookup_intrinsic_declaration (dc_name d)).
  - apply ruttc_ret; auto.
  - rbind I2F_dvalue.
    + unfold alloca; rstep.
    + intros v1 v2 Hv; unfold gwrite; rstep.
Qed.

Lemma I2F_allocate_declarations : forall (ds : list (declaration dtyp)),
    I2F_refine_MCFG (fun (_ _ : unit) => True)
      (@allocate_declarations PInf ds) (@allocate_declarations PFin ds).
Proof.
  intros ds; unfold allocate_declarations, loop_monad.
  induction ds as [| d ds' IH]; cbn.
  - apply ruttc_ret; auto.
  - rbind (fun (_ _ : unit) => True); [apply I2F_allocate_declaration | intros [] [] _; apply IH].
Qed.

Lemma I2F_initialize_global : forall (g : global dtyp),
    I2F_refine_MCFG (fun (_ _ : unit) => True)
      (@initialize_global PInf g) (@initialize_global PFin g).
Proof.
  intros g; unfold initialize_global.
  destruct (g_alias g).
  - destruct (g_exp g) as [e|].
    + destruct e; try (apply ruttc_trigger_cast; cbnn; simp I2FE_UB; auto).
      destruct id; try (apply ruttc_trigger_cast; cbnn; simp I2FE_UB; auto).
      rbind I2F_dvalue.
      * unfold gread; rstep.
      * intros p1 p2 Hp; unfold gwrite; rstep.
    + apply ruttc_trigger_cast; cbnn; simp I2FE_UB; auto.
  - rbind I2F_dvalue.
    + unfold gread; rstep.
    + intros a1 a2 Ha.
      rbind I2F_dvalue.
      * destruct (g_exp g).
        -- apply I2F_denote_exp.
        -- apply ruttc_ret; repeat constructor.
      * intros uv1 uv2 Huv; unfold store; rstep.
Qed.

Lemma I2F_initialize_globals : forall (gs : list (global dtyp)),
    I2F_refine_MCFG (fun (_ _ : unit) => True)
      (@initialize_globals PInf gs) (@initialize_globals PFin gs).
Proof.
  intros gs; unfold initialize_globals, loop_monad.
  induction gs as [| g gs' IH]; cbn.
  - apply ruttc_ret; auto.
  - rbind (fun (_ _ : unit) => True); [apply I2F_initialize_global | intros [] [] _; apply IH].
Qed.

Lemma I2F_build_global_environment : forall (mcfg : CFG.mcfg dtyp),
    I2F_refine_MCFG (fun (_ _ : unit) => True)
      (@build_global_environment PInf mcfg) (@build_global_environment PFin mcfg).
Proof.
  intros mcfg; unfold build_global_environment.
  rbind (fun (_ _ : unit) => True).
  - apply I2F_allocate_declarations.
  - intros [] [] _.
    rbind (fun (_ _ : unit) => True).
    + apply I2F_allocate_globals.
    + intros [] [] _; apply I2F_initialize_globals.
Qed.

(** ** Command-line argument allocation *)

Lemma I2F_i8_array_of_string : forall (s : string),
    I2F_dvalue (@i8_array_of_string PInf s) (@i8_array_of_string PFin s).
Proof.
  intros s; unfold i8_array_of_string.
  constructor.
  apply Forall2_app.
  - apply Forall2_map2; intros; repeat constructor.
  - repeat constructor.
Qed.

Lemma I2F_allocate_arg : forall (arg : string),
    I2F_refine_MCFG I2F_dvalue
      (@allocate_arg PInf arg) (@allocate_arg PFin arg).
Proof.
  intros arg; unfold allocate_arg.
  pose proof (I2F_i8_array_of_string arg) as Harr.
  rbind I2F_dvalue.
  - unfold alloca; rstep.
  - intros v1 v2 Hv.
    rbind (fun (_ _ : unit) => True).
    + unfold store.
      apply ruttc_trigger;
        [cbnn; simp I2FE_Memory; auto | intros [] [] _; auto].
    + intros [] [] _; apply ruttc_ret; auto.
Qed.

Lemma I2F_allocate_args : forall (args : list string),
    I2F_refine_MCFG I2F_dvalue
      (@allocate_args PInf args) (@allocate_args PFin args).
Proof.
  intros args; unfold allocate_args.
  rbind I2F_dvalue.
  - unfold alloca; rstep.
  - intros v1 v2 Hv.
    rbind (Forall2 I2F_dvalue).
    + apply ruttc_map_monad; intros; apply I2F_allocate_arg.
    + intros addrs1 addrs2 Haddrs.
      rbind (fun (_ _ : unit) => True).
      * unfold store.
        apply ruttc_trigger;
          [cbnn; simp I2FE_Memory; auto | intros [] [] _; auto].
      * intros [] [] _; apply ruttc_ret; auto.
Qed.

Lemma I2F_build_main_args : forall (args : list string),
    I2F_refine_MCFG (Forall2 I2F_dvalue)
      (@build_main_args PInf args) (@build_main_args PFin args).
Proof.
  intros args; unfold build_main_args.
  rbind I2F_dvalue; [apply I2F_allocate_args | ].
  intros v1 v2 Hv; apply ruttc_ret.
  repeat constructor; auto.
Qed.

(** ** Function table construction *)

Lemma I2F_address_one_function : forall (df : definition dtyp (CFG.cfg dtyp)),
    I2F_refine_MCFG (prod_rel Logic.eq I2F_function_denotation)
      (@address_one_function PInf df) (@address_one_function PFin df).
Proof.
  intros df; unfold address_one_function.
  rbind I2F_dvalue.
  - unfold gread; rstep.
  - intros fv1 fv2 Hfv.
    destruct Hfv as [b1 b2 Hb | | ];
      try (apply ruttc_trigger_cast; cbnn; simp I2FE_Failure; auto).
    destruct Hb; try (apply ruttc_trigger_cast; cbnn; simp I2FE_Failure; auto).
    apply ruttc_ret.
    constructor; cbn.
    + apply I2F_Addr_ptr_to_int; auto.
    + apply I2F_denote_function.
Qed.

Lemma I2F_address_one_library_function :
  forall (fid : function_id) (d1 : @function_denotation PInf) (d2 : @function_denotation PFin),
    I2F_function_denotation d1 d2 ->
    I2F_refine_MCFG (prod_rel Logic.eq I2F_function_denotation)
      (@address_one_library_function PInf (fid, d1))
      (@address_one_library_function PFin (fid, d2)).
Proof.
  intros fid d1 d2 Hd; unfold address_one_library_function.
  rbind I2F_dvalue.
  - unfold gread; rstep.
  - intros fv1 fv2 Hfv.
    destruct Hfv as [b1 b2 Hb | | ];
      try (apply ruttc_trigger_cast; cbnn; simp I2FE_Failure; auto).
    destruct Hb; try (apply ruttc_trigger_cast; cbnn; simp I2FE_Failure; auto).
    apply ruttc_ret.
    constructor; cbn; auto.
    apply I2F_Addr_ptr_to_int; auto.
Qed.

(** The built-in library denotations themselves *)
#[local] Arguments Pos.eq_dec : simpl never.

Lemma I2F_putchar_denotation :
  I2F_function_denotation (@putchar_denotation PInf) (@putchar_denotation PFin).
Proof.
  intros args1 args2 Hargs.
  unfold putchar_denotation; cbn.
  destruct Hargs as [| u1 u2 args1 args2 Hu Hargs]; [apply ruttc_trigger_cast; cbnn; simp I2FE_Failure; auto|].
  destruct Hargs; cbn; [ | unfold raise; apply ruttc_trigger_cast; cbnn; simp I2FE_Failure; auto].
  unfold ITree.map.
  destruct Hu as [b1 b2 Hb | | ]; try (rbind (fun _ _ => False); [apply ruttc_trigger_cast; cbnn; simp I2FE_UB; auto | intros ?? []]); [].
  destruct Hb as [p1 p2 Hp | sz i | p1 p2 Hp | d | f | t | | sz bits1 bits2 Hbits]; try (rbind (fun _ _ => False); [apply ruttc_trigger_cast; cbnn; simp I2FE_UB; auto | intros ?? []]); [].
  destruct (Pos.eq_dec 32 sz); cbn.
  - rewrite 2 Eqit.bind_bind.
    rbind TT; [rstep | intros [] [] _].
    rewrite 2 Eqit.bind_ret_l; rstep.
  - try (rbind (fun _ _ => False); [apply ruttc_trigger_cast; cbnn; simp I2FE_UB; auto | intros ?? []]).
Qed.

Lemma I2F_i8_str_index :
  forall (p1 : @ptr (@PROV PInf) (@PTR PInf)) (p2 : @ptr (@PROV PFin) (@PTR PFin))
    (index : Z),
    I2F_Addr p1 p2 ->
    I2F_refine_CFG Logic.eq
      (@i8_str_index PInf p1 index) (@i8_str_index PFin p2 index).
Proof.
  intros p1 p2 index Hp.
  unfold i8_str_index.
  rbind I2F_Iptr.
  - apply I2F_refine_lift', I2F_from_Z.
  - intros iptr1 iptr2 Hiptr.
    rbind I2F_Addr.
    + apply I2F_refine_lift', I2F_handle_gep_ptr; auto.
    + intros addr1 addr2 Haddr.
      rbind I2F_dvalue.
      * unfold load.
        apply ruttc_trigger;
          [cbnn; simp I2FE_Memory; auto | intros a b Hab; cbnn in Hab; simp I2FA_Memory in Hab; auto].
      * intros d1 d2 Hd.
        destruct Hd as [b1 b2 Hb | | ];
          try (unfold raise; apply ruttc_trigger_cast; cbnn; simp I2FE_Failure; auto); [].
        destruct Hb as [q1 q2 Hq | sz i | q1 q2 Hq | dd | ff | tt | | sz bits1 bits2 Hbits];
          try (unfold raise; apply ruttc_trigger_cast; cbnn; simp I2FE_Failure; auto); [].
        repeat (destruct sz as [sz|sz|]; cbn;
          try (apply ruttc_trigger_cast; cbnn; simp I2FE_Failure; auto)).
        apply ruttc_ret; auto.
Qed.

#[local] Arguments Integers.eq : simpl never.
Lemma I2F_puts_denotation :
  I2F_function_denotation (@puts_denotation PInf) (@puts_denotation PFin).
Proof.
  intros args1 args2 Hargs.
  unfold puts_denotation.
  destruct Hargs as [| u1 u2 args1 args2 Hu Hargs];
    [apply ruttc_trigger_cast; cbnn; simp I2FE_Failure; auto|].
  destruct Hargs; [ | unfold raise; apply ruttc_trigger_cast; cbnn; simp I2FE_Failure; auto].
  destruct Hu as [b1 b2 Hb | | ];
    try (rbind (fun _ _ => False); [apply ruttc_trigger_cast; cbnn; simp I2FE_UB; auto | intros ?? []]); [].
  destruct Hb as [p1 p2 Hp | sz i | p1 p2 Hp | d | f | t | | sz bits1 bits2 Hbits];
    try (rbind (fun _ _ => False); [apply ruttc_trigger_cast; cbnn; simp I2FE_UB; auto | intros ?? []]); [].
  simpl; unfold ITree.map.
  rewrite !Eqit.bind_bind.
  rbind Logic.eq.
  - apply I2F_i8_str_index; auto.
  - intros c1 c2 <-.
    rewrite !Eqit.bind_bind.
    rbind Logic.eq.
    + apply ruttc_iter with (II := Logic.eq).
      * intros [[c1' bytes1] off1] ? <-.
        break_match_goal; [rstep |].
        rbind Logic.eq.
        apply I2F_i8_str_index; auto.
        intros nc1 nc2 <-; rstep.
      * reflexivity.
    + intros bytes1 bytes2 <-.
      rewrite !Eqit.bind_bind.
      rbind (fun (_ _ : unit) => True).
      * apply ruttc_trigger; [cbnn; simp I2FE_ExternalCall; auto | intros [] [] _; auto].
      * intros [] [] _.
        rewrite !Eqit.bind_ret_l; rstep.
Qed.

Lemma I2F_LIBRARIES :
  Forall2 (prod_rel Logic.eq I2F_function_denotation)
    (@_LIBRARIES PInf) (@_LIBRARIES PFin).
Proof.
  unfold _LIBRARIES.
  constructor; [constructor; [reflexivity | apply I2F_puts_denotation] |].
  constructor; [constructor; [reflexivity | apply I2F_putchar_denotation] |].
  constructor.
Qed.

Lemma I2F_library_functions : forall (decls : list (declaration dtyp)),
    Forall2 (prod_rel Logic.eq I2F_function_denotation)
      (@library_functions PInf decls) (@library_functions PFin decls).
Proof.
  intros decls; unfold library_functions.
  apply Forall2_filter.
  - intros [n1 d1] [n2 d2] [Heq _]; cbn in Heq; subst; reflexivity.
  - apply I2F_LIBRARIES.
Qed.

(** Turning a [Forall2 (eq × I2F_function_denotation)]-related pair of
    association lists into an [I2F_ctx]-related pair of [IntMap]s. *)
Lemma I2F_ctx_of_list :
  forall (l1 : list (Z * @function_denotation PInf))
    (l2 : list (Z * @function_denotation PFin)),
    Forall2 (prod_rel Logic.eq I2F_function_denotation) l1 l2 ->
    I2F_ctx (IP.of_list l1) (IP.of_list l2).
Proof.
  intros l1 l2 H k.
  apply IM_Refine_lookup, IM_Refine_Forall2; auto.
Qed.

(** ** [denote_vellvm] ([TopLevel.v:273-286])

    Glues [build_global_environment], the [defns]/[libraries] function
    table (via [address_one_function]/[address_one_library_function]/
    [I2F_ctx_of_list]), the final [gread entry], [I2F_denote_mcfg]
    ([I2F_denotation.v]) on the resulting [I2F_ctx]/[I2F_dvalue]-related
    address and args, and the closing [match] on the [exc + dvalue]
    result (([inl],[inl]) via [raiseLLVM]/[I2FE_Exc]-triggering,
    ([inr],[inr]) via [ret]). *)
Lemma I2F_denote_vellvm :
  forall (ret_typ : dtyp) (entry : function_id)
    (args1 : list (@dvalue PInf)) (args2 : list (@dvalue PFin))
    (mcfg : CFG.mcfg dtyp),
    Forall2 I2F_dvalue args1 args2 ->
    I2F_refine_MCFG I2F_dvalue
      (@denote_vellvm PInf ret_typ entry args1 mcfg)
      (@denote_vellvm PFin ret_typ entry args2 mcfg).
Proof.
  intros * HDV.
  unfold denote_vellvm.
  erbind; [apply I2F_build_global_environment | intros [] [] _].
  erbind; [apply ruttc_map_monad; intros; apply I2F_address_one_function | intros].
  erbind. apply ruttc_map_monad_gen.
  - induction (I2F_library_functions (m_declarations mcfg))
      as [| [fid1 d1] [fid2 d2] l1 l2 [Heq Hd] Hrest IH].
    + constructor.
    + cbn in Heq; subst.
      constructor; [apply I2F_address_one_library_function; auto | apply IH].
  - intros libs1 libs2 Hlibs.
    rbind I2F_dvalue.
    + unfold gread; rstep.
    + intros addr1 addr2 Haddr.
      rbind (sum_rel I2F_dvalue I2F_dvalue).
      * apply I2F_denote_mcfg; [auto | auto | apply I2F_ctx_of_list, Forall2_app; auto].
      * intros rv1 rv2 Hrv.
        destruct Hrv as [exc1 exc2 Hexc | v1 v2 Hv].
        -- apply ruttc_trigger_cast; cbnn; simp I2FE_Exc; auto.
        -- apply ruttc_ret; auto.
Qed.

(** ** [interpreter_gen] / [interpreter_param]
    The final assembly. *)
Lemma I2F_interpreter_gen :
  forall (ret_typ : dtyp) (entry : function_id)
    (arg_gen1 : @MCFGtop PInf (list (@dvalue PInf)))
    (arg_gen2 : @MCFGtop PFin (list (@dvalue PFin)))
    (prog : ll_toplevel_entities),
    I2F_refine_MCFG (Forall2 I2F_dvalue) arg_gen1 arg_gen2 ->
    I2F_refine_MCFGbot (prod_rel I2F_FusedS I2F_dvalue)
      (@interpreter_gen PInf ret_typ entry arg_gen1 prog)
      (@interpreter_gen PFin ret_typ entry arg_gen2 prog).
Proof.
  intros.
  unfold interpreter_gen.
  eapply I2F_interp_mcfg_bind; eauto; cycle -1.
  { apply I2F_initial_FusedS. }
  intros.
  now apply I2F_denote_vellvm.
Qed.
  
Theorem I2F_interpreter_param :
  forall (args : list string) (prog : ll_toplevel_entities),
    I2F_refine_MCFGbot (prod_rel I2F_FusedS I2F_dvalue)
      (@interpreter_param PInf args prog)
      (@interpreter_param PFin args prog).
Proof.
  intros.
  apply I2F_interpreter_gen, I2F_build_main_args.
Qed.
