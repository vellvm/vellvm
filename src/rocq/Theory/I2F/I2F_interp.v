From Equations Require Import Equations.

From Stdlib Require Import
  ZArith
  Strings.String
  List
  Morphisms.
Import ListNotations.

From ITree Require Import Basics.HeterogeneousRelations ITree InterpFacts Eq.

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
  Handlers.Memory
  Utils.rutt_cutoff.

From Vellvm Require Import
  Theory.I2F.Refinement
  Theory.I2F.I2F_exp
  Theory.I2F.I2F_MemS.

Existing Instance MemoryModelStateV.
Existing Instance MemoryModelPrimitivesV.

From Paco Require Import paco.

(** ** [pure_base_to_semantic]-wrapped intrinsics

    [pure_base_to_semantic f := pure_to_semantic (pure_base_to_pure f)],
    [pure_to_semantic f args _ := EOU_to_itree (f args)]: a purely EOU-level
    computation over base values, lifted to [semantic_function]. Reduces via
    [I2F_refine_lift] to an [I2F_EOU] fact about [pure_base_to_pure]. *)

Lemma I2F_pure_base_to_semantic :
  forall (f1 : @pure_base_function PInf) (f2 : @pure_base_function PFin),
    (forall args1 args2, Forall2 I2F_dvalue_base args1 args2 ->
       I2F_EOU (sum_rel I2F_dvalue_base I2F_dvalue_base) (f1 args1) (f2 args2)) ->
    forall args1 args2 va1 va2,
      Forall2 I2F_dvalue args1 args2 ->
      I2F_refine_MCFG (sum_rel I2F_dvalue I2F_dvalue)
        (pure_base_to_semantic f1 args1 va1) (pure_base_to_semantic f2 args2 va2).
Proof.
  intros f1 f2 Hf args1 args2 va1 va2 Hargs.
  unfold pure_base_to_semantic, pure_to_semantic.
  apply I2F_refine_lift.
  unfold pure_base_to_pure.
  eapply I2F_EOU_bind.
  { eapply I2F_EOU_map_monad2; [exact Hargs | intros; apply I2F_dvalue_to_dvalue_base; auto]. }
  intros args1' args2' Hargs'.
  eapply I2F_EOU_bind; [apply Hf; auto |].
  intros ans1 ans2 Hans.
  destruct Hans; apply I2F_EOU_ret; constructor; constructor; auto.
Qed.

(** ** The 11 leaf [pure_base_function]s: none of these touch [DVALUE_Pointer]
    or [DVALUE_Iptr], so wherever the pattern actually matches,
    [I2F_dvalue_base]'s Float/Double/Int constructors force the two sides to
    carry the *same* payload. *)

Lemma I2F_llvm_fabs_f32 : forall args1 args2,
    Forall2 I2F_dvalue_base args1 args2 ->
    I2F_EOU (sum_rel I2F_dvalue_base I2F_dvalue_base) (llvm_fabs_f32 args1) (llvm_fabs_f32 args2).
Proof.
  intros args1 args2 Hargs; unfold llvm_fabs_f32.
  destruct Hargs as [ | d1 d2 l1 l2 Hd Hargs]; [constructor |].
  destruct Hd as [ | | | d | | | | ]; try (destruct Hargs; constructor).
  constructor; repeat constructor.
Qed.

Lemma I2F_llvm_fabs_f64 : forall args1 args2,
    Forall2 I2F_dvalue_base args1 args2 ->
    I2F_EOU (sum_rel I2F_dvalue_base I2F_dvalue_base) (llvm_fabs_f64 args1) (llvm_fabs_f64 args2).
Proof.
  intros args1 args2 Hargs; unfold llvm_fabs_f64.
  destruct Hargs as [ | d1 d2 l1 l2 Hd Hargs]; [constructor |].
  destruct Hd as [ | | | | d | | | ]; try (destruct Hargs; constructor).
  constructor; repeat constructor.
Qed.

Lemma I2F_llvm_maxnum_f64 : forall args1 args2,
    Forall2 I2F_dvalue_base args1 args2 ->
    I2F_EOU (sum_rel I2F_dvalue_base I2F_dvalue_base) (llvm_maxnum_f64 args1) (llvm_maxnum_f64 args2).
Proof.
  intros args1 args2 Hargs; unfold llvm_maxnum_f64.
  destruct Hargs as [ | d1 d2 l1 l2 Hd Hargs]; [constructor |].
  destruct Hd as [ | | | d1 | | | | ]; try (destruct Hargs; constructor).
  destruct Hargs as [ | d1' d2' l1' l2' Hd' Hargs]; [constructor |].
  destruct Hd' as [ | | | d2 | | | | ]; try (destruct Hargs; constructor).
  constructor; repeat constructor.
Qed.

Lemma I2F_llvm_maxnum_f32 : forall args1 args2,
    Forall2 I2F_dvalue_base args1 args2 ->
    I2F_EOU (sum_rel I2F_dvalue_base I2F_dvalue_base) (llvm_maxnum_f32 args1) (llvm_maxnum_f32 args2).
Proof.
  intros args1 args2 Hargs; unfold llvm_maxnum_f32.
  destruct Hargs as [ | d1 d2 l1 l2 Hd Hargs]; [constructor |].
  destruct Hd as [ | | | | d1 | | | ]; try (destruct Hargs; constructor).
  destruct Hargs as [ | d1' d2' l1' l2' Hd' Hargs]; [constructor |].
  destruct Hd' as [ | | | | d2 | | | ]; try (destruct Hargs; constructor).
  constructor; repeat constructor.
Qed.

Lemma I2F_llvm_minimum_f64 : forall args1 args2,
    Forall2 I2F_dvalue_base args1 args2 ->
    I2F_EOU (sum_rel I2F_dvalue_base I2F_dvalue_base) (llvm_minimum_f64 args1) (llvm_minimum_f64 args2).
Proof.
  intros args1 args2 Hargs; unfold llvm_minimum_f64.
  destruct Hargs as [ | d1 d2 l1 l2 Hd Hargs]; [constructor |].
  destruct Hd as [ | | | d1 | | | | ]; try (destruct Hargs; constructor).
  destruct Hargs as [ | d1' d2' l1' l2' Hd' Hargs]; [constructor |].
  destruct Hd' as [ | | | d2 | | | | ]; try (destruct Hargs; constructor).
  constructor; repeat constructor.
Qed.

Lemma I2F_llvm_minimum_f32 : forall args1 args2,
    Forall2 I2F_dvalue_base args1 args2 ->
    I2F_EOU (sum_rel I2F_dvalue_base I2F_dvalue_base) (llvm_minimum_f32 args1) (llvm_minimum_f32 args2).
Proof.
  intros args1 args2 Hargs; unfold llvm_minimum_f32.
  destruct Hargs as [ | d1 d2 l1 l2 Hd Hargs]; [constructor |].
  destruct Hd as [ | | | | d1 | | | ]; try (destruct Hargs; constructor).
  destruct Hargs as [ | d1' d2' l1' l2' Hd' Hargs]; [constructor |].
  destruct Hd' as [ | | | | d2 | | | ]; try (destruct Hargs; constructor).
  constructor; repeat constructor.
Qed.

Lemma I2F_llvm_vellvm_internal_throw : forall args1 args2,
    Forall2 I2F_dvalue_base args1 args2 ->
    I2F_EOU (sum_rel I2F_dvalue_base I2F_dvalue_base)
      (llvm_vellvm_internal_throw args1) (llvm_vellvm_internal_throw args2).
Proof.
  intros args1 args2 Hargs; unfold llvm_vellvm_internal_throw.
  destruct Hargs; [apply I2F_EOU_ret; repeat constructor | constructor].
Qed.

(** ** [ushl_sat] (saturated shift-left, [ushl_sat_{1,8,16,32,64}])

    [mshl]/[munsigned]/[mmax_unsigned]/[mrepr]/[mbitwidth] ([VMemInt]) are
    entirely [Params]-independent (fixed-width fixed_int, no [iptr]
    involved), so the two sides thread through *literally* the same
    control flow once [VMI] is shared explicitly; only the final wrap into
    [dvalue_base] via [tdb] genuinely differs by [Pa]. *)
Lemma I2F_ushl_sat {I : Type} (VMI : VMemInt I)
      (TDI1 : @ToDvalueBase PInf I) (TDI2 : @ToDvalueBase PFin I)
      (Htdb : forall x : I, I2F_dvalue_base (@tdb PInf I TDI1 x) (@tdb PFin I TDI2 x))
      (a b : I) :
  I2F_EOU I2F_dvalue_base (@ushl_sat I PInf TDI1 VMI a b) (@ushl_sat I PFin TDI2 VMI a b).
Proof.
  unfold ushl_sat.
  destruct (mshl a b) as [s|s|s|res]; [constructor | constructor | constructor | cbn].
  destruct (option_pred (fun bw => munsigned b >=? Z.pos bw) mbitwidth).
  { constructor; constructor. }
  destruct (Z.shiftl (munsigned a) (munsigned b) >? munsigned res).
  - destruct mmax_unsigned as [m | ]; [ | constructor].
    destruct (mrepr m) as [s|s|s|v]; cbn; [constructor | constructor | constructor | constructor; apply Htdb].
  - cbn; constructor; apply Htdb.
Qed.

(** Numeral patterns like [DVALUE_I 8 a] compile to a direct structural
    match on the literal's binary representation ([xI]/[xO]/[xH]), not a
    [Pos.eq_dec] test — so pinning [sz = n] requires recursively destructing
    the discriminee bit-by-bit, following [n]'s own (statically known)
    shape, closing every "wrong bit" branch with [constructor] (raise_error
    on both sides) along the way. *)
Ltac narrow_sz p n :=
  lazymatch n with
  | 1%positive => destruct p as [p|p|]; [constructor | constructor | ]
  | (?n'~0)%positive =>
      destruct p as [p|p|]; [constructor | | constructor]; narrow_sz p n'
  | (?n'~1)%positive =>
      destruct p as [p|p|]; [ | constructor | constructor]; narrow_sz p n'
  end.

Ltac i2f_ushl_sat_leaf n :=
  intros args1 args2 Hargs;
  destruct Hargs as [ | d1 d2 l1 l2 Hd Hargs]; [constructor |];
  destruct Hd as [ | sz1 i1 | | | | | | ]; try (destruct Hargs; constructor);
  narrow_sz sz1 n; cbn -[ushl_sat];
  destruct Hargs as [ | d1' d2' l1' l2' Hd' Hargs]; [constructor |];
  destruct Hd' as [ | sz2 i2 | | | | | | ]; try (destruct Hargs; constructor);
  narrow_sz sz2 n; cbn -[ushl_sat];
  destruct Hargs; [ | constructor];
  eapply I2F_EOU_bind; [apply I2F_ushl_sat; intros; repeat constructor |];
  intros; constructor; constructor; auto.

Lemma I2F_llvm_ushl_sat_1 : forall args1 args2,
    Forall2 I2F_dvalue_base args1 args2 ->
    I2F_EOU (sum_rel I2F_dvalue_base I2F_dvalue_base) (llvm_ushl_sat_1 args1) (llvm_ushl_sat_1 args2).
Proof. unfold llvm_ushl_sat_1; i2f_ushl_sat_leaf 1%positive. Qed.

Lemma I2F_llvm_ushl_sat_8 : forall args1 args2,
    Forall2 I2F_dvalue_base args1 args2 ->
    I2F_EOU (sum_rel I2F_dvalue_base I2F_dvalue_base) (llvm_ushl_sat_8 args1) (llvm_ushl_sat_8 args2).
Proof. unfold llvm_ushl_sat_8; i2f_ushl_sat_leaf 8%positive. Qed.

Lemma I2F_llvm_ushl_sat_16 : forall args1 args2,
    Forall2 I2F_dvalue_base args1 args2 ->
    I2F_EOU (sum_rel I2F_dvalue_base I2F_dvalue_base) (llvm_ushl_sat_16 args1) (llvm_ushl_sat_16 args2).
Proof. unfold llvm_ushl_sat_16; i2f_ushl_sat_leaf 16%positive. Qed.

Lemma I2F_llvm_ushl_sat_32 : forall args1 args2,
    Forall2 I2F_dvalue_base args1 args2 ->
    I2F_EOU (sum_rel I2F_dvalue_base I2F_dvalue_base) (llvm_ushl_sat_32 args1) (llvm_ushl_sat_32 args2).
Proof. unfold llvm_ushl_sat_32; i2f_ushl_sat_leaf 32%positive. Qed.

Lemma I2F_llvm_ushl_sat_64 : forall args1 args2,
    Forall2 I2F_dvalue_base args1 args2 ->
    I2F_EOU (sum_rel I2F_dvalue_base I2F_dvalue_base) (llvm_ushl_sat_64 args1) (llvm_ushl_sat_64 args2).
Proof. unfold llvm_ushl_sat_64; i2f_ushl_sat_leaf 64%positive. Qed.

(** ** [va_start] / [va_copy] (the only two intrinsics touching memory)

    Genuine [semantic_function]s, not routed through [pure_base_to_semantic]:
    they [trigger] real [MemoryE] events via [store]/[load]. [I2FE_Memory]'s
    [Store]/[Load] clauses only need [I2F_dvalue] on the address/value (the
    "is this actually a pointer" concern is [handle_memoryM]'s problem, not
    this layer's), so these are directly dischargeable from the [Forall2
    I2F_dvalue]/[option_rel I2F_Addr] hypotheses via the same [rstep]/[erbind]
    idiom already used for [Store]/[Load] in [I2F_denotation.v]. *)

(** [raise]/[raiseUB] compile to [trigger_cast], not a plain [ITree.trigger]
    — [rstep]'s first ([ruttc_trigger]) alternative doesn't apply to them at
    all, and going through [first [...]] somehow also blocks its second
    ([ruttc_trigger_cast]) alternative from firing (confirmed by direct
    probe: bare [rstep] makes zero progress on a [raise]-headed goal, while
    [apply ruttc_trigger_cast] alone succeeds). So [raise]/[raiseUB] goals
    need [ruttc_trigger_cast] applied explicitly. *)
Ltac i2f_va_fail :=
  apply ruttc_trigger_cast; cbnn; first [simp I2FE_Failure | simp I2FE_UB]; auto.

Ltac i2f_va_store_step :=
  erbind; [eapply ruttc_trigger; [cbnn; simp I2FE_Memory; repeat (split; auto); repeat constructor; auto | auto] |
            intros; apply ruttc_ret; auto].

Lemma I2F_llvm_va_start : forall args1 args2 va1 va2,
    Forall2 I2F_dvalue args1 args2 ->
    option_rel I2F_Addr va1 va2 ->
    I2F_refine_MCFG (sum_rel I2F_dvalue I2F_dvalue)
      (llvm_va_start args1 va1) (llvm_va_start args2 va2).
Proof.
  intros args1 args2 va1 va2 Hargs Hva; unfold llvm_va_start, I2F_refine_MCFG.
  destruct Hargs as [ | d1 d2 l1 l2 Hd Hargs]; [i2f_va_fail |].
  destruct Hargs; [ | i2f_va_fail].
  destruct Hva as [ | vp1 vp2 Hvp]; [i2f_va_fail |].
  destruct Hd as [b1 b2 Hb | p τ1 s1 s2 Hs | v1' τ1 s1 s2 Hs].
  - destruct Hb as [p1 p2 Hp | sz i | ip1 ip2 Hip | d | f | dt | | sz bits bits' Hbits].
    all: try (rbind Logic.eq; [eapply ruttc_trigger; [cbnn; simp I2FE_Memory; intuition| intros [] [] _; easy] | intros; rstep]).
    rstep; easy.
  - rbind Logic.eq; [eapply ruttc_trigger; [cbnn; simp I2FE_Memory; intuition| intros [] [] _; easy] | intros; rstep].
  - rbind Logic.eq; [eapply ruttc_trigger; [cbnn; simp I2FE_Memory; intuition| intros [] [] _; easy] | intros; rstep].
Qed.

Lemma I2F_llvm_va_copy : forall args1 args2 va1 va2,
    Forall2 I2F_dvalue args1 args2 ->
    I2F_refine_MCFG (sum_rel I2F_dvalue I2F_dvalue)
      (llvm_va_copy args1 va1) (llvm_va_copy args2 va2).
Proof.
  intros args1 args2 va1 va2 Hargs; unfold llvm_va_copy, I2F_refine_MCFG.
  destruct Hargs as [ | dst1 dst2 l1 l2 Hdst Hargs]; [i2f_va_fail |].
  destruct Hargs as [ | src1 src2 l1' l2' Hsrc Hargs]; [i2f_va_fail |].
  destruct Hargs; [ | i2f_va_fail].
  erbind;
  [eapply ruttc_trigger; [cbnn; simp I2FE_Memory; intuition | cbnn; intros *; simp I2FA_Memory; eauto] | intros].
  rbind Logic.eq; [eapply ruttc_trigger; [cbnn; simp I2FE_Memory; intuition| intros [] [] _; easy] | intros; rstep].
Qed.

Lemma I2F_llvm_va_end : forall args1 args2 va1 va2,
    I2F_refine_MCFG (sum_rel I2F_dvalue I2F_dvalue)
      (llvm_va_end args1 va1) (llvm_va_end args2 va2).
Proof.
  intros; unfold llvm_va_end; apply ruttc_ret; repeat constructor.
Qed.

Lemma I2F_handle_intrinsics A1 A2 (e1 : @IntrinsicE PInf A1) (e2 : @IntrinsicE PFin A2):
  I2FE_Intrinsic e1 e2 ->
  I2F_refine_MCFG (fun (a1 : A1) (a2 : A2) => I2FA_Intrinsic e1 a1 e2 a2) (handle_intrinsics e1) (handle_intrinsics e2).
Proof.
  intros HI.
  destruct e1 as [t1 f1 args1 va1]; destruct e2 as [t2 f2 args2 va2].
  simp I2FE_Intrinsic in HI; cbn in HI.
  destruct HI as [Ht [Hf [Hargs Hva]]]; subst.
  cbn.
  destruct (RelDec.rel_dec f2 "llvm.fabs.f32");
    [ simp I2FA_Intrinsic; apply I2F_pure_base_to_semantic; [apply I2F_llvm_fabs_f32 | exact Hargs] | ].
  destruct (RelDec.rel_dec f2 "llvm.fabs.f64");
    [ simp I2FA_Intrinsic; apply I2F_pure_base_to_semantic; [apply I2F_llvm_fabs_f64 | exact Hargs] | ].
  destruct (RelDec.rel_dec f2 "llvm.maxnum.f32");
    [ simp I2FA_Intrinsic; apply I2F_pure_base_to_semantic; [apply I2F_llvm_maxnum_f32 | exact Hargs] | ].
  destruct (RelDec.rel_dec f2 "llvm.maxnum.f64");
    [ simp I2FA_Intrinsic; apply I2F_pure_base_to_semantic; [apply I2F_llvm_maxnum_f64 | exact Hargs] | ].
  destruct (RelDec.rel_dec f2 "minimum.f32");
    [ simp I2FA_Intrinsic; apply I2F_pure_base_to_semantic; [apply I2F_llvm_minimum_f32 | exact Hargs] | ].
  destruct (RelDec.rel_dec f2 "llvm.minimum.f64");
    [ simp I2FA_Intrinsic; apply I2F_pure_base_to_semantic; [apply I2F_llvm_minimum_f64 | exact Hargs] | ].
  destruct (RelDec.rel_dec f2 "llvm.ushl.sat.i1");
    [ simp I2FA_Intrinsic; apply I2F_pure_base_to_semantic; [apply I2F_llvm_ushl_sat_1 | exact Hargs] | ].
  destruct (RelDec.rel_dec f2 "llvm.ushl.sat.i8");
    [ simp I2FA_Intrinsic; apply I2F_pure_base_to_semantic; [apply I2F_llvm_ushl_sat_8 | exact Hargs] | ].
  destruct (RelDec.rel_dec f2 "llvm.ushl.sat.i16");
    [ simp I2FA_Intrinsic; apply I2F_pure_base_to_semantic; [apply I2F_llvm_ushl_sat_16 | exact Hargs] | ].
  destruct (RelDec.rel_dec f2 "llvm.ushl.sat.i32");
    [ simp I2FA_Intrinsic; apply I2F_pure_base_to_semantic; [apply I2F_llvm_ushl_sat_32 | exact Hargs] | ].
  destruct (RelDec.rel_dec f2 "llvm.ushl.sat.i64");
    [ simp I2FA_Intrinsic; apply I2F_pure_base_to_semantic; [apply I2F_llvm_ushl_sat_64 | exact Hargs] | ].
  destruct (RelDec.rel_dec f2 "llvm.vellvm.internal.throw");
    [ simp I2FA_Intrinsic; apply I2F_pure_base_to_semantic; [apply I2F_llvm_vellvm_internal_throw | exact Hargs] | ].
  destruct (RelDec.rel_dec f2 "llvm.va_start");
    [ simp I2FA_Intrinsic; apply I2F_llvm_va_start; auto | ].
  destruct (RelDec.rel_dec f2 "llvm.va_end");
    [ simp I2FA_Intrinsic; apply I2F_llvm_va_end | ].
  destruct (RelDec.rel_dec f2 "llvm.va_copy");
    [ simp I2FA_Intrinsic; apply I2F_llvm_va_copy; auto | ].
  cbn.
  apply ruttc_trigger; cbnn.
  - simp I2FE_Intrinsic; repeat (split; auto).
  - intros a b Hab.
    cbn in Hab; unfold resum, ReSum_id, id_, Id_IFun in Hab.
    simp I2FA_Intrinsic in Hab.
    simp I2FA_Intrinsic.
Qed.
  
Lemma I2F_interp_intrinsics {R1 R2} (RR : R1 -> R2 -> Prop)
  (t1 : @MCFGtop PInf R1) (t2 : @MCFGtop PFin R2):
  I2F_refine_MCFG RR t1 t2 ->
  I2F_refine_MCFG RR
    (interp_intrinsics t1)
    (interp_intrinsics t2).
Proof.
  intros HR.
  apply ruttc_interp_itree; auto.
  - intros * Hcut.
    inv Hcut; reflexivity.
  - intros * Hcut.
    inv Hcut; reflexivity.
  - intros * HEv.
    destruct e1 as [e1|e1]; destruct e2 as [e2|e2]; try elim HEv.
    apply ruttc_trigger; auto.
    destruct e1 as [e1|e1]; destruct e2 as [e2|e2]; try elim HEv.
    2:apply ruttc_trigger; auto.
    now apply I2F_handle_intrinsics.
Qed.

