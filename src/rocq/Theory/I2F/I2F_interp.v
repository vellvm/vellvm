(** * I2F invariant for the handlers *)

From Equations Require Import Equations.

From Stdlib Require Import
  ZArith
  Strings.String
  List
  Morphisms
  Equality.
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
  Theory.I2F.I2F_memS
  Theory.I2F.I2F_memory.

Existing Instance MemoryModelStateV.
Existing Instance MemoryModelPrimitivesV.

Import Monads State StateFacts.
From Paco Require Import paco.

(** * Intrinsics (out of the memory model) *)

(** ** [pure_base_to_semantic]-wrapped intrinsics *)

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

(** ** The 11 leaf [pure_base_function]s: none of these touch [DVALUE_Pointer] or [DVALUE_Iptr] *)

Lemma I2F_llvm_fabs_f32 : forall args1 args2,
    Forall2 I2F_dvalue_base args1 args2 ->
    I2F_EOU (sum_rel I2F_dvalue_base I2F_dvalue_base) (llvm_fabs_f32 args1) (llvm_fabs_f32 args2).
Proof.
  intros args1 args2 Hargs; unfold llvm_fabs_f32.
  destruct Hargs as [ | d1 d2 l1 l2 Hd Hargs]; [constructor |].
  destruct Hd as [ | | | d | | | | | ]; try (destruct Hargs; constructor).
  constructor; repeat constructor.
Qed.

Lemma I2F_llvm_fabs_f64 : forall args1 args2,
    Forall2 I2F_dvalue_base args1 args2 ->
    I2F_EOU (sum_rel I2F_dvalue_base I2F_dvalue_base) (llvm_fabs_f64 args1) (llvm_fabs_f64 args2).
Proof.
  intros args1 args2 Hargs; unfold llvm_fabs_f64.
  destruct Hargs as [ | d1 d2 l1 l2 Hd Hargs]; [constructor |].
  destruct Hd as [ | | | | d | | | | ]; try (destruct Hargs; constructor).
  constructor; repeat constructor.
Qed.

Lemma I2F_llvm_maxnum_f64 : forall args1 args2,
    Forall2 I2F_dvalue_base args1 args2 ->
    I2F_EOU (sum_rel I2F_dvalue_base I2F_dvalue_base) (llvm_maxnum_f64 args1) (llvm_maxnum_f64 args2).
Proof.
  intros args1 args2 Hargs; unfold llvm_maxnum_f64.
  destruct Hargs as [ | d1 d2 l1 l2 Hd Hargs]; [constructor |].
  destruct Hd as [ | | | d1 | | | | | ]; try (destruct Hargs; constructor).
  destruct Hargs as [ | d1' d2' l1' l2' Hd' Hargs]; [constructor |].
  destruct Hd' as [ | | | d2 | | | | | ]; try (destruct Hargs; constructor).
  constructor; repeat constructor.
Qed.

Lemma I2F_llvm_maxnum_f32 : forall args1 args2,
    Forall2 I2F_dvalue_base args1 args2 ->
    I2F_EOU (sum_rel I2F_dvalue_base I2F_dvalue_base) (llvm_maxnum_f32 args1) (llvm_maxnum_f32 args2).
Proof.
  intros args1 args2 Hargs; unfold llvm_maxnum_f32.
  destruct Hargs as [ | d1 d2 l1 l2 Hd Hargs]; [constructor |].
  destruct Hd as [ | | | | d1 | | | | ]; try (destruct Hargs; constructor).
  destruct Hargs as [ | d1' d2' l1' l2' Hd' Hargs]; [constructor |].
  destruct Hd' as [ | | | | d2 | | | | ]; try (destruct Hargs; constructor).
  constructor; repeat constructor.
Qed.

Lemma I2F_llvm_minimum_f64 : forall args1 args2,
    Forall2 I2F_dvalue_base args1 args2 ->
    I2F_EOU (sum_rel I2F_dvalue_base I2F_dvalue_base) (llvm_minimum_f64 args1) (llvm_minimum_f64 args2).
Proof.
  intros args1 args2 Hargs; unfold llvm_minimum_f64.
  destruct Hargs as [ | d1 d2 l1 l2 Hd Hargs]; [constructor |].
  destruct Hd as [ | | | d1 | | | | | ]; try (destruct Hargs; constructor).
  destruct Hargs as [ | d1' d2' l1' l2' Hd' Hargs]; [constructor |].
  destruct Hd' as [ | | | d2 | | | | | ]; try (destruct Hargs; constructor).
  constructor; repeat constructor.
Qed.

Lemma I2F_llvm_minimum_f32 : forall args1 args2,
    Forall2 I2F_dvalue_base args1 args2 ->
    I2F_EOU (sum_rel I2F_dvalue_base I2F_dvalue_base) (llvm_minimum_f32 args1) (llvm_minimum_f32 args2).
Proof.
  intros args1 args2 Hargs; unfold llvm_minimum_f32.
  destruct Hargs as [ | d1 d2 l1 l2 Hd Hargs]; [constructor |].
  destruct Hd as [ | | | | d1 | | | | ]; try (destruct Hargs; constructor).
  destruct Hargs as [ | d1' d2' l1' l2' Hd' Hargs]; [constructor |].
  destruct Hd' as [ | | | | d2 | | | | ]; try (destruct Hargs; constructor).
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

(** ** [ushl_sat] (saturated shift-left, [ushl_sat_{1,8,16,32,64}]) *)
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
  destruct Hd as [ | sz1 i1 | | | | | | | ]; try (destruct Hargs; constructor);
  narrow_sz sz1 n; cbn -[ushl_sat];
  destruct Hargs as [ | d1' d2' l1' l2' Hd' Hargs]; [constructor |];
  destruct Hd' as [ | sz2 i2 | | | | | | | ]; try (destruct Hargs; constructor);
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

(** ** [va_start] / [va_copy] (the only two intrinsics touching memory) *)

Ltac i2f_va_fail :=
  apply ruttc_trigger_cast; cbnn; first [simp I2FE_Failure | simp I2FE_UB]; auto.

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
  destruct Hd as [b1 b2 Hb | p τ1 s1 s2 | v1' τ1 s1 s2 Hs].
  - destruct Hb as [p1 p2 Hp | sz i | ip1 ip2 Hip | d | f | h | dt | | sz bits bits' Hbits].
    all: try (rbind Logic.eq; [eapply ruttc_trigger; [cbnn; simp I2FE_Memory; intuition auto| intros [] [] _; easy] | intros; rstep]).
    rstep; easy.
  - rbind Logic.eq; [eapply ruttc_trigger; [cbnn; simp I2FE_Memory; intuition auto| intros [] [] _; easy] | intros; rstep].
  - rbind Logic.eq; [eapply ruttc_trigger; [cbnn; simp I2FE_Memory; intuition auto| intros [] [] _; easy] | intros; rstep].
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
  destruct (RelDec.rel_dec f2 "llvm.minimum.f32");
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


(** * Relating [FusedS], the product state threaded by [interp_mcfg] *)

(** ** [local_env] / [global_env] *)

Definition I2F_env : @local_env PInf -> @local_env PFin -> Prop := RM_Refine I2F_dvalue.
Definition I2F_local_env : @local_env PInf -> @local_env PFin -> Prop := I2F_env.
Definition I2F_global_env : @global_env PInf -> @global_env PFin -> Prop := I2F_env.

(** ** [stack_frame] / [stack] *)

Record I2F_stack_frame (f1 : @stack_frame PInf) (f2 : @stack_frame PFin) : Prop :=
  { i2f_sf_vars : I2F_local_env f1.(stack_vars) f2.(stack_vars);
    i2f_sf_exc  : option_rel I2F_dvalue f1.(stack_exc) f2.(stack_exc);
    i2f_sf_loc  : f1.(stack_loc) = f2.(stack_loc);
  }.

Definition I2F_stack : @stack PInf -> @stack PFin -> Prop := Forall2 I2F_stack_frame.

(** ** [FusedS] itself *)

Record I2F_FusedS (s1 : @FusedS PInf) (s2 : @FusedS PFin) : Prop :=
  { i2f_fs_mem   : I2F_State (fst s1) (fst s2);
    i2f_fs_frame : I2F_stack_frame (fst (fst (snd s1))) (fst (fst (snd s2)));
    i2f_fs_stack : I2F_stack (snd (fst (snd s1))) (snd (fst (snd s2)));
    i2f_fs_genv  : I2F_global_env (snd (snd s1)) (snd (snd s2));
  }.

(** * Per-handler compatibility *)

(** * Globals *)
Lemma I2F_fused_global :
  forall T1 T2 (e1 : @GlobalE PInf T1) (e2 : @GlobalE PFin T2),
    I2FE_Global e1 e2 ->
    forall s1 s2, I2F_FusedS s1 s2 ->
      I2F_refine_MCFGbot
        (prod_rel I2F_FusedS (fun r1 r2 => I2FA_Global e1 r1 e2 r2))
        (fused_global e1 s1) (fused_global e2 s2).
Proof.
  intros T1 T2 e1 e2 H [m1 [ls1 g1]] [m2 [ls2 g2]] Hs.
  destruct Hs as [Hmem Hframe Hstack Hgenv]; cbn in Hmem, Hframe, Hstack, Hgenv.
  destruct e1 as [x1 dv1 | x1]; destruct e2 as [x2 dv2 | x2];
    simp I2FE_Global in H; cbn in H; try contradiction.
  - (* GlobalWrite *)
    destruct H as [-> Hdv].
    unfold fused_global, on_genv, handle_global_debug, handle_global, update_globals_ref,
      I2F_refine_MCFGbot; cbn; rewrite ?Eqit.bind_ret_l.
    apply ruttc_ret.
    split.
    + constructor; cbn; auto.
      apply RM_Refine_add; auto.
    + simp I2FA_Global; auto.
  - (* GlobalRead *)
    subst.
    unfold fused_global, on_genv, handle_global_debug, handle_global, update_globals_ref,
      I2F_refine_MCFGbot; cbn.
    pose proof (RM_Refine_lookup I2F_dvalue g1 g2 Hgenv x2) as Hlk.
    unfold rid_lookup in Hlk.
    destruct Hlk as [ | dv1 dv2 Hdv]; cbn; rewrite ?Eqit.bind_ret_l.
    + rbind (fun _ _ => False);
        [rbind (fun _ _ => False);
          [apply ruttc_trigger_cast; cbnn; first [simp I2FE_Failure | simp I2FE_UB]; auto |
            intros _ _ []] |
          intros _ _ []].
    + apply ruttc_ret. split; [constructor; cbn; auto | simp I2FA_Global; auto].
Qed.

(** * Locals *)
Lemma I2F_fused_local :
  forall T1 T2 (e1 : @LocalE PInf T1) (e2 : @LocalE PFin T2),
    I2FE_Local e1 e2 ->
    forall s1 s2, I2F_FusedS s1 s2 ->
      I2F_refine_MCFGbot
        (prod_rel I2F_FusedS (fun r1 r2 => I2FA_Local e1 r1 e2 r2))
        (fused_local e1 s1) (fused_local e2 s2).
Proof.
  intros T1 T2 e1 e2 H [m1 [[f1 stk1] g1]] [m2 [[f2 stk2] g2]] Hs.
  destruct Hs as [Hmem Hframe Hstack Hgenv]; cbn in Hmem, Hframe, Hstack, Hgenv.
  destruct Hframe as [Hvars Hexc Hloc]; cbn in Hvars, Hexc, Hloc.
  destruct e1 as [x1 dv1 | x1]; destruct e2 as [x2 dv2 | x2];
    simp I2FE_Local in H; cbn in H; try contradiction.
  - (* LocalWrite *)
    destruct H as [-> Hdv].
    unfold fused_local, on_ls, handle_local_stack, handle_local_debug, handle_local,
      update_locals_ref, upd_local_sf, I2F_refine_MCFGbot; cbn; rewrite ?Eqit.bind_ret_l.
    apply ruttc_ret.
    split.
    + constructor; cbn; auto.
      constructor; cbn; auto.
      apply RM_Refine_add; auto.
    + simp I2FA_Local; auto.
  - (* LocalRead *)
    subst.
    unfold fused_local, on_ls, handle_local_stack, handle_local_debug, handle_local,
      update_locals_ref, I2F_refine_MCFGbot; cbn.
    pose proof (RM_Refine_lookup I2F_dvalue (stack_vars f1) (stack_vars f2) Hvars x2) as Hlk.
    unfold rid_lookup in Hlk.
    destruct Hlk as [ | dv1 dv2 Hdv]; cbn; rewrite ?Eqit.bind_ret_l.
    + rbind (fun _ _ => False);
        [rbind (fun _ _ => False);
          [rbind (fun _ _ => False);
            [apply ruttc_trigger_cast; cbnn; first [simp I2FE_Failure | simp I2FE_UB]; auto |
              intros _ _ []] |
            intros _ _ []] |
          intros _ _ []].
    + apply ruttc_ret.
      split; [constructor; cbn; auto; constructor; cbn; auto | simp I2FA_Local; auto].
Qed.

(** * Stack *)
Lemma I2F_fused_stack :
  forall T1 T2 (e1 : @StackE PInf T1) (e2 : @StackE PFin T2),
    I2FE_Stack e1 e2 ->
    forall s1 s2, I2F_FusedS s1 s2 ->
      I2F_refine_MCFGbot
               (prod_rel I2F_FusedS (fun r1 r2 => I2FA_Stack e1 r1 e2 r2))
        (fused_stack e1 s1) (fused_stack e2 s2).
Proof.
  intros T1 T2 e1 e2 H [m1 [[f1 stk1] g1]] [m2 [[f2 stk2] g2]] Hs.
  destruct Hs as [Hmem Hframe Hstack Hgenv]; cbn in Hmem, Hframe, Hstack, Hgenv.
  destruct e1 as [args1 | |exc1| ]; destruct e2 as [args2 | |exc2| ];
    simp I2FE_Stack in H; cbn in H; try contradiction.
  - (* StackPush *)
    unfold fused_stack, on_ls, handle_stack, I2F_refine_MCFGbot; cbn; rewrite ?Eqit.bind_ret_l.
    assert (Hinit : I2F_local_env
                      (fold_right (fun '(x,dv) => Maps.add x dv) Maps.empty args1)
                      (fold_right (fun '(x,dv) => Maps.add x dv) Maps.empty args2)).
    { induction H as [ | [x1 dv1] [x2 dv2] l1 l2 Hxd Hrest IH]; cbn.
      - apply RM_Refine_empty.
      - destruct Hxd as [Heq Hdv]; cbn in Heq; subst.
        apply RM_Refine_add; auto. }
    apply ruttc_ret.
    split.
    + constructor; cbn.
      * auto.
      * constructor; cbn; [auto | constructor | auto].
      * constructor; auto.
      * auto.
    + simp I2FA_Stack; auto.
  - (* StackPop *)
    unfold fused_stack, on_ls, handle_stack, I2F_refine_MCFGbot; cbn.
    destruct Hstack as [ | f1' f2' stk1' stk2' Hf' Hstk'].
    + cbn; rewrite ?Eqit.bind_ret_l.
      rbind (fun _ _ => False);
        [rbind (fun _ _ => False);
          [apply ruttc_trigger;
            [cbnn; first [simp I2FE_Failure | simp I2FE_UB]; auto | intros [] [] _] |
            intros _ _ []] |
          intros _ _ []].
    + cbn; rewrite ?Eqit.bind_ret_l.
      apply ruttc_ret.
      split; [constructor; cbn; auto | simp I2FA_Stack; auto].
  - (* StackRaise *)
    unfold fused_stack, on_ls, handle_stack, I2F_refine_MCFGbot; cbn; rewrite ?Eqit.bind_ret_l.
    apply ruttc_ret.
    destruct Hframe as [Hvars Hexc Hloc].
    split.
    + constructor; cbn.
      * auto.
      * constructor; cbn; [auto | constructor; auto | auto].
      * auto.
      * auto.
    + simp I2FA_Stack; auto.
  - (* StackGetExc *)
    unfold fused_stack, on_ls, handle_stack, I2F_refine_MCFGbot; cbn; rewrite ?Eqit.bind_ret_l.
    apply ruttc_ret.
    destruct Hframe as [Hvars Hexc Hloc].
    split.
    + constructor; cbn.
      * auto.
      * constructor; cbn; [auto | constructor | auto].
      * auto.
      * auto.
    + simp I2FA_Stack; auto.
Qed.

(** * Memory
Note: This essentially lifts [I2F_handle_memoryM], but through the monad morphism implementing
[memM] in a deterministic way. This is the main piece of proof that will have to be
adapted for the model. *)

(** [fresh_provenance] resolves via [next_provenance] *)
Lemma I2F_fresh_provenance_eq :
  forall s1 s2,
    I2F_State s1 s2 ->
    next_provenance (state_provenance s1) = next_provenance (state_provenance s2).
Proof.
  intros s1 s2 [_ Hprov]; cbn in *; rewrite Hprov; reflexivity.
Qed.

(** ** Interpreter-specific: [memM_interp] *)
Lemma I2F_memM_interp R1 R2 RR (t1 : @memM PInf _ R1) (t2 : @memM PFin _ R2) :
  I2F_memS I2F_State RR t1 t2 ->
  forall s1 s2,
    I2F_State s1 s2 ->
    I2F_refine_MCFGbot (prod_rel I2F_State RR) (memM_interp t1 s1) (memM_interp t2 s2).
Proof.
  induction 1 as [x1 x2 Hr | e1 e2 | e m2 | m1 e
                  | k1 k2 Hget IHget | σ1 σ2 k1 k2 Hσ Hput IHput
                  | c k1 k2 Hc IHc];
    intros s1 s2 HS; cbn.
  - pstep; constructor; constructor; auto.
  - apply ruttc_trigger_cast; constructor.
  - unfold raiseUB, trigger_cast; rewrite bind_trigger.
    pstep; repeat constructor.
  - unfold raiseOOM, trigger_cast; rewrite bind_trigger.
    pstep; repeat constructor.
  - now apply IHget.
  - now apply IHput.
  - destruct c; cbn.
    + (* Cnext_key *)
      pose proof (I2F_next_key_with_alignment
                    (i2f_ms_memory (i2f_st_ms HS)) align) as Heq.
      rewrite Heq.
      apply IHc; auto.
    + (* Cfresh_prov *)
      rewrite !Eqit.bind_ret_l.
      pose proof (I2F_fresh_provenance_eq HS) as Heq.
      cbn in Heq.
      rewrite Heq.
      apply IHc.
      constructor; cbn; [exact (i2f_st_ms HS) | reflexivity].
    + (* Cexposed_prov *)
      now apply IHc.
Qed.

Lemma I2F_fused_memory :
  forall T1 T2 (e1 : @MemoryE PInf T1) (e2 : @MemoryE PFin T2),
    I2FE_Memory e1 e2 ->
    forall s1 s2, I2F_FusedS s1 s2 ->
             I2F_refine_MCFGbot
               (prod_rel I2F_FusedS (fun r1 r2 => I2FA_Memory e1 r1 e2 r2))
               (fused_memory e1 s1) (fused_memory e2 s2).
Proof.
  intros * HM * HS.
  unfold fused_memory.
  unfold handle_memory.
  destruct s1,s2,HS; cbn in *.
  cbn in *.
  eapply ruttc_bind.
  apply I2F_memM_interp; [apply I2F_handle_memoryM; auto |]; auto.
  intros [] [] []; pstep; do 2 constructor; cbn; auto.
  constructor; auto.
Qed.

(** * Intrinsics (the internal to the memory-model ones) *)
Lemma I2F_fused_intrinsic :
  forall T1 T2 (e1 : @IntrinsicE PInf T1) (e2 : @IntrinsicE PFin T2),
    I2FE_Intrinsic e1 e2 ->
    forall s1 s2, I2F_FusedS s1 s2 ->
      I2F_refine_MCFGbot
        (prod_rel I2F_FusedS (fun r1 r2 => I2FA_Intrinsic e1 r1 e2 r2))
        (fused_intrinsic e1 s1) (fused_intrinsic e2 s2).
Proof.
  intros * HI * HS.
  unfold fused_intrinsic.
  unfold handle_intrinsic.
  destruct s1,s2,HS; cbn in *.
  cbn.
  eapply ruttc_bind.
  apply I2F_memM_interp; [apply I2F_handle_intrinsicM; auto |]; auto.
  intros [] [] []; pstep; do 2 constructor; cbn; auto.
  constructor; auto.
Qed.

(** * Draw *)
Lemma I2F_fused_draw :
  forall T1 T2 (e1 : @DrawE PInf T1) (e2 : @DrawE PFin T2),
    I2FE_Draw e1 e2 ->
    forall s1 s2, I2F_FusedS s1 s2 ->
      I2F_refine_MCFGbot
        (prod_rel I2F_FusedS (fun r1 r2 => I2FA_Draw e1 r1 e2 r2))
        (fused_draw e1 s1) (fused_draw e2 s2).
Proof.
  intros T1 T2 e1 e2 H s1 s2 Hs.
  destruct e1 as [τ1]; destruct e2 as [τ2].
  simp I2FE_Draw in H; subst.
  unfold fused_draw, handle_draw, I2F_refine_MCFGbot.
  erbind; [apply I2F_refine_lift_bot, I2F_default_dvalue_of_dtyp |].
  intros r1 r2 Hr; apply ruttc_ret; auto.
Qed.


(** * Lifting the intrinsic handler to [interp_intrinsics] *)
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

(** * Assembling the six per-handler lemmas into [interp_vellvm_h] *)
Lemma I2F_interp_vellvm_h :
  forall T1 T2 (e1 : @MCFGEtop PInf T1) (e2 : @MCFGEtop PFin T2),
    I2FE_MCFG e1 e2 ->
    forall s1 s2, I2F_FusedS s1 s2 ->
      I2F_refine_MCFGbot
        (prod_rel I2F_FusedS (fun r1 r2 => I2FA_MCFG e1 r1 e2 r2))
        (interp_vellvm_h e1 s1) (interp_vellvm_h e2 s2).
Proof.
  intros T1 T2 e1 e2 H s1 s2 Hs.
  unfold interp_vellvm_h.
  destruct e1 as [e1|e1]; destruct e2 as [e2|e2]; cbn in H; cbn; try easy.
  { (* ExternalCallE *)
    unfold fused_trigger.
    destruct e1 as [t1 f1 args1 | str1 | str1]; destruct e2 as [t2 f2 args2 | str2 | str2];
      simp I2FE_ExternalCall in H; cbn in H; try contradiction.
    - (* ExternalCall *)
      rbind I2F_dvalue.
      apply ruttc_trigger;
      [cbnn; simp I2FE_ExternalCall; auto |
      intros a b Hab; cbnn in Hab; simp I2FA_ExternalCall in Hab].
      intros r1 r2 Hr; rstep.
    - (* IO_stdout *)
      rbind Logic.eq.
      apply ruttc_trigger;
      [cbnn; simp I2FE_ExternalCall; auto |
      intros [] [] Hab; cbnn in Hab; simp I2FA_ExternalCall in Hab;
                  simp I2FA_ExternalCall; auto].
      intros r1 r2 <-; rstep.
      constructor; auto.
      cbn; simp I2FA_ExternalCall; auto.
    - (* IO_stderr *)
      rbind Logic.eq.
      apply ruttc_trigger;
      [cbnn; simp I2FE_ExternalCall; auto |
      intros [] [] Hab; cbnn in Hab; simp I2FA_ExternalCall in Hab;
      simp I2FA_ExternalCall; auto].
      intros r1 r2 <-; rstep.
      constructor; auto.
      cbn; simp I2FA_ExternalCall; auto.
  }
  destruct e1 as [e1|e1]; destruct e2 as [e2|e2]; cbn in H; cbn; try easy;
    [apply I2F_fused_intrinsic; auto |].
  destruct e1 as [e1|e1]; destruct e2 as [e2|e2]; cbn in H; cbn; try easy;
    [apply I2F_fused_global; auto|].
  destruct e1 as [e1|e1]; destruct e2 as [e2|e2]; cbn in H; cbn; try easy.
  destruct e1 as [e1|e1]; destruct e2 as [e2|e2]; cbn in H; cbn; try easy;
    [apply I2F_fused_local; auto | apply I2F_fused_stack; auto].
  destruct e1 as [e1|e1]; destruct e2 as [e2|e2]; cbn in H; cbn; try easy;
    [apply I2F_fused_memory; auto|].
  destruct e1 as [e1|e1]; destruct e2 as [e2|e2]; cbn in H; cbn; try easy;
    [apply I2F_fused_draw; auto|].
  destruct e1 as [e1|e1]; destruct e2 as [e2|e2]; cbn in H; cbn; try easy;
  [apply ruttc_trigger'; cbnn; auto |].
  destruct e1 as [e1|e1]; destruct e2 as [e2|e2]; cbn in H; cbn; try easy;
  [apply ruttc_trigger'; cbnn; auto |].
  destruct e1 as [e1|e1]; destruct e2 as [e2|e2]; cbn in H; cbn; try easy;
  [apply ruttc_trigger'; cbnn; auto |].
  destruct e1 as [e1|e1]; destruct e2 as [e2|e2]; cbn in H; cbn; try easy;
  [apply ruttc_trigger'; cbnn; auto |].
  apply ruttc_trigger'; cbnn; auto.
Qed.

(** * Transporting [ruttc] through [interp_state]
    This should be a generic lemma on [ruttc] and stateful interpreters,
    but the statement w.r.t. changing signatures is tricky
 *)
Lemma ruttc_interp_state_specialized {R1 R2} (RR : R1 -> R2 -> Prop) t1 t2
  (HR: I2F_refine_MCFG RR t1 t2):
  forall s1 s2,
    I2F_FusedS s1 s2 ->
    I2F_refine_MCFGbot (prod_rel I2F_FusedS RR)
      (interp_state interp_vellvm_h t1 s1)
      (interp_state interp_vellvm_h t2 s2).
Proof.
  ginit.
  revert t1 t2 HR.
  gcofix cih; intros.
  rewrite 2 unfold_interp_state.
  punfold HR; red in HR.
  induction HR; pclearbot.
  - cbn; gstep; constructor; auto.
  - cbn; gstep; constructor.
    gfinal; left; auto.
  - cbn.
    (* TODO fix *)
    guclo (@ruttc_clo_bind
             (@MCFGEbot PInf) (@MCFGEbot PFin) (@FusedS PInf * R1) (@FusedS PFin * R2)).
    econstructor.
    apply I2F_interp_vellvm_h; auto.
    intros [] [] []; cbn in *.
    gstep; constructor.
    gfinal; left; apply cih; auto.
    apply H1; auto.
  - cbn. rewrite tau_euttge.
    rewrite unfold_interp_state.
    apply IHHR.
  - cbn. rewrite tau_euttge.
    rewrite unfold_interp_state.
    apply IHHR.
  - cbn.
    generalize H; intros tmp.
    dependent induction H.
    cbnn; rewrite Eqit.bind_bind,bind_trigger.
    gstep; constructor; auto; constructor.
   - cbn.
    generalize H; intros tmp.
    dependent induction H.
    cbnn; rewrite Eqit.bind_bind,bind_trigger.
    gstep; constructor; auto; constructor.
Qed.


(** * The main result from this file: [interp_mcfg] *)
Lemma I2F_interp_mcfg {R} (t1 : @MCFGtop PInf R) (t2 : @MCFGtop PFin R):
  I2F_refine_MCFG Logic.eq t1 t2 ->
  forall s1 s2, I2F_FusedS s1 s2 ->
  I2F_refine_MCFGbot (prod_rel I2F_FusedS Logic.eq)
    (interp_mcfg t1 s1)
    (interp_mcfg t2 s2).
Proof.
  intros Hmcfg * Hfused.
  apply ruttc_interp_state_specialized; auto.
  apply I2F_interp_intrinsics; auto.
Qed.

Lemma I2F_interp_mcfg_bind {R1 R2 T1 T2} (RR : R1 -> R2 -> Prop) (RT : T1 -> T2 -> Prop)
  (t1 : @MCFGtop PInf R1) (t2 : @MCFGtop PFin R2)
  (k1 : R1 -> @MCFGtop PInf T1) (k2 : R2 -> @MCFGtop PFin T2) :
  I2F_refine_MCFG RR t1 t2 ->
  (forall r1 r2, RR r1 r2 -> I2F_refine_MCFG RT (k1 r1) (k2 r2)) ->
  forall s1 s2, I2F_FusedS s1 s2 ->
    I2F_refine_MCFGbot (prod_rel I2F_FusedS RT)
      (interp_mcfg (ITree.bind t1 k1) s1) (interp_mcfg (ITree.bind t2 k2) s2).
Proof.
  intros Ht Hk s1 s2 Hs.
  unfold interp_mcfg.
  apply ruttc_interp_state_specialized; auto.
  apply I2F_interp_intrinsics.
  eapply ruttc_bind; eauto.
Qed.
