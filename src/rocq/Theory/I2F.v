From ITree Require Import ITree Eq Rutt HeterogeneousRelations.

From Vellvm Require Import
  Utils
  Syntax
  Integers
  DynamicValues
  LLVMEvents
  Interfaces.IPtr
  Interfaces.Params
  Implementations.Address
  Implementations.Provenance
  Implementations.IPtrInfinite
  Implementations.IPtrFinite
  Implementations.Memory
  Implementations.ParamsV
  Denotation.

From Vellvm Require Import
  Theory.rutt_cutoff.

From Paco Require Import paco.

Definition sum_prerel {E1 E2 D1 D2 : Type -> Type} (PR1 : prerel E1 D1 ) (PR2 : prerel E2 D2) 
  : prerel (E1 +' E2) (D1 +' D2) :=
  fun A B e1 e2 =>
    match e1,e2 with
    | inl1 e1, inl1 e2 => PR1 _ _ e1 e2
    | inr1 e1, inr1 e2 => PR2 _ _ e1 e2
    | _,_ => False
    end
.

Definition sum_postrel {E1 E2 D1 D2 : Type -> Type} (PR1 : postrel E1 D1 ) (PR2 : postrel E2 D2) 
  : postrel (E1 +' E2) (D1 +' D2) :=
  fun A B e1 a e2 b => 
    match e1,e2 with
    | inl1 e1, inl1 e2 => PR1 _ _ e1 a e2 b
    | inr1 e1, inr1 e2 => PR2 _ _ e1 a e2 b
    | _,_ => False
    end
.


Section Refinement.

  Definition PInf : Params := @ParamsV IPZ IPZTheory.
  Definition PFin : Params := @ParamsV IP64Bit IP64BitTheory.

  (** * Value relations *)

  Definition I2F_Iptr : @iptr IPZ -> @iptr IP64Bit -> Prop :=
    fun z i => z = unsigned i.

  Definition I2F_Addr : @addr ProvenanceV (@AddressV IPZ) -> @addr ProvenanceV (@AddressV IP64Bit) -> Prop :=
    fun '(z,p) '(i,p') => I2F_Iptr z i /\ p = p'.

  Inductive I2F_dvalue : @dvalue PInf -> @dvalue PFin -> Prop :=
  | I2F_dvalue_Addr a a' :
    I2F_Addr a a' ->
    I2F_dvalue (@DVALUE_Addr PInf a) (@DVALUE_Addr PFin a')
  | I2F_dvalue_Int sz i :
    I2F_dvalue (DVALUE_I sz i) (DVALUE_I sz i)
  | I2F_dvalue_Ptr p p' :
    I2F_Iptr p p' ->
    I2F_dvalue (@DVALUE_Iptr PInf p) (@DVALUE_Iptr PFin p')
  | I2F_dvalue_Double d :
    I2F_dvalue (DVALUE_Double d) (DVALUE_Double d)
  | I2F_dvalue_Float f :
    I2F_dvalue (DVALUE_Float f) (DVALUE_Float f)
  | I2F_dvalue_Poison τ :
    I2F_dvalue (DVALUE_Poison τ) (DVALUE_Poison τ)
  | I2F_dvalue_None :
    I2F_dvalue DVALUE_None DVALUE_None
  | I2F_dvalue_Struct s1 s2 :
    Forall2 I2F_dvalue s1 s2 ->
    I2F_dvalue (DVALUE_Struct s1) (DVALUE_Struct s2)
  | I2F_dvalue_Packed_struct s1 s2 :
    Forall2 I2F_dvalue s1 s2 ->
    I2F_dvalue (DVALUE_Packed_struct s1) (DVALUE_Packed_struct s2)
  | I2F_dvalue_Array τ s1 s2 :
    Forall2 I2F_dvalue s1 s2 ->
    I2F_dvalue (DVALUE_Array τ s1) (DVALUE_Array τ s2)
  | I2F_dvalue_Vector τ s1 s2 :
    Forall2 I2F_dvalue s1 s2 ->
    I2F_dvalue (DVALUE_Vector τ s1) (DVALUE_Vector τ s2)
  .

  (* Exceptions are dvalues, and calls/intrinsics answer in [exc + dvalue] *)
  Notation I2F_exc_dvalue := (sum_rel I2F_dvalue I2F_dvalue).

  (** * Event relations, one per event family

      Two events are related when they are the same constructor, carrying
      pointwise [I2F]-related payloads. Recall the components that do not
      mention values ([raw_id], [dtyp], intrinsic names, [int8] streams,
      the [unit] messages of the abortive events) are shared between the
      two instantiations, hence required equal. *)

  Variant I2FE_Call : prerel (@CallE PInf) (@CallE PFin) :=
    | I2FE_call τ f1 args1 f2 args2 :
      I2F_dvalue f1 f2 ->
      Forall2 I2F_dvalue args1 args2 ->
      I2FE_Call (@Call PInf τ f1 args1) (@Call PFin τ f2 args2)
  .

  Variant I2FE_ExternalCall : prerel (@ExternalCallE PInf) (@ExternalCallE PFin) :=
    | I2FE_extcall τ f1 args1 f2 args2 :
      I2F_dvalue f1 f2 ->
      Forall2 I2F_dvalue args1 args2 ->
      I2FE_ExternalCall (@ExternalCall PInf τ f1 args1) (@ExternalCall PFin τ f2 args2)
    | I2FE_stdout str :
      I2FE_ExternalCall (@IO_stdout PInf str) (@IO_stdout PFin str)
    | I2FE_stderr str :
      I2FE_ExternalCall (@IO_stderr PInf str) (@IO_stderr PFin str)
  .

  Variant I2FE_Intrinsic : prerel (@IntrinsicE PInf) (@IntrinsicE PFin) :=
    | I2FE_intrinsic τ f args1 va1 args2 va2 :
      Forall2 I2F_dvalue args1 args2 ->
      option_rel I2F_Addr va1 va2 ->
      I2FE_Intrinsic (@Intrinsic PInf τ f args1 va1) (@Intrinsic PFin τ f args2 va2)
  .

  Variant I2FE_Global : prerel (@GlobalE PInf) (@GlobalE PFin) :=
    | I2FE_gwrite x dv1 dv2 :
      I2F_dvalue dv1 dv2 ->
      I2FE_Global (@GlobalWrite PInf x dv1) (@GlobalWrite PFin x dv2)
    | I2FE_gread x :
      I2FE_Global (@GlobalRead PInf x) (@GlobalRead PFin x)
  .

  Variant I2FE_Local : prerel (@LocalE PInf) (@LocalE PFin) :=
    | I2FE_lwrite x dv1 dv2 :
      I2F_dvalue dv1 dv2 ->
      I2FE_Local (@LocalWrite PInf x dv1) (@LocalWrite PFin x dv2)
    | I2FE_lread x :
      I2FE_Local (@LocalRead PInf x) (@LocalRead PFin x)
  .

  Variant I2FE_Stack : prerel (@StackE PInf) (@StackE PFin) :=
    | I2FE_spush args1 args2 :
      Forall2 (prod_rel Logic.eq I2F_dvalue) args1 args2 ->
      I2FE_Stack (@StackPush PInf args1) (@StackPush PFin args2)
    | I2FE_spop :
      I2FE_Stack (@StackPop PInf) (@StackPop PFin)
    | I2FE_sraise exc1 exc2 :
      I2F_dvalue exc1 exc2 ->
      I2FE_Stack (@StackRaise PInf exc1) (@StackRaise PFin exc2)
    | I2FE_sgetexc :
      I2FE_Stack (@StackGetExc PInf) (@StackGetExc PFin)
  .

  Variant I2FE_Memory : prerel (@MemoryE PInf) (@MemoryE PFin) :=
    | I2FE_mempush :
      I2FE_Memory (@MemPush PInf) (@MemPush PFin)
    | I2FE_mempop :
      I2FE_Memory (@MemPop PInf) (@MemPop PFin)
    | I2FE_alloca τ n align :
      I2FE_Memory (@Alloca PInf τ n align) (@Alloca PFin τ n align)
    | I2FE_load τ a1 a2 :
      I2F_dvalue a1 a2 ->
      I2FE_Memory (@Load PInf τ a1) (@Load PFin τ a2)
    | I2FE_store τ a1 v1 a2 v2 :
      I2F_dvalue a1 a2 ->
      I2F_dvalue v1 v2 ->
      I2FE_Memory (@Store PInf τ a1 v1) (@Store PFin τ a2 v2)
  .

  Variant I2FE_Draw : prerel (@DrawE PInf) (@DrawE PFin) :=
    | I2FE_draw τ :
      I2FE_Draw (@Draw PInf τ) (@Draw PFin τ)
  .

  Variant I2FE_Exc : prerel (@LLVMExcE PInf) (@LLVMExcE PFin) :=
    | I2FE_exc exc1 exc2 :
      I2F_dvalue exc1 exc2 ->
      I2FE_Exc (@LLVMExc PInf exc1) (@LLVMExc PFin exc2)
  .

  (* [OOME], [UBE], [DebugE], [FailureE] do not mention values: they are
     shared by both instantiations. Note that pairs of related [OOME]
     (resp. [UBE]) events can alternatively be discharged by the cut
     mechanism of [ruttc] --- see [I2F_refine] below. *)

  Variant I2FE_OOM : prerel OOME OOME :=
    | I2FE_throwOOM u1 u2 :
      I2FE_OOM (ThrowOOM u1) (ThrowOOM u2)
  .

  Variant I2FE_UB : prerel UBE UBE :=
    | I2FE_throwUB u1 u2 :
      I2FE_UB (ThrowUB u1) (ThrowUB u2)
  .

  Variant I2FE_Debug : prerel DebugE DebugE :=
    | I2FE_debug u1 u2 :
      I2FE_Debug (Debug u1) (Debug u2)
  .

  Variant I2FE_Failure : prerel FailureE FailureE :=
    | I2FE_throw u1 u2 :
      I2FE_Failure (Throw u1) (Throw u2)
  .

  (** * Answer relations, one per event family

      [ruttc] additionally takes a relation on the answers returned to two
      related events: when relating [Vis e1 k1] with [Vis e2 k2], the
      continuations only have to be related on pairs of answers related by
      it. It is our relational assumption on the environment, to be
      discharged when interpreting each event family: the answers are
      related by the [I2F] value relation matching the answer type of the
      event --- [I2F_dvalue] on [dvalue] answers, its [sum_rel]
      (resp. [option_rel]) lifting on [exc + dvalue] (resp. [option exc])
      answers, trivial on [unit], and vacuous on [void] (abortive events
      never answer). *)

  Variant I2FA_Call : postrel (@CallE PInf) (@CallE PFin) :=
    | I2FA_call τ1 f1 args1 τ2 f2 args2 r1 r2 :
      I2F_exc_dvalue r1 r2 ->
      I2FA_Call (@Call PInf τ1 f1 args1) r1 (@Call PFin τ2 f2 args2) r2
  .

  Variant I2FA_ExternalCall : postrel (@ExternalCallE PInf) (@ExternalCallE PFin) :=
    | I2FA_extcall τ1 f1 args1 τ2 f2 args2 dv1 dv2 :
      I2F_dvalue dv1 dv2 ->
      I2FA_ExternalCall (@ExternalCall PInf τ1 f1 args1) dv1 (@ExternalCall PFin τ2 f2 args2) dv2
    | I2FA_stdout str1 str2 (a b : unit) :
      I2FA_ExternalCall (@IO_stdout PInf str1) a (@IO_stdout PFin str2) b
    | I2FA_stderr str1 str2 (a b : unit) :
      I2FA_ExternalCall (@IO_stderr PInf str1) a (@IO_stderr PFin str2) b
  .

  Variant I2FA_Intrinsic : postrel (@IntrinsicE PInf) (@IntrinsicE PFin) :=
    | I2FA_intrinsic τ1 f1 args1 va1 τ2 f2 args2 va2 r1 r2 :
      I2F_exc_dvalue r1 r2 ->
      I2FA_Intrinsic (@Intrinsic PInf τ1 f1 args1 va1) r1 (@Intrinsic PFin τ2 f2 args2 va2) r2
  .

  Variant I2FA_Global : postrel (@GlobalE PInf) (@GlobalE PFin) :=
    | I2FA_gwrite x1 dv1 x2 dv2 (a b : unit) :
      I2FA_Global (@GlobalWrite PInf x1 dv1) a (@GlobalWrite PFin x2 dv2) b
    | I2FA_gread x1 x2 dv1 dv2 :
      I2F_dvalue dv1 dv2 ->
      I2FA_Global (@GlobalRead PInf x1) dv1 (@GlobalRead PFin x2) dv2
  .

  Variant I2FA_Local : postrel (@LocalE PInf) (@LocalE PFin) :=
    | I2FA_lwrite x1 dv1 x2 dv2 (a b : unit) :
      I2FA_Local (@LocalWrite PInf x1 dv1) a (@LocalWrite PFin x2 dv2) b
    | I2FA_lread x1 x2 dv1 dv2 :
      I2F_dvalue dv1 dv2 ->
      I2FA_Local (@LocalRead PInf x1) dv1 (@LocalRead PFin x2) dv2
  .

  Variant I2FA_Stack : postrel (@StackE PInf) (@StackE PFin) :=
    | I2FA_spush args1 args2 (a b : unit) :
      I2FA_Stack (@StackPush PInf args1) a (@StackPush PFin args2) b
    | I2FA_spop (a b : unit) :
      I2FA_Stack (@StackPop PInf) a (@StackPop PFin) b
    | I2FA_sraise exc1 exc2 (a b : unit) :
      I2FA_Stack (@StackRaise PInf exc1) a (@StackRaise PFin exc2) b
    | I2FA_sgetexc oe1 oe2 :
      option_rel I2F_dvalue oe1 oe2 ->
      I2FA_Stack (@StackGetExc PInf) oe1 (@StackGetExc PFin) oe2
  .

  Variant I2FA_Memory : postrel (@MemoryE PInf) (@MemoryE PFin) :=
    | I2FA_mempush (a b : unit) :
      I2FA_Memory (@MemPush PInf) a (@MemPush PFin) b
    | I2FA_mempop (a b : unit) :
      I2FA_Memory (@MemPop PInf) a (@MemPop PFin) b
    (* [Alloca] answers with the fresh address wrapped as a [dvalue]:
       the two memories allocate at [I2F_Addr]-related addresses. *)
    | I2FA_alloca τ1 n1 align1 τ2 n2 align2 dv1 dv2 :
      I2F_dvalue dv1 dv2 ->
      I2FA_Memory (@Alloca PInf τ1 n1 align1) dv1 (@Alloca PFin τ2 n2 align2) dv2
    | I2FA_load τ1 a1 τ2 a2 dv1 dv2 :
      I2F_dvalue dv1 dv2 ->
      I2FA_Memory (@Load PInf τ1 a1) dv1 (@Load PFin τ2 a2) dv2
    | I2FA_store τ1 a1 v1 τ2 a2 v2 (a b : unit) :
      I2FA_Memory (@Store PInf τ1 a1 v1) a (@Store PFin τ2 a2 v2) b
  .

  Variant I2FA_Draw : postrel (@DrawE PInf) (@DrawE PFin) :=
    | I2FA_draw τ1 τ2 dv1 dv2 :
      I2F_dvalue dv1 dv2 ->
      I2FA_Draw (@Draw PInf τ1) dv1 (@Draw PFin τ2) dv2
  .

  (* The abortive events answer in [void]: their answer relations are
     vacuous, and so are the associated continuation proof obligations. *)

  Variant I2FA_Exc : postrel (@LLVMExcE PInf) (@LLVMExcE PFin) :=
    | I2FA_exc exc1 exc2 (a b : void) :
      I2FA_Exc (@LLVMExc PInf exc1) a (@LLVMExc PFin exc2) b
  .

  Variant I2FA_OOM : postrel OOME OOME :=
    | I2FA_throwOOM u1 u2 (a b : void) :
      I2FA_OOM (ThrowOOM u1) a (ThrowOOM u2) b
  .

  Variant I2FA_UB : postrel UBE UBE :=
    | I2FA_throwUB u1 u2 (a b : void) :
      I2FA_UB (ThrowUB u1) a (ThrowUB u2) b
  .

  Variant I2FA_Debug : postrel DebugE DebugE :=
    | I2FA_debug u1 u2 (a b : unit) :
      I2FA_Debug (Debug u1) a (Debug u2) b
  .

  Variant I2FA_Failure : postrel FailureE FailureE :=
    | I2FA_throw u1 u2 (a b : void) :
      I2FA_Failure (Throw u1) a (Throw u2) b
  .

  (** * Combined relations on [MCFGEtop] and [CFGEtop]

      The per-family relations are glued along the structure of the event
      signatures with [sum_prerel]/[sum_postrel]. This is the format
      expected by the [mrec] reasoning principle
      ([RuttFacts.interp_mrec_rutt] and its [ruttc] analogue to come):
      since [CFGEtop ≡ CallE +' MCFGEtop] and [denote_mcfg] is an [mrec]
      over [CallE], the [CFG]-level relations are literally
      [sum_prerel I2FE_Call I2FE_MCFG] / [sum_postrel I2FA_Call I2FA_MCFG]. *)

  Definition I2FE_MCFG : prerel (@MCFGEtop PInf) (@MCFGEtop PFin) :=
    sum_prerel I2FE_ExternalCall
      (sum_prerel I2FE_Intrinsic
         (sum_prerel I2FE_Global
            (sum_prerel (sum_prerel I2FE_Local I2FE_Stack)
               (sum_prerel I2FE_Memory
                  (sum_prerel I2FE_Draw
                     (sum_prerel I2FE_OOM
                        (sum_prerel I2FE_Exc
                           (sum_prerel I2FE_UB
                              (sum_prerel I2FE_Debug I2FE_Failure))))))))).

  Definition I2FA_MCFG : postrel (@MCFGEtop PInf) (@MCFGEtop PFin) :=
    sum_postrel I2FA_ExternalCall
      (sum_postrel I2FA_Intrinsic
         (sum_postrel I2FA_Global
            (sum_postrel (sum_postrel I2FA_Local I2FA_Stack)
               (sum_postrel I2FA_Memory
                  (sum_postrel I2FA_Draw
                     (sum_postrel I2FA_OOM
                        (sum_postrel I2FA_Exc
                           (sum_postrel I2FA_UB
                              (sum_postrel I2FA_Debug I2FA_Failure))))))))).

  Definition I2FE_CFG : prerel (@CFGEtop PInf) (@CFGEtop PFin) :=
    sum_prerel I2FE_Call I2FE_MCFG.

  Definition I2FA_CFG : postrel (@CFGEtop PInf) (@CFGEtop PFin) :=
    sum_postrel I2FA_Call I2FA_MCFG.

  (** * The refinement relation *)

  Variant cutUB {E} `{UBE -< E} : forall [A], E A -> Prop :=
    | CutUB v : cutUB (subevent _ (ThrowUB v)).

  Variant cutOOM {E} `{OOME -< E} : forall [A], E A -> Prop :=
    | CutOOM v : cutOOM (subevent _ (ThrowOOM v)).

  (* The infinite computation (left) and the finite one (right) proceed in
     lockstep over [I2FE]-related events answered by [I2FA]-related values,
     except that the equivalence is short-circuited if the finite side runs
     out of memory (cut on OOM on the right); UB should arise simultaneously
     on both sides, so we may cut it off on the left. *)

  Definition I2F_refine_MCFG {R1 R2} (RR : R1 -> R2 -> Prop)
    : @MCFGtop PInf R1 -> @MCFGtop PFin R2 -> Prop :=
    ruttc cutUB cutOOM I2FE_MCFG I2FA_MCFG RR.

  Definition I2F_refine_CFG {R1 R2} (RR : R1 -> R2 -> Prop)
    : @CFGtop PInf R1 -> @CFGtop PFin R2 -> Prop :=
    ruttc cutUB cutOOM I2FE_CFG I2FA_CFG RR.

  Definition I2F_refine : @MCFGtop PInf (@dvalue PInf) -> @MCFGtop PFin (@dvalue PFin) -> Prop :=
    I2F_refine_MCFG I2F_dvalue.

(* Lemma I2F_refine_MCFG_trigger {A B} (e : @MCFGEtop PInf A) (f : @MCFGEtop PFin B) RR : *)
(*   I2FE_MCFG e f -> *)
(*   I2F_refine_MCFG RR (ITree.trigger e) (ITree.trigger f). *)
(* Proof. *)
(*   intros; apply ruttc_trigger; auto. *)
   
  Hint Constructors I2FA_Local.
Require Import Stdlib.Program.Equality.
  Lemma denote_expr :
    forall (e : exp dtyp) τ, I2F_refine (@denote_exp PInf τ e) (@denote_exp PFin τ e).
  Proof.
    apply (@exp_ind dtyp (fun e => forall τ, I2F_refine (@denote_exp PInf τ e) (@denote_exp PFin τ e)) (fun _ => True)); auto.
    - intros; cbn.
      destruct id; cbn.
      + apply ruttc_trigger.
        constructor.
        cbn.
        intros.
        dependent induction H; subst; auto.

      apply I2F_refine_MCFG_trigger.
    intros e.
    induction e with (Q := fun _ => True).

  (* Lemma denote_ok : Prop. *)
  (*   refine (forall i oa oa', rutt I2FE (@denote_instr PInf i oa) (@denote_instr PFin i (_ oa))). *)
  (*   3: refine (fmap _). *)
  (*   3: refine (fun '(a,p) => _). *)
  (*  3:{ cbn. *)


  (* Lemma handle_memory_refine : Prop. *)
  (*   refine (forall {X} (e : @MemoryE PInf X), _ : Prop). *)
  (*     @handle_memoryM PIn *)



End Refinement.
