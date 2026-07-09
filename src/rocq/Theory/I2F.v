From Equations Require Import Equations.

From Stdlib Require Import Lia.

From ExtLib Require Import Structures.Monads.

From ITree Require Import ITree Eq HeterogeneousRelations.

From Vellvm Require Import
  Utils
  Syntax
  VellvmIntegers
  Integers
  DynamicValues
  EOU
  LLVMEvents
  Semantics.Operations
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

(* I want versions that compute to reduce in proofs rather than nest constructors/inversions *)
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
  Hint Constructors I2F_dvalue : core.

  (* Exceptions are dvalues, and calls/intrinsics answer in [exc + dvalue] *)
  Notation I2F_exc_dvalue := (sum_rel I2F_dvalue I2F_dvalue).

  (** Relating pure computations in the [EOU] monad, mirroring the cut
      structure of [ruttc] (see [I2F_refine_lift]): lockstep on returns
      and errors, while UB on the infinite (left) side and OOM on the
      finite (right) side short-circuit. *)
  Variant I2F_EOU {A1 A2} (RR : A1 -> A2 -> Prop) : EOU A1 -> EOU A2 -> Prop :=
    | I2F_EOU_ret a1 a2 : RR a1 a2 -> I2F_EOU RR (raise_ret a1) (raise_ret a2)
    | I2F_EOU_error s1 s2 : I2F_EOU RR (raise_error s1) (raise_error s2)
    | I2F_EOU_ub s m : I2F_EOU RR (raise_ub s) m
    | I2F_EOU_oom m s : I2F_EOU RR m (raise_oom s)
  .
  #[local] Hint Constructors I2F_EOU : core.

  (** * Event relations, one per event family

      Two events are related when they are the same constructor, carrying
      pointwise [I2F]-related payloads. Recall the components that do not
      mention values ([raw_id], [dtyp], intrinsic names, [int8] streams,
      the [unit] messages of the abortive events) are shared between the
      two instantiations, hence required equal. *)

  Equations I2FE_Call : prerel (@CallE PInf) (@CallE PFin) :=
    I2FE_Call (@Call PInf τ1 f1 args1) (@Call PFin τ2 f2 args2) :=
      τ1 = τ2 /\ I2F_dvalue f1 f2 /\ Forall2 I2F_dvalue args1 args2.

  Equations I2FE_ExternalCall : prerel (@ExternalCallE PInf) (@ExternalCallE PFin) :=
    I2FE_ExternalCall (@ExternalCall PInf τ1 f1 args1) (@ExternalCall PFin τ2 f2 args2) :=
      τ1 = τ2 /\ I2F_dvalue f1 f2 /\ Forall2 I2F_dvalue args1 args2;
    I2FE_ExternalCall (@IO_stdout PInf str1) (@IO_stdout PFin str2) := str1 = str2;
    I2FE_ExternalCall (@IO_stderr PInf str1) (@IO_stderr PFin str2) := str1 = str2;
    I2FE_ExternalCall _ _ := False.

  Equations I2FE_Intrinsic : prerel (@IntrinsicE PInf) (@IntrinsicE PFin) :=
    I2FE_Intrinsic (@Intrinsic PInf τ1 f1 args1 va1) (@Intrinsic PFin τ2 f2 args2 va2) :=
      τ1 = τ2 /\ f1 = f2 /\ Forall2 I2F_dvalue args1 args2 /\ option_rel I2F_Addr va1 va2.

  Equations I2FE_Global : prerel (@GlobalE PInf) (@GlobalE PFin) :=
    I2FE_Global (@GlobalWrite PInf x1 dv1) (@GlobalWrite PFin x2 dv2) :=
      x1 = x2 /\ I2F_dvalue dv1 dv2;
    I2FE_Global (@GlobalRead PInf x1) (@GlobalRead PFin x2) := x1 = x2;
    I2FE_Global _ _ := False.

  Equations I2FE_Local : prerel (@LocalE PInf) (@LocalE PFin) :=
    I2FE_Local (@LocalWrite PInf x1 dv1) (@LocalWrite PFin x2 dv2) :=
      x1 = x2 /\ I2F_dvalue dv1 dv2;
    I2FE_Local (@LocalRead PInf x1) (@LocalRead PFin x2) := x1 = x2;
    I2FE_Local _ _ := False.

  Equations I2FE_Stack : prerel (@StackE PInf) (@StackE PFin) :=
    I2FE_Stack (@StackPush PInf args1) (@StackPush PFin args2) :=
      Forall2 (prod_rel Logic.eq I2F_dvalue) args1 args2;
    I2FE_Stack (@StackPop PInf) (@StackPop PFin) := True;
    I2FE_Stack (@StackRaise PInf exc1) (@StackRaise PFin exc2) := I2F_dvalue exc1 exc2;
    I2FE_Stack (@StackGetExc PInf) (@StackGetExc PFin) := True;
    I2FE_Stack _ _ := False.

  Equations I2FE_Memory : prerel (@MemoryE PInf) (@MemoryE PFin) :=
    I2FE_Memory (@MemPush PInf) (@MemPush PFin) := True;
    I2FE_Memory (@MemPop PInf) (@MemPop PFin) := True;
    I2FE_Memory (@Alloca PInf τ1 n1 align1) (@Alloca PFin τ2 n2 align2) :=
      τ1 = τ2 /\ n1 = n2 /\ align1 = align2;
    I2FE_Memory (@Load PInf τ1 a1) (@Load PFin τ2 a2) :=
      τ1 = τ2 /\ I2F_dvalue a1 a2;
    I2FE_Memory (@Store PInf τ1 a1 v1) (@Store PFin τ2 a2 v2) :=
      τ1 = τ2 /\ I2F_dvalue a1 a2 /\ I2F_dvalue v1 v2;
    I2FE_Memory _ _ := False.

  Equations I2FE_Draw : prerel (@DrawE PInf) (@DrawE PFin) :=
    I2FE_Draw (@Draw PInf τ1) (@Draw PFin τ2) := τ1 = τ2.

  Equations I2FE_Exc : prerel (@LLVMExcE PInf) (@LLVMExcE PFin) :=
    I2FE_Exc (@LLVMExc PInf exc1) (@LLVMExc PFin exc2) := I2F_dvalue exc1 exc2.

  (* [OOME], [UBE], [DebugE], [FailureE] do not mention values: they are
     shared by both instantiations. Note that pairs of related [OOME]
     (resp. [UBE]) events can alternatively be discharged by the cut
     mechanism of [ruttc] --- see [I2F_refine] below. *)

  Equations I2FE_OOM : prerel OOME OOME :=
    I2FE_OOM (ThrowOOM u1) (ThrowOOM u2) := True.

  Equations I2FE_UB : prerel UBE UBE :=
    I2FE_UB (ThrowUB u1) (ThrowUB u2) := True.

  Equations I2FE_Debug : prerel DebugE DebugE :=
    I2FE_Debug (Debug u1) (Debug u2) := True.

  Equations I2FE_Failure : prerel FailureE FailureE :=
    I2FE_Failure (Throw u1) (Throw u2) := True.

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

  Equations I2FA_Call : postrel (@CallE PInf) (@CallE PFin) :=
    I2FA_Call (@Call PInf τ1 f1 args1) r1 (@Call PFin τ2 f2 args2) r2 := I2F_exc_dvalue r1 r2.

  Equations I2FA_ExternalCall : postrel (@ExternalCallE PInf) (@ExternalCallE PFin) :=
    I2FA_ExternalCall (@ExternalCall PInf τ1 f1 args1) dv1 (@ExternalCall PFin τ2 f2 args2) dv2 := I2F_dvalue dv1 dv2;
    I2FA_ExternalCall (@IO_stdout PInf str1) a (@IO_stdout PFin str2) b := True;
    I2FA_ExternalCall (@IO_stderr PInf str1) a (@IO_stderr PFin str2) b := True;
    I2FA_ExternalCall _ _ _ _ := False.

  Equations I2FA_Intrinsic : postrel (@IntrinsicE PInf) (@IntrinsicE PFin) :=
    I2FA_Intrinsic (@Intrinsic PInf τ1 f1 args1 va1) r1 (@Intrinsic PFin τ2 f2 args2 va2) r2 := I2F_exc_dvalue r1 r2.

  Equations I2FA_Global : postrel (@GlobalE PInf) (@GlobalE PFin) :=
    I2FA_Global (@GlobalWrite PInf x1 dv1) a (@GlobalWrite PFin x2 dv2) b := True;
    I2FA_Global (@GlobalRead PInf x1) dv1 (@GlobalRead PFin x2) dv2 := I2F_dvalue dv1 dv2 ;
    I2FA_Global _ _ _ _ := False.
  
  Equations I2FA_Local : postrel (@LocalE PInf) (@LocalE PFin) :=
    I2FA_Local (@LocalWrite PInf x1 dv1) a (@LocalWrite PFin x2 dv2) b := True;
    I2FA_Local (@LocalRead PInf x1) dv1 (@LocalRead PFin x2) dv2 := I2F_dvalue dv1 dv2;
    I2FA_Local _ _ _ _ := False.

  Equations I2FA_Stack : postrel (@StackE PInf) (@StackE PFin) :=
    I2FA_Stack (@StackPush PInf args1) a (@StackPush PFin args2) b := True;
    I2FA_Stack (@StackPop PInf) a (@StackPop PFin) b := True;
    I2FA_Stack (@StackRaise PInf exc1) a (@StackRaise PFin exc2) b := True;
    I2FA_Stack (@StackGetExc PInf) oe1 (@StackGetExc PFin) oe2 := option_rel I2F_dvalue oe1 oe2;
    I2FA_Stack _ _ _ _ := False.

  (* [Alloca] answers with the fresh address wrapped as a [dvalue]:
     the two memories allocate at [I2F_Addr]-related addresses. *)
  Equations I2FA_Memory : postrel (@MemoryE PInf) (@MemoryE PFin) :=
    I2FA_Memory (@MemPush PInf) a (@MemPush PFin) b := True;
    I2FA_Memory (@MemPop PInf) a (@MemPop PFin) b := True;
    I2FA_Memory (@Alloca PInf τ1 n1 align1) dv1 (@Alloca PFin τ2 n2 align2) dv2 := I2F_dvalue dv1 dv2;
    I2FA_Memory (@Load PInf τ1 a1) dv1 (@Load PFin τ2 a2) dv2 := I2F_dvalue dv1 dv2;
    I2FA_Memory (@Store PInf τ1 a1 v1) a (@Store PFin τ2 a2 v2) b := True;
    I2FA_Memory _ _ _ _ := False.

  Equations I2FA_Draw : postrel (@DrawE PInf) (@DrawE PFin) :=
    I2FA_Draw (@Draw PInf τ1) dv1 (@Draw PFin τ2) dv2 := I2F_dvalue dv1 dv2.

  (* The abortive events answer in [void]: their answer relations are
     vacuous ([False] bodies), and so are the associated continuation
     proof obligations. *)

  Equations I2FA_Exc : postrel (@LLVMExcE PInf) (@LLVMExcE PFin) :=
    I2FA_Exc (@LLVMExc PInf exc1) a (@LLVMExc PFin exc2) b := False.

  Equations I2FA_OOM : postrel OOME OOME :=
    I2FA_OOM (ThrowOOM u1) a (ThrowOOM u2) b := False.

  Equations I2FA_UB : postrel UBE UBE :=
    I2FA_UB (ThrowUB u1) a (ThrowUB u2) b := False.

  Equations I2FA_Debug : postrel DebugE DebugE :=
    I2FA_Debug (Debug u1) a (Debug u2) b := True.

  Equations I2FA_Failure : postrel FailureE FailureE :=
    I2FA_Failure (Throw u1) a (Throw u2) b := False.

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

  (** Lifting [I2F_EOU]-related pure computations into the refinement.
      This is the workhorse for all the arithmetic cases of [denote_exp]:
      they end in [lift (f ...)] for pure [f]s, so each of them reduces to
      an [I2F_EOU] fact about [f], proved by first-order case analysis. *)
  Lemma I2F_refine_lift {R1 R2} (RR : R1 -> R2 -> Prop) (m1 : EOU R1) (m2 : EOU R2) :
    I2F_EOU RR m1 m2 ->
    I2F_refine_MCFG RR (EOU_to_itree m1) (EOU_to_itree m2).
  Proof.
    intros []; cbn.
    - pfold; constructor; auto.
    - apply ruttc_trigger_cast; easy.
    - pfold; red; cbn.
      apply EqCutL; constructor.
    - pfold; red; cbn.
      apply EqCutR; constructor.
  Qed.

  (* [denote_exp] only ever applies [EOU_to_itree] to pure computations we
     relate through [I2F_refine_lift]; prevent [cbn] from unfolding it into
     a stuck match that would obstruct applying the lemma. *)
  #[local] Arguments EOU_to_itree : simpl never.

(* Lemma I2F_refine_MCFG_trigger {A B} (e : @MCFGEtop PInf A) (f : @MCFGEtop PFin B) RR : *)
(*   I2FE_MCFG e f -> *)
(*   I2F_refine_MCFG RR (ITree.trigger e) (ITree.trigger f). *)
(* Proof. *)
(*   intros; apply ruttc_trigger; auto. *)
   
  (* Hint Constructors I2FA_Local. *) (* I2FA_Local is now an Equations definition, no constructors *)

  Tactic Notation "simp_id" := cbn; cbv[resum ReSum_id id_ Id_IFun].
  Tactic Notation "simp_id" "in" ident(H) := cbn in H; cbv[resum ReSum_id id_ Id_IFun] in H.

  Tactic Notation "simp!" :=
    simp I2FE_Call I2FE_ExternalCall I2FE_Intrinsic I2FE_Global I2FE_Local I2FE_Stack I2FE_Memory I2FE_Draw
         in *.

  Ltac rew H :=
    autorewrite with
      I2FE_Call I2FE_ExternalCall I2FE_Intrinsic
      I2FE_Global I2FE_Local
      I2FE_Stack I2FE_Memory I2FE_Draw
      I2FE_Failure I2FE_OOM I2FE_UB
      (* I2FA_Call I2FA_AxternalCall I2FA_Intrinsic I2FA_Global I2FA_Local I2FA_Stack I2FA_Memory I2FA_Draw *)
      in H.
  
  (** The pure content of the [EXP_Integer] case, and the one place where
      the 14-way case analysis on [dtyp] happens. *)
  Lemma I2F_denote_int_syntax_as_int : forall τ x,
      I2F_EOU I2F_dvalue
        (@denote_int_syntax_as_int PInf τ x)
        (@denote_int_syntax_as_int PFin τ x).
  Proof.
    intros; destruct τ; cbn; try (now repeat constructor).
    (* [DTYPE_Iptr]: the finite side either OOMs ([I2F_EOU_oom]) or
       returns [repr x] with [x] in range, so that [unsigned (repr x) = x]. *)
    unfold from_Z_bits.
    destruct ((denote_int_syntax x <=? @Integers.max_unsigned 64)%Z
                && (denote_int_syntax x >=? 0)%Z) eqn:EQ; cbn.
    - apply andb_prop in EQ as [LE GE].
      apply Z.leb_le in LE; apply Z.geb_le in GE.
      do 2 constructor.
      red; rewrite Integers.unsigned_repr; [reflexivity | lia].
    - constructor.
  Qed.

  (** The pure content of the [EXP_Float] case. The float parsing is
      parameter-independent: both sides run the very same computation. *)
  Lemma I2F_denote_float_syntax_as_float : forall τ x,
      I2F_EOU I2F_dvalue
        (@denote_float_syntax_as_float PInf τ x)
        (@denote_float_syntax_as_float PFin τ x).
  Proof.
    intros; destruct τ; cbn; try (now repeat constructor).
    repeat (break_match_goal; cbn); now repeat constructor.
  Qed.

  (** [I2F_EOU] is reflexive at [eq]: parameter-independent pure
      computations (e.g. type guards, which mention no value) are related
      to themselves for free, with no case analysis on their input. *)
  Lemma I2F_EOU_refl {A} (m : EOU A) : I2F_EOU Logic.eq m m.
  Proof.
    destruct m; auto.
  Qed.

  (** Compatibility of [I2F_EOU] with the monadic structure of [EOU]. *)
  Lemma I2F_EOU_bind {A1 A2 B1 B2} (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop)
        (m1 : EOU A1) (m2 : EOU A2) (k1 : A1 -> EOU B1) (k2 : A2 -> EOU B2) :
    I2F_EOU RA m1 m2 ->
    (forall a1 a2, RA a1 a2 -> I2F_EOU RB (k1 a1) (k2 a2)) ->
    I2F_EOU RB (bind m1 k1) (bind m2 k2).
  Proof.
    intros [] KEQ; cbn; eauto.
  Qed.

  Lemma I2F_EOU_map_monad {A B1 B2} (RB : B1 -> B2 -> Prop)
        (f1 : A -> EOU B1) (f2 : A -> EOU B2) (l : list A) :
    (forall a, In a l -> I2F_EOU RB (f1 a) (f2 a)) ->
    I2F_EOU (Forall2 RB) (map_monad f1 l) (map_monad f2 l).
  Proof.
    induction l as [| a l IH]; intros HIN; cbn.
    - now constructor.
    - eapply I2F_EOU_bind; [apply HIN; now left|].
      intros b1 b2 HB.
      eapply I2F_EOU_bind; [apply IH; intros; apply HIN; now right|].
      intros bs1 bs2 HBS.
      do 2 constructor; auto.
  Qed.

  Lemma Forall2_repeat {A B} (R : A -> B -> Prop) a b n :
    R a b -> Forall2 R (repeat a n) (repeat b n).
  Proof.
    induction n; cbn; intros; constructor; auto.
  Qed.

  (* The zero intptr and the null address of the two models are related. *)
  Lemma I2F_Iptr_zero : I2F_Iptr zero_iptr zero_iptr.
  Proof.
    red; cbn; rewrite ?Integers.unsigned_zero; easy.
  Qed.

  Lemma I2F_Addr_null : I2F_Addr null null.
  Proof.
    cbn; split; [apply I2F_Iptr_zero | reflexivity].
  Qed.

  (* [Extern]/[apply] rather than [Resolve]/[simple apply]: the goals show
     the instance-reduced forms of [zero_iptr]/[null], which only match the
     lemmas up to conversion. *)
  #[local] Hint Extern 1 (I2F_Iptr _ _) => apply I2F_Iptr_zero : core.
  #[local] Hint Extern 1 (I2F_Addr _ _) => apply I2F_Addr_null : core.
  #[local] Hint Resolve Forall2_repeat : core.

  (** The pure content of the [EXP_Zero_initializer] case, by induction on
      [dtyp]. The only value-dependent leaves are [DTYPE_Iptr] (the zero
      intptr on both sides) and [DTYPE_Pointer] ([null] on both sides),
      including under vectors; the aggregate cases go through the
      compatibility of [I2F_EOU] with [bind] and [map_monad]. *)
  Lemma I2F_default_dvalue_of_dtyp : forall τ,
      I2F_EOU I2F_dvalue
        (@default_dvalue_of_dtyp PInf τ)
        (@default_dvalue_of_dtyp PFin τ).
  Proof.
    induction τ; cbn; auto 6.
    - (* DTYPE_I *)
      unfold default_dvalue_of_dtyp_i; auto.
    - (* DTYPE_FP *)
      repeat (break_match_goal; cbn); auto.
    - (* DTYPE_Array *)
      eapply I2F_EOU_bind; [eassumption|].
      intros; do 2 constructor; auto.
    - (* DTYPE_Struct *)
      eapply I2F_EOU_bind; [apply I2F_EOU_map_monad; auto|].
      intros; do 2 constructor; auto.
    - (* DTYPE_Packed_struct *)
      eapply I2F_EOU_bind; [apply I2F_EOU_map_monad; auto|].
      intros; do 2 constructor; auto.
    - (* DTYPE_Vector *)
      repeat (break_match_goal; cbn);
        unfold default_dvalue_of_dtyp_i; auto 6.
  Qed.

  (** * Arithmetic bridge: [IPZ] vs [IP64Bit] under [I2F_Iptr]

      [I2F_Iptr x x'] pins [x = unsigned x'], so after substitution both
      sides of the integer operations compute on [unsigned x'],
      [unsigned y']. The lemmas below characterize the [unsigned] value of
      the finite operations on their success paths; the failure paths are
      absorbed by the [I2F_EOU] cuts (OOM on the right, UB on the left) or
      synchronize as equal booleans. *)

  Section ArithBridge.
    Context {sz : positive}.

    Lemma unsigned_add_bounded : forall (x y : @bit_int sz),
        (unsigned x + unsigned y < @Integers.modulus sz)%Z ->
        unsigned (Integers.add x y) = (unsigned x + unsigned y)%Z.
    Proof.
      intros x y B.
      pose proof (Integers.unsigned_range x); pose proof (Integers.unsigned_range y).
      unfold Integers.add.
      rewrite Integers.unsigned_repr_eq.
      apply Zmod_small; lia.
    Qed.

    Lemma unsigned_sub_bounded : forall (x y : @bit_int sz),
        (unsigned y <= unsigned x)%Z ->
        unsigned (Integers.sub x y) = (unsigned x - unsigned y)%Z.
    Proof.
      intros x y B.
      pose proof (Integers.unsigned_range x); pose proof (Integers.unsigned_range y).
      unfold Integers.sub.
      rewrite Integers.unsigned_repr_eq.
      apply Zmod_small; lia.
    Qed.

    Lemma unsigned_divu : forall (x y : @bit_int sz),
        unsigned y <> 0%Z ->
        unsigned (Integers.divu x y) = (unsigned x / unsigned y)%Z.
    Proof.
      intros x y NZ.
      pose proof (Integers.unsigned_range x); pose proof (Integers.unsigned_range y).
      unfold Integers.divu.
      rewrite Integers.unsigned_repr; auto.
      unfold Integers.max_unsigned.
      assert (0 <= unsigned x / unsigned y <= unsigned x)%Z; [| lia].
      split.
      - apply Z.div_pos; lia.
      - apply Z.div_le_upper_bound; nia.
    Qed.

    Lemma unsigned_modu : forall (x y : @bit_int sz),
        unsigned y <> 0%Z ->
        unsigned (Integers.modu x y) = (unsigned x mod unsigned y)%Z.
    Proof.
      intros x y NZ.
      pose proof (Integers.unsigned_range x); pose proof (Integers.unsigned_range y).
      unfold Integers.modu.
      rewrite Integers.unsigned_repr; auto.
      pose proof (Z.mod_pos_bound (unsigned x) (unsigned y) ltac:(lia)).
      unfold Integers.max_unsigned; lia.
    Qed.

    Lemma unsigned_shru : forall (x y : @bit_int sz),
        unsigned (Integers.shru x y) = Z.shiftr (unsigned x) (unsigned y).
    Proof.
      intros x y.
      pose proof (Integers.unsigned_range x); pose proof (Integers.unsigned_range y).
      unfold Integers.shru.
      rewrite Integers.unsigned_repr; auto.
      rewrite Z.shiftr_div_pow2 by lia.
      assert (0 < 2 ^ unsigned y)%Z by (apply Z.pow_pos_nonneg; lia).
      unfold Integers.max_unsigned.
      assert (0 <= unsigned x / 2 ^ unsigned y <= unsigned x)%Z; [| lia].
      split.
      - apply Z.div_pos; lia.
      - apply Z.div_le_upper_bound; nia.
    Qed.

    (* Bitwise operations: the exact result already fits in [sz] bits. *)

    Lemma unsigned_testbit_above : forall (x : @bit_int sz) i,
        (Z.pos sz <= i)%Z -> Z.testbit (unsigned x) i = false.
    Proof.
      intros x i LE.
      apply Ztestbit_above with (n := Pos.to_nat sz).
      - pose proof (Integers.unsigned_range x) as R.
        unfold Integers.modulus in R.
        now rewrite <- two_power_pos_nat.
      - rewrite positive_nat_Z; lia.
    Qed.

    Lemma max_unsigned_ones : @Integers.max_unsigned sz = Z.ones (Z.pos sz).
    Proof.
      unfold Integers.max_unsigned.
      rewrite Integers.modulus_power, Z.ones_equiv, two_p_equiv.
      unfold Integers.zwordsize; lia.
    Qed.

    Lemma Z_bits_range : forall z,
        (0 <= z)%Z ->
        (forall i, (Z.pos sz <= i)%Z -> Z.testbit z i = false) ->
        (0 <= z <= @Integers.max_unsigned sz)%Z.
    Proof.
      intros z NN ABOVE; split; auto.
      apply Ztestbit_le.
      - pose proof (@Integers.modulus_pos sz).
        unfold Integers.max_unsigned; lia.
      - intros i POS TB.
        rewrite max_unsigned_ones.
        destruct (Z.ltb_spec i (Z.pos sz)) as [LT | GE].
        + apply Z.ones_spec_low; lia.
        + rewrite ABOVE in TB; [discriminate | lia].
    Qed.

    Lemma unsigned_and_land : forall (x y : @bit_int sz),
        unsigned (Integers.and x y) = Z.land (unsigned x) (unsigned y).
    Proof.
      intros x y.
      pose proof (Integers.unsigned_range x); pose proof (Integers.unsigned_range y).
      unfold Integers.and.
      rewrite Integers.unsigned_repr; auto.
      apply Z_bits_range.
      - apply Z.land_nonneg; lia.
      - intros i LE.
        rewrite Z.land_spec, !unsigned_testbit_above; auto.
    Qed.

    Lemma unsigned_or_lor : forall (x y : @bit_int sz),
        unsigned (Integers.or x y) = Z.lor (unsigned x) (unsigned y).
    Proof.
      intros x y.
      pose proof (Integers.unsigned_range x); pose proof (Integers.unsigned_range y).
      unfold Integers.or.
      rewrite Integers.unsigned_repr; auto.
      apply Z_bits_range.
      - apply Z.lor_nonneg; lia.
      - intros i LE.
        rewrite Z.lor_spec, !unsigned_testbit_above; auto.
    Qed.

    Lemma unsigned_xor_lxor : forall (x y : @bit_int sz),
        unsigned (Integers.xor x y) = Z.lxor (unsigned x) (unsigned y).
    Proof.
      intros x y.
      pose proof (Integers.unsigned_range x); pose proof (Integers.unsigned_range y).
      unfold Integers.xor.
      rewrite Integers.unsigned_repr; auto.
      apply Z_bits_range.
      - apply Z.lxor_nonneg; lia.
      - intros i LE.
        rewrite Z.lxor_spec, !unsigned_testbit_above; auto.
    Qed.

    Lemma eq_unsigned_eqb : forall (x y : @bit_int sz),
        Integers.eq x y = (unsigned x =? unsigned y)%Z.
    Proof.
      intros; unfold Integers.eq.
      destruct (zeq _ _) as [e | n]; symmetry.
      - now apply Z.eqb_eq.
      - now apply Z.eqb_neq.
    Qed.

    (* The always-[zero] overflow-flag functions of the intptr instances
       make the poison guards vacuous. *)
    Lemma eq_zero_one_false : @Integers.eq sz Integers.zero Integers.one = false.
    Proof.
      rewrite eq_unsigned_eqb, Integers.unsigned_zero, Integers.unsigned_one.
      reflexivity.
    Qed.

    (* The success path of the finite [madd]. *)
    Lemma unsigned_add_no_carry : forall (x y : @bit_int sz),
        Integers.eq (Integers.add_carry x y Integers.zero) Integers.one = false ->
        unsigned (Integers.add x y) = (unsigned x + unsigned y)%Z.
    Proof.
      intros x y NC.
      unfold Integers.add_carry in NC.
      rewrite Integers.unsigned_zero, Z.add_0_r in NC.
      revert NC; destruct (zlt _ _) as [LT | GE]; intros NC.
      - apply unsigned_add_bounded; auto.
      - now rewrite Integers.eq_true in NC.
    Qed.

    (* Comparison bridges: the finite unsigned comparisons coincide with
       [mcmpu_Z] on the [unsigned] values. *)
    Lemma ltu_unsigned_ltb : forall (x y : @bit_int sz),
        Integers.ltu x y = (unsigned x <? unsigned y)%Z.
    Proof.
      intros; unfold Integers.ltu.
      destruct (zlt _ _) as [l | g]; symmetry.
      - now apply Z.ltb_lt.
      - apply Z.ltb_ge; lia.
    Qed.

    Lemma cmpu_unsigned : forall c (x y : @bit_int sz),
        Integers.cmpu c x y = mcmpu_Z c (unsigned x) (unsigned y).
    Proof.
      intros []; intros; cbv [Integers.cmpu mcmpu_Z];
        rewrite ?eq_unsigned_eqb, ?ltu_unsigned_ltb; auto.
      - now rewrite Z.leb_antisym.
      - now rewrite Z.gtb_ltb.
      - now rewrite Z.geb_leb, Z.leb_antisym.
    Qed.

  End ArithBridge.

  Lemma Z_gtb_irrefl : forall z : Z, (z >? z)%Z = false.
  Proof.
    intros; rewrite Z.gtb_ltb; apply Z.ltb_irrefl.
  Qed.

  (* The infinite side's same-sign test is always true on unsigned values;
     the finite side's is constantly true. *)
  Lemma msamesign_Z_nonneg : forall x y : Z,
      (0 <= x)%Z -> (0 <= y)%Z -> msamesign_Z x y = true.
  Proof.
    intros x y HX HY; unfold msamesign_Z.
    apply Z.geb_le in HX; apply Z.geb_le in HY.
    now rewrite HX, HY.
  Qed.

  (* Keep the overflow bounds abstract in goals rather than computed to
     20-digit literals, and keep [unsigned (repr z)] from reducing to
     [Z_mod_modulus z], so that explicit [destruct ... eqn:] and the
     [ArithBridge] lemmas apply syntactically. *)
  #[local] Arguments Integers.max_unsigned : simpl never.
  #[local] Arguments Integers.repr : simpl never.
  #[local] Arguments msamesign_Z : simpl never.

  (** Layer 2: on [bit_int sz] arguments both sides run the very same
      computation; only the [dvalue] wrapper differs. *)
  Lemma I2F_eval_int_op_bit_int : forall (sz : positive) iop (x y : @bit_int sz),
      I2F_EOU I2F_dvalue
        (@eval_int_op PInf _ _ _ iop x y)
        (@eval_int_op PFin _ _ _ iop x y).
  Proof.
    intros; destruct iop; cbn;
      repeat (break_match_goal; cbn); auto.
  Qed.

  (** Layer 1: [eval_int_op] at the intptr instantiations, where the two
      sides genuinely differ. The instances are pinned explicitly: at the
      concrete parameters, [iptr IP64Bit] is definitionally [bit_int 64]
      and inference would otherwise pick [ToDvalue_Int] rather than the
      [ToDvalue_iptr] used (at abstract [Params]) by [eval_iop_integer_h]. *)
  Lemma I2F_eval_int_op_iptr : forall iop (x y : @iptr IPZ) (x' y' : @iptr IP64Bit),
      I2F_Iptr x x' -> I2F_Iptr y y' ->
      I2F_EOU I2F_dvalue
        (@eval_int_op PInf (@iptr IPZ) (@VMemInt_iptr IPZ) (@ToDvalue_iptr PInf) iop x y)
        (@eval_int_op PFin (@iptr IP64Bit) (@VMemInt_iptr IP64Bit) (@ToDvalue_iptr PFin) iop x' y').
  Proof.
    intros * EQ1 EQ2; red in EQ1, EQ2; subst.
    destruct iop; cbn.
    - (* Add: the finite side OOMs on carry, else values agree *)
      destruct nuw, nsw; cbn; rewrite ?eq_zero_one_false; cbn;
        (destruct (Integers.eq (Integers.add_carry x' y' Integers.zero) Integers.one) eqn:NC;
         cbn; auto;
         do 2 constructor; red; rewrite unsigned_add_no_carry; auto).
    - (* Sub: the finite side OOMs on underflow *)
      destruct nuw, nsw; cbn; rewrite ?eq_zero_one_false; cbn;
        (destruct ((unsigned y' >? unsigned x')%Z) eqn:B; cbn; auto;
         rewrite Z.gtb_ltb, Z.ltb_ge in B;
         do 2 constructor; red; rewrite unsigned_sub_bounded; auto).
    - (* Mul: the finite side OOMs on overflow; the left side carries a
         vacuous [z >? z] guard. *)
      rewrite Z_gtb_irrefl; cbn.
      destruct ((unsigned x' * unsigned y' >? @Integers.max_unsigned 64)%Z) eqn:B; cbn; auto.
      rewrite Z.gtb_ltb, Z.ltb_ge in B.
      assert (RANGE : (0 <= unsigned x' * unsigned y' <= @Integers.max_unsigned 64)%Z).
      { pose proof (Integers.unsigned_range x'); pose proof (Integers.unsigned_range y'); nia. }
      rewrite Integers.unsigned_repr; auto.
      rewrite Z_gtb_irrefl; cbn.
      do 2 constructor; red; rewrite Integers.unsigned_repr; auto.
    - (* Shl: same shape as Mul *)
      rewrite Z_gtb_irrefl; cbn.
      destruct ((Z.shiftl (unsigned x') (unsigned y') >? @Integers.max_unsigned 64)%Z) eqn:B;
        cbn; auto.
      rewrite Z.gtb_ltb, Z.ltb_ge in B.
      assert (RANGE : (0 <= Z.shiftl (unsigned x') (unsigned y') <= @Integers.max_unsigned 64)%Z).
      { pose proof (Integers.unsigned_range x'); split; auto.
        apply Z.shiftl_nonneg; lia. }
      rewrite Integers.unsigned_repr; auto.
      rewrite Z_gtb_irrefl; cbn.
      do 2 constructor; red; rewrite Integers.unsigned_repr; auto.
    - (* UDiv: division by zero raises UB on both sides (left cut) *)
      destruct ((unsigned y' =? 0)%Z) eqn:Z0; cbn; auto.
      apply Z.eqb_neq in Z0.
      destruct exact; cbn.
      + destruct ((unsigned x' mod unsigned y' =? 0)%Z) eqn:EX; cbn; auto.
        do 2 constructor; red; rewrite unsigned_divu; auto.
      + do 2 constructor; red; rewrite unsigned_divu; auto.
    - (* SDiv: unsupported at iptr type on both sides *)
      now repeat constructor.
    - (* LShr *)
      rewrite Bool.andb_false_r; cbn.
      destruct exact; cbn.
      + destruct ((unsigned x' mod 2 ^ unsigned y' =? 0)%Z) eqn:EX; cbn; auto.
        do 2 constructor; red; now rewrite unsigned_shru.
      + do 2 constructor; red; now rewrite unsigned_shru.
    - (* AShr: unsupported at iptr type on both sides *)
      now repeat constructor.
    - (* URem *)
      destruct ((unsigned y' =? 0)%Z) eqn:Z0; cbn; auto.
      apply Z.eqb_neq in Z0.
      do 2 constructor; red; rewrite unsigned_modu; auto.
    - (* SRem: unsupported at iptr type on both sides *)
      now repeat constructor.
    - (* And *)
      do 2 constructor; red; now rewrite unsigned_and_land.
    - (* Or *)
      destruct disjoint; cbn.
      + rewrite eq_unsigned_eqb, unsigned_or_lor, unsigned_xor_lxor.
        destruct ((Z.lor (unsigned x') (unsigned y') =? Z.lxor (unsigned x') (unsigned y'))%Z) eqn:D;
          cbn.
        * do 2 constructor; red; now rewrite unsigned_or_lor.
        * now repeat constructor.
      + do 2 constructor; red; now rewrite unsigned_or_lor.
    - (* Xor *)
      do 2 constructor; red; now rewrite unsigned_xor_lxor.
  Qed.

  (** Compatibility of [I2F_EOU] with [vec_loop] over pairwise-related
      lists of pairs. *)
  Lemma I2F_EOU_vec_loop {A1 A2} (R : A1 -> A2 -> Prop)
        (f1 : A1 -> A1 -> EOU A1) (f2 : A2 -> A2 -> EOU A2) :
    forall l1 l2,
      Forall2 (prod_rel R R) l1 l2 ->
      (forall a b a' b', R a a' -> R b b' -> I2F_EOU R (f1 a b) (f2 a' b')) ->
      I2F_EOU (Forall2 R) (vec_loop f1 l1) (vec_loop f2 l2).
  Proof.
    intros l1 l2 F HF; induction F; cbn.
    - do 2 constructor.
    - destruct x as [a b], y as [a' b'], H as [Ha Hb]; cbn in *.
      eapply I2F_EOU_bind; [apply IHF|].
      intros acc1 acc2 HACC.
      eapply I2F_EOU_bind; [now apply HF|].
      intros v1 v2 HV.
      do 2 constructor; auto.
  Qed.

  (* Pairwise-related lists combine to [prod_rel]-related pair lists. *)
  Lemma Forall2_combine {A1 A2 B1 B2} (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop) :
    forall l1 l2 k1 k2,
      Forall2 RA l1 l2 -> Forall2 RB k1 k2 ->
      Forall2 (prod_rel RA RB) (combine l1 k1) (combine l2 k2).
  Proof.
    intros l1 l2 k1 k2 F; revert k1 k2; induction F; cbn; intros k1 k2 FK; auto.
    destruct FK; cbn; auto.
  Qed.

  Lemma Forall2_length_N {A B} (R : A -> B -> Prop) :
    forall l1 l2, Forall2 R l1 l2 -> N.length l1 = N.length l2.
  Proof.
    intros l1 l2 F; induction F; cbn; auto.
    now rewrite IHF.
  Qed.

  (** Layer 3: the scalar dispatcher. Inverting the two value relations
      keeps the case analysis synchronized (11 shape pairs rather than
      11²); the remaining cases dispatch to layers 1 and 2, or share
      their guards. *)
  Lemma I2F_eval_iop_integer_h : forall iop v1 v2 v1' v2',
      I2F_dvalue v1 v1' ->
      I2F_dvalue v2 v2' ->
      I2F_EOU I2F_dvalue
        (@eval_iop_integer_h PInf iop v1 v2)
        (@eval_iop_integer_h PFin iop v1' v2').
  Proof.
    intros * H1 H2.
    inversion H1; subst; inversion H2; subst; cbn;
      try (now repeat constructor).
    (* Iptr × Iptr: layer 1 *)
    all: try (now (apply I2F_eval_int_op_iptr; auto)).
    (* I sz × I sz0: the bitwidth test is shared, then layer 2 *)
    all: try (break_match_goal;
              [ match goal with e : _ = _ |- _ => destruct e end; cbn;
                apply I2F_eval_int_op_bit_int
              | now repeat constructor ]).
    (* Poison rows: the guards are shared, up to [I2F_Iptr] on the payload *)
    all: destruct iop; cbn; auto;
      try (match goal with H : I2F_Iptr _ _ |- _ => red in H; subst end);
      try (break_match_goal; cbn; now auto).
  Qed.

  (** Layer 4: [eval_iop] adds the pointwise vector case on top of the
      scalar dispatcher. *)
  Lemma I2F_eval_iop a1 a2 b1 b2 iop :
    I2F_dvalue a1 b1 ->
    I2F_dvalue a2 b2 ->
    I2F_EOU I2F_dvalue (eval_iop iop a1 a2) (eval_iop iop b1 b2).
  Proof.
    intros H1 H2.
    inversion H1; subst; inversion H2; subst;
      try (now (apply I2F_eval_iop_integer_h; auto)).
    (* Vector × Vector *)
    cbn.
    repeat match goal with
           | F : Forall2 I2F_dvalue _ _ |- _ =>
               rewrite (Forall2_length_N F); revert F
           end.
    intros F1 F2.
    break_match_goal; cbn; auto.
    eapply I2F_EOU_bind.
    - apply I2F_EOU_vec_loop; [eapply Forall2_combine; eauto|].
      intros; apply I2F_eval_iop_integer_h; auto.
    - intros; do 2 constructor; auto.
  Qed.
 
  (** [I2F_EOU_map_monad] generalized to two [Forall2]-related lists. *)
  Lemma I2F_EOU_map_monad2 {A1 A2 B1 B2} (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop)
        (f1 : A1 -> EOU B1) (f2 : A2 -> EOU B2) :
    forall l1 l2,
      Forall2 RA l1 l2 ->
      (forall a1 a2, RA a1 a2 -> I2F_EOU RB (f1 a1) (f2 a2)) ->
      I2F_EOU (Forall2 RB) (map_monad f1 l1) (map_monad f2 l2).
  Proof.
    intros l1 l2 F HF; induction F; cbn.
    - do 2 constructor.
    - eapply I2F_EOU_bind; [now apply HF|].
      intros b1 b2 HB.
      eapply I2F_EOU_bind; [apply IHF|].
      intros bs1 bs2 HBS.
      do 2 constructor; auto.
  Qed.

  (* The float operations are parameter-independent: related inputs have
     synchronized shapes and identical payloads, so every leaf is
     diagonal. *)
  Lemma I2F_eval_fneg_h : forall v v',
      I2F_dvalue v v' ->
      I2F_EOU I2F_dvalue (@eval_fneg_h PInf v) (@eval_fneg_h PFin v').
  Proof.
    intros * H; inversion H; subst; cbn; now repeat constructor.
  Qed.

  Lemma I2F_eval_fneg a b :
    I2F_dvalue a b ->
    I2F_EOU I2F_dvalue (eval_fneg a) (eval_fneg b).
  Proof.
    intros H.
    inversion H; subst;
      try (now (apply I2F_eval_fneg_h; auto)).
    (* Vector *)
    cbn.
    eapply I2F_EOU_bind.
    - eapply I2F_EOU_map_monad2; eauto.
      intros; now apply I2F_eval_fneg_h.
    - intros; do 2 constructor; auto.
  Qed.

  (** Same-instance [eval_int_icmp]: no [ToDvalue] is involved and all
      outputs are parameter-independent constructors, so one lemma covers
      both the [bit_int sz] case and the [Z] case used for address
      comparisons. *)
  Lemma I2F_eval_int_icmp_refl : forall Int (VMI : VMemInt Int) samesign icmp (x y : Int),
      I2F_EOU I2F_dvalue
        (@eval_int_icmp PInf Int VMI samesign icmp x y)
        (@eval_int_icmp PFin Int VMI samesign icmp x y).
  Proof.
    intros; destruct icmp; cbn;
      repeat (break_match_goal; cbn); auto.
  Qed.

  (** [eval_int_icmp] at the intptr instantiations. The signed comparisons
      are unsupported at iptr type on both sides; the unsigned ones agree
      through the comparison bridges; the same-sign poison guard is vacuous
      on both sides (unsigned values are nonnegative on the left, and the
      finite [msamesign] is constantly [true]). *)
  Lemma I2F_eval_int_icmp_iptr : forall samesign icmp (x y : @iptr IPZ) (x' y' : @iptr IP64Bit),
      I2F_Iptr x x' -> I2F_Iptr y y' ->
      I2F_EOU I2F_dvalue
        (@eval_int_icmp PInf _ (@VMemInt_iptr IPZ) samesign icmp x y)
        (@eval_int_icmp PFin _ (@VMemInt_iptr IP64Bit) samesign icmp x' y').
  Proof.
    intros * EQ1 EQ2; red in EQ1, EQ2; subst.
    pose proof (Integers.unsigned_range x'); pose proof (Integers.unsigned_range y').
    destruct icmp; cbn; try (now repeat constructor);
      rewrite ?eq_unsigned_eqb, ?ltu_unsigned_ltb, ?Z.gtb_ltb, ?Z.geb_leb, ?Z.leb_antisym;
      rewrite msamesign_Z_nonneg by lia;
      cbn; rewrite ?Bool.andb_false_r; cbn;
      break_match_goal; now repeat constructor.
  Qed.

  (** The scalar comparison dispatcher. *)
  Lemma I2F_eval_icmp_h : forall samesign icmp v1 v2 v1' v2',
      I2F_dvalue v1 v1' ->
      I2F_dvalue v2 v2' ->
      I2F_EOU I2F_dvalue
        (@eval_icmp_h PInf samesign icmp v1 v2)
        (@eval_icmp_h PFin samesign icmp v1' v2').
  Proof.
    intros * H1 H2.
    inversion H1; subst; inversion H2; subst; cbn;
      try (now repeat constructor).
    (* Iptr × Iptr *)
    all: try (now (apply I2F_eval_int_icmp_iptr; auto)).
    (* Remaining synchronized rows: [I × I] (after eliminating the
       bitwidth transport) and [Addr × Addr] (where [ptr_to_int] yields
       equal integers) run the same computation on both sides, up to the
       [dvalue] wrapper; close by symbolic execution of the shared tests. *)
    all: repeat match goal with
           | HA : I2F_Addr ?a ?b |- _ =>
               destruct a, b; destruct HA as [HI ->]; red in HI; subst
           end;
      try (match goal with
           | |- context [Pos.eq_dec ?a ?b] =>
               destruct (Pos.eq_dec a b) as [e | n]; [destruct e|]
           end);
      cbv [eq_rec_r eq_rec eq_rect Logic.eq_sym];
      destruct icmp; cbn;
      repeat (break_match_goal; cbn); now repeat constructor.
  Qed.

  Lemma I2F_eval_icmp a1 a2 b1 b2 samesign cmp :
    I2F_dvalue a1 b1 ->
    I2F_dvalue a2 b2 ->
    I2F_EOU I2F_dvalue (eval_icmp samesign cmp a1 a2)
      (eval_icmp samesign cmp b1 b2).
  Proof.
    intros H1 H2.
    inversion H1; subst; inversion H2; subst;
      try (now (apply I2F_eval_icmp_h; auto)).
    (* Vector × Vector *)
    cbn.
    repeat match goal with
           | F : Forall2 I2F_dvalue _ _ |- _ =>
               rewrite (Forall2_length_N F); revert F
           end.
    intros F1 F2.
    break_match_goal; cbn; auto.
    eapply I2F_EOU_bind.
    - apply I2F_EOU_vec_loop; [eapply Forall2_combine; eauto|].
      intros; apply I2F_eval_icmp_h; auto.
    - intros; do 2 constructor; auto.
  Qed.
 
  Lemma I2F_eval_fop_h : forall c v1 v2 v1' v2',
      I2F_dvalue v1 v1' ->
      I2F_dvalue v2 v2' ->
      I2F_EOU I2F_dvalue
        (@eval_fop_h PInf c v1 v2)
        (@eval_fop_h PFin c v1' v2').
  Proof.
    intros * H1 H2.
    inversion H1; subst; inversion H2; subst; cbn;
      try (now repeat constructor);
      destruct c; cbn;
      try (break_match_goal; cbn); now repeat constructor.
  Qed.

  Lemma I2F_eval_fop a1 a2 b1 b2 fop :
    I2F_dvalue a1 b1 ->
    I2F_dvalue a2 b2 ->
    I2F_EOU I2F_dvalue (eval_fop fop a1 a2) (eval_fop fop b1 b2).
  Proof.
    intros H1 H2.
    inversion H1; subst; inversion H2; subst;
      try (now (apply I2F_eval_fop_h; auto)).
    (* Vector × Vector *)
    cbn.
    repeat match goal with
           | F : Forall2 I2F_dvalue _ _ |- _ =>
               rewrite (Forall2_length_N F); revert F
           end.
    intros F1 F2.
    break_match_goal; cbn; auto.
    eapply I2F_EOU_bind.
    - apply I2F_EOU_vec_loop; [eapply Forall2_combine; eauto|].
      intros; apply I2F_eval_fop_h; auto.
    - intros; do 2 constructor; auto.
  Qed.

  Lemma I2F_eval_fcmp_h : forall c v1 v2 v1' v2',
      I2F_dvalue v1 v1' ->
      I2F_dvalue v2 v2' ->
      I2F_EOU I2F_dvalue
        (@eval_fcmp_h PInf c v1 v2)
        (@eval_fcmp_h PFin c v1' v2').
  Proof.
    intros * H1 H2.
    inversion H1; subst; inversion H2; subst; cbn;
      try (now repeat constructor);
      unfold float_cmp, double_cmp; destruct c; cbn;
      repeat (break_match_goal; cbn); now repeat constructor.
  Qed.

  Lemma I2F_eval_fcmp a1 a2 b1 b2 cmp :
    I2F_dvalue a1 b1 ->
    I2F_dvalue a2 b2 ->
    I2F_EOU I2F_dvalue (eval_fcmp cmp a1 a2)
      (eval_fcmp cmp b1 b2).
  Proof.
    intros H1 H2.
    inversion H1; subst; inversion H2; subst;
      try (now (apply I2F_eval_fcmp_h; auto)).
    (* Vector × Vector *)
    cbn.
    repeat match goal with
           | F : Forall2 I2F_dvalue _ _ |- _ =>
               rewrite (Forall2_length_N F); revert F
           end.
    intros F1 F2.
    break_match_goal; cbn; auto.
    eapply I2F_EOU_bind.
    - apply I2F_EOU_vec_loop; [eapply Forall2_combine; eauto|].
      intros; apply I2F_eval_fcmp_h; auto.
    - intros; do 2 constructor; auto.
  Qed.

  Lemma I2F_convert conv t_from t_to a b :
    I2F_dvalue a b ->
    I2F_EOU I2F_dvalue (convert conv t_from a t_to) (convert conv t_from b t_to).
  Admitted. 
 
  Lemma I2F_eval_gep t a1 a2 b1 b2 :
    I2F_dvalue a1 b1 ->
    Forall2 I2F_dvalue a2 b2 ->
    I2F_EOU I2F_dvalue (eval_gep t a1 a2) (eval_gep t b1 b2).
  Proof.
  Admitted.

  Lemma I2F_extract_element a1 a2 b1 b2 :
    I2F_dvalue a1 b1 ->
    I2F_dvalue a2 b2 ->
    I2F_EOU I2F_dvalue (extract_element a1 a2) (extract_element b1 b2).
  Proof.
  Admitted.
  
  Lemma I2F_insert_element a1 a2 a3 b1 b2 b3 :
    I2F_dvalue a1 b1 ->
    I2F_dvalue a2 b2 ->
    I2F_dvalue a3 b3 ->
    I2F_EOU I2F_dvalue (insert_element a1 a2 a3) (insert_element b1 b2 b3).
  Proof.
  Admitted.

  Lemma I2F_extract_value a b idxs :
    I2F_dvalue a b ->
    I2F_EOU I2F_dvalue (extract_value a (map denote_int_syntax idxs))
      (extract_value b (map denote_int_syntax idxs)).
  Proof.
  Admitted.
  
  Lemma I2F_insert_value idxs :
    forall a1 a2 b1 b2,
    I2F_dvalue a1 b1 ->
    I2F_dvalue a2 b2 ->
    I2F_EOU I2F_dvalue (insert_value a1 a2 (map denote_int_syntax idxs))
      (insert_value b1 b2 (map denote_int_syntax idxs)).
  Proof.
    induction idxs as [| i idx IH]; [cbn; intros * R1 R2; eauto | intros * R1 R2].
    inv R1; try now (cbn; eauto).
    - cbn[map insert_value].
      destruct τ; eauto.
      eapply I2F_EOU_bind; eauto.
  Admitted.
   
  Lemma I2F_eval_select a1 a2 a3 b1 b2 b3 :
    I2F_dvalue a1 b1 ->
    I2F_dvalue a2 b2 ->
    I2F_dvalue a3 b3 ->
    I2F_EOU I2F_dvalue (eval_select a1 a2 a3) (eval_select b1 b2 b3).
  Proof.
    intros R1 R2 R3.
    inv R1; cbn; eauto.
    - repeat (break_match_goal; eauto).
    - inv R2; cbn; eauto.
      inv R3; cbn; eauto.
  Admitted.

  
  Ltac rstep :=
    first [apply ruttc_trigger |
            apply ruttc_trigger_cast |
            apply ruttc_ret 
      ].
  
  Lemma I2F_freeze a b :
    I2F_dvalue a b ->
    I2F_refine (freeze a) (freeze b).
  Proof with try now (rstep; try (easy); eauto).
    intros HDV.
    induction HDV; cbn...
    
  Admitted.

  Lemma I2F_denote_expr :
    forall (e : exp dtyp) τ, I2F_refine (@denote_exp PInf τ e) (@denote_exp PFin τ e).
  Proof with try now (rstep; try (easy); eauto).
    induction e.
    - intros; cbn.
      destruct id; cbn...
    - intros [d|]; cbn...
      apply I2F_refine_lift, I2F_denote_int_syntax_as_int.
    - intros [d|]; cbn...
      apply I2F_refine_lift, I2F_denote_float_syntax_as_float.
    - destruct b; intros ?; cbn...
    - intros; cbn... 
    - (* initializer *)
      intros [d|]; cbn...
      apply I2F_refine_lift, I2F_default_dvalue_of_dtyp.
    - cbn.
      intros. 
      eapply ruttc_bind.
      + apply ruttc_map_monad.
        intros [d e] HIN; now apply (H (d,e)).
      + intros * HF...
    - cbn; intros []...
    - cbn; intros []...
    - cbn.
      intros. 
      eapply ruttc_bind.
      + apply ruttc_map_monad.
        intros [d e] HIN; now apply (H (d,e)).
      + intros * HF...
    - (* EXP_Packed_struct: the [dtyp] guard is a pure, parameter-free
         computation, related to itself by reflexivity of [I2F_EOU] ---
         no case analysis on the type. *)
      cbn; intros.
      eapply ruttc_bind.
      + apply I2F_refine_lift, I2F_EOU_refl.
      + intros [] [] _.
        eapply ruttc_bind.
        * apply ruttc_map_monad.
          intros [d e] HIN; now apply (H (d,e)).
        * intros * HF...
    - cbn; intros.
      eapply ruttc_bind.
      + apply ruttc_map_monad.
        intros [d e] HIN; now apply (H (d,e)).
      + intros * HF...
    - cbn; intros.
      eapply ruttc_bind.
      + apply ruttc_map_monad.
        intros [d e] HIN; now apply (H (d,e)).
      + intros * HF...
    - cbn; intros.
      eapply ruttc_bind; [apply IHe1 | intros].
      eapply ruttc_bind; [apply IHe2 | intros].
      apply I2F_refine_lift.
      now apply I2F_eval_iop.
    - destruct v; cbn; intros.
      eapply ruttc_bind; [apply IHe | intros].
      apply I2F_refine_lift.
      now apply I2F_eval_fneg.
    - cbn; intros.
      eapply ruttc_bind; [apply IHe1 | intros].
      eapply ruttc_bind; [apply IHe2 | intros].
      apply I2F_refine_lift.
      now apply I2F_eval_icmp.
    - cbn; intros.
      eapply ruttc_bind; [apply IHe1 | intros].
      eapply ruttc_bind; [apply IHe2 | intros].
      apply I2F_refine_lift.
      now apply I2F_eval_fop.
    - cbn; intros.
      eapply ruttc_bind; [apply IHe1 | intros].
      eapply ruttc_bind; [apply IHe2 | intros].
      apply I2F_refine_lift.
      now apply I2F_eval_fcmp.
    - cbn; intros _.
      eapply ruttc_bind; [apply IHe | intros].
      apply I2F_refine_lift.
      now apply I2F_convert.
    - destruct ptrval; cbn; intros _.
      eapply ruttc_bind; [apply IHe | intros].
      eapply ruttc_bind.
      + apply ruttc_map_monad.
        intros [x y] HIN; now apply (H (x,y)).
      + intros; apply I2F_refine_lift.
        now apply I2F_eval_gep.
    - destruct vec, idx; cbn; intros _.
      eapply ruttc_bind; [apply IHe | intros].
      eapply ruttc_bind; [apply IHe0 | intros].
      apply I2F_refine_lift.
      now apply I2F_extract_element.
    - destruct vec, elt, idx; cbn; intros _.
      eapply ruttc_bind; [apply IHe | intros].
      eapply ruttc_bind; [apply IHe0 | intros].
      eapply ruttc_bind; [apply IHe1 | intros].
      apply I2F_refine_lift.
      now apply I2F_insert_element.
    - destruct vec1,vec2,idxmask; cbn; intros _.
      eapply ruttc_bind; [apply IHe | intros].
      eapply ruttc_bind; [apply IHe0 | intros].
      eapply ruttc_bind; [apply IHe1 | intros]...
    - destruct vec; cbn; intros _.
      eapply ruttc_bind; [apply IHe | intros].
      apply I2F_refine_lift.
      now apply I2F_extract_value.
    - destruct vec, elt; cbn; intros _.
      eapply ruttc_bind; [apply IHe | intros].
      eapply ruttc_bind; [apply IHe0 | intros].
      apply I2F_refine_lift.
      now apply I2F_insert_value.
    - destruct cnd,v1,v2; cbn; intros _.
      eapply ruttc_bind; [apply IHe | intros].
      eapply ruttc_bind; [apply IHe0 | intros].
      eapply ruttc_bind; [apply IHe1 | intros].
      apply I2F_refine_lift.
      now apply I2F_eval_select.
    - destruct v; cbn; intros _.
      eapply ruttc_bind; [apply IHe | intros].
      now apply I2F_freeze.
    - cbn; intros _...
    - cbn; intros _; destruct m...
      destruct tv; cbn.
      admit.
    - (* should patch denotation to avoid case analysis at this level *)
      admit.
      
  Admitted.      

End Refinement.
