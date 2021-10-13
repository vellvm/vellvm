(* begin hide *)
Require Import String.

From ITree Require Import
     ITree
     Basics
     Basics.HeterogeneousRelations
     Eq.Eq.

From Vellvm Require Import
     Utilities
     Syntax
     Semantics
     Semantics.MemoryAddress
     Semantics.GepM
     Semantics.Memory.Sizeof
     Semantics.Memory.MemBytes
     Semantics.Memory.Sizeof.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.EitherMonad
     Structures.Functor.


From Coq Require Import Relations RelationClasses.
(* end hide *)

Module Make (A:MemoryAddress.ADDRESS)(SIZE:Sizeof)(LLVMEvents: LLVM_INTERACTIONS(A)(SIZE))(PTOI:PTOI(A))(PROVENANCE:PROVENANCE(A))(ITOP:ITOP(A)(PROVENANCE))(GEP:GEPM(A)(SIZE)(LLVMEvents))(BYTE_IMPL : ByteImpl(A)(SIZE)(LLVMEvents)).

  Module Conc := Serialization.Make A SIZE LLVMEvents PTOI PROVENANCE ITOP GEP BYTE_IMPL.

Import LLVMEvents.
Import DV.
Import Conc.

(* Refinement relation for uvalues *)
(* Definition 5.6 UValue refinement *)
Variant refine_uvalue: uvalue -> uvalue -> Prop :=
| UndefPoison: forall dt uv uv1, concretize uv1 (DVALUE_Poison dt) -> uvalue_has_dtyp uv dt -> refine_uvalue uv1 uv
| RefineConcrete: forall uv1 uv2, (forall (dv:dvalue), concretize uv2 dv -> concretize uv1 dv) -> refine_uvalue uv1 uv2
.
#[export] Hint Constructors refine_uvalue : core.

Definition uvalue_eq (uv1 uv2 : uvalue) : Prop
  := refine_uvalue uv1 uv2 /\ refine_uvalue uv2 uv1.

Instance refine_uvalue_Reflexive : Reflexive refine_uvalue.
Proof.
  repeat intro.
  destruct x; (apply RefineConcrete; solve [auto]).
Qed.

Instance uvalue_eq_Reflexive : Reflexive uvalue_eq.
Proof.
  repeat intro.
  split; reflexivity.
Qed.

(* TODO: Move these *)
  Lemma Forall_HIn_cons_inv :
    forall {X} (x : X) (xs : list X) (f : X -> Prop),
      f x ->
      Forall_HIn xs (fun x _ => f x) ->
      Forall_HIn (x::xs) (fun x _ => f x).
  Proof.
    intros X x xs f Hfx Hfxs.
    constructor; auto.
  Qed.
  
  Lemma NO_VOID_Struct_cons_inv :
    forall dt dts,
      NO_VOID dt ->
      NO_VOID (DTYPE_Struct dts) ->
      NO_VOID (DTYPE_Struct (dt :: dts)).
  Proof.
    intros dt dts NVdt NVdts.
    rewrite NO_VOID_equation in NVdts.
    rewrite NO_VOID_equation.

    apply Forall_HIn_cons_inv; auto.
  Qed.

  Lemma NO_VOID_Packed_struct_cons_inv :
    forall dt dts,
      NO_VOID dt ->
      NO_VOID (DTYPE_Packed_struct dts) ->
      NO_VOID (DTYPE_Packed_struct (dt :: dts)).
  Proof.
    intros dt dts NVdt NVdts.
    rewrite NO_VOID_equation in NVdts.
    rewrite NO_VOID_equation.

    apply Forall_HIn_cons_inv; auto.
  Qed.

(* TODO: Move this *)
Hint Rewrite NO_VOID_equation : NO_VOID.
Hint Resolve NO_VOID_Struct_cons_inv : NO_VOID.
Hint Resolve NO_VOID_Packed_struct_cons_inv : NO_VOID.
Ltac solve_no_void :=
  solve
    [ auto with NO_VOID
    | match goal with
      | H: NO_VOID _ /\ _ |- _
        => destruct H; solve_no_void
      end
    | rewrite NO_VOID_equation; solve_no_void
    ].
  
Lemma concretize_dtyp :
  forall uv dv dt,
    uvalue_has_dtyp uv dt ->
    concretize uv dv ->
    dvalue_has_dtyp dv dt.
Proof.
  intros uv dv dt DTYP CONC.
  generalize dependent dv.
  induction DTYP; intros dv CONC.
  1-8: inversion CONC; subst; solve [auto | constructor; try solve_no_void].

  (* Poison structs *)
  { inversion CONC.
    constructor.
    rewrite NO_VOID_equation.
    cbn. auto.
  }
  { inversion CONC.
    constructor.

    subst.

    (* Recover NO_VOID information *)
    specialize (IHDTYP (DVALUE_Poison dt)).
    forward IHDTYP.
    { do 2 red.
      cbn.
      reflexivity.
    }

    specialize (IHDTYP0 (DVALUE_Poison (DTYPE_Struct dts))).
    forward IHDTYP0.
    { do 2 red.
      cbn.
      reflexivity.
    }
    
    inversion IHDTYP; subst.
    inversion IHDTYP0; subst.

    solve_no_void.
  }

  (* Poison packed structs *)
  { inversion CONC.
    constructor.
    rewrite NO_VOID_equation.
    cbn. auto.
  }
  { inversion CONC.
    constructor.

    subst.

    (* Recover NO_VOID information *)
    specialize (IHDTYP (DVALUE_Poison dt)).
    forward IHDTYP.
    { do 2 red.
      cbn.
      reflexivity.
    }

    specialize (IHDTYP0 (DVALUE_Poison (DTYPE_Packed_struct dts))).
    forward IHDTYP0.
    { do 2 red.
      cbn.
      reflexivity.
    }
    
    inversion IHDTYP; subst.
    inversion IHDTYP0; subst.

    solve_no_void.
  }

  1-11: inversion CONC; subst; solve [auto | constructor; try solve_no_void].

  (* Structs *)
  { (* Nil structs *)
    do 2 red in CONC.
    cbn in CONC.
    unfold bind_RefineProp in CONC.
    destruct CONC as (ma & k' & pama & eqm & REST).
    destruct ma as [[[uba | [erra | a]]]] eqn:Hma; cbn; auto; try contradiction.
    subst.

    specialize (REST nil).
    forward REST; [reflexivity|].

    destruct (k' nil) as [[[ubk' | [errk' | k'nil]]]] eqn:Hk'nil; cbn; auto; try contradiction.
    subst.

    cbn in eqm.
    rewrite Hk'nil in eqm.
    cbn in eqm.
    subst.

    constructor.
  }
  { (* Non-nil structs *)
    do 2 red in CONC.
    rewrite concretize_uvalueM_equation in CONC.
    cbn in CONC.

    (* Urgggghhh... Missing proper instance, I think *)
    Fail rewrite RefineProp_bind_bind in CONC.
    admit.
  }

  (* Packed Structs *)
  admit.
  admit.

  (* Arrays *)
  { admit.

  }

  (* Vectors *)
  { admit.

  }

  (* Binops *)
  {
    Set Nested Proofs Allowed.

  }
  1: inversion CONC; subst; solve [auto | constructor; try solve_no_void].
  
Admitted.

Lemma refine_uvalue_dtyp :
  forall uv1 uv2 dt,
    uvalue_has_dtyp uv1 dt ->
    refine_uvalue uv1 uv2 ->
    uvalue_has_dtyp uv2 dt.
Proof.
  intros uv1 uv2 dt DTYP REF.
  induction DTYP.
  - inversion REF; subst.
Admitted.

Instance refine_uvalue_Transitive : Transitive refine_uvalue.
Proof.
  repeat intro.
  inversion H; subst.
  - (* x concretizes to poison *)
    eapply UndefPoison; eauto.
    eapply refine_uvalue_dtyp; eauto.
  - (* x may not be poison  *)
    inversion H0; subst.
    + (* y is poison *)
      pose proof (H1 (DVALUE_Poison dt)) as POISON.
      forward POISON.
      auto.

      (* x refines to poison... *)
      eapply UndefPoison; eauto.
    + constructor.
      auto.
Qed.

Instance uvalue_eq_Transitive : Transitive uvalue_eq.
Proof.
  intros x y z [Rxy Ryx] [Ryz Rzy].
  split; etransitivity; eauto.
Qed.

Instance uvalue_eq_Symmetric : Symmetric uvalue_eq.
Proof.
  intros x y [Rxy Ryx].
  split; auto.
Qed.

Instance uvalue_eq_Equivalence : Equivalence uvalue_eq.
Proof.
  split.
  - apply uvalue_eq_Reflexive.
  - apply uvalue_eq_Symmetric.
  - apply uvalue_eq_Transitive.
Qed.

Infix"×" := prod_rel (at level 90, left associativity).

Definition TT {A} : relation A := fun _ _ => True.

(* Lemma 5.7 - uses this definition of refinement 
   note that refine_uvalue is the basic Uvalue refinement given by Definition 5.6 *)
(* Refinement of uninterpreted mcfg *)
Definition refine_L0: relation (itree L0 uvalue) := eutt refine_uvalue.

(* Refinement of mcfg after globals *)
Definition refine_res1 : relation (global_env * uvalue)
  := TT × refine_uvalue.

Definition refine_L1 : relation (itree L1 (global_env * uvalue))
  := eutt refine_res1.

(* Refinement of mcfg after locals *)
Definition refine_res2 : relation (local_env * lstack * (global_env * uvalue))
  := TT × refine_res1.

Definition refine_L2 : relation (itree L2 (local_env * stack * (global_env * uvalue)))
  := eutt refine_res2.

(* For multiple CFG, after interpreting [LocalE] and [MemoryE] and [IntrinsicE] that are memory intrinsics *)
Definition refine_res3 : relation (memory_stack * (local_env * stack * (global_env * uvalue)))
  := TT × refine_res2.

Definition refine_L3 : relation (itree L3 (memory_stack * (local_env * stack * (global_env * uvalue))))
  := eutt refine_res3.

(* Refinement for after interpreting pick. *)
Definition refine_L4 : relation ((itree L4 (memory_stack * (local_env * stack * (global_env * uvalue)))) -> Prop)
  := fun ts ts' => forall t', ts' t' -> exists t, ts t /\ eutt refine_res3 t t'.

Definition refine_L5 : relation ((itree L5 (memory_stack * (local_env * stack * (global_env * uvalue)))) -> Prop)
  := fun ts ts' => forall t', ts' t' -> exists t, ts t /\ eutt refine_res3 t t'.

End Make.
