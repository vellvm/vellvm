From Coq Require Import
     Relations
     String
     List
     Lia
     ZArith
     Morphisms.

Require Import Coq.Logic.ProofIrrelevance.

From Vellvm Require Import
     Semantics.InterpretationStack
     Semantics.LLVMEvents
     Semantics.Denotation
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof
     Semantics.Lang
     Semantics.InterpretationStack
     Semantics.TopLevel
     Semantics.DynamicValues
     Semantics.LLVMParams
     Semantics.InfiniteToFinite.Conversions.BaseConversions
     Semantics.InfiniteToFinite.Conversions.DvalueConversions
     Syntax.DynamicTypes
     Theory.TopLevelRefinements
     Theory.ContainsUB
     Utils.Error
     Utils.Monads
     Utils.MapMonadExtra
     Utils.PropT
     Utils.InterpProp
     Utils.ListUtil
     Utils.Tactics
     Utils.OOMRutt
     Utils.OOMRuttProps
     Handlers.MemoryModules.FiniteAddresses
     Handlers.MemoryModules.InfiniteAddresses
     Handlers.MemoryModelImplementation.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor.

From ITree Require Import
     ITree
     Basics
     Basics.HeterogeneousRelations
     Eq.Rutt
     Eq.RuttFacts
     Eq.Eqit
     Eq.EqAxiom.

Require Import Coq.Program.Equality.
Require Import Paco.paco.

Import InterpFacts.

Import MonadNotation.
Import ListNotations.

Module EventConvert (LP1 : LLVMParams) (LP2 : LLVMParams) (AC : AddrConvert LP1.ADDR LP2.ADDR) (AC2 : AddrConvert LP2.ADDR LP1.ADDR) (E1 : LLVM_INTERACTIONS LP1.ADDR LP1.IP LP1.SIZEOF) (E2 : LLVM_INTERACTIONS LP2.ADDR LP2.IP LP2.SIZEOF).
  (* TODO: should this be a parameter? *)
  Module DVC := DVConvertMake LP1 LP2 AC E1 E2.
  Module DVCrev := DVConvertMake LP2 LP1 AC2 E2 E1.
  Import DVC.

  Definition L0_convert_helper
    (dvalue_convert : DV1.dvalue -> OOM DV2.dvalue)
    (uvalue_convert : DV1.uvalue -> OOM DV2.uvalue)
    (rev_dvalue_convert : DV2.dvalue -> OOM DV1.dvalue)
    (rev_uvalue_convert : DV2.uvalue -> OOM DV1.uvalue)
    : Handler E1.L0 E2.L0.
    refine (fun A e => _).

    refine (match e with
            | inl1 (E1.ExternalCall dt f args) =>
                _
            | inr1 (inl1 (E1.Intrinsic dt name args)) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 e0)) =>
                _ (* Globals *)
            | inr1 (inr1 (inr1 (inl1 (inl1 e0)))) =>
                _ (* Locals *)
            | inr1 (inr1 (inr1 (inl1 (inr1 e0)))) =>
                _ (* Stack *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e0)))) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0))))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0))))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e0)))))))) =>
                _ (* FailureE *)
            end).

    (* External Calls *)
    { refine (f' <- lift_OOM (uvalue_convert f);;
              args' <- lift_OOM (map_monad_In args (fun elt Hin => dvalue_convert elt));;
              dv <- trigger (E2.ExternalCall dt f' args');;
              _).

      inversion e0.
      apply (lift_OOM (rev_dvalue_convert dv)).
    }

    (* Intrinsics *)
    { inversion i; subst.
      apply (args' <- lift_OOM (map_monad_In args (fun elt Hin => dvalue_convert elt));;
             dv <- trigger (E2.Intrinsic dt name args');;
             lift_OOM (rev_dvalue_convert dv)).
    }

    (* Globals *)
    { inversion e0.
      - (* Global write *)
        apply (dv <- lift_OOM (dvalue_convert dv);;
               trigger (GlobalWrite id dv)).
      - (* Global read *)
        apply (dv <- trigger (GlobalRead id);;
               lift_OOM (rev_dvalue_convert dv)).
    }

    (* Locals *)
    { inversion e0.
      - (* Local write *)
        apply (dv <- lift_OOM (uvalue_convert dv);;
               trigger (LocalWrite id dv)).
      - (* Local read *)
        apply (dv <- trigger (LocalRead id);;
               lift_OOM (rev_uvalue_convert dv)).
    }

    (* Stack *)
    { inversion e0.
      - (* Stack Push *)
        apply (args' <- lift_OOM
                         (map_monad_In args
                            (fun '(id, uv) Hin =>
                               uv' <- uvalue_convert uv;;
                               ret (id, uv')
                         ));;
               trigger (StackPush args')).
      - (* Stack Pop *)
        apply (trigger StackPop).
    }

    (* MemoryE *)
    { inversion e0.
      - (* MemPush *)
        apply (trigger E2.MemPush).
      - (* MemPop *)
        apply (trigger E2.MemPop).
      - (* Alloca *)
        apply (ptr <- trigger (E2.Alloca t num_elements align);;
               lift_OOM (rev_dvalue_convert ptr)).
      - (* Load *)
        apply (a' <- lift_OOM (dvalue_convert a);;
               uv <- trigger (E2.Load t a');;
               lift_OOM (rev_uvalue_convert uv)).
      - (* Store *)
        apply (a' <- lift_OOM (dvalue_convert a);;
               v' <- lift_OOM (uvalue_convert v);;
               trigger (E2.Store t a' v')).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e0.
      subst.
      refine (x' <- lift_OOM (uvalue_convert x);;
              dv <- trigger (E2.pick Pre x');;
              _).
      destruct dv as [res _].
      apply (res' <- lift_OOM (rev_dvalue_convert res);;
             ret (exist (fun x => True) res' I)).
    }

    (* OOME *)
    { inversion e0.
      apply (raise_oom H).
    }

    (* UBE *)
    { inversion e0.
      apply (raise_ub H).
    }

    (* DebugE *)
    { inversion e0.
      apply (debug H).
    }

    (* FailureE *)
    { inversion e0.
      apply (raise_error H).
    }
  Defined.

  Definition L1_convert_helper
    (dvalue_convert : DV1.dvalue -> OOM DV2.dvalue)
    (uvalue_convert : DV1.uvalue -> OOM DV2.uvalue)
    (rev_dvalue_convert : DV2.dvalue -> OOM DV1.dvalue)
    (rev_uvalue_convert : DV2.uvalue -> OOM DV1.uvalue)
    : Handler E1.L1 E2.L1.
    refine (fun A e => _).

    refine (match e with
            | inl1 (E1.ExternalCall dt f args) =>
                _
            | inr1 (inl1 (E1.Intrinsic dt name args)) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 (inl1 e0))) =>
                _ (* Locals *)
            | inr1 (inr1 (inl1 (inr1 e0))) =>
                _ (* Stack *)
            | inr1 (inr1 (inr1 (inl1 e0))) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e0)))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0))))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0))))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e0))))))) =>
                _ (* FailureE *)
            end).

    (* External Calls *)
    { refine (f' <- lift_OOM (uvalue_convert f);;
              args' <- lift_OOM (map_monad_In args (fun elt Hin => dvalue_convert elt));;
              dv <- trigger (E2.ExternalCall dt f' args');;
              _).

      inversion e0.
      apply (lift_OOM (rev_dvalue_convert dv)).
    }

    (* Intrinsics *)
    { inversion i; subst.
      apply (args' <- lift_OOM (map_monad_In args (fun elt Hin => dvalue_convert elt));;
             dv <- trigger (E2.Intrinsic dt name args');;
             lift_OOM (rev_dvalue_convert dv)).
    }

    (* Locals *)
    { inversion e0.
      - (* Local write *)
        apply (dv <- lift_OOM (uvalue_convert dv);;
               trigger (LocalWrite id dv)).
      - (* Local read *)
        apply (dv <- trigger (LocalRead id);;
               lift_OOM (rev_uvalue_convert dv)).
    }

    (* Stack *)
    { inversion e0.
      - (* Stack Push *)
        apply (args' <- lift_OOM
                         (map_monad_In args
                            (fun '(id, uv) Hin =>
                               uv' <- uvalue_convert uv;;
                               ret (id, uv')
                         ));;
               trigger (StackPush args')).
      - (* Stack Pop *)
        apply (trigger StackPop).
    }

    (* MemoryE *)
    { inversion e0.
      - (* MemPush *)
        apply (trigger E2.MemPush).
      - (* MemPop *)
        apply (trigger E2.MemPop).
      - (* Alloca *)
        apply (ptr <- trigger (E2.Alloca t num_elements align);;
               lift_OOM (rev_dvalue_convert ptr)).
      - (* Load *)
        apply (a' <- lift_OOM (dvalue_convert a);;
               uv <- trigger (E2.Load t a');;
               lift_OOM (rev_uvalue_convert uv)).
      - (* Store *)
        apply (a' <- lift_OOM (dvalue_convert a);;
               v' <- lift_OOM (uvalue_convert v);;
               trigger (E2.Store t a' v')).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e0.
      subst.
      refine (x' <- lift_OOM (uvalue_convert x);;
              dv <- trigger (E2.pick Pre x');;
              _).
      destruct dv as [res _].
      apply (res' <- lift_OOM (rev_dvalue_convert res);;
             ret (exist (fun x => True) res' I)).
    }

    (* OOME *)
    { inversion e0.
      apply (raise_oom H).
    }

    (* UBE *)
    { inversion e0.
      apply (raise_ub H).
    }

    (* DebugE *)
    { inversion e0.
      apply (debug H).
    }

    (* FailureE *)
    { inversion e0.
      apply (raise_error H).
    }
  Defined.

  Definition L2_convert_helper
    (dvalue_convert : DV1.dvalue -> OOM DV2.dvalue)
    (uvalue_convert : DV1.uvalue -> OOM DV2.uvalue)
    (rev_dvalue_convert : DV2.dvalue -> OOM DV1.dvalue)
    (rev_uvalue_convert : DV2.uvalue -> OOM DV1.uvalue)
    : Handler E1.L2 E2.L2.
    refine (fun A e => _).

    refine (match e with
            | inl1 (E1.ExternalCall dt f args) =>
                _
            | inr1 (inl1 (E1.Intrinsic dt name args)) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 e0)) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inl1 e0))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e0)))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e0)))))) =>
                _ (* FailureE *)
            end).

    (* External Calls *)
    { refine (f' <- lift_OOM (uvalue_convert f);;
              args' <- lift_OOM (map_monad_In args (fun elt Hin => dvalue_convert elt));;
              dv <- trigger (E2.ExternalCall dt f' args');;
              _).

      inversion e0.
      apply (lift_OOM (rev_dvalue_convert dv)).
    }

    (* Intrinsics *)
    { inversion i; subst.
      apply (args' <- lift_OOM (map_monad_In args (fun elt Hin => dvalue_convert elt));;
             dv <- trigger (E2.Intrinsic dt name args');;
             lift_OOM (rev_dvalue_convert dv)).
    }

    (* MemoryE *)
    { inversion e0.
      - (* MemPush *)
        apply (trigger E2.MemPush).
      - (* MemPop *)
        apply (trigger E2.MemPop).
      - (* Alloca *)
        apply (ptr <- trigger (E2.Alloca t num_elements align);;
               lift_OOM (rev_dvalue_convert ptr)).
      - (* Load *)
        apply (a' <- lift_OOM (dvalue_convert a);;
               uv <- trigger (E2.Load t a');;
               lift_OOM (rev_uvalue_convert uv)).
      - (* Store *)
        apply (a' <- lift_OOM (dvalue_convert a);;
               v' <- lift_OOM (uvalue_convert v);;
               trigger (E2.Store t a' v')).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e0.
      subst.
      refine (x' <- lift_OOM (uvalue_convert x);;
              dv <- trigger (E2.pick Pre x');;
              _).
      destruct dv as [res _].
      apply (res' <- lift_OOM (rev_dvalue_convert res);;
             ret (exist (fun x => True) res' I)).
    }

    (* OOME *)
    { inversion e0.
      apply (raise_oom H).
    }

    (* UBE *)
    { inversion e0.
      apply (raise_ub H).
    }

    (* DebugE *)
    { inversion e0.
      apply (debug H).
    }

    (* FailureE *)
    { inversion e0.
      apply (raise_error H).
    }
  Defined.

  Definition L3_convert_helper
    (dvalue_convert : DV1.dvalue -> OOM DV2.dvalue)
    (uvalue_convert : DV1.uvalue -> OOM DV2.uvalue)
    (rev_dvalue_convert : DV2.dvalue -> OOM DV1.dvalue)
    (rev_uvalue_convert : DV2.uvalue -> OOM DV1.uvalue)
    : Handler E1.L3 E2.L3.
    refine (fun A e => _).

    refine (match e with
            | inl1 (E1.ExternalCall dt f args) =>
                _
            | inr1 (inl1 e0) =>
                _ (* PickE *)
            | inr1 (inr1 (inl1 e0)) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inl1 e0))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e0)))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 e0)))) =>
                _ (* FailureE *)
            end).

    (* External Calls *)
    { refine (f' <- lift_OOM (uvalue_convert f);;
              args' <- lift_OOM (map_monad_In args (fun elt Hin => dvalue_convert elt));;
              dv <- trigger (E2.ExternalCall dt f' args');;
              _).

      inversion e0.
      apply (lift_OOM (rev_dvalue_convert dv)).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e0.
      subst.
      refine (x' <- lift_OOM (uvalue_convert x);;
              dv <- trigger (E2.pick Pre x');;
              _).
      destruct dv as [res _].
      apply (res' <- lift_OOM (rev_dvalue_convert res);;
             ret (exist (fun x => True) res' I)).
    }

    (* OOME *)
    { inversion e0.
      apply (raise_oom H).
    }

    (* UBE *)
    { inversion e0.
      apply (raise_ub H).
    }

    (* DebugE *)
    { inversion e0.
      apply (debug H).
    }

    (* FailureE *)
    { inversion e0.
      apply (raise_error H).
    }
  Defined.

  Definition L4_convert_helper
    (dvalue_convert : DV1.dvalue -> OOM DV2.dvalue)
    (uvalue_convert : DV1.uvalue -> OOM DV2.uvalue)
    (rev_dvalue_convert : DV2.dvalue -> OOM DV1.dvalue)
    (rev_uvalue_convert : DV2.uvalue -> OOM DV1.uvalue)
    : Handler E1.L4 E2.L4.
    refine (fun A e => _).

    refine (match e with
            | inl1 (E1.ExternalCall dt f args) =>
                _
            | inr1 (inl1 e0) =>
                _
            | inr1 (inr1 (inl1 e0)) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inl1 e0))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 e0))) =>
                _ (* FailureE *)
            end).

    (* External Calls *)
    { refine (f' <- lift_OOM (uvalue_convert f);;
              args' <- lift_OOM (map_monad_In args (fun elt Hin => dvalue_convert elt));;
              dv <- trigger (E2.ExternalCall dt f' args');;
              _).

      inversion e0.
      apply (lift_OOM (rev_dvalue_convert dv)).
    }

    (* OOME *)
    { inversion e0.
      apply (raise_oom H).
    }

    (* UBE *)
    { inversion e0.
      apply (raise_ub H).
    }

    (* DebugE *)
    { inversion e0.
      apply (debug H).
    }

    (* FailureE *)
    { inversion e0.
      apply (raise_error H).
    }
  Defined.

  Definition L5_convert_helper
    (dvalue_convert : DV1.dvalue -> OOM DV2.dvalue)
    (uvalue_convert : DV1.uvalue -> OOM DV2.uvalue)
    (rev_dvalue_convert : DV2.dvalue -> OOM DV1.dvalue)
    (rev_uvalue_convert : DV2.uvalue -> OOM DV1.uvalue)
    : Handler E1.L5 E2.L5 := L4_convert_helper dvalue_convert uvalue_convert rev_dvalue_convert rev_uvalue_convert.

  Definition L6_convert_helper
    (dvalue_convert : DV1.dvalue -> OOM DV2.dvalue)
    (uvalue_convert : DV1.uvalue -> OOM DV2.uvalue)
    (rev_dvalue_convert : DV2.dvalue -> OOM DV1.dvalue)
    (rev_uvalue_convert : DV2.uvalue -> OOM DV1.uvalue)
    : Handler E1.L6 E2.L6 := L5_convert_helper dvalue_convert uvalue_convert rev_dvalue_convert rev_uvalue_convert.

  Definition L0_convert_lazy : Handler E1.L0 E2.L0 := L0_convert_helper (ret ∘ dvalue_convert_lazy) (ret ∘ uvalue_convert_lazy) (ret ∘ DVCrev.dvalue_convert_lazy) (ret ∘ DVCrev.uvalue_convert_lazy).
  Definition L1_convert_lazy : Handler E1.L1 E2.L1 := L1_convert_helper (ret ∘ dvalue_convert_lazy) (ret ∘ uvalue_convert_lazy) (ret ∘ DVCrev.dvalue_convert_lazy) (ret ∘ DVCrev.uvalue_convert_lazy).
  Definition L2_convert_lazy : Handler E1.L2 E2.L2 := L2_convert_helper (ret ∘ dvalue_convert_lazy) (ret ∘ uvalue_convert_lazy) (ret ∘ DVCrev.dvalue_convert_lazy) (ret ∘ DVCrev.uvalue_convert_lazy).
  Definition L3_convert_lazy : Handler E1.L3 E2.L3 := L3_convert_helper (ret ∘ dvalue_convert_lazy) (ret ∘ uvalue_convert_lazy) (ret ∘ DVCrev.dvalue_convert_lazy) (ret ∘ DVCrev.uvalue_convert_lazy).
  Definition L4_convert_lazy : Handler E1.L4 E2.L4 := L4_convert_helper (ret ∘ dvalue_convert_lazy) (ret ∘ uvalue_convert_lazy) (ret ∘ DVCrev.dvalue_convert_lazy) (ret ∘ DVCrev.uvalue_convert_lazy).
  Definition L5_convert_lazy : Handler E1.L5 E2.L5 := L5_convert_helper (ret ∘ dvalue_convert_lazy) (ret ∘ uvalue_convert_lazy) (ret ∘ DVCrev.dvalue_convert_lazy) (ret ∘ DVCrev.uvalue_convert_lazy).
  Definition L6_convert_lazy : Handler E1.L6 E2.L6 := L6_convert_helper (ret ∘ dvalue_convert_lazy) (ret ∘ uvalue_convert_lazy) (ret ∘ DVCrev.dvalue_convert_lazy) (ret ∘ DVCrev.uvalue_convert_lazy).

  Definition L0_convert_strict : Handler E1.L0 E2.L0 := L0_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict DVCrev.uvalue_convert_strict.
  Definition L1_convert_strict : Handler E1.L1 E2.L1 := L1_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict DVCrev.uvalue_convert_strict.
  Definition L2_convert_strict : Handler E1.L2 E2.L2 := L2_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict DVCrev.uvalue_convert_strict.
  Definition L3_convert_strict : Handler E1.L3 E2.L3 := L3_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict DVCrev.uvalue_convert_strict.
  Definition L4_convert_strict : Handler E1.L4 E2.L4 := L4_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict DVCrev.uvalue_convert_strict.
  Definition L5_convert_strict : Handler E1.L5 E2.L5 := L5_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict DVCrev.uvalue_convert_strict.
  Definition L6_convert_strict : Handler E1.L6 E2.L6 := L6_convert_helper dvalue_convert_strict uvalue_convert_strict DVCrev.dvalue_convert_strict DVCrev.uvalue_convert_strict.
End EventConvert.

Module EventConvertSafe
  (LP1 : LLVMParams) (LP2 : LLVMParams)
  (AC1 : AddrConvert LP1.ADDR LP2.ADDR) (AC2 : AddrConvert LP2.ADDR LP1.ADDR)
  (ACSafe : AddrConvertSafe LP1.ADDR LP2.ADDR AC1 AC2)
  (IPSafe : IPConvertSafe LP1.IP LP2.IP)
  (Events1 : LLVM_INTERACTIONS LP1.ADDR LP1.IP LP1.SIZEOF) (Events2 : LLVM_INTERACTIONS LP2.ADDR LP2.IP LP2.SIZEOF).
  Module EC := EventConvert LP1 LP2 AC1 AC2 Events1 Events2.
  Module DVCSafe := DVConvertSafe LP1 LP2 AC1 AC2 ACSafe IPSafe Events1 Events2 EC.DVC EC.DVCrev.

  (* Converting finite events to infinite events... *)
  Module DV1 := EC.DVC.DV1. (* Finite *)
  Module DV2 := EC.DVC.DV2. (* Infinite *)

  (* DVC : Fin -> Inf
     DVCrev : Inf -> Fin
   *)

  Definition dvalue_convert (dv : DV1.dvalue) : OOM DV2.dvalue
    := EC.DVC.dvalue_convert_strict dv.

  Definition dvalue_convert_safe (dv : DV1.dvalue) : DV2.dvalue.
  Proof.
    pose proof DVCSafe.dvalue_convert_strict_safe dv.
    (* Uggggh, can't destruct H because constructing a Type :'C *)
    (* destruct H as [dv_i [CONVf CONVi]]. *)
    (* remember (EC.DVC.dvalue_convert_strict dv). *)
    (* destruct o *)
  Admitted.

  Definition uvalue_convert (uv : DV1.uvalue) : OOM DV2.uvalue
    := EC.DVC.uvalue_convert_strict uv.

  Definition uvalue_convert_safe (uv : DV1.uvalue) : DV2.uvalue.
  Proof.
  Admitted.

  Definition rev_dvalue_convert (dv : DV2.dvalue) : OOM DV1.dvalue
    := EC.DVCrev.dvalue_convert_strict dv.

  Definition rev_uvalue_convert (uv : DV2.uvalue) : OOM DV1.uvalue
    := EC.DVCrev.uvalue_convert_strict uv.

  Module E1 := Events1.
  Module E2 := Events2.
  
  Definition L0_convert_safe
    : forall T, E1.L0 T -> E2.L0 T.
    refine (fun A e => _).

    refine (match e with
            | inl1 (E1.ExternalCall dt f args) =>
                _
            | inr1 (inl1 (E1.Intrinsic dt name args)) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 e0)) =>
                _ (* Globals *)
            | inr1 (inr1 (inr1 (inl1 (inl1 e0)))) =>
                _ (* Locals *)
            | inr1 (inr1 (inr1 (inl1 (inr1 e0)))) =>
                _ (* Stack *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e0)))) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0))))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0))))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e0)))))))) =>
                _ (* FailureE *)
            end).

    (* External Calls *)
    { inv e0.
      refine (let f' := uvalue_convert_safe f in
              let args' := map dvalue_convert_safe args in
              _).

      (* I can only construct an external call that gives me an E2.DV.dvalue (infinite)...

         I need to convert it back to a finite dvalue, which I can do
         with rev_dvalue_convert... But I need to know how the
         external call is handled in order to know that the dvalue
         won't cause OOM.
       *)
      epose proof (@subevent E2.ExternalCallE E2.L0 _ E2.DV.dvalue (E2.ExternalCall dt f' args')).
    (*   eapply fmap. *)
    (*   2: eauto. *)
    (*   intros dv. *)
    (*   remember (rev_dvalue_convert dv) as dvr. *)

    (*   eapply X. *)
      
    (*   forward X. *)
    (*   eapply E2.ExternalCall. *)

    (*   apply (subevent _ (E2.ExternalCall dt f' args')). *)

    (*           dv <- trigger (E2.ExternalCall dt f' args');; *)

    (*   inversion e0. *)
    (*   apply (lift_OOM (rev_dvalue_convert dv)). *)
    (* } *)

    (* (* Intrinsics *) *)
    (* { inversion i; subst. *)
    (*   apply (args' <- lift_OOM (map_monad_In args (fun elt Hin => dvalue_convert elt));; *)
    (*          dv <- trigger (E2.Intrinsic dt name args');; *)
    (*          lift_OOM (rev_dvalue_convert dv)). *)
    (* } *)

    (* (* Globals *) *)
    (* { inversion e0. *)
    (*   - (* Global write *) *)
    (*     apply (dv <- lift_OOM (dvalue_convert dv);; *)
    (*            trigger (GlobalWrite id dv)). *)
    (*   - (* Global read *) *)
    (*     apply (dv <- trigger (GlobalRead id);; *)
    (*            lift_OOM (rev_dvalue_convert dv)). *)
    (* } *)

    (* (* Locals *) *)
    (* { inversion e0. *)
    (*   - (* Local write *) *)
    (*     apply (dv <- lift_OOM (uvalue_convert dv);; *)
    (*            trigger (LocalWrite id dv)). *)
    (*   - (* Local read *) *)
    (*     apply (dv <- trigger (LocalRead id);; *)
    (*            lift_OOM (rev_uvalue_convert dv)). *)
    (* } *)

    (* (* Stack *) *)
    (* { inversion e0. *)
    (*   - (* Stack Push *) *)
    (*     apply (args' <- lift_OOM *)
    (*                      (map_monad_In args *)
    (*                         (fun '(id, uv) Hin => *)
    (*                            uv' <- uvalue_convert uv;; *)
    (*                            ret (id, uv') *)
    (*                      ));; *)
    (*            trigger (StackPush args')). *)
    (*   - (* Stack Pop *) *)
    (*     apply (trigger StackPop). *)
    (* } *)

    (* (* MemoryE *) *)
    (* { inversion e0. *)
    (*   - (* MemPush *) *)
    (*     apply (trigger E2.MemPush). *)
    (*   - (* MemPop *) *)
    (*     apply (trigger E2.MemPop). *)
    (*   - (* Alloca *) *)
    (*     apply (ptr <- trigger (E2.Alloca t num_elements align);; *)
    (*            lift_OOM (rev_dvalue_convert ptr)). *)
    (*   - (* Load *) *)
    (*     apply (a' <- lift_OOM (dvalue_convert a);; *)
    (*            uv <- trigger (E2.Load t a');; *)
    (*            lift_OOM (rev_uvalue_convert uv)). *)
    (*   - (* Store *) *)
    (*     apply (a' <- lift_OOM (dvalue_convert a);; *)
    (*            v' <- lift_OOM (uvalue_convert v);; *)
    (*            trigger (E2.Store t a' v')). *)
    (* } *)

    (* (* PickE *) *)
    (* { (* TODO: confirm whether this is sane... *) *)
    (*   inversion e0. *)
    (*   subst. *)
    (*   refine (x' <- lift_OOM (uvalue_convert x);; *)
    (*           dv <- trigger (E2.pick Pre x');; *)
    (*           _). *)
    (*   destruct dv as [res _]. *)
    (*   apply (res' <- lift_OOM (rev_dvalue_convert res);; *)
    (*          ret (exist (fun x => True) res' I)). *)
    (* } *)

    (* (* OOME *) *)
    (* { inversion e0. *)
    (*   apply (raise_oom H). *)
    (* } *)

    (* (* UBE *) *)
    (* { inversion e0. *)
    (*   apply (raise_ub H). *)
    (* } *)

    (* (* DebugE *) *)
    (* { inversion e0. *)
    (*   apply (debug H). *)
    (* } *)

    (* (* FailureE *) *)
    (* { inversion e0. *)
    (*   apply (raise_error H). *)
    (* } *)
  Admitted.
End EventConvertSafe.
