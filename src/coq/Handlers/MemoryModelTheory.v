From Vellvm.Syntax Require Import
     DataLayout
     DynamicTypes.

From Vellvm.Semantics Require Import
     MemoryParams
     SerializationParams
     LLVMParams
     LLVMEvents
     Memory.ErrSID.

From Vellvm.Handlers Require Import
     MemoryModel
     MemoryInterpreters.

From ITree Require Import
     ITree
     Basics.Basics
     Eq
     Events.StateFacts
     Events.State.

From Coq Require Import
     Morphisms.

Set Implicit Arguments.
Set Contextual Implicit.


Module MemoryModelITreeTheory (LP : LLVMParams) (MP : MemoryParams LP) (SP : SerializationParams LP MP) (MM : MemoryModel LP MP) (MI : MemoryInterpreter LP MP MM).
  Import LP.ADDR.
  Import LP.Events.
  Import MI.
  Import MM.

  Section PARAMS.
    Variable (E F G : Type -> Type).
    Context `{FailureE -< F} `{UBE -< F} `{PickConcreteMemoryE -< F} `{OOME -< F}.
    Notation Effin := (E +' IntrinsicE +' MemoryE +' F).
    Notation Effout := (E +' F).
    Notation interp_memory := (@interp_memory E F _ _ _).

    Section Structural_Lemmas.

      Lemma interp_memory_bind :
        forall (R S : Type) (t : itree Effin R) (k : R -> itree Effin S) ms,
          interp_memory (ITree.bind t k) ms ≅
                        ITree.bind (interp_memory t ms) (fun '(ms', r) => interp_memory (k r) ms').
      Proof.
        intros.
        unfold interp_memory.
        setoid_rewrite interp_state_bind.
        apply eq_itree_clo_bind with (UU := Logic.eq).
        reflexivity.
        intros [] [] EQ; inv EQ; reflexivity.
      Qed.

      Lemma interp_memory_ret :
        forall (R : Type) m (x: R),
          interp_memory (Ret x: itree Effin R) m ≅ Ret (m,x).
      Proof.
        intros; apply interp_state_ret.
      Qed.

      Lemma interp_memory_Tau :
        forall {R} (t: itree Effin R) m,
          interp_memory (Tau t) m ≅ Tau (interp_memory t m).
      Proof.
        intros.
        unfold interp_memory; rewrite interp_state_tau; reflexivity.
      Qed.

      Lemma interp_memory_vis_eqit:
        forall S X (kk : X -> itree Effin S) m
          (e : Effin X),
          interp_memory (Vis e kk) m ≅ ITree.bind (interp_memory_h e m) (fun sx => Tau (interp_memory (kk (snd sx)) (fst sx))).
      Proof.
        intros.
        unfold interp_memory.
        setoid_rewrite interp_state_vis.
        reflexivity.
      Qed.

      Lemma interp_memory_vis:
        forall m S X (kk : X -> itree Effin S) (e : Effin X),
          interp_memory (Vis e kk) m ≈ ITree.bind (interp_memory_h e m) (fun sx => interp_memory (kk (snd sx)) (fst sx)).
      Proof.
        intros.
        rewrite interp_memory_vis_eqit.
        apply eutt_eq_bind.
        intros ?; tau_steps; reflexivity.
      Qed.

      Lemma interp_memory_trigger:
        forall (m : MemState) X (e : Effin X),
          interp_memory (ITree.trigger e) m ≈ interp_memory_h e m.
      Proof.
        intros.
        unfold interp_memory.
        rewrite interp_state_trigger.
        reflexivity.
      Qed.

      Lemma interp_memory_bind_trigger_eqit:
        forall m S X (kk : X -> itree Effin S) (e : Effin X),
          interp_memory (ITree.bind (trigger e) kk) m ≅ ITree.bind (interp_memory_h e m) (fun sx => Tau (interp_memory (kk (snd sx)) (fst sx))).
      Proof.
        intros.
        unfold interp_memory.
        rewrite bind_trigger.
        setoid_rewrite interp_state_vis.
        reflexivity.
      Qed.

      Lemma interp_memory_bind_trigger:
        forall m S X
          (kk : X -> itree Effin S)
          (e : Effin X),
          interp_memory (ITree.bind (trigger e) kk) m ≈ ITree.bind (interp_memory_h e m) (fun sx => interp_memory (kk (snd sx)) (fst sx)).
      Proof.
        intros.
        rewrite interp_memory_bind_trigger_eqit.
        apply eutt_eq_bind.
        intros ?; tau_steps; reflexivity.
      Qed.

      #[global] Instance eutt_interp_memory {R} {R2} :
        Proper (eutt Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp_memory R R2).
      Proof.
        repeat intro.
        unfold interp_memory.
        subst;
          match goal with
          | H: ?x   ?y |- _ => rewrite H
          end.
        reflexivity.
      Qed.

    End Structural_Lemmas.
  End PARAMS.
End MemoryModelITreeTheory.

Module Type MemoryModelTheory (LP : LLVMParams) (MP : MemoryParams LP) (SP : SerializationParams LP MP) (MM : MemoryModel LP MP) (MI : MemoryInterpreter LP MP MM).
  Import LP.ADDR.
  Import LP.Events.
  Import MI.
  Import MM.
  Import LP.PROV.

  Require Import MemBytes.
  Module MemByte := Byte LP.ADDR LP.IP LP.SIZEOF LP.Events MP.BYTE_IMPL.
  Import MemByte.
  Import LP.SIZEOF.

  Section PARAMS.
    Variable (E F G : Type -> Type).
    Context `{FailureE -< F} `{UBE -< F} `{PickConcreteMemoryE -< F} `{OOME -< F}.
    Notation Effin := (E +' IntrinsicE +' MemoryE +' F).
    Notation Effout := (E +' F).
    Notation interp_memory := (@interp_memory E F _ _ _).

    Require Import ZArith.
    Require Import Error.

    Variable MemM : Type -> Type.
    Context `{MemM_MemMonad : MemMonad MemState Provenance MemM}.

    Parameter read_bytes :
      forall (ptr : addr) (sz : N),
        MemM (list SByte).

    Parameter write_bytes :
      forall (ptr : addr) (bytes : list SByte),
        MemM unit.

    From ExtLib Require Import
         Structures.Monads.

    Import MonadNotation.

    Definition read (ptr : addr) (dt : dtyp) : MemM uvalue
      := bytes <- read_bytes ptr (sizeof_dtyp dt);;
         ret (from_ubytes bytes dt).

    Definition write (ptr : addr) (uv : uvalue) (dt : dtyp) : MemM unit
      := sid <- fresh_sid;;
         bytes <- lift_OOM (to_ubytes uv dt sid);;
         write_bytes ptr bytes.

    Section Structural_Lemmas.
      (* Should it be any refinement? *)
      Parameter interp_memory_load :
        forall {M} `{MemMonad MemState Provenance M}
          (m : MemState) (t : dtyp) (val : uvalue) (a : addr),
          MemMonad_runs_to_prop (read a t) m m val ->
          interp_memory (trigger (Load t (DVALUE_Addr a))) m ≈ read.

      Parameter interp_memory_store :
        forall {M} `{MemMonad MemState Provenance M}
          (m m' : MemState) (val : uvalue) (dt : dtyp) (a : addr),
          MemMonad_runs_to_prop (write a val dt) m m' tt ->
          interp_memory (trigger (Store dt (DVALUE_Addr a) val)) m ≈ Ret (m', tt).

      Parameter interp_memory_alloca :
        forall {M} `{MemMonad MemState Provenance M}
          (m m' : MemState) (t : dtyp) (a : addr),
          MemMonad_runs_to_prop (allocate t) m m' a ->
          interp_memory (trigger (Alloca t)) m ≈ Ret (m', DVALUE_Addr a).

      Require Import ZArith.
      Definition pick_phys_addr (ms : MemState) (ptr : addr) (dt : dtyp) : PickConcreteMemoryE {phys : Z | concrete_memory_pick_post (ms, (ptr, dt)) phys}
        := pick True (ms, (ptr, dt)).

      From ExtLib Require Import
           Structures.Monads.
      Import MonadNotation.
      Open Scope monad_scope.

      (* Predicate taking tree, m', and a.... *)
      Parameter interp_memory_ptoi :
        forall {M} `{MemMonad MemState Provenance M}
          (m m' : MemState) (t : dtyp) (a : addr) (i : Z),
          (* MemMonad_runs_to (ptoi t a) m = Some (m', i) -> *)
          (* Intptr will really be something else *)
          interp_memory (trigger (PtoI t a)) m ≈
                        c <- trigger (pick_phys_addr m a t);;
                        let i := proj1_sig c in
                        Ret (m', DVALUE_IPTR i).

    End Structural_Lemmas.
  End PARAMS.
End MemoryModelTheory.
