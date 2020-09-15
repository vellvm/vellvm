Require Import ZArith List String Omega.
Require Import Oat.AST Vellvm.Classes Vellvm.Util.
Require Import Oat.StepSemantics Oat.OATIO.
Require Import FSets.FMapAVL.
Require Import compcert.lib.Integers.
Require Coq.Structures.OrderedTypeEx.
Require Import ZMicromega.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

Module A : OATIO.ADDR with Definition addr := Z.
  Definition addr := Z.
  Definition null := 0.
End A.

Definition addr := A.addr.

Module SS := StepSemantics.OStepSemantics(A).
Export SS.
Export SS.DV.


Module IM := FMapAVL.Make(Coq.Structures.OrderedTypeEx.Z_as_OT).
Definition IntMap := IM.t.

Definition add {a} k (v:a) := IM.add k v.
Definition delete {a} k (m:IntMap a) := IM.remove k m.
Definition member {a} k (m:IntMap a) := IM.mem k m.
Definition lookup {a} k (m:IntMap a) := IM.find k m.
Definition empty {a} := @IM.empty a.

Fixpoint add_all {a} ks (m:IntMap a) :=
  match ks with
  | [] => m
  | (k,v) :: tl => add k v (add_all tl m)
  end.

Fixpoint add_all_index {a} vs (i:Z) (m:IntMap a) :=
  match vs with
  | [] => m
  | v :: tl => add i v (add_all_index tl (i+1) m)
  end.

(* Give back a list of values from i to (i + sz) - 1 in m. *)
(* Uses def as the default value if a lookup failed. *)
Definition lookup_all_index {a} (i:Z) (sz:Z) (m:IntMap a) (def:a) : list a :=
  map (fun x =>
         let x' := lookup (Z.of_nat x) m in
         match x' with
         | None => def
         | Some val => val
         end) (seq (Z.to_nat i) (Z.to_nat sz)).

Definition union {a} (m1 : IntMap a) (m2 : IntMap a)
  := IM.map2 (fun mx my =>
                match mx with | Some x => Some x | None => my end) m1 m2.

Definition size {a} (m : IM.t a) : Z := Z.of_nat (IM.cardinal m).

Definition memory := IntMap dvalue.

Print IO.

Definition mem_step {X} (e:IO X) (m:memory) : (IO X) + (memory * X) :=
  match e with
  | Alloca t =>
    inr  (add (size m + 1) (DVALUE_Null t) m, (* Find efficient way to calculate a fresh pointer*)
          DVALUE_Addr (size m + 1))
         
  | Load dv =>
    match dv with
    | DVALUE_Addr i =>
      match lookup i m with
      | None => inl (Load dv)
      | Some dv => inr (m, dv)
      end
    | _ => inl (Load dv)
    end
  | Store dv v =>
    match dv with
    | DVALUE_Addr i =>
      inr (add i v m, ())
    | _ => inl (Store dv v)
    end
  end.

(*
 memory -> TraceLLVMIO () -> TraceX86IO () -> Prop
*)

CoFixpoint memD {X} (m:memory) (d:Trace X) : Trace X :=
  match d with
  | Trace.Tau d'            => Trace.Tau (memD m d')
  | Trace.Vis _ io k =>
    match mem_step io m with
    | inr (m', v) => Trace.Tau (memD m' (k v))
    | inl e => Trace.Vis io k
    end
  | Trace.Ret x => d
  | Trace.Err x => d
  end.


Definition run_with_memory prog : option (Trace dvalue) :=
  mret
    (memD empty (SS.step_sem prog (Step (init_state prog)))).

