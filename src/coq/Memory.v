Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util.
Require Import Vellvm.StepSemantics.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

Module A : Vellvm.StepSemantics.ADDR with Definition addr := nat.
  Definition addr := nat.
End A.  

Module SS := StepSemantics.StepSemantics(A).
Export SS.

Definition memory := list dvalue.
Definition undef := DV VALUE_Undef.

Definition mem_step {X} (e:effects X) (m:memory) :=
  match e with
  | Alloca t k =>
    inr  ((m ++ [undef])%list,
          DVALUE_Addr (List.length m),
          k)
  | Load a k =>
    inr (m,
         nth_default undef m a,
         k)

  | Store a v k =>
    inr (replace m a v,
         DV VALUE_None,
         k)

  | Call _ _ _ => inl e
  end.

CoFixpoint memD (m:memory) (d:Trace) : Trace :=
  match d with
  | Tau d'            => Tau (memD m d')
  | Vis (Eff e) =>
    match mem_step e m with
    | inr (m', v, k) => Tau (memD m' (k v))
    | inl e => Vis (Eff e)
    end
  | Vis x => Vis x
  end.
                            

Fixpoint MemDFin (m:memory) (d:Trace) (steps:nat) : option memory :=
  match steps with
  | O => None
  | S x =>
    match d with
    | Vis (Fin d) => Some m
    | Vis (Err s) => None
    | Tau d' => MemDFin m d' x
    | Vis (Eff e)  =>
      match mem_step e m with
      | inr (m', v, k) => MemDFin m' (k v) x
      | inl _ => None
      end
    end
  end%N.


(*
Previous bug: 
Fixpoint MemDFin {A} (memory:mtype) (d:Obs A) (steps:nat) : option mtype :=
  match steps with
  | O => None
  | S x =>
    match d with
    | Ret a => None
    | Fin d => Some memory
    | Err s => None
    | Tau d' => MemDFin memory d' x
    | Eff (Alloca t k)  => MemDFin (memory ++ [undef])%list (k (DVALUE_Addr (pred (List.length memory)))) x
    | Eff (Load a k)    => MemDFin memory (k (nth_default undef memory a)) x
    | Eff (Store a v k) => MemDFin (replace memory a v) k x
    | Eff (Call d ds k)    => None
    end
  end%N.
*)