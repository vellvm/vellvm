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

Definition mtype := list dvalue.
Definition undef := DV VALUE_Undef.



CoFixpoint memD (memory:mtype) (d:Trace) : Trace :=
  match d with
    | Tau d'            => Tau (memD memory d')
    | Vis (Eff (Alloca t k))  => Tau (memD (memory ++ [undef])%list
                                          (k (DVALUE_Addr (*!*)(List.length memory))))(*!(pred (List.length memory))*)
    | Vis (Eff (Load a k))    => Tau (memD memory (k (nth_default undef memory a)))
    | Vis (Eff (Store a v k)) => Tau (memD (replace memory a v) k)
    | Vis (Eff (Call d ds k)) => Vis (Eff (Call d ds k))
    | Vis x => Vis x
  end.

Fixpoint MemDFin (memory:mtype) (d:Trace) (steps:nat) : option mtype :=
  match steps with
  | O => None
  | S x =>
    match d with
    | Vis (Fin d) => Some memory
    | Vis (Err s) => None
    | Tau d' => MemDFin memory d' x
    | Vis (Eff (Alloca t k))  => MemDFin (memory ++ [undef])%list (k (DVALUE_Addr (List.length memory))) x
    | Vis (Eff (Load a k))    => MemDFin memory (k (nth_default undef memory a)) x
    | Vis (Eff (Store a v k)) => MemDFin (replace memory a v) k x
    | Vis (Eff (Call d ds k)) => None
    end
  end%N.

