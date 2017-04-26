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
Import SS.

Definition mtype := list dvalue.
Definition undef := DV (VALUE_Undef _).

(* HACK: extract ID_LAZY to lazy to fix broken cofixpoint extraction.  See Memory.ml *)
Definition ID_LAZY {A:Type} (x:A) := x.

CoFixpoint memD {A} (memory:mtype) (d:Obs A) : Obs A :=
  match d with
    | Ret a => ID_LAZY (Ret a)
    | Fin d => ID_LAZY (Fin d)
    | Err s => ID_LAZY (Err s)
    | Tau d'            => Tau (memD memory d')
    | Eff (Alloca t k)  => Tau (memD (memory ++ [undef])%list (k (DVALUE_Addr (pred (List.length memory)))))
    | Eff (Load a k)    => Tau (memD memory (k (nth_default undef memory a)))
    | Eff (Store a v k) => Tau (memD (replace memory a v) k)
    | Eff (Call d k) => Eff (Call d k)
  end.
