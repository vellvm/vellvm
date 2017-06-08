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

(* HACK: extract ID_LAZY to lazy to fix broken cofixpoint extraction.  See Memory.ml *)
Definition ID_LAZY {A:Type} (x:A) := x.

CoFixpoint memD {A} (memory:mtype) (d:Obs A) : Obs A :=
  match d with
    | Ret a => ID_LAZY (Ret a)
    | Fin d => ID_LAZY (Fin d)
    | Err s => ID_LAZY (Err s)
    | Tau d'            => Tau (memD memory d')
    | Eff (Alloca t k)  => Tau (memD (memory ++ [undef])%list (k (DVALUE_Addr (List.length memory))))
    | Eff (Load a k)    => Tau (memD memory (k (nth_default undef memory a)))
    | Eff (Store a v k) => Tau (memD (replace memory a v) k)
    | Eff (Call d ds k) => Eff (Call d ds k)
  end.


Fixpoint MemDFin {A} (memory:mtype) (d:Obs A) (steps:nat) : option mtype :=
  match steps with
  | O => None
  | S x =>
    match d with
    | Ret a => None
    | Fin d => Some memory
    | Err s => None
    | Tau d' => MemDFin memory d' x
    | Eff (Alloca t k)  => MemDFin (memory ++ [undef])%list (k (DVALUE_Addr (List.length memory))) x
    | Eff (Load a k)    => MemDFin memory (k (nth_default undef memory a)) x
    | Eff (Store a v k) => MemDFin (replace memory a v) k x
    | Eff (Call d ds k)    => None
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