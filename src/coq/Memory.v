Require Import ZArith List String Omega.
Require Import  Vellvm.LLVMAst Vellvm.Classes Vellvm.Util.
Require Import Vellvm.StepSemantics.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

Module A : Vellvm.StepSemantics.ADDR with Definition addr := nat.
  Definition addr := nat.
  Definition null := 0%nat.   (* TODO this is unsound but convenient *)
End A.  

Module SS := StepSemantics.StepSemantics(A).
Export SS.

Definition memory := list dvalue.
Definition undef t := DVALUE_Undef t None.

Definition mem_step {X} (e:IO X) (m:memory) : (IO X) + (list dvalue * X) :=
  match e with
  | Alloca t =>
    inr  ((m ++ [undef t])%list,
          DVALUE_Addr (List.length m))

  | Load t a =>
    inr (m,
         nth_default (undef t) m a)

  | Store a v =>
    inr (replace m a v,
         ())

  | GEP t a vs => inl e (* TODO: GEP semantics *)

  | ItoP t i => inl e (* TODO: ItoP semantics *)

  | PtoI t a => inl e (* TODO: ItoP semantics *)                     
                       
  | Call _ _ _  => inl e
  end.

(*
 memory -> Trace () -> Trace () -> Prop
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

(*
Fixpoint MemDFin (m:memory) (d:Trace ()) (steps:nat) : option memory :=
  match steps with
  | O => None
  | S x =>
    match d with
    | Vis (Fin d) => Some m
    | Vis (Err s) => None
    | Tau _ d' => MemDFin m d' x
    | Vis (Eff e)  =>
      match mem_step e m with
      | inr (m', v, k) => MemDFin m' (k v) x
      | inl _ => None
      end
    end
  end%N.
*)

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