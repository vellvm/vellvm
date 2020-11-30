Require Import ZArith List String Omega.
Require Import  Vellvm.LLVMAst Vellvm.Util.
Require Import Vellvm.StepSemantics.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

Inductive Addr :=
| Null
| Ptr (n:nat)
.      

Module A : Vellvm.LLVMIO.ADDR with Definition addr := Addr.
  Definition addr := Addr.
  Definition null := Null.   
End A.  

Module SS := StepSemantics.StepSemantics(A).
Export SS.
Export SS.DV.

Definition memory := list dvalue.

Definition mem_step {X} (e:IO X) (m:memory) : (IO X) + (list dvalue * X) :=
  match e in IO Y return (IO Y) + (list dvalue * Y) with 
  | Alloca t =>
    inr  ((m ++ [undef t])%list,
          DVALUE_Addr (Ptr (List.length m)))

  | Load t a =>
    inr (m,
         match a with
         | DVALUE_Addr (Ptr n) => nth_default (undef t) m n
         | _ => undef t
         end)
        
  | Store a v =>
    inr (
        match a with
        | DVALUE_Addr (Ptr n) => replace m n v
        | _ => m   (* TODO: should fail! *)
        end,
        ())

  | GEP t a vs => inl (GEP t a vs) (* TODO: GEP semantics *)

  | ItoP t i => inl (ItoP t i) (* TODO: ItoP semantics *)

  | PtoI t a => inl (PtoI t a) (* TODO: ItoP semantics *)                     
                       
  | Call t f args  => inl (Call t f args)

                         
  | DeclareFun f =>
    (* TODO: should check for re-declarations and maintain that state in the memory *)
    inr (m,
         DVALUE_FunPtr f)
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
  let scfg := AstLib.modul_of_toplevel_entities prog in
  match CFG.mcfg_of_modul scfg with
  | None => None
  | Some mcfg =>
    mret
      (memD [] 
      ('s <- SS.init_state mcfg "main";
         SS.step_sem mcfg (SS.Step s)))
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