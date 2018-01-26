Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util.
Require Import Vellvm.StepSemantics.
Require Import Integers.
Require Import ZMicromega.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

Module A : Vellvm.StepSemantics.ADDR with Definition addr := (nat * nat) % type.
  Definition addr := (nat * nat) % type.
  Definition null := (0 % nat, 0 % nat).
End A.

Module SS := StepSemantics.StepSemantics(A).
Export SS.

Definition block := list byte.
Definition memory := list block.
Definition undef t := DVALUE_Undef t None. (* TODO: should this be an empty block? *)

(* Computes the byte size of this type. *)
Fixpoint sizeof_typ (ty:typ) : Z :=
  match ty with
  | TYPE_I sz => (if Z.eqb (sz mod 8) 0 then (sz / 8) else ((sz / 8) + 1))
  | TYPE_Pointer t => 64
  | TYPE_Struct l => fold_left (fun x acc => x + sizeof_typ acc) l 0
  | TYPE_Array sz ty' => sz * sizeof_typ ty'
  | _ => 0 (* TODO: add support for more types as necessary *)
  end.

(* Initializes a block of n 0-bytes. *)
Definition init_block (n:Z) : block :=
  match n with
  | 0 => []
  | Z.pos n' => repeat Byte.zero (BinPosDef.Pos.to_nat n')
  | Z.neg _ => [] (* invalid argument *)
  end.

(* Makes a block appropriately sized for the given type. *)
Definition make_empty_block (ty:typ) : block :=
  init_block (sizeof_typ ty).

Definition mem_step {X} (e:effects X) (m:memory) :=
  match e with
  | Alloca t k =>
    let new_block := make_empty_block t in
    inr  ((m ++ [new_block]) % list,
          DVALUE_Addr (List.length m, 0 % nat),
          k)
  | Load t a k => inl e
    (*inr (m,
         nth_default (undef t) m a,
         k)*)

  | Store a v k => inl e
    (*inr (replace m a v,
         DVALUE_None,
         k)*)

  | GEP t a vs k => inl e (* TODO: GEP semantics *)

  | ItoP t i k => inl e (* TODO: ItoP semantics *)

  | PtoI t a k => inl e (* TODO: ItoP semantics *)
  | Call _ _ _ _ => inl e
  end.

(*
 memory -> Trace () -> Trace () -> Prop
*)

CoFixpoint memD (m:memory) (d:Trace ()) : Trace () :=
  match d with
  | Tau x d'            => Tau x (memD m d')
  | Vis (Eff e) =>
    match mem_step e m with
    | inr (m', v, k) => Tau tt (memD m' (k v))
    | inl e => Vis (Eff e)
    end
  | Vis x => Vis x
  end.

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
