Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util.
Require Import Vellvm.StepSemantics.
Require Import FSets.FMapAVL.
Require Import Integers.
Require Coq.Structures.OrderedTypeEx.
Require Import ZMicromega.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

Module A : Vellvm.StepSemantics.ADDR with Definition addr := (Z * Z) % type.
  Definition addr := (Z * Z) % type.
  Definition null := (0, 0).
End A.

Module SS := StepSemantics.StepSemantics(A).
Export SS.

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

Definition union {a} (m1 : IntMap a) (m2 : IntMap a)
  := IM.map2 (fun mx my =>
                match mx with | Some x => Some x | None => my end) m1 m2.

Definition size {a} (m : IM.t a) : Z := Z.of_nat (IM.cardinal m).

Inductive SByte :=
| Byte : byte -> SByte
| Ptr : addr -> SByte
| PtrFrag : SByte
| SUndef : SByte.

Definition block := IntMap SByte.
Definition memory := IntMap block.
Definition undef t := DVALUE_Undef t None. (* TODO: should this be an empty block? *)

(* Computes the byte size of this type. *)
Fixpoint sizeof_typ (ty:typ) : Z :=
  match ty with
  | TYPE_I sz => 8 (* All integers are padded to 8 bytes. *)
  | TYPE_Pointer t => 8
  | TYPE_Struct l => fold_left (fun x acc => x + sizeof_typ acc) l 0
  | TYPE_Array sz ty' => sz * sizeof_typ ty'
  | _ => 0 (* TODO: add support for more types as necessary *)
  end.


Fixpoint Z_to_sbyte_list (count: nat) (z: Z) : list SByte :=
  match count with
  | O => []
  | S n => (Z_to_sbyte_list n (z / 256)) ++ [Byte (Byte.repr (z mod 256))]
  end.

(* Serializes a dvalue into its SByte-sensitive form. *)
Fixpoint serialize_dvalue (dval:dvalue) : list SByte :=
  match dval with
  | DVALUE_Addr addr => (Ptr addr) :: (repeat PtrFrag 7)
  | DVALUE_I1 i => Z_to_sbyte_list 8 (Int1.unsigned i)
  | DVALUE_I32 i => Z_to_sbyte_list 8 (Int32.unsigned i)
  | DVALUE_I64 i => Z_to_sbyte_list 8 (Int64.unsigned i)
  | DVALUE_Struct fields | DVALUE_Array fields =>
      fold_left (fun acc '(typ, dv) => ((serialize_dvalue dv) ++ acc) % list) fields []
  | _ => [] (* TODO add more dvalues as necessary *)
  end.

(* Compute serialize_dvalue (DVALUE_I64 (Int64.repr 4294967296)). *)

(* Construct block indexed from 0 to n. *)
Fixpoint init_block_h (n:nat) (m:block) : block :=
  match n with
  | O => add 0 SUndef m
  | S n' => add (Z.of_nat n) SUndef (init_block_h n' m)
  end.

(* Initializes a block of n 0-bytes. *)
Definition init_block (n:Z) : block :=
  match n with
  | 0 => empty
  | Z.pos n' => init_block_h (BinPosDef.Pos.to_nat (n' - 1)) empty
  | Z.neg _ => empty (* invalid argument *)
  end.

(* Makes a block appropriately sized for the given type. *)
Definition make_empty_block (ty:typ) : block :=
  init_block (sizeof_typ ty).

Definition mem_step {X} (e:effects X) (m:memory) :=
  match e with
  | Alloca t k =>
    let new_block := make_empty_block t in
    inr  (add (size m) new_block m,
          DVALUE_Addr (size m, 0),
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
Print dvalue.

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
