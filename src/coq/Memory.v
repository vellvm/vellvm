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

Inductive SByte :=
| Byte : byte -> SByte
| Ptr : addr -> SByte
| PtrFrag : SByte
| SUndef : SByte.

Definition mem_block := IntMap SByte.
Definition memory := IntMap mem_block.
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

(* Convert integer to its SByte representation. *)
Fixpoint Z_to_sbyte_list (count:nat) (z:Z) : list SByte :=
  match count with
  | O => []
  | S n => (Z_to_sbyte_list n (z / 256)) ++ [Byte (Byte.repr (z mod 256))]
  end.

(* Converts SBytes into their integer representation. *)
Definition sbyte_list_to_Z (bytes:list SByte) : Z :=
  fst (fold_right (fun x acc =>
               match x with
               | Byte b =>
                 let shift := snd acc in
                 ((fst acc) + ((Byte.intval b) * shift), shift * 256)
               | _ => acc (* should not have other kinds bytes in an int *)
               end) (0, 1) bytes).

(* Serializes a dvalue into its SByte-sensitive form. *)
Fixpoint serialize_dvalue (dval:dvalue) : list SByte :=
  match dval with
  | DVALUE_Addr addr => (Ptr addr) :: (repeat PtrFrag 7)
  | DVALUE_I1 i => Z_to_sbyte_list 8 (Int1.unsigned i)
  | DVALUE_I32 i => Z_to_sbyte_list 8 (Int32.unsigned i)
  | DVALUE_I64 i => Z_to_sbyte_list 8 (Int64.unsigned i)
  | DVALUE_Struct fields | DVALUE_Array fields =>
      (* note the _right_ fold is necessary for byte ordering. *)
      fold_right (fun '(typ, dv) acc => ((serialize_dvalue dv) ++ acc) % list) [] fields
  | _ => [] (* TODO add more dvalues as necessary *)
  end.

(* Deserialize a list of SBytes into a dvalue. *)
Fixpoint deserialize_sbytes (bytes:list SByte) (t:typ) : dvalue :=
  match t with
  | TYPE_I sz =>
    let des_int := sbyte_list_to_Z bytes in
    match sz with
    | 1 => DVALUE_I1 (Int1.repr des_int)
    | 32 => DVALUE_I32 (Int32.repr des_int)
    | 64 => DVALUE_I64 (Int64.repr des_int)
    | _ => DVALUE_None (* invalid size. *)
    end
  | TYPE_Pointer t' =>
    match bytes with
    | Ptr addr :: tl => DVALUE_Addr addr
    | _ => DVALUE_None (* invalid pointer. *)
    end
  | TYPE_Array sz t' =>
    let fix array_parse count byte_sz bytes :=
        match count with
        | O => []
        | S n => (t', deserialize_sbytes (firstn byte_sz bytes) t')
                   :: array_parse n byte_sz (skipn byte_sz bytes)
        end in
    DVALUE_Array (array_parse (Z.to_nat sz) (Z.to_nat (sizeof_typ t')) bytes)
  | TYPE_Struct fields =>
    let fix struct_parse typ_list bytes :=
        match typ_list with
        | [] => []
        | t :: tl =>
          let size_ty := Z.to_nat (sizeof_typ t) in
          (t, deserialize_sbytes (firstn size_ty bytes) t)
            :: struct_parse tl (skipn size_ty bytes)
        end in
    DVALUE_Struct (struct_parse fields bytes)
  | _ => DVALUE_None (* TODO add more as serialization support increases *)
  end.

(* Construct block indexed from 0 to n. *)
Fixpoint init_block_h (n:nat) (m:mem_block) : mem_block :=
  match n with
  | O => add 0 SUndef m
  | S n' => add (Z.of_nat n) SUndef (init_block_h n' m)
  end.

(* Initializes a block of n 0-bytes. *)
Definition init_block (n:Z) : mem_block :=
  match n with
  | 0 => empty
  | Z.pos n' => init_block_h (BinPosDef.Pos.to_nat (n' - 1)) empty
  | Z.neg _ => empty (* invalid argument *)
  end.

(* Makes a block appropriately sized for the given type. *)
Definition make_empty_block (ty:typ) : mem_block :=
  init_block (sizeof_typ ty).

Definition mem_step {X} (e:effects X) (m:memory) :=
  match e with
  | Alloca t k =>
    let new_block := make_empty_block t in
    inr  (add (size m) new_block m,
          DVALUE_Addr (size m, 0),
          k)
         
  | Load t a k =>
    match a with
    | (b, i) =>
      match lookup b m with
      | Some block =>
        inr (m,
             deserialize_sbytes (lookup_all_index i (sizeof_typ t) block SUndef) t,
             k)
      | None => inl e
      end
    end

  | Store a v k =>
    match a with
    | (b, i) =>
      match lookup b m with
      | Some m' =>
        inr (add b (add_all_index (serialize_dvalue v) i m') m,
             DVALUE_None, k) 
      | None => inl e
      end
    end
      
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
