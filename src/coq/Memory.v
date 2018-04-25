Require Import ZArith List String Omega.
Require Import  Vellvm.LLVMAst Vellvm.Classes Vellvm.Util.
Require Import Vellvm.StepSemantics Vellvm.LLVMIO Vellvm.LLVMBaseTypes.
Require Import FSets.FMapAVL.
Require Import compcert.lib.Integers compcert.lib.Coqlib.
Require Coq.Structures.OrderedTypeEx.
Require Import ZMicromega.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

Definition oracle (x:unit) : Z := 0.

Module A : Vellvm.LLVMIO.ADDR with Definition addr := (Z * Z) % type.
  Definition addr := (Z * Z) % type.
  Definition null := (-1, 0).
End A.

Definition addr := A.addr.

Module SS := StepSemantics.StepSemantics(A).
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

(* Convert integer to its byte representation. *)
Fixpoint bytes_of_int (n: nat) (x: Z) {struct n}: list byte :=
  match n with
  | O => nil
  | S m => Byte.repr x :: bytes_of_int m (x / 256)
  end.

Fixpoint int_of_bytes (l: list byte): Z :=
  match l with
  | nil => 0
  | b :: l' => Byte.unsigned b + int_of_bytes l' * 256
  end.

Definition Z_to_sbyte_list (count:nat) (z:Z) : list SByte :=
  List.map Byte (bytes_of_int count z).

Definition Sbyte_to_byte_list (sb:SByte) : list byte :=
  match sb with
  | Byte b => [b]
  | Ptr _ | PtrFrag | SUndef => []
  end.

Definition sbyte_list_to_byte_list (bytes:list SByte) : list byte :=
  List.flat_map Sbyte_to_byte_list bytes.

Definition sbyte_list_to_Z (bytes:list SByte) : Z :=
  int_of_bytes (sbyte_list_to_byte_list bytes).

(** Length properties *)

Lemma length_bytes_of_int:
  forall n x, List.length (bytes_of_int n x) = n.
Proof.
  induction n; simpl; intros. auto. decEq. auto.
Qed.

Lemma int_of_bytes_of_int:
  forall n x,
  int_of_bytes (bytes_of_int n x) = x mod (two_p (Z.of_nat n * 8)).
Proof.
  induction n; intros.
  simpl. rewrite Zmod_1_r. auto.
Opaque Byte.wordsize.
  rewrite Nat2Z.inj_succ. simpl.
  replace (Z.succ (Z.of_nat n) * 8) with (Z.of_nat n * 8 + 8) by omega.
  rewrite two_p_is_exp; try omega.
  rewrite Zmod_recombine. rewrite IHn. rewrite Z.add_comm.
  change (Byte.unsigned (Byte.repr x)) with (Byte.Z_mod_modulus x).
  rewrite Byte.Z_mod_modulus_eq. reflexivity.
  apply two_p_gt_ZERO. omega. apply two_p_gt_ZERO. omega.
Qed.



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

(* Todo - complete proofs, and think about moving to MemoryProp module. *)
(* The relation defining serializable dvalues. *)
Inductive serialize_defined : dvalue -> Prop :=
  | d_addr: forall addr,
      serialize_defined (DVALUE_Addr addr)
  | d_i1: forall i1,
      serialize_defined (DVALUE_I1 i1)
  | d_i32: forall i32,
      serialize_defined (DVALUE_I32 i32)
  | d_i64: forall i64,
      serialize_defined (DVALUE_I64 i64)
  | d_struct_empty:
      serialize_defined (DVALUE_Struct [])
  | d_struct_nonempty: forall typ dval fields_list,
      serialize_defined dval ->
      serialize_defined (DVALUE_Struct fields_list) ->
      serialize_defined (DVALUE_Struct ((typ, dval) :: fields_list))
  | d_array_empty:
      serialize_defined (DVALUE_Array [])
  | d_array_nonempty: forall typ dval fields_list,
      serialize_defined dval ->
      serialize_defined (DVALUE_Array fields_list) ->
      serialize_defined (DVALUE_Array ((typ, dval) :: fields_list)).

(* Lemma assumes all integers encoded with 8 bytes. *)

Inductive sbyte_list_wf : list SByte -> Prop :=
| wf_nil : sbyte_list_wf []
| wf_cons : forall b l, sbyte_list_wf l -> sbyte_list_wf (Byte b :: l)
.                                                   

Lemma sbyte_list_to_Z_inverse:
  forall i1 : int1, (sbyte_list_to_Z (Z_to_sbyte_list 8 (Int1.unsigned i1))) = 
               (Int1.unsigned i1).
Proof.
  intros i1.
  destruct i1. simpl.
Admitted.


    
Lemma serialize_inverses : forall dval,
    serialize_defined dval -> exists typ, deserialize_sbytes (serialize_dvalue dval) typ = dval.
Proof.
  intros. destruct H.
  (* DVALUE_Addr. Type of pointer is not important. *)
  - exists (TYPE_Pointer TYPE_Void). reflexivity.
  (* DVALUE_I1. Todo: subversion lemma for integers. *)
  - exists (TYPE_I 1).
    simpl. 
      

    admit.
  (* DVALUE_I32. Todo: subversion lemma for integers. *)
  - exists (TYPE_I 32). admit.
  (* DVALUE_I64. Todo: subversion lemma for integers. *)
  - exists (TYPE_I 64). admit.
  (* DVALUE_Struct [] *)
  - exists (TYPE_Struct []). reflexivity.
  (* DVALUE_Struct fields *)
  - admit.
  (* DVALUE_Array [] *)
  - exists (TYPE_Array 0 TYPE_Void). reflexivity.
  (* DVALUE_Array fields *)
  - admit.
Admitted.

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

Print typ.

Fixpoint handle_gep_h (t:typ) (b:Z) (off:Z) (vs:list dvalue) (m:memory) : err (memory * dvalue):=
  match vs with
  | v :: vs' =>
    match v with
    | DVALUE_I32 i =>
      let k := Int32.unsigned i in
      let n := BinIntDef.Z.to_nat k in
      match t with
      | TYPE_Vector _ ta | TYPE_Array _ ta =>
                           handle_gep_h ta b (off + k * (sizeof_typ ta)) vs' m
      | TYPE_Struct ts | TYPE_Packed_struct ts => (* Handle these differently in future *)
        let offset := fold_left (fun acc t => acc + sizeof_typ t)
                                (firstn n ts) 0 in
        match nth_error ts n with
        | None => raise "overflow"
        | Some t' =>
          handle_gep_h t' b (off + offset) vs' m
        end
      | _ => raise ("non-i32-indexable type: " ++ string_of t)
      end
    | DVALUE_I64 i =>
      let k := Int64.unsigned i in
      let n := BinIntDef.Z.to_nat k in
      match t with
      | TYPE_Vector _ ta | TYPE_Array _ ta =>
                           handle_gep_h ta b (off + k * (sizeof_typ ta)) vs' m
      | _ => raise ("non-i64-indexable type: " ++ string_of t)
      end
    | _ => raise "non-I32 index"
    end
  | [] => mret (m, DVALUE_Addr (b, off))
  end.

Print IM.

Definition concretize_block (b:Z) (m:memory) : Z * memory :=
  match lookup b m with
  | None =>(b, m)
  | Some block =>
    let i := oracle () in
    let fix loop es k block : mem_block :=
        match es with
        | [] => block
        | (i, e) :: tl => loop tl (k+1) (add (k + i) e block)
        end in
    (* TODO change source block SBYTES to associate abstract pointers with concrete memory. *)
    (i, add b (loop (IM.elements block) i block) m)
  end.

Definition handle_gep (t:typ) (dv:dvalue) (vs:list dvalue) (m:memory) : err (memory * dvalue):=
  match t with
  | TYPE_Pointer t =>
    match vs with
    | DVALUE_I32 i :: vs' => (* TODO: Handle non i32 indices *)
      match dv with
      | DVALUE_Addr (b, o) =>
        handle_gep_h t b (o + (sizeof_typ t) * (Int32.unsigned i)) vs' m
      | _ => raise "non-address" 
      end
    | _ => raise "non-I32 index"
    end
  | _ => raise "non-pointer type to GEP"
  end.

Definition mem_step {X} (e:IO X) (m:memory) : err ((IO X) + (memory * X)) :=
  match e with
  | Alloca t =>
    let new_block := make_empty_block t in
    mret (
    inr  (add (size m + 1) new_block m,
          DVALUE_Addr (size m, 0))
    )
         
  | Load t dv => mret
    match dv with
    | DVALUE_Addr a =>
      match a with
      | (b, i) =>
        match lookup b m with
        | Some block =>
          inr (m,
               deserialize_sbytes (lookup_all_index i (sizeof_typ t) block SUndef) t)
        | None => inl (Load t dv)
        end
      end
    | _ => inl (Load t dv)
    end 

  | Store dv v => mret
    match dv with
    | DVALUE_Addr a =>
      match a with
      | (b, i) =>
        match lookup b m with
        | Some m' =>
          inr (add b (add_all_index (serialize_dvalue v) i m') m, ()) 
        | None => inl (Store dv v)
        end
      end
    | _ => inl (Store dv v)
    end
      
  | GEP t dv vs =>

    match handle_gep t dv vs m with
    | inl s => raise s
    | inr r => mret (inr r)
    end

  | ItoP t i =>
    match i with
    | DVALUE_I64 i => mret (inr (m, DVALUE_Addr (0, Int64.unsigned i)))
    | DVALUE_I32 i => mret (inr (m, DVALUE_Addr (0, Int32.unsigned i)))
    | DVALUE_I1 i => mret (inr (m, DVALUE_Addr (0, Int1.unsigned i)))
    | _ => raise "Non integer passed to ItoP"
    end
    
  | PtoI t a =>
    match a with
    | DVALUE_Addr (b, i) =>
      if Z.eqb b 0 then mret (inr (m, DVALUE_Addr(0, i)))
      else let (k, m) := concretize_block b m in
           mret (inr (m, DVALUE_Addr (0, (k + i))))
    | _ => raise "Non pointer passed to PtoI"
    end
                       
  | Call t f args  => mret (inl (Call t f args))

                         
  | DeclareFun f =>
    (* TODO: should check for re-declarations and maintain that state in the memory *)
    mret (inr (m,
          DVALUE_FunPtr f))
  end.

(*
 memory -> TraceLLVMIO () -> TraceX86IO () -> Prop
*)

CoFixpoint memD {X} (m:memory) (d:Trace X) : Trace X :=
  match d with
  | Trace.Tau d'            => Trace.Tau (memD m d')
  | Trace.Vis _ io k =>
    match mem_step io m with
    | inr (inr (m', v)) => Trace.Tau (memD m' (k v))
    | inr (inl e) => Trace.Vis io k
    | inl s => Trace.Err s
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
      (memD empty
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
