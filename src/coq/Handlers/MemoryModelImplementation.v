From Vellvm.Syntax Require Import
     DataLayout
     DynamicTypes.

From Vellvm.Semantics Require Import
     MemoryAddress
     MemoryParams
     LLVMParams
     LLVMEvents
     Memory.FiniteProvenance
     Memory.Sizeof
     Memory.MemBytes
     Memory.ErrSID
     VellvmIntegers.

From Vellvm Require Import
     Numeric.Coqlib
     Numeric.Integers.

From Vellvm.Handlers Require Import
     MemPropT.

From Vellvm.Utils Require Import
     Error
     PropT
     Tactics
     IntMaps.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Data.Monads.StateMonad.

From Coq Require Import
     ZArith
     Strings.String
     List
     Lia.

Import ListNotations.
Import ListUtil.
Import Utils.Monads.

Import MonadNotation.
Open Scope monad_scope.

From Vellvm.Handlers Require Import
     MemoryModel.

#[local] Open Scope Z_scope.

(** * Memory Model

    This file implements VIR's memory model as an handler for the [MemoryE] family of events.
    The model is inspired by CompCert's memory model, but differs in that it maintains two
    representation of the memory, a logical one and a low-level one.
    Pointers (type signature [MemoryAddress.ADDRESS]) are implemented as a pair containing
    an address and an offset.
*)

(* Specifying the currently supported dynamic types.
       This is mostly to rule out:

       - arbitrary bitwidth integers
       - half
       - x86_fp80
       - fp128
       - ppc_fp128
       - metadata
       - x86_mmx
       - opaque
 *)
Inductive is_supported : dtyp -> Prop :=
| is_supported_DTYPE_I1 : is_supported (DTYPE_I 1)
| is_supported_DTYPE_I8 : is_supported (DTYPE_I 8)
| is_supported_DTYPE_I32 : is_supported (DTYPE_I 32)
| is_supported_DTYPE_I64 : is_supported (DTYPE_I 64)
| is_supported_DTYPE_Pointer : is_supported (DTYPE_Pointer)
| is_supported_DTYPE_Void : is_supported (DTYPE_Void)
| is_supported_DTYPE_Float : is_supported (DTYPE_Float)
| is_supported_DTYPE_Double : is_supported (DTYPE_Double)
| is_supported_DTYPE_Array : forall sz τ, is_supported τ -> is_supported (DTYPE_Array sz τ)
| is_supported_DTYPE_Struct : forall fields, Forall is_supported fields -> is_supported (DTYPE_Struct fields)
| is_supported_DTYPE_Packed_struct : forall fields, Forall is_supported fields -> is_supported (DTYPE_Packed_struct fields)
(* TODO: unclear if is_supported τ is good enough here. Might need to make sure it's a sized type *)
| is_supported_DTYPE_Vector : forall sz τ, is_supported τ -> vector_dtyp τ -> is_supported (DTYPE_Vector sz τ)
.


(** ** Type of pointers
    Implementation of the notion of pointer used: an address and an offset.
 *)
Definition Iptr := Z. (* Integer pointer type (physical addresses) *)

(* TODO: Should probably make this an NSet, but it gives universe inconsistency with Module addr *)
Definition Prov := option (list Provenance). (* Provenance *)

Definition wildcard_prov : Prov := None.
Definition nil_prov : Prov := Some [].

(* TODO: If Prov is an NSet, I get a universe inconsistency here... *)
Module Addr : MemoryAddress.ADDRESS with Definition addr := (Iptr * Prov) % type.
  Definition addr := (Iptr * Prov) % type.
  Definition null : addr := (0, nil_prov)%Z.

  (* TODO: is this what we should be using for equality on pointers? Probably *NOT* because of provenance. *)
  Lemma eq_dec : forall (a b : addr), {a = b} + {a <> b}.
  Proof.
    intros [a1 a2] [b1 b2].

    destruct (Z.eq_dec a1 b1);
      destruct (option_eq (fun x y => list_eq_dec N.eq_dec x y) a2 b2); subst.
    - left; reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
  Qed.

  Lemma different_addrs :
    forall (a : addr), exists (b : addr), a <> b.
  Proof.
    intros a.
    destruct a.
    destruct i.
    - exists (Z.pos 1, p).
      intros CONTRA; inversion CONTRA.
    - exists (0, p).
      intros CONTRA; inversion CONTRA.
    - exists (Z.pos 1, p).
      intros CONTRA; inversion CONTRA.
  Qed.

  Definition show_addr (a : addr) := Show.show a.

  Definition ptr_overlap (a b : addr)
    := fst a = fst b.

  Definition ptr_overlap_dec (a b : addr) : {ptr_overlap a b} + {~ptr_overlap a b}
    := Z.eq_dec (fst a) (fst b).

  Lemma ptr_overlap_refl :
    forall a, ptr_overlap a a.
  Proof.
    intros a.
    destruct a; cbn; reflexivity.
  Qed.
End Addr.

Module BigIP : MemoryAddress.INTPTR with
Definition intptr := Z with
Definition from_Z := (fun (x : Z) => ret x : OOM Z).
  Definition intptr := Z.
  Definition zero := 0%Z.

  Definition eq_dec := Z.eq_dec.
  Definition eqb := Z.eqb.

  Definition to_Z (x : intptr) := x.

  (* TODO: negatives.... ???? *)
  Definition to_unsigned := to_Z.
  Definition from_Z (x : Z) : OOM intptr := ret x.

  Lemma from_Z_to_Z :
    forall (z : Z) (i : intptr),
      from_Z z = NoOom i ->
      to_Z i = z.
  Proof.
    intros z i FROM.
    inversion FROM; auto.
  Qed.

  Lemma from_Z_0 :
    from_Z 0 = NoOom zero.
  Proof.
    auto.
  Qed.

  Lemma to_Z_0 :
    to_Z zero = 0.
  Proof.
    auto.
  Qed.

  Definition mequ_Z (x y : Z) : bool :=
    Z.eqb x y.

  Definition mcmp_Z (c : comparison) (x y : Z) : bool := 
    match c with
    | Ceq => Z.eqb x y
    | Cne => Zneq_bool x y
    | Clt => Z.ltb x y
    | Cle => Z.leb x y
    | Cgt => Z.gtb x y
    | Cge => Z.geb x y
    end.

  Definition mcmpu_Z (c : comparison) (x y : Z) : bool := 
    match c with
    | Ceq => Z.eqb x y
    | Cne => Zneq_bool x y
    | Clt => Z.ltb x y
    | Cle => Z.leb x y
    | Cgt => Z.gtb x y
    | Cge => Z.geb x y
    end.

  Instance VMemInt_intptr : VMemInt intptr
    :=
    { mequ  := mequ_Z;
      mcmp  := mcmp_Z;
      mcmpu := mcmpu_Z;

      mbitwidth := None;
      mzero     := 0%Z;
      mone      := 1%Z;

      madd := fun x y => ret (Z.add x y);
      (* No overflows *)
      madd_carry := fun x y c => 0%Z;
      madd_overflow := fun x y c => 0%Z;

      msub := fun x y => ret (Z.sub x y);
      (* No overflows *)
      msub_borrow := fun x y c => 0%Z;
      msub_overflow := fun x y c => 0%Z;

      mmul := fun x y => ret (Z.mul x y);

      mdivu := fun x y => Z.div x y;
      mdivs := fun x y => ret (Z.div x y);

      mmodu := fun x y => Z.modulo x y;
      mmods := fun x y => ret (Z.modulo x y);

      mshl := fun x y => ret (Z.shiftl x y);
      mshr := fun x y => Z.shiftr x y;
      mshru := fun x y => Z.shiftr x y;

      mnegative := fun x => ret (0 - x)%Z;

      mand := Z.land;
      mor := Z.lor;
      mxor := Z.lxor;

      mmin_signed := None;
      mmax_signed := None;

      munsigned := fun x => x;
      msigned := fun x => x;

      mrepr := fun x => ret x;

      mdtyp_of_int := DTYPE_IPTR
    }.

  Lemma VMemInt_intptr_dtyp :
    @mdtyp_of_int intptr VMemInt_intptr = DTYPE_IPTR.
  Proof.
    cbn. reflexivity.
  Qed.

End BigIP.

Module BigIP_BIG : MemoryAddress.INTPTR_BIG BigIP.
  Import BigIP.

  Lemma from_Z_safe :
    forall z,
      match from_Z z with
      | NoOom _ => True
      | Oom _ => False
      end.
  Proof.
    intros z.
    unfold from_Z.
    reflexivity.
  Qed.
End BigIP_BIG.

Module IP64Bit : MemoryAddress.INTPTR.
  Definition intptr := int64.
  Definition zero := Int64.zero.

  Definition eq_dec := Int64.eq_dec.
  Definition eqb := Int64.eq.

  Definition to_Z (x : intptr) := Int64.signed x.

  (* TODO: negatives.... ???? *)
  Definition to_unsigned := to_Z.
  Definition from_Z (x : Z) : OOM intptr :=
    if (x <=? Int64.max_signed)%Z && (x >=? Int64.min_signed)%Z
    then ret (Int64.repr x)
    else Oom "IP64Bit from_Z oom.".

  Lemma from_Z_to_Z :
    forall (z : Z) (i : intptr),
      from_Z z = NoOom i ->
      to_Z i = z.
  Proof.
    intros z i FROM.
    unfold from_Z in FROM.
    break_match_hyp; inversion FROM.
    unfold to_Z.
    apply Integers.Int64.signed_repr.
    lia.
  Qed.

  Lemma from_Z_0 :
    from_Z 0 = NoOom zero.
  Proof.
    auto.
  Qed.

  Lemma to_Z_0 :
    to_Z zero = 0.
  Proof.
    auto.
  Qed.

  Instance VMemInt_intptr : VMemInt intptr
    :=
    { (* Comparisons *)
      mequ := Int64.eq;
      mcmp := Int64.cmp;
      mcmpu := Int64.cmpu;

      (* Constants *)
      mbitwidth := Some 64%nat;
      mzero := Int64.zero;
      mone := Int64.one;

      (* Arithmetic *)
      madd := fun x y =>
               if (Int64.eq (Int64.add_overflow x y Int64.zero) Int64.one)
               then Oom "IP64Bit addition overflow."
               else ret (Int64.add x y);
      madd_carry := Int64.add_carry;
      madd_overflow := Int64.add_overflow;

      msub := fun x y =>
               if (Int64.eq (Int64.sub_overflow x y Int64.zero) Int64.one)
               then Oom "IP64Bit addition overflow."
               else ret (Int64.sub x y);
      msub_borrow := Int64.sub_borrow;
      msub_overflow := Int64.sub_overflow;

      mmul :=
      fun x y =>
        let res_s' := ((Int64.signed x) * (Int64.signed y))%Z in

        let min_s_bound := Int64.min_signed >? res_s' in
        let max_s_bound := res_s' >? Int64.max_signed in

        if (orb min_s_bound max_s_bound)
        then Oom "IP64Bit multiplication overflow."
        else NoOom (Int64.mul x y);

      mdivu := Int64.divu;
      mdivs :=
      fun x y =>
        if (Int64.signed x =? Int64.max_signed) && (Int64.signed y =? (-1)%Z)
        then Oom "IP64Bit signed division overflow."
        else ret (Int64.divs x y);

      mmodu := Int64.modu;
      mmods :=
      (* TODO: is this overflow check needed? *)
      fun x y =>
        if (Int64.signed x =? Int64.max_signed) && (Int64.signed y =? (-1)%Z)
        then Oom "IP64Bit signed modulo overflow."
        else ret (Int64.mods x y);

      mshl :=
      fun x y =>
        let res := Int64.shl x y in
        if Int64.signed res =? Int64.min_signed
        then Oom "IP64Bit left shift overflow (res is min signed, should not happen)."
        else
          let nres := Int64.negative res in
          if (negb (Z.shiftr (Int64.unsigned x)
                             (64%Z - Int64.unsigned y)
                    =? (Int64.unsigned nres)
                       * (Z.pow 2 (Int64.unsigned y) - 1))%Z)
          then Oom "IP64Bit left shift overflow."
          else ret res;
      mshr := Int64.shr;
      mshru := Int64.shru;

      mnegative :=
      fun x =>
        if (Int64.signed x =? Int64.min_signed)
        then Oom "IP64Bit taking negative of smallest number."
        else ret (Int64.negative x);

      (* Logic *)
      mand := Int64.and;
      mor := Int64.or;
      mxor := Int64.xor;

      (* Bounds *)
      mmin_signed := ret Int64.min_signed;
      mmax_signed := ret Int64.max_signed;

      (* Conversion *)
      munsigned := Int64.unsigned;
      msigned := Int64.signed;

      mrepr := from_Z;

      mdtyp_of_int := DTYPE_IPTR
    }.

  Lemma VMemInt_intptr_dtyp :
    @mdtyp_of_int intptr VMemInt_intptr = DTYPE_IPTR.
  Proof.
    cbn. reflexivity.
  Qed.

End IP64Bit.


Module FinPTOI : PTOI(Addr).
  Definition ptr_to_int (ptr : Addr.addr) := fst ptr.
End FinPTOI.

Module FinPROV : PROVENANCE(Addr) with Definition Prov := Prov.
  Definition Provenance := Provenance.
  Definition AllocationId := AllocationId.
  Definition Prov := Prov.
  Definition wildcard_prov : Prov := wildcard_prov.
  Definition nil_prov : Prov := nil_prov.
  Definition address_provenance (a : Addr.addr) : Prov
    := snd a.

  (* Does the provenance set pr allow for access to aid? *)
  Definition access_allowed (pr : Prov) (aid : AllocationId) : bool
    := match pr with
       | None => true (* Wildcard can access anything. *)
       | Some prset =>
         match aid with
         | None => true (* Wildcard, can be accessed by anything. *)
         | Some aid =>
           existsb (N.eqb aid) prset
         end
       end.

  Definition aid_access_allowed (pr : AllocationId) (aid : AllocationId) : bool
    := match pr with
       | None => true
       | Some pr =>
         match aid with
         | None => true
         | Some aid =>
           N.eqb pr aid
         end
       end.

  Definition allocation_id_to_prov (aid : AllocationId) : Prov
    := fmap (fun x => [x]) aid.

  Definition provenance_to_allocation_id (pr : Provenance) : AllocationId
    := Some pr.

  Definition next_provenance (pr : Provenance) : Provenance
    := N.succ pr.

  Definition initial_provenance : Provenance
    := 0%N.

  (* Debug *)
  Definition show_prov (pr : Prov) := Show.show pr.
  Definition show_provenance (pr : Provenance) := Show.show pr.
  Definition show_allocation_id (aid : AllocationId) := Show.show aid.

End FinPROV.

Module FinITOP : ITOP(Addr)(FinPROV).
  Definition int_to_ptr (i : Z) (pr : Prov) : Addr.addr
    := (i, pr).
End FinITOP.

Module FinSizeof : Sizeof.
  (* TODO: make parameter? *)
  Definition ptr_size : nat := 8.

  Fixpoint sizeof_dtyp (ty:dtyp) : N :=
    match ty with
    | DTYPE_I 1          => 1 (* TODO: i1 sizes... *)
    | DTYPE_I 8          => 1
    | DTYPE_I 32         => 4
    | DTYPE_I 64         => 8
    | DTYPE_I _          => 0 (* Unsupported integers *)
    | DTYPE_IPTR         => N.of_nat ptr_size
    | DTYPE_Pointer      => N.of_nat ptr_size
    | DTYPE_Packed_struct l
    | DTYPE_Struct l     => fold_left (fun acc x => (acc + sizeof_dtyp x)%N) l 0%N
    | DTYPE_Vector sz ty'
    | DTYPE_Array sz ty' => sz * sizeof_dtyp ty'
    | DTYPE_Float        => 4
    | DTYPE_Double       => 8
    | DTYPE_Half         => 4
    | DTYPE_X86_fp80     => 10 (* TODO: Unsupported, currently modeled by Float32 *)
    | DTYPE_Fp128        => 16 (* TODO: Unsupported, currently modeled by Float32 *)
    | DTYPE_Ppc_fp128    => 16 (* TODO: Unsupported, currently modeled by Float32 *)
    | DTYPE_Metadata     => 0
    | DTYPE_X86_mmx      => 8 (* TODO: Unsupported *)
    | DTYPE_Opaque       => 0 (* TODO: Unsupported *)
    | _                  => 0 (* TODO: add support for more types as necessary *)
    end.

  Lemma sizeof_dtyp_void :
    sizeof_dtyp DTYPE_Void = 0%N.
  Proof. reflexivity. Qed.

  Lemma sizeof_dtyp_pos :
    forall dt,
      (0 <= sizeof_dtyp dt)%N.
  Proof.
    intros dt.
    lia.
  Qed.

  Lemma sizeof_dtyp_packed_struct_0 :
    sizeof_dtyp (DTYPE_Packed_struct nil) = 0%N.
  Proof.
    reflexivity.
  Qed.

  Lemma sizeof_dtyp_packed_struct_cons :
    forall dt dts,
      sizeof_dtyp (DTYPE_Packed_struct (dt :: dts)) = (sizeof_dtyp dt + sizeof_dtyp (DTYPE_Packed_struct dts))%N.
  Proof.
    intros dt dts.
    cbn.
    rewrite fold_sum_acc.
    reflexivity.
  Qed.

  Lemma sizeof_dtyp_struct_0 :
    sizeof_dtyp (DTYPE_Struct nil) = 0%N.
  Proof.
    reflexivity.
  Qed.

  (* TODO: this should take padding into account *)
  Lemma sizeof_dtyp_struct_cons :
    forall dt dts,
      sizeof_dtyp (DTYPE_Struct (dt :: dts)) = (sizeof_dtyp dt + sizeof_dtyp (DTYPE_Struct dts))%N.
  Proof.
    intros dt dts.
    cbn.
    rewrite fold_sum_acc.
    reflexivity.
  Qed.

  Lemma sizeof_dtyp_array :
    forall sz t,
      sizeof_dtyp (DTYPE_Array sz t) = (sz * sizeof_dtyp t)%N.
  Proof.
    reflexivity.
  Qed.

  Lemma sizeof_dtyp_vector :
    forall sz t,
      sizeof_dtyp (DTYPE_Vector sz t) = (sz * sizeof_dtyp t)%N.
  Proof.
    reflexivity.
  Qed.
End FinSizeof.

Module FinByte (ADDR : MemoryAddress.ADDRESS) (IP : MemoryAddress.INTPTR) (SIZEOF : Sizeof) (LLVMEvents:LLVM_INTERACTIONS(ADDR)(IP)(SIZEOF)) : ByteImpl(ADDR)(IP)(SIZEOF)(LLVMEvents).
  Import LLVMEvents.
  Import DV.

  Inductive UByte :=
  | mkUByte (uv : uvalue) (dt : dtyp) (idx : uvalue) (sid : store_id) : UByte.

  Definition SByte := UByte.

  Definition uvalue_sbyte := mkUByte.

  Definition sbyte_to_extractbyte (byte : SByte) : uvalue
    := match byte with
       | mkUByte uv dt idx sid => UVALUE_ExtractByte uv dt idx sid
       end.

  Lemma sbyte_to_extractbyte_inv :
    forall (b : SByte),
    exists uv dt idx sid,
      sbyte_to_extractbyte b = UVALUE_ExtractByte uv dt idx sid.
  Proof.
    intros b. destruct b.
    cbn; eauto.
  Qed.

  Lemma sbyte_to_extractbyte_of_uvalue_sbyte :
    forall uv dt idx sid,
      sbyte_to_extractbyte (uvalue_sbyte uv dt idx sid) =  UVALUE_ExtractByte uv dt idx sid.
  Proof.
    auto.
  Qed.

End FinByte.

Module FiniteMemoryModelSpecPrimitives (LP : LLVMParams) (MP : MemoryParams LP) <: MemoryModelSpecPrimitives LP MP.
  Import LP.
  Import LP.Events.
  Import LP.ADDR.
  Import LP.SIZEOF.
  Import LP.PROV.
  Import PTOI.
  Import ITOP.

  Require Import MemBytes.
  Module MemByte := Byte LP.ADDR LP.IP LP.SIZEOF LP.Events MP.BYTE_IMPL.
  Import MemByte.
  Import LP.SIZEOF.


  Section Datatype_Definition.

    (* Memory consists of bytes which have a provenance associated with them. *)
    Definition mem_byte := (SByte * AllocationId)%type.

    (** ** Memory
        Memory is just a map of blocks.
     *)
    Definition memory := IntMap mem_byte.

    (** ** Stack frames
      A frame contains the list of block ids that need to be freed when popped,
      i.e. when the function returns.
      A [frame_stack] is a list of such frames.
     *)
    Definition Frame := list Iptr.
    Inductive FrameStack' : Type :=
    | Singleton (f : Frame)
    | Snoc (s : FrameStack') (f : Frame).

    (* The kernel does not recognize yet that a parameter can be
       instantiated by an inductive type. Hint: you can rename the
       inductive type and give a definition to map the old name to the new
       name. *)
    Definition FrameStack := FrameStack'.

    (** ** Memory stack
      The full notion of state manipulated by the monad is a pair of a [memory] and a [mem_stack].
     *)
    Definition memory_stack : Type := memory * FrameStack.

  End Datatype_Definition.

  Record MemState' :=
    mkMemState
      { ms_memory_stack : memory_stack;
        ms_sid : store_id;
        ms_prov : Provenance
      }.

  (* The kernel does not recognize yet that a parameter can be
  instantiated by an inductive type. Hint: you can rename the
  inductive type and give a definition to map the old name to the new
  name.
  *)
  Definition MemState := MemState'.

  Definition mem_state_memory (ms : MemState) : memory
    := fst ms.(ms_memory_stack).

  Definition mem_state_frame_stack (ms : MemState) : FrameStack
    := snd ms.(ms_memory_stack).

  Definition read_byte_MemPropT (ptr : addr) : MemPropT MemState SByte :=
    let addr := ptr_to_int ptr in
    let pr := address_provenance ptr in
    ms <- get_mem_state;;
    let mem := mem_state_memory ms in
    match IM.find addr mem with
    | None => raise_ub "Reading from unallocated memory."
    | Some byte =>
        let aid := snd byte in
        if access_allowed pr aid
        then ret (fst byte)
        else
          raise_ub 
            ("Read from memory with invalid provenance -- addr: " ++ Show.show addr ++ ", addr prov: " ++ show_prov pr ++ ", memory allocation id: " ++ Show.show (show_allocation_id aid) ++ " memory: " ++ Show.show (map (fun '(key, (_, aid)) => (key, show_allocation_id aid)) (IM.elements mem)))
    end.

  Definition addr_allocated_prop (ptr : addr) (aid : AllocationId) : MemPropT MemState bool :=
    ms <- get_mem_state;;
    match IM.find (ptr_to_int ptr) (mem_state_memory ms) with
    | None => ret false
    | Some (byte, aid') =>
        ret (aid_access_allowed aid aid')
    end.

  Definition ptr_in_frame_prop (f : Frame) (ptr : addr) : Prop :=
    In (ptr_to_int ptr) f.

  (* Check for the current frame *)
  Definition peek_frame_stack_prop (fs : FrameStack) (f : Frame) : Prop :=
    match fs with
    | Singleton f' => f = f'
    | Snoc s f' => f = f'
    end.

  Definition pop_frame_stack_prop (fs fs' : FrameStack) : Prop :=
    match fs with
    | Singleton f => False
    | Snoc s f => s = fs'
    end.

  Definition mem_state_frame_stack_prop (ms : MemState) (fs : FrameStack) : Prop :=
    snd (ms_memory_stack ms) = fs.

  (** Allocation ids / store ids *)
  Definition used_allocation_id_prop (ms : MemState) (aid : AllocationId) : Prop :=
    exists ptr byte,
      let mem := mem_state_memory ms in
      IM.find ptr mem = Some (byte, aid).

  Definition used_store_id_prop (ms : MemState) (sid : store_id) : Prop :=
    exists ptr byte aid,
      let mem := mem_state_memory ms in
      IM.find ptr mem = Some (byte, aid) /\
        sbyte_sid byte = inr sid.
End FiniteMemoryModelSpecPrimitives.

Module FiniteMemoryModelExecPrimitives (LP : LLVMParams) (MP : MemoryParams LP) : MemoryModelExecPrimitives LP MP.
  Module MMSP := FiniteMemoryModelSpecPrimitives LP MP.
  Module MemSpec := MakeMemoryModelSpec LP MP MMSP.

  Import LP.
  Import LP.ADDR.
  Import LP.SIZEOF.
  Import LP.PROV.
  Import LP.PTOI.
  Import LP.ITOP.
  Import MMSP.
  Import MMSP.MemByte.
  Import MemSpec.
  Import MemHelpers.

  Module ESID := ERRSID ADDR IP SIZEOF PROV.

  Section MemoryPrimatives.
    Context {MemM : Type -> Type}.
    (* Context `{Monad MemM}. *)
    (* Context `{MonadAllocationId AllocationId MemM}. *)
    (* Context `{MonadStoreID MemM}. *)
    (* Context `{MonadMemState MemState MemM}. *)
    (* Context `{RAISE_ERROR MemM} `{RAISE_UB MemM} `{RAISE_OOM MemM}. *)
    Context `{MemMonad MemState AllocationId MemM}.

    (*** Data types *)
    Definition memory_empty : memory := empty.
    Definition frame_empty : FrameStack := Singleton [].
    Definition empty_memory_stack : memory_stack := (memory_empty, frame_empty).

    Definition initial_memory_state : MemState :=
      mkMemState empty_memory_stack 0%N initial_provenance.

    Definition initial_frame : Frame :=
      [].

    (** ** Fresh key getters *)

    (* Get the next key in the memory *)
    Definition next_memory_key (m : memory_stack) : Z :=
      next_key (fst m).

    (*** Primitives on memory *)
    (** Reads *)
    Definition read_byte (ptr : addr) : MemM SByte :=
      let addr := ptr_to_int ptr in
      let pr := address_provenance ptr in
      ms <- get_mem_state;;
      let mem := mem_state_memory ms in
      match IM.find addr mem with
      | None => raise_ub "Reading from unallocated memory."
      | Some (byte, aid) =>
          if access_allowed pr aid
          then ret byte

          else
            raise_ub 
              ("Read from memory with invalid provenance -- addr: " ++ Show.show addr ++ ", addr prov: " ++ show_prov pr ++ ", memory allocation id: " ++ Show.show (show_allocation_id aid) ++ " memory: " ++ Show.show (map (fun '(key, (_, aid)) => (key, show_allocation_id aid)) (IM.elements mem)))
      end.


    (** Writes *)
    Definition write_byte (ptr : addr) (byte : SByte) : MemM unit :=
      let addr := ptr_to_int ptr in
      let pr := address_provenance ptr in
      ms <- get_mem_state;;
      let mem := mem_state_memory ms in
      match IM.find addr mem with
      | None => raise_ub "Writing to unallocated memory"
      | Some (_, aid) =>
          if access_allowed pr aid
          then
            let mem' := add addr (byte, aid) mem in
            let fs := mem_state_frame_stack ms in
            put_mem_state (mkMemState (mem', fs) ms.(ms_sid) ms.(ms_prov))
          else raise_ub 
                 ("Trying to write to memory with invalid provenance -- addr: " ++ Show.show addr ++ ", addr prov: " ++ show_prov pr ++ ", memory allocation id: " ++ show_allocation_id aid ++ " Memory: " ++ Show.show (map (fun '(key, (_, aid)) => (key, show_allocation_id aid)) (IM.elements mem)))
      end.

    (** Allocations *)
    Definition addr_allocated (ptr : addr) (aid : AllocationId) : MemM bool :=
      ms <- get_mem_state;;
      match IM.find (ptr_to_int ptr) (mem_state_memory ms) with
      | None => ret false
      | Some (byte, aid') =>
          ret (aid_access_allowed aid aid')
      end.

    Definition add_to_frame (m : memory_stack) (k : Z) : memory_stack :=
      let '(m,s) := m in
      match s with
      | Singleton f => (m, Singleton (k :: f))
      | Snoc s f => (m, Snoc s (k :: f))
      end.

    Definition add_all_to_frame (m : memory_stack) (ks : list Z) : memory_stack
      := fold_left (fun ms k => add_to_frame ms k) ks m.

    Definition allocate_bytes (dt : dtyp) (init_bytes : list SByte) : MemM addr :=
      match dt with
      | DTYPE_Void => raise_ub "Allocation of type void"
      | _ =>
          ms <- get_mem_state;;
          aid <- fresh_allocation_id;;
          sid <- fresh_sid;;
          let mem_stack := ms_memory_stack ms in
          let addr := next_memory_key mem_stack in
          let '(mem, fs) := ms_memory_stack ms in
          let ptr := (int_to_ptr addr (allocation_id_to_prov aid)) in
          ptrs <- get_consecutive_ptrs ptr (length init_bytes);;
          undef_bytes <- lift_OOM (generate_undef_bytes dt sid);;
          let mem' := add_all_index (map (fun b => (b, aid)) undef_bytes) addr mem in
          let mem_stack' := add_all_to_frame (mem', fs) (map ptr_to_int ptrs) in
          ms' <- get_mem_state;;
          put_mem_state (mkMemState mem_stack' ms'.(ms_sid) ms'.(ms_prov));;
          ret ptr
      end.


    (** Frame stacks *)
    (* Check if an address is allocated in a frame *)
    Definition ptr_in_frame (f : Frame) (ptr : addr) : bool
      := existsb (fun p => Z.eqb (ptr_to_int ptr) p) f.

    (* Check for the current frame *)
    Definition peek_frame_stack (fs : FrameStack) : Frame :=
      match fs with
      | Singleton f => f
      | Snoc s f => f
      end.

    Definition push_frame_stack (fs : FrameStack) (f : Frame) : FrameStack :=
      Snoc fs f.

    Definition pop_frame_stack (fs : FrameStack) : err FrameStack :=
      match fs with
      | Singleton f => inl "Last frame, cannot pop."%string
      | Snoc s f => inr s
      end.

    Definition mem_state_set_frame_stack (ms : MemState) (fs : FrameStack) : MemState :=
      let (mem, _) := ms_memory_stack ms in
      mkMemState (mem, fs) ms.(ms_sid) ms.(ms_prov).

    Definition mempush : MemM unit :=
      ms <- get_mem_state;;
      let fs := mem_state_frame_stack ms in
      let fs' := push_frame_stack fs initial_frame in
      let ms' := mem_state_set_frame_stack ms fs' in
      put_mem_state ms'.

    Definition free_byte
               (b : Iptr)
               (m : memory) : memory
      := delete b m.

    Definition free_frame_memory (f : Frame) (m : memory) : memory :=
      fold_left (fun m key => free_byte key m) f m.

    Definition mempop : MemM unit :=
      ms <- get_mem_state;;
      let (mem, fs) := ms_memory_stack ms in
      let f := peek_frame_stack fs in
      fs' <- lift_err_RAISE_ERROR (pop_frame_stack fs);;
      let mem' := free_frame_memory f mem in
      let ms' := mkMemState (mem', fs') ms.(ms_sid) ms.(ms_prov) in
      put_mem_state ms'.

    (*** Correctness *)
    (* Import ESID. *)
    (* Definition MemStateM := ErrSID_T (state MemState). *)

    (* Instance MemStateM_MonadAllocationId : MonadAllocationId AllocationId MemStateM. *)
    (* Proof. *)
    (*   split. *)
    (*   apply ESID.fresh_allocation_id. *)
    (* Defined. *)

    (* Instance MemStateM_MonadStoreID : MonadStoreId MemStateM. *)
    (* Proof. *)
    (*   split. *)
    (*   apply ESID.fresh_sid. *)
    (* Defined. *)

    (* Instance MemStateM_MonadMemState : MonadMemState MemState MemStateM. *)
    (* Proof. *)
    (*   split. *)
    (*   - apply (lift MonadState.get). *)
    (*   - intros ms. *)
    (*     apply (lift (MonadState.put ms)). *)
    (* Defined. *)
    
    (* Instance ErrSIDMemMonad : MemMonad MemState AllocationId (ESID.ErrSID_T (state MemState)). *)
    (* Proof. *)
    (*   split. *)
    (*   - (* MemMonad_runs_to *) *)
    (*     intros A ma ms. *)
    (*     destruct ms eqn:Hms. *)
    (*     pose proof (runState (runErrSID_T ma ms_sid0 ms_prov0) ms). *)
    (*     destruct X as [[[res sid'] pr'] ms']. *)
    (*     unfold err_ub_oom. *)
    (*     constructor. *)
    (*     repeat split. *)
    (*     destruct res. *)
    (*     left. apply o. *)
    (*     destruct s. *)
    (*     right. left. apply u. *)
    (*     destruct s. *)
    (*     right. right. left. apply e. *)
    (*     repeat right. apply (ms', a). *)
    (*   - (* MemMonad_lift_stateT *) *)
    (*     admit. *)
    (* Admitted. *)

    Import EitherMonad.
    Definition exec_correct {X} (exec : MemM X) (spec : MemPropT MemState X) : Prop :=
      forall ms,
        match IdentityMonad.unIdent (unEitherT (unEitherT (unEitherT (unERR_UB_OOM (MemMonad_run exec ms))))) with
        | inl (OOM_message oom_msg) =>
            spec ms (inr (Oom oom_msg))
        | inr (inl (UB_message ub_msg)) =>
            forall res, ~ spec ms res
        | inr (inr (inl (ERR_message err_msg))) =>
            spec ms (inl err_msg)
        | inr (inr (inr (ms', res))) =>
            spec ms (inr (NoOom (ms', res)))
        end.

    (* TODO: Move these tactics *)
    Ltac MemMonad_go :=
      repeat match goal with
             | |- context [MemMonad_run (bind _ _)] => rewrite MemMonad_run_bind
             | |- context [MemMonad_run get_mem_state] => rewrite MemMonad_get_mem_state
             | |- context [MemMonad_run (ret _)] => rewrite MemMonad_run_ret
             | |- context [MemMonad_run (raise_ub _)] => rewrite MemMonad_run_raise_ub
             end.

    Ltac break_memory_lookup :=
      match goal with
      | |- context [match IM.find ?intptr ?memory with _ => _ end] =>
          let Hlookup := fresh "Hlookup" in
          let byte := fresh "byte" in
          let aid := fresh "aid" in
          destruct (IM.find intptr memory) as [[byte aid] | ]eqn:Hlookup
      end.

    Ltac MemMonad_break :=
      first
        [ break_memory_lookup
        | match goal with
          | |- context [MemMonad_run (if ?X then _ else _)] =>
              let Hcond := fresh "Hcond" in
              destruct X eqn:Hcond
          end
        ].

    Ltac MemMonad_inv_break :=
      match goal with
      | H: Some _ = Some _ |- _ =>
          inv H
      | H: None = Some _ |- _ =>
          inv H
      | H: Some _ = None |- _ =>
          inv H
      end; cbn in *.

    Ltac MemMonad_subst_if :=
      match goal with
      | H: ?X = true |- context [if ?X then _ else _] =>
          rewrite H
      | H: ?X = false |- context [if ?X then _ else _] =>
          rewrite H
      end.

    Ltac intros_mempropt_contra :=
      intros [?err | [[?ms' ?res] | ?oom]];
      match goal with
      | |- ~ _ =>
          let CONTRA := fresh "CONTRA" in
          let err := fresh "err" in
          intros CONTRA;
          destruct CONTRA as [err [CONTRA | CONTRA]]; auto;
          destruct CONTRA as (? & ? & (? & ?) & CONTRA); subst
      | |- ~ _ =>
          let CONTRA := fresh "CONTRA" in
          let err := fresh "err" in
          intros CONTRA;
          destruct CONTRA as (? & ? & (? & ?) & CONTRA); subst
      end.

    Ltac subst_mempropt :=
      repeat
        match goal with
        | Hlup: IM.find ?addr ?mem = _,
            H: context [match IM.find ?addr ?mem with _ => _ end] |- _
          => rewrite Hlup in H; cbn in H
        | HC: ?X = _,
            H: context [if ?X then _ else _] |- _
          => rewrite HC in H; cbn in H
        end.

    Ltac solve_mempropt_contra :=
      intros_mempropt_contra;
      repeat
        (first
           [ progress subst_mempropt
           | tauto
        ]).

    Ltac MemMonad_solve :=
      repeat
        (first
           [ progress (MemMonad_go; cbn)
           | MemMonad_break; try MemMonad_inv_break; cbn
           | solve_mempropt_contra
           | MemMonad_subst_if; cbn
           | repeat eexists
           | tauto
        ]).

    (** Correctness of the main operations on memory *)
    Lemma read_byte_correct :
      forall ptr, exec_correct (read_byte ptr) (read_byte_MemPropT ptr).
    Proof.
      unfold exec_correct.
      intros ptr ms.
      destruct ms.
      unfold read_byte.
      cbn.

      MemMonad_solve.
    Qed.

    Parameter write_byte_correct :
      forall ptr byte, exec_correct (write_byte ptr byte) (write_byte_spec_MemPropT ptr byte).

    Parameter allocate_bytes_correct :
      forall dt init_bytes, exec_correct (allocate_bytes dt init_bytes) (allocate_bytes_spec_MemPropT dt init_bytes).

    (** Correctness of frame stack operations *)
    Parameter mempush_correct :
      exec_correct mempush mempush_spec_MemPropT.

    Parameter mempop_correct :
      exec_correct mempop mempop_spec_MemPropT.

    (*** Initial memory state *)
    Record initial_memory_state_prop : Prop :=
      {
        initial_memory_no_allocations :
        forall ptr aid,
          ~ byte_allocated initial_memory_state ptr aid;

        initial_memory_frame_stack :
        forall fs,
          mem_state_frame_stack_prop initial_memory_state fs ->
          empty_frame_stack fs;

        initial_memory_no_reads :
        forall ptr byte,
          ~ read_byte_prop initial_memory_state ptr byte
      }.

    Record initial_frame_prop : Prop :=
      {
        initial_frame_is_empty : empty_frame initial_frame;
      }.

    Parameter initial_memory_state_correct : initial_memory_state_prop.
    Parameter initial_frame_correct : initial_frame_prop.
  End MemoryPrimatives.

End FiniteMemoryModelExecPrimitives.

Module MakeFiniteMemoryModelSpec (LP : LLVMParams) (MP : MemoryParams LP).
  Module FMSP := FiniteMemoryModelSpecPrimitives LP MP.
  Module FMS := MakeMemoryModelSpec LP MP FMSP.
End MakeFiniteMemoryModelSpec.

