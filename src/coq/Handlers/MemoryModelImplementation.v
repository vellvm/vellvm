From Vellvm.Syntax Require Import
     DataLayout
     DynamicTypes.

From Vellvm.Semantics Require Import
     MemoryAddress
     MemoryParams
     LLVMParams
     LLVMEvents
     Lang
     Memory.FiniteProvenance
     Memory.Sizeof
     Memory.MemBytes
     Memory.ErrSID
     GepM
     VellvmIntegers.

From Vellvm Require Import
     Numeric.Coqlib
     Numeric.Integers.

From Vellvm.Handlers Require Import
     MemPropT
     MemoryInterpreters.

From Vellvm.Utils Require Import
     Util
     Error
     PropT
     Tactics
     IntMaps
     MonadEq1Laws
     MonadExcLaws
     MapMonadExtra
     Raise.

From ITree Require Import
     ITree
     Eq.Eq.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Data.Monads.StateMonad.

From Coq Require Import
     ZArith
     Strings.String
     List
     Lia
     Relations
     RelationClasses.

Import ListNotations.
Import ListUtil.
Import Utils.Monads.

Import MonadNotation.
Open Scope monad_scope.

From Vellvm.Handlers Require Import
     MemoryModel
     MemoryInterpreters.

Require Import Morphisms.

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

  Lemma to_Z_inj :
    forall x y,
      to_Z x = to_Z y ->
      x = y.
  Proof.
    intros x y.
    unfold to_Z; auto.
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

  Require Import ProofIrrelevance.

  Lemma to_Z_inj :
    forall x y,
      to_Z x = to_Z y ->
      x = y.
  Proof.
    intros x y EQ.
    unfold to_Z in *.
    destruct x, y.
    unfold Int64.signed, Int64.unsigned in *.
    cbn in *.
    break_match_hyp; break_match_hyp; subst.
    - rewrite (proof_irrelevance _ intrange intrange0); auto.
    - lia.
    - lia.
    - assert (intval = intval0) by lia; subst.
      rewrite (proof_irrelevance _ intrange intrange0); auto.
  Admitted. (* This is probably awful because of lia? *)

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


Module FinPTOI : PTOI(Addr)
with Definition ptr_to_int := fun (ptr : Addr.addr) => fst ptr.
  Definition ptr_to_int (ptr : Addr.addr) := fst ptr.
End FinPTOI.

Module FinPROV : PROVENANCE(Addr)
with Definition Prov := Prov
with Definition address_provenance
    := fun (a : Addr.addr) => snd a.
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

  Definition provenance_lt (p1 p2 : Provenance) : Prop
    := N.lt p1 p2.

  Lemma aid_access_allowed_refl :
    forall aid, aid_access_allowed aid aid = true.
  Proof.
    intros aid.
    unfold aid_access_allowed.
    destruct aid; auto.
    rewrite N.eqb_refl.
    auto.
  Qed.

  Lemma access_allowed_refl :
    forall aid,
      access_allowed (allocation_id_to_prov aid) aid = true.
  Proof.
    intros aid.
    unfold access_allowed.
    cbn.
    destruct aid; auto.
    cbn.
    rewrite N.eqb_refl.
    cbn.
    auto.
  Qed.

  Lemma allocation_id_to_prov_inv:
    forall aid aid',
      allocation_id_to_prov aid = allocation_id_to_prov aid' ->
      aid = aid'.
  Proof.
    intros aid aid' H.
    unfold allocation_id_to_prov in *.
    cbn in *.
    destruct aid, aid'; inv H; auto.
  Qed.

  Lemma provenance_to_allocation_id_inv :
    forall pr pr',
      provenance_to_allocation_id pr = provenance_to_allocation_id pr' ->
      pr = pr'.
  Proof.
    intros pr pr' H.
    unfold provenance_to_allocation_id in *.
    inv H; auto.
  Qed.

  Lemma provenance_eq_dec :
    forall (pr pr' : Provenance),
      {pr = pr'} + {pr <> pr'}.
  Proof.
    unfold Provenance.
    unfold FiniteProvenance.Provenance.
    intros pr pr'.
    apply N.eq_dec.
  Defined.

  Lemma provenance_eq_dec_refl :
    forall (pr : Provenance),
      true = provenance_eq_dec pr pr.
  Proof.
    intros pr.
    destruct provenance_eq_dec; cbn; auto.
    exfalso; auto.
  Qed.

  Lemma aid_eq_dec :
    forall (aid aid' : AllocationId),
      {aid = aid'} + {aid <> aid'}.
  Proof.
    intros aid aid'.
    destruct aid, aid'; auto.
    pose proof provenance_eq_dec p p0.
    destruct H; subst; auto.
    right.
    intros CONTRA. inv CONTRA; contradiction.
    right; intros CONTRA; inv CONTRA.
    right; intros CONTRA; inv CONTRA.
  Qed.

  Lemma aid_eq_dec_refl :
    forall (aid : AllocationId),
      true = aid_eq_dec aid aid.
  Proof.
    intros aid.
    destruct (aid_eq_dec aid aid); cbn; auto.
    exfalso; auto.
  Qed.

  #[global] Instance provenance_lt_trans : Transitive provenance_lt.
  Proof.
    unfold Transitive.
    intros x y z XY YZ.
    unfold provenance_lt in *.
    lia.
  Defined.

  Lemma provenance_lt_next_provenance :
    forall pr,
      provenance_lt pr (next_provenance pr).
  Proof.
    unfold provenance_lt, next_provenance.
    lia.
  Qed.

  Lemma provenance_lt_nrefl :
    forall pr,
      ~ provenance_lt pr pr.
  Proof.
    intros pr.
    unfold provenance_lt.
    lia.
  Qed.

  #[global] Instance provenance_lt_antisym : Antisymmetric Provenance eq provenance_lt.
  Proof.
    unfold Antisymmetric.
    intros x y XY YX.
    unfold provenance_lt in *.
    lia.
  Defined.

  Lemma next_provenance_neq :
    forall pr,
      pr <> next_provenance pr.
  Proof.
    intros pr.
    unfold next_provenance.
    lia.
  Qed.

  (* Debug *)
  Definition show_prov (pr : Prov) := Show.show pr.
  Definition show_provenance (pr : Provenance) := Show.show pr.
  Definition show_allocation_id (aid : AllocationId) := Show.show aid.
End FinPROV.

Module FinITOP : ITOP(Addr)(FinPROV)(FinPTOI).
  Import Addr.
  Import FinPROV.
  Import FinPTOI.

  Definition int_to_ptr (i : Z) (pr : Prov) : addr
    := (i, pr).

  Lemma int_to_ptr_provenance :
    forall (x : Z) (p : Prov) ,
      FinPROV.address_provenance (int_to_ptr x p) = p.
  Proof.
    intros x p.
    reflexivity.
  Qed.

  Lemma int_to_ptr_ptr_to_int :
    forall (a : addr) (p : Prov),
      address_provenance a = p ->
      int_to_ptr (ptr_to_int a) p = a.
  Proof.
    intros a p PROV.
    unfold int_to_ptr.
    unfold ptr_to_int.
    destruct a; cbn.
    inv PROV; cbn; auto.
  Qed.

  Lemma ptr_to_int_int_to_ptr :
    forall (x : Z) (p : Prov),
      ptr_to_int (int_to_ptr x p) = x.
  Proof.
    intros x p.
    reflexivity.
  Qed.
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

  Lemma sizeof_dtyp_i8 :
    sizeof_dtyp (DTYPE_I 8) = 1%N.
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
  Import MP.
  Import GEP.

  Import MemBytes.
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

    (** Heaps *)
    Definition Block := list Iptr.
    Definition Heap := IntMap Block.

    (** ** Memory stack
      The full notion of state manipulated by the monad is a pair of a [memory] and a [mem_stack].
     *)
    Record memory_stack' : Type :=
      mkMemoryStack
        { memory_stack_memory : memory;
          memory_stack_frame_stack : FrameStack;
          memory_stack_heap : Heap;
        }.

    Definition memory_stack := memory_stack'.

    (** Some operations on memory *)
    Definition set_byte_raw (mem : memory) (phys_addr : Z) (byte : mem_byte) : memory :=
      IM.add phys_addr byte mem.

    Definition read_byte_raw (mem : memory) (phys_addr : Z) : option mem_byte :=
      IM.find phys_addr mem.

    Lemma set_byte_raw_eq :
      forall (mem : memory) (byte : mem_byte) (x y : Z),
        x = y ->
        read_byte_raw (set_byte_raw mem x byte) y = Some byte.
    Proof.
      intros mem byte x y XY.
      apply IP.F.add_eq_o; auto.
    Qed.

    Lemma set_byte_raw_neq :
      forall (mem : memory) (byte : mem_byte) (x y : Z),
        x <> y ->
        read_byte_raw (set_byte_raw mem x byte) y = read_byte_raw mem y.
    Proof.
      intros mem byte x y XY.
      apply IP.F.add_neq_o; auto.
    Qed.

    Lemma read_byte_raw_add_all_index_out :
      forall (mem : memory) l z p,
        p < z \/ p >= z + Zlength l ->
        read_byte_raw (add_all_index l z mem) p = read_byte_raw mem p.
    Proof.
      intros mem l z p BOUNDS.
      unfold read_byte_raw.
      eapply lookup_add_all_index_out; eauto.
    Qed.

    Lemma read_byte_raw_add_all_index_in :
      forall (mem : memory) l z p v,
        z <= p <= z + Zlength l - 1 ->
        list_nth_z l (p - z) = Some v ->
        read_byte_raw (add_all_index l z mem) p = Some v.
    Proof.
      intros mem l z p v BOUNDS IN.
      unfold read_byte_raw.
      eapply lookup_add_all_index_in; eauto.
    Qed.

    Lemma read_byte_raw_add_all_index_in_exists :
      forall (mem : memory) l z p,
        z <= p <= z + Zlength l - 1 ->
        exists v, list_nth_z l (p - z) = Some v /\
               read_byte_raw (add_all_index l z mem) p = Some v.
    Proof.
      intros mem l z p IN.
      pose proof range_list_nth_z l (p - z) as H.
      forward H.
      lia.
      destruct H as [v NTH].
      exists v.

      split; auto.
      unfold read_byte_raw.
      eapply lookup_add_all_index_in; eauto.
    Qed.

    Lemma InA_In :
      forall mem ix e,
        SetoidList.InA (IM.eq_key_elt (elt:=mem_byte)) (ix, e) (IM.elements (elt:=mem_byte) mem) ->
        In (ix, e) (IM.elements (elt:=mem_byte) mem).
    Proof.
      intros mem.
      induction (IM.elements (elt:=mem_byte) mem);
        intros ix e INS.

      - exfalso. apply SetoidList.InA_nil in INS; auto.
      - apply SetoidList.InA_cons in INS.
        destruct INS as [INS | INS]; firstorder.
        cbn in *; subst.
        left; destruct a; reflexivity.
    Qed.

    Lemma read_byte_raw_next_memory_key :
      forall (mem : memory) ix,
        ix >= next_key mem ->
        read_byte_raw mem ix = None.
    Proof.
      intros mem ix H.
      unfold read_byte_raw.
      apply IP.F.not_find_in_iff.
      unfold next_key in *.
      intros IN.
      apply IP.F.elements_in_iff in IN.
      destruct IN as [e IN].

      pose proof (maximumBy_Z_correct (-1) (map fst (IM.elements (elt:=mem_byte) mem)) ix) as LE.
      forward LE.
      { apply InA_In in IN.
        replace ix with (fst (ix, e)) by auto.
        apply in_map; auto.
      }
      apply Zle_bool_imp_le in LE.
      lia.
    Qed.

    Lemma read_byte_raw_lt_next_memory_key :
      forall (mem : memory) ix v,
        read_byte_raw mem ix = Some v ->
        ix < next_key mem.
    Proof.
      intros mem ix H.
      intros FIND.
      pose proof (Z_lt_le_dec ix (next_key mem)) as [LT | GE]; auto.
      assert (read_byte_raw mem ix = None) as NONE.
      { apply read_byte_raw_next_memory_key.
        lia.
      }
      rewrite FIND in NONE.
      inv NONE.
    Qed.

  End Datatype_Definition.

  (* Convenient to make these opaque so they don't get unfolded *)
  #[global] Opaque set_byte_raw.
  #[global] Opaque read_byte_raw.


  Record MemState' :=
    mkMemState
      { ms_memory_stack : memory_stack;
        (* Used to keep track of allocation ids in use *)
        ms_provenance : Provenance;
      }.

  (* The kernel does not recognize yet that a parameter can be
  instantiated by an inductive type. Hint: you can rename the
  inductive type and give a definition to map the old name to the new
  name.
  *)
  Definition MemState := MemState'.

  Definition mem_state_memory_stack (ms : MemState) : memory_stack
    := ms.(ms_memory_stack).

  Definition MemState_get_memory := mem_state_memory_stack.
  Definition MemState_put_memory (mem' : memory_stack) (ms : MemState) : MemState :=
    let '(mkMemState mem prov) := ms in
    (mkMemState mem' prov).

  Definition mem_state_memory (ms : MemState) : memory
    := memory_stack_memory (MemState_get_memory ms).

  Definition mem_state_provenance (ms : MemState) : Provenance
    := ms.(ms_provenance).

  Definition MemState_get_provenance := mem_state_provenance.

  Definition mem_state_frame_stack (ms : MemState) : FrameStack
    := memory_stack_frame_stack ms.(ms_memory_stack).

  Definition mem_state_heap (ms : MemState) : Heap
    := memory_stack_heap ms.(ms_memory_stack).

  Definition read_byte_MemPropT (ptr : addr) : MemPropT memory_stack SByte :=
    let addr := ptr_to_int ptr in
    let pr := address_provenance ptr in
    mem_stack <- get_mem_state;;
    let mem := memory_stack_memory mem_stack in
    match read_byte_raw mem addr with
    | None => raise_ub "Reading from unallocated memory."
    | Some byte =>
        let aid := snd byte in
        if access_allowed pr aid
        then ret (fst byte)
        else
          raise_ub
            ("Read from memory with invalid provenance -- addr: " ++ Show.show addr ++ ", addr prov: " ++ show_prov pr ++ ", memory allocation id: " ++ Show.show (show_allocation_id aid) ++ " memory: " ++ Show.show (map (fun '(key, (_, aid)) => (key, show_allocation_id aid)) (IM.elements mem)))
    end.

  Definition addr_allocated_prop (ptr : addr) (aid : AllocationId) : MemPropT memory_stack bool :=
    mem <- get_mem_state;;
    match read_byte_raw (memory_stack_memory mem) (ptr_to_int ptr) with
    | None => ret false
    | Some (byte, aid') =>
        ret (proj_sumbool (aid_eq_dec aid aid'))
    end.

  Definition ptr_in_frame_prop (f : Frame) (ptr : addr) : Prop :=
    In (ptr_to_int ptr) f.

  Definition frame_eqv (f f' : Frame) : Prop :=
    forall ptr, ptr_in_frame_prop f ptr <-> ptr_in_frame_prop f' ptr.

  #[global] Instance frame_eqv_Equivalence : Equivalence frame_eqv.
  Proof.
    split.
    - intros f ptr.
      reflexivity.
    - intros f1 f2 EQV.
      unfold frame_eqv in *.
      firstorder.
    - intros x y z XY YZ.
      firstorder.
  Qed.

  Fixpoint FSIn (f : Frame) (fs : FrameStack) : Prop :=
    match fs with
    | Singleton f' => f' = f
    | Snoc fs f' => f' = f \/ FSIn f fs
    end.

  Fixpoint FSIn_eqv (f : Frame) (fs : FrameStack) : Prop :=
    match fs with
    | Singleton f' => frame_eqv f' f
    | Snoc fs f' => frame_eqv f' f \/ FSIn_eqv f fs
    end.

  Fixpoint FSNth_rel (R : relation Frame) (fs : FrameStack) (n : nat) (f : Frame) : Prop :=
    match n with
    | 0%nat =>
        match fs with
        | Singleton f' => R f' f
        | Snoc fs f' => R f' f
        end
    | S n =>
        match fs with
        | Singleton f' => False
        | Snoc fs f' => FSNth_rel R fs n f
        end
    end.

  Definition FSNth_eqv := FSNth_rel frame_eqv.

  Definition frame_stack_eqv (fs fs' : FrameStack) : Prop :=
    forall f n, FSNth_eqv fs n f <-> FSNth_eqv fs' n f.

  #[global] Instance frame_stack_eqv_Equivalence : Equivalence frame_stack_eqv.
  Proof.
    split; try firstorder.
    - intros x y z XY YZ.
      unfold frame_stack_eqv in *.
      intros f n.
      split; intros NTH.
      + apply YZ; apply XY; auto.
      + apply XY; apply YZ; auto.
  Qed.

  (* Check for the current frame *)
  Definition peek_frame_stack_prop (fs : FrameStack) (f : Frame) : Prop :=
    match fs with
    | Singleton f' => frame_eqv f f'
    | Snoc s f' => frame_eqv f f'
    end.

  Definition pop_frame_stack_prop (fs fs' : FrameStack) : Prop :=
    match fs with
    | Singleton f => False
    | Snoc s f => frame_stack_eqv s fs'
    end.

  Definition memory_stack_frame_stack_prop (mem : memory_stack) (fs : FrameStack) : Prop :=
    frame_stack_eqv (memory_stack_frame_stack mem) fs.

  Definition mem_state_frame_stack_prop (ms : MemState) (fs : FrameStack) : Prop :=
    memory_stack_frame_stack_prop (MemState_get_memory ms) fs.

  (** Heap *)
  Definition ptr_in_heap_prop (h : Heap) (root ptr : addr) : Prop
    := match IM.find (ptr_to_int root) h with
       | None => False
       | Some ptrs => In (ptr_to_int ptr) ptrs
       end.

  Definition root_in_heap_prop (h : Heap) (root : addr) : Prop
    := member (ptr_to_int root) h.

  Record heap_eqv (h h' : Heap) : Prop :=
    {
      heap_roots_eqv : forall root, root_in_heap_prop h root <-> root_in_heap_prop h' root;
      heap_ptrs_eqv : forall root ptr, ptr_in_heap_prop h root ptr <-> ptr_in_heap_prop h' root ptr;
    }.

  #[global] Instance root_in_heap_prop_Proper :
    Proper (heap_eqv ==> eq ==> iff) root_in_heap_prop.
  Proof.
    intros h h' HEAPEQ ptr ptr' PTREQ; subst.
    inv HEAPEQ.
    eauto.
  Qed.

  #[global] Instance ptr_in_heap_prop_Proper :
    Proper (heap_eqv ==> eq ==> eq ==> iff) ptr_in_heap_prop.
  Proof.
    intros h h' HEAPEQ root root' ROOTEQ ptr ptr' PTREQ; subst.
    inv HEAPEQ.
    eauto.
  Qed.

  #[global] Instance heap_Equivalence : Equivalence heap_eqv.
  Proof.
    split.
    - intros h; split.
      + intros root.
        reflexivity.
      + intros root ptr.
        reflexivity.
    - intros h1 h2 EQV.
      firstorder.
    - intros x y z XY YZ.
      split.
      + intros root.
        rewrite XY, YZ.
        reflexivity.
      + intros root ptr.
        rewrite XY, YZ.
        reflexivity.
  Qed.

  (* Memory stack's heap *)
  Definition memory_stack_heap_prop (ms : memory_stack) (h : Heap) : Prop
    := heap_eqv (memory_stack_heap ms) h.

  Definition mem_state_heap_prop (ms : MemState) (h : Heap) : Prop :=
    memory_stack_heap_prop (MemState_get_memory ms) h.

  (** Provenance / store ids *)
  Definition used_provenance_prop (ms : MemState) (pr : Provenance) : Prop :=
    provenance_lt pr (next_provenance (mem_state_provenance ms)).

  Definition get_fresh_provenance (ms : MemState) : Provenance :=
    let pr := mem_state_provenance ms in
    next_provenance pr.

  Lemma get_fresh_provenance_fresh :
    forall (ms : MemState),
      ~ used_provenance_prop ms (get_fresh_provenance ms).
  Proof.
    intros ms.
    unfold used_provenance_prop.
    destruct ms.
    cbn.
    unfold get_fresh_provenance.
    cbn.
    apply provenance_lt_nrefl.
  Qed.

  Definition mem_state_fresh_provenance (ms : MemState) : (Provenance * MemState)%type :=
    match ms with
    | mkMemState mem_stack pr =>
        let pr' := next_provenance pr in
        (pr', mkMemState mem_stack pr')
    end.

  Definition used_store_id_prop (ms : MemState) (sid : store_id) : Prop :=
    exists ptr byte aid,
      let mem := mem_state_memory ms in
      read_byte_raw mem ptr = Some (byte, aid) /\
        sbyte_sid byte = inr sid.

  Lemma mem_state_fresh_provenance_fresh :
    forall (ms ms' : MemState) (pr : Provenance),
      mem_state_fresh_provenance ms = (pr, ms') ->
      MemState_get_memory ms = MemState_get_memory ms' /\
        (forall pr, used_provenance_prop ms pr -> used_provenance_prop ms' pr) /\
      ~ used_provenance_prop ms pr /\ used_provenance_prop ms' pr.
  Proof.
    intros ms ms' pr MSFP.
    unfold mem_state_fresh_provenance in *.
    destruct ms; cbn in *; inv MSFP.
    split; [|split; [|split]].
    - reflexivity.
    - intros pr H.
      unfold used_provenance_prop in *.
      cbn in *.
      eapply provenance_lt_trans.
      apply H.
      apply provenance_lt_next_provenance.
    - intros CONTRA;
      unfold used_provenance_prop in *.
      cbn in CONTRA.
      eapply provenance_lt_nrefl; eauto.
    - unfold used_provenance_prop in *.
      cbn.
      apply provenance_lt_next_provenance.
  Qed.

  (** Extra frame stack lemmas *)
  Lemma frame_stack_eqv_snoc_sing_inv :
    forall fs f1 f2,
      frame_stack_eqv (Snoc fs f1) (Singleton f2) -> False.
  Proof.
    intros fs f1 f2 EQV.
    destruct fs.
    - unfold frame_stack_eqv in *.
      specialize (EQV f 1%nat).
      destruct EQV as [NTH1 NTH2].
      cbn in *.
      apply NTH1.
      reflexivity.
    - unfold frame_stack_eqv in *.
      specialize (EQV f 1%nat).
      destruct EQV as [NTH1 NTH2].
      cbn in *.
      apply NTH1.
      reflexivity.
  Qed.

  Lemma frame_stack_eqv_sing_snoc_inv :
    forall fs f1 f2,
      frame_stack_eqv (Singleton f2) (Snoc fs f1) -> False.
  Proof.
    intros fs f1 f2 EQV.
    destruct fs.
    - unfold frame_stack_eqv in *.
      specialize (EQV f 1%nat).
      destruct EQV as [NTH1 NTH2].
      cbn in *.
      apply NTH2.
      reflexivity.
    - unfold frame_stack_eqv in *.
      specialize (EQV f 1%nat).
      destruct EQV as [NTH1 NTH2].
      cbn in *.
      apply NTH2.
      reflexivity.
  Qed.

  Lemma FSNTH_rel_snoc :
    forall R fs f n x,
      FSNth_rel R (Snoc fs f) (S n) x =
        FSNth_rel R fs n x.
  Proof.
    intros R fs f n x.
    cbn. reflexivity.
  Qed.

  Lemma frame_stack_snoc_inv_fs :
    forall fs1 fs2 f1 f2,
      frame_stack_eqv (Snoc fs1 f1) (Snoc fs2 f2) ->
      frame_stack_eqv fs1 fs2.
  Proof.
    intros fs1 fs2 f1 f2 EQV.
    unfold frame_stack_eqv in *.
    intros f n.
    specialize (EQV f (S n)).
    setoid_rewrite FSNTH_rel_snoc in EQV.
    apply EQV.
  Qed.

  Lemma frame_stack_snoc_inv_f :
    forall fs1 fs2 f1 f2,
      frame_stack_eqv (Snoc fs1 f1) (Snoc fs2 f2) ->
      frame_eqv f1 f2.
  Proof.
    intros fs1 fs2 f1 f2 EQV.
    unfold frame_stack_eqv in *.
    specialize (EQV f2 0%nat).
    cbn in *.
    apply EQV.
    reflexivity.
  Qed.

  Lemma frame_stack_inv :
    forall fs1 fs2,
      frame_stack_eqv fs1 fs2 ->
      (exists fs1' fs2' f1 f2,
          fs1 = (Snoc fs1' f1) /\ fs2 = (Snoc fs2' f2) /\
            frame_stack_eqv fs1' fs2' /\
            frame_eqv f1 f2) \/
        (exists f1 f2,
            fs1 = Singleton f1 /\ fs2 = Singleton f2 /\
              frame_eqv f1 f2).
  Proof.
    intros fs1 fs2 EQV.
    destruct fs1, fs2.
    - right.
      do 2 eexists.
      split; eauto.
      split; eauto.
      specialize (EQV f 0%nat).
      cbn in EQV.
      symmetry.
      apply EQV.
      reflexivity.
    - exfalso; eapply frame_stack_eqv_sing_snoc_inv; eauto.
    - exfalso; eapply frame_stack_eqv_snoc_sing_inv; eauto.
    - left.
      do 4 eexists.
      split; eauto.
      split; eauto.

      split.
      + eapply frame_stack_snoc_inv_fs; eauto.
      + eapply frame_stack_snoc_inv_f; eauto.
  Qed.

  #[global] Instance peek_frame_stack_prop_Proper :
    Proper (frame_stack_eqv ==> frame_eqv ==> iff) peek_frame_stack_prop.
  Proof.
    unfold Proper, respectful.
    intros xs ys XSYS x y XY.
    eapply frame_stack_inv in XSYS as [XSYS | XSYS].
    - (* Singleton framestacks *)
      destruct XSYS as [fs1' [fs2' [f1 [f2 [X [Y [EQFS EQF]]]]]]].
      subst.
      cbn in *.
      rewrite EQF.
      rewrite XY.
      reflexivity.
    - (* Snoc framestacks *)
      destruct XSYS as [f1 [f2 [X [Y EQF]]]].
      subst.
      cbn in *.
      rewrite EQF.
      rewrite XY.
      reflexivity.
  Qed.

  #[global] Instance peek_frame_stack_prop_impl_Proper :
    Proper (frame_stack_eqv ==> frame_eqv ==> Basics.impl ) peek_frame_stack_prop.
  Proof.
    unfold Proper, respectful.
    intros xs ys XSYS x y XY.
    rewrite XY.
    rewrite XSYS.
    intros H; auto.
  Qed.

  #[global] Instance pop_frame_stack_prop_Proper :
    Proper (frame_stack_eqv ==> frame_stack_eqv ==> iff) pop_frame_stack_prop.
  Proof.
    unfold Proper, respectful.
    intros x y XY a b AB.
    eapply frame_stack_inv in XY as [XY | XY].
    - (* Singleton framestacks *)
      destruct XY as [fs1' [fs2' [f1 [f2 [X [Y [EQFS EQF]]]]]]].
      subst.
      cbn in *.
      rewrite EQFS.
      rewrite AB.
      reflexivity.
    - (* Snoc framestacks *)
      destruct XY as [f1 [f2 [X [Y EQF]]]].
      subst.
      cbn in *.
      reflexivity.
  Qed.

  #[global] Instance frame_eqv_cons_Proper :
    Proper (eq ==> frame_eqv ==> frame_eqv) cons.
  Proof.
    unfold Proper, respectful.
    intros ptr ptr' EQ f1 f2 EQV; subst.
    unfold frame_eqv in *.
    cbn in *; intros ptr; split; firstorder.
  Qed.

  Lemma MemState_get_put_memory :
    forall ms mem,
      MemState_get_memory (MemState_put_memory mem ms) = mem.
  Proof.
    intros ms mem.
    destruct ms.
    cbn.
    reflexivity.
  Qed.

  #[global] Instance MemState_memory_MemStateMem : MemStateMem MemState memory_stack :=
    {| ms_get_memory := MemState_get_memory;
      ms_put_memory := MemState_put_memory;
      ms_get_put_memory := MemState_get_put_memory;
    |}.

End FiniteMemoryModelSpecPrimitives.

Module FiniteMemoryModelExecPrimitives (LP : LLVMParams) (MP : MemoryParams LP) <: MemoryModelExecPrimitives LP MP.
  Module MMSP := FiniteMemoryModelSpecPrimitives LP MP.
  Module MemSpec := MakeMemoryModelSpec LP MP MMSP.
  Module MemExecM := MakeMemoryExecMonad LP MP MMSP MemSpec.
  Import MemExecM.

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
  Import MP.
  Import GEP.

  (* Convenient to make these opaque so they don't get unfolded *)
  Section MemoryPrimatives.
    Context {MemM : Type -> Type}.
    Context {Eff : Type -> Type}.
    (* Context `{Monad MemM}. *)
    (* Context `{MonadProvenance Provenance MemM}. *)
    (* Context `{MonadStoreID MemM}. *)
    (* Context `{MonadMemState MemState MemM}. *)
    (* Context `{RAISE_ERROR MemM} `{RAISE_UB MemM} `{RAISE_OOM MemM}. *)
    Context {ExtraState : Type}.
    Context `{MemMonad ExtraState MemM (itree Eff)}.

    (*** Data types *)
    Definition memory_empty : memory := IntMaps.empty.
    Definition frame_empty : FrameStack := Singleton [].
    Definition heap_empty : Heap := IntMaps.empty.

    Definition empty_memory_stack : memory_stack :=
      mkMemoryStack memory_empty frame_empty heap_empty.

    Definition initial_memory_state : MemState :=
      mkMemState empty_memory_stack initial_provenance.

    Definition initial_frame : Frame :=
      [].

    Definition initial_heap : Heap := IntMaps.empty.

    (** ** Fresh key getters *)

    (* Get the next key in the memory *)
    Definition next_memory_key (m : memory_stack) : Z :=
      next_key (memory_stack_memory m).

    Lemma next_memory_key_next_key :
      forall m f h,
        next_memory_key (mkMemoryStack m f h) = next_key m.
    Proof.
      auto.
    Qed.

    Lemma next_memory_key_next_key_memory_stack_memory :
      forall ms,
        next_memory_key ms = next_key (memory_stack_memory ms).
    Proof.
      auto.
    Qed.

    (*** Primitives on memory *)
    (** Reads *)
    Definition read_byte `{MemMonad ExtraState MemM (itree Eff)} (ptr : addr) : MemM SByte :=
      let addr := ptr_to_int ptr in
      let pr := address_provenance ptr in
      ms <- get_mem_state;;
      let mem := mem_state_memory ms in
      match read_byte_raw mem addr with
      | None => raise_ub "Reading from unallocated memory."
      | Some (byte, aid) =>
          if access_allowed pr aid
          then ret byte

          else
            raise_ub
              ("Read from memory with invalid provenance -- addr: " ++ Show.show addr ++ ", addr prov: " ++ show_prov pr ++ ", memory allocation id: " ++ Show.show (show_allocation_id aid) ++ " memory: " ++ Show.show (map (fun '(key, (_, aid)) => (key, show_allocation_id aid)) (IM.elements mem)))
      end.

    (** Writes *)
    Definition write_byte `{MemMonad ExtraState MemM (itree Eff)} (ptr : addr) (byte : SByte) : MemM unit :=
      let addr := ptr_to_int ptr in
      let pr := address_provenance ptr in
      ms <- get_mem_state;;
      let mem := mem_state_memory ms in
      let prov := mem_state_provenance ms in
      match read_byte_raw mem addr with
      | None => raise_ub "Writing to unallocated memory"
      | Some (_, aid) =>
          if access_allowed pr aid
          then
            let mem' := set_byte_raw mem addr (byte, aid) in
            let fs := mem_state_frame_stack ms in
            let h := mem_state_heap ms in
            put_mem_state (mkMemState (mkMemoryStack mem' fs h) prov)
          else raise_ub
                 ("Trying to write to memory with invalid provenance -- addr: " ++ Show.show addr ++ ", addr prov: " ++ show_prov pr ++ ", memory allocation id: " ++ show_allocation_id aid ++ " Memory: " ++ Show.show (map (fun '(key, (_, aid)) => (key, show_allocation_id aid)) (IM.elements mem)))
      end.

    (** Allocations *)
    Definition addr_allocated `{MemMonad ExtraState MemM (itree Eff)} (ptr : addr) (aid : AllocationId) : MemM bool :=
      ms <- get_mem_state;;
      match read_byte_raw (mem_state_memory ms) (ptr_to_int ptr) with
      | None => ret false
      | Some (byte, aid') =>
          ret (proj_sumbool (aid_eq_dec aid aid'))
      end.

    (* Register a concrete address in a frame *)
    Definition add_to_frame (m : memory_stack) (k : Z) : memory_stack :=
      let '(mkMemoryStack m s h) := m in
      match s with
      | Singleton f => mkMemoryStack m (Singleton (k :: f)) h
      | Snoc s f => mkMemoryStack m (Snoc s (k :: f)) h
      end.

    (* Register a list of concrete addresses in a frame *)
    Definition add_all_to_frame (m : memory_stack) (ks : list Z) : memory_stack
      := fold_left (fun ms k => add_to_frame ms k) ks m.

    (* Register a ptr with the heap *)
    Definition add_to_heap (m : memory_stack) (root : Z) (ptr : Z) : memory_stack :=
      let '(mkMemoryStack m s h) := m in
      let h' := add_with root ptr ret cons h in
      mkMemoryStack m s h'.

    (* Register a list of concrete addresses in the heap *)
    Definition add_all_to_heap' (m : memory_stack) (root : Z) (ks : list Z) : memory_stack
      := fold_left (fun ms k => add_to_heap ms root k) ks m.

    Definition add_all_to_heap (m : memory_stack) (ks : list Z) : memory_stack
      := match ks with
         | [] => m
         | (root :: _) =>
             add_all_to_heap' m root ks
         end.

    Lemma add_to_frame_preserves_memory :
      forall ms k,
        memory_stack_memory (add_to_frame ms k) = memory_stack_memory ms.
    Proof.
      intros [m fs] k.
      destruct fs; auto.
    Qed.

    Lemma add_to_heap_preserves_memory :
      forall ms root k,
        memory_stack_memory (add_to_heap ms root k) = memory_stack_memory ms.
    Proof.
      intros [m fs] root k.
      destruct fs; auto.
    Qed.

    Lemma add_to_frame_preserves_heap :
      forall ms k,
        memory_stack_heap (add_to_frame ms k) = memory_stack_heap ms.
    Proof.
      intros [m fs] k.
      destruct fs; auto.
    Qed.

    Lemma add_to_heap_preserves_frame_stack :
      forall ms root k,
        memory_stack_frame_stack (add_to_heap ms root k) = memory_stack_frame_stack ms.
    Proof.
      intros [m fs] root k.
      destruct fs; auto.
    Qed.

    Lemma add_all_to_frame_preserves_memory :
      forall ms ks,
        memory_stack_memory (add_all_to_frame ms ks) = memory_stack_memory ms.
    Proof.
      intros ms ks; revert ms;
        induction ks; intros ms; auto.
      cbn in *. unfold add_all_to_frame in IHks.
      specialize (IHks (add_to_frame ms a)).
      rewrite add_to_frame_preserves_memory in IHks.
      auto.
    Qed.

    Lemma add_all_to_heap'_preserves_memory :
      forall ms root ks,
        memory_stack_memory (add_all_to_heap' ms root ks) = memory_stack_memory ms.
    Proof.
      intros ms root ks; revert ms root;
        induction ks; intros ms root; auto.
      specialize (IHks (add_to_heap ms root a) root).
      cbn in *.
      unfold add_all_to_heap' in *.
      rewrite add_to_heap_preserves_memory in IHks.
      auto.
    Qed.

    Lemma add_all_to_heap_preserves_memory :
      forall ms ks,
        memory_stack_memory (add_all_to_heap ms ks) = memory_stack_memory ms.
    Proof.
      intros ms [|a ks]; auto.
      apply add_all_to_heap'_preserves_memory.
    Qed.

    Lemma add_all_to_frame_preserves_heap :
      forall ms ks,
        memory_stack_heap (add_all_to_frame ms ks) = memory_stack_heap ms.
    Proof.
      intros ms ks; revert ms;
        induction ks; intros ms; auto.
      cbn in *. unfold add_all_to_frame in IHks.
      specialize (IHks (add_to_frame ms a)).
      rewrite add_to_frame_preserves_heap in IHks.
      auto.
    Qed.

    Lemma add_all_to_heap'_preserves_frame_stack :
      forall ms root ks,
        memory_stack_frame_stack (add_all_to_heap' ms root ks) = memory_stack_frame_stack ms.
    Proof.
      intros ms root ks; revert root ms;
        induction ks; intros root ms; auto.
      cbn in *. unfold add_all_to_heap' in IHks.
      specialize (IHks root (add_to_heap ms root a)).
      rewrite add_to_heap_preserves_frame_stack in IHks.
      auto.
    Qed.

    Lemma add_all_to_heap_preserves_frame_stack :
      forall ms ks,
        memory_stack_frame_stack (add_all_to_heap ms ks) = memory_stack_frame_stack ms.
    Proof.
      intros ms [|a ks]; auto.
      apply add_all_to_heap'_preserves_frame_stack.
    Qed.

    Lemma add_all_to_frame_nil_preserves_frames :
      forall ms,
        memory_stack_frame_stack (add_all_to_frame ms []) = memory_stack_frame_stack ms.
    Proof.
      intros [m fs].
      destruct fs; auto.
    Qed.

    Lemma add_all_to_frame_nil :
      forall ms ms',
        add_all_to_frame ms [] = ms' ->
        ms = ms'.
    Proof.
      (* TODO: move to pre opaque *)
      Transparent add_all_to_frame.
      unfold add_all_to_frame.
      Opaque add_all_to_frame.
      cbn; eauto.
    Qed.

    Lemma add_all_to_frame_cons_inv :
      forall ptr ptrs ms ms'',
        add_all_to_frame ms (ptr :: ptrs) = ms'' ->
        exists ms',
          add_to_frame ms ptr = ms' /\
            add_all_to_frame ms' ptrs = ms''.
    Proof.
      (* TODO: move to pre opaque *)
      Transparent add_all_to_frame.
      unfold add_all_to_frame.
      Opaque add_all_to_frame.
      cbn; eauto.
    Qed.

    Lemma add_all_to_heap'_cons_inv :
      forall ptr ptrs root ms ms'',
        add_all_to_heap' ms root (ptr :: ptrs) = ms'' ->
        exists ms',
          add_to_heap ms root ptr = ms' /\
            add_all_to_heap' ms' root ptrs = ms''.
    Proof.
      cbn; eauto.
    Qed.

    Lemma add_all_to_heap_cons_inv :
      forall ptr ptrs ms ms'',
        add_all_to_heap ms (ptr :: ptrs) = ms'' ->
        exists ms',
          add_to_heap ms ptr ptr = ms' /\
            add_all_to_heap' ms' ptr ptrs = ms''.
    Proof.
      cbn; eauto.
    Qed.

    Lemma add_all_to_frame_cons :
      forall ptr ptrs ms ms' ms'',
        add_to_frame ms ptr = ms' ->
        add_all_to_frame ms' ptrs = ms'' ->
        add_all_to_frame ms (ptr :: ptrs) = ms''.
    Proof.
      (* TODO: move to pre opaque *)
      Transparent add_all_to_frame.
      unfold add_all_to_frame.
      Opaque add_all_to_frame.

      intros ptr ptrs ms ms' ms'' ADD ADD_ALL.
      cbn; subst; eauto.
    Qed.

    Lemma add_all_to_heap_cons :
      forall ptr ptrs root ms ms' ms'',
        add_to_heap ms root ptr = ms' ->
        add_all_to_heap' ms' root ptrs = ms'' ->
        add_all_to_heap' ms root (ptr :: ptrs) = ms''.
    Proof.
      intros ptr ptrs ms ms' ms'' ADD ADD_ALL.
      cbn; subst; eauto.
    Qed.

    Lemma add_to_frame_add_all_to_frame :
      forall ptr ms,
        add_to_frame ms ptr = add_all_to_frame ms [ptr].
    Proof.
      intros ptr ms.
      erewrite add_all_to_frame_cons.
      reflexivity.
      reflexivity.
      symmetry.
      apply add_all_to_frame_nil.
      reflexivity.
    Qed.

    Lemma add_to_heap_add_all_to_heap :
      forall ptr root ms,
        add_to_heap ms root ptr = add_all_to_heap' ms root [ptr].
    Proof.
      intros ptr root ms.
      erewrite add_all_to_heap_cons.
      reflexivity.
      reflexivity.
      symmetry.
      reflexivity.
    Qed.

    Lemma add_to_frame_swap :
      forall ptr1 ptr2 ms ms1' ms2' ms1'' ms2'',
        add_to_frame ms ptr1 = ms1' ->
        add_to_frame ms1' ptr2 = ms1'' ->
        add_to_frame ms ptr2 = ms2' ->
        add_to_frame ms2' ptr1 = ms2'' ->
        frame_stack_eqv (memory_stack_frame_stack ms1'') (memory_stack_frame_stack ms2'').
    Proof.
      intros ptr1 ptr2 ms ms1' ms2' ms1'' ms2'' ADD1 ADD1' ADD2 ADD2'.
      destruct ms, ms1', ms2', ms1'', ms2''.
      cbn in *.
      repeat break_match_hyp; subst;
        inv ADD1; inv ADD1'; inv ADD2; inv ADD2'.

      - unfold frame_stack_eqv.
        intros f n.
        destruct n; cbn; [|tauto].

        split; intros EQV.
        + unfold frame_eqv in *; cbn in *.
          intros ptr; split; firstorder.
        + unfold frame_eqv in *; cbn in *.
          intros ptr; split; firstorder.
      - unfold frame_stack_eqv.
        intros f' n.
        destruct n; cbn; [|tauto].

        split; intros EQV.
        + unfold frame_eqv in *; cbn in *.
          intros ptr; split; firstorder.
        + unfold frame_eqv in *; cbn in *.
          intros ptr; split; firstorder.
    Qed.

    Lemma add_to_heap_swap :
      forall ptr1 ptr2 root ms ms1' ms2' ms1'' ms2'',
        add_to_heap ms root ptr1 = ms1' ->
        add_to_heap ms1' root ptr2 = ms1'' ->
        add_to_heap ms root ptr2 = ms2' ->
        add_to_heap ms2' root ptr1 = ms2'' ->
        heap_eqv (memory_stack_heap ms1'') (memory_stack_heap ms2'').
    Proof.
      intros ptr1 ptr2 root ms ms1' ms2' ms1'' ms2'' ADD1 ADD1' ADD2 ADD2'.
      destruct ms, ms1', ms2', ms1'', ms2''.
      cbn in *.
      repeat break_match_hyp; subst;
        inv ADD1; inv ADD1'; inv ADD2; inv ADD2'.

      - split.
        { intros root'.
          unfold root_in_heap_prop.
          split; intros ROOT.
          - destruct (Z.eq_dec (ptr_to_int root') root) as [EQR | NEQR].
            + subst.
              unfold add_with in *.
              break_inner_match.
              { rewrite IP.F.add_eq_o in *; auto.
                apply member_add_eq.
              }
              { rewrite IP.F.add_eq_o in *; auto.
                apply member_add_eq.
              }
            + unfold add_with in *.
              break_inner_match.
              { rewrite IP.F.add_eq_o in *; auto.
                do 2 apply member_add_preserved.
                do 2 apply member_add_ineq in ROOT; auto.
              }
              { rewrite IP.F.add_eq_o in *; auto.
                do 2 apply member_add_preserved.
                do 2 apply member_add_ineq in ROOT; auto.
              }
          - destruct (Z.eq_dec (ptr_to_int root') root) as [EQR | NEQR].
            + subst.
              unfold add_with in *.
              break_inner_match.
              { rewrite IP.F.add_eq_o in *; auto.
                apply member_add_eq.
              }
              { rewrite IP.F.add_eq_o in *; auto.
                apply member_add_eq.
              }
            + unfold add_with in *.
              break_inner_match.
              { rewrite IP.F.add_eq_o in *; auto.
                do 2 apply member_add_preserved.
                do 2 apply member_add_ineq in ROOT; auto.
              }
              { rewrite IP.F.add_eq_o in *; auto.
                do 2 apply member_add_preserved.
                do 2 apply member_add_ineq in ROOT; auto.
              }
        }
        
        intros root' a.
        unfold ptr_in_heap_prop in *.
        split; intros EQV.
        + destruct (Z.eq_dec (ptr_to_int root') root) as [EQR | NEQR].
          * subst.
            unfold add_with in *.
            break_inner_match;
              rewrite IP.F.add_eq_o in *; auto;
              rewrite IP.F.add_eq_o in *; auto;
              firstorder.
          * subst.
            unfold add_with in *.
            break_inner_match.
            { rewrite IP.F.add_eq_o in *; auto.
              rewrite IP.F.add_neq_o in *; auto.
              rewrite IP.F.add_neq_o in *; auto.
            }
            { rewrite IP.F.add_eq_o in *; auto.
              rewrite IP.F.add_neq_o in *; auto.
              rewrite IP.F.add_neq_o in *; auto.
            }
        + destruct (Z.eq_dec (ptr_to_int root') root) as [EQR | NEQR].
          * subst.
            unfold add_with in *.
            break_inner_match;
              rewrite IP.F.add_eq_o in *; auto;
              rewrite IP.F.add_eq_o in *; auto;
              firstorder.
          * subst.
            unfold add_with in *.
            break_inner_match.
            { rewrite IP.F.add_eq_o in *; auto.
              rewrite IP.F.add_neq_o in *; auto.
              rewrite IP.F.add_neq_o in *; auto.
            }
            { rewrite IP.F.add_eq_o in *; auto.
              rewrite IP.F.add_neq_o in *; auto.
              rewrite IP.F.add_neq_o in *; auto.
            }
    Qed.

    (* TODO: move this *)
    #[global] Instance ptr_in_frame_prop_int_Proper :
      Proper (frame_eqv ==> (fun a b => ptr_to_int a = ptr_to_int b) ==> iff) ptr_in_frame_prop.
    Proof.
      unfold Proper, respectful.
      intros x y XY a b AB.
      unfold frame_eqv in *.
      unfold ptr_in_frame_prop in *.
      rewrite AB; auto.
    Qed.

    #[global] Instance ptr_in_frame_prop_Proper :
      Proper (frame_eqv ==> eq ==> iff) ptr_in_frame_prop.
    Proof.
      unfold Proper, respectful.
      intros x y XY a b AB; subst.
      unfold frame_eqv in *.
      auto.
    Qed.

    #[global] Instance frame_stack_eqv_add_ptr_to_frame_Proper :
      Proper (frame_eqv ==> eq ==> frame_eqv ==> iff) add_ptr_to_frame.
    Proof.
      unfold Proper, respectful.
      intros x y XY ptr ptr' TU r s RS; subst.

      split; intros ADD.
      - (* unfold frame_stack_eqv in *. *)
        (* unfold FSNth_eqv in *. *)
        inv ADD.
        split.
        + intros ptr'0 DISJOINT.
          split; intros IN.
          * rewrite <- RS.
            apply old_frame_lu0; eauto.
            rewrite XY.
            auto.
          * rewrite <- XY.
            apply old_frame_lu0; eauto.
            rewrite RS.
            auto.
        + rewrite <- RS.
          auto.
      - inv ADD.
        split.
        + intros ptr'0 DISJOINT.
          split; intros IN.
          * rewrite RS.
            apply old_frame_lu0; eauto.
            rewrite <- XY.
            auto.
          * rewrite XY.
            apply old_frame_lu0; eauto.
            rewrite <- RS.
            auto.
        + rewrite RS.
          auto.
    Qed.

    #[global] Instance frame_stack_eqv_add_ptr_to_frame_stack_Proper :
      Proper (frame_stack_eqv ==> eq ==> frame_stack_eqv ==> iff) add_ptr_to_frame_stack.
    Proof.
      unfold Proper, respectful.
      intros x y XY ptr ptr' TU r s RS; subst.

      split; intros ADD.
      - (* unfold frame_stack_eqv in *. *)
        (* unfold FSNth_eqv in *. *)

        unfold add_ptr_to_frame_stack in ADD.
        unfold add_ptr_to_frame_stack.
        intros f PEEK.

        rewrite <- XY in PEEK.
        specialize (ADD f PEEK).
        destruct ADD as [f' [ADD [PEEK' POP]]].
        eexists.
        split; eauto.
        split; [rewrite <- RS; eauto|].

        intros fs1_pop.
        rewrite <- XY.
        rewrite <- RS.
        auto.
      - unfold add_ptr_to_frame_stack in ADD.
        unfold add_ptr_to_frame_stack.
        intros f PEEK.

        rewrite XY in PEEK.
        specialize (ADD f PEEK).
        destruct ADD as [f' [ADD [PEEK' POP]]].
        eexists.
        split; eauto.
        split; [rewrite RS; eauto|].

        intros fs1_pop.
        rewrite XY.
        rewrite RS.
        auto.
    Qed.

    #[global] Instance heap_eqv_ptr_in_head_prop_Proper :
      Proper (heap_eqv ==> eq ==> eq ==> iff) ptr_in_heap_prop.
    Proof.
      unfold Proper, respectful.
      intros x y XY root root' EQR ptr ptr' EQPTR; subst.
      rewrite XY.
      reflexivity.
    Qed.

    #[global] Instance heap_eqv_add_ptr_to_heap_Proper :
      Proper (heap_eqv ==> eq ==> eq ==> heap_eqv ==> iff) add_ptr_to_heap.
    Proof.
      unfold Proper, respectful.
      intros x y XY root root' EQR ptr ptr' EQPTR r s RS; subst.

      split; intros ADD.
      - (* unfold heap_eqv in *. *)
        (* unfold FSNth_eqv in *. *)
        destruct ADD as [OLD NEW].
        split.
        + intros ptr'0 DISJOINT root.
          rewrite <- RS.
          rewrite <- XY.
          auto.
        + intros root'0 DISJOINT ptr'0.
          rewrite <- RS.
          rewrite <- XY.
          auto.
        + intros ptr'0 DISJOINT.
          rewrite <- RS.
          rewrite <- XY.
          auto.
        + rewrite <- RS.
          auto.
        + rewrite <- RS.
          auto.
      - destruct ADD as [OLD NEW].
        split.
        + intros ptr'0 DISJOINT root.
          rewrite RS.
          rewrite XY.
          auto.
        + intros ptr'0 DISJOINT root.
          rewrite RS.
          rewrite XY.
          auto.
        + intros root'0 DISJOINT.
          rewrite XY.
          rewrite RS.
          auto.
        + rewrite RS.
          auto.
        + rewrite RS.
          auto.
    Qed.

    #[global] Instance frame_stack_eqv_add_ptrs_to_frame_stack_Proper :
      Proper (frame_stack_eqv ==> eq ==> frame_stack_eqv ==> iff) add_ptrs_to_frame_stack.
    Proof.
      unfold Proper, respectful.
      intros x y XY ptrs ptrs' TU r s RS; subst.

      split; intros ADD.
      - revert x y XY r s RS ADD.
        induction ptrs' as [|a ptrs];
          intros x y XY r s RS ADD;
          subst.
        + cbn in *; subst.
          rewrite <- XY.
          rewrite <- RS.
          auto.
        + cbn in *.
          destruct ADD as [fs' [ADDPTRS ADD]].
          eexists.
          rewrite <- RS; split; eauto.

          eapply IHptrs; eauto.
          reflexivity.
      - revert x y XY r s RS ADD.
        induction ptrs' as [|a ptrs];
          intros x y XY r s RS ADD;
          subst.
        + cbn in *; subst.
          rewrite XY.
          rewrite RS.
          auto.
        + cbn in *.
          destruct ADD as [fs' [ADDPTRS ADD]].
          eexists.
          rewrite RS; split; eauto.

          eapply IHptrs; eauto.
          reflexivity.
    Qed.

    #[global] Instance heap_eqv_add_ptrs_to_heap'_Proper :
      Proper (heap_eqv ==> eq ==> eq ==> heap_eqv ==> iff) add_ptrs_to_heap'.
    Proof.
      unfold Proper, respectful.
      intros x y XY root root' ROOTS ptrs ptrs' TU r s RS; subst.

      split; intros ADD.
      - revert x y XY r s RS ADD.
        induction ptrs' as [|a ptrs];
          intros x y XY r s RS ADD;
          subst.
        + cbn in *; subst.
          rewrite <- XY.
          rewrite <- RS.
          auto.
        + cbn in *.
          destruct ADD as [h' [ADDPTRS ADD]].
          eexists.
          rewrite <- RS; split; eauto.

          eapply IHptrs; eauto.
          reflexivity.
      - revert x y XY r s RS ADD.
        induction ptrs' as [|a ptrs];
          intros x y XY r s RS ADD;
          subst.
        + cbn in *; subst.
          rewrite XY.
          rewrite RS.
          auto.
        + cbn in *.
          destruct ADD as [h' [ADDPTRS ADD]].
          eexists.
          rewrite RS; split; eauto.

          eapply IHptrs; eauto.
          reflexivity.
    Qed.

    #[global] Instance heap_eqv_add_ptrs_to_heap_Proper :
      Proper (heap_eqv ==> eq ==> heap_eqv ==> iff) add_ptrs_to_heap.
    Proof.
      unfold Proper, respectful.
      intros x y XY ptrs ptrs' TU r s RS; subst.
      destruct ptrs'.
      - cbn. rewrite XY, RS.
        reflexivity.
      - unfold add_ptrs_to_heap.
        rewrite XY, RS.
        reflexivity.
    Qed.

    (* TODO: move this? *)
    Lemma disjoint_ptr_byte_dec :
      forall p1 p2,
        {disjoint_ptr_byte p1 p2} + { ~ disjoint_ptr_byte p1 p2}.
    Proof.
      intros p1 p2.
      unfold disjoint_ptr_byte.
      pose proof Z.eq_dec (ptr_to_int p1) (ptr_to_int p2) as [EQ | NEQ].
      - rewrite EQ.
        right.
        intros CONTRA.
        contradiction.
      - left; auto.
    Qed.

    Lemma add_ptr_to_frame_inv :
      forall ptr ptr' f f',
        add_ptr_to_frame f ptr f' ->
        ptr_in_frame_prop f' ptr' ->
        ptr_in_frame_prop f ptr' \/ ptr_to_int ptr = ptr_to_int ptr'.
    Proof.
      intros ptr ptr' f f' F F'.
      inv F.
      pose proof disjoint_ptr_byte_dec ptr ptr' as [DISJOINT | NDISJOINT].
      - specialize (old_frame_lu0 _ DISJOINT).
        left.
        apply old_frame_lu0; auto.
      - unfold disjoint_ptr_byte in NDISJOINT.
        assert (ptr_to_int ptr = ptr_to_int ptr') as EQ by lia.
        right; auto.
    Qed.

    Lemma add_ptr_to_heap_inv :
      forall ptr ptr' root root' f f',
        add_ptr_to_heap f root ptr f' ->
        ptr_in_heap_prop f' root' ptr' ->
        ptr_in_heap_prop f root' ptr' \/ (ptr_to_int ptr = ptr_to_int ptr' /\ ptr_to_int root = ptr_to_int root').
    Proof.
      intros ptr ptr' root root' f f' F F'.
      inv F.
      pose proof disjoint_ptr_byte_dec ptr ptr' as [DISJOINT | NDISJOINT].
      - specialize (old_heap_lu0 _ DISJOINT).
        left.
        apply old_heap_lu0; auto.
      - unfold disjoint_ptr_byte in NDISJOINT.
        assert (ptr_to_int ptr = ptr_to_int ptr') as EQ by lia.
        pose proof disjoint_ptr_byte_dec root root' as [DISJOINT' | NDISJOINT'].
        + left.
          apply old_heap_lu_different_root0; auto.
        + unfold disjoint_ptr_byte in NDISJOINT'.
          assert (ptr_to_int root = ptr_to_int root') as EQR by lia.
          right; firstorder.
    Qed.

    Lemma add_ptr_to_frame_eqv :
      forall ptr f f1 f2,
        add_ptr_to_frame f ptr f1 ->
        add_ptr_to_frame f ptr f2 ->
        frame_eqv f1 f2.
    Proof.
      intros ptr f f1 f2 F1 F2.
      unfold frame_eqv.
      intros ptr0.
      split; intros IN.
      - eapply add_ptr_to_frame_inv in IN; eauto.
        destruct IN as [IN | IN].
        + destruct F2.
          pose proof disjoint_ptr_byte_dec ptr ptr0 as [DISJOINT | NDISJOINT].
          * eapply old_frame_lu0; eauto.
          * unfold disjoint_ptr_byte in NDISJOINT.
            assert (ptr_to_int ptr = ptr_to_int ptr0) as EQ by lia.
            unfold ptr_in_frame_prop in *.
            rewrite <- EQ.
            auto.
        + destruct F2.
          unfold ptr_in_frame_prop in *.
          rewrite <- IN.
          auto.
      - eapply add_ptr_to_frame_inv in IN; eauto.
        destruct IN as [IN | IN].
        + destruct F1.
          pose proof disjoint_ptr_byte_dec ptr ptr0 as [DISJOINT | NDISJOINT].
          * eapply old_frame_lu0; eauto.
          * unfold disjoint_ptr_byte in NDISJOINT.
            assert (ptr_to_int ptr = ptr_to_int ptr0) as EQ by lia.
            unfold ptr_in_frame_prop in *.
            rewrite <- EQ.
            auto.
        + destruct F1.
          unfold ptr_in_frame_prop in *.
          rewrite <- IN.
          auto.
    Qed.

    Lemma add_ptr_to_frame_stack_eqv_S :
      forall ptr f f' fs fs',
        add_ptr_to_frame_stack (Snoc fs f) ptr (Snoc fs' f') ->
        add_ptr_to_frame f ptr f' /\ frame_stack_eqv fs fs'.
    Proof.
      intros ptr f f' fs fs' ADD.
      unfold add_ptr_to_frame_stack in *.
      specialize (ADD f).
      forward ADD; [cbn; reflexivity|].
      destruct ADD as [f1 [ADD [PEEK POP]]].
      cbn in PEEK.
      split.
      - rewrite PEEK in ADD; auto.
      - cbn in POP.
        specialize (POP fs').
        apply POP; reflexivity.
    Qed.

    Lemma add_ptr_to_frame_stack_eqv :
      forall ptr fs fs1 fs2,
        add_ptr_to_frame_stack fs ptr fs1 ->
        add_ptr_to_frame_stack fs ptr fs2 ->
        frame_stack_eqv fs1 fs2.
    Proof.
      intros ptr fs fs1 fs2 F1 F2.
      unfold add_ptr_to_frame_stack in *.
      intros f n.

      revert ptr f n fs fs2 F1 F2.
      induction fs1 as [f1 | fs1 IHF1 f1];
        intros ptr f n fs fs2 F1 F2;
        destruct fs2 as [f2 | fs2 f2].

      - cbn. destruct n; [|reflexivity].
        destruct fs as [f' | fs' f'].
        + specialize (F1 f').
          forward F1; [cbn; reflexivity|].
          destruct F1 as [f1' [ADD1 [PEEK1 POP1]]].

          specialize (F2 f').
          forward F2; [cbn; reflexivity|].
          destruct F2 as [f2' [ADD2 [PEEK2 POP2]]].

          cbn in *.
          pose proof (add_ptr_to_frame_eqv _ _ _ _ ADD1 ADD2) as EQV12.

          rewrite <- PEEK1.
          rewrite <- PEEK2.
          rewrite EQV12.
          reflexivity.
        + specialize (F1 f').
          forward F1; [cbn; reflexivity|].
          destruct F1 as [f1' [ADD1 [PEEK1 POP1]]].

          specialize (F2 f').
          forward F2; [cbn; reflexivity|].
          destruct F2 as [f2' [ADD2 [PEEK2 POP2]]].

          cbn in *.
          pose proof (add_ptr_to_frame_eqv _ _ _ _ ADD1 ADD2) as EQV12.

          rewrite <- PEEK1.
          rewrite <- PEEK2.
          rewrite EQV12.
          reflexivity.
      - destruct fs as [f' | fs' f'].
        + specialize (F2 f').
          forward F2; [cbn; reflexivity|].
          destruct F2 as [f2' [ADD2 [PEEK2 POP2]]].

          cbn in *.
          exfalso; eapply POP2; reflexivity.
        + specialize (F1 f').
          forward F1; [cbn; reflexivity|].
          destruct F1 as [f1' [ADD1 [PEEK1 POP1]]].

          cbn in *.
          exfalso; eapply POP1; reflexivity.
      - destruct fs as [f' | fs' f'].
        + specialize (F1 f').
          forward F1; [cbn; reflexivity|].
          destruct F1 as [f1' [ADD1 [PEEK1 POP1]]].

          cbn in *.
          exfalso; eapply POP1; reflexivity.
        + specialize (F2 f').
          forward F2; [cbn; reflexivity|].
          destruct F2 as [f2' [ADD2 [PEEK2 POP2]]].

          cbn in *.
          exfalso; eapply POP2; reflexivity.
      - destruct fs as [f' | fs' f'].
        + specialize (F1 f').
          forward F1; [cbn; reflexivity|].
          destruct F1 as [f1' [ADD1 [PEEK1 POP1]]].

          cbn in *.
          exfalso; eapply POP1; reflexivity.
        + specialize (F1 f').
          forward F1; [cbn; reflexivity|].
          destruct F1 as [f1' [ADD1 [PEEK1 POP1]]].

          specialize (F2 f').
          forward F2; [cbn; reflexivity|].
          destruct F2 as [f2' [ADD2 [PEEK2 POP2]]].

          pose proof (add_ptr_to_frame_eqv _ _ _ _ ADD1 ADD2) as EQV12.

          cbn in *.
          destruct n.
          * rewrite <- PEEK1.
            rewrite <- PEEK2.
            rewrite EQV12; reflexivity.
          * eapply POP1.
            eapply POP2.
            reflexivity.
    Qed.

    Lemma add_ptrs_to_frame_eqv :
      forall ptrs fs fs1 fs2,
        add_ptrs_to_frame_stack fs ptrs fs1 ->
        add_ptrs_to_frame_stack fs ptrs fs2 ->
        frame_stack_eqv fs1 fs2.
    Proof.
      induction ptrs;
        intros fs fs1 fs2 ADD1 ADD2.
      - cbn in *.
        rewrite <- ADD1, ADD2.
        reflexivity.
      - cbn in *.
        destruct ADD1 as [fs1' [ADDPTRS1 ADD1]].
        destruct ADD2 as [fs2' [ADDPTRS2 ADD2]].

        pose proof (IHptrs _ _ _ ADDPTRS1 ADDPTRS2) as EQV.

        eapply add_ptr_to_frame_stack_eqv; eauto.
        rewrite EQV.
        auto.
    Qed.

    Lemma add_ptr_to_heap_eqv :
      forall ptr root h h1 h2,
        add_ptr_to_heap h root ptr h1 ->
        add_ptr_to_heap h root ptr h2 ->
        heap_eqv h1 h2.
    Proof.
      intros ptr root h h1 h2 H1 H2.
      split.
      { intros root0.
        split; intros ROOT.
        - inv H1; inv H2.
          pose proof disjoint_ptr_byte_dec root root0 as [DISJOINT | NDISJOINT].
          + eapply old_heap_roots1; eauto.
            eapply old_heap_roots0; eauto.
          + unfold disjoint_ptr_byte in NDISJOINT.
            assert (ptr_to_int root = ptr_to_int root0) as EQR by lia.
            unfold root_in_heap_prop in *.
            rewrite EQR in *.
            eapply new_heap_root1.
        - inv H1; inv H2.
          pose proof disjoint_ptr_byte_dec root root0 as [DISJOINT | NDISJOINT].
          + eapply old_heap_roots0; eauto.
            eapply old_heap_roots1; eauto.
          + unfold disjoint_ptr_byte in NDISJOINT.
            assert (ptr_to_int root = ptr_to_int root0) as EQR by lia.
            unfold root_in_heap_prop in *.
            rewrite EQR in *.
            eapply new_heap_root0.
      }

      intros root0 ptr0.
      split; intros IN.
      - eapply add_ptr_to_heap_inv with (f := h) (ptr := ptr) (root := root) in IN.
        + inv H1.
          inv H2.
          destruct IN as [IN | [IN1 IN2]].
          * pose proof disjoint_ptr_byte_dec root root0 as [DISJOINT | NDISJOINT].
            -- eapply old_heap_lu_different_root1; eauto.
            -- pose proof disjoint_ptr_byte_dec ptr ptr0 as [DISJOINT' | NDISJOINT'].
               ++ eapply old_heap_lu1; eauto.
               ++ unfold disjoint_ptr_byte in NDISJOINT'.
                  assert (ptr_to_int ptr = ptr_to_int ptr0) as EQ by lia.

                  unfold disjoint_ptr_byte in NDISJOINT.
                  assert (ptr_to_int root = ptr_to_int root0) as EQR by lia.

                  unfold ptr_in_heap_prop in *.
                  rewrite EQ in *.
                  rewrite EQR in *.
                  auto.                  
          * unfold ptr_in_heap_prop in *.
            rewrite IN1 in *.
            rewrite IN2 in *.
            auto.
        + auto.
      - eapply add_ptr_to_heap_inv with (f := h) (ptr := ptr) (root := root) in IN.
        + inv H1.
          inv H2.
          destruct IN as [IN | [IN1 IN2]].
          * pose proof disjoint_ptr_byte_dec root root0 as [DISJOINT | NDISJOINT].
            -- eapply old_heap_lu_different_root0; eauto.
            -- pose proof disjoint_ptr_byte_dec ptr ptr0 as [DISJOINT' | NDISJOINT'].
               ++ eapply old_heap_lu0; eauto.
               ++ unfold disjoint_ptr_byte in NDISJOINT'.
                  assert (ptr_to_int ptr = ptr_to_int ptr0) as EQ by lia.

                  unfold disjoint_ptr_byte in NDISJOINT.
                  assert (ptr_to_int root = ptr_to_int root0) as EQR by lia.

                  unfold ptr_in_heap_prop in *.
                  rewrite EQ in *.
                  rewrite EQR in *.
                  auto.                  
          * unfold ptr_in_heap_prop in *.
            rewrite IN1 in *.
            rewrite IN2 in *.
            auto.
        + auto.
    Qed.

    Lemma add_ptrs_to_heap_eqv :
      forall ptrs root h h1 h2,
        add_ptrs_to_heap' h root ptrs h1 ->
        add_ptrs_to_heap' h root ptrs h2 ->
        heap_eqv h1 h2.
    Proof.
      induction ptrs;
        intros root h h1 h2 ADD1 ADD2.
      - cbn in *.
        rewrite <- ADD1, ADD2.
        reflexivity.
      - cbn in *.
        destruct ADD1 as [h1' [ADDPTRS1 ADD1]].
        destruct ADD2 as [h2' [ADDPTRS2 ADD2]].

        pose proof (IHptrs _ _ _ _ ADDPTRS1 ADDPTRS2) as EQV.

        eapply add_ptr_to_heap_eqv; eauto.
        rewrite EQV.
        auto.
    Qed.


    #[global] Instance frame_stack_eqv_add_all_to_frame :
      Proper ((fun ms1 ms2 => frame_stack_eqv (memory_stack_frame_stack ms1) (memory_stack_frame_stack ms2)) ==> eq ==> (fun ms1 ms2 => frame_stack_eqv (memory_stack_frame_stack ms1) (memory_stack_frame_stack ms2))) add_all_to_frame.
    Proof.
      unfold Proper, respectful.
      intros ms1 ms2 EQV y x EQ; subst.

      revert ms1 ms2 EQV.
      induction x; intros ms1 ms2 EQV.
      Transparent add_all_to_frame.
      unfold add_all_to_frame.
      cbn in *.
      auto.
      Opaque add_all_to_frame.

      assert (add_all_to_frame ms1 (a :: x) = add_all_to_frame ms1 (a :: x)) as EQ by reflexivity.
      pose proof (@add_all_to_frame_cons_inv _ _ _ _ EQ)
        as [ms' [ADD ADD_ALL]].

      assert (add_all_to_frame ms2 (a :: x) = add_all_to_frame ms2 (a :: x)) as EQ2 by reflexivity.
      pose proof (@add_all_to_frame_cons_inv _ _ _ _ EQ2)
        as [ms2' [ADD2 ADD_ALL2]].
      cbn in *.

      unfold add_to_frame in *.
      destruct ms1 as [m1 fs1].
      destruct ms2 as [m2 fs2].

      subst.

      cbn in EQV.

      pose proof (frame_stack_inv _ _ EQV) as [SNOC | SING].
      - destruct SNOC as [fs1' [fs2' [f1 [f2 [SNOC1 [SNOC2 [SEQV FEQV]]]]]]].
        subst.

        rewrite <- ADD_ALL.
        rewrite <- ADD_ALL2.

        eapply IHx.
        cbn.
        unfold frame_stack_eqv.
        intros f n.
        destruct n.
        + cbn. rewrite FEQV. reflexivity.
        + cbn. auto.
      - destruct SING as [f1 [f2 [SING1 [SING2 FEQV]]]].
        subst.

        rewrite <- ADD_ALL.
        rewrite <- ADD_ALL2.

        eapply IHx.
        cbn.
        unfold frame_stack_eqv.
        intros f n.
        destruct n.
        + cbn. rewrite FEQV. reflexivity.
        + cbn. tauto.
    Qed.

    #[global] Instance heap_eqv_add_with :
      Proper (eq ==> eq ==> heap_eqv ==> heap_eqv) (fun root a => add_with root a ret cons).
    Proof.
      unfold Proper, respectful.
      intros a b EQKEY p1 p2 EQPTR h1 h2 EQHEAP; subst.
      unfold add_with.
      split.
      { intros root.
        inv EQHEAP.
        unfold root_in_heap_prop in *.
        break_match;
          break_match.
        - destruct (Z.eq_dec (ptr_to_int root ) b) as [EQR | NEQR]; subst.
          + split; intros ROOT; apply member_add_eq.
          + split; intros ROOT;
              apply member_add_ineq in ROOT; auto;
              apply member_add_preserved; firstorder.
        - destruct (Z.eq_dec (ptr_to_int root ) b) as [EQR | NEQR]; subst.
          + split; intros ROOT; apply member_add_eq.
          + split; intros ROOT;
              apply member_add_ineq in ROOT; auto;
              apply member_add_preserved; firstorder.
        - destruct (Z.eq_dec (ptr_to_int root ) b) as [EQR | NEQR]; subst.
          + split; intros ROOT; apply member_add_eq.
          + split; intros ROOT;
              apply member_add_ineq in ROOT; auto;
              apply member_add_preserved; firstorder.
        - destruct (Z.eq_dec (ptr_to_int root ) b) as [EQR | NEQR]; subst.
          + split; intros ROOT; apply member_add_eq.
          + split; intros ROOT;
              apply member_add_ineq in ROOT; auto;
              apply member_add_preserved; firstorder.
      }

      destruct EQHEAP as [_ EQHEAP].
      unfold ptr_in_heap_prop in *.
      cbn in *.
      intros root ptr.

      destruct (Z.eq_dec (ptr_to_int root ) b) as [EQR | NEQR].
      - subst.
        pose proof (EQHEAP root ptr) as EQROOT.

        break_inner_match.
        { rewrite IP.F.add_eq_o in *; auto.
          break_inner_match.
          { rewrite IP.F.add_eq_o in *; auto.
            setoid_rewrite Heqo in EQROOT.
            setoid_rewrite Heqo0 in EQROOT.
            firstorder.
          }

          { rewrite IP.F.add_eq_o in *; auto.
            setoid_rewrite Heqo in EQROOT.
            setoid_rewrite Heqo0 in EQROOT.
            firstorder.
          }
        }
        { rewrite IP.F.add_eq_o in *; auto.
          break_inner_match.
          { rewrite IP.F.add_eq_o in *; auto.
            setoid_rewrite Heqo in EQROOT.
            setoid_rewrite Heqo0 in EQROOT.
            firstorder.
          }

          { rewrite IP.F.add_eq_o in *; auto.
            setoid_rewrite Heqo in EQROOT.
            setoid_rewrite Heqo0 in EQROOT.
            firstorder.
          }
        }
      - subst.
        pose proof (EQHEAP root ptr) as EQROOT.

        break_inner_match.
        { rewrite IP.F.add_neq_o in *; auto.
          destruct (IM.find (elt:=list Iptr) b h2) eqn:Heqo0.
          rewrite IP.F.add_neq_o in *; auto.
          rewrite IP.F.add_neq_o in *; auto.
        }
        { rewrite IP.F.add_neq_o in *; auto.
          destruct (IM.find (elt:=list Iptr) b h2) eqn:Heqo0.
          rewrite IP.F.add_neq_o in *; auto.
          rewrite IP.F.add_neq_o in *; auto.
        }
    Qed.

    #[global] Instance heap_eqv_add_all_to_heap :
      Proper ((fun ms1 ms2 => heap_eqv (memory_stack_heap ms1) (memory_stack_heap ms2)) ==> eq ==> eq ==> (fun ms1 ms2 => heap_eqv (memory_stack_heap ms1) (memory_stack_heap ms2))) add_all_to_heap'.
    Proof.
      unfold Proper, respectful.
      intros ms1 ms2 EQV y x EQ z w EQ'; subst.

      revert ms1 ms2 x EQV.
      induction w; intros ms1 ms2 x EQV.
      Transparent add_all_to_heap.
      unfold add_all_to_heap.
      cbn in *.
      auto.
      Opaque add_all_to_heap.

      rename x into root.
      rename w into x.

      assert (add_all_to_heap' ms1 root (a :: x) = add_all_to_heap' ms1 root (a :: x)) as EQ by reflexivity.
      pose proof (@add_all_to_heap'_cons_inv _ _ _ _ _ EQ)
        as [ms' [ADD ADD_ALL]].

      assert (add_all_to_heap' ms2 root (a :: x) = add_all_to_heap' ms2 root (a :: x)) as EQ2 by reflexivity.
      pose proof (@add_all_to_heap'_cons_inv _ _ _ _ _ EQ2)
        as [ms2' [ADD2 ADD_ALL2]].
      cbn in *.

      unfold add_to_heap in *.
      destruct ms1 as [m1 fs1 h1].
      destruct ms2 as [m2 fs2 h2].

      subst.

      cbn in EQV.
      Transparent add_all_to_heap.
      cbn in *.
      Opaque add_all_to_heap.

      rewrite <- ADD_ALL.
      rewrite <- ADD_ALL2.

      eapply IHw.
      cbn.
      eapply heap_eqv_add_with; eauto.
    Qed.

    (* TODO: move *)
    #[global] Instance snoc_Proper :
      Proper (frame_stack_eqv ==> frame_eqv ==> frame_stack_eqv) Snoc.
    Proof.
      unfold Proper, respectful.
      intros x y XY f f' FF.
      red.
      intros f0 n.
      destruct n.
      - cbn.
        rewrite FF.
        reflexivity.
      - cbn.
        apply XY.
    Qed.

    (* TODO: move *)
    #[global] Instance push_frame_stack_spec_Proper :
      Proper (frame_stack_eqv ==> frame_eqv ==> frame_stack_eqv ==> iff) push_frame_stack_spec.
    Proof.
      unfold Proper, respectful.
      intros x y XY f f' TU r s RS; subst.

      split; intros ADD.
      - inv ADD.
        split.
        + rewrite <- RS.
          rewrite <- XY.
          auto.
        + rewrite <- RS.
          rewrite <- TU.
          auto.
      - inv ADD.
        split.
        + rewrite RS.
          rewrite XY.
          auto.
        + rewrite RS.
          rewrite TU.
          auto.
    Qed.

    #[global] Instance member_ptr_to_int_heap_eqv_Proper :
      Proper ((fun p1 p2 => ptr_to_int p1 = ptr_to_int p2) ==> heap_eqv ==> iff) (fun p => member (ptr_to_int p)).
    Proof.
      intros p1 p2 PTREQ h1 h2 HEAPEQ; subst.
      inv HEAPEQ.
      unfold root_in_heap_prop in *.
      rewrite PTREQ.
      auto.          
    Qed.

    Lemma add_all_to_frame_cons_swap :
      forall ptrs ptr ms ms1' ms1'' ms2' ms2'',
        (* Add individual pointer first *)
        add_to_frame ms ptr = ms1' ->
        add_all_to_frame ms1' ptrs = ms1'' ->

        (* Add ptrs first *)
        add_all_to_frame ms ptrs = ms2' ->
        add_to_frame ms2' ptr = ms2'' ->

        frame_stack_eqv (memory_stack_frame_stack ms1'') (memory_stack_frame_stack ms2'').
    Proof.
      induction ptrs;
        intros ptr ms ms1' ms1'' ms2' ms2'' ADD ADD_ALL ADD_ALL' ADD'.

      rewrite add_to_frame_add_all_to_frame in *.

      - apply add_all_to_frame_nil in ADD_ALL, ADD_ALL'; subst.
        reflexivity.
      - apply add_all_to_frame_cons_inv in ADD_ALL, ADD_ALL'.
        destruct ADD_ALL as [msx [ADDx ADD_ALLx]].
        destruct ADD_ALL' as [msy [ADDy ADD_ALLy]].

        subst.

        (* ms + ptr + a ++ ptrs *)
        (* ms + a ++ ptrs + ptr *)

        (* ptrs ++ (a :: (ptr :: ms))

                         vs

                         ptr :: (ptrs ++ (a :: ms))

                         I have a lemma that's basically...

                         (ptrs ++ (ptr :: ms)) = (ptr :: (ptrs ++ ms))

                         ptr is generic, ptrs is fixed.

                         Can get...

                         ptrs ++ (a :: (ptr :: ms))
                         a :: (ptrs ++ (ptr :: ms))

                         and then

                         ptr :: (ptrs ++ (a :: ms))
                         ptrs ++ (ptr :: (a :: ms))
                         ptrs ++ (a :: (ptr :: ms))
                         a :: (ptrs ++ (ptr :: ms))
         *)

        (*
                         ptrs ++ (a :: (ptr :: ms))
                         a :: (ptrs ++ (ptr :: ms))
         *)

        assert (frame_stack_eqv
                  (memory_stack_frame_stack (add_all_to_frame (add_to_frame (add_to_frame ms ptr) a) ptrs))
                  (memory_stack_frame_stack (add_to_frame (add_all_to_frame (add_to_frame ms ptr) ptrs) a))) as EQ1.
        { eauto.
        }

        rewrite EQ1.

        assert (frame_stack_eqv
                  (memory_stack_frame_stack (add_to_frame (add_all_to_frame (add_to_frame ms a) ptrs) ptr))
                  (memory_stack_frame_stack (add_to_frame (add_all_to_frame (add_to_frame ms ptr) ptrs) a))) as EQ2.
        { assert (frame_stack_eqv
                    (memory_stack_frame_stack (add_to_frame (add_all_to_frame (add_to_frame ms a) ptrs) ptr))
                    (memory_stack_frame_stack (add_all_to_frame (add_to_frame (add_to_frame ms a) ptr) ptrs))) as EQ.
          { symmetry; eauto.
          }

          rewrite EQ.
          clear EQ.

          assert (frame_stack_eqv
                    (memory_stack_frame_stack (add_to_frame (add_to_frame ms a) ptr))
                    (memory_stack_frame_stack (add_to_frame (add_to_frame ms ptr) a))) as EQ.
          {
            eapply add_to_frame_swap; eauto.
          }

          epose proof frame_stack_eqv_add_all_to_frame (add_to_frame (add_to_frame ms a) ptr) (add_to_frame (add_to_frame ms ptr) a) as EQ'.
          forward EQ'. apply EQ.
          red in EQ'.
          specialize (EQ' ptrs ptrs eq_refl).
          rewrite EQ'.

          eauto.
        }

        rewrite EQ2.

        reflexivity.
    Qed.

    Lemma add_all_to_heap'_cons_swap :
      forall ptrs ptr root ms ms1' ms1'' ms2' ms2'',
        (* Add individual pointer first *)
        add_to_heap ms root ptr = ms1' ->
        add_all_to_heap' ms1' root ptrs = ms1'' ->

        (* Add ptrs first *)
        add_all_to_heap' ms root ptrs = ms2' ->
        add_to_heap ms2' root ptr = ms2'' ->

        heap_eqv (memory_stack_heap ms1'') (memory_stack_heap ms2'').
    Proof.
      induction ptrs;
        intros ptr root ms ms1' ms1'' ms2' ms2'' ADD ADD_ALL ADD_ALL' ADD'.

      rewrite add_to_heap_add_all_to_heap in *.

      - cbn in ADD_ALL, ADD_ALL'; subst.
        reflexivity.
      - apply add_all_to_heap'_cons_inv in ADD_ALL, ADD_ALL'.
        destruct ADD_ALL as [msx [ADDx ADD_ALLx]].
        destruct ADD_ALL' as [msy [ADDy ADD_ALLy]].

        subst.

        (* ms + ptr + a ++ ptrs *)
        (* ms + a ++ ptrs + ptr *)

        (* ptrs ++ (a :: (ptr :: ms))

                         vs

                         ptr :: (ptrs ++ (a :: ms))

                         I have a lemma that's basically...

                         (ptrs ++ (ptr :: ms)) = (ptr :: (ptrs ++ ms))

                         ptr is generic, ptrs is fixed.

                         Can get...

                         ptrs ++ (a :: (ptr :: ms))
                         a :: (ptrs ++ (ptr :: ms))

                         and then

                         ptr :: (ptrs ++ (a :: ms))
                         ptrs ++ (ptr :: (a :: ms))
                         ptrs ++ (a :: (ptr :: ms))
                         a :: (ptrs ++ (ptr :: ms))
         *)

        (*
                         ptrs ++ (a :: (ptr :: ms))
                         a :: (ptrs ++ (ptr :: ms))
         *)

        assert (heap_eqv
                  (memory_stack_heap (add_all_to_heap' (add_to_heap (add_to_heap ms root ptr) root a) root ptrs))
                  (memory_stack_heap (add_to_heap (add_all_to_heap' (add_to_heap ms root ptr) root ptrs) root a))) as EQ1.
        { eauto.
        }

        rewrite EQ1.

        assert (heap_eqv
                  (memory_stack_heap (add_to_heap (add_all_to_heap' (add_to_heap ms root a) root ptrs) root ptr))
                  (memory_stack_heap (add_to_heap (add_all_to_heap' (add_to_heap ms root ptr) root ptrs) root a))) as EQ2.
        { assert (heap_eqv
                    (memory_stack_heap (add_to_heap (add_all_to_heap' (add_to_heap ms root a) root ptrs) root ptr))
                    (memory_stack_heap (add_all_to_heap' (add_to_heap (add_to_heap ms root a) root ptr) root ptrs))) as EQ.
          { symmetry; eauto.
          }

          rewrite EQ.
          clear EQ.

          assert (heap_eqv
                    (memory_stack_heap (add_to_heap (add_to_heap ms root a) root ptr))
                    (memory_stack_heap (add_to_heap (add_to_heap ms root ptr) root a))) as EQ.
          {
            eapply add_to_heap_swap; eauto.
          }

          epose proof heap_eqv_add_all_to_heap (add_to_heap (add_to_heap ms root a) root ptr) (add_to_heap (add_to_heap ms root ptr) root a) as EQ'.
          forward EQ'. apply EQ.
          red in EQ'.
          specialize (EQ' root root eq_refl).
          specialize (EQ' ptrs ptrs eq_refl).
          rewrite EQ'.

          eauto.
        }

        rewrite EQ2.

        reflexivity.
    Qed.

    Lemma add_to_frame_correct :
      forall ptr (ms ms' : memory_stack),
        add_to_frame ms (ptr_to_int ptr) = ms' ->
        add_ptr_to_frame_stack (memory_stack_frame_stack ms) ptr (memory_stack_frame_stack ms').
    Proof.
      intros ptr ms ms' ADD.
      unfold add_ptr_to_frame_stack.
      intros f PEEK.
      exists (ptr_to_int ptr :: f).
      split; [|split].
      - (* add_ptr_to_frame *)
        split.
        + intros ptr' DISJOINT.
          split; intros IN; cbn; auto.

          destruct IN as [IN | IN];
            [contradiction | auto].
        + cbn; auto.
      - (* peek_frame_stack_prop *)
        destruct ms as [m fs].
        destruct ms' as [m' fs'].
        cbn in *.

        break_match_hyp; inv ADD;
          cbn in *; rewrite PEEK; reflexivity.
      - (* pop_frame_stack_prop *)
        destruct ms as [m fs].
        destruct ms' as [m' fs'].
        cbn in *.

        break_match_hyp; inv ADD.
        + intros fs1_pop; split; intros POP; inv POP.
        + intros fs1_pop; split; intros POP; cbn in *; auto.
    Qed.

    Lemma add_all_to_frame_correct :
      forall ptrs (ms : memory_stack) (ms' : memory_stack),
        add_all_to_frame ms (map ptr_to_int ptrs) = ms' ->
        add_ptrs_to_frame_stack (memory_stack_frame_stack ms) ptrs (memory_stack_frame_stack ms').
    Proof.
      induction ptrs;
        intros ms ms' ADD_ALL.
      - cbn in *.
        apply add_all_to_frame_nil in ADD_ALL; subst; auto.
        reflexivity.
      - cbn in *.
        eexists.
        split.
        + eapply IHptrs.
          reflexivity.
        + destruct ms as [m fs h].
          destruct ms' as [m' fs' h'].
          cbn.

          apply add_all_to_frame_cons_inv in ADD_ALL.
          destruct ADD_ALL as [ms' [ADD ADD_ALL]].

          destruct (add_all_to_frame (mkMemoryStack m fs h) (map ptr_to_int ptrs)) eqn:ADD_ALL'.
          cbn.

          rename memory_stack_memory0 into m0.
          rename memory_stack_frame_stack0 into f.
          rename memory_stack_heap0 into h0.

          assert (add_to_frame (mkMemoryStack m0 f h0) (ptr_to_int a) = add_to_frame (mkMemoryStack m0 f h0) (ptr_to_int a)) as ADD' by reflexivity.
          pose proof (add_all_to_frame_cons_swap _ _ _ _ _ _ _ ADD ADD_ALL ADD_ALL' ADD') as EQV.
          cbn in EQV.
          rewrite EQV.
          destruct f.
          * replace (Singleton f) with (memory_stack_frame_stack (mkMemoryStack m0 (Singleton f) h0)) by reflexivity.
            eapply add_to_frame_correct.
            reflexivity.
          * replace (Snoc f f0) with (memory_stack_frame_stack (mkMemoryStack m0 (Snoc f f0) h0))by reflexivity.
            eapply add_to_frame_correct.
            reflexivity.
    Qed.

    Lemma add_to_heap_correct :
      forall root ptr (ms : memory_stack) (ms' : memory_stack),
        add_to_heap ms (ptr_to_int root) (ptr_to_int ptr) = ms' ->
        add_ptr_to_heap (memory_stack_heap ms) root ptr (memory_stack_heap ms').
    Proof.
      intros root ptr ms ms' ADD.
      split.
      - (* Old *)
        intros ptr' DISJOINT root'.
        destruct ms as [mem fs h].
        unfold add_to_heap in *.
        unfold ptr_in_heap_prop in *.
        cbn in *.
        inv ADD.
        cbn.

        split; intros IN.
        + unfold add_with.
          destruct (Z.eq_dec (ptr_to_int root') (ptr_to_int root)) as [EQR | NEQR].
          * unfold Block in *.
            unfold Iptr in *.
            rewrite EQR in *.
            break_inner_match.
            -- rewrite IP.F.add_eq_o; firstorder.
            -- contradiction.
          * unfold Block in *.
            unfold Iptr in *.
            break_inner_match.
            -- rewrite IP.F.add_neq_o; firstorder.
            -- rewrite IP.F.add_neq_o; firstorder.
        + unfold add_with in *.
          destruct (Z.eq_dec (ptr_to_int root') (ptr_to_int root)) as [EQR | NEQR].
          * unfold Block in *.
            unfold Iptr in *.
            rewrite EQR in *.
            break_inner_match_hyp.
            -- rewrite IP.F.add_eq_o in IN; firstorder.
            -- rewrite IP.F.add_eq_o in IN; firstorder.
          * unfold Block in *.
            unfold Iptr in *.
            break_inner_match_hyp.
            -- rewrite IP.F.add_neq_o in IN; firstorder.
            -- rewrite IP.F.add_neq_o in IN; firstorder.
      - (* Disjoint roots *)
        intros root' H0 ptr'.
        inv ADD.
        destruct ms as [mem fs h].
        cbn.
        unfold add_with.
        break_match.
        + unfold ptr_in_heap_prop.
          rewrite IP.F.add_neq_o; auto.
          reflexivity.
        + unfold ptr_in_heap_prop.
          rewrite IP.F.add_neq_o; auto.
          reflexivity.
      - intros root' DISJOINT.
        inv ADD.
        destruct ms as [mem fs h].
        cbn.
        unfold add_with.
        break_match.
        + unfold root_in_heap_prop.
          rewrite member_add_ineq; auto.
          reflexivity.
        + unfold root_in_heap_prop.
          rewrite member_add_ineq; auto.
          reflexivity.
      - (* New *)
        destruct ms as [mem fs h].
        unfold add_to_heap in *.
        unfold ptr_in_heap_prop in *.
        cbn in *.
        inv ADD.
        cbn.

        unfold add_with.
        break_inner_match.
        -- rewrite IP.F.add_eq_o; firstorder.
        -- rewrite IP.F.add_eq_o; firstorder.
      - destruct ms as [mem fs h].
        unfold add_to_heap in *.
        unfold root_in_heap_prop in *.
        cbn in *.
        inv ADD.
        cbn.

        unfold add_with.
        break_inner_match.
        -- rewrite member_add_eq; firstorder.
        -- rewrite member_add_eq; firstorder.
    Qed.

    Lemma add_all_to_heap'_correct :
      forall ptrs root (ms : memory_stack) (ms' : memory_stack),
        add_all_to_heap' ms (ptr_to_int root) (map ptr_to_int ptrs) = ms' ->
        add_ptrs_to_heap' (memory_stack_heap ms) root ptrs (memory_stack_heap ms').
    Proof.
      induction ptrs;
        intros root ms ms' ADD_ALL.
      - cbn in *; subst; reflexivity.
      - cbn in *.
        eexists.
        split.
        + eapply IHptrs.
          reflexivity.
        + destruct ms as [m fs h].
          destruct ms' as [m' fs' h'].
          cbn.

          apply add_all_to_heap'_cons_inv in ADD_ALL.
          destruct ADD_ALL as [ms' [ADD ADD_ALL]].

          destruct (add_all_to_heap' (mkMemoryStack m fs h) (ptr_to_int root) (map ptr_to_int ptrs)) eqn:ADD_ALL'.
          cbn.

          rename memory_stack_memory0 into m0.
          rename memory_stack_frame_stack0 into f.
          rename memory_stack_heap0 into h0.

          assert (add_to_heap (mkMemoryStack m0 f h0) (ptr_to_int root) (ptr_to_int a) = add_to_heap (mkMemoryStack m0 f h0) (ptr_to_int root) (ptr_to_int a)) as ADD' by reflexivity.
          pose proof (add_all_to_heap'_cons_swap _ _ _ _ _ _ _ _ ADD ADD_ALL ADD_ALL' ADD') as EQV.
          cbn in EQV.
          replace h0 with (memory_stack_heap (mkMemoryStack m0 fs h0)) at 1 by reflexivity.
          rewrite EQV.
          replace (add_with (ptr_to_int root) (ptr_to_int a) (fun x : Z => [x]) cons h0)
            with (memory_stack_heap (mkMemoryStack m0 fs (add_with (ptr_to_int root) (ptr_to_int a) (fun x : Z => [x]) cons h0))) by reflexivity.
          eapply add_to_heap_correct.
          cbn.
          reflexivity.
    Qed.

    Lemma add_all_to_heap_correct :
      forall ptrs (ms : memory_stack) (ms' : memory_stack),
        add_all_to_heap ms (map ptr_to_int ptrs) = ms' ->
        add_ptrs_to_heap (memory_stack_heap ms) ptrs (memory_stack_heap ms').
    Proof.
      intros ptrs ms ms' H0.
      destruct ptrs.
      - cbn in *.
        Transparent add_all_to_heap.
        unfold add_all_to_heap in H0.
        Opaque add_all_to_heap.
        subst.
        reflexivity.
      - eapply add_all_to_heap'_correct; cbn in *.
        eauto.
    Qed.

    (* TODO: Move this *)
    Lemma initial_frame_empty :
      empty_frame initial_frame.
    Proof.
      unfold empty_frame.
      intros ptr.
      unfold initial_frame.
      cbn.
      auto.
    Qed.

    Lemma empty_frame_eqv :
      forall f1 f2,
        empty_frame f1 ->
        empty_frame f2 ->
        frame_eqv f1 f2.
    Proof.
      intros f1 f2 F1 F2.
      unfold empty_frame in *.
      unfold frame_eqv.
      intros ptr; split; intros IN; firstorder.
    Qed.

    (* TODO: Move this *)
    Lemma mem_state_frame_stack_prop_refl :
      forall ms fs,
        mem_state_frame_stack ms = fs ->
        mem_state_frame_stack_prop ms fs.
    Proof.
      intros [[m fsm] pr] fs EQ; subst.
      red; cbn.
      red.
      reflexivity.
    Qed.

    (* These should be opaque for convenience *)
    #[global] Opaque add_all_to_frame.
    #[global] Opaque add_all_to_heap.
    #[global] Opaque next_memory_key.

    Definition allocate_bytes `{MemMonad ExtraState MemM (itree Eff)} (dt : dtyp) (init_bytes : list SByte) : MemM addr :=
      match dtyp_eq_dec dt DTYPE_Void with
      | left _ => raise_ub "Allocation of type void"
      | _ =>
          let len := length init_bytes in
          match N.eq_dec (sizeof_dtyp dt) (N.of_nat len) with
          | right _ => raise_ub "Sizeof dtyp doesn't match number of bytes for initialization in allocation."
          | _ =>
              (* TODO: roll this into fresh provenance somehow? *)
              pr <- fresh_provenance;;
              sid <- fresh_sid;;
              ms <- get_mem_state;;
              let mem_stack := ms_memory_stack ms in
              let addr := next_memory_key mem_stack in
              let '(mkMemoryStack mem fs h) := ms_memory_stack ms in
              let aid := provenance_to_allocation_id pr in
              let ptr := (int_to_ptr addr (allocation_id_to_prov aid)) in
              ptrs <- get_consecutive_ptrs ptr (length init_bytes);;
              let mem' := add_all_index (map (fun b => (b, aid)) init_bytes) addr mem in
              let mem_stack' := add_all_to_frame (mkMemoryStack mem' fs h) (map ptr_to_int ptrs) in
              ms' <- get_mem_state;;
              let pr' := MemState_get_provenance ms' in
              put_mem_state (mkMemState mem_stack' pr');;
              ret ptr
          end
      end.

    (** Heap allocation *)
    Definition malloc_bytes `{MemMonad ExtraState MemM (itree Eff)} (init_bytes : list SByte) : MemM addr :=
      let len := length init_bytes in
      (* TODO: roll this into fresh provenance somehow? *)
      pr <- fresh_provenance;;
      sid <- fresh_sid;;
      ms <- get_mem_state;;
      let mem_stack := ms_memory_stack ms in
      let addr := next_memory_key mem_stack in
      let '(mkMemoryStack mem fs h) := ms_memory_stack ms in
      let aid := provenance_to_allocation_id pr in
      let ptr := (int_to_ptr addr (allocation_id_to_prov aid)) in
      ptrs <- get_consecutive_ptrs ptr (length init_bytes);;
      let mem' := add_all_index (map (fun b => (b, aid)) init_bytes) addr mem in
      let mem_stack' := add_all_to_heap (mkMemoryStack mem' fs h) (map ptr_to_int ptrs) in
      ms' <- get_mem_state;;
      let pr' := MemState_get_provenance ms' in
      put_mem_state (mkMemState mem_stack' pr');;
      ret ptr.

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

    (* TODO: Move this *)
    Lemma push_frame_stack_correct :
      forall fs1 f fs2,
        push_frame_stack fs1 f = fs2 ->
        push_frame_stack_spec fs1 f fs2.
    Proof.
      intros fs1 f fs2 PUSH.
      unfold push_frame_stack in PUSH.
      subst.
      split.
      - (* pop *)
        cbn. reflexivity.
      - (* peek *)
        cbn. reflexivity.
    Qed.

    (* TODO: move *)
    Lemma push_frame_stack_inj :
      forall fs1 f fs2 fs2',
        push_frame_stack_spec fs1 f fs2 ->
        push_frame_stack_spec fs1 f fs2' ->
        frame_stack_eqv fs2 fs2'.
    Proof.
      intros fs1 f fs2 fs2' PUSH1 PUSH2.
      inv PUSH1.
      inv PUSH2.

      destruct fs2, fs2'; try contradiction.
      cbn in *.
      rewrite <- new_frame0, <- new_frame1.
      rewrite can_pop0, can_pop1.
      reflexivity.
    Qed.

    Definition pop_frame_stack (fs : FrameStack) : err FrameStack :=
      match fs with
      | Singleton f => inl "Last frame, cannot pop."%string
      | Snoc s f => inr s
      end.

    Definition mem_state_set_frame_stack (ms : MemState) (fs : FrameStack) : MemState :=
      let '(mkMemoryStack mem _ h) := ms_memory_stack ms in
      let pr := mem_state_provenance ms in
      mkMemState (mkMemoryStack mem fs h) pr.

    Definition mem_state_set_heap (ms : MemState) (h : Heap) : MemState :=
      let '(mkMemoryStack mem fs _) := ms_memory_stack ms in
      let pr := mem_state_provenance ms in
      mkMemState (mkMemoryStack mem fs h) pr.

    Lemma mem_state_frame_stack_prop_set_refl :
      forall ms fs,
        mem_state_frame_stack_prop (mem_state_set_frame_stack ms fs) fs.
    Proof.
      intros [[m fsm] pr] fs.
      red; cbn.
      red.
      reflexivity.
    Qed.

    Lemma mem_state_heap_prop_set_refl :
      forall ms h,
        mem_state_heap_prop (mem_state_set_heap ms h) h.
    Proof.
      intros [[m fsm h] pr] h'.
      red; cbn.
      red.
      reflexivity.
    Qed.

    Lemma mem_state_frame_stack_prop_set_trans :
      forall ms fs fs' fs'',
        frame_stack_eqv fs' fs'' ->
        mem_state_frame_stack_prop (mem_state_set_frame_stack ms fs) fs' ->
        mem_state_frame_stack_prop (mem_state_set_frame_stack ms fs) fs''.
    Proof.
      intros [[m fsm] pr] fs fs' fs'' EQV MEMPROP.
      red; cbn.
      red in MEMPROP; cbn in MEMPROP.
      red. red in MEMPROP.
      rewrite <- EQV.
      auto.
    Qed.

    Lemma mem_state_heap_prop_set_trans :
      forall ms h h' h'',
        heap_eqv h' h'' ->
        mem_state_heap_prop (mem_state_set_heap ms h) h' ->
        mem_state_heap_prop (mem_state_set_heap ms h) h''.
    Proof.
      intros [[m fsm] pr] h h' h'' EQV MEMPROP.
      red; cbn.
      red in MEMPROP; cbn in MEMPROP.
      red. red in MEMPROP.
      rewrite <- EQV.
      auto.
    Qed.

    Definition mempush `{MemMonad ExtraState MemM (itree Eff)} : MemM unit :=
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

    Definition free_block_memory (block : Block) (m : memory) : memory :=
      fold_left (fun m key => free_byte key m) block m.

    (** Stack free *)
    Definition mempop `{MemMonad ExtraState MemM (itree Eff)} : MemM unit :=
      ms <- get_mem_state;;
      let '(mkMemoryStack mem fs h) := ms_memory_stack ms in
      let f := peek_frame_stack fs in
      fs' <- lift_err_RAISE_ERROR (pop_frame_stack fs);;
      let mem' := free_frame_memory f mem in
      let pr := mem_state_provenance ms in
      let ms' := mkMemState (mkMemoryStack mem' fs' h) pr in
      put_mem_state ms'.

    (** Free from heap *)
    Definition free `{MemMonad ExtraState MemM (itree Eff)} (ptr : addr) : MemM unit :=
      ms <- get_mem_state;;
      let '(mkMemoryStack mem fs h) := ms_memory_stack ms in
      let raw_addr := ptr_to_int ptr in
      match lookup raw_addr h with
      | None => raise_ub "Attempt to free non-heap allocated address."
      | Some block =>
          let mem' := free_block_memory block mem in
          let h' := delete raw_addr h in
          let pr := mem_state_provenance ms in
          let ms' := mkMemState (mkMemoryStack mem' fs h') pr in
          put_mem_state ms'
      end.

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

    (* Instance ErrSIDMemMonad : MemMonad MemState ExtraState AllocationId (ESID.ErrSID_T (state MemState)). *)
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

    Import Monad.

  End MemoryPrimatives.

    Import Monad.

    (* TODO: Move these tactics *)
    Ltac MemMonad_go :=
      repeat match goal with
             | |- context [MemMonad_run (bind _ _)] => rewrite MemMonad_run_bind
             | |- context [MemMonad_run get_mem_state] => rewrite MemMonad_get_mem_state
             | |- context [MemMonad_run (put_mem_state _)] => rewrite MemMonad_put_mem_state
             | |- context [MemMonad_run (ret _)] => rewrite MemMonad_run_ret
             | |- context [MemMonad_run (raise_ub _)] => rewrite MemMonad_run_raise_ub
             end.

    Ltac break_memory_lookup :=
      match goal with
      | |- context [match read_byte_raw ?memory ?intptr with _ => _ end] =>
          let Hlookup := fresh "Hlookup" in
          let byte := fresh "byte" in
          let aid := fresh "aid" in
          destruct (read_byte_raw memory intptr) as [[byte aid] | ] eqn:Hlookup
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
        | Hlup: read_byte_raw ?mem ?addr = _,
            H: context [match read_byte_raw ?mem ?addr with _ => _ end] |- _
          => rewrite Hlup in H; cbn in H
        | Hlup: read_byte_raw ?mem ?addr = _ |-
            context [match read_byte_raw ?mem ?addr with _ => _ end]
          => rewrite Hlup; cbn
        | HC: ?X = _,
            H: context [if ?X then _ else _] |- _
          => rewrite HC in H; cbn in H
        | HC: ?X = _ |-
            context [if ?X then _ else _]
          => rewrite HC; cbn
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

    Ltac unfold_MemState_get_memory :=
      unfold MemState_get_memory;
      unfold mem_state_memory_stack;
      unfold mem_state_memory.

    Ltac unfold_mem_state_memory :=
      unfold mem_state_memory;
      unfold fst;
      unfold ms_memory_stack.

    Ltac unfold_MemState_get_memory_in H :=
      unfold MemState_get_memory in H;
      unfold mem_state_memory_stack in H;
      unfold mem_state_memory in H.

    Ltac unfold_mem_state_memory_in H :=
      unfold mem_state_memory in H;
      unfold fst in H;
      unfold ms_memory_stack in H.

    Ltac solve_returns_provenance :=
      let EQ := fresh "EQ" in
      intros ? ? EQ; inv EQ; reflexivity.

    Ltac break_byte_allocated_in ALLOC :=
      destruct ALLOC as [?ms [?b [ALLOC [?EQ1 ?EQ2]]]]; subst;
      destruct ALLOC as [ALLOC ?LIFT];
      destruct ALLOC as [?ms' [?ms'' [[?EQ1 ?EQ2] ALLOC]]]; subst.

    Ltac break_read_byte_prop_in READ :=
      destruct READ as [?ms' [?ms'' [[?EQ1 ?EQ2] READ]]]; subst.

    (* TODO: move this *)
    Lemma byte_allocated_mem_stack :
      forall ms1 ms2 addr aid,
        byte_allocated ms1 addr aid ->
        mem_state_memory_stack ms1 = mem_state_memory_stack ms2 ->
        byte_allocated ms2 addr aid.
    Proof.
      intros [ms1 pr1] [ms2 pr2] addr aid ALLOC EQ.
      cbn in EQ; subst.
      break_byte_allocated_in ALLOC.
      repeat eexists; [| solve_returns_provenance].
      unfold mem_state_memory in *; cbn in *.
      break_match; [break_match|];
        tauto.
    Qed.

    (* TODO: move this *)
    Lemma read_byte_prop_mem_stack :
      forall ms1 ms2 addr sbyte,
        read_byte_prop ms1 addr sbyte ->
        mem_state_memory_stack ms1 = mem_state_memory_stack ms2 ->
        read_byte_prop ms2 addr sbyte.
    Proof.
      intros [ms1 pr1] [ms2 pr2] addr aid READ EQ.
      cbn in EQ; subst.
      break_read_byte_prop_in READ.
      repeat eexists.
      unfold mem_state_memory in *; cbn in *.
      break_match; [break_match|]; tauto.
    Qed.

    Ltac rewrite_set_byte_eq :=
      rewrite set_byte_raw_eq; [|solve [eauto]].

    Ltac rewrite_set_byte_neq :=
      first [
          match goal with
          | H: read_byte_raw (set_byte_raw _ _ _) _ = _ |- _
            => rewrite set_byte_raw_neq in H; [| solve [eauto]]
          end
        | rewrite set_byte_raw_neq; [| solve [eauto]]
        ].

    Ltac solve_byte_allocated :=
      solve [ eapply byte_allocated_mem_stack; eauto
            | repeat eexists; [| solve_returns_provenance];
              unfold mem_state_memory in *;
              first [ cbn;
                      rewrite_set_byte_eq
                    | cbn;
                      rewrite_set_byte_neq
                    | subst_mempropt
                ];
              first
                [ split; try reflexivity;
                  first [rewrite aid_access_allowed_refl | apply aid_eq_dec_refl]; auto
                | break_match; [break_match|]; split; repeat inv_option; eauto
                ]
        ].

    Ltac solve_allocations_preserved :=
      intros ?ptr ?aid; split; intros ALLOC;
      solve_byte_allocated.

    Ltac destruct_read_byte_allowed_in READ :=
      destruct READ as [?aid [?ALLOC ?ALLOWED]].

    Ltac break_read_byte_allowed_in READ :=
      cbn in READ;
      destruct READ as [?aid READ];
      destruct READ as [READ ?ALLOWED];
      destruct READ as [?ms' [?ms'' [READ [?EQ1 ?EQ2]]]]; subst;
      destruct READ as [READ ?LIFT];
      destruct READ as [?ms' [?ms'' [[?EQ1 ?EQ2] READ]]]; subst;
      cbn in READ.

    Ltac break_write_byte_allowed_in WRITE :=
      destruct WRITE as [?aid WRITE];
      destruct WRITE as [WRITE ?ALLOWED];
      destruct WRITE as [?ms' [?b [WRITE [?EQ1 ?EQ2]]]]; subst;
      destruct WRITE as [WRITE ?LIFT];
      cbn in WRITE;
      destruct WRITE as [?ms' [?ms'' [[?EQ1 ?EQ2] ?WRITE]]]; subst;
      cbn in WRITE.

    Ltac destruct_write_byte_allowed_in WRITE :=
      destruct WRITE as [?aid [?ALLOC ?ALLOWED]].

    Ltac break_write_byte_allowed_hyps :=
      repeat
        match goal with
        | WRITE : write_byte_allowed _ _ |- _ =>
            destruct_write_byte_allowed_in WRITE
        end.

    Ltac break_read_byte_allowed_hyps :=
      repeat
        match goal with
        | READ : read_byte_allowed _ _ |- _ =>
            destruct_read_byte_allowed_in READ
        end.

    Ltac break_access_hyps :=
      break_read_byte_allowed_hyps;
      break_write_byte_allowed_hyps.

    Ltac break_addr_allocated_prop_in ALLOCATED :=
       cbn in ALLOCATED;
       destruct ALLOCATED as (?ms' & ?b & ALLOCATED);
       destruct ALLOCATED as [[?C1 ?C2] ALLOCATED]; subst.

    Ltac break_lifted_addr_allocated_prop_in ALLOCATED :=
      cbn in ALLOCATED;
      destruct ALLOCATED as [?ms [?b [ALLOCATED [?EQ1 ?EQ2]]]]; subst;
      destruct ALLOCATED as [ALLOCATED ?LIFT];
      destruct ALLOCATED as [?ms' [?ms'' [[?EQ1 ?EQ2] ALLOCATED]]]; subst.

    Hint Rewrite int_to_ptr_provenance : PROVENANCE.
    Hint Resolve access_allowed_refl : ACCESS_ALLOWED.

      Ltac access_allowed_auto :=
        solve [autorewrite with PROVENANCE; eauto with ACCESS_ALLOWED].

      Ltac solve_access_allowed :=
        solve [match goal with
               | HMAPM :
                 Util.map_monad _ _ = inr ?xs,
                   IN :
                   In _ ?xs |- _ =>
                   let GENPTR := fresh "GENPTR" in
                   pose proof map_monad_err_In _ _ _ _ HMAPM IN as [?ip [GENPTR ?INip]];
                   apply handle_gep_addr_preserves_provenance in GENPTR;
                   rewrite <- GENPTR
               end; access_allowed_auto
              | access_allowed_auto
          ].

    Ltac solve_write_byte_allowed :=
      break_access_hyps; eexists; split; [| solve_access_allowed]; solve_byte_allocated.

    Ltac solve_read_byte_allowed :=
      solve_write_byte_allowed.

    Ltac solve_read_byte_allowed_all_preserved :=
      intros ?ptr; split; intros ?READ; solve_read_byte_allowed.

    Ltac solve_write_byte_allowed_all_preserved :=
      intros ?ptr; split; intros ?WRITE; solve_write_byte_allowed.

    Ltac solve_read_byte_prop :=
      solve [ eapply read_byte_prop_mem_stack; eauto
            | repeat eexists;
              first [ cbn; (*unfold_mem_state_memory; *)
                      rewrite set_byte_raw_eq; [|solve [eauto]]
                    | subst_mempropt
                ];
              cbn; subst_mempropt;
              split; auto
        ].

    Ltac solve_read_byte_prop_all_preserved :=
      split; intros ?READ; solve_read_byte_prop.

    Ltac solve_read_byte_preserved :=
      split;
      [ solve_read_byte_allowed_all_preserved
      | solve_read_byte_prop_all_preserved
      ].

    (* Ltac solve_set_byte_memory := *)
    (*   split; [solve_read_byte_allowed | solve_read_byte_prop | solve_disjoint_read_bytes]. *)

    Ltac solve_read_byte_spec :=
      split; [solve_read_byte_allowed | solve_read_byte_prop].

    Ltac solve_frame_stack_preserved :=
      solve [
          let PROP := fresh "PROP" in
          intros ?fs; split; intros PROP; unfold mem_state_frame_stack_prop in *; auto
          (* intros ?fs; split; intros PROP; inv PROP; reflexivity *)
        ].

    (* TODO: move this? *)
    (* Probably general enough to live in MemoryModel.v *)
    Lemma heap_preserved_mem_state_heap_refl :
      forall ms1 ms2,
        heap_eqv (mem_state_heap ms1) (mem_state_heap ms2) ->
        heap_preserved ms1 ms2.
    Proof.
      intros ms1 ms2 EQ.
      destruct ms1, ms2.
      unfold mem_state_heap in *.
      cbn in *.
      red.
      intros h; cbn.
      unfold memory_stack_heap_prop.
      split; intros EQV.
      rewrite <- EQ; auto.
      rewrite EQ; auto.
    Qed.

    Ltac solve_heap_preserved :=
      solve [
          let PROP := fresh "PROP" in
          intros ?fs; split; intros PROP; unfold mem_state_frame_stack_prop in *; auto
        | eapply heap_preserved_mem_state_heap_refl;
          unfold mem_state_heap;
          cbn;
          rewrite add_all_to_frame_preserves_heap;
          cbn;
          reflexivity
        ].

    (* TODO: move this stuff? *)
    Hint Resolve
         provenance_lt_trans
         provenance_lt_next_provenance
         provenance_lt_nrefl : PROVENANCE_LT.

    Hint Unfold used_provenance_prop : PROVENANCE_LT.

    Ltac solve_used_provenance_prop :=
      unfold used_provenance_prop in *;
      eauto with PROVENANCE_LT.

    Ltac solve_extend_provenance :=
      unfold extend_provenance;
      split; [|split]; solve_used_provenance_prop.

    Ltac solve_fresh_provenance_invariants :=
      split;
      [ solve_extend_provenance
      | split; [| split; [| split; [|split]]];
        [ solve_read_byte_preserved
        | solve_write_byte_allowed_all_preserved
        | solve_allocations_preserved
        | solve_frame_stack_preserved
        | solve_heap_preserved
        ]
      ].

    Section MemoryPrimatives.
      Context {MemM : Type -> Type}.
      Context {Eff : Type -> Type}.
      (* Context `{Monad MemM}. *)
      (* Context `{MonadProvenance Provenance MemM}. *)
      (* Context `{MonadStoreID MemM}. *)
      (* Context `{MonadMemState MemState MemM}. *)
      (* Context `{RAISE_ERROR MemM} `{RAISE_UB MemM} `{RAISE_OOM MemM}. *)
      Context {ExtraState : Type}.
      Context `{MemMonad ExtraState MemM (itree Eff)}.

    Lemma byte_allocated_set_byte_raw_eq :
      forall ptr aid new new_aid m1 m2,
        byte_allocated m1 ptr aid ->
        mem_state_memory m2 = set_byte_raw (mem_state_memory m1) (ptr_to_int ptr) (new, new_aid) ->
        byte_allocated m2 ptr new_aid.
    Proof.
      intros ptr aid new new_aid m1 m2 [aid' [ms [[ALLOCATED LIFT] GET]]] MEM.
      cbn in GET.
      inversion GET; subst.
      break_addr_allocated_prop_in ALLOCATED.

      unfold mem_state_memory in *.
      do 2 eexists.
      split; [| cbn; tauto].
      split; [| solve_returns_provenance].
      cbn.
      repeat eexists.
      rewrite MEM.
      rewrite set_byte_raw_eq; auto.
      cbn; split; auto.
      apply aid_eq_dec_refl.
    Qed.

    Lemma byte_allocated_set_byte_raw_neq :
      forall ptr aid new_ptr new new_aid m1 m2,
        byte_allocated m1 ptr aid ->
        disjoint_ptr_byte ptr new_ptr ->
        mem_state_memory m2 = set_byte_raw (mem_state_memory m1) (ptr_to_int new_ptr) (new, new_aid) ->
        byte_allocated m2 ptr aid.
    Proof.
      intros ptr aid new_ptr new new_aid m1 m2 [aid' [ms [[ALLOCATED LIFT] GET]]] DISJOINT MEM.
      inversion GET; subst.
      cbn in ALLOCATED.
      destruct ALLOCATED as (ms' & b & ALLOCATED).
      destruct ALLOCATED as [[C1 C2] ALLOCATED]; subst.

      do 2 eexists.
      split; [| cbn; tauto].
      split; [| solve_returns_provenance].

      repeat eexists.
      unfold mem_state_memory in *.
      rewrite MEM.
      unfold mem_byte in *.
      rewrite set_byte_raw_neq; auto.
      break_match.
      break_match.
      destruct ALLOCATED.
      cbn; split; auto.
      destruct ALLOCATED.
      match goal with
      | H: true = false |- _ =>
          inv H
      end.
    Qed.

    Lemma byte_allocated_set_byte_raw :
      forall ptr aid ptr_new new m1 m2,
        byte_allocated m1 ptr aid ->
        mem_state_memory m2 = set_byte_raw (mem_state_memory m1) (ptr_to_int ptr_new) new ->
        exists aid2, byte_allocated m2 ptr aid2.
    Proof.
      intros ptr aid ptr_new new m1 m2 ALLOCATED MEM.
      pose proof (Z.eq_dec (ptr_to_int ptr) (ptr_to_int ptr_new)) as [EQ | NEQ].
      - (* EQ *)
        destruct new.
        rewrite <- EQ in MEM.
        eexists.
        eapply byte_allocated_set_byte_raw_eq; eauto.
      - (* NEQ *)
        destruct new.
        subst.
        eexists.
        eapply byte_allocated_set_byte_raw_neq; eauto.
    Qed.

    (* TODO: add to solve_read_byte_allowed *)
    Lemma read_byte_allowed_set_frame_stack :
      forall ms f ptr,
        read_byte_allowed ms ptr <-> read_byte_allowed (mem_state_set_frame_stack ms f) ptr.
    Proof.
      intros [[ms prov] fs] f ptr.
      cbn.
      unfold read_byte_allowed;
        split; intros READ;
        cbn in *.

      - break_read_byte_allowed_in READ.

        exists aid.
        repeat eexists; [| solve_returns_provenance |]; auto.

        cbn in *.
        break_match; [break_match|]; tauto.
      - break_read_byte_allowed_in READ.

        exists aid.
        repeat eexists; [| solve_returns_provenance |]; auto.

        cbn in *.
        break_match; [break_match|]; tauto.
    Qed.

    (* TODO: add to write_byte_allowed *)
    Lemma write_byte_allowed_set_frame_stack :
      forall ms f ptr,
        write_byte_allowed ms ptr <-> write_byte_allowed (mem_state_set_frame_stack ms f) ptr.
    Proof.
      intros [[ms prov] fs] f ptr.
      cbn.
      unfold write_byte_allowed;
        split; intros WRITE;
        cbn in *.

      - break_write_byte_allowed_in WRITE.

        exists aid.
        repeat eexists; [| solve_returns_provenance |]; auto.

        cbn in *.
        break_match; [break_match|]; tauto.
      - break_write_byte_allowed_in WRITE.

        exists aid.
        repeat eexists; [| solve_returns_provenance |]; auto.

        cbn in *.
        break_match; [break_match|]; tauto.
    Qed.

    (* TODO: add to solve_read_byte_prop_all_preserved. *)
    Lemma read_byte_prop_set_frame_stack :
      forall ms f,
        read_byte_prop_all_preserved ms (mem_state_set_frame_stack ms f).
    Proof.
      intros [[ms prov] fs] f.
      cbn.
      unfold read_byte_prop_all_preserved, read_byte_prop.
      split; intros READ;
        cbn in *.

      - destruct READ as [ms' [ms'' [[EQ1 EQ2] READ]]]; subst.
        do 2 eexists; split; [tauto|].
        cbn in *.
        break_match; auto.
        break_match; tauto.
      - destruct READ as [ms' [ms'' [[EQ1 EQ2] READ]]]; subst.
        do 2 eexists; split; [tauto|].
        cbn in *.
        break_match; auto.
        break_match; tauto.
    Qed.

    (* TODO *)
    Lemma write_byte_allowed_all_preserved_set_frame_stack :
      forall ms f,
        write_byte_allowed_all_preserved ms (mem_state_set_frame_stack ms f).
    Proof.
      intros ms f ptr.
      eapply write_byte_allowed_set_frame_stack.
    Qed.

    Lemma allocations_preserved_set_frame_stack :
      forall ms f,
        allocations_preserved ms (mem_state_set_frame_stack ms f).
    Proof.
      intros ms f ptr aid.
      split; intros ALLOC.

      - destruct ms as [[ms fs] pr].
        cbn in *.
        break_byte_allocated_in ALLOC.
        cbn in ALLOC.
        unfold mem_state_memory in ALLOC.
        cbn in ALLOC.

        repeat eexists; [| solve_returns_provenance].
        cbn.
        break_match; [break_match|]; tauto.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        break_byte_allocated_in ALLOC.
        cbn in ALLOC.
        unfold mem_state_memory in ALLOC.
        cbn in ALLOC.

        repeat eexists; [| solve_returns_provenance].
        cbn.
        break_match; [break_match|]; tauto.
    Qed.

    (* TODO: move *)
    Lemma preserve_allocation_ids_set_frame_stack :
      forall ms f,
        preserve_allocation_ids ms (mem_state_set_frame_stack ms f).
    Proof.
      intros ms f pr.
      split; intros USED.

      - destruct ms as [[ms fs] pr'].
        cbn in *; auto.
      - destruct ms as [[ms fs] pr'].
        cbn in *; auto.
    Qed.

    (** Correctness of the main operations on memory *)
    Lemma read_byte_correct_base :
      forall ptr, exec_correct_memory (read_byte ptr) (read_byte_MemPropT ptr).
    Proof.
      unfold exec_correct.
      intros ptr ms st VALID.

      Ltac solve_MemMonad_valid_state :=
        solve [auto].

      (* Need to destruct ahead of time so we know if UB happens *)
      destruct (read_byte_raw (mem_state_memory ms) (ptr_to_int ptr)) as [[sbyte aid]|] eqn:READ.
      destruct (access_allowed (address_provenance ptr) aid) eqn:ACCESS.
      - (* Success *)
        right.
        split; [|split].
        + (* Error *)
          do 2 eexists; intros RUN.
          exfalso.
          unfold read_byte, read_byte_MemPropT in *.

          rewrite MemMonad_run_bind in RUN.
          rewrite MemMonad_get_mem_state in RUN.
          rewrite bind_ret_l in RUN.

          rewrite READ in RUN.
          rewrite ACCESS in RUN.

          rewrite MemMonad_run_ret in RUN.

          apply MemMonad_eq1_raise_error_inv in RUN; auto.
        + (* OOM *)
          do 2 eexists; intros RUN.
          exfalso.
          unfold read_byte, read_byte_MemPropT in *.

          rewrite MemMonad_run_bind in RUN.
          rewrite MemMonad_get_mem_state in RUN.
          rewrite bind_ret_l in RUN.

          rewrite READ in RUN.
          rewrite ACCESS in RUN.

          rewrite MemMonad_run_ret in RUN.

          apply MemMonad_eq1_raise_oom_inv in RUN; auto.
        + (* Success *)
          intros st' ms' x RUN.
          unfold read_byte, read_byte_MemPropT in *.

          rewrite MemMonad_run_bind in RUN.
          rewrite MemMonad_get_mem_state in RUN.
          rewrite bind_ret_l in RUN.

          rewrite READ in RUN.
          rewrite ACCESS in RUN.

          rewrite MemMonad_run_ret in RUN.

          apply eq1_ret_ret in RUN; [inv RUN | typeclasses eauto].
          split; [| solve_returns_provenance].

          cbn; do 2 eexists.
          unfold MemState_get_memory in *.
          unfold mem_state_memory_stack in *.
          unfold mem_state_memory in *.

          rewrite READ; cbn.
          rewrite ACCESS; cbn.
          eauto.
      - (* UB from provenance mismatch *)
        left.
        Ltac solve_read_byte_MemPropT_contra READ ACCESS :=
          solve [repeat eexists; right;
                 repeat eexists; cbn;
                 unfold MemState_get_memory in *;
                 unfold mem_state_memory_stack in *;
                 unfold mem_state_memory in *;
                 try rewrite READ in *; cbn in *;
                 try rewrite ACCESS in *; cbn in *;
                 tauto].

        repeat eexists; [| solve_returns_provenance].
        unfold mem_state_memory in *.
        solve_read_byte_MemPropT_contra READ ACCESS.
      - (* UB from accessing unallocated memory *)
        left.
        repeat eexists; [| solve_returns_provenance].
        unfold mem_state_memory in *.
        solve_read_byte_MemPropT_contra READ ACCESS.

        Unshelve.
        all: exact (""%string).
    Qed.

    Lemma read_byte_correct :
      forall ptr, exec_correct (read_byte ptr) (read_byte_spec_MemPropT ptr).
    Proof.
      intros ptr.
      pose proof read_byte_correct_base ptr as BASE.
      unfold exec_correct.
      intros ms st VALID.

      (* Need to destruct ahead of time so we know if UB happens *)
      destruct (read_byte_raw (mem_state_memory ms) (ptr_to_int ptr)) as [[sbyte aid]|] eqn:READ.
      destruct (access_allowed (address_provenance ptr) aid) eqn:ACCESS.
        - (* Success *)
        right.
        split; [|split].
        + (* Error *)
          do 2 eexists; intros RUN.
          exfalso.
          unfold read_byte, read_byte_MemPropT in *.

          rewrite MemMonad_run_bind in RUN.
          rewrite MemMonad_get_mem_state in RUN.
          rewrite bind_ret_l in RUN.

          rewrite READ in RUN.
          rewrite ACCESS in RUN.

          rewrite MemMonad_run_ret in RUN.

          apply MemMonad_eq1_raise_error_inv in RUN; auto.
        + (* OOM *)
          do 2 eexists; intros RUN.
          exfalso.
          unfold read_byte, read_byte_MemPropT in *.

          rewrite MemMonad_run_bind in RUN.
          rewrite MemMonad_get_mem_state in RUN.
          rewrite bind_ret_l in RUN.

          rewrite READ in RUN.
          rewrite ACCESS in RUN.

          rewrite MemMonad_run_ret in RUN.

          apply MemMonad_eq1_raise_oom_inv in RUN; auto.
        + (* Success *)
          intros st' ms' x RUN.
          unfold read_byte, read_byte_MemPropT in RUN.

          rewrite MemMonad_run_bind in RUN.
          rewrite MemMonad_get_mem_state in RUN.
          rewrite bind_ret_l in RUN.

          rewrite READ in RUN.
          rewrite ACCESS in RUN.

          rewrite MemMonad_run_ret in RUN.

          apply eq1_ret_ret in RUN; [inv RUN | typeclasses eauto].
          split; [|split]; auto.
          solve_read_byte_allowed.
          unfold read_byte_prop.
          unfold exec_correct_memory in BASE.

          cbn; do 2 eexists.
          unfold MemState_get_memory in *.
          unfold mem_state_memory_stack in *.
          unfold mem_state_memory in *.

          rewrite READ; cbn.
          rewrite ACCESS; cbn.
          eauto.
      - (* UB from provenance mismatch *)
        left.
        repeat eexists.
        cbn.
        intros byte.
        intros [ALLOWED VALUE].
        unfold MemState_get_memory in *;
          unfold mem_state_memory_stack in *;
          unfold mem_state_memory in *;

          unfold mem_state_memory in *.

        break_access_hyps.
        break_byte_allocated_in ALLOC.
        rewrite READ in ALLOC.
        cbn in ALLOC.
        inv ALLOC.

        destruct (aid_eq_dec aid0 aid); inv H1.
        rewrite ACCESS in ALLOWED.
        inv ALLOWED.
      - (* UB from accessing unallocated memory *)
        left.
        repeat eexists.
        cbn.
        intros byte.
        intros [ALLOWED VALUE].
        unfold MemState_get_memory in *;
          unfold mem_state_memory_stack in *;
          unfold mem_state_memory in *;

          unfold mem_state_memory in *.

        break_access_hyps.
        break_byte_allocated_in ALLOC.
        rewrite READ in ALLOC.
        cbn in ALLOC.
        inv ALLOC.
        inv H1.

        Unshelve.
        all: exact (""%string).
    Qed.

    Lemma write_byte_correct :
      forall ptr byte, exec_correct (write_byte ptr byte) (write_byte_spec_MemPropT ptr byte).
    Proof.
      unfold exec_correct.
      intros ptr byte ms st VALID.

      (* Need to destruct ahead of time so we know if UB happens *)
      destruct (read_byte_raw (mem_state_memory ms) (ptr_to_int ptr)) as [[sbyte aid]|] eqn:READ.
      destruct (access_allowed (address_provenance ptr) aid) eqn:ACCESS.

      - (* Success *)
        right.

        cbn.
        split; [| split].

        + (* Error *)
          eexists. exists ""%string.
          intros RUN.

          unfold write_byte in RUN.

          rewrite MemMonad_run_bind in RUN.
          rewrite MemMonad_get_mem_state in RUN.
          rewrite bind_ret_l in RUN.

          rewrite READ in RUN.
          rewrite ACCESS in RUN.

          rewrite MemMonad_put_mem_state in RUN.
          apply MemMonad_eq1_raise_error_inv in RUN; auto.
        + (* OOM *)
          eexists. exists ""%string.
          intros RUN.

          unfold write_byte in RUN.

          rewrite MemMonad_run_bind in RUN.
          rewrite MemMonad_get_mem_state in RUN.
          rewrite bind_ret_l in RUN.

          rewrite READ in RUN.
          rewrite ACCESS in RUN.

          rewrite MemMonad_put_mem_state in RUN.
          apply MemMonad_eq1_raise_oom_inv in RUN; auto.
        + (* Success *)
          intros st' ms' x RUN.

          unfold write_byte in RUN.

          rewrite MemMonad_run_bind in RUN.
          rewrite MemMonad_get_mem_state in RUN.
          rewrite bind_ret_l in RUN.

          rewrite READ in RUN.
          rewrite ACCESS in RUN.

          rewrite MemMonad_put_mem_state in RUN.
          apply eq1_ret_ret in RUN; [inv RUN | typeclasses eauto].

          split.
          * (* Write is allowed *)
            solve_write_byte_allowed.
          * (* Byte is set in new memory *)
            split.
            -- (* Read byte spec *)
              solve_read_byte_spec.
            -- (* Disjoint bytes are preserved *)
              intros ptr' byte' DISJOINT.
              split; intros READBYTE.
              { split.
                - (* TODO: solve_read_byte_allowed *)
                  apply read_byte_allowed_spec in READBYTE.
                  (* TODO: is there a way to avoid having to do these destructs before eexists? *)
                  break_access_hyps.
                  break_byte_allocated_in ALLOC.
                  break_match_hyp.
                  break_match_hyp.
                  { (* Read of ptr' succeeds *)
                    destruct ALLOC as [_ AIDEQ].

                    eexists; split; [solve_byte_allocated | solve_access_allowed].
                  }

                  { (* Read fails *)
                    destruct ALLOC as [_ EQ].
                    inv EQ.
                  }
                - (* TODO: solve_read_byte_prop. *)
                  apply read_byte_value in READBYTE.
                  (* TODO: is there a way to avoid having to do these destructs before eexists? *)
                  unfold read_byte_prop, read_byte_MemPropT in *.
                  cbn in READBYTE. cbn.
                  destruct READBYTE as [ms' [ms'' [[EQ1 EQ2] READBYTE]]]; subst.

                  repeat eexists.
                  cbn.
                  unfold mem_state_memory in *.
                  rewrite set_byte_raw_neq; [| solve [eauto]].
                  break_match; [break_match|]; firstorder.
              }

              { split.
                - (* TODO: solve_read_byte_allowed *)
                  apply read_byte_allowed_spec in READBYTE.
                  (* TODO: is there a way to avoid having to do these destructs before eexists? *)
                  break_access_hyps.
                  break_byte_allocated_in ALLOC.
                  cbn in ALLOC; subst.
                  break_match_hyp.
                  break_match_hyp.
                  { (* Read of ptr' succeeds *)
                    destruct ALLOC as [_ AIDEQ].

                    eexists; split; [solve_byte_allocated | solve_access_allowed].
                  }

                  { (* Read fails *)
                    destruct ALLOC as [_ EQ].
                    inv EQ.
                  }
                - (* TODO: solve_read_byte_prop. *)
                  apply read_byte_value in READBYTE.
                  (* TODO: is there a way to avoid having to do these destructs before eexists? *)
                  break_read_byte_prop_in READBYTE.
                  cbn in *.
                  repeat eexists.
                  unfold mem_state_memory in *.
                  rewrite set_byte_raw_neq in READBYTE; [| solve [eauto]].
                  break_match; [break_match|]; firstorder.
              }
          * (* TODO: solve_write_byte_operation_invariants *)
            split.
            -- (* Allocations preserved *)
              (* TODO: solve_allocations_preserved *)
              unfold allocations_preserved.
              intros addr aid'.
              split.
              { (* TODO: solve_byte_allocated *)
                intros ALLOC.

                repeat eexists; [| solve_returns_provenance].
                cbn.
                match goal with
                | |- context [ read_byte_raw (set_byte_raw _ ?p1 _) ?p2 ] =>
                    pose proof Z.eq_dec p1 p2 as [NDISJOINT | DISJOINT]
                end.

                - rewrite set_byte_raw_eq; [| solve [eauto]].
                  split; auto.

                  break_byte_allocated_in ALLOC.
                  rewrite NDISJOINT in *.
                  unfold mem_state_memory in *.
                  rewrite READ in *.
                  destruct ALLOC; auto.
                - rewrite set_byte_raw_neq; [| solve [eauto]].
                  break_byte_allocated_in ALLOC.
                  unfold mem_state_memory in *.
                  break_match; [break_match|]; firstorder.
              }
              { (* TODO: solve_byte_allocated *)
                intros ALLOC.

                repeat eexists; [| solve_returns_provenance].
                break_byte_allocated_in ALLOC.
                unfold mem_state_memory in *.
                cbn in *.
                match goal with
                | ALLOC : context [ read_byte_raw (set_byte_raw _ ?p1 _) ?p2 ] |- _ =>
                    pose proof Z.eq_dec p1 p2 as [NDISJOINT | DISJOINT]
                end.

                - rewrite NDISJOINT in *.
                  rewrite set_byte_raw_eq in ALLOC; [| solve [eauto]].
                  rewrite READ in *.
                  tauto.
                - rewrite set_byte_raw_neq in ALLOC; [| solve [eauto]].
                  break_match; [break_match|]; firstorder.
              }
            -- (* Frame stack preserved *)
              solve_frame_stack_preserved.
            -- (* Heap preserved *)
              solve_heap_preserved.
            -- (* TODO: solve_read_byte_allowed_all_preserved *)
              unfold read_byte_allowed_all_preserved.
              intros addr.
              split; intros [aid' [ALLOC ALLOWED]]; exists aid'.
              { unfold mem_state_memory in *.
                split; repeat eexists; [|solve_returns_provenance|]; cbn.
                - match goal with
                  | |- context [ read_byte_raw (set_byte_raw _ ?p1 _) ?p2 ] =>
                      pose proof Z.eq_dec p1 p2 as [NDISJOINT | DISJOINT]
                  end.
                  + rewrite NDISJOINT in *.
                    rewrite set_byte_raw_eq; [| solve [eauto]].
                    split; auto.
                    break_byte_allocated_in ALLOC.
                    break_match_hyp.
                    break_match_hyp.
                    cbn in ALLOC.
                    cbn in ALLOWED.
                    inversion READ; subst; tauto.
                    destruct ALLOC as [_ CONTRA].
                    inv CONTRA.
                  + rewrite set_byte_raw_neq; [| solve [eauto]].
                    break_byte_allocated_in ALLOC.
                    break_match_hyp.
                    break_match_hyp.
                    inversion READ; subst.
                    firstorder.
                    destruct ALLOC as [_ CONTRA].
                    inv CONTRA.
                - auto.
              }
              { unfold mem_state_memory in *.
                split; repeat eexists; [|solve_returns_provenance|]; cbn.
                - break_byte_allocated_in ALLOC.
                  cbn in *.
                  match goal with
                  | ALLOC : context [ read_byte_raw (set_byte_raw _ ?p1 _) ?p2 ] |- _ =>
                      pose proof Z.eq_dec p1 p2 as [NDISJOINT | DISJOINT]
                  end.
                  + rewrite NDISJOINT in *.
                    rewrite set_byte_raw_eq in ALLOC; [| solve [eauto]].
                    rewrite READ in *.
                    tauto.
                  + rewrite set_byte_raw_neq in ALLOC; [| solve [eauto]].
                    break_match_hyp.
                    break_match_hyp.
                    tauto.
                    tauto.
                - auto.
              }
            -- (* TODO: solve_write_byte_allowed_all_preserved *)
              intros addr.
              split; intros [aid' [ALLOC ALLOWED]]; exists aid'.
              { unfold mem_state_memory in *.
                split; repeat eexists; [|solve_returns_provenance|]; cbn.
                - match goal with
                  | |- context [ read_byte_raw (set_byte_raw _ ?p1 _) ?p2 ] =>
                      pose proof Z.eq_dec p1 p2 as [NDISJOINT | DISJOINT]
                  end.
                  + rewrite NDISJOINT in *.
                    rewrite set_byte_raw_eq; [| solve [eauto]].
                    split; auto.
                    break_byte_allocated_in ALLOC.
                    break_match_hyp.
                    break_match_hyp.
                    inversion READ; subst.
                    firstorder.
                    destruct ALLOC as [_ CONTRA].
                    inv CONTRA.
                  + rewrite set_byte_raw_neq; [| solve [eauto]].
                    break_byte_allocated_in ALLOC.
                    break_match_hyp.
                    break_match_hyp.
                    inversion READ; subst.
                    firstorder.
                    destruct ALLOC as [_ CONTRA].
                    inv CONTRA.
                - auto.
              }
              { unfold mem_state_memory in *.
                split; repeat eexists; [|solve_returns_provenance|]; cbn.
                - break_byte_allocated_in ALLOC.
                  cbn in *.
                  match goal with
                  | ALLOC : context [ read_byte_raw (set_byte_raw _ ?p1 _) ?p2 ] |- _ =>
                      pose proof Z.eq_dec p1 p2 as [NDISJOINT | DISJOINT]
                  end.
                  + rewrite NDISJOINT in *.
                    rewrite set_byte_raw_eq in ALLOC; [| solve [eauto]].
                    rewrite READ in *.
                    tauto.
                  + rewrite set_byte_raw_neq in ALLOC; [| solve [eauto]].
                    break_match_hyp.
                    break_match_hyp.
                    tauto.
                    tauto.
                - auto.
              }
            -- (* TODO: solve_preserve_allocation_ids *)
              unfold preserve_allocation_ids.
              unfold used_provenance_prop.
              intros pr'.
              split; intros LE; cbn in *; auto.
      - (* UB due to provenance *)
        left.
        Ltac solve_write_byte_MemPropT_contra READ ACCESS :=
          solve [repeat eexists; right;
                 repeat eexists; cbn;
                 try rewrite READ in *; cbn in *;
                 try rewrite ACCESS in *; cbn in *;
                 tauto].

        repeat eexists; cbn.
        intros m2 CONTRA.

        (* Access not allowed *)
        inversion CONTRA.
        unfold write_byte_allowed in *.
        unfold byte_allocated, byte_allocated_MemPropT in *.
        unfold addr_allocated_prop in *.
        destruct byte_write_succeeds0 as [aid' [ALLOC ALLOWED]].

        unfold mem_state_memory in *.
        break_byte_allocated_in ALLOC.
        cbn in *.
        rewrite READ in *.
        destruct ALLOC as [EQ AID_ALLOWED].

        destruct (aid_eq_dec aid' aid); inv AID_ALLOWED.
        rewrite ACCESS in ALLOWED; inv ALLOWED.
      - (* UB from accessing unallocated memory *)
        left.
        repeat eexists; cbn.
        intros m2 CONTRA.

        (* Accessing unallocated memory *)
        inversion CONTRA.
        unfold write_byte_allowed in *.
        unfold byte_allocated, byte_allocated_MemPropT in *.
        unfold addr_allocated_prop in *.
        destruct byte_write_succeeds0 as [aid' [ALLOC ALLOWED]].

        unfold mem_state_memory in *.
        break_byte_allocated_in ALLOC.
        cbn in *.
        rewrite READ in *.
        destruct ALLOC as [EQ AID_ALLOWED].
        inv AID_ALLOWED.

        Unshelve.
        all: exact ""%string.
    Qed.

    Lemma allocate_bytes_correct :
      forall dt init_bytes, exec_correct (allocate_bytes dt init_bytes) (allocate_bytes_spec_MemPropT dt init_bytes).
    Proof.
      unfold exec_correct.
      intros dt init_bytes ms st VALID.

      (* Need to destruct ahead of time so we know if UB happens *)
      pose proof (dtyp_eq_dec dt DTYPE_Void) as [VOID | NVOID].

      destruct (mem_state_fresh_provenance ms) as [pr' ms_fresh_pr] eqn:FRESH.

      { (* Can't allocate VOID *)
        left.
        repeat eexists; right.
        exists ms_fresh_pr. exists pr'.
        split.
        { (* fresh_provenance *)
          unfold fresh_provenance.
          cbn.
          destruct ms; inversion FRESH; cbn in *; subst.

          (* TODO: separate into lemmas? *)
          cbn.
          split; [|split; [|split; [|split; [|split]]]].
          - (* TODO: solve_extend_provenance *)
            unfold extend_provenance.
            split.
            intros pr USED.
            { eapply provenance_lt_trans; eauto.
              eapply provenance_lt_next_provenance.
            }

            eapply mem_state_fresh_provenance_fresh; eauto.
          - (* TODO: solve_read_byte_preserved *)
            unfold read_byte_preserved.
            split.
            cbn.
            + (* TODO: solve_read_byte_allowed_all_preserved *)
              unfold read_byte_allowed_all_preserved; intros ptr.
              split; intros [aid [ALLOC ALLOWED]];
                solve_read_byte_allowed.
            + (* TODO: solve_read_byte_prop_all_preserved *)
              unfold read_byte_prop_all_preserved.
              intros ptr byte.
              split; intros PROP; solve_read_byte_prop.
          - (* TODO: solve_write_byte_allowed_all_preserved *)
            unfold write_byte_allowed_all_preserved; intros ptr.
            split; intros [aid [ALLOC ALLOWED]];
              solve_write_byte_allowed.
          - (* TODO: solve_allocations_preserved *)
            unfold allocations_preserved; intros ptr aid.
            split; intros PROP;
              solve_byte_allocated.
          - solve_frame_stack_preserved.
          - solve_heap_preserved.
        }
        {
          repeat eexists.
          left. intros m2 ptr ptrs.
          intros SUCC.
          inversion SUCC.
          contradiction.
        }
      }

      { (* dt is non-void, allocation may succeed *)
        right.
        split; [|split].
        - (* Error *)
          (* Always allowed to error *)
          repeat eexists. left.
          cbn. auto.
        - (* OOM *)
          (* Always allowed to oom *)
          repeat eexists. left.
          cbn. auto.
        - (* Success *)
          unfold allocate_bytes_spec_MemPropT.
          intros st_final ms_final alloc_addr RUN.
          unfold allocate_bytes in *.
          destruct (dtyp_eq_dec dt DTYPE_Void); try contradiction.
          destruct (N.eq_dec (sizeof_dtyp dt) (N.of_nat (Datatypes.length init_bytes))) eqn:Hlen.
          2 : {
            rewrite MemMonad_run_raise_ub in RUN.
            apply rbm_raise_ret_inv in RUN; try tauto.
            typeclasses eauto.
          }

          { cbn in RUN.
            rewrite MemMonad_run_bind in RUN; auto.
            pose proof MemMonad_run_fresh_provenance ms st VALID
              as [ms' [pr' [FRESH_PR [VALID' [GET_PR [EXTEND_PR [NUSED_PR USED_PR]]]]]]].
            rewrite FRESH_PR in RUN.
            rewrite bind_ret_l in RUN.

            rewrite MemMonad_run_bind in RUN; auto.
            pose proof MemMonad_run_fresh_sid ms' st VALID' as [st' [sid [RUN_FRESH_SID [VALID'' FRESH_SID]]]].
            rewrite RUN_FRESH_SID in RUN.
            rewrite bind_ret_l in RUN.

            rewrite MemMonad_run_bind in RUN.
            rewrite MemMonad_get_mem_state in RUN.
            rewrite bind_ret_l in RUN.

            destruct ms as [ms_stack ms_prov].
            destruct ms_stack as [mem frames heap].

            destruct ms' as [[mem' fs' h'] pr''].
            unfold ms_get_memory in GET_PR.
            cbn in GET_PR.
            inv GET_PR.
            cbn in RUN.
            rename mem' into mem.
            rename fs' into frames.
            rename h' into heap.

            (* TODO: need to know something about get_consecutive_ptrs *)
            unfold get_consecutive_ptrs in *; cbn in RUN.
            do 2 rewrite MemMonad_run_bind in RUN; auto.
            rewrite bind_bind in RUN.
            destruct (intptr_seq 0 (Datatypes.length init_bytes)) as [NOOM_seq | OOM_seq] eqn:HSEQ.
            { (* no oom *)
              cbn in RUN.
              rewrite MemMonad_run_ret in RUN; auto.
              rewrite bind_ret_l in RUN.

              match goal with
              | RUN : context [Util.map_monad ?f ?s] |- _ =>
                  destruct (Util.map_monad f s) as [ERR | ptrs] eqn:HMAPM
              end.

              { (* Error *)
                cbn in RUN.
                rewrite MemMonad_run_raise_error in RUN.
                rewrite rbm_raise_bind in RUN.
                exfalso.
                symmetry in RUN.
                eapply MemMonad_eq1_raise_error_inv in RUN.
                auto.
                typeclasses eauto.
              }

              (* SUCCESS *)
              cbn in RUN.
              rewrite MemMonad_run_ret in RUN; auto.
              rewrite bind_ret_l in RUN.

              rewrite MemMonad_run_bind in RUN; auto.
              rewrite MemMonad_get_mem_state in RUN.
              rewrite bind_ret_l in RUN.

              rewrite MemMonad_run_bind in RUN; auto.
              rewrite MemMonad_put_mem_state in RUN.
              rewrite bind_ret_l in RUN.
              rewrite MemMonad_run_ret in RUN; auto.
              cbn in RUN.

              apply eq1_ret_ret in RUN; [|typeclasses eauto].
              inv RUN.
              (* Done extracting information from RUN. *)

              rename ptrs into ptrs_alloced.
              destruct ptrs_alloced as [ _ | alloc_addr ptrs] eqn:HALLOC_PTRS.
              { (* Empty ptr list... Not a contradiction, can allocate 0 bytes... MAY not be unique. *)
                cbn in HMAPM.
                cbn.
                assert (init_bytes = []) as INIT_NIL.
                { destruct init_bytes; auto.
                  cbn in *.
                  rewrite IP.from_Z_0 in HSEQ.
                  destruct (Util.map_monad IP.from_Z (Zseq 1 (Datatypes.length init_bytes))); inv HSEQ.
                  cbn in HMAPM.
                  rewrite handle_gep_addr_0 in HMAPM.
                  match goal with
                  | H:
                    context [ map_monad ?f ?l ] |- _ =>
                      destruct (map_monad f l)
                  end; inv HMAPM.
                }
                subst.
                cbn in *; inv HSEQ.
                cbn in *.

                (* Size is 0, nothing is allocated... *)
                exists ({| ms_memory_stack := mkMemoryStack mem frames heap; ms_provenance := pr'' |}).
                exists pr'.

                split; [solve_fresh_provenance_invariants|].

                eexists.
                set (alloc_addr :=
                       int_to_ptr (next_memory_key (mkMemoryStack mem frames heap))
                                  (allocation_id_to_prov (provenance_to_allocation_id pr'))).
                exists (alloc_addr, []).

                split.
                2: {
                  split; eauto.
                }

                { (* TODO: solve_allocate_bytes_succeeds_spec *)
                  split.
                  - (* allocate_bytes_consecutive *)
                    cbn.
                    repeat eexists.
                  - (* allocate_bytes_address_provenance *)
                    subst alloc_addr.
                    apply int_to_ptr_provenance.
                  - (* allocate_bytes_addresses_provenance *)
                    intros ptr IN.
                    inv IN.
                  - (* allocate_bytes_provenances_preserved *)
                    intros pr'0.
                    unfold used_provenance_prop.
                    cbn.
                    reflexivity.
                  - (* allocate_bytes_was_fresh_byte *)
                    intros ptr IN.
                    inv IN.
                  - (* allocate_bytes_now_byte_allocated *)
                    intros ptr IN.
                    inv IN.
                  - (* allocate_bytes_preserves_old_allocations *)
                    intros ptr aid NIN.
                    reflexivity.
                  - (* alloc_bytes_new_reads_allowed *)
                    intros ptr IN.
                    inv IN.
                  - (* alloc_bytes_old_reads_allowed *)
                    intros ptr' DISJOINT.
                    split; auto.
                  - (* alloc_bytes_new_reads *)
                    intros p ix byte NTH1 NTH2.
                    apply Util.not_Nth_nil in NTH1.
                    contradiction.
                  - (* alloc_bytes_old_reads *)
                    intros ptr' byte DISJOINT.
                    split; auto.
                  - (* alloc_bytes_new_writes_allowed *)
                    intros p IN.
                    inv IN.
                  - (* alloc_bytes_old_writes_allowed *)
                    intros ptr' DISJOINT.
                    split; auto.
                  - (* alloc_bytes_add_to_frame *)
                    intros fs1 fs2 POP ADD.
                    cbn in ADD; subst; auto.
                    unfold memory_stack_frame_stack_prop in *.
                    cbn in *.
                    unfold memory_stack_frame_stack.
                    cbn.
                    setoid_rewrite add_all_to_frame_nil_preserves_frames.
                    cbn.
                    rewrite POP.
                    auto.
                  - (* Heap preserved *)
                    solve_heap_preserved.
                  - (* Non-void *)
                    auto.
                  - (* Length *)
                    cbn; auto.
                }
              }

              (* Non-empty allocation *)
              cbn.

              exists ({| ms_memory_stack := (mkMemoryStack mem frames heap); ms_provenance := pr'' |}).
              exists pr'.

              split; [solve_fresh_provenance_invariants|].

              Open Scope positive.
              exists ({|
    ms_memory_stack :=
              add_all_to_frame
                (mkMemoryStack
                   (add_all_index
                   (map (fun b : SByte => (b, provenance_to_allocation_id pr'))
                      init_bytes) (next_memory_key (mkMemoryStack mem frames heap)) mem) frames heap)
                (ptr_to_int alloc_addr :: map ptr_to_int ptrs);
    ms_provenance := pr''
  |}).
              exists (alloc_addr, (alloc_addr :: ptrs)).

              Close Scope positive.
              assert (int_to_ptr
                        (next_memory_key (mkMemoryStack mem frames heap)) (allocation_id_to_prov (provenance_to_allocation_id pr')) = alloc_addr) as EQALLOC.
              {
                destruct (Datatypes.length init_bytes) eqn:LENBYTES.
                { cbn in HSEQ; inv HSEQ.
                  cbn in *.
                  inv HMAPM.
                }

                rewrite intptr_seq_succ in HSEQ.
                cbn in HSEQ.
                rewrite IP.from_Z_0 in HSEQ.
                destruct (intptr_seq 1 n0); inv HSEQ.

                unfold Util.map_monad in HMAPM.
                inversion HMAPM.
                inversion HMAPM.
                (* Fragile proof... *)
                break_match_hyp; inv H2.
                break_match_hyp; inv H3.

                rewrite handle_gep_addr_0 in Heqs.
                inv Heqs.
                reflexivity.
              }

              split.
              { (* TODO: solve_allocate_bytes_succeeds_spec *)
                split.
                - (* allocate_bytes_consecutive *)
                  do 2 eexists.
                  split.
                  + cbn.
                    rewrite HSEQ.
                    cbn.
                    split; reflexivity.
                  + rewrite EQALLOC in HMAPM.
                    rewrite HMAPM.
                    cbn.
                    split; reflexivity.
                - (* allocate_bytes_address_provenance *)
                    subst alloc_addr.
                    apply int_to_ptr_provenance.
                - (* allocate_bytes_addressses_provenance *)
                  (* TODO: Need map_monad lemmas *)
                  assert (@inr string (list addr) = ret) as INR.
                  reflexivity.
                  rewrite INR in HMAPM.
                  clear INR.

                  intros ptr IN.
                  pose proof map_monad_err_In _ _ _ _ HMAPM IN as MAPIN.
                  destruct MAPIN as [ip [GENPTR INip]].

                  apply handle_gep_addr_preserves_provenance in GENPTR.
                  rewrite int_to_ptr_provenance in GENPTR.
                  auto.
                - (* allocate_bytes_provenances_preserved *)
                  intros pr'0.
                  split; eauto.
                - (* allocate_bytes_was_fresh_byte *)
                  intros ptr IN.

                  unfold byte_not_allocated.
                  unfold byte_allocated.
                  unfold byte_allocated_MemPropT.
                  intros aid CONTRA.
                  break_lifted_addr_allocated_prop_in CONTRA.
                  cbn in CONTRA.

                  rewrite read_byte_raw_next_memory_key in CONTRA.
                  2: {
                    pose proof map_monad_err_In _ _ _ _ HMAPM IN as MAPIN.
                    destruct MAPIN as [ip [GENPTR INip]].

                    apply handle_gep_addr_ix in GENPTR.
                    rewrite ptr_to_int_int_to_ptr in GENPTR.
                    rewrite GENPTR.

                    assert (IP.to_Z ip >= 0).
                    { eapply intptr_seq_ge; eauto.
                    }

                    rewrite sizeof_dtyp_i8.
                    rewrite next_memory_key_next_key.
                    lia.
                  }

                  destruct CONTRA as [_ CONTRA].
                  inversion CONTRA.
                - (* allocate_bytes_now_byte_allocated *)
                  (* TODO: solve_byte_allocated *)
                  intros ptr IN.

                  (* New bytes are allocated because the exist in the add_all_index block *)
                  pose proof map_monad_err_In _ _ _ _ HMAPM IN as MAPIN.
                  destruct MAPIN as [ip [GENPTR INip]].

                  repeat eexists; [| solve_returns_provenance].
                  cbn.
                  unfold mem_state_memory.
                  cbn.
                  rewrite add_all_to_frame_preserves_memory.
                  cbn.

                  match goal with
                  | H: _ |- context [ read_byte_raw (add_all_index ?l ?z ?mem) ?p ] =>
                      pose proof read_byte_raw_add_all_index_in_exists mem l z p as ?READ
                  end.

                  forward READ.
                  { (* Bounds *)
                    pose proof (map_monad_err_In _ _ _ _ HMAPM IN) as [ix' [GENp IN_ix']].
                    apply handle_gep_addr_ix in GENp.
                    rewrite sizeof_dtyp_i8 in GENp.
                    replace (Z.of_N 1 * IP.to_Z ix') with (IP.to_Z ix') in GENp by lia.
                    rewrite ptr_to_int_int_to_ptr in GENp.
                    apply (in_intptr_seq _ _ _ _ HSEQ) in IN_ix'.

                    rewrite Zlength_map.
                    rewrite <- Zlength_correct in IN_ix'.
                    lia.
                  }

                  destruct READ as [(byte', aid_byte) [NTH READ]].
                  rewrite list_nth_z_map in NTH.
                  unfold option_map in NTH.
                  break_match_hyp; inv NTH.

                  (* Need this unfold for rewrite >_< *)
                  unfold mem_byte in *.
                  rewrite READ.
                  split; try tauto.
                  apply aid_eq_dec_refl.
                - (* allocate_bytes_preserves_old_allocations *)
                  intros ptr aid DISJOINT.
                  (* TODO: not enough for ptr to not be in ptrs list. Must be disjoint.

                     E.g., problem if provenances are different.
                   *)

                  split; intros ALLOC.
                  + repeat eexists; [| solve_returns_provenance];
                      cbn; unfold mem_state_memory; cbn.
                    rewrite add_all_to_frame_preserves_memory.
                    cbn.

                    erewrite read_byte_raw_add_all_index_out.
                    2: {
                      rewrite Zlength_map.
                      pose proof (Z_lt_ge_dec (ptr_to_int ptr) (next_memory_key (mkMemoryStack mem frames heap))) as [LTNEXT | GENEXT]; auto.
                      pose proof (Z_ge_lt_dec (ptr_to_int ptr) (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes)) as [LTNEXT' | GENEXT']; auto.

                                            exfalso.

                      pose proof (@exists_in_bounds_le_lt (next_memory_key (mkMemoryStack mem frames heap)) (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes) (ptr_to_int ptr)) as BOUNDS.
                      forward BOUNDS. lia.
                      destruct BOUNDS as [ix [[BOUNDLE BOUNDLT] EQ]].

                      replace (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes - next_memory_key (mkMemoryStack mem frames heap)) with (Zlength init_bytes) in BOUNDLT by lia.

                      (* Want to use bound in... *)
                      (* Need to get what ix is as an IP... *)
                      destruct (IP.from_Z ix) eqn:IX.
                      2: {
                         (* HSEQ succeeding should make this a contradiction *)
                        apply intptr_seq_from_Z with (x := ix) in HSEQ.
                        destruct HSEQ as [ipx [EQ' INSEQ]].
                        rewrite EQ' in IX.
                        inv IX.

                        rewrite <- Zlength_correct.
                        lia.
                      }

                      pose proof (in_intptr_seq _ _ i _ HSEQ) as [IN BOUNDIN].
                      apply IP.from_Z_to_Z in IX; subst.
                      forward BOUNDIN.
                      rewrite <- Zlength_correct.
                      lia.

                      set (p := int_to_ptr (ptr_to_int ptr) (allocation_id_to_prov (provenance_to_allocation_id pr'))).

                      (* I believe that p is necessarily in the result of HMAPM. *)
                      assert (In p (int_to_ptr (next_memory_key (mkMemoryStack mem frames heap))
                                               (allocation_id_to_prov
                                                  (provenance_to_allocation_id pr')) :: ptrs)) as PIN.
                      { clear - HMAPM HSEQ GENEXT GENEXT' i EQ BOUNDIN.

                        eapply map_monad_err_In' with (y:=i) in HMAPM; auto.

                        destruct HMAPM as [x [GENPTR IN]].
                        symmetry in GENPTR.
                        pose proof GENPTR as GENPTR'.
                        apply handle_gep_addr_ix in GENPTR.
                        rewrite sizeof_dtyp_i8 in GENPTR.
                        replace (Z.of_N 1 * IP.to_Z i) with (IP.to_Z i) in GENPTR by lia.
                        rewrite ptr_to_int_int_to_ptr in GENPTR.
                        rewrite <- GENPTR in EQ.

                        subst p.
                        rewrite EQ.
                        rewrite int_to_ptr_ptr_to_int; auto.

                        apply handle_gep_addr_preserves_provenance in GENPTR'.
                        rewrite int_to_ptr_provenance in GENPTR'.
                        symmetry; auto.
                      }

                      eapply map_monad_err_In with (x:=p) in HMAPM; auto.

                      (* DISJOINT should be a contradition now *)
                      exfalso.
                      (* ?p doesn't have to be ptr', but ptr_to_int ?p = ptr_to_int ptr' *)
                      eapply DISJOINT with (p:=p).
                      apply PIN.

                      subst p.
                      rewrite ptr_to_int_int_to_ptr.
                      reflexivity.
                    }

                    break_byte_allocated_in ALLOC.
                    cbn in ALLOC.

                    break_match; [break_match|]; split; tauto.
                  + break_byte_allocated_in ALLOC.
                    cbn in ALLOC.

                    unfold mem_state_memory in ALLOC; cbn in ALLOC.
                    rewrite add_all_to_frame_preserves_memory in ALLOC; cbn in ALLOC.

                    erewrite read_byte_raw_add_all_index_out in ALLOC.
                    2: {
                      rewrite Zlength_map.
                      pose proof (Z_lt_ge_dec (ptr_to_int ptr) (next_memory_key (mkMemoryStack mem frames heap))) as [LTNEXT | GENEXT]; auto.
                      pose proof (Z_ge_lt_dec (ptr_to_int ptr) (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes)) as [LTNEXT' | GENEXT']; auto.

                                            exfalso.

                      pose proof (@exists_in_bounds_le_lt (next_memory_key (mkMemoryStack mem frames heap)) (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes) (ptr_to_int ptr)) as BOUNDS.
                      forward BOUNDS. lia.
                      destruct BOUNDS as [ix [[BOUNDLE BOUNDLT] EQ]].

                      replace (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes - next_memory_key (mkMemoryStack mem frames heap)) with (Zlength init_bytes) in BOUNDLT by lia.

                      (* Want to use bound in... *)
                      (* Need to get what ix is as an IP... *)
                      destruct (IP.from_Z ix) eqn:IX.
                      2: {
                         (* HSEQ succeeding should make this a contradiction *)
                        apply intptr_seq_from_Z with (x := ix) in HSEQ.
                        destruct HSEQ as [ipx [EQ' INSEQ]].
                        rewrite EQ' in IX.
                        inv IX.

                        rewrite <- Zlength_correct.
                        lia.
                      }

                      pose proof (in_intptr_seq _ _ i _ HSEQ) as [IN BOUNDIN].
                      apply IP.from_Z_to_Z in IX; subst.
                      forward BOUNDIN.
                      rewrite <- Zlength_correct.
                      lia.

                      set (p := int_to_ptr (ptr_to_int ptr) (allocation_id_to_prov (provenance_to_allocation_id pr'))).

                      (* I believe that p is necessarily in the result of HMAPM. *)
                      assert (In p (int_to_ptr (next_memory_key (mkMemoryStack mem frames heap))
                                               (allocation_id_to_prov
                                                  (provenance_to_allocation_id pr')) :: ptrs)) as PIN.
                      { clear - HMAPM HSEQ GENEXT GENEXT' i EQ BOUNDIN.

                        eapply map_monad_err_In' with (y:=i) in HMAPM; auto.

                        destruct HMAPM as [x [GENPTR IN]].
                        symmetry in GENPTR.
                        pose proof GENPTR as GENPTR'.
                        apply handle_gep_addr_ix in GENPTR.
                        rewrite sizeof_dtyp_i8 in GENPTR.
                        replace (Z.of_N 1 * IP.to_Z i) with (IP.to_Z i) in GENPTR by lia.
                        rewrite ptr_to_int_int_to_ptr in GENPTR.
                        rewrite <- GENPTR in EQ.

                        subst p.
                        rewrite EQ.
                        rewrite int_to_ptr_ptr_to_int; auto.

                        apply handle_gep_addr_preserves_provenance in GENPTR'.
                        rewrite int_to_ptr_provenance in GENPTR'.
                        symmetry; auto.
                      }

                      eapply map_monad_err_In with (x:=p) in HMAPM; auto.

                      (* DISJOINT should be a contradition now *)
                      exfalso.
                      (* ?p doesn't have to be ptr', but ptr_to_int ?p = ptr_to_int ptr' *)
                      eapply DISJOINT with (p:=p).
                      apply PIN.

                      subst p.
                      rewrite ptr_to_int_int_to_ptr.
                      reflexivity.
                    }

                    repeat eexists; [| solve_returns_provenance].
                    cbn.

                    break_match; [break_match|]; split; tauto.
                - (* alloc_bytes_new_reads_allowed *)
                  intros p IN.
                  (* TODO: solve_read_byte_allowed *)
                  induction IN as [IN | IN]; subst.
                  + (* TODO: solve_read_byte_allowed *)
                    eexists.
                    split.
                    * (* TODO: solve_byte_allocated *)
                      repeat eexists; [| solve_returns_provenance].
                      cbn.
                      unfold mem_state_memory.
                      cbn.
                      rewrite add_all_to_frame_preserves_memory.
                      cbn in *.
                      rewrite ptr_to_int_int_to_ptr.

                      match goal with
                      | H: _ |- context [ read_byte_raw (add_all_index ?l ?z ?mem) ?p ] =>
                          pose proof read_byte_raw_add_all_index_in_exists mem l z p as ?READ
                      end.

                      forward READ.
                      { (* bounds *)
                        (* Should be a non-empty allocation *)
                        (* I know this by cons cell result of HMAPM *)
                        assert (@MonadReturnsLaws.MReturns err _ _ _ (list addr)
                                                           (int_to_ptr (next_memory_key (mkMemoryStack mem frames heap))
                                                                       (allocation_id_to_prov (provenance_to_allocation_id pr')) :: ptrs)
                                                           (Util.map_monad
            (fun ix : IP.intptr =>
             handle_gep_addr (DTYPE_I 8)
               (int_to_ptr (next_memory_key (mkMemoryStack mem frames heap))
                  (allocation_id_to_prov (provenance_to_allocation_id pr')))
               [Events.DV.DVALUE_IPTR ix]) NOOM_seq)) as MAPRET.
                        { cbn. red.
                          auto.
                        }

                        eapply map_monad_length in MAPRET.
                        cbn in MAPRET.
                        rewrite Zlength_map.
                        rewrite Zlength_correct.
                        apply intptr_seq_len in HSEQ.
                        lia.
                      }

                      destruct READ as [(byte, aid_byte) [NTH READ]].
                      rewrite list_nth_z_map in NTH.
                      unfold option_map in NTH.
                      break_match_hyp; inv NTH.

                      (* Need this unfold for rewrite >_< *)
                      unfold mem_byte in *.
                      rewrite READ.

                      split; auto.
                      apply aid_eq_dec_refl.
                    * solve_access_allowed.
                  + (* TODO: solve_read_byte_allowed *)
                    repeat eexists; [| solve_returns_provenance |];
                    cbn.
                    unfold mem_state_memory.
                    cbn.
                    rewrite add_all_to_frame_preserves_memory.
                    cbn in *.
                    rewrite ptr_to_int_int_to_ptr.

                    match goal with
                    | H: _ |- context [ read_byte_raw (add_all_index ?l ?z ?mem) ?p ] =>
                        pose proof read_byte_raw_add_all_index_in_exists mem l z p as ?READ
                    end.

                    forward READ.
                    { (* Bounds *)
                      assert (In p (int_to_ptr (next_memory_key (mkMemoryStack mem frames heap))
                                               (allocation_id_to_prov (provenance_to_allocation_id pr')) :: ptrs)) as IN'.
                      { right; auto.
                      }

                      pose proof (map_monad_err_In _ _ _ _ HMAPM IN') as [ix' [GENp IN_ix']].
                      apply handle_gep_addr_ix in GENp.
                      rewrite sizeof_dtyp_i8 in GENp.
                      replace (Z.of_N 1 * IP.to_Z ix') with (IP.to_Z ix') in GENp by lia.
                      rewrite ptr_to_int_int_to_ptr in GENp.
                      apply (in_intptr_seq _ _ _ _ HSEQ) in IN_ix'.

                      rewrite Zlength_map.
                      rewrite <- Zlength_correct in IN_ix'.
                      lia.
                    }

                    destruct READ as [(byte, aid_byte) [NTH READ]].
                    rewrite list_nth_z_map in NTH.
                    unfold option_map in NTH.
                    break_match_hyp; inv NTH.

                    (* Need this unfold for rewrite >_< *)
                    unfold mem_byte in *.
                    rewrite READ.

                    split; auto.
                    apply aid_eq_dec_refl.

                    (* Need to look up provenance via IN *)
                    (* TODO: solve_access_allowed *)
                    eapply map_monad_err_In in HMAPM.
                    2: {
                      cbn; right; eauto.
                    }

                    destruct HMAPM as [ip [GENPTR INip]].
                    apply handle_gep_addr_preserves_provenance in GENPTR.
                    rewrite int_to_ptr_provenance in GENPTR.
                    rewrite <- GENPTR.

                    solve_access_allowed.
                - (* alloc_bytes_old_reads_allowed *)
                  intros ptr' DISJOINT.
                  split; intros ALLOWED.
                  + (* TODO: solve_read_byte_allowed. *)
                    break_access_hyps.
                    (* TODO: move this into break_access_hyps? *)
                    break_byte_allocated_in ALLOC.

                    break_match; [break_match|]; destruct ALLOC as [EQM AID]; subst; [|inv AID].

                    repeat eexists; [| solve_returns_provenance |].
                    cbn.
                    unfold mem_state_memory.
                    cbn.
                    rewrite add_all_to_frame_preserves_memory.

                    cbn.
                    rewrite read_byte_raw_add_all_index_out.
                    2: {
                      left.
                      rewrite next_memory_key_next_key.
                      eapply read_byte_raw_lt_next_memory_key; eauto.
                    }

                    cbn in *.
                    rewrite Heqo; eauto.

                    solve_access_allowed.
                  + (* TODO: solve_read_byte_allowed. *)
                    break_access_hyps.
                    (* TODO: move this into break_access_hyps? *)
                    break_byte_allocated_in ALLOC.
                    cbn in ALLOC.

                    break_match; [break_match|]; destruct ALLOC as [EQM AID]; subst; [|inv AID].

                    repeat eexists; [| solve_returns_provenance |].
                    cbn.
                    unfold mem_state_memory in *.
                    cbn in *.
                    rewrite add_all_to_frame_preserves_memory in Heqo.
                    cbn in *.

                    rewrite read_byte_raw_add_all_index_out in Heqo.
                    2: {
                      (* If read is in the bounds of add_all_index then that means it's not disjoint...

                       *)

                      (*
                        If ptr' is such that...

                        ptr' >= next_mem_key and
                        ptr' < next_mem_key + length

                        then ptr' is in the allocated pointers, and
                        therefore DISJOINT doesn't hold.
                       *)
                      rewrite Zlength_map.
                      pose proof (Z_lt_ge_dec (ptr_to_int ptr') (next_memory_key (mkMemoryStack mem frames heap))) as [LTNEXT | GENEXT]; auto.
                      pose proof (Z_ge_lt_dec (ptr_to_int ptr') (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes)) as [LTNEXT' | GENEXT']; auto.

                      exfalso.

                      pose proof (@exists_in_bounds_le_lt (next_memory_key (mkMemoryStack mem frames heap)) (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes) (ptr_to_int ptr')) as BOUNDS.
                      forward BOUNDS. lia.
                      destruct BOUNDS as [ix [[BOUNDLE BOUNDLT] EQ]].

                      replace (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes - next_memory_key (mkMemoryStack mem frames heap)) with (Zlength init_bytes) in BOUNDLT by lia.

                      (* Want to use bound in... *)
                      (* Need to get what ix is as an IP... *)
                      destruct (IP.from_Z ix) eqn:IX.
                      2: {
                         (* HSEQ succeeding should make this a contradiction *)
                        apply intptr_seq_from_Z with (x := ix) in HSEQ.
                        destruct HSEQ as [ipx [EQ' INSEQ]].
                        rewrite EQ' in IX.
                        inv IX.

                        rewrite <- Zlength_correct.
                        lia.
                      }

                      pose proof (in_intptr_seq _ _ i _ HSEQ) as [IN BOUNDIN].
                      apply IP.from_Z_to_Z in IX; subst.
                      forward BOUNDIN.
                      rewrite <- Zlength_correct.
                      lia.

                      set (p := int_to_ptr (ptr_to_int ptr') (allocation_id_to_prov (provenance_to_allocation_id pr'))).

                      (* I believe that p is necessarily in the result of HMAPM. *)
                      assert (In p (int_to_ptr (next_memory_key (mkMemoryStack mem frames heap))
                                               (allocation_id_to_prov
                                                  (provenance_to_allocation_id pr')) :: ptrs)) as PIN.
                      { clear - HMAPM HSEQ GENEXT GENEXT' i EQ BOUNDIN.

                        eapply map_monad_err_In' with (y:=i) in HMAPM; auto.

                        destruct HMAPM as [x [GENPTR IN]].
                        symmetry in GENPTR.
                        pose proof GENPTR as GENPTR'.
                        apply handle_gep_addr_ix in GENPTR.
                        rewrite sizeof_dtyp_i8 in GENPTR.
                        replace (Z.of_N 1 * IP.to_Z i) with (IP.to_Z i) in GENPTR by lia.
                        rewrite ptr_to_int_int_to_ptr in GENPTR.
                        rewrite <- GENPTR in EQ.

                        subst p.
                        rewrite EQ.
                        rewrite int_to_ptr_ptr_to_int; auto.

                        apply handle_gep_addr_preserves_provenance in GENPTR'.
                        rewrite int_to_ptr_provenance in GENPTR'.
                        symmetry; auto.
                      }

                      eapply map_monad_err_In with (x:=p) in HMAPM; auto.

                      (* DISJOINT should be a contradition now *)
                      exfalso.
                      (* ?p doesn't have to be ptr', but ptr_to_int ?p = ptr_to_int ptr' *)
                      eapply DISJOINT with (p:=p).
                      apply PIN.

                      subst p.
                      rewrite ptr_to_int_int_to_ptr.
                      reflexivity.
                    }

                    rewrite Heqo; eauto.

                    solve_access_allowed.
                - (* alloc_bytes_new_reads *)
                  intros p ix byte ADDR BYTE.
                  cbn.
                  repeat eexists.
                  unfold mem_state_memory.
                  cbn.
                  rewrite add_all_to_frame_preserves_memory.
                  cbn.

                  match goal with
                  | H: _ |- context [ read_byte_raw (add_all_index ?l ?z ?mem) ?p ] =>
                      pose proof read_byte_raw_add_all_index_in_exists mem l z p as ?READ
                  end.

                  forward READ.
                  { (* Bounds *)
                    pose proof (Nth_In ADDR) as IN.
                    pose proof (map_monad_err_In _ _ _ _ HMAPM IN) as [ix' [GENp IN_ix']].
                    apply handle_gep_addr_ix in GENp.
                    rewrite sizeof_dtyp_i8 in GENp.
                    replace (Z.of_N 1 * IP.to_Z ix') with (IP.to_Z ix') in GENp by lia.
                    rewrite ptr_to_int_int_to_ptr in GENp.
                    apply (in_intptr_seq _ _ _ _ HSEQ) in IN_ix'.

                    rewrite Zlength_map.
                    rewrite <- Zlength_correct in IN_ix'.
                    lia.
                  }

                  destruct READ as [(byte', aid_byte) [NTH READ]].
                  rewrite list_nth_z_map in NTH.
                  unfold option_map in NTH.
                  break_match_hyp; inv NTH.

                  (*
                    ADDR tells me that p is in my pointers list at index `ix`...

                    Should be `next_memory_key ms + ix` basically...

                    So, `ptr_to_int p - next_memory_key (mkMemoryStack mem frames heap) = ix`

                    With that BYTE and Heqo should give me byte = byte'
                   *)
                  assert (byte = byte').
                  { pose proof (map_monad_err_Nth _ _ _ _ _ HMAPM ADDR) as [ix' [GENp NTH_ix']].
                    apply handle_gep_addr_ix in GENp.
                    rewrite ptr_to_int_int_to_ptr in GENp.
                    rewrite GENp in Heqo.

                    (* NTH_ix' -> ix = ix' *)
                    (* Heqo + BYTE *)

                    eapply intptr_seq_nth in NTH_ix'; eauto.
                    apply IP.from_Z_to_Z in NTH_ix'.
                    rewrite NTH_ix' in Heqo.

                    rewrite sizeof_dtyp_i8 in Heqo.
                    replace (next_memory_key (mkMemoryStack mem frames heap) + Z.of_N 1 * ( 0 + Z.of_nat ix) - next_memory_key (mkMemoryStack mem frames heap)) with (Z.of_nat ix) in Heqo by lia.

                    apply Util.Nth_list_nth_z in BYTE.
                    rewrite BYTE in Heqo.
                    inv Heqo; auto.
                  }

                  subst.

                  (* Need this unfold for rewrite >_< *)
                  unfold mem_byte in *.
                  rewrite READ.

                  cbn.
                  break_match.
                  split; auto.

                  apply Util.Nth_In in ADDR.
                  pose proof (map_monad_err_In _ _ _ _ HMAPM ADDR) as [ix' [GENp IN_ix']].

                  apply handle_gep_addr_preserves_provenance in GENp.
                  rewrite <- GENp in Heqb.
                  rewrite int_to_ptr_provenance in Heqb.
                  rewrite access_allowed_refl in Heqb.
                  inv Heqb.
                - (* alloc_bytes_old_reads *)
                  intros ptr' byte DISJOINT.
                  split; intros READ.
                  + (* TODO: solve_read_byte_prop *)
                    cbn.
                    repeat eexists.
                    unfold mem_state_memory.
                    cbn.
                    rewrite add_all_to_frame_preserves_memory.
                    cbn.

                    rewrite read_byte_raw_add_all_index_out.
                    2: {
                      rewrite Zlength_map.
                      pose proof (Z_lt_ge_dec (ptr_to_int ptr') (next_memory_key (mkMemoryStack mem frames heap))) as [LTNEXT | GENEXT]; auto.
                      pose proof (Z_ge_lt_dec (ptr_to_int ptr') (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes)) as [LTNEXT' | GENEXT']; auto.

                      exfalso.

                      pose proof (@exists_in_bounds_le_lt (next_memory_key (mkMemoryStack mem frames heap)) (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes) (ptr_to_int ptr')) as BOUNDS.
                      forward BOUNDS. lia.
                      destruct BOUNDS as [ix [[BOUNDLE BOUNDLT] EQ]].

                      replace (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes - next_memory_key (mkMemoryStack mem frames heap)) with (Zlength init_bytes) in BOUNDLT by lia.

                      (* Want to use bound in... *)
                      (* Need to get what ix is as an IP... *)
                      destruct (IP.from_Z ix) eqn:IX.
                      2: {
                         (* HSEQ succeeding should make this a contradiction *)
                        apply intptr_seq_from_Z with (x := ix) in HSEQ.
                        destruct HSEQ as [ipx [EQ' INSEQ]].
                        rewrite EQ' in IX.
                        inv IX.

                        rewrite <- Zlength_correct.
                        lia.
                      }

                      pose proof (in_intptr_seq _ _ i _ HSEQ) as [IN BOUNDIN].
                      apply IP.from_Z_to_Z in IX; subst.
                      forward BOUNDIN.
                      rewrite <- Zlength_correct.
                      lia.

                      set (p := int_to_ptr (ptr_to_int ptr') (allocation_id_to_prov (provenance_to_allocation_id pr'))).

                      (* I believe that p is necessarily in the result of HMAPM. *)
                      assert (In p (int_to_ptr (next_memory_key (mkMemoryStack mem frames heap))
                                               (allocation_id_to_prov
                                                  (provenance_to_allocation_id pr')) :: ptrs)) as PIN.
                      { clear - HMAPM HSEQ GENEXT GENEXT' i EQ BOUNDIN.

                        eapply map_monad_err_In' with (y:=i) in HMAPM; auto.

                        destruct HMAPM as [x [GENPTR IN]].
                        symmetry in GENPTR.
                        pose proof GENPTR as GENPTR'.
                        apply handle_gep_addr_ix in GENPTR.
                        rewrite sizeof_dtyp_i8 in GENPTR.
                        replace (Z.of_N 1 * IP.to_Z i) with (IP.to_Z i) in GENPTR by lia.
                        rewrite ptr_to_int_int_to_ptr in GENPTR.
                        rewrite <- GENPTR in EQ.

                        subst p.
                        rewrite EQ.
                        rewrite int_to_ptr_ptr_to_int; auto.

                        apply handle_gep_addr_preserves_provenance in GENPTR'.
                        rewrite int_to_ptr_provenance in GENPTR'.
                        symmetry; auto.
                      }

                      eapply map_monad_err_In with (x:=p) in HMAPM; auto.

                      (* DISJOINT should be a contradition now *)
                      exfalso.
                      (* ?p doesn't have to be ptr', but ptr_to_int ?p = ptr_to_int ptr' *)
                      eapply DISJOINT with (p:=p).
                      apply PIN.

                      subst p.
                      rewrite ptr_to_int_int_to_ptr.
                      reflexivity.
                    }

                    (* TODO: ltac to break this up *)
                    destruct READ as [ms' [ms'' [[EQ1 EQ2] READ]]]; subst.
                    cbn in READ.

                    break_match; [break_match|]; auto.
                    tauto.
                  + (* TODO: solve_read_byte_prop *)

                    (* TODO: ltac to break this up *)
                    destruct READ as [ms' [ms'' [[EQ1 EQ2] READ]]]; subst.
                    cbn in READ.
                    unfold mem_state_memory in READ.
                    cbn in READ.
                    rewrite add_all_to_frame_preserves_memory in READ.
                    cbn in READ.

                    rewrite read_byte_raw_add_all_index_out in READ.
2: {
                      rewrite Zlength_map.
                      pose proof (Z_lt_ge_dec (ptr_to_int ptr') (next_memory_key (mkMemoryStack mem frames heap))) as [LTNEXT | GENEXT]; auto.
                      pose proof (Z_ge_lt_dec (ptr_to_int ptr') (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes)) as [LTNEXT' | GENEXT']; auto.

                      exfalso.

                      pose proof (@exists_in_bounds_le_lt (next_memory_key (mkMemoryStack mem frames heap)) (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes) (ptr_to_int ptr')) as BOUNDS.
                      forward BOUNDS. lia.
                      destruct BOUNDS as [ix [[BOUNDLE BOUNDLT] EQ]].

                      replace (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes - next_memory_key (mkMemoryStack mem frames heap)) with (Zlength init_bytes) in BOUNDLT by lia.

                      (* Want to use bound in... *)
                      (* Need to get what ix is as an IP... *)
                      destruct (IP.from_Z ix) eqn:IX.
                      2: {
                         (* HSEQ succeeding should make this a contradiction *)
                        apply intptr_seq_from_Z with (x := ix) in HSEQ.
                        destruct HSEQ as [ipx [EQ' INSEQ]].
                        rewrite EQ' in IX.
                        inv IX.

                        rewrite <- Zlength_correct.
                        lia.
                      }

                      pose proof (in_intptr_seq _ _ i _ HSEQ) as [IN BOUNDIN].
                      apply IP.from_Z_to_Z in IX; subst.
                      forward BOUNDIN.
                      rewrite <- Zlength_correct.
                      lia.

                      set (p := int_to_ptr (ptr_to_int ptr') (allocation_id_to_prov (provenance_to_allocation_id pr'))).

                      (* I believe that p is necessarily in the result of HMAPM. *)
                      assert (In p (int_to_ptr (next_memory_key (mkMemoryStack mem frames heap))
                                               (allocation_id_to_prov
                                                  (provenance_to_allocation_id pr')) :: ptrs)) as PIN.
                      { clear - HMAPM HSEQ GENEXT GENEXT' i EQ BOUNDIN.

                        eapply map_monad_err_In' with (y:=i) in HMAPM; auto.

                        destruct HMAPM as [x [GENPTR IN]].
                        symmetry in GENPTR.
                        pose proof GENPTR as GENPTR'.
                        apply handle_gep_addr_ix in GENPTR.
                        rewrite sizeof_dtyp_i8 in GENPTR.
                        replace (Z.of_N 1 * IP.to_Z i) with (IP.to_Z i) in GENPTR by lia.
                        rewrite ptr_to_int_int_to_ptr in GENPTR.
                        rewrite <- GENPTR in EQ.

                        subst p.
                        rewrite EQ.
                        rewrite int_to_ptr_ptr_to_int; auto.

                        apply handle_gep_addr_preserves_provenance in GENPTR'.
                        rewrite int_to_ptr_provenance in GENPTR'.
                        symmetry; auto.
                      }

                      eapply map_monad_err_In with (x:=p) in HMAPM; auto.

                      (* DISJOINT should be a contradition now *)
                      exfalso.
                      (* ?p doesn't have to be ptr', but ptr_to_int ?p = ptr_to_int ptr' *)
                      eapply DISJOINT with (p:=p).
                      apply PIN.

                      subst p.
                      rewrite ptr_to_int_int_to_ptr.
                      reflexivity.
                    }

                    cbn.
                    repeat eexists.
                    cbn.
                    break_match; [break_match|]; tauto.
                - (* alloc_bytes_new_writes_allowed *)
                  intros p IN.
                  (* TODO: solve_write_byte_allowed. *)
                  break_access_hyps; eexists; split.
                  + (* TODO: solve_byte_allocated *)
                    repeat eexists; [| solve_returns_provenance].
                    unfold mem_state_memory.
                    cbn.
                    rewrite add_all_to_frame_preserves_memory.
                    cbn.

                  match goal with
                  | H: _ |- context [ read_byte_raw (add_all_index ?l ?z ?mem) ?p ] =>
                      pose proof read_byte_raw_add_all_index_in_exists mem l z p as ?READ
                  end.

                  forward READ.
                  { (* Bounds *)
                    pose proof (map_monad_err_In _ _ _ _ HMAPM IN) as [ix' [GENp IN_ix']].
                    apply handle_gep_addr_ix in GENp.
                    rewrite sizeof_dtyp_i8 in GENp.
                    replace (Z.of_N 1 * IP.to_Z ix') with (IP.to_Z ix') in GENp by lia.
                    rewrite ptr_to_int_int_to_ptr in GENp.
                    apply (in_intptr_seq _ _ _ _ HSEQ) in IN_ix'.

                    rewrite Zlength_map.
                    rewrite <- Zlength_correct in IN_ix'.
                    lia.
                  }

                  destruct READ as [(byte', aid_byte) [NTH READ]].
                  rewrite list_nth_z_map in NTH.
                  unfold option_map in NTH.
                  break_match_hyp; inv NTH.

                  unfold mem_byte in *.
                  rewrite READ.

                  split; auto.
                  apply aid_eq_dec_refl.
                  + solve_access_allowed.
                - (* alloc_bytes_old_writes_allowed *)
                  intros ptr' DISJOINT.
                  split; intros WRITE.
                  + (* TODO: solve_write_byte_allowed. *)
                    break_access_hyps.

                    (* TODO: move this into break_access_hyps? *)
                    break_byte_allocated_in ALLOC.
                    cbn in ALLOC.

                    break_match_hyp; [break_match_hyp|]; destruct ALLOC as [EQ1 EQ2]; inv EQ2.

                    repeat eexists; [| solve_returns_provenance |]; eauto.
                    cbn.
                    unfold mem_state_memory.
                    cbn.
                    rewrite add_all_to_frame_preserves_memory.
                    cbn.

                    rewrite read_byte_raw_add_all_index_out.
                    2: {
                      rewrite Zlength_map.
                      pose proof (Z_lt_ge_dec (ptr_to_int ptr') (next_memory_key (mkMemoryStack mem frames heap))) as [LTNEXT | GENEXT]; auto.
                      pose proof (Z_ge_lt_dec (ptr_to_int ptr') (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes)) as [LTNEXT' | GENEXT']; auto.

                      exfalso.

                      pose proof (@exists_in_bounds_le_lt (next_memory_key (mkMemoryStack mem frames heap)) (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes) (ptr_to_int ptr')) as BOUNDS.
                      forward BOUNDS. lia.
                      destruct BOUNDS as [ix [[BOUNDLE BOUNDLT] EQ]].

                      replace (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes - next_memory_key (mkMemoryStack mem frames heap)) with (Zlength init_bytes) in BOUNDLT by lia.

                      (* Want to use bound in... *)
                      (* Need to get what ix is as an IP... *)
                      destruct (IP.from_Z ix) eqn:IX.
                      2: {
                         (* HSEQ succeeding should make this a contradiction *)
                        apply intptr_seq_from_Z with (x := ix) in HSEQ.
                        destruct HSEQ as [ipx [EQ' INSEQ]].
                        rewrite EQ' in IX.
                        inv IX.

                        rewrite <- Zlength_correct.
                        lia.
                      }

                      pose proof (in_intptr_seq _ _ i _ HSEQ) as [IN BOUNDIN].
                      apply IP.from_Z_to_Z in IX; subst.
                      forward BOUNDIN.
                      rewrite <- Zlength_correct.
                      lia.

                      set (p := int_to_ptr (ptr_to_int ptr') (allocation_id_to_prov (provenance_to_allocation_id pr'))).

                      (* I believe that p is necessarily in the result of HMAPM. *)
                      assert (In p (int_to_ptr (next_memory_key (mkMemoryStack mem frames heap))
                                               (allocation_id_to_prov
                                                  (provenance_to_allocation_id pr')) :: ptrs)) as PIN.
                      { clear - HMAPM HSEQ GENEXT GENEXT' i EQ BOUNDIN.

                        eapply map_monad_err_In' with (y:=i) in HMAPM; auto.

                        destruct HMAPM as [x [GENPTR IN]].
                        symmetry in GENPTR.
                        pose proof GENPTR as GENPTR'.
                        apply handle_gep_addr_ix in GENPTR.
                        rewrite sizeof_dtyp_i8 in GENPTR.
                        replace (Z.of_N 1 * IP.to_Z i) with (IP.to_Z i) in GENPTR by lia.
                        rewrite ptr_to_int_int_to_ptr in GENPTR.
                        rewrite <- GENPTR in EQ.

                        subst p.
                        rewrite EQ.
                        rewrite int_to_ptr_ptr_to_int; auto.

                        apply handle_gep_addr_preserves_provenance in GENPTR'.
                        rewrite int_to_ptr_provenance in GENPTR'.
                        symmetry; auto.
                      }

                      eapply map_monad_err_In with (x:=p) in HMAPM; auto.

                      (* DISJOINT should be a contradition now *)
                      exfalso.
                      (* ?p doesn't have to be ptr', but ptr_to_int ?p = ptr_to_int ptr' *)
                      eapply DISJOINT with (p:=p).
                      apply PIN.

                      subst p.
                      rewrite ptr_to_int_int_to_ptr.
                      reflexivity.
                    }

                    rewrite Heqo; cbn; split; eauto.
                  + (* TODO: solve_write_byte_allowed *)
                    break_access_hyps.

                    (* TODO: move this into break_access_hyps? *)
                    break_byte_allocated_in ALLOC.
                    cbn in ALLOC.

                    unfold mem_state_memory in ALLOC.
                    cbn in ALLOC.
                    rewrite add_all_to_frame_preserves_memory in ALLOC.
                    cbn in ALLOC.

                    rewrite read_byte_raw_add_all_index_out in ALLOC.
                    2: {
                      rewrite Zlength_map.
                      pose proof (Z_lt_ge_dec (ptr_to_int ptr') (next_memory_key (mkMemoryStack mem frames heap))) as [LTNEXT | GENEXT]; auto.
                      pose proof (Z_ge_lt_dec (ptr_to_int ptr') (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes)) as [LTNEXT' | GENEXT']; auto.

                      exfalso.

                      pose proof (@exists_in_bounds_le_lt (next_memory_key (mkMemoryStack mem frames heap)) (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes) (ptr_to_int ptr')) as BOUNDS.
                      forward BOUNDS. lia.
                      destruct BOUNDS as [ix [[BOUNDLE BOUNDLT] EQ]].

                      replace (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes - next_memory_key (mkMemoryStack mem frames heap)) with (Zlength init_bytes) in BOUNDLT by lia.

                      (* Want to use bound in... *)
                      (* Need to get what ix is as an IP... *)
                      destruct (IP.from_Z ix) eqn:IX.
                      2: {
                         (* HSEQ succeeding should make this a contradiction *)
                        apply intptr_seq_from_Z with (x := ix) in HSEQ.
                        destruct HSEQ as [ipx [EQ' INSEQ]].
                        rewrite EQ' in IX.
                        inv IX.

                        rewrite <- Zlength_correct.
                        lia.
                      }

                      pose proof (in_intptr_seq _ _ i _ HSEQ) as [IN BOUNDIN].
                      apply IP.from_Z_to_Z in IX; subst.
                      forward BOUNDIN.
                      rewrite <- Zlength_correct.
                      lia.

                      set (p := int_to_ptr (ptr_to_int ptr') (allocation_id_to_prov (provenance_to_allocation_id pr'))).

                      (* I believe that p is necessarily in the result of HMAPM. *)
                      assert (In p (int_to_ptr (next_memory_key (mkMemoryStack mem frames heap))
                                               (allocation_id_to_prov
                                                  (provenance_to_allocation_id pr')) :: ptrs)) as PIN.
                      { clear - HMAPM HSEQ GENEXT GENEXT' i EQ BOUNDIN.

                        eapply map_monad_err_In' with (y:=i) in HMAPM; auto.

                        destruct HMAPM as [x [GENPTR IN]].
                        symmetry in GENPTR.
                        pose proof GENPTR as GENPTR'.
                        apply handle_gep_addr_ix in GENPTR.
                        rewrite sizeof_dtyp_i8 in GENPTR.
                        replace (Z.of_N 1 * IP.to_Z i) with (IP.to_Z i) in GENPTR by lia.
                        rewrite ptr_to_int_int_to_ptr in GENPTR.
                        rewrite <- GENPTR in EQ.

                        subst p.
                        rewrite EQ.
                        rewrite int_to_ptr_ptr_to_int; auto.

                        apply handle_gep_addr_preserves_provenance in GENPTR'.
                        rewrite int_to_ptr_provenance in GENPTR'.
                        symmetry; auto.
                      }

                      eapply map_monad_err_In with (x:=p) in HMAPM; auto.

                      (* DISJOINT should be a contradition now *)
                      exfalso.
                      (* ?p doesn't have to be ptr', but ptr_to_int ?p = ptr_to_int ptr' *)
                      eapply DISJOINT with (p:=p).
                      apply PIN.

                      subst p.
                      rewrite ptr_to_int_int_to_ptr.
                      reflexivity.
                    }

                    break_match; [break_match|].
                    repeat eexists; [| solve_returns_provenance |]; eauto.
                    cbn.
                    unfold mem_byte in *.
                    rewrite Heqo.
                    tauto.
                    destruct ALLOC as [_ CONTRA]; inv CONTRA.
                - (* alloc_bytes_add_to_frame *)
                  intros fs1 fs2 OLDFS ADD.
                  unfold memory_stack_frame_stack_prop in *.
                  cbn in OLDFS; subst.
                  cbn.

                  rewrite <- map_cons.

                  match goal with
                  | H: _ |- context [ add_all_to_frame ?ms (map ptr_to_int ?ptrs) ] =>
                      pose proof (add_all_to_frame_correct ptrs ms (add_all_to_frame ms (map ptr_to_int ptrs))) as ADDPTRS
                  end.

                  forward ADDPTRS; [reflexivity|].

                  eapply add_ptrs_to_frame_eqv; eauto.
                  rewrite <- OLDFS in ADD.
                  auto.
                - (* Heap preserved *)
                  solve_heap_preserved.
                - (* non-void *)
                  auto.
                - (* Length of init bytes matches up *)
                  cbn; auto.
              }
              { split.
                reflexivity.
                auto.
              }
            }

            { (* OOM *)
              cbn in RUN.
              rewrite MemMonad_run_raise_oom in RUN.
              rewrite rbm_raise_bind in RUN.
              exfalso.
              symmetry in RUN.
              eapply MemMonad_eq1_raise_oom_inv in RUN.
              auto.
              typeclasses eauto.
            }
          }
      }

      Unshelve.
      all: try exact ""%string.
    Qed.

    (** Malloc correctness *)
    Lemma malloc_bytes_correct :
      forall init_bytes, exec_correct (malloc_bytes init_bytes) (malloc_bytes_spec_MemPropT init_bytes).
    Proof.
      unfold exec_correct.
      intros init_bytes ms st VALID.

      destruct (mem_state_fresh_provenance ms) as [pr' ms_fresh_pr] eqn:FRESH.
      { right.
        split; [|split].
        - (* Error *)
          (* Always allowed to error *)
          repeat eexists. left.
          cbn. auto.
        - (* OOM *)
          (* Always allowed to oom *)
          repeat eexists. left.
          cbn. auto.
        - (* Success *)
          unfold malloc_bytes_spec_MemPropT.
          intros st_final ms_final alloc_addr RUN.
          unfold malloc_bytes in *.

          { cbn in RUN.
            rewrite MemMonad_run_bind in RUN; auto.
            pose proof MemMonad_run_fresh_provenance ms st VALID
              as [ms' [pr'' [FRESH_PR [VALID' [GET_PR [EXTEND_PR [NUSED_PR USED_PR]]]]]]].
            rewrite FRESH_PR in RUN.
            rewrite bind_ret_l in RUN.

            rewrite MemMonad_run_bind in RUN; auto.
            pose proof MemMonad_run_fresh_sid ms' st VALID' as [st' [sid [RUN_FRESH_SID [VALID'' FRESH_SID]]]].
            rewrite RUN_FRESH_SID in RUN.
            rewrite bind_ret_l in RUN.

            rewrite MemMonad_run_bind in RUN.
            rewrite MemMonad_get_mem_state in RUN.
            rewrite bind_ret_l in RUN.

            destruct ms as [ms_stack ms_prov].
            destruct ms_stack as [mem frames heap].

            destruct ms' as [[mem' fs' h'] pr'''].
            unfold ms_get_memory in GET_PR.
            cbn in GET_PR.
            inv GET_PR.
            cbn in RUN.
            rename mem' into mem.
            rename fs' into frames.
            rename h' into heap.

            (* TODO: need to know something about get_consecutive_ptrs *)
            unfold get_consecutive_ptrs in *; cbn in RUN.
            do 2 rewrite MemMonad_run_bind in RUN; auto.
            rewrite bind_bind in RUN.
            destruct (intptr_seq 0 (Datatypes.length init_bytes)) as [NOOM_seq | OOM_seq] eqn:HSEQ.
            { (* no oom *)
              cbn in RUN.
              rewrite MemMonad_run_ret in RUN; auto.
              rewrite bind_ret_l in RUN.

              match goal with
              | RUN : context [Util.map_monad ?f ?s] |- _ =>
                  destruct (Util.map_monad f s) as [ERR | ptrs] eqn:HMAPM
              end.

              { (* Error *)
                cbn in RUN.
                rewrite MemMonad_run_raise_error in RUN.
                rewrite rbm_raise_bind in RUN.
                exfalso.
                symmetry in RUN.
                eapply MemMonad_eq1_raise_error_inv in RUN.
                auto.
                typeclasses eauto.
              }

              (* SUCCESS *)
              cbn in RUN.
              rewrite MemMonad_run_ret in RUN; auto.
              rewrite bind_ret_l in RUN.

              rewrite MemMonad_run_bind in RUN; auto.
              rewrite MemMonad_get_mem_state in RUN.
              rewrite bind_ret_l in RUN.

              rewrite MemMonad_run_bind in RUN; auto.
              rewrite MemMonad_put_mem_state in RUN.
              rewrite bind_ret_l in RUN.
              rewrite MemMonad_run_ret in RUN; auto.
              cbn in RUN.

              apply eq1_ret_ret in RUN; [|typeclasses eauto].
              inv RUN.
              (* Done extracting information from RUN. *)

              rename ptrs into ptrs_alloced.
              destruct ptrs_alloced as [ _ | alloc_addr ptrs] eqn:HALLOC_PTRS.
              { (* Empty ptr list... Not a contradiction, can allocate 0 bytes... MAY not be unique. *)
                cbn in HMAPM.
                cbn.
                assert (init_bytes = []) as INIT_NIL.
                { destruct init_bytes; auto.
                  cbn in *.
                  rewrite IP.from_Z_0 in HSEQ.
                  destruct (Util.map_monad IP.from_Z (Zseq 1 (Datatypes.length init_bytes))); inv HSEQ.
                  cbn in HMAPM.
                  rewrite handle_gep_addr_0 in HMAPM.
                  match goal with
                  | H:
                    context [ map_monad ?f ?l ] |- _ =>
                      destruct (map_monad f l)
                  end; inv HMAPM.
                }
                subst.
                cbn in *; inv HSEQ.
                cbn in *.

                (* Size is 0, nothing is allocated... *)
                exists ({| ms_memory_stack := mkMemoryStack mem frames heap; ms_provenance := pr''' |}).
                exists pr''.

                split; [solve_fresh_provenance_invariants|].

                set (alloc_addr :=
                       int_to_ptr (next_memory_key (mkMemoryStack mem frames heap))
                                  (allocation_id_to_prov (provenance_to_allocation_id pr''))).

                eexists.
                exists (alloc_addr, []).

                split.
                2: {
                  split; eauto.
                }

                { (* TODO: solve_malloc_bytes_succeeds_spec *)
                  split.
                  - (* malloc_bytes_consecutive *)
                    cbn.
                    repeat eexists.
                  - (* malloc_bytes_address_provenance *)
                    subst alloc_addr.
                    apply int_to_ptr_provenance.
                  - (* malloc_bytes_addresses_provenance *)
                    intros ptr IN.
                    inv IN.
                  - (* malloc_bytes_provenances_preserved *)
                    intros pr'0.
                    unfold used_provenance_prop.
                    cbn.
                    reflexivity.
                  - (* malloc_bytes_was_fresh_byte *)
                    intros ptr IN.
                    inv IN.
                  - (* malloc_bytes_now_byte_allocated *)
                    intros ptr IN.
                    inv IN.
                  - (* malloc_bytes_preserves_old_allocations *)
                    intros ptr aid NIN.
                    reflexivity.
                  - (* alloc_bytes_new_reads_allowed *)
                    intros ptr IN.
                    inv IN.
                  - (* alloc_bytes_old_reads_allowed *)
                    intros ptr' DISJOINT.
                    split; auto.
                  - (* alloc_bytes_new_reads *)
                    intros p ix byte NTH1 NTH2.
                    apply Util.not_Nth_nil in NTH1.
                    contradiction.
                  - (* alloc_bytes_old_reads *)
                    intros ptr' byte DISJOINT.
                    split; auto.
                  - (* alloc_bytes_new_writes_allowed *)
                    intros p IN.
                    inv IN.
                  - (* alloc_bytes_old_writes_allowed *)
                    intros ptr' DISJOINT.
                    split; auto.
                  - (* alloc_bytes_preserve_frame_stack *)
                    solve_frame_stack_preserved.
                  - (* alloc_bytes_add_to_heap *)
                    intros h1 h2 POP ADD.
                    cbn in ADD; subst; auto.
                    unfold memory_stack_heap_prop in *.
                    cbn in *.
                    unfold memory_stack_heap.
                    cbn.
                    rewrite ADD in POP.
                    auto.
                }
              }

              (* Non-empty allocation *)
              cbn.

              exists ({| ms_memory_stack := (mkMemoryStack mem frames heap); ms_provenance := pr''' |}).
              exists pr''.

              split; [solve_fresh_provenance_invariants|].

              Open Scope positive.
              exists ({|
                    ms_memory_stack :=
                    add_all_to_heap
                      {|
                        memory_stack_memory :=
                        add_all_index
                          (map (fun b : SByte => (b, provenance_to_allocation_id pr'')) init_bytes)
                          (next_memory_key
                             {|
                               memory_stack_memory := mem;
                               memory_stack_frame_stack := frames;
                               memory_stack_heap := heap
                             |}) mem;
                        memory_stack_frame_stack := frames;
                        memory_stack_heap := heap
                      |} (map ptr_to_int (alloc_addr :: ptrs));

                    ms_provenance := pr'''
                  |}).
              exists (alloc_addr, (alloc_addr :: ptrs)).

              Close Scope positive.
              assert (int_to_ptr
                        (next_memory_key (mkMemoryStack mem frames heap)) (allocation_id_to_prov (provenance_to_allocation_id pr'')) = alloc_addr) as EQALLOC.
              {
                destruct (Datatypes.length init_bytes) eqn:LENBYTES.
                { cbn in HSEQ; inv HSEQ.
                  cbn in *.
                  inv HMAPM.
                }

                rewrite intptr_seq_succ in HSEQ.
                cbn in HSEQ.
                rewrite IP.from_Z_0 in HSEQ.
                destruct (intptr_seq 1 n); inv HSEQ.

                unfold Util.map_monad in HMAPM.
                inversion HMAPM.
                inversion HMAPM.
                (* Fragile proof... *)
                break_match_hyp; inv H2.
                break_match_hyp; inv H3.

                rewrite handle_gep_addr_0 in Heqs.
                inv Heqs.
                reflexivity.
              }

              split.
              { (* TODO: solve_malloc_bytes_succeeds_spec *)
                split.
                - (* malloc_bytes_consecutive *)
                  do 2 eexists.
                  split.
                  + cbn.
                    rewrite HSEQ.
                    cbn.
                    split; reflexivity.
                  + rewrite EQALLOC in HMAPM.
                    rewrite HMAPM.
                    cbn.
                    split; reflexivity.
                - (* malloc_bytes_address_provenance *)
                    subst alloc_addr.
                    apply int_to_ptr_provenance.
                - (* malloc_bytes_addressses_provenance *)
                  (* TODO: Need map_monad lemmas *)
                  assert (@inr string (list addr) = ret) as INR.
                  reflexivity.
                  rewrite INR in HMAPM.
                  clear INR.

                  intros ptr IN.
                  pose proof map_monad_err_In _ _ _ _ HMAPM IN as MAPIN.
                  destruct MAPIN as [ip [GENPTR INip]].

                  apply handle_gep_addr_preserves_provenance in GENPTR.
                  rewrite int_to_ptr_provenance in GENPTR.
                  auto.
                - (* malloc_bytes_provenances_preserved *)
                  intros pr'0.
                  split; eauto.
                - (* malloc_bytes_was_fresh_byte *)
                  intros ptr IN.

                  unfold byte_not_allocated.
                  unfold byte_allocated.
                  unfold byte_allocated_MemPropT.
                  intros aid CONTRA.
                  break_lifted_addr_allocated_prop_in CONTRA.
                  cbn in CONTRA.

                  rewrite read_byte_raw_next_memory_key in CONTRA.
                  2: {
                    pose proof map_monad_err_In _ _ _ _ HMAPM IN as MAPIN.
                    destruct MAPIN as [ip [GENPTR INip]].

                    apply handle_gep_addr_ix in GENPTR.
                    rewrite ptr_to_int_int_to_ptr in GENPTR.
                    rewrite GENPTR.

                    assert (IP.to_Z ip >= 0).
                    { eapply intptr_seq_ge; eauto.
                    }

                    rewrite sizeof_dtyp_i8.
                    rewrite next_memory_key_next_key.
                    lia.
                  }

                  destruct CONTRA as [_ CONTRA].
                  inversion CONTRA.
                - (* malloc_bytes_now_byte_allocated *)
                  (* TODO: solve_byte_allocated *)
                  intros ptr IN.

                  (* New bytes are allocated because the exist in the add_all_index block *)
                  pose proof map_monad_err_In _ _ _ _ HMAPM IN as MAPIN.
                  destruct MAPIN as [ip [GENPTR INip]].

                  repeat eexists; [| solve_returns_provenance].
                  cbn.
                  unfold mem_state_memory.
                  cbn.
                  rewrite add_all_to_heap_preserves_memory.
                  cbn.

                  match goal with
                  | H: _ |- context [ read_byte_raw (add_all_index ?l ?z ?mem) ?p ] =>
                      pose proof read_byte_raw_add_all_index_in_exists mem l z p as ?READ
                  end.

                  forward READ.
                  { (* Bounds *)
                    pose proof (map_monad_err_In _ _ _ _ HMAPM IN) as [ix' [GENp IN_ix']].
                    apply handle_gep_addr_ix in GENp.
                    rewrite sizeof_dtyp_i8 in GENp.
                    replace (Z.of_N 1 * IP.to_Z ix') with (IP.to_Z ix') in GENp by lia.
                    rewrite ptr_to_int_int_to_ptr in GENp.
                    apply (in_intptr_seq _ _ _ _ HSEQ) in IN_ix'.

                    rewrite Zlength_map.
                    rewrite <- Zlength_correct in IN_ix'.
                    lia.
                  }

                  destruct READ as [(byte', aid_byte) [NTH READ]].
                  rewrite list_nth_z_map in NTH.
                  unfold option_map in NTH.
                  break_match_hyp; inv NTH.

                  (* Need this unfold for rewrite >_< *)
                  unfold mem_byte in *.
                  rewrite READ.
                  split; try tauto.
                  apply aid_eq_dec_refl.
                - (* malloc_bytes_preserves_old_allocations *)
                  intros ptr aid DISJOINT.
                  (* TODO: not enough for ptr to not be in ptrs list. Must be disjoint.

                     E.g., problem if provenances are different.
                   *)

                  split; intros ALLOC.
                  + repeat eexists; [| solve_returns_provenance];
                      cbn; unfold mem_state_memory; cbn.
                    rewrite add_all_to_heap_preserves_memory.
                    cbn.

                    erewrite read_byte_raw_add_all_index_out.
                    2: {
                      rewrite Zlength_map.
                      pose proof (Z_lt_ge_dec (ptr_to_int ptr) (next_memory_key (mkMemoryStack mem frames heap))) as [LTNEXT | GENEXT]; auto.
                      pose proof (Z_ge_lt_dec (ptr_to_int ptr) (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes)) as [LTNEXT' | GENEXT']; auto.

                                            exfalso.

                      pose proof (@exists_in_bounds_le_lt (next_memory_key (mkMemoryStack mem frames heap)) (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes) (ptr_to_int ptr)) as BOUNDS.
                      forward BOUNDS. lia.
                      destruct BOUNDS as [ix [[BOUNDLE BOUNDLT] EQ]].

                      replace (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes - next_memory_key (mkMemoryStack mem frames heap)) with (Zlength init_bytes) in BOUNDLT by lia.

                      (* Want to use bound in... *)
                      (* Need to get what ix is as an IP... *)
                      destruct (IP.from_Z ix) eqn:IX.
                      2: {
                         (* HSEQ succeeding should make this a contradiction *)
                        apply intptr_seq_from_Z with (x := ix) in HSEQ.
                        destruct HSEQ as [ipx [EQ' INSEQ]].
                        rewrite EQ' in IX.
                        inv IX.

                        rewrite <- Zlength_correct.
                        lia.
                      }

                      pose proof (in_intptr_seq _ _ i _ HSEQ) as [IN BOUNDIN].
                      apply IP.from_Z_to_Z in IX; subst.
                      forward BOUNDIN.
                      rewrite <- Zlength_correct.
                      lia.

                      set (p := int_to_ptr (ptr_to_int ptr) (allocation_id_to_prov (provenance_to_allocation_id pr''))).

                      (* I believe that p is necessarily in the result of HMAPM. *)
                      assert (In p (int_to_ptr (next_memory_key (mkMemoryStack mem frames heap))
                                               (allocation_id_to_prov
                                                  (provenance_to_allocation_id pr'')) :: ptrs)) as PIN.
                      { clear - HMAPM HSEQ GENEXT GENEXT' i EQ BOUNDIN.

                        eapply map_monad_err_In' with (y:=i) in HMAPM; auto.

                        destruct HMAPM as [x [GENPTR IN]].
                        symmetry in GENPTR.
                        pose proof GENPTR as GENPTR'.
                        apply handle_gep_addr_ix in GENPTR.
                        rewrite sizeof_dtyp_i8 in GENPTR.
                        replace (Z.of_N 1 * IP.to_Z i) with (IP.to_Z i) in GENPTR by lia.
                        rewrite ptr_to_int_int_to_ptr in GENPTR.
                        rewrite <- GENPTR in EQ.

                        subst p.
                        rewrite EQ.
                        rewrite int_to_ptr_ptr_to_int; auto.

                        apply handle_gep_addr_preserves_provenance in GENPTR'.
                        rewrite int_to_ptr_provenance in GENPTR'.
                        symmetry; auto.
                      }

                      eapply map_monad_err_In with (x:=p) in HMAPM; auto.

                      (* DISJOINT should be a contradition now *)
                      exfalso.
                      (* ?p doesn't have to be ptr', but ptr_to_int ?p = ptr_to_int ptr' *)
                      eapply DISJOINT with (p:=p).
                      apply PIN.

                      subst p.
                      rewrite ptr_to_int_int_to_ptr.
                      reflexivity.
                    }

                    break_byte_allocated_in ALLOC.
                    cbn in ALLOC.

                    break_match; [break_match|]; split; tauto.
                  + break_byte_allocated_in ALLOC.
                    cbn in ALLOC.

                    unfold mem_state_memory in ALLOC; cbn in ALLOC.
                    rewrite add_all_to_heap_preserves_memory in ALLOC; cbn in ALLOC.

                    erewrite read_byte_raw_add_all_index_out in ALLOC.
                    2: {
                      rewrite Zlength_map.
                      pose proof (Z_lt_ge_dec (ptr_to_int ptr) (next_memory_key (mkMemoryStack mem frames heap))) as [LTNEXT | GENEXT]; auto.
                      pose proof (Z_ge_lt_dec (ptr_to_int ptr) (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes)) as [LTNEXT' | GENEXT']; auto.

                                            exfalso.

                      pose proof (@exists_in_bounds_le_lt (next_memory_key (mkMemoryStack mem frames heap)) (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes) (ptr_to_int ptr)) as BOUNDS.
                      forward BOUNDS. lia.
                      destruct BOUNDS as [ix [[BOUNDLE BOUNDLT] EQ]].

                      replace (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes - next_memory_key (mkMemoryStack mem frames heap)) with (Zlength init_bytes) in BOUNDLT by lia.

                      (* Want to use bound in... *)
                      (* Need to get what ix is as an IP... *)
                      destruct (IP.from_Z ix) eqn:IX.
                      2: {
                         (* HSEQ succeeding should make this a contradiction *)
                        apply intptr_seq_from_Z with (x := ix) in HSEQ.
                        destruct HSEQ as [ipx [EQ' INSEQ]].
                        rewrite EQ' in IX.
                        inv IX.

                        rewrite <- Zlength_correct.
                        lia.
                      }

                      pose proof (in_intptr_seq _ _ i _ HSEQ) as [IN BOUNDIN].
                      apply IP.from_Z_to_Z in IX; subst.
                      forward BOUNDIN.
                      rewrite <- Zlength_correct.
                      lia.

                      set (p := int_to_ptr (ptr_to_int ptr) (allocation_id_to_prov (provenance_to_allocation_id pr''))).

                      (* I believe that p is necessarily in the result of HMAPM. *)
                      assert (In p (int_to_ptr (next_memory_key (mkMemoryStack mem frames heap))
                                               (allocation_id_to_prov
                                                  (provenance_to_allocation_id pr'')) :: ptrs)) as PIN.
                      { clear - HMAPM HSEQ GENEXT GENEXT' i EQ BOUNDIN.

                        eapply map_monad_err_In' with (y:=i) in HMAPM; auto.

                        destruct HMAPM as [x [GENPTR IN]].
                        symmetry in GENPTR.
                        pose proof GENPTR as GENPTR'.
                        apply handle_gep_addr_ix in GENPTR.
                        rewrite sizeof_dtyp_i8 in GENPTR.
                        replace (Z.of_N 1 * IP.to_Z i) with (IP.to_Z i) in GENPTR by lia.
                        rewrite ptr_to_int_int_to_ptr in GENPTR.
                        rewrite <- GENPTR in EQ.

                        subst p.
                        rewrite EQ.
                        rewrite int_to_ptr_ptr_to_int; auto.

                        apply handle_gep_addr_preserves_provenance in GENPTR'.
                        rewrite int_to_ptr_provenance in GENPTR'.
                        symmetry; auto.
                      }

                      eapply map_monad_err_In with (x:=p) in HMAPM; auto.

                      (* DISJOINT should be a contradition now *)
                      exfalso.
                      (* ?p doesn't have to be ptr', but ptr_to_int ?p = ptr_to_int ptr' *)
                      eapply DISJOINT with (p:=p).
                      apply PIN.

                      subst p.
                      rewrite ptr_to_int_int_to_ptr.
                      reflexivity.
                    }

                    repeat eexists; [| solve_returns_provenance].
                    cbn.

                    break_match; [break_match|]; split; tauto.
                - (* alloc_bytes_new_reads_allowed *)
                  intros p IN.
                  (* TODO: solve_read_byte_allowed *)
                  induction IN as [IN | IN]; subst.
                  + (* TODO: solve_read_byte_allowed *)
                    eexists.
                    split.
                    * (* TODO: solve_byte_allocated *)
                      repeat eexists; [| solve_returns_provenance].
                      cbn.
                      unfold mem_state_memory.
                      cbn.
                      rewrite add_all_to_heap_preserves_memory.
                      cbn in *.
                      rewrite ptr_to_int_int_to_ptr.

                      match goal with
                      | H: _ |- context [ read_byte_raw (add_all_index ?l ?z ?mem) ?p ] =>
                          pose proof read_byte_raw_add_all_index_in_exists mem l z p as ?READ
                      end.

                      forward READ.
                      { (* bounds *)
                        (* Should be a non-empty allocation *)
                        (* I know this by cons cell result of HMAPM *)
                        assert (@MonadReturnsLaws.MReturns err _ _ _ (list addr)
                                                           (int_to_ptr (next_memory_key (mkMemoryStack mem frames heap))
                                                                       (allocation_id_to_prov (provenance_to_allocation_id pr'')) :: ptrs)
                                                           (Util.map_monad
            (fun ix : IP.intptr =>
             handle_gep_addr (DTYPE_I 8)
               (int_to_ptr (next_memory_key (mkMemoryStack mem frames heap))
                  (allocation_id_to_prov (provenance_to_allocation_id pr'')))
               [Events.DV.DVALUE_IPTR ix]) NOOM_seq)) as MAPRET.
                        { cbn. red.
                          auto.
                        }

                        eapply map_monad_length in MAPRET.
                        cbn in MAPRET.
                        rewrite Zlength_map.
                        rewrite Zlength_correct.
                        apply intptr_seq_len in HSEQ.
                        lia.
                      }

                      destruct READ as [(byte, aid_byte) [NTH READ]].
                      rewrite list_nth_z_map in NTH.
                      unfold option_map in NTH.
                      break_match_hyp; inv NTH.

                      (* Need this unfold for rewrite >_< *)
                      unfold mem_byte in *.
                      rewrite READ.

                      split; auto.
                      apply aid_eq_dec_refl.
                    * solve_access_allowed.
                  + (* TODO: solve_read_byte_allowed *)
                    repeat eexists; [| solve_returns_provenance |];
                    cbn.
                    unfold mem_state_memory.
                    cbn.
                    rewrite add_all_to_heap_preserves_memory.
                    cbn in *.
                    rewrite ptr_to_int_int_to_ptr.

                    match goal with
                    | H: _ |- context [ read_byte_raw (add_all_index ?l ?z ?mem) ?p ] =>
                        pose proof read_byte_raw_add_all_index_in_exists mem l z p as ?READ
                    end.

                    forward READ.
                    { (* Bounds *)
                      assert (In p (int_to_ptr (next_memory_key (mkMemoryStack mem frames heap))
                                               (allocation_id_to_prov (provenance_to_allocation_id pr'')) :: ptrs)) as IN'.
                      { right; auto.
                      }

                      pose proof (map_monad_err_In _ _ _ _ HMAPM IN') as [ix' [GENp IN_ix']].
                      apply handle_gep_addr_ix in GENp.
                      rewrite sizeof_dtyp_i8 in GENp.
                      replace (Z.of_N 1 * IP.to_Z ix') with (IP.to_Z ix') in GENp by lia.
                      rewrite ptr_to_int_int_to_ptr in GENp.
                      apply (in_intptr_seq _ _ _ _ HSEQ) in IN_ix'.

                      rewrite Zlength_map.
                      rewrite <- Zlength_correct in IN_ix'.
                      lia.
                    }

                    destruct READ as [(byte, aid_byte) [NTH READ]].
                    rewrite list_nth_z_map in NTH.
                    unfold option_map in NTH.
                    break_match_hyp; inv NTH.

                    (* Need this unfold for rewrite >_< *)
                    unfold mem_byte in *.
                    rewrite READ.

                    split; auto.
                    apply aid_eq_dec_refl.

                    (* Need to look up provenance via IN *)
                    (* TODO: solve_access_allowed *)
                    eapply map_monad_err_In in HMAPM.
                    2: {
                      cbn; right; eauto.
                    }

                    destruct HMAPM as [ip [GENPTR INip]].
                    apply handle_gep_addr_preserves_provenance in GENPTR.
                    rewrite int_to_ptr_provenance in GENPTR.
                    rewrite <- GENPTR.

                    solve_access_allowed.
                - (* alloc_bytes_old_reads_allowed *)
                  intros ptr' DISJOINT.
                  split; intros ALLOWED.
                  + (* TODO: solve_read_byte_allowed. *)
                    break_access_hyps.
                    (* TODO: move this into break_access_hyps? *)
                    break_byte_allocated_in ALLOC.

                    break_match; [break_match|]; destruct ALLOC as [EQM AID]; subst; [|inv AID].

                    repeat eexists; [| solve_returns_provenance |].
                    cbn.
                    unfold mem_state_memory.
                    cbn.
                    rewrite add_all_to_heap_preserves_memory.

                    cbn.
                    rewrite read_byte_raw_add_all_index_out.
                    2: {
                      left.
                      rewrite next_memory_key_next_key.
                      eapply read_byte_raw_lt_next_memory_key; eauto.
                    }

                    cbn in *.
                    rewrite Heqo; eauto.

                    solve_access_allowed.
                  + (* TODO: solve_read_byte_allowed. *)
                    break_access_hyps.
                    (* TODO: move this into break_access_hyps? *)
                    break_byte_allocated_in ALLOC.
                    cbn in ALLOC.

                    break_match; [break_match|]; destruct ALLOC as [EQM AID]; subst; [|inv AID].

                    repeat eexists; [| solve_returns_provenance |].
                    cbn.
                    unfold mem_state_memory in *.
                    cbn in *.
                    rewrite add_all_to_heap_preserves_memory in Heqo.
                    cbn in *.

                    rewrite read_byte_raw_add_all_index_out in Heqo.
                    2: {
                      (* If read is in the bounds of add_all_index then that means it's not disjoint...

                       *)

                      (*
                        If ptr' is such that...

                        ptr' >= next_mem_key and
                        ptr' < next_mem_key + length

                        then ptr' is in the allocated pointers, and
                        therefore DISJOINT doesn't hold.
                       *)
                      rewrite Zlength_map.
                      pose proof (Z_lt_ge_dec (ptr_to_int ptr') (next_memory_key (mkMemoryStack mem frames heap))) as [LTNEXT | GENEXT]; auto.
                      pose proof (Z_ge_lt_dec (ptr_to_int ptr') (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes)) as [LTNEXT' | GENEXT']; auto.

                      exfalso.

                      pose proof (@exists_in_bounds_le_lt (next_memory_key (mkMemoryStack mem frames heap)) (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes) (ptr_to_int ptr')) as BOUNDS.
                      forward BOUNDS. lia.
                      destruct BOUNDS as [ix [[BOUNDLE BOUNDLT] EQ]].

                      replace (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes - next_memory_key (mkMemoryStack mem frames heap)) with (Zlength init_bytes) in BOUNDLT by lia.

                      (* Want to use bound in... *)
                      (* Need to get what ix is as an IP... *)
                      destruct (IP.from_Z ix) eqn:IX.
                      2: {
                         (* HSEQ succeeding should make this a contradiction *)
                        apply intptr_seq_from_Z with (x := ix) in HSEQ.
                        destruct HSEQ as [ipx [EQ' INSEQ]].
                        rewrite EQ' in IX.
                        inv IX.

                        rewrite <- Zlength_correct.
                        lia.
                      }

                      pose proof (in_intptr_seq _ _ i _ HSEQ) as [IN BOUNDIN].
                      apply IP.from_Z_to_Z in IX; subst.
                      forward BOUNDIN.
                      rewrite <- Zlength_correct.
                      lia.

                      set (p := int_to_ptr (ptr_to_int ptr') (allocation_id_to_prov (provenance_to_allocation_id pr''))).

                      (* I believe that p is necessarily in the result of HMAPM. *)
                      assert (In p (int_to_ptr (next_memory_key (mkMemoryStack mem frames heap))
                                               (allocation_id_to_prov
                                                  (provenance_to_allocation_id pr'')) :: ptrs)) as PIN.
                      { clear - HMAPM HSEQ GENEXT GENEXT' i EQ BOUNDIN.

                        eapply map_monad_err_In' with (y:=i) in HMAPM; auto.

                        destruct HMAPM as [x [GENPTR IN]].
                        symmetry in GENPTR.
                        pose proof GENPTR as GENPTR'.
                        apply handle_gep_addr_ix in GENPTR.
                        rewrite sizeof_dtyp_i8 in GENPTR.
                        replace (Z.of_N 1 * IP.to_Z i) with (IP.to_Z i) in GENPTR by lia.
                        rewrite ptr_to_int_int_to_ptr in GENPTR.
                        rewrite <- GENPTR in EQ.

                        subst p.
                        rewrite EQ.
                        rewrite int_to_ptr_ptr_to_int; auto.

                        apply handle_gep_addr_preserves_provenance in GENPTR'.
                        rewrite int_to_ptr_provenance in GENPTR'.
                        symmetry; auto.
                      }

                      eapply map_monad_err_In with (x:=p) in HMAPM; auto.

                      (* DISJOINT should be a contradition now *)
                      exfalso.
                      (* ?p doesn't have to be ptr', but ptr_to_int ?p = ptr_to_int ptr' *)
                      eapply DISJOINT with (p:=p).
                      apply PIN.

                      subst p.
                      rewrite ptr_to_int_int_to_ptr.
                      reflexivity.
                    }

                    rewrite Heqo; eauto.

                    solve_access_allowed.
                - (* alloc_bytes_new_reads *)
                  intros p ix byte ADDR BYTE.
                  cbn.
                  repeat eexists.
                  unfold mem_state_memory.
                  cbn.
                  rewrite add_all_to_heap_preserves_memory.
                  cbn.

                  match goal with
                  | H: _ |- context [ read_byte_raw (add_all_index ?l ?z ?mem) ?p ] =>
                      pose proof read_byte_raw_add_all_index_in_exists mem l z p as ?READ
                  end.

                  forward READ.
                  { (* Bounds *)
                    pose proof (Nth_In ADDR) as IN.
                    pose proof (map_monad_err_In _ _ _ _ HMAPM IN) as [ix' [GENp IN_ix']].
                    apply handle_gep_addr_ix in GENp.
                    rewrite sizeof_dtyp_i8 in GENp.
                    replace (Z.of_N 1 * IP.to_Z ix') with (IP.to_Z ix') in GENp by lia.
                    rewrite ptr_to_int_int_to_ptr in GENp.
                    apply (in_intptr_seq _ _ _ _ HSEQ) in IN_ix'.

                    rewrite Zlength_map.
                    rewrite <- Zlength_correct in IN_ix'.
                    lia.
                  }

                  destruct READ as [(byte', aid_byte) [NTH READ]].
                  rewrite list_nth_z_map in NTH.
                  unfold option_map in NTH.
                  break_match_hyp; inv NTH.

                  (*
                    ADDR tells me that p is in my pointers list at index `ix`...

                    Should be `next_memory_key ms + ix` basically...

                    So, `ptr_to_int p - next_memory_key (mkMemoryStack mem frames heap) = ix`

                    With that BYTE and Heqo should give me byte = byte'
                   *)
                  assert (byte = byte').
                  { pose proof (map_monad_err_Nth _ _ _ _ _ HMAPM ADDR) as [ix' [GENp NTH_ix']].
                    apply handle_gep_addr_ix in GENp.
                    rewrite ptr_to_int_int_to_ptr in GENp.
                    rewrite GENp in Heqo.

                    (* NTH_ix' -> ix = ix' *)
                    (* Heqo + BYTE *)

                    eapply intptr_seq_nth in NTH_ix'; eauto.
                    apply IP.from_Z_to_Z in NTH_ix'.
                    rewrite NTH_ix' in Heqo.

                    rewrite sizeof_dtyp_i8 in Heqo.
                    replace (next_memory_key (mkMemoryStack mem frames heap) + Z.of_N 1 * ( 0 + Z.of_nat ix) - next_memory_key (mkMemoryStack mem frames heap)) with (Z.of_nat ix) in Heqo by lia.

                    apply Util.Nth_list_nth_z in BYTE.
                    rewrite BYTE in Heqo.
                    inv Heqo; auto.
                  }

                  subst.

                  (* Need this unfold for rewrite >_< *)
                  unfold mem_byte in *.
                  rewrite READ.

                  cbn.
                  break_match.
                  split; auto.

                  apply Util.Nth_In in ADDR.
                  pose proof (map_monad_err_In _ _ _ _ HMAPM ADDR) as [ix' [GENp IN_ix']].

                  apply handle_gep_addr_preserves_provenance in GENp.
                  rewrite <- GENp in Heqb.
                  rewrite int_to_ptr_provenance in Heqb.
                  rewrite access_allowed_refl in Heqb.
                  inv Heqb.
                - (* alloc_bytes_old_reads *)
                  intros ptr' byte DISJOINT.
                  split; intros READ.
                  + (* TODO: solve_read_byte_prop *)
                    cbn.
                    repeat eexists.
                    unfold mem_state_memory.
                    cbn.
                    rewrite add_all_to_heap_preserves_memory.
                    cbn.

                    rewrite read_byte_raw_add_all_index_out.
                    2: {
                      rewrite Zlength_map.
                      pose proof (Z_lt_ge_dec (ptr_to_int ptr') (next_memory_key (mkMemoryStack mem frames heap))) as [LTNEXT | GENEXT]; auto.
                      pose proof (Z_ge_lt_dec (ptr_to_int ptr') (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes)) as [LTNEXT' | GENEXT']; auto.

                      exfalso.

                      pose proof (@exists_in_bounds_le_lt (next_memory_key (mkMemoryStack mem frames heap)) (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes) (ptr_to_int ptr')) as BOUNDS.
                      forward BOUNDS. lia.
                      destruct BOUNDS as [ix [[BOUNDLE BOUNDLT] EQ]].

                      replace (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes - next_memory_key (mkMemoryStack mem frames heap)) with (Zlength init_bytes) in BOUNDLT by lia.

                      (* Want to use bound in... *)
                      (* Need to get what ix is as an IP... *)
                      destruct (IP.from_Z ix) eqn:IX.
                      2: {
                         (* HSEQ succeeding should make this a contradiction *)
                        apply intptr_seq_from_Z with (x := ix) in HSEQ.
                        destruct HSEQ as [ipx [EQ' INSEQ]].
                        rewrite EQ' in IX.
                        inv IX.

                        rewrite <- Zlength_correct.
                        lia.
                      }

                      pose proof (in_intptr_seq _ _ i _ HSEQ) as [IN BOUNDIN].
                      apply IP.from_Z_to_Z in IX; subst.
                      forward BOUNDIN.
                      rewrite <- Zlength_correct.
                      lia.

                      set (p := int_to_ptr (ptr_to_int ptr') (allocation_id_to_prov (provenance_to_allocation_id pr''))).

                      (* I believe that p is necessarily in the result of HMAPM. *)
                      assert (In p (int_to_ptr (next_memory_key (mkMemoryStack mem frames heap))
                                               (allocation_id_to_prov
                                                  (provenance_to_allocation_id pr'')) :: ptrs)) as PIN.
                      { clear - HMAPM HSEQ GENEXT GENEXT' i EQ BOUNDIN.

                        eapply map_monad_err_In' with (y:=i) in HMAPM; auto.

                        destruct HMAPM as [x [GENPTR IN]].
                        symmetry in GENPTR.
                        pose proof GENPTR as GENPTR'.
                        apply handle_gep_addr_ix in GENPTR.
                        rewrite sizeof_dtyp_i8 in GENPTR.
                        replace (Z.of_N 1 * IP.to_Z i) with (IP.to_Z i) in GENPTR by lia.
                        rewrite ptr_to_int_int_to_ptr in GENPTR.
                        rewrite <- GENPTR in EQ.

                        subst p.
                        rewrite EQ.
                        rewrite int_to_ptr_ptr_to_int; auto.

                        apply handle_gep_addr_preserves_provenance in GENPTR'.
                        rewrite int_to_ptr_provenance in GENPTR'.
                        symmetry; auto.
                      }

                      eapply map_monad_err_In with (x:=p) in HMAPM; auto.

                      (* DISJOINT should be a contradition now *)
                      exfalso.
                      (* ?p doesn't have to be ptr', but ptr_to_int ?p = ptr_to_int ptr' *)
                      eapply DISJOINT with (p:=p).
                      apply PIN.

                      subst p.
                      rewrite ptr_to_int_int_to_ptr.
                      reflexivity.
                    }

                    (* TODO: ltac to break this up *)
                    destruct READ as [ms' [ms'' [[EQ1 EQ2] READ]]]; subst.
                    cbn in READ.

                    break_match; [break_match|]; auto.
                    tauto.
                  + (* TODO: solve_read_byte_prop *)

                    (* TODO: ltac to break this up *)
                    destruct READ as [ms' [ms'' [[EQ1 EQ2] READ]]]; subst.
                    cbn in READ.
                    unfold mem_state_memory in READ.
                    cbn in READ.
                    rewrite add_all_to_heap_preserves_memory in READ.
                    cbn in READ.

                    rewrite read_byte_raw_add_all_index_out in READ.
2: {
                      rewrite Zlength_map.
                      pose proof (Z_lt_ge_dec (ptr_to_int ptr') (next_memory_key (mkMemoryStack mem frames heap))) as [LTNEXT | GENEXT]; auto.
                      pose proof (Z_ge_lt_dec (ptr_to_int ptr') (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes)) as [LTNEXT' | GENEXT']; auto.

                      exfalso.

                      pose proof (@exists_in_bounds_le_lt (next_memory_key (mkMemoryStack mem frames heap)) (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes) (ptr_to_int ptr')) as BOUNDS.
                      forward BOUNDS. lia.
                      destruct BOUNDS as [ix [[BOUNDLE BOUNDLT] EQ]].

                      replace (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes - next_memory_key (mkMemoryStack mem frames heap)) with (Zlength init_bytes) in BOUNDLT by lia.

                      (* Want to use bound in... *)
                      (* Need to get what ix is as an IP... *)
                      destruct (IP.from_Z ix) eqn:IX.
                      2: {
                         (* HSEQ succeeding should make this a contradiction *)
                        apply intptr_seq_from_Z with (x := ix) in HSEQ.
                        destruct HSEQ as [ipx [EQ' INSEQ]].
                        rewrite EQ' in IX.
                        inv IX.

                        rewrite <- Zlength_correct.
                        lia.
                      }

                      pose proof (in_intptr_seq _ _ i _ HSEQ) as [IN BOUNDIN].
                      apply IP.from_Z_to_Z in IX; subst.
                      forward BOUNDIN.
                      rewrite <- Zlength_correct.
                      lia.

                      set (p := int_to_ptr (ptr_to_int ptr') (allocation_id_to_prov (provenance_to_allocation_id pr''))).

                      (* I believe that p is necessarily in the result of HMAPM. *)
                      assert (In p (int_to_ptr (next_memory_key (mkMemoryStack mem frames heap))
                                               (allocation_id_to_prov
                                                  (provenance_to_allocation_id pr'')) :: ptrs)) as PIN.
                      { clear - HMAPM HSEQ GENEXT GENEXT' i EQ BOUNDIN.

                        eapply map_monad_err_In' with (y:=i) in HMAPM; auto.

                        destruct HMAPM as [x [GENPTR IN]].
                        symmetry in GENPTR.
                        pose proof GENPTR as GENPTR'.
                        apply handle_gep_addr_ix in GENPTR.
                        rewrite sizeof_dtyp_i8 in GENPTR.
                        replace (Z.of_N 1 * IP.to_Z i) with (IP.to_Z i) in GENPTR by lia.
                        rewrite ptr_to_int_int_to_ptr in GENPTR.
                        rewrite <- GENPTR in EQ.

                        subst p.
                        rewrite EQ.
                        rewrite int_to_ptr_ptr_to_int; auto.

                        apply handle_gep_addr_preserves_provenance in GENPTR'.
                        rewrite int_to_ptr_provenance in GENPTR'.
                        symmetry; auto.
                      }

                      eapply map_monad_err_In with (x:=p) in HMAPM; auto.

                      (* DISJOINT should be a contradition now *)
                      exfalso.
                      (* ?p doesn't have to be ptr', but ptr_to_int ?p = ptr_to_int ptr' *)
                      eapply DISJOINT with (p:=p).
                      apply PIN.

                      subst p.
                      rewrite ptr_to_int_int_to_ptr.
                      reflexivity.
                    }

                    cbn.
                    repeat eexists.
                    cbn.
                    break_match; [break_match|]; tauto.
                - (* alloc_bytes_new_writes_allowed *)
                  intros p IN.
                  (* TODO: solve_write_byte_allowed. *)
                  break_access_hyps; eexists; split.
                  + (* TODO: solve_byte_allocated *)
                    repeat eexists; [| solve_returns_provenance].
                    unfold mem_state_memory.
                    cbn.
                    rewrite add_all_to_heap_preserves_memory.
                    cbn.

                  match goal with
                  | H: _ |- context [ read_byte_raw (add_all_index ?l ?z ?mem) ?p ] =>
                      pose proof read_byte_raw_add_all_index_in_exists mem l z p as ?READ
                  end.

                  forward READ.
                  { (* Bounds *)
                    pose proof (map_monad_err_In _ _ _ _ HMAPM IN) as [ix' [GENp IN_ix']].
                    apply handle_gep_addr_ix in GENp.
                    rewrite sizeof_dtyp_i8 in GENp.
                    replace (Z.of_N 1 * IP.to_Z ix') with (IP.to_Z ix') in GENp by lia.
                    rewrite ptr_to_int_int_to_ptr in GENp.
                    apply (in_intptr_seq _ _ _ _ HSEQ) in IN_ix'.

                    rewrite Zlength_map.
                    rewrite <- Zlength_correct in IN_ix'.
                    lia.
                  }

                  destruct READ as [(byte', aid_byte) [NTH READ]].
                  rewrite list_nth_z_map in NTH.
                  unfold option_map in NTH.
                  break_match_hyp; inv NTH.

                  unfold mem_byte in *.
                  rewrite READ.

                  split; auto.
                  apply aid_eq_dec_refl.
                  + solve_access_allowed.
                - (* alloc_bytes_old_writes_allowed *)
                  intros ptr' DISJOINT.
                  split; intros WRITE.
                  + (* TODO: solve_write_byte_allowed. *)
                    break_access_hyps.

                    (* TODO: move this into break_access_hyps? *)
                    break_byte_allocated_in ALLOC.
                    cbn in ALLOC.

                    break_match_hyp; [break_match_hyp|]; destruct ALLOC as [EQ1 EQ2]; inv EQ2.

                    repeat eexists; [| solve_returns_provenance |]; eauto.
                    cbn.
                    unfold mem_state_memory.
                    cbn.
                    rewrite add_all_to_heap_preserves_memory.
                    cbn.

                    rewrite read_byte_raw_add_all_index_out.
                    2: {
                      rewrite Zlength_map.
                      pose proof (Z_lt_ge_dec (ptr_to_int ptr') (next_memory_key (mkMemoryStack mem frames heap))) as [LTNEXT | GENEXT]; auto.
                      pose proof (Z_ge_lt_dec (ptr_to_int ptr') (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes)) as [LTNEXT' | GENEXT']; auto.

                      exfalso.

                      pose proof (@exists_in_bounds_le_lt (next_memory_key (mkMemoryStack mem frames heap)) (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes) (ptr_to_int ptr')) as BOUNDS.
                      forward BOUNDS. lia.
                      destruct BOUNDS as [ix [[BOUNDLE BOUNDLT] EQ]].

                      replace (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes - next_memory_key (mkMemoryStack mem frames heap)) with (Zlength init_bytes) in BOUNDLT by lia.

                      (* Want to use bound in... *)
                      (* Need to get what ix is as an IP... *)
                      destruct (IP.from_Z ix) eqn:IX.
                      2: {
                         (* HSEQ succeeding should make this a contradiction *)
                        apply intptr_seq_from_Z with (x := ix) in HSEQ.
                        destruct HSEQ as [ipx [EQ' INSEQ]].
                        rewrite EQ' in IX.
                        inv IX.

                        rewrite <- Zlength_correct.
                        lia.
                      }

                      pose proof (in_intptr_seq _ _ i _ HSEQ) as [IN BOUNDIN].
                      apply IP.from_Z_to_Z in IX; subst.
                      forward BOUNDIN.
                      rewrite <- Zlength_correct.
                      lia.

                      set (p := int_to_ptr (ptr_to_int ptr') (allocation_id_to_prov (provenance_to_allocation_id pr''))).

                      (* I believe that p is necessarily in the result of HMAPM. *)
                      assert (In p (int_to_ptr (next_memory_key (mkMemoryStack mem frames heap))
                                               (allocation_id_to_prov
                                                  (provenance_to_allocation_id pr'')) :: ptrs)) as PIN.
                      { clear - HMAPM HSEQ GENEXT GENEXT' i EQ BOUNDIN.

                        eapply map_monad_err_In' with (y:=i) in HMAPM; auto.

                        destruct HMAPM as [x [GENPTR IN]].
                        symmetry in GENPTR.
                        pose proof GENPTR as GENPTR'.
                        apply handle_gep_addr_ix in GENPTR.
                        rewrite sizeof_dtyp_i8 in GENPTR.
                        replace (Z.of_N 1 * IP.to_Z i) with (IP.to_Z i) in GENPTR by lia.
                        rewrite ptr_to_int_int_to_ptr in GENPTR.
                        rewrite <- GENPTR in EQ.

                        subst p.
                        rewrite EQ.
                        rewrite int_to_ptr_ptr_to_int; auto.

                        apply handle_gep_addr_preserves_provenance in GENPTR'.
                        rewrite int_to_ptr_provenance in GENPTR'.
                        symmetry; auto.
                      }

                      eapply map_monad_err_In with (x:=p) in HMAPM; auto.

                      (* DISJOINT should be a contradition now *)
                      exfalso.
                      (* ?p doesn't have to be ptr', but ptr_to_int ?p = ptr_to_int ptr' *)
                      eapply DISJOINT with (p:=p).
                      apply PIN.

                      subst p.
                      rewrite ptr_to_int_int_to_ptr.
                      reflexivity.
                    }

                    rewrite Heqo; cbn; split; eauto.
                  + (* TODO: solve_write_byte_allowed *)
                    break_access_hyps.

                    (* TODO: move this into break_access_hyps? *)
                    break_byte_allocated_in ALLOC.
                    cbn in ALLOC.

                    unfold mem_state_memory in ALLOC.
                    cbn in ALLOC.
                    rewrite add_all_to_heap_preserves_memory in ALLOC.
                    cbn in ALLOC.

                    rewrite read_byte_raw_add_all_index_out in ALLOC.
                    2: {
                      rewrite Zlength_map.
                      pose proof (Z_lt_ge_dec (ptr_to_int ptr') (next_memory_key (mkMemoryStack mem frames heap))) as [LTNEXT | GENEXT]; auto.
                      pose proof (Z_ge_lt_dec (ptr_to_int ptr') (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes)) as [LTNEXT' | GENEXT']; auto.

                      exfalso.

                      pose proof (@exists_in_bounds_le_lt (next_memory_key (mkMemoryStack mem frames heap)) (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes) (ptr_to_int ptr')) as BOUNDS.
                      forward BOUNDS. lia.
                      destruct BOUNDS as [ix [[BOUNDLE BOUNDLT] EQ]].

                      replace (next_memory_key (mkMemoryStack mem frames heap) + Zlength init_bytes - next_memory_key (mkMemoryStack mem frames heap)) with (Zlength init_bytes) in BOUNDLT by lia.

                      (* Want to use bound in... *)
                      (* Need to get what ix is as an IP... *)
                      destruct (IP.from_Z ix) eqn:IX.
                      2: {
                         (* HSEQ succeeding should make this a contradiction *)
                        apply intptr_seq_from_Z with (x := ix) in HSEQ.
                        destruct HSEQ as [ipx [EQ' INSEQ]].
                        rewrite EQ' in IX.
                        inv IX.

                        rewrite <- Zlength_correct.
                        lia.
                      }

                      pose proof (in_intptr_seq _ _ i _ HSEQ) as [IN BOUNDIN].
                      apply IP.from_Z_to_Z in IX; subst.
                      forward BOUNDIN.
                      rewrite <- Zlength_correct.
                      lia.

                      set (p := int_to_ptr (ptr_to_int ptr') (allocation_id_to_prov (provenance_to_allocation_id pr''))).

                      (* I believe that p is necessarily in the result of HMAPM. *)
                      assert (In p (int_to_ptr (next_memory_key (mkMemoryStack mem frames heap))
                                               (allocation_id_to_prov
                                                  (provenance_to_allocation_id pr'')) :: ptrs)) as PIN.
                      { clear - HMAPM HSEQ GENEXT GENEXT' i EQ BOUNDIN.

                        eapply map_monad_err_In' with (y:=i) in HMAPM; auto.

                        destruct HMAPM as [x [GENPTR IN]].
                        symmetry in GENPTR.
                        pose proof GENPTR as GENPTR'.
                        apply handle_gep_addr_ix in GENPTR.
                        rewrite sizeof_dtyp_i8 in GENPTR.
                        replace (Z.of_N 1 * IP.to_Z i) with (IP.to_Z i) in GENPTR by lia.
                        rewrite ptr_to_int_int_to_ptr in GENPTR.
                        rewrite <- GENPTR in EQ.

                        subst p.
                        rewrite EQ.
                        rewrite int_to_ptr_ptr_to_int; auto.

                        apply handle_gep_addr_preserves_provenance in GENPTR'.
                        rewrite int_to_ptr_provenance in GENPTR'.
                        symmetry; auto.
                      }

                      eapply map_monad_err_In with (x:=p) in HMAPM; auto.

                      (* DISJOINT should be a contradition now *)
                      exfalso.
                      (* ?p doesn't have to be ptr', but ptr_to_int ?p = ptr_to_int ptr' *)
                      eapply DISJOINT with (p:=p).
                      apply PIN.

                      subst p.
                      rewrite ptr_to_int_int_to_ptr.
                      reflexivity.
                    }

                    break_match; [break_match|].
                    repeat eexists; [| solve_returns_provenance |]; eauto.
                    cbn.
                    unfold mem_byte in *.
                    rewrite Heqo.
                    tauto.
                    destruct ALLOC as [_ CONTRA]; inv CONTRA.
                - (* malloc_bytes_preserves_frame_stack *)
                  (* TODO: solve_frame_stack_preserved. *)
                  cbn.
                  unfold frame_stack_preserved, memory_stack_frame_stack_prop.
                  intros fs.
                  split; intros MSP.
                  + cbn.
                    rewrite add_all_to_heap_preserves_frame_stack.
                    cbn in *; auto.
                  + cbn in MSP.
                    rewrite add_all_to_heap_preserves_frame_stack in MSP.
                    cbn in *; auto.
                - (* malloc_bytes_add_to_heap *)
                  intros h1 h2 OLDHEAP ADD.
                  unfold memory_stack_frame_stack_prop in *.
                  cbn in OLDHEAP; subst.
                  cbn.

                  rewrite <- map_cons.

                  match goal with
                  | H: _ |- context [ add_all_to_heap ?ms (map ptr_to_int ?ptrs) ] =>
                      pose proof (add_all_to_heap_correct ptrs ms (add_all_to_heap ms (map ptr_to_int ptrs))) as ADDPTRS
                  end.

                  forward ADDPTRS; [reflexivity|].

                  eapply add_ptrs_to_heap_eqv; eauto.
                  unfold memory_stack_heap_prop in OLDHEAP.
                  rewrite <- OLDHEAP in ADD.
                  auto.
              }
              { split.
                reflexivity.
                auto.
              }
            }

            { (* OOM *)
              cbn in RUN.
              rewrite MemMonad_run_raise_oom in RUN.
              rewrite rbm_raise_bind in RUN.
              exfalso.
              symmetry in RUN.
              eapply MemMonad_eq1_raise_oom_inv in RUN.
              auto.
              typeclasses eauto.
            }
          }
      }

      Unshelve.
      all: try exact ""%string.
    Qed.

    (** Correctness of frame stack operations *)
    Lemma mempush_correct :
      exec_correct mempush mempush_spec_MemPropT.
    Proof.
      unfold exec_correct.
      intros ms st VALID.

      right.
      cbn.
      split; [do 2 exists ""%string; auto|].
      split; [do 2 exists ""%string; auto|].

      intros st' ms' [] RUN.
      unfold mempush in RUN.
      rewrite MemMonad_run_bind in RUN; auto.
      rewrite MemMonad_get_mem_state in RUN.
      rewrite bind_ret_l in RUN.
      rewrite MemMonad_put_mem_state in RUN.
      apply eq1_ret_ret in RUN; [inv RUN | typeclasses eauto].

      split.
      - (* fresh_frame *)
        intros fs1 fs2 f POP EMPTY PUSH.
        pose proof empty_frame_eqv _ _ EMPTY initial_frame_empty as EQinit.

        (* This:

          (mem_state_set_frame_stack ms (push_frame_stack (mem_state_frame_stack ms) initial_frame))

          Should be equivalent to (f :: fs1).
         *)
        eapply mem_state_frame_stack_prop_set_trans; [|apply mem_state_frame_stack_prop_set_refl].

        pose proof (eq_refl (push_frame_stack (mem_state_frame_stack ms) initial_frame)) as PUSH_INIT.
        apply push_frame_stack_correct in PUSH_INIT.

        unfold mem_state_frame_stack_prop in POP.
        red in POP.
        rewrite <- POP in PUSH.
        rewrite EQinit in PUSH.

        eapply push_frame_stack_inj; eauto.
      - (* mempush_invariants *)
        split.
        + (* read_byte_preserved *)
          (* TODO: solve_read_byte_preserved. *)
          split.
          * (* solve_read_byte_allowed_all_preserved. *)
            intros ?ptr; split; intros ?READ.
            -- (* read_byte_allowed *)
              apply read_byte_allowed_set_frame_stack; eauto.
            -- (* read_byte_allowed *)
              (* TODO: solve_read_byte_allowed *)
              eapply read_byte_allowed_set_frame_stack; eauto.
          * (* solve_read_byte_prop_all_preserved. *)
            apply read_byte_prop_set_frame_stack.
        + (* write_byte_allowed_all_preserved *)
            apply write_byte_allowed_all_preserved_set_frame_stack.
        + (* allocations_preserved *)
        (* TODO: move to solve_allocations_preserved *)
          apply allocations_preserved_set_frame_stack.
        + (* preserve_allocation_ids *)
          (* TODO: solve_preserve_allocation_ids *)
          apply preserve_allocation_ids_set_frame_stack.
        + unfold mem_state_set_frame_stack.
          red.
          unfold memory_stack_heap_prop. cbn.
          unfold memory_stack_heap.
          destruct ms.
          cbn.
          unfold MemState_get_memory.
          unfold mem_state_memory_stack.
          break_match.
          cbn.
          reflexivity.
    Qed.

    (* TODO: move *)
    Lemma read_byte_raw_memory_empty :
      forall ptr,
        read_byte_raw memory_empty ptr = None.
    Proof.
      intros ptr.
      Transparent read_byte_raw.
      unfold read_byte_raw.
      Opaque read_byte_raw.
      unfold memory_empty.
      apply IP.F.empty_o.
    Qed.

    Lemma free_byte_read_byte_raw :
      forall m m' ptr,
        free_byte ptr m = m' ->
        read_byte_raw m' ptr = None.
    Proof.
      intros m m' ptr FREE.
      Transparent read_byte_raw.
      unfold read_byte_raw.
      Opaque read_byte_raw.
      unfold free_byte in FREE.
      subst.
      apply IP.F.remove_eq_o; auto.
    Qed.

    Lemma free_frame_memory_cons :
      forall f m m' a,
        free_frame_memory (a :: f) m = m' ->
        exists m'',
          free_byte a m  = m'' /\
            free_frame_memory f m'' = m'.
    Proof.
      intros f m m' a FREE.
      rewrite list_cons_app in FREE.
      unfold free_frame_memory in *.
      rewrite fold_left_app in FREE.
      set (m'' := fold_left (fun (m : memory) (key : Iptr) => free_byte key m) [a] m).
      exists m''.
      subst m''.
      cbn; split; auto.
    Qed.

    Lemma free_block_memory_cons :
      forall block m m' a,
        free_block_memory (a :: block) m = m' ->
        exists m'',
          free_byte a m  = m'' /\
            free_block_memory block m'' = m'.
    Proof.
      intros f m m' a FREE.
      rewrite list_cons_app in FREE.
      unfold free_block_memory in *.
      rewrite fold_left_app in FREE.
      set (m'' := fold_left (fun (m : memory) (key : Iptr) => free_byte key m) [a] m).
      exists m''.
      subst m''.
      cbn; split; auto.
    Qed.

    Lemma free_byte_no_add :
      forall m m' ptr ptr',
        read_byte_raw m ptr = None ->
        free_byte ptr' m = m' ->
        read_byte_raw m' ptr = None.
    Proof.
      intros m m' ptr ptr' READ FREE.
      Transparent read_byte_raw.
      unfold read_byte_raw in *.
      Opaque read_byte_raw.
      unfold free_byte in FREE.
      subst.
      rewrite IP.F.remove_o.
      break_match; auto.
    Qed.

    Lemma free_frame_memory_no_add :
      forall f m m' ptr,
        read_byte_raw m ptr = None ->
        free_frame_memory f m = m' ->
        read_byte_raw m' ptr = None.
    Proof.
      induction f; intros m m' ptr READ FREE.
      - inv FREE; auto.
      - apply free_frame_memory_cons in FREE.
        destruct FREE as [m'' [FREEBYTE FREE]].

        eapply IHf.
        eapply free_byte_no_add; eauto.
        eauto.
    Qed.

    Lemma free_block_memory_no_add :
      forall block m m' ptr,
        read_byte_raw m ptr = None ->
        free_block_memory block m = m' ->
        read_byte_raw m' ptr = None.
    Proof.
      apply free_frame_memory_no_add.
    Qed.

    Lemma free_frame_memory_read_byte_raw :
      forall (f : Frame) (m m' : memory) ptr,
        free_frame_memory f m = m' ->
        ptr_in_frame_prop f ptr ->
        read_byte_raw m' (ptr_to_int ptr) = None.
    Proof.
      induction f;
        intros m m' ptr FREE IN.

      - inv IN.
      - apply free_frame_memory_cons in FREE.
        destruct FREE as [m'' [FREEBYTE FREE]].

        destruct IN as [IN | IN].
        + subst a.
          eapply free_frame_memory_no_add; eauto.
          eapply free_byte_read_byte_raw; eauto.
        + eapply IHf; eauto.
    Qed.

    Lemma free_block_memory_read_byte_raw :
      forall (block : Block) (m m' : memory) ptr,
        free_block_memory block m = m' ->
        In (ptr_to_int ptr) block ->
        read_byte_raw m' (ptr_to_int ptr) = None.
    Proof.
      induction block;
        intros m m' ptr FREE IN.

      - inv IN.
      - apply free_block_memory_cons in FREE.
        destruct FREE as [m'' [FREEBYTE FREE]].

        destruct IN as [IN | IN].
        + subst a.
          eapply free_block_memory_no_add; eauto.
          eapply free_byte_read_byte_raw; eauto.
        + eapply IHblock; eauto.
    Qed.

    Lemma free_byte_byte_not_allocated :
      forall (ms ms' : MemState) (m m' : memory) (ptr : addr),
        free_byte (ptr_to_int ptr) m = m' ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        byte_not_allocated ms' ptr.
    Proof.
      intros ms ms' m m' ptr FREE MS MS'.
      intros aid CONTRA.
      break_byte_allocated_in CONTRA.
      cbn in CONTRA.
      break_match; [|inv CONTRA; inv H1].
      break_match. subst.

      symmetry in MS'.
      apply free_byte_read_byte_raw in MS'.
      unfold mem_state_memory in *.
      rewrite MS' in Heqo.
      inv Heqo.
    Qed.

    Lemma free_frame_memory_byte_not_allocated :
      forall (ms ms' : MemState) (m m' : memory) f (ptr : addr),
        free_frame_memory f m = m' ->
        ptr_in_frame_prop f ptr ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        byte_not_allocated ms' ptr.
    Proof.
      intros ms ms' m m' f ptr FREE IN MS MS'.
      intros aid CONTRA.
      break_byte_allocated_in CONTRA.
      cbn in CONTRA.
      break_match; [|inv CONTRA; inv H1].
      break_match. subst.

      symmetry in MS'.
      eapply free_frame_memory_read_byte_raw in MS'; eauto.
      unfold mem_state_memory in *.
      rewrite Heqo in MS'.
      inv MS'.
    Qed.

    Lemma free_block_memory_byte_not_allocated :
      forall (ms ms' : MemState) (m m' : memory) block (ptr : addr),
        free_block_memory block m = m' ->
        In (ptr_to_int ptr) block ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        byte_not_allocated ms' ptr.
    Proof.
      intros ms ms' m m' block ptr FREE IN MS MS'.
      intros aid CONTRA.
      break_byte_allocated_in CONTRA.
      cbn in CONTRA.
      break_match; [|inv CONTRA; inv H1].
      break_match. subst.

      symmetry in MS'.
      eapply free_frame_memory_read_byte_raw in MS'; eauto.
      unfold mem_state_memory in *.
      rewrite Heqo in MS'.
      inv MS'.
    Qed.

    (* TODO move these *)
    Lemma free_byte_disjoint :
      forall m m' ptr ptr',
        free_byte ptr' m = m' ->
        ptr <> ptr' ->
        read_byte_raw m' ptr = read_byte_raw m ptr.
    Proof.
      intros m m' ptr ptr' FREE NEQ.
      Transparent read_byte_raw.
      unfold read_byte_raw in *.
      Opaque read_byte_raw.
      unfold free_byte in FREE.
      subst.
      rewrite IP.F.remove_neq_o; auto.
    Qed.

    Lemma free_frame_memory_disjoint :
      forall f m m' ptr,
        ~ ptr_in_frame_prop f ptr ->
        free_frame_memory f m = m' ->
        read_byte_raw m' (ptr_to_int ptr) = read_byte_raw m (ptr_to_int ptr).
    Proof.
      induction f; intros m m' ptr NIN FREE.
      - inv FREE; auto.
      - apply free_frame_memory_cons in FREE.
        destruct FREE as [m'' [FREEBYTE FREE]].

        erewrite IHf with (m:=m'').
        eapply free_byte_disjoint; eauto.
        firstorder.
        firstorder.
        auto.
    Qed.

    Lemma free_frame_memory_read_byte_raw_disjoint :
      forall (f : Frame) (m m' : memory) ptr,
        free_frame_memory f m = m' ->
        ~ptr_in_frame_prop f ptr ->
        read_byte_raw m' (ptr_to_int ptr) = read_byte_raw m (ptr_to_int ptr).
    Proof.
      induction f;
        intros m m' ptr FREE IN.

      - inv FREE. cbn.
        auto.
      - apply free_frame_memory_cons in FREE.
        destruct FREE as [m'' [FREEBYTE FREE]].
        cbn in IN.

        erewrite free_frame_memory_disjoint with (m:=m''); eauto.
        erewrite free_byte_disjoint with (m:=m); eauto.
    Qed.

    Lemma free_byte_byte_disjoint_allocated :
      forall (ms ms' : MemState) (m m' : memory) (ptr ptr' : addr) aid,
        free_byte (ptr_to_int ptr) m = m' ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        disjoint_ptr_byte ptr ptr' ->
        byte_allocated ms ptr' aid <-> byte_allocated ms' ptr' aid.
    Proof.
      intros ms ms' m m' ptr ptr' aid FREE MS MS' DISJOINT.
      split; intro ALLOC.
      - destruct ms as [[ms fs] pr].
        break_byte_allocated_in ALLOC.
        cbn in ALLOC.
        unfold mem_state_memory in ALLOC.
        cbn in ALLOC.

        repeat eexists; [| solve_returns_provenance].
        unfold mem_state_memory in *.
        rewrite MS'.
        erewrite free_byte_disjoint; eauto.
        cbn in *.
        break_match.
        break_match.
        tauto.
        tauto.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        break_byte_allocated_in ALLOC.
        cbn in ALLOC.

        unfold mem_state_memory in *.
        rewrite MS' in ALLOC.
        erewrite free_byte_disjoint in ALLOC; eauto.

        repeat eexists; [| solve_returns_provenance].
        cbn.
        break_match.
        break_match.
        tauto.
        tauto.
    Qed.

    Lemma byte_allocated_mem_state_refl :
      forall (ms ms' : MemState) (m : memory) (ptr : addr) aid,
        mem_state_memory ms = m ->
        mem_state_memory ms' = m ->
        byte_allocated ms ptr aid <-> byte_allocated ms' ptr aid.
    Proof.
      intros ms ms' m ptr aid MEQ1 MEQ2.
      split; intros ALLOC.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        break_byte_allocated_in ALLOC.
        cbn in ALLOC.

        repeat eexists; [| solve_returns_provenance].
        unfold mem_state_memory in *.
        break_match.
        break_match.
        tauto.
        tauto.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        break_byte_allocated_in ALLOC.
        cbn in ALLOC.

        repeat eexists; [| solve_returns_provenance].
        unfold mem_state_memory in *.
        cbn.
        break_match.
        break_match.
        tauto.
        tauto.
    Qed.

    Lemma free_frame_memory_byte_disjoint_allocated :
      forall f (ms ms' : MemState) (m m' : memory) (ptr : addr) aid,
        free_frame_memory f m = m' ->
        ~ptr_in_frame_prop f ptr ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        byte_allocated ms ptr aid <-> byte_allocated ms' ptr aid.
    Proof.
      induction f;
        intros ms ms' m m' ptr aid FREE NIN MS MS'.
      - inv FREE.
        cbn in H0.
        eapply byte_allocated_mem_state_refl; eauto.
      - apply free_frame_memory_cons in FREE.
        destruct FREE as [m'' [FREEBYTE FREE]].

        set (aptr := int_to_ptr a nil_prov).
        erewrite free_byte_byte_disjoint_allocated
          with (ptr:=aptr) (ms':= mkMemState (mkMemoryStack m'' (Singleton initial_frame) initial_heap) initial_provenance).
        2: {
          subst aptr. rewrite ptr_to_int_int_to_ptr; eauto.
        }
        all: eauto.
        2: {
          subst aptr.
          unfold disjoint_ptr_byte.
          rewrite ptr_to_int_int_to_ptr.
          firstorder.
        }

        eapply IHf; eauto.
        firstorder.
    Qed.

    Lemma free_block_memory_byte_disjoint_allocated :
      forall block (ms ms' : MemState) (m m' : memory) (ptr : addr) aid,
        free_block_memory block m = m' ->
        ~In (ptr_to_int ptr) block ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        byte_allocated ms ptr aid <-> byte_allocated ms' ptr aid.
    Proof.
      induction block;
        intros ms ms' m m' ptr aid FREE NIN MS MS'.
      - inv FREE.
        cbn in H0.
        eapply byte_allocated_mem_state_refl; eauto.
      - apply free_block_memory_cons in FREE.
        destruct FREE as [m'' [FREEBYTE FREE]].

        set (aptr := int_to_ptr a nil_prov).
        erewrite free_byte_byte_disjoint_allocated
          with (ptr:=aptr) (ms':= mkMemState (mkMemoryStack m'' (Singleton initial_frame) initial_heap) initial_provenance).
        2: {
          subst aptr. rewrite ptr_to_int_int_to_ptr; eauto.
        }
        all: eauto.
        2: {
          subst aptr.
          unfold disjoint_ptr_byte.
          rewrite ptr_to_int_int_to_ptr.
          firstorder.
        }

        eapply IHblock; eauto.
        firstorder.
    Qed.

    Lemma peek_frame_stack_prop_frame_eqv :
      forall fs f f',
        peek_frame_stack_prop fs f ->
        peek_frame_stack_prop fs f' ->
        frame_eqv f f'.
    Proof.
      intros fs f f' PEEK1 PEEK2.
      destruct fs; cbn in *;
        rewrite <- PEEK2 in PEEK1;
        auto.
    Qed.

    Lemma ptr_nin_current_frame :
      forall ptr ms fs f,
        ~ ptr_in_current_frame ms ptr ->
        mem_state_frame_stack_prop ms fs ->
        peek_frame_stack_prop fs f ->
        ~ ptr_in_frame_prop f ptr.
    Proof.
      intros ptr ms fs f NIN FS PEEK IN.
      unfold ptr_in_current_frame in NIN.
      apply NIN.
      intros fs' FS' f' PEEK'.
      unfold mem_state_frame_stack_prop in *.
      unfold memory_stack_frame_stack_prop in *.
      rewrite FS in FS'.
      rewrite <- FS' in PEEK'.
      erewrite peek_frame_stack_prop_frame_eqv
        with (f:=f') (f':=f); eauto.
    Qed.

    (* TODO: move *)
    Lemma free_byte_byte_disjoint_read_byte_allowed :
      forall (ms ms' : MemState) (m m' : memory) (ptr ptr' : addr),
        free_byte (ptr_to_int ptr) m = m' ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        disjoint_ptr_byte ptr ptr' ->
        read_byte_allowed ms ptr' <-> read_byte_allowed ms' ptr'.
    Proof.
      intros ms ms' m m' ptr ptr' FREE MS MS' DISJOINT.
      split; intro READ.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        unfold read_byte_allowed in *.
        destruct READ as [aid READ].
        destruct READ as [READ ALLOWED].
        exists aid.
        split; eauto.
        subst ms.

        erewrite <- free_byte_byte_disjoint_allocated; eauto.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        unfold read_byte_allowed in *.
        destruct READ as [aid READ].
        destruct READ as [READ ALLOWED].
        exists aid.
        split; eauto.
        subst ms.

        erewrite free_byte_byte_disjoint_allocated; eauto.
    Qed.

    Lemma free_frame_memory_byte_disjoint_read_byte_allowed :
      forall f (ms ms' : MemState) (m m' : memory) (ptr : addr),
        free_frame_memory f m = m' ->
        ~ptr_in_frame_prop f ptr ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        read_byte_allowed ms ptr <-> read_byte_allowed ms' ptr.
    Proof.
      intros f ms ms' m m' ptr FREE DISJOINT MS MS'.
      split; intro READ.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        unfold read_byte_allowed in *.
        destruct READ as [aid READ].
        destruct READ as [READ ALLOWED].
        exists aid.
        split; eauto.
        subst ms.

        erewrite <- free_frame_memory_byte_disjoint_allocated; eauto.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        unfold read_byte_allowed in *.
        destruct READ as [aid READ].
        destruct READ as [READ ALLOWED].
        exists aid.
        split; eauto.
        subst ms.

        erewrite free_frame_memory_byte_disjoint_allocated; eauto.
    Qed.

    Lemma free_block_memory_byte_disjoint_read_byte_allowed :
      forall block (ms ms' : MemState) (m m' : memory) (ptr : addr),
        free_block_memory block m = m' ->
        ~In (ptr_to_int ptr) block ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        read_byte_allowed ms ptr <-> read_byte_allowed ms' ptr.
    Proof.
      intros block ms ms' m m' ptr FREE DISJOINT MS MS'.
      split; intro READ.
      - destruct ms as [[ms fs h] pr].
        cbn in *.
        unfold read_byte_allowed in *.
        destruct READ as [aid READ].
        destruct READ as [READ ALLOWED].
        exists aid.
        split; eauto.
        subst ms.

        erewrite <- free_block_memory_byte_disjoint_allocated; eauto.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        unfold read_byte_allowed in *.
        destruct READ as [aid READ].
        destruct READ as [READ ALLOWED].
        exists aid.
        split; eauto.
        subst ms.

        erewrite free_frame_memory_byte_disjoint_allocated; eauto.
    Qed.

    Lemma free_byte_byte_disjoint_read_byte_prop :
      forall (ms ms' : MemState) (m m' : memory) (ptr ptr' : addr) byte,
        free_byte (ptr_to_int ptr) m = m' ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        disjoint_ptr_byte ptr ptr' ->
        read_byte_prop ms ptr' byte <-> read_byte_prop ms' ptr' byte.
    Proof.
      intros ms ms' m m' ptr ptr' byte FREE MS MS' DISJOINT.
      split; intro READ.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        destruct READ as [ms'' [ms''' [[EQ1 EQ2] READ]]]; subst.
        repeat eexists.
        cbn in *.
        unfold mem_state_memory in *.
        rewrite MS'.
        erewrite free_byte_disjoint; eauto.
        break_match.
        break_match.
        all: tauto.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        destruct READ as [ms'' [ms''' [[EQ1 EQ2] READ]]]; subst.
        repeat eexists.
        cbn in *.
        unfold mem_state_memory in *.
        rewrite MS' in READ.
        erewrite free_byte_disjoint in READ; eauto.
        break_match.
        break_match.
        all: tauto.
    Qed.

    Lemma free_frame_memory_byte_disjoint_read_byte_prop :
      forall f (ms ms' : MemState) (m m' : memory) (ptr : addr) byte,
        free_frame_memory f m = m' ->
        ~ptr_in_frame_prop f ptr ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        read_byte_prop ms ptr byte <-> read_byte_prop ms' ptr byte.
    Proof.
      intros f ms ms' m m' ptr byte FREE DISJOINT MS MS'.
      split; intro READ.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        destruct READ as [ms'' [ms''' [[EQ1 EQ2] READ]]]; subst.
        repeat eexists.
        cbn in *.
        unfold mem_state_memory in *.
        rewrite MS'.
        erewrite free_frame_memory_disjoint; eauto.
        break_match.
        break_match.
        all: tauto.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        destruct READ as [ms'' [ms''' [[EQ1 EQ2] READ]]]; subst.
        repeat eexists.
        cbn in *.
        unfold mem_state_memory in *.
        rewrite MS' in READ.
        erewrite free_frame_memory_disjoint in READ; eauto.
        break_match.
        break_match.
        all: tauto.
    Qed.

    Lemma free_block_memory_byte_disjoint_read_byte_prop :
      forall block (ms ms' : MemState) (m m' : memory) (ptr : addr) byte,
        free_block_memory block m = m' ->
        ~In (ptr_to_int ptr) block ->
        mem_state_memory ms = m ->
        mem_state_memory ms' = m' ->
        read_byte_prop ms ptr byte <-> read_byte_prop ms' ptr byte.
    Proof.
      intros block ms ms' m m' ptr byte FREE DISJOINT MS MS'.
      split; intro READ.
      - destruct ms as [[ms fs h] pr].
        cbn in *.
        destruct READ as [ms'' [ms''' [[EQ1 EQ2] READ]]]; subst.
        repeat eexists.
        cbn in *.
        unfold mem_state_memory in *.
        rewrite MS'.
        erewrite free_frame_memory_disjoint; eauto.
        break_match.
        break_match.
        all: tauto.
      - destruct ms as [[ms fs] pr].
        cbn in *.
        destruct READ as [ms'' [ms''' [[EQ1 EQ2] READ]]]; subst.
        repeat eexists.
        cbn in *.
        unfold mem_state_memory in *.
        rewrite MS' in READ.
        erewrite free_frame_memory_disjoint in READ; eauto.
        break_match.
        break_match.
        all: tauto.
    Qed.


    Lemma mempop_correct :
      exec_correct mempop mempop_spec_MemPropT.
    Proof.
      unfold exec_correct.
      intros ms st VALID.

      right.
      cbn.
      split; [do 2 exists ""%string; auto|].
      split; [do 2 exists ""%string; auto|].

      intros st' ms' [] RUN.
      unfold mempop in RUN.
      rewrite MemMonad_run_bind in RUN; auto.
      rewrite MemMonad_get_mem_state in RUN.
      rewrite bind_ret_l in RUN.
      destruct ms as [[mem fs h] pr].
      cbn in RUN.
      rewrite MemMonad_run_bind in RUN.
      destruct fs as [f | fs f].
      - (* Pop singleton, error *)
        cbn in RUN.
        rewrite MemMonad_run_raise_error in RUN.
        rewrite rbm_raise_bind in RUN; [|solve [typeclasses eauto]].
        symmetry in RUN.
        apply MemMonad_eq1_raise_error_inv in RUN.
        contradiction.
      - (* Pop succeeds *)
        cbn in RUN.
        rewrite MemMonad_run_ret in RUN; auto.
        rewrite bind_ret_l in RUN.
        rewrite MemMonad_put_mem_state in RUN.

        apply eq1_ret_ret in RUN; [inv RUN | typeclasses eauto].

        (* mempop_spec *)
        { split.
          - (* bytes_freed *)
            (* TODO : solve_byte_not_allocated? *)
            intros ptr IN.

            unfold ptr_in_current_frame in IN.
            specialize (IN (Snoc fs f)).
            forward IN.
            { apply mem_state_frame_stack_prop_refl.
              cbn. reflexivity.
            }
            specialize (IN f).
            forward IN.
            cbn. reflexivity.

            eapply free_frame_memory_byte_not_allocated
              with (ms := mkMemState (mkMemoryStack mem (Snoc fs f) h) pr); eauto.
          - (* non_frame_bytes_preserved *)
            intros ptr aid NIN.

            eapply free_frame_memory_byte_disjoint_allocated; cbn; eauto.
            eapply ptr_nin_current_frame; cbn; eauto.
            unfold mem_state_frame_stack_prop. red. reflexivity.
            cbn. reflexivity.
          - (* non_frame_bytes_read *)
            intros ptr byte NIN.

            split; intros READ.
            + split.
              * (* read_byte_allowed *)
                eapply free_frame_memory_byte_disjoint_read_byte_allowed
                  with (ms := mkMemState (mkMemoryStack mem (Snoc fs f) h) pr); cbn;
                  eauto.
                eapply ptr_nin_current_frame; eauto.
                all: unfold mem_state_frame_stack_prop; cbn; red; try reflexivity.
                cbn. reflexivity.
                inv READ; solve_read_byte_allowed.
              * (* read_byte_prop *)
                eapply free_frame_memory_byte_disjoint_read_byte_prop
                  with (ms := mkMemState (mkMemoryStack mem (Snoc fs f) h) pr);
                  eauto.
                eapply ptr_nin_current_frame; eauto.
                all: unfold mem_state_frame_stack_prop; try solve [cbn; reflexivity].
                cbn. red; reflexivity.
                cbn. red; reflexivity.

                inv READ; solve_read_byte_prop.
            + (* read_byte_spec *)
              split.
              * (* read_byte_allowed *)
                eapply free_frame_memory_byte_disjoint_read_byte_allowed
                  with (ms := mkMemState (mkMemoryStack mem (Snoc fs f) h) pr)
                       (ms' := {|
                                ms_memory_stack :=
                                (mkMemoryStack (fold_left (fun (m : memory) (key : Iptr) => free_byte key m) f mem) fs h);
                                ms_provenance := pr
                              |});
                  eauto.
                eapply ptr_nin_current_frame; eauto.
                all: unfold mem_state_frame_stack_prop; try solve [cbn; reflexivity].
                cbn. red. reflexivity.
                cbn. red. reflexivity.
                inv READ; solve_read_byte_allowed.
              * (* read_byte_prop *)
                eapply free_frame_memory_byte_disjoint_read_byte_prop
                  with (ms := mkMemState (mkMemoryStack mem (Snoc fs f) h) pr)
                       (ms' := {|
                                ms_memory_stack :=
                                (mkMemoryStack (fold_left (fun (m : memory) (key : Iptr) => free_byte key m) f mem) fs h);
                                ms_provenance := pr
                              |});
                  eauto.
                eapply ptr_nin_current_frame; eauto.
                all: unfold mem_state_frame_stack_prop; try solve [cbn; reflexivity].
                cbn. red. reflexivity.
                cbn. reflexivity.
                inv READ; solve_read_byte_prop.
          - (* pop_frame *)
            intros fs1 fs2 FS POP.
            unfold pop_frame_stack_prop in POP.
            destruct fs1; [contradiction|].
            red; cbn.
            red in FS; cbn in FS.
            apply frame_stack_snoc_inv_fs in FS.
            rewrite FS.
            rewrite POP.
            reflexivity.
          - (* mempop_invariants *)
            split.
            + (* preserve_allocation_ids *)
              red. unfold used_provenance_prop.
              cbn. reflexivity.
            + (* heap preserved *)
              solve_heap_preserved.
        }
    Qed.

    Lemma free_correct :
      forall ptr,
        exec_correct (free ptr) (free_spec_MemPropT ptr).
    Proof.
      unfold exec_correct.
      intros ptr ms st VALID.

      (* Need to determine if `ptr` is a root in the heap... If not,
         UB has occurred.
       *)

      destruct ms as [[mem fs h] pr].
      destruct (member (ptr_to_int ptr) h) eqn:ROOTIN.

      2: { (* UB, ptr not a root of the heap *)
        left.
        eexists.
        cbn.
        intros m2 FREE.
        inv FREE.
        unfold root_in_memstate_heap in *.
        specialize (free_was_root0 h).
        forward free_was_root0.
        cbn. red. cbn. reflexivity.
        unfold root_in_heap_prop in free_was_root0.
        rewrite ROOTIN in free_was_root0.
        inv free_was_root0.
      }
      
      pose proof (member_lookup _ _ ROOTIN) as (block & FINDPTR).
      right.
      cbn.
      split; [do 2 exists ""%string; auto|].
      split; [do 2 exists ""%string; auto|].

      intros st' ms' [] RUN.
      unfold free in RUN.
      rewrite MemMonad_run_bind in RUN; auto.
      rewrite MemMonad_get_mem_state in RUN.
      rewrite bind_ret_l in RUN.
      cbn in RUN.
      rewrite FINDPTR in RUN.
      rewrite MemMonad_put_mem_state in RUN.
      eapply eq1_ret_ret in RUN; [| typeclasses eauto].
      inv RUN.

      (* Proof of free_spec *)
      split.
      - (* free_was_root *)
        red.
        intros h0 HEAP.
        cbn in *.
        red.
        unfold memory_stack_heap_prop in HEAP.
        cbn in HEAP.
        eapply member_ptr_to_int_heap_eqv_Proper.
        reflexivity.
        symmetry; eauto.
        eauto.
      (* - (* free_removes_root *) *)
      (*   intros CONTRA. *)
      (*   red in CONTRA. *)
      (*   cbn in CONTRA. *)
      (*   specialize (CONTRA (delete (ptr_to_int ptr) h)). *)
      (*   forward CONTRA. *)
      (*   { unfold memory_stack_heap_prop; reflexivity. *)
      (*   } *)

      (*   unfold root_in_heap_prop in *. *)
      (*   unfold member, delete in *. *)
      (*   rewrite IP.F.remove_eq_b in CONTRA; auto; inv CONTRA. *)
      - (* free_bytes_freed *)
        (* TODO : solve_byte_not_allocated? *)
        intros ptr0 HEAP.
        red in HEAP.
        cbn in HEAP.
        specialize (HEAP h).
        forward HEAP.
        { unfold memory_stack_heap_prop; reflexivity.
        }

        unfold byte_not_allocated.
        intros aid ALLOCATED.

        unfold ptr_in_heap_prop in HEAP.
        break_match_hyp; try inv HEAP.
        unfold lookup in FINDPTR.
        rewrite FINDPTR in Heqo; inv Heqo.

        eapply free_block_memory_byte_not_allocated
          with (ms := mkMemState (mkMemoryStack mem fs h) pr); eauto.

        cbn.
        reflexivity.

      - (* free_non_block_bytes_preserved *)
        intros ptr0 aid NIN.

        eapply free_block_memory_byte_disjoint_allocated; cbn; eauto.
        { unfold ptr_in_memstate_heap in *.
          cbn in *.
          intros IN.
          apply NIN.
          intros h0 H0.
          red in H0.
          cbn in H0.
          rewrite <- H0.
          red.
          unfold lookup in FINDPTR.
          rewrite FINDPTR; auto.
        }        
      - (* free_non_frame_bytes_read *)
        intros ptr0 byte NIN.

        split; intros READ.
        + split.
          * (* read_byte_allowed *)
            eapply free_block_memory_byte_disjoint_read_byte_allowed
              with (ms := mkMemState (mkMemoryStack mem fs h) pr); cbn;
              eauto.
            { unfold ptr_in_memstate_heap in *.
              cbn in *.
              intros IN.
              apply NIN.
              intros h0 H0.
              red in H0.
              cbn in H0.
              rewrite <- H0.
              red.
              unfold lookup in FINDPTR.
              rewrite FINDPTR; auto.
            }
            inv READ; solve_read_byte_allowed.
          * (* read_byte_prop *)
            eapply free_block_memory_byte_disjoint_read_byte_prop
              with (ms := mkMemState (mkMemoryStack mem fs h) pr);
              eauto.
            { unfold ptr_in_memstate_heap in *.
              cbn in *.
              intros IN.
              apply NIN.
              intros h0 H0.
              red in H0.
              cbn in H0.
              rewrite <- H0.
              red.
              unfold lookup in FINDPTR.
              rewrite FINDPTR; eauto.
            }
            inv READ; solve_read_byte_prop.
            inv READ; solve_read_byte_prop.
        + (* read_byte_spec *)
          split.
          * (* read_byte_allowed *)
            eapply free_block_memory_byte_disjoint_read_byte_allowed
              with (ms := mkMemState (mkMemoryStack mem fs h) pr)
                   (ms' := {|
                            ms_memory_stack :=
                            mkMemoryStack (free_block_memory block mem) fs (delete (ptr_to_int ptr) h);
                            ms_provenance := pr
                          |});
              eauto.
            { unfold ptr_in_memstate_heap in *.
              cbn in *.
              intros IN.
              apply NIN.
              intros h0 H0.
              red in H0.
              cbn in H0.
              rewrite <- H0.
              red.
              unfold lookup in FINDPTR.
              rewrite FINDPTR; eauto.
            }
            all: unfold mem_state_frame_stack_prop; try solve [cbn; reflexivity].
            inv READ; solve_read_byte_allowed.
          * (* read_byte_prop *)
            eapply free_frame_memory_byte_disjoint_read_byte_prop
              with (ms := mkMemState (mkMemoryStack mem fs h) pr)
                   (ms' := {|
                            ms_memory_stack :=
                            mkMemoryStack (free_block_memory block mem) fs (delete (ptr_to_int ptr) h);
                            ms_provenance := pr
                          |});
              eauto.
            { unfold ptr_in_memstate_heap in *.
              cbn in *.
              intros IN.
              apply NIN.
              intros h0 H0.
              red in H0.
              cbn in H0.
              rewrite <- H0.
              red.
              unfold lookup in FINDPTR.
              rewrite FINDPTR; eauto.
            }
            all: unfold mem_state_frame_stack_prop; try solve [cbn; reflexivity].
            inv READ; solve_read_byte_prop.
      - (* free_block *)
        intros h1 h2 HEAP1 HEAP2.
        cbn in *.
        unfold memory_stack_heap_prop in *.
        cbn in *.
        split.
        + (* free_block_ptrs_freed *)
          intros ptr0 IN CONTRA.
          inv HEAP2.
          apply heap_ptrs_eqv0 in CONTRA.
          unfold ptr_in_heap_prop in *.
          break_match_hyp; try inv CONTRA.
          unfold delete in *.
          rewrite IP.F.remove_eq_o in Heqo; auto; inv Heqo.
        + (* free_block_root_freed *)
          intros CONTRA.
          inv HEAP2.
          apply heap_roots_eqv0 in CONTRA.
          unfold root_in_heap_prop in *.
          unfold member, delete in *.
          rewrite IP.F.remove_eq_b in CONTRA; auto; inv CONTRA.
        + (* free_block_disjoint_preserved *)
          intros ptr0 root' DISJOINT.
          split; intros IN.
          * apply HEAP2.
            unfold ptr_in_heap_prop.
            unfold delete.
            rewrite IP.F.remove_neq_o; auto.
            apply HEAP1; auto.
          * apply HEAP2 in IN.
            unfold ptr_in_heap_prop in IN.
            unfold delete in IN.
            rewrite IP.F.remove_neq_o in IN; auto.
            apply HEAP1 in IN; auto.
        + (* free_block_disjoint_roots *)
          intros root' DISJOINT.
          split; intros IN.
          * apply HEAP2.
            unfold root_in_heap_prop.
            unfold delete.
            rewrite IP.F.remove_neq_b; auto.
            apply HEAP1; auto.
          * apply HEAP2 in IN.
            unfold root_in_heap_prop in IN.
            unfold delete in IN.
            rewrite IP.F.remove_neq_b in IN; auto.
            apply HEAP1 in IN; auto.
      - (* free_invariants *)
        split.
        + (* Allocation ids preserved *)
          red. unfold used_provenance_prop.
          cbn. reflexivity.
        + (* Framestack preserved *)
          solve_frame_stack_preserved.

          Unshelve.
          all: exact ""%string.
    Qed.

    (*** Initial memory state *)
    Record initial_memory_state_prop : Prop :=
      {
        initial_memory_no_allocations :
        forall ptr aid,
          ~ byte_allocated initial_memory_state ptr aid;

        initial_memory_frame_stack :
        forall fs,
          memory_stack_frame_stack_prop (MemState_get_memory initial_memory_state) fs ->
          empty_frame_stack fs;

        initial_memory_heap :
        forall h,
          memory_stack_heap_prop (MemState_get_memory initial_memory_state) h ->
          empty_heap h;

        initial_memory_read_ub :
        forall ptr byte,
          read_byte_prop initial_memory_state ptr byte
      }.

    Record initial_frame_prop : Prop :=
      {
        initial_frame_is_empty : empty_frame initial_frame;
      }.

    Record initial_heap_prop : Prop :=
      {
        initial_heap_is_empty : empty_heap initial_heap;
      }.

    Lemma initial_frame_correct : initial_frame_prop.
    Proof.
      split.
      apply initial_frame_empty.
    Qed.

    Lemma initial_heap_correct : initial_heap_prop.
    Proof.
      split.
      split.
      - intros root.
        unfold initial_heap.
        unfold root_in_heap_prop.
        intros CONTRA.
        rewrite IP.F.empty_a in CONTRA.
        inv CONTRA.
      - intros ptr.
        unfold initial_heap.
        cbn.
        auto.
    Qed.

    (* TODO: move this? *)
    #[global] Instance empty_frame_stack_Proper :
      Proper (frame_stack_eqv ==> iff) empty_frame_stack.
    Proof.
      intros fs' fs FS.
      split; intros [NOPOP EMPTY].
      - split.
        + setoid_rewrite <- FS.
          auto.
        + setoid_rewrite <- FS.
          auto.
      - split.
        + setoid_rewrite FS.
          auto.
        + setoid_rewrite FS.
          auto.
    Qed.

    (* TODO: move this? *)
    #[global] Instance empty_frame_Proper :
      Proper (frame_eqv ==> iff) empty_frame.
    Proof.
      intros f' f F.
      unfold empty_frame.
      setoid_rewrite F.
      reflexivity.
    Qed.

    (* TODO: move this? *)
    Lemma empty_frame_nil :
      empty_frame [].
    Proof.
      red.
      cbn.
      auto.
    Qed.

    (* TODO: move this? *)
    Lemma empty_frame_stack_frame_empty :
      empty_frame_stack frame_empty.
    Proof.
      unfold frame_empty.
      split.
      - intros f CONTRA.
        cbn in *; auto.
      - intros f CONTRA.
        cbn in *.
        rewrite CONTRA.
        apply empty_frame_nil.
    Qed.

    (* TODO: move this? *)
    #[global] Instance empty_heap_Proper :
      Proper (heap_eqv ==> iff) empty_heap.
    Proof.
      intros f' f F.
      split; intros [ROOTS PTRS].
      - split; setoid_rewrite <- F; auto.
      - split; setoid_rewrite F; auto.
    Qed.

    (* TODO: move this? *)
    Lemma empty_heap_heap_empty :
      empty_heap heap_empty.
    Proof.
      unfold heap_empty.
      split.
      - intros root CONTRA.
        red in CONTRA.
        unfold member in CONTRA.
        rewrite IP.F.empty_a in CONTRA.
        inv CONTRA.
      - intros root ptr CONTRA.
        red in CONTRA.
        unfold member in CONTRA.
        rewrite IP.F.empty_o in CONTRA.
        inv CONTRA.
    Qed.

    Lemma initial_memory_state_correct : initial_memory_state_prop.
    Proof.
      split.
      - intros ptr aid CONTRA.
        unfold initial_memory_state in *.
        break_byte_allocated_in CONTRA.
        break_match_hyp; [break_match_hyp|].
        + cbn in *.
          rewrite read_byte_raw_memory_empty in Heqo.
          inv Heqo.
        + cbn in *.
          destruct CONTRA as [_ CONTRA].
          inv CONTRA.
      - intros fs FS.
        cbn in FS.
        red in FS.
        rewrite <- FS.
        cbn.
        apply empty_frame_stack_frame_empty.
      - intros h HEAP.
        cbn in HEAP.
        red in HEAP.
        rewrite <- HEAP.
        cbn.
        apply empty_heap_heap_empty.
      - intros ptr byte.
        solve_read_byte_prop.
    Qed.

  End MemoryPrimatives.

End FiniteMemoryModelExecPrimitives.

Module MakeFiniteMemoryModelSpec (LP : LLVMParams) (MP : MemoryParams LP).
  Module FMSP := FiniteMemoryModelSpecPrimitives LP MP.
  Module FMS := MakeMemoryModelSpec LP MP FMSP.

  Export FMSP FMS.
End MakeFiniteMemoryModelSpec.

Module MakeFiniteMemoryModelExec (LP : LLVMParams) (MP : MemoryParams LP).
  Module FMEP := FiniteMemoryModelExecPrimitives LP MP.
  Module FME := MakeMemoryModelExec LP MP FMEP.
End MakeFiniteMemoryModelExec.

Module MakeFiniteMemory (LP : LLVMParams) <: Memory LP.
  Import LP.

  Module GEP := GepM.Make ADDR IP SIZEOF Events PTOI PROV ITOP.
  Module Byte := FinByte ADDR IP SIZEOF Events.

  Module MP := MemoryParams.Make LP GEP Byte.

  Module MMEP := FiniteMemoryModelExecPrimitives LP MP.
  Module MEM_MODEL := MakeMemoryModelExec LP MP MMEP.
  Module MEM_SPEC_INTERP := MakeMemorySpecInterpreter LP MP MMEP.MMSP MMEP.MemSpec MMEP.MemExecM.
  Module MEM_EXEC_INTERP := MakeMemoryExecInterpreter LP MP MMEP MEM_MODEL MEM_SPEC_INTERP.

  (* Serialization *)
  Module SP := SerializationParams.Make LP MP.

  Export GEP Byte MP MEM_MODEL SP.
End MakeFiniteMemory.

Module LLVMParamsBigIntptr := LLVMParams.MakeBig Addr BigIP FinSizeof FinPTOI FinPROV FinITOP BigIP_BIG.
Module LLVMParams64BitIntptr := LLVMParams.Make Addr IP64Bit FinSizeof FinPTOI FinPROV FinITOP.

Module MemoryBigIntptr := MakeFiniteMemory LLVMParamsBigIntptr.
Module Memory64BitIntptr := MakeFiniteMemory LLVMParams64BitIntptr.


Module MemoryBigIntptrInfiniteSpec <: MemoryModelInfiniteSpec LLVMParamsBigIntptr MemoryBigIntptr.MP MemoryBigIntptr.MMEP.MMSP MemoryBigIntptr.MMEP.MemSpec.
  (* Intptrs are "big" *)
  Module LP := LLVMParamsBigIntptr.
  Module MP := MemoryBigIntptr.MP.

  Module MMSP := MemoryBigIntptr.MMEP.MMSP.
  Module MMS := MemoryBigIntptr.MMEP.MemSpec.
  Module MME := MemoryBigIntptr.MEM_MODEL.

  Import LP.Events.
  Import LP.ITOP.
  Import LP.PTOI.
  Import LP.IP_BIG.
  Import LP.IP.
  Import LP.ADDR.
  Import LP.PROV.
  Import LP.SIZEOF.

  Import MMSP.
  Import MMS.
  Import MemHelpers.

  Import Monad.
  Import MapMonadExtra.
  Import MP.GEP.

  Module MSIH := MemStateInfiniteHelpers LP MP MMSP MMS.
  Import MSIH.

  Import MemoryBigIntptr.
  Import MMEP.
  Import MP.BYTE_IMPL.
  Import MemExecM.

  Module MemTheory  := MemoryModelTheory LP MP MMEP MME.
  Import MemTheory.

  Module SpecInterp := MakeMemorySpecInterpreter LP MP MMSP MMS MemExecM.
  Module ExecInterp := MakeMemoryExecInterpreter LP MP MMEP MME SpecInterp.
  Import SpecInterp.
  Import ExecInterp.

  Definition Eff := FailureE +' OOME +' UBE.

  Import Eq.
  Import MMSP.

(*   Lemma allocate_bytes_always_succeeds : *)
(*     forall dt init_bytes ms_init, *)
(*     exists (alloc_addr : addr) ms_final, *)
(*       allocate_bytes_spec_MemPropT dt init_bytes ms_init (ret (ms_final, alloc_addr)). *)
(*   Proof. *)
(*     intros dt init_bytes ms_init. *)

(*     remember ms_init as m. *)
(*     destruct m. *)
(*     destruct ms_memory_stack0. *)
(*     destruct (MMSP.mem_state_fresh_provenance ms_init) as [p ms_fresh_prov] eqn:FRESH. *)
(*     apply mem_state_fresh_provenance_fresh in FRESH as [MEMEQ [PRESERVED_PR FRESH]].     *)

(*     set (next_ptr := *)
(*            (LLVMParamsBigIntptr.ITOP.int_to_ptr *)
(*               (next_memory_key *)
(*                  {| *)
(*                    memory_stack_memory := memory_stack_memory0; *)
(*                    memory_stack_frame_stack := memory_stack_frame_stack0; *)
(*                    memory_stack_heap := memory_stack_heap0 *)
(*                  |}) *)
(* (LLVMParamsBigIntptr.PROV.allocation_id_to_prov *)
(*               (LLVMParamsBigIntptr.PROV.provenance_to_allocation_id *)
(*                  (LLVMParamsBigIntptr.PROV.next_provenance ms_provenance0))))). *)

(*     assert (MonadLawsE (MemStateFreshT (itree Eff))) as LAWS by admit. *)
(*     assert (Eq1_ret_inv (MemStateFreshT (itree Eff))) as RETINV by admit. *)
(*     (* pose proof @get_consecutive_ptrs_succeeds (MemStateFreshT (itree Eff)) _ _ _ RETINV _ _ LAWS next_ptr (Datatypes.length init_bytes) as (ptrs & CONSEC). *) *)
(*     assert (MonadLawsE (MemPropT MMSP.MemState)) as LAWS' by admit. *)
(*     assert (Eq1_ret_inv (MemPropT MMSP.MemState)) as RETINV' by admit. *)
(*     (* pose proof @get_consecutive_ptrs_succeeds (MemPropT MMSP.MemState) _ _ _ RETINV' _ _ LAWS' next_ptr (Datatypes.length init_bytes) as (ptrs & CONSEC). *) *)
(*     pose proof @get_consecutive_ptrs_succeeds (MemStateFreshT (itree Eff)) _ _ _ RETINV _ _ LAWS next_ptr (Datatypes.length init_bytes) as (ptrs & CONSEC). *)

(*     exists next_ptr. *)
(*     exists ({| *)
(*         MemoryBigIntptrInfiniteSpec.MMSP.ms_memory_stack := *)
(*           add_all_to_frame *)
(*             {| *)
(*               MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_memory := *)
(*                 add_all_index *)
(*                   (map *)
(*                      (fun b : SByte => *)
(*                       (b, *)
(*                       LLVMParamsBigIntptr.PROV.provenance_to_allocation_id *)
(*                         (LLVMParamsBigIntptr.PROV.next_provenance ms_provenance0))) init_bytes) *)
(*                   (next_memory_key *)
(*                      {| *)
(*                        MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_memory := memory_stack_memory0; *)
(*                        MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_frame_stack := *)
(*                          memory_stack_frame_stack0; *)
(*                        MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_heap := memory_stack_heap0 *)
(*                      |}) memory_stack_memory0; *)
(*               MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_frame_stack := memory_stack_frame_stack0; *)
(*               MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_heap := memory_stack_heap0 *)
(*             |} (map LLVMParamsBigIntptr.PTOI.ptr_to_int ptrs); *)
(*         MemoryBigIntptrInfiniteSpec.MMSP.ms_provenance := *)
(*           LLVMParamsBigIntptr.PROV.next_provenance ms_provenance0 *)
(*         |}). *)

(*     assert store_id as init_store_id. *)
(*     admit. *)

(*     pose proof @allocate_bytes_correct (MemStateFreshT (itree Eff)) Eff as CORRECT. *)
(*     unfold exec_correct in CORRECT. *)
(*     specialize (CORRECT store_id _ _ _ _ _ _ _ _ _ _ _ _ dt init_bytes ms_init init_store_id). *)
(*     forward CORRECT. *)
(*     admit. *)
(*     destruct CORRECT as [UB | CORRECT]. *)
(*       - (* UB in spec *) *)
(*         destruct UB as [ubmsg UB]. *)
(*         unfold MemSpec.allocate_bytes_spec_MemPropT in *. *)

(*         (* Fresh provenance bind in MemPropT *) *)
(*         cbn in UB. *)
(*         destruct UB as [[] | UB]. *)
(*         destruct UB as [ms_fresh_pr [pr [FRESH_PROV_INVARIANTS UB]]]. *)
(*         destruct UB as [ALLOC_FAILS_UB | UB]. *)
(*         + (* Allocation fails, should be bogus because we prove it succeeds... *) *)
          
(*         +  *)
        
(*         rewrite MemMonad_run_fresh_provenance in UB. *)
(*         unfold MemSpec.allocate_bytes_spec_MemPropT' in . *)

(*         cbn in UB. *)
        
(*         destruct UB as [sab [pr ]. *)
(*       destruct UB as [sab [a [BLAH REST]]]. *)

    

(*   Qed. *)

  (* TODO: Move this thing? *)
  Lemma get_consecutive_MemPropT_MemStateFreshT :
    forall ptr len ptrs,
      (@get_consecutive_ptrs (MemPropT MemState) (@MemPropT_Monad MemState) (@MemPropT_RAISE_OOM MemState)
                             (@MemPropT_RAISE_ERROR MemState) ptr len
                             ≈ @ret (MemPropT MemState) (@MemPropT_Monad MemState) (list addr) ptrs)%monad <->
        (@get_consecutive_ptrs (MemStateFreshT (itree Eff)) _
                               _ _
                               ptr len
                               ≈ ret ptrs)%monad.
  Proof.
    intros ptr len ptrs.
    split; intros CONSEC.
    - unfold get_consecutive_ptrs in *.
      destruct (intptr_seq 0 len) eqn:HSEQ.
      + cbn in *.
        unfold eq1 in CONSEC.
        red in CONSEC.
        do 6 red.
        intros sid ms.
        rewrite bind_ret_l.
        cbn.

        specialize (CONSEC ms (ret (ms, ptrs))).
        cbn in CONSEC.
        destruct CONSEC as [blah CONSEC].
        forward CONSEC; auto.
        destruct CONSEC as [ms' [a [[EQ1 EQ2] CONSEC]]].
        subst.
        destruct (map_monad
        (fun ix : LLVMParamsBigIntptr.IP.intptr =>
           GEP.handle_gep_addr (DTYPE_I 8) ptr [LLVMParamsBigIntptr.Events.DV.DVALUE_IPTR ix]) l);
          inv CONSEC.

        cbn.
        reflexivity.
      + cbn in *.
        unfold eq1 in CONSEC.
        intros sid ms.
        specialize (CONSEC ms (ret (ms, ptrs))).
        cbn in CONSEC.
        destruct CONSEC as [blah CONSEC].
        forward CONSEC; auto.
        destruct CONSEC as [ms' [a [[]CONSEC]]].
    - unfold get_consecutive_ptrs in *.
      destruct (intptr_seq 0 len) eqn:HSEQ.
      + cbn in *.
        unfold eq1 in CONSEC.
        do 7 red in CONSEC.
        do 2 red.
        intros ms x.
        setoid_rewrite bind_ret_l in CONSEC.
        cbn in CONSEC.

        destruct (map_monad
                    (fun ix : LLVMParamsBigIntptr.IP.intptr =>
                       GEP.handle_gep_addr (DTYPE_I 8) ptr [LLVMParamsBigIntptr.Events.DV.DVALUE_IPTR ix]) l) eqn:HMAPM.
        { (* Error raised *)
          cbn in CONSEC.
          specialize (CONSEC 0%N ms).
          (* Contradition, need inversion lemma *)
          admit.
        }

        specialize (CONSEC 0%N ms).
        cbn in CONSEC.
        assert (l0 = ptrs) by admit; subst.
        destruct_err_ub_oom x.
        * split; intros H.
          destruct H; auto.
          destruct H as [ms' [a' [[EQ1 EQ2] H]]]; subst.
          rewrite HMAPM in H.
          cbn in H.
          auto.

          inv H.
        * split; intros H.
          destruct H; auto.
          destruct H as [ms' [a' [[EQ1 EQ2] H]]]; subst.
          rewrite HMAPM in H.
          cbn in H.
          auto.

          inv H.
        * split; intros H.
          destruct H; auto.
          destruct H as [ms' [a' [[EQ1 EQ2] H]]]; subst.
          rewrite HMAPM in H.
          cbn in H.
          auto.

          inv H.
        * destruct x0.
          split; intros H.
          -- destruct H as [ms' [a' [[EQ1 EQ2] H]]]; subst.
             rewrite HMAPM in H.
             cbn in H.
             auto.
          -- exists ms. exists l.
             split; auto.
             rewrite HMAPM.
             cbn.
             auto.
      + cbn in *.
        unfold eq1 in CONSEC.
        do 7 red in CONSEC.
        do 2 red.
        intros ms x.
        setoid_rewrite bind_bind in CONSEC.
        
        specialize (CONSEC 0%N ms).
        (* need inversion lemma for consec *)
        admit.
  Admitted.

  Lemma allocate_bytes_succeeds_spec_correct :
    forall (ms_init ms_fresh_pr ms_final : MemState) (st sid st' st_final : store_id) dt init_bytes (pr : Provenance) (ptr : addr) (ptrs : list addr)
      (VALID : @MemMonad_valid_state store_id (MemStateFreshT (itree Eff)) (itree Eff) _ _ _ _ _ _ _ _ _ _ _ _ ms_init st)
      (VALID' : @MemMonad_valid_state store_id (MemStateFreshT (itree Eff)) (itree Eff) _ _ _ _ _ _ _ _ _ _ _ _ ms_fresh_pr st)
      (BYTES_SIZE : sizeof_dtyp dt = N.of_nat (length init_bytes))
      (NON_VOID : dt <> DTYPE_Void)
      (RUN_FRESH : (@MemMonad_run store_id (MemStateFreshT (itree Eff)) (itree Eff) _ _ _ _ _ _ _ _ _ _ _ _ _ fresh_provenance ms_init st ≈ ret (st, (ms_fresh_pr, pr)))%monad)
      (MEMORY_FRESH : ms_get_memory ms_init = ms_get_memory ms_fresh_pr)
      (RUN_FRESH_SID : (@MemMonad_run store_id (MemStateFreshT (itree Eff)) (itree Eff) _ _ _ _ _ _ _ _ _ _ _ _ _ fresh_sid ms_fresh_pr st ≈ ret (st', (ms_fresh_pr, sid)))%monad)
      (ALLOC : (@MemMonad_run store_id (MemStateFreshT (itree Eff)) (itree Eff) _ _ _ _ _ _ _ _ _ _ _ _ _ (@allocate_bytes (MemStateFreshT (itree Eff)) Eff _ _ _ _ _ _ _ _ _ _ _ _ _ dt init_bytes) ms_init st ≈ ret (st', (ms_final, ptr)))%monad)
      (CONSEC : (@get_consecutive_ptrs (MemStateFreshT (itree Eff)) _ _ _ ptr (length init_bytes) ≈ ret ptrs)%monad)
      (PR : address_provenance ptr = allocation_id_to_prov (provenance_to_allocation_id pr)),
      allocate_bytes_succeeds_spec ms_fresh_pr dt init_bytes pr ms_final ptr ptrs.
  Proof.
    intros ms_init ms_fresh_pr ms_final st sid st' st_final dt init_bytes pr ptr ptrs VALID VALID' BYTES_SIZE NON_VOID RUN_FRESH MEMORY_FRESH RUN_FRESH_SID ALLOC CONSEC PR.

    Opaque get_consecutive_ptrs.
    unfold allocate_bytes in ALLOC.

    destruct (dtyp_eq_dec dt DTYPE_Void) as [EQ_VOID | ];
      [contradiction |].

    destruct (N.eq_dec (LLVMParamsBigIntptr.SIZEOF.sizeof_dtyp dt)
                       (N.of_nat (Datatypes.length init_bytes))) as [EQ_SIZE | NEQ_SIZE];
      [| contradiction].

    pose proof (MemMonad_run_fresh_provenance ms_init st VALID) as
      [ms_fresh_pr' [pr' [RUN_FRESH' [VALID_FRESH' [MEMORY_FRESH' [PROV_PRESERVED' PROV_FRESH']]]]]].

    rewrite MemMonad_run_bind in ALLOC.
    rewrite RUN_FRESH in ALLOC.
    setoid_rewrite bind_ret_l in ALLOC.

    rename ALLOC into RUN.
    rename ms_fresh_pr into ms'.
    rename MEMORY_FRESH into GET_PR.
    
    { rewrite MemMonad_run_bind in RUN; auto.
      rewrite RUN_FRESH_SID in RUN.
      setoid_rewrite bind_ret_l in RUN.

      rewrite MemMonad_run_bind in RUN.
      rewrite MemMonad_get_mem_state in RUN.
      setoid_rewrite bind_ret_l in RUN.

      destruct ms_init as [ms_stack ms_prov].
      destruct ms_stack as [mem frames heap].

      destruct ms' as [[mem' fs' h'] pr'''].

      cbn in RUN_FRESH.
      repeat rewrite bind_ret_l in RUN_FRESH.
      cbn in RUN_FRESH.
      repeat rewrite bind_ret_l in RUN_FRESH.
      cbn in RUN_FRESH.
      rewrite map_ret in RUN_FRESH.
      pose proof (@eq1_ret_ret (itree Eff) (@ITreeMonad.Eq1_ITree Eff) _ _ (prod store_id (prod MemState _)) _ _ RUN_FRESH) as EQ_RET_FRESH.
      inv EQ_RET_FRESH.

      
      unfold ms_get_memory in GET_PR.
      cbn in GET_PR.
      inv GET_PR.
      cbn in RUN.

      rename mem' into mem.
      rename fs' into frames.
      rename h' into heap.

      cbn in RUN.
      rewrite map_bind in RUN.

      set (next_ptr :=
           (LLVMParamsBigIntptr.ITOP.int_to_ptr
              (next_memory_key
                 {|
                   memory_stack_memory := mem;
                   memory_stack_frame_stack := frames;
                   memory_stack_heap := heap
                 |})
           (LLVMParamsBigIntptr.PROV.allocation_id_to_prov
              (LLVMParamsBigIntptr.PROV.provenance_to_allocation_id (LLVMParamsBigIntptr.PROV.next_provenance ms_prov))))).

      assert (MonadLawsE (MemStateFreshT (itree Eff))) as LAWS by admit.
      assert (Eq1_ret_inv (MemStateFreshT (itree Eff))) as RETINV by admit.
      assert (MonadLawsE (MemPropT MemState)) as LAWS' by admit.
      assert (Eq1_ret_inv (MemPropT MemState)) as RETINV' by admit.
      pose proof @get_consecutive_ptrs_succeeds (MemStateFreshT (itree Eff)) _ _ _ RETINV _ _ LAWS next_ptr (Datatypes.length init_bytes) as (ptrs' & CONSEC').

      unfold eq1 in CONSEC'.
      unfold MonadState.Eq1_stateTM in *.
      unfold pointwise_relation in CONSEC'.
      specialize (CONSEC' st').
      unfold eq1 in CONSEC'.
      specialize (CONSEC' 
              {|
                MemoryBigIntptrInfiniteSpec.MMSP.ms_memory_stack :=
                  {|
                    MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_memory := mem;
                    MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_frame_stack := frames;
                    MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_heap := heap
                  |};
                MemoryBigIntptrInfiniteSpec.MMSP.ms_provenance := LLVMParamsBigIntptr.PROV.next_provenance ms_prov
              |}).
      unfold ITreeMonad.Eq1_ITree in CONSEC'.

      subst next_ptr.
      cbn in CONSEC'.
      rewrite CONSEC' in RUN.

      repeat rewrite bind_ret_l in RUN.
      rewrite map_ret in RUN.
      cbn in RUN.

      pose proof (@eq1_ret_ret (itree Eff) (@ITreeMonad.Eq1_ITree Eff) _ _ (prod store_id (prod MemState addr)) _ _ RUN) as EQ_RET.
      inv EQ_RET.

      pose proof CONSEC as CONSEC''.
      unfold eq1 in CONSEC''.
      unfold MonadState.Eq1_stateTM in *.
      unfold pointwise_relation in CONSEC''.

      setoid_rewrite CONSEC'' in CONSEC'.
      cbn in CONSEC'.
      pose proof (@eq1_ret_ret (itree Eff) (@ITreeMonad.Eq1_ITree Eff) _ _ _ _ _ CONSEC') as EQ_RET.
      inv EQ_RET.
      clear CONSEC''.

      (* SUCCESS *)
      (* Done extracting information from RUN. *)

      rewrite int_to_ptr_provenance in PR.
      (* Done extracting extra info *)

      rename ptrs' into ptrs_alloced.
      destruct ptrs_alloced as [ _ | alloc_addr ptrs] eqn:HALLOC_PTRS.
      { (* Empty ptr list... Not a contradiction, can allocate 0 bytes... MAY not be unique. *)
        assert (init_bytes = []) as INIT_NIL.
        { admit.
        }
        assert (ptrs_alloced = []) as PTRS_NIL.
        { admit.
        }
        subst.
        cbn in *.

        split.
        - (* allocate_bytes_consecutive *)
          cbn.
          repeat eexists.
        - (* allocate_bytes_address_provenance *)
          rewrite int_to_ptr_provenance.
          auto.
        - (* allocate_bytes_addresses_provenance *)
          intros ptr IN.
          inv IN.
        - (* allocate_bytes_provenances_preserved *)
          intros pr'0.
          unfold used_provenance_prop.
          cbn.
          reflexivity.
        - (* allocate_bytes_was_fresh_byte *)
          intros ptr IN.
          inv IN.
        - (* allocate_bytes_now_byte_allocated *)
          intros ptr IN.
          inv IN.
        - (* alloc_bytes_preserves_old_allocations *)
          intros ptr aid NIN.
          reflexivity.
        - (* alloc_bytes_new_reads_allowed *)
          intros ptr IN.
          inv IN.
        - (* alloc_bytes_old_reads_allowed *)
          intros ptr' DISJOINT.
          split; auto.
        - (* alloc_bytes_new_reads *)
          intros p ix byte NTH1 NTH2.
          apply Util.not_Nth_nil in NTH1.
          contradiction.
        - (* alloc_bytes_old_reads *)
          intros ptr' byte DISJOINT.
          split; auto.
        - (* alloc_bytes_new_writes_allowed *)
          intros p IN.
          inv IN.
        - (* alloc_bytes_old_writes_allowed *)
          intros ptr' DISJOINT.
          split; auto.
        - (* alloc_bytes_add_to_frame *)
          intros fs1 fs2 POP ADD.
          cbn in ADD; subst; auto.
          unfold memory_stack_frame_stack_prop in *.
          cbn in *.
          unfold memory_stack_frame_stack.
          cbn.
          setoid_rewrite add_all_to_frame_nil_preserves_frames.
          cbn.
          rewrite POP.
          auto.
        - (* Heap preserved *)
          solve_heap_preserved.
        - (* Non-void *)
          auto.
        - (* Length *)
          cbn; auto.
      }

      (* Non-empty allocation *)
      (* TODO: solve_alloc_bytes_succeeds_spec *)
      split.
      - (* alloc_bytes_consecutive *)
        eapply get_consecutive_MemPropT_MemStateFreshT.
        eapply CONSEC.
        cbn.
        eauto.
      - (* alloc_bytes_address_provenance *)
        apply int_to_ptr_provenance.
      - (* alloc_bytes_addressses_provenance *)
        (* TODO: Need map_monad lemmas *)
        intros ptr IN.
        eapply get_consecutive_ptrs_prov in IN; auto.
        2: {
          eapply get_consecutive_MemPropT_MemStateFreshT.
          apply CONSEC.
        }
        rewrite int_to_ptr_provenance in IN.
        auto.
      - (* alloc_bytes_provenances_preserved *)
        intros pr'0.
        split; eauto.
      - (* alloc_bytes_was_fresh_byte *)
        intros ptr IN.

        (* Bundle this into a byte_not_allocated lemma *)
        Set Nested Proofs Allowed.
        (* TODO: Move these and incorporate into solve_byte_not_allocated *)
        Lemma byte_not_allocated_ge_next_memory_key :
          forall (mem : memory_stack) (ms : MemState) (ptr : addr),
            MemState_get_memory ms = mem ->
            next_memory_key mem <= ptr_to_int ptr ->
            byte_not_allocated ms ptr.
        Proof.
          intros mem ms ptr MEM NEXT.
          unfold byte_not_allocated.
          unfold byte_allocated.
          unfold byte_allocated_MemPropT.
          intros aid CONTRA.
          cbn in CONTRA.
          destruct CONTRA as [ms' [a [CONTRA [EQ1 EQ2]]]]. subst ms' a.
          unfold lift_memory_MemPropT in CONTRA.
          destruct CONTRA as [CONTRA PROV].
          cbn in CONTRA.
          destruct CONTRA as [ms' [mem' [[EQ1 EQ2] CONTRA]]].
          subst.
          rewrite read_byte_raw_next_memory_key in CONTRA.
          - destruct CONTRA as [_ CONTRA]; inv CONTRA.
          - rewrite next_memory_key_next_key_memory_stack_memory in NEXT.
            lia.
        Qed.

        Lemma byte_not_allocated_get_consecutive_ptrs :
          forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
            `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM} `{LAWS : @MonadLawsE M EQM HM}
            (mem : memory_stack) (ms : MemState) (ptr : addr) (len : nat) (ptrs : list addr),
            MemState_get_memory ms = mem ->
            next_memory_key mem <= ptr_to_int ptr ->
            (@get_consecutive_ptrs M HM OOM ERR ptr len ≈ ret ptrs)%monad ->
            forall p, In p ptrs -> byte_not_allocated ms p.
        Proof.
          intros M HM OOM ERR EQM EQV EQRET LAWS mem ms ptr len ptrs MEM NEXT CONSEC p IN.
          eapply get_consecutive_ptrs_ge with (p := p) in CONSEC; eauto.
          eapply byte_not_allocated_ge_next_memory_key; eauto.
          lia.
        Qed.

        eapply byte_not_allocated_get_consecutive_ptrs with
          (ptr :=
             (LLVMParamsBigIntptr.ITOP.int_to_ptr
                (next_memory_key
                   {|
                     MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_memory := mem;
                     MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_frame_stack := frames;
                      MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_heap := heap
                    |})
                 (LLVMParamsBigIntptr.PROV.allocation_id_to_prov
                    (LLVMParamsBigIntptr.PROV.provenance_to_allocation_id
                       (LLVMParamsBigIntptr.PROV.next_provenance ms_prov))))).

        reflexivity.
        cbn. rewrite ptr_to_int_int_to_ptr. reflexivity.
        eapply get_consecutive_MemPropT_MemStateFreshT; eauto.
        auto.
      - (* alloc_bytes_now_byte_allocated *)
        (* TODO: solve_byte_allocated *)
        intros ptr IN.

        Lemma byte_allocated_add_all_index :
          forall (ms : MemState) (mem : memory) (bytes : list mem_byte) (ix : Z) (aid : AllocationId),
            mem_state_memory ms = add_all_index bytes ix mem ->
            (forall mb, In mb bytes -> snd mb = aid) ->
            (forall p, ix <= ptr_to_int p < ix + (Z.of_nat (length bytes)) -> byte_allocated ms p aid).
        Proof.
          intros ms mem bytes ix aid H H0 p H1.
        Admitted.

        Lemma byte_allocated_get_consecutive_ptrs :
          forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
            `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
            `{LAWS : @MonadLawsE M EQM HM}

            (mem : memory) (ms : MemState) (ptr : addr) (len : nat) (ptrs : list addr)
            (bytes : list mem_byte) (aid : AllocationId),
            mem_state_memory ms = add_all_index bytes (ptr_to_int ptr) mem ->
            length bytes = len ->
            (forall mb, In mb bytes -> snd mb = aid) ->
            (@get_consecutive_ptrs M HM OOM ERR ptr len ≈ ret ptrs)%monad ->
            forall p, In p ptrs -> byte_allocated ms p aid.
        Proof.
          intros M HM OOM ERR EQM EQV EQRET LAWS mem ms ptr len ptrs
                 bytes aid MEM LEN AIDS CONSEC p IN.

          eapply byte_allocated_add_all_index; eauto.
          eapply get_consecutive_ptrs_range in CONSEC; eauto.
          lia.
        Qed.

        eapply byte_allocated_get_consecutive_ptrs.
        + unfold mem_state_memory.
          cbn.
          rewrite add_all_to_frame_preserves_memory.
          cbn.
          rewrite ptr_to_int_int_to_ptr.
          reflexivity.
        + rewrite map_length. reflexivity.
        + intros mb INMB.
          apply in_map_iff in INMB as (sb & MBEQ & INSB).
          inv MBEQ.
          cbn. reflexivity.
        + eapply get_consecutive_MemPropT_MemStateFreshT; eauto.
        + auto.
      - (* alloc_bytes_preserves_old_allocations *)
        intros ptr aid DISJOINT.
        (* TODO: not enough for ptr to not be in ptrs list. Must be disjoint.

                     E.g., problem if provenances are different.
         *)

        (* TODO: Move and reuse *)
        Lemma byte_allocated_preserved_get_consecutive_ptrs :
          forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
            `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
            `{LAWS : @MonadLawsE M EQM HM}

            (mem : memory) (ms ms' : MemState) (ptr : addr) (len : nat) (ptrs : list addr)
            (bytes : list mem_byte) (p : addr) (aid : AllocationId),
            mem_state_memory ms = mem ->
            mem_state_memory ms' = add_all_index bytes (ptr_to_int ptr) mem ->
            (@get_consecutive_ptrs M HM OOM ERR ptr len ≈ ret ptrs)%monad ->
            (length bytes = len) ->
            (forall new_p, In new_p ptrs -> disjoint_ptr_byte new_p p) ->
            byte_allocated ms p aid <->
            byte_allocated ms' p aid.
        Proof.
          intros M HM OOM ERR EQM EQV EQRET LAWS mem ms ms' ptr len ptrs
                 bytes p aid MEM1 MEM2 CONSEC BYTELEN DISJOINT.
          unfold mem_state_memory in *.
          split; intros ALLOC.
          - repeat eexists; [| solve_returns_provenance];
              cbn; unfold mem_state_memory; cbn; rewrite MEM2.

            erewrite read_byte_raw_add_all_index_out.
            2: {
              unfold disjoint_ptr_byte in *.
            (* I should know from get_consecutive_ptrs and DISJOINT
               that p can't be in this range.

               I should know that:

               forall ix, ptoi ptr <= ix < ptoi ptr + len, exists new_p, In new_p ptrs.

             *)
              Lemma get_consecutive_ptrs_covers_range :
                forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
                  `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
                  `{LAWS : @MonadLawsE M EQM HM}
                  ptr len ptrs,
                  (@get_consecutive_ptrs M HM OOM ERR ptr len ≈ ret ptrs)%monad ->
                  forall ix, ptr_to_int ptr <= ix < ptr_to_int ptr + (Z.of_nat len) ->
                  exists p', ptr_to_int p' = ix /\ In p' ptrs.
              Proof.
                (* TODO: This is kind of related to get_consecutive_ptrs_nth *)
                intros M HM OOM ERR EQM EQV EQRET LAWS ptr len ptrs CONSEC ix RANGE.
                Transparent get_consecutive_ptrs.
                unfold get_consecutive_ptrs in CONSEC.
                Opaque get_consecutive_ptrs.

                (* Technically this can be more general with inversion lemma for raise_oom *)
                destruct (intptr_seq 0 len) eqn:HSEQ.
                - cbn in *.
                  setoid_rewrite Monad.bind_ret_l in CONSEC.

                  destruct (map_monad
                              (fun ix : LLVMParamsBigIntptr.IP.intptr =>
                                 GEP.handle_gep_addr (DTYPE_I 8) ptr [LLVMParamsBigIntptr.Events.DV.DVALUE_IPTR ix])
                              l) eqn:HMAPM.
                  + cbn in CONSEC.
                    (* TODO: need inversion lemma *)
                    admit.
                  + cbn in CONSEC.
                    apply eq1_ret_ret in CONSEC; eauto.
                    inv CONSEC.

                    pose proof (@exists_in_bounds_le_lt
                                  (ptr_to_int ptr)
                                  (ptr_to_int ptr + Z.of_nat len)
                                  ix) as BOUNDS.

                    forward BOUNDS. lia.
                    destruct BOUNDS as [offset [[BOUNDLE BOUNDLT] EQ]].

                    (* How does ix connect to HSEQ?

                       EQ: ix = ptr_to_int ptr + offset
                       BOUNDLE : 0 <= offset
                       BOUNDLT : offset < Z.of_nat len

                       Then with:

                       HSEQ: intptr_seq 0 len = NoOom l

                       I should know that:

                       exists ip_offset, In ip_offset l /\ from_Z ip_offset = offset

                       (or maybe to_Z ip_offset = NoOom offset)
                     *)
                    pose proof intptr_seq_from_Z 0 len l HSEQ offset as FROMZ.
                    forward FROMZ; [lia|].
                    destruct FROMZ as (ip_offset & FROMZ & INSEQ).

                    eapply map_monad_err_In' with (y := ip_offset) in HMAPM; auto.
                    destruct HMAPM as (p' & GEP & IN).
                    symmetry in GEP.
                    cbn in GEP.
                    apply GEP.handle_gep_addr_ix in GEP.
                    exists p'. split; auto.
                    subst.

                    rewrite sizeof_dtyp_i8 in GEP.
                    erewrite from_Z_to_Z in GEP; [|apply FROMZ].
                    lia.
              Admitted.

              pose proof (get_consecutive_ptrs_covers_range ptr len ptrs CONSEC) as INRANGE.
              subst.
              rewrite <- Zlength_correct in INRANGE.

              pose proof (Z_lt_ge_dec (ptr_to_int p) (ptr_to_int ptr)) as [LTNEXT | GENEXT]; auto.
              pose proof (Z_ge_lt_dec (ptr_to_int p) (ptr_to_int ptr + Zlength bytes)) as [LTNEXT' | GENEXT']; auto.

              specialize (INRANGE (ptr_to_int p)).
              forward INRANGE; [lia|].
              destruct INRANGE as (p' & EQ & INRANGE).
              specialize (DISJOINT p' INRANGE).
              lia.
            }

            break_byte_allocated_in ALLOC.
            cbn in ALLOC.

            break_match; [break_match|]; split; tauto.
          - break_byte_allocated_in ALLOC.
            cbn in ALLOC.

            unfold mem_state_memory in ALLOC; cbn in ALLOC.
            rewrite MEM2 in ALLOC.

            erewrite read_byte_raw_add_all_index_out in ALLOC.
            2: {
              unfold disjoint_ptr_byte in *.

              pose proof (get_consecutive_ptrs_covers_range ptr (Datatypes.length bytes) ptrs CONSEC) as INRANGE.
              subst.
              rewrite <- Zlength_correct in INRANGE.

              pose proof (Z_lt_ge_dec (ptr_to_int p) (ptr_to_int ptr)) as [LTNEXT | GENEXT]; auto.
              pose proof (Z_ge_lt_dec (ptr_to_int p) (ptr_to_int ptr + Zlength bytes)) as [LTNEXT' | GENEXT']; auto.

              specialize (INRANGE (ptr_to_int p)).
              forward INRANGE; [lia|].
              destruct INRANGE as (p' & EQ & INRANGE).
              specialize (DISJOINT p' INRANGE).
              lia.
            }

            repeat eexists; [| solve_returns_provenance].
            cbn.

            break_match; [break_match|]; split; tauto.
        Qed.

        eapply byte_allocated_preserved_get_consecutive_ptrs.
        + reflexivity.
        + cbn.
          unfold mem_state_memory.
          cbn.
          rewrite add_all_to_frame_preserves_memory.
          cbn.
          rewrite ptr_to_int_int_to_ptr.
          reflexivity.
        + eapply get_consecutive_MemPropT_MemStateFreshT; eauto.
        + rewrite map_length. reflexivity.
        + intros new_p IN. auto.
      - (* alloc_bytes_new_reads_allowed *)
        intros p IN.

        (* TODO: move and add to solve_read_byte_allowed *)
        Lemma read_byte_allowed_add_all_index :
          forall (ms : MemState) (mem : memory) (bytes : list mem_byte) (ix : Z) (aid : AllocationId),
            mem_state_memory ms = add_all_index bytes ix mem ->
            (forall mb, In mb bytes -> snd mb = aid) ->
            (forall p,
                ix <= ptr_to_int p < ix + (Z.of_nat (length bytes)) ->
                access_allowed (address_provenance p) aid ->
                read_byte_allowed ms p).
        Proof.
          intros ms mem bytes ix aid MEM AID p IN_BOUNDS ACCESS_ALLOWED.
          unfold read_byte_allowed.
          exists aid. split; auto.
          eapply byte_allocated_add_all_index; eauto.
        Qed.

        eapply read_byte_allowed_add_all_index.
        + unfold mem_state_memory.
          cbn.
          rewrite add_all_to_frame_preserves_memory.
          cbn.
          reflexivity.
        + intros mb INMB.
          apply in_map_iff in INMB as (sb & MB & INSB).
          inv MB.
          cbn.
          reflexivity.
        + rewrite map_length.
          (* True because of CONSEC *)
          assert (Z.of_nat (length init_bytes) > 0) by admit.
          set (next_ptr :=
                 (LLVMParamsBigIntptr.ITOP.int_to_ptr
                    (next_memory_key
                       {|
                         MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_memory := mem;
                         MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_frame_stack := frames;
                         MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_heap := heap
                       |})
                    (LLVMParamsBigIntptr.PROV.allocation_id_to_prov
                       (LLVMParamsBigIntptr.PROV.provenance_to_allocation_id
                          (LLVMParamsBigIntptr.PROV.next_provenance ms_prov))))).
          epose proof (get_consecutive_ptrs_range next_ptr (Datatypes.length init_bytes) (alloc_addr :: ptrs) CONSEC p IN) as INRANGE.
          subst next_ptr.
          rewrite ptr_to_int_int_to_ptr in INRANGE.
          auto.
        + pose proof CONSEC as PROV.
          eapply get_consecutive_ptrs_prov in PROV.
          2: eauto.
          rewrite int_to_ptr_provenance in PROV.
          rewrite PROV.
          apply access_allowed_refl.
      - (* alloc_bytes_old_reads_allowed *)
        intros ptr' DISJOINT.

        (* TODO: Move and reuse *)
        Lemma read_byte_allowed_preserved_get_consecutive_ptrs :
          forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
            `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
            `{LAWS : @MonadLawsE M EQM HM}

            (mem : memory) (ms ms' : MemState) (ptr : addr) (len : nat) (ptrs : list addr)
            (bytes : list mem_byte) (p : addr),
            mem_state_memory ms = mem ->
            mem_state_memory ms' = add_all_index bytes (ptr_to_int ptr) mem ->
            (@get_consecutive_ptrs M HM OOM ERR ptr len ≈ ret ptrs)%monad ->
            (length bytes = len) ->
            (forall new_p, In new_p ptrs -> disjoint_ptr_byte new_p p) ->
            read_byte_allowed ms p <->
              read_byte_allowed ms' p.
        Proof.
          intros M HM OOM ERR EQM EQV EQRET LAWS mem ms ms' ptr len ptrs
                 bytes p MEM1 MEM2 CONSEC BYTELEN DISJOINT.
          split; intros ALLOC.
          - break_read_byte_allowed_hyps.
            eexists; split; eauto.
            eapply byte_allocated_preserved_get_consecutive_ptrs with (ms := ms) (ms' := ms');
              eauto.
          - break_read_byte_allowed_hyps.
            eexists; split; eauto.
            eapply byte_allocated_preserved_get_consecutive_ptrs with (ms := ms) (ms' := ms');
              eauto.
        Qed.

        eapply read_byte_allowed_preserved_get_consecutive_ptrs. 
        + reflexivity.
        + cbn.
          unfold mem_state_memory.
          cbn.
          rewrite add_all_to_frame_preserves_memory.
          cbn.
          rewrite ptr_to_int_int_to_ptr.
          reflexivity.
        + eapply get_consecutive_MemPropT_MemStateFreshT; eauto.
        + rewrite map_length. reflexivity.
        + intros new_p IN. auto.
      - (* alloc_bytes_new_reads *)
        intros p ix byte ADDR BYTE.

        (* TODO: move and add to solve_read_byte_allowed *)
        Lemma read_byte_add_all_index :
          forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
            `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
            `{LAWS : @MonadLawsE M EQM HM}

            (ms : MemState) (mem : memory) (bytes : list mem_byte)
            (byte : SByte) (offset : nat) (aid : AllocationId) p ptr ptrs,

            mem_state_memory ms = add_all_index bytes (ptr_to_int ptr) mem ->
            Util.Nth bytes offset (byte, aid) ->
            (@get_consecutive_ptrs M HM OOM ERR ptr (length bytes) ≈ ret ptrs)%monad ->
            Util.Nth ptrs offset p ->
            access_allowed (address_provenance p) aid ->
            read_byte_prop ms p byte.
        Proof.
          intros M HM OOM ERR EQM EQV EQRET LAWS
                 ms mem bytes byte offset aid p ptr ptrs
                 MEM BYTE CONSEC PTR ACCESS_ALLOWED.

          unfold read_byte_prop, read_byte_MemPropT.
          cbn.
          do 2 eexists; split; auto.

          unfold mem_state_memory in *.
          rewrite MEM.
          erewrite read_byte_raw_add_all_index_in with (v := (byte, aid)).

          { cbn.
            rewrite ACCESS_ALLOWED.
            auto.
          }

          { eapply get_consecutive_ptrs_range with (p:=p) in CONSEC.
            rewrite Zlength_correct.
            lia.
            eapply Nth_In; eauto.
          }

          { eapply get_consecutive_ptrs_nth in CONSEC; eauto.
            destruct CONSEC as (ip_offset & FROMZ & GEP).
            eapply GEP.handle_gep_addr_ix in GEP.
            rewrite sizeof_dtyp_i8 in GEP.
            assert (ptr_to_int p - ptr_to_int ptr = to_Z ip_offset) as EQOFF by lia.
            symmetry in FROMZ; apply from_Z_to_Z in FROMZ.
            rewrite FROMZ in EQOFF.
            rewrite EQOFF.
            eapply Nth_list_nth_z; eauto.
          }
        Qed.

        eapply read_byte_add_all_index.
        + unfold mem_state_memory.
          cbn.
          rewrite add_all_to_frame_preserves_memory.
          cbn.
          rewrite ptr_to_int_int_to_ptr.
          reflexivity.
        + eapply Nth_map; eauto.
        + rewrite map_length.
          eapply get_consecutive_MemPropT_MemStateFreshT; eauto.
        + eauto.
        + pose proof CONSEC as PROV.
          eapply get_consecutive_ptrs_prov in PROV.
          2: eapply Nth_In; eauto.
          rewrite int_to_ptr_provenance in PROV.
          rewrite PROV.
          apply access_allowed_refl.
      - (* alloc_bytes_old_reads *)
        intros ptr' byte DISJOINT.

        (* TODO: Move and reuse *)
        Lemma read_byte_preserved_get_consecutive_ptrs :
          forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
            `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
            `{LAWS : @MonadLawsE M EQM HM}

            (mem : memory) (ms ms' : MemState) (ptr : addr) (len : nat) (ptrs : list addr)
            (bytes : list mem_byte) (p : addr) byte,
            mem_state_memory ms = mem ->
            mem_state_memory ms' = add_all_index bytes (ptr_to_int ptr) mem ->
            (@get_consecutive_ptrs M HM OOM ERR ptr len ≈ ret ptrs)%monad ->
            (length bytes = len) ->
            (forall new_p, In new_p ptrs -> disjoint_ptr_byte new_p p) ->
            read_byte_prop ms p byte <->
              read_byte_prop ms' p byte.
        Proof.
          intros M HM OOM ERR EQM EQV EQRET LAWS mem ms ms' ptr len ptrs
                 bytes p byte MEM1 MEM2 CONSEC BYTELEN DISJOINT.

          unfold mem_state_memory in *.

          split; intros READ.
          - destruct READ as [?ms' [?ms'' [[?EQ1 ?EQ2] READ]]].
            subst ms'0 ms''.
            repeat eexists.
            rewrite MEM2.
            rewrite MEM1 in READ.
            cbn in *.
            erewrite read_byte_raw_add_all_index_out.
            2: {
              pose proof (get_consecutive_ptrs_covers_range ptr len ptrs CONSEC) as INRANGE.
              subst.
              rewrite <- Zlength_correct in INRANGE.

              pose proof (Z_lt_ge_dec (ptr_to_int p) (ptr_to_int ptr)) as [LTNEXT | GENEXT]; auto.
              pose proof (Z_ge_lt_dec (ptr_to_int p) (ptr_to_int ptr + Zlength bytes)) as [LTNEXT' | GENEXT']; auto.

              specialize (INRANGE (ptr_to_int p)).
              forward INRANGE; [lia|].
              destruct INRANGE as (p' & EQ & INRANGE).
              specialize (DISJOINT p' INRANGE).
              unfold disjoint_ptr_byte in DISJOINT.
              lia.
            }

            cbn.
            break_match; [break_match|]; split; tauto.
          - destruct READ as [?ms' [?ms'' [[?EQ1 ?EQ2] READ]]].
            subst ms'0 ms''.
            repeat eexists.
            rewrite MEM2 in READ.
            rewrite MEM1.
            cbn in *.
            erewrite read_byte_raw_add_all_index_out in READ.
            2: {
              pose proof (get_consecutive_ptrs_covers_range ptr len ptrs CONSEC) as INRANGE.
              subst.
              rewrite <- Zlength_correct in INRANGE.

              pose proof (Z_lt_ge_dec (ptr_to_int p) (ptr_to_int ptr)) as [LTNEXT | GENEXT]; auto.
              pose proof (Z_ge_lt_dec (ptr_to_int p) (ptr_to_int ptr + Zlength bytes)) as [LTNEXT' | GENEXT']; auto.

              specialize (INRANGE (ptr_to_int p)).
              forward INRANGE; [lia|].
              destruct INRANGE as (p' & EQ & INRANGE).
              specialize (DISJOINT p' INRANGE).
              unfold disjoint_ptr_byte in DISJOINT.
              lia.
            }

            cbn.
            break_match; [break_match|]; split; tauto.
        Qed.

        eapply read_byte_preserved_get_consecutive_ptrs.
        + reflexivity.
        + cbn.
          unfold mem_state_memory.
          cbn.
          rewrite add_all_to_frame_preserves_memory.
          cbn.
          rewrite ptr_to_int_int_to_ptr.
          reflexivity.
        + eapply get_consecutive_MemPropT_MemStateFreshT; eauto.
        + rewrite map_length. reflexivity.
        + intros new_p IN. auto.
      - (* alloc_bytes_new_writes_allowed *)
        intros p IN.

        (* TODO: move and add to solve_read_byte_allowed *)
        Lemma write_byte_allowed_add_all_index :
          forall (ms : MemState) (mem : memory) (bytes : list mem_byte) (ix : Z) (aid : AllocationId),
            mem_state_memory ms = add_all_index bytes ix mem ->
            (forall mb, In mb bytes -> snd mb = aid) ->
            (forall p,
                ix <= ptr_to_int p < ix + (Z.of_nat (length bytes)) ->
                access_allowed (address_provenance p) aid ->
                write_byte_allowed ms p).
        Proof.
          intros ms mem bytes ix aid MEM AID p IN_BOUNDS ACCESS_ALLOWED.
          unfold read_byte_allowed.
          exists aid. split; auto.
          eapply byte_allocated_add_all_index; eauto.
        Qed.

        eapply write_byte_allowed_add_all_index.
        + unfold mem_state_memory.
          cbn.
          rewrite add_all_to_frame_preserves_memory.
          cbn.
          reflexivity.
        + intros mb INMB.
          apply in_map_iff in INMB as (sb & MB & INSB).
          inv MB.
          cbn.
          reflexivity.
        + rewrite map_length.
          (* True because of CONSEC *)
          assert (Z.of_nat (length init_bytes) > 0) by admit.
          set (next_ptr :=
                 (LLVMParamsBigIntptr.ITOP.int_to_ptr
                    (next_memory_key
                       {|
                         MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_memory := mem;
                         MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_frame_stack := frames;
                         MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_heap := heap
                       |})
                    (LLVMParamsBigIntptr.PROV.allocation_id_to_prov
                       (LLVMParamsBigIntptr.PROV.provenance_to_allocation_id
                          (LLVMParamsBigIntptr.PROV.next_provenance ms_prov))))).
          epose proof (get_consecutive_ptrs_range next_ptr (Datatypes.length init_bytes) (alloc_addr :: ptrs) CONSEC p IN) as INRANGE.
          subst next_ptr.
          rewrite ptr_to_int_int_to_ptr in INRANGE.
          auto.
        + pose proof CONSEC as PROV.
          eapply get_consecutive_ptrs_prov in PROV.
          2: eauto.
          rewrite int_to_ptr_provenance in PROV.
          rewrite PROV.
          apply access_allowed_refl.
      - (* alloc_bytes_old_writes_allowed *)
        intros ptr' DISJOINT.

        (* TODO: Move and reuse *)
        Lemma write_byte_allowed_preserved_get_consecutive_ptrs :
          forall {M} `{HM : Monad M} `{OOM : RAISE_OOM M} `{ERR : RAISE_ERROR M} `{EQM : Eq1 M}
            `{EQV : @Eq1Equivalence M HM EQM} `{EQRET : @Eq1_ret_inv M EQM HM}
            `{LAWS : @MonadLawsE M EQM HM}

            (mem : memory) (ms ms' : MemState) (ptr : addr) (len : nat) (ptrs : list addr)
            (bytes : list mem_byte) (p : addr),
            mem_state_memory ms = mem ->
            mem_state_memory ms' = add_all_index bytes (ptr_to_int ptr) mem ->
            (@get_consecutive_ptrs M HM OOM ERR ptr len ≈ ret ptrs)%monad ->
            (length bytes = len) ->
            (forall new_p, In new_p ptrs -> disjoint_ptr_byte new_p p) ->
            write_byte_allowed ms p <->
              write_byte_allowed ms' p.
        Proof.
          intros M HM OOM ERR EQM EQV EQRET LAWS mem ms ms' ptr len ptrs
                 bytes p MEM1 MEM2 CONSEC BYTELEN DISJOINT.
          split; intros ALLOC.
          - break_write_byte_allowed_hyps.
            eexists; split; eauto.
            eapply byte_allocated_preserved_get_consecutive_ptrs with (ms := ms) (ms' := ms');
              eauto.
          - break_write_byte_allowed_hyps.
            eexists; split; eauto.
            eapply byte_allocated_preserved_get_consecutive_ptrs with (ms := ms) (ms' := ms');
              eauto.
        Qed.

        eapply write_byte_allowed_preserved_get_consecutive_ptrs. 
        + reflexivity.
        + cbn.
          unfold mem_state_memory.
          cbn.
          rewrite add_all_to_frame_preserves_memory.
          cbn.
          rewrite ptr_to_int_int_to_ptr.
          reflexivity.
        + eapply get_consecutive_MemPropT_MemStateFreshT; eauto.
        + rewrite map_length. reflexivity.
        + intros new_p IN. auto.
      - (* Adding to framestack *)
        intros fs1 fs2 OLDFS ADD.
        unfold memory_stack_frame_stack_prop in *.
        cbn in OLDFS; subst.
        cbn.

        rewrite <- map_cons.

        match goal with
        | H: _ |- context [ add_all_to_frame ?ms (map ptr_to_int ?ptrs) ] =>
            pose proof (add_all_to_frame_correct ptrs ms (add_all_to_frame ms (map ptr_to_int ptrs))) as ADDPTRS
        end.

        forward ADDPTRS; [reflexivity|].

        eapply add_ptrs_to_frame_eqv; eauto.
        rewrite <- OLDFS in ADD.
        auto.
      - (* Heap preserved *)
        solve_heap_preserved.
      - (* non-void *)
        auto.
      - (* Length of init bytes matches up *)
        cbn; auto.
  Admitted.

  Lemma allocate_can_always_succeed :
    forall (m1 : MemState) (t : dtyp) (init_bytes : list SByte)
      (BYTES_SIZE : sizeof_dtyp t = N.of_nat (length init_bytes))
      (NON_VOID : t <> DTYPE_Void),
    exists m2 pr ptr ptrs,
      allocate_bytes_succeeds_spec m1 t init_bytes pr m2 ptr ptrs.
  Proof.
    intros m1 t init_bytes BYTES_SIZE NON_VOID.

    remember (@allocate_bytes (MemStateFreshT (itree Eff)) Eff _ _ _ _ _ _ _ _ _ _ _ _ _ t init_bytes) as alloc.

    (* May need a specific initial extra state... *)
    assert store_id as init_store_id.
    admit.

    remember m1 as m.
    destruct m.
    destruct ms_memory_stack0.
    destruct (MMSP.mem_state_fresh_provenance m1) as [p m1'] eqn:FRESH.
    apply mem_state_fresh_provenance_fresh in FRESH as [MEMEQ [PRESERVED_PR FRESH]].    

    set (next_ptr :=
           (LLVMParamsBigIntptr.ITOP.int_to_ptr
              (next_memory_key
                 {|
                   memory_stack_memory := memory_stack_memory0;
                   memory_stack_frame_stack := memory_stack_frame_stack0;
                   memory_stack_heap := memory_stack_heap0
                 |})
(LLVMParamsBigIntptr.PROV.allocation_id_to_prov
              (LLVMParamsBigIntptr.PROV.provenance_to_allocation_id
                 (LLVMParamsBigIntptr.PROV.next_provenance ms_provenance0))))).

    (* (LLVMParamsBigIntptr.PROV.allocation_id_to_prov
                 (LLVMParamsBigIntptr.PROV.provenance_to_allocation_id p)))). *)

    assert (MonadLawsE (MemStateFreshT (itree Eff))) as LAWS by admit.
    assert (Eq1_ret_inv (MemStateFreshT (itree Eff))) as RETINV by admit.
    (* pose proof @get_consecutive_ptrs_succeeds (MemStateFreshT (itree Eff)) _ _ _ RETINV _ _ LAWS next_ptr (Datatypes.length init_bytes) as (ptrs & CONSEC). *)
    assert (MonadLawsE (MemPropT MMSP.MemState)) as LAWS' by admit.
    assert (Eq1_ret_inv (MemPropT MMSP.MemState)) as RETINV' by admit.
    (* pose proof @get_consecutive_ptrs_succeeds (MemPropT MMSP.MemState) _ _ _ RETINV' _ _ LAWS' next_ptr (Datatypes.length init_bytes) as (ptrs & CONSEC). *)
    pose proof @get_consecutive_ptrs_succeeds (MemStateFreshT (itree Eff)) _ _ _ RETINV _ _ LAWS next_ptr (Datatypes.length init_bytes) as (ptrs & CONSEC).

    Opaque get_consecutive_ptrs.

    (* exists ({| *)
    (*     ms_memory_stack := *)
    (*       add_all_to_frame *)
    (*         {| *)
    (*           memory_stack_memory := *)
    (*             add_all_index *)
    (*               (map (fun b : SByte => (b, LLVMParamsBigIntptr.PROV.provenance_to_allocation_id p)) *)
    (*                  init_bytes) *)
    (*               (next_memory_key *)
    (*                  {| *)
    (*                    memory_stack_memory := memory_stack_memory0; *)
    (*                    memory_stack_frame_stack := memory_stack_frame_stack0; *)
    (*                    memory_stack_heap := memory_stack_heap0 *)
    (*                  |}) memory_stack_memory0; *)
    (*           memory_stack_frame_stack := memory_stack_frame_stack0; *)
    (*           memory_stack_heap := memory_stack_heap0 *)
    (*         |} (map LLVMParamsBigIntptr.PTOI.ptr_to_int ptrs); *)
    (*     ms_provenance := MMSP.MemState_get_provenance m1' *)
    (*     |}). *)

    exists ({|
        MemoryBigIntptrInfiniteSpec.MMSP.ms_memory_stack :=
          add_all_to_frame
            {|
              MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_memory :=
                add_all_index
                  (map
                     (fun b : SByte =>
                      (b,
                      LLVMParamsBigIntptr.PROV.provenance_to_allocation_id
                        (LLVMParamsBigIntptr.PROV.next_provenance ms_provenance0))) init_bytes)
                  (next_memory_key
                     {|
                       MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_memory := memory_stack_memory0;
                       MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_frame_stack :=
                         memory_stack_frame_stack0;
                       MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_heap := memory_stack_heap0
                     |}) memory_stack_memory0;
              MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_frame_stack := memory_stack_frame_stack0;
              MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_heap := memory_stack_heap0
            |} (map LLVMParamsBigIntptr.PTOI.ptr_to_int ptrs);
        MemoryBigIntptrInfiniteSpec.MMSP.ms_provenance :=
          LLVMParamsBigIntptr.PROV.next_provenance ms_provenance0
      |}).

    exists (LLVMParamsBigIntptr.PROV.next_provenance ms_provenance0). exists next_ptr. exists ptrs.

    apply allocate_bytes_succeeds_spec_correct with (st := init_store_id) (st' := BinNatDef.N.succ init_store_id).
    { cbn.
      unfold allocate_bytes.
      cbn.

      destruct (dtyp_eq_dec t DTYPE_Void) as [EQ_VOID | ];
        [contradiction |].

      destruct (N.eq_dec (LLVMParamsBigIntptr.SIZEOF.sizeof_dtyp t)
                         (N.of_nat (Datatypes.length init_bytes))) as [EQ_SIZE | NEQ_SIZE];
        [| contradiction].

      setoid_rewrite map_bind.
      repeat rewrite bind_ret_l.
      cbn.
      repeat rewrite bind_ret_l.
      cbn.
      (* break_match. *)
      (* setoid_rewrite map_bind. *)
      (* cbn. *)

      (* set (next_ptr := *)
      (*        (LLVMParamsBigIntptr.ITOP.int_to_ptr *)
      (*           (next_memory_key *)
      (*              {| *)
      (*                memory_stack_memory := memory_stack_memory0; *)
      (*                memory_stack_frame_stack := memory_stack_frame_stack0; *)
      (*                memory_stack_heap := memory_stack_heap0 *)
      (*              |}) *)
      (*           (LLVMParamsBigIntptr.PROV.allocation_id_to_prov *)
      (*              (LLVMParamsBigIntptr.PROV.provenance_to_allocation_id p)))). *)

      rewrite map_bind.

      unfold eq1 in CONSEC.
      unfold MonadState.Eq1_stateTM in *.
      unfold pointwise_relation in CONSEC.
      specialize (CONSEC (BinNatDef.N.succ init_store_id)).
      unfold eq1 in CONSEC.
      specialize (CONSEC {|
          MemoryBigIntptrInfiniteSpec.MMSP.ms_memory_stack :=
            {|
              MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_memory := memory_stack_memory0;
              MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_frame_stack := memory_stack_frame_stack0;
              MemoryBigIntptrInfiniteSpec.MMSP.memory_stack_heap := memory_stack_heap0
            |};
          MemoryBigIntptrInfiniteSpec.MMSP.ms_provenance :=
            LLVMParamsBigIntptr.PROV.next_provenance ms_provenance0
        |}).
      unfold ITreeMonad.Eq1_ITree in CONSEC.
      subst next_ptr.
      setoid_rewrite CONSEC.

      repeat setoid_rewrite bind_ret_l.
      cbn.
      reflexivity.
    }

    { auto.
    }

    { subst next_ptr.
      rewrite int_to_ptr_provenance.
      reflexivity.
    }

    split.
    - apply CONSEC.
      cbn.
      auto.
    - subst next_ptr.
      rewrite int_to_ptr_provenance.
      reflexivity.
    - intros ptr IN.
      admit.
    - intros pr'.
      cbn.
      split; intros USED.
      + subst; eauto.
      + subst; eauto.
        cbn in *.
        admit.
    - intros ptr IN.
      unfold byte_not_allocated.
      intros aid CONTRA.
      (* ptr is larger than anything in original memory *)
      admit.
    - intros ptr IN.
      (* Freshly allocated *)
      admit.
    - intros ptr aid DISJOINT.
      admit.
    - intros p0 IN.
      admit.
    - 




    pose proof allocate_bytes_correct t init_bytes as ALLOC_CORRECT.
    assert (exists sid' ms' alloc_addr, MemStateFreshT_run alloc m1 init_store_id ≈ ret (sid', (ms', alloc_addr))).
    { subst alloc.
      do 3 eexists.
      cbn.
      unfold allocate_bytes.
      cbn.

      destruct (dtyp_eq_dec t DTYPE_Void) as [EQ_VOID | ];
        [contradiction |].

      destruct (N.eq_dec (LLVMParamsBigIntptr.SIZEOF.sizeof_dtyp t)
                         (N.of_nat (Datatypes.length init_bytes))) as [EQ_SIZE | NEQ_SIZE];
        [| contradiction].

      setoid_rewrite map_bind.
      rewrite bind_ret_l.
      cbn.
      break_match.
      repeat rewrite bind_ret_l.
      cbn.
      break_match.
      setoid_rewrite map_bind.
      cbn.

      set (next_ptr :=
           (LLVMParamsBigIntptr.ITOP.int_to_ptr
              (next_memory_key
                 {|
                   memory_stack_memory := memory_stack_memory0;
                   memory_stack_frame_stack := memory_stack_frame_stack0;
                   memory_stack_heap := memory_stack_heap0
                 |})
           (LLVMParamsBigIntptr.PROV.allocation_id_to_prov
              (LLVMParamsBigIntptr.PROV.provenance_to_allocation_id p)))).

      assert (MonadLawsE (MemStateFreshT (itree Eff))) as LAWS by admit.
      assert (Eq1_ret_inv (MemStateFreshT (itree Eff))) as RETINV by admit.
      pose proof @get_consecutive_ptrs_succeeds (MemStateFreshT (itree Eff)) _ _ _ RETINV _ _ LAWS next_ptr (Datatypes.length init_bytes) as (ptrs & CONSEC).

      unfold eq1 in CONSEC.
      unfold MonadState.Eq1_stateTM in *.
      unfold pointwise_relation in CONSEC.
      specialize (CONSEC (BinNatDef.N.succ init_store_id)).
      unfold eq1 in CONSEC.
      specialize (CONSEC m).
      setoid_rewrite CONSEC.

      repeat setoid_rewrite bind_ret_l.
      cbn.
      reflexivity.
    }


  (Ret
     (BinNatDef.N.succ init_store_id,
     ({|
        ms_memory_stack :=
          add_all_to_frame
            {|
              memory_stack_memory :=
                add_all_index
                  (map (fun b : SByte => (b, LLVMParamsBigIntptr.PROV.provenance_to_allocation_id p))
                     init_bytes)
                  (next_memory_key
                     {|
                       memory_stack_memory := memory_stack_memory0;
                       memory_stack_frame_stack := memory_stack_frame_stack0;
                       memory_stack_heap := memory_stack_heap0
                     |}) memory_stack_memory0;
              memory_stack_frame_stack := memory_stack_frame_stack0;
              memory_stack_heap := memory_stack_heap0
            |} (map LLVMParamsBigIntptr.PTOI.ptr_to_int ptrs);
        ms_provenance := MMSP.MemState_get_provenance m
      |}, next_ptr)) ≈ Ret (?sid', (?ms', ?alloc_addr)))%monad


    
    remember (MemStateFreshT_run alloc m1 init_store_id) as run_alloc.
    subst alloc.

    unfold allocate_bytes in *.
    destruct (dtyp_eq_dec t DTYPE_Void) as [EQ_VOID | ];
      [contradiction|].

    destruct (N.eq_dec (LLVMParamsBigIntptr.SIZEOF.sizeof_dtyp t)
                       (N.of_nat (Datatypes.length init_bytes))) as [EQ_SIZE | NEQ_SIZE];
      [| contradiction].

    cbn in *.

    setoid_rewrite bind_ret_l in Heqrun_alloc.

    specialize (alloc init_store_id).


    setoid_rewrite BYTES_SIZE in alloc.
    
    Check alloc.
    MemStateT.

      (* Should run allocate_bytes, which should succeed *)
      (* Ideally we run this in a specialized version of MemM... *)

      (* Going down the allocate_bytes_correct route is just suffering for no reason...

         I end up having to prove allocate_bytes_succeeds_spec anawyay

       *)
      pose proof allocate_bytes_correct t init_bytes as ALLOC_CORRECT.
      unfold exec_correct in *.
      specialize (ALLOC_CORRECT m1 st VALID).
      destruct ALLOC_CORRECT as [UB | ALLOC_CORRECT].
      - (* UB in spec *)
        destruct UB as [ubmsg UB].
        unfold MemSpec.allocate_bytes_spec_MemPropT in *.

        (* Fresh provenance bind in MemPropT *)
        cbn in *.
        destruct UB as [[] | UB].
        destruct UB as [ms_fresh_pr [pr [FRESH_PROV_INVARIANTS UB]]].
        destruct UB as [ALLOC_FAILS_UB | UB].
        + (* Allocation fails, should be bogus because we prove it succeeds... *)
        + 
        
        rewrite MemMonad_run_fresh_provenance in UB.
        unfold MemSpec.allocate_bytes_spec_MemPropT' in .

        cbn in UB.
        
        destruct UB as [sab [pr ].
      destruct UB as [sab [a [BLAH REST]]].
      
      cbn in *.
      (* Allocate bytes will always succeed, just need the right MemM monad to run it... *)
      pose proof @allocate_bytes MemM Eff ExtraState _ _ _ _ _ _ _ _ _ _ _ _ t init_bytes as ALLOC_BYTES.

  (*   epose proof MemoryBigIntptr.MMEP.allocate_bytes. *)
  (*   epose proof (@can_find_fresh_block (MemPropT MemState) (@MemPropT_Monad MemState) (@MemPropT_Eq1 MemState) _ _ _ _ _ m1 (length init_bytes)) as (pr & ptr & ptrs & CONSEC_PTRS & CONSEC_FRESH & PTR_PR & PTRS_PR & UNUSED_PR). *)
  (*   pose proof (big_intptr_seq_succeeds 0 (length init_bytes)) as (ixs & SEQ_ixs). *)

  (*   (* m1 + init_bytes starting at ptr *) *)
  (*   pose proof mem_state_fresh_provenance m1 as (pr' & FRESH_PROV). *)
  (*   set (m *)
  (*   prov <- fresh_provenance;; *)
  (*   set (m2 := initialize_memory m1 ptr pr init_bytes). *)
  (*   exists m2. *)
  (*   exists pr. *)

  (*   exists ptr. exists ptrs. *)

  (*   split. *)
  (*   - (* allocate_bytes_consecutive *) *)
  (*     apply CONSEC_PTRS. *)
  (*     cbn; auto. *)
  (*   - (* allocate_bytes_address_provenance *) *)
  (*     auto. *)
  (*   - (* allocate_bytes_addresses_provenance *) *)
  (*     auto. *)
  (*   - (* allocate_bytes_provenances_preserved *) *)
  (*     intros pr'0. *)
  (*     admit. *)
  (*   - (* allocate_bytes_was_fresh_byte *) *)
  (*     auto. *)
  (*   - (* allocate_bytes_now_byte_allocated *) *)
  (*     admit. *)
  (*   - (* allocate_bytes_preserves_old_allocations *) *)
  (*     admit. *)
  (*   - (* alloc_bytes_new_reads_allowed *) *)
  (*     admit. *)
  (*   - (* alloc_bytes_old_reads_allowed *) *)
  (*     admit. *)
  (*     (* intros ptr' DISJOINT. *)
  (*     split; auto. *) *)
  (*   - (* alloc_bytes_new_reads *) *)
  (*     intros p ix byte NTH1 NTH2. *)
  (*     (* apply Util.not_Nth_nil in NTH1. *) *)
  (*     (* contradiction. *) *)
  (*     admit. *)
  (*   - (* alloc_bytes_old_reads *) *)
  (*     intros ptr' byte DISJOINT. *)
  (*     split; auto. *)
  (*     admit. *)
  (*     admit. *)
  (*   - (* alloc_bytes_new_writes_allowed *) *)
  (*     intros p IN. *)
  (*     admit. *)
  (*     (* inv IN. *) *)
  (*   - (* alloc_bytes_old_writes_allowed *) *)
  (*     intros ptr' DISJOINT. *)
  (*     split; auto. *)
  (*     admit. *)
  (*     admit. *)
  (*   - (* alloc_bytes_add_to_frame *) *)
  (*     (* *)
  (*     intros fs1 fs2 POP ADD. *)
  (*     cbn in ADD; subst; auto. *)
  (*     unfold memory_stack_frame_stack_prop in *. *)
  (*     cbn in *. *)
  (*     unfold memory_stack_frame_stack. *)
  (*     cbn. *)
  (*     setoid_rewrite add_all_to_frame_nil_preserves_frames. *)
  (*     cbn. *)
  (*     rewrite POP. *)
  (*     auto. *) *)
  (*     admit. *)
  (*   - (* Heap preserved *) *)
  (*     admit. *)
  (*     solve_heap_preserved. *)
  (*   - (* Non-void *) *)
  (*     auto. *)
  (*   - (* Length *) *)
  (*     cbn; auto. *)
    (* Qed. *)
  Admitted.
End MemoryBigIntptrInfiniteSpec.
