(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2018 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

(* begin hide *)
From Coq Require Import
     Morphisms ZArith List String Lia
     FSets.FMapAVL
     FSets.FSetAVL
     FSetProperties
     FMapFacts
     Structures.OrderedTypeEx
     micromega.Lia
     Relations
     Wellfounded
     Psatz.

From ITree Require Import
     ITree
     Basics.Basics
     Events.Exception
     Eq.Eq
     Events.StateFacts
     Events.State.

Import Basics.Basics.Monads.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Programming.Eqv
     Data.String
     Data.Monads.EitherMonad
     Data.Monads.IdentityMonad.

From Vellvm Require Import
     Numeric.Coqlib
     Numeric.Integers
     Numeric.Floats
     Utils.Tactics
     Utils.Util
     Utils.Error
     Utils.UBAndErrors
     Utils.ListUtil
     Utils.IntMaps
     Utils.NMaps
     Utils.Monads
     Utils.StateMonads
     Syntax.LLVMAst
     Syntax.DynamicTypes
     Syntax.DataLayout
     Semantics.VellvmIntegers
     Semantics.DynamicValues
     Semantics.Denotation
     Semantics.MemoryAddress
     Semantics.GepM
     Semantics.Memory.Sizeof
     Semantics.Memory.MemBytes
     Semantics.Memory.FiniteProvenance
     Semantics.Memory.ErrSID
     Semantics.Memory.Overlaps
     Semantics.MemoryParams
     Semantics.LLVMEvents
     Semantics.LLVMParams
     Handlers.MemoryModel.

Require Import Ceres.Ceres.

Import IdentityMonad.

Import MonadNotation.
Import EqvNotation.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

#[local] Open Scope Z_scope.
(* end hide *)

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
      true = (@provenance_eq_dec pr pr).
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
    pose proof @provenance_eq_dec p p0.
    destruct H; subst; auto.
    right.
    intros CONTRA. inv CONTRA; contradiction.
    right; intros CONTRA; inv CONTRA.
    right; intros CONTRA; inv CONTRA.
  Qed.

  Lemma aid_eq_dec_refl :
    forall (aid : AllocationId),
      true = @aid_eq_dec aid aid.
  Proof.
    intros aid.
    destruct (@aid_eq_dec aid aid); cbn; auto.
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

(** ** Memory model
    Implementation of the memory model, i.e. a handler for [MemoryE].
    The memory itself, [memory], is a finite map (using the standard library's AVLs)
    indexed on [Z]. 
*)
Module Type FinMemory (LP : LLVMParams) (MP : MemoryParams LP).
  Import MP.
  Import LP.
  Import Events.
  Import DV.
  Import PTOI.
  Import PROV.
  Import ITOP.
  Import SIZEOF.
  Import GEP.
  Import ADDR.
  Import PROV.

  Module BYTE := Byte ADDR IP SIZEOF Events BYTE_IMPL.
  Import BYTE.

  Module ESID := ERRSID ADDR IP SIZEOF PROV.
  Import ESID.

  Module PROV_F := PROV_FUNCS ADDR PROV.
  Import PROV_F.

  Module OVER := PTOIOverlaps ADDR PTOI SIZEOF.
  Export OVER.
  Module OVER_H := OverlapHelpers ADDR SIZEOF OVER.
  Export OVER_H.

  Open Scope list.

  Module SIZEOF_H := Sizeof_helpers SIZEOF.
  Import SIZEOF_H.

  (* Definition endianess : Endianess *)
  (*   := dl_endianess datalayout. *)
  Definition endianess : Endianess
    := ENDIAN_LITTLE.

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
    Definition mem_frame := list Iptr.
    Inductive frame_stack : Type := | Singleton (f : mem_frame) | Snoc (s : frame_stack) (f : mem_frame).
    (* Definition frame_stack := list mem_frame. *)

    (** ** Memory stack
      The full notion of state manipulated by the monad is a pair of a [memory] and a [mem_stack].
     *)
    Definition memory_stack : Type := memory * frame_stack.

  End Datatype_Definition.

  Section Serialization.

   (** ** Serialization
       Conversion back and forth between values and their byte representation
   *)

    (** ** Reading values in memory
      Given an offset in [mem_block], we decode a [uvalue] at [dtyp] [t] by looking up the
      appropriate number of [SByte] and deserializing them.
     *)

  (* Given a little endian list of bytes, match the endianess of `e` *)
  Definition correct_endianess {BYTES : Type} (e : Endianess) (bytes : list BYTES)
    := match e with
       | ENDIAN_BIG => rev bytes
       | ENDIAN_LITTLE => bytes
       end.

  (* Converts an integer [x] to its byte representation over [n] bytes.
     The representation is little endian. In particular, if [n] is too small,
     only the least significant bytes are returned.
   *)
  Fixpoint bytes_of_int_little_endian (n: nat) (x: Z) {struct n}: list byte :=
    match n with
    | O => nil
    | S m => Byte.repr x :: bytes_of_int_little_endian m (x / 256)
    end.

  Definition bytes_of_int (e : Endianess) (n : nat) (x : Z) : list byte :=
    correct_endianess e (bytes_of_int_little_endian n x).

  (*
  Definition sbytes_of_int (e : Endianess) (count:nat) (z:Z) : list SByte :=
    List.map Byte (bytes_of_int e count z). *)

  Definition uvalue_bytes_little_endian (uv :  uvalue) (dt : dtyp) (sid : store_id) : OOM (list uvalue)
    := map_monad (fun n => n' <- IP.from_Z (Z.of_N n);;
                        ret (UVALUE_ExtractByte uv dt (UVALUE_IPTR n') sid)) (Nseq 0 (N.to_nat ptr_size)).

   Definition uvalue_bytes (e : Endianess) (uv :  uvalue) (dt : dtyp) (sid : store_id) : OOM (list uvalue)
      := fmap (correct_endianess e) (uvalue_bytes_little_endian uv dt sid).

    (* TODO: move this *)
    Definition dtyp_eqb (dt1 dt2 : dtyp) : bool
      := match @dtyp_eq_dec dt1 dt2 with
         | left x => true
         | right x => false
         end.

    (* TODO: revive this *)
    (* Definition fp_alignment (bits : N) : option Alignment := *)
    (*   let fp_map := dl_floating_point_alignments datalayout *)
    (*   in NM.find bits fp_map. *)

    (*  TODO: revive this *)
    (* Definition int_alignment (bits : N) : option Alignment := *)
    (*   let int_map := dl_integer_alignments datalayout *)
    (*   in match NM.find bits int_map with *)
    (*      | Some align => Some align *)
    (*      | None => *)
    (*        let keys  := map fst (NM.elements int_map) in *)
    (*        let bits' := nextOrMaximumOpt N.leb bits keys  *)
    (*        in match bits' with *)
    (*           | Some bits => NM.find bits int_map *)
    (*           | None => None *)
    (*           end *)
    (*      end. *)

    (* TODO: Finish this function *)
    (* Fixpoint dtyp_alignment (dt : dtyp) : option Alignment := *)
    (*   match dt with *)
    (*   | DTYPE_I sz => *)
    (*     int_alignment sz *)
    (*   | DTYPE_IPTR => *)
    (*     (* TODO: should these have the same alignments as pointers? *) *)
    (*     int_alignment (N.of_nat ptr_size * 4)%N *)
    (*   | DTYPE_Pointer => *)
    (*     (* TODO: address spaces? *) *)
    (*     Some (ps_alignment (head (dl_pointer_alignments datalayout))) *)
    (*   | DTYPE_Void => *)
    (*     None *)
    (*   | DTYPE_Half => *)
    (*     fp_alignment 16 *)
    (*   | DTYPE_Float => *)
    (*     fp_alignment 32 *)
    (*   | DTYPE_Double => *)
    (*     fp_alignment 64 *)
    (*   | DTYPE_X86_fp80 => *)
    (*     fp_alignment 80 *)
    (*   | DTYPE_Fp128 => *)
    (*     fp_alignment 128 *)
    (*   | DTYPE_Ppc_fp128 => *)
    (*     fp_alignment 128 *)
    (*   | DTYPE_Metadata => *)
    (*     None *)
    (*   | DTYPE_X86_mmx => _ *)
    (*   | DTYPE_Array sz t => *)
    (*     dtyp_alignment t *)
    (*   | DTYPE_Struct fields => _ *)
    (*   | DTYPE_Packed_struct fields => _ *)
    (*   | DTYPE_Opaque => _ *)
    (*   | DTYPE_Vector sz t => _ *)
    (*   end. *)

    Definition dtyp_extract_fields (dt : dtyp) : err (list dtyp)
      := match dt with
         | DTYPE_Struct fields
         | DTYPE_Packed_struct fields =>
           ret fields
         | DTYPE_Array sz t
         | DTYPE_Vector sz t =>
           ret (repeat t (N.to_nat sz))
         | _ => inl "No fields."
         end.

    Definition extract_byte_to_sbyte (uv : uvalue) : ERR SByte
      := match uv with
         | UVALUE_ExtractByte uv dt idx sid =>
           ret (uvalue_sbyte uv dt idx sid)
         | _ => inl (ERR_message "extract_byte_to_ubyte invalid conversion.")
         end.

    Definition sbyte_sid_match (a b : SByte) : bool
      := match sbyte_to_extractbyte a, sbyte_to_extractbyte b with
         | UVALUE_ExtractByte uv dt idx sid, UVALUE_ExtractByte uv' dt' idx' sid' =>
           N.eqb sid sid'
         | _, _ => false
         end.

    Definition replace_sid (sid : store_id) (ub : SByte) : SByte
      := match sbyte_to_extractbyte ub with
         | UVALUE_ExtractByte uv dt idx sid_old =>
           uvalue_sbyte uv dt idx sid
         | _ =>
           ub (* Should not happen... *)
         end.

    Definition filter_sid_matches (byte : SByte) (sbytes : list (N * SByte)) : (list (N * SByte) * list (N * SByte))
      := filter_split (fun '(n, uv) => sbyte_sid_match byte uv) sbytes.

    (* TODO: should I move this? *)
    (* Assign fresh sids to ubytes while preserving entanglement *)
    Program Fixpoint re_sid_ubytes_helper (bytes : list (N * SByte)) (acc : NMap SByte) {measure (length bytes)} : ErrSID (NMap SByte)
      := match bytes with
         | [] => ret acc
         | ((n, x)::xs) =>
           match sbyte_to_extractbyte x with
           | UVALUE_ExtractByte uv dt idx sid =>
             let '(ins, outs) := filter_sid_matches x xs in
             nsid <- fresh_sid;;
             let acc := @NM.add _ n (replace_sid nsid x) acc in
             (* Assign new sid to entangled bytes *)
             let acc := fold_left (fun acc '(n, ub) => @NM.add _ n (replace_sid nsid ub) acc) ins acc in
             re_sid_ubytes_helper outs acc
           | _ => raise_error "re_sid_ubytes_helper: sbyte_to_extractbyte did not yield UVALUE_ExtractByte"
           end
         end.
    Next Obligation.
      cbn.
      symmetry in Heq_anonymous.
      apply filter_split_out_length in Heq_anonymous.
      lia.
    Defined.

    Definition re_sid_ubytes (bytes : list SByte) : ErrSID (list SByte)
      := let len := length bytes in
         byte_map <- re_sid_ubytes_helper (zip (Nseq 0 len) bytes) (@NM.empty _);;
         trywith_error "re_sid_ubytes: missing indices." (NM_find_many (Nseq 0 len) byte_map).

    Definition sigT_of_prod {A B : Type} (p : A * B) : {_ : A & B} :=
      let (a, b) := p in existT (fun _ : A => B) a b.

    Definition uvalue_measure_rel (uv1 uv2 : uvalue) : Prop :=
      (uvalue_measure uv1 < uvalue_measure uv2)%nat.

    Lemma wf_uvalue_measure_rel :
      @well_founded uvalue uvalue_measure_rel.
    Proof.
      unfold uvalue_measure_rel.
      apply wf_inverse_image.
      apply Wf_nat.lt_wf.
    Defined.

    Definition lt_uvalue_dtyp (uvdt1 uvdt2 : (uvalue * dtyp)) : Prop :=
      lexprod uvalue (fun uv => dtyp) uvalue_measure_rel (fun uv dt1f dt2f => dtyp_measure dt1f < dtyp_measure dt2f)%nat (sigT_of_prod uvdt1) (sigT_of_prod uvdt2).

    Lemma wf_lt_uvalue_dtyp : well_founded lt_uvalue_dtyp.
    Proof.
      unfold lt_uvalue_dtyp.
      apply wf_inverse_image.
      apply wf_lexprod.
      - unfold well_founded; intros a.
        exact wf_uvalue_measure_rel.
      - intros uv.
        apply wf_inverse_image.
        apply Wf_nat.lt_wf.
    Defined.

    Definition lex_nats (ns1 ns2 : (nat * nat)) : Prop :=
      lexprod nat (fun n => nat) lt (fun _ => lt) (sigT_of_prod ns1) (sigT_of_prod ns2).

    Lemma well_founded_lex_nats :
      well_founded lex_nats.
    Proof.
      unfold lex_nats.
      apply wf_inverse_image.
      apply wf_lexprod; intros;
      apply Wf_nat.lt_wf.
    Qed.

    (* This is mostly to_ubytes, except it will also unwrap concatbytes *)
  Obligation Tactic := try Tactics.program_simpl; try solve [solve_uvalue_dtyp_measure | intuition; try (inversion H); try (inversion H0)].
  Program Fixpoint serialize_sbytes (uv : uvalue) (dt : dtyp) {measure (uvalue_measure uv, dtyp_measure dt) lex_nats} : ErrSID (list SByte)
    :=
      match uv with
       (* Base types *)
       | UVALUE_Addr _
       | UVALUE_I1 _
       | UVALUE_I8 _
       | UVALUE_I32 _
       | UVALUE_I64 _
       | UVALUE_IPTR _
       | UVALUE_Float _
       | UVALUE_Double _

       (* Expressions *)
       | UVALUE_IBinop _ _ _
       | UVALUE_ICmp _ _ _
       | UVALUE_FBinop _ _ _ _
       | UVALUE_FCmp _ _ _
       | UVALUE_Conversion _ _ _ _
       | UVALUE_GetElementPtr _ _ _
       | UVALUE_ExtractElement _ _
       | UVALUE_InsertElement _ _ _
       | UVALUE_ShuffleVector _ _ _
       | UVALUE_ExtractValue _ _
       | UVALUE_InsertValue _ _ _
       | UVALUE_Select _ _ _ =>
         sid <- fresh_sid;;
         lift_OOM (to_ubytes uv dt sid)

       (* Undef values, these can possibly be aggregates *)
       | UVALUE_Undef _ =>
         match dt with
         | DTYPE_Struct [] =>
           ret []
         | DTYPE_Struct (t::ts) =>
           f_bytes <- serialize_sbytes (UVALUE_Undef t) t;; (* How do I know this is smaller? *)
           fields_bytes <- serialize_sbytes (UVALUE_Undef (DTYPE_Struct ts)) (DTYPE_Struct ts);;
           ret (f_bytes ++ fields_bytes)

         | DTYPE_Packed_struct [] =>
           ret []
         | DTYPE_Packed_struct (t::ts) =>
           f_bytes <- serialize_sbytes (UVALUE_Undef t) t;; (* How do I know this is smaller? *)
           fields_bytes <- serialize_sbytes (UVALUE_Undef (DTYPE_Packed_struct ts)) (DTYPE_Packed_struct ts);;
           ret (f_bytes ++ fields_bytes)

         | DTYPE_Array sz t =>
           field_bytes <- map_monad_In (repeatN sz (UVALUE_Undef t)) (fun elt Hin => serialize_sbytes elt t);;
           ret (concat field_bytes)

         | DTYPE_Vector sz t =>
           field_bytes <- map_monad_In (repeatN sz (UVALUE_Undef t)) (fun elt Hin => serialize_sbytes elt t);;
           ret (concat field_bytes)
         | _ =>
           sid <- fresh_sid;;
           lift_OOM (to_ubytes uv dt sid)
         end

       (* Poison values, possibly aggregates *)
       | UVALUE_Poison _ =>
         match dt with
         | DTYPE_Struct [] =>
           ret []
         | DTYPE_Struct (t::ts) =>
           f_bytes <- serialize_sbytes (UVALUE_Poison t) t;; (* How do I know this is smaller? *)
           fields_bytes <- serialize_sbytes (UVALUE_Poison (DTYPE_Struct ts)) (DTYPE_Struct ts);;
           ret (f_bytes ++ fields_bytes)

         | DTYPE_Packed_struct [] =>
           ret []
         | DTYPE_Packed_struct (t::ts) =>
           f_bytes <- serialize_sbytes (UVALUE_Poison t) t;; (* How do I know this is smaller? *)
           fields_bytes <- serialize_sbytes (UVALUE_Poison (DTYPE_Packed_struct ts)) (DTYPE_Packed_struct ts);;
           ret (f_bytes ++ fields_bytes)

         | DTYPE_Array sz t =>
           field_bytes <- map_monad_In (repeatN sz (UVALUE_Poison t)) (fun elt Hin => serialize_sbytes elt t);;
           ret (concat field_bytes)

         | DTYPE_Vector sz t =>
           field_bytes <- map_monad_In (repeatN sz (UVALUE_Poison t)) (fun elt Hin => serialize_sbytes elt t);;
           ret (concat field_bytes)
         | _ =>
           sid <- fresh_sid;;
           lift_OOM (to_ubytes uv dt sid)
         end

       (* TODO: each field gets a separate store id... Is that sensible? *)
       (* Padded aggregate types *)
       | UVALUE_Struct [] =>
         ret []
       | UVALUE_Struct (f::fields) =>
         (* TODO: take padding into account *)
         match dt with
         | DTYPE_Struct (t::ts) =>
           f_bytes <- serialize_sbytes f t;;
           fields_bytes <- serialize_sbytes (UVALUE_Struct fields) (DTYPE_Struct ts);;
           ret (f_bytes ++ fields_bytes)
         | _ =>
           raise_error "serialize_sbytes: UVALUE_Struct field / type mismatch."
         end

       (* Packed aggregate types *)
       | UVALUE_Packed_struct [] =>
         ret []
       | UVALUE_Packed_struct (f::fields) =>
         (* TODO: take padding into account *)
         match dt with
         | DTYPE_Packed_struct (t::ts) =>
           f_bytes <- serialize_sbytes f t;;
           fields_bytes <- serialize_sbytes (UVALUE_Packed_struct fields) (DTYPE_Packed_struct ts);;
           ret (f_bytes ++ fields_bytes)
         | _ =>
           raise_error "serialize_sbytes: UVALUE_Packed_struct field / type mismatch."
         end

       | UVALUE_Array elts =>
         match dt with
         | DTYPE_Array sz t =>
           field_bytes <- map_monad_In elts (fun elt Hin => serialize_sbytes elt t);;
           ret (concat field_bytes)
         | _ =>
           raise_error "serialize_sbytes: UVALUE_Array with incorrect type."
         end
       | UVALUE_Vector elts =>
         match dt with
         | DTYPE_Vector sz t =>
           field_bytes <- map_monad_In elts (fun elt Hin => serialize_sbytes elt t);;
           ret (concat field_bytes)
         | _ =>
           raise_error "serialize_sbytes: UVALUE_Array with incorrect type."
         end

       | UVALUE_None => ret nil

       (* Byte manipulation. *)
       | UVALUE_ExtractByte uv dt' idx sid =>
         raise_error "serialize_sbytes: UVALUE_ExtractByte not guarded by UVALUE_ConcatBytes."

       | UVALUE_ConcatBytes bytes t =>
         (* TODO: should provide *new* sids... May need to make this function in a fresh sid monad *)
         bytes' <- lift_ERR_RAISE_ERROR (map_monad extract_byte_to_sbyte bytes);;
         re_sid_ubytes bytes'
       end.
  Next Obligation.
    unfold Wf.MR.
    unfold lex_nats.
    apply wf_inverse_image.
    apply wf_lexprod; intros;
      apply Wf_nat.lt_wf.
  Qed.

  Lemma serialize_sbytes_equation : forall (uv : uvalue) (dt : dtyp),
      serialize_sbytes uv dt =
      match uv with
       (* Base types *)
       | UVALUE_Addr _
       | UVALUE_I1 _
       | UVALUE_I8 _
       | UVALUE_I32 _
       | UVALUE_I64 _
       | UVALUE_IPTR _
       | UVALUE_Float _
       | UVALUE_Double _

       (* Expressions *)
       | UVALUE_IBinop _ _ _
       | UVALUE_ICmp _ _ _
       | UVALUE_FBinop _ _ _ _
       | UVALUE_FCmp _ _ _
       | UVALUE_Conversion _ _ _ _
       | UVALUE_GetElementPtr _ _ _
       | UVALUE_ExtractElement _ _
       | UVALUE_InsertElement _ _ _
       | UVALUE_ShuffleVector _ _ _
       | UVALUE_ExtractValue _ _
       | UVALUE_InsertValue _ _ _
       | UVALUE_Select _ _ _ =>
         sid <- fresh_sid;;
         lift_OOM (to_ubytes uv dt sid)

       (* Undef values, these can possibly be aggregates *)
       | UVALUE_Undef _ =>
         match dt with
         | DTYPE_Struct [] =>
           ret []
         | DTYPE_Struct (t::ts) =>
           f_bytes <- serialize_sbytes (UVALUE_Undef t) t;; (* How do I know this is smaller? *)
           fields_bytes <- serialize_sbytes (UVALUE_Undef (DTYPE_Struct ts)) (DTYPE_Struct ts);;
           ret (f_bytes ++ fields_bytes)

         | DTYPE_Packed_struct [] =>
           ret []
         | DTYPE_Packed_struct (t::ts) =>
           f_bytes <- serialize_sbytes (UVALUE_Undef t) t;; (* How do I know this is smaller? *)
           fields_bytes <- serialize_sbytes (UVALUE_Undef (DTYPE_Packed_struct ts)) (DTYPE_Packed_struct ts);;
           ret (f_bytes ++ fields_bytes)

         | DTYPE_Array sz t =>
           field_bytes <- map_monad_In (repeatN sz (UVALUE_Undef t)) (fun elt Hin => serialize_sbytes elt t);;
           ret (concat field_bytes)

         | DTYPE_Vector sz t =>
           field_bytes <- map_monad_In (repeatN sz (UVALUE_Undef t)) (fun elt Hin => serialize_sbytes elt t);;
           ret (concat field_bytes)
         | _ =>
           sid <- fresh_sid;;
           lift_OOM (to_ubytes uv dt sid)
         end

       (* Poison values, possibly aggregates *)
       | UVALUE_Poison _ =>
         match dt with
         | DTYPE_Struct [] =>
           ret []
         | DTYPE_Struct (t::ts) =>
           f_bytes <- serialize_sbytes (UVALUE_Poison t) t;; (* How do I know this is smaller? *)
           fields_bytes <- serialize_sbytes (UVALUE_Poison (DTYPE_Struct ts)) (DTYPE_Struct ts);;
           ret (f_bytes ++ fields_bytes)

         | DTYPE_Packed_struct [] =>
           ret []
         | DTYPE_Packed_struct (t::ts) =>
           f_bytes <- serialize_sbytes (UVALUE_Poison t) t;; (* How do I know this is smaller? *)
           fields_bytes <- serialize_sbytes (UVALUE_Poison (DTYPE_Packed_struct ts)) (DTYPE_Packed_struct ts);;
           ret (f_bytes ++ fields_bytes)

         | DTYPE_Array sz t =>
           field_bytes <- map_monad_In (repeatN sz (UVALUE_Poison t)) (fun elt Hin => serialize_sbytes elt t);;
           ret (concat field_bytes)

         | DTYPE_Vector sz t =>
           field_bytes <- map_monad_In (repeatN sz (UVALUE_Poison t)) (fun elt Hin => serialize_sbytes elt t);;
           ret (concat field_bytes)
         | _ =>
           sid <- fresh_sid;;
           lift_OOM (to_ubytes uv dt sid)
         end

       (* TODO: each field gets a separate store id... Is that sensible? *)
       (* Padded aggregate types *)
       | UVALUE_Struct [] =>
         ret []
       | UVALUE_Struct (f::fields) =>
         (* TODO: take padding into account *)
         match dt with
         | DTYPE_Struct (t::ts) =>
           f_bytes <- serialize_sbytes f t;;
           fields_bytes <- serialize_sbytes (UVALUE_Struct fields) (DTYPE_Struct ts);;
           ret (f_bytes ++ fields_bytes)
         | _ =>
           raise_error "serialize_sbytes: UVALUE_Struct field / type mismatch."
         end

       (* Packed aggregate types *)
       | UVALUE_Packed_struct [] =>
         ret []
       | UVALUE_Packed_struct (f::fields) =>
         (* TODO: take padding into account *)
         match dt with
         | DTYPE_Packed_struct (t::ts) =>
           f_bytes <- serialize_sbytes f t;;
           fields_bytes <- serialize_sbytes (UVALUE_Packed_struct fields) (DTYPE_Packed_struct ts);;
           ret (f_bytes ++ fields_bytes)
         | _ =>
           raise_error "serialize_sbytes: UVALUE_Packed_struct field / type mismatch."
         end

       | UVALUE_Array elts =>
         match dt with
         | DTYPE_Array sz t =>
           field_bytes <- map_monad_In elts (fun elt Hin => serialize_sbytes elt t);;
           ret (concat field_bytes)
         | _ =>
           raise_error "serialize_sbytes: UVALUE_Array with incorrect type."
         end
       | UVALUE_Vector elts =>
         match dt with
         | DTYPE_Vector sz t =>
           field_bytes <- map_monad_In elts (fun elt Hin => serialize_sbytes elt t);;
           ret (concat field_bytes)
         | _ =>
           raise_error "serialize_sbytes: UVALUE_Array with incorrect type."
         end

       | UVALUE_None => ret nil

       (* Byte manipulation. *)
       | UVALUE_ExtractByte uv dt' idx sid =>
         raise_error "serialize_sbytes: UVALUE_ExtractByte not guarded by UVALUE_ConcatBytes."

       | UVALUE_ConcatBytes bytes t =>
         (* TODO: should provide *new* sids... May need to make this function in a fresh sid monad *)
         bytes' <- lift_ERR_RAISE_ERROR (map_monad extract_byte_to_sbyte bytes);;
         re_sid_ubytes bytes'
       end.
  Proof.
    (* intros uv dt. *)
    (* unfold serialize_sbytes. *)
    (* unfold serialize_sbytes_func at 1. *)
    (* rewrite Wf.WfExtensionality.fix_sub_eq_ext. *)
    (* destruct uv. *)
    (* all: try reflexivity. *)
    (* all: cbn. *)
    (* - destruct dt; try reflexivity. *)
    (*   destruct (Datatypes.length fields0 =? Datatypes.length fields)%nat eqn:Hlen. *)
    (*   + cbn. *)
    (*     reflexivity. *)
    (*   + *)


    (* destruct uv; try reflexivity. simpl. *)
    (* destruct dt; try reflexivity. simpl. *)
    (* break_match. *)
    (*  destruct (find (fun a : ident * typ => Ident.eq_dec id (fst a)) env). *)
    (* destruct p; simpl; eauto. *)
    (* reflexivity. *)
  Admitted.

  (* deserialize_sbytes takes a list of SBytes and turns them into a uvalue.

     This relies on the similar, but different, from_ubytes function
     which given a set of bytes checks if all of the bytes are from
     the same uvalue, and if so returns the original uvalue, and
     otherwise returns a UVALUE_ConcatBytes value instead.

     The reason we also have deserialize_sbytes is in order to deal
     with aggregate data types.
   *)
  Obligation Tactic := try Tactics.program_simpl; try solve [solve_dtyp_measure].
  Program Fixpoint deserialize_sbytes (bytes : list SByte) (dt : dtyp) {measure (dtyp_measure dt)} : err uvalue
    :=
      match dt with
       (* TODO: should we bother with this? *)
       (* Array and vector types *)
       | DTYPE_Array sz t =>
         let size := sizeof_dtyp t in
         let size_nat := N.to_nat size in
         fields <- monad_fold_right (fun acc idx => uv <- deserialize_sbytes (between (idx*size) ((idx+1) * size) bytes) t;; ret (uv::acc)) (Nseq 0 size_nat) [];;
         ret (UVALUE_Array fields)

       | DTYPE_Vector sz t =>
         let size := sizeof_dtyp t in
         let size_nat := N.to_nat size in
         fields <- monad_fold_right (fun acc idx => uv <- deserialize_sbytes (between (idx*size) ((idx+1) * size) bytes) t;; ret (uv::acc)) (Nseq 0 size_nat) [];;
         ret (UVALUE_Vector fields)

       (* Padded aggregate types *)
       | DTYPE_Struct fields =>
         (* TODO: Add padding *)
         match fields with
         | [] => ret (UVALUE_Struct []) (* TODO: Not 100% sure about this. *)
         | (dt::dts) =>
           let sz := sizeof_dtyp dt in
           let init_bytes := take sz bytes in
           let rest_bytes := drop sz bytes in
           f <- deserialize_sbytes init_bytes dt;;
           rest <- deserialize_sbytes rest_bytes (DTYPE_Struct dts);;
           match rest with
           | UVALUE_Struct fs =>
             ret (UVALUE_Struct (f::fs))
           | _ =>
             inl "deserialize_sbytes: DTYPE_Struct recursive call did not return a struct."
           end
         end

       (* Structures with no padding *)
       | DTYPE_Packed_struct fields =>
         match fields with
         | [] => ret (UVALUE_Packed_struct []) (* TODO: Not 100% sure about this. *)
         | (dt::dts) =>
           let sz := sizeof_dtyp dt in
           let init_bytes := take sz bytes in
           let rest_bytes := drop sz bytes in
           f <- deserialize_sbytes init_bytes dt;;
           rest <- deserialize_sbytes rest_bytes (DTYPE_Packed_struct dts);;
           match rest with
           | UVALUE_Packed_struct fs =>
             ret (UVALUE_Packed_struct (f::fs))
           | _ =>
             inl "deserialize_sbytes: DTYPE_Struct recursive call did not return a struct."
           end
         end

       (* Base types *)
       | DTYPE_I _
       | DTYPE_IPTR
       | DTYPE_Pointer
       | DTYPE_Half
       | DTYPE_Float
       | DTYPE_Double
       | DTYPE_X86_fp80
       | DTYPE_Fp128
       | DTYPE_Ppc_fp128
       | DTYPE_X86_mmx
       | DTYPE_Opaque
       | DTYPE_Metadata =>
         ret (from_ubytes bytes dt)

       | DTYPE_Void =>
         inl "deserialize_sbytes: Attempt to deserialize void."
      end.

(* (* TODO: *)

(*   What is the difference between a pointer and an integer...? *)

(*   Primarily, it's that pointers have provenance and integers don't? *)

(*   So, if we do PVI is there really any difference between an address *)
(*   and an integer, and should we actually distinguish between them? *)

(*   Provenance in UVALUE_IPTR probably means we need provenance in *all* *)
(*   data types... i1, i8, i32, etc, and even doubles and floats... *)
(*  *) *)

(* (* TODO: *)

(*    Should uvalue have something like... UVALUE_ExtractByte which *)
(*    extracts a certain byte out of a uvalue? *)

(*    Will probably need an equivalence relation on UVALUEs, likely won't *)
(*    end up with a round-trip property with regular equality... *)
(* *) *)

  End Serialization.

  Section Logical_Operations.

    Definition memory_empty : memory := empty.

    (*  TODO: Is DTYPE_Void fine here? *)
    Definition SUndef : ErrSID SByte :=
      sid <- fresh_sid;;
      ret (uvalue_sbyte (UVALUE_Undef DTYPE_Void) DTYPE_Void (UVALUE_IPTR IP.zero) sid).

    (** ** Reading values from memory *)
    Definition read_memory (mem : memory) (address : addr) (t : dtyp) : err uvalue :=
      let addr := ptr_to_int address in
      let pr := address_provenance address in
      match IM_find_many (Zseq addr (N.to_nat (sizeof_dtyp t))) mem with
      | None => failwith "Reading from unallocated memory."
      | Some mem_bytes =>
        let bytes     := map fst mem_bytes in
        let alloc_ids := map snd mem_bytes in
        if all_accesses_allowed pr alloc_ids
        then deserialize_sbytes bytes t
        else failwith ("Read from memory with invalid provenance -- addr: " ++ Show.show addr ++ ", addr prov: " ++ show_prov pr ++ ", memory allocation ids: " ++ Show.show (map show_allocation_id alloc_ids) ++ " memory: " ++ Show.show (map (fun '(key, (_, aid)) => (key, show_allocation_id aid)) (IM.elements mem)))
      end.

    (** ** Writing values to memory
      Serialize [v] into [SByte]s, and store them in the [memory] starting at [addr].

      Also make sure that the write of provenance [pr] is allowed.

      Returns a list of all the AllocationIds for the bytes that would be written in order.
      This is useful for preserving the allocation ids when writing new bytes.
     *)
    Definition write_allowed (mem : memory) (address : addr) (len : nat) : err (list AllocationId)
      :=
        let addr := ptr_to_int address in
        let pr := address_provenance address in
        let mem_bytes := IM_find_many (Zseq addr len) mem in
        match mem_bytes with
        | None => failwith "Trying to write to unallocated memory."
        | Some mem_bytes =>
          let alloc_ids := map snd mem_bytes in
          if all_accesses_allowed pr alloc_ids
          then ret alloc_ids
          else failwith ("Trying to write to memory with invalid provenance -- addr: " ++ Show.show addr ++ ", addr prov: " ++ show_prov pr ++ ", memory allocation ids: " ++ Show.show (map show_allocation_id alloc_ids) ++ " memory: " ++ Show.show (map (fun '(key, (_, aid)) => (key, show_allocation_id aid)) (IM.elements mem)))
        end.

    Definition write_allowed_errsid (mem : memory) (address : addr) (len : nat) : ErrSID (list AllocationId)
      := match write_allowed mem address len with
         | inr aids => ret aids
         | inl ub => raise_ub ub
         end.

    Definition write_memory (mem : memory) (address : addr) (v : uvalue) (dt : dtyp) : ErrSID memory
      :=
        (* Check that we're allowed to write to each place in memory *)
        aids <- write_allowed_errsid mem address (N.to_nat (sizeof_dtyp dt));;
        bytes <- serialize_sbytes v dt;;
        let mem_bytes := zip bytes aids in
        ret (add_all_index mem_bytes (ptr_to_int address) mem).

    (** ** Array element lookup
      A [memory] can be seen as storing an array of elements of [dtyp] [t], from which we retrieve
      the [i]th [uvalue].
      The [size] argument has no effect, but we need to provide one to the array type.
     *)
    Definition get_array_cell_memory (mem : memory) (address : addr) (i : nat) (size : N) (t : dtyp) : ErrSID uvalue :=
      let addr := ptr_to_int address in
      let pr := address_provenance address in
      'offset <- lift_err_RAISE_ERROR
                  (handle_gep_h (DTYPE_Array size t)
                                addr
                                [DVALUE_I64 (DynamicValues.Int64.repr (Z.of_nat i))]);;
      err_to_ub (read_memory mem (int_to_ptr offset pr) t).

    (** ** Array element writing
      Treat a [memory] as though it is an array storing elements of
      type [t], and write the value [v] to index [i] in this array.

      - [t] should be the type of [v].
      - [size] does nothing, but we need to provide one for the array type.
    *)
    Definition write_array_cell_memory (mem : memory) (address : addr) (i : nat) (size : N) (t : dtyp) (v : uvalue) : ErrSID memory :=
      let addr := ptr_to_int address in
      let pr := address_provenance address in
      'offset <- lift_err_RAISE_ERROR
                  (handle_gep_h (DTYPE_Array size t)
                                addr
                                [DVALUE_I64 (DynamicValues.Int64.repr (Z.of_nat i))]);;
      write_memory mem (int_to_ptr offset pr) v t.

    (** ** Array lookups -- mem_block
      Retrieve the values stored at position [from] to position [from + len - 1] in an array stored in a [memory].
     *)
    Definition get_array_memory (mem : memory) (address : addr) (from len : nat) (size : N) (t : dtyp) : ErrSID (list uvalue) :=
      map_monad (fun i => get_array_cell_memory mem address i size t) (seq from len).

    (** ** Array writes -- mem_block
      Write all of the values in [vs] to an array stored in a [memory], starting from index [from].

      - [t] should be the type of each [v] in [vs]
     *)
    Fixpoint write_array_memory' (mem : memory) (address : addr) (i : nat) (size : N) (t : dtyp) (vs : list uvalue) : ErrSID memory :=
      match vs with
      | []       => ret mem
      | (v :: vs) =>
        mem' <- write_array_cell_memory mem address i size t v;;
        write_array_memory' mem' address (S i) size t vs
      end.

    Definition write_array_memory (mem : memory) (address : addr) (from : nat) (t : dtyp) (vs : list uvalue) : ErrSID memory :=
      let size := (N.of_nat (length vs)) in
      write_array_memory' mem address from size t vs.

  End Logical_Operations.


  Section Memory_Operations.

    (** Check if the block for an address is allocated.

        Note: This does not check that the address is in range of the
        block. *)
    (* TODO:2 should this check if everything is in range...? *)
    Definition allocated (a : addr) (m : memory_stack) : Prop :=
      member (ptr_to_int a) (fst m).

      (* LLVM 5.0 memcpy
         According to the documentation: http://releases.llvm.org/5.0.0/docs/LangRef.html#llvm-memcpy-intrinsic
         this operation can never fail?  It doesn't return any status code...
       *)

      (** ** MemCopy
          Implementation of the [memcpy] intrinsics.
       *)
      Definition handle_memcpy (args : list dvalue) (m:memory) : err memory :=
        match args with
        | DVALUE_Addr dst ::
                      DVALUE_Addr src ::
                      DVALUE_I32 len ::
                      DVALUE_I32 align :: (* alignment ignored *)
                      DVALUE_I1 volatile :: [] (* volatile ignored *)  =>

          let src_id := ptr_to_int src in
          let dst_id := ptr_to_int dst in
          let mem_block_size := unsigned len in
          (* From LLVM Docs : The 'llvm.memcpy.*' intrinsics copy a block of *)
      (*        memory from the source location to the destination location, *)
      (*        which are not allowed to overlap. *)
          if (no_overlap dst mem_block_size
                           src mem_block_size) then
            (* Check that everything in src / dst is actually
               allocated, and that provenances match up. *)
            let maybe_sbytes := IM_find_many (Zseq src_id (Z.to_nat mem_block_size)) m in
            let maybe_dbytes := IM_find_many (Zseq dst_id (Z.to_nat mem_block_size)) m in
            match maybe_sbytes, maybe_dbytes with
            | Some sbytes, Some dbytes =>
              let saids := map snd sbytes in
              let daids := map snd dbytes in
              if all_accesses_allowed (address_provenance src) saids && all_accesses_allowed (address_provenance dst) daids
              then
                let mbytes := zip (map fst sbytes) daids in
                ret (add_all_index mbytes dst_id m)
              else failwith "memcpy provenance mismatch."
            | _, _ => failwith "memcpy involving unallocated memory."
            end
          else
            failwith "memcpy has overlapping src and dst memory location"
        | _ => failwith "memcpy got incorrect arguments"
        end.

  End Memory_Operations.

  Section Frame_Stack_Operations.

    (* The initial frame stack is not an empty stack, but a singleton stack containing an empty frame *)
    Definition frame_empty : frame_stack := Singleton [].

    (** ** Free
        [free_frame f m] deallocates the frame [f] from the memory [m].
        This acts on both representations of the memory:
        - on the logical memory, it simply removes all keys indicated by the frame;
        - on the concrete side, for each element of the frame, we lookup in the logical memory
        if it is bounded to a logical block, and if so if this logical block contains an associated
        concrete block. If so, we delete this association from the concrete memory.
     *)
    Definition free_byte
               (b : Iptr)
               (m : memory) : memory
      := delete b m.

    Definition free_frame_memory (f : mem_frame) (m : memory) : memory :=
      fold_left (fun m key => free_byte key m) f m.

    Definition equivs : frame_stack -> frame_stack -> Prop := Logic.eq.

    #[global, refine] Instance equivs_Equiv : Equivalence equivs := _. Defined.

  End Frame_Stack_Operations.

  Section Memory_Stack_Operations.

   (** ** Top-level interface
       Ideally, outside of this module, the [memory_stack] datatype should be abstract and all interactions should go
       through this interface.
    *)

    (** ** The empty memory
        Both the concrete and logical views of the memory are empty maps, i.e. nothing is allocated.
        It is a matter of convention, by we consider the empty memory to contain a single empty frame
        in its stack, rather than an empty stack.
     *)
    Definition empty_memory_stack : memory_stack := (memory_empty, frame_empty).


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

  Definition initial_memory_state : MemState :=
    mkMemState empty_memory_stack 0%N initial_provenance.

  Definition MemStateT M := stateT MemState M.

  Definition mem_state_lift_itree {E A} (t : itree E A) : MemStateT (itree E) A
    := lift t.

  Definition mem_state_raiseUB {E A} `{UBE -< E} (msg : string) : MemStateT (itree E) A
    := mem_state_lift_itree (raiseUB msg).

  Definition mem_state_raiseOOM {E A} `{OOME -< E} (msg : string) : MemStateT (itree E) A
    := mem_state_lift_itree (raiseOOM msg).

  Definition mem_state_raise {E A} `{FailureE -< E} (msg : string) : MemStateT (itree E) A
    := mem_state_lift_itree (raise msg).

  Definition mem_state_lift_err {E} `{FailureE -< E} {A} (e : err A) : MemStateT (itree E) A
    := mem_state_lift_itree (lift_pure_err e).

  Definition mem_state_get_sid {M} `{Monad M} : MemStateT M store_id
    := fmap ms_sid MonadState.get.

  Definition MemState_set_sid (sid : store_id) (ms : MemState) : MemState
    := match ms with
       | mkMemState ms_memory_stack ms_sid ms_prov =>
         mkMemState ms_memory_stack sid ms_prov
       end.

  Definition MemState_set_prov (prov : Provenance) (ms : MemState) : MemState
    := match ms with
       | mkMemState ms_memory_stack ms_sid ms_prov =>
         mkMemState ms_memory_stack ms_sid prov
       end.

  Definition MemState_set_memory_stack (m : memory_stack) (ms : MemState) : MemState
    := match ms with
       | mkMemState ms_memory_stack ms_sid ms_prov =>
         mkMemState m ms_sid ms_prov
       end.

  Definition mem_state_put_sid {M} `{Monad M} (sid : store_id) : MemStateT M unit
    := modify (MemState_set_sid sid);; ret tt.

  Definition mem_state_put_prov {M} `{Monad M} (prov : Provenance) : MemStateT M unit
    := modify (MemState_set_prov prov);; ret tt.

  Definition mem_state_put_memory_stack {M} `{Monad M} (m : memory_stack) : MemStateT M unit
    := modify (MemState_set_memory_stack m);; ret tt.

  Definition mem_state_get_prov {M} `{Monad M} : MemStateT M Provenance
    := fmap ms_prov MonadState.get.

  Definition mem_state_get_memory_stack {M} `{Monad M} : MemStateT M memory_stack
    := fmap ms_memory_stack MonadState.get.

  Definition MemState_modify_memory_stack {M} `{Monad M} (f : memory_stack -> memory_stack) (ms : MemState) : MemState
    := match ms with
       | mkMemState ms_memory_stack ms_sid ms_prov =>
         mkMemState (f ms_memory_stack) ms_sid ms_prov
       end.

  Definition mem_state_modify_memory_stack {M} `{Monad M}
             (f : memory_stack -> memory_stack) : MemStateT M unit
    := modify (MemState_modify_memory_stack f);; ret tt.

  Definition mem_state_lift_ErrSID {E} `{FailureE -< E} `{UBE -< E} `{OOME -< E} {A} (e : ErrSID A) : MemStateT (itree E) A
    :=
      sid <- mem_state_get_sid;;
      pr <-  mem_state_get_prov;;
      match runErrSID e sid pr with
      | (inl (OOM_message msg), sid, pr) =>
          mem_state_raiseOOM msg
      | (inr (inl (UB_message msg)), sid, pr) =>
        mem_state_raiseUB msg
      | (inr (inr (inl (ERR_message msg))), sid, pr) =>
        mem_state_raise msg
      | (inr (inr (inr x)), sid, pr) =>
        mem_state_put_sid sid;;
        mem_state_put_prov pr;;
        ret x
      end.

  Definition mem_state_lift_err_ub_oom {E} `{FailureE -< E} `{UBE -< E} `{OOME -< E} {A} (e : err_ub_oom A) : MemStateT (itree E) A
    := match unIdent (unEitherT (unEitherT (unEitherT (unERR_UB_OOM e)))) with
       | inl (OOM_message oom) => mem_state_raiseOOM oom
       | inr (inl (UB_message ub)) => mem_state_raiseUB ub
       | inr (inr (inl (ERR_message err))) => mem_state_raise err
       | inr (inr (inr x)) => ret x
       end.

    (** ** Fresh key getters *)

    (* Get the next key in the memory *)
    Definition next_memory_key (m : memory_stack) : Z :=
      next_key (fst m).

    (** ** Array lookups -- memory_stack
      Retrieve the values stored at position [from] to position [from + len - 1] in an array stored at address [a] in memory.
     *)
    Definition get_array (m: memory_stack) (a : addr) (from len: nat) (size : N) (t : dtyp) : ErrSID (list uvalue) :=
      get_array_memory (fst m) a from len size t.

    Definition get_array_cell (m : memory_stack) (a : addr) (i : nat) (τ : dtyp) : ErrSID uvalue :=
        get_array_cell_memory (fst m) a i (sizeof_dtyp τ) τ.

    (** ** Array writes -- memory_stack
     *)
    Definition write_array (ms : memory_stack) (a : addr) (from : nat) (τ : dtyp) (vs : list uvalue) : ErrSID memory_stack :=
      let '(m, fs) := ms in
      m' <- write_array_memory m a from τ vs;;
      ret (m', fs)
    .

    Definition write_array_cell (ms : memory_stack) (a : addr) (i : nat) (τ : dtyp) (v : uvalue) : ErrSID memory_stack :=
      let '(m, fs) := ms in
      m' <- write_array_cell_memory m a i 0 τ v;;
      ret (m', fs).

    Definition free_frame (m : memory_stack) : err memory_stack :=
      let '(m,sf) := m in
      match sf with
      | Snoc sf f => inr (free_frame_memory f m,sf)
      | _ => failwith "Ill-form frame-stack: attempting to free when only one frame is in scope"
      end.

    Definition push_fresh_frame (m : memory_stack) : memory_stack :=
      let '(m,s) := m in (m, Snoc s []).

    Definition add_to_frame (m : memory_stack) (k : Z) : memory_stack :=
      let '(m,s) := m in
      match s with
      | Singleton f => (m, Singleton (k :: f))
      | Snoc s f => (m, Snoc s (k :: f))
      end.

    Definition add_all_to_frame (m : memory_stack) (ks : list Z) : memory_stack
      := fold_left (fun ms k => add_to_frame ms k) ks m.

    (* TODO: figure out allocation address *)
    (* Where does this address come from? *)
    (* Should I make sure that the bytes pointed to by this address
       have not been allocated to? *)
    (* x is the starting index for the bytes *)
    Definition allocate_undef_bytes_size (m : memory) (addr : Z) (aid : AllocationId) (sz : N) (x : N) (t :  dtyp) : ErrSID (memory * list Z)
      := (N.recursion
           (fun (x : N) => ret (m, []))
           (fun n mf x =>
              '(m, addrs) <- mf (N.succ x);;
              sid <- fresh_sid;;
              x' <- lift_OOM (IP.from_Z (Z.of_N x));;
              let undef := uvalue_sbyte (UVALUE_Undef t) t (UVALUE_IPTR x') sid in
              let new_addr := addr + Z.of_N x in
              ret (IM.add new_addr (undef, aid) m, (addr::addrs)))
           sz) x.

    Definition allocate_undef_bytes (m : memory) (addr : Z) (aid : AllocationId) (t :  dtyp) : ErrSID (memory * list Z)
      := allocate_undef_bytes_size m addr aid (sizeof_dtyp t) 0%N t.

    (* TODO: make 'addr' nondeterministic, see issue #170 *)
    Definition allocate (ms : memory_stack) (t : dtyp) : ErrSID (memory_stack * addr) :=
      match t with
      | DTYPE_Void => raise_ub "Allocation of type void"
      | _ =>
        let '(m, fs) := ms in
        aid <- fresh_allocation_id;;
        let addr := next_memory_key ms in
        '(m', addrs) <- allocate_undef_bytes m addr aid t;;
        let ms' := add_all_to_frame (m', fs) addrs in
        ret (ms', (int_to_ptr addr (allocation_id_to_prov aid)))
      end.

    Definition read (ms : memory_stack) (ptr : addr) (t : dtyp) : err uvalue :=
      let '(m, fs) := ms in
      read_memory m ptr t.

    Definition write (ms : memory_stack) (ptr : addr) (v : uvalue) (t : dtyp) : ErrSID memory_stack :=
      let '(m, fs) := ms in
      m' <- write_memory m ptr v t;;
      ret (m', fs).

    (* Test whether a given address belong to the current main frame,
       and hence if it will be collected when the current function returns
     *)
    Definition in_frame (a : addr) (m : memory_stack) : Prop :=
      let '(_,s) := m in
      match s with
      | Singleton f | Snoc _ f => In (ptr_to_int a) f
      end.

    Record ext_memory (m1 : memory_stack) (a : addr) (τ : dtyp) (v : uvalue) (m2 : memory_stack) : Prop :=
      {
      (* TODO: might want to extend this so if the size is 0 I know
               what the value of read is... *)
      new_lu  : sizeof_dtyp τ <> 0%N -> read m2 a τ = inr v;
      old_lu  : forall a' τ', allocated a' m1 ->
                         no_overlap_dtyp a τ a' τ' ->
                         read m2 a' τ' = read m1 a' τ'
      }.

    Definition same_reads (m1 m2 : memory_stack) : Prop := forall a τ, read m1 a τ = read m2 a τ.

    Record allocate_spec (m1 : memory_stack) (τ : dtyp) (m2 : memory_stack) (a : addr) : Prop :=
      {
      was_fresh : ~ allocated a m1;
      is_allocated : ext_memory m1 a τ (UVALUE_Undef τ) m2
      }.

    Record write_spec (m1 : memory_stack) (a : addr) (v : dvalue) (m2 : memory_stack) : Prop :=
      {
      was_allocated : allocated a m1;
      is_written    : forall τ, is_supported τ ->
                           dvalue_has_dtyp v τ ->
                           ext_memory m1 a τ (dvalue_to_uvalue v) m2
      }.

    Record read_spec (m : memory_stack) (a : addr) (τ : dtyp) (v : uvalue) : Prop :=
      {
      is_read : read m a τ = inr v
      }.

  End Memory_Stack_Operations.

      Fixpoint uvalue_to_string (u : uvalue) : string
        := match u with
           | UVALUE_Addr a => "UVALUE_Addr"
           | UVALUE_I1 x => "UVALUE_I1"
           | UVALUE_I8 x => "UVALUE_I8"
           | UVALUE_I32 x => "UVALUE_I32"
           | UVALUE_I64 x => "UVALUE_I64"
           | UVALUE_IPTR x => "UVALUE_IPTR"
           | UVALUE_Double x => "UVALUE_Double"
           | UVALUE_Float x => "UVALUE_Float"
           | UVALUE_Undef t => "UVALUE_Undef"
           | UVALUE_Poison t => "UVALUE_Poison"
           | UVALUE_None => "UVALUE_None"
           | UVALUE_Struct fields => "UVALUE_Struct"
           | UVALUE_Packed_struct fields => "UVALUE_Packed_struct"
           | UVALUE_Array elts => "UVALUE_Array"
           | UVALUE_Vector elts => "UVALUE_Vector"
           | UVALUE_IBinop iop v1 v2 => "UVALUE_IBinop"
           | UVALUE_ICmp cmp v1 v2 => "UVALUE_ICmp"
           | UVALUE_FBinop fop fm v1 v2 => "UVALUE_FBinop"
           | UVALUE_FCmp cmp v1 v2 => "UVALUE_FCmp"
           | UVALUE_Conversion conv t_from v t_to => "UVALUE_Conversion"
           | UVALUE_GetElementPtr t ptrval idxs => "UVALUE_GetElementPtr"
           | UVALUE_ExtractElement vec idx => "UVALUE_ExtractElement"
           | UVALUE_InsertElement vec elt idx => "UVALUE_InsertElement"
           | UVALUE_ShuffleVector vec1 vec2 idxmask => "UVALUE_ShuffleVector"
           | UVALUE_ExtractValue vec idxs => "UVALUE_ExtractValue"
           | UVALUE_InsertValue vec elt idxs => "UVALUE_InsertValue"
           | UVALUE_Select cnd v1 v2 => "UVALUE_Select"
           | UVALUE_ExtractByte uv dt idx sid => "UVALUE_ExtractByte " ++ uvalue_to_string uv ++ " typ " ++ uvalue_to_string idx ++ " " ++ Show.show sid
           | UVALUE_ConcatBytes uvs dt => "UVALUE_ConcatBytes " ++ Show.show (map uvalue_to_string uvs)
           end.


  (** ** Memory Handler
      Implementation of the memory model per se as a memory handler to the [MemoryE] interface.
   *)
  Definition handle_memory {E} `{FailureE -< E} `{UBE -< E} `{OOME -< E} 
    : MemoryE ~> MemStateT (itree E) :=
    fun T e =>
      match e with
      | MemPush =>
          mem_state_modify_memory_stack push_fresh_frame

      | MemPop =>
        m <- mem_state_get_memory_stack;;
        'm' <- mem_state_lift_err (free_frame m);;
        mem_state_put_memory_stack m';;
        ret tt

      | Alloca t =>
        m <- mem_state_get_memory_stack;;
        '(m',a) <- mem_state_lift_ErrSID (allocate m t);;
        mem_state_put_memory_stack m';;
        ret (DVALUE_Addr a)

      | Load t dv =>
         match dv with
         | DVALUE_Addr ptr =>
           m <- mem_state_get_memory_stack;;
           match read m ptr t with
           | inr v => ret v
           | inl s => mem_state_raiseUB s
           end
        | _ => mem_state_raise "Attempting to load from a non-address dvalue"
        end

      | Store dt da v =>
        m <- mem_state_get_memory_stack;;
        match da with
        | DVALUE_Addr ptr =>
          'm' <- mem_state_lift_ErrSID (write m ptr v dt);;
          mem_state_put_memory_stack m';;
          ret tt
        | _ => mem_state_raise ("Attempting to store to a non-address dvalue: " ++ (to_string da))
        end

      end.

  Definition handle_intrinsic {E} `{FailureE -< E} `{UBE -< E} : IntrinsicE ~> MemStateT (itree E) :=
    fun T e =>
      match e with
      | Intrinsic t name args =>
        (* Pick all arguments, they should all be unique. *)
        if string_dec name "llvm.memcpy.p0i8.p0i8.i32" then  (* FIXME: use reldec typeclass? *)
          '(m, s) <- mem_state_get_memory_stack;;
          match handle_memcpy args m with
          | inl err => mem_state_raiseUB err
          | inr m' =>
            mem_state_put_memory_stack (m', s);;
            ret DVALUE_None
          end
        else
          mem_state_raise ("Unknown intrinsic: " ++ name)
      end.

  Section PARAMS.
    Variable (E F G : Type -> Type).
    Context `{FailureE -< F} `{UBE -< F} `{OOME -< F}.
    Notation Effin := (E +' IntrinsicE +' MemoryE +' F).
    Notation Effout := (E +' F).

    Definition E_trigger : forall R, E R -> (MemStateT (itree Effout) R) :=
      fun R e => mem_state_lift_itree (trigger e).

    Definition F_trigger : forall R, F R -> (MemStateT (itree Effout) R) :=
      fun R e => mem_state_lift_itree (trigger e).

    Definition interp_memory_h := case_ E_trigger (case_ handle_intrinsic  (case_ handle_memory F_trigger)).

    Definition interp_memory :
      itree Effin ~> MemStateT (itree Effout) :=
      interp_state interp_memory_h.

  End PARAMS.
End FinMemory.

Module Make (LP : LLVMParams) (MP : MemoryParams LP) : FinMemory LP MP.
  Include FinMemory LP MP.
End Make.

Module LLVMParamsBigIntptr := LLVMParams.MakeBig FiniteMemory.Addr FiniteMemory.BigIP FiniteMemory.FinSizeof FiniteMemory.FinPTOI FiniteMemory.FinPROV FiniteMemory.FinITOP BigIP_BIG.

Module LLVMParams64BitIntptr := LLVMParams.Make FiniteMemory.Addr FiniteMemory.IP64Bit FiniteMemory.FinSizeof FiniteMemory.FinPTOI FiniteMemory.FinPROV FiniteMemory.FinITOP.
