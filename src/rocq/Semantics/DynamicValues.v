(* begin hide *)
From Stdlib Require Import
  Relations
  DecidableClass
  Program.Wf
  Numbers.HexadecimalString
  Lists.List. 

Import BinInt.

From Flocq.IEEE754 Require Import
  Bits
  BinarySingleNaN
  Binary.

From ExtLib Require Import
  Core.RelDec
  Programming.Eqv
  Structures.Monads
  Data.Monads.EitherMonad
  Structures.Functor
  Data.Nat
  Data.List.

From Vellvm Require Import
  Numeric
  Utils
  Syntax
  Params
  EOU
  VellvmIntegers.

Import DList.

Require Import Stdlib.Program.Equality.

(* Import EqvNotation. *)
Import Logic.

Open Scope N_scope.
(* end hide *)

(** * Dynamic values
    Definition of the dynamic values manipulated by VIR.

  map_to {X} : (forall (n:N), fin n -> X)


 *)

#[global] Instance Eqv_nat : Eqv nat := (@eq nat).

(* Floating-point rounding mode *)
Definition FT_Rounding:mode := mode_NE.

Definition inttyp (x:N) : Type :=
  match x with
  | 1 => int1
  | 8 => int8
  | 16 => int16
  | 32 => int32
  | 64 => int64
  | _ => False
  end.

(* TODO: This probably should live somewhere else... *)
#[refine]#[local] Instance Decidable_eq_N : forall (x y : N), Decidable (eq x y) := {
    Decidable_witness := N.eqb x y
  }.
apply N.eqb_eq.
Qed.

(* SAZ - TODO make this into typeclasses the way we did with bitint? *)
Definition ll_float  := Floats.float32.
Definition ll_double := Floats.float.

(* Sizeof is needed for for ConcatBytes case *)
Section DValue.
  Context {Pa : Params}.

  Variant memory_bit :=
  | Bit_ptr (p:ptr) (idx : N)  (* idx'th bit of pointer p *)
  | Bit_psn                    (* poison *)
  | Bit_bit (b:@bit_int 1)     (* actual bit *)
  .    
  
  Variant dvalue_base : Set :=
  | DVALUE_Pointer (p:ptr)
  | DVALUE_I (sz : positive) (x:@bit_int sz)
  | DVALUE_Iptr (x:iptr)
    (* TODO - this version | DVALUE_FP (fp:floating_point_variant) (x:@float_val fp) *)
  | DVALUE_Double (x:ll_double)
  | DVALUE_Float (x:ll_float)

  (* DESIGN CHOICE:
     - There is only one canonical representation of poison values.
     - It is a dvalue_base because it has no substructure; even if the type t is structured
   *)                   
  | DVALUE_Poison (t:dtyp)
  | DVALUE_None
    (* Byte type carrier.  Invariant: length bits = sz *)
  | DVALUE_B (sz : positive) (bits : list memory_bit)
  .

  
  (* The set of dynamic values manipulated by an LLVM program. *)
  Unset Elimination Schemes.
  Inductive dvalue : Set :=
  | DVALUE_Base (db : dvalue_base)      
  | DVALUE_Struct (packed:bool) (fields: list dvalue)
  (* REVISIT: DESIGN CHOICE:
     - Array and Vector values carry their "full" dtyp (which includes a length)
   *)                  
  | DVALUE_Array (vector:bool) (t:dtyp) (elts: list dvalue)
  .
  Set Elimination Schemes.


  Coercion DVALUE_Base : dvalue_base >-> dvalue.

  (* Partial coercion in the other direction *)
  Definition dvalue_to_dvalue_base (dv : dvalue) : EOU dvalue_base :=
    match dv with
    | DVALUE_Base d => ret d
    | _ => raise_error "dvalue_to_dvalue_base: got non-base value"
    end.
  
  Definition dtyp_base_of_dvalue_base (v:dvalue_base) : option dtyp_base :=
    match v with
    | DVALUE_Pointer a => Some DTYPE_Pointer
    | DVALUE_I sz x => Some (DTYPE_I sz)
    | DVALUE_Iptr x => Some (DTYPE_Iptr)
    | DVALUE_Double x => Some (DTYPE_FP FP_double)
    | DVALUE_Float x => Some (DTYPE_FP FP_float)
    | DVALUE_Poison t =>
        match t with
        | DTYPE_Base dt => Some dt
        | _ => None
        end
    | DVALUE_None => Some DTYPE_Void
    | DVALUE_B sz bits => Some (DTYPE_B sz)
    end.

  Definition dtyp_of_dvalue_base (v:dvalue_base) : dtyp :=
    match v with
    | DVALUE_Pointer a => DTYPE_Pointer
    | DVALUE_I sz x => (DTYPE_I sz)
    | DVALUE_Iptr x => (DTYPE_Iptr)
    | DVALUE_Double x => (DTYPE_FP FP_double)
    | DVALUE_Float x => (DTYPE_FP FP_float)
    | DVALUE_Poison t => t
    | DVALUE_None =>  DTYPE_Void
    | DVALUE_B sz bits =>  (DTYPE_B sz)
    end.
  
  Fixpoint dtyp_of_dvalue (v:dvalue) : EOU dtyp :=
    match v with
    | DVALUE_Base vb => ret (dtyp_of_dvalue_base vb)
    | DVALUE_Struct p fields =>
        dts <- map_monad dtyp_of_dvalue fields ;;
        ret (DTYPE_Struct p dts)
    | DVALUE_Array p (DTYPE_Array q sz t) elts =>
        if @NO_VOID_dec t
        then
          if forallb (fun e => match dtyp_of_dvalue e with
                            | raise_ret t' => dtyp_eqb t t'
                            | _ => false end) elts
             && N.eqb sz (N.of_nat (length elts))
          then ret (DTYPE_Array p (N.of_nat (length elts)) t)
          else raise_error "dtyp_of_dvalue: mismatched element type in array"
        else raise_error "dtyp_of_dvalue: void in array type"
    | _ => raise_error "dtyp_of_dvalue: missing case"
    end.

  Definition double_to_hex_string (f : float) : string
    := "0x" ++ NilEmpty.string_of_uint (N.to_hex_uint (Z.to_N (unsigned (Float.to_bits f)))).

  Definition float_to_hex_string (f : float32) : string
    := double_to_hex_string (Float32.to_double f).

  #[global] Instance showFloat : Show float
    := {| show := double_to_hex_string |}.

  #[global] Instance showFloat32 : Show float32
    := {| show := float_to_hex_string |}.

  Definition show_memory_bit (mb : memory_bit) : string :=
    match mb with
    | Bit_ptr ptr n => show_ptr ptr ++ "[" ++ show n ++ "]"
    | Bit_psn => "p"
    | Bit_bit i => show (unsigned i)
    end.

  #[global] Instance showMemoryBit : Show memory_bit
    := {| show := show_memory_bit |}.                                          
  
  Definition show_dvalue_base (dv : dvalue_base) : string :=
    match dv with
    | DVALUE_Pointer a => "addr " ++ show_ptr a
    | DVALUE_I sz x => "i" ++ show (Zpos sz) ++ " " ++ show (unsigned x)
    | DVALUE_Iptr x => "intptr " ++ show (to_Z x)
    | DVALUE_Double x => "double " ++ show x
    | DVALUE_Float x => "float " ++ show x
    | DVALUE_Poison t => "poison[" ++ show_dtyp t ++ "]"
    | DVALUE_None => "none"
    | DVALUE_B sz x => "b" ++ show (Zpos sz) ++ "[" ++ show x ++ "]"
    end.      

  #[global] Instance showDvalueBase : Show dvalue_base
    := {| show := show_dvalue_base |}.
  
  Fixpoint show_dvalue (dv : dvalue) : string :=
    match dv with
    | DVALUE_Base db => show db
    | DVALUE_Struct p fields =>
        if p then
          "<{" ++ String.concat ", " (map show_dvalue fields) ++ "}>"
        else "{" ++ String.concat ", " (map show_dvalue fields) ++ "}"
    | DVALUE_Array false t elts => show_dtyp t ++ " [" ++ String.concat ", " (map show_dvalue elts) ++ "]"
    | DVALUE_Array true t elts => show_dtyp t ++ " < " ++ String.concat ", " (map show_dvalue elts) ++ ">"
    end.

  #[global] Instance showDValue : Show dvalue
   := {| show := show_dvalue |}.                                       


  Section DvalueInd.
  (* Induction principles ----------------------------------------------------- *)
    
    Variable P : dvalue -> Prop.
    Hypothesis IH_Base : forall dv, P (DVALUE_Base dv).
    Hypothesis IH_Struct        : forall p (fields: list dvalue) (IH : Forall P fields), P (DVALUE_Struct p fields).
    Hypothesis IH_Array         : forall v t (elts: list dvalue) (IH : Forall P elts), P (DVALUE_Array v t elts).
    Lemma dvalue_ind : forall (dv:dvalue), P dv.
    Proof using All.
      fix IH 1.
      remember P as P0 in IH.
      destruct dv; auto; subst.
      - apply IH_Struct.
        induction fields; eauto.
      - apply IH_Array.
        induction elts; eauto.
    Qed.
  End DvalueInd.

  Section DecidableEquality.

    Lemma memory_bit_eq_dec : forall (b1 b2 : memory_bit), {b1 = b2} + {b1 <> b2}.
    Proof.
      intros b1 b2.
      decide equality; subst.
      - destruct (N.eq_dec idx idx0); subst; auto.
      - destruct (eq_dec_ptr p p0); subst; auto.
      - destruct (Integers.eq_dec b b0); subst; auto.
    Defined.
      
    Lemma dvalue_base_eq_dec : forall (v1 v2 : dvalue_base), {v1 = v2} + {v1 <> v2}.
    Proof.
      intros.
      destruct v1; destruct v2; try solve [right; intros H; inversion H].
      - destruct (eq_dec_ptr p p0); subst; auto. right; intros H; inversion H; contradiction.
      - destruct (Pos.eq_dec sz sz0); subst.
         + destruct (Integers.eq_dec x x0); subst; auto.
           right. intros H; inversion H. subst_existT. contradiction.
         + right. intros H. inversion H. subst_existT. contradiction.
      - destruct (eq_dec_iptr x x0); subst; auto.
        right. intros H. inversion H. subst_existT. contradiction.
      - destruct (Float.eq_dec x x0); subst; auto.
        right. intros H. inversion H. subst_existT. contradiction.
      - destruct (Float32.eq_dec x x0); subst; auto.
        right. intros H. inversion H. subst_existT. contradiction.
      - destruct (dtyp_eq_dec t t0); subst; auto.
        right. intros H. inversion H. subst_existT. contradiction.
      - left; auto.
      -  destruct (Pos.eq_dec sz sz0); subst; auto.
         destruct (list_eq_dec memory_bit_eq_dec bits bits0); subst; auto.
         + right. intros H. inversion H. subst_existT. contradiction.
         + right. intros H. inversion H. subst_existT. contradiction.
    Defined.

    Lemma dvalue_eq_dec : forall (dv1 dv2 : dvalue), {dv1 = dv2} + {dv1 <> dv2}.
    Proof.
      refine (fix f v1 v2 :=
                let lsteq_dec := list_eq_dec f in
                match v1, v2 with
                | DVALUE_Base v1, DVALUE_Base v2 => _
                | DVALUE_Struct p fields, DVALUE_Struct p' fields' => _
                | DVALUE_Array v t elts, DVALUE_Array v' t' elts' => _
                | _, _ => _                                                                   
                end); try (ltac:(dec_dtyp); fail).
      - destruct (dvalue_base_eq_dec v1 v2).
        + left; subst; reflexivity.
        + right; intros H; inversion H. contradiction.
      - destruct (bool_dec p p').
        + destruct (lsteq_dec fields fields').
          * left; subst; reflexivity.
          * right; intros H; inversion H. contradiction.
        + right; intros H; inversion H. contradiction.
      - destruct (bool_dec v v').
        + destruct (dtyp_eq_dec t t').
          * destruct (lsteq_dec elts elts').
            --  left; subst; reflexivity.
            -- right; intros H; inversion H. contradiction.
          * right; intros H; inversion H. contradiction.
        + right; intros H; inversion H. contradiction.            
    Defined.

    Definition dvalue_eqb (dv1 dv2 : dvalue) : bool :=
      if dvalue_eq_dec dv1 dv2 then true else false.
    
    #[global] Instance eq_dec_dvalue : RelDec (@eq dvalue) := RelDec_from_dec (@eq dvalue) (@dvalue_eq_dec).
    #[global] Instance eqv_dvalue : Eqv dvalue := (@eq dvalue).
    Hint Unfold eqv_dvalue : core.
  
    Hint Unfold eqv_dvalue : core.

    Definition dvalue_is_poison (dv : dvalue) : bool :=
      match dv with
      | DVALUE_Base (DVALUE_Poison dt) => true
      | _ => false
      end.
    
    Lemma ibinop_eq_dec : forall (op1 op2:ibinop), {op1 = op2} + {op1 <> op2}.
      intros.
      repeat decide equality.
    Qed.

    Lemma fbinop_eq_dec : forall (op1 op2:fbinop), {op1 = op2} + {op1 <> op2}.
      intros.
      repeat decide equality.
    Qed.

    Lemma icmp_eq_dec : forall (op1 op2:icmp), {op1 = op2} + {op1 <> op2}.
      intros.
      repeat decide equality.
    Qed.

    Lemma fcmp_eq_dec : forall (op1 op2:fcmp), {op1 = op2} + {op1 <> op2}.
      intros.
      repeat decide equality.
    Qed.

    Lemma fast_math_eq_dec : forall (op1 op2:fast_math), {op1 = op2} + {op1 <> op2}.
      intros.
      repeat decide equality.
    Qed.

    Lemma conversion_type_eq_dec : forall (op1 op2:conversion_type), {op1 = op2} + {op1 <> op2}.
      intros.
      repeat decide equality.
    Qed.

    Arguments ibinop_eq_dec: clear implicits.
    Arguments fbinop_eq_dec: clear implicits.
    Arguments icmp_eq_dec: clear implicits.
    Arguments fcmp_eq_dec: clear implicits.
    Arguments fast_math_eq_dec: clear implicits.
    Arguments conversion_type_eq_dec: clear implicits.

    Ltac __abs := right; intros H; inversion H; contradiction.
    Ltac __eq := left; subst; reflexivity.

  End DecidableEquality.

  (* SAZ: Not sure why these are needed *)
  (*
  Definition is_DVALUE_I1 (d:dvalue) : bool :=
    match d with
    | DVALUE_I 1 _ => true
    | _ => false
    end.

  Definition is_DVALUE_I8 (d:dvalue) : bool :=
    match d with
    | DVALUE_I 8 _ => true
    | _ => false
    end.

  Definition is_DVALUE_I16 (d:dvalue) : bool :=
    match d with
    | DVALUE_I 16 _ => true
    | _ => false
    end.

  Definition is_DVALUE_I32 (d:dvalue) : bool :=
    match d with
    | DVALUE_I 32 _ => true
    | _ => false
    end.

  Definition is_DVALUE_I64 (d:dvalue) : bool :=
    match d with
    | DVALUE_I 64 _ => true
    | _ => false
    end.

   *)

  Definition is_DVALUE_IX (d:dvalue_base) : bool :=
    match d with
    | DVALUE_I _ _ => true
    | _ => false
    end.
  
  Class ToDvalueBase I : Type :=
    { tdb : I -> dvalue_base;
    }.

  #[global] Existing Instance VMemInt_iptr. 

  #[global] Instance ToDvalue_iptr : ToDvalueBase iptr :=
    { tdb := DVALUE_Iptr }.

  #[global] Instance ToDvalue_Int `{sz : positive} : ToDvalueBase (@bit_int sz) :=
    { tdb := @DVALUE_I sz }.

  Definition dvalue_base_int_unsigned (dv : dvalue_base) : Z
    := match dv with
       | DVALUE_I sz x => unsigned x
       | DVALUE_Iptr x => to_unsigned x
       | _ => 0
       end.

  (* SAZ: Could consider adding a typeclass to construct poison values from dtyp or dtyp_base *)
  Definition dvp (t : dtyp_base) : dvalue_base := DVALUE_Poison (DTYPE_Base t).
  

  (* Arithmetic Operations ---------------------------------------------------- *)
  Section ARITHMETIC.

    (* Evaluate integer opererations to get a dvalue.

     These operations are between VInts, which are "vellvm"
     integers. This is a typeclass that wraps all of the integer
     operations that we use for integer types with different bitwidths.

     *)

    Definition eval_int_op {Int} `{VMemInt Int} `{ToDvalueBase Int} (iop:ibinop) (x y: Int) : EOU dvalue_base :=
      match iop with
      | Add nuw nsw =>
          if orb (andb nuw (mequ (madd_carry x y mzero) mone))
               (andb nsw (mequ (madd_overflow x y mzero) mone))
          then ret (dvp mdtyp_of_int)
          else tdb <$> madd x y
                         
      | Sub nuw nsw =>
          if orb (andb nuw (mequ (msub_borrow x y mzero) mone))
               (andb nsw (mequ (msub_overflow x y mzero) mone))
          then ret (dvp mdtyp_of_int)
          else tdb <$> (msub x y)
                         
      | Mul nuw nsw => 
          (* I1 mul can't overflow, just based on the 4 possible multiplications. *)
          if (option_pred (fun bw => Pos.eqb bw 1) mbitwidth)
          then tdb <$> (mmul x y)
          else
            res <- mmul x y;;
            
            let res_u' := ((munsigned x) * (munsigned y))%Z in
            let res_s' := ((msigned x) * (msigned y))%Z in

            let min_s_bound := match fmap (fun m => m >? res_s') mmin_signed with
                               | None => false
                               | Some x => x
                               end in
            let max_s_bound := match fmap (fun m => res_s' >? m) mmax_signed with
                               | None => false
                               | Some x => x
                               end in

            if dtyp_base_eq_dec mdtyp_of_int DTYPE_Iptr
            then
              if (res_u' >? munsigned res)
              then raise_oom "Multiplication overflow on iptr."
              else ret (tdb res)
            else
              if orb (andb nuw (res_u' >? munsigned res))
                   (andb nsw (orb min_s_bound max_s_bound))
              then ret (dvp mdtyp_of_int)
              else ret (tdb res)                               
                       
      | Shl nuw nsw =>
          res <- mshl x y;;
          
          let res_u := munsigned res in
          let res_u' := Z.shiftl (munsigned x) (munsigned y) in

          if dtyp_base_eq_dec (@mdtyp_of_int Int _) DTYPE_Iptr
          then
            (* TODO: Do we need to check for the unsigned case? Return result anyway? *)
            if (res_u' >? res_u)
            then raise_oom "Shl unsigned overflow on iptr."
            else
              ret (tdb res)
          else
            (* Unsigned shift x right by bitwidth - y. If shifted x != sign bit * (2^y - 1),
         then there is overflow. *)
            if option_pred (fun bw => munsigned y >=? Zpos bw) mbitwidth
            then ret (dvp mdtyp_of_int)
            else
              
              if andb nuw (res_u' >? res_u)
              then ret (dvp mdtyp_of_int)
              else
                (* Need to separate this out because mnegative can OOM *)
                if nsw
                then
                  match mbitwidth with
                  | None =>
                      ret (tdb res)
                  | Some bw =>
                      (* TODO: should this OOM here? *)
                      nres <- mnegative res;;
                      if (negb (Z.shiftr (munsigned x)
                                  (Zpos bw - munsigned y)
                                =? (munsigned nres)
                                   * (Z.pow 2 (munsigned y) - 1))%Z)
                      then ret (dvp mdtyp_of_int)
                      else ret (tdb res)
                  end
                else ret (tdb res)

      | UDiv ex => 
          if (munsigned y =? 0)%Z
          then raise_ub "Unsigned division by 0."
          else if andb ex (negb ((munsigned x) mod (munsigned y) =? 0))%Z
               then ret (dvp mdtyp_of_int)
               else ret (tdb (mdivu x y))

      | SDiv ex =>
          if dtyp_base_eq_dec mdtyp_of_int DTYPE_Iptr
          then raise_error "Signed division for iptr."
          else
            (* What does signed i1 mean? *)
            if (msigned y =? 0)%Z
            then raise_ub "Signed division by 0."
            else
              if (from_option false (fmap (fun min => min =? msigned x) mmin_signed) && (msigned y =? -1))%Z
              then raise_ub "Signed division overflow."
              else if andb ex (negb ((msigned x) mod (msigned y) =? 0))%Z
                   then ret (dvp mdtyp_of_int)
                   else tdb <$> mdivs x y                      
                                  
      | LShr ex =>
          if option_pred (fun bw => (munsigned y) >=? Zpos bw) mbitwidth && negb (dtyp_base_eqb mdtyp_of_int DTYPE_Iptr)
          then ret (dvp mdtyp_of_int)
          else if andb ex (negb ((munsigned x)
                                   mod (Z.pow 2 (munsigned y)) =? 0))%Z
               then ret (dvp mdtyp_of_int)
               else ret (tdb (mshru x y))
                        
      | AShr ex =>
          if dtyp_base_eq_dec mdtyp_of_int DTYPE_Iptr
          then raise_error "Arithmetic shift for iptr."
          else
            if option_pred (fun bw => (munsigned y) >=? Zpos bw) mbitwidth
            then ret (dvp mdtyp_of_int)
            else if andb ex (negb ((munsigned x)
                                     mod (Z.pow 2 (munsigned y)) =? 0))%Z
                 then ret (dvp mdtyp_of_int)
                 else ret (tdb (mshr x y))
                          
      | URem =>
          if (munsigned y =? 0)%Z
          then raise_ub "Unsigned mod 0."
          else ret (tdb (mmodu x y))

      | SRem =>
          if dtyp_base_eq_dec mdtyp_of_int DTYPE_Iptr
          then raise_error "Signed division for iptr."
          else
            if (msigned y =? 0)%Z
            then raise_ub "Signed mod 0."
            else tdb <$> mmods x y
                           
      | And =>
          ret (tdb (mand x y))

      | Or b =>
          if b then
            (* TODO: disjoint causes poison for non-disjoint `or` inputs
               I've currently implemented the disjointness check by
               seeing whether `or` and `xor` give the same result.  
             *)
            if mequ (mor x y) (mxor x y) then
              ret (tdb (mor x y))
            else ret (dvp mdtyp_of_int)
          else 
            ret (tdb (mor x y))

      | Xor =>
          ret (tdb (mxor x y))
      end.
    Arguments eval_int_op _ _ _ : simpl nomatch.

    (* Evaluate the given iop on the given arguments according to the bitsize *)
    (* TODO: Needed? If not, delete *)
    (* Definition integer_op (bits:positive) (iop:ibinop) (x y:@bit_int bits) : EOU dvalue := *)
    (*   eval_int_op iop x y. *)
    (* Arguments integer_op _ _ _ _ : simpl nomatch. *)

  (* Convert written integer constant to corresponding integer with bitsize bits.
     Takes the integer modulo 2^bits. *)
  Definition coerce_integer_to_int (bits:option positive) (i:Z) : EOU dvalue_base :=
    match bits with
    | Some sz  => ret (@DVALUE_I sz (repr i))
    | None    =>
        i' <- mrepr i;;
        ret (DVALUE_Iptr i')
    end.
  Arguments coerce_integer_to_int _ _ : simpl nomatch.

  (* Integer iop evaluation, called from eval_iop.
     Here the values must be integers. Helper defined
     in order to prevent eval_iop from being recursive. *)
  Definition eval_iop_integer_base (iop : ibinop) (v1 v2 : dvalue_base) : EOU dvalue_base.
    refine
      (match v1, v2 with
       | DVALUE_I sz1 i1, DVALUE_I sz2 i2 =>
           _
       | DVALUE_Iptr i1, DVALUE_Iptr i2 =>
           eval_int_op iop i1 i2
       | DVALUE_Poison t, _             =>
           match iop with
           | SDiv _ =>
               x <- match v2 with
                   | DVALUE_I sz2 i2 =>
                       ret (@Integers.signed sz2 i2)
                   | DVALUE_Iptr i2 =>
                       ret (to_Z i2)
                   | _ => raise_error "ill_typed-iop: sdiv"
                   end;;
               if Z.eq_dec x (-1)
               then raise_ub "Signed division poison overflow"
               else ret (DVALUE_Poison t)
           | _ =>
               ret (DVALUE_Poison t)
           end
       | _, DVALUE_Poison t             =>
           if iop_is_div iop
           then raise_ub "Division by poison."
           else ret (DVALUE_Poison t)
       | _, _                           => raise_error "ill_typed-iop"
       end).
    destruct (Pos.eq_dec sz1 sz2); subst.
    - apply (eval_int_op iop i1 i2).
    - apply (raise_error "ill_typed-iop: integer bitwidth mismatch.").
  Defined.

  (* I split the definition between the vector and other evaluations because
     otherwise eval_iop should be recursive to allow for vector calculations,
     but rocq can't find a fixpoint. *)
  Definition eval_iop iop v1 v2 : EOU dvalue :=
    match v1, v2 with
    | (DVALUE_Base v1), (DVALUE_Base v2) =>
        DVALUE_Base <$> (eval_iop_integer_base iop v1 v2)
                           
    | (DVALUE_Array true t elts1), (DVALUE_Array true _ elts2) =>
        let n := N.length elts1 in
        let m := N.length elts2 in
        if n =? m  then
          elts1' <- map_monad dvalue_to_dvalue_base elts1 ;;
          elts2' <- map_monad dvalue_to_dvalue_base elts2 ;;
          ans <- vec_loop (eval_iop_integer_base iop) (List.combine elts1' elts2') ;;
          ret (DVALUE_Array true t (List.map DVALUE_Base ans))
        else
          raise_ub ("iop: " ++ (show iop) ++  " of different-length vectors")

    | _, _ => raise_error "eval_iop called on illegal dvalue"
    end.
  Arguments eval_iop _ _ _ : simpl nomatch.

  Definition eval_int_icmp {Int} `{VMI : VMemInt Int} (samesign:bool) icmp (x y : Int) : EOU dvalue_base :=
    c <- match icmp with
        | Eq => ret (mcmpu Ceq x y)
        | Ne => ret (mcmpu Cne x y)
        | Ugt => ret (mcmpu Cgt x y)
        | Uge => ret (mcmpu Cge x y)
        | Ult => ret (mcmpu Clt x y)
        | Ule => ret (mcmpu Cle x y)
        | Sgt =>
            if dtyp_base_eq_dec (@mdtyp_of_int Int VMI) DTYPE_Iptr
            then raise_error "Signed '>' comparison on iptr type."
            else ret (mcmp Cgt x y)
        | Sge =>
            if dtyp_base_eq_dec (@mdtyp_of_int Int VMI) DTYPE_Iptr
            then raise_error "Signed '>=' comparison on iptr type."
            else ret (mcmp Cge x y)
        | Slt =>
            if dtyp_base_eq_dec (@mdtyp_of_int Int VMI) DTYPE_Iptr
            then raise_error "Signed '<' comparison on iptr type."
            else ret (mcmp Clt x y)
        | Sle =>
            if dtyp_base_eq_dec (@mdtyp_of_int Int VMI) DTYPE_Iptr
            then raise_error "Signed '>' comparison on iptr type."
            else ret (mcmp Cle x y)
        end;;
    ret ((* Check for sign *)
        if samesign && negb (msamesign x y) then
          (dvp  (DTYPE_I 1))
        else if c
             then @DVALUE_I 1 (Integers.one)
             else @DVALUE_I 1 (Integers.zero)).
  Arguments eval_int_icmp _ _ _ _ : simpl nomatch.

  Definition double_op (fop:fbinop) (v1:ll_double) (v2:ll_double) : EOU dvalue_base :=
    match fop with
    | FAdd => ret (DVALUE_Double (b64_plus FT_Rounding v1 v2))
    | FSub => ret (DVALUE_Double (b64_minus FT_Rounding v1 v2))
    | FMul => ret (DVALUE_Double (b64_mult FT_Rounding v1 v2))
    | FDiv => ret (DVALUE_Double (b64_div FT_Rounding v1 v2))
    | FRem => raise_error "unimplemented double operation"
    end.

  Definition float_op (fop:fbinop) (v1:ll_float) (v2:ll_float) : EOU dvalue_base :=
    match fop with
    | FAdd => ret (DVALUE_Float (b32_plus FT_Rounding v1 v2))
    | FSub => ret (DVALUE_Float (b32_minus FT_Rounding v1 v2))
    | FMul => ret (DVALUE_Float (b32_mult FT_Rounding v1 v2))
    | FDiv => ret (DVALUE_Float (b32_div FT_Rounding v1 v2))
    | FRem => raise_error "unimplemented float operation"
    end.

  Definition eval_fop_base (fop:fbinop) (v1:dvalue_base) (v2:dvalue_base) : EOU dvalue_base :=
    match v1, v2 with
    | DVALUE_Float f1, DVALUE_Float f2   => float_op fop f1 f2
    | DVALUE_Double d1, DVALUE_Double d2 => double_op fop d1 d2
    | DVALUE_Poison t, _                 => ret (DVALUE_Poison t)
    | DVALUE_Float _, DVALUE_Poison t
    | DVALUE_Double _, DVALUE_Poison t
      =>
        if fop_is_div fop
        then raise_ub "Division by poison."
        else ret (DVALUE_Poison t)
    | _, _                               =>
        raise_error ("ill_typed-fop: " ++ (show fop) ++ " " ++ (show v1) ++ " " ++ (show v2))
    end.

  Definition eval_fop (fop:fbinop) (v1:dvalue) (v2:dvalue) : EOU dvalue :=
    match v1, v2 with
    | (DVALUE_Base dv1), (DVALUE_Base dv2) =>
        DVALUE_Base <$> (eval_fop_base fop dv1 dv2)
      
    | (DVALUE_Array true t elts1), (DVALUE_Array true _ elts2) =>
        let n := N.length elts1 in
        let m := N.length elts2 in
        if n =? m  then
          elts1' <- map_monad dvalue_to_dvalue_base elts1 ;;
          elts2' <- map_monad dvalue_to_dvalue_base elts2 ;;
          ans <- vec_loop (eval_fop_base fop) (List.combine elts1' elts2') ;;
          ret (DVALUE_Array true t (List.map DVALUE_Base ans))
        else
        raise_ub ("fop: " ++ (show fop) ++  " different-length vectors of type "
                    ++ (show t) ++ "v1 = " ++ (show v1) ++ "v2 = " ++ (show v2)
          )
    | _, _ => raise_error "eval_fop got illegal value"
    end.
  
  Definition eval_fneg_base (v:dvalue_base) : EOU dvalue_base :=
    match v with
    | DVALUE_Float f  => ret (DVALUE_Float (Float32.neg f))
    | DVALUE_Double f => ret (DVALUE_Double (Float.neg f))
    | DVALUE_Poison t => ret (DVALUE_Poison t)
    | _ => raise_error "ill_typed-fneg "
    end.

  Definition eval_fneg (v:dvalue) : EOU dvalue :=
    match v with
    | DVALUE_Base db =>
        DVALUE_Base <$> (eval_fneg_base db)
                    
    | DVALUE_Array true t elts =>
        elts' <- map_monad dvalue_to_dvalue_base elts ;;        
        ans <- map_monad (eval_fneg_base) elts' ;;
        ret (DVALUE_Array true t (List.map DVALUE_Base ans))
    | _ => raise_error "eval_fneg got illegal value"
    end.
  
  Definition not_nan32 (f:ll_float) : bool :=
    negb (Flocq.IEEE754.Binary.is_nan _ _ f).

  Definition ordered32 (f1 f2:ll_float) : bool :=
    andb (not_nan32 f1) (not_nan32 f2).

  Definition not_nan64 (f:ll_double) : bool :=
    negb (Flocq.IEEE754.Binary.is_nan _ _ f).

  Definition ordered64 (f1 f2:ll_double) : bool :=
    andb (not_nan64 f1) (not_nan64 f2).

  Definition float_cmp (fcmp:fcmp) (x:ll_float) (y:ll_float) : dvalue_base :=
    if match fcmp with
       | FFalse => false
       | FOeq => andb (ordered32 x y) (Float32.cmp Ceq x y)
       | FOgt => andb (ordered32 x y) (Float32.cmp Cgt x y)
       | FOge => andb (ordered32 x y) (Float32.cmp Cge x y)
       | FOlt => andb (ordered32 x y) (Float32.cmp Clt x y)
       | FOle => andb (ordered32 x y) (Float32.cmp Cle x y)
       | FOne => andb (ordered32 x y) (Float32.cmp Cne x y)
       | FOrd => ordered32 x y
       | FUno => negb (ordered32 x y)
       | FUeq => orb (negb (ordered32 x y)) (Float32.cmp Ceq x y)
       | FUgt => orb (negb (ordered32 x y)) (Float32.cmp Cgt x y)
       | FUge => orb (negb (ordered32 x y)) (Float32.cmp Cge x y)
       | FUlt => orb (negb (ordered32 x y)) (Float32.cmp Clt x y)
       | FUle => orb (negb (ordered32 x y)) (Float32.cmp Cle x y)
       | FUne => orb (negb (ordered32 x y)) (Float32.cmp Cne x y)
       | FTrue => true
       end
    then @DVALUE_I 1 Integers.one else @DVALUE_I 1 Integers.zero.
  Arguments float_cmp _ _ _ : simpl nomatch.

  Definition double_cmp (fcmp:fcmp) (x:ll_double) (y:ll_double) : dvalue_base :=
    if match fcmp with
       | FFalse => false
       | FOeq => andb (ordered64 x y) (Float.cmp Ceq x y)
       | FOgt => andb (ordered64 x y) (Float.cmp Cgt x y)
       | FOge => andb (ordered64 x y) (Float.cmp Cge x y)
       | FOlt => andb (ordered64 x y) (Float.cmp Clt x y)
       | FOle => andb (ordered64 x y) (Float.cmp Cle x y)
       | FOne => andb (ordered64 x y) (Float.cmp Cne x y)
       | FOrd => ordered64 x y
       | FUno => negb (ordered64 x y)
       | FUeq => orb (negb (ordered64 x y)) (Float.cmp Ceq x y)
       | FUgt => orb (negb (ordered64 x y)) (Float.cmp Cgt x y)
       | FUge => orb (negb (ordered64 x y)) (Float.cmp Cge x y)
       | FUlt => orb (negb (ordered64 x y)) (Float.cmp Clt x y)
       | FUle => orb (negb (ordered64 x y)) (Float.cmp Cle x y)
       | FUne => orb (negb (ordered64 x y)) (Float.cmp Cne x y)
       | FTrue => true
       end
    then @DVALUE_I 1 Integers.one else @DVALUE_I 1 Integers.zero.
    Arguments double_cmp _ _ _ : simpl nomatch.

  Definition eval_fcmp_base (fcmp:fcmp) (v1:dvalue_base) (v2:dvalue_base) : EOU dvalue_base :=
    match v1, v2 with
    | DVALUE_Float f1, DVALUE_Float f2 => ret (float_cmp fcmp f1 f2)
    | DVALUE_Double f1, DVALUE_Double f2 => ret (double_cmp fcmp f1 f2)
    | DVALUE_Poison t1, DVALUE_Poison t2 => ret (DVALUE_Poison t1)
    | DVALUE_Poison t, DVALUE_Double _ => ret (DVALUE_Poison t)
    | DVALUE_Poison t, DVALUE_Float _ => ret (DVALUE_Poison t)
    | DVALUE_Double _, DVALUE_Poison t => ret (DVALUE_Poison t)
    | DVALUE_Float _, DVALUE_Poison t => ret (DVALUE_Poison t)
    | _, _ => raise_error "ill_typed-fcmp"
    end.

  Definition eval_fcmp (fcmp:fcmp) (v1:dvalue) (v2:dvalue) : EOU dvalue :=
    match v1, v2 with
    | (DVALUE_Base dv1), (DVALUE_Base dv2) =>
        DVALUE_Base <$> (eval_fcmp_base fcmp dv1 dv2)
                    
    | (DVALUE_Array true t elts1), (DVALUE_Array true _ elts2) =>
        let n := N.length elts1 in
        let m := N.length elts2 in
        if n =? m  then
          elts1' <- map_monad dvalue_to_dvalue_base elts1 ;;
          elts2' <- map_monad dvalue_to_dvalue_base elts2 ;;
          ans <- vec_loop (eval_fcmp_base fcmp) (List.combine elts1' elts2') ;;
          ret (DVALUE_Array true (DTYPE_Array true n (DTYPE_I 1)) (List.map DVALUE_Base ans))
        else
          raise_ub "fcmp of different-length vectors"
    | _, _ => raise_error "eval_fcmp got illegal value"
    end.

  End ARITHMETIC.

  (* monadically split a list into a prefix, an element, and a tail

      Should satisfy: [split err pre idx l] = [Some (xs, x, tl)] then (pre ++ l) = (xs ++ [x] ++ tl)
      and ((length pre) + idx) = (length xs)  so if pre = [] then idx = length xs
   *)
  Fixpoint split_h {A} (pre:list A) (idx:Z) (l : list A) : option (list A * A * list A) :=
    match l with
    | [] => None
    | h::tl =>
        (if idx =? 0 then Some (pre, h, tl)
         else split_h (pre ++ [h]) (idx-1) tl)%Z
    end%list.

  Definition split {A} (pre:list A) (idx:Z) (l : list A) : option (list A * A * list A) :=
    if (idx <? 0)%Z then
      None
    else
      split_h pre idx l.
    
  Fixpoint insert_value (str : dvalue) (elt : dvalue) (idxs : list Z) : EOU dvalue :=
    match idxs with
    | [] => ret elt
    | i::tl => 
        match str with
        | DVALUE_Struct p elts =>
            '(pre,sub,post) <- option_ub "insertvalue struct index out of bounds" (split [] i elts) ;;
            modified_subfield <- insert_value sub elt tl ;;
            ret (DVALUE_Struct p (pre ++ [modified_subfield] ++ post)%list)
    
        | DVALUE_Array false t elts =>
            '(pre,sub,post) <- option_ub "insertvalue array index out of bounds" (split [] i elts) ;;
            modified_subfield <- insert_value sub elt tl ;;
            ret (DVALUE_Array false t (pre ++ [modified_subfield] ++ post))

        | DVALUE_Base (DVALUE_Poison (DTYPE_Struct p ts)) =>
            '(pre_t, sub_t, post_t) <- option_ub "insertvalue poison index out of bounds" (split [] i ts) ;;
            let pre_dv := List.map (fun t => DVALUE_Base (DVALUE_Poison t)) pre_t in
            let post_dv := List.map (fun t => DVALUE_Base (DVALUE_Poison t)) post_t in
            modified_subfield <- insert_value (DVALUE_Base (DVALUE_Poison sub_t)) elt tl ;;
            ret (DVALUE_Struct p (pre_dv ++ [modified_subfield] ++ post_dv))
                
        | _ => raise_error "insertvalue: non-aggregate type"
        end
    end.

  Fixpoint extract_value (str : dvalue) (idxs : list Z) : EOU dvalue :=
    match idxs with
    | [] => ret str
    | i::tl => 
        match str with
        | DVALUE_Struct p elts =>
            '(pre,sub,post) <- option_ub "extractvalue struct index out of bounds" (split [] i elts) ;;
            extract_value sub tl 
    
        | DVALUE_Array false t elts =>
            '(pre,sub,post) <- option_ub "extractvalue array index out of bounds" (split [] i elts) ;;
            extract_value sub tl 

        | DVALUE_Base (DVALUE_Poison (DTYPE_Struct p ts)) =>
            '(pre_t, sub_t, post_t) <- option_ub "extractvalue poison index out of bounds" (split [] i ts) ;;
            extract_value (DVALUE_Base (DVALUE_Poison sub_t)) tl 
                
        | _ => raise_error "extractvalue: non-aggregate type"
        end
    end.

  Definition dvalue_to_Z (dv : dvalue) : option Z :=
    match dv with
    (* TODO: should this be restricted to 32 / 64-bit integers? *)      
    | DVALUE_Base (@DVALUE_I sz i2) => Some (signed i2)
    | _ => None
    end.
  
  (* get the idx'th element of a vector, return [poison] if not in bounds. *)
  (* LANGREF? : What is the behavior if [vex] is poison?  UB or return poision?  *)
  Definition extract_element (vec:dvalue) (idx:dvalue) : EOU dvalue :=
    match vec with
    | DVALUE_Array true (DTYPE_Array true _ dt) elts =>
        match dvalue_to_Z idx with
        | Some i =>
            match split [] i elts with
            | None => ret (DVALUE_Base (DVALUE_Poison dt))
            | Some (pre, elt, post) =>  ret elt
            end
        | None => raise_error "extractelemnt: non-integer index"
        end
    | _ => raise_error "extractelement: non-vector type"
    end.

  Definition insert_element (vec : dvalue) (elt : dvalue) (idx : dvalue) : EOU dvalue :=
    match vec with
    | DVALUE_Array true (DTYPE_Array true sz dt) elts =>
        match dvalue_to_Z idx with
        | Some i =>
            match split [] i elts with
            | None => ret (DVALUE_Base (DVALUE_Poison (DTYPE_Array true sz dt)))
            | Some (pre, _, post) =>  ret (DVALUE_Array true (DTYPE_Array true sz dt) (pre ++ [elt] ++ post))
            end
        | None => raise_error "insertelement: non-integer index"
        end
    | DVALUE_Base (DVALUE_Poison (DTYPE_Array true sz dt)) =>
        let elts : list dvalue := repeat (DVALUE_Base (DVALUE_Poison dt)) (N.to_nat sz) in
        match dvalue_to_Z idx with
        | Some i =>
            match split [] i elts with
            | None => ret (DVALUE_Base (DVALUE_Poison (DTYPE_Array true sz dt)))
            | Some (pre, _, post) =>  ret (DVALUE_Array true (DTYPE_Array true sz dt) (pre ++ [elt] ++ post))
            end
        | None => raise_error "insertelement: non-integer index"
        end
    | _ => raise_error ("insertelement: non-vector type " ++ (show vec))%string
    end.

(*  ------------------------------------------------------------------------- *)


  Variant dvalue_base_has_dtyp_base : dvalue_base -> dtyp_base -> Prop :=
  | DVALUE_Pointer_typ   : forall a, dvalue_base_has_dtyp_base (DVALUE_Pointer a) DTYPE_Pointer
  | DVALUE_I_typ      : forall sz x, dvalue_base_has_dtyp_base (@DVALUE_I sz x) (DTYPE_I sz)
  | DVALUE_Iptr_typ   : forall x, dvalue_base_has_dtyp_base (@DVALUE_Iptr x) DTYPE_Iptr
  | DVALUE_Double_typ : forall x, dvalue_base_has_dtyp_base (DVALUE_Double x) (DTYPE_FP FP_double)
  | DVALUE_Float_typ  : forall x, dvalue_base_has_dtyp_base (DVALUE_Float x) (DTYPE_FP FP_float)
  | DVALUE_None_typ   : dvalue_base_has_dtyp_base DVALUE_None DTYPE_Void
  | DVALUE_Poison_typ : forall τ, NO_VOID_base τ -> dvalue_base_has_dtyp_base (DVALUE_Poison (DTYPE_Base τ)) τ
  | DVALUE_B_typ      : forall sz bits, length bits = (Pos.to_nat sz) ->
                                   dvalue_base_has_dtyp_base (@DVALUE_B sz bits) (DTYPE_B sz)
  .
  
  (* Poison not included because of concretize *)
  Unset Elimination Schemes.
  Inductive dvalue_has_dtyp : dvalue -> dtyp -> Prop :=
  | DVALUE_Base_typ :
    forall dv t,
      dvalue_base_has_dtyp_base dv t -> dvalue_has_dtyp (DVALUE_Base dv) (DTYPE_Base t)

  | DVALUE_Poison_typ_agg :
    forall t,
      dvalue_has_dtyp (DVALUE_Base (DVALUE_Poison t)) t
                                                       
  | DVALUE_Struct_typ :
    forall p fields dts,
      List.Forall2 dvalue_has_dtyp fields dts ->
      dvalue_has_dtyp (DVALUE_Struct p fields) (DTYPE_Struct p dts)

  (* Do we have to exclude mmx? "There are no arrays, vectors or constants of this type" *)
  | DVALUE_Array_typ :
    forall v xs sz dt,
      NO_VOID dt ->
      Forall (fun x => dvalue_has_dtyp x dt) xs ->
      length xs = (N.to_nat sz) ->
      dvalue_has_dtyp (DVALUE_Array v (DTYPE_Array v sz dt) xs) (DTYPE_Array v sz dt) 
  .
  Set Elimination Schemes.

  Hint Constructors dvalue_has_dtyp : dvalue.

  Definition default_dvalue_of_dtyp_i (sz : positive) : dvalue_base :=
    @DVALUE_I sz (repr 0).

  Definition default_dvalue_base_of_dtyp_base (dt : dtyp_base) : EOU dvalue_base :=
    match dt with
    | DTYPE_I sz => ret (default_dvalue_of_dtyp_i sz)
    | DTYPE_Iptr => ret (@DVALUE_Iptr zero_iptr)
    | DTYPE_Pointer => ret (DVALUE_Pointer null)
    | DTYPE_Void => raise_error "DTYPE_Void is not a true LLVM value"
    | DTYPE_FP FP_float => ret (DVALUE_Float Float32.zero)
    | DTYPE_FP FP_double => ret (DVALUE_Double (Float32.to_double Float32.zero))
    | DTYPE_FP fp => raise_error ("Unimplemented default type: floating point " ++ show fp)
    | DTYPE_Label => raise_error "Unimplemented default type: label"
    | DTYPE_Token => raise_error "Unimplemented default type: token"                             
    | DTYPE_Metadata => raise_error "Unimplemented default type: metadata"
    | DTYPE_X86_mmx => raise_error "Unimplemented default type: x86_mmx"
    | DTYPE_Opaque => raise_error "Unimplemented default type: opaque"
    | DTYPE_B sz => ret (DVALUE_B sz (repeat (Bit_bit zero) (Pos.to_nat sz)))
    end.
  
  (* Handler for PickE which concretizes everything to 0 *)
  (* If this succeeds the dvalue returned should agree with
     dvalue_has_dtyp for the sake of the dvalue_default lemma. *)
  Fixpoint default_dvalue_of_dtyp (dt : dtyp) : EOU dvalue :=
    match dt with
    | DTYPE_Base dt => DVALUE_Base <$> (default_dvalue_base_of_dtyp_base dt)
    | DTYPE_Struct p fields =>
        v <- map_monad default_dvalue_of_dtyp fields;;
        ret (DVALUE_Struct p v)
    | DTYPE_Array v sz t =>
        dv <- default_dvalue_of_dtyp t ;;
        ret (DVALUE_Array v dt (repeat dv (N.to_nat sz)))
    end.

  Lemma dvalue_default_base_NO_VOID :
    forall t v, default_dvalue_base_of_dtyp_base t = raise_ret v -> NO_VOID_base t.
  Proof.
    destruct t; intros; cbn; auto.
    simpl in H. inversion H.
  Qed.    
    
  Lemma dvalue_default_NO_VOID :
    forall t v, default_dvalue_of_dtyp t = raise_ret v -> NO_VOID t.
  Proof using.
    induction t; intros; cbn; auto.
    -  simpl in H.
       destruct (default_dvalue_base_of_dtyp_base t) eqn:HEQ; inversion H.
       eapply dvalue_default_base_NO_VOID. eapply HEQ.
    - cbn in H0.
      break_match_hyp_inv.
      rewrite FORALL_forall.
      rewrite Forall_forall.
      intros.
      edestruct map_monad_EOU_success; eauto.
    - cbn in H.
      break_match_hyp_inv.
      eapply IHt. reflexivity.
  Qed.
  
End DValue.

Arguments DVALUE_I {Pa} sz.
#[global] Hint Constructors dvalue_has_dtyp : dvalue.
#[global] Hint Resolve forall_repeat_true : DVALUE_HAS_DTYP.
#[global] Hint Constructors dvalue_has_dtyp : DVALUE_HAS_DTYP.
#[global] Hint Rewrite Nnat.Nat2N.id : DVALUE_HAS_DTYP.
#[global] Hint Resolve List.repeat_length : DVALUE_HAS_DTYP.

