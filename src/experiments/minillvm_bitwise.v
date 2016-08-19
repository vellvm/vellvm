Require Import ZArith.
Require Import String.
Require Import Program.Wf.
Require Import OrdersEx.
Require Import Util.
Require Import SetsAndMaps.
Require Import List.
Require Import block_model.
Require Import LTS.
Import ListNotations.
Import Equalities.
Import Bool.
Import CoqEqDec.
Import Coq.Classes.EquivDec.
Import Coqlib.

Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

(* Single-threaded MiniLLVM - to be merged with the main file 
   when the memory models are reconciled *)

(* CFG setup *)
(* Consider just choosing something for node (maybe positive?),
   and using a kind of map other than FMap. *)
Parameter (node : Type) (node_eq : EqDec_eq node).
Module Node_Dec <: MiniDecidableType.
  Definition t := node.
  Definition eq_dec := eq_dec.
End Node_Dec.
Module Node_Dec' := Make_UDT Node_Dec.
Module NodeMap := FMap' Node_Dec'.
Definition node_map := NodeMap.t.
Module NodeSet := NodeMap.MSet.
Definition node_set := NodeSet.t.

Inductive edge_type : Set := Seq | T | F.
Instance edge_type_eq : @EqDec edge_type eq eq_equivalence.
Proof. eq_dec_inst. Qed. (* It would be nice if Scheme Equality did this. *)  

Definition edge := (node * edge_type * node)%type.
Instance edge_eq : @EqDec edge eq eq_equivalence.
Proof. eq_dec_inst; apply eq_dec. Qed.
Module Edge_Dec <: MiniDecidableType.
  Definition t := edge.
  Definition eq_dec := @eq_dec edge edge_eq.
End Edge_Dec.
Module Edge_Dec' := Make_UDT Edge_Dec.
Module EdgeSet := MSet' (Edge_Dec').
Definition edge_set := EdgeSet.t.

Module String_Dec <: MiniDecidableType.
  Definition t := string.
  Definition eq_dec := string_dec.
End String_Dec.
Module String_Dec' := Make_UDT String_Dec.
Module StringMap := FMap' String_Dec'.
Definition string_map := StringMap.t. (* convert threads to idents? *)

Definition ident := positive.
Instance ident_eq : @EqDec ident eq eq_equivalence.
Proof. eq_dec_inst. Qed.

(* Turn trit lists back into unknown memvals *)
Section LLVM.
  Inductive type : Set :=
  | Int_ty : nat -> type
  | Pointer_ty : type -> type
  | Array_ty : nat -> type -> type
  | Struct_ty : list type -> type.
  (* Nested induction nonsense thanks to CPDT *)
  Fixpoint type_ind' (P : type -> Type) (Q : list type -> Type)
    (Hint : forall n, P (Int_ty n)) (Hptr : forall t, P t -> P (Pointer_ty t))
    (Harray : forall t n, P t -> P (Array_ty n t))
    (Hnil : Q nil) (Hcons : forall t rest, P t -> Q rest -> Q (t :: rest))
    (Hstruct : forall tl, Q tl -> P (Struct_ty tl)) t : P t :=
    match t with
    | Int_ty n => Hint n
    | Pointer_ty t => Hptr _ (type_ind' P Q Hint Hptr Harray Hnil Hcons Hstruct t)
    | Array_ty n t => Harray _ _ (type_ind' P Q Hint Hptr Harray Hnil Hcons Hstruct t)
    | Struct_ty tl => Hstruct _ ((fix type_list_ind tl : Q tl :=
        match tl with
        | nil => Hnil
        | t :: rest => Hcons _ _ 
            (type_ind' P Q Hint Hptr Harray Hnil Hcons Hstruct t)
            (type_list_ind rest)
        end) tl)
    end.

  Instance type_eq : @EqDec type eq eq_equivalence.
  Proof.
    unfold EqDec; unfold equiv; unfold complement; intro t; 
      einduction t using type_ind'; intros.
    - destruct y; try (right; intro; discriminate); auto.
      destruct (eq_dec n n0); clarify.
      right; intro H; inversion H; auto.
    - destruct y; try (right; intro; discriminate).
      specialize (IHt0 y); destruct IHt0; clarify.
      right; intro H; inversion H; auto.
    - destruct y; try (right; intro; discriminate).
      destruct (eq_dec n n0); try (right; intro H; inversion H; auto; fail).
      specialize (IHt0 y); destruct IHt0; clarify.
      right; intro H; inversion H; auto.
    - instantiate (1 := fun tl => forall tl', {tl = tl'} + {tl <> tl'});
      clarify.
      destruct tl'; try (right; intro; discriminate); auto.
    - clarify.
      destruct tl'; try (right; intro; discriminate).
      specialize (IHt0 t); destruct IHt0; [|right; intro]; clarify.
      specialize (IHt1 tl'); destruct IHt1; [|right; intro]; clarify.
    - clarify.
      destruct y; try (right; intro; discriminate).
      specialize (IHt0 l); destruct IHt0; clarify.
      right; intro H; inversion H; auto.
  Qed.

  Global Instance Z_eq : @EqDec Z eq eq_equivalence.
  Proof. eq_dec_inst. Qed.

  Variables (block : Type) (block_eq : EqDec_eq block).
  Variables (num : Type) (num_eq : EqDec_eq num).
  Definition data := list num.
  Instance data_eq : EqDec_eq data.
  Proof. apply list_eq; auto. Qed.

  Section Memory.
(*    Inductive trit := Zero | One | Undef.
    Definition neg_trit t :=
      match t with
      | One => Zero
      | Zero => One
      | Undef => Undef
      end.*)

    Definition ref := (block * data * nat)%type.
    Global Instance ref_eq : @EqDec ref eq eq_equivalence.
    Proof. eq_dec_inst. Qed.

    Inductive mem_data :=
    | Num (n : num)
    | PtrFrag (index : nat) (p : ref).
    Global Instance mem_data_eq : @EqDec mem_data eq eq_equivalence.
    Proof. eq_dec_inst. Qed.
    (*Definition Undef_tryte := Tryte Undef Undef Undef Undef 
                                    Undef Undef Undef Undef.*)

    Definition LLVM_access := mem_op block mem_data.
    Definition mem := list LLVM_access.
    Global Instance LLVM_access_eq : @EqDec LLVM_access eq eq_equivalence.
    Proof. eq_dec_inst. Qed.

    (* Round to the nearest multiple. *)
    Definition padn n a := 
      match NPeano.modulo n a with 
      | O => n 
      | d => (n + (a - d))%nat
      end.

    Lemma padn_ge : forall n a, (n <= padn n a)%nat.
    Proof.
      unfold padn; intros.
      destruct (NPeano.modulo n a); omega.
    Qed.

(*    Fixpoint encode_int' i n :=
      match n with
      | O => []
      | S n' => let d := two_power_nat n' in 
          (if zle d i then One else Zero) :: encode_int' (i mod d) n'
      end.

    Opaque mult.

    Lemma two_power_pow : forall n, Z_of_nat (NPeano.pow 2 n) = two_power_nat n.
    Proof.
      induction n; clarify.
      rewrite two_power_nat_S, Nat2Z.inj_mul, IHn; clarify.
    Qed.

    (* What about negative numbers? Using a fixed representation here, but 
       in theory this is target-dependent. *)
    Definition encode_int i n :=
      match n with
      | O => []
      | S O => if eq_dec i 0 then [Zero] else [One]
      | S n' => if zlt i 0 then One :: encode_int' (i + two_power_nat n') n'
                else Zero :: encode_int' i n'
      end.
    Hint Opaque encode_int.

    Definition encode_nat m n := encode_int (Z_of_nat m) n.

    Fixpoint make_trytes tl :=
      match tl with
      | t0 :: t1 :: t2 :: t3 :: t4 :: t5 :: t6 :: t7 :: rest =>
          Tryte t0 t1 t2 t3 t4 t5 t6 t7 :: make_trytes rest
      | _ => []
      end.

    Inductive realize_trit : trit -> Z -> Prop :=
    | realize_zero : realize_trit Zero 0
    | realize_one : realize_trit One 1
    | undef_zero : realize_trit Undef 0
    | undef_one : realize_trit Undef 1.
    
    Inductive realize_trits' : list trit -> Z -> Prop :=
    | realize'_nil : realize_trits' [] 0
    | realize'_cons t i (Ht : realize_trit t i) ts i' 
        (Hts : realize_trits' ts i') 
        i'' (Hresult : i'' = i * two_power_nat (length ts) + i') : 
        realize_trits' (t :: ts) i''.

    Inductive realize_trits : list trit -> Z -> Prop :=
    | realize_nil : realize_trits [] 0
    | realize_single t i (Ht : realize_trit t i) : realize_trits [t] i
    | realize_pos t (Hpos : realize_trit t 0) ts (Hlen : (length ts > 0)%nat) i
        (Hts : realize_trits' ts i) : realize_trits (t :: ts) i
    | realize_neg t (Hneg : realize_trit t 1) ts (Hlen : (length ts > 0)%nat) i
        (Hts : realize_trits' ts i) i'
        (Hcomp : i' = i - two_power_nat (length ts)) :
        realize_trits (t :: ts) i'.
    Hint Constructors realize_trit realize_trits' realize_trits.

    Lemma realize_test : realize_trits [One; One; Undef; Undef; One] (-3).
    Proof.
      eapply realize_neg; clarify.
      econstructor; [eauto | | eauto].
      econstructor; [apply undef_one | | eauto].
      econstructor; [apply undef_zero | eauto | eauto].
      { clarify. }
    Qed.
    
    Fixpoint decode_trits' ts :=
      match ts with
      | [] => Some 0
      | t :: rest =>
          match (t, decode_trits' rest) with
          | (Zero, Some i) => Some i
          | (One, Some i) => Some (two_power_nat (length rest) + i)
          | _ => None
          end
      end.

    Definition decode_trits ts :=
      match ts with
      | [] => Some 0
      | [Zero] => Some 0
      | [One] => Some 1
      | Zero :: rest => decode_trits' rest
      | One :: rest =>
          match decode_trits' rest with
          | Some i => Some (i - two_power_nat (length rest))
          | None => None
          end
      | _ => None
      end.

    Opaque Z.add.

    Lemma decode_realize' : forall ts i, decode_trits' ts = Some i ->
      (forall i', realize_trits' ts i' <-> i' = i).
      induction ts; clarify.
      - split; clarify; inversion H; auto.
      - destruct a; clarify.
        + split; intro X; clarify.
          * inversion X; clarify.
            inversion Ht; clarify.
            rewrite IHts in Hts; eauto.
          * econstructor; eauto; clarify.
            rewrite IHts; eauto.
            omega.
        + split; intro X; clarify.
          * inversion X; clarify.
            rewrite IHts in Hts; eauto.
            assert (i = 1) by (inversion Ht; auto); subst; auto.
          * econstructor; eauto.
            rewrite IHts; eauto.
    Qed.

    Lemma decode_realize : forall ts i, decode_trits ts = Some i ->
      (forall i', realize_trits ts i' <-> i' = i).
    Proof.
      destruct ts; clarify.
      { split; clarify; inversion H; auto. }
      destruct t; clarify; destruct ts; clarify.
      - split; clarify; inversion H; try (inversion Ht); clarify; omega.
      - rewrite <- (decode_realize' (t :: ts)); clarify.
        split; intro X; [inversion X | econstructor]; clarify.
        inversion Hneg.
        { destruct t; clarify. }
      - split; clarify; inversion H; try (inversion Ht); clarify; omega.
      - split; intro X; [inversion X; clarify|].
        { inversion Hpos. }
        + rewrite (decode_realize'(i := x) (t :: ts)) in Hts; clarify.
          { destruct t; clarify. }
        + eapply realize_neg; eauto; clarify.
          rewrite decode_realize'; eauto.
          { destruct t; clarify. }
    Qed.

    Fixpoint break_trytes ts :=
      match ts with
      | [] => Some []
      | t :: rest =>
          match (t, break_trytes rest) with
          | (Tryte t0 t1 t2 t3 t4 t5 t6 t7, Some l) =>
              Some (t0 :: t1 :: t2 :: t3 :: t4 :: t5 :: t6 :: t7 :: l)
          | _ => None
          end
      end.

    Lemma encode'_length : forall n i, length (encode_int' i n) = n.
    Proof. induction n; clarify. Qed.

    Opaque two_power_nat Z.mul.

    Lemma encode_decode' : forall k i, 0 <= i < two_power_nat k ->
      decode_trits' (encode_int' i k) = Some i.
    Proof.
      induction k; clarify.
      { rewrite two_power_nat_O in *; assert (i = 0) by omega; clarify. }
      rewrite two_power_nat_S in *.
      destruct (zle (two_power_nat k) i); clarify.
      - rewrite IHk; clarify; [|apply Z_mod_lt; omega].
        rewrite encode'_length.
        rewrite (Z_div_mod_eq i (2 ^ Z_of_nat k)) at 2.
        rewrite two_power_nat_equiv in *.
        assert (i / 2 ^ Z_of_nat k = 1) as Heq; 
          [| rewrite Heq, Z.mul_1_r; destruct (i mod 2 ^ Z.of_nat k); clarify].
        erewrite Zdiv_unique; eauto.
        + instantiate (1 := i - 2 ^ Z_of_nat k); omega.
        + omega.
        + apply Z.lt_gt; apply Z.pow_pos_nonneg; omega.
      - rewrite IHk; clarify; [|apply Z_mod_lt; omega].
        rewrite Z.mod_small; auto; omega.
    Qed.

    Opaque decode_trits' encode_int'.

    Lemma encode_decode : forall k i, (k > 1)%nat ->
      -(two_power_nat (k - 1)) <= i < two_power_nat (k - 1) ->
      decode_trits (encode_int i k) = Some i.
    Proof.
      destruct k; clarify; [omega|].
      destruct k; clarify; [omega|].
      destruct (zlt i 0); clarify.
      - rewrite <- cond; rewrite encode_decode'; [|omega].
        generalize (encode'_length (S k) (i + two_power_nat (S k)));
          rewrite cond; simpl; intro Hlen.
        inversion Hlen; clarify.
        rewrite Z.add_simpl_r; auto.
      - rewrite <- cond; rewrite encode_decode'; auto; omega.
    Qed.      *)
    
  End Memory.
(*  Hint Constructors realize_trit realize_trits' realize_trits.*)

  Section Syntax.
    Inductive const : Type :=
    | Int_c : data -> const
    | Pointer_c : ref -> const
    | Complex_c : list const -> const.
    (* Nested induction nonsense thanks to CPDT *)
    Fixpoint const_ind' (P : const -> Type) (Q : list const -> Type)
      (Hint : forall z, P (Int_c z)) (Hptr : forall p, P (Pointer_c p))
      (Hnil : Q nil) (Hcons : forall c rest, P c -> Q rest -> Q (c :: rest))
      (Hcomplex : forall cl, Q cl -> P (Complex_c cl)) c : P c :=
      match c with
      | Int_c z => Hint z
      | Pointer_c p => Hptr p
      | Complex_c cl => Hcomplex _ ((fix const_list_ind cl : Q cl :=
          match cl with
          | nil => Hnil
          | c :: rest => Hcons _ _ 
              (const_ind' P Q Hint Hptr Hnil Hcons Hcomplex c)
              (const_list_ind rest)
          end) cl)
      end.

(*    Global Instance list_trit_eq : EqDec_eq (list trit).
    Proof. apply list_eq; eq_dec_inst. Qed.*)
    
    Global Instance const_eq : @EqDec const eq eq_equivalence.
    Proof.
      unfold EqDec; unfold equiv; unfold complement; intros x;
        change (forall y, {x = y} + {x <> y}); einduction x using const_ind';
        intros.
      - destruct y; try (right; intro; discriminate); auto.
        destruct (eq_dec z d); clarify; right; intro; inversion H; auto.
      - destruct y; try (right; intro; discriminate).
        destruct (eq_dec p r); clarify; right; intro H; inversion H; auto.
      - instantiate (1 := fun cl => forall cl', {cl = cl'} + {cl <> cl'});
          clarify.
        destruct cl'; try (right; intro; discriminate); auto.
      - clarify.
        destruct cl'; try (right; intro; discriminate).
        specialize (IHc c0); destruct IHc; [|right; intro]; clarify.
        specialize (IHc0 cl'); destruct IHc0; [|right; intro]; clarify.
      - clarify.
        destruct y; try (right; intro; discriminate).
        specialize (IHc l); destruct IHc; clarify.
        right; intro H; inversion H; auto.
    Qed.

    Inductive expr : Type :=
    | Local (i : ident)
    | Const (c : const)
    | Global (i : ident).
    
    Inductive op : Set := Add | Sub | Mul | Pad | And | Or.

    Inductive cmp : Set := Eq | Ne | Slt.

    Inductive instr : Type :=
    | Assign : ident -> op -> type -> expr -> expr -> instr
    | ICmp : ident -> cmp -> type -> expr -> expr -> instr
    | Br_i1 : expr -> instr
    | Br_label : instr
    | Alloca : ident -> type -> instr
    | Gep : ident -> type -> type -> expr -> list (type * expr) -> instr
    | Bitcast : type -> expr -> type -> instr
    | Load : ident -> type -> expr -> instr
    | Store : type -> expr -> type -> expr -> instr
    | Cmpxchg : ident -> type -> expr -> type -> expr -> type -> expr -> instr
    | Phi : ident -> type -> node_map expr -> instr
    | Call : ident -> type -> expr -> list expr -> instr
    | Ret : type -> expr -> instr
    (* dummy instruction for simulation *)
    | Output : expr -> instr.
    
    Definition def i x := match i with
    | Assign y _ _ _ _ => y = x
    | ICmp y _ _ _ _ => y = x
    | Alloca y _ => y = x
    | Gep y _ _ _ _ => y = x
    | Load y _ _ => y = x
    | Cmpxchg y _ _ _ _ _ _ => y = x
    | Phi y _ _ => y = x
    | Call y _ _ _ => y = x
    | _ => False
    end.
  End Syntax.

  Variables (do_op : op -> data -> data -> option data)
            (do_cmp : cmp -> data -> data -> option data).
  Variables (concrete_int : data -> option Z) (inject_int : Z -> data)
            (realize_data : data -> Z -> Prop).
  Hypotheses (inject_concrete : forall i, concrete_int (inject_int i) = Some i)
    (realize_concrete : forall d i (Hconcrete : concrete_int d = Some i) i',
       realize_data d i' <-> i' = i).
  (* define ops/cmps on ground ints *)
  Hypothesis (do_eq : forall v v',
    do_cmp Eq v v = Some v' -> concrete_int v' = Some 1).
  Definition inject_nat n := inject_int (Z_of_nat n).

  Context (ML : Memory_Layout mem_data block_eq).

  Section Target.
    
    (* Alignment will be given in bytes, because we don't have a good way
       of doing any other kind of alignment. *)
    (* Endianness is as yet unimplemented. *)
    Class Target := 
    { int_align : list (option nat); ptr_size : nat; ptr_align : nat;
      big_endian : bool;
      int_align_pos : ~In (Some O) int_align;
      int_align_sane : Forall (fun o => match o with Some a =>
        (a < NPeano.pow 2 (8*ptr_size - 1))%nat | None => True end) int_align;
      ptr_size_pos : (ptr_size > 0)%nat;
      ptr_align_pos : (ptr_align > 0)%nat;
      ptr_align_sane : (ptr_align < NPeano.pow 2 (8*ptr_size - 1))%nat }.

    Context {T : Target}.

    Definition get_align n :=
      match nth_error int_align n with
      | Some (Some a) => a
      | Some None => 
          match find (fun o => match o with Some _ => true | _ => false end) 
                     (skipn n int_align) with
          | Some (Some a) => a
          | _ => S O
          end
      | None =>
          match find (fun o => match o with Some _ => true | _ => false end)
                     (rev int_align) with
          | Some (Some a) => a
          | _ => S O
          end
      end. (* Length of list should be equal to largest declared int size.
              If this is true, failure cases should not be reached
              unless no int alignment is declared. *)

    Lemma in_skipn : forall {A} (a : A) n l, In a (skipn n l) -> In a l.
    Proof.
      induction n; clarify.
      destruct l; clarify.
    Qed.

    Lemma get_align_pos : forall n, (get_align n > 0)%nat.
    Proof.
      unfold get_align; intro.
      destruct (nth_error int_align n) eqn: Hnth; clarify.
      - exploit nth_error_in; eauto; intro.
        destruct o; clarify.
        + destruct n0; auto.
          generalize (int_align_pos H); clarify.
        + destruct (find (fun o => match o with | Some _ => true | None => false
            end) (skipn n int_align)) eqn: Hfind; clarify. 
          generalize (find_success _ _ _ Hfind); clarify.
          destruct n0; clarify; exploit int_align_pos; clarify.
          eapply in_skipn; eauto.
      - destruct (find (fun o => match o with | Some _ => true | None => false
            end) (rev int_align)) eqn: Hfind; clarify. 
          generalize (find_success _ _ _ Hfind); clarify.
          destruct n0; clarify; exploit int_align_pos; clarify.
          rewrite in_rev; auto.
    Qed.

    Lemma one_sane : (1 < NPeano.pow 2 (8*ptr_size - 1))%nat.
    Proof.
      apply NPeano.Nat.pow_gt_1; auto.
      generalize (ptr_size_pos); omega.
    Qed.
    Hint Resolve one_sane.

    Lemma get_align_sane : forall n, (get_align n <
      NPeano.pow 2 (8*ptr_size - 1))%nat.
    Proof.
      unfold get_align; intro.
      generalize (int_align_sane); intro Hsane; rewrite Forall_forall in *.
      destruct (nth_error int_align n) eqn: Hnth; clarify.
      - exploit nth_error_in; eauto; intro.
        destruct o; clarify.
        + specialize (Hsane _ H); clarify.
        + destruct (find (fun o => match o with | Some _ => true | None => false
            end) (skipn n int_align)) eqn: Hfind; clarify.
          destruct o; clarify.
          generalize (find_success _ _ _ Hfind); intros [Hin _].
          exploit Hsane; [eapply in_skipn; eauto | clarify].
      - destruct (find (fun o => match o with | Some _ => true | None => false
            end) (rev int_align)) eqn: Hfind; clarify. 
          generalize (find_success _ _ _ Hfind); clarify.
          exploit Hsane; [rewrite in_rev; eauto | clarify].
    Qed.
          
    Fixpoint first_align t :=
      match t with
      | Int_ty n => get_align n
      | Pointer_ty _ => ptr_align
      | Array_ty _ t => first_align t
      | Struct_ty tys =>
          match tys with
          | [] => S O
          | t :: _ => first_align t
          end
      end.

    Lemma first_align_pos : forall t, (first_align t > 0)%nat.
    Proof.
      einduction t using type_ind'; simpl; try assumption.
      - apply get_align_pos.
      - apply ptr_align_pos.
      - instantiate (1 := fun ts => match ts with [] => True 
          | t :: _ => (first_align t > 0)%nat end); clarify.
      - clarify.
      - destruct tl; clarify.
    Qed.

    Lemma first_align_sane : forall t, (first_align t <
      NPeano.pow 2 (8*ptr_size - 1))%nat.
    Proof.
      einduction t using type_ind'; simpl; try assumption.
      - apply get_align_sane.
      - apply ptr_align_sane.
      - instantiate (1 := fun ts => match ts with [] => True 
          | t :: _ => (first_align t < NPeano.pow 2 (8*ptr_size - 1))%nat end); 
          clarify.
      - clarify.
      - destruct tl; clarify.
    Qed.

    (* size in bytes *)
    Fixpoint size_of (t : type) :=
      match t with
      | Int_ty n => NPeano.div (padn n 8) 8
      | Pointer_ty _ => ptr_size
      | Array_ty n t => (n * padn (size_of t) (first_align t))%nat
      | Struct_ty tys => (fix size_of_tys tys := 
          match tys with
          | [] => O
          | t :: rest => (padn (size_of t) (first_align (Struct_ty rest)) + 
                          size_of_tys rest)%nat
          end) tys
      end.

    Lemma struct_size : forall t tys (Hin : In t tys),
      (size_of t <= size_of (Struct_ty tys))%nat.
    Proof.
      induction tys; clarify.
      generalize (padn_ge (size_of a) (first_align (Struct_ty tys)));
        destruct Hin; clarify; omega.
    Qed.

    Fixpoint add_all l :=
      match l with
      | [] => 0
      | n :: rest => n + add_all rest
      end.

    (* This needs to use do_op. *)
    Definition pad_offset o a := do_op Pad o (inject_nat a).
    (* This is getting pretty weird... *)

    Fixpoint compute_offset (o : data) t (il : list data) :=
      match il with
      | [] => Some o
      | i :: rest =>
          match t with
          | Pointer_ty ty =>
              match (pad_offset o (first_align ty),
  do_op Mul i (inject_nat (padn (size_of ty) (first_align ty))))
              with
              | (Some o', Some off) =>
                  match do_op Add o' off with
                  | Some o'' => compute_offset o'' ty rest
                  | None => None
                  end
              | _ => None
              end
          | Array_ty _ ty =>
              match (pad_offset o (first_align ty),
  do_op Mul i (inject_nat (padn (size_of ty) (first_align ty))))
              with
              | (Some o', Some off) =>
                  match do_op Add o' off with
                  | Some o'' => compute_offset o'' ty rest
                  | None => None
                  end
              | _ => None
              end
          | Struct_ty tys => (* indices must be concrete *)
              match concrete_int i with
              | Some i' =>
                  if i' <? 0 then None else let n := nat_of_Z i' in
                  (fix elm_offset o n tys :=
                   match tys with
                   | [] => None
                   | ty :: trest => 
                       match (pad_offset o (first_align ty), n) with
                       | (Some o', O) => compute_offset o' ty rest
                       | (Some o', S n') =>
                           match do_op Add o' (inject_nat (size_of ty)) with
                           | Some o'' => elm_offset o'' n' trest
                           | None => None
                           end
                       | _ => None
                       end
                   end) o n tys
              | None => None
              end
          | _ => None
          end
      end.

    (* Do we write (undef, 0, etc.) to the padding bytes, or leave them 
       as they are? *)
(*    Definition extend (ts : list trit) n := 
      replicate Zero (n - length ts) ++ ts.*)

    Fixpoint lower_val (t : type) (o : nat) (v : const) :=
      let lower_vals := fix lower_vals ts o vs {struct vs} :=
          match (vs, ts) with
          | (_, []) => Some []
          | (v :: vrest, t :: trest) =>
              let o' := padn o (first_align t) in
              match (lower_val t o' v, 
                     lower_vals trest (o' + size_of t)%nat vrest) with
              | (Some mv, Some mv') => Some (mv ++ mv')
              | _ => None
              end
          | _ => None
          end in
      let o' := padn o (first_align t) in
      match (t, v) with
      | (Int_ty n, Int_c i) =>
          Some (combine (interval o' (o' + size_of (Int_ty n))) (map Num i))
      | (Pointer_ty _, Pointer_c p) => 
          Some (map (fun n => ((o' + n)%nat, PtrFrag n p))
                    (interval 0 ptr_size))
      | (Array_ty n t, Complex_c vs) => lower_vals (replicate t n) o vs
      | (Struct_ty ts, Complex_c vs) => lower_vals ts o vs
      | _ => None
      end.

    Lemma pad_pad : forall o n, n <> O -> padn (padn o n) n = padn o n.
    Proof.
      unfold padn; intros.
      destruct (NPeano.modulo o n) eqn: Hmod; clarsimp.
      rewrite NPeano.Nat.add_mod, Hmod; auto.
      rewrite (NPeano.Nat.mod_small (n - S n0)); [|omega].
      generalize (NPeano.mod_bound_pos o n); intro Hlt; use Hlt; [|omega];
        use Hlt; [|omega]; rewrite Hmod in Hlt.
      assert ((S n0 + (n - S n0))%nat = n) as Hn by omega; rewrite Hn.
      rewrite NPeano.Nat.mod_same; auto.
    Qed.

    Lemma pad_plus : forall o k n, n <> O -> NPeano.modulo k n = O ->
      padn (padn o n + k) n = padn (o + k) n.
    Proof.
      unfold padn; intros.
      destruct (NPeano.modulo o n) eqn: Hmod; clarsimp.
      rewrite NPeano.Nat.add_mod, (NPeano.Nat.add_mod _ k); clarsimp.
      rewrite plus_0_r.
      rewrite NPeano.Nat.add_mod; auto.
      rewrite (NPeano.Nat.mod_small (n - S n0)); [|omega].
      generalize (NPeano.mod_bound_pos o n); intro Hlt; use Hlt; [|omega];
        use Hlt; [|omega]; rewrite Hmod in *.
      assert ((S n0 + (n - S n0))%nat = n) as Hn by omega; rewrite Hn.
      rewrite plus_0_r, NPeano.Nat.mod_same, NPeano.Nat.mod_0_l; auto.
      rewrite NPeano.Nat.mod_small; clarify; omega.
    Qed. (* Unfortunately, size is not always a multiple of alignment -
            for instance, in a struct with fields of varying sizes. *)

    Fixpoint lower_vals ts o vs {struct vs} :=
      match (vs, ts) with
      | (_, []) => Some []
      | (v :: vrest, t :: trest) =>
          let o' := padn o (first_align t) in
          match (lower_val t o' v, 
                 lower_vals trest (o' + size_of t)%nat vrest) with
          | (Some mv, Some mv') => Some (mv ++ mv')
          | _ => None
          end
      | _ => None
      end.

    Lemma lower_pad : forall t o v,
      lower_val t (padn o (first_align t)) v = lower_val t o v.
    Proof.
      destruct v, t; clarify; try rewrite pad_pad; auto.
      - generalize (get_align_pos n); omega.
      - generalize (ptr_align_pos); omega.
      - destruct l; clarify.
        destruct n; clarify.
        rewrite pad_pad; auto.
        generalize (first_align_pos t); omega.
      - destruct l; clarify.
        destruct l0; clarify.
        rewrite pad_pad; auto.
        generalize (first_align_pos t); omega.
    Qed.

    (* The type in the pointer path tells how to interpret the indices.
       The type of the read/write tells what values are acceptable. *)
    (* In the SEMANTICS, gep needs to translate indices at the static type indicated
       into indices according to the type tag in the pointer. 
       E.g., if p = (i8*, l, []), then gep i16* p 2 yields (i8*, l, [4]).
       Since this basically means reducing everything to i8, we might as well
       just compute the offset in bytes at the gep. *)

    Definition mk_read t b o v : option (list LLVM_access) :=
      match lower_val t o v with
      | Some mv => Some (map 
          (fun (x : nat * mem_data) => let (o, v) := x in MRead (b, o) v) mv)
      | None => None
      end.
    Definition mk_write t b o v : option (list LLVM_access) :=
      match lower_val t o v with
      | Some mv => Some (map 
          (fun (x : nat * mem_data) => let (o, v) := x in MWrite (b, o) v) mv)
      | None => None
      end.
    Definition mk_alloc t b : list LLVM_access := [MAlloc b (size_of t)].
    Definition mk_malloc b n : list LLVM_access := [MAlloc b n].
    Definition mk_free b : list LLVM_access := [MFree b].

    Definition mk_reads ts b o vs : option (list LLVM_access) :=
      match lower_vals ts o vs with
      | Some mv => Some (map 
          (fun (x : nat * mem_data) => let (o, v) := x in MRead (b, o) v) mv)
      | None => None
      end.
    Definition mk_writes ts b o vs : option (list LLVM_access) :=
      match lower_val ts o vs with
      | Some mv => Some (map 
          (fun (x : nat * mem_data) => let (o, v) := x in MWrite (b, o) v) mv)
      | None => None
      end.

  End Target.

  Section CFGs.
    Record CFG := { Nodes : node_set; Edges : edge_set;
                    Start : node; Exit : node; Label : node -> instr }.

    Definition SSA G := forall x, exists n, 
      NodeMap.MSet.For_all (fun n' => def (Label G n) x -> n' = n) (Nodes G).

    Definition out_edges (G : CFG) (ty : edge_type) (n : node) :=
      EdgeSet.filter (fun e => match e with (u, t, _) => 
        beq u n && beq t ty end) (Edges G).

    Lemma out_edges_form : forall G ty n e 
      (Hin : EdgeSet.In e (out_edges G ty n)), 
      EdgeSet.In e (Edges G) /\ exists n', e = (n, ty, n').
    Proof.
      unfold out_edges; intros.
      rewrite EdgeSet.filter_spec in Hin.
      destruct e as ((?, ?), ?); unfold beq in *; clarify; eauto.
      { repeat intro; clarify. }
    Qed.

    Definition next_node (G : CFG) (ty : edge_type) (n : node) :=
      match EdgeSet.choose (out_edges G ty n) with
      | None => n
      | Some (_, _, n') => n'
      end.

    Lemma next_node_edges: forall G G' ty n, Edges G = Edges G' -> 
      next_node G ty n = next_node G' ty n.
    Proof. unfold next_node; unfold out_edges; clarsimp. Qed.
    
    Lemma next_node_cases : forall G ty n,
      (EdgeSet.In (n, ty, next_node G ty n) (out_edges G ty n)) \/ 
      (next_node G ty n = n /\ EdgeSet.Empty (out_edges G ty n)).
    Proof.
      unfold next_node; intros.
      destruct (EdgeSet.choose (out_edges G ty n)) eqn: choose;
        [exploit EdgeSet.choose_spec1 | generalize EdgeSet.choose_spec2]; eauto;
      clarify.
      left; exploit out_edges_form; eauto; clarify.
    Qed.

    Corollary next_node_inv : forall G ty n n' (Hnext : next_node G ty n = n'),
      (EdgeSet.In (n, ty, n') (out_edges G ty n)) \/ (n' = n /\
        EdgeSet.Empty (out_edges G ty n)).
    Proof. clarify; apply next_node_cases. Qed.

    Definition seq_instr i := match i with
    | Ret _ _ => false
    | Br_i1 _ => false
    | _ => true
    end.

    Definition instr_edges (G : CFG) := NodeSet.For_all (fun n =>
      if seq_instr (Label G n) then exists n', 
        EdgeSet.Equal (out_edges G Seq n) (EdgeSet.singleton (n, Seq, n')) /\ 
        forall ty, ty <> Seq -> EdgeSet.Equal (out_edges G ty n) EdgeSet.empty
      else match Label G n with
      | Ret _ _ => forall ty, EdgeSet.Equal (out_edges G ty n) EdgeSet.empty
      | Br_i1 _ => exists nt nf, EdgeSet.Equal (out_edges G T n) (EdgeSet.singleton (n, T, nt)) /\ 
          EdgeSet.Equal (out_edges G F n) (EdgeSet.singleton (n, F, nf)) /\
          forall ty, ty <> T /\ ty <> F -> EdgeSet.Equal (out_edges G ty n) EdgeSet.empty
      | _ => False end) (Nodes G).

    Inductive wf_CFG G : Prop :=
    | wf_def (Hstart : NodeSet.In (Start G) (Nodes G))
        (Hexit : NodeSet.In (Exit G) (Nodes G))
        (Hedges : EdgeSet.For_all (fun e => match e with (n, _, n') =>
           NodeSet.In n (Nodes G) -> NodeSet.In n' (Nodes G) end) (Edges G))
        (Hinstr_edges : instr_edges G).
        
    Lemma choose_singleton : forall S e 
      (Heq : EdgeSet.Equal S (EdgeSet.singleton e)), EdgeSet.choose S = Some e.
    Proof.
      intros; destruct (EdgeSet.choose S) eqn: choose;
        [exploit EdgeSet.choose_spec1 | exploit EdgeSet.choose_spec2]; eauto;
        clarify.
      + unfold EdgeSet.Equal in Heq; rewrite Heq in *; 
          rewrite EdgeSet.singleton_spec in *; clarify.
      + unfold EdgeSet.Equal in Heq; rewrite Heq; 
          rewrite EdgeSet.singleton_spec; eauto.
    Qed.

    Lemma wf_next_in : forall G (Hwf : wf_CFG G) n 
      (Hin : NodeSet.In n (Nodes G)) ty, 
    NodeSet.In (next_node G ty n) (Nodes G).
    Proof.
      intros; generalize (next_node_cases G ty n); intros [? | [Hfail ?]].
      - exploit out_edges_form; eauto; intros [He ?]; inversion Hwf.        
        specialize (Hedges _ He); auto.
      - rewrite Hfail; auto.
    Qed.

    Lemma wf_next_defined : forall G (Hwf : wf_CFG G) 
      n (Hin : NodeSet.In n (Nodes G)) 
      ty x y n' (Hedge : EdgeSet.In (x, y, n') (out_edges G ty n)),
      next_node G ty n = n' /\ NodeSet.In n' (Nodes G).
    Proof.
      intros; inversion Hwf; specialize (Hinstr_edges _ Hin).
      exploit out_edges_form; eauto; intros [He ?]; clarify.
      specialize (Hedges _ He); clarify.
      generalize EdgeSet.empty_spec; intro Hempty.
      destruct (seq_instr (Label G n)).
      - destruct Hinstr_edges as [n2 [Hseq Hr]]; destruct (eq_dec ty Seq); clarify.
        + unfold next_node; unfold EdgeSet.Equal in Hseq; rewrite Hseq in *.
          erewrite choose_singleton; eauto 2; clarify.
          rewrite EdgeSet.singleton_spec in Hedge; clarify.
        + unfold EdgeSet.Equal in Hr; rewrite Hr in Hedge; auto; 
            specialize (Hempty _ Hedge); contradiction.
      - destruct (Label G n); try contradiction.
        + destruct Hinstr_edges as [nt [nf [HT [HF Hr]]]]; 
            destruct (eq_dec ty T); destruct (eq_dec ty F); clarify.
          * unfold next_node; unfold EdgeSet.Equal in HT; rewrite HT in *.
            erewrite choose_singleton; eauto 2; clarify.
            rewrite EdgeSet.singleton_spec in Hedge; clarify.
          * unfold next_node; unfold EdgeSet.Equal in HF; rewrite HF in *.
            erewrite choose_singleton; eauto 2; clarify.
            rewrite EdgeSet.singleton_spec in Hedge; clarify.
          * unfold EdgeSet.Equal in Hr; rewrite Hr in Hedge; auto; 
              specialize (Hempty _ Hedge); contradiction.
        + unfold EdgeSet.Equal in Hinstr_edges; rewrite Hinstr_edges in Hedge; 
            auto; specialize (Hempty _ Hedge); contradiction.
    Qed.

    (* better treatment of function pointers? *)
    Definition fun_def := (ref * ident * list ident * CFG)%type.
    Definition prog := list fun_def.
    Definition find_fun l (P : prog) := 
      match find (fun x => beq l (fst (fst (fst x)))) P with
      | Some (_, f, params, G) => Some (f, params, G)
      | None => None
      end.
    Definition find_loc f (P : prog) :=
      match find (fun x => beq f (snd (fst (fst x)))) P with
      | Some (l, _, _, _) => Some l
      | None => None
      end.
    Definition find_name l (P : prog) :=
      match find (fun x => beq l (fst (fst (fst x)))) P with
      | Some (_, f, _, _) => Some f
      | None => None
      end.
    Definition find_graph f (P : prog) := 
      match find (fun x => beq f (snd (fst (fst x)))) P with
      | Some (_, _, _, G) => Some G
      | None => None
      end.
 
    Lemma find_fun_drop : forall l l' f P1 params G P2 (Hdiff : l <> l'),
      find_fun l (P1 ++ (l', f, params, G) :: P2) = find_fun l (P1 ++ P2).
    Proof.
      intros; unfold find_fun; rewrite find_drop; auto; unfold beq; clarify.
    Qed.

    Lemma find_graph_drop : forall f P1 l f' params G P2 (Hdiff : f <> f'),
      find_graph f (P1 ++ (l, f', params, G) :: P2) = find_graph f (P1 ++ P2).
    Proof.
      intros; unfold find_graph; rewrite find_drop; auto; unfold beq; clarify.
    Qed.

    Definition wf_prog (P : prog) := forall i l f params G
      (Hi : nth_error P i = Some (l, f, params, G)),
      wf_CFG G /\ forall j l' f' params' G' 
      (Hj : nth_error P j = Some (l', f', params', G')),
      (l = l' \/ f = f') -> i = j.

    Lemma find_fun_graph : forall l P f params G (Hwf : wf_prog P)
      (Hfun : find_fun l P = Some (f, params, G)),
      find_graph f P = Some G.
    Proof.
      unfold find_fun; clarsimp.
      destruct x as (((?, ?), ?), ?); clarify.
      exploit @find_nth_error; eauto; intros [i [_ [Hnth ?]]].
      exploit @find_success; eauto; intros [Hin _].
      unfold find_graph.
      exploit (find_succeeds (fun x : ref * ident * list ident * CFG => 
        beq f (snd (fst (fst x))))); eauto 2; unfold beq in *; clarify.
      destruct x as (((?, ?), ?), ?).
      generalize (find_nth_error _ _ _ H0); intros [j [_ [Hnth' ?]]];
        unfold wf_prog in Hwf.
      specialize (Hwf _ _ _ _ _ Hnth); destruct Hwf as [_ Hwf];
        specialize (Hwf _ _ _ _ _ Hnth'); clarify.
      rewrite Hnth in Hnth'; clarify.
    Qed.      

    Lemma find_wf_graph : forall f P G (Hwf : wf_prog P)
      (Hfind : find_graph f P = Some G), wf_CFG G.
    Proof.
      unfold wf_prog, find_graph; clarsimp.
      destruct x as (((l, f'), params), ?); clarify.
      exploit @find_nth_error; eauto; intros [i [_ [Hnth _]]].
      specialize (Hwf i _ _ _ _ Hnth); clarify.
    Qed.

    Lemma wf_find_fun : forall P1 l f params G P2 
      (Hwf : wf_prog (P1 ++ (l, f, params, G) :: P2)),
      find_fun l (P1 ++ (l, f, params, G) :: P2) = Some (f, params, G).
    Proof.
      unfold find_fun; clarsimp.
      exists (l, f, params, G); split; auto.
      unfold wf_prog in Hwf.
      specialize (Hwf (length P1)); rewrite nth_error_split in Hwf; clarsimp.
      destruct (find (fun x => beq l (fst (fst (fst x)))) P1) eqn: find.
      { exploit @find_nth_error; eauto; intros [j [? [Hfound Hcond]]].
        specialize (Hwf2 j); rewrite nth_error_app in Hwf2; clarify.
        destruct p as (((l', f'), params'), G');
          specialize (Hwf2 _ _ _ _ Hfound); clarify.
        unfold beq in Hcond; clarify.
        exfalso; apply (lt_irrefl _ l0). }
      unfold beq; clarify.
    Qed.

    Corollary wf_find_fun_iff : forall P1 l f params G P2 
      (Hwf : wf_prog (P1 ++ (l, f, params, G) :: P2)) l',
      find_fun l' (P1 ++ (l, f, params, G) :: P2) =
      if eq_dec l' l then Some (f, params, G) else find_fun l' (P1 ++ P2).
    Proof.
      intros; destruct (eq_dec l' l); [subst; apply wf_find_fun; auto|].
      unfold find_fun; rewrite find_drop; auto.
      unfold beq; clarify.
    Qed.      

    Lemma wf_find_loc : forall P1 l f params G P2 
      (Hwf : wf_prog (P1 ++ (l, f, params, G) :: P2)),
      find_loc f (P1 ++ (l, f, params, G) :: P2) = Some l.
    Proof.
      unfold find_loc; clarsimp.
      exists (l, f, params, G); split; auto.
      unfold wf_prog in Hwf.
      specialize (Hwf (length P1)); rewrite nth_error_split in Hwf; clarsimp.
      destruct (find (fun x => beq f (snd (fst (fst x)))) P1) eqn: find.
      { exploit @find_nth_error; eauto; intros [j [? [Hfound Hcond]]].
        specialize (Hwf2 j); rewrite nth_error_app in Hwf2; clarify.
        destruct p as (((l', f'), params'), G');
          specialize (Hwf2 _ _ _ _ Hfound); clarify.
        unfold beq in Hcond; clarify. 
        exfalso; apply (lt_irrefl _ l0).
      }
      unfold beq; clarify.
    Qed.

    Lemma wf_find_name : forall P1 l f params G P2 
      (Hwf : wf_prog (P1 ++ (l, f, params, G) :: P2)),
      find_name l (P1 ++ (l, f, params, G) :: P2) = Some f.
    Proof.
      unfold find_name; clarsimp.
      exists (l, f, params, G); split; auto.
      unfold wf_prog in Hwf.
      specialize (Hwf (length P1)); rewrite nth_error_split in Hwf; clarsimp.
      destruct (find (fun x => beq l (fst (fst (fst x)))) P1) eqn: find.
      { exploit @find_nth_error; eauto; intros [j [? [Hfound Hcond]]].
        specialize (Hwf2 j); rewrite nth_error_app in Hwf2; clarify.
        destruct p as (((l', f'), params'), G'); 
          specialize (Hwf2 _ _ _ _ Hfound); clarify.
        unfold beq in Hcond; clarify. 
        exfalso; apply (lt_irrefl _ l0). }
      unfold beq; clarify.
    Qed.

    Lemma wf_find_graph : forall P1 l f params G P2 
      (Hwf : wf_prog (P1 ++ (l, f, params, G) :: P2)),
      find_graph f (P1 ++ (l, f, params, G) :: P2) = Some G.
    Proof.
      unfold find_graph; clarsimp.
      exists (l, f, params, G); split; auto.
      unfold wf_prog in Hwf.
      specialize (Hwf (length P1)); rewrite nth_error_split in Hwf; clarsimp.
      destruct (find (fun x => beq f (snd (fst (fst x)))) P1) eqn: find.
      { exploit @find_nth_error; eauto; intros [j [? [Hfound Hcond]]].
        specialize (Hwf2 j); rewrite nth_error_app in Hwf2; clarify.
        destruct p as (((l', f'), params'), G'); 
          specialize (Hwf2 _ _ _ _ Hfound); clarify.
        unfold beq in Hcond; clarify. 
        exfalso; apply (lt_irrefl _ l0). }
      unfold beq; clarify.
    Qed.

    Lemma wf_replace : forall P (Hwf : wf_prog P)
      n l f params G (Hnth : nth_error P n = Some (l, f, params, G))
      params' G' (Hwf_G' : wf_CFG G'),
      wf_prog (replace P n (l, f, params', G')).
    Proof.
      unfold wf_prog; clarify.
      specialize (Hwf i).
      destruct (lt_dec n (length P)); [|rewrite replace_over in *; 
        rewrite replace_over in Hi; clarsimp].
      rewrite nth_error_replace in Hi; auto.
      destruct (eq_dec n i); clarify.
      + specialize (Hwf _ _ _ _ Hnth); clarify.
        rewrite nth_error_replace in Hj; clarify; eauto.
      + specialize (Hwf _ _ _ _ Hi); clarify.
        rewrite nth_error_replace in Hj; destruct (eq_dec n j); clarify;
          eauto.
    Qed.

  End CFGs.

  Global Instance o_Z_eq : EqDec_eq (option Z).
  Proof. eq_dec_inst. Qed.
    
  Definition is_true v :=
    if eq_dec (concrete_int v) (Some 1) then true else false.

  Variable (cmp_ptr : cmp -> ref -> ref -> data).

  Section Semantics.
    Context {TGT : Target}.

    Section Exp_Semantics.
      Definition env := ident -> option const. (* use map? *)
      Definition start_env : env := fun x => None.
      Definition upd {A} (f : ident -> option A) := 
        fun x v y => if eq_dec y x then Some v else f y.

      Definition eval_expr env gt e : option const := match e with
      | Local i => env i
      | Const c => Some c
      | Global i => gt i
      end.

      Fixpoint eval_exprs env gt es := match es with
      | [] => Some []
      | e :: rest => match (eval_expr env gt e, eval_exprs env gt rest) with
                     | (Some v, Some vs) => Some (v :: vs)
                     | _ => None
                     end
      end.
      Lemma eval_exprs_spec : forall env gt es vs
        (Heval : eval_exprs env gt es = Some vs),
        Forall2 (fun e v => eval_expr env gt e = Some v) es vs.
      Proof. induction es; clarify. Qed.

      Fixpoint eval_exprs_to_ints env gt es := match es with
      | [] => Some []
      | e :: rest => match (eval_expr env gt e, eval_exprs_to_ints env gt rest) 
                     with
                     | (Some (Int_c v), Some vs) => Some (v :: vs)
                     | _ => None
                     end
      end.
      Lemma eval_exprs_to_ints_spec : forall env gt es vs
        (Heval : eval_exprs_to_ints env gt es = Some vs),
        Forall2 (fun e v => eval_expr env gt e = Some (Int_c v)) es vs.
      Proof. 
        induction es; clarify.
        destruct x; clarify.
      Qed.

(*      Definition zero_tryte := Tryte Zero Zero Zero Zero Zero Zero Zero Zero.
      Definition one_tryte := Tryte Zero Zero Zero Zero Zero Zero Zero One.
      Definition undef_tryte := Tryte Zero Zero Zero Zero Zero Zero Zero Undef.*)

(*      Global Instance o_list_trit_eq : EqDec_eq (option (list trit)).
      Proof. eq_dec_inst. Qed.*)
(*      Lemma eq_true : forall v1 v2 v3,
        (do_cmp Eq v1 v2 = Some v3 /\ is_true v3 = true) <-> v1 = v2.
      Proof.
        intros; rewrite <- (do_eq _ _ v3); unfold is_true; split; clarify.
      Qed.*)

(*      Definition ref_cmp (p1 p2 : ref) := match p1, p2 with
      | (b, o, n), (b', o', n') => 
          if eq_dec b b' then if is_true Eq o o'
                         then if eq_dec n n' then One else Zero else Zero
          else if is_true Slt o (inject_nat n)
               then if eq_dec (do_cmp Slt o' (encode_nat n' (8 * ptr_size)))
                              (Some [One]) 
               then Zero else Undef else Undef
      end.*)

(*      Definition cmp_ptr cmp (v1 v2 : ref) := match cmp with
      | Eq => ref_cmp v1 v2
      | Ne => neg_trit (ref_cmp v1 v2)
      | _ => Undef
      end.*)

      Definition eval_cmp env gt cmp e1 e2 :=
        match (eval_expr env gt e1, eval_expr env gt e2) with
        | (Some (Int_c v1), Some (Int_c v2)) => do_cmp cmp v1 v2
        | (Some (Pointer_c v1), Some (Pointer_c v2)) =>
            Some (cmp_ptr cmp v1 v2)
        | _ => None
        end.

      Definition eval_is_zero env gt e := 
        eval_cmp env gt Eq e (Const (Int_c (inject_int 0))).

      Definition eval_op env gt op e1 e2 :=
        match (eval_expr env gt e1, eval_expr env gt e2) with
        | (Some (Int_c v1), Some (Int_c v2)) => do_op op v1 v2
        | _ => None
        end.

      Fixpoint init_env params args := match (params, args) with
      | ([], []) => Some start_env
      | (x :: params', v :: args') => match init_env params' args' with
                                      | Some env' => Some (upd env' x v)
                                      | _ => None
                                      end
      | _ => None
      end.
    End Exp_Semantics.

    Variable P : prog.

    Definition frame := (ident * node * ident * env * list block)%type.
    Definition base_config :=
      (ident * node * node * env * list frame * list block)%type.
    Inductive config : Type := 
    | Normal : base_config -> config
    | Error : config.

    Definition init_config (c : config) := match c with 
    | Normal (f, p0, p, e, [], []) => 
        match find_graph f P with
        | Some G => if eq_dec p (Start G) then true else false
        | None => false
        end
    | _ => false
    end.

    Definition start_call v vs := match v with Pointer_c ptr =>
      match find_fun ptr P with
      | Some (f, params, G') => match init_env params vs with
                             | Some env' => Some (f, G', env')
                             | _ => None
                             end
      | _ => None
      end
    | _ => None
    end.

    Lemma start_call_graph : forall v vs f G env (Hwf : wf_prog P)
      (Hstart_call : start_call v vs = Some (f, G, env)),
      find_graph f P = Some G.
    Proof.
      unfold start_call; clarify.
      destruct v; clarsimp.
      destruct x as ((?, ?), ?); clarsimp.
      eapply find_fun_graph; eauto.
    Qed.

    Inductive step_label := Out (v : const) | Op (a : LLVM_access).
    Fixpoint get_out l := match l with 
    | [] => []
    | Out v :: rest => v :: get_out rest
    | Op _ :: rest => get_out rest
    end.
    Fixpoint get_ops l := match l with 
    | [] => []
    | Out _ :: rest => get_ops rest
    | Op a :: rest => a :: get_ops rest
    end.

    Lemma get_out_app : forall l l', 
      get_out (l ++ l') = get_out l ++ get_out l'.
    Proof.
      induction l; clarify.
      destruct a; clarify; rewrite IHl; auto.
    Qed.

    Lemma get_ops_app : forall l l', 
      get_ops (l ++ l') = get_ops l ++ get_ops l'.
    Proof.
      induction l; clarify.
      destruct a; clarify; rewrite IHl; auto.
    Qed.
    Hint Rewrite get_out_app get_ops_app : minillvm.

    Fixpoint interval n m := match m with
    | O => []
    | S j => if le_lt_dec n j then interval n j ++ [j] else []
    end.

    (* add more errors *)
    Inductive step (gt : env) : config -> list step_label -> config -> Prop :=
    | assign : forall f G p0 p env st al x op ty e1 e2 v 
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Assign x op ty e1 e2) (Hnot_exit : p <> Exit G)
         (Hop : eval_op env gt op e1 e2 = Some v),
        step gt (Normal (f, p0, p, env, st, al)) [] 
                (Normal (f, p, next_node G Seq p, upd env x (Int_c v), st, al))
    | icmp : forall f G p0 p env st al x cmp ty e1 e2 v 
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = ICmp x cmp ty e1 e2) (Hnot_exit : p <> Exit G)
         (Hcmp : eval_cmp env gt cmp e1 e2 = Some v),
        step gt (Normal (f, p0, p, env, st, al)) [] 
                (Normal (f, p, next_node G Seq p, upd env x (Int_c v), st, al))
    | br_false : forall f G p0 p env st al e v 
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Br_i1 e) (Hnot_exit : p <> Exit G) 
         (Hcmp : eval_is_zero env gt e = Some v) (Hfalse : v <> inject_int 0),
        step gt (Normal (f, p0, p, env, st, al)) []
                (Normal (f, p, next_node G F p, env, st, al))
    | br_true : forall f G p0 p env st al e v 
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Br_i1 e) (Hnot_exit : p <> Exit G) 
         (Hcmp : eval_is_zero env gt e = Some v) (Htrue : v <> inject_int 1),
        step gt (Normal (f, p0, p, env, st, al)) [] (Normal (f, p, next_node G T p, env, st, al))
    | br_label : forall f G p0 p env st al (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Br_label) (Hnot_exit : p <> Exit G),
        step gt (Normal (f, p0, p, env, st, al)) []
                (Normal (f, p, next_node G Seq p, env, st, al))
    | alloca : forall f G p0 p env st al x ty b ops
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Alloca x ty) (Hnot_exit : p <> Exit G)
         (Halloc : mk_alloc ty b = ops),
        step gt (Normal (f, p0, p, env, st, al)) (map Op ops)
                (Normal (f, p, next_node G Seq p, 
                         upd env x (Pointer_c (b, inject_int 0, 
                                               size_of ty)), st, b :: al))
    | gep : forall f G p0 p env st al x ty1 ty2 e es b o n ind off v
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Gep x ty1 ty2 e es) (Hnot_exit : p <> Exit G)
         (Hbase : eval_expr env gt e = Some (Pointer_c (b, o, n)))
         (Hind : Forall2 (fun a i => eval_expr env gt a = Some (Int_c i))
                         (map snd es) ind)
         (Hoff : compute_offset o (Pointer_ty ty1) ind = Some off) 
         (Hext : v = Pointer_c (b, off, n)),
        step gt (Normal (f, p0, p, env, st, al)) [] 
                (Normal (f, p, next_node G Seq p, upd env x v, st, al))
    | bitcast : forall f G p0 p env st al ty1 e ty2
         (Hgraph : find_graph f P = Some G)
         (Hinstr : Label G p = Bitcast ty1 e ty2) (Hnot_exit : p <> Exit G),
        step gt (Normal (f, p0, p, env, st, al)) []
                (Normal (f, p, next_node G Seq p, env, st, al))
    | load : forall f G p0 p env st al x ty e b o n off v ops
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Load x ty e) (Hnot_exit : p <> Exit G)
         (Htarget : eval_expr env gt e = Some (Pointer_c (b, o, n)))
         (Hrealize : realize_data o off)
         (Hin : off >= 0 /\ off < Z_of_nat n)
         (Hread : mk_read ty b (nat_of_Z off) v = Some ops),
(* Nondeterministically realize the offset. But realizing the offset to
   an invalid location should be a different kind of error than guessing
   the wrong value... *)
        step gt (Normal (f, p0, p, env, st, al)) (map Op ops)
                (Normal (f, p, next_node G Seq p, upd env x v, st, al))
    | store : forall f G p0 p env st al ty1 e1 ty2 e2 v b o n off ops
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Store ty1 e1 ty2 e2) (Hnot_exit : p <> Exit G)
         (Hval : eval_expr env gt e1 = Some v)
         (Htarget : eval_expr env gt e2 = Some (Pointer_c (b, o, n)))
         (Hrealize : realize_data o off)
         (Hin : off >= 0 /\ off < Z_of_nat n)
         (Hwrite : mk_write ty1 b (nat_of_Z off) v = Some ops),
        step gt (Normal (f, p0, p, env, st, al)) (map Op ops)
                (Normal (f, p, next_node G Seq p, env, st, al))
    | store_fail : forall f G p0 p env st al ty1 e1 ty2 e2
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Store ty1 e1 ty2 e2) (Hnot_exit : p <> Exit G)
         (Hfail : (forall v', eval_expr env gt e1 <> Some v') \/
           (forall p, eval_expr env gt e2 <> Some (Pointer_c p))),
        step gt (Normal (f, p0, p, env, st, al)) [] Error
    | cmpxchg_eq : forall f G p0 p env st al x ty1 e1 ty2 e2 ty3 e3 b o n off
         rops wops v vw
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Cmpxchg x ty1 e1 ty2 e2 ty3 e3)
         (Hnot_exit : p <> Exit G) 
         (Htarget : eval_expr env gt e1 = Some (Pointer_c (b, o, n)))
         (Hrealize : realize_data o off)
         (Hin : off >= 0 /\ off < Z_of_nat n)
         (Hcheck : eval_expr env gt e2 = Some v)
         (Hread : mk_read ty1 b (nat_of_Z off) v = Some rops)
         (Hval : eval_expr env gt e3 = Some vw)
         (Hwrite : mk_write ty3 b (nat_of_Z off) vw = Some wops),
        step gt (Normal (f, p0, p, env, st, al)) (map Op (rops ++ wops))
          (Normal (f, p, next_node G Seq p, upd env x v, st, al))
    | cmpxchg_no : forall f G p0 p env st al x ty1 e1 ty2 e2 ty3 e3 b o n off
         rops v vc vw
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Cmpxchg x ty1 e1 ty2 e2 ty3 e3)
         (Hnot_exit : p <> Exit G) 
         (Htarget : eval_expr env gt e1 = Some (Pointer_c (b, o, n)))
         (Hrealize : realize_data o off)
         (Hin : off >= 0 /\ off < Z_of_nat n)
         (Hcheck : eval_expr env gt e2 = Some vc)
         (Hread : mk_read ty1 b (nat_of_Z off) v = Some rops)
         (Hfail : eval_cmp env gt Eq (Const vc) (Const v) <> Some (inject_int 1))
         (Hval : eval_expr env gt e3 = Some vw),
        step gt (Normal (f, p0, p, env, st, al)) (map Op rops)
                (Normal (f, p, next_node G Seq p, upd env x v, st, al))
    | phi : forall f G p0 p env st al x ty vals e v
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Phi x ty vals) (Hnot_exit : p <> Exit G) 
         (Hlookup : NodeMap.find p0 vals = Some e) 
         (Hval : eval_expr env gt e = Some v),
        step gt (Normal (f, p0, p, env, st, al)) []
                (Normal (f, p, next_node G Seq p, upd env x v, st, al))
    | call : forall f G p0 p env st al x ty e args v vs f' G' env' 
         (Hgraph : find_graph f P = Some G)
         (Hinstr : Label G p = Call x ty e args) (Hnot_exit : p <> Exit G)
         (Htarget : eval_expr env gt e = Some v)
         (Hargs : eval_exprs env gt args = Some vs)
         (Hcall : start_call v vs = Some (f', G', env')),
        step gt (Normal (f, p0, p, env, st, al)) []
                (Normal (f', p, Start G', env', 
                         (f, next_node G Seq p, x, env, al) :: st, []))
    | ret_pop : forall f G p0 p env ret_f ret_addr ret_var ret_env ret_al st al 
         ty e v ops (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Ret ty e) (Hnot_exit : p <> Exit G) 
         (Hval : eval_expr env gt e = Some v)
         (Hfree : ops = map (fun a => Op (MFree a)) al),
        step gt (Normal (f, p0, p, env, 
                         (ret_f, ret_addr, ret_var, ret_env, ret_al) :: st, al))
                ops
                (Normal (ret_f, p, ret_addr, upd ret_env ret_var v, st, ret_al))
    | ret_main : forall f G p0 p env al ty e v ops
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Ret ty e) (Hnot_exit : p <> Exit G) 
         (Hval : eval_expr env gt e = Some v)
         (Hfree : ops = map (fun a => Op (MFree a)) al),
        step gt (Normal (f, p0, p, env, [], al)) ops
                (Normal (f, p, Exit G, env, [], []))
    | out : forall f G p0 p env st al
         (Hgraph : find_graph f P = Some G) e (Hinstr : Label G p = Output e) 
         (Hnot_exit : p <> Exit G) v (Hval : eval_expr env gt e = Some v),
        step gt (Normal (f, p0, p, env, st, al)) [Out v]
                (Normal (f, p, next_node G Seq p, env, st, al))
    | error : forall k, step gt Error k Error.
    Hint Constructors step.

    Global Instance nat_eq : @EqDec nat eq eq_equivalence.
    Proof. eq_dec_inst. Qed.

    Inductive mem_step gt : (config * mem) -> list const ->
      (config * mem) -> Prop :=
    | step_once : forall m c l c' (Hstep : step gt c l c')
        (Hmem : can_do_ops m (get_ops l)), 
       mem_step gt (c, m) (get_out l) (c', m ++ get_ops l).

    Lemma step_once' : forall gt c m l c' m' (Hstep : step gt c l c')
      (Hmem : can_do_ops m (get_ops l)) k, m' = m ++ get_ops l ->
      k = get_out l -> mem_step gt (c, m) k (c', m').
    Proof. clarify; apply step_once; auto. Qed.

    Lemma step_consistent : forall m m' (Hcon : consistent m)
      gt c l c' (Hstep : mem_step gt (c, m) l (c', m')), 
      consistent m'.
    Proof.
      intros; inversion Hstep; clarify.
    Qed.

    Typeclasses eauto := 2.
(*    Lemma get_frees : forall al, get_ops (make_free al) =
      map (fun l => MFree l) al.
    Proof. induction al; clarsimp. Qed.*)

    Lemma get_ops_map_ops : forall k, get_ops (map Op k) = k.
    Proof. induction k; clarsimp. Qed.

(*    Lemma get_ops_comb_ops : forall c k k', get_ops
      (map (fun a : loc * sconst => Op (c (fst a) (snd a))) (combine k k')) =
      map (fun a : loc * sconst => (c (fst a) (snd a))) (combine k k').
    Proof. 
      induction k; clarify.
      destruct k'; clarify.
      rewrite IHk; auto.
    Qed.      *)

    Lemma get_out_map_ops : forall k, get_out (map Op k) = [].
    Proof. induction k; clarsimp. Qed.

    Lemma get_ops_map_out : forall k, get_ops (map Out k) = [].
    Proof. induction k; clarify. Qed.

    Lemma get_out_map_out : forall k, get_out (map Out k) = k.
    Proof. induction k; clarsimp. Qed.

    Lemma mem_step_error : forall gt m k, consistent m ->
      mem_step gt (Error, m) k (Error, m).
    Proof.
      intros; exploit step_once; eauto 2.
      - instantiate (1 := map Out k); rewrite get_ops_map_out; clarify.
        unfold can_do_ops; autorewrite with list; eauto.
      - rewrite get_ops_map_out, get_out_map_out; clarsimp; eauto.
    Qed.

(*    Lemma step_no_cast : forall gt c k c' (Hstep : step gt c k c'),
      Forall (fun x => is_mcast x = false) (get_ops k).
    Proof. 
      intros; inversion Hstep; clarify; try (
        try (rewrite get_ops_map_ops); try (rewrite get_ops_comb_ops);
        rewrite Forall_forall; intros; rewrite in_map_iff in *; clarify).
      rewrite get_ops_app, get_ops_comb_ops; rewrite get_ops_comb_ops.
      rewrite Forall_forall; intros; rewrite in_app in *.
      destruct H; rewrite in_map_iff in *; clarify.
    Qed.

    Lemma mstep_no_cast : forall gt C C' k (Hmstep : mem_step gt C k C')
      (Hno_cast : Forall (fun x => is_mcast x = false) (snd C)),
      Forall (fun x => is_mcast x = false) (snd C').
    Proof.
      intros; inversion Hmstep; clarify.
      rewrite Forall_app; exploit step_no_cast; eauto; clarify;
        rewrite Forall_rev; auto.
    Qed.

    Lemma step_star_no_cast : forall gt C C' tr 
      (Hrtc : rtc (mem_step gt) C tr C')
      (Hcon : consistent(ML := ML) (snd C) = true)
      (Hno_cast : Forall (fun x => is_mcast x = false) (snd C)),
      consistent(ML := ML) (snd C') = true /\
      Forall (fun x => is_mcast x = false) (snd C').
    Proof.
      intros ? ? ? ? ?; induction Hrtc; clarify.
      destruct s as (c, m); destruct s' as (c', m'); clarify;
        exploit step_consistent; eauto 2; exploit mstep_no_cast; eauto.
    Qed.*)
    
    Lemma mem_step_trace : forall gt C tr C' (Hrtc : rtc (mem_step gt) C tr C'),
      exists tr', rtc (step gt) (fst C) tr' (fst C') /\ get_out tr' = tr.
    Proof.
      intros; induction Hrtc; clarify; eauto.
      inversion Hstep; clarify.
      eexists; split; [eapply rtc_step; eauto | clarify].
      autorewrite with minillvm; auto.
    Qed.

    (* TODO: Coinduction! *)
    Definition traces gt tr := exists c0, init_config c0 = true /\
      traces_from (mem_step gt) (c0, []) tr.

    Definition reachable gt C := exists c0, init_config c0 = true /\
      exists tr, rtc (mem_step gt) (c0, []) tr C.

    Lemma reachable_base : forall gt c0 (Hinit : init_config c0 = true),
      reachable gt (c0, []).
    Proof. unfold reachable; eauto. Qed.
    Hint Resolve reachable_base.

    Lemma reachable_step : forall gt C C' (Hreach : reachable gt C)
      l (Hstep : mem_step gt C l C'), reachable gt C'.
    Proof.
      unfold reachable; intros; destruct Hreach as [? [? [tr ?]]].
      eexists; split; eauto.
      exists (tr ++ l); eapply rtc_rev_step; eauto.
    Qed.

    Definition fun_of (c : base_config) :=
      match c with (f, _, _, _, _, _) => f end.
    Definition node_of (c : base_config) := 
      match c with (_, _, p, _, _, _) => p end.
    Definition env_of (c : base_config) :=
      match c with (_, _, _, env, _, _) => env end.
    Definition stack_of (c : base_config) := 
      match c with (_, _, _, _, st, _) => st end.
    Definition update_node (c : config) (n : node) := match c with 
      | Normal (f, p0, p, env, st, al) => Normal (f, p0, n, env, st, al) 
      | Error => Error 
      end.
    Definition in_graph f n := match find_graph f P with
      | Some G => NodeSet.In n (Nodes G)
      | None => False
      end.
    Definition safe c := match c with 
    | Normal c => in_graph (fun_of c) (node_of c) /\
        Forall (fun fr => match fr with (f, p, _, _, _) => in_graph f p end)
               (stack_of c)
    | Error => True
    end.

    Context (Hwf : wf_prog P).

    Lemma init_safe : forall c0 (Hinit : init_config c0 = true),
      safe c0.
    Proof.
      unfold init_config, safe; destruct c0; clarify.
      destruct b as (((((f, ?), p), ?), ?), ?); clarify.
      destruct (find_graph f P) eqn: Hgraph; clarify.
      unfold in_graph; rewrite Hgraph; exploit find_wf_graph; eauto; 
        intro HG; inversion HG; auto.
    Qed.

    Lemma step_safe : forall gt c l c' (Hstep : step gt c l c')
      (Hsafe : safe c), safe c'.
    Proof.
      intros; unfold safe, in_graph in *; inversion Hstep; clarify; 
        rewrite Hgraph in *;
        try (apply wf_next_in; auto; eapply find_wf_graph; eauto).
      - exploit start_call_graph; eauto; intro Hgraph'; rewrite Hgraph'.
        exploit find_wf_graph; eauto; intro HG'; inversion HG'; clarify.
        constructor; auto.
        rewrite Hgraph; apply wf_next_in; auto; eapply find_wf_graph; eauto.
      - inversion Hsafe2; clarify.
      - exploit find_wf_graph; eauto; intro HG; inversion HG; auto.
    Qed.

    Lemma mstep_safe : forall gt c m l c' m' 
      (Hmstep : mem_step gt (c, m) l (c', m')) (Hsafe : safe c), safe c'.
    Proof. intros; inversion Hmstep; eapply step_safe; eauto. Qed.

    Lemma step_star_safe : forall gt C tr C' 
      (Hstep_star : rtc (mem_step gt) C tr C') (Hsafe : safe (fst C)), 
      safe (fst C').
    Proof.
      intros; induction Hstep_star; clarify.
      destruct s, s'; exploit mstep_safe; eauto.
    Qed.

    Corollary reachable_safe : forall gt c m (Hreach : reachable gt (c, m)),
      safe c.
    Proof.
      unfold reachable; intros; destruct Hreach as [c0 [Hinit [tr Hrtc]]].
      exploit step_star_safe; eauto.
      simpl; apply init_safe; auto.
    Qed.

    Section Exec.
      Context (MLI : @ML_impl _ _ _ ML).

      Fixpoint read_num mv n :=
        match n with
        | O => Some []
        | S n' =>
            match mv with
            | Num d :: rest =>
                match read_num rest n' with
                | Some ds => Some (d :: ds)
                | None => None
                end
            | _ => None
            end
        end.

      Definition raise_int (n : nat) (o : nat) (mv : list mem_data) :=
        read_num (skipn o mv) (size_of (Int_ty n)).

      Fixpoint read_val (t : type) (o0 : nat) (o : nat) (mv : list mem_data) :=
        let o' := padn o (first_align t) in
        match t with
        | Int_ty n =>
            match raise_int n (o' - o0) mv with
            | Some i => Some (Int_c i)
            | None => None
            end
        | Pointer_ty _ =>
            match nth_error mv o' with
            | Some (PtrFrag n p) => Some (Pointer_c p)
            | _ => None
            end
        | Array_ty n t =>
            match (fix read_vals n o :=
                     match n with
                     | O => Some []
                     | S n' =>
                       let o' := padn o (first_align t) in
                       match (read_val t o0 o' mv,
                              read_vals n' (o' + size_of t)%nat) with
                       | (Some v, Some vs) => Some (v :: vs)
                       | _ => None
                       end
                     end) n o with
            | Some vs => Some (Complex_c vs)
            | None => None
            end
        | Struct_ty ts =>
            match (fix read_vals ts o :=
                     match ts with
                     | [] => Some []
                     | t :: trest =>
                       let o' := padn o (first_align t) in
                       match (read_val t o0 o' mv,
                              read_vals trest (o' + size_of t)%nat) with
                       | (Some v, Some vs) => Some (v :: vs)
                       | _ => None
                       end
                     end) ts o with
            | Some vs => Some (Complex_c vs)
            | None => None
            end
        end.

      Fixpoint read_bytes (m : mem) (p : ptr block) n := let (b, o) := p in
        match n with
        | O => Some []
        | S n' =>
            match (read m p, read_bytes m (b, S o) n') with
            | (Some v, Some vs) => Some (v :: vs)
            | _ => None
            end
        end.

      Definition read_val' m ty (p : ptr block) := let (b, o) := p in
        let o' := padn o (first_align ty) in
        match read_bytes m (b, o') (size_of ty) with
        | Some mv => read_val ty o' o' mv
        | None => None
        end.

      Instance oconst_eq : @EqDec (option const) eq eq_equivalence.
      Proof.
        repeat intro.
        destruct x; destruct y; clarify; try (right; clarify; fail).
        destruct (eq_dec c c0); clarify; unfold equiv; right; intro; clarify.
      Qed.

(*      (* When decisions must be made, treat undef as 0. *)
      Fixpoint decode_0_trits' ts :=
        match ts with
        | [] => 0
        | One :: rest => two_power_nat (length rest) + decode_0_trits' rest
        | _ :: rest => decode_0_trits' rest
        end.

      Definition decode_0_trits ts :=
        match ts with
        | [] => 0
        | [One] => 1
        | [_] => 0
        | One :: rest => decode_0_trits' rest - two_power_nat (length rest)
        | _ :: rest => decode_0_trits' rest
        end.

      Lemma decode_0_realize' : forall ts, 
        realize_trits' ts (decode_0_trits' ts).
      Proof.
        induction ts; clarify.
        destruct a; eauto; clarify.
      Qed.

      Lemma decode_0_realize : forall ts, 
        realize_trits ts (decode_0_trits ts).
      Proof.
        destruct ts; clarify.
        destruct t; clarify.
        - eapply realize_pos; clarify; apply decode_0_realize'.
        - eapply realize_neg; clarify; apply decode_0_realize'.
        - eapply realize_pos; clarify; apply decode_0_realize'.
      Qed.
      Hint Resolve decode_0_realize' decode_0_realize.

      Corollary decode_0_decode : forall ts v,
        decode_trits ts = Some v -> v = decode_0_trits ts.
      Proof.
        intros; generalize (decode_0_realize ts); intro Hrealize.
        rewrite decode_realize in Hrealize; eauto.
      Qed.*)

      Variable (realize_fun : data -> Z).
      Hypothesis (realize_fun_correct : 
        forall d, realize_data d (realize_fun d)).

      Definition do_step gt (C : config * mem) :=
        match C with (Normal (f, p0, p, env, st, al), m) =>
        match find_graph f P with
        | Some G => if eq_dec p (Exit G) then None else
            match Label G p with
            | Assign x op ty e1 e2 =>
                match eval_op env gt op e1 e2 with
                | Some v => Some ([], Normal (f, p, next_node G Seq p, upd env x (Int_c v), st, al))
                | None => None
                end
            | ICmp x cmp ty e1 e2 =>
                match eval_cmp env gt cmp e1 e2 with
                | Some v => Some ([], Normal (f, p, next_node G Seq p, upd env x (Int_c v), st, al))
                | None => None
                end
            | Br_i1 e =>
                match eval_is_zero env gt e with
                | Some v => Some ([], Normal (f, p, next_node G (if is_true v then F else T) p, env, st, al))
                | None => None
                end
            | Br_label => Some ([], Normal (f, p, next_node G Seq p, env, st, al))
            | Alloca x ty =>
                match get_free m (size_of ty) with
                | Some b => Some (map Op (mk_alloc ty b), Normal
                    (f, p, next_node G Seq p, 
                     upd env x (Pointer_c (b, inject_int 0, size_of ty)), st, b :: al))
                | None => None
                end
            | Gep x ty1 ty2 e es =>
                match eval_expr env gt e with
                | Some (Pointer_c (b, o, n)) =>
                    match eval_exprs_to_ints env gt (map snd es) with
                    | Some ind =>
                        match compute_offset o (Pointer_ty ty1) ind 
                        with
                        | Some off => Some ([], Normal (f, p, next_node G Seq p, upd env x (Pointer_c (b, off, n)), st, al))
                        | None => None
                        end
                    | None => None
                    end
                | _ => None
                end
            | Bitcast _ _ _ => Some ([], Normal (f, p, next_node G Seq p, env, st, al))
            | Load x ty e =>
                match eval_expr env gt e with
                | Some (Pointer_c (b, o, n)) =>
                    let off := realize_fun o in
                    if zle 0 off then if zlt off (Z_of_nat n) then
                      match read_val' m ty (b, nat_of_Z off) with
                      | Some v =>
                          match mk_read ty b (nat_of_Z off) v with
                          | Some ops => Some (map Op ops, Normal (f, p, next_node G Seq p, upd env x v, st, al))
                          | None => None
                          end
                      | None => None
                      end
                    else None else None
                | _ => None
                end
            | Store ty1 e1 ty2 e2 =>
                match (eval_expr env gt e1, eval_expr env gt e2) with
                | (Some v, Some (Pointer_c (b, o, n))) =>
                    let off := realize_fun o in
                    if zle 0 off then if zlt off (Z_of_nat n) then
                      match mk_write ty1 b (nat_of_Z off) v with
                      | Some ops => Some (map Op ops, Normal (f, p, next_node G Seq p, env, st, al))
                      | None => None
                      end
                    else None else None
                | _ => Some ([], Error)
                end
            | Cmpxchg x ty1 e1 ty2 e2 ty3 e3 =>
                match (eval_expr env gt e1, eval_expr env gt e2, 
                       eval_expr env gt e3) with
                | (Some (Pointer_c (b, o, n)), Some vc, Some vw) =>
                    let off := realize_fun o in
                    if zle 0 off then if zlt off (Z_of_nat n) then
                      match read_val' m ty1 (b, nat_of_Z off) with
                      | Some v =>
                          match mk_read ty1 b (nat_of_Z off) v with
                          | Some rops =>
                              if eq_dec v vc then
                                match mk_write ty3 b (nat_of_Z off) vw with
                                | Some wops => Some (map Op (rops ++ wops), Normal (f, p, next_node G Seq p, upd env x v, st, al))
                                | None => None
                                end
                              else match eval_cmp env gt Eq (Const vc) (Const v) with
                              | Some vr => if is_true vr then None else Some (map Op rops, Normal (f, p, next_node G Seq p, upd env x v, st, al))
                              | None => None
                                   end
                          | None => None
                          end
                      | None => None
                      end
                    else None else None
                | _ => None
                end
            | Phi x ty vals =>
                match NodeMap.find p0 vals with
                | Some e =>
                    match eval_expr env gt e with
                    | Some v => Some ([], Normal (f, p, next_node G Seq p, upd env x v, st, al))
                    | None => None
                    end
                | None => None
                end
            | Call x ty e args =>
                match (eval_expr env gt e, eval_exprs env gt args) with
                | (Some v, Some vs) =>
                    match start_call v vs with
                    | Some (f', G', env') => Some ([], Normal (f', p, Start G', env', (f, next_node G Seq p, x, env, al) :: st, []))
                    | _ => None
                    end
                | _ => None
                end
            | Ret ty e =>
                match eval_expr env gt e with
                | Some v => Some (map (fun a => Op (MFree a)) al, Normal
                    match st with
                    | [] => (f, p, Exit G, env, [], [])
                    | (ret_f, ret_addr, ret_var, ret_env, ret_al) :: st =>
                         (ret_f, p, ret_addr, upd ret_env ret_var v, st, ret_al)
                    end)
                | None => None
                end
            | Output e =>
                match eval_expr env gt e with
                | Some v => Some ([Out v], Normal (f, p, next_node G Seq p, env, st, al))
                | None => None
                end
            end
        | None => None
        end
        | (Error, _) => Some ([], Error) end.

      Ltac step_case tac := first [eapply assign; eauto 2; tac 
        | eapply icmp; eauto 2; tac | eapply br_false; eauto 2; tac 
        | eapply br_true; eauto 2; tac | eapply br_label; eauto 2; tac 
        | eapply alloca; eauto 2; tac | eapply gep; eauto 2; tac
        | eapply bitcast; eauto 2; tac
        | eapply load; eauto 2; tac | eapply store; eauto 2; tac
        | eapply store_fail; eauto 2; tac | eapply cmpxchg_eq; eauto 2; tac 
        | eapply cmpxchg_no; eauto 2; tac | eapply phi; eauto 2; tac 
        | eapply call; eauto 2; tac | eapply ret_pop; eauto 2; tac 
        | eapply ret_main; eauto 2; tac | eapply out; eauto 2; tac].

      Lemma do_step_correct : forall gt c m l c'
        (Hdo : do_step gt (c, m) = Some (l, c')), step gt c l c'.
      Proof.
        unfold do_step; clarify.
        destruct c as [(((((f, p0), p), env), st), al)|]; clarify.
        destruct (Label x p) eqn: Hinstr; clarify; try (step_case fail).
        - destruct (is_true x0) eqn: Hzero; [eapply br_false | eapply br_true];
            eauto 2; unfold is_true in Hzero; clarify.
          + clear cond0; intro; clarify; rewrite inject_concrete in *; clarify.
          + clear cond0; intro; clarify; rewrite inject_concrete in *; clarify.
        - exploit alloca; eauto; clarify; eauto.
        - destruct x0; clarify.
          destruct r as ((b, o), z); clarify.
          eapply gep; eauto 2.
          apply eval_exprs_to_ints_spec; auto.
        - destruct x0; clarify.
          destruct r as ((b, o), z); clarify.
          eapply load; eauto 2; omega.
        - destruct (eval_expr env gt e) eqn: He; clarify; 
            [|eapply store_fail; eauto; left; repeat intro; clarify].
          destruct (eval_expr env gt e0) eqn: He0; clarify; 
            [|eapply store_fail; eauto; right; repeat intro; clarify].
          destruct c0; clarify; try (eapply store_fail; eauto; right; 
                                     repeat intro; clarsimp).
          destruct r as ((b, o), z); clarify.
          eapply store; eauto 2; omega.
        - destruct x0; clarify.
          destruct r as ((b, o), z); clarify.
          destruct (eq_dec x2 x0); clarify; 
            [eapply cmpxchg_eq | eapply cmpxchg_no]; eauto 2; try omega.
          unfold is_true in *; clarsimp; intro; clarify.
        - destruct x2 as ((f', G'), env'); clarify; eauto.
        - destruct st; clarify; eauto.
          destruct f0 as ((((?, ?), ?), ?), ?); eauto.
      Qed.

      Definition do_mem_step gt (C : config * mem) :=
        match (C, do_step gt C) with
        | (c, m, Some (l, c')) => 
            if can_do_list m (get_ops l) then
              Some (get_out l, (c', m ++ get_ops l))
            else None
        | _ => None
        end.

      Fixpoint do_mem_steps gt C n :=
        match n with
        | O => Some ([], C)
        | S n' =>
            match do_mem_step gt C with
            | Some (k, C') =>
                match do_mem_steps gt C' n' with
                | Some (k', C'') => Some (k ++ k', C'')
                | None => Some (k, C')
                end
            | None => Some ([], C)
            end
        end.

    End Exec.

  End Semantics.

  Hint Resolve reachable_base.

  Section Simulation.
    Variables (P Q : prog) (TGT : Target).

    Definition simulation (R : config * mem -> config * mem -> Prop) gt :=
      (forall c0, init_config P c0 = true -> 
         exists c0', init_config Q c0' = true /\ R (c0, []) (c0', [])) /\
      forall C C' (Hreach : reachable P gt C)
        (Hreach' : reachable Q gt C') (Hsim : R C C') 
        l C2 (Hstep : mem_step P gt C l C2),
       exists C2', mem_step Q gt C' l C2' /\ R C2 C2'.

    Lemma sim_rtc : forall R gt (Hsim : simulation R gt) c m tr c2 m2
      (Hreach : reachable P gt (c, m)) 
      (Hstep_star : rtc (mem_step P gt) (c, m) tr (c2, m2))
      c' m' (Hreach : reachable Q gt (c', m')) (HR : R (c, m) (c', m')),
      exists c2' m2', rtc (mem_step Q gt) (c', m') tr (c2', m2') /\ 
        reachable P gt (c2, m2) /\ reachable Q gt (c2', m2') /\ 
        R (c2, m2) (c2', m2').
    Proof.
      unfold simulation; intros ? ? [Hbase Hstep] ? ? ? ? ? ? ?;
        induction Hstep_star; clarify.
      - eexists; eexists; split; [apply rtc_refl|]; auto.
      - exploit Hstep; eauto.
        intros [(c2', m2') [? ?]].
        use IHHstep_star; [|eapply reachable_step; eauto].
        specialize (IHHstep_star c2' m2'); use IHHstep_star;
          [use IHHstep_star | eapply reachable_step; eauto].
        destruct IHHstep_star as [c2'' [m2'' [? [? [? ?]]]]].
        exists c2''; exists m2''; repeat split; auto.
        eapply rtc_step; eauto.
    Qed.

    Theorem simulation_refinement : forall R gt (Hsim : simulation R gt) tr,
      traces P gt tr -> traces Q gt tr.
    Proof.
      unfold traces, traces_from, simulation; intros.
      destruct H as [c0 [Hinit [(c, m) Hrtc]]].
      destruct Hsim as [Hbase Hstep]; exploit Hbase; eauto; clarify.
      exploit sim_rtc; eauto.
      { unfold simulation; eauto. }
      clarify; eauto.
    Qed.

    Definition lo_simulation (R : config * mem -> config * mem -> Prop) gt :=
      (forall c0, init_config P c0 = true -> 
         exists c0', init_config Q c0' = true /\ R (c0, []) (c0', [])) /\
      forall C C' (Hreach : reachable P gt C) 
        (Hreach' : reachable Q gt C') (Hsim : R C C')
        l C2 (Hstep : mem_step P gt C l C2),
       (l = [] /\ R C2 C') \/
       exists C2', mem_step Q gt C' l C2' /\ R C2 C2'.

    Lemma lo_sim_rtc : forall R gt (Hsim : lo_simulation R gt) c m tr c2 m2
      (Hreach : reachable P gt (c, m)) 
      (Hstep_star : rtc (mem_step P gt) (c, m) tr (c2, m2))
      c' m' (Hreach : reachable Q gt (c', m')) (HR : R (c, m) (c', m')),
      exists c2' m2', rtc (mem_step Q gt) (c', m') tr (c2', m2') /\ 
        reachable P gt (c2, m2) /\ reachable Q gt (c2', m2') /\ 
        R (c2, m2) (c2', m2').
    Proof.
      unfold lo_simulation; intros ? ? [Hbase Hstep] ? ? ? ? ? ? ?;
        induction Hstep_star; clarify.
      - eexists; eexists; split; [apply rtc_refl|]; auto.
      - use IHHstep_star; [|eapply reachable_step; eauto].
        exploit Hstep; eauto.
        intros [? | [(c2', m2') [? ?]]]; clarify.
        specialize (IHHstep_star c2' m2'); use IHHstep_star;
          [use IHHstep_star | eapply reachable_step; eauto].
        destruct IHHstep_star as [c2'' [m2'' [? [? [? ?]]]]].
        exists c2''; exists m2''; repeat split; auto.
        eapply rtc_step; eauto.
    Qed.

    Theorem lo_simulation_refinement : forall R gt (Hsim : lo_simulation R gt)
      tr, traces P gt tr -> traces Q gt tr.
    Proof.
      unfold traces, traces_from, lo_simulation; intros.
      destruct H as [c0 [Hinit [(c, m) Hrtc]]].
      destruct Hsim as [Hbase Hstep]; exploit Hbase; eauto; clarify.
      exploit lo_sim_rtc; eauto.
      { unfold lo_simulation; eauto. }
      clarify; eauto.
    Qed.

    Definition ro_simulation (R : config * mem -> config * mem -> Prop) gt :=
      (forall c0, init_config P c0 = true ->
         exists c0', init_config Q c0' = true /\ R (c0, []) (c0', [])) /\
      forall C C' (Hreach : reachable P gt C)
        (Hreach' : reachable Q gt C') (Hsim : R C C')
        l C2 (Hstep : mem_step P gt C l C2),
       exists C2', (mem_step Q gt C' l C2' \/ exists C2'', 
         mem_step Q gt C' [] C2'' /\ mem_step Q gt C2'' l C2') /\ 
        R C2 C2'.

    Lemma ro_sim_rtc : forall R gt (Hsim : ro_simulation R gt) c m tr c2 m2
      (Hreach : reachable P gt (c, m)) 
      (Hstep_star : rtc (mem_step P gt) (c, m) tr (c2, m2))
      c' m' (Hreach : reachable Q gt (c', m')) (HR : R (c, m) (c', m')),
      exists c2' m2', rtc (mem_step Q gt) (c', m') tr (c2', m2') /\ 
        reachable P gt (c2, m2) /\ reachable Q gt (c2', m2') /\ 
        R (c2, m2) (c2', m2').
    Proof.
      unfold ro_simulation; intros ? ? [Hbase Hstep] ? ? ? ? ? ? ?;
        induction Hstep_star; clarify.
      - eexists; eexists; split; [apply rtc_refl|]; auto.
      - use IHHstep_star; [|eapply reachable_step; eauto].
        exploit Hstep; eauto.
        intros [(c2', m2') [[? | [(c2'', m2'') [? ?]]] ?]]; clarify.
        + specialize (IHHstep_star c2' m2'); use IHHstep_star;
            [use IHHstep_star | eapply reachable_step; eauto].
          destruct IHHstep_star as [c2'' [m2'' [? [? [? ?]]]]].
          exists c2''; exists m2''; repeat split; auto.
          eapply rtc_step; eauto.
        + specialize (IHHstep_star c2' m2'); use IHHstep_star;
            [use IHHstep_star |].
          destruct IHHstep_star as [c2''' [m2''' [? [? [? ?]]]]].
          exists c2'''; exists m2'''; repeat split; auto.
          eapply rtc_step_silent; eauto.
          eapply rtc_step; eauto.
          { eapply reachable_step; [eapply reachable_step|]; eauto. }
    Qed.

    Theorem ro_simulation_refinement : forall R gt (Hsim : ro_simulation R gt)
      tr, traces P gt tr -> traces Q gt tr.
    Proof.
      unfold traces, traces_from, ro_simulation; intros.
      destruct H as [c0 [Hinit [(c, m) Hrtc]]].
      destruct Hsim as [Hbase Hstep]; exploit Hbase; eauto; clarify.
      exploit ro_sim_rtc; eauto.
      { unfold ro_simulation; eauto. }
      clarify; eauto.
    Qed.

    Definition similar {S L} (init init' : S -> Prop) step step' 
      (T : list L -> Prop) s s' := 
      exists (R : S -> S -> Prop), (forall s s' l, R s s' -> 
         (traces_from step s l \/ traces_from step' s' l) -> T l) /\
      (forall s0, init s0 -> exists s0', init' s0' /\ R s0 s0') /\
      (forall s s' l s2, R s s' /\ step s l s2 -> T l /\ exists s2', 
         step' s' l s2' /\ R s2 s2') /\ R s s'.

    Definition similar_config gt To Tm c c' := 
      similar (fun c => init_config P c = true)
              (fun c => init_config Q c = true) (step P gt) (step Q gt)
              (fun l => To (get_out l) /\ Tm (get_ops l)) c c'.

    Definition step_mem m l m' := can_do_ops m l /\ m' = m ++ l.
    Definition similar_mem T (m m' : mem) := 
      similar (fun m => m = []) (fun m => m = []) step_mem step_mem T m m'.

    Definition similar_state gt T C C' := 
      similar (fun C => init_config P (fst C) = true /\ snd C = [])
              (fun C => init_config Q (fst C) = true /\ snd C = [])
              (mem_step P gt) (mem_step Q gt) T C C'.

    Theorem composition : forall gt To Tm c c' m m'
      (Hc : similar_config gt To Tm c c') (Hm : similar_mem Tm m m'),
      similar_state gt To (c, m) (c', m').
    Proof.
      unfold similar_state, similar_config, similar_mem, similar.
      intros ? ? ? ? ? ? ? [Rc [HTc [Hbasec [Hsimc Hc]]]] 
        [Rm [HTm [Hbasem [Hsimm Hm]]]].
      exists (fun C C' => Rc (fst C) (fst C') /\ Rm (snd C) (snd C')); 
        split; clarify.
      - unfold traces_from in *; destruct H0; clarify;
          exploit mem_step_trace; eauto; clarify.
        + exploit (HTc (fst s)).
          * eauto.
          * left; eexists; eauto.
          * clarify.
        + exploit (HTc (fst s)).
          * eauto.
          * right; eexists; eauto.
          * clarify.
      - split; clarify.
        + exploit Hbasec; eauto.
          intros [c0' ?]; exists (c0', []); split; clarify.
          destruct s0; clarify.
        + inversion H2; clarify.
          exploit Hsimc; eauto.
          intros [HT [c2' [Hstep' HRc']]]; clarify.
          exploit Hsimm; eauto.
          { unfold step_mem; repeat split; eauto. }
          intros [_ [m2' [Hstep_mem' HRm']]].
          exists (c2', m2'); repeat split; auto.
          unfold step_mem in *; clarify.
          destruct s'; apply step_once; clarify.
    Qed.      

    Lemma similar_rtc : forall gt C tr C2
      (Hrtc : rtc (mem_step P gt) C tr C2)
      T C' (Hsim : similar_state gt T C C'),
      exists C2', rtc (mem_step Q gt) C' tr C2' /\
        similar_state gt T C C'.
    Proof.
      intros ? ? ? ? ?; induction Hrtc; clarify.
      - eexists; split; [apply rtc_refl | auto].
      - unfold similar_state, similar in Hsim; 
          destruct Hsim as [R [HT [Hbase [Hsim HR]]]].
        exploit Hsim; eauto; clarify.
        specialize (IHHrtc T0 x); use IHHrtc; clarify.
        eexists; split; [eapply rtc_step|]; eauto.
        unfold similar_state, similar; exists R; auto.        
        { unfold similar_state, similar; exists R; auto. }
    Qed.      

    Theorem similar_refinement : forall gt T C C'
      (Hsim : similar_state gt T C C') tr,
      traces P gt tr -> traces Q gt tr.
    Proof.
      unfold traces, traces_from, similar_state, similar; intros.
      destruct H as [c0 [Hinit [(c, m) Hrtc]]];
        destruct Hsim as [R [? [Hbase [Hsim]]]].
      generalize (Hbase (c0, [])); intro X; use X; destruct X as [(c0', ?) ?];
        clarify.
      exists c0'; clarify.
      exploit similar_rtc; eauto.
      { unfold similar_state, similar; eauto. }
      clarify; eauto.
    Qed.
    
    (* Add error at this level? *)

  End Simulation.

End LLVM.
Arguments Alloca [block] _ _ _.
Arguments Int_c [block] _ _.
Arguments Local [block] _ _.

Extract Constant node => "int".
Extract Inlined Constant node_eq => 
  "(fun a b -> if a = b then Left else Right)".
Extraction "minillvm_bitwise.ml" do_mem_steps.