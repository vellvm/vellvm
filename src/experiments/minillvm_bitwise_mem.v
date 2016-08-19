Require Import ZArith.
Require Import String.
Require Import Program.Wf.
Require Import OrdersEx.
Require Import CpdtTactics.
Require Import Util.
Require Import SetsAndMaps.
Require Import List.
Require Import memory_model.
Require Import Morphisms.
Require Import LTS.
Import ListNotations.
Import Equalities.
Import Bool.
Import CoqEqDec.
Import Coq.Classes.EquivDec.
Import Coqlib.

Require Import linking.linking.

(* Single-threaded MiniLLVM - to be merged with the main file 
   when the memory models are reconciled *)

Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Inductive tri : Set := Yes | No | Maybe.
Definition neg_tri t := match t with
| Yes => No
| No => Yes
| Maybe => Maybe
end.

(* Expected operations on pointers. *)
(* We have two kinds of equality on pointers: a decidable syntactic equality (=)
   and a tri-state semantic equality (aliasing). *)
Section Pointer.
  Variables (config ptr loc : Type).

  Class PtrType {ptr_eq : EqDec_eq ptr} {loc_eq : EqDec_eq loc} := { 
    ptr_eq : ptr -> ptr -> tri; 
    ptr_eq_refl : forall p, ptr_eq p p = Yes; 
    ptr_eq_sym : forall p p', ptr_eq p p' = ptr_eq p' p;
    normalize : config -> ptr -> loc;
    inject : config -> loc -> ptr;
    inject_norm : forall c l, normalize c (inject c l) = l }.
  (* What other assumptions might we want to make? *)
  (* cast from int to ptr? Is this independent of memory? *)
  
End Pointer.

Section Structured.
(* In this version, locations contain small data,
   and the structured pointer unit converts accesses on structured data into
   sequences of small memory ops. *)
(* The weakness of this approach is that all memory steps may perform large 
   numbers of accesses, and we need axioms on them that allow reasoning without
   constraining the possible layouts. *)
  Variables (type loc val mval : Type) 
    (type_eq : EqDec_eq type) (loc_eq : EqDec_eq loc) (mval_eq : EqDec_eq mval).
  
  Definition ptr_path := (type * loc * list Z)%type.

  Global Instance ptr_path_eq : @EqDec ptr_path eq eq_equivalence.
  Proof. eq_dec_inst. Qed.

  Inductive struct_op :=
  | SAlloc (t : type) (l : loc)
  | SFree (t : type) (l : loc)
  | SRead (t : type) (p : ptr_path) (v : val)
  | SWrite (t : type) (p : ptr_path) (v : val).

  Definition loc_of s := match s with
  | SAlloc _ l => l
  | SFree _ l => l
  | SRead _ (_, l, _) _ => l
  | SWrite _ (_, l, _) _ => l
  end.

  Class StructuredPtr (ML : Memory_Layout mval loc_eq) :=
    { can_lower : struct_op -> list (mem_op loc mval) -> Prop;
      (* Is this a reasonable axiom? Would it be if we added a well-aligned
         predicate on locs, or took into account the size of types? *)
      lower_succeeds : forall s, exists ops, can_lower s ops;
      (* How about this? *)
      loc_sep : forall s s' (Hdiff : loc_of s <> loc_of s') ops ops'
        (Hlower : can_lower s ops) (Hlower' : can_lower s' ops')
        x x' (Hin : In x ops) (Hin' : In x' ops'), 
       memory_model.loc_of x <> memory_model.loc_of x';
      read_reads : forall t p v ops (Hlower : can_lower (SRead t p v) ops) x
        (Hin : In x ops), exists l v', x = MRead l v';
      write_writes : forall t p v ops (Hlower : can_lower (SWrite t p v) ops) x
        (Hin : In x ops), exists l v', x = MWrite l v';
      read_written : forall t p v ops (Hlower : can_lower (SWrite t p v) ops)
        v' ops' (Hlower' : can_lower (SRead t p v') ops')
        m (Hcon : consistent (m ++ ops)),
        consistent (m ++ ops ++ ops') <-> v' = v;
      (* Should these ensure that well-typed reads and writes act as expected? 
       *)
      alloc_allows : forall t l ops (Hlower : can_lower (SAlloc t l) ops)
        ops' (Hlower' : can_lower (SFree t l) ops') 
        m (Hcon : consistent (m ++ ops)),
        consistent (m ++ ops ++ ops');
      free_allows : forall t l ops (Hlower : can_lower (SFree t l) ops)
        ops' (Hlower' : can_lower (SAlloc t l) ops') 
        m (Hcon : consistent (m ++ ops)),
        consistent (m ++ ops ++ ops') }.

  Context `{SP : StructuredPtr}.

  (* Derived interface *)
  Lemma loc_comm : forall s1 s2 (Hdiff_loc : loc_of s1 <> loc_of s2)
    ops1 ops2 (Hlower1 : can_lower s1 ops1) (Hlower2 : can_lower s2 ops2) m1 m2,
    consistent (m1 ++ ops1 ++ ops2 ++ m2) <-> 
    consistent (m1 ++ ops2 ++ ops1 ++ m2).
  Proof.
    intros; rewrite loc_comm_ops; [reflexivity|].
    rewrite Forall_forall; repeat intro; rewrite in_map_iff in *; clarify.
    exploit loc_sep; eauto.
  Qed.

  Lemma loc_valid : forall s1 s2 (Hdiff_loc : loc_of s1 <> loc_of s2)
    ops1 ops2 (Hlower1 : can_lower s1 ops1) (Hlower2 : can_lower s2 ops2) m,
    consistent (m ++ ops1 ++ ops2) <-> 
    (consistent (m ++ ops1) /\ consistent (m ++ ops2)).
  Proof.
    intros; apply loc_valid_ops.
    rewrite Forall_forall; repeat intro; rewrite in_map_iff in *; clarify.
    exploit loc_sep; eauto.
  Qed.

  Lemma read_noop : forall t p v ops (Hlower : can_lower (SRead t p v) ops)
    m m2 (Hcon : consistent (m ++ ops)),
    consistent (m ++ ops ++ m2) <-> consistent (m ++ m2).
  Proof.
    intros; apply reads_noops; auto.
    rewrite Forall_forall; repeat intro.
    exploit read_reads; eauto; clarify.
  Qed.

  Inductive can_lower_ops : list struct_op -> list (mem_op loc mval) -> Prop :=
  | lower_nil : can_lower_ops [] []
  | lower_cons : forall s ops sl ops', can_lower s ops -> 
      can_lower_ops sl ops' -> can_lower_ops (s :: sl) (ops ++ ops').
  Hint Constructors can_lower_ops.

End Structured.
Arguments SAlloc [type] [loc] [val] _ _.
Arguments SFree [type] [loc] [val] _ _.
Arguments SRead [type] [loc] [val] _ _ _.
Arguments SWrite [type] [loc] [val] _ _ _.

Section Values.

  Inductive type : Set :=
  | Int_ty : type
  | Pointer_ty : type -> type
  | Complex_ty : list type -> type.
  (* Nested induction nonsense thanks to CPDT *)
  Fixpoint type_ind' (P : type -> Type) (Q : list type -> Type)
    (Hint : P Int_ty) (Hptr : forall t, P t -> P (Pointer_ty t))
    (Hnil : Q nil) (Hcons : forall t rest, P t -> Q rest -> Q (t :: rest))
    (Hcomplex : forall tl, Q tl -> P (Complex_ty tl)) t : P t :=
    match t with
    | Int_ty => Hint
    | Pointer_ty t => Hptr _ (type_ind' P Q Hint Hptr Hnil Hcons Hcomplex t)
    | Complex_ty tl => Hcomplex _ ((fix type_list_ind tl : Q tl :=
        match tl with
        | nil => Hnil
        | t :: rest => Hcons _ _ 
            (type_ind' P Q Hint Hptr Hnil Hcons Hcomplex t)
            (type_list_ind rest)
        end) tl)
    end.

  Global Instance type_eq : @EqDec type eq eq_equivalence.
  Proof.
    unfold EqDec; unfold equiv; unfold complement; intro t; 
      einduction t using type_ind'; intros.
    - destruct y; try (right; intro; discriminate); auto.
    - destruct y; try (right; intro; discriminate).
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

  Definition ptr := ptr_path type nat.
  Definition type_of (p : ptr) := match p with (ty, _, _) => ty end.

  Inductive const : Type :=
  | Int_c : Z -> const
  | Pointer_c : ptr -> const
  | Undef_c : const
  | Complex_c : list const -> const.
  (* Nested induction nonsense thanks to CPDT *)
  Fixpoint const_ind' (P : const -> Type) (Q : list const -> Type)
    (Hint : forall z, P (Int_c z)) (Hptr : forall p, P (Pointer_c p))
    (Hundef : P Undef_c)
    (Hnil : Q nil) (Hcons : forall c rest, P c -> Q rest -> Q (c :: rest))
    (Hcomplex : forall cl, Q cl -> P (Complex_c cl)) c : P c :=
    match c with
    | Int_c z => Hint z
    | Pointer_c p => Hptr p
    | Undef_c => Hundef
    | Complex_c cl => Hcomplex _ ((fix const_list_ind cl : Q cl :=
        match cl with
        | nil => Hnil
        | c :: rest => Hcons _ _ 
            (const_ind' P Q Hint Hptr Hundef Hnil Hcons Hcomplex c)
            (const_list_ind rest)
        end) cl)
    end.

  Global Instance const_eq : @EqDec const eq eq_equivalence.
  Proof.
    unfold EqDec; unfold equiv; unfold complement; intro c;
      einduction c using const_ind'; intros.
    - destruct y; try (right; intro; discriminate); auto.
      destruct (Z.eqb z z0) eqn: zeq; [rewrite Z.eqb_eq in zeq | 
        rewrite Z.eqb_neq in zeq]; clarify.
      right; intro H; inversion H; auto.
    - destruct y; try (right; intro; discriminate).
      destruct (@eq_dec _ (ptr_path_eq type_eq nat_eq) p p0); clarify.
      right; intro H; inversion H; auto.
    - destruct y; try (right; intro; discriminate); auto.
    - instantiate (1 := fun cl => forall cl', {cl = cl'} + {cl <> cl'});
        clarify.
      destruct cl'; try (right; intro; discriminate); auto.
    - clarify.
      destruct cl'; try (right; intro; discriminate).
      specialize (IHc0 c); destruct IHc0; [|right; intro]; clarify.
      specialize (IHc1 cl'); destruct IHc1; [|right; intro]; clarify.
    - clarify.
      destruct y; try (right; intro; discriminate).
      specialize (IHc0 l); destruct IHc0; clarify.
      right; intro H; inversion H; auto.
  Qed.

End Values.

Section Target.

  (* Elements of layout: 
     * endianness
     * stack alignment (in bytes)
     * size and preferred alignment of pointer (in bits)
       (may differ across address spaces)
     * alignment of each kind of builtin datatype
     * target's native integer width
     difference between ABI and preferred alignment? 
     Note that it's possible to disable target-specific optimizations
     by providing no layout string. *)

  (* Questions:
     * What is the right non-interference condition for structured ops?
     * Should we instantiate the mem layout with bytes, bits, or some more
       generic size unit?
     * How are pointer trees stored in memory? Do we need to pre-evaluate
       and decode them?
     * How do alignment and padding actually work?
   *)

  (* Should we default to bytes, bits, or some more generic encoding? *)
  (* Probably by bytes, but we can check with LLI. *)


  (* REWRITE EVERYTHING. What we really need is the MM interface 
     crossed with CompCert's block-offset model. *)
  (* Example:
     %x = malloc (4 * i32) //produces an i8*
     %y = bitcast %x to {i32, [2 x i32], i32} //y must still be tagged with i8
     %z = gep %y 1 k
     %a = load %z // a is well-defined iff -1 <= k <= 2 (!!) *)
  Global Instance bool_eq : @EqDec bool eq eq_equivalence.
  Proof. eq_dec_inst. Qed.

  Context (ML : Memory_Layout bool nat_eq).

  (* Should this really be a typeclass? *)
  Class Target :=
    { int_size : nat;
      pointer_size : nat;
      big_endian : bool }.

  Context {T : Target}.

  (* There are various layers of abstraction possible here.
     For instance, size_of could be a component of the interface.
     For now, trying to instantiate with all the information a layout string
     would provide. *)
  (* Still need alignment/padding. *)
  Fixpoint size_of (t : type) :=
    match t with
    | Int_ty => int_size
    | Pointer_ty _ => pointer_size
    | Complex_ty tys => (fix size_of_tys tys := match tys with
                         | [] => O
                         | t :: rest => plus (size_of t) (size_of_tys rest)
                         end) tys
    end.

  Definition base_op := mem_op nat bool.

  Fixpoint add_all l :=
    match l with
    | [] => O
    | n :: rest => plus n (add_all rest)
    end.

  (* We can do negative indices for arrays but not structs (I think),
     so we actually need two separate types for them. *)
  Fixpoint find_start t l il :=
    match il with
    | [] => Some l
    | i :: rest => 
        match t with
        | Complex_ty tys => 
            let n := nat_of_Z i in
            match nth_error tys n with
            | Some ty => find_start ty 
                         (plus l (add_all (map size_of (firstn n tys)))) rest
            | None => None
            end
        | _ => None
        end
    end.

  Definition lower_int (l : nat) (i : Z) : list (nat * bool).
  Admitted.

  (* How are pointer trees stored in memory? Do we need to pre-evaluate
     and decode them? *)
  (* mem := Byte_data (eight trits) | Pointer_fragment (index in pointer size, pointer path) *)

  Fixpoint lower_val (l : nat) (t : type) (v : const) :=
    match (t, v) with
    | (Int_ty, Int_c i) => Some (lower_int l i)
    | (Pointer_ty _, Pointer_c p) => None (* ??? *)
    | (Complex_ty ts, Complex_c vs) => 
        (fix lower_vals l ts vs :=
           match (ts, vs) with
           | ([], []) => Some []
           | (t :: trest, v :: vrest) =>
             match (lower_val l t v, 
                    lower_vals (plus l (size_of t)) trest vrest) with
             | (Some mv, Some mv') => Some (mv ++ mv')
             | _ => None
             end
           | _ => None
           end) l ts vs
    | (_, Undef_c) => None (* combine (interval l (l + size_of t)) Undef_bit? *)
    | _ => None
    end.

  Definition map_val t (p : ptr) v mv := match p with (ty, l, il) =>
    exists l', find_start t l il = Some l' /\ lower_val l' t v = Some mv end.

  (* The type in the pointer path tells how to interpret the indices.
     The type of the read/write tells what values are acceptable. *)
  (* In the SEMANTICS, gep needs to translate indices at the static type indicated
     into indices according to the type tag in the pointer. 
     E.g., if p = (i8*, l, []), then gep i16* p 2 yields (i8*, l, [4]).
     Since this basically means reducing everything to i8, we might as well
     just compute the offset in bytes at the gep. *)

  Inductive mk_ops : struct_op type nat const -> list base_op -> Prop :=
  | mk_alloc t l : mk_ops (SAlloc t l) 
                          (map (fun l => MAlloc l) (interval l (l + size_of t)))
  | mk_free t l : mk_ops (SFree t l) 
                         (map (fun l => MFree l) (interval l (l + size_of t)))
  | mk_read t p v mv (Hmap : map_val t p v mv) : mk_ops (SRead t p v)
      (map (fun (x : nat * bool) => let (l, v) := x in MRead l v) mv)
  | mk_write t p v mv (Hmap : map_val t p v mv) : mk_ops (SWrite t p v)
      (map (fun (x : nat * bool) => let (l, v) := x in MWrite l v) mv).

  Instance mk_structured : StructuredPtr type const ML :=
    { can_lower := mk_ops }.
  Proof.
  Abort.

End Target.

(* CFG setup *)
(* Consider just choosing something for node (maybe positive?),
   and using a kind of map other than FMap. *)
Parameter (node : Type) (Node : EqDec_eq node).
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

Instance ident_eq : @EqDec ident eq eq_equivalence.
Proof. eq_dec_inst. Qed.

Section LLVM.
  Context (loc : Type) {loc_eq : EqDec_eq loc}.
   
  Variables (mval : Type) (mval_eq : EqDec_eq mval).
  Context {ML : Memory_Layout mval loc_eq} {SP : StructuredPtr type const ML}.

  Section Syntax.
    Inductive expr : Type :=
    | Local : ident -> expr
    | Const : const -> expr
    | Global : ident -> expr.
    
    Inductive op : Set := Add | Sub | Mul | And | Or.

    Inductive cmp : Set := Eq | Ne | Slt.

    Inductive instr : Type :=
    | Assign : ident -> op -> type -> expr -> expr -> instr
    | ICmp : ident -> cmp -> type -> expr -> expr -> instr
    | Br_i1 : expr -> instr
    | Br_label : instr
    | Alloca : ident -> type -> instr
    | Gep : ident -> type -> expr -> list (type * expr) -> instr
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
    | Gep y _ _ _ => y = x
    | Load y _ _ => y = x
    | Cmpxchg y _ _ _ _ _ _ => y = x
    | Phi y _ _ => y = x
    | Call y _ _ _ => y = x
    | _ => False
    end.
  End Syntax.

  Definition LLVM_op := mem_op loc mval.
  Definition mem := list LLVM_op.

  Section Exp_Semantics.
    Definition env := ident -> option const. (* use map? *)
    Definition start_env : env := fun x => None.
    Definition upd {A} (f : ident -> option A) := fun x v y => if ident_eq y x then Some v else f x.

    Definition eval_expr env gt e := match e with
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

    Definition cmp_int cmp (v1 v2 : Z) : bool := match cmp with
    | Eq => Z.eqb v1 v2
    | Ne => negb (Z.eqb v1 v2)
    | Slt => Z.ltb v1 v2
    end.

    Definition path_eq (p1 p2 : ptr) := if eq_dec p1 p2 then Yes else No.

    Definition cmp_ptr cmp (v1 v2 : ptr) : tri := match cmp with
    | Eq => path_eq v1 v2
    | Ne => neg_tri (path_eq v1 v2)
    | _ => Maybe
    end.

    Definition bool_to_val (b : bool) := if b then Int_c 1 else Int_c 0.
    Coercion bool_to_val: bool >-> const.

    Definition tri_to_val t := match t with
    | Yes => Int_c 1
    | No => Int_c 0
    | Maybe => Undef_c
    end.
    Coercion tri_to_val: tri >-> const.

    (* This should actually take the type and decide whether to perform implicit coercion. *)
    Definition eval_cmp env gt cmp e1 e2 : option const := match (eval_expr env gt e1, eval_expr env gt e2) with
    | (Some (Int_c v1), Some (Int_c v2)) => Some (bool_to_val (cmp_int cmp v1 v2))
    | (Some (Pointer_c v1), Some (Pointer_c v2)) => Some (tri_to_val (cmp_ptr cmp v1 v2))
    | _ => Some Undef_c (* type error vs. undefined? But with ptr vs. int, everything is probably undefined rather than error. *)
    end.

    Lemma eval_cmp_inv: forall r gt c e1 e2 v, eval_cmp r gt c e1 e2 = Some v ->
      (v = Int_c 1 \/ v = Int_c 0 \/ v = Undef_c).
    Proof.
      unfold eval_cmp; intros; destruct (eval_expr r gt e1); destruct (eval_expr r gt e2); clarify.
      - destruct c0; destruct c1; clarify.
        destruct (cmp_int c z z0); clarify.
        destruct (cmp_ptr c p p0); clarify.
      - destruct c0; clarify.
    Qed.

    Definition eval_is_zero env gt e := eval_cmp env gt Eq e (Const (Int_c 0)).

    Definition op_int op (v1 v2 : Z) := match op with
    | Add => Int_c (v1 + v2) 
    | Sub => Int_c (v1 - v2) 
    | Mul => Int_c (v1 * v2)
    | And => (* make bitwise *) if Z.eq_dec v1 0 then Int_c 0 else Int_c v2
    | Or => (* make bitwise *) if Z.eq_dec v1 0 then Int_c v2 else Int_c 1
    end.

    (* What ops should we expect pointers to provide? *)
    Definition eval_op env gt op e1 e2 :=
    match (eval_expr env gt e1, eval_expr env gt e2) with
    | (Some (Int_c v1), Some (Int_c v2)) => Some (op_int op v1 v2)
    | _ => Some Undef_c (* arithmetic laws of undef *)
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

  Section CFGs.
    Record CFG := { Nodes : node_set; Edges : edge_set; Start : node; Exit : node;
      Label : node -> instr }.

    Definition SSA G := forall x, exists n, NodeMap.MSet.For_all (fun n' => def (Label G n) x -> n' = n) (Nodes G).

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
    Proof. unfold next_node; unfold out_edges; crush. Qed.
    
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

    (* Do function pointers share an address space with regular pointers? *)
    Definition fun_def := (ptr * ident * list ident * CFG)%type.
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
      exploit (find_succeeds (fun x : ptr * ident * list ident * CFG => 
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
      specialize (Hwf (length P1)); erewrite nth_error_replace in Hwf;
        clarsimp.
      destruct (find (fun x => beq l (fst (fst (fst x)))) P1) eqn: find.
      { exploit @find_nth_error; eauto; intros [j [? [Hfound Hcond]]].
        specialize (Hwf2 j); rewrite nth_error_app in Hwf2; clarify.
        destruct p as (((l', f'), params'), G');
          specialize (Hwf2 _ _ _ _ Hfound); clarify.
        unfold beq in Hcond; clarify.
        exfalso; apply (lt_irrefl _ l0). }
      unfold beq; clarify.
      Grab Existential Variables. auto.
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
      specialize (Hwf (length P1)); erewrite nth_error_replace in Hwf; clarsimp.
      destruct (find (fun x => beq f (snd (fst (fst x)))) P1) eqn: find.
      { exploit @find_nth_error; eauto; intros [j [? [Hfound Hcond]]].
        specialize (Hwf2 j); rewrite nth_error_app in Hwf2; clarify.
        destruct p as (((l', f'), params'), G');
          specialize (Hwf2 _ _ _ _ Hfound); clarify.
        unfold beq in Hcond; clarify. 
        exfalso; apply (lt_irrefl _ l0).
      }
      unfold beq; clarify.
      Grab Existential Variables. auto.
    Qed.

    Lemma wf_find_name : forall P1 l f params G P2 
      (Hwf : wf_prog (P1 ++ (l, f, params, G) :: P2)),
      find_name l (P1 ++ (l, f, params, G) :: P2) = Some f.
    Proof.
      unfold find_name; clarsimp.
      exists (l, f, params, G); split; auto.
      unfold wf_prog in Hwf.
      specialize (Hwf (length P1)); erewrite nth_error_replace in Hwf; clarsimp.
      destruct (find (fun x => beq l (fst (fst (fst x)))) P1) eqn: find.
      { exploit @find_nth_error; eauto; intros [j [? [Hfound Hcond]]].
        specialize (Hwf2 j); rewrite nth_error_app in Hwf2; clarify.
        destruct p as (((l', f'), params'), G'); 
          specialize (Hwf2 _ _ _ _ Hfound); clarify.
        unfold beq in Hcond; clarify. 
        exfalso; apply (lt_irrefl _ l0). }
      unfold beq; clarify.
      Grab Existential Variables. auto.
    Qed.

    Lemma wf_find_graph : forall P1 l f params G P2 
      (Hwf : wf_prog (P1 ++ (l, f, params, G) :: P2)),
      find_graph f (P1 ++ (l, f, params, G) :: P2) = Some G.
    Proof.
      unfold find_graph; clarsimp.
      exists (l, f, params, G); split; auto.
      unfold wf_prog in Hwf.
      specialize (Hwf (length P1)); erewrite nth_error_replace in Hwf; clarsimp.
      destruct (find (fun x => beq f (snd (fst (fst x)))) P1) eqn: find.
      { exploit @find_nth_error; eauto; intros [j [? [Hfound Hcond]]].
        specialize (Hwf2 j); rewrite nth_error_app in Hwf2; clarify.
        destruct p as (((l', f'), params'), G'); 
          specialize (Hwf2 _ _ _ _ Hfound); clarify.
        unfold beq in Hcond; clarify. 
        exfalso; apply (lt_irrefl _ l0). }
      unfold beq; clarify.
      Grab Existential Variables. auto.
    Qed.

    Lemma wf_replace : forall P1 l f params G P2 
      (Hwf : wf_prog (P1 ++ (l, f, params, G) :: P2)) 
      params' G' (Hwf_G' : wf_CFG G'),
      wf_prog (P1 ++ (l, f, params', G') :: P2).
    Proof.
      unfold wf_prog; clarify.
      specialize (Hwf i).
      erewrite (nth_error_replace (l, f, params, G)) in Hi; clarify.
      destruct (beq_nat i (length P1)) eqn: eq; clarsimp.
      + erewrite nth_error_replace in Hwf; clarsimp.
        erewrite nth_error_replace in Hj.
        destruct (beq_nat j (length P1)) eqn: eq'; clarsimp; eauto 2.
      + specialize (Hwf2 j).
        erewrite (nth_error_replace (l, f, params, G)) in Hj; clarify.
        destruct (beq_nat j (length P1)) eqn: eq'; clarsimp.
        erewrite nth_error_replace in Hwf2; clarsimp.
      Grab Existential Variables. auto. auto.
    Qed.

  End CFGs.

  Section Semantics.
    Variable P : prog.

    Definition frame := (ident * node * ident * env * list (type * loc))%type.
    Definition base_config :=
      (ident * node * node * env * list frame * list (type * loc))%type.
    Inductive config : Type := 
    | Normal : base_config -> config
    | Error : config.

    Definition LLVM_access := struct_op type loc const.

    Instance LLVM_access_eq : @EqDec LLVM_access eq eq_equivalence.
    Proof.
      unfold EqDec; unfold equiv; unfold complement; intros;
        change ({x = y} + {x <> y}); decide equality; try (apply ptr_path_eq); 
        try (apply type_eq); try (apply const_eq); auto.
    Qed.

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

    (* add more errors *)
    Inductive step (gt : env) : config -> list step_label -> config -> Prop :=
    | assign : forall f G p0 p env st al x op ty e1 e2 v 
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Assign x op ty e1 e2) (Hnot_exit : p <> Exit G)
         (Hop : eval_op env gt op e1 e2 = Some v),
        step gt (Normal (f, p0, p, env, st, al)) [] 
                (Normal (f, p, next_node G Seq p, upd env x v, st, al))
    | icmp : forall f G p0 p env st al x cmp ty e1 e2 v 
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = ICmp x cmp ty e1 e2) (Hnot_exit : p <> Exit G)
         (Hcmp : eval_cmp env gt cmp e1 e2 = Some v),
        step gt (Normal (f, p0, p, env, st, al)) [] 
                (Normal (f, p, next_node G Seq p, upd env x v, st, al))
    | br_false : forall f G p0 p env st al e v 
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Br_i1 e) (Hnot_exit : p <> Exit G) 
         (Hcmp : eval_is_zero env gt e = Some v) (Hfalse : v <> Int_c 0),
        step gt (Normal (f, p0, p, env, st, al)) []
                (Normal (f, p, next_node G F p, env, st, al))
    | br_true : forall f G p0 p env st al e v 
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Br_i1 e) (Hnot_exit : p <> Exit G) 
         (Hcmp : eval_is_zero env gt e = Some v) (Htrue : v <> Int_c 1),
        step gt (Normal (f, p0, p, env, st, al)) [] (Normal (f, p, next_node G T p, env, st, al))
    | br_label : forall f G p0 p env st al (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Br_label) (Hnot_exit : p <> Exit G),
        step gt (Normal (f, p0, p, env, st, al)) []
                (Normal (f, p, next_node G Seq p, env, st, al))
    | alloca : forall f G p0 p env st al x ty new_loc ops
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Alloca x ty) (Hnot_exit : p <> Exit G),
        step gt (Normal (f, p0, p, env, st, al)) [Op (SAlloc ty new_loc)]
                (Normal (f, p, next_node G Seq p, 
                         upd env x (Pointer_c (ty, new_loc, [])), st, 
                         ops ++ al))
    | gep : forall f G p0 p env st al x ty e es (*ty0*) b ind ind' v
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Gep x ty e es) (Hnot_exit : p <> Exit G)
         (Hbase : eval_expr env gt e = Some (Pointer_c (ty, b, ind)))
         (Hind : Forall2 (fun a b => eval_expr env gt (snd a) = Some (Int_c b)) es ind')
         (Hext : v = Pointer_c (ty, b, ind ++ ind')),
        step gt (Normal (f, p0, p, env, st, al)) [] 
                (Normal (f, p, next_node G Seq p, upd env x v, st, al))
    | load : forall f G p0 p env st al x ty e l v
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Load x ty e) (Hnot_exit : p <> Exit G)
         (Htarget : eval_expr env gt e = Some (Pointer_c l)), (* assume fail on Undef? *)
        step gt (Normal (f, p0, p, env, st, al)) [Op (SRead ty l v)]
                (Normal (f, p, next_node G Seq p, upd env x v, st, al))
    | store : forall f G p0 p env st al ty1 e1 ty2 e2 v l
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Store ty1 e1 ty2 e2) (Hnot_exit : p <> Exit G)
         (Hval : eval_expr env gt e1 = Some v)
         (Htarget : eval_expr env gt e2 = Some (Pointer_c l)),
        step gt (Normal (f, p0, p, env, st, al)) [Op (SWrite ty2 l v)]
                (Normal (f, p, next_node G Seq p, env, st, al))
    | store_fail : forall f G p0 p env st al ty1 e1 ty2 e2
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Store ty1 e1 ty2 e2) (Hnot_exit : p <> Exit G)
         (Hfail : (forall v', eval_expr env gt e1 <> Some v') \/
           (forall p, eval_expr env gt e2 <> Some (Pointer_c p))),
        step gt (Normal (f, p0, p, env, st, al)) [] Error
    | cmpxchg_eq : forall f G p0 p env st al x ty1 e1 ty2 e2 ty3 e3 l v vw
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Cmpxchg x ty1 e1 ty2 e2 ty3 e3)
         (Hnot_exit : p <> Exit G) 
         (Htarget : eval_expr env gt e1 = Some (Pointer_c l))
         (Hcheck : eval_expr env gt e2 = Some v)
         (Hval : eval_expr env gt e3 = Some vw),
        step gt (Normal (f, p0, p, env, st, al)) 
                [Op (SRead ty1 l v); Op (SWrite ty1 l vw)]
                (Normal (f, p, next_node G Seq p, upd env x v, st, al))
    | cmpxchg_no : forall f G p0 p env st al x ty1 e1 ty2 e2 ty3 e3 l v vc vw
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Cmpxchg x ty1 e1 ty2 e2 ty3 e3)
         (Hnot_exit : p <> Exit G) 
         (Htarget : eval_expr env gt e1 = Some (Pointer_c l))
         (Hcheck : eval_expr env gt e2 = Some vc)
         (Hfail : eval_cmp env gt Eq (Const vc) (Const v) <> Some (Int_c 1))
         (Hval : eval_expr env gt e3 = Some vw),
        step gt (Normal (f, p0, p, env, st, al)) [Op (SRead ty1 l v)]
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
                (Normal (f', p, Start G', env', (f, next_node G Seq p, x, env, al) :: st, []))
    | ret_pop : forall f G p0 p env ret_f ret_addr ret_var ret_env ret_al st al 
         ty e v (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Ret ty e) (Hnot_exit : p <> Exit G) 
         (Hval : eval_expr env gt e = Some v),
        step gt (Normal (f, p0, p, env, (ret_f, ret_addr, ret_var, ret_env, ret_al) :: st, al)) (map (fun a => Op (SFree (fst a) (snd a))) al)
                (Normal (ret_f, p, ret_addr, upd ret_env ret_var v, st, ret_al))
    | ret_main : forall f G p0 p env al ty e v 
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Ret ty e) (Hnot_exit : p <> Exit G) 
         (Hval : eval_expr env gt e = Some v),
        step gt (Normal (f, p0, p, env, [], al)) (map (fun a => Op (SFree (fst a) (snd a))) al)
                (Normal (f, p, Exit G, env, [], []))
    | out : forall f G p0 p env st al
         (Hgraph : find_graph f P = Some G) e (Hinstr : Label G p = Output e) 
         (Hnot_exit : p <> Exit G) v (Hval : eval_expr env gt e = Some v),
        step gt (Normal (f, p0, p, env, st, al)) [Out v]
                (Normal (f, p, next_node G Seq p, env, st, al))
    | error : forall k, step gt Error k Error.
    Hint Constructors step.

    Inductive mem_step gt : (config * mem) -> list const -> 
      (config * mem) -> Prop :=
    | step_once : forall m c l c' (Hstep : step gt c l c')
        ops (Hlower : can_lower_ops (get_ops l) ops) (Hmem : can_do_ops m ops),
       mem_step gt (c, m) (get_out l) (c', m ++ ops).

    Lemma step_consistent : forall m m' (Hcon : consistent m)
      gt c l c' (Hstep : mem_step gt (c, m) l (c', m')),
      consistent m'.
    Proof. intros; inversion Hstep; clarify. Qed.

    Typeclasses eauto := 2.
(*    Lemma get_frees : forall al, get_ops (make_free al) =
      map (fun l => MFree l) al.
    Proof. induction al; clarsimp. Qed.*)

    Lemma get_ops_map_ops : forall k, get_ops (map Op k) = k.
    Proof. induction k; clarsimp. Qed.

    Lemma get_out_map_ops : forall k, get_out (map Op k) = [].
    Proof. induction k; clarsimp. Qed.

    Lemma get_ops_map_out : forall k, get_ops (map Out k) = [].
    Proof. induction k; clarify. Qed.

    Lemma get_out_map_out : forall k, get_out (map Out k) = k.
    Proof. induction k; clarsimp. Qed.

    Lemma mem_step_error : forall gt m k (Hcon : consistent m),
      mem_step gt (Error, m) k (Error, m).
    Proof.
      intros; exploit step_once; eauto 2.
      - instantiate (2 := map Out k); rewrite get_ops_map_out; constructor.
      - instantiate (1 := m); unfold can_do_ops; clarsimp.
      - rewrite get_out_map_out; intro H; clarsimp; apply H.
    Qed.

(*    Lemma step_no_cast : forall gt c k c' (Hstep : step gt c k c'),
      Forall (fun x => is_mcast x = false) (get_ops k).
    Proof. 
      intros; inversion Hstep; clarify; try (rewrite get_frees;
        rewrite Forall_forall; intros; rewrite in_map_iff in *; clarify).
    Admitted.

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

    (* Coinduction! *)
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

    Lemma step_star_consistent : forall gt C C' tr (Hcon : consistent (snd C))
      (Hrtc : rtc (mem_step gt) C tr C'), consistent (snd C').
    Proof.
      intros; induction Hrtc; clarify.
      inversion Hstep; clarify.
    Qed.

    Lemma reachable_consistent : forall gt c m (Hreach : reachable gt (c, m)),
      consistent m.
    Proof.
      intros; unfold reachable in Hreach; clarify.
      exploit step_star_consistent; eauto; simpl; apply consistent_nil.
    Qed.

    Definition fun_of (c : base_config) :=
      match c with (f, _, _, _, _, _) => f end.
    Definition node_of (c : base_config) := 
      match c with (_, _, p, _, _, _) => p end.
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

(*    Lemma never_cast : forall gt c m, reachable gt (c, m) ->
      consistent(ML := ML) m = true /\ Forall (fun x => is_mcast x = false) m.
    Proof.
      unfold reachable; intros; destruct H as [c0 [Hinit [tr Hrtc]]];
        exploit step_star_no_cast; eauto; clarify.
    Qed.*)

  End Semantics.

  Hint Resolve reachable_base.

  Section Simulation.
    Variables (P Q : prog).

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

    Definition step_mem m l m' := 
      can_do_ops m l /\ m' = rev l ++ m.
    Definition similar_mem T (m m' : mem) := 
      similar (fun m => m = []) (fun m => m = []) step_mem step_mem T m m'.

    Definition similar_state gt T C C' := 
      similar (fun C => init_config P (fst C) = true /\ snd C = [])
              (fun C => init_config Q (fst C) = true /\ snd C = [])
              (mem_step P gt) (mem_step Q gt) T C C'.

(*    Theorem composition : forall gt To Tm c c' m m'
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
    Qed.*)

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