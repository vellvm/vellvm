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
(* In this version, locations contain large data,
   and the locations in paths are sent directly to memory,
   with the rest remaining as an index into the result. *)
(* The weakness of this approach is that the large data must be read before being written. *)
  Variables (type loc : Type) (type_eq : EqDec_eq type) (loc_eq : EqDec_eq loc).
  
  Definition ptr_path := (type * loc * list Z)%type.

  Instance ptr_path_eq : @EqDec ptr_path eq eq_equivalence.
  Proof. eq_dec_inst. Qed.

  Typeclasses eauto := 2.
  Instance StructuredPtr : @PtrType type _ _ ptr_path_eq loc_eq :=
    { ptr_eq := fun a b => if eq_dec a b then Yes else No; 
      normalize := fun t a => match a with (_, l, _) => l end; 
      inject := fun t l => (t, l, []) }.
  Proof.
    clarify.
    intros; destruct (eq_dec p p'); clarify.
    auto.
  Qed.

End Structured.

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
  Variables (loc : Type) (loc_eq : EqDec_eq loc).

  Section Syntax.
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

    Instance type_eq : @EqDec type eq eq_equivalence.
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
   
    Definition ptr := ptr_path type loc.
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

    Definition path_eq := @ptr_eq _ _ _ _ _ (@StructuredPtr _ _ type_eq loc_eq).

    Instance const_eq : @EqDec const eq eq_equivalence.
    Proof.
      unfold EqDec; unfold equiv; unfold complement; intro c;
        einduction c using const_ind'; intros.
      - destruct y; try (right; intro; discriminate); auto.
        destruct (Z.eqb z z0) eqn: zeq; [rewrite Z.eqb_eq in zeq | 
          rewrite Z.eqb_neq in zeq]; clarify.
        right; intro H; inversion H; auto.
      - destruct y; try (right; intro; discriminate).
        destruct (@eq_dec _ (ptr_path_eq type_eq loc_eq) p p0); clarify.
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

    (* This should be genericized for layout. *)
    (* It should also probably take a type and be a function. *)
    Inductive index_into : const -> list Z -> const -> Prop :=
    | index_nil : forall c, index_into c [] c
    | index_0 : forall c z zl c', Z.to_nat z = O -> index_into c zl c' ->
        index_into c (z :: zl) c'
    | index_i : forall cl z n c zl c', Z.to_nat z = n -> 
        nth_error cl n = Some c -> index_into c zl c' -> 
        index_into (Complex_c cl) (z :: zl) c'.

    Fixpoint replace_nth {A} l n (a : A) := match l with
    | nil => nil
    | x :: rest => match n with 
                   | O => a :: rest
                   | S n' => replace_nth rest n' a
                   end
    end.

    Inductive replace_at : const -> list Z -> const -> const -> Prop :=
    | replace_nil : forall c c', replace_at c [] c' c'
    | replace_0 : forall c z zl c' c'', Z.to_nat z = O -> 
        replace_at c zl c' c'' -> replace_at c (z :: zl) c' c''
    | replace_i : forall cl z n c zl c' c'', Z.to_nat z = n ->
        nth_error cl n = Some c -> replace_at c zl c' c'' -> 
        replace_at (Complex_c cl) (z :: zl) c' 
                   (Complex_c (replace_nth cl n c'')).

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

  Definition LLVM_access := mem_op loc const Z.
  Definition mem := list LLVM_access.

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
    Definition fun_def := (loc * ident * list ident * CFG)%type.
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
      exploit (find_succeeds (fun x : loc * ident * list ident * CFG => 
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

    Definition frame := (ident * node * ident * env * list loc)%type.
    Definition base_config :=
      (ident * node * node * env * list frame * list loc)%type.
    Inductive config : Type := 
    | Normal : base_config -> config
    | Error : config.

    Instance LLVM_access_eq : @EqDec LLVM_access eq eq_equivalence.
    Proof. 
      unfold EqDec; unfold equiv; unfold complement; intros;
        change ({x = y} + {x <> y}); decide equality; try (apply const_eq).
      destruct (Z.eqb c z) eqn: zeq; [rewrite Z.eqb_eq in zeq | 
          rewrite Z.eqb_neq in zeq]; clarify.
    Qed.

    Definition init_config (c : config) := match c with 
    | Normal (f, p0, p, e, [], []) => 
        match find_graph f P with
        | Some G => if eq_dec p (Start G) then true else false
        | None => false
        end
    | _ => false
    end.

    Definition flatten := @normalize _ _ _ _ _ 
      (@StructuredPtr _ _ type_eq loc_eq).

    Definition start_call v vs := match v with Pointer_c ptr =>
      match find_fun (flatten (type_of ptr) ptr) P with
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

    Definition make_free al : list step_label := 
      map (fun l => Op (MFree l)) al.

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
    | alloca : forall f G p0 p env st al x ty new_loc
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Alloca x ty) (Hnot_exit : p <> Exit G),
        step gt (Normal (f, p0, p, env, st, al)) [Op (MAlloc new_loc)]
                (Normal (f, p, next_node G Seq p, 
                         upd env x (Pointer_c (ty, new_loc, [])), st, 
                         new_loc :: al))
    | gep : forall f G p0 p env st al x ty e es (*ty0*) b ind ind' v
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Gep x ty e es) (Hnot_exit : p <> Exit G)
         (Hbase : eval_expr env gt e = Some (Pointer_c (ty, b, ind)))
         (Hind : Forall2 (fun a b => eval_expr env gt (snd a) = Some (Int_c b)) es ind')
         (Hext : v = Pointer_c (ty, b, ind ++ ind')),
        step gt (Normal (f, p0, p, env, st, al)) [] 
                (Normal (f, p, next_node G Seq p, upd env x v, st, al))
    | load : forall f G p0 p env st al x ty e ty' l zl v v'
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Load x ty e) (Hnot_exit : p <> Exit G)
         (Htarget : eval_expr env gt e = Some (Pointer_c (ty', l, zl)))
         (Hind : index_into v zl v'), (* assume fail on Undef? *)
        step gt (Normal (f, p0, p, env, st, al)) [Op (MRead l v)]
                (Normal (f, p, next_node G Seq p, upd env x v, st, al))
    | store : forall f G p0 p env st al ty1 e1 ty2 e2 v ty' l zl vw v'
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Store ty1 e1 ty2 e2) (Hnot_exit : p <> Exit G)
         (Hval : eval_expr env gt e1 = Some vw)
         (Htarget : eval_expr env gt e2 = Some (Pointer_c (ty', l, zl)))
         (Hreplace : replace_at v zl vw v'),
        step gt (Normal (f, p0, p, env, st, al)) 
                [Op (MRead l v); Op (MWrite l v')]
                (Normal (f, p, next_node G Seq p, env, st, al))
    | store_fail : forall f G p0 p env st al ty1 e1 ty2 e2
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Store ty1 e1 ty2 e2) (Hnot_exit : p <> Exit G)
         (Hfail : (forall v', eval_expr env gt e1 <> Some v') \/
           (forall p, eval_expr env gt e2 <> Some (Pointer_c p))),
        step gt (Normal (f, p0, p, env, st, al)) [] Error
    | cmpxchg_eq : forall f G p0 p env st al x ty1 e1 ty2 e2 ty3 e3 ty' l zl 
         v vc vw v'
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Cmpxchg x ty1 e1 ty2 e2 ty3 e3)
         (Hnot_exit : p <> Exit G) 
         (Htarget : eval_expr env gt e1 = Some (Pointer_c (ty', l, zl)))
         (Hcheck : eval_expr env gt e2 = Some vc)
         (Hindex : index_into v zl vc)
         (Hval : eval_expr env gt e3 = Some vw)
         (Hreplace : replace_at v zl vw v'),
        step gt (Normal (f, p0, p, env, st, al))
          [Op (MRead l v); Op (MWrite l v')] 
          (Normal (f, p, next_node G Seq p, upd env x v, st, al))
    | cmpxchg_no : forall f G p0 p env st al x ty1 e1 ty2 e2 ty3 e3 ty' l zl
         v vc vw
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Cmpxchg x ty1 e1 ty2 e2 ty3 e3)
         (Hnot_exit : p <> Exit G) 
         (Htarget : eval_expr env gt e1 = Some (Pointer_c (ty', l, zl)))
         (Hcheck : eval_expr env gt e2 = Some vc)
(*         (Hfail : eval_cmp env gt Eq (Const v') (Const v) <> Some (Int_c 1))*)
         (Hfail : ~index_into v zl vc)
         (Hval : eval_expr env gt e3 = Some vw),
        step gt (Normal (f, p0, p, env, st, al)) [Op (MRead l v)]
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
        step gt (Normal (f, p0, p, env, (ret_f, ret_addr, ret_var, ret_env, ret_al) :: st, al)) (make_free al)
                (Normal (ret_f, p, ret_addr, upd ret_env ret_var v, st, ret_al))
    | ret_main : forall f G p0 p env al ty e v 
         (Hgraph : find_graph f P = Some G) 
         (Hinstr : Label G p = Ret ty e) (Hnot_exit : p <> Exit G) 
         (Hval : eval_expr env gt e = Some v),
        step gt (Normal (f, p0, p, env, [], al)) (make_free al)
                (Normal (f, p, Exit G, env, [], []))
    | out : forall f G p0 p env st al
         (Hgraph : find_graph f P = Some G) e (Hinstr : Label G p = Output e) 
         (Hnot_exit : p <> Exit G) v (Hval : eval_expr env gt e = Some v),
        step gt (Normal (f, p0, p, env, st, al)) [Out v]
                (Normal (f, p, next_node G Seq p, env, st, al))
    | error : forall k
       (Hno_cast : Forall (fun x => is_mcast x = false) (get_ops k)),
       step gt Error k Error.
    Hint Constructors step.

    Context (ML : Memory_Layout Z loc_eq const_eq).

    Inductive mem_step gt : (config * mem) -> list const -> 
      (config * mem) -> Prop :=
    | step_once : forall m c l c' (Hstep : step gt c l c')
        (Hmem : can_do_ops(ML := ML) m (get_ops l) = true), 
       mem_step gt (c, m) (get_out l) (c', rev (get_ops l) ++ m).

    Lemma step_consistent : forall m m' (Hcon : consistent(ML := ML) m = true)
      gt c l c' (Hstep : mem_step gt (c, m) l (c', m')), 
      consistent(ML := ML) m' = true.
    Proof.
      intros; inversion Hstep; clarify.
      apply consistent_app; auto.
    Qed.

    Typeclasses eauto := 2.
    Lemma get_frees : forall al, get_ops (make_free al) =
      map (fun l => MFree l) al.
    Proof. induction al; clarsimp. Qed.

    Lemma get_ops_map_out : forall k, get_ops (map Out k) = [].
    Proof. induction k; clarify. Qed.

    Lemma get_out_map_out : forall k, get_out (map Out k) = k.
    Proof. induction k; clarsimp. Qed.

    Lemma mem_step_error : forall gt m k, mem_step gt (Error, m) k (Error, m).
    Proof.
      intros; exploit step_once; eauto 2.
      - apply error.
        instantiate (1 := map Out k); rewrite get_ops_map_out; clarify.
      - rewrite get_ops_map_out; clarify.
      - rewrite get_out_map_out; rewrite get_ops_map_out; clarify; eauto.
    Qed.

    Lemma step_no_cast : forall gt c k c' (Hstep : step gt c k c'),
      Forall (fun x => is_mcast x = false) (get_ops k).
    Proof. 
      intros; inversion Hstep; clarify; try (rewrite get_frees;
        rewrite Forall_forall; intros; rewrite in_map_iff in *; clarify).
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
    Qed.
    
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

    Lemma never_cast : forall gt c m, reachable gt (c, m) ->
      consistent(ML := ML) m = true /\ Forall (fun x => is_mcast x = false) m.
    Proof.
      unfold reachable; intros; destruct H as [c0 [Hinit [tr Hrtc]]];
        exploit step_star_no_cast; eauto; clarify.
    Qed.

  End Semantics.

  Hint Resolve reachable_base.

  Section Simulation.
    Variables (P Q : prog).
    Context (ML : Memory_Layout Z loc_eq const_eq).

    Definition simulation (R : config * mem -> config * mem -> Prop) gt :=
      (forall c0, init_config P c0 = true -> 
         exists c0', init_config Q c0' = true /\ R (c0, []) (c0', [])) /\
      forall C C' (Hreach : reachable P ML gt C)
        (Hreach' : reachable Q ML gt C') (Hsim : R C C') 
        l C2 (Hstep : mem_step P ML gt C l C2),
       exists C2', mem_step Q ML gt C' l C2' /\ R C2 C2'.

    Lemma sim_rtc : forall R gt (Hsim : simulation R gt) c m tr c2 m2
      (Hreach : reachable P ML gt (c, m)) 
      (Hstep_star : rtc (mem_step P ML gt) (c, m) tr (c2, m2))
      c' m' (Hreach : reachable Q ML gt (c', m')) (HR : R (c, m) (c', m')),
      exists c2' m2', rtc (mem_step Q ML gt) (c', m') tr (c2', m2') /\ 
        reachable P ML gt (c2, m2) /\ reachable Q ML gt (c2', m2') /\ 
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
      traces P ML gt tr -> traces Q ML gt tr.
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
      forall C C' (Hreach : reachable P ML gt C) 
        (Hreach' : reachable Q ML gt C') (Hsim : R C C')
        l C2 (Hstep : mem_step P ML gt C l C2),
       (l = [] /\ R C2 C') \/
       exists C2', mem_step Q ML gt C' l C2' /\ R C2 C2'.

    Lemma lo_sim_rtc : forall R gt (Hsim : lo_simulation R gt) c m tr c2 m2
      (Hreach : reachable P ML gt (c, m)) 
      (Hstep_star : rtc (mem_step P ML gt) (c, m) tr (c2, m2))
      c' m' (Hreach : reachable Q ML gt (c', m')) (HR : R (c, m) (c', m')),
      exists c2' m2', rtc (mem_step Q ML gt) (c', m') tr (c2', m2') /\ 
        reachable P ML gt (c2, m2) /\ reachable Q ML gt (c2', m2') /\ 
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
      tr, traces P ML gt tr -> traces Q ML gt tr.
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
      forall C C' (Hreach : reachable P ML gt C)
        (Hreach' : reachable Q ML gt C') (Hsim : R C C')
        l C2 (Hstep : mem_step P ML gt C l C2),
       exists C2', (mem_step Q ML gt C' l C2' \/ exists C2'', 
         mem_step Q ML gt C' [] C2'' /\ mem_step Q ML gt C2'' l C2') /\ 
        R C2 C2'.

    Lemma ro_sim_rtc : forall R gt (Hsim : ro_simulation R gt) c m tr c2 m2
      (Hreach : reachable P ML gt (c, m)) 
      (Hstep_star : rtc (mem_step P ML gt) (c, m) tr (c2, m2))
      c' m' (Hreach : reachable Q ML gt (c', m')) (HR : R (c, m) (c', m')),
      exists c2' m2', rtc (mem_step Q ML gt) (c', m') tr (c2', m2') /\ 
        reachable P ML gt (c2, m2) /\ reachable Q ML gt (c2', m2') /\ 
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
      tr, traces P ML gt tr -> traces Q ML gt tr.
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
      can_do_ops(Val := const_eq) m l = true /\ m' = rev l ++ m.
    Definition similar_mem T (m m' : mem) := 
      similar (fun m => m = []) (fun m => m = []) step_mem step_mem T m m'.

    Definition similar_state gt T C C' := 
      similar (fun C => init_config P (fst C) = true /\ snd C = [])
              (fun C => init_config Q (fst C) = true /\ snd C = [])
              (mem_step P ML gt) (mem_step Q ML gt) T C C'.

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
      (Hrtc : rtc (mem_step P ML gt) C tr C2)
      T C' (Hsim : similar_state gt T C C'),
      exists C2', rtc (mem_step Q ML gt) C' tr C2' /\
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
      traces P ML gt tr -> traces Q ML gt tr.
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