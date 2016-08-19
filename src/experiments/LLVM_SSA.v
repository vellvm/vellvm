Add LoadPath "C:\Users\William\My Documents\cpdt/src".
Add LoadPath "C:\Users\William\My Documents\Coq\sf".
Require Import CpdtTactics.
Require Import LibTactics.
Require Import minillvm.
Require Import String.
Require Import List.
Require Import Relation_Operators.
Import ListNotations.

Set Implicit Arguments.

(* SSA representation(s) of MiniLLVM. *)
Definition label := node.

Inductive l_instr :=
| l_Assign : string -> op -> expr -> expr -> l_instr
| l_ICmp : string -> cmp -> expr -> expr -> l_instr
| l_Br_i1 : expr -> label -> label -> l_instr
| l_Br_label : label -> l_instr.

Definition SSA_block := (label * list (string * node_map expr) * list l_instr)%type. (* l: x <- phi(...); ...; i; ... *)

Definition instr_to_block G n i :=
  match i with
  | Assign x o _ e1 e2 => Some ((n, [], [l_Assign x o e1 e2; l_Br_label (next_node G Seq n)]))
  | ICmp x c _ e1 e2 => Some ((n, [], [l_ICmp x c e1 e2; l_Br_label (next_node G Seq n)]))
  | Br_i1 e => Some ((n, [], [l_Br_i1 e (next_node G T n) (next_node G F n)]))
  | Br_label => Some ((n, [], [l_Br_label (next_node G Seq n)]))
  | Phi x _ es => Some ((n, [(x, es)], [l_Br_label (next_node G Seq n)]))
  | _ => None
  end.

Lemma instr_label: forall G n i x, instr_to_block G n i = Some x -> fst (fst x) = n.
Proof.
  destruct i; clarify.
Qed.

Lemma same_graph_instr_block: forall G G' n i, Edges G = Edges G' -> instr_to_block G n i = instr_to_block G' n i.
Proof.
  destruct i; clarify; repeat (rewrite (next_node_edges G G')); eauto.
Qed.

(* Use dominator tree to embed dominated blocks inside dominating blocks. *)
Inductive tree (A : Type) :=
| Node : A -> list (tree A) -> tree A.

Definition root {A} (t : tree A) := match t with Node x _ => x end.
Definition children {A} (t : tree A) := match t with Node _ ch => ch end.

Fixpoint to_list {A} (tr : tree A) :=
  match tr with Node x ch =>
    fold_left (fun acc tr => acc ++ to_list tr) ch [x]
  end.

Inductive subtree {A} (tr : tree A) : tree A -> Prop :=
| sub_root: subtree tr tr
| sub_child: forall tr' x ch, subtree tr tr' -> In tr' ch -> subtree tr (Node x ch).
Hint Immediate sub_root.

Fixpoint tree_find {A} (f : A -> bool) (tr : tree A) :=
  match tr with Node x ch =>
    if f x then Some x 
    else fold_left (fun r tr => match r with Some x => Some x | None => tree_find f tr end) ch None
  end.

Fixpoint subtree_find {A} (f : A -> bool) (tr : tree A) :=
  match tr with Node x ch =>
    if f x then Some (Node x ch) 
    else fold_left (fun r tr => match r with Some x => Some x | None => subtree_find f tr end) ch None
  end.

Fixpoint tree_map {A B} (f : A -> B) (tr : tree A) :=
  match tr with Node x ch => Node (f x) (map (tree_map f) ch) end.

Lemma map_root: forall {A B} (f : A -> B) tr, root (tree_map f tr) = f (root tr).
Proof.
  destruct tr; clarify.
Qed.

Lemma subtree_map: forall {A B} tr tr' (f : A -> B), subtree tr tr' -> subtree (tree_map f tr) (tree_map f tr').
Proof.
  intros; induction H; clarify.
    econstructor; eauto.
    apply in_map; auto.
Qed.

(* From CPDT. *)
Section tree_ind'.
  Variable A : Type.
  Variable P : tree A -> Prop.
  Hypothesis IH : forall x ch, Forall P ch -> P (Node x ch).

  Fixpoint tree_ind' tr : P tr :=
    match tr with Node x ch => IH x 
        ((fix list_tree_ind' ch : Forall P ch :=
          match ch with
            | [] => Forall_nil P
            | tr::rest => Forall_cons tr (tree_ind' tr) (list_tree_ind' rest)
          end) ch)
    end.
End tree_ind'.

(* From Coq'Art. This is the one that should be automatically generated... *)
Section best_tree_ind.
  Variable A : Type.
  Variable P : tree A -> Prop.
  Variable Q : list (tree A) -> Prop.
  Hypotheses (tree_IH: forall x ch, Q ch -> P (Node x ch))
             (list_base: Q [])
             (list_IH: forall tr, P tr -> forall rest, Q rest -> Q (tr :: rest)).

  Fixpoint best_tree_ind tr : P tr :=
    match tr with Node x ch => tree_IH x 
      ((fix l_ind l : Q l := match l with 
                             | [] => list_base 
                             | tr :: rest => list_IH (best_tree_ind tr) (l_ind rest)
                             end) ch)
    end.
End best_tree_ind.

Lemma tree_ind'': forall {A} (P : tree A -> Prop), (forall x ch, (forall c, In c ch -> P c) -> P (Node x ch)) -> 
  forall tr, P tr.
Proof.
  intros; apply tree_ind'; intros.
    rewrite Forall_forall in *; crush.
Qed.    

Close Scope string_scope.

Lemma acc_mono: forall {A} l (l0 l1 : list A),
  fold_left (fun acc tr => acc ++ to_list tr) l (l0 ++ l1) =
  l0 ++ fold_left (fun acc tr => acc ++ to_list tr) l l1.
Proof.
  induction l; crush.
Qed.

Corollary acc_prefix: forall {A} l (l0 : list A),
  fold_left (fun acc tr => acc ++ to_list tr) l l0 =
  l0 ++ fold_left (fun acc tr => acc ++ to_list tr) l [].
Proof.
  intros; generalize (acc_mono l l0 []); autorewrite with list in *; auto.
Qed.

Lemma stays_found: forall {A} f ch (r : A), fold_left (fun r tr => match r with Some x => Some x | None => tree_find f tr end) 
  ch (Some r) = Some r.
Proof.
  induction ch; crush.
Qed.

Lemma stays_found_sub: forall {A} f ch (r : tree A), fold_left (fun r tr => match r with Some x => Some x | None => subtree_find f tr end) 
  ch (Some r) = Some r.
Proof.
  induction ch; crush.
Qed.

Lemma tree_find_spec: forall {A} (tr : tree A) f, tree_find f tr = find f (to_list tr).
Proof.
  intros; apply (best_tree_ind (fun tr => tree_find f tr = find f (to_list tr)) 
                               (fun l => fold_left (fun r tr => match r with Some x => Some x | None => tree_find f tr end) l None =
                                         find f (fold_left (fun acc tr => acc ++ to_list tr) l []))); clarify.
    rewrite acc_prefix; crush.
    rewrite acc_prefix; crush.
    crush.
      destruct (find f (to_list tr0)) eqn: found; rewrite acc_prefix; [rewrite stays_found|]; rewrite find_app; crush.
Qed.  

Lemma subtree_find_None: forall {A} (tr : tree A) f, subtree_find f tr = None ->
  tree_find f tr = None.
Proof.
  intros; apply (best_tree_ind (fun tr => subtree_find f tr = None -> tree_find f tr = None) 
    (fun l => fold_left (fun r tr => match r with Some x => Some x | None => subtree_find f tr end) l None = None ->
              fold_left (fun r tr => match r with Some x => Some x | None => tree_find f tr end) l None = None)); clarify.
    destruct (subtree_find f tr0); [rewrite stays_found_sub in H2 |]; crush.
Qed.

Lemma subtree_find_Some: forall {A} (tr : tree A) f tr', subtree_find f tr = Some tr' ->
  tree_find f tr = Some (root tr') /\ subtree tr' tr.
Proof.
  intros; apply (best_tree_ind (fun tr => forall tr', subtree_find f tr = Some tr' -> tree_find f tr = Some (root tr') /\ subtree tr' tr) 
    (fun l => forall tr', fold_left (fun r tr => match r with Some x => Some x | None => subtree_find f tr end) l None = Some tr' ->
              fold_left (fun r tr => match r with Some x => Some x | None => tree_find f tr end) l None = Some (root tr') /\ exists d, In d l /\ subtree tr' d)); 
    clarify.
    specialize (H0 _ H1); crush.
      econstructor; eauto.
    destruct (subtree_find f tr0) eqn: found; [rewrite stays_found_sub in H2 |]; clarify.
      specialize (H0 tr'0); clarify; crush.
        apply stays_found.
        eexists; crush.
      specialize (H1 _ H2); clarify.
        generalize (subtree_find_None _ _ found); intro not_found; rewrite not_found; crush.
        eexists; split; eauto.
Qed.

Corollary find_subtree: forall {A} (tr : tree A) f x, tree_find f tr = Some x ->
  f x = true /\ exists tr', subtree_find f tr = Some tr' /\ root tr' = x /\ subtree tr' tr.
Proof.
  intros; split.
    rewrite tree_find_spec in H; specialize (find_success _ _ H); clarify.
    destruct (subtree_find f tr) eqn: subt.
      generalize (subtree_find_Some _ _ subt); clarify; eexists; crush.
      generalize (subtree_find_None _ _ subt); crush.
Qed.

(* translation *)
Fixpoint some_list {A} (l : list (option A)) :=
  match l with
  | [] => Some []
  | x::rest => match (x, some_list rest) with (Some x', Some rest') => Some (x'::rest') | _ => None end
  end.

Lemma some_list_spec: forall {A} (l : list (option A)) l', some_list l = Some l' ->
  Forall2 (fun xo x' => match xo with Some x => x = x' | None => False end) l l'.
Proof.
  induction l; clarify.
Qed.

Lemma in_some_list_iff: forall {A} (l : list (option A)) l' x, some_list l = Some l' ->
  (In (Some x) l <-> In x l').
Proof.
  induction l; clarify.
    crush.
    specialize (IHl _ x H); rewrite IHl; crush.
Qed.

Lemma in_some_list_ex: forall {A} (l : list (option A)) l' xo, some_list l = Some l' ->
  In xo l -> exists x, xo = Some x /\ In x l'.
Proof.
  induction l; clarify.
    destruct H0. 
      eexists; crush.
      specialize (IHl _ _ H H0); clarify.
        exists x1; auto.
Qed.

Lemma in_some_map1: forall {A B} (f : A -> option B) l l' x, some_list (map f l) = Some l' ->
  In x l -> exists x', f x = Some x' /\ In x' l'.
Proof.
  intros; eapply in_some_list_ex; eauto.
  apply in_map; auto.
Qed.

Lemma in_some_map2: forall {A B} (f : A -> option B) l l' x', some_list (map f l) = Some l' ->
  In x' l' -> exists x, f x = Some x' /\ In x l.
Proof.
  intros; apply in_map_iff.
  rewrite in_some_list_iff; eauto.
Qed.

Lemma some_list_cons: forall {A} (l : list (option A)) l' x, some_list l = Some l' ->
  some_list (Some x :: l) = Some (x :: l').
Proof.
  simpl; intros; autorewrite with core in *; eexists; crush.
Qed.
Hint Resolve some_list_cons.

Fixpoint CFG_to_blocks G dom : option (tree SSA_block) :=
  match dom with Node n ch => 
    match (instr_to_block G n (Label G n), some_list (map (CFG_to_blocks G) ch)) with 
    | (Some b, Some ch') => Some (Node b ch')
    | _ => None
    end
  end.

Lemma CFG_blocks_entry: forall G ch bl, some_list (map (CFG_to_blocks G) ch) = Some bl ->
  forall tr, In tr ch -> exists bl', CFG_to_blocks G tr = Some bl' /\ In bl' bl.
Proof.
  intros.
  eapply in_some_map1; eauto.
Qed.

Lemma dom_tree_blocks: forall G dom bl, CFG_to_blocks G dom = Some bl ->
  tree_map (fun x => fst (fst x)) bl = dom.
Proof.
  intro; apply (best_tree_ind (fun dom => forall bl, CFG_to_blocks G dom = Some bl ->
    tree_map (fun x => fst (fst x)) bl = dom) (fun ch => forall ch', some_list (map (CFG_to_blocks G) ch) = 
    Some ch' -> map (tree_map (fun x => fst (fst x))) ch' = ch)); clarify.
    specialize (H _ H1); generalize (instr_label _ _ _ H0); clarify.
    specialize (H _ H1); specialize (H0 _ H2); clarify.
Qed.

Lemma CFG_subtree: forall G dom bl tr, CFG_to_blocks G dom = Some bl -> subtree tr bl ->
  exists dom', subtree dom' dom /\ CFG_to_blocks G dom' = Some tr.
Proof.
  intro; apply (best_tree_ind (fun dom => forall bl tr, CFG_to_blocks G dom = Some bl -> 
    subtree tr bl -> exists dom', subtree dom' dom /\ CFG_to_blocks G dom' = Some tr)
    (fun ch => forall ch' tr, some_list (map (CFG_to_blocks G) ch) = Some ch' -> forall tr', In tr' ch' -> subtree tr tr' ->
     exists dom' dom'', In dom'' ch /\ subtree dom' dom'' /\ CFG_to_blocks G dom' = Some tr)); clarify.
    inversion H1; clarify.
      exists (Node x ch); crush.
        eexists; crush.
      specialize (H _ _ H2 _ H6 H5); clarify.
        exists x2; crush.
        econstructor; eauto.
    destruct H2; clarify.
      specialize (H _ _ H1 H3); clarify.
        repeat eexists; eauto.
      specialize (H0 _ _ H4 _ H2 H3); clarify.
        repeat eexists; eauto.
Qed.
    
Lemma CFG_dom_subtree: forall G dom dom', subtree dom' dom -> forall bl, CFG_to_blocks G dom = Some bl ->
  exists bl', CFG_to_blocks G dom' = Some bl' /\ subtree bl' bl.
Proof.
  intros G dom dom' H; induction H; clarify.
    rewrite H; eexists; crush.
    generalize (CFG_blocks_entry _ _ H2 _ H0); clarify.
      specialize (IHsubtree _ H3); clarify.
      exists x3; clarify; econstructor; eauto.
Qed.

Lemma union_add: forall s x s', NodeSet.Equal (NodeSet.union s (NodeSet.add x s')) (NodeSet.union (NodeSet.add x s) s').
Proof.
  NodeSet.fsetdec.
Qed.

Inductive prim :=
| Op : op -> prim
| Cmp : cmp -> prim
| C : const -> prim.

Inductive CPS_term :=
| Pri : prim -> list CPS_term -> CPS_term
| Var : string -> CPS_term
| Glb : string -> CPS_term
| App : list CPS_term -> CPS_term -> CPS_term
| If : CPS_term -> CPS_term -> CPS_term -> CPS_term
| Let : string -> CPS_term -> CPS_term -> CPS_term
| L : label -> CPS_term
| Letrec : label -> list string -> CPS_term -> CPS_term -> CPS_term.

Definition expr_to_CPS e :=
  match e with
  | Local x => Var x
  | Const c => Pri (C c) []
  | Global x => Glb x
  end.

Definition make_phis l (phis : list (string * node_map expr)) := some_list
  (map (fun p => match (NodeMap.find l (snd p)) with Some e => Some (expr_to_CPS e) | _ => None end) phis).

Definition make_call (bl : tree SSA_block) (l : label) (l' : label) := 
  match tree_find (fun b => if node_eq_dec l' (fst (fst b)) then true else false) bl with
  | Some (_, phis, _) =>
    match make_phis l phis with
    | Some el => Some (App el (L l'))
    | None => None
    end
  | None => None
  end.

Lemma make_phis_spec: forall l phis tl, make_phis l phis = Some tl -> 
  Forall2 (fun phi t => exists e, NodeMap.MapsTo l e (snd phi) /\ expr_to_CPS e = t) phis tl.
Proof.
  unfold make_phis; induction phis; clarify; constructor; auto.
    generalize (NodeMap.find_2 H); eexists; crush.
Qed.

Definition terminal i :=
  match i with
  | l_Br_i1 _ _ _ => true
  | l_Br_label _ => true
  | _ => false
  end.

Fixpoint instrs_to_CPS (bl : tree SSA_block) (l : label) (il : list l_instr) :=
  match il with
  | [] => None
  | i::rest => 
    if terminal i then
         match i with
         | l_Br_i1 e l1 l2 => match (make_call bl l l1, make_call bl l l2) with
                              | (Some c1, Some c2) => Some (If (expr_to_CPS e) c1 c2)
                              | _ => None
                              end
         | l_Br_label l' => make_call bl l l'
         | _ => None
         end
    else match instrs_to_CPS bl l rest with
         | Some body =>
           match i with
           | l_Assign x o e1 e2 => Some (Let x (Pri (Op o) [expr_to_CPS e1; expr_to_CPS e2]) body)
           | l_ICmp x c e1 e2 => Some (Let x (Pri (Cmp c) [expr_to_CPS e1; expr_to_CPS e2]) body)
           | _ => None
           end
         | None => None
         end
  end.

Definition block_to_CPS bl := 
  match bl with Node (l, phis, il) ch => instrs_to_CPS bl l il end.

Fixpoint blocks_to_CPS (bl : tree SSA_block) (tail : CPS_term) := 
  match bl with Node (l, phis, il) ch =>
    match block_to_CPS bl with
    | Some body => match fold_right (fun bl to => match to with Some t => blocks_to_CPS bl t | None => None end) 
                                    (Some body) ch with
                   | Some b => Some (Letrec l (map (fun p => fst p) phis) b tail)
                   | None => None
                   end
    | None => None
    end
  end.

Definition fun_body bl := 
  match block_to_CPS bl with
  | Some body => fold_right (fun bl to => match to with Some t => blocks_to_CPS bl t | None => None end)
                            (Some body) (children bl)
  | None => None
  end.

Fixpoint add_letrecs lrl t :=
  match lrl with
  | [] => t
  | (a, b, c)::rest => Letrec a b c (add_letrecs rest t)
  end.

Fixpoint blocks_to_letrecs (bl : tree SSA_block) := 
  match bl with Node (l, phis, il) ch =>
    match block_to_CPS bl with
    | Some body => match fold_right (fun bl to => match to with Some t => blocks_to_CPS bl t | None => None end) 
                                    (Some body) ch with
                   | Some b => Some (l, map (fun p => fst p) phis, b)
                   | None => None
                   end
    | None => None
    end
  end.

Lemma fold_lrl: forall ch body t, fold_right (fun bl to => match to with Some t => blocks_to_CPS bl t | None => None end) 
  (Some body) ch = Some t -> exists lrl, some_list (map (fun tr => blocks_to_letrecs tr) ch) = Some lrl /\ t = add_letrecs lrl body.
Proof.
  induction ch; clarify.
    eexists; crush.
    specialize (IHch _ _ H); clarify.
      destruct a; clarify.
      destruct s as ((?, ?), ?); clarify.
      rewrite H0; rewrite H2; rewrite H1.
      eexists; split; eauto.
Qed.

Lemma fun_lrl: forall bl t, fun_body bl = Some t -> exists t', block_to_CPS bl = Some t' /\ 
  exists lrl, some_list (map (fun tr => blocks_to_letrecs tr) (children bl)) = Some lrl /\ t = add_letrecs lrl t'.
Proof.
  unfold fun_body; clarify.
  eexists; split; eauto.
  apply fold_lrl; auto.
Qed.

Definition prog_to_CPS bl :=
  match bl with Node (l, _, _) _ =>
    blocks_to_CPS bl (App [] (L l))
  end.

Parameters a b c d : label.
Axiom abcd_distinct : (a <> b /\ b <> c /\ a <> c /\ a <> d /\ b <> d /\ c <> d).

Open Scope string_scope.
Definition test_prog := 
  {|Nodes := NodeSet.add a (NodeSet.add b (NodeSet.singleton c));
    Edges := EdgeSet.add (a, Seq, b) (EdgeSet.add (b, Seq, c) (EdgeSet.singleton (c, Seq, c)));
    Start := a; Exit := c; 
    Label := fun n => if node_eq_dec n a then Assign "x0" Add Int_ty (Const (Int_c 0)) (Const (Int_c 1))
                 else if node_eq_dec n b then Phi "x1" Int_ty (NodeMap.add a (Local "x0") (NodeMap.empty expr))
                 else Br_label|}.

Lemma find_add1: forall A k (v : A) m, NodeMap.find k (NodeMap.add k v m) = Some v.
Proof.
  intros; generalize (NodeMap.add_1 m v eq_refl(x := k)); apply NodeMap.find_1.
Qed.

Lemma find_add2: forall A k k' (v : A) m, k <> k' -> 
  NodeMap.find k (NodeMap.add k' v m) = NodeMap.find k m.
Proof.
  intros; destruct (NodeMap.find k m) eqn: found.
    generalize (NodeMap.find_2 found); intro.
      assert (k' <> k); auto.
      generalize (NodeMap.add_2 v H1 H0); apply NodeMap.find_1.
    destruct (NodeMap.find k (NodeMap.add k' v m)) eqn: found'; auto.
      assert (k' <> k); auto.
      generalize (NodeMap.find_2 found'); intro.
      generalize (NodeMap.add_3 H0 H1); intro.
      generalize (NodeMap.find_1 H2); crush.
Qed.
Hint Rewrite find_add1.

Definition test_blocks :=  
  Node (a, [], [l_Assign "x0" Add (Const (Int_c 0)) (Const (Int_c 1));
                l_Br_label b])
   [Node (b, [("x1", NodeMap.add a (Local "x0") (NodeMap.empty expr))],
             [l_Br_label c])
     [Node (c, [], [l_Br_label c]) []]].

Import Bool.
Lemma next_a: next_node test_prog Seq a = b.
Proof.
  unfold next_node; simpl.
    destruct (EdgeSet.choose (EdgeSet.filter (fun e => match e with (u, t, _) => node_beq u a && edge_type_beq t Seq end)
      (Edges test_prog))) eqn: edge; clarify; rewrite edge.
      generalize (EdgeSet.choose_spec1 edge); rewrite EdgeSet.filter_spec; crush.
        destruct e as ((?, ?), ?); rewrite andb_true_iff in *.
        specialize (internal_edge_type_dec_bl e); clarify.
        specialize (H _ H2); subst.
        unfold node_beq in *; clarify.
        rewrite EdgeSet.add_spec in *; crush.
        generalize abcd_distinct; rewrite EdgeSet.add_spec in *; crush.
        rewrite EdgeSet.singleton_spec in *; crush.
      generalize (EdgeSet.choose_spec2 edge); intro.
        unfold EdgeSet.Empty in *; specialize (H (a, Seq, b)); rewrite EdgeSet.filter_spec in *;
          crush; rewrite EdgeSet.add_spec in *; crush.
        unfold node_beq in *; rewrite andb_true_iff in *; clarify.
        destruct (node_eq_dec a a); crush.
Qed.

Lemma next_b: next_node test_prog Seq b = c.
Proof.
  unfold next_node; simpl.
    destruct (EdgeSet.choose (EdgeSet.filter (fun e => match e with (u, t, _) => node_beq u b && edge_type_beq t Seq end)
      (Edges test_prog))) eqn: edge; clarify; rewrite edge.
      generalize (EdgeSet.choose_spec1 edge); rewrite EdgeSet.filter_spec; crush.
        destruct e as ((?, ?), ?); rewrite andb_true_iff in *.
        specialize (internal_edge_type_dec_bl e); clarify.
        specialize (H _ H2); subst.
        unfold node_beq in *; clarify.
        generalize abcd_distinct; rewrite EdgeSet.add_spec in *; crush.
        rewrite EdgeSet.add_spec in *; crush.
        rewrite EdgeSet.singleton_spec in *; crush.
      generalize (EdgeSet.choose_spec2 edge); intro.
        unfold EdgeSet.Empty in *; specialize (H (b, Seq, c)); rewrite EdgeSet.filter_spec in *;
          crush; repeat (rewrite EdgeSet.add_spec in *; crush).
        unfold node_beq in *; rewrite andb_true_iff in *; clarify.
        destruct (node_eq_dec b b); crush.
Qed.

Lemma next_c: next_node test_prog Seq c = c.
Proof.
  unfold next_node; simpl.
    destruct (EdgeSet.choose (EdgeSet.filter (fun e => match e with (u, t, _) => node_beq u c && edge_type_beq t Seq end)
      (Edges test_prog))) eqn: edge; clarify; rewrite edge.
      generalize (EdgeSet.choose_spec1 edge); rewrite EdgeSet.filter_spec; crush.
        destruct e as ((?, ?), ?); rewrite andb_true_iff in *.
        specialize (internal_edge_type_dec_bl e); clarify.
        specialize (H _ H2); subst.
        unfold node_beq in *; clarify.
        generalize abcd_distinct; rewrite EdgeSet.add_spec in *; crush.
        rewrite EdgeSet.add_spec in *; crush.
        rewrite EdgeSet.singleton_spec in *; crush.
      generalize (EdgeSet.choose_spec2 edge); intro.
        unfold EdgeSet.Empty in *; specialize (H (c, Seq, b)); rewrite EdgeSet.filter_spec in *;
          crush; repeat (rewrite EdgeSet.add_spec in *; crush).
Qed.

Lemma test_CFG_to_blocks: CFG_to_blocks test_prog (Node a [Node b [Node c []]]) = Some test_blocks.
Proof.
  simpl.
    destruct (node_eq_dec a a); clarify.
    generalize abcd_distinct; destruct (node_eq_dec b a); crush.
    destruct (node_eq_dec b b); clarify.
    destruct (node_eq_dec c a); crush.
    destruct (node_eq_dec c b); crush.
    rewrite next_a; rewrite next_b; rewrite next_c; eexists; eauto.
Qed.
    
Definition test_term := 
  Letrec a []
    (Letrec b ["x1"] 
       (Letrec c [] (App [] (L c)) (App [] (L c)))
       (Let "x0" (Pri (Op Add) [Pri (C (Int_c 0)) []; Pri (C (Int_c 1)) []])
                 (App [Var "x0"] (L b))))
    (App [] (L a)).

Lemma test_prog_to_CPS: prog_to_CPS test_blocks = Some test_term.
Proof.
  simpl.
  unfold make_call; simpl.
  generalize abcd_distinct; destruct (node_eq_dec b a); crush.
  destruct (node_eq_dec b b); clarify.
  destruct (node_eq_dec c b); crush.
  destruct (node_eq_dec c c); clarify.
  destruct (node_eq_dec b c); crush.
  unfold make_phis; simpl.
  rewrite find_add1.
  eexists; eauto.
Qed.

(* What does this look like down the tree? *)
Lemma test2: exists t, prog_to_CPS (Node (b, [("x1", NodeMap.add a (Local "x0") (NodeMap.empty expr))],
             [l_Br_label c])
     [Node (c, [], [l_Br_label c]) []]) = Some t.
Proof.
  simpl.
  unfold make_call; simpl.
  generalize abcd_distinct; destruct (node_eq_dec c b); crush.
  destruct (node_eq_dec c c); clarify.
  destruct (node_eq_dec b c); crush.
  eexists; eauto.

(* semantics *)
Definition get_value t :=
  match t with
  | Pri (C v) [] => Some v
  | _ => None
  end.

Definition get_values tl :=
  fold_right (fun t vlo => match (get_value t, vlo) with (Some v, Some vl) => Some (v :: vl) | _ => None end)
             (Some []) tl.

Definition eval_prim p args :=
  match (p, args) with
  | (Op o, [v1; v2]) => eval_op start_env start_env o (Const v1) (Const v2)
  | (Cmp c, [v1; v2]) => eval_cmp start_env start_env c (Const v1) (Const v2)
  | _ => None
  end.

Definition closure := (list string * CPS_term * env)%type.
Definition fenv := node_map closure.
Definition config := (env * fenv * CPS_term)%type.

Fixpoint upd_list {A} (env : string -> option A) xl vl :=
  match (xl, vl) with
  | (x :: xrest, v :: vrest) => upd_list (upd env x v) xrest vrest
  | _ => env
  end.

Inductive step_CPS (gt : env) : config -> config -> Prop :=
| pri_frame: forall e f p tl t tl' e' f' t', step_CPS gt (e, f, t) (e', f', t') ->
    step_CPS gt (e, f, Pri p (tl ++ t :: tl')) (e, f, Pri p (tl ++ t' :: tl'))
| pri_red: forall e f p tl vl v, get_values tl = Some vl -> eval_prim p vl = Some v ->
    step_CPS gt (e, f, Pri p tl) (e, f, Pri (C v) [])
| var: forall e f x v, e x = Some v -> step_CPS gt (e, f, Var x) (e, f, Pri (C v) [])
| glb: forall e f x v, gt x = Some v -> step_CPS gt (e, f, Glb x) (e, f, Pri (C v) [])
| app_frame1: forall e f tl t e' f' t', step_CPS gt (e, f, t) (e', f', t') -> 
    step_CPS gt (e, f, App tl t) (e, f, App tl t')
| app_frame2: forall e f tl t tl' l e' f' t', step_CPS gt (e, f, t) (e', f', t') -> 
    step_CPS gt (e, f, App (tl ++ t :: tl') (L l)) (e, f, App (tl ++ t' :: tl') (L l))
| app_call: forall e f tl vl l args body env, get_values tl = Some vl -> NodeMap.find l f = Some (args, body, env) -> 
    step_CPS gt (e, f, App tl (L l)) (upd_list env args vl, f, body)
| if_frame: forall e f t e' f' t' t1 t2, step_CPS gt (e, f, t) (e', f', t') -> 
    step_CPS gt (e, f, If t t1 t2) (e, f, If t' t1 t2)
| if_false: forall e f t1 t2, step_CPS gt (e, f, If (Pri (C (Int_c 0)) []) t1 t2) (e, f, t2)
| if_true: forall e f t1 t2 v, v <> Int_c 0 -> step_CPS gt (e, f, If (Pri (C v) []) t1 t2) (e, f, t1)
| let_frame: forall e f x t1 t2 e' f' t1', step_CPS gt (e, f, t1) (e', f', t1') -> 
    step_CPS gt (e, f, Let x t1 t2) (e, f, Let x t1' t2)
| let_red: forall e f x t1 v1 t2, get_value t1 = Some v1 ->
    step_CPS gt (e, f, Let x t1 t2) (upd e x v1, f, t2)
| letrec: forall e f l args body t, 
    step_CPS gt (e, f, Letrec l args body t) (e, NodeMap.add l (args, body, e) f, t).

(* That's all very well and good, but how about a relation that singles out the chunks that correspond to
   steps in the original program? *)
(* Let is a bit weird - local environments are forgotten when nested inside App or Pri.
   This probably doesn't come up in real programs, though. *)
Inductive step_silent (gt : env) : config -> config -> Prop :=
| pri_frame_s: forall e f p tl t tl' e' f' t', step_silent gt (e, f, t) (e', f', t') ->
    step_silent gt (e, f, Pri p (tl ++ t :: tl')) (e, f, Pri p (tl ++ t' :: tl'))
| pri_red_s: forall e f p tl vl v, get_values tl = Some vl -> eval_prim p vl = Some v ->
    step_silent gt (e, f, Pri p tl) (e, f, Pri (C v) [])
| var_s: forall e f x v, e x = Some v -> step_silent gt (e, f, Var x) (e, f, Pri (C v) [])
| glb_s: forall e f x v, gt x = Some v -> step_silent gt (e, f, Glb x) (e, f, Pri (C v) [])
| if_frame_s: forall e f t e' f' t' t1 t2, step_silent gt (e, f, t) (e', f', t') -> 
    step_silent gt (e, f, If t t1 t2) (e, f, If t' t1 t2)
| if_false_s: forall e f t1 t2, step_silent gt (e, f, If (Pri (C (Int_c 0)) []) t1 t2) (e, f, t2)
| if_true_s: forall e f t1 t2 v, v <> Int_c 0 -> step_silent gt (e, f, If (Pri (C v) []) t1 t2) (e, f, t1)
| let_frame_s: forall e f x t1 t2 e' f' t1', step_silent gt (e, f, t1) (e', f', t1') -> 
    step_silent gt (e, f, Let x t1 t2) (e, f, Let x t1' t2)
| let_red_s: forall e f x t1 v1 t2, get_value t1 = Some v1 -> 
    step_silent gt (e, f, Let x t1 t2) (upd e x v1, f, t2)
| letrec_s: forall e f l args body t, 
    step_silent gt (e, f, Letrec l args body t) (e, NodeMap.add l (args, body, e) f, t).

Definition step_silent_e gt e f t t' := step_silent gt (e, f, t) (e, f, t').

Inductive step_label gt : config -> config -> Prop :=
| label_app: forall e f tl tl' vl l args body env c2, 
    Forall2 (fun t t' => clos_refl_trans _ (step_silent_e gt e f) t t') tl tl' -> 
    get_values tl' = Some vl -> NodeMap.find l f = Some (args, body, env) -> 
    clos_refl_trans _ (step_silent gt) (upd_list env args vl, f, body) c2 ->
    step_label gt (e, f, App tl (L l)) c2.

Lemma silent_step: forall gt c c', step_silent gt c c' -> step_CPS gt c c'.
Proof.
  intros; induction H; econstructor; eauto.
Qed.

Hint Immediate rt_refl.

Lemma silent_steps: forall gt c c', clos_refl_trans _ (step_silent gt) c c' -> 
  clos_refl_trans _ (step_CPS gt) c c'.
Proof.
  intros; induction H; clarify.
    apply rt_step; apply silent_step; auto.
    eapply rt_trans; eauto.
Qed. 

Lemma t_rt_trans: forall {A} (R : A -> A -> Prop) x y z, clos_refl_trans _ R y z -> clos_trans _ R x y -> 
  clos_trans _ R x z.
Proof.
  intros ? ? ? ? ? H; induction H; clarify.
    eapply t_trans; eauto; apply t_step; auto.
Qed.

Lemma rt_t_trans: forall {A} (R : A -> A -> Prop) x y z, clos_refl_trans _ R x y -> clos_trans _ R y z -> 
  clos_trans _ R x z.
Proof.
  intros ? ? ? ? ? H; induction H; clarify.
    eapply t_trans; eauto; apply t_step; auto.
Qed.

Lemma expr_eval: forall gt env f e v, eval_expr env gt e = Some v ->
  clos_refl_trans _ (step_silent_e gt env f) (expr_to_CPS e) (Pri (C v) []).
Proof.
  destruct e; clarify.
    constructor; constructor; auto.
    constructor; constructor; auto.
Qed.

Lemma pri_frame_star: forall p h r gt env f t t', clos_refl_trans _ (step_silent_e gt env f) t t' ->
  clos_refl_trans _ (step_silent_e gt env f) (Pri p (h ++ t :: r)) (Pri p (h ++ t' :: r)).
Proof.
  intros; induction H; clarify.
    constructor; eapply pri_frame_s; eauto.
    eapply rt_trans; eauto.
Qed.

Corollary pri_frame_star1: forall p r gt env f t t', clos_refl_trans _ (step_silent_e gt env f) t t' ->
  clos_refl_trans _ (step_silent_e gt env f) (Pri p (t :: r)) (Pri p (t' :: r)).
Proof.
  intros; generalize (pri_frame_star p [] r H); clarify.
Qed.

Corollary pri_frame_star2: forall p t0 gt env f t t', clos_refl_trans _ (step_silent_e gt env f) t t' ->
  clos_refl_trans _ (step_silent_e gt env f) (Pri p ([t0; t])) (Pri p ([t0; t'])).
Proof.
  intros; generalize (pri_frame_star p [t0] [] H); clarify.
Qed.

Lemma pri_eval_op: forall gt env f e1 e2 op v, eval_op env gt op e1 e2 = Some v ->
  clos_refl_trans _ (step_silent_e gt env f) (Pri (Op op) [expr_to_CPS e1; expr_to_CPS e2]) (Pri (C v) []).
Proof.
  intros; unfold eval_op in H; destruct (eval_expr env gt e1) eqn: v1; clarify.
    destruct (eval_expr env gt e2) eqn: v2; clarify.
      eapply rt_trans.
        apply pri_frame_star1; apply expr_eval; eauto.
        eapply rt_trans.
          eapply pri_frame_star2; apply expr_eval; eauto.
          constructor; eapply pri_red_s; clarify.
      destruct c0; discriminate.
Qed.

Lemma pri_eval_cmp: forall gt env f e1 e2 cmp v, eval_cmp env gt cmp e1 e2 = Some v ->
  clos_refl_trans _ (step_silent_e gt env f) (Pri (Cmp cmp) [expr_to_CPS e1; expr_to_CPS e2]) (Pri (C v) []).
Proof.
  intros; unfold eval_cmp in H; destruct (eval_expr env gt e1) eqn: v1; clarify.
    destruct (eval_expr env gt e2) eqn: v2; clarify.
      eapply rt_trans.
        apply pri_frame_star1; apply expr_eval; eauto.
        eapply rt_trans.
          eapply pri_frame_star2; apply expr_eval; eauto.
          constructor; eapply pri_red_s; clarify.
      destruct c0; discriminate.
Qed.

Lemma let_frame_star: forall x t2 gt env f t t', clos_refl_trans _ (step_silent_e gt env f) t t' ->
  clos_refl_trans _ (step_silent_e gt env f) (Let x t t2) (Let x t' t2).
Proof.
  intros; induction H; clarify.
    constructor; econstructor; eauto.
    eapply rt_trans; eauto.
Qed.

Lemma if_frame_star: forall t1 t2 gt env f t t', clos_refl_trans _ (step_silent_e gt env f) t t' ->
  clos_refl_trans _ (step_silent_e gt env f) (If t t1 t2) (If t' t1 t2).
Proof.
  intros; induction H; clarify.
    constructor; econstructor; eauto.
    eapply rt_trans; eauto.
Qed.

Lemma upd_nil: forall {A : Type} (env : string -> option A) xs, upd_list env xs [] = env.
Proof.
  destruct xs; auto.
Qed.

Lemma silent_envs: forall gt e f t t', clos_refl_trans _ (step_silent_e gt e f) t t' ->
  clos_refl_trans _ (step_silent gt) (e, f, t) (e, f, t').
Proof.
  intros; induction H; unfold step_silent_e in *; clarify.
    constructor; auto.
    eapply rt_trans; eauto.
Qed.

Lemma app_frame_star: forall l h r gt env f t t', clos_refl_trans _ (step_silent_e gt env f) t t' ->
  clos_refl_trans _ (step_CPS gt) (env, f, App (h ++ t :: r) (L l)) (env, f, App (h ++ t' :: r) (L l)).
Proof.
  intros; induction H; clarify.
    constructor; eapply app_frame2; apply silent_step; eauto.
    eapply rt_trans; eauto.
Qed.

Corollary app_frame_star1: forall l r gt env f t t', clos_refl_trans _ (step_silent_e gt env f) t t' ->
  clos_refl_trans _ (step_CPS gt) (env, f, App (t :: r) (L l)) (env, f, App (t' :: r) (L l)).
Proof.
  intros; generalize (app_frame_star l [] r H); clarify.
Qed.

Close Scope string_scope.
Lemma app_cons_assoc_r: forall {A} x (y : A) z, x ++ y :: z = (x ++ [y]) ++ z.
Proof.
  clarify.
Qed.

Lemma app_frame_star_list: forall tl tl' gt env f, Forall2 (fun t t' => clos_refl_trans _ (step_silent_e gt env f) t t') tl tl' ->
  forall l rest, clos_refl_trans _ (step_CPS gt) (env, f, App (rest ++ tl) (L l)) (env, f, App (rest ++ tl') (L l)).
Proof.
  intros until f; intro; induction H; clarify.
    eapply rt_trans; [apply app_frame_star; eauto|].
    rewrite app_cons_assoc_r; rewrite (app_cons_assoc_r _ _ l'); apply IHForall2.
Qed.

Lemma app_frame_star_all: forall l tl tl' gt env f, Forall2 (fun t t' => clos_refl_trans _ (step_silent_e gt env f) t t') tl tl' ->
  clos_refl_trans _ (step_CPS gt) (env, f, App tl (L l)) (env, f, App tl' (L l)).
Proof.
  intros; generalize (app_frame_star_list H l []); auto.
Qed.

Lemma label_step: forall gt c c', step_label gt c c' -> clos_trans config (step_CPS gt) c c'.
Proof.
  intros; inversion H; clarify.
    eapply t_rt_trans; [apply silent_steps; eassumption|].
    eapply rt_t_trans; [apply app_frame_star_all; apply H0 | apply t_step; apply app_call; eauto].
Qed.

Lemma label_add_steps: forall gt c c' c'', step_label gt c c' ->
  clos_refl_trans _ (step_silent gt) c' c'' -> step_label gt c c''.
Proof.
  intros; inversion H; clarify; econstructor; eauto.
    eapply rt_trans; eauto.
Qed.

Check add_letrecs.
Fixpoint upd_funs f (lrl : list (label * list string * CPS_term)) (e : env) :=
  match lrl with
  | [] => f
  | (l, xs, b)::rest => upd_funs (NodeMap.add l (xs, b, e) f) rest e
  end.

Lemma clos_refl_inv: forall {A} R x y, clos_refl_trans A R x y -> 
  x = y \/ exists z, R x z /\ clos_refl_trans A R z y.
Proof.
  intros; induction H; clarify.
    right; eexists; crush.
    destruct IHclos_refl_trans1; [destruct IHclos_refl_trans2; [left | right] | right]; crush; eexists; eauto.
      split; eauto; eapply rt_trans; eauto.
Qed.  

Lemma step_letrecs: forall gt lrl e f t e' f' t', clos_refl_trans _ (step_silent gt) (e, f, add_letrecs lrl t) (e', f', t') ->
  (exists lrl1 lrl2, lrl = lrl1 ++ lrl2 /\ e' = e /\ t' = add_letrecs lrl2 t /\ f' = upd_funs f lrl1 e) \/ 
  (clos_refl_trans _ (step_silent gt) (e, upd_funs f lrl e, t) (e', f', t')).
Proof.
  induction lrl; clarify.
    destruct a0 as ((?, ?), ?).
    generalize (clos_refl_inv H); intro inv; destruct inv; clarify.
      left; exists ([] : list (label * list string * CPS_term)); exists ((l, l0, c0) :: lrl); auto.
      inversion H0; clarify.
        specialize (IHlrl _ _ _ _ _ _ H1); destruct IHlrl; clarify.
        left; eexists; exists x0; crush.
Qed.

Fixpoint not_def l t :=
  match t with
  | Letrec l' _ _ t => l <> l' /\ not_def l t
  | If _ t f => not_def l t /\ not_def l f
  | Let _ _ t => not_def l t
  | _ => True
  end.

Lemma not_def_step: forall c c' l gt, step_silent gt c c' -> not_def l (snd c) -> not_def l (snd c').
Proof.
  intros; destruct c0 as ((?, ?), t); induction t; inversion H; clarify.
Qed.

Lemma not_def_mono: forall c c' l gt, clos_refl_trans _ (step_silent gt) c c' -> not_def l (snd c) -> not_def l (snd c').
Proof.
  intros; induction H; auto; eapply not_def_step; eauto.
Qed.

Lemma labels_mono: forall c l def gt c', clos_refl_trans _ (step_silent gt) c c' -> not_def l (snd c) ->
  NodeMap.find l (snd (fst c)) = Some def -> NodeMap.find l (snd (fst c')) = Some def.
Proof.
  intros; induction H; clarify.
    inversion H; clarify.
      rewrite find_add2; auto.
    generalize (not_def_mono _ H H0); clarify.
Qed.

Inductive for_none {A} P : tree A -> Prop :=
| for_noneI: forall x ch, ~P x -> Forall (for_none P) ch ->
    for_none P (Node x ch).

Inductive for_one {A} (P : A -> Prop) : tree A -> Prop :=
| for_one_t: forall x ch, P x -> Forall (for_none P) ch ->
    for_one P (Node x ch)
| for_one_f: forall x ch, ~P x -> for_one_aux P ch ->
    for_one P (Node x ch)
with for_one_aux {A} (P : A -> Prop) : list (tree A) -> Prop :=
| for_one_nil: for_one_aux P []
| for_one_cons: forall tr rest, ((for_one P tr /\ Forall (for_none P) rest) \/ 
    (for_none P tr /\ for_one_aux P rest)) -> for_one_aux P (tr::rest).
Hint Resolve for_one_nil.

Lemma for_none_one: forall A (P : A -> Prop) tr, for_none P tr -> for_one P tr.
Proof.
  intros A P; apply (best_tree_ind (fun tr => for_none P tr -> for_one P tr)
    (fun ch => Forall (for_none P) ch -> for_one_aux P ch)); clarify.
    inversion H0; clarify.
      apply for_one_f; eauto.
    inversion H1; clarify.
      econstructor; auto.
Qed.

Lemma for_none_one_list: forall A (P : A -> Prop) ch, Forall (for_none P) ch -> for_one_aux P ch.
Proof.
  induction ch; clarify.
    inversion H; clarify.
    econstructor; auto.
Qed.

Lemma instrs_not_def: forall bl l il t l', instrs_to_CPS bl l il = Some t -> not_def l' t.
Proof.
  induction il; clarify.
    destruct a0; clarify.
      unfold make_call in *; autorewrite with core in *; clarify.
        destruct x1 as ((?, ?), ?); destruct x2 as ((?, ?), ?); autorewrite with core in *; clarify.
      unfold make_call in *; autorewrite with core in *; clarify.
        destruct x as ((?, ?), ?); autorewrite with core in *; clarify.
    destruct a0; clarify.
Qed.

Lemma fun_not_def: forall l bl t, fun_body bl = Some t -> Forall (for_none (fun x => fst (fst x) = l)) (children bl) -> not_def l t.
Proof.
  intro; apply (best_tree_ind(fun bl => forall t, fun_body bl = Some t -> Forall (for_none (fun x => fst (fst x) = l)) (children bl) -> not_def l t)
    (fun ch => forall b t, fold_right (fun bl to => match to with Some t => blocks_to_CPS bl t | None => None end) (Some b) ch = Some t -> 
                           not_def l b -> Forall (for_none (fun x => fst (fst x) = l)) ch -> not_def l t)); clarify.
    destruct x as ((?, ?), ?); autorewrite with core in *; clarify.
      eapply H; eauto.
      eapply instrs_not_def; eauto.
    inversion H3; destruct tr; destruct p as ((?, ?), ?); clarify.
      inversion H7; clarify; split; auto.
      eapply H0; eauto.
Qed.

Lemma funs_not_def: forall l ch t0 t, fold_right (fun bl to => match to with Some t => blocks_to_CPS bl t | None => None end) 
  (Some t0) ch = Some t -> Forall (for_none (fun x => fst (fst x) = l)) ch -> not_def l t0 -> not_def l t.
Proof.
  induction ch; clarify.
    inversion H0; clarify.
    specialize (IHch _ _ H); clarify.
    destruct a0; clarify.
    destruct s as ((?, ?), ?); autorewrite with core in *; clarify.
    inversion H5; clarify.
Qed.

Lemma construct_body: forall bl body, fun_body bl = Some body -> 
  (forall l, for_one (fun x => fst (fst x) = l) bl) -> 
  exists tail, block_to_CPS bl = Some tail /\
  forall gt e f, exists f', clos_refl_trans _ (step_silent gt) (e, f, body) (e, f', tail) /\ 
  forall l phis il ch', In (Node (l, phis, il) ch') (children bl) -> 
    exists b, fun_body (Node (l, phis, il) ch') = Some b /\ 
    NodeMap.find l f' = Some (map (fun p => fst p) phis, b, e).
Proof.
  apply (best_tree_ind (fun bl => forall body, fun_body bl = Some body ->
    (forall l, for_one (fun x => fst (fst x) = l) bl) -> 
    exists tail, block_to_CPS bl = Some tail /\
    forall gt e f, exists f', clos_refl_trans _ (step_silent gt) (e, f, body) (e, f', tail) /\ 
    forall l phis il ch', In (Node (l, phis, il) ch') (children bl) ->
    exists b, fun_body (Node (l, phis, il) ch') = Some b /\ 
    NodeMap.find l f' = Some (map (fun p => fst p) phis, b, e)) 
  (fun ch => forall t t', fold_right (fun bl to => match to with Some t => blocks_to_CPS bl t | None => None end) 
    (Some t) ch = Some t' -> (forall l, for_one_aux (fun x => fst (fst x) = l) ch /\ (not_def l t \/ Forall (for_none (fun x => fst (fst x) = l)) ch)) ->
    forall gt e f, exists f', clos_refl_trans _ (step_silent gt) (e, f, t') (e, f', t) /\ 
    forall l phis il ch', In (Node (l, phis, il) ch') ch ->
    exists b, fun_body (Node (l, phis, il) ch') = Some b /\ 
    NodeMap.find l f' = Some (map (fun p => fst p) phis, b, e))); clarify; eauto.
    eexists; crush.
      apply H; auto.
      intro; specialize (H1 l); inversion H1; clarify.
        split; auto; apply for_none_one_list; auto.
        destruct x as ((?, ?), ?); left; eapply instrs_not_def; eauto.
    eexists; crush.
    destruct tr; clarify.
      destruct p as ((?, ?), ?); autorewrite with core in *; clarify.
      specialize (H x1); clarify.
      destruct H; intros.
        eexists; crush.
        specialize (H2 l3); clarify.
          inversion H; clarify.
          destruct H6; clarify; apply for_none_one; auto.
        clarify.
          assert (forall l3 : label, for_one_aux (fun x => fst (fst x) = l3) rest /\ (not_def l3 t \/ Forall (for_none (fun x => fst (fst x) = l3)) rest))
            as uniqueness; intros.
            specialize (H2 l3); clarify; inversion H2; clarify.
              destruct H8; clarify.
                split; [apply for_none_one_list; auto | destruct H6; clarify].
                destruct H6; clarify.
                  inversion H6; clarify.
            specialize (H0 _ _ H1 uniqueness gt e (NodeMap.add l0 (map (fun p => fst p) l1, x1, e) f));
              clarify.
            eexists; split.
              eapply rt_trans; [eapply rt_step; econstructor | eauto].
              clarify.
                destruct H7; clarify.
                inversion H7; clarify.
                setoid_rewrite H3; rewrite H4; repeat eexists; eauto.
                generalize (labels_mono(def := (map (fun p => fst p) phis, x1, e)) l3 H0); clarify.
                apply H7; auto.
                specialize (H2 l3); clarify.
                inversion H2; clarify.
                destruct H10; clarify.
                  eapply funs_not_def; eauto.
                    destruct H8; clarify; inversion H8; clarify.
                    inversion H13; clarify.
                  inversion H9; clarify.
Qed.

Lemma appears_CFG: forall G l dom bl, CFG_to_blocks G dom = Some bl ->
  (for_one (fun x => x = l) dom -> for_one (fun x => fst (fst x) = l) bl) /\
  (for_none (fun x => x = l) dom -> for_none (fun x => fst (fst x) = l) bl).
Proof.
  intros G l; apply (best_tree_ind (fun dom => forall bl, CFG_to_blocks G dom = Some bl -> (for_one (fun x => x = l) dom -> 
    for_one (fun x => fst (fst x) = l) bl) /\ (for_none (fun x => x = l) dom -> 
    for_none (fun x => fst (fst x) = l) bl)) (fun ch => forall ch', fold_left (fun r tr => let (y, o) := (r, CFG_to_blocks G tr) in
    match y with Some r' => match o with Some tr' => Some (r' ++ [tr'])%list | None => None end | None => None end) 
    ch (Some []) = Some ch' -> (for_one_aux (fun x => x = l) ch -> for_one_aux (fun x => fst (fst x) = l) ch') /\
    (Forall (for_none (fun x => x = l)) ch -> Forall (for_none (fun x => fst (fst x) = l)) ch'))); clarify.
    generalize (instr_label _ _ _ H0); specialize (H _ H1); clarify.
      split; clarify.
        inversion H2; clarify; [apply for_one_t | apply for_one_f]; auto.
        inversion H2; clarify; constructor; auto.
    destruct (CFG_to_blocks G tr); [rewrite CFG_acc_prefix in * | rewrite CFG_acc_None in *]; clarify.
      specialize (H0 x); rewrite H1 in H0; clarify.
      specialize (H t); split; intro H'; inversion H'; clarify.
      constructor; destruct H4; clarify.
Qed.

Corollary appears_once_CFG: forall G dom bl l, for_one (fun x => x = l) dom -> 
  CFG_to_blocks G dom = Some bl -> for_one (fun x => fst (fst x) = l) bl.
Proof.
  intros; generalize (appears_CFG _ l _ H0); crush.
Qed.

Lemma not_appears_CFG: forall G l dom bl, CFG_to_blocks G dom = Some bl ->
  for_none (fun x => x = l) dom -> for_none (fun x => fst (fst x) = l) bl.
Proof.
  apply appears_CFG.
Qed.

Lemma no_subtree: forall {A} (P : A -> Prop) tr, for_none P tr ->
  forall tr', subtree tr' tr -> ~P (root tr').
Proof.
  induction tr using tree_ind'; clarify.
    inversion H1; clarify.
      inversion H0; clarify.
      inversion H0; clarify.
        rewrite Forall_forall in *; specialize (H _ H5); clarify.
Qed.

Lemma same_subtree: forall {A} (P : A -> Prop) tr, for_one P tr -> 
  forall tr' tr'', P (root tr') -> subtree tr' tr -> P (root tr'') -> subtree tr'' tr ->
  tr' = tr''.
Proof.
  intros A P; apply (best_tree_ind (fun tr => for_one P tr -> forall tr' tr'', 
    P (root tr') -> subtree tr' tr -> P (root tr'') -> subtree tr'' tr -> tr' = tr'')
    (fun ch => for_one_aux P ch -> forall tr' tr'0 tr'' tr''0, P (root tr') -> In tr'0 ch -> 
     subtree tr' tr'0 -> P (root tr'') -> In tr''0 ch -> subtree tr'' tr''0 -> tr' = tr'')); clarify.
    inversion H2; inversion H4; inversion H0; clarify.
      rewrite Forall_forall in *; specialize (H13 _ H9).
        generalize (no_subtree H13 H8); clarify.
      rewrite Forall_forall in *; specialize (H13 _ H8).
        generalize (no_subtree H13 H7); clarify.
      rewrite Forall_forall in *; specialize (H16 _ H8).
        generalize (no_subtree H16 H7); clarify.
      eauto.
    inversion H1; clarify.
      destruct H9; clarify.
        destruct H3; clarify. 
          destruct H6; clarify.
            rewrite Forall_forall in *; specialize (H9 _ H3).
            generalize (no_subtree H9 H7); clarify.
          rewrite Forall_forall in *; specialize (H9 _ H3).
            generalize (no_subtree H9 H4); clarify.
      destruct H3; clarify.
        generalize (no_subtree H8 H4); clarify.
        destruct H6; clarify.
          generalize (no_subtree H8 H7); clarify.
          eauto.
Qed.  

Lemma find_root: forall {A} (f : A -> bool) tr, f (root tr) = true -> tree_find f tr = Some (root tr).
Proof.
  destruct tr; clarify.
Qed.

Arguments tree_find A f tr : simpl never.
Arguments subtree_find A f tr : simpl never.
Arguments fun_body bl : simpl never.

(* If there are no back-edges, then all jumps from a node will be either back to that node
   or to one of its children in the dominator tree (is this true?). *)
(* We need to know that any vars needed in the next block will be passed in as 
   arguments to the phi or given the right value in outer lets, which is not currently true. *)
Lemma CPS_complete: forall G q gt p0 p env st al p' env' args dom', 
  step G q gt (p0, p, env, st, al) [] (p, p', env', st, al) ->
  forall dom bl body xs f, CFG_to_blocks G dom = Some bl -> 
  (forall l, for_one (fun x => x = l) dom) -> p = root dom -> 
  fun_body bl = Some body -> NodeMap.find p f = Some (xs, body, env) -> 
  make_phis p0 (snd (fst (root bl))) = Some args -> xs = map (fst(A := string)(B := node_map expr)) (snd (fst (root bl))) ->
  p' = root dom' -> (dom' = dom \/ In dom' (children dom)) ->
  exists bl', CFG_to_blocks G dom' = Some bl' /\ 
    exists f' args', step_label gt (env, f, App args (L p)) (env', f', App args' (L p')) /\ 
    exists xs' body' cenv', fun_body bl' = Some body' /\ 
    NodeMap.find p' f' = Some (xs', body', cenv') /\ xs' = map (fst(A := string)(B := node_map expr)) (snd (fst (root bl'))) /\
    make_phis p (snd (fst (root bl'))) = Some args'.
Proof.
  intros.
    generalize (construct_body H3); intro con.
    destruct con; [intro; eapply appears_once_CFG; eauto | clarify].
    generalize (appears_once_CFG _ (H1 (root dom)) H0); intro unique_p.
    generalize (CFG_dom_subtree(dom := dom)(dom' := dom') G); intro CFG'.
    assert (subtree dom' dom) as dom_sub; [destruct dom; destruct H8; clarify; econstructor; clarify | specialize (CFG' dom_sub _ H0)].
    destruct dom; clarify.
    exists x0; clarify.
    destruct x1 as ((p, phis), il).
    generalize (instr_label _ _ _ H0); clarify.
    unfold instr_to_block in H0; inversion H; match goal with [H': Label G p = ?a |- _] => rewrite H' in H0 end; 
      clarify; try discriminate.
      (* Assign *)
      specialize (H10 gt env f); clarify.
      unfold make_call in H0; autorewrite with core in *; clarify.
      destruct x4 as ((?, ?), ?); autorewrite with core in *; clarify.
      eexists; exists x4; split.
        econstructor; clarify; eauto.
          rewrite upd_nil; eapply rt_trans; eauto.
          eapply rt_trans.
            apply silent_envs; apply let_frame_star; apply pri_eval_op; eauto.
            constructor; apply let_red_s; simpl; auto.
        generalize (find_subtree _ _ H0); clarify.
          destruct H8; clarify.
            (* self-loop *)
            unfold instr_to_block in H2; rewrite H14 in H2; rewrite H7 in H2; inversion H2.
              eexists; eexists; eexists; split; [apply H3|].
              generalize (same_subtree unique_p); intro locate_p.
              specialize (locate_p (Node (p, [], [l_Assign x1 op e1 e2; l_Br_label (next_node G Seq p)]) x2) x3); simpl in locate_p; clarify.
              destruct x3; destruct p1 as ((?, ?), ?); simpl in H13; inversion H13; simpl in *.
              repeat (rewrite H17 in *); clear H17; clarify.
              inversion locate_p; clarify.
              split; clarify.
                generalize (labels_mono(def := ([], body, env)) p H5); simpl; intro same_f; apply same_f; auto.
                  eapply fun_not_def; eauto.
                    inversion unique_p; clarify; auto.
            (* to child *)
            generalize (CFG_blocks_entry _ _ H7 _ H8); clarify.
              rewrite H11 in H2; clarify.
              destruct x0.
              destruct s as ((?, ?), ?); specialize (H9 _ _ _ _ H16); destruct H9 as [? [? ?]].
              generalize (appears_once_CFG(bl := Node (p, [], [l_Assign x1 op e1 e2; l_Br_label (next_node G Seq p)]) x2) 
                G (H1 (next_node G Seq p))); simpl; intro unique_p'.
              unfold instr_to_block in unique_p'; rewrite H14 in unique_p'; rewrite H7 in unique_p'; specialize (unique_p' eq_refl).
              generalize (same_subtree(tr' := x3)(tr'' := Node (l3, l4, l5) l2) unique_p'); rewrite H13; simpl; intro locate_p'.
              assert (x3 = Node (l3, l4, l5) l2); [apply locate_p'; auto | clarify].
                destruct dom'; clarify.
                  generalize (instr_label _ _ _ H11); clarify.
                repeat eexists; eauto.
      (* ICmp *)
      specialize (H10 gt env f); clarify.
      unfold make_call in H0; autorewrite with core in *; clarify.
      destruct x4 as ((?, ?), ?); autorewrite with core in *; clarify.
      eexists; exists x4; split.
        econstructor; clarify; eauto.
          rewrite upd_nil; eapply rt_trans; eauto.
          eapply rt_trans.
            apply silent_envs; apply let_frame_star; apply pri_eval_cmp; eauto.
            constructor; apply let_red_s; simpl; auto.
        generalize (find_subtree _ _ H0); clarify.
          destruct H8; clarify.
            (* self-loop *)
            unfold instr_to_block in H2; rewrite H14 in H2; rewrite H7 in H2; inversion H2.
              eexists; eexists; eexists; split; [apply H3|].
              generalize (same_subtree unique_p); intro locate_p. 
              specialize (locate_p (Node (p, [], [l_ICmp x1 cmp e1 e2; l_Br_label (next_node G Seq p)]) x2) x3); simpl in locate_p; clarify.
              destruct x3. destruct p1 as ((?, ?), ?); simpl in H13; inversion H13; simpl in *.
              repeat (rewrite H17 in *); clear H17; clarify.
              inversion locate_p; clarify.
              split; clarify.
                generalize (labels_mono(def := ([], body, env)) p H5); simpl; intro same_f; apply same_f; auto.
                  eapply fun_not_def; eauto.
                    inversion unique_p; clarify; auto.
            (* to child *)
            generalize (CFG_blocks_entry _ _ H7 _ H8); clarify.
              rewrite H11 in H2; clarify.
              destruct x0.
              destruct s as ((?, ?), ?); specialize (H9 _ _ _ _ H16); destruct H9 as [? [? ?]].
              generalize (appears_once_CFG(bl := Node (p, [], [l_ICmp x1 cmp e1 e2; l_Br_label (next_node G Seq p)]) x2) 
                G (H1 (next_node G Seq p))); simpl; intro unique_p'.
              unfold instr_to_block in unique_p'; rewrite H14 in unique_p'; rewrite H7 in unique_p'; specialize (unique_p' eq_refl).
              generalize (same_subtree(tr' := x3)(tr'' := Node (l3, l4, l5) l2) unique_p'); rewrite H13; simpl; intro locate_p'.
              assert (x3 = Node (l3, l4, l5) l2); [apply locate_p'; auto | clarify].
                destruct dom'; clarify.
                  generalize (instr_label _ _ _ H11); clarify.
                repeat eexists; eauto.
      (* Br_i1 false *)
      specialize (H10 gt env' f); clarify.
      unfold make_call in H5; autorewrite with core in *; clarify.
      destruct x4 as ((?, ?), ?); autorewrite with core in *; clarify.
      eexists; exists x4; split.
        econstructor; clarify; eauto.
          rewrite upd_nil; eapply rt_trans; eauto.
          eapply rt_trans.
            apply silent_envs; apply if_frame_star; apply expr_eval; eauto.
            constructor; apply if_false_s.
        generalize (find_subtree _ _ H5); clarify.
          destruct H8; clarify.
            (* self-loop *)
            unfold instr_to_block in H2; rewrite H14 in H2; rewrite H7 in H2; inversion H2.
              eexists; eexists; eexists; split; [apply H3|].
              generalize (same_subtree unique_p); intro locate_p.
              specialize (locate_p (Node (p, [], [l_Br_i1 e (next_node G T p) (next_node G F p)]) x2) x3); simpl in locate_p; clarify.
              destruct x3; destruct p1 as ((?, ?), ?).
              repeat (rewrite H17 in *); clear H17; clarify.
              inversion locate_p; clarify.
              split; clarify.
              generalize (labels_mono(def := ([], body, env')) p H9); simpl; intro same_f; apply same_f; auto.
              eapply fun_not_def; eauto.
              inversion unique_p; clarify; auto.
            (* to child *)
            generalize (CFG_blocks_entry _ _ H7 _ H8); clarify.
              rewrite H12 in H2; clarify.
              destruct x0.
              destruct s as ((?, ?), ?); specialize (H10 _ _ _ _ H18); destruct H10 as [? [? ?]].
              generalize (appears_once_CFG(bl := Node (p, [], [l_Br_i1 e (next_node G T p) (next_node G F p)]) x2)
                G (H1 (next_node G F p))); simpl; intro unique_p'.
              unfold instr_to_block in unique_p'; rewrite H14 in unique_p'; rewrite H7 in unique_p'; specialize (unique_p' eq_refl).
              generalize (same_subtree(tr' := x3)(tr'' := Node (l3, l4, l5) l2) unique_p'); rewrite H15; simpl; intro locate_p'.
              assert (x3 = Node (l3, l4, l5) l2); [apply locate_p'; auto | clarify].
                destruct dom'; clarify.
                  generalize (instr_label _ _ _ H12); clarify.
                repeat eexists; eauto.
      (* Br_i1 true *)
      specialize (H10 gt env' f); clarify.
      unfold make_call in H0; autorewrite with core in *; clarify.
      destruct x4 as ((?, ?), ?); clarify.
      eexists; exists x4; split.
        econstructor; clarify; eauto.
          rewrite upd_nil; eapply rt_trans; eauto.
          eapply rt_trans.
            apply silent_envs; apply if_frame_star; apply expr_eval; eauto.
            constructor; apply if_true_s; auto.
        generalize (find_subtree _ _ H0); clarify.
          destruct H8; clarify.
            (* self-loop *)
            unfold instr_to_block in H2; rewrite H17 in H2; rewrite H7 in H2; inversion H2.
              eexists; eexists; eexists; split; [apply H3|].
              generalize (same_subtree unique_p); intro locate_p.
              specialize (locate_p (Node (p, [], [l_Br_i1 e (next_node G T p) (next_node G F p)]) x2) x1); simpl in locate_p; clarify.
              destruct x1; destruct p1 as ((?, ?), ?).
              repeat (rewrite H15 in *); clear H15; clarify.
              inversion locate_p; clarify.
              split; clarify.
              generalize (labels_mono(def := ([], body, env')) p H9); simpl; intro same_f; apply same_f; auto.
              eapply fun_not_def; eauto.
              inversion unique_p; clarify; auto.
            (* to child *)
            generalize (CFG_blocks_entry _ _ H7 _ H8); clarify.
              rewrite H12 in H2; clarify.
              destruct x0.
              destruct s as ((?, ?), ?); specialize (H10 _ _ _ _ H18); destruct H10 as [? [? ?]].
              generalize (appears_once_CFG(bl := Node (p, [], [l_Br_i1 e (next_node G T p) (next_node G F p)]) x2)
                G (H1 (next_node G T p))); simpl; intro unique_p'.
              unfold instr_to_block in unique_p'; rewrite H17 in unique_p'; rewrite H7 in unique_p'; specialize (unique_p' eq_refl).
              generalize (same_subtree(tr' := x1)(tr'' := Node (l3, l4, l5) l2) unique_p'); rewrite H14; simpl; intro locate_p'.
              assert (x1 = Node (l3, l4, l5) l2); [apply locate_p'; auto | clarify].
                destruct dom'; clarify.
                  generalize (instr_label _ _ _ H12); clarify.
                repeat eexists; eauto.
      (* Br_label *)
      specialize (H10 gt env' f); clarify.
      unfold make_call in H9; autorewrite with core in *; clarify.
      destruct x3 as ((?, ?), ?); clarify.
      eexists; exists x3; split.
        econstructor; clarify; eauto.
        generalize (find_subtree _ _ H9); clarify.
          destruct H8; clarify.
            (* self-loop *)
            unfold instr_to_block in H2; rewrite H13 in H2; rewrite H7 in H2; inversion H2.
              eexists; eexists; eexists; split; [apply H3|].
              generalize (same_subtree unique_p); intro locate_p.
              specialize (locate_p (Node (p, [], [l_Br_label (next_node G Seq p)]) x2) x); simpl in locate_p; clarify.
              destruct x. destruct p1 as ((?, ?), ?).
              repeat (rewrite H17 in *); clear H17; clarify.
              inversion locate_p; clarify.
              split; clarify.
              generalize (labels_mono(def := ([], body, env')) p H0); simpl; intro same_f; apply same_f; auto.
              eapply fun_not_def; eauto.
              inversion unique_p; clarify; auto.
            (* to child *)
            generalize (CFG_blocks_entry _ _ H7 _ H8); clarify.
              rewrite H11 in H2; clarify.
              destruct x0.
              destruct s as ((?, ?), ?); specialize (H5 _ _ _ _ H16); destruct H5 as [? [? ?]].
              generalize (appears_once_CFG(bl := Node (p, [], [l_Br_label (next_node G Seq p)]) x2)
                G (H1 (next_node G Seq p))); simpl; intro unique_p'.
              unfold instr_to_block in unique_p'; rewrite H13 in unique_p'; rewrite H7 in unique_p'; specialize (unique_p' eq_refl).
              generalize (same_subtree(tr' := x)(tr'' := Node (l3, l4, l5) l2) unique_p'); rewrite H14; simpl; intro locate_p'.
              assert (x = Node (l3, l4, l5) l2); [apply locate_p'; auto | clarify].
                destruct dom'; clarify.
                  generalize (instr_label _ _ _ H11); clarify.
                repeat eexists; eauto.
      (* Phi *)
      specialize (H10 gt (upd env x1 v) f); clarify.
      unfold make_call in H9; autorewrite with core in *; clarify.
      destruct x5 as ((?, ?), ?); clarify.
      rewrite H0 in H20; clarify.
      eexists; exists x5; split.
        econstructor; [constructor; [apply expr_eval|] | | | ]; eauto; clarify; eauto.
        generalize (find_subtree _ _ H9); clarify.
          destruct H8; clarify.
            (* self-loop *)
            unfold instr_to_block in H2; rewrite H17 in H2; rewrite H7 in H2; inversion H2.
              eexists; eexists; eexists; split; [apply H3|].
              generalize (same_subtree unique_p); intro locate_p.
              specialize (locate_p (Node (p, [(x1, vals)], [l_Br_label (next_node G Seq p)]) x2) x); simpl in locate_p; clarify.
              destruct x; destruct p1 as ((?, ?), ?).
              repeat (rewrite H15 in *); clear H15; clarify.
              inversion locate_p; clarify.
              split; clarify.
                generalize (labels_mono(def := ([x1], body, env)) p H5); simpl; intro same_f; apply same_f; auto.
                  eapply fun_not_def; eauto.
                  inversion unique_p; clarify; auto.
                split; auto; eexists; crush.
            (* to child *)
            generalize (CFG_blocks_entry _ _ H7 _ H8); clarify.
              rewrite H12 in H2; clarify.
              destruct x0.
              destruct s as ((?, ?), ?); specialize (H10 _ _ _ _ H18); destruct H10 as [? [? ?]].
              generalize (appears_once_CFG(bl := Node (p, [(x1, vals)], [l_Br_label (next_node G Seq p)]) x2)
                G (H1 (next_node G Seq p))); simpl; intro unique_p'.
              unfold instr_to_block in unique_p'; rewrite H17 in unique_p'; rewrite H7 in unique_p'; specialize (unique_p' eq_refl).
              generalize (same_subtree(tr' := x)(tr'' := Node (l3, l4, l5) l2) unique_p'); rewrite H14; simpl; intro locate_p'.
              assert (x = Node (l3, l4, l5) l2); [apply locate_p'; auto | clarify].
                destruct dom'; clarify.
                  generalize (instr_label _ _ _ H12); clarify.
                repeat eexists; eauto.
Qed.

(* I might benefit by proving confluence of step_CPS. *)
Lemma construct_body: forall bl body, fun_body bl = Some body -> 
  (forall l, for_one (fun x => fst (fst x) = l) bl) -> 
  exists tail, block_to_CPS bl = Some tail /\
  forall gt e f, exists f', clos_refl_trans _ (step_silent gt) (e, f, body) (e, f', tail) /\ 
  (* anything that reaches a call must pass through tail *)
  forall l phis il ch', In (Node (l, phis, il) ch') (children bl) -> 
    exists b, fun_body (Node (l, phis, il) ch') = Some b /\ 
    NodeMap.find l f' = Some (map (fun p => fst p) phis, b, e).
Proof.
  apply (best_tree_ind (fun bl => forall body, fun_body bl = Some body ->
    (forall l, for_one (fun x => fst (fst x) = l) bl) -> 
    exists tail, block_to_CPS bl = Some tail /\
    forall gt e f, exists f', clos_refl_trans _ (step_silent gt) (e, f, body) (e, f', tail) /\ 
    forall l phis il ch', In (Node (l, phis, il) ch') (children bl) ->
    exists b, fun_body (Node (l, phis, il) ch') = Some b /\ 
    NodeMap.find l f' = Some (map (fun p => fst p) phis, b, e)) 
  (fun ch => forall t t', fold_right (fun bl to => match to with Some t => blocks_to_CPS bl t | None => None end) 
    (Some t) ch = Some t' -> (forall l, for_one_aux (fun x => fst (fst x) = l) ch /\ (not_def l t \/ Forall (for_none (fun x => fst (fst x) = l)) ch)) ->
    forall gt e f, exists f', clos_refl_trans _ (step_silent gt) (e, f, t') (e, f', t) /\ 
    forall l phis il ch', In (Node (l, phis, il) ch') ch ->
    exists b, fun_body (Node (l, phis, il) ch') = Some b /\ 
    NodeMap.find l f' = Some (map (fun p => fst p) phis, b, e))); clarify; eauto.
    eexists; crush.
      apply H; auto.
      intro; specialize (H1 l); inversion H1; clarify.
        split; auto; apply for_none_one_list; auto.
        destruct x as ((?, ?), ?); left; eapply instrs_not_def; eauto.
    eexists; crush.
    destruct tr; clarify.
      destruct p as ((?, ?), ?); autorewrite with core in *; clarify.
      specialize (H x1); clarify.
      destruct H; intros.
        eexists; crush.
        specialize (H2 l3); clarify.
          inversion H; clarify.
          destruct H6; clarify; apply for_none_one; auto.
        clarify.
          assert (forall l3 : label, for_one_aux (fun x => fst (fst x) = l3) rest /\ (not_def l3 t \/ Forall (for_none (fun x => fst (fst x) = l3)) rest))
            as uniqueness; intros.
            specialize (H2 l3); clarify; inversion H2; clarify.
              destruct H8; clarify.
                split; [apply for_none_one_list; auto | destruct H6; clarify].
                destruct H6; clarify.
                  inversion H6; clarify.
            specialize (H0 _ _ H1 uniqueness gt e (NodeMap.add l0 (map (fun p => fst p) l1, x1, e) f));
              clarify.
            eexists; split.
              eapply rt_trans; [eapply rt_step; econstructor | eauto].
              clarify.
                destruct H7; clarify.
                inversion H7; clarify.
                setoid_rewrite H3; rewrite H4; repeat eexists; eauto.
                generalize (labels_mono(def := (map (fun p => fst p) phis, x1, e)) l3 H0); clarify.
                apply H7; auto.
                specialize (H2 l3); clarify.
                inversion H2; clarify.
                destruct H10; clarify.
                  eapply funs_not_def; eauto.
                    destruct H8; clarify; inversion H8; clarify.
                    inversion H13; clarify.
                  inversion H9; clarify.
Qed.


Lemma CPS_sound: forall gt env f args p env' f' args' p', 
  step_label gt (env, f, App args (L p)) (env', f', App args' (L p')) -> 
  forall G q dom bl body xs p0(*!!*) st al dom', CFG_to_blocks G dom = Some bl -> 
  (forall l, for_one (fun x => x = l) dom) -> p = root dom -> 
  fun_body bl = Some body -> NodeMap.find p f = Some (xs, body, env) -> 
  make_phis p0 (snd (fst (root bl))) = Some args -> xs = map (fst(A := string)(B := node_map expr)) (snd (fst (root bl))) ->
  p' = root dom' -> (dom' = dom \/ In dom' (children dom)) ->
  step G q gt (p0, p, env, st, al) [] (p, p', env', st, al) /\ 
    exists bl', CFG_to_blocks G dom' = Some bl' /\ 
    exists xs' body' cenv', fun_body bl' = Some body' /\
    NodeMap.find p' f' = Some (xs', body', cenv') /\ xs' = map (fst(A := string)(B := node_map expr)) (snd (fst (root bl'))) /\
    make_phis p (snd (fst (root bl'))) = Some args'.
Proof.
  intros; inversion H; clarify.
    rewrite H16 in H4; clarify.
    generalize (construct_body H3); intro con.
    destruct con; [intro; eapply appears_once_CFG; eauto | clarify].
    generalize (appears_once_CFG _ (H1 (root dom)) H0); intro unique_p.
    generalize (CFG_dom_subtree(dom := dom)(dom' := dom') G); intro CFG'.
    assert (subtree dom' dom) as dom_sub; [destruct dom; destruct H8; clarify; econstructor; clarify | specialize (CFG' dom_sub _ H0)].

    unfold fun_body in H3; destruct bl; autorewrite with core in *; clarify.
  intros; eapply (step_label_ind'(gt := gt) (fun env f t env' f' t' => t = App args (L p) -> t' = App args' (L p') ->
        forall G dom bl body xs cenv q p0 st al, CFG_to_blocks G dom = Some bl -> p = root dom -> 
        fun_body bl = Some body -> NodeMap.find p f = Some (xs, body, cenv) -> 
        step G q gt (p0, p, env, st, al) [] (p, p', env', st, al) /\ exists dom' bl' xs' body' cenv', 
        In dom' (children dom) /\ p' = root dom' /\ CFG_to_blocks G dom' = Some bl' /\ fun_body bl' = Some body' /\
        NodeMap.find p' f' = Some (xs', body', cenv'))); try reflexivity; eauto; intros.
    (* base case *)
    skip.
    (* inductive case *)
    clarify.
      skip.

(* Turning variable names into indices *)
Definition incr m := StringMap.map (fun n => n + 1) m.

Fixpoint de_bruijn_aux t m :=
  match t with
  | Pri p tl => Pri p (de_bruijn_list_aux tl m)
  | Var x => match StringMap.find x m with
             | Some n => Index n
             | None => Var x
             end
  | Glb x => Glb x
  | App tl t => App (de_bruijn_list_aux tl m) (de_bruijn_aux t m)
  | If t1 t2 t3 => If (de_bruijn_aux t1 m) (de_bruijn_aux t2 m) (de_bruijn_aux t3 m)
  | Let x t1 t2 => Let (Pro (de_bruijn_aux t1 m)) (de_bruijn_aux t2 (StringMap.add x 0 (incr m)))
  | _ => t
  end
with de_bruijn_list_aux tl m :=
  match tl with
  | [] => []
  | t::rest => de_bruijn_aux t m :: de_bruijn_list_aux rest m
  end.