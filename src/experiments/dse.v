Require Import Util.
Require Import minillvm_bitwise_mem.
Require Import CoqEqDec.
Require Import Morphisms.
Require Import memory_model.
Require Import String.
Require Import ZArith.
Require Import Relation_Operators.
Require Import List.
Require Import LTS.
Import ListNotations.
Import Bool.
Import Coq.Classes.EquivDec.
Require Import Coqlib.

Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Section CFG_ops.
  Definition EdgeSet_map f s := 
    EdgeSet.fold (fun e s => EdgeSet.add (f e) s) s EdgeSet.empty.

  Lemma EdgeSet_map_spec : forall f s e, EdgeSet.In e (EdgeSet_map f s) <->
    (exists e', f e' = e /\ EdgeSet.In e' s).
  Proof.
    intros f s e; unfold EdgeSet_map; split; apply EdgeSet.fold_rec_bis; clarify.
    - rewrite H in *; eauto.
    - generalize (EdgeSet.empty_spec); intro empty; contradiction (empty _ H).
    - rewrite EdgeSet.add_spec in *; setoid_rewrite EdgeSet.add_spec; 
        destruct H2; clarify; eauto.
    - rewrite <- H in *; apply H0; eauto.
    - generalize (EdgeSet.empty_spec); intro empty; contradiction (empty _ H2).
    - rewrite EdgeSet.add_spec in *; destruct H22; clarify; eauto.
  Qed.

  Variable (loc : Type).

  Definition remove_seq n (G : CFG loc) := let n' := next_node G Seq n in
    if eq_dec n n' then None else Some
    {| Nodes := NodeSet.remove n (Nodes G);
       Edges := EdgeSet_map (fun e => match e with (n1, ty, n2) => 
                  if eq_dec n2 n then (n1, ty, n') else e end) (Edges G);
       Start := Start G; Exit := Exit G; Label := Label G |}.

  Instance out_proper n ty : Proper (eq ==> eq)
     (fun e0 : EdgeSet.elt =>
      let (p, _) := e0 in let (u, t) := p in beq u n && beq t ty).
  Proof. repeat intro; clarify. Qed.
  Hint Resolve out_proper.

  Lemma remove_out_edges : forall n G ty n' G' 
    (Hrem : remove_seq n G = Some G'), EdgeSet.Equal 
    (out_edges G' ty n') 
    (EdgeSet_map (fun e => match e with (n1, ty, n2) => if eq_dec n2 n then 
      (n1, ty, next_node G Seq n) else e end) (out_edges G ty n')).
  Proof.
    unfold out_edges, remove_seq; repeat intro; simpl.
    rewrite EdgeSet.filter_spec; auto.
    clarify; repeat rewrite EdgeSet_map_spec.
    split; clarify.
    - exists x; destruct x as ((?, ?), ?); split; clarify.
      rewrite EdgeSet.filter_spec; clarify.
    - rewrite EdgeSet.filter_spec in *; clarify; split; eauto.
      destruct x as ((?, ?), ?); destruct (eq_dec n2 n); clarify.
  Qed.            

  Lemma remove_wf : forall G n G' (Hwf : wf_CFG G) (Hstart : n <> Start G)
    (Hexit : n <> Exit G) (Hrem : remove_seq n G = Some G'), wf_CFG G'.
  Proof.
    intros; inversion Hwf; constructor.
    - unfold remove_seq in *; clarify.
      rewrite NodeSet.remove_spec; clarify.
    - unfold remove_seq in *; clarify.
      rewrite NodeSet.remove_spec; clarify.
    - intros ((a, y), b); unfold remove_seq in *; clarify.
      rewrite NodeSet.remove_spec in *; rewrite EdgeSet_map_spec in H;
        clarify.
      destruct x as ((a', y'), b'); clarify.
      destruct (eq_dec b' n); clarify.
      + apply wf_next_in; auto.
        exploit Hedges; eauto.
      + exploit Hedges; eauto.
    - unfold instr_edges in *; repeat intro.
      exploit Hinstr_edges.
      { unfold remove_seq in *; clarify.
        rewrite NodeSet.remove_spec in *; clarify; eauto. }
      clear Hwf; intro Hwf.
      assert (Label G' = Label G) as Hlabel; [unfold remove_seq in *; clarify|];
        rewrite Hlabel.
      destruct (seq_instr (Label G x)); [|destruct (Label G x)]; clarify.
      + exists (if eq_dec x0 n then next_node G Seq n else x0); split; 
          repeat intro; setoid_rewrite remove_out_edges; eauto;
          setoid_rewrite EdgeSet_map_spec.
        * setoid_rewrite Hwf1; setoid_rewrite EdgeSet.singleton_spec; split; 
              clarify.
          eexists; split; eauto; clarify.
        * generalize (EdgeSet.empty_spec); intro empty; split; clarify.
          rewrite Hwf2 in H12; specialize (empty x1); clarify.
          specialize (empty a); clarify.
      + exists (if eq_dec x0 n then next_node G Seq n else x0);
          exists (if eq_dec x1 n then next_node G Seq n else x1);
          split; [| split]; repeat intro; setoid_rewrite remove_out_edges; 
          eauto; setoid_rewrite EdgeSet_map_spec; [setoid_rewrite Hwf1 |
          setoid_rewrite Hwf21 |]; try setoid_rewrite EdgeSet.singleton_spec.
        * split; clarify; eexists; split; eauto; clarify.
        * split; clarify; eexists; split; eauto; clarify.
        * generalize (EdgeSet.empty_spec); intro empty; split; clarify.
          rewrite Hwf22 in H12; specialize (empty x2); clarify.
          specialize (empty a); clarify.
      + rewrite remove_out_edges; eauto; intro a; rewrite EdgeSet_map_spec; 
          generalize (EdgeSet.empty_spec); intro empty; split; 
          [intros [e0 [_ Hin]]; rewrite Hwf in Hin | intro Hin];
          specialize (empty _ Hin); clarify.
  Qed.

  Lemma remove_next_node : forall n G ty n' (Hwf : wf_CFG G)
    (Hstart : n <> Start G) (Hexit : n <> Exit G)
    (Hnode : NodeSet.In n' (Nodes G)) (Hreal : n' <> n)
    G' (Hrem : remove_seq n G = Some G'),
    next_node G' ty n' = 
      if eq_dec (next_node G ty n') n then next_node G Seq n 
      else next_node G ty n'.
  Proof.
    intros; generalize (next_node_cases G' ty n'); 
      intros [Hin | [Hfail Hempty]].
    - rewrite remove_out_edges in Hin; eauto 2; rewrite EdgeSet_map_spec in Hin.
      destruct Hin as [((a, y), b) [? Hin]]; clarify.
      destruct (eq_dec b n); clarify.
      + exploit wf_next_defined; eauto 2; clarify.
      + destruct (eq_dec (next_node G ty n') n); auto;
          [|exploit (wf_next_defined Hwf Hnode); eauto 2; clarify].
        generalize (next_node_cases G ty n'); intros [Hin' | [Hfail ?]]; 
          rewrite e in *; [|rewrite Hfail in *; clarify].
        assert (EdgeSet.In (n', ty, next_node G Seq n) (out_edges G' ty n')).
        * rewrite remove_out_edges; eauto; rewrite EdgeSet_map_spec.
          exists (n', ty, n); clarify.
        * exploit wf_next_defined.
          { eapply remove_wf; eauto. }
          { unfold remove_seq in *; clarify.
            rewrite NodeSet.remove_spec; split; eauto. }
          { eauto. }
          clarify.
    - generalize (next_node_cases G ty n'); intros [Hin | [Hfail' Hempty']].
      + assert (EdgeSet.In (n', ty, if eq_dec (next_node G ty n') n then
          next_node G Seq n else next_node G ty n') (out_edges G' ty n')) 
          as Hin'; [| specialize (Hempty _ Hin'); clarify].
        rewrite remove_out_edges; eauto; rewrite EdgeSet_map_spec.
        exists (n', ty, next_node G ty n'); clarify.
      + rewrite Hfail, Hfail'.
        destruct (eq_dec n' n) eqn: X; setoid_rewrite X; clarify.
  Qed.        
        
  Variables (mval : Type) (loc_eq : EqDec_eq loc) (mval_eq : EqDec_eq mval).
  Context {ML : Memory_Layout mval loc_eq} 
    {SP : StructuredPtr type (const loc) ML}.
  Definition mem := mem loc mval.

  (* Should the analysis for non-intersection go into StructuredPtr? *)
  Definition not_read_again P gt C l := forall c' (m' : mem)
    (Hlater : exists tr, rtc (mem_step P gt) C tr (c', m'))
    (Hnormal : c' <> Error loc) c'' k ops (Hstep : step P gt c' k c'')
    (Hlower : can_lower_ops (get_ops k) ops) l' v (Hread : In (MRead l' v) ops),
    l' <> l.

  Definition is_dead_store P gt f n := match find_graph f P with None => False
  | Some G => (exists ty1 e1 ty2 e2, Label G n = Store ty1 e1 ty2 e2) /\ 
      forall c m (Hreach : reachable P gt (c, m))
      p0 env st al (Hconfig : c = Normal (f, p0, n, env, st, al))
      k c' ops (Hstep : mem_step P gt (c, m) k (c', m ++ ops)),
      Forall (fun a => exists l v, a = MWrite l v /\ 
                         not_read_again P gt (c', m ++ ops) l) ops end.

  Inductive remove_ops (P : LLVM_op loc mval -> Prop) : mem -> mem -> Prop :=
  | remove_nil : remove_ops P [] []
  | remove_cons : forall a m m' (Hrem : remove_ops P m m'), 
      remove_ops P (a :: m) (a :: m')
  | remove_P : forall a m m' (Hrem : remove_ops P m m') (HP : P a),
      remove_ops P (a :: m) m'.
  Hint Constructors remove_ops.

  Lemma remove_ops_snoc : forall P m m' a, remove_ops P m m' ->
    remove_ops P (m ++ [a]) (m' ++ [a]).
  Proof. intros; induction H; clarify. Qed.

  Lemma snoc_inv : forall {A} (l : list A), l = nil \/ 
    exists l' x, l = l' ++ [x].
  Proof.
    induction l; clarify.
    right; destruct l; clarify.
    - exists []; simpl; eauto.
    - destruct x; clarify.
      + exists [a]; simpl; eauto.
      + exists (a :: a1 :: x); simpl; eauto.
  Qed.

  Lemma remove_ops_snoc_inv : forall P m m' a
    (Hremove : remove_ops P (m ++ [a]) m'),
    (exists m'', m' = m'' ++ [a] /\ remove_ops P m m'') \/
    (P a /\ remove_ops P m m').
  Proof.
    intros; eapply (remove_ops_ind(P := P) (fun m1 m' => forall m a, 
      m1 = m ++ [a] -> (exists m'', m' = m'' ++ [a] /\ remove_ops P m m'') \/
    (P a /\ remove_ops P m m'))); clarify; auto.
    - destruct m0; clarify.
    - destruct m1; clarify.
      + inversion Hrem; clarify.
        left; exists []; eauto.
      + left; eexists; split; eauto; simpl; auto.
    - destruct m1; clarify; eauto.
  Qed.

  Lemma remove_ops_app : forall P ops m m', remove_ops P m m' ->
    remove_ops P (m ++ ops) (m' ++ ops).
  Proof. 
    induction ops; clarsimp.
    specialize (IHops (m ++ [a]) (m' ++ [a])); clarsimp; apply IHops.
    apply remove_ops_snoc; auto.
  Qed.

  Lemma remove_ops_rev_ind : forall P (Q : mem -> mem -> Prop) (Hnil : Q [] [])
    (Hcons : forall a m m', remove_ops P m m' -> Q m m' -> 
                            Q (m ++ [a]) (m' ++ [a]))
    (HP : forall a m m', remove_ops P m m' -> Q m m' -> P a -> Q (m ++ [a]) m')
    m m' (Hremove : remove_ops P m m'), Q m m'.
  Proof.
    induction m using rev_ind; clarify.
    - inversion Hremove; clarify.
    - exploit remove_ops_snoc_inv; eauto; clarify.
  Qed.

  Definition is_phi (i : instr loc) := 
    match i with Phi _ _ _ => true | _ => false end.

  Definition skip_node (c c' : config loc) (P : prog loc) f n n' : Prop := 
    match (c, c') with 
      | (Normal (f1, p0, p, env, st, al), 
         Normal (f1', p0', p', env', st', al')) => 
        f1' = f1 /\ (p0' = p0 \/ 
          forall G, find_graph f1 P = Some G -> is_phi (Label G p) = false) /\
        p' = (if eq_dec f1 f then if eq_dec p n then n' else p else p) /\
        env' = env /\ st' = map (fun fr => match fr with (f1, p, x, env, al) => 
          (f1, if eq_dec f1 f then if eq_dec p n then n' 
                              else p else p, x, env, al) end) st /\ al' = al
      | (Error, Error) => True
      | _ => False
    end.

  Instance ptr_eq : @EqDec (ptr loc) eq eq_equivalence.
  Proof. apply ptr_path_eq; [apply type_eq | apply loc_eq]. Qed.

  Lemma remove_call : forall P1 l f params (G G' : CFG loc) P2 c' c2'
    (Hwf : wf_prog (P1 ++ (l, f, params, G) :: P2))
    (Hwf' : wf_prog (P1 ++ (l, f, params, G') :: P2)) 
    n (Hrem : remove_seq n G = Some G')
    G1 G1' f1 (Hgraph : find_graph f1 (P1 ++ (l, f, params, G) :: P2) = Some G1)
    (Hgraph' : find_graph f1 (P1 ++ (l, f, params, G') :: P2) = Some G1')
    (Hexit : Exit G1' = Exit G1) 
    x ty e args p (Hcall' : Label G1' p = Call x ty e args) 
    (Hcall : Label G1 p = Call x ty e args)
    gt p0 env st al f' (Gt : CFG loc) env' x st' (Hstep : step
      (P1 ++ (l, f, params, G') :: P2) gt c' [] c2')
    (Hc' : c' = Normal (f1, p0, p, env, st, al))
    (Hin : NodeSet.In p (Nodes G1'))
    (Hc2' : c2' = Normal (f', p, Start Gt, env',
      (f1, next_node G1' Seq p, x, env, al) :: st', []))
    (Hstart : n <> Start G) (Hexit : n <> Exit G) 
    c (Hnode : fun_of c <> f \/ node_of c <> n)
    (Hskip : skip_node (Normal c) c' (P1 ++ (l, f, params, G) :: P2) f n
      (next_node G Seq n)),
    exists c2, skip_node c2 c2' (P1 ++ (l, f, params, G) :: P2) f n 
      (next_node G Seq n) /\
      step (P1 ++ (l, f, params, G) :: P2) gt (Normal c) [] c2.
  Proof.
    intros; destruct c as (((((?, ?), ?), ?), ?), ?); unfold skip_node in Hskip;
      clarify.
    assert ((if eq_dec i f then if eq_dec n1 n then next_node G Seq n else n1 
      else n1) = n1) as node by (destruct Hnode; clarify); rewrite node in *; 
      clear node.
    inversion Hstep; clarify; rewrite Hgraph0 in Hgraph'; inversion Hgraph';
      subst; rewrite Hinstr in Hcall'; try discriminate.
    inversion Hcall'; subst.
    unfold start_call in Hcall0.
    destruct v; clarify.
    destruct (eq_dec p l) eqn: eq.
    - subst; rewrite wf_find_fun in *; clarify.
      eexists; split; [|eapply call; eauto 2].
      + instantiate (2 := G).
        unfold skip_node; repeat split; auto; clarify; 
          [unfold remove_seq in Hrem; clarify|].
        destruct (eq_dec i f'); clarify.
        * rewrite wf_find_graph in *; clarify.
          erewrite remove_next_node; eauto 2.
          { exploit (Hwf (length P1)); [erewrite nth_error_replace; eauto 2;
              rewrite <- beq_nat_refl; clarify | clarify]. }
          { unfold remove_seq in Hrem; clarify.
            rewrite NodeSet.remove_spec in *; clarify. }
        * rewrite find_graph_drop in *; auto; rewrite Hgraph0 in Hgraph; 
            clarify.
      + intro; clarify.
      + clarify; rewrite wf_find_fun; auto; clarsimp.
    - destruct x0 as ((?, ?), ?); clarify.
      generalize (find_fun_graph _ Hwf' Hcall01); intro Hgraph'.
      destruct (eq_dec f' f).
      { unfold find_fun in *; clarify.
        destruct x0 as (((?, ?), ?), ?); clarify.
        exploit @find_nth_error; eauto 2; intros [j [_ [Hnth ?]]].
        specialize (Hwf' (length P1)); erewrite nth_error_replace in Hwf';
          rewrite <- beq_nat_refl in Hwf'; clarify.
        specialize (Hwf'2 _ _ _ _ _ Hnth); clarify.
        erewrite nth_error_replace in Hnth; rewrite <- beq_nat_refl in Hnth;
          unfold beq in *; clarify. }
      eexists; split; [|eapply call; eauto 2]; clarify.
      + unfold skip_node; repeat split; auto; clarify.
        destruct (eq_dec i f); clarify.
        * rewrite wf_find_graph in *; clarify.
          erewrite remove_next_node; eauto 2.
          { exploit (Hwf (length P1)); [erewrite nth_error_replace; eauto 2;
              rewrite <- beq_nat_refl; clarify | clarify]. }
          { unfold remove_seq in Hrem; clarify.
            rewrite NodeSet.remove_spec in *; clarify. }
        * rewrite find_graph_drop in *; auto; rewrite Hgraph0 in Hgraph; 
            clarify.
      + intro; clarify.
      + rewrite find_fun_drop in *; auto; clarsimp.
    Grab Existential Variables. auto. auto. auto. auto.
  Qed.

  Ltac step_case tac := first [eapply assign; eauto 2; tac 
    | eapply icmp; eauto 2; tac | eapply br_false; eauto 2; tac 
    | eapply br_true; eauto 2; tac | eapply br_label; eauto 2; tac 
    | eapply alloca; eauto 2; tac | eapply gep; eauto 2; tac
    | eapply load; eauto 2; tac | eapply store; eauto 2; tac
    | eapply store_fail; eauto 2; tac | eapply cmpxchg_eq; eauto 2; tac 
    | eapply cmpxchg_no; eauto 2; tac | eapply phi; eauto 2; tac 
    | eapply call; eauto 2; tac | eapply ret_pop; eauto 2; tac 
    | eapply ret_main; eauto 2; tac | eapply out; eauto 2; tac].

  Lemma skip_step_other : forall P1 l f params G G' P2 gt c' ops c2'
    (Hwf : wf_prog (P1 ++ (l, f, params, G) :: P2))
    (Hwf' : wf_prog (P1 ++ (l, f, params, G') :: P2))
    (Hstarts : Start G' = Start G) (Hfun : fun_of c' <> f)
    (Hstep : step (P1 ++ (l, f, params, G') :: P2) gt (Normal c') ops c2')
    n n' (Hstart : n <> Start G)
    c (Hskip : skip_node c (Normal c') (P1 ++ (l, f, params, G) :: P2) f n n'),
    exists c2, skip_node c2 c2' (P1 ++ (l, f, params, G) :: P2) f n n' /\
      step (P1 ++ (l, f, params, G) :: P2) gt c ops c2.
  Proof.
    intros; destruct c as [(((((f', p0'), p'), env'), st'), al')|];
      destruct c' as (((((?, ?), ?), ?), ?), ?); unfold skip_node in Hskip;
      clarify.
    destruct (eq_dec f' f); clarify.
    inversion Hstep; clarify; destruct (eq_dec f' f); 
      try (contradiction Hfun; auto; fail);
      let tac := rewrite find_graph_drop in *; auto; fail in try (
      eexists; split; [|step_case tac]; clarify; unfold skip_node; clarify).
(*    - Ltac error_tac1 := eexists; split; [|eapply store; eauto 2; clarsimp];
        unfold skip_node; clarify; rewrite find_graph_drop in *; auto.
      destruct (eval_expr env' gt e1) eqn: He1; clarify; [|error_tac1].
      destruct (eval_expr env' gt e2) eqn: He2; clarify; [|error_tac1].
      destruct c0; clarify; [error_tac1 | | error_tac1].
      eexists; split; [|eapply store; eauto 2; rewrite find_graph_drop in *;
        auto]; clarify; unfold skip_node; clarify.*)
    - destruct Hskip21 as [? | Hnot_phi].
      * subst; let tac := rewrite find_graph_drop in *; auto; fail in try (
          eexists; split; [|step_case tac]; clarify; unfold skip_node; clarify).
      * specialize (Hnot_phi G0); rewrite find_graph_drop in *; auto; clarsimp.
    - destruct (eq_dec f'0 f); clarify.
      + generalize (start_call_graph _ _ Hwf' Hcall); intro Hgraph'.
        rewrite wf_find_graph in Hgraph'; clarify.
        rewrite Hstarts; eexists; split; [|eapply call; eauto].
        * unfold skip_node; repeat split; auto; clarify.
        * rewrite find_graph_drop in *; auto.
        * unfold start_call in *.
          destruct v; clarify.
          destruct x0 as ((?, ?), ?); clarify.
          unfold find_fun in Hcall1.
          destruct (find (fun x0 => beq p (fst (fst (fst x0))))
            (P1 ++ (l, f, params, G'0) :: P2)) as [(((?, ?), ?), ?) |] 
            eqn: Hfind; [|clarify].
          exploit @find_nth_error; eauto.
          intros [j [_ [Hnth ?]]]; unfold wf_prog in Hwf';
            specialize (Hwf' (length P1)); erewrite nth_error_replace in Hwf';
            clarify.
          rewrite <- beq_nat_refl in Hwf'; specialize (Hwf' _ _ _ _ eq_refl);
            destruct Hwf' as [_ Hwf']; specialize (Hwf' _ _ _ _ _ Hnth);
            clarify.
          erewrite nth_error_replace in Hnth; rewrite <- beq_nat_refl in Hnth;
            unfold beq in *; clarify; rewrite wf_find_fun; auto.
          rewrite Hcall21; auto.
      + eexists; split; [|eapply call; eauto].
        * unfold skip_node; repeat split; auto; clarify.
        * rewrite find_graph_drop in *; auto.
        * unfold start_call in *.
          destruct v; clarify.
          rewrite wf_find_fun_iff in Hcall1; clarify.
          destruct (eq_dec p l); clarify.
          rewrite find_fun_drop; auto; rewrite Hcall1; auto.
    - destruct st' as [ | [(((?, ?), ?), ?) st']]; clarify.
      eexists; split; [|eapply ret_pop; eauto; rewrite find_graph_drop in *; 
        auto]; clarify; unfold skip_node; clarify.
    - destruct st' as [ | [(((?, ?), ?), ?) st']]; clarify.
      eexists; split; [|eapply ret_main; eauto; rewrite find_graph_drop in *; 
        auto]; clarify; unfold skip_node; clarify.
    Grab Existential Variables. auto. auto.
  Qed.


  Lemma remove_step : forall P1 l f params n G G' P2 gt c' ops c2'
    (Hwf : wf_prog (P1 ++ (l, f, params, G) :: P2)) (Hstart : n <> Start G)
    (Hexit : n <> Exit G) (Hrem : remove_seq n G = Some G')
    (Hstep : step (P1 ++ (l, f, params, G') :: P2) gt c' ops c2')
    c (Hskip : skip_node (Normal c) c' (P1 ++ (l, f, params, G) :: P2) f n 
        (next_node G Seq n))
    (Hsafe : safe (P1 ++ (l, f, params, G) :: P2) (Normal c))
    (Hnode : fun_of c <> f \/ node_of c <> n),
    exists c2, skip_node c2 c2' (P1 ++ (l, f, params, G) :: P2) f n 
      (next_node G Seq n) /\
      step (P1 ++ (l, f, params, G) :: P2) gt (Normal c) ops c2.
  Proof.
    intros; generalize (find_wf_graph(G := G) f Hwf); intro Hwf_G.
    rewrite wf_find_graph in Hwf_G; auto; use Hwf_G.
    intros; generalize (remove_wf Hwf_G Hstart Hexit Hrem); intro Hwf_G'.
    generalize (wf_replace _ _ _ _ _ _ Hwf params Hwf_G'); intro Hwf'.
    assert (Start G' = Start G) as Hstarts; 
      [unfold remove_seq in Hrem; clarify|].
    destruct c as (((((?, ?), ?), ?), ?), ?); destruct c' as [c'|];
      [|unfold skip_node in Hskip]; clarify.
    destruct (eq_dec (fun_of c') f); [|eapply skip_step_other; eauto 2].
    unfold in_graph in Hsafe1; clarify.
    destruct c' as (((((f1, p0), p), env), st), al); unfold skip_node in Hskip;
      clarify.
    destruct (eq_dec n1 n); clarify.
    rewrite wf_find_graph in Hsafe1; auto.
    inversion Hstep; clarify; rewrite wf_find_graph in Hgraph; clarify;
      destruct (eq_dec n1 n); try (contradiction Hnode; auto; fail);
      let tac := rewrite wf_find_graph; auto; fail in try (
      unfold remove_seq in Hrem; clarify; eexists; split; [|step_case tac];
      unfold skip_node; clarify; erewrite (remove_next_node _ _ Hstart); 
      unfold remove_seq; eauto 2; clarify; fail).
(*    - Ltac error_tac2 := eexists; split; [|eapply store; eauto 2; clarsimp];
        unfold skip_node; clarify; rewrite wf_find_graph; auto.
      unfold remove_seq in Hrem; clarify.
      destruct (eval_expr e gt e1) eqn: He1; clarify; [|error_tac2].
      destruct (eval_expr e gt e2) eqn: He2; clarify; [|error_tac2].
      destruct c0; clarify; [error_tac2 | | error_tac2].
      eexists; split; [|eapply store; eauto 2; clarsimp; rewrite wf_find_graph; 
        auto].
      unfold skip_node; clarify; erewrite (remove_next_node _ _ Hstart); 
        unfold remove_seq; eauto 2; clarify.*)
    - destruct Hskip21 as [? | Hnot_phi].
      * subst; let tac := rewrite wf_find_graph; auto; fail in try (
          unfold remove_seq in Hrem; clarify; eexists; split; [|step_case tac];
          unfold skip_node; clarify; erewrite (remove_next_node _ _ Hstart); 
          unfold remove_seq; eauto 2; clarify).
      * rewrite wf_find_graph in Hnot_phi; clarify.
        unfold remove_seq in Hrem; clarsimp.
    - eapply (remove_call _ _ _ _ _  Hwf Hwf' Hrem
        (wf_find_graph _ _ _ _ _ _ Hwf) (wf_find_graph _ _ _ _ _ _ Hwf'));
        eauto 2; unfold remove_seq in Hrem; clarify.
      * rewrite NodeSet.remove_spec; auto.
      * unfold skip_node; repeat split; auto; clarify.
    - destruct l0 as [|((((?, ?), ?), ?), ?)]; unfold remove_seq in Hrem;
        clarify.
      eexists; split; [|eapply ret_pop; eauto; rewrite wf_find_graph; auto];
        clarify.
      unfold skip_node; repeat split; auto; clarify.
    - destruct l0 as [|((((?, ?), ?), ?), ?)]; unfold remove_seq in Hrem;
        clarify.
      eexists; split; [|eapply ret_main; eauto; rewrite wf_find_graph; auto];
        clarify.
      unfold skip_node; repeat split; auto; clarify.
    Grab Existential Variables. auto. auto. auto. auto. auto. auto. auto. auto.
      auto. auto. auto. auto. auto.
  Qed.

  Lemma remove_mstep : forall P1 l f params n G G' P2 gt c' m k c2' m2
    (Hwf : wf_prog (P1 ++ (l, f, params, G) :: P2)) (Hstart : n <> Start G)
    (Hrem : remove_seq n G = Some G') (Hexit : n <> Exit G)
    (Hmstep : mem_step (P1 ++ (l, f, params, G') :: P2) gt 
      (c', m) k (c2', m2)) 
    c (Hskip : skip_node (Normal c) c' (P1 ++ (l, f, params, G) :: P2) f n 
        (next_node G Seq n))
    (Hsafe : safe (P1 ++ (l, f, params, G) :: P2) (Normal c))
    (Hnode : fun_of c <> f \/ node_of c <> n),
    exists c2, skip_node c2 c2' (P1 ++ (l, f, params, G) :: P2) f n 
      (next_node G Seq n) /\ 
      mem_step (P1 ++ (l, f, params, G) :: P2) gt (Normal c, m) k (c2, m2).
  Proof.
    intros; generalize (find_wf_graph(G := G) f Hwf); intro Hwf_G.
    rewrite wf_find_graph in Hwf_G; auto; use Hwf_G.
    intros; generalize (remove_wf Hwf_G Hstart Hexit Hrem); intro Hwf_G'.
    inversion Hmstep.
    exploit remove_step; eauto; intros [c2 [Hskip2 Hstep2]].
    exists c2; split; auto; apply step_once; auto.
  Qed.

  Definition dse_sim P f n gt (C' C : config loc * mem) := 
    match (C, C') with ((c, m), (c', m')) => c = Error loc \/ (
      remove_ops (fun op => exists l v, op = MWrite l v /\ 
                            not_read_again P gt C l) m m' /\
      match find_graph f P with
      | Some G => skip_node c c' P f n (next_node G Seq n)
      | None => False
      end)
    end.

  Lemma step_not_read_again : forall P gt C l (Hnra : not_read_again P gt C l)
    k C2 (Hstep : mem_step P gt C k C2),
    not_read_again P gt C2 l.
  Proof.
    unfold not_read_again; repeat intro.
    exploit Hnra; eauto.
    destruct Hlater as [tr Hlater]; exists (k ++ tr); eapply rtc_step; eauto.
  Qed.

  Lemma step_remove_dead : forall P gt c m m'
    (Hremove : remove_ops (fun op => exists l v, op = MWrite l v /\ 
       not_read_again P gt (c, m) l) m m')
    k c2 m2 (Hmstep : mem_step P gt (c, m) k (c2, m2)),
    remove_ops (fun op => exists l v, op = MWrite l v /\ 
      not_read_again P gt (c2, m2) l) m m'.
  Proof.
    intros; induction Hremove; clarify.
    constructor; auto.
    repeat eexists; eauto; eapply step_not_read_again; eauto.
  Qed.

(*  Lemma remove_unread_cast : forall m m' P gt C
    (Hremove : remove_ops (fun op => exists l v, op = MWrite l v /\ 
       not_read_again P gt C l) m m'),
    Forall (fun x => is_mcast x = false) m <-> 
    Forall (fun x => is_mcast x = false) m'.
  Proof.
    intros; induction Hremove; clarify.
    - split; auto.
    - split; intro H; inversion H; constructor; auto; [rewrite <- IHHremove |
        rewrite IHHremove]; auto.
    - split; intro H; [inversion H | constructor; auto]; [rewrite <- IHHremove |
        rewrite IHHremove]; auto.
  Qed.    *)

  Lemma simple_similar : forall sm sm' (op : LLVM_op loc mval)
    (Hsim : sm' (loc_of op) = sm (loc_of op) \/ 
      (exists v, sm (loc_of op) = Stored v /\ sm' (loc_of op) <> Freed))
    (Hnot_read : match op with MRead l v => sm l = sm' l | _ => True end),
    match simple_access sm op with Some _ => true 
    | None => false end =
    match simple_access sm' op with Some _ => true 
    | None => false end.
  Proof. 
    intros; destruct op; clarify; destruct (sm l); clarsimp;
      destruct (sm' l); clarsimp.
    inversion Hnot_read; clarify.
  Qed.

  Lemma simple_same : forall sm sm' l (Hsame : sm l = sm' l)
    (op : LLVM_op loc mval) (Hloc : loc_of op = l)
    sm2 (Happ : simple_access sm op = Some sm2)
    sm2' (Happ' : simple_access sm' op = Some sm2'),
    sm2 l = sm2' l.
  Proof. 
    intros; destruct op; clarify; destruct (sm' l) eqn: state; clarsimp;
      unfold simple_update; clarify.
  Qed.

  Lemma simple_remove_unread : forall m m' P gt C
    (Hremove : remove_ops (fun op => exists l v, op = MWrite l v /\ 
       not_read_again P gt C l) m m')
    sm (Hsm : make_simple m = Some sm) 
    sm' (Hsm' : make_simple m' = Some sm') l
    (Hwrite_alloc : write_alloc m),
    sm' l = sm l \/ (exists v, sm l = Stored v /\ sm' l <> Freed).
  Proof.
    intros ? ? ? ? ? ?; induction Hremove using remove_ops_rev_ind; clarsimp.
    - rewrite make_simple_snoc in Hsm, Hsm'; destruct Hsm as [sm1 [Hsm1 Ha]];
        destruct Hsm' as [sm1' [Hsm1' Ha']].
      destruct (eq_dec l (loc_of a)).
      + destruct a; clarify; destruct (sm1 l0) eqn: cell; 
          destruct (sm1' l0) eqn: cell'; clarify;
          unfold simple_update; clarsimp.
      + generalize (write_alloc_prefix _ Hwrite_alloc).
        rewrite (simple_diff_loc _ _ Ha); eauto 2.
        rewrite (simple_diff_loc _ _ Ha'); eauto 2.
    - generalize (write_alloc_prefix _ Hwrite_alloc).
      rewrite make_simple_snoc in Hsm; clarify.
      unfold simple_update; destruct (eq_dec l x); clarify.
      right; eexists; split; eauto; specialize (IHHremove x1); clarify.
      specialize (IHHremove x); destruct (x1 x) eqn: cell; clarsimp.
      specialize (Hwrite_alloc m); clarify.
      specialize (Hwrite_alloc _ Hsm1); clarify.
  Qed.

  Lemma read_init_snoc : forall (m : mem) a (Hread_init : read_init m),
    match a with 
      MRead l v => forall sm, make_simple m = Some sm -> sm l <> Uninit 
      | _ => True 
    end -> read_init (m ++ [a]).
  Proof.
    repeat intro.
    generalize (snoc_inv m2); intros [? | ?]; clarify.
    - exploit (app_inj_tail m m1); eauto; clarsimp.
    - exploit (app_inj_tail m (m1 ++ MRead l v :: x));
        [rewrite <- app_assoc; eauto | clarify].
      specialize (Hread_init m1); clarsimp.
  Qed.

  Lemma read_init_snoc_iff : forall (m : mem) a (Hread_init : read_init m),
    read_init (m ++ [a]) <-> match a with 
      MRead l v => forall sm, make_simple m = Some sm -> sm l <> Uninit 
      | _ => True 
    end.
  Proof.
    intros; split; [intro Hread | apply read_init_snoc; auto].
    specialize (Hread m); destruct a; clarify.
  Qed.

  Lemma write_alloc_snoc : forall (m : mem) a (Hwrite_alloc : write_alloc m),
    match a with 
      MWrite l v => forall sm, make_simple m = Some sm -> sm l <> Freed
      | _ => True 
    end -> write_alloc (m ++ [a]).
  Proof.
    repeat intro.
    generalize (snoc_inv m2); intros [? | ?]; clarify.
    - exploit (app_inj_tail m m1); eauto; clarsimp.
    - exploit (app_inj_tail m (m1 ++ MWrite l v :: x));
        [rewrite <- app_assoc; eauto | clarify].
      specialize (Hwrite_alloc m1); clarsimp.
  Qed.

  Lemma write_alloc_snoc_iff : forall (m : mem) a 
    (Hwrite_alloc : write_alloc m),
    write_alloc (m ++ [a]) <-> match a with 
      MWrite l v => forall sm, make_simple m = Some sm -> sm l <> Freed
      | _ => True 
    end.
  Proof.
    intros; split; [intro Hwrite | apply write_alloc_snoc; auto].
    specialize (Hwrite m); destruct a; clarify.
  Qed.

  Lemma safe_remove_unread : forall m m' P gt C
    (Hremove : remove_ops (fun op => exists l v, op = MWrite l v /\ 
       not_read_again P gt C l) m m') 
    (Hcon : consistent m) (Hcon' : consistent m')
    (Hread_init : read_init m') (Hwrite_alloc : write_alloc m),
    read_init m /\ write_alloc m'.
  Proof.
    intros ? ? ? ? ? ?; induction Hremove using remove_ops_rev_ind; clarsimp.
    - generalize (read_init_prefix _ Hread_init);
        generalize (write_alloc_prefix _ Hwrite_alloc);
        generalize (consistent_prefix _ _ Hcon');
        generalize (consistent_prefix _ _ Hcon); 
        intros Hcon1 Hcon1' Hwrite Hread; clarify.
      rewrite read_init_snoc_iff, write_alloc_snoc_iff; auto.
      destruct a; clarify.
      + destruct (make_simple m) eqn: Hm; clarify.
(*        generalize (simple_no_cast _ Hm); intro.
        rewrite remove_unread_cast in *; eauto 2.*)
        exploit (consistent_simple Hcon1'); eauto 2; clarsimp.
        exploit (simple_remove_unread); eauto 2; instantiate (1 := l).
        rewrite read_init_snoc_iff in Hread_init; auto.
        intros [? | ?]; clarsimp.
      + destruct (make_simple m') eqn: Hm; clarify.
(*        generalize (simple_no_cast _ Hm); intro.
        rewrite <- remove_unread_cast in *; eauto 2.*)
        exploit (consistent_simple Hcon1); eauto 2; clarsimp.
        exploit (simple_remove_unread); eauto 2; instantiate (1 := l).
        rewrite write_alloc_snoc_iff in Hwrite_alloc; auto.
        intros [? | ?]; clarsimp.
    - generalize (consistent_prefix _ _ Hcon); 
        generalize (write_alloc_prefix _ Hwrite_alloc); clarify.
      rewrite read_init_snoc_iff; auto.
  Qed.

  Lemma remove_unread_op : forall m m' P gt C
    (Hremove : remove_ops (fun op => exists l v, op = MWrite l v /\ 
       not_read_again P gt C l) m m')
    sm (Hsm : make_simple m = Some sm) 
    sm' (Hsm' : make_simple m' = Some sm')
    op (Hnot_read : match op with MRead l v => sm l = sm' l | _ => True end)
    (Hcon : consistent m) (Hcon' : consistent m')
(*    (Hno_cast_m : Forall (fun x => is_mcast x = false) m)
    (Hno_cast : is_mcast op = false)*)
    (Hread_init : read_init (m' ++ [op]))
    (Hwrite_alloc : write_alloc (m ++ [op])),
    can_do_op m op <-> can_do_op m' op.
  Proof.
    intros; generalize (write_alloc_prefix _ Hwrite_alloc); intro.
    exploit simple_remove_unread; eauto 2.
    instantiate (1 := loc_of op); intro Hcases.
    generalize (read_init_prefix _ Hread_init); intro.
    exploit safe_remove_unread; eauto; intros [Hread' Hwrite'].
    exploit simple_op; eauto 2.
    { rewrite write_alloc_snoc_iff in *; auto; destruct op; clarsimp. }
    intros [? [? Hop']]; clarsimp.
    exploit (simple_op _ Hcon); eauto 2.
    { rewrite read_init_snoc_iff in *; auto; destruct op; clarsimp. }
    intros [? [? Hop]]; clarsimp.
    rewrite Hop, Hop'.
    exploit simple_similar; eauto; intro.
    destruct (simple_access x op); split; clarify.
  Qed.    

  Lemma remove_unread_ops : forall ops m m' P gt C
    (Hremove : remove_ops (fun op => exists l v, op = MWrite l v /\ 
       not_read_again P gt C l) m m')
    sm (Hsm : make_simple m = Some sm) 
    sm' (Hsm' : make_simple m' = Some sm')
    (Hnot_read : Forall (fun op => match op with 
      MRead l v => sm l = sm' l | _ => True end) ops)
    (Hcon : consistent m) (Hcon' : consistent m')
(*    (Hno_cast_m : Forall (fun x => is_mcast x = false) m)
    (Hno_cast_ops : Forall (fun x => is_mcast x = false) ops)*)
    (Hread_init : read_init (m' ++ ops)) 
    (Hwrite_alloc : write_alloc (m ++ ops)),
    can_do_ops m ops <-> can_do_ops m' ops.
  Proof.
    unfold can_do_ops; induction ops; clarsimp.
    { split; auto. }
    rewrite Forall_forall in Hnot_read; clarify.
    generalize (Hnot_read a); clarify.
    generalize (read_init_prefix(m := m' ++ [a]) ops);
      generalize (write_alloc_prefix(m := m ++ [a]) ops);
      repeat rewrite <- app_assoc; simpl; clarify.
    assert (consistent (m ++ [a]) <-> consistent (m' ++ [a])) as Hcan.
    { eapply remove_unread_op; eauto 2. }
    specialize (IHops (m ++ [a]) (m' ++ [a])); 
      setoid_rewrite <- app_assoc in IHops; simpl in IHops.
    split; intro Hcons.
    - exploit (consistent_prefix (m ++ [a]) ops).
      { rewrite <- app_assoc; simpl; auto. }
      intro Hcon1.
      exploit (safe_remove_unread(m := m ++ [a])(m' := m' ++ [a])); eauto.
      { apply remove_ops_snoc; eauto. }
      { rewrite <- Hcan; auto. }
      clarify.
      exploit (consistent_simple Hcon1); eauto; intros [sm1 Hsm1].
      rewrite Hcan in Hcon1; exploit (consistent_simple Hcon1); eauto; 
        intros [sm1' Hsm1'].
      rewrite IHops in Hcons; eauto.
      + apply remove_ops_snoc; eauto.
      + rewrite make_simple_snoc in Hsm1, Hsm1'; clarsimp.
        rewrite Forall_forall; intros b ?; specialize (Hnot_read b);
          destruct b; clarify.
        destruct (eq_dec (loc_of a) l).
        * eapply (simple_same _ _ Hnot_read); eauto.
        * rewrite (simple_diff_loc _ _ Hsm12), (simple_diff_loc _ _ Hsm1'2);
            auto.
      + rewrite Hcan; auto.
    - exploit (consistent_prefix (m' ++ [a]) ops).
      { rewrite <- app_assoc; simpl; auto. }
      intro Hcon1.
      exploit (safe_remove_unread(m := m ++ [a])(m' := m' ++ [a])); eauto.
      { apply remove_ops_snoc; eauto. }
      { rewrite Hcan; auto. }
      clarify.
      exploit (consistent_simple Hcon1); eauto; intros [sm1 Hsm1].
      rewrite <- Hcan in Hcon1; exploit (consistent_simple Hcon1); eauto; 
        intros [sm1' Hsm1'].
      rewrite IHops; eauto.
      + apply remove_ops_snoc; eauto.
      + rewrite make_simple_snoc in Hsm1, Hsm1'; clarsimp.
        rewrite Forall_forall; intros b ?; specialize (Hnot_read b);
          destruct b; clarify.
        destruct (eq_dec (loc_of a) l).
        * eapply (simple_same _ _ Hnot_read); eauto.
        * rewrite (simple_diff_loc _ _ Hsm12), (simple_diff_loc _ _ Hsm1'2);
            auto.
      + rewrite <- Hcan; auto.
  Qed.

  Lemma step_read_state : forall m m' P gt c0 m0
    (Hremove : remove_ops (fun op => exists l v, op = MWrite l v /\ 
       not_read_again P gt (Normal c0, m0) l) m m')
    sm (Hsm : make_simple m = Some sm) 
    sm' (Hsm' : make_simple m' = Some sm')
    k c2 ops (Hstep : step P gt (Normal c0) k c2)
    (Hops : can_lower_ops (get_ops k) ops),
    Forall (fun op => match op with 
      MRead l v => sm l = sm' l | _ => True end) ops.
  Proof.
    intros ? ? ? ? ? ? ?; induction Hremove using remove_ops_rev_ind; clarify;
      rewrite Forall_forall in *; intros op Hin; destruct op; clarify.
    - unfold make_simple in *; clarify.
    - rewrite make_simple_snoc in Hsm, Hsm'; clarify.
      exploit IHHremove; eauto; intro Hops'; rewrite Forall_forall in Hops';
        specialize (Hops' _ Hin); clarify.
      destruct (eq_dec l (loc_of a)).
      + eapply simple_same; eauto.
      + rewrite (simple_diff_loc _ _ Hsm2), (simple_diff_loc _ _ Hsm'2); auto.
    - rewrite make_simple_snoc in Hsm; clarify.
      exploit IHHremove; eauto; intro Hops'; rewrite Forall_forall in Hops';
        specialize (Hops' _ Hin); unfold simple_update; clarify.
      specialize (H2 (Normal c0) m0); use H2; eauto; use H2.
      specialize (H2 _ _ _ Hstep Hops _ _ Hin); clarify.
  Qed.

  Lemma dead_store_ops : forall m m' P gt c0 m0
    (Hremove : remove_ops (fun op => exists l v, op = MWrite l v /\ 
       not_read_again P gt (Normal c0, m0) l) m m')
    k c2 ops (Hstep : step P gt (Normal c0) k c2)
    (Hops : can_lower_ops (get_ops k) ops)
    (Hcon : consistent m) (Hcon' : consistent m')
(*    (Hno_cast : Forall (fun x => is_mcast x = false) m)*)
    (Hread_init : read_init (m' ++ ops))
    (Hwrite_alloc : write_alloc (m ++ ops)),
    can_do_ops m ops <-> can_do_ops m' ops.
  Proof.
    intros; generalize (write_alloc_prefix _ Hwrite_alloc); intro.
    exploit (safe_remove_unread); eauto 2.
    { eapply read_init_prefix; eauto. }
    intros [Hinit' Halloc'].
    exploit (consistent_simple Hcon); auto.
    intros [sm Hsm].
    exploit (consistent_simple Hcon'); auto.
    { eapply read_init_prefix; eauto. }
    intros [sm' Hsm'].
    eapply remove_unread_ops; eauto 2.
    eapply step_read_state; eauto.
  Qed.

  Lemma dead_store_step : forall P gt c m m'
    (Hremove : remove_ops (fun op => exists l v, op = MWrite l v /\ 
       not_read_again P gt (Normal c, m) l) m m')
    (Hcon : consistent m) (Hcon' : consistent m')
(*    (Hno_cast : Forall (fun x => is_mcast x = false) m)*)
    l c2 m2 (Hmstep : mem_step P gt (Normal c, m') l (c2, m' ++ m2))
    (Hread_init : read_init (m' ++ m2)) (Hwrite_alloc : write_alloc (m ++ m2)),
    mem_step P gt (Normal c, m) l (c2, m ++ m2) /\ 
      remove_ops (fun op => exists l v, op = MWrite l v /\ 
      not_read_again P gt (c2, m ++ m2) l) (m ++ m2) (m' ++ m2).
  Proof.
    intros; inversion Hmstep; clarify.
    exploit app_inv_head; eauto; clarify.
    assert (mem_step P gt (Normal c, m) (get_out l0) (c2, m ++ m2)).
    - constructor; auto.
      erewrite dead_store_ops; eauto 2.      
    - split; auto; apply remove_ops_app; eapply step_remove_dead; eauto.
  Qed.

(*  Lemma write_alloc_frees : forall al m,
    write_alloc(Val := const_eq Ptr) (rev (get_ops (make_free al)) ++ m)
  = write_alloc(Val := const_eq Ptr) m.
  Proof.
    intros; rewrite get_frees; induction al using rev_ind; clarify.
    rewrite map_app; rewrite rev_app_distr; clarify.
  Qed.*)

  (* MOVE UP *)
  Lemma simple_write : forall m (Hcon : consistent m)
(*    (Hno_cast : Forall (fun x => is_mcast x = false) m)*)
    (Hread_init : read_init m) l v
    (Hwrite_alloc : write_alloc (m ++ [MWrite l v])),
    can_do_op m (MWrite l v).
  Proof. 
    intros; exploit (simple_op); eauto 2.
    { apply read_init_snoc; auto. }
    intros [sm [Hsm Hcan]]; rewrite Hcan; clarify.
  Qed.

  Lemma simple_writes : forall ops m (Hcon : consistent m)
(*    (Hno_cast : Forall (fun x => is_mcast x = false) m)*)
    (Hread_init : read_init m) (Hwrite_alloc : write_alloc (m ++ ops))
    (Hwrites : Forall (fun x => exists l v, x = MWrite l v) ops),
    can_do_ops m ops.
  Proof.
    unfold can_do_ops; induction ops; clarsimp.
    inversion Hwrites; clarify.
    exploit simple_write; eauto.
    instantiate (2 := x0); instantiate (1 := x1); eapply write_alloc_prefix;
      rewrite <- app_assoc; simpl; eauto.
    unfold can_do_op; intro; exploit IHops; eauto.
    - apply read_init_snoc; auto.
    - rewrite <- app_assoc; simpl; auto.
    - rewrite <- app_assoc; simpl; auto.
  Qed.
  (* END MOVE UP *)

  Lemma remove_app : forall P m m' (Hremove : remove_ops P m m') m''
    (Hforall : Forall P m''), remove_ops P (m ++ m'') m'.
  Proof.
    intros ? ? ? Hremove; induction Hremove; clarify.
    induction m''; clarify.
    inversion Hforall; clarify.
  Qed.

  Theorem dse_correct : forall P gt f n (Hdead : is_dead_store P gt f n)
    P1 P2 l params (G : CFG loc) (Hgraph : P = P1 ++ (l, f, params, G) :: P2)
    (Hstart : n <> Start G) (Hexit : n <> Exit G)
    (Hnot_phi : is_phi (Label G (next_node G Seq n)) = false)
    G' (Hrem : remove_seq n G = Some G')
    P' (Hgraph' : P' = P1 ++ (l, f, params, G') :: P2)
    (Hwf : wf_prog P) (Hstart : n <> Start G) (Hwf_CFG : wf_CFG G)
    (Hread_init : forall c' m', 
      reachable (P1 ++ (l, f, params, G') :: P2) gt (c', m') -> 
      read_init m')
    (Hwrite_alloc : forall c m k c', 
      reachable (P1 ++ (l, f, params, G) :: P2) gt (c, m) -> 
      step (P1 ++ (l, f, params, G) :: P2) gt c k c' ->
      forall ops, can_lower_ops (get_ops k) ops ->
      write_alloc (m ++ ops)),
    ro_simulation P' P (dse_sim P f n gt) gt.
  Proof.
    clarify; exploit wf_find_graph; eauto; intro Hf.
    generalize (find_wf_graph(G := G) f Hwf); intro Hwf_G.
    rewrite wf_find_graph in Hwf_G; auto; use Hwf_G.
    generalize (remove_wf Hwf_G Hstart Hexit Hrem); intro Hwf_G'.
    generalize (wf_replace _ _ _ _ _ _ Hwf params Hwf_G'); intro Hwf'.
    exploit wf_find_graph; eauto; intro Hf'.
    unfold ro_simulation; intros; split; intros.
    - unfold dse_sim; clarify.
      exists c0; unfold init_config in *; 
        destruct c0 as [(((((f1, p0), p), env), st), al)|]; clarify.
      destruct (eq_dec f1 f); clarify.
      + rewrite Hf' in H; clarify.
        unfold remove_seq in *; repeat split; clarify.
        right; unfold skip_node; clarify.
      + rewrite find_graph_drop; rewrite find_graph_drop in H;
          unfold skip_node; repeat split; auto; right; clarify.
    - unfold dse_sim in Hsim; destruct C as (c', m'); destruct C' as (c, m);
        destruct C2 as (c2', m2').
      generalize (reachable_consistent Hreach); 
        generalize (reachable_consistent Hreach'); intros Hcon Hcon'.
      destruct c as [c|]; clarify; [|eexists; split; [left;
        apply mem_step_error | unfold dse_sim; clarify]]; auto.
      rewrite wf_find_graph in Hsim2; auto.
(*      generalize (never_cast Hreach); intros [Hcon Hno_cast].
      generalize (never_cast Hreach'); intros [Hcon' Hno_cast'].*)
      destruct (eq_dec (fun_of c) f).
      + destruct (eq_dec (node_of c) n).
        * unfold is_dead_store in Hdead.
          rewrite Hf in Hdead.
          destruct Hdead as [[ty1 [e1 [ty2 [e2 Hstore]]]] Hdead].
          specialize (Hdead _ _ Hreach');
            destruct c as (((((f1, p0), p), env), st), al); clarify.
          Ltac error_tac l := rewrite <- (get_out_map_out l);
            rewrite <- (get_out_map_out []); eexists; split; 
            [right; eexists; split; constructor; repeat rewrite get_ops_map_out;
            clarify; unfold can_do_ops; eauto using lower_nil; 
            autorewrite with list; auto; [eapply store_fail; eauto 2; 
            try (left; clarsimp; fail); try (right; clarsimp; fail) | 
            eapply error; eauto 2] | unfold dse_sim; clarify].
          destruct (eval_expr env gt e1) as [v|] eqn: He1; [|error_tac l0].
          destruct (eval_expr env gt e2) as [v'|] eqn: He2; [|error_tac l0].
          destruct v' as [? | l' | ? | ?]; 
            [error_tac l0 | clarify | error_tac l0 | error_tac l0].
          exploit (store(loc := loc)); try (apply Hf); eauto 2.
          intro Hstep0.
          assert (skip_node (Normal (f, n, next_node G Seq n, env, st, al)) c'
            (P1 ++ (l, f, params, G) :: P2) f n (next_node G Seq n)) as Hskip.
          { unfold skip_node in *; destruct c' as [(((((?, ?), ?), ?), ?), ?)|];
              repeat split; auto; clarify.
            right; rewrite wf_find_graph; auto; clarify. }
          generalize (Hread_init _ _ Hreach); intro Hinit'.
          assert (write_alloc m) as Halloc.
          { inversion Hreach'; clarify.
            exploit @rtc_rev_cases; eauto 2; intros [? | Hcase]; clarify.
            { apply write_alloc_nil. }
            inversion Hcase21; clarify.
            eapply Hwrite_alloc; [unfold reachable; repeat eexists; eauto| |];
              eauto. }
          exploit safe_remove_unread; eauto 2; intros [Hinit Halloc'].
          generalize (Hwrite_alloc _ _ _ _ Hreach' Hstep0); clarify.
          assert (exists ops, can_lower_ops [SWrite ty2 l' v] ops) 
            as [ops Hops].
          { generalize (lower_succeeds (SWrite ty2 l' v)); clarify; eexists;
              constructor; [|constructor]; eauto. }
          assert (can_do_ops m ops) as Hcan.
          { apply simple_writes; auto.
            rewrite Forall_forall; intros; eapply write_writes; eauto.
            inversion Hops as [| ? ? ? ? Hlower Hlower']; inversion Hlower';
              clarify; autorewrite with list in *; eauto. }
          assert (remove_ops (fun op => exists l1 v1, op = MWrite l1 v1 /\
            not_read_again (P1 ++ (l, f, params, G) :: P2) gt
              (Normal (f, n, next_node G Seq n, env, st, al), 
              (m ++ ops)) l1) (m ++ ops) m') as Hmem1.
          { apply remove_app.
            eapply step_remove_dead; eauto; constructor; eauto.
            eapply Hdead; constructor; eauto. }
          exploit remove_mstep; try (apply Hwf); eauto 2.
          { eapply step_safe; eauto. 
            eapply reachable_safe; eauto. }
          { simpl; right; unfold remove_seq in Hrem; clarify. }
          intros [c2 [Hskip2 Hstep2']].
          inversion Hstep2'; clarify.
          exploit dead_store_step; eauto 2.
          { eapply Hread_init; eapply reachable_step; eauto 2. }
          { eapply Hwrite_alloc; [eapply reachable_step| |]; eauto 2.
            exploit step_once; try (apply Hstep0); eauto 2. }
          intros [Hstep2 Hmem2].
          exists (c2, m ++ ops ++ ops0); split.
          { right; eexists; split; eauto.
            exploit step_once; try (apply Hstep0); clarify; eauto 2. 
            rewrite app_assoc; auto. }
          { unfold dse_sim; rewrite app_assoc; clarify. }
        * exploit remove_mstep; try (apply Hwf); eauto 2.
          { eapply reachable_safe; eauto. }
          intros [c2 [Hskip2 Hstep0]].
          inversion Hstep0; clarify.
          exploit dead_store_step; eauto 2.
          { eapply Hread_init; eapply reachable_step; eauto. }
          intros [Hstep2 Hmem2].
          eexists; split; [left; eauto|].
          unfold dse_sim; clarify.
      + exploit remove_mstep; try (apply Hwf); eauto 2.
        { eapply reachable_safe; eauto. }
        intros [c2 [Hskip2 Hstep0]].
        inversion Hstep0; clarify.
        exploit dead_store_step; eauto 2.
        { eapply Hread_init; eapply reachable_step; eauto. }
        intros [Hstep2 Hmem2].
        eexists; split; [left; eauto|].
        unfold dse_sim; clarify.
  Qed.

End CFG_ops.