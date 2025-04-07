From ExtLib Require Import
     Structures.Monad.

From Paco Require Import paco.

From ITree Require Import
     Indexed.Sum
     ITree
     ITreeFacts
     Props.Infinite.

From ITree.Extra Require Import
     Dijkstra.DijkstraMonad
     Dijkstra.PureITreeBasics.

Import Monads.
Import MonadNotation.
#[local] Open Scope monad_scope.

Section PureITree.

  Definition PureITree A := itree void1 A.

  (*Morally, this is the type of pure itree specifcations. A sigma of this with a monotonicity requiremnet is used
    in order to proved the ordered monad law*)
  Definition _PureITreeSpec A := forall (p : itree void1 A -> Prop), resp_eutt p -> Prop.



  (*Monotonicity condition for specs on pure itrees*)
  Definition monotonici A (w : _PureITreeSpec A) :=
    forall (p p' : itree void1 A -> Prop) (Hp : resp_eutt p) (Hp' : resp_eutt p'),
                                          (forall i', p i' -> p' i') -> w p Hp -> w p' Hp'.

  (* same as monot  *)
  Definition dmonot A (w : _PureITreeSpec A) :=
    forall (p p' : itree void1 A -> Prop) Hp Hp', (forall t, p t <-> p' t) -> (w p Hp <-> w p' Hp').
  (* what if we identify a spec with the intersection of all of the preds it accepts*)
  Lemma monot_imp_dmonot : forall A (w : _PureITreeSpec A), monotonici A w -> dmonot A w.
  Proof.
    unfold monotonici, dmonot. intros. split.
    - apply H; auto. intros. apply H0. auto.
    - apply H; auto. intros. apply H0. auto.
  Qed.

  (* does not hold for many basic specs  *)
  Definition amonot A (w : _PureITreeSpec A) :=
    forall (p p' : itree void1 A -> Prop) Hp Hp', (forall t, p t -> p' t) -> w p' Hp' -> w p Hp.

  (*Sigm*)
  Definition PureITreeSpec A := {w : _PureITreeSpec A | monotonici A w}.

  (*The set of predicates that accept divergent trees*)
  Definition _div_spec A : _PureITreeSpec A := fun p _ => p ITree.spin.

  Lemma div_spec_monot : forall A, monotonici A (_div_spec A).
    Proof.
      unfold monotonici, _div_spec. auto.
    Qed.

  Lemma div_spec_amonot : forall A , amonot A (_div_spec A).
  Proof.
    unfold amonot, _div_spec. intros. auto.
  Abort.
  Definition div_spec A := exist _ (_div_spec A) (div_spec_monot A).

  (*Morally, this is the return function. This is paired with a proof that all such specs are monotonic*)
  Definition _retpi A (a : A) : _PureITreeSpec A := fun p _ => p (ret a).

  Lemma retpi_monot : forall A (a : A), monotonici A (_retpi A a).
  Proof.
    unfold monotonici. intuition. unfold _retpi in *. auto.
  Qed.

  Lemma retpi_amonot : forall A (a : A), amonot A ( _retpi A a ).
  Proof.
    unfold amonot, _retpi. intros.
    Abort.

  (*Proof that the predicate used in the bind function respects eutt*)
  Lemma bind_pred_resp_eutt : forall A B (f : A -> _PureITreeSpec B)
                                     (p : itree void1 B -> Prop) (Hp : resp_eutt p),
      resp_eutt (fun (t : itree void1 A) => (exists a, ret a ≈ t /\ f a p Hp) \/
                                            (any_infinite t /\ p ITree.spin)).
  Proof.
    intros. intros t1 t2 Heutt. setoid_rewrite Heutt. reflexivity.
  Qed.

  (*the bind function for the PureITreeSpec monad
    intuitively, you have two choices, prove the tree evaluates to a and prove f a p,
    or prove t is infinite and prove that the infinite predicate is in w*)
  Definition _bindpi A B (w : _PureITreeSpec A) (f : A -> _PureITreeSpec B) : _PureITreeSpec B :=
    fun (p : itree void1 B -> Prop) (Hp : resp_eutt p) =>
      w (fun (t : itree void1 A) => (exists a, ret a ≈ t /\ f a p Hp) \/
                                    (any_infinite t /\ p ITree.spin ))
        (bind_pred_resp_eutt A B f p Hp).

  Lemma bindpi_monot : forall A B (w : _PureITreeSpec A) (f : A -> _PureITreeSpec B),
      monotonici A w -> (forall a, monotonici B (f a)) -> monotonici B (_bindpi A B w f).
  Proof.
    unfold monotonici. intros. unfold _bindpi in *.
    set (fun (t : itree void1 A) p0 Hp0 =>
      (exists a, ret a ≈ t /\ f a p0 Hp0) \/ (any_infinite t /\ p ITree.spin))  as fp.
    enough (forall t, fp t p Hp -> fp t p' Hp').
    - eapply H with (p := fun t => fp t p Hp).
      + intros.  apply H3 in H4.
        unfold fp in H4. destruct H4; auto.
        destruct H4. right. auto.
      + apply H2.
    - unfold fp. intros. destruct H3; auto. left.
      intros. destruct H3 as [a [Hvala Hfa] ].
      exists a. split; auto.
      eapply H0; [ eauto | ].
      revert Hfa; apply H0; auto.
  Qed.

  (*Definition of ret accounting for the proof of monotonicity*)
  Definition retpi A (a : A) : PureITreeSpec A :=
    exist _ (_retpi A a) (retpi_monot A a).

  (*Definition of bind accounting for the proof of monotonicity*)
  Definition bindpi A B (w : PureITreeSpec A) (f : A -> PureITreeSpec B) :=
    let '(exist _ w' Hw') := w in
    let f' := fun a => proj1_sig (f a) in
    let Hf' := fun a => proj2_sig (f a) in
    exist _ (_bindpi A B w' f') (bindpi_monot A B w' f' Hw' Hf').

  Lemma inf_tree_pred_resp_eutt : forall A B (p : itree void1 B -> Prop),
      resp_eutt (fun (t : itree void1 (A+B)) => any_infinite t /\ p ITree.spin).
  Proof.
    intros. intros t1 t2 Heutt. rewrite Heutt. reflexivity.
  Qed.

  Lemma term_b_pred_resp_eutt : forall A B (p : itree void1 B -> Prop),
      resp_eutt (fun (t : itree void1 (A + B)) => exists b, ret (inr b) ≈ t /\ p (ret b)  ).
  Proof.
    intros. intros t1 t2 Heutt. split; intros.
    - destruct H. exists x. rewrite <- Heutt. auto.
    - destruct H. exists x. rewrite Heutt. auto.
  Qed.

  Lemma cont_a_pred_resp_eutt : forall A B
                                       (F : A -> Prop),
      resp_eutt (fun (t : itree void1 (A + B)) => exists a' , ret (inl a') ≈ t /\ F a'  ).
  Proof.
    intros. intros t1 t2 Heutt. split; intros.
    - destruct H. exists x. rewrite <- Heutt. auto.
    - destruct H. exists x. rewrite Heutt. auto.
  Qed.

  Lemma resp_eutt_or : forall A (p p' : itree void1 A -> Prop),
      resp_eutt p -> resp_eutt p' -> resp_eutt (fun t => p t \/ p' t).
  Proof.
    intros. intros t1 t2 Ht. split; intros.
    - destruct  H1.
      + left. eapply H; eauto. symmetry. auto.
      + right. eapply H0; eauto. symmetry. auto.
    - destruct H1.
      + left. eapply H; eauto.
      + right. eapply H0; eauto.
  Qed.

  Definition iterF_body' {A B : Type}
            (p : itree void1 B -> Prop) (Hp : resp_eutt p) (F : A -> Prop) :=
    fun (t : itree void1 (A + B) ) =>( any_infinite t /\ p ITree.spin) \/
                                    (exists b, ret (inr b) ≈ t /\ p (ret b)  ) \/
                                    (exists a', ret (inl a') ≈ t /\ F a').

  Variant iterF_body {A B : Type}
            (p : itree void1 B -> Prop) (Hp : resp_eutt p) (F : A -> Prop)
            (t : itree void1 (A + B)) : Prop :=
    | inf_tau (Ht: any_infinite t) (Hspin : p ITree.spin)
    | term_b (b : B) (Hretb : ret (inr b) ≈ t ) (Hb : p (ret b))
    | cont_a (a' : A) (Hreta : ret (inl a') ≈ t) (Hcorec : F a')
.

 Lemma iterF_body_equiv : forall A B
            (p : itree void1 B -> Prop) (Hp : resp_eutt p) (F : A -> Prop)
            (t : itree void1 (A + B)), iterF_body p Hp F t <-> iterF_body p Hp F t.
   Proof.
     split; intros; auto.
   Qed.

Hint Constructors iterF_body : itree.

  Lemma iterF_body'_resp_eutt : forall (A B : Type)
            (p : itree void1 B -> Prop) (Hp : resp_eutt p) (F : A -> Prop),
      resp_eutt (iterF_body' p Hp F).
  Proof.
    intros. eapply resp_eutt_or; try eapply resp_eutt_or; intros.
    - apply inf_tree_pred_resp_eutt.
    - apply term_b_pred_resp_eutt.
    - apply cont_a_pred_resp_eutt.
  Qed.

  Lemma iterF_body_resp_eutt : forall (A B : Type)
            (p : itree void1 B -> Prop) (Hp : resp_eutt p) (F : A -> Prop),
      resp_eutt (iterF_body p Hp F).
  Proof.
    intros. intros t1 t2 Heutt. split; intros; inversion H; subst; auto.
    - apply inf_tau; auto. rewrite Heutt in Ht. auto.
    - eapply term_b; eauto. rewrite Hretb. auto.
    - eapply cont_a; eauto. rewrite Hreta. auto.
    - apply inf_tau; auto. rewrite Heutt. auto.
    - eapply term_b; eauto. rewrite Hretb. symmetry. auto.
    - eapply cont_a; eauto. rewrite Hreta. symmetry. auto.
  Qed.

  Variant iterF {A B : Type} (body : A -> PureITreeSpec (A + B))
          (a : A) (p : itree void1 B -> Prop) (Hp : resp_eutt p) (F : A -> Prop) : Prop :=
    | iterF_con : proj1_sig (body a) (iterF_body p Hp F) (iterF_body_resp_eutt A B p Hp F) -> iterF body a p Hp F.

(*
  Inductive iter_ind {A B : Type} (f : A -> PureITreeSpec (A + B) ) (a : A) (p : itree void1 B -> Prop)
           (Hp : resp_eutt _ _ p) : Prop :=
    | iter_ind_cons (Hiter : iterF f a p Hp (fun a0 => iter_ind f a0 p Hp) ) .
*)
(*
  Lemma

  Inductive iter_ind {A B : Type} (body : A -> _PureITreeSpec (A + B) ) (p : itree void1 B -> Prop)
            (Hp : resp_eutt _ _ p) : A -> Prop :=
    | Hiter (a : A) : body a (fun t : itree void1 (A + B) => (any_infinite t /\ p spin)
                                                   \/ (exists b, t ≈ (ret (inr b) /\ p (ret b) ))
                                             \/ (exists a', t ≈ (ret (inl a')) /\
                                         iter_ind body p Hp a') ) .
*)
Hint Constructors iterF : itree.
Lemma iterF_monotone {A B} (body:  (A -> PureITreeSpec (A + B)))
      (sim sim' : A -> Prop) (a : A)
      (p : itree void1 B -> Prop) (Hp : resp_eutt p)
      (IN : iterF body a p Hp sim) (LE : sim <1= sim'):
  iterF body a p Hp sim'.
  Proof.
    induction IN; constructor; auto.
    destruct (body a) as [fa Hfa] eqn : Heq. simpl in *.
    refine (Hfa _ _ _ _ _ H). intros. inversion H0; eauto with itree.
  Qed.

  Definition iter_ {A B} sim (body : A -> PureITreeSpec (A + B)) a p Hp : Prop :=
    iterF body a p Hp sim.
  Hint Unfold iter_ : itree.

  Lemma iterF_monotone' {A B} body p Hp : monotone1 (fun sim a => @iter_ A B sim body a p Hp).
  Proof.
    do 2 red. intros. eapply iterF_monotone; eauto.
  Qed.

  Hint Resolve iterF_monotone' : paco.

  Definition _iter {A B} :=
    fun (f : A -> PureITreeSpec (A + B) ) (a : A) (p : itree void1 B -> Prop) (Hp : resp_eutt p) =>
      paco1 (fun (F : A -> Prop) a => @iter_ A B F f a p Hp ) bot1 a.



  Lemma iter_monot : forall A B (f : A -> PureITreeSpec (A + B) ) (a : A),
                              monotonici B (_iter f a).
    Proof.
      unfold monotonici. intros. generalize dependent a.
      pcofix CIH. pfold. intros. punfold H1.
      red. red in H1. inversion H1; simpl in *.
      constructor. destruct (f a) as [fa Hfa] eqn : Heq. simpl in *.
      refine (Hfa _ _ _ _ _ H0). intros t. intros. inversion H2; subst; eauto with itree.
      pclearbot. eapply cont_a; eauto with itree.
    Qed.

  Definition iterp {A B} (body : A -> PureITreeSpec (A + B) ) (init : A) : PureITreeSpec B :=
    exist _ (_iter body init) (iter_monot A B body init).

(*there may be a way to reason about iteration in spec monads *)

  (*Monad equivalence relation for PureITreeSpec monad *)
  #[global] Instance PureITreeSpecEq : Eq1 PureITreeSpec :=
    fun A w1 w2 => forall (p : itree void1 A -> Prop) (Hp : resp_eutt p), proj1_sig w1 p Hp <-> proj1_sig w2 p Hp.

  #[global] Instance PureItreeSpecMonad : Monad PureITreeSpec :=
    {
      ret := retpi;
      bind := bindpi
    }.

  (*Monad law proofs*)
  Lemma retpi_bindpi : forall A B (f : A -> PureITreeSpec B) (a : A),
      (bind (ret a) f ≈ f a)%monad.
  Proof.
    intros. split.
    - cbn. unfold _bindpi. unfold _retpi. intros.
      destruct H.
      + destruct H as [a0 [Hvala0 Hfa0] ].
        apply eutt_inv_Ret in Hvala0. subst. auto.
      + exfalso. destruct H. eapply ret_not_div. eauto.
    - simpl. destruct (f a) as [fa Hfa] eqn : Heq. simpl. intros.
      left. exists a. split.
      + reflexivity.
      + rewrite Heq.  auto.
  Qed.

  Lemma bindpi_retpi : forall A (w : PureITreeSpec A), (bind w (fun x => ret x) ≈ w)%monad.
  Proof.
    intros. destruct w as [ w Hw]. split.
    - intros. simpl in *. unfold _bindpi in H.
      unfold _retpi in H. simpl in H.
      refine (Hw _ _ _ _ _ H).
      intros. destruct H0.
      + destruct H0 as [a [ Hvala Hpa]  ].
        eapply Hp; eauto. symmetry. auto.
      + destruct H0. apply div_spin_eutt in H0. eapply Hp; eauto.
    - simpl. intros. unfold _bindpi.
      refine (Hw _ _ _ _ _ H). intros. unfold _retpi.
      specialize (eutt_reta_or_div i') as Hor. destruct Hor.
      + destruct H1 as [a Ha]. left. exists a. split; auto. eapply Hp; eauto.
      + right. split; auto. specialize (div_spin_eutt H1) as H2. symmetry in H2. eapply Hp; eauto.
   Qed.

  Lemma bindpi_bindpi : forall (A B C : Type) (w : PureITreeSpec A)
                               (f : A -> PureITreeSpec B) (g : B -> PureITreeSpec C),
      (bind (bind w f) g ≈ bind w (fun a => bind (f a) g))%monad.
  Proof.
    intros. destruct w as [w Hw]. simpl. split; intros.
    - simpl in *. refine (Hw _ _ _ _ _ H). intros t0. intros. destruct H0.
      + destruct H0 as [a [Hreta Hfa]].
        left. exists a. split; auto. destruct (f a) as [wfa Hwfa]. simpl in *.
        refine (Hwfa _ _ _ _ _ Hfa). intros t1. intros. destruct H0; auto.
      + destruct H0. destruct H1.
        * destruct H1 as [b [Hretb Hgb ]  ]. exfalso. specialize (@ret_not_div B void1 b) as Hndiv.
          rewrite Hretb in Hndiv. apply Hndiv. apply spin_infinite.
        *  right. destruct H1. auto.
    - simpl in *. refine (Hw _ _ _ _ _ H). intros t0. intros. destruct H0.
      +  destruct H0 as [a [Hreta Hfa] ]. left. exists a. split; auto.
         destruct (f a) as [wfa Hwfa]. simpl in *.
         refine (Hwfa _ _ _ _ _ Hfa). intros t1. intros.
         destruct H0; auto.
      + destruct H0. right. split; auto. right. split; auto. apply spin_infinite.
  Qed.

  Instance PureItreeSpecLaws : MonadLawsE PureITreeSpec.
  Proof.
    constructor.
    - apply retpi_bindpi.
    - apply bindpi_retpi.
    - apply bindpi_bindpi.
    - intros. red. red. intros mx my Hxy. red. red. red. intros f g Hfg.
      intros. red in Hfg. destruct mx as [ mx Hmx]. destruct my as [my Hmy].
      cbn. unfold _bindpi. do 2 red in Hxy. cbn in Hxy.
      rewrite Hxy. red in Hmy. split; intros; try refine (Hmy _ _ _ _ _ H); eauto.
      + intros. cbn in H0. destruct H0; eauto. left.
        decompose record H0. exists x. split; auto. apply Hfg. auto.
      + intros. cbn in H0. destruct H0; eauto. left.
        decompose record H0. exists x. split; auto. apply Hfg. auto.
  Qed.


  Instance PureITreeOrderM : OrderM PureITreeSpec :=
    fun A (w1 w2 : PureITreeSpec A) => forall p Hp, proj1_sig w2 p Hp -> proj1_sig w1 p Hp.

  Instance PureItreeOrder : OrderedMonad PureITreeSpec.
  Proof.
    constructor.
    - intros. repeat red. intros. destruct w. auto.
    - intros. repeat red. repeat red in H, H0. intros. destruct w1.
      destruct w2. destruct w3. simpl in *. auto.
    - intros. destruct w1 as [w1' Hw1']. destruct w2 as [w2' Hw2']. simpl in *.
      intros p Hp. simpl.
      unfold _bindpi. intros.  eapply H. simpl.
      refine (Hw2' _ _ _ _ _ H1). intros t. intros. destruct H2; auto.
      destruct H2 as [a [Hreta Hf2a] ]. left. specialize (H0 a p Hp). exists a. auto.
  Qed.
(*
  Instance PureITreeIter : Iter (Kleisli PureITreeSpec) sum := @iterp.

  Instance PureITreeIterUnfold : IterUnfold  (Kleisli PureITreeSpec) sum.
  Proof.
    intros A B f a.
    constructor.
    (*this case went through without even needing coinduction???*)
    - intros. red. repeat red in H. punfold H. destruct H.
      cbn. unfold bindpi, _bindpi. destruct (f a) as [fa Hfa]; simpl in *.
      eapply Hfa; eauto. intros t ?Ht. inversion Ht; eauto.
      + left. exists (inr b). split; auto.
      + left. exists (inl a'). split; auto. pclearbot. auto.
    (*very suspicious that I no longer need to coinduct, I think I will move this onto a refactor branch to experiment on*)
    - revert a. (* pcofix CIH. *) intros. cbn in H. pfold. unfold bindpi, _bindpi in H.
      constructor. destruct (f a) as [fa Hfa]; simpl in *. eapply Hfa; try apply H.
      intros t ?Ht. simpl in Ht. basic_solve; auto.
      + eapply cont_a; try apply H0. cbn in H1.
        red in H1. auto.
      + eapply term_b; try apply H0. auto.
  Qed.

  Instance PureITreeIterNatural : IterNatural (Kleisli PureITreeSpec) sum.
  Proof.
    intros A B C. intros. constructor.
    - intros. generalize dependent a. pcofix CIH. intros. pfold. repeat red in H.
      punfold H0. destruct H0.
      destruct (f a) as [fa Hfa] eqn : Heq. simpl in *. constructor.
      cbn. rewrite Heq. simpl. unfold _bindpi. eapply Hfa; eauto.
      intros t ?Ht. basic_solve.
      + right. split; auto. apply inf_tau; auto. apply spin_div.
      + left. exists (inr b). split; auto. cbn. unfold bindpi, _bindpi. simpl.
        destruct (g b) as [gb Hgb] eqn : Heq'. simpl in *. eapply Hgb; try apply H1. intros ?t ?Ht.
        clear H. specialize (eutt_reta_or_div C t0) as Hor. basic_solve.
        * left. exists a0. unfold _retpi. split; auto. eapply term_b; try reflexivity. eapply Hp; eauto.
        * right. split; auto. eapply inf_tau; try apply spin_div. eapply Hp; eauto. symmetry. apply div_spin_eutt. auto.
      + left. exists (inl a'). split; auto. cbn. unfold _bindpi, _retpi, id. left. exists a'.
        split; try reflexivity. eapply cont_a; try reflexivity. right. apply CIH; auto.
    - intros. generalize dependent a. pcofix CIH. intros. pfold. red.
      repeat red in H0.
      constructor.
      destruct (f a) as [fa Hfa] eqn : Heq. simpl in *. punfold H0. destruct H0. simpl in H.
      cbn in H. unfold bindpi, _bindpi in H. rewrite Heq in H. simpl in *. eapply Hfa; try apply H.
      intros t ?. simpl in *. basic_solve.
      + cbn in H1. unfold _bindpi, _retpi in H1. basic_solve. unfold id in *. basic_solve.
        eapply cont_a; eauto. auto.
      + cbn in H1. unfold bindpi, _bindpi in H1. eapply term_b; try apply H0.
        left. exists b. split; try reflexivity. destruct (g b) as [gb Hgb] eqn : Heq'.
        simpl in *. eapply Hgb; try apply H1. intros ?t ?Ht. simpl in *. basic_solve.
        * unfold _retpi in H3. basic_solve. eapply Hp; eauto. symmetry. auto.
        * apply div_spin_eutt in H2. eapply Hp; eauto.
      + apply inf_tau; auto. right. split; auto. apply spin_div.
   Qed.

  (*I am sorry, I will come up for some automation for this eventually*)
  Instance PureITreeDinatural : IterDinatural (Kleisli PureITreeSpec) sum.
  Proof.
    intros A B C. intros. constructor.
    (* can't coinduct in this case it seems, fingers crossed I don't need to *)
    - intros. cbn. unfold bindpi, _bindpi. destruct (f a) as [fa Hfa] eqn : Heq. simpl.
      cbn in H. punfold H. destruct H. cbn in H. unfold bindpi, _bindpi in H. rewrite Heq in H. simpl in *.
      eapply Hfa; try apply H. intros t ?. simpl in H0.
      basic_solve; auto.
      + rename a0 into b. left. exists (inl b). split; auto. cbn. cbn in H1. clear H. clear H0.
        generalize dependent b. pcofix CIH.
        intros. pfold. constructor. cbn. unfold bindpi, _bindpi.
        destruct (g b) as [gb Hgb] eqn : ?Heq. simpl in *. eapply Hgb; try apply H1.
        intros ?t ?Ht. basic_solve.
        * right. split; auto. apply inf_tau; auto. apply spin_div.
        * rename b0 into c. left. exists (inr c). split; auto. cbn. unfold _retpi.
          eapply term_b; eauto. reflexivity.
        * left. exists (inl a'). split; auto. cbn. punfold Hcorec. destruct Hcorec. cbn in H.
          unfold bindpi, _bindpi in H. destruct (f a') as [fa' Hfa'] eqn :?Heq. simpl in *.
          eapply Hfa'; try apply H. intros ?t ?Ht. simpl in *. basic_solve.
          -- cbn in H2. rename a0 into b'. eapply cont_a; eauto. auto.
          -- cbn in H2. rename b0 into c. unfold _retpi in H2. basic_solve.
             eapply term_b; try apply Hb. auto.
          -- apply inf_tau; auto.
      + cbn in H1. unfold _retpi in H1. basic_solve. rename b into c. left.
        exists (inr c). auto.
  - intros. generalize dependent a. pcofix CIH.
    intros. pfold. constructor. cbn. cbn in H0. unfold bindpi, _bindpi in *.
    destruct (f a) as [fa Hfa] eqn : Heq. simpl in *. eapply Hfa; try apply H0.
    intros t ?. simpl in *. basic_solve.
    + rename a0 into b. left. exists (inl b). split; auto. cbn. cbn in H1. red in H1.
      punfold H1. destruct H1. cbn in H1. unfold bindpi, _bindpi in H1. destruct (g b) as [gb Hgb] eqn : ?Heq.
      simpl in *. eapply Hgb; try apply H1. intros ?t ?Ht. simpl in *. clear H1.
      basic_solve.
      * cbn in H2. eapply cont_a; try apply H1. right. apply CIH. cbn.
        unfold bindpi, _bindpi. destruct (f a0) as [fa0 Hfa0] eqn : ?Heq. simpl in *.
        eapply Hfa0; try apply H2. intros ?t ?Ht. basic_solve; auto.
        -- rename b0 into c. left. exists (inr c). split; auto.
        -- rename a' into b'. left. exists (inl b'). split; auto.
      * cbn in H2. unfold _retpi in H2. basic_solve.
        rename b0 into c. eapply term_b; try apply Hb. auto.
      * apply inf_tau; auto.
    + cbn in H1. unfold _retpi, id in H1. left. rename b into c. exists (inr c). split; auto.
      cbn. unfold _retpi. eapply term_b; eauto. reflexivity.
    + right. split; auto. apply inf_tau; auto. apply spin_div.
  Qed.

  Instance PureITreeIterCodiagonal : IterCodiagonal (Kleisli PureITreeSpec) sum.
  Proof.
    intros A B f. constructor.
    - intros. generalize dependent a. pcofix CIH. intros. cbn in H0. punfold H0.
      pfold. destruct H0. constructor. cbn in H. cbn. punfold H.  destruct H.
      unfold bindpi, _bindpi. destruct (f a) as [fa Hfa] eqn : Heq. simpl in *. eapply Hfa; try apply H.
      intros t ?. simpl in *. basic_solve.
      + right. split; auto.
      + left. exists (inr (inr b) ). split; auto. clear H. cbn. unfold _retpi.
        eapply term_b; try apply Hb0. reflexivity.
      + left. exists (inr (inl a0) ). clear H. split; auto. cbn. unfold _retpi.
        eapply cont_a; unfold id; try reflexivity. right. apply CIH. apply Hcorec.
      + left. exists (inl a'). split; auto. cbn. unfold _retpi.
        eapply cont_a; try reflexivity. clear H. right. apply CIH. red. pfold.
        red. constructor. punfold Hcorec. red in Hcorec. destruct Hcorec. destruct (f a') as [fa' Hfa'] eqn : ?Heq.
        simpl in *. red. pfold. constructor. rewrite Heq0. simpl in *.
        eapply Hfa'; try apply H. clear H. intros ?t ?Ht. auto.
    - intros. punfold H. generalize dependent a. pcofix CIH. intros. cbn in H0. pfold. constructor.
      destruct H0. cbn in H. cbn.  unfold bindpi, _bindpi in H. pfold. constructor.
      destruct (f a) as [fa Hfa] eqn : Heq. simpl in *. eapply Hfa; try apply H.
      rename H into Ha.
      intros t ?. simpl in *. basic_solve.
      + cbn in H0. unfold _retpi in H0. basic_solve. eapply cont_a; try apply H.
        clear H.  left.
        generalize dependent a0.
        pcofix CIH'. intros. pfold. constructor. clear Ha. punfold Hcorec.
        destruct Hcorec. cbn in H. unfold bindpi, _bindpi in H. simpl in *.
        destruct (f a0) as [fa0 Hfa0] eqn : ?Heq. simpl in *. eapply Hfa0; try apply H.
        clear H. intros ?t ?Ht. simpl in *. basic_solve.
        * cbn in H0. unfold _retpi in H0. basic_solve. eapply cont_a; try apply H. auto.
        * cbn in H0. unfold _retpi in H0. basic_solve. eapply term_b; try apply H. eapply cont_a; try reflexivity.
          right. apply CIH. punfold Hcorec.
        * cbn in H0. unfold _retpi, id in H0. basic_solve. eapply term_b; try apply H.
          eapply term_b; try reflexivity. auto.
        * apply inf_tau; auto.
      + cbn in H0. unfold _retpi, id in H0. basic_solve. eapply term_b; try apply H. eapply cont_a; try reflexivity.
        right. apply CIH. punfold Hcorec.
      + cbn in H0. unfold _retpi, id in H0. basic_solve. eapply term_b; try apply H. eapply term_b; try reflexivity.
        auto.
      + apply inf_tau; auto.
   Qed.


  Lemma obsip_pres_iter_right : forall A B (f : A -> itree void1 (A + B) ) (a : A)
            (p : itree void1 B -> Prop) (Hp : resp_eutt void1 B p),
     proj1_sig (obsip B (iter f a)) p Hp -> proj1_sig (iterp (fun x => obsip _ (f x) ) a) p Hp.
  Proof.
    intros. generalize dependent a. pcofix CIH. intros. pfold. constructor.
    cbn. red.
    simpl. specialize (unfold_iter_ktree f a) as Hunfold.
    cbn in H0. red in H0. symmetry in Hunfold. eapply Hp in H0;
                                                 try (rewrite <- Hunfold; reflexivity).
    specialize (eutt_reta_or_div _ (f a) ) as [Hret | Hdiv]; basic_solve.
    - eapply cont_a; try apply Hret. right. apply CIH. cbn. red. eapply Hp; eauto. rewrite <- Hret.
      setoid_rewrite bind_ret.
      rewrite tau_eutt. reflexivity.
    - eapply term_b; try apply Hret. eapply Hp; eauto.
      rewrite <- Hret. match goal with | |- _ ≈ ITree.bind _ ?g =>
                              specialize (bind_ret (inr b) g) as Hbind_ret end.
        rewrite Hbind_ret. reflexivity.
    - apply div_spin_eutt in Hdiv as Hspin. apply inf_tau; auto.
      eapply Hp; eauto. rewrite Hspin. apply spin_bind.
   Qed.

  Ltac proof_by_contra := match goal with | |- ?P => destruct (classic P) as [ ? | Hcontra];
                                                     auto end.

  Lemma obsip_pres_iter_left : forall A B (f : A -> itree void1 (A + B) ) (a : A)
                             (p : itree void1 B -> Prop) (Hp : resp_eutt void1 B p),
      proj1_sig (iterp (fun x => obsip _ (f x) ) a) p Hp -> proj1_sig (obsip B (iter f a)) p Hp.
  Proof.
    intros. cbn. red. cbn in H. red in H. cbn in H.
    punfold H. destruct H. cbn in H. red in H.
    basic_solve; auto.
    - apply div_spin_eutt in Ht as H1. eapply Hp; eauto.
      specialize (unfold_iter_ktree f a) as Hunfold. rewrite Hunfold. rewrite H1.
      symmetry. apply spin_bind.
    - specialize (unfold_iter_ktree f a) as Hunfold.
      eapply Hp; eauto. rewrite Hunfold. rewrite <- Hretb.
      match goal with | |- ITree.bind _ ?g ≈ _ => specialize (bind_ret (inr b) g)
      as Hbind_ret end. simpl in *. rewrite Hbind_ret. reflexivity.
    - specialize (unfold_iter_ktree f a) as Hunfold. eapply Hp; eauto;
      try (rewrite Hunfold; reflexivity).
      (* assert (_iter (fun x : A=> obsip (A + B) (f x) ) a'  p Hp); auto. *) unfold resp_eutt in *.
      eapply Hp with (t1 := KTree.iter f a'); eauto.
      + rewrite <- Hreta. setoid_rewrite bind_ret.
        rewrite tau_eutt. reflexivity.
      + (* I have unfolded in some sense, I want to have a coinductive hyp here *)
  Abort.

  Lemma iter_too_big_aux : exists A B (f : A -> itree void1 (A + B) ) (p : itree void1 B -> Prop) (a : A) Hp,
       proj1_sig (iterp (fun x => obsip _ (f x) ) a) p Hp /\ ~ proj1_sig (obsip B (iter f a)) p Hp.
  Proof.
    exists nat. exists nat. exists (fun n => ret (inl n) ). exists (fun _ => False).
    exists 0. assert (resp_eutt _ _ (fun _  : itree void1 nat => False) ).
    { intros t1 t2. tauto. } exists H.
    split; auto.
    pcofix CIH. pfold. constructor. cbn. red. eapply cont_a; eauto. reflexivity.
  Qed.

  Lemma iter_too_big : ~  forall A B (f : A -> itree void1 (A + B) ) (a : A)
                             (p : itree void1 B -> Prop) (Hp : resp_eutt void1 B p),
      proj1_sig (iterp (fun x => obsip _ (f x) ) a) p Hp -> proj1_sig (obsip B (iter f a)) p Hp.
  Proof.
    intro Hcontra.
    specialize iter_too_big_aux as Hlem. basic_solve. auto.
  Qed.

  (*Other direction is odd, because I can't just straightforwardly coinduct*)

  Lemma obsip_pres_iter : forall A B (f : A -> itree void1 (A + B) ) (a : A),
        obsip _ (iter f a) ≈ iterp (fun (x : A) => obsip (A + B) (f x) ) a.
  Proof.
    intros. constructor.
    -  apply obsip_pres_iter_right.
    - intros. cbn. red. cbn in H. unfold obsip, _obsip in H. simpl in H.
      red in H. punfold H. destruct H. simpl in *.
      cbn in H.
  Abort.
*)

  (*Definition of effect observation from pure itrees into pure itree specs *)
  Definition _obsip A (t : itree void1 A) : _PureITreeSpec A := fun p _ => p t.
(*
  Definition f A : A -> itree void1 nat := fun (a : A) => ret 2.

  Lemma ex : forall p Hp, _obsip nat (bind spin f) p Hp.
    intros. unfold _obsip. *)

  Lemma obsip_monot : forall A (t : itree void1 A), monotonici A (_obsip A t).
  Proof.
    unfold monotonici. intros. unfold _obsip in *. auto.
  Qed.

  Definition obsip A (t : itree void1 A) : PureITreeSpec A :=
    exist _ (_obsip A t) (obsip_monot A t).

  (*Proof that this effect observation is a valid monad morphism*)
  Lemma obsip_pres_ret : forall A (a : A), (obsip A (ret a) ≈ ret a)%monad.
  Proof.
    intros. intros p Hp. cbn. unfold _retpi, _obsip. tauto.
  Qed.

  Lemma obsip_pres_bind : forall A B (t : itree void1 A) (f : A -> itree void1 B),
        (obsip B (bind t f) ≈ bind (obsip A t) (fun a => obsip B (f a)))%monad.
  Proof.
    intros. intros p Hp. cbn. unfold _obsip, _bindpi. split; intros.
    - specialize (eutt_reta_or_div t) as Hor. destruct Hor.
      + destruct H0 as [a Hreta ]. left. exists a. split; auto.
        eapply Hp; eauto. specialize (bind_ret_l a f) as H1. rewrite <- H1.
        rewrite Hreta. reflexivity.
      + right. split; auto. apply div_spin_eutt in H0. rewrite (spin_bind f), <- H0; apply H.
    - destruct H.
      + destruct H as [a [Hreta Hpfa] ]. specialize (bind_ret_l a f) as H1.
        eapply Hp; eauto.  rewrite <- H1. rewrite Hreta. reflexivity.
      + destruct H. apply div_spin_eutt in H.
        rewrite H, <- spin_bind. apply H0.
  Qed.

  Lemma obsip_eutt : forall A (t1 t2 : itree void1 A), t1 ≈ t2 <-> (obsip A t1 ≈ obsip A t2)%monad.
  Proof.
    split; intros; unfold obsip, _obsip in *; simpl in *.
    - intros p Hp. simpl. split; intros; eapply Hp; eauto.
      symmetry. auto.
    - set (fun t => t ≈ t1) as p.
      assert (Hp : resp_eutt p).
      + intros t3 t4. unfold p. split; intros.
        * rewrite <- H1. symmetry. auto.
        * rewrite H0. auto.
      + specialize (H p Hp). simpl in *. unfold p in H. symmetry. apply H. reflexivity.
  Qed.

  #[global] Instance PureITreeEffectObs : EffectObs (itree void1) (PureITreeSpec) := obsip.

  #[global] Instance PureITreeMorph : MonadMorphism (itree void1) (PureITreeSpec) PureITreeEffectObs.
  Proof.
    constructor.
    - apply obsip_pres_ret.
    - apply obsip_pres_bind.
  Qed.

End PureITree.
