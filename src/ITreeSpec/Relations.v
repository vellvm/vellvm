From ITree Require Import
  ITree
  HeterogeneousRelations.

From Stdlib Require Import
  Eqdep.

Ltac inj_existT := repeat match goal with
                          | H:existT _ _ _ = _ |- _ => apply inj_pairT2 in H
                          end.

Class ReflexivePostRel {E} (PR : postrel E E) : Prop :=
  { refl_postrel : forall X (e : E X) x, PR _ _ e x e x
  ; refl_postrel_inv : forall X (e : E X) x y, PR _ _ e x e y -> x = y
  }.

Class ReflexivePreRel {E} (PR : prerel E E) : Prop :=
  refl_prerel : forall X (e : E X), PR _ _ e e.

Class TransitivePreRel {E} (PR : prerel E E) : Prop :=
  trans_prerel : forall X Y Z (a : E X) (b : E Y) (c : E Z),
      PR _ _ a b ->
      PR _ _ b c ->
      PR _ _ a c.

Class TransitivePostRel {E} (PR : postrel E E) : Prop :=
  trans_postrel :
    forall A B C (ea : E A) (eb : E B) (ec : E C) a b c,
      PR _ _ ea a eb b ->
      PR _ _ eb b ec c ->
      PR _ _ ea a ec c.

Class SymmetricPostRel {E} (PR : postrel E E) : Prop :=
  symm_postrel : forall A B (ea : E A) (eb : E B) a b,
      PR _ _ ea a eb b ->
      PR _ _ eb b ea a.

Class SymmetricPreRel {E} (PR : prerel E E) : Prop :=
  symm_prerel : forall A B (ea : E A) (eb : E B),
      PR _ _ ea eb ->
      PR _ _ eb ea.

Variant RComposePostRel {E1 E2 E3}
  (RPre1 : prerel E1 E2) (RPre2 : prerel E2 E3) (RPost1 : postrel E1 E2) (RPost2 : postrel E2 E3) : postrel E1 E3 :=
  | RComposePostRel_intro {A C} (e1 : E1 A) (e3 : E3 C) a c :
    (forall B (e2 : E2 B), RPre1 A B e1 e2 -> RPre2 B C e2 e3 -> exists b, RPost1 A B e1 a e2 b /\ RPost2 B C e2 b e3 c) ->
    RComposePostRel RPre1 RPre2 RPost1 RPost2 A C e1 a e3 c.

Variant RComposePostRel' {E1 E2 E3}
  (RPost1 : postrel E1 E2) (RPost2 : postrel E2 E3) : postrel E1 E3 :=
  | RComposePostRel_intro' {A C} (e1 : E1 A) (e3 : E3 C) a c :
    forall {B} (e2 : E2 B) b,
      RPost1 A B e1 a e2 b ->
      RPost2 B C e2 b e3 c ->
      RComposePostRel' RPost1 RPost2 A C e1 a e3 c.

Variant RComposePreRel {E1 E2 E3}
  (RPre1 : prerel E1 E2) (RPre2 : prerel E2 E3) : prerel E1 E3 :=
  | RComposePreRel_intro {A C} (e1 : E1 A) (e3 : E3 C) :
    forall {B} e2, RPre1 A B e1 e2 -> RPre2 B C e2 e3 ->
    @RComposePreRel E1 E2 E3 RPre1 RPre2 A C e1 e3.

Lemma trans_RComposePreRel :
  forall E (PRE : prerel E E) `{TRANS : @TransitivePreRel _ PRE},
  forall {X Y} (e1 : E X) (e2 : E Y),
    RComposePreRel PRE PRE _ _ e1 e2 -> PRE _ _ e1 e2.
Proof.
  intros E PRE TRANS X Y e1 e2.
  intros REL.
  inversion REL; inj_existT; subst.
  eapply TRANS; eauto.
Qed.

Lemma refl_RComposePreRel :
  forall E (PRE : prerel E E) `{REFL : @ReflexivePreRel _ PRE},
  forall {X Y} (e1 : E X) (e2 : E Y),
    PRE _ _ e1 e2 ->
    RComposePreRel PRE PRE _ _ e1 e2.
Proof.
  intros E PRE REFL X Y e1 e2.
  intros REL.
  econstructor.
  apply REL.
  apply refl_prerel.
Qed.

Lemma trans_RComposePostRel' :
  forall E (POST : postrel E E) `{TRANS : @TransitivePostRel _ POST},
  forall {X Y} (e1 : E X) x (e2 : E Y) y,
    RComposePostRel' POST POST _ _ e1 x e2 y -> POST _ _ e1 x e2 y.
Proof.
  intros E POST TRANS X Y e1 x e2 y REL.
  inversion REL; inj_existT; subst.
  eapply TRANS; eauto.
Qed.

Lemma refl_RComposePostRel' :
  forall E (POST : postrel E E) `{REFL : @ReflexivePostRel _ POST},
  forall {X Y} (e1 : E X) x (e2 : E Y) y,
    POST _ _ e1 x e2 y ->
    RComposePostRel' POST POST _ _ e1 x e2 y.
Proof.
  intros E POST REFL X Y e1 x e2 y REL.
  econstructor.
  apply REL.
  apply refl_postrel.
Qed.

Variant SumPostRel {E1 E2 D1 D2}
  (RPost1 : postrel E1 E2) (RPost2 : postrel D1 D2) : postrel (E1 +' D1) (E2 +' D2) :=
  | SumPostRel_inl {X Y} (e1 : E1 X) (e2 : E2 Y) a b : RPost1 _ _ e1 a e2 b -> @SumPostRel _ _ _ _ RPost1 RPost2 _ _ (inl1 e1) a (inl1 e2) b
  | SumPostRel_inr {X Y} (d1 : D1 X) (d2 : D2 Y) a b : RPost2 _ _ d1 a d2 b -> @SumPostRel _ _ _ _ RPost1 RPost2 _ _ (inr1 d1) a (inr1 d2) b.

Variant SumPreRel {E1 E2 D1 D2}
  (RPre1 : prerel E1 E2) (RPre2 : prerel D1 D2) : prerel (E1 +' D1) (E2 +' D2) :=
  | SumPreRel_inl {X Y} (e1 : E1 X) (e2 : E2 Y) : RPre1 _ _ e1 e2 -> @SumPreRel _ _ _ _ RPre1 RPre2 _ _ (inl1 e1) (inl1 e2)
  | SumPreRel_inr {X Y} (d1 : D1 X) (d2 : D2 Y) : RPre2 _ _ d1 d2 -> @SumPreRel _ _ _ _ RPre1 RPre2 _ _ (inr1 d1) (inr1 d2).
