From ITree Require Import
  ITree
  HeterogeneousRelations.

Class ReflexivePostRel {E} (PR : postrel E E) : Prop :=
  refl_postrel : forall X (e : E X) a b, PR _ _ e a e b -> a = b.

Class ReflexivePreRel {E} (PR : prerel E E) : Prop :=
  refl_prerel : forall X (e : E X), PR _ _ e e.

Variant SumPostRel {E1 E2 D1 D2}
  (RPost1 : postrel E1 E2) (RPost2 : postrel D1 D2) : postrel (E1 +' D1) (E2 +' D2) :=
  | SumPostRel_inl {X Y} (e1 : E1 X) (e2 : E2 Y) a b : RPost1 _ _ e1 a e2 b -> @SumPostRel _ _ _ _ RPost1 RPost2 _ _ (inl1 e1) a (inl1 e2) b
  | SumPostRel_inr {X Y} (d1 : D1 X) (d2 : D2 Y) a b : RPost2 _ _ d1 a d2 b -> @SumPostRel _ _ _ _ RPost1 RPost2 _ _ (inr1 d1) a (inr1 d2) b.

Variant SumPreRel {E1 E2 D1 D2}
  (RPre1 : prerel E1 E2) (RPre2 : prerel D1 D2) : prerel (E1 +' D1) (E2 +' D2) :=
  | SumPreRel_inl {X Y} (e1 : E1 X) (e2 : E2 Y) : RPre1 _ _ e1 e2 -> @SumPreRel _ _ _ _ RPre1 RPre2 _ _ (inl1 e1) (inl1 e2)
  | SumPreRel_inr {X Y} (d1 : D1 X) (d2 : D2 Y) : RPre2 _ _ d1 d2 -> @SumPreRel _ _ _ _ RPre1 RPre2 _ _ (inr1 d1) (inr1 d2).
