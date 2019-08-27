From ITree Require Import 
     ITree
     Events.State.

Set Implicit Arguments.

(* View XY Z X generalizes the Subevent relation.
   Should be thought as `X` is a subdomain of `XY`, and `Z` a view of the complement.
   Note that one could always chose to take Z = unit, but it is important to express operations.
 *)
Class View {XY Z X : Type -> Type} : Type :=
  { preview : XY ~> X +' Z
    ; review : X ~> XY
    ; preview_review : forall {t} (x : X t), preview (review x) = inl1 x
    ; review_preview : forall {t} (xy : XY t) x, preview xy = inl1 x -> review x = xy
  }.
Arguments View : clear implicits.
Arguments preview {_ _ _} _ [_].
Arguments review {_ _ _} _ [_].

(* Partial injection of the bigger domain of events back into the smaller one *)
Definition isa {X Z y} {V : View X Z y} : forall t, X t -> option (y t) :=
  fun t mx =>
    match V.(preview) mx with
    | inl1 x => Some x
    | inr1 _ => None
    end.

(* Embedding of the subdomain into the bigger one *)
Definition subevent {X Z y} {V : View X Z y} : y ~> X := V.(review).

(* Generic lifting of an type-indexed function from the subdomain of effects `a`
   into the ambient one `A`.
   This is where we crucially need the `Z` argument to
   ̀View` for `preview` to also tell us how to embed the complement `A\a` into
   `B`. *)
Definition over {A B a} {z : View A B a} (f : a ~> B) : A ~> B :=
  fun t a => match z.(preview) a with
          | inl1 a => f _ a
          | inr1 b => b
          end.
Arguments over {_ _ _ _} _ [_] _.

(* The less informative previous Subevent relation is recovered by dismissing the `Z` parameter *)
Definition Subevent A B := forall x, View A x B.

(* Should be enough to express generic lemmas as needed for swap *)
(* The instance from atomic domains of events to bigger ones is expressed through `over` *)

(*
  forall f, translate f (trigger x) = trigger (f x)
  over {V} swap (subevent {V} x) = subevent {V} (swap {V} x)
  -----------------
  translate swap (trigger (subevent {f} x)) ~ trigger (subevent {f} (swap x))
  
  forall V, translate (over {z:=V} (swap a b)) X

  translate (over f) (Vis e k) = Vis (over f e) (fun x => translate (over f) k)
  translate (over f) (translate (over g) X) = 
*)

(* Things are also interested with respect to simplifying the construction of interpreters.
 Consider the case from GlobalE for example *)
From ITree Require Import 
     Events.State.
From Vellvm Require Import
     LLVMEvents.
From ExtLib Require Import
     Programming.Show
     Structures.Monads
     Structures.Maps.

Section Globals.
  Variable (k v:Type).
  Context {map : Type}.
  Context {M: Map k v map}.
  Context {SK : Show k}.
 
  Import ITree.Basics.Basics.Monads.

  (* Lift an interpreter g handling only GlobalE to one over a generic overset of effects.
     Note that we use the Z parameter here with another structure than a domain of events.
     Makes a lot of sense, but raises the question of instances to be inferred.
     Relates to our concern for generic triggers?
   *)
  Definition foo {e f s}
             {vv :View f (stateT s (itree e)) (GlobalE k v)}
             (g : GlobalE k v ~> stateT s (itree e))
    : itree f ~> stateT s (itree e).
  Proof.
    eapply interp_state.
    intros.
    generalize (@over _ _ _ vv). intros.
    eapply X0. eapply g. eapply X.
  Defined.

End Globals.

(* We should still be able to build our instances with a bit more work *)
Instance View_id {A} : View A void1 A.
refine
  {| preview := inl1
     ; review := fun _ x => x
  |}.
auto.
intros ? ? ? H; inversion H; auto.
Defined.

Instance View_none {A}: View A A void1.
refine
  {| preview := inr1
     ; review := fun t (x: void1 t) => match x with end
  |}.
intros ? x; inversion x.
intros ? ? x; inversion x.
Defined.

(* Z +' B ? *)
Instance View_L {A B Z a} {_ : View A Z a} : View (A +' B) Z a.
Admitted.
Definition View_R {A B Z b} (_ : View B Z b) : View (A +' B) Z b.
Admitted.



(* **** JUNK TO SORT **** *)

(* We can define join if need be *)
 CoFixpoint join {E} : itree (itree E) ~> itree E.
  intros. econstructor.
  destruct (X.(observe)).
  { eapply RetF. exact r. }
  { eapply TauF. exact (join _ _ t). }
  { eapply TauF. eapply ITree.bind'. 2: exact e.
    exact (fun x => join _ _ (k x)). }
  Defined.

(*
  E -< itree E  :: trigger
  MonadTrans (stateT s)
  trigger :: stateT s (itree E)

  View A Z x -> B -< Z -> View (A +' B) Z x
  View A void1 x
*)

(*
  e1 ~> stateT s1 (itree f1)
  e2 ~> stateT s2 (itree f2)

  itree (stateT s1 (itree f1) +' stateT s2 (itree f2))
  stateT s1 (itree (itree f1 +' stateT s2 (itree f2)))
 *)
(* Old version toying with a four places version of View *)
(*
  Record View {XY Z X Y : Type -> Type} : Type :=
  { preview : XY ~> X +' Z
  ; review : Y ~> Z
  }.
  Arguments View : clear implicits.
  Arguments preview {_ _ _ _} _ [_].
  Arguments review {_ _ _ _} _ [_].

  Definition isa {X y} {V : View X X y y} : forall t, X t -> option (y t).
  intros. eapply V.(preview) in X0.  destruct X0. exact (Some y0). exact None.
  Defined.

  Definition inject {X y} {V : View X X y y} : y ~> X := V.(review).

  Definition over {A B a Z} {z : View A B a Z} (f : a ~> B) : A ~> B.
    refine (fun t a => match z.(preview) a with
                    | inl1 a => f _ a
                    | inr1 b => b
                    end).
  Defined.



  Definition View_id {A} : View A A void1.
  Admitted.
  Definition View_none {A} : View A void1.
  Admitted.
  Definition View_L {A B a} (_ : View A a) : View (A +' B) a.
  Admitted.
  Definition View_R {A B b} (_ : View B b) : View (A +' B) b.
  Admitted.
*)

(* Trying to figure out what we need exactly
    Record we_want {X Y x : Type -> Type} : Type :=
    { other : Type -> Type
    ; otherp : other ~> Y
    ; go : (x ~> Y) -> (X ~> Y)
    ; iso : Iso X (other + x)
    ; _ : forall h a, go h = match iso a with
                        | inl b => otherp b
                        | inr b => h b
                        end

    }.
    Arguments we_want : clear implicits.



    Definition ww_map {A} : we_want A A A.
      refine {| other := void1
             |}.
      destruct 1.
      exact (fun x => x).
    Defined.

    Definition ww_ignore {A x} : we_want A  A x.
    refine {| other := A
              ; otherp := fun _ x => x
              ;go := fun _ _ x => x
           |}.
    Defined.

    Definition ww_x {A B C x} (wwA : we_want A C x) (wwB : we_want B C x)
    : we_want (A +' B) C x.
    refine {| other := wwA.(other) +' wwB.(other)
            |}.
    { destruct 1.
      eapply wwA.(otherp). assumption.
      eapply wwB.(otherp). assumption. }
    destruct 2.
    eapply wwA.(go); eauto.
    eapply wwB.(go); eauto.
    Defined.

    (X ~> x + other) -> (other ~> Y) -> (x ~> Y) -> itree X ~> T (itree Y)

*)

(* First version, Gregory trying to stick mor precisely to Haskell's prisms
  Section with_mapping.
    Record Prism {B A : Type -> Type} : Type :=
    { p_ask : forall t, A t -> option (B t)
    ; p_put : forall t, B t -> A t
    ; ask_put : forall t (x : A t) y, p_ask x = Some y -> p_put y = x
    ; put_ask : forall t (x : B t), p_ask (p_put x) = Some x
    ; ask_only : forall t (x : A t), p_ask x = None -> forall y, p_put y <> x
    }.
    Arguments Prism _ _ : clear implicits.
    Arguments ask_put {_ _} _ _ _.
    Arguments put_ask {_ _} _ _.
    Arguments ask_only {_ _} _ _ _.

    Definition Prism_id {A} : Prism A A.
    refine
    {| p_ask _ x := Some x
     ; p_put _ x := x
     |}.
    { inversion 1. auto. }
    { reflexivity. }
    { inversion 1. }
    Defined.

    Definition Prism_L {A B C} (P : Prism B A) : Prism (B +' C) (A +' C).
    econstructor.
    Unshelve.
    4:{ intros. destruct X.
      eapply P.(p_ask) in a.
      destruct a.
      { eapply Some. constructor. eapply b. }
      { eapply None. }
      eapply Some. right. assumption. }
    4: { destruct 1.
         { constructor. eapply P.(p_put). assumption. }
         right. assumption. }
    { simpl. destruct x; simpl; intros.
      { generalize (P.(ask_put) _ a).
        destruct (p_ask P t a).
        { inversion H.
          intro. specialize (H0 _ eq_refl).
          congruence. }
        { congruence. } }
      { inversion H. congruence. } }
    { simpl.
      destruct x.
      erewrite put_ask. reflexivity. reflexivity. }
    { simpl. destruct x; try congruence.
      generalize (P.(ask_only) _ a).
      destruct (p_ask P t a); try congruence.
      intros. destruct y.
      intro. inversion H1. eapply H; eauto.
      congruence. }
    Defined.

    Record Prism' {A B C D : Type -> Type} : Type :=
    { pleft : Prism C A
    ; pright : Prism D B
    }.
    Arguments Prism' : clear implicits.
    Arguments pleft {_ _ _ _} _.
    Arguments pright {_ _ _ _} _.
    

    Definition pover {A B C D} (p : Prism' A B C D) : (C ~> D) -> (A ~> B).
      intros.
      eapply (p.(pleft).(p_ask)) in X0.
      destruct X0.
      { eapply X in c.
        eapply (p.(pright).(p_put) _ c). }
      { 

    view   : A -> a + o
    insert : a + o -> A

    Record Prism' {A B C D : Type -> Type} : Type :=
    { get : forall t, A t -> option (C t)
    ; put : 


  End with_mapping.

*)