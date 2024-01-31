(* begin hide *)
From Coq Require Import
     String
     Classes.Morphisms.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Structures.MonadExc
     Data.Monads.EitherMonad.

From ITree Require Import
     ITree.

From Vellvm.Utils Require Import
     MonadReturnsLaws
     MonadEq1Laws
     Tactics.

Import Monad.

(* end hide *)

(** * Error and exception monads
  The arithmetic performed by vir programs being essentially pure, we have chosen
  not to wrap it in the [itree] monad. It gets instead injected into it when
  representing syntactic constructs relying on it.

  It is however not completely pure: it is partial, and may raise undefined behavior.
  We hence use a nested "double" error monad for this purpose.
*)

Notation err := (sum string).

Definition trywith {E A:Type} {F} `{Monad F} `{MonadExc E F} (e:E) (o:option A) : F A :=
    match o with
    | Some x => ret x
    | None => raise e
    end.
#[export] Hint Unfold trywith: core.
Arguments trywith _ _ _ _ _: simpl nomatch.

Definition failwith {A:Type} {F} `{Monad F} `{MonadExc string F} (s:string) : F A := raise s.
#[export] Hint Unfold failwith: core.
Arguments failwith _ _ _ _: simpl nomatch.

(* A computation that can run out of memory. *)
Variant OOM (A:Type) : Type :=
  | NoOom : A -> OOM A
  | Oom : string -> OOM A.
Arguments NoOom {_} _.
Arguments Oom {_}.

Definition OOM_to_err {A} (o : OOM A) : err A
  := match o with
     | NoOom x => inr x
     | Oom msg => inl msg
     end.

Global Instance MonadOOM : Monad OOM.
Proof using.
  split.
  - refine (fun _ x => NoOom x).
  - refine (fun A B ma k =>
              match ma with
              | NoOom a => k a
              | Oom s => Oom s
              end
           ).
Defined.

Global Instance FunctorOOM : Functor OOM.
Proof using.
  split.
  - refine (fun A B f ma =>
              match ma with
              | NoOom a => NoOom (f a)
              | Oom s => Oom s
              end).
Defined.

Section OOMLaws.
  Global Instance MonadEq1OOM : Eq1 OOM.
  Proof using.
    unfold Eq1.
    refine (fun _ a b =>
              match a, b with
              | NoOom a, NoOom b => a = b
              | Oom s1, Oom s2 => True
              | _, _ => False
              end).
  Defined.

  Global Instance MonadEq1Eqv : Eq1Equivalence OOM.
  Proof using.
    split.
    - unfold eq1, Reflexive.
      intros x; destruct x; cbn; auto.
    - unfold eq1, Symmetric.
      intros x y; destruct x, y; cbn; auto.
    - unfold eq1, Transitive.
      intros x y z; destruct x, y, z; cbn; auto.
      intros H H0.
      congruence.
      intros H H0.
      contradiction.
  Defined.

  Global Instance MonadLawsEOOM : @MonadLawsE OOM MonadEq1OOM MonadOOM.
  Proof using.
    split.
    - reflexivity.
    - intros A x.
      destruct x; cbn; auto.
    - intros A B C x f g.
      destruct x; cbn; auto.
      reflexivity.
    - intros A B.
      unfold Proper, respectful.
      intros x y H x0 y0 H0.
      unfold pointwise_relation in H0.
      destruct x, y; cbn; eauto; inversion H; subst; auto.
  Defined.

  Definition OOMReturns {A} (x : A) (ma : OOM A) : Prop
    := match ma with
       | NoOom y => x = y
       | Oom s => False
       end.

  Definition OOMFails {A} (ma : OOM A) : Prop
    := match ma with
       | NoOom x => False
       | Oom s => True
       end.

  Lemma OOMFails_OOMReturns :
    forall {A} (ma : OOM A),
      OOMFails ma -> forall a, ~ OOMReturns a ma.
  Proof using.
    intros A ma H a.
    intros CONTRA.
    destruct ma; auto.
  Qed.

  Lemma OOMReturns_OOMFails :
    forall {A} (ma : OOM A) (a : A),
      OOMReturns a ma -> ~ OOMFails ma.
  Proof using.
    intros A ma a H.
    destruct ma; auto.
  Qed.

  Lemma OOMFails_ret :
    forall {A} (a : A),
      ~ OOMFails (ret a).
  Proof using.
    intros A a.
    cbn; auto.
  Qed.

  Lemma OOMFails_bind_ma : forall {A B} (ma : OOM A) (k : A -> OOM B),
      OOMFails ma -> OOMFails (bind ma k).
  Proof using.
    intros A B ma k FAILS.
    destruct ma; cbn in *; [contradiction|auto].
  Qed.

  Lemma OOMFails_bind_k : forall {A B} (ma : OOM A) (a : A) (k : A -> OOM B),
      OOMReturns a ma ->
      OOMFails (k a) ->
      OOMFails (bind ma k).
  Proof using.
    intros A B ma a k RETS FAILS.
    destruct ma; cbn in *;
      [subst; eauto | contradiction].
  Qed.

  Lemma OOMFails_bind_inv : forall {A B} (ma : OOM A) (k : A -> OOM B),
      OOMFails (bind ma k) ->
      OOMFails ma \/ (exists a, OOMReturns a ma /\ OOMFails (k a)).
  Proof using.
    intros A B ma k FAILS.
    destruct ma; cbn in *.
    - right; eexists; split; auto.
    - left; auto.
  Qed.

  Lemma OOMReturns_bind :
    forall {A B} (a : A) (b : B) (ma : OOM A) (k : A -> OOM B),
      OOMReturns a ma -> OOMReturns b (k a) -> OOMReturns b (bind ma k).
  Proof using.
    intros A B a b ma k RETA RETB.
    destruct ma; cbn; auto.
    inversion RETA; subst; auto.
  Qed.

  Lemma OOMReturns_strong_bind_inv :
    forall {A B} (ma : OOM A) (k : A -> OOM B) (b : B),
      OOMReturns b (bind ma k) -> exists a : A , OOMReturns a ma /\ OOMReturns b (k a).
  Proof using.
    intros A B ma k b RET.
    cbn in RET.
    destruct ma; cbn in RET; try contradiction.
    exists a.
    split; cbn; auto.
  Qed.

  Lemma OOMReturns_bind_inv :
    forall {A B} (ma : OOM A) (k : A -> OOM B) (b : B),
      OOMReturns b (bind ma k) -> (OOMFails ma \/ exists a : A , OOMReturns a ma /\ OOMReturns b (k a)).
  Proof using.
    intros A B ma k b RET.
    right; apply OOMReturns_strong_bind_inv; auto.
  Qed.

  Lemma OOMReturns_ret :
    forall {A} (a : A) (ma : OOM A),
      eq1 ma (ret a) -> OOMReturns a ma.
  Proof using.
    intros A a ma EQ.
    destruct ma; cbn in *; auto.
  Qed.

  Lemma OOMReturns_ret_inv :
    forall {A} (x y : A),
      OOMReturns x (ret y) -> x = y.
  Proof using.
    intros A x y RET.
    cbn in RET; auto.
  Qed.

  Global Instance OOMReturns_Proper {A} {a : A} : Proper (eq1 ==> Basics.impl) (OOMReturns a).
  Proof using.
    unfold Proper, respectful.
    do 2 red.
    intros x y EQ RET.
    destruct x, y; cbn in *; subst; auto.
    contradiction.
  Qed.

  Global Instance MonadReturnsOOM : @MonadReturns OOM MonadOOM MonadEq1OOM
    := { MReturns := fun A => OOMReturns;
         MFails := fun A => OOMFails;
         MFails_ret := fun A => OOMFails_ret;
         MFails_bind_ma := fun A B => OOMFails_bind_ma;
         MFails_bind_k := fun A B => OOMFails_bind_k;
         MFails_bind_inv := fun A B => OOMFails_bind_inv;
         MReturns_bind := fun A B => OOMReturns_bind;
         MReturns_bind_inv := fun A B => OOMReturns_bind_inv;
         MReturns_ret := fun A => OOMReturns_ret;
         MReturns_ret_inv := fun A => OOMReturns_ret_inv
       }.

  Global Instance MonadReturns_OOM_Fails : MonadReturnsFails OOM
    := { MReturns_MFails := fun A => OOMReturns_OOMFails;
         MFails_MReturns := fun A => OOMFails_OOMReturns
    }.

  Global Instance MonadReturns_OOM_StrongBindInv : MonadReturnsStrongBindInv OOM
    := {  MReturns_strong_bind_inv := fun A B => OOMReturns_strong_bind_inv }.

  Global Instance EQRET_OOM : @Eq1_ret_inv OOM MonadEq1OOM MonadOOM.
  Proof using.
    split.
    intros A x y H.
    cbn in H. auto.
  Qed.
End OOMLaws.

Inductive UB_MESSAGE :=
| UB_message : string -> UB_MESSAGE
.

Inductive ERR_MESSAGE :=
| ERR_message : string -> ERR_MESSAGE
.

Inductive OOM_MESSAGE :=
| OOM_message : string -> OOM_MESSAGE
.

Notation UB := (sum UB_MESSAGE).
Notation ERR := (sum ERR_MESSAGE).

#[global] Instance Exception_UB : MonadExc UB_MESSAGE UB := Exception_either UB_MESSAGE.
#[global] Instance Exception_ERR : MonadExc ERR_MESSAGE ERR := Exception_either ERR_MESSAGE.

Class RAISE_ERROR (M : Type -> Type) : Type :=
  { raise_error : forall {A}, string -> M A }.

Class RAISE_UB (M : Type -> Type) : Type :=
  { raise_ub : forall {A}, string -> M A }.

Class RAISE_OOM (M : Type -> Type) : Type :=
  { raise_oom : forall {A}, string -> M A }.

Definition trywith_error {A} {M} `{Monad M} `{RAISE_ERROR M} (e:string) (o:option A) : M A :=
    match o with
    | Some x => ret x
    | None => raise_error e
    end.

Definition trywith_ub {A} {M} `{Monad M} `{RAISE_UB M} (e:string) (o:option A) : M A :=
    match o with
    | Some x => ret x
    | None => raise_ub e
    end.

Definition trywith_oom {A} {M} `{Monad M} `{RAISE_OOM M} (e:string) (o:option A) : M A :=
    match o with
    | Some x => ret x
    | None => raise_oom e
    end.

Section MFails_Exceptions.
  Context (M : Type -> Type).
  Context {Monad : Monad M}.
  Context {Eq1 : @Eq1 M}.
  Context {MRET : @MonadReturns M Monad Eq1}.
  Context {ERR : RAISE_ERROR M}.
  Context {UB : RAISE_UB M}.
  Context {OOM : RAISE_OOM M}.

  Class MFails_ERROR :=
    { mfails_error : forall {A} s, MFails (@raise_error M ERR A s) }.

  Class MFails_UB :=
    { mfails_ub : forall {A} s, MFails (@raise_ub M UB A s) }.

  Class MFails_OOM :=
    { mfails_oom : forall {A} s, MFails (@raise_oom M OOM A s) }.
End MFails_Exceptions.

#[global] Instance RAISE_ERROR_E_MT {M : Type -> Type} {MT : (Type -> Type) -> Type -> Type} `{MonadT (MT M) M} `{RAISE_ERROR M} : RAISE_ERROR (MT M) :=
  { raise_error := fun A e => lift (raise_error e);
  }.

#[global] Instance RAISE_UB_E_MT {M : Type -> Type} {MT : (Type -> Type) -> Type -> Type} `{MonadT (MT M) M} `{RAISE_UB M} : RAISE_UB (MT M) :=
  { raise_ub := fun A e => lift (raise_ub e);
  }.

#[global] Instance RAISE_OOM_E_MT {M : Type -> Type} {MT : (Type -> Type) -> Type -> Type} `{MonadT (MT M) M} `{RAISE_OOM M} : RAISE_OOM (MT M) :=
  { raise_oom := fun A e => lift (raise_oom e);
  }.

#[global] Instance RAISE_ERROR_MonadExc {M} `{MonadExc ERR_MESSAGE M} : RAISE_ERROR M
  := { raise_error := fun _ msg => MonadExc.raise (ERR_message msg) }.

#[global] Instance RAISE_UB_MonadExc {M} `{MonadExc UB_MESSAGE M} : RAISE_UB M
  := { raise_ub := fun _ msg => MonadExc.raise (UB_message msg) }.

#[global] Instance RAISE_OOM_MonadExc {M} `{MonadExc OOM_MESSAGE M} : RAISE_OOM M
  := { raise_oom := fun _ msg => MonadExc.raise (OOM_message msg) }.

#[global] Instance Exception_UB_string : MonadExc string UB :=
  {| MonadExc.raise := fun _ msg => inl (UB_message msg);
     catch := fun T c h =>
                match c with
                | inl (UB_message msg) => h msg
                | inr _ => c
                end
  |}.

#[global] Instance Exception_ERR_string : MonadExc string ERR :=
  {| MonadExc.raise := fun _ msg => inl (ERR_message msg);
     catch := fun T c h =>
                match c with
                | inl (ERR_message msg) => h msg
                | inr _ => c
                end
  |}.

Definition err_to_ERR {A} (e : err A) : ERR A
  := match e with
     | inl e => inl (ERR_message e)
     | inr x => inr x
     end.

Definition lift_err {M A} `{MonadExc string M} `{Monad M} (e : err A) : (M A)
  := match e with
     | inl e => MonadExc.raise e
     | inr x => ret x
     end.

Definition lift_ERR {M A} `{MonadExc ERR_MESSAGE M} `{Monad M} (e : ERR A) : (M A)
  := match e with
     | inl e => MonadExc.raise e
     | inr x => ret x
     end.

Definition lift_err_RAISE_ERROR {A} {M} `{Monad M} `{RAISE_ERROR M} (e : err A) : M A
  := match e with
     | inl x => raise_error x
     | inr x => ret x
     end.

Definition lift_ERR_RAISE_ERROR {A} {M} `{Monad M} `{RAISE_ERROR M} (e : ERR A) : M A
  := match e with
     | inl (ERR_message x) => raise_error x
     | inr x => ret x
     end.

Definition lift_OOM {M : Type -> Type} `{Monad M} `{RAISE_OOM M} {A} (ma : OOM A) : M A
  := match ma with
     | NoOom a => ret a
     | Oom s => raise_oom s
     end.

Definition lift_err_oom_RAISE_ERROR_OOM
  {A} {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_OOM M}
  (e : err (OOM A)) : M A
  := match e with
     | inl x => raise_error x
     | inr (Oom msg) => raise_oom msg
     | inr (NoOom x) => ret x
     end.

Inductive err_ub_oom_T (m : Type -> Type) (A : Type) : Type
  := ERR_UB_OOM { unERR_UB_OOM : eitherT ERR_MESSAGE (eitherT UB_MESSAGE (eitherT OOM_MESSAGE m)) A }.

Definition err_ub_oom : Type -> Type
  := err_ub_oom_T IdentityMonad.ident.

Arguments ERR_UB_OOM {_ _} _.
Arguments unERR_UB_OOM {_ _} _.

Definition run_err_ub_oom_T {M : Type -> Type} {A} (euo : err_ub_oom_T M A) : M (OOM_MESSAGE + (UB_MESSAGE + (ERR_MESSAGE + A)))%type :=
       match euo with
       | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT x))) =>
           x
       end.

Definition run_err_ub_oom {A} (euo : err_ub_oom A) : (OOM_MESSAGE + (UB_MESSAGE + (ERR_MESSAGE + A)))%type :=
  IdentityMonad.unIdent (run_err_ub_oom_T euo).

#[global] Instance err_ub_oom_T_MT {M : Type -> Type} `{HM: Monad M} : MonadT (err_ub_oom_T M) M.
Proof using.
  constructor.
  intros T mt.
  refine (ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT _)))).
  exact (fmap (fun v => inr (inr (inr v))) mt).
Defined.

Notation OOM_unERR_UB_OOM oom_msg :=
  ({| unERR_UB_OOM :=
     {|
       EitherMonad.unEitherT :=
       {|
         EitherMonad.unEitherT :=
         {|
           EitherMonad.unEitherT := {| IdentityMonad.unIdent := inl (OOM_message oom_msg) |}
         |}
       |}
     |}
   |}).

Notation UB_unERR_UB_OOM ub_msg :=
  ({| unERR_UB_OOM :=
     {|
       EitherMonad.unEitherT :=
       {|
         EitherMonad.unEitherT :=
         {|
           EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inl (UB_message ub_msg)) |}
         |}
       |}
     |}
   |}).

Notation ERR_unERR_UB_OOM err_msg :=
  ({| unERR_UB_OOM :=
     {|
       EitherMonad.unEitherT :=
       {|
         EitherMonad.unEitherT :=
         {|
           EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inl (ERR_message err_msg))) |}
         |}
       |}
     |}
   |}).

Notation success_unERR_UB_OOM v :=
  ({| unERR_UB_OOM :=
     {|
       EitherMonad.unEitherT :=
       {|
         EitherMonad.unEitherT :=
         {|
           EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr v)) |}
         |}
       |}
     |}
   |}).

Import MonadNotation.
Import Utils.Monads.

Section err_ub_oom_monad.
  Variable (M : Type -> Type).
  Context {HM : Monad M}.

  #[global] Instance EqM_err_ub_oom : Monad.Eq1 err_ub_oom.
  Proof using.
    (* refine (fun T mt1 mt2 => _). *)
    (* destruct mt1, mt2. *)
    (* apply (Monad.eq1 unERR_UB_OOM0 unERR_UB_OOM1). *)

    refine (fun T mt1 mt2 => _).

    (* mt2 should be a refinement of mt1 *)
    destruct mt1 as [[[[[[oom_mt1 | [ub_mt1 | [err_mt1 | t1]]]]]]]].
    - (* OOM can only refine to OOM *)
      destruct mt2 as [[[[[[oom_mt2 | [ub_mt2 | [err_mt2 | t2]]]]]]]].
      + exact True.
      + exact False.
      + exact False.
      + exact False.
    - (* UB *)
      exact True.
    - (* Error *)
      exact True.
    - (* Success *)
      destruct mt2 as [[[[[[oom_mt2 | [ub_mt2 | [err_mt2 | t2]]]]]]]].
      + (* OOM refines everything *)
        exact True.
      + exact False.
      + exact False.
      + exact (t1 = t2).
  Defined.

  #[global] Instance Reflexive_err_ub_oom_eq1 {A : Type} : Reflexive (@eq1 err_ub_oom _ A).
  Proof using.
    unfold Reflexive.
    intros x.
    destruct x as [[[[[[[oom_x] | [[ub_x] | [[err_x] | x']]]]]]]] eqn:Hx; cbn; auto.
  Defined.

  #[global] Instance Transitive_err_ub_oom_eq1 {A : Type} : Transitive (@eq1 err_ub_oom _ A).
  Proof using.
    unfold Transitive.
    intros x y z XY YZ.
    destruct x as [[[[[[[oom_x] | [[ub_x] | [[err_x] | x']]]]]]]] eqn:Hx;
      destruct y as [[[[[[[oom_y] | [[ub_y] | [[err_y] | y']]]]]]]] eqn:Hy;
      destruct z as [[[[[[[oom_z] | [[ub_z] | [[err_z] | z']]]]]]]] eqn:Hz;
      cbn in *; subst; auto; try contradiction.
  Defined.

  #[global] Instance Monad_err_ub_oom : Monad (err_ub_oom_T M).
  Proof using HM M.
    split.
    - exact (fun T t => ERR_UB_OOM (ret t)).
    - exact (fun A B ema k =>
               match ema with
               | ERR_UB_OOM ma =>
                   ERR_UB_OOM (bind ma (fun a => unERR_UB_OOM (k a)))
               end).
  Defined.

  #[global] Instance Functor_err_ub_oom : Functor (err_ub_oom_T M).
  Proof using HM M.
    split.
    - exact (fun A B f ema =>
               ERR_UB_OOM (fmap f (unERR_UB_OOM ema))).
  Defined.
End err_ub_oom_monad.

Section err_ub_oom_extra.
  #[global] Instance MonadLawsE_err_ub_oom : MonadLawsE err_ub_oom.
  Proof using.
    split.
    - intros A B f x.
      cbn.
      destruct (f x) as [[[[[[oom_fx | [ub_fx | [err_fx | fx]]]]]]]]; cbn; auto.
    - intros A x.
      destruct x as [[[[[[oom_x | [ub_x | [err_x | x]]]]]]]]; cbn; auto.
    - intros A B C x f g.
      cbn.
      destruct x as [[[[[[oom_x | [ub_x | [err_x | x]]]]]]]]; cbn; auto.
      destruct (f x) as [[[[[[oom_fx | [ub_fx | [err_fx | fx]]]]]]]]; cbn; auto.
      destruct (g fx) as [[[[[[oom_gfx | [ub_gfx | [err_gfx | gfx]]]]]]]]; cbn; auto.
    - intros A B.
      unfold Proper, respectful.
      intros x y H x0 y0 H0.

      destruct x as [[[[[[[oom_x] | [[ub_x] | [[err_x] | x]]]]]]]]; cbn; auto.
      destruct y as [[[[[[[oom_y] | [[ub_y] | [[err_y] | y]]]]]]]]; cbn; auto; inversion H.
      destruct y as [[[[[[[oom_y] | [[ub_y] | [[err_y] | y]]]]]]]]; cbn; auto; inversion H.

      destruct (unEitherT (unEitherT (unEitherT (unERR_UB_OOM (x0 x)))));
      destruct unIdent; auto; destruct s; auto; destruct s; auto.

      subst.

      destruct (x0 y) as [[[[[[oom_x0y | [ub_x0y | [err_x0y | x0y]]]]]]]] eqn:Hx0y; cbn; auto;
        unfold pointwise_relation in H0;
        specialize (H0 y);

        unfold EqM_err_ub_oom in *;
        cbn in *;

        unfold eq1 in H0;
        rewrite Hx0y in H0;

        destruct (y0 y) as [[[[[[oom_y0y | [ub_y0y | [err_y0y | y0y]]]]]]]]; cbn; auto.
  Defined.


  #[global] Instance RAISE_ERROR_err_ub_oom {M : Type -> Type} `{Monad M} : RAISE_ERROR (err_ub_oom_T M)
    := { raise_error := fun _ msg => ERR_UB_OOM (raise_error msg) }.

  #[global] Instance RAISE_UB_err_ub_oom_T {M : Type -> Type} `{Monad M} : RAISE_UB (err_ub_oom_T M)
    := { raise_ub := fun _ msg => ERR_UB_OOM (raise_ub msg) }.

  #[global] Instance RAISE_OOM_err_ub_oom_T {M : Type -> Type} `{Monad M} : RAISE_OOM (err_ub_oom_T M)
    := { raise_oom := fun _ msg => ERR_UB_OOM (raise_oom msg) }.

  Lemma unERR_UB_OOM_bind :
    forall {A B} (ma : err_ub_oom A) (k : A -> err_ub_oom B),
      Monad.eq1 (unERR_UB_OOM (x <- ma;; k x)) (x <- unERR_UB_OOM ma;; (unERR_UB_OOM (k x))).
  Proof using.
    intros A B ma k.
    cbn.
    destruct ma as [[[[[[oom_ma | [ub_ma | [err_ma | ma]]]]]]]]; cbn; reflexivity.
  Qed.

  Section MonadReturns.
    Definition ErrUBOOMReturns {A} (a : A) (ma : err_ub_oom A) : Prop
      := match ma with
         | ERR_UB_OOM ea =>
             match IdentityMonad.unIdent (unEitherT (unEitherT (unEitherT ea))) with
             | inl (OOM_message msg) => False
             | inr (inl (UB_message msg)) => True
             | inr (inr (inl (ERR_message msg))) => True
             | inr (inr (inr a')) => a' = a
             end
         end.

    Definition ErrUBOOMFails {A} (ma : err_ub_oom A) : Prop
      := match ma with
         | ERR_UB_OOM ea =>
             match IdentityMonad.unIdent (unEitherT (unEitherT (unEitherT ea))) with
             | inl (OOM_message msg) => True
             | inr (inl (UB_message msg)) => True
             | inr (inr (inl (ERR_message msg))) => True
             | inr (inr (inr a')) => False
             end
         end.

    Lemma ErrUBOOMFails_ret : forall {A} (a : A),
        ~ ErrUBOOMFails (ret a).
    Proof using.
      intros A a CONTRA.
      inversion CONTRA.
    Qed.

    Lemma ErrUBOOMFails_bind_ma : forall {A B} (ma : err_ub_oom A) (k : A -> err_ub_oom B),
        ErrUBOOMFails ma -> ErrUBOOMFails (bind ma k).
    Proof using.
      intros A B ma k FAILS.
      destruct ma as [[[[[[[oom_ma] | [[ub_ma] | [[err_ma] | a]]]]]]]] eqn:Hma;
        cbn in *; auto; contradiction.
    Qed.

    Lemma ErrUBOOMFails_bind_k : forall {A B} (ma : err_ub_oom A) (a : A) (k : A -> err_ub_oom B),
        ErrUBOOMReturns a ma ->
        ErrUBOOMFails (k a) ->
        ErrUBOOMFails (bind ma k).
    Proof using.
      intros A B ma a k RETS FAILS.
      destruct ma as [[[[[[[oom_ma] | [[ub_ma] | [[err_ma] | a']]]]]]]] eqn:Hma;
        cbn in *; auto; subst.
      destruct (k a) as [[[[[[[oom_ka] | [[ub_ka] | [[err_ka] | ka]]]]]]]] eqn:Hka;
        cbn in *; auto.
    Qed.

    Lemma ErrUBOOMFails_bind_inv : forall {A B} (ma : err_ub_oom A) (k : A -> err_ub_oom B),
        ErrUBOOMFails (bind ma k) ->
        ErrUBOOMFails ma \/ (exists a, ErrUBOOMReturns a ma /\ ErrUBOOMFails (k a)).
    Proof using.
      intros A B ma k FAILS.
      destruct ma as [[[[[[[oom_ma] | [[ub_ma] | [[err_ma] | a']]]]]]]] eqn:Hma;
        cbn in *; auto; subst.
      destruct (k a') as [[[[[[[oom_ka'] | [[ub_ka'] | [[err_ka'] | ka']]]]]]]] eqn:Hka';
        cbn in *; auto; right; eexists; split; try rewrite Hka'; eauto.
    Qed.

    Lemma ErrUBOOMReturns_bind :
      forall {A B} (a : A) (b : B) (ma : err_ub_oom A) (k : A -> err_ub_oom B),
        ErrUBOOMReturns a ma -> ErrUBOOMReturns b (k a) -> ErrUBOOMReturns b (bind ma k).
    Proof using.
      intros * Ha Hb.
      unfold ErrUBOOMReturns in *.
      destruct ma as [[[[[[[oom_ma] | [[ub_ma] | [[err_ma] | ma]]]]]]]]; cbn in *; try solve [inversion Ha]; auto.
      subst.
      destruct (k a); auto.
    Qed.

    Lemma ErrUBOOMReturns_bind_inv :
      forall {A B} (ma : err_ub_oom A) (k : A -> err_ub_oom B) (b : B),
        ErrUBOOMReturns b (bind ma k) -> (ErrUBOOMFails ma \/ exists a : A , ErrUBOOMReturns a ma /\ ErrUBOOMReturns b (k a)).
    Proof using.
      intros * Hb.
      unfold ErrUBOOMReturns in *.
      destruct ma as [[[[[[[oom_ma] | [[ub_ma] | [[err_ma] | a]]]]]]]];
        cbn in *; try solve [inversion Hb]; auto.
      right.

      exists a.
      split; auto.

      destruct (k a) as [[[[[[[oom_ka] | [[ub_ka] | [[err_ka] | ka]]]]]]]] eqn:Hk;
        inversion Hb; cbn in *; subst; auto.
    Qed.

    Lemma ErrUBOOMReturns_ret :
      forall {A} (a : A) (ma : err_ub_oom A),
        Monad.eq1 ma (ret a) -> ErrUBOOMReturns a ma.
    Proof using.
      intros * Hma.
      destruct ma as [[[[[[[oom_ma] | [[ub_ma] | [[err_ma] | ma]]]]]]]];
        cbn in *; auto; try contradiction.
    Qed.

    Lemma ErrUBOOMReturns_ret_inv :
      forall {A} (x y : A),
        ErrUBOOMReturns x (ret y) -> x = y.
    Proof using.
      intros * H.
      unfold ErrUBOOMReturns in H.
      inversion H; auto.
    Qed.

    #[global] Instance MonadReturns_ErrUBOOM : MonadReturns err_ub_oom
      := { MReturns := fun A => ErrUBOOMReturns;
           MFails := fun A => ErrUBOOMFails;
           MFails_ret := fun A => ErrUBOOMFails_ret;
           MFails_bind_ma := fun A B => ErrUBOOMFails_bind_ma;
           MFails_bind_k := fun A B => ErrUBOOMFails_bind_k;
           MFails_bind_inv := fun A B => ErrUBOOMFails_bind_inv;
           MReturns_bind := fun A B => ErrUBOOMReturns_bind;
           MReturns_bind_inv := fun A B => ErrUBOOMReturns_bind_inv;
           MReturns_ret := fun A => ErrUBOOMReturns_ret;
           MReturns_ret_inv := fun A => ErrUBOOMReturns_ret_inv
      }.

  End MonadReturns.

  Definition err_to_err_ub_oom {A} (e : err A) : err_ub_oom A
    := match e with
       | inr a => ret a
       | inl e => raise_error e
       end.
End err_ub_oom_extra.

Ltac inv_err_ub_oom :=
  match goal with
  | h: {| unERR_UB_OOM := {| unEitherT := {| unEitherT := {| unEitherT := {| IdentityMonad.unIdent := inl _ |} |} |} |} |}
       = {| unERR_UB_OOM := {| unEitherT := {| unEitherT := {| unEitherT := {| IdentityMonad.unIdent := inl _ |} |} |} |} |} |- _ =>
      inv h
  | h: {| unERR_UB_OOM := {| unEitherT := {| unEitherT := {| unEitherT := {| IdentityMonad.unIdent := inr _ |} |} |} |} |}
       = {| unERR_UB_OOM := {| unEitherT := {| unEitherT := {| unEitherT := {| IdentityMonad.unIdent := inr _ |} |} |} |} |} |- _ =>
      inv h
  | h: {| unERR_UB_OOM := {| unEitherT := {| unEitherT := {| unEitherT := {| IdentityMonad.unIdent := inl _ |} |} |} |} |}
       = {| unERR_UB_OOM := {| unEitherT := {| unEitherT := {| unEitherT := {| IdentityMonad.unIdent := inr _ |} |} |} |} |} |- _ =>
      inv h
  | h: {| unERR_UB_OOM := {| unEitherT := {| unEitherT := {| unEitherT := {| IdentityMonad.unIdent := inr _ |} |} |} |} |}
       = {| unERR_UB_OOM := {| unEitherT := {| unEitherT := {| unEitherT := {| IdentityMonad.unIdent := inl _ |} |} |} |} |} |- _ =>
      inv h
  end.

(*
-Ltac inv_err_or_ub :=
-  match goal with
-  | h: {| unERR_OR_UB := {| unEitherT := inl _ |} |} =
-       {| unERR_OR_UB := {| unEitherT := inl _ |} |} |- _ => inv h
-  | h: {| unERR_OR_UB := {| unEitherT := inr _ |} |} =
-       {| unERR_OR_UB := {| unEitherT := inr _ |} |} |- _ => inv h
-  | h: {| unERR_OR_UB := {| unEitherT := inr _ |} |} =
-       {| unERR_OR_UB := {| unEitherT := inl _ |} |} |- _ => inv h
-  | h: {| unERR_OR_UB := {| unEitherT := inl _ |} |} =
-       {| unERR_OR_UB := {| unEitherT := inr _ |} |} |- _ => inv h
-  end.
*)
