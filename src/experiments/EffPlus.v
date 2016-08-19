Require Import Arith List Util.

Import ListNotations.


Module Type EFF_SYNTAX_PARAMS.

  Parameter vty : Set.                    (* value types *)
  Parameter etc : Set.                    (* effect type constructors *)

  Parameter pri : Set.                    (* value con/destructors *)
  Parameter hnd : Set.                    (* handler constructors *)
  Parameter eff : Set.                    (* effect constructors *)

End EFF_SYNTAX_PARAMS.


Module Eff_Base(Import ES:EFF_SYNTAX_PARAMS).

  Inductive sym : Set := Sym :> nat -> sym.

  Inductive exp : Set :=                  (* expressions *)
  | Var : nat -> exp                      (* variables *)
  | Pri : pri -> list exp -> exp          (* primitives *)
  | App : list exp -> exp -> exp          (* application *)
  | Abs : exp -> exp                      (* abstraction *)
  | Seq : exp -> exp -> exp               (* sequencing, let *)
  | Eff : sym -> eff -> list exp -> exp   (* effects *)
  | Hnd : hnd -> list exp -> exp -> exp.  (* handlers *)

  Parameter substitute : list exp -> exp -> exp.

  Inductive rty : Set := 
  | Nil : rty                             (* closed computation *)
  | Cmp : vty -> rty.                     (* computation returning vty *)

  Inductive cty : Set :=                  (* computation types *)
  | Rty :> rty -> cty                     (* non-arrow *)
  | Arr : list vty -> rty -> cty.         (* arrow *)

  Inductive ty : Set :=
  | Cty :> cty -> ty
  | Vty :> vty -> ty.

  Inductive ety : Set :=                  
  | Ety : etc -> list ty -> ety.          (* effect types *)

  Definition env : Set := list vty.
  Definition sig : Set := list ety.

  Module Type EFF_TYP_SEM_PARAMS.
    
    Axiom val_sig : val -> vty -> Prop.
    Axiom pri_sig : pri -> list ty -> cty -> Prop.
    Axiom eff_sig : eff -> list vty -> ety -> (list vty * rty) -> Prop.
    Axiom hnd_sig : hnd -> sig -> list sig -> list ty -> ety -> Prop.

    Parameter eval_cmp : (list val * pri * list exp) -> val -> Prop.
    Parameter eval_nil : (list val * pri * list exp) -> exp -> Prop.
    Parameter react_cmp : (hnd * list exp) -> (eff * list exp * exp) -> exp -> Prop.
    Parameter react_nil : (hnd * list exp) -> (eff * list exp) -> exp -> Prop.

  End EFF_TYP_SEM_PARAMS.

  Module Eff_Typ_Sem (Import ET:EFF_TYP_SEM_PARAMS).

    Inductive wt_exp (G:env) (E:sig) : exp -> ty -> Prop :=

    | wt_var : forall x T,
      nth_error G x = Some T ->
      wt_exp G E (Var x) T

    | wt_val : forall v T,
      val_sig v T ->
      wt_exp G E (Val v) T

    | wt_pri : forall p param pts tr,
      pri_sig p pts tr ->
      Forall2 (wt_exp G E) param pts ->
      wt_exp G E (Pri p param) tr

    | wt_app : forall vts tr vs e,
      Forall2 (wt_exp G E) vs (map Vty vts) ->
      wt_exp G E e (Arr vts tr) ->
      wt_exp G E (App vs e) (Cty tr)

    | wt_abs : forall T A e,
      wt_exp (T::G) E e A ->
      wt_exp G E (Abs e) A

    | wt_seq : forall T e k,
      wt_exp G E e (Cmp T) ->
      wt_exp (T::G) E k Nil ->
      wt_exp G E (Seq e k) Nil

    | wt_eff : forall F s f vs pts vts rt,
      eff_sig f pts F (vts, rt) ->
      nth_error E s = Some F ->
      Forall2 (wt_exp G E) vs (map Vty vts) ->
      wt_exp G E (Eff s f vs) (Arr vts rt)

    | wt_hnd : forall F Es h param k pts,
      hnd_sig h E Es pts F ->
      Forall3 (wt_exp G) Es param pts ->
      wt_exp G (F::E) k Nil ->
      wt_exp G E (Hnd h param k) Nil.


    Parameter proj_val : list exp -> option (list val).

    Inductive step : exp -> exp -> Prop :=

    | step_app_cons : forall v vs k,
      step (App (Val v::vs) (Abs k))
           (App vs (substitute [v] k))

    | step_app_nil : forall k,
      step (App [] k) k

    | step_delta_cmp : forall es vs p ps v k,
      proj_val es = Some vs ->
      eval_cmp (vs, p, ps) v ->
      step (Seq (App es (Pri p ps)) k)
           (substitute [v] k)

    | step_delta_nil : forall es vs p ps e,
      proj_val es = Some vs ->
      eval_nil (vs, p, ps) e ->
      step (App es (Pri p ps)) e

    | step_hoist_cmp : forall h hps fps es s f k,
      step (Hnd h hps (Seq (App es (Eff (S s) f fps)) k))
           (Seq (App es (Eff s f fps)) (Hnd h hps k))
      
    | step_hoist_nil : forall h hps fps es s f,
      step (Hnd h hps (App es (Eff (S s) f fps)))
           (App es (Eff s f fps))

    | step_react_cmp : forall h hps fps es f e k,
      react_cmp (h, hps) (f, fps, k) e ->
      step (Hnd h hps (Seq (App es (Eff O f fps)) k)) e
           
    | step_react_nil : forall h hps fps es f e,
      react_nil (h, hps) (f, fps) e ->
      step (Hnd h hps (App es (Eff O f fps))) e.

    Module Eff_Props.

      Inductive nf : exp -> Prop :=
      | nf_cmp : forall vs s f ps k, nf (Seq (App vs (Eff s f ps)) k)
      | nf_nil : forall vs s f ps, nf (App vs (Eff s f ps)).

      Lemma step_progress : forall E e,
        wt_exp [] E e Nil ->
        nf e \/ exists e', step e e'.
      Proof.
        remember [] as G. remember (Cty Nil) as T. 
        induction 1; subst G.

        (* var *) destruct x; inversion H.
        (* val *) inversion HeqT.
        (* pri *) right; eexists. eapply step_delta_nil.

      Abort.

      Lemma step_preservation : forall E e e',
        step e e' ->
        wt_exp [] E e Nil ->
        wt_exp [] E e' Nil.
      Proof.
      Abort.


    End Eff_Props.

  End Eff_Typ_Sem.

End Eff_Base.