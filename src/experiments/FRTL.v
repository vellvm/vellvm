Require Import AST.
Require Import Events.
Require Import Globalenvs.
Require Import Integers.
Require Import Memory.
Require Import Op.
Require Import Smallstep.
Require Import Values.

Require Import Registers.
Require Import RTL.

Require Import Arith.
Require Import List.
Import ListNotations.

Definition Nth {A:Type} (l:list A) (n:nat) (a:A) : Prop := nth_error l n = Some a.

Definition genv := Genv.t unit unit.
Definition empty_genv : genv := Genv.empty_genv _ _.

(* to avoid having two notions of substitution, single syntactic category *)
Inductive fid := Fid : nat -> fid.

Inductive vid := Vid : nat -> vid.
Scheme Equality for vid.

Definition proj_vid (v:vid) : nat := let (n) := v in n.

Module ANF.

Inductive tm : Type :=
  | Ret: vid -> tm
  | App: fid -> list vid -> tm
  | Pri: operation -> list vid -> tm -> tm
  | Rec: tm -> tm -> tm
  | Cnd: vid -> tm -> tm -> tm.


Inductive eval (E:list val) (D:list (list val * tm)) : tm -> val -> Prop :=

| eval_ret : forall x v,
    Nth E x v ->
    eval E D (Ret (Vid x)) v

| eval_app : forall f vs E' k args v,
    Nth D f (E', k) ->
    Forall2 (Nth E) (map proj_vid args) vs -> 
    eval (vs ++ E') D k v ->
    eval E D (App (Fid f) args) v

| eval_pri : forall t op vs args v,
    Forall2 (Nth E) (map proj_vid args) vs ->
    eval_operation empty_genv Vzero op vs Mem.empty = Some v ->
    eval E D (Pri op args t) v

| eval_rec : forall k t v,
    eval E ((E,k)::D) t v ->
    eval E D (Rec k t) v

| eval_cnd : forall x g b tt ft v,
    Nth E x g ->
    Val.bool_of_val g b ->
    eval E D (if b then tt else ft) v ->
    eval E D (Cnd (Vid x) tt ft) v.

End ANF.


Module MRTL.

Inductive tm : Type :=
  | Ret: reg -> tm
  | Jmp: fid -> tm
  | Mov: reg -> reg -> tm -> tm
  | Pri: operation -> list reg -> reg -> tm -> tm
  | Rec: tm -> tm -> tm
  | Cnd: reg -> tm -> tm -> tm.

Inductive eval (E:regset) (D:list tm) : tm -> val -> Prop :=
  
| eval_ret : forall r v,
    E#r = v ->
    eval E D (Ret r) v

| eval_jmp : forall f t v,
    Nth D f t ->
    eval E D t v ->
    eval E D (Jmp (Fid f)) v

| eval_mov : forall r d t v,
    E#r = v ->
    eval (E#d <- v) D t v ->
    eval E D (Mov r d t) v

| eval_pri : forall d t op args u v,
    eval_operation empty_genv Vzero op (E##args) Mem.empty = Some u ->
    eval (E#d <- u) D t v ->
    eval E D (Pri op args d t) v

| eval_rec : forall k t v,
    eval E (k::D) t v ->
    eval E D (Rec k t) v

| eval_cnd : forall r b tt ft g v,
    E#r = g ->
    Val.bool_of_val g b ->
    eval E D (if b then tt else ft) v ->
    eval E D (Cnd r tt ft) v.

End MRTL.

Definition replacen {A} (n:nat) (l:list A) (a:A) :=
  firstn n l ++ a :: skipn (S n) l.

Eval compute in replacen 3 [1; 2; 3] 9.

Definition venv := list (list reg).

Definition venv_tr (G:venv) (x:vid) (r:reg) : Prop := 
  let '(Vid n) := x in In r (nth n G []).
Definition venv_free (G:venv) (r:reg) : Prop := ~ exists x, venv_tr G x r.
Definition venv_le (G G':venv) : Prop := forall x r, venv_tr G x r -> venv_tr G' x r.
Definition venv_extend (G:venv) (x:vid) (r:reg) : venv :=
  let '(Vid n) := x in replacen n G (r::nth n G []).

Definition fenv := list (venv * list reg).

Definition singleton {A} (a:A) := [a].

Inductive tr_tm (G:venv) (D:fenv) : ANF.tm -> MRTL.tm -> Prop :=

| tr_ret : forall x r,
    venv_tr G x r ->
    tr_tm G D (ANF.Ret x) (MRTL.Ret r)

| tr_pri : forall d op args rs t t',
    Forall2 (venv_tr G) args rs ->
    venv_free G d ->
    tr_tm ([d]::G) D t t' ->
    tr_tm G D (ANF.Pri op args t) (MRTL.Pri op rs d t')

| tr_cnd : forall x r tt ft tt' ft',
    venv_tr G x r ->
    tr_tm G D tt tt' ->
    tr_tm G D ft ft' ->
    tr_tm G D (ANF.Cnd x tt ft) (MRTL.Cnd r tt' ft')

| tr_rec : forall G' rs k k' t t',
    venv_le G' G ->
    Forall (venv_free G') rs ->
    tr_tm (map singleton rs ++ G') ((G',rs)::D) k k' ->
    tr_tm G ((G', rs)::D) t t' ->
    tr_tm G D (ANF.Rec k t) (MRTL.Rec k' t')

| tr_app : forall G' f rs args,
    Nth D f (G',rs) ->
    Forall2 (venv_tr G) args rs ->
    tr_tm G D (ANF.App (Fid f) args) (MRTL.Jmp (Fid f))

| tr_weaken : forall G' t t',
    venv_le G' G ->
    tr_tm G' D t t' ->
    tr_tm G D t t'

| tr_phi : forall x q r t t',
    venv_tr G x q ->
    venv_free G r ->
    tr_tm (venv_extend G x r) D t t'->
    tr_tm G D t (MRTL.Mov q r t').






Inductive tr_val (G:list (list reg)) : vid -> reg -> Prop :=
  tr_val_intro : forall x r rs,
    Nth G x rs ->
    In r rs ->
    tr_val G (Vid x) r.

Definition reg_free (G:list (list reg)) (r:reg) : Prop :=
  ~ exists x, tr_val G x r.

Definition le_env (G G':list (list reg)) : Prop :=
  forall x r, tr_val G x r -> tr_val G' x r.

Fixpoint env_extend' (G:list (list reg)) (n:nat) (r:reg) : option (list (list reg)) :=
  match G, n with 
    | rs::G', O => Some ((r::rs)::G')
    | rs::G', S n' => match env_extend' G' n' r with
                        | Some G'' => Some (rs :: G'')
                        | None => None
                      end
    | _, _ => None
  end.

Inductive env_extend : (list (list reg)) -> vid -> reg -> (list (list reg)) -> Prop :=
  env_extend_intro : forall G n r G',
    env_extend' G n r = Some G' ->
    env_extend G (Vid n) r G'.


Definition singleton {A} (a:A) : list A := [a].

Notation venv := (list (list reg)).
Notation kenv := (list (list reg * venv * node)).

Inductive tr_tm (G:venv) (D:list (list reg * node)) : tm -> (code * node) -> Prop :=

| tr_ret : forall C x r n,
    tr_val G x r ->
    C!n = Some (Ireturn (Some r)) ->
    tr_tm G D (Ret x) (C, n)

| tr_app : forall C f rs args n,
    Nth D f (rs, n) ->
    Forall2 (tr_val G) args rs ->
    tr_tm G D (App (Fid f) args) (C, n)

| tr_mov : forall C n n' q r x t,
    tr_val G x q ->
    C!n = Some (Iop Omove [q] r n') ->
    reg_free G r ->
    tr_tm ([r]::G) D t (C, n') ->
    tr_tm G D (Mov x t) (C, n)

| tr_pri : forall C r rs t n n' op args,
    Forall2 (tr_val G) args rs ->
    C!n = Some (Iop op rs r n') ->
    reg_free G r ->
    tr_tm ([r]::G) D t (C, n') ->
    tr_tm G D (Pri op args t) (C, n)

| tr_rec : forall C rs m n k t narg,
    tr_tm (map singleton rs ++ G) ((rs,m)::D) k (C, m) ->
    tr_tm G ((rs,m)::D) t (C, n) ->
    tr_tm G D (Rec narg k t) (C, n)

| tr_cnd : forall C x r n tn fn tt ft,
    tr_val G x r ->
    C!n = Some (Icond (Ccompimm Cne Int.zero) [r] tn fn) ->
    tr_tm G D tt (C, tn) ->
    tr_tm G D ft (C, fn) ->
    tr_tm G D (Cnd x tt ft) (C, n)

| tr_weaken : forall C G' t n,
    le_env G' G ->
    tr_tm G' D t (C, n) ->
    tr_tm G D t (C, n)

| tr_phi : forall C G' x q r t n n',
    tr_val G x q ->
    C!n = Some (Iop Omove [q] r n') ->
    reg_free G r ->
    env_extend G x r G' ->
    tr_tm G' D t (C, n') ->
    tr_tm G D t (C, n).

Section CORRECTNESS.

(* Definition local_related' (G:list (list reg)) (vs:list val) (rs:regset) : Prop := *)
(*   Forall2 (fun v rr=> Forall (eq v) rs##rr) vs G. *)

(* Definition locals_related'' (G:list (list reg)) (vs:list val) (rs:regset) : Prop := *)
(*   Forall2 (fun v => Forall (fun r => v = rs#r)) vs G. *)

Definition locals_related (G:list (list reg)) (vs:list val) (rs:regset) : Prop :=
  forall x r, tr_val G (Vid x) r -> nth x vs Vundef = rs#r.

Definition conts_related (D:list (list reg * node)) (ks:list tm) (C:code) : Prop :=
  forall f rs n, Nth D f (rs, n) -> 

Lemma tr_correct :
  eval [] [] stm (Vint n) <->
    State [] fmain Vzero pc rs Mem.empty


Variable tcode : RTL.code.
Variable tentry : node.
Variable stm : tm.

Hypothesis Htr_tm : tr_tm [] [] stm (tcode, tentry).

Open Scope positive_scope.

Let tprog : RTL.program :=
  mkprogram [(1, Gfun (Internal (RTL.mkfunction signature_main [] 0 tcode tentry)))] 1.

Let rsem := RTL.semantics tprog.

Let fmain : RTL.function :=
  RTL.mkfunction signature_main [] 0 tcode tentry.



Theorem tr_correct : forall n, 
  eval [] [] stm (Vint n) <-> 
    forall i, Smallstep.initial_state rsem i -> 
      exists f, Star rsem i E0 f /\ Smallstep.final_state rsem f n.
Proof.
  split.
  - intros. inversion Htr_tm; subst.
    + eexists. split. eapply star_step. 
    inversion H0; subst.
    eapply exec_function_internal.

  - admit.
Qed.

Inductive tr_tm (G:list reg) (D:list (list reg * node)) : tm -> (code * node) -> Prop :=

| tr_ret : forall C x r n,
    Nth G x r ->
    C!n = Some (Ireturn (Some r)) ->
    tr_tm G D (Ret (Vid x)) (C, n)

| tr_app : forall C f rs args n,
    Nth D f (rs, n) ->
    Forall2 (Nth G) (map proj_vid args) rs ->
    tr_tm G D (App (Fid f) args) (C, n)

| tr_mov : forall C n n' q r x t,
    Nth G x q ->
    C!n = Some (Iop Omove [q] r n') ->
    ~ In r G ->
    tr_tm (r::G) D t (C, n') ->
    tr_tm G D (Mov (Vid x) t) (C, n)

| tr_pri : forall C r rs t n n' op args,
    C!n = Some (Iop op rs r n') ->
    Forall2 (Nth G) (map proj_vid args) rs ->
    ~ In r G ->
    tr_tm (r::G) D t (C, n') ->
    tr_tm G D (Pri op args t) (C, n)

| tr_rec : forall C rs m n k t narg,
    tr_tm (rs ++ G) ((rs,m)::D) k (C, m) ->
    tr_tm G ((rs,m)::D) t (C, n) ->
    tr_tm G D (Rec narg k t) (C, n)

| tr_cnd : forall C x r n tn fn tt ft,
    Nth G x r ->
    C!n = Some (Icond (Ccompimm Cne Int.zero) [r] tn fn) ->
    tr_tm G D tt (C, tn) ->
    tr_tm G D ft (C, fn) ->
    tr_tm G D (Cnd (Vid x) tt ft) (C, n).

| tr_arg :
    Nth G' 
    C!n = Some (Iop Omove [q] r n') ->
    ~ In r G
    tr_tm G D t (C, n') ->
    tr_tm G D t (C, n)


Inductive step (G:genv): tm -> trace -> tm -> Prop :=

| exec_opr: forall op args p vs,
    proj_args args = Some vs ->
    eval_operation empty_genv Vzero op vs Mem.empty = Some p ->
    step G (Opr op args) E0 (Ret (Val p))

| exec_cnd: forall g tc fc b,
    Val.bool_of_val g b ->
    step G (Cnd (Val g) tc fc) E0 (if b then tc else fc)

| exec_seq_1: forall c c' d E,
    step G c E c' ->
    step G (Seq c d) E (Seq c' d)

| exec_seq_2: forall v c,
    step G (Seq (Ret v) c) E0 (substitute v c)

| exec_app: forall v c,
    step G (App v (Abs c)) E0 (substitute v c)

| exec_lbl: forall c d,
    step G (Lbl c d) E0 (substitute d c).


Definition initial_state : tm -> tm -> Prop := eq.

Inductive final_state : tm -> int -> Prop :=
| final_state_intro: forall r,
    final_state (Ret (Val (Vint r))) r.

Definition semantics (p: tm) :=
  Semantics step (initial_state p) final_state empty_genv.

(* Require Import Ordered. *)
(* Require FMapAVL. *)
(* Module Regmap := FMapAVL.Make(OrderedPositive). *)
(* Print Module Type Regmap. *)
(* Print Module Type Regset. *)


(**
  The specification of a correct translation to RTL can be given in terms of a
  type derivation including Top. Top indicates that a variable is never used and
  allows the corresponding RTL register to be reused in the continuation.
  The translation itself includes a parameter mapping de bruijn indices to the 
  associated register (just a list env?). Adding a binding is legal as long as
  the rest of the bindings associated with that register have type Top (and will
  not be used for the remainder of the computation).

  Is this related to Beringer's type system for register allocation?
*)

Require Import Registers.
Require Import RTL.
Require Import Maps.



(* the translation should be type-directed. We need to know when we have a 
   continuation vs expr vs operand
*)

(* Inductive tr_val (G: list reg) : val -> reg -> Prop := *)
(* | tr_val_var : forall x r, *)
(*   nth G x = Some r -> *)
(*   tr_val G (Var x) r. *)

(* RTL doesn't have immediate operands -> constants bound through redundant seq/ret *)
(* actually, source shouldn't have use of Pri at all -- translate to const opr *)

(* cfg fragments *)
Inductive cfg : Type := Cfg : code -> node -> node -> list reg -> reg -> cfg.

Inductive tr_cmp (G:list reg) : cmp -> cfg -> Prop :=
| tr_opr : forall C n n' op rs r vs,
  C!n = Some (Iop op rs r n') ->
  Forall2 (tr_val G) vs rs ->
  tr_cmp G (Opr op vs) (Cfg C n n' [] r)

| tr_cnd : forall C g r n nt nf nj vg cf ct,
  C!n = Some (Icond (Ccompimm Cne Int.zero) [g] nt nf) ->
  tr_cmp G ct (Cfg C nt nj [] r) ->
  tr_cmp G cf (Cfg C nf nj [] r) ->
  tr_val G vg g ->
  tr_cmp G (Cnd vg ct cf) (Cfg C n nj [] r)
  
| tr_seq : forall C q r n n' n'' c d,
  ~ In q G ->
  tr_cmp G c (Cfg C n n' [] q) ->
  tr_cmp (q::G) d (Cfg C n' n'' [] r) ->
  tr_cmp G (Seq c d) (Cfg C n n'' [] r)

| tr_ret : forall C n v r,
  tr_val G v r ->
  tr_cmp G (Ret v) (Cfg C n n [] r)

| tr_app : forall C p q r m n n' v c,
  tr_val G v q ->
  C!m = Some (Iop Omove [q] p n) ->
  tr_cmp G c (Cfg C n n' [p] r) ->
  tr_cmp G (App v c) (Cfg C m n' [] r)

| tr_abs : forall C q r n n' c,
  ~ In q G ->
  tr_cmp (q::G) c (Cfg C n n' [] r) ->
  tr_cmp G (Abs c) (Cfg C n n' [q] r).

| tr_lbl :
  tr_cmp G (Lbl c d) (Cfg C n n' [] 

| tr_jmp :

Eval compute in Regset.max_elt Regset.empty.

Require Import PArith.

Open Scope positive.

Definition next_reg (r:Regset.t) : positive :=
  match Regset.max_elt r with
    | Some p => p + 1
    | None => 1
  end.

Eval compute in Regset.remove 1 (Regset.add 1 (Regset.empty)).