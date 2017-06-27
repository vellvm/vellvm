(* QuickChick dependencies *)
Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.

Require Import ZArith.

(* CompCert dependencies *)
Require Import compcert.lib.Integers.

(* Vellvm dependencies *)
Require Import Vellvm.Ollvm_ast Vellvm.Compiler Vellvm.AstLib Vellvm.CFG Vellvm.StepSemantics Vellvm.Memory.
Require Import Vellvm.Classes.
Require Import Vellvm.AstLib.
Require Import Vellvm.DecidableEquality.

(* Source and Target QuickChick dependencies *)
Require Import Vellvm.ImpQuickChick.
Require Import Vellvm.OllvmQuickChick.
Require Import Vellvm.MemoryQuickChick.

(* Logical Foundations dependencies *)
Require Import Vellvm.Imp Vellvm.Maps Vellvm.ImpCEvalFun.
Open Scope list_scope.
Require Import Program.

(* Verification File *)
Require Import Vellvm.ImpCorrectness.


(* Derive ArbitrarySizedSuchThat for (fun a : aexp => aevalR test_state a n). *)

Fixpoint is_prefix_of {A : Type} `{eq_dec A} (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], _ => true
  | (x :: xs), (y :: ys) =>
    if decide (x = y) then
      is_prefix_of xs ys else
      false
  | _, _ => false
  end.

Definition compile_aexp_monotonic_aux
           (g : ctxt) (a : aexp) (n m : int) (code: list elt)
  :=
    let '((n', m', code'), v_opt) := compile_aexp g a (n,m,code) in
    match v_opt with
    | inl err => false
    | inr v' => andb (andb (Z.leb n n') (Z.leb m m'))
                    (is_prefix_of (List.rev code) (List.rev code'))
    end.

Definition test_compile_aexp_monotonic (a : aexp) (n m : int) :=
  let fvs := IDSet.elements (fv a) in
  let g := compile_fv fvs in (* using this as initial context and code for now *)
  let '((n', m', c), new_context_opt) := g (n, m, [])%Z in
  match new_context_opt with
  | inl e => whenFail "Compilation of free variables failed" false
  | inr new_context =>   
    checker (compile_aexp_monotonic_aux new_context a n' m' c)
  end.


(*! Section TestCompileAexpMonotonic *)

Existing Instance genSaexp.

(*! QuickChick (forAll arbitrary test_compile_aexp_monotonic). *)

Remove Hints genSaexp : typeclass_instances.
(* End Section *)


(*
Open Scope nat.
Inductive is_even : nat -> Prop :=
| even_O: is_even O
| even_S: forall n : nat, is_even n -> is_even (S (S n)).
Derive ArbitrarySizedSuchThat for (fun n => is_even n).

Remove Hints gen_small_typ : typeclass_instances.


Derive ArbitrarySizedSuchThat for (fun instr => is_Op instr).
Print GenSizedSuchThatis_Op.
Sample (genST (fun i => is_Op i)).
Sample (@arbitraryST 

Instance gen_instr_op : GenSizedSuchThat instr (fun instr => is_Op instr) :=
  {| arbitrarySizeST n :=
       (liftGen Some (liftGen INSTR_Op (arbitrarySized n)))
  |}.

Sample (genST (fun i => is_Op i)).
*)



(* Derive ArbitrarySizedSuchThat for (fun env => env_lt n env). *)

(*
Import Vellvm.ImpCorrectness.
Require Import Vellvm.MemoryQuickChick.
Sample (@arbitrarySizeST _ (fun x => is_Op x) GenSizedSuchThatis_Op 3).

Sample (genST (fun i => is_Op i)).

Derive ArbitrarySizedSuchThat for (fun instr => is_Eff instr).
Derive ArbitrarySizedSuchThat for (fun instr => is_Op instr).
Derive ArbitrarySizedSuchThat for (fun instr => is_Op instr).
Derive ArbitrarySizedSuchThat for (fun instr => is_Op instr).




(* Print env_lt. *)

From QuickChick Require Import QuickChick.
Local Open Scope nat.
Import Ollvm_ast.
Derive Arbitrary for Expr
Derive Arbitrary for value.

Derive ArbitrarySizedSuchThat for (fun i => is_Op i).

Derive ArbitrarySizedSuchThat for (fun instr => is_Op instr).

*)

(* Derive ArbitrarySizedSuchThat for (fun env => env_lt n env). *)
(* Sample (genST (fun env => env_tl env)). *)

(* Derive ArbitrarySizedSuchThat for (fun instr => is_Op instr). *)

(*
Lemma env_extends_lt :
  forall e n dv
    (Henv: env_lt n e),
    env_extends e (add_env_Z n dv e).
*)

