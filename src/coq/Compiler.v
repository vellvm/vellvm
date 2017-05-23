Require Import ZArith String Omega Lists Equalities MSets.

(* Vellvm dependencies *)
Require Import Vellvm.Classes Vellvm.Ollvm_ast Vellvm.AstLib.

(* Logical Foundations dependencies *)
Require Import Imp Maps.


(* Auxilliary definitions for working with Identifiers ---------------------- *)

Module IDDec <: MiniDecidableType.
  Definition t := id.
  Lemma eq_dec : forall (x y : t), {x = y} + {x <> y}.
  Proof.
    intros x y.
    destruct x as [s]. destruct y as [t].
    destruct (s == t); subst; auto.
    right. unfold not. intros H. apply n. inversion H; auto.
  Qed.
End IDDec.
Module ID := Make_UDT(IDDec).
Instance eq_dec_id : eq_dec id := ID.eq_dec.

Module IDSet := MSetWeakList.Make(ID).


(* Free variable calculation ------------------------------------------------ *)

Class FV X := fv : X -> IDSet.t.

Fixpoint fv_aexp (a:aexp) : IDSet.t :=
  match a with
  | ANum _ => IDSet.empty
  | AId x => IDSet.singleton x
  | APlus a1 a2
  | AMinus a1 a2
  | AMult a1 a2 => IDSet.union (fv_aexp a1) (fv_aexp a2)
  end.
Instance FV_aexp : FV aexp := fv_aexp.

Fixpoint fv_bexp (b:bexp) : IDSet.t :=
  match b with
  | BTrue | BFalse => IDSet.empty
  | BEq a1 a2
  | BLe a1 a2 => IDSet.union (fv a1) (fv a2)
  | BNot b => fv_bexp b
  | BAnd b1 b2 => IDSet.union (fv_bexp b1) (fv_bexp b2)
  end.
Instance FV_bexp : FV bexp := fv_bexp.

Fixpoint fv_com (c:com) : IDSet.t :=
  match c with
  | CSkip => IDSet.empty
  | CAss x a => IDSet.union (IDSet.singleton x) (fv a)
  | CSeq c1 c2 => IDSet.union (fv_com c1) (fv_com c2)
  | CIf b c1 c2 => IDSet.union (fv b) (IDSet.union (fv_com c1) (fv_com c2))
  | CWhile b c => IDSet.union (fv b) (fv_com c)
  end.
Instance FV_com : FV com := fv_com.

(* LLVM Identifier generation monad ----------------------------------------- *)

Definition GenSym A := ST int A.
Definition gensym : () -> GenSym (local_id) :=
  fun _ => fun n => (1+n, Anon (n))%Z.


(* A context maps Imp variables to Vellvm identifiers
   Invariant: 
      storage space for an Imp variable is represented as an alloca'ed 
      ctxt (Id X) is the identifier for the pointer to the storage for X.

*)
Definition ctxt := partial_map ident.

Inductive elt :=
| L (lbl:block_id)
| I (id:instr_id) (ins:instr)
| T (id:instr_id) (t:terminator)
.    















