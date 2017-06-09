(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import Vellvm.Maps Vellvm.Imp.

Require Import ZArith String Omega List Equalities MSets.
Import ListNotations.

(* Vellvm dependencies *)
Require Import Vellvm.Ollvm_ast Vellvm.Compiler Vellvm.AstLib Vellvm.CFG Vellvm.StepSemantics Vellvm.Memory.
Require Import Vellvm.Classes.

(* Logical Foundations dependencies *)
Require Import Vellvm.Imp Vellvm.Maps Vellvm.ImpCEvalFun.
Import ListNotations.
Open Scope list_scope.

Lemma compile_aexp_adds_code :
  forall g a
    (f : LLVM Ollvm_ast.value)
    (HC : compile_aexp g a = f)
    (v : Ollvm_ast.value)
    n n' m m' code code'
    (H : f (n,m,code) = ((n',m',code'),inr v)),
  exists code'', code' = code'' ++ code.
Proof.
  intros g a.
  induction a; intros; simpl in HC.
  - unfold llvm_ret in HC. subst. inversion H. subst.
    exists []. simpl. reflexivity.
  - unfold llvm_bind in HC. subst.
    unfold lift in H.
    unfold trywith in H.
    destruct (g i). simpl in H.
    unfold llvm_ret in H. inversion H. subst.
    exists [ I (IId (lid_of_Z n)) (INSTR_Load false i64 (i64ptr, v0) None)].
    simpl. reflexivity.
    simpl in H. inversion H.
    (* Automate these cases *)
Admitted.    

Definition iid n (id:instr_id) : Prop := (IId (lid_of_Z n)) = id.


Inductive code_at (CFG:mcfg) (f:function_id) : list elt -> Prop := 
| code_at_nil : code_at CFG f []
| code_at_uid :                         
    forall id i id' code
      (HF: fetch CFG (mk_pc f id) = Some (Step i id'))
      (IHC: code_at CFG f code),
      code_at CFG f ((I id i)::code)
| code_at_term :
    forall id bid term code
      (HF: fetch CFG (mk_pc f id) = Some (Jump bid term))
      (IHC: code_at CFG f code),
      code_at CFG f ((T id term)::code)
| code_at_label :
    forall bid code
      (ICH: code_at CFG f code),
      code_at CFG f ((L bid)::code)
.



Lemma compile_aexp_correct :
  forall (g:ctxt)
    (a:aexp)
    (f : LLVM Ollvm_ast.value)
    (HC : compile_aexp g a = f)
    (v : Ollvm_ast.value)
    n n' m m' code code'
    (H : f (n,m,code) = ((n',m',code'),inr v))
    (CFG : mcfg)
    (fn : function_id)
    (Hload: code_at CFG fn code')
    
  ,
    True.
    

                                      

