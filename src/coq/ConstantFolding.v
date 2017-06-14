Require Import Vellvm.StepSemantics Vellvm.AstLib Vellvm.Ollvm_ast.
Require Import ZArith List String Omega.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Vellvm.Ollvm_ast Vellvm.AstLib Vellvm.CFG.
Import ListNotations.
Require Import BinInt.

Require Import paco.
Require Import Recdef.
Require Import Bool String Ascii List.
Require Import Omega.
Require Import Vellvm.Util.
Import ListNotations. 

Module A : Vellvm.StepSemantics.ADDR with Definition addr := nat.
  Definition addr := nat.
End A.  


Module SS := StepSemantics.StepSemantics(A).
Export SS.


Print value.


Definition nat := int.
Print ibinop.

Fixpoint fold_value (d : Ollvm_ast.value) : Ollvm_ast.value :=
  match d with
      | SV s =>
      match s with
        | VALUE_Ident a => SV (VALUE_Ident a)
        | VALUE_Integer a => SV (VALUE_Integer a)
        | VALUE_Float a => SV (VALUE_Float a)
        | VALUE_Bool a => SV (VALUE_Bool a)
        | VALUE_Null => SV (VALUE_Null)
        | VALUE_Zero_initializer => SV (VALUE_Zero_initializer)
        | VALUE_Cstring a => SV (VALUE_Cstring a)
        | VALUE_None => SV (VALUE_None)
        | VALUE_Undef => SV (VALUE_Undef)
        | VALUE_Struct a => SV (VALUE_Struct a)
        | VALUE_Packed_struct a => SV (VALUE_Packed_struct a)
        | VALUE_Array a => SV (VALUE_Array a)
        | VALUE_Vector a => SV (VALUE_Vector a)
        | OP_IBinop iop b v1 v2 => let cv1 := fold_value v1 in
                                 let cv2 := fold_value v2 in
                                 match cv1, cv2 with
                                   | SV (Ollvm_ast.VALUE_Integer x), SV (Ollvm_ast.VALUE_Integer y) =>
                                      match iop with
                                        | Ollvm_ast.Add _ _ =>  SV (Ollvm_ast.VALUE_Integer (x+y)%Z)
                                        | Ollvm_ast.Sub _ _ =>  SV (Ollvm_ast.VALUE_Integer (x-y)%Z)
                                        | Ollvm_ast.Mul _ _ =>  SV (Ollvm_ast.VALUE_Integer (x*y)%Z)
                                        | _ =>  SV (OP_IBinop iop b cv1 cv2)
                                      end
                                    | _ , _ => SV (OP_IBinop iop b cv1 cv2)
                                end
        | OP_ICmp a b v1 v2 =>  let cv1 := fold_value v1 in
                                let cv2 := fold_value v2 in
                              SV (OP_ICmp a b cv1 cv2)
        | OP_FCmp a b v1 v2  =>  let cv1 := fold_value v1 in
                                let cv2 := fold_value v2 in
                              SV (OP_FCmp a b cv1 cv2)
        | OP_FBinop a b c v1 v2 => let cv1 := fold_value v1 in
                                let cv2 := fold_value v2 in
                              SV (OP_FBinop a b c cv1 cv2)
        | OP_Conversion a b v1 d => let cv1 := fold_value v1 in
                                 SV (OP_Conversion a b v1 d)
        | OP_GetElementPtr a b c  => SV (OP_GetElementPtr a b c)
        | OP_ExtractElement a b  => SV (OP_ExtractElement a b)
        | OP_InsertElement a b c  => SV (OP_InsertElement a b c)
        | OP_ShuffleVector a b c  => SV (OP_ShuffleVector a b c)
        | OP_ExtractValue a b  => SV (OP_ExtractValue a b)
        | OP_InsertValue a b c => SV (OP_InsertValue a b c)
        | OP_Select a b c => SV (OP_Select a b c)
      end
  end.




Definition fold_instruction i :=
  match i with
    | INSTR_Op o => INSTR_Op (fold_value o)
    | INSTR_Call fn args => INSTR_Call fn (map (fun p => (fst p, fold_value (snd p))) args)
    | INSTR_Phi t args => INSTR_Phi t (map (fun p => (fst p, fold_value (snd p))) args)
    | INSTR_Alloca a b c => INSTR_Alloca a b c
    | INSTR_Load t a (b,d) c => INSTR_Load t a (b, fold_value d) c 
    | INSTR_Store t a (b,d) c => INSTR_Store t a (b, fold_value d) c
    | INSTR_Unreachable => INSTR_Unreachable
    | INSTR_Fence => INSTR_Fence
    | INSTR_AtomicCmpXchg => INSTR_AtomicCmpXchg
    | INSTR_AtomicRMW => INSTR_AtomicRMW
    | INSTR_VAArg => INSTR_VAArg
    | INSTR_LandingPad => INSTR_LandingPad
  end.



Definition fold_term t :=
  match t with
    | TERM_Ret (a, b) => TERM_Ret (a, fold_value b)
    | TERM_Ret_void => TERM_Ret_void
    | TERM_Br (a, b) v1 v2 => TERM_Br (a, fold_value b) v1 v2 
    | TERM_Br_1 b => TERM_Br_1 b
    | TERM_Switch v default_dest a => TERM_Switch v default_dest a
    | TERM_IndirectBr v brs => TERM_IndirectBr v brs
    | TERM_Resume v => TERM_Resume v
    | TERM_Invoke fnptrval args to_label unwind_label =>  TERM_Invoke fnptrval args to_label unwind_label
  end.

Definition fold_command c :=
  match c with
    | Step i p => Step (fold_instruction i) p
    | Jump t b => Jump t (fold_term b)
  end.

Definition fold_phis (ps : list (local_id * instr)) :=
  map (fun p => (fst p, fold_instruction (snd p))) ps.

Definition fold_block_entry b :=
  match b with
    | Phis p ls  n => Phis p (fold_phis ls)  n
  end.






Definition fold_controlflowgraph cfg :=
  {|
    init := init cfg;
    code := fun p => match (code cfg p) with
                       | None => None
                       | Some x => Some (fold_command x)
                     end;
    phis := fun t => match (phis cfg t) with
                       | None => None
                       | Some (Phis p ls n) => Some (Phis p (fold_phis ls)  n)
                     end;
    glbl := glbl cfg;

  |}.

Print value_ind'.


Lemma constantfold_correct :
  forall v st, eval_op st (fold_value v) = eval_op st v.
Proof. intros. induction v using value_ind'; try eauto; simpl; try rewrite <- IHv2; try rewrite <- IHv1; eauto. 
  - destruct (fold_value v1); eauto. destruct e; eauto. destruct (fold_value v2); eauto. destruct e; eauto. destruct iop; eauto.
Qed.




