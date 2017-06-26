(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import ZArith String Omega List Equalities MSets.

(* CompCert *)
Require Import compcert.lib.Integers.

(* Vellvm dependencies *)
Require Import Vellvm.Classes Vellvm.Ollvm_ast Vellvm.AstLib.

(* Logical Foundations dependencies *)
Require Import Vellvm.Imp Vellvm.Maps.

(* Setup for 1bit integers *)
Module Wordsize1.
  Definition wordsize := 1%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize1.

Module Int1 := Make(Wordsize1).

Definition int1 := Int1.int.

(* "Flattened" representation of Vellvm code *)
Inductive elt :=
| L (lbl:block_id)
| I (id:instr_id) (ins:instr)
| T (id:instr_id) (t:terminator)
.    

Instance string_of_elt : StringOf elt :=
  fun elt =>
    match elt with
    | L lbl => ("Block " ++ (string_of lbl) ++ ": ")%string
    | I id ins => ("Instr " ++ (string_of id) ++ ": " ++ (string_of ins))%string
    | T id t => ("Terminator " ++ (string_of id) ++ ": " ++ (string_of t))%string
    end.


Definition blocks_of_elts (entry_label:block_id) (code:list elt) : err (list block) :=
  '(insns, term_opt, blks) <-
   monad_fold_right
   (fun '(insns, term_opt, blks) e =>
      match e with
      | L l =>
        match term_opt with
        | None => 
          if (List.length insns) == 0%nat then mret ([], None, blks)
          else failwith "terminator not found"
        | Some tm =>
          mret ([], None, (mk_block l [] insns tm)::blks)
        end
      | T id t  => mret ([], Some (id, t), blks)
      | I uid insn => mret ((uid,insn)::insns, term_opt, blks)
      end
   ) code ([], None, []) 
  ;
    match term_opt with
    | None => failwith "terminator not found"
    | Some tm =>
      mret ((mk_block entry_label [] insns tm) :: blks)
    end.


(* Auxilliary definitions for working with Identifiers ---------------------- *)

Module IDDec <: MiniDecidableType.
  Definition t := id.
  Lemma eq_dec : forall (x y : t), {x = y} + {x <> y}.
  Proof.
    intros x y.
    destruct x as [s]. destruct y as [t].
    destruct (s == t); subst; auto.
    right. unfold not. intros H. apply n. inversion H; auto.
  Defined.
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

Definition LLVM A := ST (int * int * list elt) (err A).

Definition llvm_map (A B:Type) (f:A->B) (g:LLVM A) : LLVM B :=
  fun s =>
    let '(st, x) := g s in
    match x with
    | inl e  => (st, inl e)
    | inr a => (st, inr (f a))
    end.

Instance llvm_functor : @Functor LLVM := llvm_map.

Definition llvm_ret (A:Type) (x:A) : LLVM A :=
  fun s => (s, inr x).
Hint Unfold llvm_ret.


Definition llvm_bind (A B:Type) (g:LLVM A) (f:A -> LLVM B) : LLVM B :=
  fun s =>
    let '(st, x) := g s in
    match x with
    | inl e => (st, inl e)
    | inr a => (f a) st
    end.
Hint Unfold llvm_bind.
Program Instance llvm_monad : (@Monad LLVM) llvm_functor := _.
Next Obligation.
  split.
  - exact llvm_ret.
  - exact llvm_bind.
Defined.    

Instance llvm_err : (@ExceptionMonad string LLVM _ _) := fun _ e => fun s => (s, inl e).
Hint Unfold llvm_err.

(* Start the counters at 1 so that 0 can be used at the toplevel *)
Definition run {A} (g : LLVM A) : err (A * list elt) :=
  let '((_,_,c), x) := g (1,1,[])%Z in
  match x with
  | inl e => inl e
  | inr a => inr (a, List.rev c)
  end.

Definition lift {A} (e:string) (m:option A) : LLVM A :=
  fun s => (s, trywith e m).
Hint Unfold lift.

Definition lid_of_Z (n:int) : local_id := Raw n.

Lemma lid_of_Z_inj: forall n1 n2, n1 <> n2 -> lid_of_Z n1 <> lid_of_Z n2.
Proof.
  intros. unfold lid_of_Z. unfold not. intros. apply H. inversion H0. reflexivity.
Qed.

Lemma lid_of_Z_inj2: forall n1 n2, lid_of_Z n1 = lid_of_Z n2 -> n1 = n2.
Proof.
  intros n1 n2 H.
  inversion H.
  reflexivity.
Qed.  

Definition genlabel : () -> LLVM (local_id) :=
  fun _ => fun '(n,m,c) => ((1+n,m,c), mret (lid_of_Z n))%Z.
Hint Unfold genlabel.

Definition genvoid : () -> LLVM (instr_id) :=
  fun _ => fun '(n,m,c) => ((n,1+m,c), mret (IVoid m))%Z.
Hint Unfold genvoid.

(* A context maps Imp variables to Vellvm identifiers
   Invariant: 
      storage space for an Imp variable is represented as an alloca'ed 
      ctxt (Id X) is the pointer to the storage for X.
*)
Definition ctxt := partial_map value.

Definition val_of_nat (n:nat) : value :=
  SV (VALUE_Integer (Z.of_nat n)).

Definition val_of_int64 (i:int64) : value :=
  SV (VALUE_Integer (Int64.signed i)).

Definition val_of_int1 (i:int1) : value :=
  SV (VALUE_Integer (Int1.signed i)).

Definition val_of_ident (id:ident) : value :=
  SV (VALUE_Ident id).

Definition local (lid:local_id) : value := val_of_ident (ID_Local lid).

Definition val_of_bool (b:bool) : value := SV (VALUE_Bool b).

Definition i1 := TYPE_I (1)%Z.
Definition i64 := TYPE_I (64)%Z.
Definition i64ptr := TYPE_Pointer i64.

Definition emit instr : LLVM local_id :=
  fun '(n,m,c) =>
    let lid := lid_of_Z n in
    ((1+n,m, (I (IId lid) instr)::c), mret lid)%Z.
  
Definition binop op t v1 v2 : LLVM local_id :=
  emit (INSTR_Op (SV (OP_IBinop op t v1 v2))).

Definition load v : LLVM local_id := 
  emit (INSTR_Load false i64 (i64ptr, v) None).

Definition comp cmp v1 v2 : LLVM local_id :=
  emit (INSTR_Op (SV (OP_ICmp cmp i64 v1 v2))).

Definition alloca : () -> LLVM local_id :=
  fun _ => emit (INSTR_Alloca i64 None None).

Definition term t : LLVM () := 
  fun '(n,m,c) =>
    let tid := (IVoid m) in
    ((n,1+m,((T tid t)::c)), mret ())%Z.

Definition emitvoid instr : LLVM () := 
  fun '(n,m,c) =>
    let tid := (IVoid m) in
    ((n,1+m,((I tid instr)::c)), mret ())%Z.

Definition store v vptr : LLVM () :=
  emitvoid (INSTR_Store false (i64, v) (i64ptr, vptr) None).

Definition label l : LLVM () :=
  fun '(n,m,c) => ((n,m,(L l)::c), mret ()).


(*! Section Compiler *)

(* Note: list of instructions in code is generated in reverse order *)
Fixpoint compile_aexp (g:ctxt) (a:aexp) : LLVM value :=
  let compile_binop (op:ibinop) (a1 a2:aexp) :=
      'v1 <- compile_aexp g a1;
      'v2 <- compile_aexp g a2;
      'lid <- binop op i64 v1 v2;
      mret (local lid)
  in
  match a with
  | ANum n => (* TO SEE: mret (val_of_int64 n) *)
    (*! *) 'lid <- binop (Add false false) i64 (val_of_int64 n) (val_of_nat 0);
      mret (local lid)
    (*! mret (val_of_int64 n) *)
  | AId x =>
    'ptr <- lift "AId ident not found" (g x);
    'lid <- load ptr;
     mret (local lid)

  | APlus a1 a2  => compile_binop (Add false false) a1 a2
  | AMinus a1 a2 => compile_binop (Sub false false) a1 a2
  | AMult a1 a2  => compile_binop (Mul false false) a1 a2
  end.
    
Fixpoint compile_bexp (g:ctxt) (b:bexp) : LLVM value :=
  let compile_icmp (cmp:icmp) (a1 a2:aexp) :=
      'v1 <- compile_aexp g a1;
      'v2 <- compile_aexp g a2;
      'lid <- comp cmp v1 v2;
      mret (local lid)
  in
  match b with
  | BTrue     => 
    'lid <- comp Eq (val_of_int64 (Int64.repr 0)) (val_of_int64 (Int64.repr 0));
    mret (local lid)
  | BFalse    => 
    'lid <- comp Eq (val_of_int64 (Int64.repr 1)) (val_of_int64 (Int64.repr 0));
    mret (local lid)
  | BEq a1 a2 => compile_icmp Eq a1 a2
  | BLe a1 a2 => compile_icmp Sle a1 a2
  | BNot b =>
    'v <- compile_bexp g b;
    'lid <- emit (INSTR_Op (SV (OP_ICmp Eq i1 (val_of_int1 (Int1.repr 0)) v)));
    mret (local lid) 

  | BAnd b1 b2 =>
    'v1 <- compile_bexp g b1;
    'v2 <- compile_bexp g b2;
    'lid <- binop And i1 v1 v2;
    mret (local lid)
  end.


Fixpoint compile_com (g:ctxt) (c:com) : LLVM () :=
  match c with
  | CSkip => mret ()

  | CAss x a => 
    'v <- compile_aexp g a;
    'ptr <- lift "CAss ident not found" (g x);
    '; store v ptr;
    mret () 

  | CSeq c1 c2 =>
    'code1 <- compile_com g c1;
    'code2 <- compile_com g c2;
    mret ()

  | CIf b c1 c2 =>
    'br1 <- genlabel ();
    'br2 <- genlabel ();
    'merge <- genlabel ();    
    'v <- compile_bexp g b;
    '; term (TERM_Br (i1, v) br1 br2);
    '; label br1;
    '; compile_com g c1;
    '; term (TERM_Br_1 merge);
    '; label br2;
    '; compile_com g c2;
    '; term (TERM_Br_1 merge);
    '; label merge;
    mret ()    

  | CWhile b c =>
    'entry <- genlabel (); 
    'body <- genlabel (); 
    'exit <- genlabel ();
    '; term (TERM_Br_1 entry);
    '; label entry;
    'v <- compile_bexp g b;
    '; term (TERM_Br (i1, v) body exit);
    '; label body;
    '; compile_com g c;    
    '; term (TERM_Br_1 entry);
    '; label exit;
    mret ()    
  end.

Fixpoint compile_fv (l:list id) : LLVM ctxt :=
  match l with
  | [] => mret empty
  | x::xs =>
    'g <- compile_fv xs;
    'uid <- alloca ();
    (* '; store (val_of_nat 0) (local uid); *)
    (* CHKoh: is the following right? *)
    'v <- compile_aexp g (ANum (Int64.repr 0%Z)); 
    '; store v (local uid);
      
    mret (update g x (local uid)) 
  end.

Definition print_imp_id (x:id) (g:ctxt) : LLVM () :=
  let 'Id s := x in
  let fn_name := ("print_" ++ s)%string in
  'ptr <- lift "AId ident not found" (g x);
  'lid <- load ptr;
  '; emitvoid (INSTR_Call (TYPE_Void, ID_Global(Name fn_name)) [(i64, local lid)]);
  mret ().
    

Fixpoint print_fv (l:list id) (g:ctxt) : LLVM () :=
  match l with
  | [] => mret ()
  | x::xs =>
    '; print_fv xs g;
    '; print_imp_id x g;
      mret ()
  end.

Definition imp_prog_type := TYPE_Function TYPE_Void [].
Definition imp_decl : declaration :=
  {| dc_name := Name "imp_command";
     dc_type := imp_prog_type;
     dc_param_attrs := ([],[]);
     dc_linkage := None;
     dc_visibility := None;
     dc_dll_storage := None;
     dc_cconv := None;
     dc_attrs := [];
     dc_section := None;
     dc_align := None;
     dc_gc := None
  |}.

Definition print_fn_type := TYPE_Function TYPE_Void [i64].
Definition print_decl (fn:string) : declaration :=
  {| dc_name := Name fn;
     dc_type := print_fn_type;
     dc_param_attrs := ([],[[]]);
     dc_linkage := Some (LINKAGE_External);
     dc_visibility := None;
     dc_dll_storage := None;
     dc_cconv := None;
     dc_attrs := [];
     dc_section := None;
     dc_align := None;
     dc_gc := None
  |}.


Definition compile (c:com) : err (toplevel_entities (list block)) :=
  '(fvs, elts) <-
          run (
            let fvs := IDSet.elements (fv c) in
            'g <- compile_fv fvs;  
            '; compile_com g c; 
(*            '; print_fv fvs g;  (* UNCOMMENT to enable imp state printing *) *)
            '; term TERM_Ret_void;    
            mret fvs
          );
  'blocks <- blocks_of_elts (Anon 0)%Z elts;
  mret
   ((List.map (fun x => let 'Id s := x in TLE_Declaration (print_decl ("print_" ++ s))) fvs) ++
   [
    TLE_Definition
    {|
    df_prototype := imp_decl;
    df_args := [];
    df_instrs := blocks
  |}]).
