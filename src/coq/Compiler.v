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

Module Int1 := Ollvm_ast.Int1.
Definition int1 := Int1.int.

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

(* LLVM values -------------------------------------------------------------- *)

Definition i1 := TYPE_I (1)%Z.
Definition i64 := TYPE_I (64)%Z.
Definition i64ptr := TYPE_Pointer i64.

Definition val_of_nat (n:nat) : value :=
  SV (VALUE_Integer (Z.of_nat n)).

Definition val_of_int64 (i:int64) : value :=
  SV (VALUE_Integer (Int64.signed i)).

Definition val_of_int1 (i:int1) : value :=
  SV (VALUE_Integer (Int1.signed i)).

Definition val_of_ident (id:ident) : value :=
  SV (VALUE_Ident id).

Definition local (lid:local_id) : value := val_of_ident (ID_Local lid).

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

(* LLVM compiler monads ----------------------------------------- *)

(* 
  Compiler state for expressions
    n - IId counter 
    is - instructions
*)
Definition EXP A := ST (int * code) (err A).

Definition exp_map (A B:Type) (f:A->B) (g:EXP A) : EXP B :=
  fun s =>
    let '(st, x) := g s in
    match x with
    | inl e  => (st, inl e)
    | inr a => (st, inr (f a))
    end.

Instance exp_functor : @Functor EXP := exp_map.

Definition exp_ret (A:Type) (x:A) : EXP A :=
  fun s => (s, inr x).

Definition exp_bind (A B:Type) (g:EXP A) (f:A -> EXP B) : EXP B :=
  fun s =>
    let '(st, x) := g s in
    match x with
    | inl e => (st, inl e)
    | inr a => (f a) st
    end.
Program Instance exp_monad : (@Monad EXP) exp_functor := _.
Next Obligation.
  split.
  - exact exp_ret.
  - exact exp_bind.
Defined.    

Instance exp_err : (@ExceptionMonad string EXP _ _) := fun _ e => fun s => (s, inl e).

Definition lift_exp {A} (e:string) (m:option A) : EXP A :=
  fun s => (s, trywith e m).

Definition emit instr : EXP local_id :=
  fun '(n, is) =>
    let lid := lid_of_Z n in
    ((1+n, ((IId lid, instr)::is)), mret lid)%Z.
  
Definition binop op t v1 v2 : EXP local_id :=
  emit (INSTR_Op (SV (OP_IBinop op t v1 v2))).

Definition load v : EXP local_id := 
  emit (INSTR_Load false i64 (i64ptr, v) None).

Definition comp cmp v1 v2 : EXP local_id :=
  emit (INSTR_Op (SV (OP_ICmp cmp i64 v1 v2))).

(* initialization monad ----------------------------------------------------- *)

Definition INIT A := ST (int * int * code) (err A).

Definition init_map (A B:Type) (f:A->B) (g:INIT A) : INIT B :=
  fun s =>
    let '(st, x) := g s in
    match x with
    | inl e  => (st, inl e)
    | inr a => (st, inr (f a))
    end.

Instance init_functor : @Functor INIT := init_map.

Definition init_ret (A:Type) (x:A) : INIT A :=
  fun s => (s, inr x).

Definition init_bind (A B:Type) (g:INIT A) (f:A -> INIT B) : INIT B :=
  fun s =>
    let '(st, x) := g s in
    match x with
    | inl e => (st, inl e)
    | inr a => (f a) st
    end.
Program Instance init_monad : (@Monad INIT) init_functor := _.
Next Obligation.
  split.
  - exact init_ret.
  - exact init_bind.
Defined.    

Instance init_err : (@ExceptionMonad string INIT _ _) := fun _ e => fun s => (s, inl e).

Definition lift_init {A} (e:string) (m:option A) : INIT A :=
  fun s => (s, trywith e m).


Definition alloca : () -> INIT local_id :=
  fun _ => fun '(n, m, is) =>
    let lid := lid_of_Z n in
    let vid := IVoid m in
    ((1+n, 1+m, ((vid, INSTR_Store false (i64, val_of_nat 0) (i64ptr, local lid) None) :: (IId lid, INSTR_Alloca i64 None None)::is)), mret lid)%Z.
  

(* 
  Compiler state for commands
    n  - IId counter
    m  - IVoid counter 
    // state of the partially completed basic block:
    is - code of current block; instructions emitted here in reverse order
    tm - the terminator for the current block
    bs - list of completed blocks 
*)
Record cmd_state :=
  mk_cs {
      n : int;                
      m : int;                
      is : code;             
      tm : terminator;
      bs : list block;      
    }.

Definition CMD A := ST cmd_state (err A).

Definition cmd_map (A B:Type) (f:A->B) (g:CMD A) : CMD B :=
  fun s =>
    let '(st, x) := g s in
    match x with
    | inl e  => (st, inl e)
    | inr a => (st, inr (f a))
    end.

Instance cmd_functor : @Functor CMD := cmd_map.

Definition cmd_ret (A:Type) (x:A) : CMD A :=
  fun s => (s, inr x).

Definition cmd_bind (A B:Type) (g:CMD A) (f:A -> CMD B) : CMD B :=
  fun s =>
    let '(st, x) := g s in
    match x with
    | inl e => (st, inl e)
    | inr a => (f a) st
    end.

Program Instance cmd_monad : (@Monad CMD) cmd_functor := _.
Next Obligation.
  split.
  - exact cmd_ret.
  - exact cmd_bind.
Defined.    

Instance cmd_err : (@ExceptionMonad string CMD _ _) := fun _ e => fun s => (s, inl e).

Definition cmd_of_exp {A} (exp : EXP A) : CMD (code * A) :=
  fun '(mk_cs n m is tm bs) =>
    let '((n', ise), v) := exp (n, []) in
    match v with
    | inl e => (mk_cs n m is tm bs, inl e)
    | inr ans => (mk_cs n' m is tm bs, inr (ise, ans))
    end.

Definition cmd_of_init {A} (init : INIT A) : CMD (code * A) :=
  fun '(mk_cs n m is tm bs) =>
    let '((n', m', ise), v) := init (n, m, []) in
    match v with
    | inl e => (mk_cs n m is tm bs, inl e)
    | inr ans => (mk_cs n' m' is tm bs, inr (ise, ans))
    end.
  

Definition inject_code (ise:code) : CMD () :=
    fun '(mk_cs n m is tm bs) => (mk_cs n m (ise++is) tm bs, mret ()).

Definition lift_cmd {A} (e:string) (m:option A) : CMD A :=
  fun s => (s, trywith e m).

Definition emit_cmd instr : CMD local_id :=
  fun '(mk_cs n m is tm bs) =>
    let lid := lid_of_Z n in
    (mk_cs (1+n) m ((IId lid, instr)::is) tm bs, mret lid)%Z.

(*
Definition alloca : () -> CMD local_id :=
   fun _ => emit_cmd (INSTR_Alloca i64 None None).
*)  
  
Definition emitvoid instr : CMD () :=
    fun '(mk_cs n m is tm bs) =>
      let tid := (IVoid m) in
      (mk_cs n (1+m) ((tid, instr)::is) tm bs, mret ())%Z.
    
Definition store v vptr : CMD () :=
  emitvoid (INSTR_Store false (i64, v) (i64ptr, vptr) None).

Definition gen_label : () -> CMD local_id :=
 fun _ => fun '(mk_cs n m is tm bs) =>
    let lid := lid_of_Z n in
    (mk_cs (1+n) m is tm bs, mret lid)%Z.
  
Definition close_block (bid:block_id) (tm_new:terminator) : CMD () :=
  fun '(mk_cs n m is tm bs) =>
    let blk := mk_block bid [] (rev is) ((IVoid m), tm) in
    (mk_cs n (1+m) [] tm_new (blk::bs), mret ())%Z.


Definition run {A} (g : CMD A) : err (A * block_id * list block) :=
  let '(mk_cs n m is tm bs, x) := g (mk_cs 0 0 [] TERM_Ret_void [])%Z in
  match x with
  | inl e => inl e
  | inr a =>
    let bid := lid_of_Z n in
    let blk := mk_block bid [] (rev is) ((IVoid m), tm) in
    inr (a, bid, blk::bs)
  end.


(*! Section Compiler *)

(* A context maps Imp variables to Vellvm identifiers
   Invariant: 
      storage space for an Imp variable is represented as an alloca'ed 
      ctxt (Id X) is the pointer to the storage for X.
*)
Definition ctxt := partial_map value.


Fixpoint compile_aexp (g:ctxt) (a:aexp) : EXP value :=
  let compile_binop (op:ibinop) (a1 a2:aexp) :=
      'v1 <- compile_aexp g a1;
      'v2 <- compile_aexp g a2;
      'lid <- binop op i64 v1 v2;
      mret (local lid)
  in
  match a with
  | ANum n => (*!*) mret (val_of_int64 n) 
  (*! 'lid <- binop (Add false false) i64 (val_of_int64 n) (val_of_nat n);
      mret (local lid) *)
  | AId x =>
    'ptr <- lift_exp "AId ident not found" (g x);
    'lid <- load ptr;
     mret (local lid)

  | APlus a1 a2  => compile_binop (Add false false) a1 a2
  | AMinus a1 a2 => compile_binop (Sub false false) a1 a2
  | AMult a1 a2  => compile_binop (Mul false false) a1 a2
  end.
    
Fixpoint compile_bexp (g:ctxt) (b:bexp) : EXP value :=
  let compile_icmp (cmp:icmp) (a1 a2:aexp) :=
      'v1 <- compile_aexp g a1;
      'v2 <- compile_aexp g a2;
      'lid <- comp cmp v1 v2;
      mret (local lid)
  in
  match b with
  | BTrue     => mret (val_of_int1 (Int1.repr 1))
  | BFalse    => mret (val_of_int1 (Int1.repr 0))
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


Fixpoint compile_com (g:ctxt) (c:com) : CMD () :=
  match c with
  | CSkip => mret ()   

  | CAss x a => 
    '(cd, v) <- cmd_of_exp (compile_aexp g a);
    '_ <- inject_code cd;
    'ptr <- lift_cmd "CAss ident not found" (g x);
    '; store v ptr;
    mret ()           

  | CSeq c1 c2 =>
    '_ <- compile_com g c2;  
    '_ <- compile_com g c1;  
    mret ()

  | CIf b c1 c2 =>
    'br1 <- gen_label ();
    'br2 <- gen_label ();
    'merge <- gen_label ();    

    '_ <- close_block merge (TERM_Br_1 merge);
    '_ <- compile_com g c2;
    '_ <- close_block br2 (TERM_Br_1 merge);
    '_ <- compile_com g c1;
    '(cdb, v) <- cmd_of_exp (compile_bexp g b);
    '_ <- close_block br1 (TERM_Br (i1, v) br1 br2);
    '_ <- inject_code cdb;
    mret ()

  | CWhile b c =>
    'entry <- gen_label (); 
    'body <- gen_label (); 
    'exit <- gen_label ();

    '_ <- close_block exit (TERM_Br_1 entry);
    '_ <- compile_com g c;
    '(cdb, v) <- cmd_of_exp (compile_bexp g b);      

    '_ <- close_block body (TERM_Br (i1, v) body exit);
    '_ <- inject_code cdb;
    '_ <- close_block entry (TERM_Br_1 entry);
    mret ()    
  end.

Fixpoint compile_fv (l:list id) : INIT ctxt :=
  match l with
  | [] => mret empty
  | x::xs =>
    'g <- compile_fv xs;
    'uid <- alloca ();
    (* '; store (val_of_nat 0) (local uid); *)
    (* CHKoh: is the following right? *)
    (* 'v <- compile_aexp g (ANum (Int64.repr 0%Z));  *)
(*    '; store (val_of_nat 0) (local uid); *)
      
    mret (update g x (local uid)) 
  end.

(* TODO: Adjust for cmd/exp distinction *)
(*
Definition print_imp_id (x:id) (g:ctxt) : CMD () :=
  let 'Id s := x in
  let fn_name := ("print_" ++ s)%string in
  'ptr <- lift_cmd "AId ident not found" (g x);
  'lid <- load ptr;
  '; emitvoid (INSTR_Call (TYPE_Void, ID_Global(Name fn_name)) [(i64, local lid)]);
  mret ().
    

Fixpoint print_fv (l:list id) (g:ctxt) : CMD () :=
  match l with
  | [] => mret ()
  | x::xs =>
    '; print_fv xs g;
    '; print_imp_id x g;
      mret ()
  end.
*)
  
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
  '(fvs, bid, blocks) <-
          run (
            let fvs := IDSet.elements (fv c) in
            '(cd, g) <- cmd_of_init (compile_fv fvs);  
            '; compile_com g c;
            '; inject_code cd;   
(*            '; print_fv fvs g;  (* UNCOMMENT to enable imp state printing *) *)
            mret fvs
          )
  ;
  mret
   ((List.map (fun x => let 'Id s := x in TLE_Declaration (print_decl ("print_" ++ s))) fvs) ++
   [
    TLE_Definition
    {|
    df_prototype := imp_decl;
    df_args := [];
    df_instrs := blocks
  |}]).
