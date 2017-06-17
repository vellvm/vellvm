(******** Memory.v ********)


Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util.
Require Import Vellvm.StepSemantics.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

Module A : Vellvm.StepSemantics.ADDR with Definition addr := nat.
  Definition addr := nat.
End A.  

Module SS := StepSemantics.StepSemantics(A).
Export SS.

Definition mtype := list dvalue.
Definition undef := DV VALUE_Undef.

CoFixpoint memD (memory:mtype) (d:Trace) : Trace :=
  match d with
    | Tau d'            => Tau (memD memory d')
    | Vis (Eff (Alloca t k))  => Tau (memD (memory ++ [undef])%list
                                          (k (DVALUE_Addr (**!*)(List.length memory)(**!(pred (List.length memory))*))))
    | Vis (Eff (Load a k))    => Tau (memD memory (k (nth_default undef memory a)))
    | Vis (Eff (Store a v k)) => Tau (memD (replace memory a v) k)
    | Vis (Eff (Call d ds k)) => Vis (Eff (Call d ds k))
    | Vis x => Vis x
  end.

Fixpoint MemDFin (memory:mtype) (d:Trace) (steps:nat) : option mtype :=
  match steps with
  | O => None
  | S x =>
    match d with
    | Vis (Fin d) => Some memory
    | Vis (Err s) => None
    | Tau d' => MemDFin memory d' x
    | Vis (Eff (Alloca t k))  =>
      MemDFin (memory ++ [undef])%list (k (DVALUE_Addr
                                             (*!*) (*  (List.length memory) *) 
                                             (*! *)  (pred (List.length memory)) (*  *)
                                       )) x
    | Vis (Eff (Load a k))    => MemDFin memory (k (nth_default undef memory a)) x
    | Vis (Eff (Store a v k)) => MemDFin (replace memory a v) k x
    | Vis (Eff (Call d ds k)) => None
    end
  end%N.


(*
Previous bug: 
Fixpoint MemDFin {A} (memory:mtype) (d:Obs A) (steps:nat) : option mtype :=
  match steps with
  | O => None
  | S x =>
    match d with
    | Ret a => None
    | Fin d => Some memory
    | Err s => None
    | Tau d' => MemDFin memory d' x
    | Eff (Alloca t k)  => MemDFin (memory ++ [undef])%list (k (DVALUE_Addr (pred (List.length memory)))) x
    | Eff (Load a k)    => MemDFin memory (k (nth_default undef memory a)) x
    | Eff (Store a v k) => MemDFin (replace memory a v) k x
    | Eff (Call d ds k)    => None
    end
  end%N.
*)
(******** End of Memory.v ********)


(******** Compiler.v ********)


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

(* Vellvm dependencies *)
Require Import Vellvm.Classes Vellvm.Ollvm_ast Vellvm.AstLib.

(* Logical Foundations dependencies *)
Require Import Vellvm.Imp Vellvm.Maps.

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
        | Some (id, t) =>
          mret ([], None, (mk_block l insns t id)::blks)
        end
      | T id t  => mret ([], Some (id, t), blks)
      | I uid insn => mret ((uid,insn)::insns, term_opt, blks)
      end
   ) code ([], None, []) 
  ;
    match term_opt with
    | None => failwith "terminator not found"
    | Some (id, t) =>
      mret ((mk_block entry_label insns t id) :: blks)
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

Definition llvm_bind (A B:Type) (g:LLVM A) (f:A -> LLVM B) : LLVM B :=
  fun s =>
    let '(st, x) := g s in
    match x with
    | inl e => (st, inl e)
    | inr a => (f a) st
    end.
Program Instance llvm_monad : (@Monad LLVM) llvm_functor := _.
Next Obligation.
  split.
  - exact llvm_ret.
  - exact llvm_bind.
Defined.    

Instance llvm_err : (@ExceptionMonad string LLVM _ _) := fun _ e => fun s => (s, inl e).

(* Start the counters at 1 so that 0 can be used at the toplevel *)
Definition run {A} (g : LLVM A) : err (A * list elt) :=
  let '((_,_,c), x) := g (1,1,[])%Z in
  match x with
  | inl e => inl e
  | inr a => inr (a, List.rev c)
  end.

Definition lift {A} (e:string) (m:option A) : LLVM A :=
  fun s => (s, trywith e m).

Definition lid_of_Z (n:int) : local_id := Name ("x"++(string_of n))%string.

Definition genlabel : () -> LLVM (local_id) :=
  fun _ => fun '(n,m,c) => ((1+n,m,c), mret (lid_of_Z n))%Z.

Definition genvoid : () -> LLVM (instr_id) :=
  fun _ => fun '(n,m,c) => ((n,1+m,c), mret (IVoid m))%Z.

(* A context maps Imp variables to Vellvm identifiers
   Invariant: 
      storage space for an Imp variable is represented as an alloca'ed 
      ctxt (Id X) is the pointer to the storage for X.
*)
Definition ctxt := partial_map value.

Definition val_of_nat (n:nat) : value :=
  SV (VALUE_Integer (Z.of_nat n)).

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


(* Note: list of instructions in code is generated in reverse order *)
Fixpoint compile_aexp (g:ctxt) (a:aexp) : LLVM value :=
  let compile_binop (op:ibinop) (a1 a2:aexp) :=
      'v1 <- compile_aexp g a1;
      'v2 <- compile_aexp g a2;
      'lid <- binop op i64 v1 v2;
      mret (local lid)
  in
  match a with
  | ANum n => mret (val_of_nat n)

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
  | BTrue     => mret (val_of_bool true)
  | BFalse    => mret (val_of_bool false)
  | BEq a1 a2 => compile_icmp Eq a1 a2
  | BLe a1 a2 => compile_icmp Ule a1 a2

  | BNot b =>
    'v <- compile_bexp g b;
    'lid <- binop Xor i1 v (val_of_bool true);
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
    '; store (val_of_nat 0) (local uid);
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



(* Testing infrastructure *)

Definition compile_aexp_wrapper (a : aexp) : err (value * list elt) :=
  run (let fvs := IDSet.elements (fv a) in
       'g <- compile_fv fvs;
         compile_aexp g a).


Definition compile_bexp_wrapper (b : bexp) : err (value * list elt) :=
  run (let fvs := IDSet.elements (fv b) in
       'g <- compile_fv fvs;
         compile_bexp g b).
(******** End of Compiler.v ********)


(******** CompilerProp.v ********)


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

Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.

Require Import ZArith String Omega List Equalities MSets.
Import ListNotations.

(* Vellvm dependencies *)
Require Import Vellvm.Ollvm_ast.
Require Import Vellvm.AstLib.
Require Import Vellvm.CFG.
Require Import Vellvm.StepSemantics.
Require Import Vellvm.Classes.

(* Logical Foundations dependencies *)
Require Import Vellvm.Imp.
Require Import Vellvm.Maps.
Require Import Vellvm.ImpCEvalFun.
Import ListNotations.

Require Import Vellvm.ImpQuickChick.

(* Equality for the imp final memory states. *)

(* These definitions should probably go in a library *)
Definition dvalue_of_nat (n:nat) : dvalue :=
  DV (VALUE_Integer (Z.of_nat n)).

Definition imp_val_eqb (v1 v2 : dvalue) : bool :=
  match v1, v2 with
  | (DV (VALUE_Integer z1)), (DV (VALUE_Integer z2)) => Z.eqb z1 z2
  | _, _ => false
  end.

Fixpoint imp_memory_eqb (m1 : list dvalue) (m2 : list dvalue) : bool :=
  match m1, m2 with
  | [], [] => true
  | x::xs, y::ys => if imp_val_eqb x y then imp_memory_eqb xs ys else false
  | _, _ => false 
  end.  

(* The executable test function for compiler correctnes. *)

(* TODO: 
     Add a 'run' function to Imp to execute n steps of the
     Imp operational semantics starting from a given state.

     One possible testing issue: the Vellvm code of a given
     imp program will take many more steps.
 *)
Require Import List.


Fixpoint string_of_dvalue' (v : dvalue) :=
  match v with
  | DV expr =>
    match expr with
    | VALUE_Ident id => string_of id
    | VALUE_Integer x => string_of x
    | VALUE_Bool b => string_of b
    | VALUE_Null => "null"
    | VALUE_Zero_initializer => "zero initializer"
    | VALUE_Cstring s => s
    | VALUE_None => "none" 
    | VALUE_Undef => "undef" 
    | OP_IBinop iop t v1 v2 =>
      ((string_of iop) ++ " " ++ (string_of t)
                       ++ " " ++ (string_of_dvalue' v1)
                       ++ " " ++ (string_of_dvalue' v2))%string
    | OP_GetElementPtr t ptrval idxs =>
      "getelementptr"
    | _ => "string_of_dvalue' todo"
    end
  | DVALUE_CodePointer p => "string_of_dvalue' todo (code pointer)"
  | DVALUE_Addr a => "string_of_dvalue' todo (addr)"
  end.

Instance string_of_value : StringOf dvalue := string_of_dvalue'.

Instance string_of_mem : StringOf mtype :=
  fun mem => ("[" ++ show_nat (List.length mem) ++ "] " ++ string_of mem)%string.
(*
  fun (mem: mtype) =>
    fold_left (fun s cell =>
                 match cell with
                 | DV (VALUE_Integer z) => (s ++ (string_of z) ++ "; ")%string
                 | DVALUE_CodePointer p => (s ++ "code pointer; ")%string
                 | DVALUE_Addr a => (s ++ "addr; ")%string
                 | _ => (s ++ "~VALUE_Integer; ")%string
                 end)
              mem "".
*)

Definition state_to_string (fv : list id) (st : state) : string :=
  fold_left (fun acc x => (match x with
                        | Id ident => (ident ++ ": " ++ show_nat (st x) ++ ", ")%string
                        end)) fv "".

Instance string_of_IDSet_elt : StringOf IDSet.elt :=
  fun elem => 
    match elem with
    | Id name => name
    end.

Definition compile_and_execute (c : Imp.com) : err mtype :=
  let fvs := IDSet.elements (fv c) in
  match compile c with
  | inl e => inl e
  | inr ll_prog =>
    let m := modul_of_toplevel_entities ll_prog in
    match mcfg_of_modul m with
    | None => inl "Compilation failed"
    | Some mcfg =>
      match init_state mcfg "imp_command" with
      | inl e => inl "init failed"
      | inr initial_state =>
        let semantics := sem mcfg initial_state in
        let llvm_final_state := MemDFin [] semantics 10000 in
        match llvm_final_state with
        | Some st => inr st
        | None => inl "out of gas"
        end
      end
    end
  end.

Definition imp_compiler_correct_aux (p:Imp.com) : Checker :=
  let fvs := IDSet.elements (fv p) in
  match compile p with
  | inl e => whenFail "Compilation failed" false
  | inr ll_prog =>
    let m := modul_of_toplevel_entities ll_prog in
    match mcfg_of_modul m with
    | None => whenFail "Compilation failed" false
    | Some mcfg =>
      match init_state mcfg "imp_command" with
      | inl e => whenFail "init failed" false
      | inr initial_state =>
        let semantics := sem mcfg initial_state in
        let llvm_final_state := MemDFin [] semantics 15000 in
        let imp_state := ceval_step empty_state p 100 in
        match (llvm_final_state, imp_state) with
        | (None, None) => whenFail "both out of gas" true
        | (Some llvm_st, None) => whenFail "imp out of gas" true
        | (None, Some imp_st) => whenFail "llvm out of gas" true
        | (Some llvm_st, Some imp_st) => 
          let ans_state := List.map (fun x => dvalue_of_nat (imp_st x)) fvs in
          checker (whenFail ("not equal: llvm: "
                               ++ (string_of llvm_st)
                               ++ "; imp: "
                               ++ (string_of ans_state)
                               ++ "; free vars: "
                               ++ (string_of fvs) (* (elems_to_string fvs) *)
                               ++ "; compiled code: "
                               ++ (string_of ll_prog))
                            (imp_memory_eqb (*!*) (List.rev llvm_st) (*! llvm_st *) ans_state))
        end        
      end
    end
  end.

(*
Definition imp_compiler_correct_bool (p:Imp.com) : bool :=
  let fvs := IDSet.elements (fv p) in
  match compile p with
  | inl e => false
  | inr ll_prog =>
    let m := modul_of_toplevel_entities ll_prog in
    match mcfg_of_modul m with
    | None => false
    | Some mcfg =>
      match init_state mcfg "imp_command" with
      | inl e => false
      | inr initial_state =>
        let semantics := sem mcfg initial_state in
        let llvm_final_state := MemDFin [] semantics 15000 in
        let imp_state := ceval_step empty_state p 100 in
        match (llvm_final_state, imp_state) with
        | (None, None) => true
        | (Some llvm_st, None) => true
        | (None, Some imp_st) => true
        | (Some llvm_st, Some imp_st) => 
          let ans_state := List.map (fun x => dvalue_of_nat (imp_st x)) fvs in
          imp_memory_eqb (List.rev llvm_st) ans_state
        end        
      end
    end
  end.


Definition compile_aexp_bool (a:aexp) : bool :=
  let p := (Id "fresh_var" ::= a) in
  imp_compiler_correct_bool p.  

Compute (compile_aexp_bool (AMult (ANum 2) (ANum 3))).
*)

Definition compile_aexp_correct (a:aexp) : Checker :=
  let p := (Id "fresh_var" ::= a) in
  imp_compiler_correct_aux p.  


Definition compile_bexp_correct (b:bexp) : Checker :=
  let p := (IFB b THEN idX ::= ANum 1 ELSE idY ::= ANum 2 FI) in
  imp_compiler_correct_aux p.  
  



(* Tests *)

Extract Constant Test.defNumTests => "100".

(* Fails compilation because of wrongly-corrected monad_fold_left *)
Example prog1 := (idX ::= ANum 1).
Example prog2 := (idW ::= AId idW).

(* Fails compilation because of off-by-one in Alloca for MemDFin *)
Example prog3 := idX ::= ANum 1 ;; idY ::= ANum 2 ;; idZ ::= ANum 3 ;; idW ::= ANum 4.
Example prog4 := idX ::= AId idY.
Example prog5 := idX ::= APlus (AId idW) (AId idX).

(* Fails compilation because of memory allocation of free vars in reverse order
   during compilation *)
Example prog6 := idY ::= APlus (AId idZ) (ANum 4).

(* Fails because of N semantics in Imp but Z semantics for Vellvm *)
Example prog7 :=
  IFB (BEq (AMult (ANum 10) (AId idW)) (AMult (ANum 6) (ANum 5))) THEN
    X ::= (APlus (AId idY) (AMult (APlus (ANum 1) (ANum 5)) (APlus (ANum 1) (ANum 0))))
  ELSE Y ::= (APlus (AId idY) (APlus (AMinus (ANum 3) (ANum 4)) (ANum 2))) FI.
  (* IF (10 * W == 6 * 5) THEN
       X = Y + ( (1 + 5) * (1 + 0) )
     ELSE
       Y = Y + ((3 - 4) + 2)
     END *)

Example prog8 :=
  IFB (BFalse) THEN
    X ::= ANum 10
  ELSE Y ::= (AMinus (ANum 3) (ANum 4)) FI.

Example prog9 :=
  Y ::= (AMinus (ANum 3) (ANum 4)).


Definition show_aexp_compilation_result (result : err (Ollvm_ast.value * list elt)) :=
  match result with
  | inl _ => "err" 
  | inr (_, elts) => string_of elts
  end.

Definition show_bexp_compilation_result (result : err (Ollvm_ast.value * list elt)) :=
  match result with
  | inl _ => "err"
  | inr (_ , elts) => string_of elts
  end.


Definition show_result (result : err (toplevel_entities (list block))) :=
  match result with
  | inl _ => "error"
  | inr l => fold_left (fun s tle_blk => (s ++ "; " ++ (string_of tle_blk))%string) l ""
  end.

(*
Compute (show_aexp_compilation_result
           (compile_aexp_wrapper (AMult (AId idX) (APlus (ANum 1) (ANum 2))))).

Compute (show_bexp_compilation_result
           (compile_bexp_wrapper (BEq (ANum 5) (APlus (ANum 2) (ANum 3))))).

Compute (show_result (compile prog3)).
Compute (show_result (compile prog4)).
Compute (show_result (compile prog6)).

Compute (compile_and_execute prog3).
Compute (compile_and_execute prog4).
Compute (compile_and_execute prog5).
Compute (compile_and_execute prog7).
Compute (compile_and_execute prog8).
Compute (compile_and_execute prog9).
*)

(* Compute (compile_and_execute prog5). *)

(* QuickChick (forAll arbitrary
                   imp_compiler_correct_aux). *)

(* QuickChick (forAll (test_com_gen 2) imp_compiler_correct_aux). *)



(* QuickChick (forAll (test_aexp_gen) compile_aexp_correct). *)
(* QuickChick (forAll (test_bexp_gen) compile_bexp_correct). *)


Definition prog10 :=
  IFB (BNot (BNot (BLe (AMult (ANum 6) (ANum 6)) (AId Y))))
  THEN idY ::= AId idX
  ELSE idZ ::= AId idZ FI.

Definition prog11 :=
  IFB (BLe (AMult (ANum 6) (ANum 6)) (AId Y))
  THEN idY ::= AId idX
  ELSE idZ ::= AId idZ FI.

Definition prog12 :=
  IFB (BNot (BNot (BLe (ANum 0) (AId Y))))
  THEN idY ::= AId idX
  ELSE idZ ::= AId idZ FI.

Definition prog13 :=
  IFB (BNot (BNot (BEq (ANum 0) (AId Y))))
  THEN SKIP
  ELSE SKIP FI.

Definition prog14 :=
  IFB (BNot (BEq (ANum 0) (AId Y)))
  THEN SKIP
  ELSE SKIP FI.

Definition prog15 :=
  IFB (BEq (ANum 0) (AId Y))
  THEN SKIP
  ELSE SKIP FI.

Definition prog16 :=
  IFB (BNot BTrue)
  THEN SKIP
  ELSE SKIP FI.


(*
Compute (show_result (compile prog10)).
Compute (compile_and_execute prog10).
Compute (compile_and_execute prog11).
Compute (compile_and_execute prog12).
Compute (compile_and_execute prog13).
Compute (compile_and_execute prog14).
Compute (show_result (compile prog14)).
Compute (compile_and_execute prog15).
Compute (compile_and_execute prog16).
Compute (show_result (compile prog16)).
*)

(*!
QuickChick*) QuickChick  (forAllShrink (test_com_gen 3) (@shrink com shrcom) 
                   imp_compiler_correct_aux). (*
*)


(******** End of CompilerProp.v ********)