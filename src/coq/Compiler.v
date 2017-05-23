Require Import ZArith String Omega List Equalities MSets.

(* Vellvm dependencies *)
Require Import Vellvm.Classes Vellvm.Ollvm_ast Vellvm.AstLib.

(* Logical Foundations dependencies *)
Require Import Imp Maps.

(* "Flattened" representation of Vellvm code *)
Inductive elt :=
| L (lbl:block_id)
| I (id:instr_id) (ins:instr)
| T (id:instr_id) (t:terminator)
.    

Fixpoint monad_fold_left {A B} `{Monad M} (f : A -> B -> M A) (l:list B) (a:A) : M A :=
  match l with
  | [] => mret a
  | x::xs =>
    'y <- monad_fold_left f xs a;
      f y x
  end.

Definition blocks_of_elts (entry_label:block_id) (code:list elt) : option (list block) :=
  '(insns, term_opt, blks) <-
   monad_fold_left
   (fun '(insns, term_opt, blks) e =>
      match e with
      | L l =>
        match term_opt with
        | None => 
          if (List.length insns) == 0 then mret ([], None, blks)
          else None
        | Some (id, t) =>
          mret ([], None, (mk_block l insns t id)::blks)
        end
      | T id t  => mret ([], Some (id, t), blks)
      | I uid insn => mret ((uid,insn)::insns, term_opt, blks)
      end
   ) code ([], None, []) 
  ;
    match term_opt with
    | None => None
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

Definition GenSym A := ST (int*int) (option A).

Definition gensym_map (A B:Type) (f:A->B) (g:GenSym A) : GenSym B :=
  fun s =>
    let '(n, x) := g s in
    match x with
    | None => (n, None)
    | Some a => (n, Some (f a))
    end.

Instance gensym_functor : @Functor GenSym := gensym_map.

Definition gensym_ret (A:Type) (x:A) : GenSym A :=
  fun s => (s, Some x).

Definition gensym_bind (A B:Type) (g:GenSym A) (f:A -> GenSym B) : GenSym B :=
  fun s =>
    let '(n, x) := g s in
    match x with
    | None => (n, None)
    | Some a => (f a) n
    end.
Program Instance gensym_monad : (@Monad GenSym) gensym_functor := _.
Next Obligation.
  split.
  - exact gensym_ret.
  - exact gensym_bind.
Defined.    

Definition run {A} (g : GenSym A) : option A :=
  let '(_, x) := g (0,0)%Z in x.

Definition lift {A} (m:option A) : GenSym A :=
  fun s => (s, m).

Definition gensym : () -> GenSym (local_id) :=
  fun _ => fun '(n,m) => ((1+n,m), Some (Anon (n)))%Z.

Definition genvoid : () -> GenSym (instr_id) :=
  fun _ => fun '(n,m) => ((n,1+m), Some (IVoid m))%Z.

(* A context maps Imp variables to Vellvm identifiers
   Invariant: 
      storage space for an Imp variable is represented as an alloca'ed 
      ctxt (Id X) is the identifier for the pointer to the storage for X.
*)
Definition ctxt := partial_map ident.

Definition val_of_nat (n:nat) : value :=
  SV (VALUE_Integer (Z.of_nat n)).

Definition val_of_ident (id:ident) : value :=
  SV (VALUE_Ident id).

Definition val_of_bool (b:bool) : value :=
  SV (VALUE_Bool b).

Definition i1 := TYPE_I (1)%Z.
Definition i64 := TYPE_I (64)%Z.
Definition i64ptr := TYPE_Pointer i64.

(* Note: list of instructions in code is generated in reverse order *)
Fixpoint compile_aexp (g:ctxt) (a:aexp) : GenSym (value * list elt) :=
  let compile_binop (op:ibinop) (a1 a2:aexp) :=
      '(v1, code1) <- compile_aexp g a1;
      '(v2, code2) <- compile_aexp g a2;
      'lid <- gensym ();
      mret (val_of_ident (ID_Local lid), [I (IId lid) (INSTR_Op (SV (OP_IBinop op i64 v1 v2)))] ++ code2 ++ code1)
  in
  match a with
  | ANum n => mret (val_of_nat n, [])

  | AId x =>
    'uid <- lift (g x);
    'lid <- gensym ();
     mret (val_of_ident (ID_Local lid), [I (IId lid) (INSTR_Load false i64 (i64ptr, val_of_ident uid) None)])

  | APlus a1 a2 => compile_binop (Add false false) a1 a2
  | AMinus a1 a2 => compile_binop (Sub false false) a1 a2
  | AMult a1 a2 => compile_binop (Mul false false) a1 a2
  end.

    
Fixpoint compile_bexp (g:ctxt) (b:bexp) : GenSym (value * list elt) :=
  let compile_icmp (cmp:icmp) (a1 a2:aexp) :=
      '(v1, code1) <- compile_aexp g a1;
      '(v2, code2) <- compile_aexp g a2;
      'lid <- gensym ();
      mret (val_of_ident (ID_Local lid), [I (IId lid) (INSTR_Op (SV (OP_ICmp cmp i64 v1 v2)))] ++ code2 ++ code1)
  in
  match b with
  | BTrue => mret (val_of_bool true, [])
  | BFalse => mret (val_of_bool false, [])
  | BEq a1 a2 => compile_icmp Eq a1 a2
  | BLe a1 a2 => compile_icmp Ule a1 a2
  | BNot b =>
    '(v, code) <- compile_bexp g b;
    'lid <- gensym ();
    mret (val_of_ident (ID_Local lid), [I (IId lid) (INSTR_Op (SV (OP_IBinop Xor i1 v (val_of_bool true))))] ++ code)
  | BAnd b1 b2 =>
    '(v1, code1) <- compile_bexp g b1;
    '(v2, code2) <- compile_bexp g b2;
    'lid <- gensym ();
    mret (val_of_ident (ID_Local lid), [I (IId lid) (INSTR_Op (SV (OP_IBinop And i1 v1 v2)))] ++ code2 ++ code1)
  end.

Fixpoint compile_com (g:ctxt) (c:com) : GenSym (list elt) :=
  match c with
  | CSkip => mret []

  | CAss x a =>
    '(v, code) <- compile_aexp g a;
    'uid <- lift (g x);
    'vid <- genvoid ();
    mret ((I vid (INSTR_Store false (i64, v) (i64ptr, val_of_ident uid) None)) :: code)

  | CSeq c1 c2 =>
    'code1 <- compile_com g c1;
    'code2 <- compile_com g c2;
    mret (code2 ++ code1)

  | CIf b c1 c2 =>
    '(v, codeb) <- compile_bexp g b;
    'code1 <- compile_com g c1;
    'code2 <- compile_com g c2;
    'br1 <- gensym ();
    'br2 <- gensym ();
    'vid <- genvoid ();
    mret (code2 ++ [L br2] ++ code1 ++ [L br1] ++ [T vid (TERM_Br (i1, v) br1 br2)] ++ codeb)

  | CWhile b c =>
    '(v, codeb) <- compile_bexp g b;
    'code <- compile_com g c;
    'entry <- gensym (); 
    'body <- gensym (); 
    'exit <- gensym ();
    'vidbody <- genvoid ();
    'videntry <- genvoid ();
    'vidheader <- genvoid ();
    mret ([L exit]
            ++ [T vidbody (TERM_Br_1 entry)] ++ code ++ [L body]
            ++ [T videntry (TERM_Br (i1, v) body exit)] ++ codeb ++ [L entry]
            ++ [T vidheader (TERM_Br_1 entry)])
  end.

Fixpoint compile_fv (l:list id) : GenSym (ctxt * list elt) :=
  match l with
  | [] => mret (empty, [])
  | x::xs =>
    '(g, code) <- compile_fv xs;
    'uid <- gensym ();
    mret (update g x (ID_Local uid), [I (IId uid) (INSTR_Alloca i64 None None)]++code)  
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


Definition compile (c:com) : option (definition (list block)) :=
  'elts <-
          run (
            let fvs := fv c in
            '(g, code_fv) <- compile_fv (IDSet.elements fvs);
              'code <- compile_com g c;
              mret (code ++ code_fv)
          );
  'blocks <- blocks_of_elts (Name "entry") elts;
  mret {|
    df_prototype := imp_decl;
    df_args := [];
    df_instrs := blocks
  |}.









