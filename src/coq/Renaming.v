(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import Ascii Strings.String.
Require Import Vellvm.Classes Vellvm.Util.
Require Import Vellvm.LLVMAst Vellvm.AstLib Vellvm.CFG.

Open Scope string_scope.

Class Swap (A:Type) := swap : raw_id -> raw_id -> A -> A.
Class SwapLaws (A:Type) `{Swap A} := {
  swap_same_id : forall (i:raw_id) (x:A),
    swap i i x = x
}.

Definition swap_raw_id (id1 id2:raw_id) (id:raw_id) : raw_id :=
  if id == id1 then id2 else
    if id == id2 then id1 else
      id.
Instance raw_id_swap : Swap raw_id := swap_raw_id.

Program Instance raw_id_swaplaws : SwapLaws raw_id.
Next Obligation.
  unfold swap. unfold raw_id_swap. unfold swap_raw_id.
  destruct (x == i); auto.
Qed.

Definition swap_ident (id1 id2:raw_id) (id:ident) : ident :=
  match id with
  | ID_Global i => ID_Global (swap id1 id2 i)
  | ID_Local i => ID_Local (swap id1 id2 i)
  end.
Instance ident_swap : Swap ident := swap_ident.
Program Instance ident_swaplaws : SwapLaws ident.
Next Obligation.
  unfold swap. unfold ident_swap. unfold swap_ident. destruct x.
  rewrite swap_same_id. reflexivity.
  rewrite swap_same_id. reflexivity.
Qed.  

Instance swap_of_pair {A B} `(SA:Swap A) `(SB:Swap B) : Swap (A * B)%type :=
  fun id1 id2 p => (swap id1 id2 (fst p), swap id2 id2 (snd p)).
  
Instance swap_of_option {A} `(SA:Swap A) : Swap (option A) :=
  fun id1 id2 opt => match opt with None => None | Some x => Some (swap id1 id2 x) end.

Fixpoint swap_typ (id1 id2:raw_id) (t:typ) : typ :=
  match t with
  | TYPE_Pointer t' => TYPE_Pointer (swap_typ id1 id2 t')
  | TYPE_Array sz t' => TYPE_Array sz (swap_typ id1 id2 t')
  | TYPE_Function ret args => TYPE_Function (swap_typ id1 id2 ret) (List.map (swap_typ id1 id2) args)
  | TYPE_Struct fields => TYPE_Struct (List.map (swap_typ id1 id2) fields)
  | TYPE_Packed_struct fields => TYPE_Packed_struct (List.map (swap_typ id1 id2) fields)
  | TYPE_Vector sz t' => TYPE_Vector sz (swap_typ id1 id2 t')
  | TYPE_Identified id => TYPE_Identified (swap id1 id2 id)
  | _ => t
  end.

Instance swap_of_typ : Swap typ := swap_typ.

Instance swap_of_tident : Swap tident := swap.

Fixpoint swap_exp (id1 id2:raw_id) (e:exp) : exp :=
  match e with
  | EXP_Ident id => EXP_Ident (swap id1 id2 id)
  | EXP_Integer _
  | EXP_Float   _
  | EXP_Hex     _
  | EXP_Bool    _
  | EXP_Null
  | EXP_Zero_initializer
  | EXP_Cstring _
  | EXP_Undef => e
  | EXP_Struct fields =>
    EXP_Struct (List.map (fun '(t,e) => (swap id1 id2 t, swap_exp id1 id2 e)) fields)
  | EXP_Packed_struct fields =>
    EXP_Packed_struct (List.map (fun '(t,e) => (swap id1 id2 t, swap_exp id1 id2 e)) fields)    
  | EXP_Array elts =>
    EXP_Array (List.map (fun '(t,e) => (swap id1 id2 t, swap_exp id1 id2 e)) elts)
  | EXP_Vector elts =>
    EXP_Vector (List.map (fun '(t,e) => (swap id1 id2 t, swap_exp id1 id2 e)) elts)
  | OP_IBinop iop t v1 v2 =>
    OP_IBinop iop (swap id1 id2 t) (swap_exp id1 id2 v1) (swap_exp id1 id2 v2)
  | OP_ICmp cmp t v1 v2 =>
    OP_ICmp cmp (swap id1 id2 t) (swap_exp id1 id2 v1) (swap_exp id1 id2 v2)
  | OP_FBinop fop fm t v1 v2 =>
    OP_FBinop fop fm (swap id1 id2 t) (swap_exp id1 id2 v1) (swap_exp id1 id2 v2)    
  | OP_FCmp cmp t v1 v2 =>
    OP_FCmp cmp (swap id1 id2 t) (swap_exp id1 id2 v1) (swap_exp id1 id2 v2)    
  | OP_Conversion conv t_from v t_to =>
    OP_Conversion conv (swap id1 id2 t_from) (swap_exp id1 id2 v) (swap id1 id2 t_to)
  | OP_GetElementPtr t ptrval idxs =>
    OP_GetElementPtr (swap id1 id2 t) (swap id1 id2 (fst ptrval), swap_exp id1 id2 (snd ptrval))
                     (List.map (fun '(t,e) => (swap id1 id2 t, swap_exp id1 id2 e)) idxs)
  | OP_ExtractElement vec idx =>
    OP_ExtractElement (swap id1 id2 (fst vec), swap_exp id1 id2 (snd vec))
                      (swap id1 id2 (fst idx), swap_exp id1 id2 (snd idx))
  | OP_InsertElement  vec elt idx =>
    OP_InsertElement (swap id1 id2 (fst vec), swap_exp id1 id2 (snd vec))
                     (swap id1 id2 (fst elt), swap_exp id1 id2 (snd elt))                     
                     (swap id1 id2 (fst idx), swap_exp id1 id2 (snd idx))
  | OP_ShuffleVector vec1 vec2 idxmask =>
    OP_ShuffleVector (swap id1 id2 (fst vec1), swap_exp id1 id2 (snd vec1))
                     (swap id1 id2 (fst vec2), swap_exp id1 id2 (snd vec2))                     
                     (swap id1 id2 (fst idxmask), swap_exp id1 id2 (snd idxmask))
  | OP_ExtractValue  vec idxs =>
    OP_ExtractValue  (swap id1 id2 (fst vec), swap_exp id1 id2 (snd vec))
                     idxs
  | OP_InsertValue vec elt idxs =>
    OP_InsertValue (swap id1 id2 (fst vec), swap_exp id1 id2 (snd vec))
                   (swap id1 id2 (fst elt), swap_exp id1 id2 (snd elt))
                   idxs
  | OP_Select cnd v1 v2 =>
    OP_Select (swap id1 id2 (fst cnd), swap_exp id1 id2 (snd cnd))
              (swap id1 id2 (fst v1), swap_exp id1 id2 (snd v1))
              (swap id1 id2 (fst v2), swap_exp id1 id2 (snd v2))
  end.

Instance swap_of_exp : Swap exp := swap_exp.

Instance swap_of_texp : Swap texp := swap.

Definition swap_instr_id (id1 id2:raw_id) (i:instr_id) : instr_id :=
  match i with
  | IId id => IId (swap id1 id2 id)
  | IVoid n => IVoid n  (* TODO: support renaming these too? *)
  end.

Instance swap_of_instr_id : Swap instr_id := swap_instr_id.

Definition swap_phi (id1 id2:raw_id) (p:phi) : phi :=
  match p with
  | Phi t args => Phi (swap id1 id2 t) (List.map (swap id1 id2) args)
  end.
Instance swap_of_phi : Swap phi := swap_phi.

Definition swap_instr (id1 id2:raw_id) (ins:instr) : instr :=
  match ins with
  | INSTR_Op op => INSTR_Op (swap id1 id2 op)
  | INSTR_Call fn args => INSTR_Call (swap id1 id2 fn) (List.map (swap id1 id2) args)
  | INSTR_Alloca t nb align =>
    INSTR_Alloca (swap id1 id2 t) (swap id1 id2 nb) align
  | INSTR_Load volatile t ptr align =>
    INSTR_Load volatile (swap id1 id2 t) (swap id1 id2 ptr) align
  | INSTR_Store volatile val ptr align =>
    INSTR_Store volatile (swap id1 id2 val) (swap id1 id2 ptr) align
  | INSTR_Fence
  | INSTR_AtomicCmpXchg
  | INSTR_AtomicRMW
  | INSTR_Unreachable
  | INSTR_VAArg
  | INSTR_LandingPad => ins
  end.
Instance swap_of_instr : Swap instr := swap_instr.

Definition mangle_instr (i:instr_id * instr) : (instr_id * instr) :=
  match i with
  | _ => i
  end.

Definition mangle_block (blk:block) : block :=
  blk.

Definition mangle_blocks (blks:list block) : list block :=
  List.map mangle_block blks.

Definition mangle_definition (d:definition (list block)) : definition (list block) :=
  mk_definition _
  (df_prototype d)
  (df_args d)
  (mangle_blocks (df_instrs d))
.


Definition mangle_toplevel_entity (tle : toplevel_entity (list block)) : toplevel_entity (list block) :=
  match tle with
  | TLE_Definition d => TLE_Definition (mangle_definition d)
  | _ => tle
  end.

Definition transform (prog: list (toplevel_entity (list block))) : list (toplevel_entity (list block)) :=
  List.map mangle_toplevel_entity prog.