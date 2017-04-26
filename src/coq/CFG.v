(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import ZArith List String Omega.
Require Import Vellvm.AstLib Vellvm.Ollvm_ast.
Require Import Vellvm.Classes.
Import ListNotations.

(* paths into a program ----------------------------------------------------- *)

Record path :=
  mk_path {
      fn  : function_id;
      bn  : block_id;
      ins : instr_id;
    }.

Definition string_of_path p : string :=
  "@" ++ (string_of_raw_id (fn p)) ++ ":" ++ (string_of_raw_id (bn p)) ++ ":" ++ (string_of_instr_id (ins p)).


Require Import Equalities.
Module PATH <: UsualDecidableTypeFull.
  Definition t := path.
  Include HasUsualEq.
  Include UsualIsEq.
  Include UsualIsEqOrig.
  
  Lemma eq_dec : forall (x y : path), {x = y} + {x <> y}.
  Proof.
    intros x y.
    destruct x as [xf xb xi]; destruct y as [yf yb yi].
    destruct (xf == yf).
    - destruct (xb == yb).
      + destruct (xi == yi).
        * subst. left. reflexivity.
        * right. unfold not. intros. apply n. inversion H. auto.
      + right. unfold not. intros. apply n. inversion H. auto.
    - right. unfold not. intros. apply n. inversion H. auto.
  Qed.

  Include HasEqDec2Bool.
  
End PATH.
Instance eq_dec_path : eq_dec path := PATH.eq_dec.


(* control flow graphs (CFGs) ----------------------------------------------- *)

(* The path p in the step is the "fallthrough" to the next instruction. *)
Inductive cmd : Set :=
| Step  (i:instr) (p:path)
| Jump  (t:terminator)
.                    

Inductive block_entry : Set :=
| Phis (phis : list (local_id * instr)) (p:path)
.

Record cfg := mkCFG
{
  init : path;
  code : path  -> option cmd; 
  funs : function_id -> option (list ident * block_id * instr_id);  
  blks : function_id -> block_id -> option block_entry;  
}.

(* structurally well-formed CFGs 
   - the initial path denotes a command  
   - fallthrough closure: each fallthrough path maps to a command 
   - jump closure: each label used in a terminator leads to a
     block within the same function body.
*)

Definition path_exists (CFG : cfg) (p:path) : Prop :=
  exists cmd, (code CFG p) = Some cmd.

Definition lbls (t:terminator) : list block_id :=
  match t with
  | TERM_Ret _        
  | TERM_Ret_void   => []
  | TERM_Br _ l1 l2 => [l1; l2] 
  | TERM_Br_1 l => [l] 
  | TERM_Switch _ l brs => l::(List.map (fun x => snd x) brs)
  | TERM_IndirectBr _ brs => brs
  | TERM_Resume _    => []
  | TERM_Invoke  _ _ l1 l2 => [l1; l2] 
  end.


Definition wf_cfg (CFG : cfg) : Prop :=
  path_exists CFG (init CFG) 
  /\ (forall fn args bn ins, (funs CFG fn) = Some (args, bn, ins) -> path_exists CFG (mk_path fn bn ins)) 
  /\ (forall p q i, (code CFG p) = Some (Step i q) -> path_exists CFG q)
  /\ (forall p t, (code CFG p) = Some (Jump t) ->
    Forall (fun bn => exists phis, exists q, (blks CFG (fn p) bn) = Some (Phis phis q) /\ path_exists CFG q) (lbls t)).











(* creating CFGs from syntax ------------------------------------------------ *)

Fixpoint entities_to_init ets : option path :=
  match ets with
    | [] => None
    | (TLE_Definition d) :: t =>
      if (dc_name (df_prototype d)) == (Name "main") then
        match (df_instrs d) with
          | [] => None
          | b :: _ => Some (match blk_instrs b with
                        | [] => mk_path (Name "main") (blk_id b) (blk_term_id b)
                        | (iid, _) :: t => mk_path (Name "main") (blk_id b) iid
                            end)
        end
      else entities_to_init t
    | _ :: t => entities_to_init t
  end.

Fixpoint entities_to_funs ets fid :=
  match ets with
    | [] => None
    | (TLE_Definition d) :: t =>
      if (dc_name (df_prototype d)) == fid then
        match df_instrs d with
          | [] => None
          | b :: _ => Some (match blk_instrs b with
                              | [] => (map (fun x => ID_Local x) (df_args d), blk_id b, blk_term_id b)
                              | (iid, _) :: t => (map (fun x => ID_Local x) (df_args d), blk_id b, iid)
                            end)
        end
      else entities_to_funs t fid
    | _ :: t => entities_to_funs t fid
  end.

Fixpoint phis_from_block fname bname term_id (b : list (instr_id * instr)) : option block_entry :=
  match b with
    | (IId iid, INSTR_Phi i v as ins) :: t =>
       'rest <- phis_from_block fname bname term_id t;
        match rest with
          | Phis phis p => Some (Phis ((iid, ins)::phis) p) 
        end
    | (IVoid _, INSTR_Phi i v as ins) :: t => None
    | (next, _) :: _ => Some (Phis [] {| fn := fname; bn := bname; ins := next |})
    | [] => Some (Phis [] {| fn := fname; bn := bname; ins := term_id |})
  end.

Fixpoint entities_to_blks ets fid bid : option block_entry :=
  match ets with
    | [] => None
    | (TLE_Definition d) :: t =>
      if (dc_name (df_prototype d)) == fid then
        'bs <- find (fun b => RawID.eqb bid (blk_id b)) (df_instrs d);
        phis_from_block fid bid (blk_term_id bs) (blk_instrs bs) 
      else entities_to_blks t fid bid
    | _ :: t => entities_to_blks t fid bid
  end.

Definition next_or_term term_id (is : list (instr_id * instr)) : instr_id :=
  match is with
  | [] => term_id
  | (next, _)::_ => next
  end.

Fixpoint cmd_from_block to_find fn bn term_id is : option cmd :=
  match is with
    | [] => None
    | (id, ins) :: rest =>
      if to_find == id then
        Some (Step ins (mk_path fn bn (next_or_term term_id rest)))
      else cmd_from_block to_find fn bn term_id rest
  end.

Fixpoint cmd_from_term to_find (term_id:instr_id) term : option cmd :=
  if to_find == term_id then Some (Jump term) else None.

Fixpoint entities_to_code ets (p : path) : option cmd :=
  match ets with
    | [] => None
    | (TLE_Definition d) :: t =>
      if (dc_name (df_prototype d)) == (fn p) then
        'b <- find (fun b => RawID.eqb (bn p) (blk_id b)) (df_instrs d);
        match cmd_from_block (ins p) (fn p) (bn p) (blk_term_id b) (blk_instrs b) with
          | Some x => Some x
          | None => cmd_from_term (ins p) (blk_term_id b) (blk_term b)
        end
      else entities_to_code t p
    | _::t => entities_to_code t p
  end.

Definition TLE_to_cfg tl :=
  'init <- entities_to_init tl;
  Some {| init := init;
          code := entities_to_code tl;
          blks := entities_to_blks tl;
          funs := entities_to_funs tl
       |}.

