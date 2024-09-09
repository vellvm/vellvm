(* begin hide *)
From Vellvm Require Import
     Syntax.CFG
     Syntax.DynamicTypes
     Syntax.LLVMAst
     Syntax.Scope
     Analysis.Dom.
(* end hide *)

  Lemma instr_id_eq_dec : forall (x y : instr_id), {x = y} + {x <> y}.
  Proof.
    intros. destruct (Eqv.eqv_dec_p x y); auto.
  Qed.

  Definition def_sites_phis (phis : list (local_id * phi dtyp)) : list instr_id :=
    List.map (fun '(x,_) => IId x) phis.

  Definition pc : Type := block_id * option (nat * instr_id).

  Lemma pc_eq_dec : forall (x y : pc), {x = y} + {x <> y}.
  Proof.
    repeat decide equality.
  Qed.

  Definition opt_succ (mn : option (nat * instr_id)) : nat :=
    match mn with | Some (n,_) => S n | None => 0 end.

  Definition succ_instr (c : cfg dtyp) (v v' : pc) : Prop :=
    let '(bid,mx) := v in
    match find_block c.(blks) bid with
    | Some bk =>
      match List.nth_error
              (def_sites_phis bk.(blk_phis) ++ List.map fst bk.(blk_code)) (opt_succ mx) with
      | None => exists bid', List.In bid' (successors bk) /\ v' = (bid',None)
      | Some iid => v' = (bid, Some (opt_succ mx, iid))
      end
    | None => False
    end.

  Definition mem_instr (c : cfg dtyp) (p : pc) : Prop :=
    let '(bid,mx) := p in
    match find_block c.(blks) bid with
    | Some bk =>
      match mx with
      | None => True
      | Some (offset,x) =>
        match List.nth_error
                (def_sites_phis bk.(blk_phis) ++ List.map fst bk.(blk_code)) offset with
        | None => False
        | Some iid => x = iid
        end
      end
    | None => False
    end.

(* IN PROGRESS, IF NEEDED :  optimization to do one pass over all instrs.
potentially nice for large programs.  *)

(* private modified copy of Def_sites from Scope.v, now as a list. *)

Require Import List.
Import ListNotations.

Class Def_sites_list (A : Type) := { def_sites: A ->  list raw_id }.

#[local] Instance instr_id_defs_list : Def_sites_list instr_id :=
  {| def_sites := fun id =>
                    match id with
                    | IId id => [id]
                    | _ => []
                        end |}.

#[local] Instance code_defs_list {T} : Def_sites_list (code T) :=
  {| def_sites := fold_right (fun '(id,_) acc => def_sites id ++ acc) [] |}.

#[local] Instance block_def_sites_list {T} : Def_sites_list (block T) :=
  {| def_sites := fun bk => map fst bk.(blk_phis) ++ def_sites bk.(blk_code) |}.

#[local] Instance ocfg_def_sites_list {T} : Def_sites_list (ocfg T) :=
  {| def_sites := List.flat_map def_sites |}.

#[local] Instance cfg_def_sites_list {T} : Def_sites_list (cfg T) :=
  {| def_sites := fun cfg => def_sites cfg.(blks) |}.  

Definition all_assigned_ids (c : cfg dtyp ): list raw_id := 
  cfg_def_sites_list.(def_sites) c.

(*  intuition: every assignment should be to a unique id. 
    if the list of all assigned ids contains a duplicate, 
    we can't be in SSA. *)
Definition in_ssa (c : cfg dtyp) : Prop := 
  NoDup (all_assigned_ids c).

From Vellvm Require Import 
Printfdefn
TypToDtyp.

Require Import String.
Open Scope string_scope. 

Definition printf_cfgs := 
(map df_instrs (convert_types (mcfg_of_tle printf_definition)).(m_definitions)).


Definition printf_cfg := 

hd ({| init := (Name "") ; blks := [] ; args := [] |}) printf_cfgs. 

Example printf_hd_in_ssa : in_ssa printf_cfg.
Proof. 
  unfold printf_cfg.
  unfold in_ssa. 
  unfold all_assigned_ids.
  unfold def_sites.
  (* ^ not necessary but makes proof more legible *)
  simpl.
  repeat apply NoDup_cons.  

(* destruct repeated false \/ patterns *)
all: 
  simpl; unfold "~"; try intro; 
  repeat (destruct H; try discriminate H).  
(* final nil case *)
apply NoDup_nil.  
Qed.      
  
Example printf_in_ssa : Forall in_ssa printf_cfgs.
Proof. 
  unfold printf_cfgs.
  unfold in_ssa. 
  unfold all_assigned_ids.
  unfold def_sites.
  (* ^ not necessary but makes proof more legible *)
  simpl.
  repeat apply NoDup_cons.  

(* destruct repeated false \/ patterns *)
all: 
  simpl; unfold "~"; try intro; 
  repeat (destruct H; try discriminate H).  
(* final nil case *)
apply NoDup_nil.  
Qed.     

(* old code:  *)
(*   
  let count_instrs (iids : list instr_id) := 
  fold_left (fun n i => 
    match i with 
    | IId _ => n + 1
    | _ => 0
    end) iids 0
  
  in 
  let count_in_block n b := 
  let code : code dtyp := b.(blk_code) in
    let iids : list instr_id  := List.map fst code in 
    let blk_n  := count_instrs iids in 
    n + blk_n
  in 
  let count := fold_left 
  count_in_block bs 0 in  *)
  (* for each b in bs, 
      for each instr in b, 
      if it's an assignment instr, 
      (set.add lhs, counter++).
      
    return set.size = counter.
    *)

(**  ------------------------------------------------------------------------- *)
(** * GRAPH instance for dominance calculation *)

(** Graph of program points *)


Module idGraph <: GRAPH.
  Definition t := cfg dtyp.
  Definition V := pc.
  Definition eq_dec_V := pc_eq_dec.
  Definition entry (g : cfg dtyp) : pc := (init g, None).
  Definition edge := succ_instr.
  Definition mem := mem_instr.
End idGraph.

(** Instantiate the dominance spec for this graph *)

Module Export Dom := Dom.Spec idGraph.
