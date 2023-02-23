(* begin hide *)
From Vellvm Require Import
     Utils.Util
     Syntax.CFG
     Syntax.DynamicTypes
     Syntax.LLVMAst
     Syntax.AstLib
     Syntax.Scope
     Analysis.Dom
     Analysis.DomKildall.
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

