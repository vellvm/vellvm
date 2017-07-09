Require Import List.
Import ListNotations.
Require Import String.

Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.

Require Import Vminus.Atom.
Require Import Vminus.CompilImp.

Require Import Vminus.AtomQuickChick.
Require Import Vminus.VminusQuickChick.


(** Opsem **)

(*
Instance gen_loc `{Gen nat} : GenSized (list Atom.t * V.Opsem.loc) :=
  {| arbitrarySized n :=
       let fresh_list := get_fresh_atoms n [] in
       bindGen (vectorOf n arbitrary) (fun nat_list => 
       returnGen (fresh_list,
                  fun (a : Atom.t) =>
                    match (index_of_atom_in_list a fresh_list) with
                    | None => None
                    | Some i =>
                      List.nth_error nat_list i
                    end))
  |}.

Instance show_loc `{Show Atom.t} `{Show nat}:
  Show (list Atom.t * V.Opsem.loc) :=
  {| show paired_loc := (
       let '(atom_list, atom_map) := paired_loc in
       let fix helper atom_list atom_map :=
           match atom_list with
           | [] => "]"
           | (a :: l) =>
             match atom_map a with
             | None => "loc domain is inconsistent"
             | Some n => "(" ++ (show a) ++ ", " ++ (show n) ++ "), "
                            ++ helper l atom_map
             end
           end in
       "[" ++ helper atom_list atom_map )%string
  |}.

Sample (@arbitrary (list Atom.t * V.Opsem.loc) _).
 *)

Definition gen_loc_from_atom_list (atom_list : list Atom.t) : G V.Opsem.loc :=
  bindGen (vectorOf (List.length atom_list) arbitrary) (fun nat_list => 
  returnGen (fun (a : Atom.t) =>
               match (index_of_atom_in_list a atom_list) with
               | None => None
               | Some i =>
                 List.nth_error nat_list i
               end)).

Instance gen_opsem_state `{Gen V.Opsem.mem} `{Gen V.Opsem.loc} `{Gen Vminus.pc}
  : Gen V.Opsem.state :=
  {| arbitrary :=
       liftGen5 V.Opsem.mkst
                arbitrary
                arbitrary
                arbitrary
                arbitrary
                arbitrary
  |}.

(* Print V.Opsem.state. *)



(* Sample (@arbitrary V.Opsem.state _). *)






(* Generators for predicates *)

(*
Import 

Definition insn_at_pc := 

Fixpoint gen_cfg_with_instrs_at (
         (st GenSizedSuchThat (fun g => insns_at_pc g p instrs)
*)