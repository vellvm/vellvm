Require Import List.
Import ListNotations.

Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.

Require Import Vminus.Atom.

Instance show_atom : Show Atom.t :=
  {| show x := show (Atom.nat_of x) |}.

Fixpoint get_fresh_atoms n l :=
  match n with
  | 0 => l
  | S n' => get_fresh_atoms n' ((Atom.fresh l) :: l)
  end.

Definition fresh_store : list Atom.t := get_fresh_atoms 100 [].
Definition gen_fresh (atom_store : list Atom.t) : G Atom.t := 
  oneof (returnGen (Atom.fresh [])) (List.map returnGen atom_store).

Fixpoint index_of_atom_in_list (a : Atom.t) (l : list Atom.t) : option nat :=
  match l with
  | [] => None
  | (a' :: l') => if Atom.eq_dec a a' then Some 0 else
                   match index_of_atom_in_list a l' with
                   | Some n => Some (S n)
                   | None => None
                   end
  end.