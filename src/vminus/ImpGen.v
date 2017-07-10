(** ** QuickChick infrastructure for Imp **)

Require Import List.
Import ListNotations.
Require Import Arith.
Require Import String.

Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.

Require Import Vminus.Atom.
Require Import Vminus.Imp.

Require Import Vminus.AtomGen.

(** ** id **)
Definition id_store := get_fresh_atoms 5 [].

Instance gen_id: Gen id :=
  {| arbitrary := gen_fresh id_store |}.

Instance gen_ids: GenSized (list id) :=
  {| arbitrarySized n := returnGen (get_fresh_atoms n []) |}.

Instance shrink_id : Shrink id := {| shrink x := [] |}.

Instance show_id: Show id :=
  {| show x :=
       ("Id "%string ++ (show x) ++ "")%string |}.

(* Sample (@arbitrary id _). *)

(** ** aexp **)

Derive Arbitrary for aexp.
Derive Show for aexp.

Instance show_aexp: Show aexp :=
  {| show := (
       fix show_aexp_func a :=
           match a with
           | ANum n => "ANum " ++ (show n)
           | AId ident => show ident
           | APlus a1 a2 => "(" ++ (show_aexp_func a1) ++ " + " ++
                               (show_aexp_func a2) ++ ")"
           | AMinus a1 a2 => "(" ++ (show_aexp_func a1) ++ " - " ++
                                (show_aexp_func a2) ++ ")"
           | AMult a1 a2 => "(" ++ (show_aexp_func a1) ++ " * " ++
                               (show_aexp_func a2) ++ ")"
           end)%string
  |}.

Instance gen_plus_aexp `{Gen nat} `{Gen id} : GenSized aexp :=
  {| arbitrarySized :=
       fix gen_plus_aexp_func n :=
         match n with
         | 0 => liftGen ANum arbitrary
         | S n' =>
           let plus_gen :=
               (liftGen2 APlus
                         (liftGen AId arbitrary)
                         (gen_plus_aexp_func n')) in
           plus_gen
         end
  |}.

(* Sample (@arbitrary aexp _). *)

(** ** bexp **)

Derive Arbitrary for bexp.
Derive Show for bexp.

Instance show_bexp: Show bexp :=
  {| show :=
       fix show_bexp_func b := (
         match b with
         | BTrue => "true" 
         | BFalse => "false"
         | BEq a1 a2 => (show a1) ++ " = " ++ (show a2)
         | BLe a1 a2 => (show a1) ++ " <= " ++ (show a2)
         | BNot b => "~(" ++ (show_bexp_func b) ++ ")"
         | BAnd b1 b2 => (show_bexp_func b1) ++ " /\ " ++ (show_bexp_func b2)
         end)%string
  |}.

Instance gen_bexp_with_small_aexp `{GenSized aexp} : GenSized bexp :=
  {| arbitrarySized :=
       fix gen_bexp_func n :=
         match n with
         | 0 => elems [BTrue ; BFalse]
         | S n' =>
           let beq_gen := liftGen2 BEq (arbitrarySized 1) (arbitrarySized 1) in
           let ble_gen := liftGen2 BLe (arbitrarySized 1) (arbitrarySized 1) in
           let bnot_gen := liftGen BNot (gen_bexp_func n') in
           let band_gen := liftGen2 BAnd (gen_bexp_func n') (gen_bexp_func n')
           in
           oneOf [ beq_gen ; ble_gen ; bnot_gen ; band_gen ]
         end
  |}.

(* Sample (@arbitrary bexp _). *)

(** ** com **)

Derive Arbitrary for com.
Derive Show for com.

Instance gen_seq_and_assgn_com `{Gen id} `{Gen aexp} `{Gen bexp} : GenSized com :=
  {| arbitrarySized :=
       fix com_gen_func n :=
         match n with
         | 0 => liftGen2 CAss arbitrary arbitrary
         | S n' =>
           let gen := com_gen_func n' in
           liftGen2 CSeq gen gen
         end
  |}.

(*
Instance gen_if_com `{Gen id} `{Gen aexp} `{Gen bexp} : GenSized com :=
  {| arbitrarySized :=
       fix com_gen_func n :=
         match n with
         | 0 => freq [(2, returnGen CSkip) ;
                       (6, liftGen2 CAss arbitrary arbitrary)]
         | S n' =>
           let gen := com_gen_func n' in
           oneOf [liftGen3 CIf arbitrary gen gen; liftGen2 CSeq gen gen]
         end
  |}.
 *)

(** EX: Write a generator that generates only IF-THEN-ELSE ... *)

(* Sample (@arbitrarySized com gen_if_com 2). *)



