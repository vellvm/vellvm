Require Import Vellvm.Maps Vellvm.Imp.

Require Import compcert.lib.Integers.

Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Require Import List ZArith.
Import ListNotations.
Require Import String.


(* i64 *)
Definition show_int64 n := show_int (Int64.signed n).
Instance show__int64 : Show int64 := {| show := show_int64 |}.
Definition gen_i64_func (n : nat) :=
  let genZ := @arbitrarySized Z genZSized n in
  let symmetric_int64_gen := bindGen genZ (fun z => returnGen (Int64.repr z)) in
  let extremities_gen := freq [(1, returnGen (Int64.repr (Int64.max_signed)));
                               (1, returnGen (Int64.repr (Int64.min_signed)))] in
  freq [(9, symmetric_int64_gen); (1, extremities_gen)].

Instance gen_i64 : GenSized int64 := {| arbitrarySized := gen_i64_func |}.

Definition test_i64_gen := gen_i64_func 10.

Instance shrink_i64 : Shrink int64 :=
  {| shrink n := [Int64.repr 0%Z;
                  Int64.repr (Int64.max_signed); 
                  Int64.repr (Int64.min_signed)] |}.

(* Id *)
Derive Show for id.

Definition idX := Id "X".
Definition idY := Id "Y".
Definition idZ := Id "Z".
Definition idW := Id "W".

Definition test_id_gen := elems [idX; idY; idZ; idW].
Definition test_id_gen_restricted :=
  freq [(6, returnGen idX) ; (4, returnGen idY)].

Instance gen_id : Gen id := {| arbitrary := test_id_gen |}.

Instance shrink_id : Shrink id := {| shrink := fun _ => [] |}.

(* State *)

Definition show_state_func (st : state) : string :=
  "W = " ++ (show_int64 (st idW)) ++ ", " ++
  "X = " ++ (show_int64 (st idX)) ++ ", " ++
  "Y = " ++ (show_int64 (st idY)) ++ ", " ++
  "Z = " ++ (show_int64 (st idZ)) ++ ", ".

Instance show_state: Show state := {| show := show_state_func |}.

Fixpoint gen_state_func (num_gen : G int64) (id_gen : G id) (n : nat) : G state :=
  match n with
  | 0 => returnGen empty_state
  | S n' =>
    bindGen id_gen (fun id =>
    bindGen num_gen (fun val => 
    bindGen (gen_state_func num_gen id_gen n')
            (fun st =>
               returnGen (t_update st id val))))
  end.

Instance gen_state : GenSized state :=
  {| arbitrarySized := gen_state_func test_i64_gen test_id_gen |}.

Definition test_state_gen := gen_state_func test_i64_gen test_id_gen 5.
Sample test_state_gen.

Instance shrink_state : Shrink state :=
  {| shrink := fun _ => [] |}.


(**** Arithmetic Expressions ****)

Fixpoint show_aexp_func (a : aexp) : string :=
  match a with
  | ANum n => "ANum " ++ (show_int64 n)
  | AId ident =>
    match ident with
    | Id name => name
    end
  | APlus a1 a2 => "(" ++ (show_aexp_func a1) ++ " + " ++
                       (show_aexp_func a2) ++ ")"
  | AMinus a1 a2 => "(" ++ (show_aexp_func a1) ++ " - " ++
                        (show_aexp_func a2) ++ ")"
  | AMult a1 a2 => "(" ++ (show_aexp_func a1) ++ " * " ++
                        (show_aexp_func a2) ++ ")"
  end.

Instance show_aexp : Show aexp := {| show := show_aexp_func |}.

Fixpoint gen_aexp_func (i64_gen : G int64) (id_gen: G id) (n : nat) : G aexp :=
  match n with
  | 0 => liftGen ANum i64_gen
  | S n' =>
    let var_gen := (liftGen AId id_gen) in
    let plus_gen := (liftGen2 APlus
                              (gen_aexp_func i64_gen id_gen n')
                              (gen_aexp_func i64_gen id_gen n')) in
    let minus_gen := (liftGen2 AMinus
                                  (gen_aexp_func i64_gen id_gen n')
                                  (gen_aexp_func i64_gen id_gen n')) in
    let mult_gen := (liftGen2 AMult
                                 (gen_aexp_func i64_gen id_gen n')
                                 (gen_aexp_func i64_gen id_gen n'))
    in 
    (* oneOf [var_gen; plus_gen; minus_gen; mult_gen; liftGen ANum i64_gen] *)
    oneOf [var_gen; plus_gen; mult_gen; liftGen ANum i64_gen]
  end.

Fixpoint gen_simple_aexp_func (i64_gen : G int64) (id_gen : G id) (n : nat) : G aexp :=
  match n with
  | 0 => liftGen ANum i64_gen
  | S n' =>
    let plus_gen := (liftGen2 APlus
                              (liftGen AId id_gen)
                              (gen_simple_aexp_func i64_gen id_gen n')) in
    plus_gen
  end.

Definition test_aexp_gen := gen_aexp_func test_i64_gen test_id_gen 3.

Derive Arbitrary for aexp.
Sample (@arbitrarySized aexp genSaexp 4).

(**** Boolean expressions ****)

Fixpoint show_bexp_func (b : bexp) : string :=
  match b with
  | BTrue => "true" 
  | BFalse => "false"
  | BEq a1 a2 => (show_aexp_func a1) ++ " = " ++ (show_aexp_func a2)
  | BLe a1 a2 => (show_aexp_func a1) ++ " <= " ++ (show_aexp_func a2)
  | BNot b => "~(" ++ (show_bexp_func b) ++ ")"
  | BAnd b1 b2 => (show_bexp_func b1) ++ " /\ " ++ (show_bexp_func b2)
  end.

Instance show_bexp : Show bexp := {| show := show_bexp_func |}.

Fixpoint gen_bexp_func (aexp_sized_gen : nat -> G aexp) (n : nat) : G bexp :=
  match n with
  | 0 => elems [BTrue ; BFalse]
  | S n' =>
    let beq_gen := liftGen2 BEq (aexp_sized_gen n) (aexp_sized_gen n) in
    let ble_gen := liftGen2 BLe (aexp_sized_gen n) (aexp_sized_gen n) in
    let bnot_gen := liftGen BNot (gen_bexp_func aexp_sized_gen n') in
    let band_gen := liftGen2 BAnd (gen_bexp_func aexp_sized_gen n') 
                                  (gen_bexp_func aexp_sized_gen n')
    in
       oneOf [ beq_gen ; ble_gen ; bnot_gen ; band_gen ]
  end.

Definition test_bexp_gen := gen_bexp_func (gen_aexp_func test_i64_gen test_id_gen) 3.

Derive Arbitrary for bexp.

(**** Commands ****)

Fixpoint show_com_func (c : com) : string :=
  match c with
  | CSkip => "Skip"
  | x ::= a => match x with | Id ident => ident ++ " := " ++ (show_aexp_func a) end
  | CSeq c1 c2 => (show_com_func c1) ++ ";" ++ newline ++ (show_com_func c2)
  | CIf b c1 c2 => "If (" ++ (show_bexp_func b) ++ ") then "
                          ++ (show_com_func c1) ++ " else "
                          ++ (show_com_func c2) ++ " endIf"
  | CWhile b c => "While (" ++ (show_bexp_func b) ++ ") do "
                            ++ (show_com_func c) ++ " endWhile"
  end.

Instance show_com : Show com := {| show := show_com_func |}.
 
Fixpoint com_gen_func 
         (id_gen : G id)
         (aexp_gen : G aexp) (bexp_gen : G bexp) (n : nat) : G com :=
  match n with
  | 0 => freq [(2, returnGen CSkip) ; (6, liftGen2 CAss id_gen aexp_gen)]
  | S n' =>
    let gen := com_gen_func id_gen aexp_gen bexp_gen n' in
    oneOf [liftGen3 CIf bexp_gen gen gen;
             liftGen2 CWhile bexp_gen gen; liftGen2 CSeq gen gen]
  end.

Fixpoint com_if_gen_func 
         (id_gen : G id)
         (aexp_gen : G aexp) (bexp_gen : G bexp) (n : nat) : G com :=
  match n with
  | 0 => frequency (returnGen CSkip)
                  [(2, returnGen CSkip) ; (6, liftGen2 CAss id_gen aexp_gen)]
  | S n' =>
    let gen := com_gen_func id_gen aexp_gen bexp_gen n' in
    oneOf [liftGen3 CIf bexp_gen gen gen; liftGen2 CSeq gen gen]
  end.

Derive Arbitrary for com.

Definition test_com_gen n :=
  let aexp_sized_gen := gen_aexp_func test_i64_gen test_id_gen in
  let aexp_gen := aexp_sized_gen 3 in
  (* let aexp_gen := simple_aexp_gen_func (choose (0, 5)) test_id_gen 3 in *)
  let bexp_gen := gen_bexp_func aexp_sized_gen 3 in
  com_gen_func test_id_gen aexp_gen bexp_gen n.