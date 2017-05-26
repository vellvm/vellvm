Require Import Vellvm.Maps Vellvm.Imp.
Require Import Vellvm.CompilerProp.

Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Require Import List ZArith.
Import ListNotations.
Require Import String.


Instance state_shrinker : Shrink state :=
  {| shrink := fun _ => [] |}.

Derive Show for id.

Definition idX := Id "X".
Definition idY := Id "Y".
Definition idZ := Id "Z".
Definition idW := Id "W".

Definition test_id_gen := elems [idX; idY; idZ; idW].
Definition test_id_gen_restricted :=
  frequency (returnGen idX) [(6, returnGen idX) ; (4, returnGen idY)].

Instance id_gen : Gen id := {| arbitrary := test_id_gen |}.


Definition show_state_func (st : state) : string :=
  "W = " ++ (show_nat (st idW)) ++ ", " ++
  "X = " ++ (show_nat (st idX)) ++ ", " ++
  "Y = " ++ (show_nat (st idY)) ++ ", " ++
  "Z = " ++ (show_nat (st idZ)) ++ ", ".

Instance show_state: Show state := {| show := show_state_func |}.

Fixpoint state_gen_func (num_gen : G nat) (id_gen : G id) (n : nat) : G state :=
  match n with
  | 0 => returnGen empty_state
  | S n' =>
    bindGen id_gen (fun id =>
    bindGen num_gen (fun val => 
    bindGen (state_gen_func num_gen id_gen n')
            (fun st =>
               returnGen (t_update st id val))))
  end.

Definition test_nat_gen := choose (1, 10).

Definition test_state_gen := state_gen_func test_nat_gen test_id_gen 5.
Sample test_state_gen.

Instance state_gen : GenSized state :=
  {| arbitrarySized := state_gen_func test_nat_gen test_id_gen |}.

Instance shrink_id : Shrink id := {| shrink := fun _ => [] |}.


(**** Arithmetic Expressions ****)

Fixpoint show_aexp_func (a : aexp) : string :=
  match a with
  | ANum n => "ANum " ++ (show_nat n)
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

Fixpoint aexp_gen_func (num_gen : G nat) (id_gen: G id) (n : nat) : G aexp :=
  match n with
  | 0 => liftGen ANum num_gen
  | S n' =>
    let var_gen := (liftGen AId id_gen) in
    let plus_gen := (liftGen2 APlus
                              (aexp_gen_func num_gen id_gen n')
                              (aexp_gen_func num_gen id_gen n')) in
    let minus_gen := (liftGen2 AMinus
                                  (aexp_gen_func num_gen id_gen n')
                                  (aexp_gen_func num_gen id_gen n')) in
    let mult_gen := (liftGen2 AMult
                                 (aexp_gen_func num_gen id_gen n')
                                 (aexp_gen_func num_gen id_gen n'))
    in 
       oneOf [var_gen; plus_gen; minus_gen; mult_gen; liftGen ANum num_gen]
  end.

Fixpoint simple_aexp_gen_func (num_gen : G nat) (id_gen : G id) (n : nat) : G aexp :=
  match n with
  | 0 => liftGen ANum num_gen
  | S n' =>
    let plus_gen := (liftGen2 APlus
                              (liftGen AId id_gen)
                              (aexp_gen_func num_gen id_gen n')) in
    plus_gen
  end.


Fixpoint shrink_aexp_func (a : aexp) : list aexp :=
  let shrink_helper op a1 a2 :=
      [a1] ++ [a2]
           ++ (map (fun a2' => op a1 a2') (shrink_aexp_func a2))
           ++ (map (fun a1' => op a1' a2) (shrink_aexp_func a1))
  in
  match a with
  | ANum n => [] 
  | AId x => []
  | APlus a1 a2 => shrink_helper APlus a2 a2
  | AMinus a1 a2 => shrink_helper AMinus a2 a2
  | AMult a1 a2 => shrink_helper AMult a2 a2
  end.

                   
Instance aexp_shrinker : Shrink aexp :=
  {| shrink := shrink_aexp_func |}.


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

Fixpoint bexp_gen_func (aexp_sized_gen : nat -> G aexp) (n : nat) : G bexp :=
  match n with
  | 0 => elems [BTrue ; BFalse]
  | S n' =>
    let beq_gen := liftGen2 BEq (aexp_sized_gen n) (aexp_sized_gen n) in
    let ble_gen := liftGen2 BLe (aexp_sized_gen n) (aexp_sized_gen n) in
    let bnot_gen := liftGen BNot (bexp_gen_func aexp_sized_gen n') in
    let band_gen := liftGen2 BAnd (bexp_gen_func aexp_sized_gen n') 
                                  (bexp_gen_func aexp_sized_gen n')
    in
       oneOf [ beq_gen ; ble_gen ; bnot_gen ; band_gen ]
  end.

Fixpoint shrink_bexp_func (b : bexp) : list bexp :=
  match b with
  | BTrue | BFalse => []
  | BEq a1 a2
  | BLe a1 a2 => [BTrue ; BFalse]
                   ++ (map (fun a1' => BEq a1' a2) (shrink_aexp_func a1))
                   ++ (map (fun a2' => BEq a1 a2') (shrink_aexp_func a2))
  | BNot b => [BTrue ; BFalse] ++ (map (fun b' => BNot b') (shrink_bexp_func b))
  | BAnd b1 b2 =>
    [BTrue ; BFalse] ++ (map (fun b1' => BAnd b1' b2) (shrink_bexp_func b1))
                    ++ (map (fun b2' => BAnd b1 b2') (shrink_bexp_func b2))
  end.

Instance bexp_shrinker : Shrink bexp :=
  {| shrink := shrink_bexp_func |}.


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
  | 0 => frequency (returnGen CSkip)
                  [(2, returnGen CSkip) ; (6, liftGen2 CAss id_gen aexp_gen)]
  | S n' =>
    let gen := com_gen_func id_gen aexp_gen bexp_gen n' in
    oneOf [liftGen3 CIf bexp_gen gen gen;
             liftGen2 CWhile bexp_gen gen; liftGen2 CSeq gen gen]
  end.




Instance com_gen : GenSized com := 
  {| arbitrarySized n :=
       let aexp_sized_gen := aexp_gen_func test_nat_gen test_id_gen in
       (* let aexp_gen := aexp_sized_gen 3 in *)
       let aexp_gen := simple_aexp_gen_func (choose (0, 5)) test_id_gen 3 in
       let bexp_gen := bexp_gen_func aexp_sized_gen 3 in
       com_gen_func test_id_gen aexp_gen bexp_gen n |}.

Fixpoint shrink_com_func
         (shrink_aexp : aexp -> list aexp)
         (shrink_bexp : bexp -> list bexp)
         (c : com) : list com :=
  let rec_shrink := shrink_com_func shrink_aexp shrink_bexp in
  match c with
  | CSkip => []
  | x ::= a => map (fun a' => CAss x a') (shrink_aexp a)
  | CSeq c1 c2 => [c1] ++ [c2]
                       ++ (map (fun c2' => CSeq c1 c2') (rec_shrink c2))
                       ++ (map (fun c1' => CSeq c1' c2) (rec_shrink c1))
  | CWhile b c => let shrunk_b_list := shrink_bexp b in
                  (map (fun b' => CWhile b' c) shrunk_b_list)
                    ++ (map (fun c' => CWhile b c') (rec_shrink c))
                    ++ [c] 
  | CIf b c1 c2 =>
    [c1] ++ [c2]
         ++ (map (fun b' => CIf b' c1 c2) (shrink_bexp b))
         ++ (map (fun c1' => CIf b c1' c2) (rec_shrink c1))
         ++ (map (fun c2' => CIf b c1 c2) (rec_shrink c2))
  end.


Require Import Nat.

Fixpoint fold_direct_constants (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId x => AId x
  | APlus a1 a2 =>
    match fold_direct_constants a1, fold_direct_constants a2 with
    | ANum n1, ANum n2 => (*!*) ANum (n1 + n2) (*! ANum (n1 + n1) *)
    | a1', a2' => APlus a1' a2'
    end
  | AMinus a1 a2 =>
    match fold_direct_constants a1, fold_direct_constants a2 with
    | ANum n1, ANum n2 => ANum (n1 - n2)
    | a1', a2' => AMinus a1' a2'
    end 
  | AMult a1 a2 =>
    match fold_direct_constants a1, fold_direct_constants a2 with
    | ANum n1, ANum n2 => ANum (n1 * n2)
    | ANum n1, a2' => if eqb n1 0 then ANum 0 else AMult (ANum n1) a2'
    | a1', ANum n2 => if eqb n2 0 then ANum 0 else AMult a1' (ANum n2)
    | a1', a2' => AMult a1' a2'
    end
  end.


Definition test_aexp1 :=
  AMinus (ANum 7)
         (AMult 
            (AMinus (ANum 4) (ANum 1))
            (AMinus (ANum 1) (ANum 7))).

Compute (fold_direct_constants test_aexp1).

Definition test_aexp2 :=
  AMinus (AMult (APlus (ANum 4) (ANum 7)) (AId (Id "Z"))) (ANum 2).

Compute (fold_direct_constants test_aexp2).


Fixpoint fold_constants_for_bool (b : bexp) :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 =>
    let a1' := fold_direct_constants a1 in
    let a2' := fold_direct_constants a2 in
    match a1', a2' with
    | ANum n1, ANum n2 => if eqb n1 n2 then BTrue else BFalse
    | _, _ => BEq a1 a2
    end
  | BLe a1 a2 =>
    let a1' := fold_direct_constants a1 in
    let a2' := fold_direct_constants a2 in
    match a1', a2' with
    | ANum n1, ANum n2 => if leb n1 n2 then BTrue else BFalse
    | _, _ => BLe a1' a2'
    end
  | BNot b => let b' := fold_constants_for_bool b in
              match b' with
              | BTrue => BFalse
              | BFalse => BTrue
              | _ => b'
              end
  | BAnd b1 b2 =>
    let b1' := fold_constants_for_bool b1 in
    let b2' := fold_constants_for_bool b2 in
    match b1', b2' with
    | BTrue, BTrue => BTrue
    | _, BFalse | BFalse, _ => BFalse
    | _, _ => BAnd b1' b2'
    end
  end.


Fixpoint fold_constants_and_clear_deadcode (c : com) : com :=
  match c with
  | CSkip => c
  | x ::= a => CAss x (fold_direct_constants a)
  | c1 ;; c2 =>
    let c1' := fold_constants_and_clear_deadcode c1 in
    let c2' := fold_constants_and_clear_deadcode c2 in
    match c1', c2' with
    | CSkip, CSkip => CSkip
    | CSkip, c2' => c2'
    | c1', CSkip => c1'
    | _, _ => CSeq c1' c2'
    end
  | CIf b c1 c2 =>
    let b' := fold_constants_for_bool b in
    match b' with
    | BTrue => fold_constants_and_clear_deadcode c1 
    | BFalse => fold_constants_and_clear_deadcode c2
    | _ => CIf b'
               (fold_constants_and_clear_deadcode c1)
               (fold_constants_and_clear_deadcode c2)
    end
  | CWhile b c =>
    let b' := fold_constants_for_bool b in
    match b' with
    | BFalse => CSkip
    | _ => CWhile b' (fold_constants_and_clear_deadcode c)
    end
  end.

Fixpoint shrink_com_with_constant_folding_func
         (shrink_aexp : aexp -> list aexp)
         (shrink_bexp : bexp -> list bexp)
         (c : com) : list com :=
  let rec_shrink := shrink_com_with_constant_folding_func shrink_aexp shrink_bexp in  
  match c with
  | CSkip => []
  | x ::= a =>
          let folded_a := fold_direct_constants a in
          map (fun a' => x ::= a') (shrink_aexp folded_a)
              (* ++ (map (fun a' => x ::= a') (shrink_aexp a)) *)
  | CSeq c1 c2 => []
  | CWhile b c =>
    let clean_b := fold_constants_for_bool b in
    let shrunk_b_list := shrink_bexp clean_b in
    (map (fun b' => CWhile b' c) shrunk_b_list)
      ++ (map (fun c' => CWhile clean_b c') (rec_shrink c))
      ++ [c] 
  | CIf b c1 c2 =>
    let clean_b := fold_constants_for_bool b in
    [c1] ++ [c2]
         ++ (map (fun b' => CIf b' c1 c2) (shrink_bexp clean_b))
         ++ (map (fun c1' => CIf clean_b c1' c2) (rec_shrink c1))
         ++ (map (fun c2' => CIf clean_b c1 c2) (rec_shrink c2))
  end.


Instance com_shrinker : Shrink com :=
  {| shrink := shrink_com_with_constant_folding_func shrink_aexp_func shrink_bexp_func |}.


(* Example program that fails imp_compiler_correct here:
Eample prog1 := X ::= APlus (AId W) (AId W).
*)

(*
QuickChick (forAll arbitrary
                   (fun prog => let (res_string, res_val) := imp_compiler_correct_aux prog in
                             res_val)).
*)

Definition result1 := imp_compiler_correct_aux prog1.
(* Recursive Extraction result1.  *)
(* Eval vm_compute in (imp_compiler_correct_aux prog1). *)