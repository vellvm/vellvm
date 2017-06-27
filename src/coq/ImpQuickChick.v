Require Import Vellvm.Maps Vellvm.Imp.

Require Import compcert.lib.Integers.

Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Require Import List ZArith.
Import ListNotations.
Require Import String.

(* i64 *)

Definition show_int64 (n : int64) := show_int (Int64.signed n).

Instance show_i64 : Show int64 := {| show := show_int64 |}.


Instance gen_large_i64 : GenSized int64 :=
  {| arbitrarySized n :=
       let n' := if leb n 1000 then n else 1000 in
       let genZ := (let z := Z.of_nat n' in choose (900, 1000)%Z) in
       bindGen genZ (fun z => returnGen (Int64.repr z))
  |}.

Instance gen_i64 : GenSized int64 :=
  {| arbitrarySized n := 
       let genZ := (let z := Z.of_nat n in choose (-z, z)%Z) in
       bindGen genZ (fun z => returnGen (Int64.repr z)) 
  |}.

Instance gen_nonneg_i64 : GenSized int64 :=
  {| arbitrarySized n := 
       let genZ := (let z := Z.of_nat n in choose (0, z)%Z) in
       bindGen genZ (fun z => returnGen (Int64.repr z))
  |}.

Instance gen_small_nonneg_i64 : GenSized int64 :=
  {| arbitrarySized n :=
       let n' := if leb n 10 then n else 10 in
       let genZ := (let z := Z.of_nat n' in choose (0, z)%Z) in
       bindGen genZ (fun z => returnGen (Int64.repr z))
  |}.


(*
Instance gen_i64_with_extremes : GenSized int64 :=
  {| arbitrarySized n := 
     let genZ := (let z := Z.of_nat n in choose (-z, z)%Z) in
     let symmetric_int64_gen := bindGen genZ (fun z => returnGen (Int64.repr z)) in
     let extremities_gen := freq [(1, returnGen (Int64.repr (Int64.max_signed)));
                                    (1, returnGen (Int64.repr (Int64.min_signed)))] in
     freq [(9, symmetric_int64_gen); (1, extremities_gen)] |}.
*)

Instance shrink_i64 : Shrink int64 :=
  {| shrink n := [Int64.zero; Int64.one;
                    Int64.repr (Int64.max_signed); 
                    Int64.repr (Int64.min_signed)] |}.

(* 
  We force the tester to register manually 
  when there are multiple possibilities. 
 *)
Remove Hints gen_i64 : typeclass_instances. 
Remove Hints gen_nonneg_i64 : typeclass_instances. 
Remove Hints gen_small_nonneg_i64 : typeclass_instances. 
Remove Hints gen_large_i64 : typeclass_instances. 

(* Id *)
Derive Show for id.

Definition idX := Id "X".
Definition idY := Id "Y".
Definition idZ := Id "Z".
Definition idW := Id "W".

Definition test_id_gen := elems [idX; idY; idZ; idW].
Definition test_id_gen_restricted :=
  freq [(6, returnGen idX) ; (4, returnGen idY)].

Definition test_state :=
  t_update
    (t_update
       (t_update
          (t_update empty_state idX Int64.zero)
          idY Int64.zero)
       idZ Int64.zero)
    idW Int64.zero.

Instance gen_id : Gen id := {| arbitrary := test_id_gen |}.

Instance shrink_id : Shrink id := {| shrink := fun _ => [] |}.

(* State *)

Instance show_state `{Show int64}: Show state :=
  {| show st := (
       "W = " ++ (show (st idW)) ++ ", " ++
       "X = " ++ (show (st idX)) ++ ", " ++
       "Y = " ++ (show (st idY)) ++ ", " ++
       "Z = " ++ (show (st idZ)) ++ ", ")%string
  |}.
       
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

Instance gen_state `{GenSized int64}: GenSized state :=
  {| arbitrarySized n := gen_state_func (arbitrarySized n) test_id_gen n |}.

Instance shrink_state : Shrink state :=
  {| shrink := fun _ => [] |}.

(**** Arithmetic Expressions ****)

Instance show_aexp `{Show int64} : Show aexp :=
  {| show := (
       fix show_aexp_func a :=
           match a with
           | ANum n => "ANum " ++ (show n)
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
           end)%string
  |}.

Instance gen_adhoc_aexp `{Gen int64} `{Gen id} : GenSized aexp :=
  {| arbitrarySized := 
       fix gen_aexp_func n :=
         match n with
         | 0 => liftGen ANum arbitrary
         | S n' =>
           let var_gen := (liftGen AId arbitrary) in
           let plus_gen := (liftGen2 APlus
                                     (gen_aexp_func n')
                                     (gen_aexp_func n')) in
           let minus_gen := (liftGen2 AMinus
                                      (gen_aexp_func n')
                                      (gen_aexp_func n')) in
           let mult_gen := (liftGen2 AMult
                                     (gen_aexp_func n')
                                     (gen_aexp_func n'))
           in 
           oneOf [var_gen; plus_gen; minus_gen; mult_gen; liftGen ANum arbitrary]
           (* oneOf [var_gen; plus_gen; mult_gen; liftGen ANum arbitrary] *)
         end
  |}.

Instance gen_plus_aexp `{Gen int64} `{Gen id} : GenSized aexp :=
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

Instance shr_aexp : Shrink aexp :=
  {| shrink :=
       fix shrink_aexp_func expr := 
         let shrink_binop binop a1 a2 :=
             (List.map (fun a2' => binop a1 a2') (shrink_aexp_func a2))
               ++ (List.map (fun a1' => binop a1' a2) (shrink_aexp_func a1))
               ++ [a1 ; a2] in
         match expr with
         | AId _ => []
         | ANum n => List.map ANum (shrink n)
         | APlus a1 a2 => shrink_binop APlus a1 a2
         | AMinus a1 a2 => shrink_binop AMinus a1 a2
         | AMult a1 a2 => shrink_binop AMult a1 a2
         end
  |}.

(* 
  We force the tester to register manually 
  when there are multiple possibilities. 
 *)
Existing Instance gen_i64.
Derive Arbitrary for aexp.
Remove Hints gen_i64 : typeclass_instances.

Remove Hints genSaexp : typeclass_instances.
Remove Hints gen_plus_aexp : typeclass_instances.
Remove Hints gen_adhoc_aexp : typeclass_instances.

Remove Hints shraexp : typeclass_instances.

(**** Boolean expressions ****)

Instance show_bexp `{Show aexp} : Show bexp :=
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

Instance gen_bexp_with_proportional_aexp `{GenSized aexp} : GenSized bexp :=
  {| arbitrarySized :=
       fix gen_bexp_func n :=
         match n with
         | 0 => elems [BTrue ; BFalse]
         | S n' =>
           let beq_gen := liftGen2 BEq (arbitrarySized n) (arbitrarySized n) in
           let ble_gen := liftGen2 BLe (arbitrarySized n) (arbitrarySized n) in
           let bnot_gen := liftGen BNot (gen_bexp_func n') in
           let band_gen := liftGen2 BAnd (gen_bexp_func n') (gen_bexp_func n')
           in
           oneOf [ beq_gen ; ble_gen ; bnot_gen ; band_gen ]
         end
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

Instance gen_small_bexp_small_aexp_with_high_prob `{GenSized aexp} : GenSized bexp :=
  {| arbitrarySized :=
       fix gen_bexp_func n :=
         match n with
         | 0 => elems [BTrue ; BFalse]
         | S n' => 
           let beq_gen := liftGen2 BEq (arbitrarySized 3) (arbitrarySized 3) in
           let ble_gen := liftGen2 BLe (arbitrarySized 3) (arbitrarySized 3) in
           let bnot_gen := liftGen BNot (gen_bexp_func n') in
           let band_gen := liftGen2 BAnd (gen_bexp_func n') (gen_bexp_func n')
           in
           oneOf [ returnGen BTrue; returnGen BFalse;
                     beq_gen ; ble_gen ; bnot_gen ; band_gen ]
         end
  |}.

(* 
  We force the tester to register manually 
  when there are multiple possibilities. 
 *)
Existing Instance genSaexp.
Derive Arbitrary for bexp.
Remove Hints genSaexp : typeclass_instances.

Remove Hints gen_bexp_with_proportional_aexp : typeclass_instances.
Remove Hints gen_bexp_with_small_aexp : typeclass_instances.
Remove Hints gen_small_bexp_small_aexp_with_high_prob : typeclass_instances.
Remove Hints genSbexp : typeclass_instances.

(**** Commands ****)

Derive Show for com.

Instance show_com `{Show aexp} `{Show bexp} : Show com :=
  {| show :=
       fix show_com_func c := (
         match c with
         | CSkip => "Skip"
         | x ::= a => match x with | Id ident => ident ++ " := " ++ (show a) end
               | CSeq c1 c2 => (show_com_func c1) ++ ";" ++ newline ++ (show_com_func c2)
               | CIf b c1 c2 => "If (" ++ (show b) ++ ") then "
                                      ++ (show_com_func c1) ++ " else "
                                      ++ (show_com_func c2) ++ " endIf"
               | CWhile b c => "While (" ++ (show b) ++ ") do "
                                        ++ (show_com_func c) ++ " endWhile"
         end)%string
  |}.

Instance gen_all_com `{Gen id} `{Gen aexp} `{Gen bexp} : GenSized com :=
  {| arbitrarySized :=
       fix com_gen_func n :=
         match n with
         | 0 => freq [(2, returnGen CSkip) ; (6, liftGen2 CAss arbitrary arbitrary)]
         | S n' =>
           let gen := com_gen_func n' in
           oneOf [liftGen3 CIf arbitrary gen gen;
                    liftGen2 CWhile arbitrary gen; liftGen2 CSeq gen gen]
         end
  |}.

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

(*
Instance adhoc_com_gen : GenSized com :=
  {| arbitrarySized :=
       let aexp_gen := @arbitrarySized aexp gen_aexp 3 in
       (* let aexp_gen := simple_aexp_gen_func (choose (0, 5)) test_id_gen 3 in *)
       let bexp_gen := @arbitrarySized bexp gen_bexp_with_small_aexp 3 in
       @com_gen _ aexp_gen bexp_gen
  |}.
 *)

Instance gen_while_com `{Gen aexp} `{Gen bexp} : GenSized com :=
  {| arbitrarySized :=
       fix com_gen_func n :=
         match n with
         | 0 => liftGen2 CAss arbitrary arbitrary
         | S n' =>
           let gen := com_gen_func n' in
           oneOf [liftGen2 CWhile arbitrary gen;
                    liftGen3 CIf arbitrary gen gen;
                    liftGen2 CSeq gen gen]
         end
  |}.


(* 
  We force the tester to register manually 
  when there are multiple possibilities. 
 *)
Existing Instance genSaexp.
Existing Instance genSbexp.
Derive Arbitrary for com.
Remove Hints genSaexp : typeclass_instances.
Remove Hints genSbexp : typeclass_instances.

Remove Hints gen_seq_and_assgn_com : typeclass_instances.
Remove Hints gen_all_com : typeclass_instances.
Remove Hints gen_if_com : typeclass_instances.
Remove Hints gen_while_com : typeclass_instances.
Remove Hints genScom : typeclass_instances.

(* Print Hint GenSized. *)