From Coq Require Import
     Arith
     Lia
     Lists.List
     Strings.String
     ZArith.

From Vellvm Require Import
     Syntax.
From Imp2Vir Require Import Fin.

Import ListNotations.

Require Import Vec.

Open Scope Z_scope.

Section CvirCombinators.

Record cvir (n_in n_out : nat) : Type := {
   n_int : nat;
   blocks : forall
     (v_in : Vec.t raw_id n_in)
     (v_out : Vec.t raw_id n_out)
     (v_int : Vec.t raw_id n_int),
     list (block typ);
                                      }.

 (* Given a blocks, returns the corresponding CVIR *)
Definition mk_cvir
  {n_in n_out n_int : nat}
  (blocks : forall
    (v_in : Vec.t raw_id n_in)
    (v_out : Vec.t raw_id n_out)
    (v_int : Vec.t raw_id n_int),
    list (block typ)
  ) :
  cvir n_in n_out :=
  {|
    n_int := n_int;
    blocks := blocks
  |}.

Arguments n_int {_} {_}.
Arguments blocks {_} {_}.


(** Basic CVIR *)

(* Take a code (ie. list of instructions) and create a simple CVIR with 1 input
and 1 output (inconditional branch) *)
Definition block_cvir (c : code typ) : cvir 1 1 :=
  mk_cvir (fun
    (vi : Vec.t raw_id 1)
    (vo : Vec.t raw_id 1)
    (vt : Vec.t raw_id 0)
    => [mk_block (Vec.hd vi) List.nil c (TERM_Br_1 (hd vo)) None]
  ).

(* Take a code (ie. list of instructions) and an expression, and create a simple
 CVIR with 1 input and 2 outputs (conditional branch on e) *)
Definition branch_cvir (c : code typ) (e : texp typ) : cvir 1 2 :=
  mk_cvir (fun
    (vi : Vec.t raw_id 1)
    (vo : Vec.t raw_id 2)
    (vt : Vec.t raw_id 0)
    => [mk_block (Vec.hd vi) (List.nil) c (TERM_Br e (Vec.hd vo) (Vec.hd (Vec.tl vo))) None]
  ).

(* Take a code (ie. list of instructions) and an expression, and create a simple
 CVIR with 1 input and no output (block returns e) *)
Definition ret_cvir (c : code typ) (e : texp typ) : cvir 1 0 :=
  mk_cvir (fun vi vo (vt : Vec.t raw_id 0) =>
    [mk_block (Vec.hd vi) List.nil c (TERM_Ret e) None]
  ).

(* Take a code (ie. list of instructions) and an expression, and create a simple
 CVIR with 1 input and no output (block returns void) *)
Definition ret_void_cvir (c : code typ) : cvir 1 0 :=
  mk_cvir (fun vi vo (vt : Vec.t raw_id 0) =>
    [mk_block (Vec.hd vi) List.nil c (TERM_Ret_void) None]
  ).

(** Combinators over CVIR *)


(* Taking 2 cvir as input, create a new cvir concanating inputs and ouputs
// similar to app_asm in itree tutorial *)
Definition merge_cvir
           {ni1 no1 ni2 no2 : nat}
           (b1: cvir ni1 no1)
           (b2: cvir ni2 no2) :
  cvir (ni1+ni2) (no1+no2) :=
  mk_cvir (fun vi vo vt =>
    let '(li,ri) := Vec.splitat ni1 vi in
    let '(lo,ro) := Vec.splitat no1 vo in
    let '(lt,rt) := Vec.splitat (n_int b1) vt in
    (blocks b1 li lo lt) ++ (blocks b2 ri ro rt)).

(* Reordering of the vectors *)

Definition sym_i_cvir {ni1 ni2 ni3 no : nat} (b : cvir (ni1 + (ni2 + ni3)) no) :
  cvir (ni1 + (ni3 + ni2)) no :=
  mk_cvir (fun vi vo (vt : Vec.t raw_id (n_int b)) =>
    blocks b (sym_vec vi) vo vt
  ).

Definition sym_o_cvir {ni no1 no2 no3 : nat} (b : cvir ni (no1 + (no2 + no3))) :
  cvir ni (no1 + (no3 + no2)) :=
  mk_cvir (fun vi vo (vt : Vec.t raw_id (n_int b)) =>
    blocks b vi (sym_vec vo) vt
  ).

Definition cast_i_cvir {ni ni' no : nat} (b : cvir ni no) (H : ni = ni') : cvir ni' no :=
  mk_cvir (fun vi vo (vt : Vec.t raw_id (n_int b)) =>
    blocks b (Vec.cast vi (eq_sym H)) vo vt
  ).

Definition cast_o_cvir {ni no no' : nat} (b : cvir ni no) (H : no = no') : cvir ni no' :=
  mk_cvir (fun vi vo (vt : Vec.t raw_id (n_int b)) =>
    blocks b vi (Vec.cast vo (eq_sym H)) vt
          ).

(* NOTE (vi=(0,1,2,3,4,5), i = 4) => (vi->(4,0,1,2,3,5)) *)
(* Bring the i-th input at the head of the input vector *)
Program Definition focus_input_cvir {ni no : nat} (b : cvir ni no) (i : Fin.fin ni) : cvir ni no :=
  let b := cast_i_cvir b (_ : ni = proj1_sig i + (1 + (ni - proj1_sig i - 1)))%nat in
  let b := sym_i_cvir b in
  let b := cast_i_cvir b (_ : _ = 0 + ((ni - 1) + 1))%nat in
  let b := sym_i_cvir b in
  cast_i_cvir b (_ : _ = ni).
Next Obligation.
  destruct i.
  simpl.
  lia.
Defined.
Next Obligation.
  destruct i.
  simpl.
  lia.
Defined.
Next Obligation.
  destruct ni; destruct i ; lia.
Defined.


(* Bring the i-th output at the head of the output vector *)
Program Definition focus_output_cvir {ni no : nat} (b : cvir ni no) (o : Fin.fin no) : cvir ni no :=
  let b := cast_o_cvir b (_ : no = proj1_sig o + (1 + (no - proj1_sig o - 1)))%nat in
  let b := sym_o_cvir b in
  let b := cast_o_cvir b (_ : _ = 0 + ((no - 1) + 1))%nat in
  let b := sym_o_cvir b in
  cast_o_cvir b (_ : _ = no).
Next Obligation.
  destruct o.
  simpl.
  lia.
Defined.
Next Obligation.
  destruct o.
  simpl.
  lia.
Defined.
Next Obligation.
  destruct no ; [ destruct o |] ; lia.
Defined.

(* Connect the fist input and the first output of a CVIR and internalize them *)
Definition loop_cvir {ni no : nat} (b : cvir (S ni) (S no)) : cvir ni no :=
  mk_cvir (fun vi vo vt =>
    let '(newint,vt) := Vec.uncons vt in
    (blocks b) (newint :: vi)%vec (newint :: vo)%vec vt
  ).

(* wrapper for loop_cvir *)
Definition loop_cvir' {ni no ni' no' : nat} (b : cvir ni no)
  (Heqi : ni = S ni') (Heqo : no = S no') :
  cvir ni' no' :=
  loop_cvir (cast_o_cvir (cast_i_cvir b Heqi) Heqo).


(* Connect the first input of b2 to the first output of b1 *)
Program Definition seq_cvir {ni1 no1 ni2 no2 : nat}
  (b1 : cvir ni1 (S no1))
  (b2: cvir (S ni2) no2) :
  cvir (ni1+ni2) (no1+no2) :=
  (* firstly, merge b1 and b2 *)
  let b := merge_cvir b1 b2 in
  (* bring the first output of b2 at the first place of b *)
  let b := focus_input_cvir b (fi' ni1) in
  (* connect the first input of b (ie. 1st input of b2)
     to the first output of b (ie. 1st ouput of b1) *)
  loop_cvir' b _ _.
Next Obligation.
  apply Nat.lt_add_pos_r.
  apply Nat.lt_0_succ.
Defined.

(* Connect the first output of b to its first input, and internalize the only
the ouput *)
Definition loop_cvir_open {ni no : nat} (b : cvir (S ni) (S no)) : cvir (S ni) no :=
  mk_cvir (fun vi vo vt =>
    (blocks b) vi (hd vi :: vo)%vec vt).


(* Merge the first output with the second one *)
Definition join_cvir {ni no : nat} (b : cvir ni (S (S no))) : cvir ni (S no) :=
  mk_cvir (fun vi vo vt =>
    let o := Vec.hd vo in
    (blocks b) vi (o :: vo)%vec vt).

(* Remove the inputs of a cvir (without output)... Is that useful ? *)
Definition close_cvir {ni} (b : cvir ni 0) : cvir 0 0 :=
  mk_cvir (fun vi vo vt =>
    let '(vi,vt) := Vec.splitat ni vt in
    (blocks b) vi vo vt).

(*
Definition cond_cvir {ni1 no1 ni2 no2 : nat}
  (b1 : cvir (S ni1) (S no1)) (b2: cvir (S ni2) (S no2)) (e : texp typ) :
  cvir (ni1+ni2) (no1+no2) :=
    let cond_ir := branch_cvir [] e in
    let branchs_ir := join_cvir b1 b2 in
    seq_cvir cond_ir branchs_ir
    join_cvir (cast_o_cvir (seq_cvir (seq_cvir cond_ir b1) b2) _).
 *)

Definition fnbody := (block typ * list (block typ))%type.
Definition program := toplevel_entity typ fnbody.

Definition entry_block : block typ :=
  mk_block (Anon 0) List.nil List.nil (TERM_Br_1 (Anon 1)) None.

End CvirCombinators.

Arguments n_int {_} {_}.
Arguments blocks {_} {_}.
