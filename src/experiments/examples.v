Require Import minillvm_bitwise.
Require Import block_model.
Require Import List.
Require Import CoqEqDec.
Require Import ZArith.
Require Import LTS.
Require Import Util.
Require Import Coqlib.
Import ListNotations.

Set Implicit Arguments.

Section Examples.

  Variables (block : Type) (block_eq : EqDec_eq block).
  Variable bmain : block.
  Variable main : ident.

  Definition i16 := Int_ty 16.
  Definition i32 := Int_ty 32.
  Definition i64 := Int_ty 64.
  Definition int_to_i32 i : const block := Int_c (encode_int i 32).
  Definition int_to_i64 i : const block := Int_c (encode_int i 64).

  Coercion Const : const >-> expr.
  Coercion int_to_i64 : Z >-> const.

  Definition make_prog G : prog block := 
    [((bmain, replicate Zero 32, 1%nat), main, [], G)].
  
  Definition struct1 := Struct_ty [i32; Array_ty 4 i32; i32].

  Variables (n0 n1 n2 n3 n4 n5 n6 n7 : node) (p x y z : ident).
  Hypothesis (Hnodes : distinct [n0; n1; n2; n3; n4; n5; n6; n7]).

  Definition test1 := {| Nodes := NodeSet.of_list [n0; n1; n2; n3; n4; n5]; 
    Edges := EdgeSet.of_list [(n0, Seq, n1); (n1, Seq, n2); (n2, Seq, n3);
                              (n3, Seq, n4); (n4, Seq, n5)];
    Start := n0; Exit := n5; 
    Label := fun n =>
      if eq_dec n n0 then Alloca p struct1 
      else if eq_dec n n1 then Store struct1 (Complex_c [int_to_i32 0; 
        Complex_c (map int_to_i32 [1; 2; 3; 4]); int_to_i32 5])
        (Pointer_ty struct1) (Local p)
      else if eq_dec n n2 then Gep x struct1 (Pointer_ty struct1) (Local p)
        [(i32, Const (int_to_i32 0)); (i32, Const (int_to_i32 1)); 
         (i32, Const (int_to_i32 3))]
      else if eq_dec n n3 then Load y i32 (Local x)
      else if eq_dec n n4 then Output (Local y)
      else @Br_label block |}. (* expected result: 4 *)

  Definition test2 := {| Nodes := NodeSet.of_list [n0; n1; n2; n3; n4; n5]; 
    Edges := EdgeSet.of_list [(n0, Seq, n1); (n1, Seq, n2); (n2, Seq, n3);
                              (n3, Seq, n4); (n4, Seq, n5)];
    Start := n0; Exit := n5; 
    Label := fun n =>
      if eq_dec n n0 then Alloca p struct1 
      else if eq_dec n n1 then Store struct1 (Const (Complex_c [int_to_i32 0; 
        Complex_c [int_to_i32 1; int_to_i32 2; int_to_i32 3; int_to_i32 4]; int_to_i32 5]))
        (Pointer_ty struct1) (Local p)
      else if eq_dec n n2 then Gep x struct1 (Pointer_ty struct1) (Local p)
        [(i32, Const (int_to_i32 0)); (i32, Const (int_to_i32 1)); 
         (i32, Const (int_to_i32 4))]
      else if eq_dec n n3 then Load y i32 (Local x)
      else if eq_dec n n4 then Output (Local y)
      else @Br_label block |}. (* expected result: 5 *)

  Definition test3 := {| Nodes := NodeSet.of_list [n0; n1; n2; n3; n4; n5]; 
    Edges := EdgeSet.of_list [(n0, Seq, n1); (n1, Seq, n2); (n2, Seq, n3);
                              (n3, Seq, n4); (n4, Seq, n5)];
    Start := n0; Exit := n5; 
    Label := fun n =>
      if eq_dec n n0 then Alloca p struct1 
      else if eq_dec n n1 then Store struct1 (Const (Complex_c [int_to_i32 0; 
        Complex_c [int_to_i32 1; int_to_i32 2; int_to_i32 3; int_to_i32 4]; int_to_i32 5]))
        (Pointer_ty struct1) (Local p)
      else if eq_dec n n2 then Gep x struct1 (Pointer_ty struct1) (Local p)
        [(i32, Const (int_to_i32 0)); (i32, Const (int_to_i32 1)); 
         (i32, Const (int_to_i32 (-1)))]
      else if eq_dec n n3 then Load y i32 (Local x)
      else if eq_dec n n4 then Output (Local y)
      else @Br_label block |}. (* expected result: 0 *)

  Definition test4 := {| Nodes := NodeSet.of_list [n0; n1; n2; n3; n4; n5]; 
    Edges := EdgeSet.of_list [(n0, Seq, n1); (n1, Seq, n2); (n2, Seq, n3);
                              (n3, Seq, n4); (n4, Seq, n5)];
    Start := n0; Exit := n5; 
    Label := fun n =>
      if eq_dec n n0 then Alloca p struct1 
      else if eq_dec n n1 then Store struct1 (Const (Complex_c [int_to_i32 0; 
        Complex_c [int_to_i32 1; int_to_i32 2; int_to_i32 3; int_to_i32 4]; int_to_i32 5]))
        (Pointer_ty struct1) (Local p)
      else if eq_dec n n2 then Gep x struct1 (Pointer_ty struct1) (Local p)
        [(i32, Const (int_to_i32 0)); (i32, Const (int_to_i32 1)); 
         (i32, Const (int_to_i32 5))]
      else if eq_dec n n3 then Load y i32 (Local x)
      else if eq_dec n n4 then Output (Local y)
      else @Br_label block |}. (* expected result: failure *)

  Definition test5 := {| Nodes := NodeSet.of_list [n0; n1; n2; n3; n4; n5]; 
    Edges := EdgeSet.of_list [(n0, Seq, n1); (n1, Seq, n2); (n2, Seq, n3);
                              (n3, Seq, n4); (n4, Seq, n5)];
    Start := n0; Exit := n5; 
    Label := fun n =>
      if eq_dec n n0 then Alloca p struct1 
      else if eq_dec n n1 then Store struct1 (Const (Complex_c [int_to_i32 0; 
        Complex_c [int_to_i32 1; int_to_i32 2; int_to_i32 3; int_to_i32 4]; int_to_i32 5]))
        (Pointer_ty struct1) (Local p)
      else if eq_dec n n2 then Gep x struct1 (Pointer_ty struct1) (Local p)
        [(i32, Const (int_to_i32 0)); (i32, Const (int_to_i32 1)); 
         (i32, Const (int_to_i32 (-2)))]
      else if eq_dec n n3 then Load y i32 (Local x)
      else if eq_dec n n4 then Output (Local y)
      else @Br_label block |}. (* expected result: failure *)

  Definition test6 := {| Nodes := NodeSet.of_list [n0; n1; n2; n3; n4; n5]; 
    Edges := EdgeSet.of_list [(n0, Seq, n1); (n1, Seq, n2); (n2, Seq, n3);
                              (n3, Seq, n4); (n4, Seq, n5)];
    Start := n0; Exit := n5; 
    Label := fun n =>
      if eq_dec n n0 then Alloca p struct1 
      else if eq_dec n n1 then Store struct1 (Const (Complex_c [int_to_i32 0; 
        Complex_c [int_to_i32 1; int_to_i32 2; int_to_i32 3; int_to_i32 4]; int_to_i32 5]))
        (Pointer_ty struct1) (Local p)
      else if eq_dec n n2 then Gep x struct1 (Pointer_ty struct1) (Local p)
        [(i32, Const (int_to_i32 0)); (i32, Const (int_to_i32 2))]
      else if eq_dec n n3 then Load y i32 (Local x)
      else if eq_dec n n4 then Output (Local y)
      else @Br_label block |}. (* expected result: 5 *)

  Definition test_cast := 
 {| Nodes := NodeSet.of_list [n0; n1; n2; n3; n4; n5; n6]; 
    Edges := EdgeSet.of_list [(n0, Seq, n1); (n1, Seq, n2); (n2, Seq, n3);
                              (n3, Seq, n4); (n4, Seq, n5); (n5, Seq, n6)];
    Start := n0; Exit := n6;
    Label := fun n =>
      if eq_dec n n0 then Alloca p struct1 
      else if eq_dec n n1 then Store struct1 (Complex_c [int_to_i32 0; 
        Complex_c [int_to_i32 1; int_to_i32 2; int_to_i32 3; int_to_i32 4]; int_to_i32 5])
        (Pointer_ty struct1) (Local p)
      else if eq_dec n n2 then Bitcast (Pointer_ty struct1) (Local p) 
                                       (Pointer_ty (Array_ty 12 i16))
      else if eq_dec n n3 then Gep x (Array_ty 12 i16)
        (Pointer_ty (Array_ty 12 i16)) (Local p)
        [(i32, Const (int_to_i32 0)); (i32, Const (int_to_i32 5))]
      else if eq_dec n n4 then Load y i16 (Local x)
      else if eq_dec n n5 then Output (Local y)
      else @Br_label block |}. (* expected result: 2 *)

  Fixpoint index_of {A} {A_eq : EqDec_eq A} (a : A) l : option nat :=
    match l with
    | [] => None
    | x :: rest => if eq_dec a x then Some O
                   else match index_of a rest with
                        | Some n => Some (S n)
                        | None => None
                        end
    end.

  Fixpoint make_seq nl :=
    match nl with
    | [] => EdgeSet.empty
    | n1 :: rest =>
        match rest with
        | [] => EdgeSet.empty
        | n2 :: _ => EdgeSet.add (n1, Seq, n2) (make_seq rest)
        end
    end.

  Definition list_to_graph il := 
    let nl := firstn (length il) [n0; n1; n2; n3; n4; n5; n6] ++ [n7] in
    {| Nodes := NodeSet.of_list nl; Edges := make_seq nl;
       Start := n0; Exit := n7;
       Label := fun n => match index_of n nl with
                         | Some i => nth i il (@Br_label block)
                         | None => @Br_label block
                         end |}.

  Definition add_twice := list_to_graph 
    [Assign x Add i32 (int_to_i32 5) (int_to_i32 9);
     Assign y Add i32 (Local x) (int_to_i32 15);
     Output (Local y)]. (* expected result: 29 *)

  Definition alloca1 := list_to_graph
    [Alloca x i64; Store i64 17 i64 (Local x);
     Load y i64 (Local x); Output (Local y)]. 
    (* expected result : 17 *)

  Definition alloca2 := list_to_graph
    [Alloca p i64; Store i64 17 i64 (Local p);
     Alloca x (Pointer_ty i64);
     Store (Pointer_ty i64) (Local p) (Pointer_ty i64) (Local x);
     Load y (Pointer_ty i64) (Local x); Load z i64 (Local y);
     Output (Local z)].
    (* expected result : 17 *)

  Definition br2 :=
 {| Nodes := NodeSet.of_list [n0; n1; n2; n3; n4];
    Edges := EdgeSet.of_list [(n0, Seq, n1); (n1, Seq, n2); (n2, Seq, n3);
                              (n3, Seq, n4)];
    Start := n0; Exit := n4;
    Label := fun n =>
      if eq_dec n n0 then Assign x Add i64 5 12
      else if eq_dec n n3 then Output (Local x)
      else @Br_label block |}. (* expected result: 17 *)

  Definition cbr2 :=
 {| Nodes := NodeSet.of_list [n0; n1; n2; n3; n4];
    Edges := EdgeSet.of_list [(n0, Seq, n1); (n1, T, n2); (n1, F, n3);
                              (n2, Seq, n4); (n3, Seq, n4)];
    Start := n0; Exit := n4;
    Label := fun n =>
      if eq_dec n n0 then ICmp x Slt i64 3 0
      else if eq_dec n n1 then Br_i1 (Local x)
      else if eq_dec n n2 then Output 7
      else if eq_dec n n3 then Output 9
      else @Br_label block |}. (* expected result: 9 *)

  Lemma wf_test1 : wf_CFG test1.
  Proof.
(*    constructor; unfold test1; clarify.
    - NodeSet.fsetdec.
    - NodeSet.fsetdec.
    - unfold EdgeSet.For_all; clarify.
      destruct x as ((n, t), n'); clarify.
      rewrite EdgeSet.add_spec in H; destruct H as [H | H]; clarify;
        [NodeSet.fsetdec|].
      rewrite EdgeSet.add_spec in H; destruct H as [H | H]; clarify;
        [NodeSet.fsetdec|].
      rewrite EdgeSet.add_spec in H; destruct H as [H | H]; clarify;
        [NodeSet.fsetdec|].
      rewrite EdgeSet.add_spec in H; destruct H as [H | H]; clarify;
        [NodeSet.fsetdec|].
      rewrite EdgeSet.F.empty_iff in H; contradiction H.
    - unfold instr_edges, NodeSet.For_all; simpl.
      intros n H.
      rewrite NodeSet.add_spec in H; destruct H as [H | H].*)
  Abort.

  Variables (n8 n9 n10 n11 n12 n13 n14 n15 n16 : node).
  Variables (r1 r2 r3 r5 r7 r9 : ident).

  Definition cbr :=
 {| Nodes := NodeSet.of_list [n0; n1; n2; n3; n4; n5; n6; n7; n8; n9; n10;
                              n11; n12; n13; n14; n15];
    Edges := EdgeSet.union (make_seq [n0; n1; n2; n3; n4; n5; n6]) (EdgeSet.union (EdgeSet.of_list [(n6, T, n7); (n6, F, n10)]) (EdgeSet.union (make_seq [n7; n8; n9]) (EdgeSet.union (make_seq [n10; n11; n12]) (EdgeSet.of_list [(n9, Seq, n13); (n12, Seq, n13); (n13, Seq, n14); (n14, Seq, n15)]))));
    Start := n0; Exit := n15;
    Label := fun n =>
      if eq_dec n n0 then Alloca r1 i64
      else if eq_dec n n1 then Alloca y i64
      else if eq_dec n n2 then Store i64 0 i64 (Local r1)
      else if eq_dec n n3 then Store i64 100 i64 (Local y)
      else if eq_dec n n4 then Load r2 i64 (Local y)
      else if eq_dec n n5 then ICmp r3 Ne i64 (Local r2) 0
      else if eq_dec n n6 then Br_i1 (Local r3)
      else if eq_dec n n7 then Assign r5 Add i64 42 0
      else if eq_dec n n8 then Store i64 (Local r5) i64 (Local r1)
      else if eq_dec n n10 then Assign r7 Add i64 0 0
      else if eq_dec n n11 then Store i64 (Local r7) i64 (Local r1)
      else if eq_dec n n13 then Load r9 i64 (Local r1)
      else if eq_dec n n14 then Output (Local r9)
      else @Br_label block |}. (* expected result: 42 *)

End Examples.

Parameters (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 : node).

Section Concrete.
  Definition test_prog1 := make_prog O xH
    (test1 _ n0 n1 n2 n3 n4 n5 (Pos.of_nat 1) (Pos.of_nat 2) (Pos.of_nat 3)).

  Definition test_prog2 := make_prog O xH
    (test2 _ n0 n1 n2 n3 n4 n5 (Pos.of_nat 1) (Pos.of_nat 2) (Pos.of_nat 3)).

  Definition test_prog3 := make_prog O xH
    (test3 _ n0 n1 n2 n3 n4 n5 (Pos.of_nat 1) (Pos.of_nat 2) (Pos.of_nat 3)).

  Definition test_prog4 := make_prog O xH
    (test4 _ n0 n1 n2 n3 n4 n5 (Pos.of_nat 1) (Pos.of_nat 2) (Pos.of_nat 3)).

  Definition test_prog5 := make_prog O xH
    (test5 _ n0 n1 n2 n3 n4 n5 (Pos.of_nat 1) (Pos.of_nat 2) (Pos.of_nat 3)).

  Definition cast_prog := make_prog O xH
    (test_cast _ n0 n1 n2 n3 n4 n5 n6 (Pos.of_nat 1) (Pos.of_nat 2) 
               (Pos.of_nat 3)).

  Definition add_prog := make_prog O xH
    (add_twice _ n0 n1 n2 n3 n4 n5 n6 n7 (Pos.of_nat 1) (Pos.of_nat 2)).

  Definition test_prog6 := make_prog O xH
    (test6 _ n0 n1 n2 n3 n4 n5 (Pos.of_nat 1) (Pos.of_nat 2) (Pos.of_nat 3)).

  Definition alloca_prog1 := make_prog O xH
    (alloca1 _ n0 n1 n2 n3 n4 n5 n6 n7 (Pos.of_nat 1) (Pos.of_nat 2)).

  Definition alloca_prog2 := make_prog O xH
    (alloca2 _ n0 n1 n2 n3 n4 n5 n6 n7 (Pos.of_nat 1) (Pos.of_nat 2)
             (Pos.of_nat 3) (Pos.of_nat 4)).

  Definition br_prog2 := make_prog O xH
    (br2 _ n0 n1 n2 n3 n4 (Pos.of_nat 1)).

  Definition cbr_prog2 := make_prog O xH
    (cbr2 _ n0 n1 n2 n3 n4 (Pos.of_nat 1)).

  Definition cbr_prog := make_prog O xH
    (cbr _ n0 n1 n2 n3 n4 n5 n6 n7 (Pos.of_nat 1) n8 n9 n10 n11 n12 n13 n14 n15 (Pos.of_nat 2) (Pos.of_nat 3) (Pos.of_nat 4) (Pos.of_nat 5) (Pos.of_nat 6) (Pos.of_nat 7)).

  Definition factrect :=
    [(O, replicate Zero 32, 1%nat, Pos.of_nat 1, [],
      list_to_graph n0 n1 n2 n3 n4 n5 n6 n7 [Call (Pos.of_nat 1) i64 (Pointer_c (S O, replicate Zero 32, 1%nat)) [Const (int_to_i64 _ 5)]; Output (Local (Pos.of_nat 1))]);
     (S O, replicate Zero 32, 1%nat, Pos.of_nat 2, [Pos.of_nat 1],
      {| Nodes := NodeSet.of_list [n0; n1; n2; n3; n4; n5; n6; n7];
         Edges := EdgeSet.union (EdgeSet.of_list [(n0, Seq, n1); (n1, T, n2); (n1, F, n3); (n2, Seq, n7)]) (make_seq [n3; n4; n5; n6; n7]);
    Start := n0; Exit := n7;
    Label := fun n =>
      if eq_dec n n0 then ICmp (Pos.of_nat 2) Eq i64 (Local (Pos.of_nat 1)) (int_to_i64 _ 0)
      else if eq_dec n n1 then Br_i1 (Local (Pos.of_nat 2))
      else if eq_dec n n2 then Ret i64 (int_to_i64 _ 1)
      else if eq_dec n n3 then Assign (Pos.of_nat 3) Sub i64 (Local (Pos.of_nat 1)) (int_to_i64 _ 1)
      else if eq_dec n n4 then Call (Pos.of_nat 4) i64 (Pointer_c (S O, replicate Zero 32, 1%nat)) [Local (Pos.of_nat 3)]
      else if eq_dec n n5 then Assign (Pos.of_nat 5) Mul i64 (Local (Pos.of_nat 1)) (Local (Pos.of_nat 4))
      else if eq_dec n n6 then Ret i64 (Local (Pos.of_nat 5))
      else @Br_label nat |})].

  Definition test_progs := [(add_prog, Some [29]); (test_prog6, Some [5]);
    (alloca_prog1, Some [17]); (alloca_prog2, Some [17]);
    (br_prog2, Some [17]); (cbr_prog2, Some [9]); (cbr_prog, Some [42]);
    (factrect, Some [120])].

  Instance simple_target : Target := 
    {| int_align := replicate None 8 ++ [Some (1%nat)] ++ replicate None 7 ++
       [Some (2%nat)] ++ replicate None 15 ++ [Some (4%nat)] ++ 
       replicate None 31 ++ [Some (8%nat)];
       ptr_size := 4%nat; ptr_align := 4%nat; big_endian := true |}.

  Fixpoint fresh_nat_aux l f :=
    match l with
    | [] => f
    | n :: rest => fresh_nat_aux rest (max f (S n))
    end.
  Definition fresh_nat l := fresh_nat_aux l O.

  Lemma fresh_nat_aux_spec : forall l f, (f <= fresh_nat_aux l f /\
    Forall (fun n => (n < fresh_nat_aux l f)) l)%nat.
  Proof.
    induction l; clarify; split.
    - etransitivity; [|apply IHl].
      apply Max.le_max_l.
    - specialize (IHl (max f (S a))); clarify.
      constructor.
      + eapply lt_le_trans; [|apply IHl1].
        eapply lt_le_trans; [|apply Max.le_max_r]; auto.
      + eapply Forall_impl; [|apply IHl2]; clarify.
  Qed.
  
  Lemma fresh_nat_spec : forall l, ~In (fresh_nat l) l.
  Proof.
    unfold fresh_nat; repeat intro.
    generalize (fresh_nat_aux_spec l 0); intros [_ Hlt].
    rewrite Forall_forall in Hlt; specialize (Hlt _ H); omega.
  Qed.

  Fixpoint bitwise_and v1 v2 :=
    match (v1, v2) with
    | ([], []) => Some []
    | (t1 :: rest1, t2 :: rest2) =>
        match bitwise_and rest1 rest2 with
        | Some rest' =>
            Some ((match t1 with One => t2 | _ => Zero end) :: rest')
        | None => None
        end
    | _ => None
    end.

  Fixpoint bitwise_or v1 v2 :=
    match (v1, v2) with
    | ([], []) => Some []
    | (t1 :: rest1, t2 :: rest2) =>
        match bitwise_or rest1 rest2 with
        | Some rest' =>
            Some ((match t1 with One => One | _ => t2 end) :: rest')
        | None => None
        end
    | _ => None
    end.

  Definition simple_do_op op v1 v2 :=
    let i1 := decode_0_trits v1 in let i2 := decode_0_trits v2 in
    match op with
    | Add => Some (encode_int (i1 + i2) (length v1))
    | Sub => Some (encode_int (i1 - i2) (length v1))
    | Mul => Some (encode_int (i1 * i2) (length v1))
    | Pad => Some (encode_int (let d := i1 mod i2 in if eq_dec d 0 then i1 else i1 + (i2 - d)) (length v1))
    | And => bitwise_and v1 v2
    | Or => bitwise_or v1 v2
    end.

  Definition simple_do_cmp cmp v1 v2 :=
    let i1 := decode_0_trits v1 in let i2 := decode_0_trits v2 in
    match cmp with
    | Eq => Some (if eq_dec v1 v2 then [One] else [Zero])
    | Ne => Some (if eq_dec v1 v2 then [Zero] else [One])
    | Slt => let i1 := decode_0_trits v1 in let i2 := decode_0_trits v2 in
             Some (if zlt i1 i2 then [One] else [Zero])
    end.

  Definition run_step (P : prog nat) C := 
    do_step simple_do_op simple_do_cmp P (simple_impl _ fresh_nat_spec) (fun _ => None) C.

  Definition run_prog_n (P : prog nat) n := 
    do_mem_steps simple_do_op simple_do_cmp P (simple_impl _ fresh_nat_spec) (fun _ => None)
      (Normal (xH, n0, n0, @start_env _, [], []), []) n.

  Definition run_prog P := run_prog_n P 100.
  
  Fixpoint get_ints (l : list (const nat)) :=
    match l with
    | [] => Some []
    | Int_c ts :: rest =>
        match get_ints rest with
        | Some il => Some (decode_0_trits ts :: il)
        | _ => None
        end
    | _ => None
    end.

  Definition get_result P :=
    match run_prog P with
    | Some (ol, _) => get_ints ol
    | _ => None
    end.
  
  Inductive test_result := Right | Wrong (z : option (list Z)).

  Instance o_list_Z_eq : EqDec_eq (option (list Z)).
  Proof. eq_dec_inst. Qed.

  Fixpoint run_tests tests :=
    match tests with
    | [] => []
    | (P, r) :: rest =>
        let r' := get_result P in
        (if eq_dec r' r then Right else Wrong r') :: run_tests rest
    end.

  Definition run_all_tests := run_tests test_progs.

End Concrete.

Extract Constant n0 => "0".
Extract Constant n1 => "1".
Extract Constant n2 => "2".
Extract Constant n3 => "3".
Extract Constant n4 => "4".
Extract Constant n5 => "5".
Extract Constant n6 => "6".
Extract Constant n7 => "7".
Extract Constant n8 => "8".
Extract Constant n9 => "9".
Extract Constant n10 => "10".
Extract Constant n11 => "11".
Extract Constant n12 => "12".
Extract Constant n13 => "13".
Extract Constant n14 => "14".
Extract Constant n15 => "15".
Extraction "examples.ml" env_of run_step run_all_tests.