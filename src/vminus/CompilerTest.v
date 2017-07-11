Require Import List.
Import ListNotations.
Require Import String.
Require Import Arith.

Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.

Require Import Vminus.Vminus.
Require Import Vminus.Atom.
Require Import Vminus.ListCFG.
Require Import Vminus.Imp.
Require Import Vminus.Compiler.
Require Import Vminus.CompilerProp.

Require Import Vminus.ImpGen.
Require Import Vminus.VminusGen.
Require Import Vminus.CompilerGen.

(** ** QuickChick and Vellvm **************************************************)
(** One may expect a compiler for a language as simple as IMP to be relatively 
    straightforward, and a proof of its correctness to be correspondingly
    so. However, LLVM is a full-featured IR, and a faithful formalization 
    is necessarily complex and large. When the compiler is under development, 
    even stating the correctness of the compiler can be difficult, much 
    less prove it.

    But if we have interpreters for both the source and target, testing the 
    compiler is a much simpler affair. Moreover, the simplicity of the source 
    language, i.e. Imp. means that it is really easy to test! *)

(** Following the lecture on compiler correctness, the first step is to define
    what it means for an Imp state and an LLVM "state" to be equivalent. 
    For correct compilation, it should be that all variables in the Imp state
    can be mapped to their corresponding entities in the LLVM "state" following
    the compiler, and that their values are equal. 

    In this case, Imp variables are simplified to exactly the LLVM memory addr,
    so an Imp variable with identifier 42 is in LLVM memory at address 42. 
    Equivalence is thus checked by taking an ordering of the Imp variables and
    checking the value at each corresponding address. *)

(** Hence we have the following. *)


(*
(** Definition of a proper compiler, not correctness in the sense of 
    semantics-preserving translation *)
Definition comp_correct (comp : ectmon (val * list insn))
                        (eval : mem -> nat) : Prop :=
  forall cs cs' g st is k v,
    
  (* uid, val, instruction *) (cs', (v, is)) = comp cs ->
  insns_at_pc g (st_pc st) (is ++ k) ->
  exists st',
    st_mem st' = st_mem st /\
    insns_at_pc g (st_pc st') k /\
    star (Opsem.step g) st st' /\
    ids_preserved cs st st' /\
    good_return cs' v /\
    ctx_incr cs cs' /\
    eval_val (st_loc st') v = Some (eval (st_mem st)).

Lemma comp_aexp_correct : forall (a:aexp),
  comp_correct (comp_aexp a) (aeval a).

Lemma comp_bop_correct : forall b comp1 comp2 eval1 eval2
    (IHa1: comp_correct comp1 eval1)
    (IHa2: comp_correct comp2 eval2),
    comp_correct (comp_bop b comp1 comp2)
                 (fun m => bop_denote b (eval1 m) (eval2 m)).

Lemma comp_store_correct : 
  forall g a v le lr cs st,
  insns_at_pc g (block_entry le) (steval (comp_store a v lr) cs) ->
  st_pc st = (block_entry le) ->
  exists st',
    plus (step g) st st' /\
    st_pc st' = (block_entry lr) /\
    st_mem st' = (Memory.update (st_mem st) v (aeval a (st_mem st))).
  
Lemma comp_cond_correct :
  forall g cs b le l1 l2 st,
  insns_at_pc g (block_entry le) (steval (comp_cond b l1 l2) cs) ->
  st_pc st = (block_entry le) ->
  exists st',
    plus (step g) st st' /\
    st_pc st' = block_entry (if beval b (st_mem st) then l1 else l2) /\
    st_mem st = st_mem st'.
*)

(*
  (* plug in any cfg and initial execution state such that instructions at the 
     current pc has instructions is ++ k. Then there exists an intermediate
     state whose memory is the same as the initial, the instructions at this
     new pc is just k, we can step from st to st', ids are preserved, 
     ... 

     So we need generators for:
     - instructions, for extraneous k
     - states, in particular program counters to place the instructions at
     - 
     And we need to:
     - construct a dummy CFG g where instructions are placed in a given 
       block, and which tell us where the cut-point target pc is.
     - execute instructions from an initial state until this intermediate 
       state is reached. 
     - have a Checker for the conjunction of properties.  
   *)
*)

Fixpoint memory_on_domain_checker
         (dom: list addr) (mem1 mem2 : V.Opsem.mem) : Checker :=
  match dom with
  | [] => checker true
  | (a :: l) =>
    if Nat.eqb (mem1 a) (mem2 a) then
      memory_on_domain_checker l mem1 mem2
    else
      whenFail
        ("memory_equal: memory at " ++ (Atom.string_of a)
                                    ++ " not equal:"
                                    ++ " mem1 has " ++ (show (mem1 a))
                                    ++ "; mem2 has " ++ (show (mem2 a))
        )%string
        false
  end.

Fixpoint loc_on_domain_checker
         (dom: list uid) (loc1 loc2 : V.Opsem.loc) : Checker :=
  match dom with
  | [] => checker true
  | (a :: l) =>
    match loc1 a, loc2 a with
    | Some n1, Some n2 =>
      if Nat.eqb n1 n2 then loc_on_domain_checker l loc1 loc2
      else whenFail "loc_equal: locs disagree" false
    | None, None => loc_on_domain_checker l loc1 loc2
    | _, _ => whenFail "loc_equal: locs disagree" false
    end
  end.

Fixpoint insns_at_pc_checker `{Show pc}
         (g: ListCFG.t) (p: pc) (k : list insn) : Checker :=
  match k with
  | [] => checker true
  | (uid, cmd) :: instrs =>
    match ListCFG.fetch g p with
    | Some (uid', cmd') =>
      if eq_dec_uid uid uid' then
        if eq_dec_cmd cmd cmd' then insns_at_pc_checker g (incr_pc p) instrs
        else whenFail ("insns_at_pc: cmd at pc "
                         ++ (show p) ++ " not equal") false
      else whenFail ("insns_at_pc: uid at pc "
                       ++ (show p) ++ "not equal") false
    | None => whenFail "insns_at_pc: cannot fetch" false
    end
  end.

Definition eval_equal_checker
           (eval: V.Opsem.mem -> nat) 
           (st: V.Opsem.state) (v: val)
  : Checker :=
  let run_result := V.Opsem.eval_val (V.Opsem.st_loc st) v in
  let expected_result := eval (V.Opsem.st_mem st) in
  match run_result with
  | Some n =>
    whenFail "eval_equal: evaluation value not the same"
             (Nat.eqb n expected_result)
  | None => whenFail "eval_equal: run did not obtain any value" false
  end.

Definition ids_preserved_checker (cs : list uid) (st st': V.Opsem.state)
  : Checker :=
  loc_on_domain_checker cs (V.Opsem.st_loc st) (V.Opsem.st_loc st').

Definition expression_step_checker
           (eval: V.Opsem.mem -> nat)
           (g: ListCFG.t)
           (initial_state final_state: V.Opsem.state)
           (k: list insn) (end_of_expr: pc)
           (cs cs': list uid)
           (v : val) : Checker :=
  conjoin [ids_preserved_checker cs initial_state final_state;
             insns_at_pc_checker g end_of_expr k;
             eval_equal_checker eval final_state v].  
(*
    good_return cs' v /\
    ctx_incr cs cs'
 *)


Definition comp_correct_checker_inner
           (comp: ectmon (val * list insn)) (eval: V.Opsem.mem -> nat)
           (cs : list uid) (st: V.Opsem.state) (k: list insn)
  : Checker :=
  let '(cs', (v, instrs)) := comp cs in
  let '(g, cutpoint) := wrap_code_in_cfg (V.Opsem.st_pc st) instrs k in
  match V.Opsem.eval_until_pc g st cutpoint 1000 with
  | inl err => whenFail ("comp_correct_checker: " ++ err) false
  | inr st' => 
    expression_step_checker eval g st st' k cutpoint cs cs' v
  end.

Definition comp_correct_checker
           (comp: ectmon (val * list insn)) (eval: V.Opsem.mem -> nat)
  : Checker :=
  forAll arbitrary (fun (cs : list uid) =>
  forAll arbitrary (fun (start_evaluation_state: state_with_meta) =>
  forAll arbitrary (fun (extra_insn : list insn) =>
    comp_correct_checker_inner
      comp eval
      cs (state_of start_evaluation_state) extra_insn))).

(*
Lemma comp_aexp_correct : forall (a:aexp),
  comp_correct (comp_aexp a) (aeval a).
 *)

(**! Section test_compile_aexp extends compiler *)

Definition comp_aexp_correct_checker :=
  forAll arbitrary (fun a: aexp =>
    (* collect a ( *) comp_correct_checker (comp_aexp a) (aeval a)).

(* QuickChick comp_aexp_correct_checker. *)

(*
Lemma comp_bop_correct : forall b comp1 comp2 eval1 eval2
    (IHa1: comp_correct comp1 eval1)
    (IHa2: comp_correct comp2 eval2),
    comp_correct (comp_bop b comp1 comp2)
                 (fun m => bop_denote b (eval1 m) (eval2 m)).
 *)

(**! Section test_compile_bexp extends compiler *)

(* Fatal error with stack overflow 
Definition comp_bop_correct_checker: Checker :=
  forAll arbitrary (fun (a1: aexp) =>
  forAll arbitrary (fun (a2: aexp) =>
  forAll arbitrary (fun (binop: bop) => 
    collect (binop, a1, a2) (comp_correct_checker 
      (comp_bop binop (comp_aexp a1) (comp_aexp a2))
      (fun m => V.Opsem.bop_denote binop (aeval a1 m) (aeval a2 m)))))).
 *)

Definition comp_bop_correct_checker: Checker :=
  forAll arbitrary (fun (a1: aexp) =>
  forAll arbitrary (fun (a2: aexp) =>
  forAll arbitrary (fun (binop: bop) => 
    collect binop (comp_correct_checker 
      (comp_bop binop (comp_aexp a1) (comp_aexp a2))
      (fun m => V.Opsem.bop_denote binop (aeval a1 m) (aeval a2 m)))))).

(* QuickChick comp_bop_correct_checker. *)

(*
Lemma comp_bexp_correct : forall (b:bexp),
  comp_correct (comp_bexp b) (fun m => b2n (beval b m)).
 *)

Definition comp_bexp_correct_checker : Checker :=
  forAll arbitrary (fun b: bexp => 
    comp_correct_checker (comp_bexp b) (fun m => if (beval b m) then 1 else 0)).

(* QuickChick comp_bexp_correct_checker. *)

(*
Lemma comp_store_correct : 
  forall g a v le lr cs st,
  insns_at_pc g (block_entry le) (steval (comp_store a v lr) cs) ->
  st_pc st = (block_entry le) ->
  exists st',
    plus (step g) st st' /\
    st_pc st' = (block_entry lr) /\
    st_mem st' = (Memory.update (st_mem st) v (aeval a (st_mem st))).
*)

Definition comp_store_correct_checker_inner'
           (a : aexp) (v: addr) (lr le: lbl) (cs: list uid)
           (stm: state_with_meta)
  : Checker :=
  let st := V.Opsem.mkst (stm_mem stm) (block_entry le) (stm_loc stm)
                         (stm_ppc stm) (stm_ploc stm) in
  let stm := mk_st_with_meta
               (stm_mem stm) (stm_mem_dom stm)
               (block_entry le)
               (stm_loc stm) (stm_loc_dom stm)
               (stm_ppc stm)
               (stm_ploc stm) (stm_ploc_dom stm) in
  let '(g, end_pc) :=
      wrap_code_in_cfg (block_entry le)
                       (Stmon.steval (comp_store a v lr) cs) [] in
  match (V.Opsem.eval_once_and_until_pc g st (block_entry lr) 1000) with
  | inl err => whenFail ("comp_store_correct: " ++ err) false
  | inr st' =>
    if (eq_dec_pc (V.Opsem.st_pc st') (block_entry lr)) then
      let new_dom := (v :: stm_mem_dom stm) in
      whenFail ("::: cfg is: " ++ show g ++
                " ::: initial state pc: " ++ show (stm_pc stm) ++
                " ::: le: " ++ show le ++ 
                " ::: lr: " ++ show lr ++
                " ::: store to " ++ show v ++
                " ::: curr pc: " ++ show (block_entry lr) ++
                " ::: final memory: " ++
                show_memory (V.Opsem.st_mem st') new_dom ++
                " ::: initial memory: " ++
                show_memory (V.Opsem.st_mem st) new_dom)
        (memory_on_domain_checker new_dom
          (V.Opsem.st_mem st')
          (V.Opsem.Memory.update (V.Opsem.st_mem st) v
                                 (aeval a (V.Opsem.st_mem st))))
    else whenFail "comp_store_correct: pc not expected" false
  end.

Definition comp_store_correct_checker_inner
           (a : aexp) (v: addr) (lr le: lbl) (cs: list uid)
           (stm: state_with_meta)
  : Checker :=
  let st := V.Opsem.mkst (stm_mem stm) (block_entry le) (stm_loc stm)
                         (stm_ppc stm) (stm_ploc stm) in
  let '(g, end_pc) :=
      wrap_code_in_cfg (block_entry le)
                       (Stmon.steval (comp_store a v lr) cs) [] in
  match (V.Opsem.eval_once_and_until_pc g st (block_entry lr) 1000) with
  | inl err => whenFail ("comp_store_correct: " ++ err) false
  | inr st' =>
    if (eq_dec_pc (V.Opsem.st_pc st') (block_entry lr)) then
      let new_dom := (v :: stm_mem_dom stm) in
      whenFail "comp_store_correct: memories mismatch"
               (memory_on_domain_checker new_dom
                 (V.Opsem.st_mem st')
                 (V.Opsem.Memory.update (V.Opsem.st_mem st) v
                                        (aeval a (V.Opsem.st_mem st))))
    else whenFail "comp_store_correct: pc not expected" false
  end.

Definition comp_store_correct_checker: Checker :=
  forAll arbitrary (fun (a: aexp) =>
  forAll arbitrary (fun (v: addr) =>
  forAll arbitrary (fun (lr: lbl) =>
  forAll arbitrary (fun (le: lbl) =>
  forAll arbitrary (fun (cs: list uid) =>
  forAll arbitrary (fun (stm: state_with_meta) =>
    comp_store_correct_checker_inner a v lr le cs stm)))))).

(* QuickChick comp_store_correct_checker. *)

(*  
Lemma comp_cond_correct :
  forall g cs b le l1 l2 st,
  insns_at_pc g (block_entry le) (steval (comp_cond b l1 l2) cs) ->
  st_pc st = (block_entry le) ->
  exists st',
    plus (step g) st st' /\
    st_pc st' = block_entry (if beval b (st_mem st) then l1 else l2) /\
    st_mem st = st_mem st'.
*)

Definition comp_cond_correct_checker_inner
           (b: bexp) (cs: list uid) (le l1 l2: lbl)
           (stm: state_with_meta)
  : Checker :=
  let st := V.Opsem.mkst (stm_mem stm) (block_entry le) (stm_loc stm)
                         (stm_ppc stm) (stm_ploc stm) in
  let '(g, end_pc) :=
      wrap_code_in_cfg (block_entry le)
                       (Stmon.steval (comp_cond b l1 l2) cs) [] in
  let l := (if beval b (V.Opsem.st_mem st) then l1 else l2) in  
  match (V.Opsem.eval_until_pc g st (block_entry l) 1000) with
  | inl err =>
    whenFail 
      ("::: cfg is: " ++ show g ++
       "::: comp_cond_correct: " ++ err ++
       "::: looking for pc: " ++ show end_pc
      )
      false
  | inr st' =>
    if (eq_dec_pc (V.Opsem.st_pc st') (block_entry l)) then 
      whenFail "comp_store_correct: memories mismatch"
               (memory_on_domain_checker (stm_mem_dom stm)
                                         (V.Opsem.st_mem st)
                                         (V.Opsem.st_mem st'))
    else whenFail "comp_cond_correct: pc not expected" false
  end.

Definition comp_cond_correct_checker : Checker :=
  forAll arbitrary (fun (b: bexp) =>
  forAll arbitrary (fun (le: lbl) =>
  forAll arbitrary (fun (l1: lbl) =>
  forAll arbitrary (fun (l2: lbl) =>
  forAll arbitrary (fun (cs: list uid) =>
  forAll arbitrary (fun (stm: state_with_meta) =>
    comp_cond_correct_checker_inner b cs le l1 l2 stm)))))).

(* QuickChick comp_cond_correct_checker. *)

(*
Inductive match_config : Imp.com -> (cfg * lbl * lbl) -> Prop :=
  | MC_Skip : forall bs l,
      match_config SKIP (bs, l, l)
  | MC_Ass : forall g l l' uid a cs,
      insns_at_pc g (block_entry l) (steval (comp_store a uid l') cs) ->
      match_config (CAss uid a) (g, l, l')
  | MC_Seq : forall g l1 l2 l3 c1 c2,
      match_config c1 (g, l1, l2) ->
      match_config c2 (g, l2, l3) ->
      match_config (CSeq c1 c2) (g, l1, l3)
  | MC_If : forall g le lr l1 l2 b c1 c2 cs,
      match_config c1 (g, l1, lr) ->
      match_config c2 (g, l2, lr) ->
      insns_at_pc g (block_entry le) (steval (comp_cond b l1 l2) cs) ->
      match_config (CIf b c1 c2) (g, le, lr)
  | MC_While : forall g le lb lr b c cs,
      match_config c (g, lb, le) ->
      insns_at_pc g (block_entry le) (steval (comp_cond b lb lr) cs) ->
      match_config (CWhile b c) (g, le, lr).
*)

(*
Definition match_config_checker
           (c: Imp.com) ((g, l1 l2): cfg * lbl * lbl)
  : Checker :=
  match c with
  | SKIP => whenFail "match_config: labels not equal for skip"
                    (eq_dec_lbl l1 l2)
  | 
*)                    

(*
Inductive match_states (g:cfg) (r:lbl)
  : (com * Imp.state) -> Opsem.state -> Prop :=
  match_states_intro : forall c mem st l,
    match_config c (g, l, r) ->
    st_pc st = block_entry l ->
    st_mem st = mem ->
    match_states g r (c, mem) st.

Lemma transl_sim_step_final :
  forall g r imp_st imp_st' vmn_st,
  Imp.step imp_st imp_st' ->
  match_states g r imp_st vmn_st ->
  exists vmn_st',
    (plus (Opsem.step g) vmn_st vmn_st' \/
     star (Opsem.step g) vmn_st vmn_st' /\ imp_size imp_st' < imp_size imp_st) /\
    match_states g r imp_st' vmn_st'.
*)