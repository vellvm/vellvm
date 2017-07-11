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

(** This lecture shows how QuickChick can be used to test the compiler. For
    simplicity, the target language is the simplified SSA language Vminus, and
    we use a variant of Imp whose names are just memory addresses which can be 
    interpreted in the memory of Vminus states. Imp states and Vminus memory
    are hence essentially the same, and this makes it easy to state correct 
    compilation: after running the source program and its compilation, 
    every Imp variable/address is mapped to the same nat by both the Imp state 
    and Vminus memory. 

    A Vminus state consists of a memory (mapping addresses to nat), a program 
    counter, an environment mapping locals to nat, a "previous" program 
    counter, and a "previous" environment. The latter two are needed for
    executing phi nodes. A configuration consists of a Vminus state and a CFG,
    which "holds" Vminus instructions organized in basic blocks.
*)

(** Here's a look at what we mean. 

    Lemma comp_aexp_correct : forall (a:aexp),
      comp_correct (comp_aexp a) (aeval a).
    
    Definition comp_correct (comp : ectmon (val * list insn))
                            (eval : mem -> nat) : Prop :=
      forall (cs cs': list uid) (g: ListCFG.t) (st: V.Opsem.state)
        (is k: list insn) (v: val), 
      (cs', (v, is)) = comp cs ->
      insns_at_pc g (st_pc st) (is ++ k) ->
      exists st',
        st_mem st' = st_mem st /\
        insns_at_pc g (st_pc st') k /\
        star (Opsem.step g) st st' /\
        ids_preserved cs st st' /\
        good_return cs' v /\
        ctx_incr cs cs' /\
        eval_val (st_loc st') v = Some (eval (st_mem st)).
*)

(** That is, compiling Imp aexp is correct if:
    - for any compilation run on an initial list of uids, 
    - wherever we place the compilation result "is" in the CFG, as long
      as the pc is pointed to it, (insns_at_pc g (st_pc) (is ++ k)),
    - we can run to the end of compilation (insns_at_pc g (st_pc st') k),
    - and in this state st', the memory is the same as above; but evaluating 
      the result of the expression in this state (eval_val (st_loc st') v)
      is exactly the same as evaluating it according to the Imp state
      (eval (st_mem st)). 
    - This last fact may not be obvious from the body of comp_correct. But note 
      comp_aexp_correct; the evaluation function passed to it is Imp's aeval, 
      and this is where the coincidence of Imp states and Vminus memory comes 
      into play.
    There is a bunch of other things that we need here, so as to prove correct
    compilation for com. But the above description is the crux.
*)

(** We would like to write Checkers for propositions like the ones above.
    To do so, we first need QuickChick infrastructure for Imp commands.

    Exercise...
 *)

Require Import Vminus.ImpGen.

(** Looking at comp_correct, it is clear that we need to generate more. 
    In particular, it would seem that we need generators for the following:
    - uid
    - CFG
    - Vminus states
    - Vminus instructions
    - values
    However, note that the only value v (with cs', is) is computed by comp 
    rather than generated, so we don't actually need a generator for value. 
    Moreover, the CFG g should not be generated randomly the same way we do 
    others, because it has to satisfy insns_at_pc; it is unlikely for just 
    "any" CFG to satisfy this precondition of the lemma. *)

(**
    Exercise: Generators and Shows for uid and Vminus instructions, using 
    automation as much as possible. (It is however useful to have custom Shows 
    that are more descriptive.)

    For states, we would like to know the domains of their memories and local
    environment, so we have created an extended state that holds this 
    information, called state_with_meta. The generator and show for this have
    been done for you.
 *)

Require Import Vminus.VminusGen.
Require Import Vminus.CompilerGen.

(** With these out of the way, we can now address the remaining gaps. In its 
    current form, comp_correct is inefficient and challenging for testing. 
    Firstly, some of the quantities are computed by a function, so it is 
    unnecessary to generate them in the first place, although seemingly 
    suggested by "forall". Secondly, the CFG g is not just any CFG, but one 
    that satisfies insns_at_pc for the compilation result - random generation 
    in the usual way is very, very unlikely to meet this condition, so most
    checks would end up being vacuously true. Thirdly, a Checker for the 
    the existence of st' really needs to compute it, and this is not part of
    the lemma itself. 

    Hence the first order of affairs is to massage the lemma into a 
    Checker-friendly version.
 *)

(** Firstly, let us drop the unnecessary variables, and use state_with_meta 
    instead of just V.Opsem.state.

    Definition comp_correct (comp : ectmon (val * list insn))
                            (eval : mem -> nat) : Prop :=
      forall (cs: list uid) (g: ListCFG.t) (st: state_with_meta)
        (k: list insn),

      let (cs', (v, is)) := comp cs in

      insns_at_pc g (st_pc st) (is ++ k) ->
      exists st',
        st_mem st' = st_mem st /\
        insns_at_pc g (st_pc st') k /\
        star (Opsem.step g) st st' /\
        ids_preserved cs st st' /\
        good_return cs' v /\
        ctx_incr cs cs' /\
        eval_val (st_loc st') v = Some (eval (st_mem st)).

    This is of course not accepted by Coq, but we will eventually get to a
    Checker.
 *)

(** Secondly, we need to write a custom generator that generates CFGs 
    satisfying insns_at_pc. An easier option is to just construct a CFG 
    containing the required instructions deterministically. 

    Let us call this function wrap_code_in_cfg pc is k (in correspondence with 
    insns_at_pc g (st_pc st) (is ++ k)).

    Exercise...
*)

Require Import Vminus.CompilerGen.

(** The to-be-Checkable lemma is thus:

    Definition comp_correct (comp : ectmon (val * list insn))
                            (eval : mem -> nat) : Prop :=
      forall (cs: list uid) (g: ListCFG.t) (st: state_with_meta)
        (k: list insn),

      let (cs', (v, is)) := comp cs in
      let g := wrap_code_in_cfg (st_pc st) is k in

      exists st',
        st_mem st' = st_mem st /\
        insns_at_pc g (st_pc st') k /\
        star (Opsem.step g) st st' /\
        ids_preserved cs st st' /\
        good_return cs' v /\
        ctx_incr cs cs' /\
        eval_val (st_loc st') v = Some (eval (st_mem st)). 
*)

(** Thirdly, if we have grasped the meaning of the lemma, we know that st'
    is given by executing the compilation result; this is the point of 
    "loading" the compilation result at the current pc in g, and is of course 
    also stated by "star (Opsem.step g) st st'". So we need an executable 
    evaluator for Vminus. The state st' is obtained by running this evaluator 
    until we reach (the start of) k. 
    
    The simplest way of doing so is to stop at the program counter that begins
    k, and this is actually determined by the CFG that loaded (is ++ k). 

    Exercise: Change wrap_code_in_cfg to return (g, pc), where the latter is 
    the pc that begins k. *)

Require Import Vminus.CompilerGen.

(** Now we need the evaluator itself. This has been defined. *)

Check V.Opsem.eval_until_pc.

(** Now the lemma is:

    Definition comp_correct (comp : ectmon (val * list insn))
                            (eval : mem -> nat) : Prop :=
      forall (cs: list uid) (g: ListCFG.t) (st: state_with_meta)
        (k: list insn),

      let (cs', (v, is)) := comp cs in
      let (g, endpoint) := wrap_code_in_cfg (st_pc st) is k in

      match V.Opsem.eval_until_pc g st cutpoint 1000 with
      | inl err => false (* either out of fuel or no st' *)
      | inr st' => 
        st_mem st' = st_mem st /\
        insns_at_pc g (st_pc st') k /\
        star (Opsem.step g) st st' /\
        ids_preserved cs st st' /\
        good_return cs' v /\
        ctx_incr cs cs' /\
        eval_val (st_loc st') v = Some (eval (st_mem st))
      end.
 *)

(** And with this, the major obstacles are out of the way, and we only have
    to write a Checker for the big conjunction. Because the conjunction is 
    huge, it is easier to write a Checker for each conjunct. That is, we would
    like to have:
    - A Checker that checks that two memories are the same. This is where 
      knowing their domains is useful, and is where state_with_meta comes in.
    - A Checker that checks for insns_at_pc g.
    - A Checker for ids_preserved.
    - A Checker for good_return.
    - A Checker for ctxt_incr.
    - A Checker that checks for equality between the two ways of evaluation.
    Note that "star (Opsem.step g) st st'" doesn't need checking, because it is
    implicit in eval_until_pc. With respect to correctness of aexp compilation 
    itself, the last is most relevant. 

    To give a headstart, most of these are defined below.
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
        ("memory_equal: memory at " ++ (show a)
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


(** We can now compose the checkers using QuickChick's conjoin combinator. *)
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

(** Finally, a Checker for comp_correct and comp_aexp could look like the 
    following. It is convenient to split the Checker into a part that does 
    only the generation, and a part that does the checking, because a type 
    error can cause the typechecker to get stuck trying to resolve the issue
    by looking for typeclass instances that don't exist.    
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


(**! Section test_compile_aexp extends compiler *)

Definition comp_aexp_correct_checker :=
  forAll arbitrary (fun a: aexp =>
    (* collect a ( *) comp_correct_checker (comp_aexp a) (aeval a)).

(*! QuickChick comp_aexp_correct_checker. *)


(** Now you are on your own! **)

(** Exercise: Write a Checker for the following lemma. 

Lemma comp_bop_correct : forall b comp1 comp2 eval1 eval2
    (IHa1: comp_correct comp1 eval1)
    (IHa2: comp_correct comp2 eval2),
    comp_correct (comp_bop b comp1 comp2)
                 (fun m => bop_denote b (eval1 m) (eval2 m)).
*)

(** Exercise: Write a Checker for the following lemma. 

Lemma comp_bexp_correct : forall (b:bexp),
  comp_correct (comp_bexp b) (fun m => b2n (beval b m)).
*)

(** Exercise: Write a Checker for the following lemma.

Lemma comp_store_correct : 
  forall g a v le lr cs st,
  insns_at_pc g (block_entry le) (steval (comp_store a v lr) cs) ->
  st_pc st = (block_entry le) ->
  exists st',
    plus (step g) st st' /\
    st_pc st' = (block_entry lr) /\
    st_mem st' = (Memory.update (st_mem st) v (aeval a (st_mem st))).
*)

(** Exercise: Write a Checker for the following lemma.

Lemma comp_cond_correct :
  forall g cs b le l1 l2 st,
  insns_at_pc g (block_entry le) (steval (comp_cond b l1 l2) cs) ->
  st_pc st = (block_entry le) ->
  exists st',
    plus (step g) st st' /\
    st_pc st' = block_entry (if beval b (st_mem st) then l1 else l2) /\
    st_mem st = st_mem st'.
*)
