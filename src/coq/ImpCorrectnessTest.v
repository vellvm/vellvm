(* QuickChick dependencies *)
Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import QcDoNotation.
Require Import QuickChick.RoseTrees.

Require Import ZArith.
Require Import String.
Require Import Sumbool.

(* CompCert dependencies *)
Require Import compcert.lib.Integers.

(* Vellvm dependencies *)
Require Import Vellvm.Ollvm_ast Vellvm.CFG.
Require Import Vellvm.StepSemantics Vellvm.Memory.
Require Import Vellvm.Compiler.
Require Import Vellvm.CFGProp.
Require Import Vellvm.Classes.
Require Import Vellvm.AstLib.
Require Import Vellvm.DecidableEquality.

(* Source and Target QuickChick dependencies *)
Require Import Vellvm.ImpQuickChick.
Require Import Vellvm.OllvmQuickChick.
Require Import Vellvm.MemoryQuickChick.
Require Import Vellvm.CompilerQuickChick.

(* Logical Foundations dependencies *)
Require Import Vellvm.Imp Vellvm.Maps Vellvm.ImpCEvalFun.
Open Scope list_scope.
Require Import Program.

(* Verification Files *)
Require Import Vellvm.ImpCorrectness.


(** Earlier, we considered the problem of proving algorithms (the compiler) 
    correct, and showed that we can first test for correctness by writing a 
    property Checker for the algorithm, and running QuickChick on it. To do 
    this, we mirrored the implementation and developed generators, Show's, and 
    shrinkers for the data types handled by and within the implementation.

    Now, we consider the problem of proving propositions correct, and
    show how this can be done by interpreting propositions "operationally".
    To do this, we similarly mirror the logic development by developing 
    generators and property Checkers for logical definitions (e.g. inductive 
    propositions) and theorems waiting to be proved. 

    To see why, consider ...
*)


(** ** A small example *)
(*
Fixpoint prefix_bool {A : Type} `{eq_dec A} (l1 l2 : list A) :=
  match l1, l2 with
  | [], _ => true
  | (x :: xs), (y :: ys) =>
    if x == y then prefix_bool xs ys else false
  | _, [] => false
  end.

Definition compile_aexp_monotonic_bool
           (g : ctxt) (a : aexp) (n m : int) (code: list elt) :=
    let '((n', m', code'), v_opt) := compile_aexp g a (n,m,code) in
    match v_opt with
    | inl err => false
    | inr v' =>
      andb (andb (Z.leb n n') (Z.leb m m'))
           (prefix_bool (List.rev code) (List.rev code'))
    end.

(** Define property Checkers for lemmas and theorems. *)
Definition test_compile_aexp_monotonic (a : aexp) (n m : int) :=
  let fvs := IDSet.elements (fv a) in
  let g := compile_fv fvs in (* use this as initial context and code for now *)
  let '((n', m', c), new_context_opt) := g (n, m, [])%Z in
  match new_context_opt with
  | inl e => whenFail "Compilation of free variables failed" false
  | inr new_context =>   
    checker (compile_aexp_monotonic_bool new_context a n' m' c)
  end.

(*** ! Section TestCompileAexpMonotonic *)

Existing Instance genSaexp.

Definition test_compile_aexp_monotonic_wrapper :=
  forAll arbitrary test_compile_aexp_monotonic.

(*** ! QuickChick test_compile_aexp_monotonic_wrapper. *)

Remove Hints genSaexp : typeclass_instances.
(* End Section *)
 *)


(** ** Generators, Shows, and Functions *)

Instance gen_iid :
  GenSuchThat (int * instr_id)
              (fun '(n, id) => iid n id) :=
  {| arbitraryST :=
       do! n <- arbitrary;
       returnGen (Some (n, IId (lid_of_Z n)))
  |}.

Instance gen_Rv64 `{Gen int64}:
  GenSuchThat (dvalue * int64) (fun '(v, i) => Rv64 v i) :=
  {| arbitraryST :=
       do! i <- arbitrary;
       returnGen (Some (DVALUE_I64 i, i))
  |}.

Instance gen_Rv1: GenSuchThat (dvalue * bool) (fun '(v, b) => Rv1 v b) :=
  {| arbitraryST :=
       do! b <- arbitrary;
     match b with
     | true => returnGen (Some (DVALUE_I1 StepSemantics.Int1.one, b))
     | false => returnGen (Some (DVALUE_I1 StepSemantics.Int1.zero, b))
     end
  |}.

Instance show_bundled_memory :
  Show (list id * ctxt * env * memory * Imp.state) :=
  {| show x := 
       match x with
       | (ids, c, e, m, s) =>
         ("vars: " ++ (show ids) ++ "; " ++
                   "env: " ++ (show e) ++ "; " ++
                   "mem: " ++ (show m) ++ "; ")%string
       end
  |}.

(** The following deviates from the logic development in two ways. Firstly,
    we introduce (vars : list id) so that we can compute with the domain of 
    Imp.state; this is essential for Checking. Secondly, we generate elements
    that satisfy both memory_invariant and env_lt at the same time, rather than
    build generators separately for each. This is because of efficiency. 
  *)
Definition memory_invariant_bundle_with_env_lt
           (vars: list id) (g: ctxt) (e: env) (m: memory) (st: Imp.state)
           (bound : int) :=
  memory_invariant g e m st
  /\ (forall x, List.In x vars <-> exists v, g x = Some v)
  /\ env_lt bound e.

Existing Instance gen_small_nonneg_i64.

Instance gen_memory_bundle_with_env_lt (bound : int):
  GenSizedSuchThat
    (list id * ctxt * env * memory * Imp.state)
    (fun '(vars, g, e, m, st) => 
       memory_invariant_bundle_with_env_lt vars g e m st bound) :=
  {| arbitrarySizeST :=
       fix gen_mem n :=
         match n with
         | 0 => returnGen (Some ([], empty, [], [], empty_state))
         | S n' => (* local (lid_of_Z n) *)
           do! m_opt <- gen_mem n';
           match m_opt with
           | Some (idents, c, e, m, s) => 
             do! ident <- arbitrary;
             do! label_id <- arbitrary;
             do! contents <- arbitrary;
             let addr := n in (* deterministic, always appending *)
             let label_id := if (label_id <? bound)%Z then label_id
                             else (bound - 1)%Z in
             let idents' := ident :: idents in
             let c' := update c ident (local (lid_of_Z label_id)) in
             let e' := add_env_Z label_id (DVALUE_Addr addr) e in
             let m' := m ++ [DVALUE_I64 contents] in
             let s' := t_update s ident contents in
             returnGen (Some (idents', c', e', m', s'))
           | None => returnGen None
           end
         end
  |}.

Remove Hints gen_small_nonneg_i64.

Definition get_compiled_prefix `{eq_dec A} (code_before code_after : list A) :=
  let fix get_suffix l1 l2 :=
      match l1, l2 with
      | (x :: xs), (y :: ys) =>
        if x == y then
          get_suffix xs ys
        else None
      | [], ys => Some ys
      | _, _ => None
      end
  in match (get_suffix (List.rev code_before) (List.rev code_after)) with
     | Some l => Some (List.rev l)
     | None => None
     end.







(** ** Things break here *)
(*
Fixpoint compiled_code_of (elts : list elt) : option code :=
  match elts with
  | [] => Some []
  | I id instr :: tl =>
    match compiled_code_of tl with
    | Some tl' => Some ((id, instr) :: tl')
    | None => None
    end
  | _ => None
  end.

Definition imp_inject_into_tle (blocks: list Ollvm_ast.block) :
  list (toplevel_entity (list Ollvm_ast.block)) :=
  [
    TLE_Definition
      {|
        df_prototype := imp_decl;
        df_args := [];
        df_instrs := blocks
      |}
  ].

Definition build_mcfg_from_blocks (blocks: list Ollvm_ast.block) :=
  let tle_entities := imp_inject_into_tle blocks in
  let m := modul_of_toplevel_entities tle_entities in
  mcfg_of_modul m.

Fixpoint wrap_elts_in_cfg
         (e : list elt)
         (instr_id_after_compiling_e : int) : err (option mcfg) :=
  let bid := Anon 0%Z in
  'blocks <- blocks_of_elts bid e
          (IVoid instr_id_after_compiling_e, TERM_Ret_void);
  mret (build_mcfg_from_blocks blocks).

(** ** Checkers *)

(** Given a complicated formula or property of interest, we can break it down
    and have separate Checkers for each part. So far, we have mostly defined 
    boolean tests, and then wrapped them up into a final Checker when running 
    QuickChick. However, combinators like "forAll", "conjoin" and "whenFail" 
    lets us compose Checkers, so the boolean tests could have been Checkers 
    themselves instead. 
 *)

Definition Rv64e_checker (v_err : err dvalue) (i : int64) : Checker :=
  match v_err with
  | inl _ => whenFail "RV64e: err" false 
  | inr v => 
    match v with
    | DVALUE_I64 i' =>
      if i == i' then 
        checker true
      else
        whenFail "RV64e: not the same integer" false
    | _ => whenFail "RV64e: not DVALUE_I64" false
    end
  end.

(** This departs significantly from the equivalent logical form, although the 
    equivalence should be proven. 
    TODO: Check equivalence!
*)
Fixpoint env_extends_checker (e1 e2 : env) : Checker :=
  match e1 with
  | [] => checker true
  | (lid1, dval1) :: l =>
    let is_in := List.existsb
                   (fun '(lid2, dval2) =>
                      if (lid1 == lid2) then
                        if (dval1 == dval2) then true else false
                      else false)
                   e2 in
    if is_in then 
      env_extends_checker l e2
    else whenFail "env_extends: not an extension" false
  end.

Fixpoint memory_bundle_invariant_checker (vars: list id)
         (g : ctxt) (e : env) (m : memory) (st: Imp.state) : Checker :=
  match vars with
  | [] => checker true
  | Id var :: vars' =>
    match lookup_env e (Name var) with
    | Some (DVALUE_Addr a) =>
      if (List.nth_default undef m a) == DVALUE_I64 (st (Id var)) then
        memory_bundle_invariant_checker vars' g e m st
      else whenFail "memory_invariant: values do not agree" false 
    | _ => whenFail "memory_invariant: var not found" false
    end
  end.

Fixpoint env_lt_checker (bound: int) (e: env) : Checker :=
  match e with
  | [] => checker true
  | (Raw n, dval) :: l =>
    if (n <? bound)%Z then env_lt_checker bound l else
      whenFail "env_lt: fails bound" false
  | _ => whenFail "env_lt: env not in the right form" false
  end.

Definition memory_bundle_invariant_and_env_lt_checker
           (vars: list id) (g : ctxt) (e : env) (m : memory) (st: Imp.state)
           (n : int) : Checker :=
  conjoin [memory_bundle_invariant_checker vars g e m st;
             env_lt_checker n e].

Fixpoint compiled_code_checker elts code : Checker :=
  match elts, code with
  | [], [] => checker true
  | (I id instr :: tl), ((id', instr') :: cd)  =>
    if id == id' then
      if instr == instr' then
        compiled_code_checker tl cd
      else whenFail "compiled_code: instrs are not equal" false
    else whenFail "compiled_code: ids are not equal" false
  | [], _
  | (_ :: _), [] => whenFail "compiled_code: lengths not equal" false                     
  | _, (_ :: _) =>
    whenFail "compiled_code: elts not in the right form" false
  end.

Fixpoint CFG_has_code_at_checker
         (CFG : mcfg) (P : pc -> Checker) (p : pc) (c : code) : Checker :=
  let step_checker c_iid c_instr := 
      match fetch CFG p with
      | Some (CFG.Step instr) =>
        if instr == c_instr then          
          if (pt p == c_iid) then checker true
          else whenFail "CFG_has_code_at: pc not in sync" false
        else whenFail "CFG_has_code_at: instrs not the same" false
      | Some _ => whenFail "CFG_has_code_at: jump is unexpected" false
      | None => whenFail "CFG_has_code_at: no instruction at pc" false
      end in
  match c with
  | [(iid, instr0)] =>
    match incr_pc CFG p with
    | Some pc_next =>
      conjoin [step_checker iid instr0 ;
                 whenFail "CFG_has_code_at: P does not hold for next pc"
                          (P pc_next)]
    | None => whenFail "CFG_has_code_at: no next pc" false
    end
  | (iid, instr0) :: cd =>
    match incr_pc CFG p with
    | Some pc_next =>
      conjoin [step_checker iid instr0 ;
                 CFG_has_code_at_checker CFG P pc_next cd]
    | None => whenFail "CFG_has_code_at: no next pc" false
    end
  | _ => whenFail "CFG_has_code_at: code is empty, not allowed" false
  end.

Definition combine_if_then_else
           (if_checker: Checker)
           (then_check : Checker)
           (else_check: Checker) : Checker :=
  do! if_result <- liftGen unProp if_checker;
    let '(MkRose r _) := if_result in
  match ok r with
  | Some true => then_check
  | Some false | None => else_check
  end.

Fixpoint step_star_checker (CFG: mcfg) (R: SS.state -> memory -> Checker)
         (s : SS.state) (m : memory)
         (fuel : nat) : Checker :=
  match fuel with
  | 0 => R s m
  | S fuel' => 
    combine_if_then_else (R s m) 
      (checker true) (* step_zero *)      
      (match stepD CFG s with
       | Step s' => step_star_checker CFG R s' m fuel' (* step_tau *)
       | Obs (Eff e) =>
         match mem_step e m with
         | inr (m', v, k) => step_star_checker CFG R (k v) m' fuel'
         | inl _ => whenFail "step_star: mem_step fails" false
         end
       | _ => whenFail "step_star: stepD to jump is unexpected" false
       end)
  end.

Definition compile_aexp_final_state_checker
           (llvm_ans : Ollvm_ast.value) (ans: Int64.int)           
           (vars: list id) (g : ctxt) (e: env) (st : Imp.state)
           (end_local_id : int) (end_pc : pc) :
  SS.state -> memory -> Checker :=
  fun '(pc', e', k') mem' =>
    if pc' == end_pc then 
    conjoin [memory_bundle_invariant_checker vars g e' mem' st ;
               Rv64e_checker (eval_op e (Some (TYPE_I 64)%Z) llvm_ans) ans;
               env_extends_checker e e';
               env_lt_checker end_local_id e']
    else whenFail "compile_aexp: final state has wrong pc" false.

(* The following is currently unsafe in two ways, and should be improved: 
   - Firstly, the CFG has to come from wrap_elts_in_cfg, which ensures 
     CFG_has_code_at holds, fixes a dummy block_id, and fixes the IMP 
     function_id used by the compiler.
   - The PC wrapping here relies on the dummy block_id.
 *)


Definition unsafe_aexp_compiled_code_checker
           (llvm_ans: Ollvm_ast.value) (ans: int64)
           (end_local_id : int)
           (vars: list id) (g: ctxt) (e: env) (m: memory) (st: Imp.state)
           (CFG: mcfg) (start_instr_id: int) (k: stack) (end_instr_id: int)
           (c : code) : Checker :=
  match c with
  | [] => Rv64e_checker (eval_op e (Some (TYPE_I 64)%Z) llvm_ans) ans
  | _ :: _ => checker true 
    (*
    let imp_fid := Name "imp_command" in
    let dummy_bid := Anon 0%Z in 
    let start_pc := mk_pc imp_fid dummy_bid (IVoid start_instr_id) in
    let end_pc := mk_pc imp_fid dummy_bid (IVoid end_instr_id) in
    step_star_checker CFG
                      (compile_aexp_final_state_checker
                         llvm_ans ans
                         vars g e st
                         end_local_id end_pc)
                      (start_pc, e, k) m 1000 *)
  end.



(*
Definition unsafe_aexp_compiled_code_checker
           (llvm_ans: Ollvm_ast.value) (ans: int64)
           (end_local_id : int)
           (vars: list id) (g: ctxt) (e: env) (m: memory) (st: Imp.state)
           (CFG: mcfg) (start_instr_id: int) (k: stack) (end_instr_id: int)
           (c : code) : Checker :=
  match c with
  | [] => Rv64e_checker (eval_op e (Some (TYPE_I 64)%Z) llvm_ans) ans
  | _ :: _ => checker true 
    (*
    let imp_fid := Name "imp_command" in
    let dummy_bid := Anon 0%Z in 
    let start_pc := mk_pc imp_fid dummy_bid (IVoid start_instr_id) in
    let end_pc := mk_pc imp_fid dummy_bid (IVoid end_instr_id) in
    step_star_checker CFG
                      (compile_aexp_final_state_checker
                         llvm_ans ans
                         vars g e st
                         end_local_id end_pc)
                      (start_pc, e, k) m 1000 *)
  end.
 *)

(* ! Section TestCompileAexp *)

(** Hiccups: Typeclass magic means that subtle mistakes can make the typechecker
    run forever. 
    (1) Try interchanging arguments for memory_invariant_bundle_with_env_lt.
    (2) Partial-evaluate whenFail, i.e. without false, say.
    (3) Any type error beyond the trivial causes a problem.
 *)


Existing Instance gen_small_nonneg_i64.
Existing Instance genSaexp.

Definition check_compile_aexp_correct_simple : Checker := 
  forAll arbitrary (fun (a : aexp) =>
  forAll arbitrary (fun (local_id instr_id : int) =>
  forAll arbitrary (fun (cd : list elt) => 
  forAll (genST (fun '(vars, g, e, m, st) =>
               memory_invariant_bundle_with_env_lt vars g e m st local_id))
  (fun bundled_memory_opt =>
     match bundled_memory_opt with
     | None => whenFail "generation of compatible memory failed" false
     | Some (vars, g, e, m, st) =>
       forAll arbitrary (fun (k : stack) => 
       let ans := aeval st a in
       let '((local_id', instr_id', cd'), v_opt) :=
           compile_aexp g a (local_id, instr_id, cd) in
       match v_opt with
       | inl _ => whenFail "compilation failed" true
       | inr v =>
         match get_compiled_prefix cd cd' with
         | Some cd_a => 
           match compiled_code_of cd_a with
           | Some c_a =>
             match wrap_elts_in_cfg (List.rev cd_a) instr_id' with
             | inr cfg =>
               unsafe_aexp_compiled_code_checker v ans local_id'
               vars g e m st instr_id k instr_id' (List.rev c_a)
             | inl _ => whenFail "CFG generation failed" false
             end
           | None => whenFail "compiled code not well-formed" false
           end
         | None => whenFail "compiled code not prefix" false
         end
       end)
     end)))). 


(* ! QuickChick check_compile_aexp_correct_simple. *)

 *)

(* End TestCompileAexp *)

(** ** Notes *******************************************************************
- Prenexification
- Functional dependence of exists
- Further constraints after exists
- Dependent generation (e.g. CFG that satisfies a property most of the time, 
  but not all the time)
- Adopting the discipline of having Decidable propositions everywhere,
  so that both generation and testing use one copy. 
- Higher-order constructs are difficult, e.g. continuation for effects and
  partial maps for Imp.state. 

Lemma compile_aexp_correct_simple2A:
  forall (a : aexp) (st : Imp.state) (g : ctxt)
    (e : env) (mem : memory) (vars : list id)
    (v_err : err Ollvm_ast.value),
    satisfies_memory_invariant_and_bound (vars, g, e, mem, st) n /\
    compile_aexp g a (0, 0, cd) = ((n', m', cd'), v_err) ->
    match v_err with
    | inl err => True (* Says nothing *)
    | inr v =>       
      let cd_a := get_compiled_prefix [] cd' in
      match cd_a with
      | None => False
      | Some cd_a =>
        let c_a := compiled_code_of cd_a in
        match c_a with
        | None => False
        | Some c_a => 
          (forall (k : stack) (fn : function_id) (bid: block_id) phis term,
              step_code (fixed cfg...)
                        (aexp_correct_relation2 vars g e st n' v
                                                (aeval st a)
                                                k fn bid phis term)
                        (List.rev c_a)
                        (slc_pc fn bid phis term c_a, e, k)
                        mem)
        end
      end
    end.

Definition check_compile_aexp_correct_simple2A :=
  forAll arbitrary
         (fun (a : aexp) => 
         forAll (genST (fun bundle => satisfies_memory_invariant_and_bound bundle 0)%Z)
         (fun bundle =>
            match bundle with
            | None => checker true
            | Some (vars, g, e, mem, st) =>
              let result := compile_aexp g a (0, 0, [])%Z in
              match result with
              | ((n', m', cd'), inr v) =>
                let cd_a := get_compiled_prefix [] cd' in
                match cd_a with
                | None => whenFail "not monotonic" false
                | Some cd_a =>
                  let c_a := compiled_code_of cd_a in
                  match c_a with
                  | None => whenFail "compiled result not well-formed" false
                  | Some c_a =>
                    match build_mcfg cd_a with
                    | None => checker true
                    | Some mcfg =>
                      forAll arbitrary
                             (fun (k : stack) => forAll arbitrary
                             (fun (fn : function_id) => forAll arbitrary
                             (fun (bid : block_id) => forAll arbitrary
                             (fun phis => forAll arbitrary
                             (fun term =>
                                step_code_bool
                                  mcfg
                                  (aexp_correct_relation_bool2 vars g e st n' v
                                                               (aeval st a)
                                                               k fn bid phis term)
                                  (List.rev c_a)
                                  (slc_pc fn bid phis term c_a, e, k)
                                  mem)))))
                    end
                  end
                end
              | _ => whenFail "couldn't compile" true
              end
            end)).
*)

(*
Instance dec_stepD_is_Step : forall CFG (s s' : SS.state), Decidable (stepD CFG s = Step s').
Proof.
  intros CFG [[p e] stk] s'.
  set (fetched := fetch p).
  destruct p as [fn_id [bid phis code [iid term]]]; unfold Decidable;
    try solve [intros H; inversion H].
  unfold fetch in fetched; simpl in fetched.
  destruct code; simpl; unfold stepD.
  { destruct term;
      try solve [right; simpl; intros H; inversion H].
    { right;
        simpl;
        destruct stk;
        destruct v;
        unfold lift_err_d;
        destruct (eval_op e (Some t) v);
        intros H; try solve [inversion H].
      destruct f; inversion H.
    }
    { right;
        simpl;
        destruct stk;
        intros H; try solve [inversion H].
      destruct f; inversion H.
    }
    { right;
        simpl;
        destruct v;
        unfold lift_err_d.
      destruct (eval_op e (Some t) v) as [ | b].
      { intros H; inversion H. }
      { destruct b;
          try solve [intros H; inversion H].
        destruct (Int1.eq x Int1.one); destruct trywith;
          try solve [intros H; inversion H].
        destruct trywith;
          try solve [intros H; inversion H].
        destruct jump;
          solve [intros H; inversion H].
        destruct trywith;
          try solve [intros H; inversion H];
          try solve [destruct jump; intros H; inversion H].
      }       
    }
    { right;
        simpl;
        unfold lift_err_d;
        destruct trywith;
        try solve [intros H; inversion H].
      destruct trywith;
        try solve [intros H; inversion H].
      destruct jump;
        try solve [intros H; inversion H].
    }
  }
  { destruct p as [i insn].
    destruct i as [[s | i | i] | i].
    { destruct insn;
        unfold lift_err_d;
        try solve [right; intros H; inversion H].
      { destruct eval_op;
          try solve [right; intros H; inversion H].
        left; destruct s' as [[p' e'] stk'].
        unfold add_env.
        

        repeat destruct s'.
        simpl.
      
    Print instr_id.
    Print raw_id.
    
    destruct i.
    { destruct i0.
*)



(** ** Sidetrack into verified generators *)
(** The generators for propositions above are entirely unchecked and trusted to 
    be generating the right elements, but this may not be true as code and 
    logical definitions evolve. To keep test suites in sync with the 
    development, it can be useful to go the extra mile and prove generators
    "correct".
*)
Instance gen_aevalR (st : Imp.state) (a : aexp) :
  GenSuchThat Int64.int (fun ans => aevalR st a ans) :=
  {| arbitraryST := returnGen (Some (aeval st a)) |}.

Instance gen_aevalR_is_correct (st: Imp.state) (a : aexp) :
  SuchThatCorrect (fun ans => aevalR st a ans) (genST (fun ans => aevalR st a ans)).
Proof.
  unfold arbitraryST; simpl.
  constructor; rewrite semReturn; 
    unfold Sets.lift, imset, set_incl, bigcup, set1, setU.
  - intros a' [ans (H_eval_to_ans, H_some_ans)].
    rewrite <- aeval_iff_aevalR in H_eval_to_ans.
    rewrite H_eval_to_ans; auto.
  - intros [a' | ] H_aeval; try solve [right; inversion H_aeval].
    left; exists a'; split; auto.
    rewrite <- aeval_iff_aevalR.
    inversion H_aeval; trivial.
Qed.

Instance gen_aevalR_correct (st: Imp.state) (a:aexp):
  GenSuchThatCorrect (fun ans: Int64.int => aevalR st a ans).

(** The generator is actually redundant, because it is just running a function;
    it makes better sense to run the function directly and not sample at all. 
    But this shows how we can use an algorithm corresponding to a predicate as 
    a generator for it, and to also use its equivalence proof to prove the 
    generator correct. Verified testing keeps it in sync with code changes and 
    proofs. *)

(** ** Junk ********************************************************************
QuickChickDebug Debug On. 
Print GenSizedSuchThatis_Op.

Instance gen_straight_code : GenSizedSuchThat code (fun c => straight c) :=
  {| arbitrarySizeST :=
       fix gen_straight_code n :=
         match n with
         | 0 => returnGen (Some [])
         | S n' =>
           doM! tl <- gen_straight_code n';
           do! id <- arbitrary;
           doM! instr <- genST (fun i => is_Op i);
           returnGen (Some ((id, instr) :: tl))
         end
  |}.

Inductive fooP : nat -> Foo -> Prop.
Instance dec_dooP n : Dec (foo n).

if (fooP 42)? then ...
else ...

From QuickChick Require Import QuickChick.
Local Open Scope nat.
Import Ollvm_ast.
Derive Arbitrary for Expr
Derive Arbitrary for value.
*)