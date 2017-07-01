(* QuickChick dependencies *)
Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import QcDoNotation.

Require Import ZArith.
Require Import String.
Require Import Sumbool.

(* CompCert dependencies *)
Require Import compcert.lib.Integers.

(* Vellvm dependencies *)
Require Import Vellvm.Ollvm_ast Vellvm.Compiler Vellvm.AstLib Vellvm.CFG Vellvm.StepSemantics Vellvm.Memory.
Require Import Vellvm.Classes.
Require Import Vellvm.AstLib.
Require Import Vellvm.DecidableEquality.

(* Source and Target QuickChick dependencies *)
Require Import Vellvm.ImpQuickChick.
Require Import Vellvm.OllvmQuickChick.
Require Import Vellvm.MemoryQuickChick.

(* Logical Foundations dependencies *)
Require Import Vellvm.Imp Vellvm.Maps Vellvm.ImpCEvalFun.
Open Scope list_scope.
Require Import Program.

(* Verification File *)
Require Import Vellvm.ImpCorrectness.

(* Derive ArbitrarySizedSuchThat for (fun a : aexp => aevalR test_state a n). *)

Inductive prefix_of {A : Type}: list A -> list A -> Prop :=
| prefix_nil : forall l : list A, prefix_of [] l
| prefix_cons_same : forall a l1 l2, prefix_of l1 l2 -> prefix_of (a :: l1) (a :: l2).

Inductive suffix_of {A : Type}: list A -> list A -> Prop :=
| suffix_nil : forall l : list A, suffix_of l []
| suffix_app : forall a l1 l2, suffix_of l1 l2 -> suffix_of (l1 ++ [a]) (l2 ++ [a]).

Instance dec_prefix_of : forall A `{eq_dec A} (l1 l2 : list A), Decidable (prefix_of l1 l2).
Proof.
  intros A A_decidable.
  induction l1 as [| a l1']; unfold Decidable.
  - intros [| a l2']; left; constructor.
  - intros [| b l2']; try solve [right; intros H; inversion H].
    refine
      (match a == b with
       | left _ =>
         match decide (prefix_of l1' l2') with
         | left tail_eq => _
         | right tail_neq => right _
         end
       | right head_neq => right _
       end).
    { subst; constructor. constructor. tauto. }
    { intros H. apply tail_neq. inversion H; subst; auto. }
    { intros H. apply head_neq. inversion H; subst; auto. }
Defined.

Instance dec_Z_leq : forall n m : int, Decidable (n <= m)%Z.
Proof.
  unfold Decidable. intros n m.
  destruct (n <=? m)%Z eqn:n_m.
  - left; rewrite Z.leb_le in n_m; auto.
  - right; intros H; rewrite <- Z.leb_le in H;
      rewrite n_m in H; inversion H.
Defined.

Definition compile_aexp_monotonic_aux
           (g : ctxt) (a : aexp) (n m : int) (code: list elt)
  :=
    let '((n', m', code'), v_opt) := compile_aexp g a (n,m,code) in
    match v_opt with
    | inl err => false
    | inr v' =>
      andb (andb (Z.leb n n') (Z.leb m m'))
           (match decide (prefix_of (List.rev code) (List.rev code')) with
            | left _ => true
            | right _ => false
            end)
    end.

Definition test_compile_aexp_monotonic (a : aexp) (n m : int) :=
  let fvs := IDSet.elements (fv a) in
  let g := compile_fv fvs in (* using this as initial context and code for now *)
  let '((n', m', c), new_context_opt) := g (n, m, [])%Z in
  match new_context_opt with
  | inl e => whenFail "Compilation of free variables failed" false
  | inr new_context =>   
    checker (compile_aexp_monotonic_aux new_context a n' m' c)
  end.

(*! Section TestCompileAexpMonotonic *)

Existing Instance genSaexp.

Definition test_compile_aexp_monotonic_wrapper :=
  forAll arbitrary test_compile_aexp_monotonic.

(*! QuickChick test_compile_aexp_monotonic_wrapper. *)

Remove Hints genSaexp : typeclass_instances.
(* End Section *)

Definition bundled_memory := ((list id) * ctxt * env * memory * Imp.state)%type.

Definition satisfies_memory_invariant_and_bound (m : bundled_memory) (n : int) : Prop :=
  match m with
  | (_, c, e, mem, s) => memory_invariant c e mem s /\ env_lt n e
  end.

Fixpoint check_env_lt (n : int) (e : env) : bool :=
  match e with
  | [] => true
  | (Raw local_id, _) :: rest =>
    if Z.ltb local_id n then check_env_lt n rest
    else false
  | _ => false
  end.

Fixpoint check_memory_invariant (m : bundled_memory) :=
  match m with
  | ([], _, _, _, _) => true
  | (Id var :: vars, c, e, mem, st) =>
    match lookup_env e (Name var) with
    | Some (DVALUE_Addr a) =>
      if (List.nth_default undef mem a) == DVALUE_I64 (st (Id var)) then true
      else false
    | _ => false
    end
  end.

Definition check_memory_invariant_and_bound (m : bundled_memory) (n : int) : bool :=
  match m with
  | (vars, c, e, mem, s) =>
    andb (check_memory_invariant (vars, c, e, mem, s))
         (check_env_lt n e)
  end.

Definition aexp_correct_relation1
           (vars : list id) (g : ctxt) (e: env) (st : Imp.state) 
           (bound : int) (v : Ollvm_ast.value) (ans : int64)
           (k : stack) (fn : function_id) (bid: block_id)
           (phis : list (local_id * phi)) (term : (instr_id * terminator))
           (s : SS.state) (mem : memory) :=
  let '(pc', e', k') := s in
  pc' = slc_pc fn bid phis term [] /\
  satisfies_memory_invariant_and_bound (vars, g, e', mem, st) bound /\
  Rv64e (eval_op e' (Some (TYPE_I 64)%Z) v) ans /\
  env_extends e e'.

Definition aexp_correct_relation2
           (vars : list id) (g : ctxt) (e: env) (st : Imp.state) 
           (bound : int) (v : Ollvm_ast.value) (ans : int64)
           (k : stack) (fn : function_id) (bid : block_id)
           (phis : list (local_id * phi)) (term : (instr_id * terminator))
           (s : SS.state) (mem : memory) :=
  let '(pc', e', k') := s in  
  satisfies_memory_invariant_and_bound (vars, g, e', mem, st) bound.

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

Fixpoint compiled_code_of (elts : list elt) :=
  match elts with
  | [] => Some []
  | I id instr :: tl =>
    match compiled_code_of tl with
    | Some tl' => Some ((id, instr) :: tl')
    | None => None
    end
  | _ => None
  end.

Definition empty_cfg : cfg :=
  {| init := Name "start" ; blks := (fun blk => None); glbl := [] |}.


(***************** Goals: *************************************************************
Lemma compile_aexp_correct :
  forall 
    (a:aexp) (st:Imp.state) (ans:int64)
    (HAexp: aeval st a = ans)

    (g:ctxt)
    (n m:int) (cd:list elt)
    (n' m':int) (cd':list elt)
    (v : Ollvm_ast.value)
    (Hcomp : compile_aexp g a (n,m,cd) = ((n',m',cd'),inr v)),

  exists cd_a c_a,
    cd' = cd_a ++ cd
    /\ compiled_code cd_a c_a
    /\ straight c_a
    /\ forall
    (e:env)
    (mem:memory) (Hlt:env_lt n e)
    (HM: memory_invariant g e mem st)
    (k:stack)
    (CFG : mcfg) (fn : function_id) (bid: block_id) phis term,
      step_code
        CFG
        (fun s' mem' =>
           let '(pc', e', k') := s' in
           pc' = slc_pc fn bid phis term [] /\
           memory_invariant g e' mem' st /\
           Rv64e (eval_op e' (Some (TYPE_I 64)) v) ans /\
           env_extends e e' /\
           env_lt n' e'
        )
        (List.rev c_a)
        (slc_pc fn bid phis term (List.rev c_a), e, k) mem.

Notes: 
- Prenexification
- Functional dependence of exists
- Further constraints after exists
- Dependent generation (e.g. CFG that satisfies a property most of the time, 
  but not all the time)
- Adopting the discipline of having Decidable propositions everywhere,
  so that both generation and testing use one copy. 
- Higher-order constructs are difficult, e.g. continuation for effects and
  partial maps for Imp.state. 

Lemma compile_aexp_correct_simple1:
  forall (a : aexp) (st : Imp.state) (g : ctxt)
    (e : env) (mem : memory) (vars : list id)
    (n m : int) (cd : list elt)
    (n' m' : int) (cd' : list elt) (v_err : err Ollvm_ast.value),
    (* Simplification: restriction to compatible e, m *) 
    satisfies_memory_invariant_and_bound (vars, g, e, mem, st) n /\
    compile_aexp g a (n, m, cd) = ((n', m', cd'), v_err) ->
    match v_err with
    | inl err => True (* Says nothing *)
    | inr v =>       
      let cd_a := get_compiled_prefix cd cd' in
      match cd_a with
      | None => False
      | Some cd_a =>
        let c_a := compiled_code_of cd_a in
        match c_a with
        | None => False
        | Some c_a => 
          (forall (k : stack) (CFG: mcfg) (fn : function_id) (bid: block_id) phis term,
              step_code CFG
                        (aexp_correct_relation1 vars g e st n' v
                                                (aeval st a)
                                                k fn bid phis term)
                        (List.rev c_a)
                        (slc_pc fn bid phis term c_a, e, k)
                        mem)
        end
      end
    end.

Lemma compile_aexp_correct_simple2:
  forall (a : aexp) (st : Imp.state) (g : ctxt)
    (e : env) (mem : memory) (vars : list id)
    (n m : int) (cd : list elt)
    (n' m' : int) (cd' : list elt) (v_err : err Ollvm_ast.value),
    satisfies_memory_invariant_and_bound (vars, g, e, mem, st) n /\
    compile_aexp g a (n, m, cd) = ((n', m', cd'), v_err) ->
    match v_err with
    | inl err => True (* Says nothing *)
    | inr v =>       
      let cd_a := get_compiled_prefix cd cd' in
      match cd_a with
      | None => False
      | Some cd_a =>
        let c_a := compiled_code_of cd_a in
        match c_a with
        | None => False
        | Some c_a => 
          (forall (k : stack) (CFG: mcfg) (fn : function_id) (bid: block_id) phis term,
              step_code CFG
                        (aexp_correct_relation2 vars g e st n' v
                                                (aeval st a)
                                                k fn bid phis term)
                        (List.rev c_a)
                        (slc_pc fn bid phis term c_a, e, k)
                        mem)
        end
      end
    end.

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
****)

Definition aexp_correct_relation_bool2
           (vars : list id) (g : ctxt) (e: env) (st : Imp.state) 
           (bound : int) (v : Ollvm_ast.value) (ans : int64)
           (k : stack) (fn : function_id) (bid : block_id)
           (phis : list (local_id * phi)) (term : (instr_id * terminator))
           (s : SS.state) (mem : memory) : bool :=
  let '(pc', e', k') := s in  
  check_memory_invariant_and_bound (vars, g, e', mem, st) bound.

Definition inject_into_tle elts :=
  'blocks <- blocks_of_elts (Anon 0)%Z elts;
    mret
   ([
    TLE_Definition
    {|
    df_prototype := imp_decl;
    df_args := [];
    df_instrs := blocks
    |}]).

Definition build_mcfg elts :=
  match inject_into_tle elts with
  | inl err => None
  | inr entities => 
    let m := modul_of_toplevel_entities entities in
    mcfg_of_modul m
  end.

Instance dec_is_Op : forall (i : instr), Decidable (is_Op i).
Proof.
  intros i; unfold Decidable; destruct i;
    try solve [right; intros H; inversion H; auto];
    try solve [left; constructor].
Defined.

Instance dec_is_Eff : forall (i : instr), Decidable (is_Eff i).
Proof.
  intros i; unfold Decidable; destruct i;
    try solve [right; intros H; inversion H; auto];
    try solve [left; constructor].
Defined.

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

Fixpoint step_code_bool (CFG : mcfg) (R : SS.state -> memory -> bool)
         (cs : code) (st : SS.state) (mem : memory) : bool :=
  match cs, st, mem with
  | [], s, m => if R s m then true else false
  | (id, i) :: cd, s, m =>
    if decide (is_Op i) then
      (* missing prefix test *)
      match stepD CFG s with
      | Step s' => step_code_bool CFG R cd s' m
      | _ => false
      end
    else
      if decide (is_Eff i) then
        (* missing prefix test *)
        match stepD CFG s with
        | Obs (Eff e) =>
          match mem_step e m with
          | inr (m', v, k) =>
            step_code_bool CFG R cd (k v) m'
          | inl _ => false
          end
        | _ => false
        end
      else true
  end.

Existing Instance gen_adhoc_aexp.

Instance show_bundled_memory : Show bundled_memory :=
  {| show x := 
       match x with
       | (ids, c, e, m, s) =>
         ("vars: " ++ (show ids) ++ "; " ++
                   "env: " ++ (show e) ++ "; " ++
                   "mem: " ++ (show m) ++ "; ")%string
       end
  |}.

Instance gen_consistent_memory (bound : int):
  GenSizedSuchThat bundled_memory (fun m => satisfies_memory_invariant_and_bound m bound) :=
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
             let label_id := if Z.leb bound label_id then bound else label_id in
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

(*! QuickChick check_compile_aexp_correct_simple2A. *)

Instance show_mcfg : Show mcfg := {| show x := "(show mcfg not implemented)" |}.

(*
Definition is_env_extends (e e' : env) : Decidable (env_extends e e').
Proof.
  induction e; unfold Decidable.
  - left. unfold env_extends.
    intros op t dv eval_op_empty.
    destruct op; destruct e; inversion eval_op_empty.
    destruct t; simpl in *.
   ;
    
  match e with
  | [] => inl _
  | [] => 
*)

Derive ArbitrarySizedSuchThat for (fun (instr : instr) => is_Op instr).
Derive ArbitrarySizedSuchThat for (fun (instr : instr) => is_Eff instr).

(* 
QuickChickDebug Debug On. 
Print GenSizedSuchThatis_Op.
Print Hint GenSizedSuchThat. 
Sample (@arbitraryST instr (fun instr => is_Op instr) _).
*)

(* Derive ArbitrarySizedSuchThat for (fun code => straight code)). *)

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

Fixpoint is_Op_bool (i : instr) : bool :=
  match i with
  | INSTR_Op _ => true
  | _ => false
  end.

Fixpoint is_Eff_bool (i : instr) : bool :=
  match i with
  | INSTR_Alloca _ _ _ => true
  | INSTR_Load _ _ _ _ => true
  | INSTR_Store _ _ _ _ => true
  | _ => false
  end.

Fixpoint straight_bool (c : code) : bool :=
  match c with
  | [] => true
  | ((id, i) :: c') =>
    if orb (is_Op_bool i) (is_Eff_bool i) then straight_bool c'
    else false
  end.

Fixpoint compiled_code_bool elts code : bool :=
  match elts, code with
  | [], [] => true
  | (I id instr :: tl), ((id', instr') :: cd)  =>
    if id == id' then
      if instr == instr' then
        compiled_code_bool tl cd
      else false
    else false
  | _, _ => false
  end.

(* Derive ArbitrarySizedSuchThat for (fun env => env_lt n env). *)

Instance gen_env_lt (bound : int) :
  GenSizedSuchThat env (fun env => env_lt bound env) :=
  
  {| arbitrarySizeST :=
       fix gen_env_lt n :=
         match n with
         | 0 => returnGen (Some [])
         | S n' =>
           do! n <- arbitrary;
           do! dv <- arbitrary;
           let m := if Z.leb bound n then bound else n in
           do! env_opt <- gen_env_lt n';
           match env_opt with
           | Some env' =>
             returnGen (Some (add_env_Z m dv env'))
           | None =>
             returnGen None
           end
         end
  |}.


(* 
Sample (genST (fun m => satisfies_memory_invariant_and_bound m 3)%Z).
Sample (@arbitrary stack _) 
Sample (@arbitrary function_id _).
Sample (@arbitrary block_id _).
Sample (@arbitrary instr_id _).
Sample (@arbitrary phi _).
Sample (@arbitrary terminator _).
Sample (@arbitrary code _).
 *)

(*
Definition check_compile_aexp_correct :=
  forAll arbitrary
         (fun (a : aexp) => forAll arbitrary
         (fun (st : Imp.state) =>
         forAll (genST (fun bundle => satisfies_memory_invariant_and_bound bundle 3)%Z)
         (fun bundle =>
            match bundle with
            | None => checker true
            | Some (vars, g, env, mem, state) =>
              let result := compile_aexp g a (0, 0, [])%Z in
              match result with
              | ((n', m', cd'), inr v) =>
                forAll arbitrary
                       (fun (k : stack) => forAll arbitrary
                       (* (fun (CFG : mcfg) => forAll arbitrary *)
                       (fun (fn : function_id) => forAll arbitrary
                       (fun (bid : block_id) => forAll arbitrary
                       (fun phis => forAll arbitrary
                       (fun term =>
                          step_code_checker
                            CFG
                            (fun s' mem' =>
                               let '(pc', e', k') := s' in
                               (* pc' == slc_pc fn bid phis term [] *)
                               check_memory_invariant_and_bound (, g, e', mem', ) n'
                       )))))
              | _ => checker false
              end
                        end))).
*)
          

(*
Inductive fooP : nat -> Foo -> Prop.
Instance dec_dooP n : Dec (foo n).

if (fooP 42)? then ...
else ...

pp
*)

(*
From QuickChick Require Import QuickChick.
Local Open Scope nat.
Import Ollvm_ast.
Derive Arbitrary for Expr
Derive Arbitrary for value.

*)

(* Derive ArbitrarySizedSuchThat for (fun env => env_lt n env). *)
(* Sample (genST (fun env => env_tl env)). *)

(* Derive ArbitrarySizedSuchThat for (fun instr => is_Op instr). *)
