Require Import Arith Util List.
Require Import String.
Require Import Omega.

Import ListNotations OptionNotations.

Set Implicit Arguments.

Definition path := (string * nat)%type.
Definition path_eq_dec : forall (p q:path), {p = q} + {p <> q}.
Proof.
  repeat decide equality.
Defined.
  
Definition var := nat.

(* LLVM-Specific operations ------------------------------------------------- *)


(* Integer-valued operations *)
Inductive  ibinop :=
| Add : bool -> bool -> ibinop (* nuw * nsw *)
| Sub : bool -> bool -> ibinop
| Mul : bool -> bool -> ibinop
| Shl : bool -> bool -> ibinop
| UDiv : bool -> ibinop       (* exact *)
| SDiv : bool -> ibinop
| LShr : bool -> ibinop
| AShr : bool -> ibinop
| URem : ibinop
| SRem : ibinop
| And : ibinop
| Or : ibinop
| Xor : ibinop
.

Inductive cmpop :=
| Eq   (* equal *)
| Ne   (* not equal *)
| Ugt  (* unsigned greater than *)
| Uge  (* unsigned greater or equal *)
| Ult  (* unsigned less than *)
| Ule  (* unsigned less or equal *)
| Sgt  (* signed greater than *)
| Sge  (* signed greater or equal *)
| Slt  (* signed less than *)
| Sle  (* signed less or equal *)
.

Inductive const_val : Set :=
| IConst : nat -> const_val  (* Should be I32 or I64 not nat *)
.

(* Parameterized to allow for constant vs. non-constant expressions *)
Inductive op (X:Set) : Set :=
| IOp  : ibinop -> X -> X -> op X
| ICmp : cmpop -> X -> X -> op X.

(* "Real LLVM" allows constant expressions which can involve
  - any arithmetic, cast, or otherwise "pure" operations and constants
  - not allowed: alloca, load, store, etc.
*)
Inductive const_exp : Set :=
| CCst : const_val -> const_exp
| COp  : op const_exp -> const_exp
.
    
(* CFG ---------------------------------------------------------------------- *)

(* operand values *)
Inductive opnd :=
| OErr : opnd
| OVar : var -> opnd        (* Free variables / external calls *)
| OCst : const_exp -> opnd  (* constant_expressions *)
| OLoc : path -> opnd       (* SSA local variable *)
| OLbl : path -> opnd.      (* Function / code pointer *)


Inductive arg :=
| AVAL : opnd -> arg
| APRJ : nat -> arg.       (* LLVM blockaddres(@function, %block) *)

Record tgt := branch {phis: list (path * opnd); next:path}.

Inductive ins :=
| ERR   (* LLVM: Unreachable *)
| CALL (target:opnd) (args:list arg) (next:path)
| TAIL (target:opnd) (args:list arg)
| POP  (next:path)
| OP   (oper:op opnd) (next:path)
| RET  (val:opnd)
| BR   (br:tgt)       (* replaces PMOV *)
| CBR  (val:opnd) (br0:tgt) (br1:tgt)
(* | SWI  (nexts:list path)    (* LLVM: indirectbr ? *) *)
.

Definition cfg := path -> option ins.

Inductive dval :=
| DErr : dval
| DVar : var -> dval
| DCst : const_val -> dval
| DRec : path -> list (path * dval) -> dval
.

Definition env :=  list (path * dval).

Inductive frame := 
| KApp : dval -> frame
| KSeq : path -> path -> env -> frame
| KPrj : nat -> frame.


Definition eval_cst (c:const_exp) : const_val :=
  match c with
  | CCst v => v
  | _ => IConst 0
  end.   (* TODO: Real operational semantics *)

Definition eval_opnd (e:env) (o:opnd) : dval :=
  match o with
  | OErr => DErr
  | OVar x => DVar x
  | OCst c => DCst (eval_cst c)
  | OLoc p => assoc_f path_eq_dec DErr id p e
  | OLbl p => DRec p e
  end.

Definition eval_arg (e:env) (o:arg) : frame :=
  match o with
  | AVAL d => KApp (eval_opnd e d)
  | APRJ i => KPrj i
  end.

Definition bin f v1 v2 :=
  match v1, v2 with
  | DCst (IConst n),  DCst (IConst m) => DCst (IConst (f n m))
  | _, _ => DErr
  end.


Definition eval_binop (b:ibinop) (v1:dval) (v2:dval) : dval :=
  match b with
  | Add _ _ => bin plus v1 v2
  | Sub _ _ => bin minus v1 v2
  | Mul _ _ => bin mult v1 v2
  | _ => DErr
  end.

Definition cmp (f:nat -> nat -> bool) v1 v2 :=
  match v1, v2 with
  | DCst (IConst n),  DCst (IConst m) =>
    if f n m then DCst (IConst 1) else DCst (IConst 0)
  | _, _ => DErr
  end.

Definition eval_cmpop (c:cmpop) (v1:dval) (v2:dval) : dval :=
  match c with
  | Eq => cmp beq_nat v1 v2
  | Ne => cmp (fun n m => negb (beq_nat n m)) v1 v2
  | _ => DErr
  end.

  
Definition eval_op (e:env) (o:op opnd) : dval :=
  match o with
  | IOp b o1 o2 => eval_binop b (eval_opnd e o1) (eval_opnd e o2)
  | ICmp c o1 o2 => eval_cmpop c (eval_opnd e o1) (eval_opnd e o2)
  end.

Definition eval_tgt (e:env) (tgt:tgt) :=
  (next tgt, map_snd (eval_opnd e) (phis tgt)).

Definition st := (path * env * list frame) % type.

Definition step (CFG:cfg) (s:st) : option st :=
  let '(p, e, k) := s in
  do i <- CFG p;
  match i, k with
  | TAIL o args, _ =>
    match eval_opnd e o with
    | DRec p' e' => Some (p', e', map (eval_arg e) args ++ k)
    | _ => None
    end

  | CALL o args p'', _ =>
    match eval_opnd e o with
    | DRec p' e' => Some (p', e', map (eval_arg e) args ++ KSeq p p'' e::k)
    | _ => None
    end

  | OP o p', _ =>
    match eval_op e o with
    | DCst v => Some (p', (p, (DCst v))::e, k)
    | _ => None
    end

  | RET o, KSeq q p' e'::k' =>
    Some (p', (q, eval_opnd e o)::e', k')

  | POP p', KApp d::k' =>
    Some (p', (p, d)::e, k')

  | BR tgt, _ =>
    let '(p', e') := eval_tgt e tgt in
    Some (p', e'++e, k)
         
  | CBR o tgt1 tgt2, _ =>
    match eval_opnd e o with
    | DCst (IConst n) =>   (* NOTE: 0 = false 1 = true *)
      let '(p', e') := eval_tgt e (if zerop n then tgt2 else tgt1) in
      Some (p', e'++e, k)
    | _ => None
    end

  | RET _, _
  | POP _, _ 
  | ERR, _ => None
  end.

(*
fact:
0: POP  // x
1: ICMP %0 0
2: CBR %1 (@3 []) (@4 [])

3: RET 1

4: Sub %0 1
5: CALL fact (%4)
6: Mul %0 %5
7: Ret %6
 *)
Open Scope string_scope.

(* TODO: fix notation *)
Notation "$$ n" := (OCst (CCst (IConst n))) (at level 75, right associativity).

Definition code : Type := list (path * ins).

Definition fact_code :=
  let fo := fun n => ("fact", n) in
  List.map (fun p => (fo (fst p), (snd p)))
  [ (0 , (POP (fo 1)));
    (1 , (OP (ICmp Eq (OLoc (fo 0)) ($$0)) (fo 2)));
    (2 , (CBR (OLoc (fo 1))
                    {|phis := []; next := (fo 3)|}
                    {|phis := []; next := (fo 4)|}));
    (3 , (RET ($$1)));
    (4 , (OP (IOp (Sub true true) (OLoc (fo 0)) ($$1)) (fo 5)));
    (5 , (CALL (OLbl (fo 0)) [AVAL (OLoc (fo 4))] (fo 6)));
    (6 , (OP (IOp (Mul true true) (OLoc (fo 0)) (OLoc (fo 5))) (fo 7)));
    (7 , (RET (OLoc (fo 6))));
    (8 , (CALL (OLbl (fo 0)) [AVAL ($$3)] (fo 9)));
    (9 , (RET (OLoc (fo 8))))].

Definition fact_cfg := fun p => assoc path_eq_dec p fact_code. 

Definition fact_s0 : st := (("fact",8), [], []).

Fixpoint run cfg n s :=
  match n with
  | 0 => Some s
  | S m => 
    match step cfg s with
    | None => Some s
    | Some s' => run cfg m s'
    end
  end.

Eval cbv in run fact_cfg 100 fact_s0.


(*  ------------------------------------------------------------------------- *)
(*
Definition example : cfg :=
```llvm

   define f (%0, %1) {
   entry:
     %2 op opnd opnd
     %3 op opnd opnd
     %4 cbr %d  (%lbl1 []) (%lbl2 [])

   lbl1: []   (* <-- phis arguments *)
     %5 op opnd opnd
     %6 br (lbl3 [0:opnd, 1:opnd])
       
   lbl2: []
    %7 op opnd opnd
    %8 br (lbl3 [0:opnd, 1:opnd])       
           
   lbl3: [0,1]
    %9 op opnd
    %10 ret opnd         
   }
```

(f, n) 
ENTRY: (* = (f, 0) *)
0: POP
1: POP
2: op %0 %1
3: op %2 %2
4: CBR opnd (@5 []) (@7 [])

LBL1:  (* = 5 *)
5: op %0 %2
6: BR (@9 [0:opnd, 1:opnd])

LBL2:  (* = 7 *)
7: op %2 %1
8: BR (@9 [0:opnd, 1:opnd])

LBL3:  (* = 9 *)
9: PHI
10: PHI
11: op %9 %10
10: op opnd
*)

(*  ------------------------------------------------------------------------- *)



(*  ------------------------------------------------------------------------- *)
(* Sketch of well-formedness constraint for cfg code *)

Definition is_branch_tgt (cfg:cfg) tgt : Prop :=
  exists p, ((cfg p = Some (BR tgt) \/
         exists o tgt', cfg p = Some (CBR o tgt tgt') \/ cfg p = Some (CBR o tgt' tgt))).

Definition targets_compatible (cfg:cfg) : Prop :=
  forall tgt1 tgt2, is_branch_tgt cfg tgt1 /\ is_branch_tgt cfg tgt2 ->
               (next tgt1) = (next tgt2) -> (map fst (phis tgt1)) = (map fst (phis tgt2)).

Definition is_predecessor (cfg:cfg) (p:path) tgt : Prop :=
  p = (next tgt) /\ is_branch_tgt cfg tgt.

Definition ins_succesors (i:ins) : list path :=
  match i with
  | ERR   => []
  | CALL _ _ next => [next]
  | TAIL _ _ => []
  | POP next => [next]
  | OP  _ next => [next]
  | RET _ => []
  | BR tgt => [next tgt]
  | CBR _ tgt1 tgt2 => [next tgt1 ; next tgt2]
  end.


Definition successors (CFG:cfg) (p:path) : list path :=
  match (CFG p) with
  | None => []
  | Some i => ins_succesors i
  end.

  
           




           

  
