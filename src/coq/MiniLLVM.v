Add Rec LoadPath "/Users/stevez/vellvm/lib/paco/src" as Paco.
Require Import paco.
Require Import List Bool String Ascii.
Require Import Omega.
Require Import Vellvm.Util.
Import ListNotations OptionNotations.

Set Implicit Arguments.

Open Scope string_scope.
Open Scope list_scope.
Open Scope bool_scope.

(* syntax ------------------------------------------------------------------- *)

Definition int := nat.
Definition int_eq_dec := eq_nat_dec.
Definition int_beq := beq_nat.

Inductive raw_id : Set :=
| Name (s:string)     (* Named identifiers are strings: %argc, %val, %x, etc. *)  
| Anon (n:nat)        (* Anonymous identifiers must be sequentially numbered %0, %1, %2, etc. *)
.
Scheme Equality for raw_id.

Definition local_id := raw_id.
Definition local_id_beq := raw_id_beq.
Definition local_id_eq_dec := raw_id_eq_dec.

Inductive ident : Set :=
| ID_Global (id:raw_id)   (* @id *)
| ID_Local  (id:raw_id)   (* %id *)
.
Scheme Equality for ident.

Inductive typ : Set :=
| TYPE_I (sz:nat)
| TYPE_Pointer (t:typ)
| TYPE_Void
.
Scheme Equality for typ.

Inductive icmp : Set := Eq | Ule.
Scheme Equality for icmp.

Inductive ibinop : Set :=
| Add 
| Sub 
| Mul 
.
Scheme Equality for ibinop.

Definition tident : Set := (typ * ident)%type.
Definition tident_beq t1 t2 := (typ_beq (fst t1) (fst t2)) && (ident_beq (snd t1) (snd t2)).
Lemma tident_eq_dec : forall (t1 t2 : tident), {t1 = t2} + {t1 <> t2}.
Proof.
  destruct t1; destruct t2.
  destruct (typ_eq_dec t t0).
  destruct (ident_eq_dec i i0).
  - left. subst. reflexivity.
  - right. unfold not. intros H. apply n. inversion H. auto.
  - right. unfold not. intros H. apply n. inversion H. auto.
Qed.    
    
Inductive Expr (a:Set) : Set :=
| VALUE_Ident   (id:ident)  
| VALUE_Integer (x:int)
| VALUE_Bool    (b:bool)
| VALUE_Null
| VALUE_Undef
| OP_IBinop           (iop:ibinop) (t:typ) (v1:a) (v2:a)  
| OP_ICmp             (cmp:icmp)   (t:typ) (v1:a) (v2:a)
.


(* static values *)
Inductive value : Set :=
| SV : Expr value -> value.
            
Definition tvalue : Set := typ * value.

Inductive instr_id : Set :=
| IId   (id:raw_id)    (* Anonymous or explicitly named instructions *)
| IVoid (n:nat)        (* "Void" return type, each with unique number (NOTE: these are distinct from Anon raw_id)*)
.
Scheme Equality for instr_id.

Inductive instr : Set :=
| INSTR_Op   (op:value)                          (* INVARIANT: op must be of the form SV (OP_ ...) *)
| INSTR_Call (fn:tident) (args:list tvalue)      (* CORNER CASE: return type is void treated specially *)

| INSTR_Phi  (t:typ) (args:list (ident * value))

| INSTR_Alloca (t:typ) 
| INSTR_Load   (t:typ) (ptr:tvalue)     
| INSTR_Store  (val:tvalue) (ptr:tident)

(* Terminators *)
(* Types in branches are TYPE_Label constant *)
| INSTR_Ret        (v:tvalue)
| INSTR_Ret_void
| INSTR_Br         (v:tvalue) (br1:tident) (br2:tident) 
| INSTR_Br_1       (br:tident)

| INSTR_Unreachable
.

Definition function_id := local_id.

Record declaration : Set :=
  mk_declaration
  {
    dc_name        : function_id;  
    dc_type        : typ;    (* INVARIANT: should be TYPE_Function (ret_t * args_t) *)
  }.

Definition block_id : Set := local_id.
        
Definition block : Set := block_id * list (instr_id * instr).

Record definition :=
  mk_definition
  {
    df_prototype   : declaration;
    df_args        : list local_id;
    df_instrs      : list block;
  }.

Inductive toplevel_entity : Set :=
| TLE_Definition      (defn:definition)
.

Definition toplevel_entities : Set := list toplevel_entity.


Set Contextual Implicit.
Generalizable All Variables.


(* induction principles ----------------------------------------------------- *)
Section ValueInd.

  Variable P : value -> Prop.
  Hypothesis IH_Ident   : forall (id:ident), P (SV (VALUE_Ident _ id)).
  Hypothesis IH_Integer : forall (x:int), P (SV (VALUE_Integer _ x)).
  Hypothesis IH_Bool    : forall (b:bool), P (SV (VALUE_Bool _ b)).
  Hypothesis IH_Null    : P (SV (VALUE_Null _ )).
  Hypothesis IH_Undef   : P (SV (VALUE_Undef _ )).
  Hypothesis IH_IBinop  : forall (iop:ibinop) (t:typ) (v1:value) (v2:value), P v1 -> P v2 -> P (SV (OP_IBinop iop t v1 v2)).
  Hypothesis IH_ICmp    : forall (cmp:icmp)   (t:typ) (v1:value) (v2:value), P v1 -> P v2 -> P (SV (OP_ICmp cmp t v1 v2)).

  Lemma value_ind' : forall (v:value), P v.
    fix IH 1.
    destruct v. destruct e.
    - apply IH_Ident.
    - apply IH_Integer.
    - apply IH_Bool.
    - apply IH_Null.
    - apply IH_Undef.
    - apply IH_IBinop. apply IH. apply IH.
    - apply IH_ICmp. apply IH. apply IH.
  Qed.
End ValueInd.


(* operational semantics --------------------------------------------------- *)

Record path :=
  mk_path {
      fn  : function_id;
      bn  : block_id;
      ins : instr_id;
    }.


Inductive cmd : Set :=
| Step  (i:instr) (p:path)
| Jump  (i:instr)
.                    

Inductive block_entry : Set :=
| Phis (phis : list (local_id * instr)) (p:path)
.

Record cfg := mkCFG
{
  init : path;
  code : path  -> option cmd; 
  funs : function_id -> option (list ident * block_id * instr_id);  
  blks : function_id -> block_id -> option block_entry;  
}.


(* The set of dynamic values manipulated by an LLVM program. This datatype
   uses the "Expr" functor from the Ollvm_ast definition, injecting new base values.
   This allows the semantics to do 'symbolic' execution for things that we don't 
   have a way of interpreting concretely (e.g. undef).   
*)

Inductive dvalue : Set :=
| DV : Expr dvalue -> dvalue
| DVALUE_CodePointer (p : path)
| DVALUE_Addr (a:nat)
.

Definition env  := list (raw_id * dvalue).

Inductive frame : Set :=
| KRet      (e:env) (id:raw_id) (q:path)
| KRet_void (e:env) (q:path)
.       
          
Definition stack := list frame.
Definition state := (path * env * stack)%type.


Definition init_state (CFG:cfg) : state := (init CFG, [], []).

Definition def_id_of_path (p:path) : option raw_id :=
  match ins p with
  | IId id => Some id
  | _ => None
  end.

Definition raw_id_of_ident (i:ident) : option raw_id :=
  match i with
  | ID_Global _ => None
  | ID_Local i => Some i
  end.


Definition lookup_env (e:env) (id:raw_id) : option dvalue :=
  assoc raw_id_eq_dec id e.

Definition eval_iop iop v1 v2 :=
  match v1, v2 with
  | DV (VALUE_Integer _ i1), DV (VALUE_Integer _ i2) =>
    Some (DV (VALUE_Integer _
    match iop with
    | Add => (i1 + i2)
    | Sub => (i1 - i2)
    | Mul => (i1 * i2)
    end))
  | _, _ => None
  end.


Definition eval_icmp icmp v1 v2 :=
  match v1, v2 with
  | DV (VALUE_Integer _ i1), DV (VALUE_Integer _ i2) =>
    Some (DV (VALUE_Bool _
    match icmp with
    | Eq => nat_beq i1 i2
    | Ule => leb i1 i2
    end))
  | _, _ => None
  end.

Definition eval_expr {A:Set} (f:env -> A -> option dvalue) (e:env) (o:Expr A) : option dvalue :=
  match o with
  | VALUE_Ident _ id => 
    do i <- raw_id_of_ident id;
      lookup_env e i
  | VALUE_Integer _ x => Some (DV (VALUE_Integer _ x))
  | VALUE_Null _  => Some (DV (VALUE_Null _))
  | VALUE_Undef _ => Some (DV (VALUE_Undef _))
  | OP_IBinop iop _ op1 op2 =>
    do v1 <- f e op1;
    do v2 <- f e op2;
    (eval_iop iop) v1 v2
  | OP_ICmp cmp _ op1 op2 => 
    do v1 <- f e op1;
    do v2 <- f e op2;
    (eval_icmp cmp) v1 v2

  | _ => None
  end.

Fixpoint eval_op (e:env) (o:value) : option dvalue :=
  match o with
  | SV o' => eval_expr eval_op e o'
  end.



Fixpoint jump (CFG:cfg) (p:path) (e_init:env) (e:env) ps (q:path) (k:stack) : option state :=
  match ps with
  | [] => Some (q, e, k)
  | (id, (INSTR_Phi _ ls))::rest => 
    match assoc ident_eq_dec (ID_Local (bn p)) ls with
    | Some op => match eval_op e_init op with
                | Some dv => jump CFG p e_init ((id,dv)::e) rest q k
                | None => None
                end
    | None => None
    end
  | _ => None
  end.

Fixpoint step (CFG:cfg) (s:state) : option state :=
  let '(p, e, k) := s in
  do cmd <- (code CFG) p;
    match cmd with
      
    | Step (INSTR_Op op) p' =>
      do id <- def_id_of_path p;
      do dv <- eval_op e op;
       Some (p', (id, dv)::e, k)
        
    | Step (INSTR_Call (ret_ty,ID_Global f) args) p' =>
      do id <- def_id_of_path p;
      do fn <- (funs CFG) f;
      let '(ids, blk, i) := fn in
      do ids' <- map_option raw_id_of_ident ids;
      do dvs <-  map_option (eval_op e) (map snd args);
      match ret_ty with
      | TYPE_Void => Some (mk_path f blk i, combine ids' dvs, (KRet_void e p')::k)
      | _ => Some (mk_path f blk i, combine ids' dvs, (KRet e id p')::k)
      end

(*        
    | Step (INSTR_Alloca t) p'      => None
    | Step (INSTR_Load t ptr) p'    => None
    | Step (INSTR_Store val ptr) p' => None
 *)
        
    | Step (INSTR_Unreachable) _ => None
                                                       
    | Jump (INSTR_Ret (t, op)) =>
      match k, eval_op e op with
      | (KRet e' id p') :: k', Some dv => Some (p', (id, dv)::e', k')
      | _, _ => None
      end

    | Jump (INSTR_Ret_void) =>
      match k with
      | (KRet_void e' p')::k' => Some (p', e', k')
      | _ => None
      end

    | Jump (INSTR_Br (_,op) (_, br1) (_, br2)) =>
      do br <-
      match eval_op e op  with
      | Some (DV (VALUE_Bool _ true))  => Some br1
      | Some (DV (VALUE_Bool _ false)) => Some br2
      | Some _ => None
      | None => None
      end;
      do lbl <- raw_id_of_ident br;
        match (blks CFG) (bn p) lbl with
          | Some (Phis ps q) => 
            jump CFG p e e ps q k
          | None => None
        end
        
    | Jump (INSTR_Br_1 (_, br)) =>
      do lbl <- raw_id_of_ident br;
        match (blks CFG) (bn p) lbl with
          | Some (Phis ps q) => 
            jump CFG p e e ps q k
          | None => None
        end
      
                              
    | _ => None
    end.

Definition addr := nat.

Inductive mem d : Type :=
| Alloc (t:typ)  (k:addr -> d)
| Load  (a:addr) (k:dvalue -> d)
| Store (a:addr) (v:dvalue) (k:d)
.    

(* Domain of semantics *)
CoInductive D X :=
| Ret : X -> D X
| Fin : D X
| Err : D X 
| Tau : D X -> D X
| Eff : mem (D X) -> D X
.

(* TODO: look at Gil's paco library and read the paper about extensible coinduction *)
(*
(* Domain of semantics *)
CoInductive D' (E:Type -> Type) (X:Type) : Type :=
| Ret' : X -> D' E X
| Fin' : D' E X
| Err' : D' E X 
| Tau' : D' E X -> D' E X
| Eff' : forall (E':Type -> Type) (f: forall x, E x -> E' x), (E (D' E' X)) -> D' E X
.
*)

Definition mtype := list dvalue.
Definition undef := DV (VALUE_Undef _).
                         
CoFixpoint memD {A} (memory:mtype) (d:D A) : D A :=
  match d with
    | Ret a => Ret a
    | Fin => Fin
    | Err => Err
    | Tau d'            => Tau (memD memory d')
    | Eff (Alloc t k)   => Tau (memD (memory ++ [undef]) (k (List.length memory)))
    | Eff (Load a k)    => Tau (memD memory (k (nth_default undef memory a)))
    | Eff (Store a v k) => Tau (memD (replace memory a v) k)
  end.



(* Parameterize by an "effects relation" that also constrains the effecs other information? *)
Inductive d_equiv_mem_step {A} (R: D A -> D A -> Prop) : mem (D A) -> mem (D A) -> Prop :=
| d_equiv_mem_Alloc : forall n f g, (forall (a:addr), R (f a) (g a)) -> d_equiv_mem_step R (Alloc n f) (Alloc n g)
| d_equiv_mem_Load  : forall a f g, (forall (dv:dvalue), R (f dv) (g dv)) -> d_equiv_mem_step R (Load a f) (Load a g)
| d_equiv_mem_Store : forall a n d1 d2, (R d1 d2) -> d_equiv_mem_step R (Store a n d1) (Store a n d2)
.    


Inductive d_equiv_step {A} (R:D A -> D A -> Prop) : D A -> D A -> Prop :=
| d_equiv_step_ret : forall a, d_equiv_step R (Ret a) (Ret a)
| d_equiv_step_fin : d_equiv_step R Fin Fin
| d_equiv_step_err : d_equiv_step R Err Err
| d_equiv_step_tau : forall d1 d2, R d1 d2 -> d_equiv_step R (Tau d1) (Tau d2)
| d_equiv_step_lft : forall d1 d2, d_equiv_step R d1 d2 -> d_equiv_step R (Tau d1) d2
| d_equiv_step_rgt : forall d1 d2, d_equiv_step R d1 d2 -> d_equiv_step R d1 (Tau d2)
| d_equiv_step_eff : forall m1 m2, d_equiv_mem_step R m1 m2 -> d_equiv_step R (Eff m1) (Eff m2)
.    

Hint Constructors d_equiv_mem_step d_equiv_step.  (* d_equiv *)

Definition d_equiv {A} (p q : D A) := paco2 (@d_equiv_step A) bot2 p q.
Hint Unfold d_equiv.
Lemma d_equiv_gen_mon A : monotone2 (@d_equiv_step A).
  pmonauto.
Proof.
Admitted.

Hint Resolve d_equiv_gen_mon : paco.

(*
CoInductive d_equiv {A} : D A -> D A -> Prop :=
| d_equiv_fix : forall d1 d2,
  d_equiv_step d_equiv d1 d2 ->
  d_equiv d1 d2.
*)

Ltac punfold' H := let x := fresh "_x_" in
  repeat red in H;
  let G := type of H in paco_class G (@pacounfold);
  intro x; match goal with [x:=?lem|-_] => clear x; eapply lem in H end.



Section D_EQUIV_COIND.

  Variable A : Type.
  Variable R : D A -> D A -> Prop.

  Variables (p:D A) (q:D A).
  Hypothesis Hrpq : R p q.
  Hypothesis H : forall d1 d2,
    R d1 d2 -> d_equiv_step R d1 d2.
  
  Theorem d_equiv_coind :
    d_equiv p q.
  Proof.
    revert p q Hrpq.
    pcofix CIH.
    intros ? ? Hr.
    apply H in Hr. revert r CIH. induction Hr; intros; subst; try solve [clear CIH; auto].
    - pfold. constructor. right. auto.
    - pfold. constructor. specialize (IHHr r CIH).
      punfold IHHr.
    - pfold. constructor. specialize (IHHr r CIH).
      punfold IHHr.
    - pfold.
      constructor. 
      inversion H0; subst.
      + constructor. intros. right. eauto. 
      + constructor. intros. right. eauto. 
      + constructor. right. eauto. 
  Qed.
(*
    
    cofix CIH.
    intros ? ? Hr.
    apply H in Hr. induction Hr; subst; try solve [clear CIH; auto].
    - constructor. constructor. eapply CIH. apply H0. 
    - constructor. constructor. eapply CIH. apply H0.
    - constructor. constructor. eapply CIH. apply H0.
    - constructor. constructor.
      inversion H0; subst.
      + constructor. intros. apply CIH. apply H1.
      + constructor. intros. apply CIH. apply H1.
      + constructor. apply CIH. assumption.
*)

End D_EQUIV_COIND.
Arguments d_equiv_coind [_] _ [_ _] _ _.

Check d_equiv_coind.


Fixpoint taus {A} (n:nat) (d:D A) : D A :=
  match n with
  | 0 => d
  | S n => Tau (taus n d)
  end.

Lemma stutter : forall {A} (d1 d2 : D A) n m, d_equiv (taus n d1) (taus m d2) -> d_equiv d1 d2.
Proof.
  intros.
  generalize dependent m.
  induction n.
  induction m. simpl.
  intros. assumption.
  simpl. intros. apply IHm. simpl. 
Admitted.  

Inductive Empty :=.
Definition DLim := D Empty.

Section UNFOLDING.

Definition id_match_d {A} (d:D A) : D A :=
  match d with
    | Ret a => Ret a
    | Fin => Fin
    | Err => Err
    | Tau d' => Tau d'
    | Eff m => Eff m
  end.

Lemma id_d_eq : forall A (d:D A),
  d = id_match_d d.
Proof.
  destruct d; auto.
Qed.

End UNFOLDING.
Arguments id_d_eq {_} _ .

Definition mem_map {A B} (f:A -> B) (m:mem A) : mem B :=
  match m with
  | Alloc t g => Alloc t (fun a => f (g a))
  | Load a g  => Load a (fun dv => f (g dv))
  | Store a dv d => Store a dv (f d)
  end.

CoFixpoint d_map {A B} (f:A -> B) (d:D A) : D B :=
  match d with
    | Ret a => Ret (f a)
    | Fin => Fin
    | Err => Err
    | Tau d' => Tau (d_map f d')
    | Eff m => Eff (mem_map (d_map f) m)
  end.

Class Functor (F:Type -> Type) (equiv:forall A, F A -> F A -> Prop) :=
  { fmap {A B} : (A -> B) -> F A -> F B
  ; fmap_id : forall A (a:F A), equiv _ (fmap id a) a
  ; fmap_comp : forall A B C (f:A -> B) (g:B -> C) (a:F A),
      equiv _ (fmap g (fmap f a)) (fmap (fun a => g (f a)) a)
  }.

Instance functor_option : Functor option (fun A => @eq (option A)) :=
  { fmap := @option_map }.
Proof.
  - abstract (destruct a; simpl; auto).
  - abstract (destruct a; simpl; auto).
Defined. 

(*
Instance functor_mem_map : Functor (mem nat) :=
  { fmap := mem_map }.
*)

Instance functor_d : Functor D (@d_equiv) :=
  { fmap := @d_map }.
Proof.
  - intros. 
    set (R (d1 d2:D A) := d1 = d_map id d2).
    apply d_equiv_coind with (R := R).
    + subst R; simpl; auto.
    + unfold R at 1. intros. subst d1.
      destruct d2;
        try solve [rewrite id_d_eq; rewrite id_d_eq at 1; simpl; constructor; unfold R; auto].
(*
  - intros. 
    set (R (d1 d2:D C) := exists a, d1 =  d_map g (d_map f a) /\
                                    d2 = d_map (fun a0 : A => g (f a0)) a).
    apply d_equiv_coind with (R:=R).
    + unfold R; eauto.
    + unfold R at 1. intros ? ? [d [-> ->]].
      destruct d;
        try solve [rewrite id_d_eq at 1; rewrite id_d_eq; simpl; constructor; unfold R; eauto].
Qed.
 *)
Admitted.      

(* Note: for guardedness, bind Ret introduces extra Tau *)
Definition bind {A B} (m:D A) (f:A -> D B) : D B :=
  (cofix bindf m:= 
     match m with
       | Ret a => Tau (f a)
       | Fin => Fin
       | Err => Err
       | Tau d' => Tau (bindf d')
       | Eff m => Eff (mem_map bindf m)
     end) m.

Definition lift_option_d {A B} (m:option A) (f: A -> D B) : D B :=
  match m with
    | None => Err
    | Some b => f b
  end.

Notation "'do' x <- m ; f" := (lift_option_d m (fun x => f)) 
   (at level 200, x ident, m at level 100, f at level 200).


Fixpoint stepD (CFG:cfg) (s:state) : D state :=
  let '(p, e, k) := s in
  do cmd <- (code CFG) p;
    match cmd with
      
    | Step (INSTR_Op op) p' =>
      do id <- def_id_of_path p;
      do dv <- eval_op e op;
       Ret (p', (id, dv)::e, k)
        
    | Step (INSTR_Call (ret_ty,ID_Global f) args) p' =>
      do id <- def_id_of_path p;
      do fn <- (funs CFG) f;
      let '(ids, blk, i) := fn in
      do ids' <- map_option raw_id_of_ident ids;
      do dvs <-  map_option (eval_op e) (map snd args);
      match ret_ty with
      | TYPE_Void => Ret (mk_path f blk i, combine ids' dvs, (KRet_void e p')::k)
      | _ => Ret (mk_path f blk i, combine ids' dvs, (KRet e id p')::k)
      end
        
    | Step (INSTR_Unreachable) _ => Err
                                                       
    | Jump (INSTR_Ret (t, op)) =>
      match k, eval_op e op with
      | [], Some dv => Fin
      | (KRet e' id p') :: k', Some dv => Ret (p', (id, dv)::e', k')
      | _, _ => Err
      end

    | Jump (INSTR_Ret_void) =>
      match k with
      | [] => Fin
      | (KRet_void e' p')::k' => Ret (p', e', k')
      | _ => Err
      end
        
    | Jump (INSTR_Br (_,op) (_, br1) (_, br2)) =>
      do br <-
      match eval_op e op  with
      | Some (DV (VALUE_Bool _ true))  => Some br1
      | Some (DV (VALUE_Bool _ false)) => Some br2
      | Some _ => None
      | None => None
      end;
      do lbl <- raw_id_of_ident br;
        match (blks CFG) (bn p) lbl with
          | Some (Phis ps q) => 
            lift_option_d (jump CFG p e e ps q k) (@Ret state)
          | None => Err
        end
        
    | Jump (INSTR_Br_1 (_, br)) =>
      do lbl <- raw_id_of_ident br;
        match (blks CFG) (bn p) lbl with
          | Some (Phis ps q) => 
            lift_option_d (jump CFG p e e ps q k) (@Ret state)
          | None => Err
        end
      
    | Step (INSTR_Alloca t) p' =>
      do id <- def_id_of_path p;
      Eff (Alloc t (fun (a:nat) => Ret (p', (id, DVALUE_Addr a)::e, k)))
        
    | Step (INSTR_Load t (_,ptr)) p' =>
      do id <- def_id_of_path p;
      do dv <- eval_op e ptr;
      match dv with
        | DVALUE_Addr a => Eff (Load a (fun dv => Ret (p', (id, dv)::e, k)))
        | _ => Err
      end

        
    | Step (INSTR_Store (_, val) (_, ptr)) p' =>
      match eval_op e val, eval_op e (SV (VALUE_Ident _ ptr)) with
      | Some dv, Some (DVALUE_Addr a) => Eff (Store a dv (Ret (p', e, k)))
      | _, _ => Err
      end

          
    | _ => Err
    end.


(* Note: codomain is D'  *)
CoFixpoint sem (CFG:cfg) (s:state) : DLim :=
  bind (stepD CFG s) (sem CFG).


Definition run (CFG:cfg) : DLim :=
  memD [] (sem CFG (init_state CFG)).


Lemma sem_unfold : forall CFG s, 
  sem CFG s = bind (stepD CFG s) (sem CFG).
Proof.
  intros. rewrite (id_d_eq (sem CFG s)). rewrite id_d_eq. simpl. auto.
Qed.


Definition CFG_equiv (CFG1 CFG2:cfg) : Prop :=
  d_equiv (sem CFG1 (init_state CFG1)) (sem CFG2 (init_state CFG2)).

Lemma dequiv_mem_step_id : forall A (m : mem _) (R: D A -> D A -> Prop), (forall d', R d' d') -> d_equiv_mem_step R m m.
Proof.
  intros.
  destruct m; auto.
Qed.  

Lemma dequiv_step_id : forall A d (R: D A -> D A -> Prop), (forall d', R d' d') -> d_equiv_step R d d.
Proof.
  intros.
  destruct d; auto.
  constructor.
  apply dequiv_mem_step_id; auto.
Qed.  
  

Lemma CFG_Equiv_refl : forall CFG, CFG_equiv CFG CFG.
Proof.
  intros CFG.
  unfold CFG_equiv.
  set (R (d1 d2 : DLim) := d1 = d2).
  eapply (d_equiv_coind R).
  unfold R. reflexivity.
  intros.
  unfold R in H. subst.
  apply dequiv_step_id.
  intros. unfold R. reflexivity.
Qed.



  