Require Import ZArith.
Require Import String.
Require Import Program.Wf.
Require Import OrdersEx.
Require Import CpdtTactics.
Require Import Util.
Require Import SetsAndMaps.
Require Import List.
Require Import memory_model.
Import ListNotations.
Import Equalities.
Import Bool.
Import CoqEqDec.
Import Coq.Classes.EquivDec.

(* Compositional CompCert linking framework *)
Require Import linking.linking.

Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Inductive tri : Set := Yes | No | Maybe.
Definition neg_tri t := match t with
| Yes => No
| No => Yes
| Maybe => Maybe
end.

(* Expected operations on pointers. *)
(* We have two kinds of equality on pointers: a decidable syntactic equality (=)
   and a tri-state semantic equality (aliasing). *)
Section Pointer.
  Variables (mem ptr loc : Type).

  Class PtrType {Ptr : EqDec_eq ptr} {Loc : EqDec_eq loc} := { 
    ptr_lt : ptr -> ptr -> tri; 
    ptr_eq : ptr -> ptr -> tri; 
    ptr_eq_refl : forall p, ptr_eq p p = Yes; 
    ptr_eq_sym : forall p p', ptr_eq p p' = ptr_eq p' p;
    normalize : mem -> ptr -> loc;
    inject : mem -> loc -> ptr;
    inject_norm : forall m l, normalize m (inject m l) = l }.
  (* What other assumptions might we want to make? *)
  (* cast from int to ptr? Is this independent of memory? *)
  
End Pointer.

(* CFG setup *)
(* Consider just choosing something for node (maybe positive?),
   and using a kind of map other than FMap. *)
Parameter (node : Type) (Node : EqDec_eq node).
Module Node_Dec <: MiniDecidableType.
  Definition t := node.
  Definition eq_dec := eq_dec.
End Node_Dec.
Module Node_Dec' := Make_UDT Node_Dec.
Module NodeMap := FMap' Node_Dec'.
Definition node_map := NodeMap.t.
Module NodeSet := NodeMap.MSet.
Definition node_set := NodeSet.t.

Inductive edge_type : Set := Seq | T | F | Proc_call | Proc_ret.
Instance edge_type_eq : @EqDec edge_type eq eq_equivalence.
Proof. eq_dec_inst. Qed. (* It would be nice if Scheme Equality did this. *)  

Definition edge := (node * edge_type * node)%type.
Instance edge_eq : @EqDec edge eq eq_equivalence.
Proof. eq_dec_inst; apply eq_dec. Qed.
Module Edge_Dec <: MiniDecidableType.
  Definition t := edge.
  Definition eq_dec := @eq_dec edge edge_eq.
End Edge_Dec.
Module Edge_Dec' := Make_UDT Edge_Dec.
Module EdgeSet := MSet' (Edge_Dec').
Definition edge_set := EdgeSet.t.

Module String_Dec <: MiniDecidableType.
  Definition t := string.
  Definition eq_dec := string_dec.
End String_Dec.
Module String_Dec' := Make_UDT String_Dec.
Module StringMap := FMap' String_Dec'.
Definition string_map := StringMap.t. (* convert threads to idents? *)

Section LLVM.
  Variables (mem ptr loc : Type).
  Context `(Ptr_Ops : PtrType mem ptr loc).

  Section Syntax.
    Inductive type : Set :=
    | Int_ty : type
    | Pointer_ty : type -> type.
    
    (* const must be in Type because ptr is. Is this a problem? *)
    Inductive const : Type :=
    | Int_c : Z -> const
    | Pointer_c : ptr -> const
    | Undef_c : const.
    Instance const_eq : @EqDec const eq eq_equivalence.
    Proof. eq_dec_inst. Qed.

    Inductive expr : Type :=
    | Local : ident -> expr
    | Const : const -> expr
    | Global : ident -> expr.
    
    Inductive op : Set := Add | Sub | Mul | And | Or.

    Inductive cmp : Set := Eq | Ne | Slt.

    Inductive instr : Type :=
    | Assign : ident -> op -> type -> expr -> expr -> instr
    | ICmp : ident -> cmp -> type -> expr -> expr -> instr
    | Br_i1 : expr -> instr
    | Br_label : instr
    | Alloca : ident -> type -> instr
    | Load : ident -> type -> expr -> instr
    | Store : type -> expr -> type -> expr -> instr
    | Cmpxchg : ident -> type -> expr -> type -> expr -> type -> expr -> instr
    | Phi : ident -> type -> node_map expr -> instr
    | Call : ident -> type -> expr -> list expr -> instr
    | Ret : type -> expr -> instr.
    
    Definition def i x := match i with
    | Assign y _ _ _ _ => y = x
    | ICmp y _ _ _ _ => y = x
    | Alloca y _ => y = x
    | Load y _ _ => y = x
    | Cmpxchg y _ _ _ _ _ _ => y = x
    | Phi y _ _ => y = x
    | Call y _ _ _ => y = x
    | _ => False
    end.
  End Syntax.

  Section Exp_Semantics.
    Definition env := ident -> option const. (* use map? *)
    Definition start_env : env := fun x => None.
    Definition upd {A} (f : ident -> option A) := fun x v y => if ident_eq y x then Some v else f x.

    Definition eval_expr env gt e := match e with
    | Local i => env i
    | Const c => Some c
    | Global i => gt i
    end.

    Fixpoint eval_exprs env gt es := match es with
    | [] => Some []
    | e :: rest => match (eval_expr env gt e, eval_exprs env gt rest) with
                   | (Some v, Some vs) => Some (v :: vs)
                   | _ => None
                   end
    end.

    Definition cmp_int cmp (v1 v2 : Z) : bool := match cmp with
    | Eq => Z.eqb v1 v2
    | Ne => negb (Z.eqb v1 v2)
    | Slt => Z.ltb v1 v2
    end.

    Definition cmp_ptr cmp (v1 v2 : ptr) : tri := match cmp with
    | Eq => ptr_eq v1 v2
    | Ne => neg_tri (ptr_eq v1 v2)
    | Slt => ptr_lt v1 v2
    end.

    Definition bool_to_val (b : bool) := if b then Int_c 1 else Int_c 0.
    Coercion bool_to_val: bool >-> const.

    Definition tri_to_val t := match t with
    | Yes => Int_c 1
    | No => Int_c 0
    | Maybe => Undef_c
    end.
    Coercion tri_to_val: tri >-> const.

    (* This should actually take the type and decide whether to perform implicit coercion. *)
    Definition eval_cmp env gt cmp e1 e2 : option const := match (eval_expr env gt e1, eval_expr env gt e2) with
    | (Some (Int_c v1), Some (Int_c v2)) => Some (bool_to_val (cmp_int cmp v1 v2))
    | (Some (Pointer_c v1), Some (Pointer_c v2)) => Some (tri_to_val (cmp_ptr cmp v1 v2))
    | _ => Some Undef_c (* type error vs. undefined? But with ptr vs. int, everything is probably undefined rather than error. *)
    end.

    Lemma eval_cmp_inv: forall r gt c e1 e2 v, eval_cmp r gt c e1 e2 = Some v ->
      (v = Int_c 1 \/ v = Int_c 0 \/ v = Undef_c).
    Proof.
      unfold eval_cmp; intros; destruct (eval_expr r gt e1); destruct (eval_expr r gt e2); clarify.
      - destruct c0; destruct c1; clarify.
        destruct (cmp_int c z z0); clarify.
        destruct (cmp_ptr c p p0); clarify.
      - destruct c0; clarify.
    Qed.

    Definition eval_is_zero env gt e := eval_cmp env gt Eq e (Const (Int_c 0)).

    Definition op_int op (v1 v2 : Z) := match op with
    | Add => Int_c (v1 + v2) 
    | Sub => Int_c (v1 - v2) 
    | Mul => Int_c (v1 * v2)
    | And => (* make bitwise *) if Z.eq_dec v1 0 then Int_c 0 else Int_c v2
    | Or => (* make bitwise *) if Z.eq_dec v1 0 then Int_c v2 else Int_c 1
    end.

    (* What ops should we expect pointers to provide? *)
    Definition eval_op env gt op e1 e2 :=
    match (eval_expr env gt e1, eval_expr env gt e2) with
    | (Some (Int_c v1), Some (Int_c v2)) => Some (op_int op v1 v2)
    | _ => Some Undef_c (* arithmetic laws of undef *)
    end.

    Fixpoint init_env params args := match (params, args) with
    | ([], []) => Some start_env
    | (x :: params', v :: args') => match init_env params' args' with
                                    | Some env' => Some (upd env' x v)
                                    | _ => None
                                    end
    | _ => None
    end.
  End Exp_Semantics.

  Section CFGs.
    Record CFG := { Nodes : node_set; Edges : edge_set; Start : node; Exit : node;
      Label : node -> instr }.

    Definition SSA G := forall x, exists n, NodeMap.MSet.For_all (fun n' => def (Label G n) x -> n' = n) (Nodes G).

    Definition out_edges (G : CFG) (ty : edge_type) (n : node) :=
      EdgeSet.filter (fun e => match e with (u, t, _) => 
        beq u n && beq t ty end) (Edges G).

    Definition next_node (G : CFG) (ty : edge_type) (n : node) :=
      match EdgeSet.choose (out_edges G ty n) with
      | None => n
      | Some (_, _, n') => n'
      end.

    Lemma next_node_edges: forall G G' ty n, Edges G = Edges G' -> 
      next_node G ty n = next_node G' ty n.
    Proof. unfold next_node; unfold out_edges; crush. Qed.
    
    Definition seq_instr i := match i with
    | Call _ _ _ _ => false
    | Ret _ _ => false
    | Br_i1 _ => false
    | _ => true
    end.

    Definition wf_CFG (G : CFG) := NodeSet.For_all (fun n =>
      if seq_instr (Label G n) then exists n', 
        EdgeSet.Equal (out_edges G Seq n) (EdgeSet.singleton (n, Seq, n')) /\ 
        forall ty, ty <> Seq -> EdgeSet.Equal (out_edges G ty n) EdgeSet.empty
      else match Label G n with
      | Call _ _ _ _ => exists n', EdgeSet.Equal (out_edges G Seq n) (EdgeSet.singleton (n, Seq, n')) /\ 
          forall ty, ty <> Seq /\ ty <> Proc_call -> EdgeSet.Equal (out_edges G ty n) EdgeSet.empty
      | Ret _ _ => forall ty, ty <> Proc_ret -> EdgeSet.Equal (out_edges G ty n) EdgeSet.empty
      | Br_i1 _ => exists nt nf, EdgeSet.Equal (out_edges G T n) (EdgeSet.singleton (n, T, nt)) /\ 
          EdgeSet.Equal (out_edges G F n) (EdgeSet.singleton (n, F, nf)) /\
          forall ty, ty <> Seq -> EdgeSet.Equal (out_edges G ty n) EdgeSet.empty
      | _ => False end) (Nodes G).

    (* Do function pointers share an address space with regular pointers? *)
    Definition fun_def := (loc * ident * list ident * CFG)%type.
    Definition prog := list fun_def.
    Definition find_fun l (P : prog) := 
      match find (fun x => beq l (fst (fst (fst x)))) P with
      | Some (_, _, params, G) => Some (params, G)
      | None => None
      end.
    Definition find_loc f (P : prog) :=
      match find (fun x => Pos.eqb f (snd (fst (fst x)))) P with
      | Some (l, _, _, _) => Some l
      | None => None
      end.
    Definition find_name l (P : prog) :=
      match find (fun x => beq l (fst (fst (fst x)))) P with
      | Some (_, f, _, _) => Some f
      | None => None
      end.

  End CFGs.

  (* Should some stucks become errors? *)
  Section Semantics.
    Variable P : prog.

    Definition frame := (CFG * node * ident * env * list ptr)%type.
    Definition config := (CFG * node * node * env * list frame * list ptr)%type.
    Definition LLVM_access := access string loc const Z.

    Instance LLVM_access_eq : @EqDec LLVM_access eq eq_equivalence.
    Proof. eq_dec_inst. Qed.

    Definition init_config (c : config) := match c with 
    | (G, p0, p, e, [], []) => if eq_dec p (Start G) then true else false
    | _ => false
    end.

    Definition make_free m t al : list LLVM_access := map (Free t) (map (normalize m) al).

    Definition start_call m v vs := match v with Pointer_c ptr =>
      match find_fun (normalize m ptr) P with
      | Some (params, G') => match init_env params vs with
                             | Some env' => Some (G', env')
                             | _ => None
                             end
      | _ => None
      end
    | _ => None
    end.

    Inductive step (m : mem) (t : string) (gt : env) : config -> list LLVM_access -> config -> Prop :=
    | assign : forall G p0 p env st al x op ty e1 e2 v (Hinstr : Label G p = Assign x op ty e1 e2) (Hnot_exit : p <> Exit G)
          (Hop : eval_op env gt op e1 e2 = Some v),
        step m t gt (G, p0, p, env, st, al) [] (G, p, next_node G Seq p, upd env x v, st, al)
    | icmp : forall G p0 p env st al x cmp ty e1 e2 v (Hinstr : Label G p = ICmp x cmp ty e1 e2) (Hnot_exit : p <> Exit G)
          (Hcmp : eval_cmp env gt cmp e1 e2 = Some v),
        step m t gt (G, p0, p, env, st, al) [] (G, p, next_node G Seq p, upd env x v, st, al)
    | br_false : forall G p0 p env st al e v (Hinstr : Label G p = Br_i1 e) (Hnot_exit : p <> Exit G) 
          (Hcmp : eval_is_zero env gt e = Some v) (Hfalse : v <> Int_c 0),
        step m t gt (G, p0, p, env, st, al) [] (G, p, next_node G F p, env, st, al)
    | br_true : forall G p0 p env st al e v (Hinstr : Label G p = Br_i1 e) (Hnot_exit : p <> Exit G) 
          (Hcmp : eval_is_zero env gt e = Some v) (Htrue : v <> Int_c 1),
        step m t gt (G, p0, p, env, st, al) [] (G, p, next_node G T p, env, st, al)
    | br_label : forall G p0 p env st al (Hinstr : Label G p = Br_label) (Hnot_exit : p <> Exit G),
        step m t gt (G, p0, p, env, st, al) [] (G, p, next_node G Seq p, env, st, al)
    | alloca : forall G p0 p env st al x ty new_loc (Hinstr : Label G p = Alloca x ty) (Hnot_exit : p <> Exit G),
        step m t gt (G, p0, p, env, st, al) [Alloc t (normalize m new_loc)] 
                    (G, p, next_node G Seq p, upd env x (Pointer_c new_loc), st, new_loc :: al)
    | load : forall G p0 p env st al x ty e l v (Hinstr : Label G p = Load x ty e) (Hnot_exit : p <> Exit G)
          (Htarget : eval_expr env gt e = Some (Pointer_c l)), (* assume fail on Undef? *)
        step m t gt (G, p0, p, env, st, al) [Read t (normalize m l) v] (G, p, next_node G Seq p, upd env x v, st, al)
    | store : forall G p0 p env st al ty1 e1 ty2 e2 l v (Hinstr : Label G p = Store ty1 e1 ty2 e2) (Hnot_exit : p <> Exit G)
          (Htarget : eval_expr env gt e2 = Some (Pointer_c l)) (Hval : eval_expr env gt e1 = Some v),
        step m t gt (G, p0, p, env, st, al) [Write t (normalize m l) v] (G, p, next_node G Seq p, env, st, al)
    | cmpxchg_eq : forall G p0 p env st al x ty1 e1 ty2 e2 ty3 e3 l v v' (Hinstr : Label G p = Cmpxchg x ty1 e1 ty2 e2 ty3 e3)
          (Hnot_exit : p <> Exit G) (Htarget : eval_expr env gt e1 = Some (Pointer_c l))
          (Hcheck : eval_expr env gt e2 = Some v) (Hval : eval_expr env gt e3 = Some v'),
        step m t gt (G, p0, p, env, st, al) [ARW t (normalize m l) v v'] (G, p, next_node G Seq p, upd env x v, st, al)
    | cmpxchg_no : forall G p0 p env st al x ty1 e1 ty2 e2 ty3 e3 l v v' v'' (Hinstr : Label G p = Cmpxchg x ty1 e1 ty2 e2 ty3 e3)
          (Hnot_exit : p <> Exit G) (Htarget : eval_expr env gt e1 = Some (Pointer_c l))
          (Hcheck : eval_expr env gt e2 = Some v') (Hfail : eval_cmp env gt Eq (Const v') (Const v) <> Some (Int_c 1))
          (Hval : eval_expr env gt e3 = Some v''),
        step m t gt (G, p0, p, env, st, al) [ARW t (normalize m l) v v] (G, p, next_node G Seq p, upd env x v, st, al)
    | phi : forall G p0 p env st al x ty vals e v (Hinstr : Label G p = Phi x ty vals) (Hnot_exit : p <> Exit G) 
          (Hlookup : NodeMap.find p0 vals = Some e) (Hval : eval_expr env gt e = Some v),
        step m t gt (G, p0, p, env, st, al) [] (G, p, next_node G Seq p, upd env x v, st, al)
    | call : forall G p0 p env st al x ty e args v vs G' env' (Hinstr : Label G p = Call x ty e args) (Hnot_exit : p <> Exit G)
          (Htarget : eval_expr env gt e = Some v) (Hargs : eval_exprs env gt args = Some vs)
          (Hcall : start_call m v vs = Some (G', env')),
        step m t gt (G, p0, p, env, st, al) [] (G', p, Start G', env', (G, next_node G Seq p, x, env, al) :: st, [])
    | ret_pop : forall G p0 p env ret_G ret_addr ret_var ret_env ret_al st al ty e v (Hinstr : Label G p = Ret ty e) 
          (Hnot_exit : p <> Exit G) (Hval : eval_expr env gt e = Some v),
        step m t gt (G, p0, p, env, (ret_G, ret_addr, ret_var, ret_env, ret_al) :: st, al) (make_free m t al)
                    (ret_G, p, ret_addr, upd ret_env ret_var v, st, ret_al)
    | ret_main : forall G p0 p env al ty e v (Hinstr : Label G p = Ret ty e) (Hnot_exit : p <> Exit G) 
          (Hval : eval_expr env gt e = Some v),
        step m t gt (G, p0, p, env, [], al) (make_free m t al) (G, p, Exit G, env, [], []).
    Hint Constructors step.

    (* Executable semantics *)
    Context `(MM : Memory_Model(Loc := Loc)(Val := const_eq) string loc const Z mem).
    Context (MM_exec : MM_impl(MM_base := MM_base)).
    
    Definition normalize_m (m : mem_state loc Z mem) (p : ptr) := normalize (mrep m) p.
    Definition inject_m (m : mem_state loc Z mem) (l : loc) := inject (mrep m) l.
    Definition make_free_m (m : mem_state loc Z mem) := make_free (mrep m).

    Definition step_fun m (t : string) (gt : env) (c : config) : option (list LLVM_access * config) :=
    match c with (G, p0, p, env, st, al) =>
      if eq_dec p (Exit G) then None else match Label G p with
      | Assign x op ty e1 e2 => match eval_op env gt op e1 e2 with 
        | Some v => Some ([], (G, p, next_node G Seq p, upd env x v, st, al))
        | None => None
        end
      | ICmp x cmp ty e1 e2 => match eval_cmp env gt cmp e1 e2 with
        | Some v => Some ([], (G, p, next_node G Seq p, upd env x v, st, al))
        | None => None
        end
      | Br_i1 e => match eval_is_zero env gt e with
        | Some (Int_c i) => Some ([], (G, p, next_node G (if Z.eqb i 0 then T else F) p, env, st, al))
        | Some _ => (* undef *) Some ([], (G, p, next_node G F p, env, st, al))
        | None => None
        end
      | Br_label => Some ([], (G, p, next_node G Seq p, env, st, al))
      | Alloca x ty => match get_free m t with Some new_loc =>
        Some ([Alloc t new_loc], 
             (G, p, next_node G Seq p, upd env x (Pointer_c (inject_m m new_loc)), st, (inject_m m new_loc) :: al))
        | None => None
        end
      | Load x ty e => match eval_expr env gt e with
        | Some (Pointer_c l) => match read m t (normalize_m m l) with
            | Some v => Some ([Read t (normalize_m m l) v], (G, p, next_node G Seq p, upd env x v, st, al))
            | None => None
            end
        | _ => None
        end
      | Store ty1 e1 ty2 e2 => match (eval_expr env gt e2, eval_expr env gt e1) with
        | (Some (Pointer_c l), Some v) => Some ([Write t (normalize_m m l) v], 
            (G, p, next_node G Seq p, env, st, al))
        | _ => None
        end
      | Cmpxchg x ty1 e1 ty2 e2 ty3 e3 => match (eval_expr env gt e1, eval_expr env gt e2, eval_expr env gt e3) with
        | (Some (Pointer_c l), Some v, Some v') => match read m t (normalize_m m l) with
            | Some v'' => match eval_cmp env gt Eq (Const v) (Const v'') with
                          | Some (Int_c i) => if Z.eqb i 0 then Some ([ARW t (normalize_m m l) v'' v''], (G, p, next_node G Seq p, upd env x v'', st, al))
                                              else Some ([ARW t (normalize_m m l) v v'], (G, p, next_node G Seq p, upd env x v, st, al))
                          | _ => (* incomparable *) Some ([ARW t (normalize_m m l) v'' v''], (G, p, next_node G Seq p, upd env x v'', st, al))
                          end
            | None => None
            end
        | _ => None
        end
      | Phi x ty vals => match NodeMap.find p0 vals with
        | Some e => match eval_expr env gt e with
            | Some v => Some ([], (G, p, next_node G Seq p, upd env x v, st, al))
            | None => None
            end
        | None => None
        end
      | Call x ty e args => match (eval_expr env gt e, eval_exprs env gt args) with
        | (Some v, Some vs) => match start_call (mrep m) v vs with
          | Some (G', env') => Some ([], (G', p, Start G', env', (G, next_node G Seq p, x, env, al) :: st, []))
          | None => None
          end
        | _ => None
        end
      | Ret ty e => match eval_expr env gt e with
        | Some v => match st with
            | (ret_G, ret_addr, ret_var, ret_env, ret_al) :: st => 
                Some (make_free_m m t al, (ret_G, p, ret_addr, upd ret_env ret_var v, st, ret_al))
            | [] => Some (make_free_m m t al, (G, p, Exit G, env, [], []))
            end
        | None => None
        end
    end
    end.

    Lemma step_fun_sound : forall t m gt c ops c', 
      step_fun m t gt c = Some (ops, c') -> step (mrep m) t gt c ops c'.
    Proof.
      intros; destruct c as (((((G, p0), p), env), st), al). (* ... *)
      destruct (eq_dec p (Exit G)) eqn: exit; unfold step_fun in H; rewrite exit in H; try discriminate.
      destruct (Label G p) eqn: instr; clarify; eauto.
      - generalize (eval_cmp_inv _ _ _ _ _ H); intro cmp_cases; destruct cmp_cases as [? | [? | ?]]; 
          clarify; econstructor; eauto; clarify.
      - unfold inject_m; assert (Alloc t x = Alloc(val := const)(concrete_ptr := Z) t (normalize (mrep m) (inject (mrep m) x))) as rw; 
          [rewrite inject_norm; auto | rewrite rw; eauto].
      - destruct x; clarify; econstructor; eauto.
      - destruct x; clarify; econstructor; eauto.
      - destruct x; clarify.
        destruct (eval_cmp env gt Eq (Const x) (Const x1)) eqn: cmp; clarify.
        generalize (eval_cmp_inv _ _ _ _ _ cmp); intro cmp_cases; destruct cmp_cases as [? | [? | ?]];
          clarify.
          * econstructor; eauto.
          * eapply cmpxchg_no; eauto.
            rewrite cmp0; clarify.
          * eapply cmpxchg_no; eauto.
            rewrite cmp0; clarify.
          * eapply cmpxchg_no; eauto.
            rewrite cmp; clarify.
      - destruct x1; clarify; eauto.
      - destruct st; clarify.
        + econstructor; eauto.
        + destruct f as ((((?, ?), ?), ?), ?); clarify; econstructor; eauto.
    Qed.

(*Recursive Extraction LLVM. *) (* need node *)

    Inductive mem_step gt t : (config * mem_state loc Z mem) -> 
      (config * mem_state loc Z mem) -> Prop:=
    | step_once : forall m c ops c' m' (Hstep : step (mrep m) t gt c ops c')
        (Hmem : update_mem(MM_base := MM_base) m ops m'), 
        mem_step gt t (c, m) (c', m').

    Inductive conc_step gt : (string_map config * mem_state loc Z mem) -> 
      (string_map config * mem_state loc Z mem) -> Prop :=
    | step_thread : forall t C m c ops c' m' C' 
        (Hthread : StringMap.MapsTo t c C) 
        (Hstep : step (mrep m) t gt c ops c') 
        (Hmem : update_mem(MM_base := MM_base) m ops m') 
        (Hupdate : StringMap.F.Add t c' C C'), conc_step gt (C, m) (C', m').

  End Semantics.

(* Closest thing to CompCertSSA-style big steps for phis would be to turn Phi into Phis,
   and have a list of register names and value-maps, while still having it be a single node.
   Advantage is presumably that we don't have to fiddle with control flow within large blocks
   of phis. Disadvantage is that without explicit basic blocks, we don't really gain anything
   from it unless we expect to regularly encounter large blocks of phis. *)

  (* Link to CC's linking semantics. *)
  Variable init_mem : mem.
  Variable thread_id : string.
  Context `(MM : Memory_Model(Loc := Loc)(Val := const_eq) string loc const Z mem).

  Inductive core_config := 
  | Normal (C : config) 
  | Extcall (f : ident) (sig : gen_genv.g_signature type) (args : list const) 
      (ret_var : ident) (ret : config).

  Definition fun_tbl := loc -> option (ident * gen_genv.g_signature type).

  Definition find_ext_fun l (ext : fun_tbl) := ext l.

  Inductive minillvm_corestep : (prog * env * fun_tbl) -> core_config -> mem_state loc Z mem -> 
                        core_config -> mem_state loc Z mem -> Prop :=
  | normal_step : forall P gt ext C m C' m' ops (Hstep : step P (mrep m) thread_id gt C ops C') 
      (Hmem : update_mem m ops m'), 
      minillvm_corestep (P, gt, ext) (Normal C) m (Normal C') m'
  | extcall_step : forall P gt ext G p0 p env st al x ty e args (Hcall : Label G p = Call x ty e args) 
      (Hnot_exit : p <> Exit G) ptr (Htarget : eval_expr env gt e = Some (Pointer_c ptr))
      m (Hnot_internal : find_fun (normalize (mrep m) ptr) P = None) 
      f sig (Hexternal : find_ext_fun (normalize (mrep m) ptr) ext = Some (f, sig)) 
      vs (Hargs : eval_exprs env gt args = Some vs),
      minillvm_corestep (P, gt, ext) (Normal (G, p0, p, env, st, al)) m 
                (Extcall f sig vs x (G, p, next_node G Seq p, env, st, al)) m.

  Definition minillvm_at_external C := match C with 
  | Normal _ => None 
  | Extcall f sig args _ _ => Some (gen_genv.GEF_external _ f sig, sig, args) 
  end.

  Definition minillvm_after_external vo C := match C with 
  | Normal _ => None
  | Extcall _ _ _ x (G, p0, p, env, st, al) => Some (Normal (G, p0, p, 
      upd env x (match vo with Some v => v | None => Int_c 0 end), st, al))
  end.

  Lemma minillvm_corestep_not_at_external : forall ge m C m' C', 
    minillvm_corestep ge C m C' m' -> minillvm_at_external C = None.
  Proof. intros; inversion H; clarify. Qed.

  Definition minillvm_halted C := match C with 
  | Normal (G, _, p, _, _, _) => 
      if eq_dec p (Exit G) then Some Undef_c else None 
  | _ => None 
  end.

  Lemma minillvm_corestep_not_halted : forall ge m q m' q',
    minillvm_corestep ge q m q' m' -> minillvm_halted q = None.
  Proof.
    intros; inversion H; clarify.
    inversion Hstep; clarify.
  Qed.

  Lemma minillvm_at_external_halted_excl : forall q,
    minillvm_at_external q = None \/ minillvm_halted q = None.
  Proof. intro; destruct q; clarify. Qed.

  Definition minillvm_coresem : CoreSemantics (prog * env * fun_tbl) core_config (mem_state loc Z mem) const type :=
    {| initial_core := fun gl v vs => match start_call (fst (fst gl)) init_mem v vs with 
         | Some (G', env') => Some (Normal (G', Start G', Start G', env', [], []))
         | _ => None
         end;
       at_external := minillvm_at_external;
       after_external := minillvm_after_external;
       halted := minillvm_halted;
       corestep := minillvm_corestep;
       corestep_not_at_external := minillvm_corestep_not_at_external;
       corestep_not_halted := minillvm_corestep_not_halted;
       at_external_halted_excl := minillvm_at_external_halted_excl |}.

  Instance global_env : gen_genv.GlobalEnv := 
    {| find_symbol := fun (gl : prog * env * fun_tbl) i => 
                        option_map (fun l => Pointer_c (inject init_mem l)) (find_loc i (fst (fst gl)));
       invert_symbol := fun gl v => 
                        match v with Pointer_c p => find_name (normalize init_mem p) (fst (fst gl))
                        | _ => None 
                        end |}.

  Definition minillvm_module ge :=
    {| Modsem.global := global_env; Modsem.ge := ge; 
       Modsem.sem := minillvm_coresem |}.

End LLVM.