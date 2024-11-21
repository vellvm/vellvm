From Vellvm Require Import
  Utilities
  AstLib
  Semantics.Memory.Sizeof
  LLVMEvents
  LLVMAst
  QC.Utils
  QC.Generators
  Handlers
  QC.DList
  VellvmIntegers
  DynamicTypes.

(* Maybe also import InterpretationStack *)

From ExtLib.Structures Require Export
  Applicative Monad Monoid.

Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.EitherMonad.
Require Export ExtLib.Structures.Functor.

Require Import List.

Import ListNotations.
Import MonadNotation.
Import ApplicativeNotation.

Import Floats.
From Coq Require Import
  ZArith Bool.Bool String.

Require Import QuickChick.Generators.
Require Import QuickChick.Producer.

From ExtLib.Structures Require Export Functor.
(* Import QcDefaultNotation. *)
Open Scope qc_scope.
Open Scope Z_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

Unset Guard Checking.

Module GEN_ALIVE2 (ADDR : MemoryAddress.ADDRESS) (IP:MemoryAddress.INTPTR) (SIZEOF : Sizeof).
  Definition is_nil {A} (l : list A) : bool :=
    match l with
    | nil => true   
    | _ => false
    end.
  
  Module DV := DynamicValues.DVALUE(ADDR)(IP)(SIZEOF).
  Import DV.
  Definition var_context := list (ident * typ).
  Record GenState :=
    mkGenState
      {
        num_void : N
      ; num_raw : N
      ; gen_local_ctx : var_context
                          (* ; backtrack_instrs : list (instr typ) *)
      }.

  Definition init_GenState : GenState
    :=
    {|
      num_void := 0
    ; num_raw := 0
    ; gen_local_ctx := []
    |}.

  Definition increment_void (gs : GenState) : GenState
    :=
    {|
      num_void := N.succ gs.(num_void)
    ; num_raw := gs.(num_raw)
    ; gen_local_ctx := gs.(gen_local_ctx)
    |}.
  
  Definition increment_raw (gs : GenState) : GenState
    :=
    {|
      num_void := gs.(num_void)
    ; num_raw := N.succ gs.(num_raw)
    ; gen_local_ctx := gs.(gen_local_ctx)
    |}.

  Definition replace_local_ctx (ctx : var_context) (gs : GenState) : GenState
    :=
    {|
      num_void := gs.(num_void)
    ;  num_raw := gs.(num_raw)
    ; gen_local_ctx := ctx
    |}.
    
  Definition GenALIVE2 := (eitherT string (stateT GenState G)).

  Definition get_void (gs : GenState) : N
    := gs.(num_void).
  
  Definition get_raw (gs : GenState) : N
    := gs.(num_raw).
  
  #[global] Instance monad_stateT {s m} `{Monad m} : Monad (stateT s m).
  Proof.
    apply Monad_stateT. typeclasses eauto.
  Defined.

  Definition new_void_id : GenALIVE2 instr_id
    := n <- gets get_void;;
       modify increment_void;;
       ret (IVoid (Z.of_N n)).
  
  Definition new_raw_id : GenALIVE2 raw_id
    := n <- gets get_raw;;
       modify increment_raw;;
       ret (Name ("v" ++ CeresString.string_of_N n)).

  Definition get_local_ctx : GenALIVE2 var_context
    := gets (fun gs => gs.(gen_local_ctx)).

  Definition set_local_ctx (ctx : var_context) : GenALIVE2 unit
    := modify (replace_local_ctx ctx);;
       ret tt.

  #[global] Instance STGST : Monad (stateT GenState G).
  Proof.
    apply Monad_stateT. typeclasses eauto.
  Defined.
  
  #[global] Instance MGEN : Monad GenALIVE2.
  Proof.
    apply Monad_eitherT. typeclasses eauto.
  Defined.

  Definition lift_GenALIVE2 {A} (g : G A) : GenALIVE2 A.
    unfold GenALIVE2.
    apply mkEitherT.
    apply mkStateT.
    refine (fun stack => _).
    refine (a <- g;; _).
    refine (ret (inr a, stack)).
  Defined.

  #[global] Instance MGENT: MonadT GenALIVE2 G.
  unfold GenALIVE2.
  constructor.
  exact @lift_GenALIVE2.
  Defined.
  
  Definition failGen {A : Type} (s : string) : GenALIVE2 A.
    apply mkEitherT.
    apply mkStateT.
    refine (fun stack => _ ).
    exact (ret (inl (s), stack)).
  Defined.

  Definition add_to_local_ctx (var : ident * typ): GenALIVE2 unit
    := ctx <- get_local_ctx;;
       set_local_ctx (var :: ctx).

  Definition append_to_local_ctx (vars : list (ident * typ)): GenALIVE2 unit
    := ctx <- get_local_ctx;;
       set_local_ctx (vars ++ ctx).

  Fixpoint remove_fst_id_var_context (id : ident) (l : var_context) : var_context
    := match l with
       | nil => nil 
       | hd::tl => match Ident.eq_dec id (fst hd) with
                 | left _ => tl
                 | right _ => hd:: remove_fst_id_var_context id tl
                 end
       end.
           
  Definition remove_fst_from_local_ctx (id : ident) : GenALIVE2 unit
    := ctx <- get_local_ctx;;
       set_local_ctx (remove_fst_id_var_context id ctx);;
       ret tt.

  Definition reset_local_ctx : GenALIVE2 unit
    := set_local_ctx [].

  Definition hide_local_ctx {A} (g : GenALIVE2 A): GenALIVE2 A
    := saved_local_ctx <- get_local_ctx;;
       reset_local_ctx;;
       a <- g;;
       set_local_ctx saved_local_ctx;;
       ret a.

  Definition backtrack_local_ctx {A} (g : GenALIVE2 A) : GenALIVE2 A
    := saved_local_ctx <- get_local_ctx;;
       a <- g;;
       set_local_ctx saved_local_ctx;;
       ret a.

  Definition freq_ALIVE2 {A} (gs : list (nat * GenALIVE2 A)) : GenALIVE2 A
    :=
     fst
         (fold_left
            (fun '(gacc, k) '(fk, a) =>
               let fkn := N.of_nat fk in
               let k' := (k + fkn)%N in
               let gen' :=
                 swap <- lift (fmap (fun x => N.leb x fkn) (choose (0%N, k')));;
                 if swap
                 then (* swap *)
                   a
                 else (* No swap *)
                   gacc
               in (gen', k'))
            gs (failGen ("Failgen at freq_ALIVE2"), 0%N)).

  Definition elems_ALIVE2 {A : Type} (l: list A) : GenALIVE2 A
    := fst
         (fold_left
            (fun '(gacc, k) a =>
               let gen' :=
                 swap <- lift (fmap (N.eqb 0) (choose (0%N, k)));;
                 match swap with
                 | true => ret a
                 | false => gacc
                 end
               in (gen', (k+1)%N))
            l (failGen "elems_LLVM", 0%N)).
  
  Definition vectorOf_ALIVE2 {A : Type} (k : nat) (g : GenALIVE2 A) : GenALIVE2 (list A).
    refine (fold_left _ _ _).
    refine (fun l g => _).
    refine (a <- g ;; _).
    refine (a' <- l ;; _).
    exact (ret (a :: a')).
    exact (repeat g k).
    exact (ret []).
  Defined.

  Definition run_GenALIVE2 {A : Type} (g : GenALIVE2 A) : G (string + A)
    :=
    let ran := runStateT (unEitherT g) init_GenState in
    '(errA, _) <- ran;;
    ret errA
  .
  
  Definition gen_int (sz : N) : GenALIVE2 Z :=
    let i_sz := Z.of_N sz in
    if i_sz <=? 8 then lift_GenALIVE2 (choose (0, 2 ^ i_sz - 1)) else ret 10000.
  
  Definition gen_float32 : GenALIVE2 float32 :=
    lift_GenALIVE2 fing32.
  
  Definition gen_int_exp (sz : N) : GenALIVE2 (exp typ) :=
    i_val <- gen_int sz;;
    (ret (EXP_Integer i_val)).

  Definition gen_float_exp : GenALIVE2 (exp typ) :=
    ret EXP_Float <*> gen_float32.

  (* size is the max depth of the data structure
     int, float, double -> 0
     ptr x -> size(x) + 1
     vector n t -> size(t) + 1
     struct -> max(size(l)) + 1
   *)
  Fixpoint depth_of_typ (t : typ) : nat :=
    match t with
    | TYPE_Array n sub_t
    | TYPE_Vector n sub_t => depth_of_typ (sub_t) + 1
    | TYPE_Pointer (Some sub_t) => depth_of_typ (sub_t) + 1
    | TYPE_Struct vars
    | TYPE_Packed_struct vars => fold_right (fun x acc => max (depth_of_typ x) acc) 0%nat vars
    | _ => 0
    end.  

Fixpoint normalized_typ_eq (a : typ) (b : typ) {struct a} : bool
    := match a with
       | TYPE_I sz =>
         match b with
         | TYPE_I sz' => if Pos.eq_dec sz sz' then true else false
         | _ => false
         end
       | TYPE_IPTR =>
         match b with
         | TYPE_IPTR => true
         | _ => false
         end
       | TYPE_Pointer t =>
         match b with
         | TYPE_Pointer t' =>
             match (t, t') with
             | (Some t, Some t') => normalized_typ_eq t t'
             | (None, None) => true
             | _ => false
             end
         | _ => false
         end
       | TYPE_Void =>
         match b with
         | TYPE_Void => true
         | _ => false
         end
       | TYPE_Half =>
         match b with
         | TYPE_Half => true
         | _ => false
         end
       | TYPE_Float =>
         match b with
         | TYPE_Float => true
         | _ => false
         end
       | TYPE_Double =>
         match b with
         | TYPE_Double => true
         | _ => false
         end
       | TYPE_X86_fp80 =>
         match b with
         | TYPE_X86_fp80 => true
         | _ => false
         end
       | TYPE_Fp128 =>
         match b with
         | TYPE_Fp128 => true
         | _ => false
         end
       | TYPE_Ppc_fp128 =>
         match b with
         | TYPE_Ppc_fp128 => true
         | _ => false
         end
       | TYPE_Metadata =>
         match b with
         | TYPE_Metadata => true
         | _ => false
         end
       | TYPE_X86_mmx =>
         match b with
         | TYPE_X86_mmx => true
         | _ => false
         end
       | TYPE_Array sz t =>
         match b with
         | TYPE_Array sz' t' =>
           if N.eq_dec sz sz'
           then normalized_typ_eq t t'
           else false
         | _ => false
         end
       | TYPE_Function ret args varargs=>
         match b with
         | TYPE_Function ret' args' varargs' =>
             (* Do this to fix the extraction *)
             let eq_vararg := match varargs, varargs' with
                              | true, true => true
                              | false, false => true
                              | _, _ => false
                              end in
                             
             Nat.eqb (Datatypes.length args) (Datatypes.length args') &&
               normalized_typ_eq ret ret' &&
               forallb id (zipWith (fun a b => normalized_typ_eq a b) args args')
             && eq_vararg(* Bool.eqb varargs varargs' *)
         | _ => false
         end
       | TYPE_Struct fields =>
         match b with
         | TYPE_Struct fields' =>
             Nat.eqb (Datatypes.length fields) (Datatypes.length fields') &&
             forallb id (zipWith (fun a b => normalized_typ_eq a b) fields fields')
         | _ => false
         end
       | TYPE_Packed_struct fields =>
         match b with
         | TYPE_Packed_struct fields' =>
             Nat.eqb (Datatypes.length fields) (Datatypes.length fields') &&
             forallb id (zipWith (fun a b => normalized_typ_eq a b) fields fields')
         | _ => false
         end
       | TYPE_Opaque =>
         match b with
         | TYPE_Opaque => false (* TODO: Unsure if this should compare equal *)
         | _ => false
         end
       | TYPE_Vector sz t =>
         match b with
         | TYPE_Vector sz' t' =>
           if N.eq_dec sz sz'
           then normalized_typ_eq t t'
           else false
         | _ => false
         end
       | TYPE_Identified id => false
       end.

  Definition filter_type (ty : typ) (ctx : list (ident * typ)) : list (ident * typ)
    := filter (fun '(i, t) => normalized_typ_eq (ty) (t)) ctx.

  Fixpoint gen_exp_size (sz : nat) (t : typ) {struct sz}: GenALIVE2 (exp typ) :=
    let fix gen_size_0 (ty : typ) : GenALIVE2 (exp typ) :=
          match ty with
          | TYPE_I sz =>
              ret (Npos sz) >>= gen_int_exp
          | TYPE_Float =>
              gen_float_exp
          | TYPE_Double =>
              f32 <- gen_float32;;
              ret (EXP_Double (Float.of_single f32))
          | TYPE_Array n t =>
              es <- vectorOf_ALIVE2 (N.to_nat n) (gen_exp_size 0 t);;
              ret (EXP_Array (TYPE_Array n t) (map (fun e => (t, e)) es))
          | TYPE_Vector n t =>
              es <- vectorOf_ALIVE2 (N.to_nat n) (gen_exp_size 0 t);;
              ret (EXP_Vector (TYPE_Vector n t) (map (fun e => (t, e)) es))
          | TYPE_Struct vars =>
              failGen "Struct generation unimplemented"
          | TYPE_Packed_struct vars =>
               failGen "Packed Struct generation unimplemented"
          | _ => failGen "Unimplemented"
          end in
    match sz with
    | 0%nat => (* Generate value-like expression *)
        exp1 <- gen_size_0 t;;
        (* exp2 <- gen_exp_ident t;; *)
        (* TODO: Can express this in more elegant way *)
        (* TODO: May have some problem at generating ident *)
        (* It is possible that exp2 is none, so need to match exp2*)
        freq_ALIVE2 [(1%nat, ret exp1)]
    | (S z)%nat => (* Generate instruction-like expression *)
        match t with
        | TYPE_I sz =>
            ret (OP_IBinop (LLVMAst.Add false false)) <*> ret t <*> gen_exp_size 0 t <*> ret (EXP_Integer 0)
        | TYPE_Float =>
            ret (OP_FBinop (LLVMAst.FAdd) []) <*> ret t <*> gen_exp_size 0 t <*> ret (EXP_Float Float32.zero)
        | TYPE_Double =>
            ret (OP_FBinop (LLVMAst.FAdd) []) <*> ret t <*> gen_exp_size 0 t <*> ret (EXP_Double Float.zero)
        | _ => failGen "Unimplemented"
        end
    end.

  Definition gen_exp_ident (t : typ): GenALIVE2 (exp typ) :=
    (* Remove from local ctx *)
    local_ctx <- get_local_ctx;;
    let ts := filter_type t local_ctx in
    let gen_idents : list (nat * GenALIVE2 (exp typ)) :=
      match ts with
      | [] => []
      | _ => [(16%nat, fmap (fun '(i, _) => EXP_Ident i) (elems_ALIVE2 ts))]
      end in
    if (is_nil gen_idents) then gen_exp_size 0 t else freq_ALIVE2 gen_idents
  .

  Fixpoint gen_exp (ty : typ) : GenALIVE2 (exp typ) :=
    freq_ALIVE2 [(16%nat, gen_exp_ident ty); (16%nat, gen_exp_size 0 ty)].
  
  Definition add_id_to_instr (t_instr : typ * instr typ) : GenALIVE2 (instr_id * instr typ)
    :=
    match t_instr with
    | (TYPE_Void, instr) =>
        vid <- new_void_id;;
        ret (vid, instr)
    | (t, instr) =>
        i <- new_raw_id;;
        add_to_local_ctx (ID_Local i, t);;
        ret (IId i, instr)
    end.

  (* TODO: handle opaque pointers?  *)
  Fixpoint gen_instantiate_instr (index : nat) (tgt : typ) {struct index}: GenALIVE2 (instr_id * instr typ) :=
    match tgt with
    | TYPE_I _ =>
        exp <- gen_exp_size 1 tgt;;
        (add_id_to_instr (tgt, INSTR_Op exp))
    | TYPE_Float =>
        exp <- gen_exp_size 1 tgt;;
        add_id_to_instr (tgt, INSTR_Op exp)
    | TYPE_Double =>
        exp <- gen_exp_size 1 tgt;;
        add_id_to_instr (tgt, INSTR_Op exp)
    | TYPE_Vector sz t' =>
        e_src <- gen_exp_size 0 tgt;;
        e_input <- gen_exp_size 0 t';;
        let e_index := EXP_Integer (Z.of_nat index) in
        let exp := OP_InsertElement (tgt, e_src) (t', e_input) (TYPE_I 8, e_index) in
        ins <- add_id_to_instr (tgt, INSTR_Op exp);;
        match e_src with
        | EXP_Ident id => remove_fst_from_local_ctx id;;
                         ret ins
        | _ => ret ins
        end
    | TYPE_Array sz t' =>
        (* Assumption is that src have already been created, either undef or not *)
        e_src <- gen_exp_ident tgt;;
        e_input <- gen_exp_size 0 t';;
        let exp := OP_InsertValue (tgt, e_src) (t', e_input) [Z.of_nat index] in
        ins <- add_id_to_instr (tgt, INSTR_Op exp);;
        match e_src with
        | EXP_Ident id => remove_fst_from_local_ctx id;;
                         ret ins
        | _ => ret ins
        end
    | TYPE_Struct fields =>
        (* Assumption is that src have already been created, either undef or not *)
        e_src <- gen_exp_ident tgt;;
        t' <-  match nth_error fields index with
              | Some t => ret t
              | _ => failGen "Out of Bounds"
              end;;
        e_input <- gen_exp_size 0 t';;
        let exp := OP_InsertValue (tgt, e_src) (t', e_input) [Z.of_nat index] in
        ins <- add_id_to_instr (tgt, INSTR_Op exp);;
        match e_src with
        | EXP_Ident id => remove_fst_from_local_ctx id;;
                         ret ins
        | _ => ret ins
        end
    | TYPE_Packed_struct fields =>
        e_src <- gen_exp_size 0 tgt;;
        t' <-  match nth_error fields index with
              | Some t => ret t
              | _ => failGen "Out of Bounds"
              end;;
        e_input <- gen_exp_size 0 t';;
        let exp := OP_InsertValue (tgt, e_src) (t', e_input) [Z.of_nat index] in
        ins <- add_id_to_instr (tgt, INSTR_Op exp);;
        match e_src with
        | EXP_Ident id => remove_fst_from_local_ctx id;;
                         ret ins
        | _ => ret ins
        end
    | TYPE_Pointer (Some t') =>
        e_src <- gen_exp_ident tgt;;
        e_input <- gen_exp_size 0 t';;
        let ins := INSTR_Store (t', e_input) (tgt, e_src) [] in
        add_id_to_instr (TYPE_Void, ins)
    | _ => failGen "Unimplemented"
    end.

  (* ins_<_> is type instr typ
     inst_<_> is type (instr_id * instr typ)
     <_>_instrs is type (list (instr_id * instr typ))
   *)

  Definition instr_id2raw_id (iid : instr_id) : GenALIVE2 raw_id
    :=
    match iid with
    | IId rid => ret rid
    | _ => failGen "No raw id"
    end.

  (*
    Given an array of types (assuming from struct, packedstruct, array, or vector),
    the auxiliary function will generate all the instructions needed to instantiate those functions,
    following with an insertelements / insertvalue functions.
   *)
  (* Fixpoint gen_instrs_arrays (depth index : nat) (t : typ) : GenALIVE2 (list (instr_id * instr typ * typ)) *)
  (*   := *)
  (*   subtyp_array <- *)
  (*     match t with *)
  (*     | TYPE_Vector sz sub_t *)
  (*     | TYPE_Array sz sub_t => ret (repeat sub_t (N.to_nat sz)) *)
  (*     | TYPE_Struct sub_ts *)
  (*     | TYPE_Packed_struct sub_ts => ret sub_ts *)
  (*     | _ => failGen "No array" *)
  (*     end;; *)
  (*   @foldM GenALIVE2 MGEN step []. *)

  (* TODO: handle opaque pointers?  *)
  Fixpoint gen_instrs (depth : nat) (t : typ) {struct depth} : GenALIVE2 (list (instr_id * instr typ))
    :=
    (* here is a potential infinite loop *)
    (* let fix gen_instr_iter (sz : nat) (l : list (instr_id * instr typ)) {struct sz}: GenALIVE2 (list (instr_id * instr typ)):= *)
    (*   match sz with *)
    (*   | O => ret l *)
    (*   | S z => *)
    (*       inst <- gen_instantiate_instr z t;; *)
    (*       gen_instr_iter sz ([inst] ++ l) *)
    (*   end in *)
    match t with
    | TYPE_I _ =>
        inst <- gen_instantiate_instr 0 t;;
        ret [inst]
    | TYPE_Float
    | TYPE_Double =>
        inst <- gen_instantiate_instr 0 t;;
        ret [inst]
    | TYPE_Vector sz t' =>
        (*
          1. Generate an instruction for this type
          2. rest <- gen_initializations args';;
          3. Generate some instructions for filling this type
         *)
        let sz_nat := N.to_nat sz in
        let ins_alloca := INSTR_Alloca t [] in
        '(inst_alloca_id, inst_alloca_instr) <- hide_local_ctx (add_id_to_instr (TYPE_Pointer (Some t), ins_alloca));;
        inst_alloca_raw_id <- instr_id2raw_id inst_alloca_id;;
        let ins_load := INSTR_Load t (TYPE_Pointer (Some t), EXP_Ident (ID_Local inst_alloca_raw_id)) [] in
        '(inst_load_id, inst_load_instr) <- add_id_to_instr (t, ins_load);;
        inst_load_raw_id <- instr_id2raw_id inst_load_id;;
        insts <- gen_instrs_arrays (depth - 1) (inst_load_raw_id) t true;;
        (* Need a foldr here -> insertsomething in, for each one, possibly generate higher value using maybe... *)
        ret ([(inst_alloca_id, inst_alloca_instr); (inst_load_id, inst_load_instr)] ++ insts)
        (* l_instrs <- gen_instrs (depth - 1) t';; *)
        (* upper_instrs <- gen_instr_iter (N.to_nat sz) [];; *)
        (* ret (upper_instrs ++ l_instrs) *)
    | TYPE_Array sz t' => 
        let sz_nat := N.to_nat sz in
        let ins_alloca := INSTR_Alloca t [] in
        '(inst_alloca_id, inst_alloca_instr) <- hide_local_ctx (add_id_to_instr (TYPE_Pointer (Some t), ins_alloca));;
        inst_alloca_raw_id <- instr_id2raw_id inst_alloca_id;;
        let ins_load := INSTR_Load t (TYPE_Pointer (Some t), EXP_Ident (ID_Local inst_alloca_raw_id)) [] in
        '(inst_load_id, inst_load_instr) <- add_id_to_instr (t, ins_load);;
        inst_load_raw_id <- instr_id2raw_id inst_load_id;;
        insts <- gen_instrs_arrays (depth - 1) (inst_load_raw_id) t false;;
        (* Need a foldr here -> insertsomething in, for each one, possibly generate higher value using maybe... *)
        ret ([(inst_alloca_id, inst_alloca_instr); (inst_load_id, inst_load_instr)] ++ insts)
        (* l_instrs <- gen_instrs (depth - 1) t';; *)
        (* upper_instrs <- gen_instr_iter (N.to_nat sz) [];; *)
        (* ret (upper_instrs ++ l_instrs) *)
    | TYPE_Struct fields =>
        let ins_alloca := INSTR_Alloca t [] in
        '(inst_alloca_id, inst_alloca_instr) <- hide_local_ctx (add_id_to_instr (TYPE_Pointer (Some t), ins_alloca));;
        inst_alloca_raw_id <- instr_id2raw_id inst_alloca_id;;
        let ins_load := INSTR_Load t (TYPE_Pointer (Some t), EXP_Ident (ID_Local inst_alloca_raw_id)) [] in
        '(inst_load_id, inst_load_instr) <- add_id_to_instr (t, ins_load);;
        inst_load_raw_id <- instr_id2raw_id inst_load_id;;
        insts <- gen_instrs_arrays (depth - 1) (inst_load_raw_id) t false;;
        (* Need a foldr here -> insertsomething in, for each one, possibly generate higher value using maybe... *)
        ret ([(inst_alloca_id, inst_alloca_instr); (inst_load_id, inst_load_instr)] ++ insts)
        (* l_instrs <- foldM (fun acc t' => gen_instrs (depth - 1) t' >>= (fun instrs => ret (acc ++ instrs))) [] fields;; *)
        (* upper_instrs <- gen_instr_iter (List.length fields) [];; *)
        (* ret (upper_instrs ++ l_instrs) *)
    | TYPE_Packed_struct fields =>
        let ins_alloca := INSTR_Alloca t [] in
        '(inst_alloca_id, inst_alloca_instr) <- hide_local_ctx (add_id_to_instr (TYPE_Pointer (Some t), ins_alloca));;
        inst_alloca_raw_id <- instr_id2raw_id inst_alloca_id;;
        let ins_load := INSTR_Load t (TYPE_Pointer (Some t), EXP_Ident (ID_Local inst_alloca_raw_id)) [] in
        '(inst_load_id, inst_load_instr) <- add_id_to_instr (t, ins_load);;
        inst_load_raw_id <- instr_id2raw_id inst_load_id;;
        insts <- gen_instrs_arrays (depth - 1) (inst_load_raw_id) t false;;
        (* Need a foldr here -> insertsomething in, for each one, possibly generate higher value using maybe... *)
        ret ([(inst_alloca_id, inst_alloca_instr); (inst_load_id, inst_load_instr)] ++ insts)
        (* l_instrs <- foldM (fun acc t' => gen_instrs (depth - 1) t' >>= (fun instrs => ret (acc ++ instrs))) [] fields;; *)
        (* upper_instrs <- gen_instr_iter (List.length fields) [];; *)
        (* ret (upper_instrs ++ l_instrs) *)
    | TYPE_Pointer (Some t') =>
    (* Generate alloca *)
        let ins_alloca := INSTR_Alloca t [] in
        inst_alloca <- add_id_to_instr (t, ins_alloca);;
    (* Generate instructions for subtypes *)
        upper_instrs <- gen_instrs (depth - 1) t';;
    (* Generate instantiation *)
        inst_store <- gen_instantiate_instr 0 t;;
        ret (inst_alloca :: upper_instrs ++ [inst_store])
    | _ => failGen "Unimplemented"
    end
  with
  (*
    Given an array of types (assuming from struct, packedstruct, array, or vector),
    the auxiliary function will generate all the instructions needed to instantiate those functions,
    following with an insertelements / insertvalue functions.
   *)
   gen_instrs_arrays (depth: nat) (rid: raw_id) (t : typ) (is_insertelement : bool) {struct depth} : GenALIVE2 (list (instr_id * instr typ))
   :=
     let step (acc : list (instr_id * instr typ) * raw_id) (it : nat * typ) : GenALIVE2 (list (instr_id * instr typ) * raw_id) :=
       (* Recurring by generating more instructions on gen_instrs.
          There are two ways to generate instructions.
          1. Not generate -> simply get an expression. <- Only do this when there exists some expression that I can use.
          1.1 If the output is failGen, don't roll a dice. Else, roll a dice.
          2. Generate -> create newer instructions and put them into lists.
          Then, instantiate the element into the list *)
       let (index, t') := it in
       let (accl, accid) := acc in
     (*   exp <- catch (gen_exp t) (fun err => ret (EXP_Undef));; *)
     (*   want_instr <- *)
     (*     match exp with *)
     (*     | EXP_Undef (* Nothing was generated *) *)
     (*       => ret false *)
     (*     | _ => freq_ALIVE2 [(16%nat, true); (16%nat, false)] *)
     (*     end in *)
     (* if want_instr *)
     (* then  *)
     (* else *)
       instrs <- gen_instrs depth t';;
       let src_id := ID_Local accid in
       let e_src := EXP_Ident src_id in
       e_input <- gen_exp_ident t';;
       let e_index := EXP_Integer (Z.of_nat index) in
       let set_instr :=
         if is_insertelement
         then
           INSTR_Op (OP_InsertElement (t, e_src) (t', e_input) (TYPE_I 32, e_index))
         else
           INSTR_Op (OP_InsertValue (t, e_src) (t', e_input) (map (Z.of_nat) [0%nat; index]))
           in
       (* Need to remove the old one *)
       remove_fst_from_local_ctx src_id;;
       (* Give a new instruction id *)
       '(inst_set_id, inst_set_instr) <- add_id_to_instr (t, set_instr);;
       inst_set_raw_id <- instr_id2raw_id inst_set_id;;
       ret (accl ++ instrs ++ [(inst_set_id, inst_set_instr)], inst_set_raw_id)
     in
       subtyp_array <-
         match t with
         | TYPE_Vector sz sub_t
         | TYPE_Array sz sub_t => ret (repeat sub_t (N.to_nat sz))
         | TYPE_Struct sub_ts
         | TYPE_Packed_struct sub_ts => ret sub_ts
         | _ => failGen "No array"
         end;;
       let fix get_index_array (index : nat) (typ_array : list typ) : list (nat * typ) :=
         match typ_array with
         | nil => []
         | x::xs => (index , x) :: get_index_array (index + 1)%nat xs
         end in
       '(codes, _) <- @foldM GenALIVE2 MGEN (nat * typ) (list (instr_id * instr typ) * raw_id) step ([], rid) (get_index_array 0%nat subtyp_array);;
       ret codes.

  (* Definition gen_initializations_aux (acc : GenALIVE2 (code typ)) (t : typ): GenALIVE2 (code typ) *)
  (*   := *)
  (*   let depth_t := depth_of_typ t in *)
  (*       rest <- acc;; *)
  (*       instr <- hide_local_ctx (gen_instrs depth_t t);; *)
  (*       ret (rest ++ instr). *)

  Fixpoint gen_initializations (args : list typ) : GenALIVE2 (code typ)
    :=
    (* foldM gen_initializations_aux (ret []) args. *)
    match args with
    | nil => ret []
    | t::args' =>
        let depth_t := depth_of_typ t in
        rest <- gen_initializations args';;
        instr <- gen_instrs depth_t t;;
        (* Not sure if I need this. *)
        (*    Allocate store *)
        (* alloca_store <- fix_alloca isntr;; *)
        ret (instr ++ rest)
    end.

  (* How to generate a list of arguments
     Can be done by iterate on the list of functions.
     For each one of them, generate and backtrack required commands
   *)

  (* This function assumes the existence of such function in the LLVM context, i.e. the AST *)
  Definition gen_call_fn (args: list typ) (ret_t : typ) (fn : string) : GenALIVE2 (instr_id * instr typ) :=
    args_texp <- map_monad
                  (fun (arg_typ : typ) =>
                     arg_exp <- gen_exp_ident arg_typ;;
                     ret ((arg_typ,arg_exp), []))
                  args;;
    let fun_exp : (exp typ) := EXP_Ident (ID_Global (Name fn)) in
    let fun_typ : typ := TYPE_Function ret_t args false in
    let fun_instr : (instr typ) := INSTR_Call (fun_typ, fun_exp) args_texp [] in
    fun_id_instr <- add_id_to_instr (fun_typ, fun_instr);;
    ret fun_id_instr
    .
  
(*   Definition gen_code_w_pred (args: list typ) (ret_t : typ) (fn: string) : GenALIVE2 (code typ) *)
(*     := *)
  (* . *)

  Definition gen_fn_params (args: list typ) : GenALIVE2 (list (typ * exp typ * list param_attr))
    :=
        args_texp <- map_monad
                  (fun (arg_typ : typ) =>
                     arg_exp <- gen_exp_size 0 arg_typ;;
                     ret ((arg_typ,arg_exp), []))
                  args;;
  ret args_texp.
    
  
  Definition assemble_pred_fn_blocks (init_code: code typ) (args_t : list typ) (ret_t : typ) (args_texp : list (typ * exp typ * list param_attr)) (fn_str: string): GenALIVE2 (block typ * list (block typ))
    :=
    let pred_bid : block_id := Name "predicate" in
    let fn_bid : block_id := Name "fn" in
    (* Generate function call itself *)
    let fn_exp : (exp typ) := EXP_Ident (ID_Global (Name fn_str)) in
    let fn_typ : typ := TYPE_Function ret_t args_t false in
    let fn_instr : (instr typ) := INSTR_Call (fn_typ, fn_exp) args_texp [] in
    '(fn_instr_id, fn_instr) <- add_id_to_instr (fn_typ, fn_instr);;
 
    let pred_b :=
      {|
        blk_id := pred_bid
      ; blk_phis := []
      ; blk_code := init_code
      ; blk_term := TERM_Br_1 fn_bid
      ; blk_comments := None
      |} in
    let fn_term := match fn_instr_id with
                   | IId rid => TERM_Ret (ret_t, EXP_Ident (ID_Local rid))
                   | IVoid _ => TERM_Ret_void
                   end in
    let fn_b :=
      {|
        blk_id := fn_bid
      ; blk_phis := []
      ; blk_code := [(fn_instr_id, fn_instr)]
      ; blk_term := fn_term
      ; blk_comments := None
      |} in
    ret (pred_b, [fn_b]).

  (* Definition var_context := list (ident * typ). *)
  Definition runnable_blocks : Set := (block typ * list (block typ)).
  
  Definition gen_pred_fn_blocks (args_t: list typ) (ret_t : typ) (src_fn_str tgt_fn_str : string): GenALIVE2 (runnable_blocks * runnable_blocks)
    :=
    init_code <- gen_initializations args_t;;
    (* '(fn_instr_id, fn_instr) <- gen_call_fn args ret_t fn;; *)
    local_ctx <- get_local_ctx;;
    let show_string := DString_to_string (ShowAST.dshow local_ctx) in
    (* Generate params that will be used by both function calls *)
    args_texp <- map_monad
                  (fun (arg_typ : typ) =>
                     arg_exp <- gen_exp_ident arg_typ;;
                     ret ((arg_typ, arg_exp), []))
                  args_t;;
    src_fn_blocks <- assemble_pred_fn_blocks init_code args_t ret_t args_texp src_fn_str;;
    tgt_fn_blocks <- assemble_pred_fn_blocks init_code args_t ret_t args_texp tgt_fn_str;;
    match ret_t with
    | TYPE_Opaque => failGen show_string
    | _ =>
        ret (src_fn_blocks, tgt_fn_blocks)
    end
  .

  (* Assemble the wrapper function *)
  Definition assemble_runner_def (ret_t : typ) (fn_str : string) (pred_fn_blocks : runnable_blocks) : definition typ runnable_blocks
    :=
    let name := Name ("runner" ++ fn_str) in
    let runner_typ :=
      TYPE_Function ret_t [] false in
    (* let param_attr_slots := map (fun _ => []) args_t in *)
    let param_attr_slots := [] in
    let prototype :=
      mk_declaration name runner_typ
        ([], param_attr_slots)
        []
        []
    in
    mk_definition (runnable_blocks) prototype [] pred_fn_blocks.
  
  Definition gen_runner_tle (args_t : list typ) (ret_t : typ) (src_fn_str tgt_fn_str : string) : GenALIVE2 (toplevel_entity typ runnable_blocks * toplevel_entity typ runnable_blocks)
    :=
    reset_local_ctx;;
    '(src_fn_blocks, tgt_fn_blocks) <- gen_pred_fn_blocks args_t ret_t src_fn_str tgt_fn_str;;
    let src_def := assemble_runner_def ret_t src_fn_str src_fn_blocks in
    let tgt_def := assemble_runner_def ret_t tgt_fn_str tgt_fn_blocks in
    ret (TLE_Definition src_def, TLE_Definition tgt_def).

  

  (* TODO: Supposed to take a parsed program (TLE maybe?) and output a fixed list of TLEs
   Need to find what the type of the input is
   TODO: Maybe don't need this. Cuz it requires me to record the generated program. Should instead manipulate it at main *)
  Definition gen_tester : GenALIVE2 (list (toplevel_entity typ (block typ * list (block typ))))
    :=
    failGen "Unimplemented".
  
  Fixpoint gen_uvalue (t : typ) : GenALIVE2 uvalue :=
    match t with
    | @TYPE_I sz =>
        ret (@UVALUE_I sz) <*> (ret repr <*> lift_GenALIVE2 (choose (0, Z.min (2^(Zpos sz) - 1) 10000)))
    | TYPE_Float =>
        ret UVALUE_Float <*> lift_GenALIVE2 fing32
    | TYPE_Double =>
        failGen "Generating UValue Double - Not supported"
    | TYPE_Void => ret UVALUE_None
    | TYPE_Vector sz subtyp =>
        ret (UVALUE_Vector (DTYPE_Vector sz (TypToDtyp.typ_to_dtyp [] subtyp))) <*> (vectorOf_ALIVE2 (N.to_nat sz) (gen_uvalue subtyp))
    | TYPE_Array sz subtyp =>
        ret (UVALUE_Array (DTYPE_Array sz (TypToDtyp.typ_to_dtyp [] subtyp))) <*> (vectorOf_ALIVE2 (N.to_nat sz) (gen_uvalue subtyp))
    | _ => failGen "Invalid"
    end.
                                            
  
End GEN_ALIVE2.


(* Require Import QuickChick.QuickChick. *)

(* Module G := GEN_ALIVE2 MemoryModelImplementation.FinAddr MemoryModelImplementation.IP64Bit MemoryModelImplementation.FinSizeof  . (* LLVMEvents64. *) *)
(* Import G. *)
 
(* (* Extract Inlined Constant fst => "fst". *) *)
(* (* Extract Inlined Constant app => "append". *) *)
(* (* Extract Inlined Constant rev => "rev". *) *)
(* (* Extract Inlined Constant map => "map". *) *)
(* (* Extract Inlined Constant combine => "combine". *) *)
(* (* (* Extract Inlined Constant eqn => "( == )". *) *) *)

(* (* Recursive Extraction nat_gen_example. *) *)

