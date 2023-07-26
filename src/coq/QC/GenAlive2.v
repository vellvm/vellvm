From Vellvm Require Import
  Utilities
  AstLib
  Semantics.Memory.Sizeof
  LLVMEvents
  LLVMAst
  QC.Utils
  QC.Generators
  Handlers.
(* Maybe also import InterpretationStack *)

From ExtLib.Structures Require Export
  Functor Applicative Monad Monoid.

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

Require Import QuickChick.GenLow.
Require Import QuickChick.GenHigh.
Import GenHigh.
Import GenLow.
(* Import QcDefaultNotation. *)
Open Scope qc_scope.
Open Scope Z_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

Unset Guard Checking.

Module GEN_ALIVE2 (ADDR : MemoryAddress.ADDRESS) (IP:MemoryAddress.INTPTR) (SIZEOF : Sizeof).
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
           
  Definition remove_fst_from_local_ctx (var : ident * typ) : GenALIVE2 unit
    := ctx <- get_local_ctx;;
       set_local_ctx (remove_fst_id_var_context (fst var) ctx);;
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
    | TYPE_Array n t
    | TYPE_Vector n t => depth_of_typ (t) + 1
    | TYPE_Pointer t => depth_of_typ (t) + 1
    | TYPE_Struct vars
    | TYPE_Packed_struct vars => fold_right (fun x acc => max (depth_of_typ x) acc) 0%nat vars
    | _ => 0
    end.  

  (* (* *)
  (*   exp that directly link to types should be generated when a flag is up *)
  (*   exp that are not related to types should be generated when a flag is down *)
  (*  *) *)
  (* Fixpoint gen_exp_size (depth: nat) (t : typ) {struct depth}: GenALIVE2 (exp typ) := *)
  (*   local_ctx <- get_local_ctx;; *)
  (*   match t with *)
  (*   | TYPE_I sz => *)
  (*       match depth with *)
  (*       | O => *)
  (*           ret sz >>= gen_int_exp *)
  (*       | S _ => *)
  (*           ret (OP_IBinop (LLVMAst.Add false false)) <*> ret t <*> gen_exp_size O t <*> ret (EXP_Integer 0) *)
  (*       end *)
  (*   | TYPE_Float => *)
  (*       match depth with *)
  (*       | O => *)
  (*           gen_float_exp *)
  (*       | S _ => *)
  (*           ret (OP_FBinop (LLVMAst.FAdd) []) <*> ret t <*> gen_exp_size O t <*> ret (EXP_Float Float32.zero) *)
  (*       end *)
  (*   | TYPE_Double => *)
  (*       match depth with *)
  (*       | O => *)
  (*           f32 <- gen_float32;;               *)
  (*           ret (EXP_Double (Float.of_single f32)) *)
  (*       | S _ => *)
  (*           ret (OP_FBinop (LLVMAst.FAdd) []) <*> ret t <*> gen_exp_size O t <*> ret (EXP_Double Float.zero) *)
  (*       end *)
  (*   | TYPE_Array n t => *)
  (*       match depth with *)
  (*       | O => *)
  (*           es <- vectorOf_ALIVE2 (N.to_nat n) (gen_exp_size O t);; *)
  (*           ret (EXP_Array (map (fun e => (t, e)) es)) *)
  (*       | S z => *)
  (*           (* First loop through all and create instructions that add into backtrack_instrs *) *)
  (*           (* Pick up last instrs and return *) *)
  (*           failGen "Unimplemented" *)
  (*       end *)
  (*   | TYPE_Vector n t => *)
  (*       match depth with *)
  (*       | O => *)
  (*           es <- vectorOf_ALIVE2 (N.to_nat n) (gen_exp_size O t);; *)
  (*           ret (EXP_Vector (map (fun e => (t, e)) es)) *)
  (*       | S z => *)
  (*           (* First loop through all and create instructions that add into backtrack_instrs *) *)
  (*           (* Pick up last instrs and return *) *)
  (*           failGen "Unimplemented" *)
  (*       end *)
  (*   | TYPE_Struct vars *)
  (*   | TYPE_Packed_struct vars => failGen "Unimplemented" *)
  (*   | _ => failGen "Unimplemented" *)
  (*   end *)
  (* with *)
  (* gen_instr (depth : nat) (t : typ) {struct depth}: GenALIVE2 (instr typ) *)
  (* := *)
  (*   let fix propogate (t : list typ) : GenALIVE2 (list (instr typ)) := *)
  (*     failGen "Unimplemented" *)
  (*   in  *)
  (*   match t with *)
  (*   | TYPE_Array n t => *)
  (*   (* Iterate the array from the start. *)
  (*      For each iteration, do: *)
  (*        generate an insertelement instruction *)
  (*        Propogate the new vector id to the next *) *)
  (*       failGen "Unimplemented" *)
  (*   | _ => failGen "Unimplemented" *)
  (*   end *)
  (* . *)


  
  Fixpoint gen_exp_size (sz : nat) (t : typ) {struct sz}: GenALIVE2 (exp typ) :=
    local_ctx <- get_local_ctx;;
    let fix gen_size_0 (ty : typ) : GenALIVE2 (exp typ) :=
          match ty with
          | TYPE_I sz =>
              ret sz >>= gen_int_exp
          | TYPE_Float =>
              gen_float_exp
          | TYPE_Double =>
              f32 <- gen_float32;;              
              ret (EXP_Double (Float.of_single f32))
          | TYPE_Array n t
          | TYPE_Vector n t =>
              es <- vectorOf_ALIVE2 (N.to_nat n) (gen_exp_size 0 t);;
              ret (EXP_Array (map (fun e => (t, e)) es))    
          | TYPE_Struct vars =>
              failGen "Unimplemented"
          | TYPE_Packed_struct vars =>
              failGen "Unimplemented"
          | _ => failGen "Unimplemented"
          end in
    match sz with
    | 0%nat =>
        gen_size_0 t
    | (S z)%nat =>
        match t with
        | TYPE_I sz =>
            ret (OP_IBinop (LLVMAst.Add false false)) <*> ret t <*> gen_exp_size 0 t <*> ret (EXP_Integer 0)
        | TYPE_Float =>
            ret (OP_FBinop (LLVMAst.FAdd) []) <*> ret t <*> gen_exp_size 0 t <*> ret (EXP_Float Float32.zero)
        | TYPE_Double =>
            ret (OP_FBinop (LLVMAst.FAdd) []) <*> ret t <*> gen_exp_size 0 t <*> ret (EXP_Double Float.zero)
        | _ => failGen "Unimplemented"
        end
    end
  with gen_exp_ident (t : typ): GenALIVE2 (exp typ) :=
         (* Remove from local ctx *)
        failGen "Unimplemented"
  (* Need to think about this. *)
  .

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

  Fixpoint gen_instr (index : nat) (tgt : typ) {struct index}: GenALIVE2 (instr_id * instr typ) :=
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
        add_id_to_instr (tgt, INSTR_Op exp)
    | TYPE_Array sz t' =>
        (* Assumption is that src have already been created, either undef or not *)
        e_src <- gen_exp_ident tgt;;
        e_input <- gen_exp_size 0 t';;
        let exp := OP_InsertValue (tgt, e_src) (t', e_input) [Z.of_nat index] in
        add_id_to_instr (tgt, INSTR_Op exp)
    | TYPE_Struct fields =>
        (* Assumption is that src have already been created, either undef or not *)
        e_src <- gen_exp_ident tgt;;
        t' <-  match nth_error fields index with
            | Some t => ret t
              | _ => failGen "Out of Bounds"
              end;;
        e_input <- gen_exp_size 0 t';;
        let exp := OP_InsertValue (tgt, e_src) (t', e_input) [Z.of_nat index] in
        add_id_to_instr (tgt, INSTR_Op exp)
    | TYPE_Packed_struct fields =>
        e_src <- gen_exp_size 0 tgt;;
        t' <-  match nth_error fields index with
            | Some t => ret t
              | _ => failGen "Out of Bounds"
              end;;
        e_input <- gen_exp_size 0 t';;
        let exp := OP_InsertValue (tgt, e_src) (t', e_input) [Z.of_nat index] in
        add_id_to_instr (tgt, INSTR_Op exp)
    | TYPE_Pointer t => failGen "Unimplemented"
    | _ => failGen "Unimplemented"
    end.
Search length.
  Fixpoint gen_instrs (depth : nat) (t : typ) {struct depth} : GenALIVE2 (list (instr_id * instr typ))
    :=
    let fix gen_instr_iter (sz : nat) (l : list (instr_id * instr typ)) {struct sz}: GenALIVE2 (list (instr_id * instr typ)):=
      match sz with
      | O => ret l
      | S z =>
          inst <- gen_instr z t;;
          gen_instr_iter sz l
      end in
    match t with
    | TYPE_I _ =>
        inst <- gen_instr 0 t;;
        ret [inst]
    | TYPE_Float
    | TYPE_Double =>
        inst <- gen_instr 0 t;;
        ret [inst]
    | TYPE_Vector sz t' =>
        gen_instr_iter (N.to_nat sz) []
    | TYPE_Array sz t' =>
        (* Put an undef vector in there *)
        gen_instr_iter (N.to_nat sz) []
    | TYPE_Struct fields =>
        gen_instr_iter (List.length fields) []
    | TYPE_Packed_struct fields =>
        gen_instr_iter (List.length fields) []
    | _ => failGen "Unimplemented"
       end.


  Definition gen_instr_id (t : typ): GenALIVE2 (instr_id * instr typ)
    := t_instr <- gen_instr t;; add_id_to_instr t_instr.

  Fixpoint gen_initializations (args : list typ) : GenALIVE2 (code typ)
    :=
    match args with
    | nil => ret []
    | t::args' =>
        instr <- gen_instr_id t;;
        (* Not sure if I need this.
           Allocate store *)
        (* alloca_store <- fix_alloca isntr;; *)
        rest <- gen_initializations args';;
        ret (instr :: rest)
    end.
  
  Fixpoint gen_uvalue (t : typ) : GenALIVE2 uvalue :=
    match t with
    | TYPE_I i =>
        match i with
        | 1%N =>
            ret UVALUE_I1 <*> (ret repr <*> lift_GenALIVE2 (choose (0, 1)))
        | 8%N =>
            ret UVALUE_I8 <*> (ret repr <*> lift_GenALIVE2 (choose (0, 2^8 - 1)))
        | 32%N =>
            ret UVALUE_I32 <*> (ret repr <*> lift_GenALIVE2 (choose (0, 10000))) (* Modify to smaller number. Should be 2^32 - 1 *)
        | 64%N =>
            ret UVALUE_I64 <*> (ret repr <*> lift_GenALIVE2 (choose (0, 10000))) (* Modify to smaller number. Should be 2^64 - 1 *)
        | _ =>
            failGen "Invalid size"
        end
    | TYPE_Float =>
        ret UVALUE_Float <*> lift_GenALIVE2 fing32
    | TYPE_Double =>
        failGen "Generating UValue Double - Not supported"
    | TYPE_Void => ret UVALUE_None
    | TYPE_Vector sz subtyp =>
        ret UVALUE_Vector <*> (vectorOf_ALIVE2 (N.to_nat sz) (gen_uvalue subtyp))
    | TYPE_Array sz subtyp =>
        ret UVALUE_Array <*> (vectorOf_ALIVE2 (N.to_nat sz) (gen_uvalue subtyp))
    | _ => failGen "Invalid"
    end.
                                            


  (* How to generate a list of arguments
     Can be done by iterate on the list of functions.
     For each one of them, generate and backtrack required commands
   *)
  
  Definition gen_pred_function (args: list typ) (ret_t : typ) (fn1 fn2: string) : GenALIVE2 (toplevel_entity typ (block typ * list (block typ)))
    :=
    failGen "Invalid".
  
End GEN_ALIVE2.

(* Module G := GEN_ALIVE2 MemoryModelImplementation.FinAddr MemoryModelImplementation.IP64Bit MemoryModelImplementation.FinSizeof  . (* LLVMEvents64. *) *)
 
(* (* Extract Inlined Constant fst => "fst". *) *)
(* (* Extract Inlined Constant app => "append". *) *)
(* (* Extract Inlined Constant rev => "rev". *) *)
(* (* Extract Inlined Constant map => "map". *) *)
(* (* Extract Inlined Constant combine => "combine". *) *)
(* (* (* Extract Inlined Constant eqn => "( == )". *) *) *)

(* (* Recursive Extraction nat_gen_example. *) *)
