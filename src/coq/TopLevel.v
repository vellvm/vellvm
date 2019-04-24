(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

From Coq Require Import
     List String.

From ITree Require Import
     ITree
     Events.State.

From ExtLib Require Import 
     Structures.Monads
     Data.Map.FMapAList.

From Vellvm Require Import
     AstLib
     TransformTypes
     DynamicTypes
     LLVMEvents
     Denotation
     Local
     Stack
     Memory
     Intrinsics
     LLVMAst
     Util
     Error.


Import MonadNotation.
Import ListNotations.
Import Monads.

Module IO := LLVMEvents.Make(Memory.A).
Module M := Memory.Make(IO).
Module D := Denotation(Memory.A)(IO).
Module INT := Intrinsics.Make(Memory.A)(IO).

Import IO.
Export IO.DV.

Open Scope string_scope.

(* SAZ: Add this to the itrees library? *)
Definition map_bind {E} {A} (f : A -> itree E unit) (l:list A) : itree E unit :=
  List.fold_right (fun (x:A) t => (f x) ;; t) (ret tt) l.

Definition allocate_global (g:global dtyp) : LLVM _CFG unit :=
  (vis (Alloca (g_typ _ g)) (fun v => trigger (GlobalWrite (g_ident _ g) v))).

Definition allocate_globals (gs:list (global dtyp)) : LLVM _CFG unit :=
  map_bind allocate_global gs.

(* Who is in charge of allocating the addresses for external functions declared in this mcfg? *)
Definition allocate_declaration (d:declaration dtyp) : LLVM _CFG unit :=
  (* SAZ TODO:  Don't allocate pointers for LLVM intrinsics declarations *)
    vis (Alloca DTYPE_Pointer) (fun v => trigger (GlobalWrite (dc_name _ d) v)).

Definition allocate_declarations (ds:list (declaration dtyp)) : LLVM _CFG unit :=
  map_bind allocate_declaration ds.

Definition initialize_global (g:global dtyp) : LLVM _CFG unit :=
  let dt := (g_typ _ g) in
  a <- trigger (GlobalRead (g_ident _ g));;
  dv <- match (g_exp _ g) with
       | None => ret DVALUE_Undef
       | Some e => D.denote_exp (Some dt) e
       end ;;
  trigger (Store a dv).

Definition initialize_globals (gs:list (global dtyp)): LLVM _CFG unit :=
  map_bind initialize_global gs.
  
Definition build_global_environment (CFG : CFG.mcfg dtyp) : LLVM _CFG unit :=
  allocate_globals (m_globals _ _ CFG) ;;
  allocate_declarations ((m_declarations _ _ CFG) ++ (List.map (df_prototype _ _) (m_definitions _ _ CFG)));;
  initialize_globals (m_globals _ _ CFG).


(* Local environment implementation *)
Definition local_env := FMapAList.alist raw_id dvalue.
Definition global_env := FMapAList.alist raw_id dvalue.
Definition function_env := FMapAList.alist dvalue D.function_denotation.

Definition address_one_function (df : definition dtyp (CFG.cfg dtyp)) : LLVM _CFG (dvalue * D.function_denotation) :=
  let fid := (dc_name _ (df_prototype _ _ df)) in
  fv <- trigger (GlobalRead fid) ;;
  ret (fv, D.denote_function df).
   

(* (for now) assume that [main (i64 argc, i8** argv)] 
    pass in 0 and null as the arguments to main
   Note: this isn't compliant with standard C semantics
*)
Definition main_args := [DV.DVALUE_I64 (DynamicValues.Int64.zero);
                         DV.DVALUE_Addr (Memory.A.null)
                        ].

Definition eval_typ (CFG:CFG.mcfg typ) (t:typ) : dtyp :=
      TypeUtil.normalize_type_dtyp (m_type_defs _ _ CFG) t.


Definition normalize_types (CFG:(CFG.mcfg typ)) : (CFG.mcfg dtyp) :=
  TransformTypes.fmap_mcfg _ _ (eval_typ CFG) CFG.


Definition run_with_memory (prog: list (toplevel_entity typ (list (block typ)))) :
  option (LLVM _MCFG2 (M.memory * ((local_env * stack) * dvalue))) :=
    let scfg := Vellvm.AstLib.modul_of_toplevel_entities _ prog in
    ucfg <- CFG.mcfg_of_modul _ scfg ;;
    let mcfg := normalize_types ucfg in 
       let core_trace : LLVM _CFG dvalue :=
           'glbls <- build_global_environment mcfg ;;
           'defns <- map_monad address_one_function (m_definitions _ _ mcfg) ;;
           'addr <- trigger (GlobalRead (Name "main")) ;;
           D.denote_mcfg defns DTYPE_Void addr main_args
       in

       let after_intrinsics_trace : LLVM _CFG dvalue := INT.interpret_intrinsics core_trace in
       
       let glbl_trace : LLVM _ ((local_env * stack) * dvalue) :=
           run_local_stack
             (@handle_local raw_id dvalue _ _ show_raw_id _ _)
             after_intrinsics_trace ([], [])
       in

       let mem_trace : LLVM _ ((local_env * stack) * dvalue) :=
           
       
       let interpreted_Trace := M.run_memory mem_trace M.empty in

       ret interpreted_Trace.
