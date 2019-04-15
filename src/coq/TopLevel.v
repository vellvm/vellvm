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

Definition allocate_globals (gs:list (global dtyp)) : LLVM _CFG D.genv :=
  monad_fold_right
    (fun (m:D.genv) (g:(global dtyp)) =>
       vis (Alloca (g_typ _ g)) (fun v => ret (D.ENV.add (g_ident _ g) v m))) gs (@D.ENV.empty _).


(* Who is in charge of allocating the addresses for external functions declared in this mcfg? *)
Definition register_declaration (g:D.genv) (d:declaration dtyp) : LLVM _CFG D.genv :=
  (* SAZ TODO:  Don't allocate pointers for LLVM intrinsics declarations *)
    vis (Alloca DTYPE_Pointer) (fun v => ret (D.ENV.add (dc_name _ d) v g)).


Definition initialize_globals (gs:list (global dtyp)) (g:D.genv) : LLVM _CFG unit :=
  monad_fold_right
    (fun (_:unit) (glb:global dtyp) =>
       let dt := (g_typ _ glb) in
       a <- lift_err ret (D.lookup_env g (g_ident _ glb)) ;;
       dv <-
           match (g_exp _ glb) with
           | None => ret DVALUE_Undef
           | Some e => D.denote_exp g (Some dt) e
           end ;;
       vis (Store a dv) ret)
    gs tt.
  
Definition build_global_environment (CFG : CFG.mcfg dtyp) : LLVM _CFG D.genv :=
  g <- allocate_globals (m_globals _ _ CFG) ;;
  g1 <- monad_fold_right register_declaration
       ((m_declarations _ _ CFG) ++ (List.map (df_prototype _ _) (m_definitions _ _ CFG))) g;;
  initialize_globals (m_globals _ _ CFG) g1 ;;
  ret g1.

(* Local environment implementation *)
Definition local_env := FMapAList.alist raw_id dvalue.


Definition function_env := FMapAList.alist dvalue D.function_denotation.

(* let d := (df_prototype df) in *)
(* -  let fid := (dc_name d) in *)
(* -  liftM (fun fv => (fv, (df_args df, D.denote_cfg CFG g (df_instrs df)))) (D.lookup_env g fid). *)

Definition address_one_function (g:D.genv) (df : definition dtyp (CFG.cfg dtyp)) : err (dvalue * D.function_denotation) :=
  let fid := (dc_name _ (df_prototype _ _ df)) in
   liftM (fun fv => (fv, D.denote_function g df)) (D.lookup_env g fid).
   

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
           'defns <- lift_err ret (map_monad (address_one_function glbls) (m_definitions _ _ mcfg)) ;;
           'addr <- lift_err ret (D.lookup_env glbls (Name "main")) ;;
           D.denote_mcfg defns DTYPE_Void addr main_args
       in

       let after_intrinsics_trace : LLVM _CFG dvalue := INT.interpret_intrinsics core_trace in
       
       let mem_trace : LLVM _ ((local_env * stack) * dvalue) :=
           run_local_stack
             (@handle_local raw_id dvalue _ _ show_raw_id _ _)
             after_intrinsics_trace ([], [])
       in

       let interpreted_Trace := M.run_memory mem_trace M.empty in

       ret interpreted_Trace.
