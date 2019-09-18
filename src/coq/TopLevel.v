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
     Ensembles List String.

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
     Handlers.Global
     Handlers.Local
     Handlers.Stack
     Handlers.Memory
     Handlers.Intrinsics
     LLVMAst
     Util
     Error
     Handlers.Pick
     PropT.


Import MonadNotation.
Import ListNotations.
Import Monads.

Module IO := LLVMEvents.Make(Memory.A).
Module M := Memory.Make(IO).
Module D := Denotation(Memory.A)(IO).
Module INT := Intrinsics.Make(Memory.A)(IO).
Module P := Pick.Make(Memory.A)(IO).
Import IO.
Export IO.DV.

Open Scope string_scope.

Definition allocate_global (g:global dtyp) : LLVM _CFG unit :=
  (vis (Alloca (g_typ _ g)) (fun v => trigger (GlobalWrite (g_ident _ g) v))).

Definition allocate_globals (gs:list (global dtyp)) : LLVM _CFG unit :=
  map_monad_ allocate_global gs.

(* Who is in charge of allocating the addresses for external functions declared in this mcfg? *)
Definition allocate_declaration (d:declaration dtyp) : LLVM _CFG unit :=
  (* SAZ TODO:  Don't allocate pointers for LLVM intrinsics declarations *)
    vis (Alloca DTYPE_Pointer) (fun v => trigger (GlobalWrite (dc_name _ d) v)).

Definition allocate_declarations (ds:list (declaration dtyp)) : LLVM _CFG unit :=
  map_monad_ allocate_declaration ds.

Definition initialize_global (g:global dtyp) : LLVM exp_E unit :=
  let dt := (g_typ _ g) in
  a <- trigger (GlobalRead (g_ident _ g));;
  uv <- match (g_exp _ g) with
       | None => ret (UVALUE_Undef dt)
       | Some e => D.denote_exp (Some dt) e
       end ;;
  (* CB TODO: Do we need pick here? *)
  dv <- trigger (pick uv True) ;;
  (* da <- trigger (pick a True) ;; *)
  trigger (Store a dv).

Definition initialize_globals (gs:list (global dtyp)): LLVM exp_E unit :=
  map_monad_ initialize_global gs.

Definition build_global_environment (CFG : CFG.mcfg dtyp) : LLVM _CFG unit :=
  allocate_globals (m_globals _ _ CFG) ;;
  allocate_declarations ((m_declarations _ _ CFG) ++ (List.map (df_prototype _ _) (m_definitions _ _ CFG)));;
  translate _exp_E_to_CFG (initialize_globals (m_globals _ _ CFG)).

(* Local environment implementation *)
Definition local_env := FMapAList.alist raw_id uvalue.
Definition global_env := FMapAList.alist raw_id dvalue.
Definition function_env := FMapAList.alist dvalue D.function_denotation.

Definition address_one_function (df : definition dtyp (CFG.cfg dtyp)) : LLVM _CFG (dvalue * D.function_denotation) :=
  let fid := (dc_name _ (df_prototype _ _ df)) in
  fv <- trigger (GlobalRead fid) ;;
  (* CB TODO: do we need pick here? *)
  (* dfv <- trigger (pick fv True) ;; *)
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


Definition build_MCFG (mcfg : CFG.mcfg dtyp) : LLVM _CFG uvalue
  := build_global_environment mcfg ;;
     'defns <- map_monad address_one_function (m_definitions _ _ mcfg) ;;
     'addr <- trigger (GlobalRead (Name "main")) ;;
     D.denote_mcfg defns DTYPE_Void addr main_args.

Definition build_MCFG1 (trace : LLVM _CFG uvalue) : LLVM _MCFG1 (global_env * uvalue)
  := @run_global _ _ _ _ show_raw_id _ _ _ _ _ trace [].

Definition build_MCFG2 (trace : LLVM _MCFG1 (global_env * uvalue)) : LLVM _MCFG2 (local_env * stack * (global_env * uvalue))
  := run_local_stack (@handle_local raw_id uvalue _ _ show_raw_id _ _) trace ([], []).

Definition build_MCFG3 (trace : LLVM _MCFG2 (local_env * stack * (global_env * uvalue))) : LLVM _MCFG3 (M.memory_stack * ((local_env * (@stack (list (raw_id * uvalue)))) * (global_env * uvalue)))
  := M.run_memory trace (M.empty, [[]]).

(* YZ TODO: Principle this definition and move it into Handlers/Pick  *)
Program Definition interp_undef {X} (trace : LLVM _MCFG3 X) : LLVM _MCFG4 X.
unfold _MCFG3 in *. unfold _MCFG4.
eapply interp. 2: exact trace.
intros T E.
repeat match goal with
| [ H : (?e +' ?E) ?T |- _ ] => destruct H as [event | undef]; try apply (trigger event)
end.
apply P.concretize_picks; auto.
Defined.

(* YZ TODO: Principle this *)
Program Definition embed_in_mcfg4 (T : Type) (E: (Failure.FailureE +' UndefinedBehaviour.UndefinedBehaviourE) T) : _MCFG4 T.
firstorder.
Defined.

Program Definition interp_model {X} (trace : LLVM _MCFG3 X) : PropT (LLVM _MCFG4) X.
unfold _MCFG3 in *. unfold _MCFG4.
eapply interp. 2: exact trace.
intros T E.
repeat match goal with
| [ H : (?e +' ?E) ?T |- _ ] => destruct H as [event | undef]; try exact (fun l => l = trigger event) (* YZ: this is the trigger instance of PropT *)
       end.
intros t.
refine (P.Pick_handler undef _).
(* Mmmh how can we conclude here? Some kind of subevent under the prop monad *)
Abort.

Definition build_MCFG4 (trace : LLVM _MCFG3 (M.memory_stack * ((local_env * (@stack (list (raw_id * uvalue)))) * (global_env * uvalue)))) : LLVM _MCFG4 (M.memory_stack * ((local_env * (@stack (list (raw_id * uvalue)))) * (global_env * dvalue)))
  := '(m, (env, (genv, uv))) <- (interp_undef trace);;
     dv <- translate embed_in_mcfg4 (P.concretize_uvalue uv);;
     ret (m, (env, (genv, dv))).

Definition interpreter (prog: list (toplevel_entity typ (list (block typ)))) :
  option (LLVM _MCFG4 (M.memory_stack * ((local_env * (@stack (list (raw_id * uvalue)))) * (global_env * dvalue)))) :=
    let scfg := Vellvm.AstLib.modul_of_toplevel_entities _ prog in

    ucfg <- CFG.mcfg_of_modul _ scfg ;;
    let mcfg := normalize_types ucfg in

    let core_trace        := build_MCFG mcfg in
    let global_trace      := INT.interpret_intrinsics core_trace in
    let local_trace       := build_MCFG1 global_trace in
    let mem_trace         := build_MCFG2 local_trace in
    let undef_Trace       := build_MCFG3 mem_trace in
    let interpreted_trace := build_MCFG4 undef_Trace in

    Some interpreted_trace.

(*
Definition model (prog: list (toplevel_entity typ (list (block typ)))) :
  option (LLVM _MCFG4 (M.memory_stack * ((local_env * (@stack (list (raw_id * uvalue)))) * (global_env * dvalue)))) :=
    let scfg := Vellvm.AstLib.modul_of_toplevel_entities _ prog in

    ucfg <- CFG.mcfg_of_modul _ scfg ;;
    let mcfg := normalize_types ucfg in

    let core_trace        := build_MCFG mcfg in
    let global_trace      := INT.interpret_intrinsics core_trace in
    let local_trace       := build_MCFG1 global_trace in
    let mem_trace         := build_MCFG2 local_trace in
    let undef_Trace       := build_MCFG3 mem_trace in
    let interpreted_trace := build_MCFG4 undef_Trace in

    Some interpreted_trace.
*)
