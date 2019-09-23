(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

(** * Plugging the pieces together: executable and propositional semantics for Vellvm *)

(* begin hide *)
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

(* end hide *)

(**
   This file ties things together to concretely defines the semantics of a [Vellvm]
   program. It covers two main tasks to do so: to initialize the memory, and to
   chain together the successive interpreters.
   As such, the raw denotation of a [Vellvm] program in terms of an [itree] is
   progressively stripped out of its events.
   We provide two such chains of interpretations: a model, that handles the
   internal non-determinism due to under-defined values into the non-determinism
   monad; and an executable one, that arbitrarily interpret under-defined values
   by setting its bits to 0.
 *)

(** Initialization
    The initialization phase allocates and initializes globals,
    and allocates function pointers.
    This initialization phase is internalized in [Vellvm], it is
    an [itree] as any other.
 *)

Definition allocate_global (g:global dtyp) : itree L0 unit :=
  (vis (Alloca (g_typ _ g)) (fun v => trigger (GlobalWrite (g_ident _ g) v))).

Definition allocate_globals (gs:list (global dtyp)) : itree L0 unit :=
  map_monad_ allocate_global gs.

(* Who is in charge of allocating the addresses for external functions declared in this mcfg? *)
Definition allocate_declaration (d:declaration dtyp) : itree L0 unit :=
  (* SAZ TODO:  Don't allocate pointers for LLVM intrinsics declarations *)
    vis (Alloca DTYPE_Pointer) (fun v => trigger (GlobalWrite (dc_name _ d) v)).

Definition allocate_declarations (ds:list (declaration dtyp)) : itree L0 unit :=
  map_monad_ allocate_declaration ds.

Definition initialize_global (g:global dtyp) : itree exp_E unit :=
  let dt := (g_typ _ g) in
  a <- trigger (GlobalRead (g_ident _ g));;
  uv <- match (g_exp _ g) with
       | None => ret (UVALUE_Undef dt)
       | Some e => D.denote_exp (Some dt) e
       end ;;
  (* CB TODO: Do we need pick here? *)
  dv <- trigger (pick uv True) ;;
  trigger (Store a dv).

Definition initialize_globals (gs:list (global dtyp)): itree exp_E unit :=
  map_monad_ initialize_global gs.

Definition build_global_environment (CFG : CFG.mcfg dtyp) : itree L0 unit :=
  allocate_globals (m_globals _ _ CFG) ;;
  allocate_declarations ((m_declarations _ _ CFG) ++ (List.map (df_prototype _ _) (m_definitions _ _ CFG)));;
  translate _exp_E_to_L0 (initialize_globals (m_globals _ _ CFG)).

(** Local environment implementation
    The map-based handlers are defined parameterized over a domain of key and value.
    We now pick concrete such domain.
    Note that while local environments may store under-defined values,
    global environments are statically guaranteed to store [dvalue]s.
 *)
Definition local_env := FMapAList.alist raw_id uvalue.
Definition global_env := FMapAList.alist raw_id dvalue.
Definition function_env := FMapAList.alist dvalue D.function_denotation.

(**
   Denotes a function and returns its pointer.
 *)

Definition address_one_function (df : definition dtyp (CFG.cfg dtyp)) : itree L0 (dvalue * D.function_denotation) :=
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

(**
   Transformation and normalization of types.
*)
Definition eval_typ (CFG:CFG.mcfg typ) (t:typ) : dtyp :=
      TypeUtil.normalize_type_dtyp (m_type_defs _ _ CFG) t.

Definition normalize_types (CFG:(CFG.mcfg typ)) : (CFG.mcfg dtyp) :=
  TransformTypes.fmap_mcfg _ _ (eval_typ CFG) CFG.

(**
   We are now ready to define our semantics. Guided by the events and handlers,
   we work in layers: the first layer is defined as the uninterpreted [itree]
   resulting from the denotation of the LLVM program. Each successive handler
   then transform a tree at layer n to a tree at layer (n+1).
 *)

(* Initialization and denotation of a Vellvm program *)
Definition build_MCFG (mcfg : CFG.mcfg dtyp) : itree L0 uvalue
  := build_global_environment mcfg ;;
     'defns <- map_monad address_one_function (m_definitions _ _ mcfg) ;;
     'addr <- trigger (GlobalRead (Name "main")) ;;
     D.denote_mcfg defns DTYPE_Void addr main_args.

(* Interpretation of the global environment *)
(* TODO YZ: Why do we need to provide this instance explicitly? *)
Definition build_MCFG1 (trace : itree L0 uvalue) : itree L1 (global_env * uvalue)
  := @run_global _ _ _ _ show_raw_id _ _ _ _ _ trace [].

(* Interpretation of the local environment: map and stack *)
Definition build_MCFG2 (trace : itree L1 (global_env * uvalue)) : itree L2 (local_env * stack * (global_env * uvalue))
  := run_local_stack (@handle_local raw_id uvalue _ _ show_raw_id _ _) trace ([], []).

(* Interpretation of the memory *)
Definition build_MCFG3 (trace : itree L2 (local_env * stack * (global_env * uvalue))) : itree L3 (M.memory_stack * ((local_env * (@stack (list (raw_id * uvalue)))) * (global_env * uvalue)))
  := M.run_memory trace (M.empty, [[]]).

(* YZ TODO: Principle this definition and move it into Handlers/Pick  *)
Program Definition interp_undef {X} (trace : itree L3 X) : itree L4 X.
unfold L3 in *. unfold L4.
eapply interp. 2: exact trace.
intros T E.
repeat match goal with
| [ H : (?e +' ?E) ?T |- _ ] => destruct H as [event | undef]; try apply (trigger event)
end.
apply P.concretize_picks; auto.
Defined.

(* YZ TODO: Principle this *)
Program Definition embed_in_mcfg4 (T : Type) (E: (FailureE +' UBE) T) : L4 T.
firstorder.
Defined.

Program Definition model_undef {X} (trace : itree L3 X) : PropT (itree L4) X.
unfold L3 in *. unfold L4.
eapply interp. 2: exact trace.
intros T E.
repeat match goal with
| [ H : (?e +' ?E) ?T |- _ ] => destruct H as [event | undef]; try exact (fun l => l = trigger event) (* YZ: this is the trigger instance of PropT *)
       end.
intros t.
generalize (P.Pick_handler undef); intros P.
refine (exists t', P t' /\ t = translate subevent t').
Defined.

Definition build_MCFG4 (trace : itree L3 (M.memory_stack * ((local_env * (@stack (list (raw_id * uvalue)))) * (global_env * uvalue)))) : itree L4 (M.memory_stack * ((local_env * (@stack (list (raw_id * uvalue)))) * (global_env * dvalue)))
  := '(m, (env, (genv, uv))) <- (interp_undef trace);;
     dv <- translate embed_in_mcfg4 (P.concretize_uvalue uv);;
     ret (m, (env, (genv, dv))).

Definition model_MCFG4 (trace : itree L3 (M.memory_stack * ((local_env * (@stack (list (raw_id * uvalue)))) * (global_env * uvalue)))) : PropT (itree L4) (M.memory_stack * ((local_env * (@stack (list (raw_id * uvalue)))) * (global_env * dvalue))).
  refine ( '(m, (env, (genv, uv))) <- (model_undef trace);; _).
  (* dv <- translate embed_in_mcfg4 (P.concretize_uvalue uv);; *)
  (*    ret (m, (env, (genv, dv))). *)
Admitted.

Definition interpreter (prog: list (toplevel_entity typ (list (block typ)))) :
  option (itree L4 (M.memory_stack * ((local_env * (@stack (list (raw_id * uvalue)))) * (global_env * dvalue)))) :=
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
  option (itree _MCFG4 (M.memory_stack * ((local_env * (@stack (list (raw_id * uvalue)))) * (global_env * dvalue)))) :=
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
