(* begin hide *)
Require Import Equalities.

From Coq Require Import ZArith List String.

From Vellvm Require Import
     Utilities
     Syntax.LLVMAst
     Syntax.AstLib.

From ExtLib Require Import
     Programming.Eqv
     Structures.Monads.



Import ListNotations.
Import EqvNotation.
Import MonadNotation.
Open Scope list.
Open Scope monad_scope.
(* end hide *)

(** * VIR internal AST

    Internally, a VIR program is represented as an element of the [mcfg] type.

    This file also provides the function [mcfg_of_tle] allowing to convert a
    [toplevel_entities (block T * list (block T))], i.e. the output of the
    parser, into a [mcfg], i.e. the input to the semantics.

    Before being fed to the semantics, a last step of pre-processing will be
    required: the conversion of types. This step is performed in the [TypToDtyp]
    module.
*)

(* control flow graphs (CFGs) ----------------------------------------------- *)
Section CFG.
  Variable (T:Set).

  Inductive cmd : Set :=
  | Inst (i:instr T)
  | Term (t:terminator T)
  .

  (** * Open cfg
      A potentially open cfg ([ocfg]) is simply a list of blocks.
   *)
  Definition ocfg := list (block T).

  (** * cfg
      Each function definition corresponds to a control-flow graph
   - init is the entry block
   - blks is a list of labeled blocks
   - args is the list of identifiers brought into scope by this function
   *)
  Record cfg := mkCFG
                  {
                    init : block_id;
                    blks : ocfg;
                    args : list raw_id;
                  }.

  Record modul {FnBody:Set} : Set :=
    mk_modul
      {
        m_name: option string;
        m_target: option string;
        m_datalayout: option string;
        m_type_defs: list (ident * T);
        m_globals: list (global T);
        m_declarations: list (declaration T);
        m_definitions: list (@definition T FnBody);
      }.

  (** * mcfg
      An [mcfg] is a module where each function body has been converted to a cfg.
      This structure is the internal representation of a VIR program.
   *)
  Definition mcfg : Set := @modul cfg.

  (* We now define the conversion from the output of the parser to the internal
     structure of a [mcfg].
     The process is fairly simple, it simply consists in two steps:
     1. dispatching the various toplevel entities into their internal representation
     inside of the structure of [modul], as performed by [modul_of_toplevel_entities]
     2. building proper [cfg]s out of the bare non-empty list of [block] provided by
     the parser, as performed by [mcfg_of_modul]
     Finally, [mcfg_of_tle] composes both functions with their parameters specialized
     to get a direct translation from the output of the parser to the input format
     of the semantics (before conversion of types).
   *)

  Definition target_of {X} (tle : toplevel_entity T X) : option string :=
    match tle with
    | TLE_Target tgt => Some tgt
    | _ => None
    end.

  Definition datalayout_of {X} (tle : toplevel_entity T X) : option string :=
    match tle with
    | TLE_Datalayout l => Some l
    | _ => None
    end.

  Definition filename_of {X} (tle : toplevel_entity T X) : option string :=
    match tle with
    | TLE_Source_filename l => Some l
    | _ => None
    end.

  Definition globals_of {X} (tle : toplevel_entity T X) : list (global T) :=
    match tle with
    | TLE_Global g => [g]
    | _ => []
    end.

  Definition declarations_of {X} (tle : toplevel_entity T X) : list (declaration T) :=
    match tle with
    | TLE_Declaration d => [d]
    | _ => []
    end.

  Definition definitions_of {X} (tle : toplevel_entity T X) : list (definition T X) :=
    match tle with
    | TLE_Definition d => [d]
    | _ => []
    end.

  Definition type_defs_of {X} (tle : toplevel_entity T X) : list (ident * T) :=
    match tle with
    | TLE_Type_decl id t => [(id,t)]
    | _ => []
    end.

  Definition modul_of_toplevel_entities {X} (tles : toplevel_entities T X) : @modul X :=
    {|
      m_name := find_map filename_of tles;
      m_target := find_map target_of tles;
      m_datalayout := find_map datalayout_of tles;
      m_type_defs := flat_map type_defs_of tles;
      m_globals := flat_map globals_of tles;
      m_declarations := flat_map declarations_of tles;
      m_definitions := flat_map definitions_of tles;
    |}.

  Definition tle_of_name {X} (m_name: option string): toplevel_entities T X :=
    match m_name with
    | None => []
    | Some n => [TLE_Source_filename n]
    end.

  Definition tle_of_target {X} (m_target: option string): toplevel_entities T X :=
    match m_target with
    | None => []
    | Some n => [TLE_Target n]
    end.

  Definition tle_of_datalayout {X} (m_datalayout: option string): toplevel_entities T X :=
    match m_datalayout with
    | None => []
    | Some n => [TLE_Datalayout n]
    end.

  Fixpoint tle_of_type_defs {X} (m_type_defs: list (ident * T)): toplevel_entities T X :=
    match m_type_defs with
    | [] => []
    | (id, t)::l => (TLE_Type_decl id t)::(tle_of_type_defs l)
    end.

  Fixpoint tle_of_globals {X} (m_globals: list (global T)): toplevel_entities T X :=
    match m_globals with
    | [] => []
    | g::gs => (TLE_Global g)::(tle_of_globals gs)
    end.

  Fixpoint tle_of_declarations {X} (m_declarations: list (declaration T)): toplevel_entities T X :=
    match m_declarations with
    | [] => []
    | d::ds => (TLE_Declaration d)::(tle_of_declarations ds)
    end.

  Fixpoint tle_of_definitions {X} (m_definitions: list (definition T X)): toplevel_entities T X :=
    match m_definitions with
    | [] => []
    | d::ds => (TLE_Definition d)::(tle_of_definitions ds)
    end.

  Definition toplevel_entities_of_modul {X} (m: @modul X): toplevel_entities T X :=
    tle_of_name (m_name m)
    ++ tle_of_target (m_target m)
    ++ tle_of_datalayout (m_datalayout m)
    ++ tle_of_type_defs (m_type_defs m)
    ++ tle_of_globals (m_globals m)
    ++ tle_of_declarations (m_declarations m)
    ++ tle_of_definitions (m_definitions m)
  .

  Definition init_of_definition (d : definition T (block T * list (block T))) : block_id :=
    blk_id (fst (df_instrs d)).

  Definition cfg_of_definition (d : definition T (block T * list (block T))) : cfg :=
    {| init := init_of_definition d;
       blks := fst (df_instrs d) :: snd (df_instrs d);
       args := df_args d;
    |}.

  Definition mcfg_of_modul (m : @modul (block T * list (block T))) : mcfg :=
    let defns := map (fun d => {|
                          df_prototype := df_prototype d;
                          df_args := df_args d;
                          df_instrs := cfg_of_definition d
                        |}) (m_definitions m)
    in
    {|
      m_name := m_name m;
      m_target := m_target m;
      m_datalayout := m_datalayout m;
      m_type_defs := m_type_defs m;
      m_globals := m_globals m;
      m_declarations := m_declarations m;
      m_definitions := defns
    |}.

  (* Utility to lookup by id a block from a list of blocks *)
  Definition find_block (bs: list (block T)) block_id : option (block T) :=
    find (fun b => if (blk_id b) ~=? block_id then true else false) bs.

  Fixpoint modul_defns_of_mcfg_defns (ds: list (definition T cfg)): option (list (definition T (block T * list (block T)))) :=
    match ds with
    | [] => Some []
    | d::ds => match blks (df_instrs d) with
              | [] => None
              | x::xs => match modul_defns_of_mcfg_defns ds with
                        | None => None
                        | Some l => Some (
                                       {|
                                         df_prototype := df_prototype d;
                                         df_args := df_args d;
                                         df_instrs := (x, xs)
                                       |}
                                         ::l)
                        end
              end
    end.

  Definition modul_of_mcfg (m: mcfg): option (@modul (block T * list (block T))) :=
    match modul_defns_of_mcfg_defns (m_definitions m) with
    | None => None
    | Some defns => Some
                     {|
                       m_name := m_name m;
                       m_target := m_target m;
                       m_datalayout := m_datalayout m;
                       m_type_defs := m_type_defs m;
                       m_globals := m_globals m;
                       m_declarations := m_declarations m;
                       m_definitions := defns
                     |}
    end.

End CFG.

Arguments modul_of_toplevel_entities {T X}.
Arguments mcfg_of_modul {T}.
Arguments modul_of_mcfg {T}.
Arguments modul_defns_of_mcfg_defns {T}.

(* Conversion of the output of the parser to the [mcfg] structure manipulated internally *)
Definition mcfg_of_tle (p : toplevel_entities typ (block typ * list (block typ))) :=
  mcfg_of_modul (modul_of_toplevel_entities p).

Arguments modul {_} _.
Arguments mk_modul {_ _}.
Arguments m_name {_ _}.
Arguments m_target {_ _}.
Arguments m_datalayout {_ _}.
Arguments m_type_defs {_ _}.
Arguments m_globals {_ _}.
Arguments m_declarations {_ _}.
Arguments m_definitions {_ _}.
Arguments mkCFG {_}.
Arguments find_block {_}.
Arguments blks {_}.
Arguments init {_}.
Arguments args {_}.

Section TLE_To_Modul.

  Lemma modul_defns_of_mcfg_defns_map_cfg_of_definition:
    forall {T} (l: list (definition T (block T * list (block T)))),
      modul_defns_of_mcfg_defns (map (fun d => {|
                                          df_prototype := df_prototype d;
                                          df_args := df_args d;
                                          df_instrs := cfg_of_definition T d
                                        |}) l) = Some l.
  Proof using.
    induction l; simpl; auto.
    rewrite IHl. repeat f_equal.
    destruct a; simpl; f_equal.
    destruct df_instrs; simpl; auto.
  Qed.

  Lemma modul_of_mcfg_of_modul:
    forall {T} (m: @modul T _),
      modul_of_mcfg (mcfg_of_modul m) = Some m.
  Proof using.
    destruct m.
    unfold mcfg_of_modul; simpl.
    unfold modul_of_mcfg; simpl.
    rewrite modul_defns_of_mcfg_defns_map_cfg_of_definition.
    reflexivity.
  Qed.

  Definition opt_first {T: Type} (o1 o2: option T): option T :=
    match o1 with | Some x => Some x | None => o2 end.

  Definition modul_app {T X} (m1 m2: @modul T X): @modul T X :=
    let (name1, target1, layout1, tdefs1, globs1, decls1, defs1) := m1 in
    let (name2, target2, layout2, tdefs2, globs2, decls2, defs2) := m2 in
    {|
      m_name := opt_first name1 name2;
      m_target := opt_first target1 target2;
      m_datalayout := opt_first layout1 layout2;
      m_type_defs := tdefs1 ++ tdefs2;
      m_globals := globs1 ++ globs2;
      m_declarations := decls1 ++ decls2;
      m_definitions := defs1 ++ defs2
    |}.

  Lemma modul_of_toplevel_entities_cons:
    forall {T X} tle tles,
      @modul_of_toplevel_entities T X (tle :: tles) = modul_app (modul_of_toplevel_entities [tle]) (modul_of_toplevel_entities tles).
  Proof using.
    intros.
    unfold modul_of_toplevel_entities; cbn; f_equal;
      try ((break_match_goal; reflexivity) || (rewrite !app_nil_r; reflexivity)).
  Qed.

  Lemma modul_of_toplevel_entities_app:
    forall {T X} tle1 tle2,
    @modul_of_toplevel_entities T X (tle1 ++ tle2) = modul_app (modul_of_toplevel_entities tle1) (modul_of_toplevel_entities tle2).
  Proof using.
    induction tle1 as [| tle tle1 IH]; intros; cbn; [reflexivity |].
    rewrite modul_of_toplevel_entities_cons, IH; cbn.
    f_equal;
      try ((break_match_goal; reflexivity) || (rewrite !app_nil_r, app_assoc; reflexivity)).
  Qed.

  Infix "@@" := (modul_app) (at level 60).

  Lemma m_definitions_app: forall {T X} (p1 p2 : @modul T X),
      m_definitions (p1 @@ p2) = m_definitions p1 ++ m_definitions p2.
  Proof using.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma m_name_app: forall {T X} (p1 p2 : @modul T X),
      m_name (p1 @@ p2) = opt_first (m_name p1) (m_name p2).
  Proof using.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma m_target_app: forall {T X} (p1 p2 : @modul T X),
      m_target (p1 @@ p2) = opt_first (m_target p1) (m_target p2).
  Proof using.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma m_datalayout_app: forall {T X} (p1 p2 : @modul T X),
      m_datalayout (p1 @@ p2) = opt_first (m_datalayout p1) (m_datalayout p2).
  Proof using.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma m_type_defs_app: forall {T X} (p1 p2 : @modul T X),
      m_type_defs (p1 @@ p2) = m_type_defs p1 ++ m_type_defs p2.
  Proof using.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma m_globals_app: forall {T X} (p1 p2 : @modul T X),
      m_globals (p1 @@ p2) = m_globals p1 ++ m_globals p2.
  Proof using.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma m_declarations_app: forall {T X} (p1 p2 : @modul T X),
      m_declarations (p1 @@ p2) = m_declarations p1 ++ m_declarations p2.
  Proof using.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma map_option_cons_inv: forall {A B} (f : A -> option B) (a : A) (l : list A) (r : list B),
      map_option f (a :: l) = Some r ->
       exists b r',
        f a = Some b /\
        map_option f l = Some r' /\
        r = b :: r'.
  Proof using.
    intros.
    cbn in H; do 2 (break_match_hyp; try inv_option).
    do 2 eexists; repeat split; auto.
  Qed.

  Lemma map_option_cons: forall {A B} (f : A -> option B) (a : A) (b : B) (l : list A) (r : list B),
        f a = Some b ->
        map_option f l = Some r ->
        map_option f (a :: l) = Some (b :: r).
  Proof using.
    intros * EQ1 EQ2; simpl; rewrite EQ1, EQ2; reflexivity.
  Qed.

  Lemma map_option_app_inv: forall {A B} (f : A -> option B) (l1 l2 : list A) (r : list B),
      map_option f (l1 ++ l2) = Some r ->
      exists r1 r2,
        map_option f l1 = Some r1 /\
        map_option f l2 = Some r2 /\
        r = r1 ++ r2.
  Proof using.
    induction l1 as [| x l1 IH]; intros * EQ.
    - do 2 eexists; repeat split; try reflexivity; auto.
    - generalize EQ; intros EQ'; apply map_option_cons_inv in EQ'; destruct EQ' as (b & ? & EQ1 & EQ2 & ->).
      apply IH in EQ2; destruct EQ2 as (r1 & r2 & EQ2 & EQ3 & ->).
      exists (b::r1), r2; repeat split; auto.
      apply map_option_cons; auto.
  Qed.

  Lemma mcfg_of_app_modul: forall {T} (p1 p2 : @modul T _),
      mcfg_of_modul (p1 @@ p2) = mcfg_of_modul p1 @@ mcfg_of_modul p2.
  Proof using.
    intros; cbn.
    unfold mcfg_of_modul.
    rewrite  m_name_app, m_target_app, m_datalayout_app, m_type_defs_app, m_globals_app, m_declarations_app; f_equal; try reflexivity.
    rewrite m_definitions_app, map_app; reflexivity.
  Qed.

End TLE_To_Modul.

Module CFGNotations.
  Infix "@@" := (modul_app) (at level 60).
End CFGNotations.
