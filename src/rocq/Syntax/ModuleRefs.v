(* begin hide *)
From Vellvm Require Import
  Utils
  Syntax.LLVMAst
  Syntax.RawIdMaps.

Import ListNotations.
(* end hide *)

(** * Module-level references

    A module can name a metadata node ([!1 = !{i64 8}]) and a set of function
    attributes ([attributes #0 = { noreturn nounwind }]), and then refer to
    them by number: [load ptr, ptr %p, !align !1] or [define void @f() #0].
    The conversion to an [mcfg] keeps neither kind of definition, so
    [resolve_module_refs] replaces the references by what they name:

    - in the metadata attached to instructions, phis, and terminators, a
      value [!N] becomes the node [!N] names (one level: the nodes it contains
      are left as they are, so self-referential nodes such as loop metadata
      stay finite);
    - in the function attributes of declarations, definitions, calls, and
      invokes, [#N] becomes the attributes of group [#N].

    A direct call or invoke of [@f] also refers to [@f]'s declaration (or
    definition) in the module, whose parameter and return-value attributes
    apply to the call together with the call site's own (LangRef combines
    them: e.g. [nonnull] on the declaration and [noundef] at the call site
    make a null argument undefined behavior).  So those attributes are
    appended to the call site's.

    References to undefined numbers are left in place.  The numbers are local
    to a module, so this must run on each module before modules are linked. *)

Section ModuleRefs.
  Context {T : Set}.

  Definition metadata_defs (tles : toplevel_entities T (block T * list (block T)))
    : IntMap (metadata T) :=
    fold_left (fun m tle =>
                 match tle with
                 | TLE_Metadata (METADATA_Id (Anon n)) _ md => IntMaps.add n md m
                 | _ => m
                 end) tles IntMaps.empty.

  Definition attribute_groups (tles : toplevel_entities T (block T * list (block T)))
    : IntMap (list fn_attr) :=
    fold_left (fun m tle =>
                 match tle with
                 | TLE_Attribute_group n attrs => IntMaps.add n attrs m
                 | _ => m
                 end) tles IntMaps.empty.

  (** ** Metadata *)

  (* Instruction metadata is a list of [kind value] pairs. *)
  Definition resolve_metadata (defs : IntMap (metadata T)) (md : metadata T) : metadata T :=
    match md with
    | METADATA_Pair kind (METADATA_Id (Anon n)) =>
        match IntMaps.lookup n defs with
        | Some node => METADATA_Pair kind node
        | None => md
        end
    | _ => md
    end.

  Definition resolve_metadata_list (defs : IntMap (metadata T)) (mds : list (metadata T))
    : list (metadata T) :=
    List.map (resolve_metadata defs) mds.

  (** ** Attribute groups *)

  Definition expand_fn_attrs (groups : IntMap (list fn_attr)) (attrs : list fn_attr)
    : list fn_attr :=
    flat_map (fun a =>
                match a with
                | FNATTR_Attr_grp n =>
                    match IntMaps.lookup n groups with
                    | Some attrs' => attrs'
                    | None => [a]
                    end
                | _ => [a]
                end) attrs.

  (* Function attributes of a call or invoke are [ANN_fun_attribute]s. *)
  Definition expand_annotations (groups : IntMap (list fn_attr)) (anns : list (annotation T))
    : list (annotation T) :=
    flat_map (fun ann =>
                match ann with
                | ANN_fun_attribute a => List.map ANN_fun_attribute (expand_fn_attrs groups [a])
                | _ => [ann]
                end) anns.

  Definition expand_declaration (groups : IntMap (list fn_attr)) (d : declaration T)
    : declaration T :=
    mk_declaration (dc_name d) (dc_type d) (dc_param_attrs d)
                   (expand_fn_attrs groups (dc_attrs d)) (dc_annotations d).

  (** ** Callee attributes *)

  (* The return-value and parameter attributes of the module's functions. *)
  Definition callee_attrs (tles : toplevel_entities T (block T * list (block T)))
    : rmap (list param_attr * list (list param_attr)) :=
    fold_left (fun m tle =>
                 match tle with
                 | TLE_Declaration d => RM.add (dc_name d) (dc_param_attrs d) m
                 | TLE_Definition d =>
                     RM.add (dc_name (df_prototype d)) (dc_param_attrs (df_prototype d)) m
                 | _ => m
                 end) tles (RM.empty _).

  (* Each argument gets its parameter's attributes; arguments past the
     declared parameters (varargs) get none. *)
  Fixpoint merge_arg_attrs (args : list (texp T * list param_attr)) (attrss : list (list param_attr))
    : list (texp T * list param_attr) :=
    match args, attrss with
    | (a, attrs) :: args', attrs' :: attrss' => (a, attrs ++ attrs') :: merge_arg_attrs args' attrss'
    | _, _ => args
    end.

  (* A direct call's arguments and annotations, with its callee's
     attributes appended. *)
  Definition merge_callee_attrs (callees : rmap (list param_attr * list (list param_attr)))
             (fn : texp T) (args : list (texp T * list param_attr)) (anns : list (annotation T))
    : list (texp T * list param_attr) * list (annotation T) :=
    match snd fn with
    | EXP_Ident (ID_Global f) =>
        match rid_lookup f callees with
        | Some (ret_attrs, attrss) =>
            (merge_arg_attrs args attrss, anns ++ List.map ANN_ret_attribute ret_attrs)
        | None => (args, anns)
        end
    | _ => (args, anns)
    end.

  (** ** Function bodies *)

  Definition resolve_instr (groups : IntMap (list fn_attr))
             (callees : rmap (list param_attr * list (list param_attr))) (i : instr T) : instr T :=
    match i with
    | INSTR_Call fn args anns obs =>
        let '(args', anns') := merge_callee_attrs callees fn args anns in
        INSTR_Call fn args' (expand_annotations groups anns') obs
    | _ => i
    end.

  Definition resolve_terminator (groups : IntMap (list fn_attr))
             (callees : rmap (list param_attr * list (list param_attr))) (t : terminator T) : terminator T :=
    match t with
    | TERM_Invoke fn args to_label unwind_label anns obs =>
        let '(args', anns') := merge_callee_attrs callees fn args anns in
        TERM_Invoke fn args' to_label unwind_label (expand_annotations groups anns') obs
    | _ => t
    end.

  Definition resolve_block (defs : IntMap (metadata T)) (groups : IntMap (list fn_attr))
             (callees : rmap (list param_attr * list (list param_attr)))
             (b : block T) : block T :=
    mk_block (blk_id b)
             (List.map (fun '(id, p, md) => (id, p, resolve_metadata_list defs md)) (blk_phis b))
             (List.map (fun '(id, i, md) => (id, resolve_instr groups callees i, resolve_metadata_list defs md))
                       (blk_code b))
             (let '(id, t, md) := blk_term b in
              (id, resolve_terminator groups callees t, resolve_metadata_list defs md))
             (blk_comments b).

  Definition resolve_definition (defs : IntMap (metadata T)) (groups : IntMap (list fn_attr))
             (callees : rmap (list param_attr * list (list param_attr)))
             (d : definition T (block T * list (block T)))
    : definition T (block T * list (block T)) :=
    let '(entry, blks) := df_instrs d in
    mk_definition (expand_declaration groups (df_prototype d)) (df_args d)
                  (resolve_block defs groups callees entry,
                   List.map (resolve_block defs groups callees) blks).

  Definition resolve_module_refs (tles : toplevel_entities T (block T * list (block T)))
    : toplevel_entities T (block T * list (block T)) :=
    let defs := metadata_defs tles in
    let groups := attribute_groups tles in
    let callees := callee_attrs tles in
    List.map (fun tle =>
                match tle with
                | TLE_Declaration d => TLE_Declaration (expand_declaration groups d)
                | TLE_Definition d => TLE_Definition (resolve_definition defs groups callees d)
                | _ => tle
                end) tles.

End ModuleRefs.
