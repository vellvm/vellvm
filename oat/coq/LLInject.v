Require Import List.
Import ListNotations.
Require Import ZArith.

Require Import Vellvm.LLVMAst.
Require Import Vellvm.AstLib.

Require Import Oat.LL.

From Coq Require Import String.

Open Scope string_scope.

Definition llvm_block : Set := LLVMAst.block typ.
Definition FnBody := llvm_block * list llvm_block.

Module LLVM := LLVMAst.

Definition map_id (id : String.string) : raw_id := Name id.

Fixpoint map_ty (t : ty) : typ :=
  match t with
  | Void => TYPE_Void
  | I1 => TYPE_I 1%Z
  | I8 => TYPE_I 8%Z
  | I64 => TYPE_I 64%Z
  | Ptr t' => TYPE_Pointer (map_ty t')
  | Struct tlist => TYPE_Struct (List.map map_ty tlist)
  | Array n t' => TYPE_Array (Z.of_nat n) (map_ty t')
  | Fun tlist t' =>
    TYPE_Function (map_ty t')
                  (List.map map_ty tlist)
  | Namedt tid =>
    TYPE_Identified (ID_Global (map_id tid))
  end.

Fixpoint map_ginit_to_value (x : ginit) : LLVM.exp typ :=
  match x with
  | GNull => EXP_Null
  | GGid id => EXP_Ident (ID_Global (map_id id))
  | GInt n => EXP_Integer (0%Z) (* SAZ: TODO  (Int64.signed n) *)
  | GString s => EXP_Cstring s 
  | GArray l =>
    EXP_Array
      (List.map
         (fun '(t, y) =>
            (map_ty t, map_ginit_to_value y))
         l)
  | GStruct l =>
    EXP_Struct
      (List.map
         (fun '(t, y) =>
            (map_ty t, map_ginit_to_value y))
         l)
  end.

Definition map_gdecl (id : gid) (decl : gdecl): toplevel_entity typ FnBody :=
  let '(t, v) := decl in 
  TLE_Global
    {| g_ident := map_id id ;
       g_typ := map_ty t;
       g_constant := false; (* check *)
       g_exp := Some (map_ginit_to_value v);

       (* check *)
       g_linkage := None; 
       g_visibility := None;
       g_dll_storage := None;
       g_thread_local := None;
       
       g_unnamed_addr := false;
       g_addrspace := None;
       g_externally_initialized := false;
       g_section := None;
       g_align := None
    |}.


Definition map_fty (name : gid) (function_type : fty) : LLVM.declaration typ :=
  let '(args_ty, ret_ty) := function_type in
  {| 
     dc_name := map_id name;
     dc_type := TYPE_Function (map_ty ret_ty) (List.map map_ty args_ty); 
     dc_param_attrs := ([], []);
     dc_linkage := None; 
     dc_visibility := None; 
     dc_dll_storage := None;
     dc_cconv := None;
     dc_attrs := [];
     dc_section := None;
     dc_align := None; 
     dc_gc := None;
  |}.

Definition map_operand (opr : operand) : exp typ :=
  match opr with
  | Null => EXP_Null
  | Const n => EXP_Integer (0%Z) (* SAZ: TODO -- convert nat to Z  (Int64.signed n) *)
  | Gid id => EXP_Ident (ID_Global (map_id id))
  | Id id => EXP_Ident (ID_Local (map_id id))
  end.

Definition map_bop (b : bop) : ibinop :=
  match b with
  | Add => LLVM.Add false false 
  | Sub => LLVM.Sub false false 
  | Mul => LLVM.Mul false false 
  | Shl => LLVM.Shl false false 
  | Lshr => LLVM.LShr false
  | Ashr => LLVM.AShr false 
  | And => LLVM.And 
  | Or => LLVM.Or
  | Xor => LLVM.Xor                    
  end.

Definition map_cnd (c : cnd) : icmp :=
  match c with
  | Eq => LLVM.Eq
  | Ne => LLVM.Ne
  | Slt => LLVM.Slt
  | Sle => LLVM.Sle
  | Sgt => LLVM.Sgt
  | Sge => LLVM.Sge
  end.

Definition compile_insn
           (st : int * code typ)
           (uid_insn : uid * insn) : int * code typ :=
  let '(counter, curr) := st in 
  let '(uid, insn) := uid_insn in
  match insn with
  | Binop bop t opr1 opr2 =>
    let iid := IId (map_id uid) in
    let instr := 
        INSTR_Op
          (OP_IBinop (map_bop bop) (map_ty t)
                     (map_operand opr1) (map_operand opr2)) in 
    (counter, (iid, instr) :: curr)
  | Alloca t =>
    let iid := IId (map_id uid) in
    let instr := INSTR_Alloca (map_ty t) None None in 
    (counter, (iid, instr) :: curr)
  | Load t opr =>
    let iid := IId (map_id uid) in 
    let t' := map_ty t in
    let instr := INSTR_Load false t' (t', map_operand opr) None in
    (counter, (iid, instr) :: curr)
  | Store t opr1 opr2 =>
    let iid := IVoid counter in
    let t' := map_ty t in
    let instr := INSTR_Store false
                             (t', map_operand opr1)
                             (t', map_operand opr2)
                             None
    in
    ((counter + 1)%Z, (iid, instr) :: curr)
  | Icmp cond t opr1 opr2 =>
      let iid := IId (map_id uid) in
      let instr := 
          INSTR_Op (OP_ICmp (map_cnd cond)
                            (map_ty t)
                            (map_operand opr1) (map_operand opr2))
      in
      (counter, (iid, instr) :: curr)
  | Call t opr args =>
    (* injection is partial because LLVM calls need identifiers *)
    let (iid, counter') :=
        match t with
        | Void => (IVoid counter, (counter + 1)%Z)
        | _ => (IId (map_id uid), counter)
        end in
    let instr := INSTR_Call (map_ty t, map_operand opr)
                            (List.map (fun '(arg_ty, arg) =>
                                         (map_ty arg_ty, map_operand arg))
                                      args) in
    (counter', (iid, instr) :: curr)
  | Bitcast t1 opr t2 =>
    let iid := IId (map_id uid) in
    let instr := 
        INSTR_Op
          (OP_Conversion LLVM.Bitcast
                           (map_ty t1) (map_operand opr) (map_ty t2)) in
    (counter, (iid, instr) :: curr)
  | Gep t opr operands =>
    (* check *)
    let iid := IId (map_id uid) in
    let t' := map_ty t in
    let instr := 
        INSTR_Op
          (OP_GetElementPtr
             t' 
             (t', map_operand opr)
             (List.map (fun opr => (TYPE_I 64%Z, map_operand opr)) operands)) in
    (counter, (iid, instr) :: curr)
  end.

Definition map_terminator (term : terminator) : LLVM.terminator typ :=
  match term with
  | Ret t opr_opt =>
    match opr_opt with
    | None => TERM_Ret_void
    | Some opr =>
      TERM_Ret (map_ty t, map_operand opr)
    end
  | Br id =>
    TERM_Br_1 (map_id id)
  | Cbr opr id1 id2 =>
    TERM_Br (TYPE_I 1%Z, map_operand opr) (map_id id1) (map_id id2)
  end.

Definition map_block (block_id : lbl)
           (blk : block) : (llvm_block) :=
  let '(counter, instrs) :=
      List.fold_left compile_insn (insns blk) (1%Z, []) in
  let instrs := List.rev instrs in
  {| blk_id := map_id block_id ;
     blk_phis := [] ;
     blk_code := instrs;
     blk_comments := None; 
     blk_term :=
       let '(uid, tminator) := term blk in
       (IVoid counter, map_terminator tminator)
  |}.

Scheme Equality for String.string.

Definition map_fdecl (name : gid) (decl : fdecl)
  : option (toplevel_entity typ FnBody) :=

  let '(entry, blks) := f_cfg decl in

  let '(other_blks, all_labels) :=
      List.fold_left
        (fun blks_labels '(label, blk) =>
           let '(blks, labels) := blks_labels in
           let blk' := map_block label blk in
           (blk' :: blks, label :: labels))
        blks ([], []) in

  if List.existsb (fun label => string_beq label "entry") all_labels then
    None
  else 
    let entry_blk := map_block "entry" entry in
    let instrs := (entry_blk, List.rev other_blks) in
    Some (TLE_Definition 
            {| df_prototype := map_fty name (f_ty decl);
               df_args := List.map map_id (f_param decl) ;
               df_instrs := instrs
            |}
         ).
          
Definition inject_tdecls (declarations : list (tid * ty)) :
  toplevel_entities typ (FnBody : Set) :=
  List.map
    (fun '(id, t) =>
       TLE_Type_decl (ID_Global (map_id id)) (map_ty t)) declarations.

Definition inject_gdecls (declarations : list (gid * gdecl)) :
  toplevel_entities typ FnBody :=
  List.map (fun '(id, decl) => map_gdecl id decl) declarations.

Definition inject_fdecls (declarations : list (gid * fdecl)) :
  option (toplevel_entities typ FnBody) :=
  let res :=
      List.fold_left
        (fun tles_opt '(gid, decl) =>
           match tles_opt with
           | None => None
           | Some tles =>
             let tle_opt := map_fdecl gid decl in
             match tle_opt with
             | None => None
             | Some tle => Some (tle :: tles)
             end
           end)
        declarations
        (Some [])        
  in
  match res with
  | None => None
  | Some res' => Some (List.rev res')
  end.

Definition inject_edecls (declarations : list (gid * ty)) :
  toplevel_entities typ FnBody :=
  (* confirm map to TLE_Type_decl *)
  List.map (fun '(gid, ty) =>
              TLE_Type_decl (ID_Global (map_id gid)) (map_ty ty))
           declarations.

Definition inject_prog (p : prog) : option (modul typ FnBody) :=
  match inject_fdecls (fdecls p) with
  | None => None
  | Some func_decls =>
    Some (modul_of_toplevel_entities _
            (inject_tdecls (tdecls p) ++
                           inject_gdecls (gdecls p) ++
                           func_decls ++
                           inject_edecls (edecls p)))%list
  end.
