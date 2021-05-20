(** 
    Show instances for Vellvm. These serialize Vellvm ASTs into the
    standard format for .ll files. The result of show on a Vellvm
    program should give you a string that can be read by clang.
*)

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Eqv.

From Vellvm Require Import LLVMAst Util AstLib Syntax.CFG Semantics.TopLevel.
Require Import Integers Floats.

Require Import List.

Import ListNotations.
Import MonadNotation.

From Coq Require Import
     ZArith List String Lia Bool.Bool.

Section ShowInstances.
  Definition show_raw_id (rid : raw_id) : string
    := match rid with
       | Name s => s
       | Anon i => show i
       | Raw i  => show i
       end.

  Global Instance showRawId : Show raw_id
    := {| show := show_raw_id |}.

  Definition show_ident (i : ident) : string
    := match i with
       | ID_Global r => "@" ++ show_raw_id r
       | ID_Local r  => "%" ++ show_raw_id r
       end.

  Global Instance showIdent : Show ident
    := {| show := show_ident |}.

  Local Open Scope string.

  Fixpoint show_typ (t : typ) : string :=
    match t with
    | TYPE_I sz                 => "i" ++ show sz
    | TYPE_Pointer t            => show_typ t ++ "*"
    | TYPE_Void                 => "void"
    | TYPE_Half                 => "half"
    | TYPE_Float                => "float"
    | TYPE_Double               => "double"
    | TYPE_X86_fp80             => "x86_fp80"
    | TYPE_Fp128                => "fp128"
    | TYPE_Ppc_fp128            => "ppc_fp128"
    | TYPE_Metadata             => "metadata"
    | TYPE_X86_mmx              => "x86_mmx"
    | TYPE_Array sz t           => "[" ++ show sz ++ " x " ++ show_typ t ++ "]"
    | TYPE_Function ret args    => show_typ ret ++ " (" ++ concat ", " (map show_typ args) ++ ")"
    | TYPE_Struct fields        => "{" ++ concat ", " (map show_typ fields) ++ "}"
    | TYPE_Packed_struct fields => "<{" ++ concat ", " (map show_typ fields) ++ "}>"
    | TYPE_Opaque               => "opaque"
    | TYPE_Vector sz t          => "<" ++ show sz ++ " x " ++ show_typ t ++ ">"
    | TYPE_Identified id        => show id
    end.

  Global Instance showTyp:  Show typ :=
    {|
    show := show_typ
    |}.

  Definition show_ibinop (iop : ibinop) : string
    := match iop with
       (* TODO print flags *)
       | LLVMAst.Add _ _ => "add"
       | Sub _ _ => "sub"
       | Mul _ _ => "mul"
       | Shl _ _ => "shl"
       | UDiv _  => "udiv"
       | SDiv _  => "sdiv"
       | LShr _  => "lshr"
       | AShr _  => "ashr"
       | URem    => "urem"
       | SRem    => "srem"
       | And     => "and"
       | Or      => "or"
       | Xor     => "xor"
       end.

  Global Instance showIBinop : Show ibinop
    := {| show := show_ibinop |}.

  Definition show_icmp (cmp : icmp) : string
    := match cmp with
       | Eq  => "eq"
       | Ne  => "ne"
       | Ugt => "ugt"
       | Uge => "uge"
       | Ult => "ult"
       | Ule => "ule"
       | Sgt => "sgt"
       | Sge => "sge"
       | Slt => "slt"
       | Sle => "sle"
       end.

  Global Instance showICmp : Show icmp
    := {| show := show_icmp |}.

  Fixpoint show_exp (v : exp typ) :=
      match v with
      | EXP_Ident id => show id
      | EXP_Integer x => show x
      | EXP_Bool b => show b
      | EXP_Null => "null"
      | EXP_Zero_initializer => "zero initializer"
      | EXP_Cstring s => "unimplemented cstring" (* TODO, this is wrong *)
      | EXP_Undef => "undef"
      | OP_IBinop iop t v1 v2 =>
        show iop ++ " " ++ show t ++ " " ++ show_exp v1 ++ ", " ++ show_exp v2
      | OP_ICmp cmp t v1 v2 =>
        "icmp " ++ show cmp ++ " " ++ show t ++ " " ++ show_exp v1 ++ ", " ++ show_exp v2
      | OP_GetElementPtr t ptrval idxs =>
        "todo: getelementptr"
      | OP_Select (tc, cnd) (t1, v1) (t2, v2) =>
        "select " ++ show tc ++ " " ++ show_exp cnd ++ ", " ++ show t1 ++ " " ++ show_exp v1  ++ ", " ++ show t2 ++ " " ++ show_exp v2
      | _ => "show_exp todo"
      end.

  Global Instance showExp : Show (exp typ)
    := {| show := show_exp |}.

  Global Instance showTExp : Show (texp typ)
    := {| show te :=
            match te with
            | (t, e) => show t ++ " " ++ show e
            end
       |}.

  Definition show_opt_prefix {A} `{Show A} (prefix : string) (ma : option A) : string
    := match ma with
       | None   => ""
       | Some a => prefix ++ show a
       end.

  Definition show_instr (i : instr typ) : string
    := match i with
       | INSTR_Comment s => "; " ++ s
       | INSTR_Op e => show e
       | INSTR_Load vol t ptr align =>
         "load " ++ show t ++ ", " ++ show ptr ++ show_opt_prefix ", align " align
       | INSTR_Store vol tval ptr align =>
         "store " ++ (if vol then "volatile " else "") ++ show tval ++ ", " ++ show ptr ++ show_opt_prefix ", align " align
       | INSTR_Alloca t nb align =>
         "alloca " ++ show t ++ show_opt_prefix ", " nb ++ show_opt_prefix ", align " align
       | _ => "show_instr todo"
       end.

  Global Instance showInstr : Show (instr typ)
    := {| show := show_instr |}.

  Global Instance showInstrId : Show instr_id
    := {| show i :=
            match i with
            | IId raw => ("%" ++ show raw)%string
            | IVoid n => ("void<" ++ show n ++ ">")%string
            end
       |}.

  Definition show_instr_id (inst : instr_id * instr typ) : string
    :=
      let '(iid, i) := inst in
      match iid with
        | IId _ =>
          (show iid ++ " = " ++ show i)%string
        | IVoid n =>
          show i
      end.

  Global Instance showInstrWithId : Show (instr_id * instr typ)
    := {| show := show_instr_id |}.

  Definition show_terminator (t : terminator typ) : string
    := match t with
       | TERM_Ret v => "ret " ++ show v
       | TERM_Ret_void => "ret"
       | TERM_Br te b1 b2 =>
         "br " ++ show te ++ ", label %" ++ show b1 ++ ", label %" ++ show b2
       | TERM_Br_1 b =>
         "br label %" ++ show b
       | _ => "show_terminator todo"
       end.

  Global Instance showTerminator : Show (terminator typ)
    := {| show := show_terminator |}.

  Definition show_code (indent : string) (c : code typ) : string
    := concatStr (map (fun iid => indent ++ show_instr_id iid ++ newline) c).

  Global Instance showCode : Show (code typ)
    := {| show := show_code "    " |}.

  Definition show_phi_block (p : block_id * exp typ) : string :=
    let '(bid, e) := p in
    "[ " ++ show e ++ ", " ++ "%" ++ show bid ++ " ]".

  Definition intersperse (sep : string) (l : list string) : string
    := fold_left (fun acc s => if StringOrdFacts.eqb "" acc then s else s ++ sep ++ acc) l "".

  Global Instance showPhi : Show (phi typ)
    := {| show p :=
            let '(Phi t phis) := p in
            "phi " ++ show t ++ " " ++ intersperse ", " (map show_phi_block phis)
       |}.

  Definition show_block (indent : string) (b : block typ) : string
    :=
      let phis   := concatStr (map (fun '(l, p) => indent ++ "%" ++ show l ++ " = " ++ show p ++ newline) (blk_phis b)) in
      let code   := show_code indent (blk_code b) in
      let term   := indent ++ show (blk_term b) ++ newline in
      show (blk_id b) ++ ":" ++ newline
           ++ phis
           ++ code
           ++ term.

  Global Instance showBlock: Show (block typ) :=
    {|
    show := show_block "    "
    |}.

  Definition show_arg (arg : local_id * typ) : string
    := let '(i, t) := arg in
       show t ++ " %" ++ show i.

  Definition show_arg_list (args : list (local_id * typ)) : string
    :=
      let arg_str := concat ", " (map show_arg args) in
      concatStr ["("; arg_str; ")"].

  (* TODO: REALLY?!? *)
  Fixpoint zip {X Y} (xs : list X) (ys : list Y) : list (X * Y)
    := match xs, ys with
       | [], _ => []
       | _, [] => []
       | (x::xs), (y::ys) => (x, y) :: zip xs ys
       end.

  Definition show_definition (defn : definition typ (block typ * list (block typ))) : string
    :=
      let name  := defn.(df_prototype).(dc_name) in
      let ftype := defn.(df_prototype).(dc_type) in
      match ftype with
      | TYPE_Function ret_t args_t
        =>
        let args := zip defn.(df_args) args_t in
        let blocks :=
            match df_instrs defn with
            | (b, bs) => concat newline (map (show_block "    ") (b::bs))
            end in
        concatStr
          [ "define "; show ret_t; " @"; show name; show_arg_list args; " {"; newline
          ; blocks
          ; "}"; newline
          ]
      | _ => "Invalid type on function: " ++ show name
      end.

  Global Instance showDefinition: Show (definition typ (block typ * list (block typ))) :=
    {| show := show_definition |}.

  Definition show_tle (tle : toplevel_entity typ (block typ * list (block typ))) : string
    := match tle with
       | TLE_Definition defn => show_definition defn
       | _ => "todo: show_tle"
       end.

  Global Instance showTLE: Show (toplevel_entity typ (block typ * list (block typ))) :=
    {| show := show_tle |}.

  Global Instance showProg : Show (list (toplevel_entity typ (block typ * list (block typ)))) :=
    {| show tles := concat (newline ++ newline) (map show_tle tles) |}.

End ShowInstances.
