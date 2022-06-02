(** 
    Show instances for Vellvm. These serialize Vellvm ASTs into the
    standard format for .ll files. The result of show on a Vellvm
    program should give you a string that can be read by clang.
*)

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Eqv.

From Vellvm Require Import LLVMAst Util AstLib Syntax.CFG DynamicTypes.

Require Import Integers Floats.

Require Import List.

Import ListNotations.
Import MonadNotation.

From Coq Require Import
     ZArith List String Lia Bool.Bool Hexadecimal Numbers.HexadecimalString Numbers.HexadecimalZ.

From QuickChick Require Import Show.
(* Import QcDefaultNotation. Open Scope qc_scope. *)
Set Warnings "-extraction-opaque-accessed,-extraction".


(*  ------------------------------------------------------------------------- *)
(* SAZ: this function was gotten from QuickChick Test.v, but really doesn't belong there. 
   TODO: Move somewhere saner
*)
Fixpoint concatStr (l : list string) : string :=
  match l with
    | nil => ""
    | (h :: t) => h ++ concatStr t
  end.
(*  ------------------------------------------------------------------------- *)


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
    | TYPE_IPTR                 => "iptr"
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

  Definition show_dtyp (t : dtyp) : string
    := match t with
    | DTYPE_I sz                 => "Integer" ++ (show sz)
    | DTYPE_IPTR                 => "iptr"
    | DTYPE_Pointer              => "Pointer"
    | DTYPE_Void                 => "Void"
    | DTYPE_Half                 => "Half"
    | DTYPE_Float                => "Float"
    | DTYPE_Double               => "Double"
    | DTYPE_X86_fp80             => "x86 fp80"
    | DTYPE_Fp128                => "Fp128"
    | DTYPE_Ppc_fp128            => "Ppc_fp128"
    | DTYPE_Metadata             => "Metadata"
    | DTYPE_X86_mmx              => "X86_mmx"
    | DTYPE_Array sz t           => "Array"
    | DTYPE_Struct fields        => "Struct"
    | DTYPE_Packed_struct fields => "Packed struct"
    | DTYPE_Opaque               => "Opaque"
    | DTYPE_Vector sz t          => "Vector"
    end.

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

  Definition show_fbinop (fop : fbinop) : string
    := match fop with
       | FAdd => "fadd"
       | FSub => "fsub"
       | FMul => "fmul"
       | FDiv => "fdiv"
       | FRem => "frem"
       end.

  Global Instance showFBinop : Show fbinop
    := {| show := show_fbinop |}.
  
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

  Definition show_fcmp (cmp: fcmp) : string
    := match cmp with 
      |FFalse => "ffalse"
      |FOeq => "foeq"
      |FOgt => "fogt"
      |FOge => "foge"
      |FOlt => "folt"
      |FOle => "fole"
      |FOne => "fone"
      |FOrd => "ford"
      |FUno => "funo"
      |FUeq => "fueq"
      |FUgt => "fugt"
      |FUge => "fuge"
      |FUlt => "fult"
      |FUle => "fule"
      |FUne => "fune"
      |FTrue => "ftrue"
    end.
  Global Instance showFCmp : Show fcmp 
  := {| show := show_fcmp|}.

  Definition double_to_hex_string (f : float) : string
    := "0x" ++ NilEmpty.string_of_uint (N.to_hex_uint (Z.to_N (Int64.unsigned (Float.to_bits f)))).

  Definition float_to_hex_string (f : float32) : string
    := double_to_hex_string (Float32.to_double f).

  Global Instance showFloat : Show float
    := {| show := double_to_hex_string |}.

  Global Instance showFloat32 : Show float32
    := {| show := float_to_hex_string |}.

  Definition show_int (x : Integers.Int.int) : string
    := show (Int.unsigned x).
  
  Global Instance Show_Int : Show Integers.Int.int
  := {| show := show_int|}.

  Definition show_fast_math (fm : fast_math) : string
    := match fm with
       | Nnan => "nnan"
       | Ninf => "ninf"
       | Nsz => "nsz"
       | Arcp => "arcp"
       | Fast => "fast"
       end.

  Global Instance showFastMatch : Show fast_math
    := {| show := show_fast_math |}.
  Definition show_conversion_type (ct : conversion_type) : string
    := match ct with
       | Trunc => "trunc"
       | Zext => "zext"
       | Sext => "sext"
       | Fptrunc => "fptrunc"
       | Fpext => "fpext"
       | Uitofp => "uitofp"
       | Sitofp => "sitofp"
       | Fptoui => "fptoui"
       | Fptosi => "fptosi"
       | Inttoptr => "inttoptr"
       | Ptrtoint => "ptrtoint"
       | Bitcast => "bitcast"
       end.
  Global Instance ShowConversionType : Show conversion_type
    := {| show := show_conversion_type |}.
  Fixpoint show_exp (v : exp typ) :=
      match v with
      | EXP_Ident id => show id
      | EXP_Integer x => show x
      | EXP_Float f => show f
      | EXP_Double f => show f
      | EXP_Bool b => show b
      | EXP_Null => "null"
      | EXP_Zero_initializer => "zero initializer"
      | EXP_Cstring s => "unimplemented cstring" (* TODO, this is wrong *)
      | EXP_Undef => "undef"
      | EXP_Struct fields => "{"  ++ concat ", " (map (fun '(ty,ex) => show ty ++ " " ++ show_exp ex) fields) ++ "}"
      | EXP_Packed_struct fields => "<{"  ++ concat ", " (map (fun '(ty,ex) => show ty ++ " " ++ show_exp ex) fields) ++ "}>"
      | EXP_Array elts => "["  ++ concat ", " (map (fun '(ty,ex) => show ty ++ " " ++ show_exp ex) elts) ++ "]"
      | EXP_Vector elts => "<"  ++ concat ", " (map (fun '(ty,ex) => show ty ++ " " ++ show_exp ex) elts) ++ ">"
      | OP_IBinop iop t v1 v2 =>
        show iop ++ " " ++ show t ++ " " ++ show_exp v1 ++ ", " ++ show_exp v2
      | OP_FBinop fop fmath t v1 v2 =>
          let fmath_string :=
            match fmath with
            | nil => " "
            | _ =>  " " ++ concat " " (map (fun x => show x) fmath) ++  " "
            end in              
         show fop ++ fmath_string ++ show t ++ " " ++ show_exp v1 ++ ", " ++ show_exp v2
      | OP_ICmp cmp t v1 v2
      | OP_FCmp cmp t v1 v2 =>
          "icmp " ++ show cmp ++ " " ++ show t ++ " " ++ show_exp v1 ++ ", " ++ show_exp v2
      | OP_Conversion conv t_from v t_to => show conv ++ " " ++ show t_from ++ " " ++ show_exp v ++ " to " ++ show t_to
      | OP_GetElementPtr t ptrval idxs =>
      let (tptr, exp) := ptrval in
      "getelementptr " ++ show t ++ ", " ++ show tptr ++ " " ++ show_exp exp ++ fold_left (fun str '(ty, ex) => str ++ ", " ++ show ty ++ " "++ show_exp ex) idxs ""
      | OP_ExtractValue vec idxs =>
      let (tptr, exp) := vec in
      "extractvalue " ++ show tptr ++ " " ++ show_exp exp ++ ", " ++ concat ", " (map (fun x => show x) idxs)
      | OP_ExtractElement vec idx =>
      let (tptr, exp) := vec in 
      let (tidx, iexp) := idx in
      "extractelement " ++ show tptr ++ " " ++ show_exp exp ++ ", " ++ show tidx ++ " " ++ show_exp iexp
      | OP_InsertElement vec elt idx =>
      let (tptr, exp) := vec in
      let (telt, eexp) := elt in
      let (tidx, iexp) := idx in
      "insertelement " ++ show tptr ++ " " ++ show_exp exp ++ ", " ++ show telt ++ " " ++ show_exp eexp ++ ", " ++ show tidx ++ " " ++ show_exp iexp
      | OP_InsertValue vec elt idxs =>
      let (tptr, exp) := vec in
      let (telt, eexp) := elt in 
      "insertvalue " ++ show tptr ++ " " ++ show_exp exp ++ ", " ++ show telt ++ " " ++ show_exp eexp ++ ", " ++ concat ", " (map (fun x => show x) idxs)
      | OP_Select (tc, cnd) (t1, v1) (t2, v2) =>
          "select " ++ show tc ++ " " ++ show_exp cnd ++ ", " ++ show t1 ++ " " ++ show_exp v1  ++ ", " ++ show t2 ++ " " ++ show_exp v2
      | OP_Freeze (ty, ex) => "freeze " ++ show ty ++ " " ++ show_exp ex
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
    := fold_left (fun acc s => if StringOrdFacts.eqb "" acc then s else acc ++ sep ++ s) l "".

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

  Definition show_typ_instr (typ_instr: typ * instr typ) : string :=
    let (t, i) := typ_instr in
    "(" ++ (show t) ++ ", " ++ (show i) ++ ")".

  Global Instance showTypInstr: Show (typ * instr typ) :=
    {|
    show := show_typ_instr
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
