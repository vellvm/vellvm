Require Import Ceres.Ceres.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

From ExtLib.Structures Require Export
     Functor Applicative Monads.

Require Import ExtLib.Data.Monads.StateMonad.

From Vellvm Require Import LLVMAst Util AstLib TypeUtil CFG Show.
Require Import Integers Floats.

Require Import List.

Import ListNotations.
Import MonadNotation.
Import ApplicativeNotation.

From Coq Require Import
     ZArith List String Omega Bool.Bool.

Open Scope Z_scope.

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
      | EXP_Cstring s => s (* TODO, this is probably wrong *)
      | EXP_Undef => "undef"
      | OP_IBinop iop t v1 v2 =>
        show iop ++ " " ++ show t ++ " " ++ show_exp v1 ++ " " ++ show_exp v2
      | OP_ICmp cmp t v1 v2 =>
        show cmp ++ " " ++ show t ++ " " ++ show_exp v1 ++ " " ++ show_exp v2
      | OP_GetElementPtr t ptrval idxs =>
        "getelementptr"
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
  
  Fixpoint show_instr (i : instr typ) : string
    := match i with
       | INSTR_Comment s => "; " ++ s
       | INSTR_Op e => show e
       | INSTR_Load vol t ptr align =>
         "load " ++ show t ++ " " ++ show ptr ++ show_opt_prefix ", align " align
       | INSTR_Store vol tval ptr align =>
         "store " ++ show tval ++ " " ++ show ptr ++ show_opt_prefix ", align " align
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
         "br " ++ show te ++ ", label " ++ show b1 ++ ", label " ++ show b2
       | TERM_Br_1 b =>
         "br label " ++ show b
       | _ => "show_terminator todo"
       end.

  Global Instance showTerminator : Show (terminator typ)
    := {| show := show_terminator |}.

  Definition show_code (indent : string) (c : code typ) : string
    := concatStr (map (fun iid => indent ++ show_instr_id iid ++ newline) c).

  Global Instance showCode : Show (code typ)
    := {| show := show_code "    " |}.

  Definition show_block (indent : string) (b : block typ) : string
    :=
      let code   := show_code indent (blk_code b) in
      let term   := indent ++ show (snd (blk_term b)) ++ newline in
      show (blk_id b) ++ ":" ++ newline
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

  Definition show_definition (defn : definition typ (list (block typ))) : string
    :=
      let name  := defn.(df_prototype).(dc_name) in
      let ftype := defn.(df_prototype).(dc_type) in
      match ftype with
      | TYPE_Function ret_t args_t
        =>
        let args := zip defn.(df_args) args_t in
        let blocks := concat newline (map (show_block "    ") (df_instrs defn)) in
        concatStr
          [ "define "; show ret_t; " @"; show name; show_arg_list args; " {"; newline
          ; blocks
          ; "}"; newline
          ]
      | _ => "Invalid type on function: " ++ show name
      end.

  Global Instance showDefinition: Show (definition typ (list (block typ))) :=
    {| show := show_definition |}.

  Definition show_tle (tle : toplevel_entity typ (list (block typ))) : string
    := match tle with
       | TLE_Definition defn => show_definition defn
       | _ => "todo: show_tle"
       end.

  Global Instance showTLE: Show (toplevel_entity typ (list (block typ))) :=
    {| show := show_tle |}.

  Global Instance showProg : Show (list (toplevel_entity typ (list (block typ)))) :=
    {| show tles := concat (newline ++ newline) (map show_tle tles) |}.

End ShowInstances.

Section Helpers.
  Fixpoint max_nat_list (l : list nat) : nat :=
    match l with
    | [] => 0
    | x::rest => max x (max_nat_list rest)
    end.

  (* TODO: how big should lists be? *)
  Fixpoint sizeof_typ (t : typ) : nat :=
    match t with
    | TYPE_Pointer t            => S (sizeof_typ t)
    | TYPE_Array sz t           => S (sizeof_typ t)
    | TYPE_Function ret args    => max (sizeof_typ ret) (max_nat_list (map sizeof_typ args))
    | TYPE_Struct fields        => max_nat_list (map sizeof_typ fields)
    | TYPE_Packed_struct fields => max_nat_list (map sizeof_typ fields)
    | TYPE_Vector sz t          => S (sizeof_typ t)
    | _                         => 0
    end.

  (* TODO: Move these *)
  Fixpoint find_pred {A} (p : A -> bool) (l : list A) : option A
    := match l with
       | []   => None
       | x::xs =>
         if p x
         then Some x
         else find_pred p xs
       end.

  Fixpoint is_sized_type_h (t : typ) : bool
    := match t with
       | TYPE_I sz                 => true
       | TYPE_Pointer t            => true
       | TYPE_Void                 => false
       | TYPE_Half                 => true
       | TYPE_Float                => true
       | TYPE_Double               => true
       | TYPE_X86_fp80             => true
       | TYPE_Fp128                => true
       | TYPE_Ppc_fp128            => true
       | TYPE_Metadata             => true (* Is this right? *)
       | TYPE_X86_mmx              => true
       | TYPE_Array sz t           => is_sized_type_h t
       | TYPE_Function ret args    => false
       | TYPE_Struct fields        => true
       | TYPE_Packed_struct fields => true
       | TYPE_Opaque               => false
       | TYPE_Vector sz t          => is_sized_type_h t
       | TYPE_Identified id        => false (* Shouldn't happen *)
       end.

  (* Only works correctly if the type is well formed *)
  Definition is_sized_type (typ_ctx : list (ident * typ)) (t : typ) : bool
    := is_sized_type_h (normalize_type typ_ctx t).

  Definition is_int_type_h (t : typ) : bool
    := match t with
       | TYPE_I sz => true
       | _ => false
       end.

  (* Only works correctly if the type is well formed *)
  Definition is_int_type (typ_ctx : list (ident * typ)) (t : typ) : bool
    := is_int_type_h (normalize_type typ_ctx t).

  (* TODO: incomplete. Should typecheck *)
  Fixpoint well_formed_op (typ_ctx : list (ident * typ)) (op : exp typ) : bool :=
    match op with
    | OP_IBinop iop t v1 v2              => true
    | OP_ICmp cmp t v1 v2                => true
    | OP_FBinop fop fm t v1 v2           => true
    | OP_FCmp cmp t v1 v2                => true
    | OP_Conversion conv t_from v t_to   => true
    | OP_GetElementPtr t ptrval idxs     => true
    | OP_ExtractElement vec idx          => true
    | OP_InsertElement vec elt idx       => true
    | OP_ShuffleVector vec1 vec2 idxmask => true
    | OP_ExtractValue vec idxs           => true
    | OP_InsertValue vec elt idxs        => true
    | OP_Select cnd v1 v2                => true
    | OP_Freeze v                        => true
    | _                                  => false
    end.

  (*
  Fixpoint well_formed_instr (ctx : list (ident * typ)) (i : instr typ) : bool :=
    match i with
    | INSTR_Comment msg => true
    | INSTR_Op op => well_formed_op ctx op
    | INSTR_Call fn args => _
    | INSTR_Alloca t nb align => is_sized_typ ctx t (* The alignment may not be greater than 1 << 29. *)
    | INSTR_Load volatile t ptr align => _
    | INSTR_Store volatile val ptr align => _
    | INSTR_Fence => _
    | INSTR_AtomicCmpXchg => _
    | INSTR_AtomicRMW => _
    | INSTR_Unreachable => _
    | INSTR_VAArg => _
    | INSTR_LandingPad => _
    end.
   *)

  Definition genNatInt : G int
    := fmap (fun n => Int.repr (Z.of_nat n)) (arbitrary : G nat).

  Definition genPosInt : G int
    := fmap (fun n => Int.repr (Z.of_nat (S n))) (arbitrary : G nat).

  Definition genPosZ : G Z
    :=
      n <- (arbitrary : G nat);;
      ret (Z.of_nat n).
End Helpers.

Section GenerationState.
  Record GenState :=
    mkGenState
    { num_void : nat
    ; num_raw  : nat
    ; num_global : nat
    ; num_blocks : nat
    (* Types of values *)
    ; gen_ctx : list (ident * typ)
    (* Type aliases *)
    ; gen_typ_ctx : list (ident * typ)
    }.

  Definition init_GenState : GenState
    := {| num_void   := 0
        ; num_raw    := 0
        ; num_global := 0
        ; num_blocks := 0
        ; gen_ctx    := []
        ; gen_typ_ctx    := []
       |}.

  Definition increment_raw (gs : GenState) : GenState
    := {| num_void    := gs.(num_void)
        ; num_raw     := S gs.(num_raw)
        ; num_global  := gs.(num_global)
        ; num_blocks  := gs.(num_blocks)
        ; gen_ctx     := gs.(gen_ctx)
        ; gen_typ_ctx := gs.(gen_typ_ctx)
       |}.

  Definition increment_global (gs : GenState) : GenState
    := {| num_void    := gs.(num_void)
        ; num_raw     := gs.(num_raw)
        ; num_global  := S gs.(num_global)
        ; num_blocks  := gs.(num_blocks)
        ; gen_ctx     := gs.(gen_ctx)
        ; gen_typ_ctx := gs.(gen_typ_ctx)
       |}.

  Definition increment_void (gs : GenState) : GenState
    := {| num_void    := S gs.(num_void)
        ; num_raw     := gs.(num_raw)
        ; num_global  := gs.(num_global)
        ; num_blocks  := gs.(num_blocks)
        ; gen_ctx     := gs.(gen_ctx)
        ; gen_typ_ctx := gs.(gen_typ_ctx)
       |}.

  Definition increment_blocks (gs : GenState) : GenState
    := {| num_void    := gs.(num_void)
        ; num_raw     := gs.(num_raw)
        ; num_global  := gs.(num_global)
        ; num_blocks  := S gs.(num_blocks)
        ; gen_ctx     := gs.(gen_ctx)
        ; gen_typ_ctx := gs.(gen_typ_ctx)
       |}.

  Definition replace_ctx (ctx : list (ident * typ)) (gs : GenState) : GenState
    := {| num_void    := gs.(num_void)
        ; num_raw     := gs.(num_raw)
        ; num_global  := gs.(num_global)
        ; num_blocks  := gs.(num_blocks)
        ; gen_ctx     := ctx
        ; gen_typ_ctx := gs.(gen_typ_ctx)
       |}.

  Definition replace_typ_ctx (typ_ctx : list (ident * typ)) (gs : GenState) : GenState
    := {| num_void    := gs.(num_void)
        ; num_raw     := gs.(num_raw)
        ; num_global  := gs.(num_global)
        ; num_blocks  := gs.(num_blocks)
        ; gen_ctx     := gs.(gen_ctx)
        ; gen_typ_ctx := typ_ctx
       |}.

  Definition GenLLVM := stateT GenState G.

  Definition get_raw (gs : GenState) : nat
    := gs.(num_raw).

  Definition get_global (gs : GenState) : nat
    := gs.(num_global).

  Definition get_void (gs : GenState) : nat
    := gs.(num_void).

  Definition get_blocks (gs : GenState) : nat
    := gs.(num_blocks).

  Definition new_raw_id : GenLLVM raw_id
    := n <- gets get_raw;;
       modify increment_raw;;
       ret (Name ("v" ++ show n)).

  Definition new_global_id : GenLLVM raw_id
    := n <- gets get_global;;
       modify increment_global;;
       ret (Name ("g" ++ show n)).

  Definition new_void_id : GenLLVM instr_id
    := n <- gets get_void;;
       modify increment_void;;
       ret (IVoid (Z.of_nat n)).

  Definition new_block_id : GenLLVM block_id
    := n <- gets get_blocks;;
       modify increment_blocks;;
       ret (Name ("b" ++ show n)).

  Definition get_ctx : GenLLVM (list (ident * typ))
    := gets (fun gs => gs.(gen_ctx)).

  Definition get_typ_ctx : GenLLVM (list (ident * typ))
    := gets (fun gs => gs.(gen_typ_ctx)).

  Definition add_to_ctx (x : (ident * typ)) : GenLLVM  unit
    := ctx <- get_ctx;;
       let new_ctx := x :: ctx in
       modify (replace_ctx new_ctx);;
       ret tt.

  Definition add_to_typ_ctx (x : (ident * typ)) : GenLLVM  unit
    := ctx <- get_typ_ctx;;
       let new_ctx := x :: ctx in
       modify (replace_typ_ctx new_ctx);;
       ret tt.

  Definition append_to_ctx (vars : list (ident * typ)) : GenLLVM unit
    := ctx <- get_ctx;;
       let new_ctx := vars ++ ctx in
       modify (replace_ctx new_ctx);;
       ret tt.

  Definition append_to_typ_ctx (aliases : list (ident * typ)) : GenLLVM unit
    := ctx <- get_typ_ctx;;
       let new_ctx := aliases ++ ctx in
       modify (replace_typ_ctx new_ctx);;
       ret tt.

  Definition reset_ctx : GenLLVM unit
    := modify (replace_ctx []);; ret tt.

  Definition reset_typ_ctx : GenLLVM unit
    := modify (replace_typ_ctx []);; ret tt.

  Definition oneOf_LLVM {A} (gs : list (GenLLVM A)) : GenLLVM A
    := n <- lift (choose (0, List.length gs - 1)%nat);;
       nth n gs (lift failGen).

  Definition freq_LLVM {A} (gs : list (nat * GenLLVM A)) : GenLLVM A
    := mkStateT
         (fun st => freq_ failGen (fmap (fun '(n, g) => (n, runStateT g st)) gs)).

  Definition vectorOf_LLVM {A : Type} (k : nat) (g : GenLLVM A)
    : GenLLVM (list A) :=
    fold_right (fun m m' =>
                  x <- m;;
                  xs <- m';;
                  ret (x :: xs)) (ret []) (repeat g k).

  Definition sized_LLVM {A : Type} (gn : nat -> GenLLVM A) : GenLLVM A
    := mkStateT
         (fun st => sized (fun n => runStateT (gn n) st)).

  Definition resize_LLVM {A : Type} (sz : nat) (g : GenLLVM A) : GenLLVM A
    := mkStateT
         (fun st => resize sz (runStateT g st)).

  Definition listOf_LLVM {A : Type} (g : GenLLVM A) : GenLLVM (list A) :=
    sized_LLVM (fun n =>
                  k <- lift (choose (0, n)%nat);;
                  vectorOf_LLVM k g).

  Definition nonemptyListOf_LLVM
             {A : Type} (g : GenLLVM A) : GenLLVM (list A)
    := sized_LLVM (fun n =>
                     k <- lift (choose (1, n)%nat);;
                     vectorOf_LLVM k g).

  Definition run_GenLLVM {A} (g : GenLLVM A) : G A
    := fmap fst (runStateT g init_GenState).
End GenerationState.

Section TypGenerators.
  (* TODO: These currently don't generate pointer types either. *)

  (* Not sized in the QuickChick sense, sized in the LLVM sense. *)
  Definition gen_sized_typ_0 : GenLLVM typ :=
    aliases <- get_typ_ctx;;
    let sized_aliases := filter (fun '(i,t) => is_sized_type aliases t) aliases in
    let ident_gen :=
        (* Don't want to fail if there are no identifiers *)
        if (List.length sized_aliases =? 0)%nat
        then []
        else [ret TYPE_Identified <*> oneOf_LLVM (map (fun '(i,_) => ret i) sized_aliases)] in
    oneOf_LLVM
           (ident_gen ++
           (map ret
                [ TYPE_I 1
                ; TYPE_I 8
                ; TYPE_I 32
                ; TYPE_I 64
                (* TODO: Generate floats and stuff *)
                (* TODO: Could generate TYPE_Identified if we filter for sized types *)
                (* ; TYPE_Half *)
                (* ; TYPE_Double *)
                (* ; TYPE_X86_fp80 *)
                (* ; TYPE_Fp128 *)
                (* ; TYPE_Ppc_fp128 *)
                (* ; TYPE_Metadata *)
                (* ; TYPE_X86_mmx *)
                (* ; TYPE_Opaque *)
                ])).

  Program Fixpoint gen_sized_typ_size (sz : nat) {measure sz} : GenLLVM typ :=
    match sz with
    | O => gen_sized_typ_0
    | (S sz') =>
      oneOf_LLVM
        [ gen_sized_typ_0
        ; ret TYPE_Pointer <*> gen_sized_typ_size sz'
        (* Might want to restrict the size to something reasonable *)
        ; ret TYPE_Array <*> lift genPosZ <*> gen_sized_typ_size sz'
        ; ret TYPE_Vector <*> lift genPosZ <*> gen_sized_typ_size sz'
        ; let n := Nat.div sz 2 in
          ret TYPE_Function <*> gen_sized_typ_size n <*> listOf_LLVM (gen_sized_typ_size n)
        ; ret TYPE_Struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz')
        ; ret TYPE_Packed_struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz')
        ]
    end.
  Next Obligation.
    cbn.
    assert (0 <= 1)%nat by omega.
    pose proof Nat.divmod_spec sz' 1 0 0 H.
    cbn; destruct (Nat.divmod sz' 1 0 0).
    cbn; omega.
  Qed.
  Next Obligation.
    cbn.
    assert (0 <= 1)%nat by omega.
    pose proof Nat.divmod_spec sz' 1 0 0 H.
    cbn; destruct (Nat.divmod sz' 1 0 0).
    cbn; omega.
  Qed.

  Definition gen_sized_typ : GenLLVM typ
    := sized_LLVM (fun sz => gen_sized_typ_size sz).

  (* Generate a type of size 0 *)
  Definition gen_typ_0 : GenLLVM typ :=
    aliases <- get_typ_ctx;;
    let identified :=
        match aliases with
        | [] => []
        | _  => [(ret TYPE_Identified <*> oneOf_LLVM (map (fun '(i,_) => ret i) aliases))]
        end
    in
    oneOf_LLVM
          ((* identified ++ *)
           (map ret
                [ TYPE_I 1
                ; TYPE_I 8
                ; TYPE_I 32
                ; TYPE_I 64
                ; TYPE_Void
                (* TODO: Generate floats and stuff *)
                (* ; TYPE_Half *)
                (* ; TYPE_Double *)
                (* ; TYPE_X86_fp80 *)
                (* ; TYPE_Fp128 *)
                (* ; TYPE_Ppc_fp128 *)
                (* ; TYPE_Metadata *)
                (* ; TYPE_X86_mmx *)
                (* ; TYPE_Opaque *)
                ])).

  (* TODO: This should probably be mutually recursive with
     gen_sized_typ since pointers of any type are considered sized *)
  Program Fixpoint gen_typ_size (sz : nat) {measure sz} : GenLLVM typ :=
    match sz with
    | 0%nat => gen_typ_0
    | (S sz') => oneOf_LLVM
                      [ gen_typ_0
                      (* Might want to restrict the size to something reasonable *)
                      (* TODO: Make sure length of Array >= 0, and length of vector >= 1 *)
                      ; ret TYPE_Array <*> lift genPosZ <*> gen_sized_typ_size sz'
                      ; ret TYPE_Vector <*> lift genPosZ <*> gen_sized_typ_size sz'
                      ; let n := Nat.div sz 2 in
                        ret TYPE_Function <*> gen_typ_size n <*> listOf_LLVM (gen_sized_typ_size n)
                      ; ret TYPE_Struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz')
                      ; ret TYPE_Packed_struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz')
                      ]
    end.
  Next Obligation.
    cbn.
    assert (0 <= 1)%nat by omega.
    pose proof Nat.divmod_spec sz' 1 0 0 H.
    cbn; destruct (Nat.divmod sz' 1 0 0).
    cbn; omega.
  Qed.

  Definition gen_typ : GenLLVM typ
    := sized_LLVM (fun sz => gen_typ_size sz).

  Definition gen_typ_non_void_0 : GenLLVM typ :=
    aliases <- get_typ_ctx;;
    let identified :=
        match aliases with
        | [] => []
        | _  => [(ret TYPE_Identified <*> oneOf_LLVM (map (fun '(i,_) => ret i) aliases))]
        end
    in
    oneOf_LLVM
          (identified ++
           (map ret
                [ TYPE_I 1
                ; TYPE_I 8
                ; TYPE_I 32
                ; TYPE_I 64
                (* TODO: Generate floats and stuff *)
                (* ; TYPE_Half *)
                (* ; TYPE_Double *)
                (* ; TYPE_X86_fp80 *)
                (* ; TYPE_Fp128 *)
                (* ; TYPE_Ppc_fp128 *)
                (* ; TYPE_Metadata *)
                (* ; TYPE_X86_mmx *)
                (* ; TYPE_Opaque *)
                ])).

  Program Fixpoint gen_typ_non_void_size (sz : nat) {measure sz} : GenLLVM typ :=
    match sz with
    | 0%nat => gen_typ_non_void_0
    | (S sz') => oneOf_LLVM
                      [ gen_typ_non_void_0
                      (* Might want to restrict the size to something reasonable *)
                      (* TODO: Make sure length of Array >= 0, and length of vector >= 1 *)
                      ; ret TYPE_Array <*> lift genPosZ <*> gen_sized_typ_size sz'
                      ; ret TYPE_Vector <*> lift genPosZ <*> gen_sized_typ_size sz'
                      ; let n := Nat.div sz 2 in
                        ret TYPE_Function <*> gen_typ_size n <*> listOf_LLVM (gen_sized_typ_size n)
                      ; ret TYPE_Struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz')
                      ; ret TYPE_Packed_struct <*> nonemptyListOf_LLVM (gen_sized_typ_size sz')
                      ]
    end.

  (* TODO: look up identifiers *)
  (* Types for operation expressions *)
  Definition gen_op_typ : GenLLVM typ :=
    oneOf_LLVM
           (map ret
                [ TYPE_I 1
                ; TYPE_I 8
                ; TYPE_I 32
                ; TYPE_I 64
                (* TODO: Generate floats and stuff *)
                (* ; TYPE_Half *)
                (* ; TYPE_Double *)
                (* ; TYPE_X86_fp80 *)
                (* ; TYPE_Fp128 *)
                (* ; TYPE_Ppc_fp128 *)
                (* ; TYPE_Metadata *)
                (* ; TYPE_X86_mmx *)
                (* ; TYPE_Opaque *)
                ]).

  (* TODO: look up identifiers *)
  Definition gen_int_typ : GenLLVM typ :=
    oneOf_LLVM
           (map ret
                [ TYPE_I 1
                ; TYPE_I 8
                ; TYPE_I 32
                ; TYPE_I 64
                ]).
End TypGenerators.

Section ExpGenerators.
  (* nuw / nsw make poison values likely *)
  Definition gen_ibinop : G ibinop :=
    oneOf_ failGen
           [ ret LLVMAst.Add <*> ret false <*> ret false
           ; ret Sub <*> ret false <*> ret false
           ; ret Mul <*> ret false <*> ret false
           ; ret Shl <*> ret false <*> ret false
           ; ret UDiv <*> ret false
           ; ret SDiv <*> ret false
           ; ret LShr <*> ret false
           ; ret AShr <*> ret false
           ; ret URem
           ; ret SRem
           ; ret And
           ; ret Or
           ; ret Xor
           ].

  Definition gen_icmp : G icmp :=
    oneOf_ failGen
           (map ret
                [ Eq; Ne; Ugt; Uge; Ult; Ule; Sgt; Sge; Slt; Sle]).


  (* TODO: Move. Also, do I really have to define this? *)
  Fixpoint zipWith {A B C} (f : A -> B -> C) (xs : list A) (ys : list B) : list C
    := match xs, ys with
       | [], _        => []
       | _, []        => []
       | a::xs', b::ys' => f a b :: zipWith f xs' ys'
       end.

  (* TODO: Move this*)
  (* This only returns what you expect on normalized typs *)
  (* TODO: I don't think this does the right thing for pointers to
           identified types... It should be conservative and say that
           the types are *not* equal always, though.
   *)
  Program Fixpoint normalized_typ_eq (a : typ) (b : typ) {measure (sizeof_typ a)} : bool
    := match a with
       | TYPE_I sz =>
         match b with
         | TYPE_I sz' => if Z.eq_dec sz sz' then true else false
         | _ => false
         end
       | TYPE_Pointer t =>
         match b with
         | TYPE_Pointer t' => normalized_typ_eq t t'
         | _ => false
         end
       | TYPE_Void =>
         match b with
         | TYPE_Void => true
         | _ => false
         end
       | TYPE_Half =>
         match b with
         | TYPE_Half => true
         | _ => false
         end
       | TYPE_Float =>
         match b with
         | TYPE_Float => true
         | _ => false
         end
       | TYPE_Double =>
         match b with
         | TYPE_Double => true
         | _ => false
         end
       | TYPE_X86_fp80 =>
         match b with
         | TYPE_X86_fp80 => true
         | _ => false
         end
       | TYPE_Fp128 =>
         match b with
         | TYPE_Fp128 => true
         | _ => false
         end
       | TYPE_Ppc_fp128 =>
         match b with
         | TYPE_Ppc_fp128 => true
         | _ => false
         end
       | TYPE_Metadata =>
         match b with
         | TYPE_Metadata => true
         | _ => false
         end
       | TYPE_X86_mmx =>
         match b with
         | TYPE_X86_mmx => true
         | _ => false
         end
       | TYPE_Array sz t =>
         match b with
         | TYPE_Array sz' t' =>
           if Z.eq_dec sz sz'
           then normalized_typ_eq t t'
           else false
         | _ => false
         end
       | TYPE_Function ret args =>
         match b with
         | TYPE_Function ret' args' =>
           normalized_typ_eq ret ret' && forallb id (zipWith (fun a b => @normalized_typ_eq a b _) args args')
         | _ => false
         end
       | TYPE_Struct fields =>
         match b with
         | TYPE_Struct fields' => forallb id (zipWith (fun a b => @normalized_typ_eq a b _) fields fields')
         | _ => false
         end
       | TYPE_Packed_struct fields =>
         match b with
         | TYPE_Packed_struct fields' => forallb id (zipWith (fun a b => @normalized_typ_eq a b _) fields fields')
         | _ => false
         end
       | TYPE_Opaque =>
         match b with
         | TYPE_Opaque => false (* TODO: Unsure if this should compare equal *)
         | _ => false
         end
       | TYPE_Vector sz t =>
         match b with
         | TYPE_Vector sz' t' =>
           if Z.eq_dec sz sz'
           then normalized_typ_eq t t'
           else false
         | _ => false
         end
       | TYPE_Identified id => false
       end.
  Admit Obligations.

  (* Generate an expression of a given type *)
  (* Context should probably not have duplicate ids *)
  (* May want to decrease size more for arrays and vectors *)
  (* TODO: Need a restricted version of the type generator for this? *)
  (* TODO: look up named types from the context *)
  (* TODO: generate conversions? *)
  Unset Guard Checking.

  (* TODO: Move this *)
  Fixpoint replicateM {M : Type -> Type} {A} `{Monad M} (n : nat) (ma : M A) : M (list A)
    := match n with
       | O    => a <- ma;; ret [a]
       | S n' => a <- ma;; rest <- replicateM n' ma;; ret (a :: rest)
       end.

  Definition filter_type (ty : typ) (ctx : list (ident * typ)) : list (ident * typ)
    := filter (fun '(i, t) => normalized_typ_eq (normalize_type ctx ty) (normalize_type ctx t)) ctx.
  
  (* TODO: should make it much more likely to pick an identifier for
           better test cases *)
  Fixpoint gen_exp_size (sz : nat) (t : typ) {struct t} : GenLLVM (exp typ) :=
    match sz with
    | 0%nat =>
      ctx <- get_ctx;;
      let ts := filter_type t ctx in
      let gen_idents :=
          match ts with
          | [] => []
          | _ => [(16%nat, fmap (fun '(i,_) => EXP_Ident i) (oneOf_LLVM (fmap ret ts)))]
          end in
      let gen_size_0 :=
          match t with
          | TYPE_I n                  => ret EXP_Integer <*> lift (arbitrary : G Z) (* TODO: should the integer be forced to be in bounds? *)
          | TYPE_Pointer t            => lift failGen (* Only pointer type expressions might be conversions? Maybe GEP? *)
          | TYPE_Void                 => lift failGen (* There should be no expressions of type void *)
          | TYPE_Function ret args    => lift failGen (* No expressions of function type *)
          | TYPE_Opaque               => lift failGen (* TODO: not sure what these should be... *)
          | TYPE_Array n t            => lift failGen
          | TYPE_Vector sz t          => lift failGen
          | TYPE_Struct fields        => lift failGen
          | TYPE_Packed_struct fields => lift failGen
          | TYPE_Identified id        =>
            ctx <- get_ctx;;
            match find_pred (fun '(i,t) => if Ident.eq_dec id i then true else false) ctx with
            | None => lift failGen
            | Some (i,t) => gen_exp_size sz t
            end
          (* Not generating these types for now *)
          | TYPE_Half                 => lift failGen
          | TYPE_Float                => lift failGen
          | TYPE_Double               => lift failGen
          | TYPE_X86_fp80             => lift failGen
          | TYPE_Fp128                => lift failGen
          | TYPE_Ppc_fp128            => lift failGen
          | TYPE_Metadata             => lift failGen
          | TYPE_X86_mmx              => lift failGen
          end in
      freq_LLVM
        (gen_idents ++ [(1%nat, gen_size_0)])
    | (S sz') =>
      let gens :=
          match t with
          | TYPE_I isz =>
            (* TODO: If I1 also allow ICmp and FCmp *)
            [let n := Nat.div sz 2 in
             ret OP_IBinop <*> lift gen_ibinop <*> ret t <*> gen_exp_size n t <*> gen_exp_size n t]
          | TYPE_Array n t =>
            [es <- vectorOf_LLVM (Z.to_nat n) (gen_exp_size sz' t);;
             ret (EXP_Array (map (fun e => (t, e)) es))]
          | TYPE_Vector n t =>
            [es <- vectorOf_LLVM (Z.to_nat n) (gen_exp_size sz' t);;
             ret (EXP_Array (map (fun e => (t, e)) es))]
          | TYPE_Struct fields =>
            (* Should we divide size evenly amongst components of struct? *)
            [tes <- map_monad (fun t => e <- gen_exp_size sz' t;; ret (t, e)) fields;;
             ret (EXP_Struct tes)]
          | TYPE_Packed_struct fields =>
            (* Should we divide size evenly amongst components of struct? *)
            [tes <- map_monad (fun t => e <- gen_exp_size sz' t;; ret (t, e)) fields;;
             ret (EXP_Packed_struct tes)]
          | TYPE_Pointer t         => [lift failGen] (* GEP? *)
          | TYPE_Void              => [lift failGen] (* No void type expressions *)
          | TYPE_Function ret args => [lift failGen] (* These shouldn't exist, I think *)
          | TYPE_Opaque            => [lift failGen] (* TODO: not sure what these should be... *)
          | TYPE_Half              => [lift failGen]
          | TYPE_Float             => [lift failGen]
          | TYPE_Double            => [lift failGen]
          | TYPE_X86_fp80          => [lift failGen]
          | TYPE_Fp128             => [lift failGen]
          | TYPE_Ppc_fp128         => [lift failGen]
          | TYPE_Metadata          => [lift failGen]
          | TYPE_X86_mmx           => [lift failGen]
          | TYPE_Identified id     =>
            [ctx <- get_ctx;;
             match find_pred (fun '(i,t) => if Ident.eq_dec id i then true else false) ctx with
             | None => lift failGen
             | Some (i,t) => gen_exp_size sz t
             end]
          end
      in
      (* short-circuit to size 0 *)
      oneOf_LLVM (gen_exp_size 0 t :: gens)
    end.

  Definition gen_exp (t : typ) : GenLLVM (exp typ)
    := sized_LLVM (fun sz => gen_exp_size sz t).

  Definition gen_texp : GenLLVM (texp typ)
    := t <- gen_typ;;
       e <- gen_exp t;;
       ret (t, e).

  Definition gen_sized_texp : GenLLVM (texp typ)
    := t <- gen_sized_typ;;
       e <- gen_exp t;;
       ret (t, e).

  Definition gen_op (t : typ) : GenLLVM (exp typ)
    := sized_LLVM
         (fun sz =>
            match t with
            | TYPE_I isz =>
              (* TODO: If I1 also allow ICmp and FCmp *)
              let n := Nat.div sz 2 in
              ret OP_IBinop <*> lift gen_ibinop <*> ret t <*> gen_exp_size n t <*> gen_exp_size n t
            | _ => lift failGen
            end).

  Definition gen_int_texp : GenLLVM (texp typ)
    := t <- gen_int_typ;;
       e <- gen_exp t;;
       ret (t, e).

End ExpGenerators.

Section InstrGenerators.

  (* TODO: move this *)
  Definition genInt : G int
    := fmap Int.repr (arbitrary : G Z).

  Instance GenInt : Gen int
    := Build_Gen int genInt.

  (* TODO: move this. Also give a less confusing name because genOption is a thing? *)
  Definition gen_option {A} (g : G A) : G (option A)
    := freq_ failGen [(1%nat, ret None); (7%nat, liftM Some g)].

  (* TODO: move these *)
  Definition opt_add_state {A} {ST} (st : ST) (o : option (A * ST)) : (option A * ST)
    := match o with
       | None => (None, st)
       | (Some (a, st')) => (Some a, st')
       end.

  Definition gen_opt_LLVM {A} (g : GenLLVM A) : GenLLVM (option A)
    := mkStateT
         (fun st =>
            opt <- gen_option (runStateT g st);;
            ret (opt_add_state st opt)).

  Definition gen_load : GenLLVM (typ * instr typ)
    := t   <- gen_sized_typ;;
       let pt := TYPE_Pointer t in
       vol <- lift (arbitrary : G bool);;
       ptr <- gen_exp pt;;
       align <- lift arbitrary;;
       ret (t, INSTR_Load vol t (pt, ptr) align).

  Definition gen_store : GenLLVM (typ * instr typ)
    := vol   <- lift arbitrary;;
       align <- lift arbitrary;;

       val <- gen_sized_texp;;
       let '(t, e) := val in

       let pt := TYPE_Pointer t in
       pexp <- gen_exp pt;;
       let ptr := (pt, pexp) in

       ret (TYPE_Void, INSTR_Store vol val ptr align).


  (* Generate an instruction, as well as its type...

     The type is sometimes void for instructions that don't really
     compute a value, like void function calls, stores, etc.
   *)
  Definition gen_instr : GenLLVM (typ * instr typ) :=
    oneOf_LLVM
      [ t <- gen_op_typ;; i <- ret INSTR_Op <*> gen_op t;; ret (t, i)
      ; t <- gen_sized_typ;;
        num_elems <- gen_opt_LLVM gen_int_texp;;
        align <- lift arbitrary;;
        ret (TYPE_Pointer t, INSTR_Alloca t num_elems align)
      (* TODO: Generate calls *)
      ; gen_load
      ; gen_store
      (* TODO: Generate atomic operations and other instructions *)
      ].

  (* TODO: Generate instructions with ids *)
  (* Make sure we can add these new ids to the context! *)

  (* TODO: want to generate phi nodes, which might be a bit
  complicated because we need to know that an id that occurs in a
  later block is in context *)

  (* Generate a block of code, spitting out a new context. *)
  Definition gen_instr_id : GenLLVM (instr_id * instr typ)
    := '(t, instr) <- gen_instr;;
       match t with
       | TYPE_Void =>
         vid <- new_void_id;;
         ret (vid, instr)
       | _ =>
         i <- new_raw_id;;
         add_to_ctx (ID_Local i, t);;
         ret (IId i, instr)
       end.

  Fixpoint gen_code_length (n : nat) : GenLLVM (code typ)
    := match n with
       | O => ret []
       | S n' =>
         instr <- gen_instr_id;;
         rest  <- gen_code_length n';;
         ret (instr :: rest)
       end.

  Definition gen_code : GenLLVM (code typ)
    := n <- lift arbitrary;;
       gen_code_length n.

  (* Returns a terminator and a list of new blocks that it reaches *)
  (* Need to make returns more likely than branches so we don't get an
     endless tree of blocks *)
  Fixpoint gen_terminator_sz
             (sz : nat) (t : typ) {struct t} : GenLLVM (terminator typ * list (block typ))
    :=
      ctx <- get_ctx;;
      match sz with
       | 0%nat =>
         (* Only returns allowed *)
         match (normalize_type ctx t) with
         | TYPE_Void => ret (TERM_Ret_void, [])
         | _ =>
           e <- gen_exp t;;
           ret (TERM_Ret (t, e), [])
         end
       | S sz' =>
         (* Need to lift oneOf to GenLLVM ...*)
         freq_LLVM
           [ (6%nat, gen_terminator_sz 0 t)
           ; (min sz' 6%nat, '(b, bs) <- gen_blocks_sz sz' t;; ret (TERM_Br_1 (blk_id b), bs))
           ; (min sz' 6%nat, ctx <- get_ctx;;
                   c <- gen_exp (TYPE_I 1);;
                   '(b1, bs1) <- gen_blocks_sz sz' t;;

                   (* Restore context so blocks in second branch don't refer
                      to variables from the first branch. *)
                   modify (replace_ctx ctx);;
                   '(b2, bs2) <- gen_blocks_sz sz' t;;

                   ret (TERM_Br (TYPE_I 1, c) (blk_id b1) (blk_id b2), bs1 ++ bs2))
           ]
       end
  with gen_blocks_sz (sz : nat) (t : typ) {struct t} : GenLLVM (block typ * list (block typ))
         :=
           bid <- new_block_id;;
           code <- gen_code;;
           '(term, bs) <- gen_terminator_sz (sz - 1) t;;
           i <- new_raw_id;;
           let b := {| blk_id   := bid
                     ; blk_phis := []
                     ; blk_code := code
                     ; blk_term := (IId i, term)
                     ; blk_comments := None
                    |} in
           ret (b, b :: bs).

  Definition gen_blocks (t : typ) : GenLLVM (list (block typ))
    := sized_LLVM (fun n => fmap snd (gen_blocks_sz n t)).

  (* Don't want to generate CFGs, actually. Want to generated TLEs *)
  Definition gen_definition (name : global_id) (ret_t : typ) (args : list (local_id * typ)) : GenLLVM (definition typ (list (block typ)))
    :=
      ctx <- get_ctx;;
      (* Add arguments to context *)
      let args_ctx := map (fun '(i, t) => (ID_Local i, t)) args in
      append_to_ctx args_ctx;;

      bs <- gen_blocks ret_t;;

      let args_t := map snd args in
      let f_type := TYPE_Function ret_t args_t in
      let prototype :=
          mk_declaration name f_type
                         ([], [])
                         None None None None
                         []
                         None None None
      in
      (* Reset context *)
      modify (replace_ctx ((ID_Global name, f_type) :: ctx));;
      ret (mk_definition (list (block typ)) prototype (map fst args) bs).

  Definition gen_new_definition (ret_t : typ) (args : list (local_id * typ)) : GenLLVM (definition typ (list (block typ)))
    :=
      name <- new_global_id;;
      gen_definition name ret_t args.

  Definition gen_main : GenLLVM (definition typ (list (block typ)))
    := gen_definition (Name "main") (TYPE_I 8) [].

  Definition gen_main_tle : GenLLVM (toplevel_entity typ (list (block typ)))
    := ret TLE_Definition <*> gen_main.

  Definition gen_llvm :GenLLVM (list (toplevel_entity typ (list (block typ))))
    := fmap ret gen_main_tle.

End InstrGenerators.
