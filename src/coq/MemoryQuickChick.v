Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Require Import List ZArith.
Import ListNotations.
Require Import String.

Require Import compcert.lib.Integers.
Require Import Vellvm.Ollvm_ast.
Require Import Vellvm.StepSemantics.
Require Import Vellvm.Memory.
Require Import Vellvm.CFG.

Require Import Vellvm.OllvmQuickChick.
Require Import Vellvm.ImpQuickChick.

Open Scope nat.

Instance gen_addr : GenSized A.addr.
Proof.
  auto with typeclass_instances.
Defined.

Instance show_addr : Show A.addr.
Proof. 
  auto with typeclass_instances.
Defined.

Derive Arbitrary for instr_id.
Derive Show for instr_id.

Instance gen_bool : Gen bool :=
  {| arbitrary := oneOf [returnGen true; returnGen false] |}.

Instance show_bool : Show bool :=
  {| show := fun (b : bool) => if b then "true" else "false" |}.

Instance gen_i1 : Gen int1 :=
  {| arbitrary :=
       bindGen arbitrary (fun (b : bool) =>
                            if b then returnGen (Int1.one)
                            else returnGen (Int1.zero))
  |}.

Instance shrink_i1 : Shrink int1 :=
  {| shrink x := [] |}.

Instance show_i1 : Show int1 := {| show n := show_int (Int1.signed n) |}.

Instance gen_small_nonneg_i32 : GenSized int32 :=
  {| arbitrarySized n :=
       let n' := if Nat.leb n 10 then n else 10 in
       let genZ := (let z := Z.of_nat n' in choose (0, z)%Z) in
       bindGen genZ (fun z => returnGen (Int32.repr z))
  |}.

Instance shrink_i32 : Shrink int32 :=
  {| shrink x := [Int32.zero; Int32.one; x] |}.

Instance show_i32 : Show int32 := {| show n := show_int (Int32.signed n) |}.

Existing Instance gen_small_nonneg_i64.

Fixpoint gen_dvalue (n : nat) : G dvalue :=
  let g_expr := freq [(5, liftGen VALUE_Ident arbitrary);
                        (5, liftGen VALUE_Integer arbitrary)
                        (* (5, liftGen VALUE_Float arbitrary);
                        (5, liftGen VALUE_Bool arbitrary);
                        (5, returnGen VALUE_Null);
                        (3, returnGen VALUE_Zero_initializer);
                        (5, liftGen VALUE_Cstring arbitrary);
                        (1, returnGen VALUE_None);
                        (1, returnGen VALUE_Undef) *)] in
  let g_base := freq [(5, liftGen DVALUE_CodePointer arbitrary);
                        (5, liftGen DVALUE_Addr arbitrary);
                        (5, liftGen DVALUE_I1 arbitrary);
                        (5, liftGen DVALUE_I32 (arbitrarySized n));
                        (5, liftGen DVALUE_I64 (arbitrarySized n));
                        (0, returnGen DVALUE_Poison)
                     ] in 
  match n with
  | 0 => freq [(5, liftGen DV g_expr); (5, g_base)]
  | S n' =>
    let next_g :=
        freq [(* (5, liftGen VALUE_Struct (listOf (liftGen2 pair arbitrary (gen_dvalue n')))); *)
                (5, liftGen4 OP_IBinop arbitrary arbitrary (gen_dvalue n') (gen_dvalue n'));
                (5, liftGen4 OP_ICmp arbitrary arbitrary (gen_dvalue n') (gen_dvalue n'));
                (5, liftGen4 OP_Conversion arbitrary arbitrary (gen_dvalue n') arbitrary)
                (*
                (5, liftGen3 OP_GetElementPtr
                             arbitrary
                             (liftGen2 pair arbitrary (gen_dvalue n'))
                             (listOf (liftGen2 pair arbitrary (gen_dvalue n'))));
                (5, liftGen2 OP_ExtractElement
                             (liftGen2 pair arbitrary (gen_dvalue n'))
                             (liftGen2 pair arbitrary (gen_dvalue n')));
                (5, liftGen3 OP_InsertElement
                             (liftGen2 pair arbitrary (gen_dvalue n'))
                             (liftGen2 pair arbitrary (gen_dvalue n'))
                             (liftGen2 pair arbitrary (gen_dvalue n')));
                (2, liftGen3 OP_ShuffleVector
                             (liftGen2 pair arbitrary (gen_dvalue n'))
                             (liftGen2 pair arbitrary (gen_dvalue n'))
                             (liftGen2 pair arbitrary (gen_dvalue n')));
                (5, liftGen2 OP_ExtractValue
                             (liftGen2 pair arbitrary (gen_dvalue n'))
                             arbitrary);
                (5, liftGen3 OP_InsertValue
                             (liftGen2 pair arbitrary (gen_dvalue n'))
                             (liftGen2 pair arbitrary (gen_dvalue n'))
                             arbitrary);
                (5, liftGen3 OP_Select
                             (liftGen2 pair arbitrary (gen_dvalue n'))
                             (liftGen2 pair arbitrary (gen_dvalue n'))
                             (liftGen2 pair arbitrary (gen_dvalue n'))) *)
             ]
    in
    freq [(3, liftGen DV next_g); (1, liftGen DV g_expr)]
  end.

Remove Hints gen_small_nonneg_i64 : typeclass_instances.

Instance gen_small_dvalue : GenSized dvalue :=
  {| arbitrarySized n :=
       if leb n 2 then gen_dvalue n else
         gen_dvalue 2
  |}.

Remove Hints gen_dvalue.

Instance show_dvalue : Show dvalue :=
  {| show := fix show_dv (v : dvalue) :=
       let fix show_expr e :=
           match e with
           | VALUE_Ident ident => show ident
           | VALUE_Integer n => show n
           | VALUE_Float f => show f
           | VALUE_Bool b => show b
           | VALUE_Null => "null"
           | VALUE_Zero_initializer => "zero_initialize"
           | VALUE_Cstring s => s
           | VALUE_None => "none"
           | VALUE_Undef => "undef"
           | VALUE_Struct fields => 
             "{ " ++ (List.fold_right
                        (fun f curr => (show (fst f)) ++ " " ++ (show_dv (snd f)) ++ ", " ++ curr)
                        "}" fields)
           | VALUE_Packed_struct fields =>
             "<{ " ++ (List.fold_right
                         (fun f curr => (show (fst f)) ++ " " ++ (show_dv (snd f)) ++ ", " ++ curr)
                         "}>" fields)
           | VALUE_Array arr =>
             "[ " ++ (List.fold_right
                        (fun a curr => (show (fst a)) ++ " " ++ (show_dv (snd a)) ++ ", " ++ curr)
                        "]" arr)
           | VALUE_Vector vec =>
             "< " ++ (List.fold_right
                        (fun a curr => (show (fst a)) ++ " " ++ (show_dv (snd a)) ++ ", " ++ curr)
                        ">" vec)
           | OP_IBinop op t v1 v2 =>
             (show op) ++ " " ++ (show t) ++ " "
                       ++ (show_dv v1) ++ " " ++ (show_dv v2)
           | OP_ICmp op t v1 v2 =>
             (show op) ++ " " ++ (show t) ++ " "
                       ++ (show_dv v1) ++ " " ++ (show_dv v2)
           | OP_FBinop op fm t v1 v2 =>
             (show op) ++ " " ++ (show fm) ++ " " ++ (show t) ++ " "
                       ++ (show_dv v1) ++ " " ++ (show_dv v2)
           | OP_FCmp op t v1 v2 =>
             (show op) ++ " " ++ (show t) ++ " "
                       ++ (show_dv v1) ++ " " ++ (show_dv v2)
           | OP_Conversion conv t_from v t_to =>
             "cast" ++ " " ++ (show t_from) ++ " " ++ (show_dv v)
                    ++ " to " ++ (show t_to)
           | OP_GetElementPtr base_t (ptr_t, ptr_v) idxs =>
             "getelementptr " ++ (show base_t) ++ ", "
                              ++ (show ptr_t) ++ " " ++ (show_dv ptr_v) ++ ", "
                              ++ (List.fold_right
                                    (fun idx curr =>
                                       (show (fst idx)) ++ " " ++ (show_dv (snd idx)) ++
                                                        ", " ++ curr)
                                    "" idxs)
           | OP_ExtractElement vec idx =>
             "extractelement " ++ (show (fst vec)) ++ " " ++ (show_dv (snd vec)) ++ ", "
                               ++ (show (fst idx)) ++ " " ++ (show_dv (snd idx))
           | OP_InsertElement vec elt idx =>
             "insertelement " ++ (show (fst vec)) ++ " " ++ (show_dv (snd vec)) ++ ", "
                              ++ (show (fst elt)) ++ " " ++ (show_dv (snd elt)) ++ ", "
                              ++ (show (fst idx)) ++ " " ++ (show_dv (snd idx))
           | OP_ShuffleVector vec1 vec2 idxmask => "shufflevector not implemented"
           | OP_ExtractValue vec idxs =>
             "extractvalue " ++ (show (fst vec)) ++ " " ++ (show_dv (snd vec)) ++ ", "
                             ++ (List.fold_right
                                   (fun idx curr =>
                                      (show idx) ++ ", " ++ curr)
                                   "" idxs)
           | OP_InsertValue vec elt idxs =>
             "insertvalue " ++ (show (fst vec)) ++ " " ++ (show_dv (snd vec)) ++ ", "
                            ++ (show (fst elt)) ++ " " ++ (show_dv (snd elt)) ++ ", "
                            ++ (List.fold_right
                                  (fun idx curr =>
                                     (show idx) ++ ", " ++ curr)
                                  "" idxs)
           | OP_Select cnd v1 v2 =>
             "select " ++ (show (fst cnd)) ++ " " ++ (show_dv (snd cnd)) ++ ", "
                       ++ (show (fst v1)) ++ " " ++ (show_dv (snd v1)) ++ ", "
                       ++ (show (fst v2)) ++ " " ++ (show_dv (snd v2)) ++ ", "
           end in
       match v with
       | DV e => show_expr e 
       | DVALUE_CodePointer instr_id => show instr_id
       | DVALUE_Addr a => show a
       | DVALUE_I1 n => show n
       | DVALUE_I32 n => show n
       | DVALUE_I64 n => show n
       | DVALUE_Poison => "poison"
       end
  |}.

(* Really need well-formed env generators: Sample (@arbitrary env _). *)

Instance gen_small_env : GenSized env :=
  {| arbitrarySized n :=
       if leb n 2 then vectorOf n arbitrary else
         vectorOf n arbitrary
  |}.

Instance gen_small_global_env : GenSized genv :=
  {| arbitrarySized n :=
       if leb n 2 then vectorOf n arbitrary else
         vectorOf n arbitrary
  |}.

Instance shrink_env : Shrink env :=
  {| shrink x := [] |}.

Instance shrink_genv : Shrink genv :=
  {| shrink x := [] |}.

Derive Arbitrary for pc.
Derive Show for pc.

(* Sample (@arbitrary pc _). type abbreviation cyclic? *)

Derive Arbitrary for frame.
Derive Show for frame.

Instance gen_small_stack : GenSized stack :=
  {| arbitrarySized n :=
       if leb n 2 then vectorOf n arbitrary else
         vectorOf n arbitrary
  |}.

Instance gen_state : GenSized state.
Proof. unfold state. auto with typeclass_instances. Defined.
