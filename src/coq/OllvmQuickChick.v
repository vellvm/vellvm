Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Require Import List ZArith.
Import ListNotations.
Require Import String.

Require Import compcert.lib.Integers.
Require Import Vellvm.Ollvm_ast.

Instance gen_numeric_literal_string : Gen string :=
  {| arbitrary := bindGen (@arbitrarySized nat genNatSized 3)
                          (fun n => returnGen ("id" ++ show_nat n)%string) |}.

Instance shrink_string : Shrink string := {| shrink x := [] |}.

Instance gen_dummy_float : Gen float.
Proof. unfold float. auto with typeclass_instances. Defined.

Instance show_float : Show float := {| show x := x |}.

Derive Arbitrary for linkage.
Derive Show for linkage.
Derive Arbitrary for dll_storage.
Derive Show for dll_storage.
Derive Arbitrary for visibility.
Derive Show for visibility.
Derive Arbitrary for cconv.
Derive Show for cconv.
Derive Arbitrary for param_attr.
Derive Show for param_attr.
Derive Arbitrary for fn_attr.
Derive Show for fn_attr.

Derive Arbitrary for raw_id.
Derive Show for raw_id.
Derive Arbitrary for ident.
Derive Show for ident.

Instance gen_local_id : Gen local_id.
Proof. auto with typeclass_instances. Defined.

Instance gen_global_id : Gen global_id.
Proof. auto with typeclass_instances. Defined.

Instance gen_block_id : Gen block_id.
Proof. auto with typeclass_instances. Defined.

Instance gen_function_id : Gen function_id.
Proof. auto with typeclass_instances. Defined.

Instance shrink_local_id : Shrink local_id.
Proof. auto with typeclass_instances. Defined.

Instance shrink_global_id : Shrink global_id.
Proof. auto with typeclass_instances. Defined.

Instance shrink_block_id : Shrink block_id.
Proof. auto with typeclass_instances. Defined.

Instance shrink_function_id : Shrink function_id.
Proof. auto with typeclass_instances. Defined.

Instance show_local_id : Show local_id.
Proof. auto with typeclass_instances. Defined.

Instance show_global_id : Show global_id.
Proof. auto with typeclass_instances. Defined.

Instance show_block_id : Show block_id.
Proof. auto with typeclass_instances. Defined.

Instance show_function_id : Show function_id.
Proof. auto with typeclass_instances. Defined.

Definition gen_regular_typ_size : G int :=
  freq [(3, returnGen (64%Z));
          (2, returnGen (32%Z));
          (1, returnGen (8%Z))].

Instance gen_typ : GenSized typ :=
  {| arbitrarySized :=
       fix generate_typ n :=
         let g := freq
                    [(5, bindGen gen_regular_typ_size (fun n => returnGen (TYPE_I n)));
                       (*                       
                       (5, returnGen (TYPE_Void));
                       (5, returnGen (TYPE_Half));
                       (5, returnGen (TYPE_Float));
                       (5, returnGen (TYPE_Double));
                       (1, returnGen (TYPE_X86_fp80));
                       (1, returnGen (TYPE_Fp128));
                       (2, returnGen (TYPE_Metadata));
                       (1, returnGen (TYPE_X86_mmx));
                       (2, returnGen (TYPE_Opaque));
                        *)
                       (5, liftGen TYPE_Identified arbitrary)
                    ]
         in 
         match n with
         | 0 => g
         | S n' =>
           freq [(0, liftGen TYPE_Pointer (generate_typ n'));
                   (0, liftGen2 TYPE_Array gen_regular_typ_size (generate_typ n'));
                   (0, liftGen2 TYPE_Function
                                (generate_typ n')
                                (listOf (generate_typ n'))) ;
                   (0, liftGen TYPE_Struct (listOf (generate_typ n')));
                   (0, liftGen TYPE_Packed_struct (listOf (generate_typ n')));
                   (0, liftGen2 TYPE_Vector gen_regular_typ_size (generate_typ n'));
                   (3, g)]
         end
  |}.

(* Large types don't scale! *)
Instance gen_small_typ : GenSized typ :=
  {| arbitrarySized n :=
       if Nat.leb n 2 then (arbitrarySized n) else 
         (arbitrarySized 3)
  |}.

Remove Hints gen_typ : typeclass_instances.

Instance shrink_typ : Shrink typ :=
  {| shrink x := [] |}. 

Instance show_typ : Show typ :=
  {| show := (
       fix show_t t :=
         match t with
         | TYPE_I sz => "i" ++ (show sz)
         | TYPE_Pointer t => (show_t t) ++ "*"
         | TYPE_Void => "void" 
         | TYPE_Half => "half"
         | TYPE_Float => "float"
         | TYPE_Double => "double"
         | TYPE_X86_fp80 => "X86_Fp80"
         | TYPE_Fp128 => "Fp128"
         | TYPE_Ppc_fp128 => "Ppc_fp128"
         (* | TYPE_Label  label is not really a type *)
         | TYPE_Metadata => "metadata"
         | TYPE_X86_mmx => "X86_mmx"
         | TYPE_Array sz t => "[" ++ (show sz) ++ " x " ++ (show_t t) ++ "]"
         | TYPE_Function ret args =>
           (show_t ret) ++ " ( " ++
                        (List.fold_right (fun arg curr => (show_t arg) ++ " " ++ curr)
                                         ")" args)
         | TYPE_Struct fields =>
           "{" ++ (List.fold_right (fun f curr => (show_t f) ++ " " ++ curr)
                                   "}" fields)
         | TYPE_Packed_struct fields =>
           "<{" ++ (List.fold_right (fun f curr => (show_t f) ++ " " ++ curr)
                                   "}>" fields)           
         | TYPE_Opaque => "opaque"
         | TYPE_Vector sz t =>  "<" ++ (show sz) ++ " x " ++ (show_t t) ++ ">"
         | TYPE_Identified id => show id
         end )%string
  |}.

Derive Arbitrary for icmp.

Instance show_icmp : Show icmp :=
  {| show cmp :=
       match cmp with 
       | Ollvm_ast.Eq => "eq"
       | Ne => "ne"
       | Ugt => "ugt"
       | Uge => "uge" 
       | Ult => "ult"
       | Ule => "ule"
       | Sgt => "sgt"
       | Sge => "sge"
       | Slt => "slt"
       | Sle => "sle"
       end
  |}.

Derive Arbitrary for fcmp.
Derive Show for fcmp.

Derive Arbitrary for ibinop.
Derive Show for ibinop.

Derive Arbitrary for fbinop.
Derive Show for fbinop.

Derive Arbitrary for fast_math.
Derive Show for fast_math.

Derive Arbitrary for conversion_type.
Derive Show for conversion_type.

Instance gen_static_value : GenSized Ollvm_ast.value :=
  {| arbitrarySized :=
       fix gen_sv n :=
         let g := freq [(5, liftGen VALUE_Ident arbitrary);
                          (5, liftGen VALUE_Integer arbitrary)
                          (*
                          (5, liftGen VALUE_Float arbitrary);
                          (5, liftGen VALUE_Bool arbitrary);
                          (5, returnGen VALUE_Null);
                          (3, returnGen VALUE_Zero_initializer);
                          (5, liftGen VALUE_Cstring arbitrary);
                          (1, returnGen VALUE_None);
                          (1, returnGen VALUE_Undef) *)]
         in
         match n with
         | 0 => liftGen SV g
         | S n' =>
           let next_g :=
               freq [(* (5, liftGen VALUE_Struct (listOf (liftGen2 pair arbitrary (gen_sv n'))));
                       (5, liftGen VALUE_Struct (listOf (liftGen2 pair arbitrary (gen_sv n')))); *)
                       (5, liftGen4 OP_IBinop arbitrary arbitrary (gen_sv n') (gen_sv n'));
                       (5, liftGen4 OP_ICmp arbitrary arbitrary (gen_sv n') (gen_sv n'))
                       (*
                       (5, liftGen4 OP_Conversion arbitrary arbitrary (gen_sv n') arbitrary);
                       (5, liftGen3 OP_GetElementPtr
                                    arbitrary
                                    (liftGen2 pair arbitrary (gen_sv n'))
                                    (listOf (liftGen2 pair arbitrary (gen_sv n'))));
                       (5, liftGen2 OP_ExtractElement
                                    (liftGen2 pair arbitrary (gen_sv n'))
                                    (liftGen2 pair arbitrary (gen_sv n')));
                       (5, liftGen3 OP_InsertElement
                                    (liftGen2 pair arbitrary (gen_sv n'))
                                    (liftGen2 pair arbitrary (gen_sv n'))
                                    (liftGen2 pair arbitrary (gen_sv n')));
                       (2, liftGen3 OP_ShuffleVector
                                    (liftGen2 pair arbitrary (gen_sv n'))
                                    (liftGen2 pair arbitrary (gen_sv n'))
                                    (liftGen2 pair arbitrary (gen_sv n')));
                       (5, liftGen2 OP_ExtractValue
                                    (liftGen2 pair arbitrary (gen_sv n'))
                                    arbitrary);
                       (5, liftGen3 OP_InsertValue
                                    (liftGen2 pair arbitrary (gen_sv n'))
                                    (liftGen2 pair arbitrary (gen_sv n'))
                                    arbitrary);
                       (5, liftGen3 OP_Select
                                    (liftGen2 pair arbitrary (gen_sv n'))
                                    (liftGen2 pair arbitrary (gen_sv n'))
                                    (liftGen2 pair arbitrary (gen_sv n')))
                       *)
                    ]
           in
           freq [(3, liftGen SV next_g); (1, liftGen SV g)]
         end
  |}.

Instance gen_small_static_value : GenSized Ollvm_ast.value :=
  {| arbitrarySized n :=
       if Nat.leb n 2 then (arbitrarySized n) else 
         (arbitrarySized 2)
  |}.


Instance show_static_value : Show Ollvm_ast.value := (
  {| show := fix show_sv (v : Ollvm_ast.value) :=
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
                        (fun f curr => (show (fst f)) ++ " " ++ (show_sv (snd f)) ++ ", " ++ curr)
                        "}" fields)
           | VALUE_Packed_struct fields =>
             "<{ " ++ (List.fold_right
                         (fun f curr => (show (fst f)) ++ " " ++ (show_sv (snd f)) ++ ", " ++ curr)
                         "}>" fields)
           | VALUE_Array arr =>
             "[ " ++ (List.fold_right
                        (fun a curr => (show (fst a)) ++ " " ++ (show_sv (snd a)) ++ ", " ++ curr)
                        "]" arr)
           | VALUE_Vector vec =>
             "< " ++ (List.fold_right
                        (fun a curr => (show (fst a)) ++ " " ++ (show_sv (snd a)) ++ ", " ++ curr)
                        ">" vec)
           | OP_IBinop op t v1 v2 =>
             (show op) ++ " " ++ (show t) ++ " "
                       ++ (show_sv v1) ++ " " ++ (show_sv v2)
           | OP_ICmp op t v1 v2 =>
             (show op) ++ " " ++ (show t) ++ " "
                       ++ (show_sv v1) ++ " " ++ (show_sv v2)
           | OP_FBinop op fm t v1 v2 =>
             (show op) ++ " " ++ (show fm) ++ " " ++ (show t) ++ " "
                       ++ (show_sv v1) ++ " " ++ (show_sv v2)
           | OP_FCmp op t v1 v2 =>
             (show op) ++ " " ++ (show t) ++ " "
                       ++ (show_sv v1) ++ " " ++ (show_sv v2)
           | OP_Conversion conv t_from v t_to =>
             "cast" ++ " " ++ (show t_from) ++ " " ++ (show_sv v)
                    ++ " to " ++ (show t_to)
           | OP_GetElementPtr base_t (ptr_t, ptr_v) idxs =>
             "getelementptr " ++ (show base_t) ++ ", "
                              ++ (show ptr_t) ++ " " ++ (show_sv ptr_v) ++ ", "
                              ++ (List.fold_right
                                    (fun idx curr =>
                                       (show (fst idx)) ++ " " ++ (show_sv (snd idx)) ++
                                                        ", " ++ curr)
                                    "" idxs)
           | OP_ExtractElement vec idx =>
             "extractelement " ++ (show (fst vec)) ++ " " ++ (show_sv (snd vec)) ++ ", "
                               ++ (show (fst idx)) ++ " " ++ (show_sv (snd idx))
           | OP_InsertElement vec elt idx =>
             "insertelement " ++ (show (fst vec)) ++ " " ++ (show_sv (snd vec)) ++ ", "
                              ++ (show (fst elt)) ++ " " ++ (show_sv (snd elt)) ++ ", "
                              ++ (show (fst idx)) ++ " " ++ (show_sv (snd idx))
           | OP_ShuffleVector vec1 vec2 idxmask => "shufflevector not implemented"
           | OP_ExtractValue vec idxs =>
             "extractvalue " ++ (show (fst vec)) ++ " " ++ (show_sv (snd vec)) ++ ", "
                             ++ (List.fold_right
                                   (fun idx curr =>
                                      (show idx) ++ ", " ++ curr)
                                   "" idxs)
           | OP_InsertValue vec elt idxs =>
             "insertvalue " ++ (show (fst vec)) ++ " " ++ (show_sv (snd vec)) ++ ", "
                            ++ (show (fst elt)) ++ " " ++ (show_sv (snd elt)) ++ ", "
                            ++ (List.fold_right
                                  (fun idx curr =>
                                     (show idx) ++ ", " ++ curr)
                                  "" idxs)
           | OP_Select cnd v1 v2 =>
             "select " ++ (show (fst cnd)) ++ " " ++ (show_sv (snd cnd)) ++ ", "
                       ++ (show (fst v1)) ++ " " ++ (show_sv (snd v1)) ++ ", "
                       ++ (show (fst v2)) ++ " " ++ (show_sv (snd v2)) ++ ", "
           end in
       match v with
       | SV e => show_expr e 
       end
  |} )%string.

Instance shrink_static_value : Shrink Ollvm_ast.value :=
  {| shrink x := [] |}.

Remove Hints gen_static_value : typeclass_instances.

(* Sample (@arbitrary Ollvm_ast.value _). *)

Instance gen_tvalue : GenSized tvalue.
Proof. unfold tvalue. auto with typeclass_instances. Defined.

Instance show_tvalue : Show tvalue.
Proof. unfold tvalue. auto with typeclass_instances. Defined.

Derive Arbitrary for instr_id.
Derive Show for instr_id.
Derive Arbitrary for phi.
Derive Show for phi.

(******** Instr ********)

Derive Arbitrary for instr.
Derive Show for instr.


(******** End of Instr ********)
(******** Terminator ********)

Derive Arbitrary for terminator.
Derive Show for terminator.

(******** End of Terminator ********)

Derive Arbitrary for thread_local_storage.
Derive Show for thread_local_storage.

Derive Arbitrary for global.
Derive Show for global.

(******** Declaration ********)

Derive Arbitrary for declaration.
Derive Show for declaration.

(* Sample (@arbitrary declaration _). *)

(******** End of Declaration ********)

(******** Code ********)

Instance gen_code : Gen code.
Proof. unfold code. auto with typeclass_instances. Defined.

(* Sample (@arbitrary code _). *)

(******** End of Code ********)

(******** Block ********)

Derive Arbitrary for block.
Derive Show for block.

(******** End of Block ********)


Instance gen_metadata : GenSized metadata :=
  {| arbitrarySized :=
       let g := freq [(5, liftGen METADATA_Const arbitrary);
                      (2, returnGen METADATA_Null);
                      (5, liftGen METADATA_Id arbitrary);
                      (5, liftGen METADATA_String arbitrary)] in
       let fix gen_md n :=
           match n with
           | 0 => g
           | S n' =>
             freq [(5, liftGen METADATA_Node (vectorOf n' (gen_md n')));
                   (5, liftGen METADATA_Named (vectorOf n' arbitrary));
                   (2, g)]
           end in
       gen_md
  |}.

Instance shrink_metadata : Shrink metadata :=
  {| shrink x := [] |}.









