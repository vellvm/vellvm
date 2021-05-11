From QuickChick Require Import QuickChick.
From Vellvm Require Import ShowAST ReprAST GenAST TopLevel LLVMAst DynamicValues.
Require Import Semantics.LLVMEvents.
Require Import Semantics.InterpretationStack.
Require Import Handlers.Handlers.

Require Import String.
Require Import ZArith.

From ITree Require Import
     ITree
     Interp.Recursion
     Events.Exception.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

(* TODO: Use the existing vellvm version of this? *)
Inductive MlResult a e :=
| MlOk : a -> MlResult a e
| MlError : e -> MlResult a e.

Extract Inductive MlResult => "result" [ "Ok" "Error" ].

Unset Guard Checking.
Fixpoint step (t : ITreeDefinition.itree L5 TopLevel.res_L4) : MlResult DV.uvalue string
  := match observe t with
     | RetF (_,(_,(_,x))) => MlOk _ string x
     | TauF t => step t
     | VisF _ e k => MlError _ string "Uninterpreted event"
     end.
Set Guard Checking.

Definition interpret (prog : list (toplevel_entity typ (block typ * list (block typ)))) : MlResult uvalue string
  := step (TopLevel.interpreter prog).

Axiom to_caml_str : string -> string.
Extract Constant to_caml_str =>
"fun (s: char list) ->
  let r = Bytes.create (List.length s) in
  let rec fill pos = function
  | [] -> r
  | c :: s -> Bytes.set r pos c; fill (pos + 1) s
  in Bytes.to_string (fill 0 s)".


Axiom llc_command : string -> int.
Extract Constant llc_command => "fun prog -> let f = open_out ""temporary_vellvm.ll"" in Printf.fprintf f ""%s"" prog; close_out f; Sys.command ""clang -Wno-everything temporary_vellvm.ll -o vellvmqc && ./vellvmqc""".

Axiom vellvm_print_ll : list (toplevel_entity typ (block typ * list (block typ))) -> string.
Extract Constant vellvm_print_ll => "fun prog -> Llvm_printer.toplevel_entities Format.str_formatter prog; Format.flush_str_formatter".

Definition run_llc (prog : list (toplevel_entity typ (block typ * list (block typ)))) : uvalue
  := UVALUE_I8 (repr (llc_command (to_caml_str (show prog)))).

Definition vellvm_agrees_with_clang (prog : list (toplevel_entity typ (block typ * list (block typ)))) : Checker
  := 
    (* collect (show prog) *)
            match interpret prog, run_llc prog with
            | MlOk (UVALUE_I8 x), UVALUE_I8 y =>
              whenFail ("Vellvm: " ++ show (unsigned x) ++ " | Clang: " ++ show (unsigned y) ++ " | Ast: " ++ ReprAST.repr prog) (equ x y)
            | _, _ => checker true
            end.

Definition agrees := (forAll (run_GenLLVM gen_llvm) vellvm_agrees_with_clang).
Extract Constant defNumTests    => "0".
QCInclude "../../ml/*".
QCInclude "../../ml/libvellvm/*".
(* QCInclude "../../ml/libvellvm/llvm_printer.ml". *)
(* QCInclude "../../ml/libvellvm/Camlcoq.ml". *)
(* QCInclude "../../ml/extracted/*ml". *)
QuickChickDebug Debug On.
QuickChick (forAll (run_GenLLVM gen_llvm) vellvm_agrees_with_clang).
(*! QuickChick agrees. *)


(* Definition v0 := DVALUE_I64 (match eval_int_op (Sub false false) (Int64.repr 0) (Int64.repr 3) with *)
(*          | inr (DVALUE_I64 x) => x *)
(*          | _ => zero *)
(*          end). *)

(* Definition v1 := eval_icmp Ule v0 (DVALUE_I64 (Int64.repr 9)). *)

(* Compute v1. *)
(* Definition v1_dv := (DVALUE_I1 *)
(*                                         {| *)
(*                                         Int1.intval := 0; *)
(*                                         Int1.intrange := Int1.Z_mod_modulus_range' 0 |}). *)

(* Definition v2 := eval_select_h v1_dv (dvalue_to_uvalue v0) (dvalue_to_uvalue (DVALUE_I64 (Int64.repr 9))). *)

(* Compute v2. *)

(* Definition v2_uv := (UVALUE_I64 *)
(*                                         {| *)
(*                                         Int64.intval := 9; *)
(*                                         Int64.intrange := Integers.Int64.Z_mod_modulus_range' 9 |}). *)

(* Definition v2_dv := (DVALUE_I64 *)
(*                                         {| *)
(*                                         Int64.intval := 9; *)
(*                                         Int64.intrange := Integers.Int64.Z_mod_modulus_range' 9 |}). *)


(* Definition v3 := eval_icmp Ugt v2_dv (DVALUE_I64 zero). *)

(* Compute v3. *)

(* Compute (Z.rem (-1) 4). *)
(* Compute (Int64.mods (Int64.repr (-1)) (Int64.repr 4)). *)


(* define i8 @main() { *)
(* b0: *)
(* br label %b1 *)
(* b1: *)
(* %v0 = srem i64 -1, 4 *)
(* %v1 = icmp ule i64 %v0, 3 *)
(* %v2 = select i1 %v1, i64 %v0, i64 3 *)
(* %v3 = icmp ugt i64 %v2, 0 *)
(* br i1 %v3, label %b4, label %b2 *)
(* b4: *)
(* %v4 = phi i64 [ %v5, %b3 ], [ %v2, %b1 ] *)
(* %v7 = alloca i1 *)
(* store i1 %v1, i1* %v7 *)
(* %v8 = add i1 %v3, %v1 *)
(* %v9 = srem i32 0, 5 *)
(* %v10 = xor i1 %v1, 3 *)
(* ret i8 -2 *)
(* b3: *)
(* %v5 = sub i64 %v4, 1 *)
(* %v6 = icmp ugt i64 %v5, 0 *)
(* br i1 %v6, label %b4, label %b2 *)
(* b2: *)
(* ret i8 4 *)
(* } *)
(* Vellvm: 4 | Clang: 254 *)


(* define i8 @main() { *)
(* b0: *)
(* br label %b1 *)
(* b1: *)
(* %v0 = lshr i64 -6, -5 *)
(* %v1 = icmp ule i64 %v0, 10 *)
(* %v2 = select i1 %v1, i64 %v0, i64 10 *)
(* %v3 = icmp ugt i64 %v2, 0 *)
(* br i1 %v3, label %b4, label %b2 *)
(* b4: *)
(* %v5 = mul i32 -3, -2 *)
(* ret i8 -6 *)
(* b2: *)
(* ret i8 1 *)
(* } *)


                                                             

(* Definition v0 : uvalue := (match eval_int_op (UDiv false) (Int64.repr (-1)) (Int64.repr 2) with *)
(*          | inr dv => dvalue_to_uvalue dv *)
(*          | _ => UVALUE_Poison *)
(*         end). *)

(* Compute (eval_int_icmp Ule *)
(*                        (match eval_int_op (UDiv false) (Int64.repr (-1)) (Int64.repr 2) with *)
(*          | inr (DVALUE_I64 x) => x *)
(*          | _ => zero *)
(*         end) (Int64.repr 3)). *)

(* Definition v1 : dvalue := (eval_int_icmp Ule *)
(*                        (match eval_int_op (UDiv false) (Int64.repr (-1)) (Int64.repr 2) with *)
(*          | inr (DVALUE_I64 x) => x *)
(*          | _ => zero *)
(*         end) (Int64.repr 3)). *)

(* Compute eval_select_h v1 v0 (UVALUE_I64 (Int64.repr 3)). *)







(* define i8 @main() { *)
(* b0: *)
(* br label %b1 *)
(* b1: *)
(* %v0 = udiv i64 -1, 2 *)
(* %v1 = icmp ule i64 %v0, 3 ; v1 = 0 *)
(* %v2 = select i1 %v1, i64 %v0, i64 3 ; v2 = 3 *)
(* %v3 = icmp ugt i64 %v2, 0 *)
(* br i1 %v3, label %b4, label %b2 *)
(* b3: *)
(* %v5 = sub i64 %v4, 1 *)
(* %v6 = icmp ugt i64 sub i64 %v4, 1, 0 *)
(* br i1 %v6, label %b4, label %b2 *)
(* b4: *)
(* %v7 = sub i8 -2, -2 *)
(* ret i8 %v7 *)
(* b2: *)
(* ret i8 0 *)
(* } *)
(* (0,1) *)


(* (* Am I generating next block for loop???? *) *)
(* define i8 @main() { *)
(* b0: *)
(* br label %b1 *)
(* b1: *)
(* %v0 = lshr i64 -6, -5 *)
(* %v1 = icmp ule i64 %v0, 10 *)
(* %v2 = select i1 %v1, i64 %v0, i64 10 *)
(* %v3 = icmp ugt i64 %v2, 0 *)
(* br i1 %v3, label %b4, label %b2 *)
(* b4: *)
(* %v5 = mul i32 -3, -2 *)
(* ret i8 -6 *)
(* b2: *)
(* ret i8 1 *)
(* } *)

(* (1,250) *)


(* (* *)

(* define i8 @main() { *)
(* b0: *)
(* br label %b1 *)
(* b1: *)
(* %v0 = xor i64 -1, 3 *)
(* %v1 = icmp ule i64 %v0, 4 *)
(* %v2 = select i1 %v1, i64 %v0, i64 4 *)
(* %v3 = icmp ugt i64 %v2, 0 *)
(* br i1 %v3, label %b4, label %b2 *)
(* b4: *)
(* %v9 = alloca i32 *)
(* store i32 0, i32* %v9 *)
(* %v10 = sub i32 4, 5 *)
(* ret i8 5 *)
(* b2: *)
(* %v4 = mul i32 1, 2 *)
(* %v5 = alloca i64 *)
(* store i64 %v2, i64* %v5 *)
(* %v6 = ashr i8 1, 4 *)
(* %v7 = alloca i64 *)
(* store i64 %v0, i64* %v7 *)
(* ret i8 %v6 *)
(* } *)
(* *) *)
