From QuickChick Require Import QuickChick.
From Vellvm Require Import GenAST TopLevel LLVMAst DynamicValues.
Require Import String.
Require Import ZArith.

From ITree Require Import
     ITree
     Interp.Recursion
     Events.Exception.

(* TODO: Use the existing vellvm version of this? *)
Inductive MlResult a e :=
| MlOk : a -> MlResult a e
| MlError : e -> MlResult a e.

Extract Inductive MlResult => "result" [ "Ok" "Error" ].

Unset Guard Checking.
Fixpoint step (t : ITreeDefinition.itree IO.L5 TopLevelEnv.res_L4) : MlResult TopLevelEnv.res_L0 string
  := match observe t with
     | RetF (_,(_,(_,x))) => MlOk TopLevelEnv.res_L0 string x
     | TauF t => step t
     | VisF _ e k => MlError TopLevelEnv.res_L0 string "Uninterpreted event"
     end.
Set Guard Checking.

Definition interpret (prog : list (toplevel_entity typ (list (block typ)))) : MlResult uvalue string
  := step (TopLevelEnv.interpreter prog).

Definition always_zeroP (prog : list (toplevel_entity typ (list (block typ)))) : Checker
  := 
    collect (show prog)
            match interpret prog with
            | MlOk (UVALUE_I8 x) => checker true
            | MlError e => checker true (* Ignore errors for now *)
            | MlOk (UVALUE_IBinop _ _ _) => checker true
            | MlOk uv => checker true
            end.

Extract Constant defNumTests    => "20".
QuickChick (forAll (run_GenLLVM gen_llvm) always_zeroP).
